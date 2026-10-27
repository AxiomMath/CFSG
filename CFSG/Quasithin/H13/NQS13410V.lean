module

public import CFSG.Quasithin.H13.NQS13410U
public import CFSG.Quasithin.H13.NQS13410M
public import CFSG.Quasithin.H13.NQS13410S
public import CFSG.Quasithin.H13.NQS13410T

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_T_of_conj_eq {K T U : Subgroup G} (hCKT : (K ⊔ T) ⊓ centralizer (U : Set G) ≤ T)
    {k t : G} (hk : k ∈ K) (ht : t ∈ T) (h : k⁻¹ * t ∈ centralizer (U : Set G)) : k ∈ T := by
  have h1 : k⁻¹ * t ∈ T :=
    hCKT (mem_inf.2 ⟨mul_mem (inv_mem (mem_sup_left hk)) (mem_sup_right ht), h⟩)
  have e : k = t * (k⁻¹ * t)⁻¹ := by group
  rw [e]
  exact mul_mem ht (inv_mem h1)

theorem l32_parData {K T U L₁ Z : Subgroup G} (C : L3Coords K U)
    (hCB : ∀ s : ↥(normalizer (U : Set G)), (s : G) ∈ T ⊓ K → C.ρ s ∈ l3B)
    (hKU : K ≤ normalizer (U : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ K) K) (hCKT : K ⊓ centralizer (U : Set G) ≤ T)
    (hL1T : L₁ ⊔ T ≤ K ⊔ T) (hZL1 : centralizer (Z : Set G) ≤ L₁ ⊔ T)
    (hL1Z : L₁ ⊔ T ≤ centralizer (Z : Set G))
    (hCUTZ : ∀ w ∈ U, w ∈ centralizer (T : Set G) → w ∈ Z)
    (hfix : ∀ k ∈ K, (∀ w ∈ U, w ∈ centralizer (T : Set G) → k * w * k⁻¹ = w) →
      k ∈ centralizer (Z : Set G))
    (hU1 : U ≠ ⊥) (hT2 : IsPGroup 2 ↥T) (hTU : T ≤ normalizer (U : Set G)) (hUT : U ≤ T) :
    ParData K T U (L₁ ⊔ T) C.ρ ⊤ (l3Stab l3e1) ∧
      ∀ β ∈ l3B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ C.ρ g = β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥K →* L3.Γ := C.ρ.comp (Subgroup.inclusion hKU) with hf
  have hfs : Function.Surjective f := by
    intro γ
    obtain ⟨g, hgK, hg⟩ := C.image_K γ
    exact ⟨⟨g, hgK⟩, hg⟩
  set P := ((T ⊓ K).subgroupOf K).map f with hP
  have hidx : ¬ 2 ∣ P.index := fun h => hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ hfs))
  have h8 : 8 ∣ Nat.card ↥P := by
    have h1 := P.index_mul_card
    rw [HSType.card_SL_three_two] at h1
    have hcop : Nat.Coprime 8 P.index :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)))
    exact hcop.dvd_of_dvd_mul_left ⟨21, by omega⟩
  have hPB : P ≤ l3B := by
    rintro _ ⟨k, hk, rfl⟩
    exact hCB (Subgroup.inclusion hKU k) (mem_subgroupOf.1 hk)
  have hPeq : P = l3B := by
    refine eq_of_le_of_card_ge hPB ?_
    rw [card_l3B]
    exact Nat.le_of_dvd Nat.card_pos h8
  have hB : ∀ β ∈ l3B, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ C.ρ g = β := by
    intro β hβ
    rw [← hPeq] at hβ
    obtain ⟨k, hk, rfl⟩ := hβ
    exact ⟨Subgroup.inclusion hKU k, mem_subgroupOf.1 hk, rfl⟩
  have hfixT : ∀ w : ↥U, (w : G) ∈ centralizer (T : Set G) → C.c w = 0 ∨ C.c w = l3e1 := by
    intro w hwT
    by_cases hw0 : C.c w = 0
    · exact Or.inl hw0
    refine Or.inr (l3_fixB _ hw0 fun b hb => ?_)
    obtain ⟨s, hs, hsb⟩ := hB b hb
    rw [← hsb]
    refine (C.fix_iff s w).1 ?_
    rw [mem_centralizer_iff.mp hwT s (mem_inf.1 hs).1, mul_inv_cancel_right]
  have hrho : ∀ g : ↥(normalizer (U : Set G)), C.ρ g ∈ l3Stab l3e1 →
      ∀ w : ↥U, (w : G) ∈ centralizer (T : Set G) → (g : G) * w * (g : G)⁻¹ = w := by
    intro g hg w hwT
    refine (C.fix_iff g w).2 ?_
    rcases hfixT w hwT with h | h
    · rw [h, L3.act_zero]
    · rw [h]
      exact hg
  obtain ⟨x, hxU, hxT, hx1⟩ := exists_mem_centralizer_ne_one hT2 hUT hTU hU1
  set u₀ : ↥U := ⟨x, hxU⟩ with hu₀def
  have hu₀1 : u₀ ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hcu₀ : C.c u₀ = l3e1 := (hfixT u₀ hxT).resolve_left (C.c_ne_zero hu₀1)
  have hu₀Z : x ∈ Z := hCUTZ x hxU hxT
  refine ⟨⟨hKU, hTK, hL1T, le_sup_right, fun g hgK h1 => hCKT (mem_inf.2 ⟨hgK, (C.ker g).1 h1⟩),
    fun γ _ => C.image_K γ, fun _ _ => mem_top _, fun g hgK => ⟨fun h => ?_, fun h => ?_⟩⟩, hB⟩
  · exact hZL1 (hfix g hgK fun w hwU hwT => hrho g h ⟨w, hwU⟩ hwT)
  · have hgZ := hL1Z h
    have h2 : (g : G) * (u₀ : G) * (g : G)⁻¹ = u₀ := by
      show (g : G) * x * (g : G)⁻¹ = x
      rw [← mem_centralizer_iff.mp hgZ x hu₀Z, mul_inv_cancel_right]
    have h3 := (C.fix_iff g u₀).1 h2
    rw [hcu₀] at h3
    exact h3

theorem inW4_e0123 : InW4 e0123 := by decide

theorem mem_coreMod_e45 : e45 ∈ G6.coreMod 6 := by decide

omit [Finite G] in
theorem frame4_parData {K T U L₁ Z : Subgroup G} (F : Frame4 T K U)
    (hTK : T ≤ normalizer (K : Set G)) (hCKT : (K ⊔ T) ⊓ centralizer (U : Set G) ≤ T)
    (hL1T : L₁ ⊔ T ≤ K ⊔ T) (hZL1 : centralizer (Z : Set G) ≤ L₁ ⊔ T)
    (hL1Z : L₁ ⊔ T ≤ centralizer (Z : Set G))
    (hCUTZ : ∀ w ∈ U, w ∈ centralizer (T : Set G) → w ∈ Z)
    (hfix : ∀ k ∈ K, (∀ w ∈ U, w ∈ centralizer (T : Set G) → k * w * k⁻¹ = w) →
      k ∈ centralizer (Z : Set G)) :
    ParData K T U (L₁ ⊔ T) F.ρ (alternatingGroup (Fin 6)) stab45 ∧
      ∀ β ∈ a6D, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ F.ρ g = β := by
  classical
  have hfixiff : ∀ (g : ↥(normalizer (U : Set G))) (w : ↥U),
      (g : G) * w * (g : G)⁻¹ = w ↔ act4f (F.ρ g) (F.ψ w) = F.ψ w := by
    intro g w
    have h1 := F.equiv g w
    constructor
    · intro h
      have h2 : conjAct U g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
      rw [h2] at h1
      exact (congrArg Subtype.val h1).symm
    · intro h
      have h2 : F.ψ (conjAct U g w) = F.ψ w := by
        rw [h1]
        exact Subtype.ext h
      have h3 := congrArg Subtype.val (F.ψ.injective h2)
      rw [A5.conjAct_val] at h3
      exact h3
  have hker : ∀ g : ↥(normalizer (U : Set G)), F.ρ g = 1 → (g : G) ∈ centralizer (U : Set G) :=
    fun g h1 => mem_centralizer_iff.2 fun w hw => by
      have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1]; exact act4f_one _ (F.ψ ⟨w, hw⟩).2)
      calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
        _ = g * w := by group
  have hB : ∀ β ∈ a6D, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ F.ρ g = β := by
    intro β hβ
    obtain ⟨hβD, hβ1⟩ := (mem_a6D_iff β).1 hβ
    obtain ⟨t, htT, hρt⟩ := F.DA_T β hβD (Perm.mem_alternatingGroup.2 hβ1)
    obtain ⟨k, hkK, hρk⟩ := (F.image_L β).2 (Perm.mem_alternatingGroup.2 hβ1)
    have h1 : F.ρ (k⁻¹ * t) = 1 := by rw [map_mul, map_inv, hρk, hρt, inv_mul_cancel]
    exact ⟨k, mem_inf.2 ⟨mem_T_of_conj_eq hCKT hkK htT (hker _ h1), hkK⟩, hρk⟩
  set w₀ : ↥U := F.ψ.symm ⟨e0123, inW4_e0123⟩ with hw₀
  have hψw₀ : (F.ψ w₀ : P6) = e0123 := by rw [hw₀, MulEquiv.apply_symm_apply]
  have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
    have hD := F.T_D ⟨t, F.T_le ht⟩ ht
    have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact act4f_e0123_of_inD6 _ hD)
    calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
      _ = w₀ * t := by rw [h1]
  refine ⟨⟨F.L_le, hTK, hL1T, le_sup_right, fun g hgK h1 => hCKT (mem_inf.2
    ⟨mem_sup_left hgK, hker g h1⟩), fun γ hγ => (F.image_L γ).2 hγ,
    fun g hgK => (F.image_L _).1 ⟨g, hgK, rfl⟩, fun g hgK => ⟨fun h => ?_, fun h => ?_⟩⟩, hB⟩
  · have hP45 := ((mem_stab45_iff _).1 h).2
    refine hZL1 (hfix g hgK fun w hwU hwT => (hfixiff g ⟨w, hwU⟩).2 ?_)
    refine act4f_fix_of_pres45 _ hP45 _ (F.ψ ⟨w, hwU⟩).2 fun τ hτ => ?_
    obtain ⟨hτD, hτ1⟩ := (mem_a6D_iff τ).1 hτ
    obtain ⟨t, htT, hρt⟩ := F.DA_T τ hτD (Perm.mem_alternatingGroup.2 hτ1)
    rw [← hρt]
    refine (hfixiff t ⟨w, hwU⟩).1 ?_
    show (t : G) * w * (t : G)⁻¹ = w
    rw [mem_centralizer_iff.mp hwT t htT, mul_inv_cancel_right]
  · have hgZ := hL1Z h
    have h2 : (g : G) * (w₀ : G) * (g : G)⁻¹ = w₀ := by
      rw [← mem_centralizer_iff.mp hgZ w₀ (hCUTZ w₀ w₀.2 hw₀T), mul_inv_cancel_right]
    have h3 := (hfixiff g w₀).1 h2
    rw [hψw₀] at h3
    have h4 : Perm.sign (F.ρ g) = 1 := Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, hgK, rfl⟩)
    exact (mem_stab45_iff _).2 ⟨h4, pres45_of_act4f_fix _ h3⟩

omit [Finite G] in
theorem frame5_parData {K T U L₁ Z : Subgroup G} (F : Frame5 T K U)
    (hTK : T ≤ normalizer (K : Set G)) (hCKT : (K ⊔ T) ⊓ centralizer (U : Set G) ≤ T)
    (hL1T : L₁ ⊔ T ≤ K ⊔ T) (hZL1 : centralizer (Z : Set G) ≤ L₁ ⊔ T)
    (hL1Z : L₁ ⊔ T ≤ centralizer (Z : Set G))
    (hCUTZ : ∀ w ∈ U, w ∈ centralizer (T : Set G) → w ∈ Z)
    (hfix : ∀ k ∈ K, (∀ w ∈ U, w ∈ centralizer (T : Set G) → k * w * k⁻¹ = w) →
      k ∈ centralizer (Z : Set G)) :
    ParData K T U (L₁ ⊔ T) F.ρ (alternatingGroup (Fin 6)) stab45 ∧
      ∀ β ∈ a6D, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ F.ρ g = β := by
  classical
  have hfixiff : ∀ (g : ↥(normalizer (U : Set G))) (w : ↥U),
      (g : G) * w * (g : G)⁻¹ = w ↔ G6.permAct 6 (F.ρ g) (F.ψ w) = F.ψ w := by
    intro g w
    have h1 := F.equiv g w
    constructor
    · intro h
      have h2 : conjAct U g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
      rw [h2] at h1
      exact (congrArg Subtype.val h1).symm
    · intro h
      have h2 : F.ψ (conjAct U g w) = F.ψ w := by
        rw [h1]
        exact Subtype.ext h
      have h3 := congrArg Subtype.val (F.ψ.injective h2)
      rw [A5.conjAct_val] at h3
      exact h3
  have hker : ∀ g : ↥(normalizer (U : Set G)), F.ρ g = 1 → (g : G) ∈ centralizer (U : Set G) :=
    fun g h1 => mem_centralizer_iff.2 fun w hw => by
      have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1, map_one]; rfl)
      calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
        _ = g * w := by group
  have hB : ∀ β ∈ a6D, ∃ g : ↥(normalizer (U : Set G)), (g : G) ∈ T ⊓ K ∧ F.ρ g = β := by
    intro β hβ
    obtain ⟨hβD, hβ1⟩ := (mem_a6D_iff β).1 hβ
    obtain ⟨t, htT, hρt⟩ := F.DA_T β hβD (Perm.mem_alternatingGroup.2 hβ1)
    obtain ⟨k, hkK, hρk⟩ := (F.image_L β).2 (Perm.mem_alternatingGroup.2 hβ1)
    have h1 : F.ρ (k⁻¹ * t) = 1 := by rw [map_mul, map_inv, hρk, hρt, inv_mul_cancel]
    exact ⟨k, mem_inf.2 ⟨mem_T_of_conj_eq hCKT hkK htT (hker _ h1), hkK⟩, hρk⟩
  set w₀ : ↥U := F.ψ.symm ⟨e45, mem_coreMod_e45⟩ with hw₀
  have hψw₀ : ((F.ψ w₀ : ↥(G6.coreMod 6)) : G6.PermMod 6) = e45 := by
    rw [hw₀, MulEquiv.apply_symm_apply]
  have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
    have hD := F.T_D ⟨t, F.T_le ht⟩ ht
    have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact permAct_e45_of_inD6 _ hD)
    calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
      _ = w₀ * t := by rw [h1]
  refine ⟨⟨F.L_le, hTK, hL1T, le_sup_right, fun g hgK h1 => hCKT (mem_inf.2
    ⟨mem_sup_left hgK, hker g h1⟩), fun γ hγ => (F.image_L γ).2 hγ,
    fun g hgK => (F.image_L _).1 ⟨g, hgK, rfl⟩, fun g hgK => ⟨fun h => ?_, fun h => ?_⟩⟩, hB⟩
  · have hP45 := ((mem_stab45_iff _).1 h).2
    refine hZL1 (hfix g hgK fun w hwU hwT => (hfixiff g ⟨w, hwU⟩).2 ?_)
    refine permAct_fix_of_pres45 _ hP45 _ fun τ hτ => ?_
    obtain ⟨hτD, hτ1⟩ := (mem_a6D_iff τ).1 hτ
    obtain ⟨t, htT, hρt⟩ := F.DA_T τ hτD (Perm.mem_alternatingGroup.2 hτ1)
    rw [← hρt]
    refine (hfixiff t ⟨w, hwU⟩).1 ?_
    show (t : G) * w * (t : G)⁻¹ = w
    rw [mem_centralizer_iff.mp hwT t htT, mul_inv_cancel_right]
  · have hgZ := hL1Z h
    have h2 : (g : G) * (w₀ : G) * (g : G)⁻¹ = w₀ := by
      rw [← mem_centralizer_iff.mp hgZ w₀ (hCUTZ w₀ w₀.2 hw₀T), mul_inv_cancel_right]
    have h3 := (hfixiff g w₀).1 h2
    rw [hψw₀] at h3
    have h4 : Perm.sign (F.ρ g) = 1 := Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, hgK, rfl⟩)
    exact (mem_stab45_iff _).2 ⟨h4, pres45_of_permAct_fix _ h3⟩

end CFSG.Quasithin.H13.NQS134
