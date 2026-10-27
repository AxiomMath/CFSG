module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL3b
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL3a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open Module
open CFSG.QuasithinUnique.Setup.Offender (commGL fixGL mem_fixGL)

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {𝓛 : Subgroup (E ≃ₗ[ZMod 2] E)}

theorem eq_one_or_eq_of_centralizer [FiniteDimensional (ZMod 2) E] [IsSimpleGroup ↥𝓛]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) (hE : commGL 𝓛 ⊤ = ⊤)
    (hdim : finrank (ZMod 2) E ≤ 6) {c c' : E ≃ₗ[ZMod 2] E} (hc : ∀ y ∈ 𝓛, c * y = y * c)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hc' : ∀ y ∈ 𝓛, c' * y = y * c') (hcc' : c * c' = c' * c) :
    c' = 1 ∨ c' = c := by
  classical
  haveI : Finite E := Module.finite_of_finite (ZMod 2)
  obtain ⟨-, hXK, hK3, hfaithK, -⟩ := centralizer_structure eV hE hdim hc hc2 hc1
  set N : E →ₗ[ZMod 2] E := (c : E →ₗ[ZMod 2] E) - LinearMap.id with hN
  have hNapp : ∀ v, N v = c v - v := fun v => rfl
  have hNy : ∀ y ∈ 𝓛, ∀ v, N (y v) = y (N v) := fun y hy v => by
    rw [hNapp, hNapp, map_sub, CFSG.ASVolI.burnsideB49x_gl_apply_comm (hc y hy)]
  have hNc' : ∀ v, N (c' v) = c' (N v) := fun v => by
    rw [hNapp, hNapp, map_sub, CFSG.ASVolI.burnsideB49x_gl_apply_comm hcc']
  have hKinv : ∀ y ∈ 𝓛, ∀ x ∈ LinearMap.ker N, y x ∈ LinearMap.ker N := by
    intro y hy x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hNy y hy, hx, map_zero]
  have hc'K : ∀ x ∈ LinearMap.ker N, c' x ∈ LinearMap.ker N := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hNc', hx, map_zero]
  have hfixK : ∀ x ∈ LinearMap.ker N, c' x = x := by
    set φ : LinearMap.ker N →ₗ[ZMod 2] LinearMap.ker N := (c' : E →ₗ[ZMod 2] E).restrict hc'K with hφ
    have hφapp : ∀ x : LinearMap.ker N, ((φ x : LinearMap.ker N) : E) = c' x := fun _ => rfl
    rcases eq_zero_or_eq_id_of_commute_resSub eV hKinv hK3 hfaithK (h := φ) (fun y x => Subtype.ext (by
        rw [hφapp, resSub_apply, resSub_apply, hφapp]
        exact CFSG.ASVolI.burnsideB49x_gl_apply_comm (hc' y y.2) x)) with h0 | h1
    · exfalso
      haveI : Module.Finite (ZMod 2) (LinearMap.ker N) := Module.Finite.of_finite
      haveI : Nontrivial (LinearMap.ker N) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
      obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker N)
      apply hx
      have h2 : φ x = 0 := by rw [h0]; rfl
      have h3 : c' (x : E) = 0 := congrArg Subtype.val h2
      exact Subtype.ext ((LinearEquiv.map_eq_zero_iff c').1 h3)
    · intro x hx
      exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨x, hx⟩)
  have hNK : ∀ v, N v ∈ LinearMap.ker N := fun v => by rw [← hXK]; exact ⟨v, rfl⟩
  have hsub : ∀ v, c' v - v ∈ LinearMap.ker N := fun v => by
    rw [LinearMap.mem_ker, map_sub, hNc', hfixK _ (hNK v), sub_self]
  obtain ⟨s, hs⟩ := (N.codRestrict (LinearMap.ker N) hNK).exists_rightInverse_of_surjective (by
    rw [LinearMap.range_eq_top]
    intro x
    obtain ⟨v, hv⟩ : (x : E) ∈ LinearMap.range N := by rw [hXK]; exact x.2
    exact ⟨v, Subtype.ext hv⟩)
  have hsapp : ∀ x : LinearMap.ker N, N (s x) = x := fun x =>
    congrArg Subtype.val (LinearMap.congr_fun hs x)
  set h : LinearMap.ker N →ₗ[ZMod 2] LinearMap.ker N :=
    (((c' : E →ₗ[ZMod 2] E) - LinearMap.id) ∘ₗ s).codRestrict (LinearMap.ker N) (fun x => hsub (s x))
    with hhdef
  have hhapp : ∀ x : LinearMap.ker N, ((h x : LinearMap.ker N) : E) = c' (s x) - s x := fun _ => rfl
  have hkey : ∀ v, c' v - v = h (N.codRestrict (LinearMap.ker N) hNK v) := by
    intro v
    rw [hhapp]
    have h1 : s (N.codRestrict (LinearMap.ker N) hNK v) - v ∈ LinearMap.ker N := by
      rw [LinearMap.mem_ker, map_sub, hsapp]
      exact sub_self _
    have h2 := hfixK _ h1
    rw [map_sub, sub_eq_iff_eq_add] at h2
    rw [h2]
    abel
  rcases eq_zero_or_eq_id_of_commute_resSub eV hKinv hK3 hfaithK (h := h) (fun y x => Subtype.ext (by
      have h1 : N.codRestrict (LinearMap.ker N) hNK ((y : E ≃ₗ[ZMod 2] E) (s x)) =
          resSub 𝓛 (LinearMap.ker N) hKinv y x := Subtype.ext (by
        show N ((y : E ≃ₗ[ZMod 2] E) (s x)) = (y : E ≃ₗ[ZMod 2] E) x
        rw [hNy _ y.2, hsapp])
      rw [resSub_apply, ← h1, ← hkey, hhapp, map_sub,
        CFSG.ASVolI.burnsideB49x_gl_apply_comm (hc' y y.2)])) with h0 | h1
  · left
    refine LinearEquiv.ext fun v => ?_
    have h2 := hkey v
    rw [h0, LinearMap.zero_apply, Submodule.coe_zero, sub_eq_zero] at h2
    exact h2
  · right
    refine LinearEquiv.ext fun v => ?_
    have h2 := hkey v
    rw [h1, LinearMap.id_apply] at h2
    have h3 : c' v - v = c v - v := h2
    exact sub_left_inj.1 h3

theorem le_of_offender_of_finrank_le_six [FiniteDimensional (ZMod 2) E] [IsSimpleGroup ↥𝓛]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hE : commGL 𝓛 ⊤ = ⊤) (hdim : finrank (ZMod 2) E ≤ 6) {T : Subgroup (E ≃ₗ[ZMod 2] E)}
    (hTe : CFSG.IsElementaryAbelian 2 ↥T)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹)
    (hoff : Nat.card E ≤ Nat.card ↥T * Nat.card ↥(fixGL T)) : T ≤ 𝓛 := by
  classical
  haveI : Finite E := Module.finite_of_finite (ZMod 2)
  haveI := hTe
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hTe.toIsMulCommutative.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hTsq : ∀ t : ↥T, t * t = 1 := fun t => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (t : E ≃ₗ[ZMod 2] E) t.2)
  intro t₁ ht₁T
  by_contra ht₁L
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = cHom hcen hT ⟨t₁, ht₁T⟩ := ⟨_, rfl⟩
  have hc₁1 : c₁ ≠ 1 := fun h => ht₁L ((cHom_eq_one_iff hcen hT ⟨t₁, ht₁T⟩).1 (by rw [← hc₁]; exact h))
  have hc₁c : ∀ y ∈ 𝓛, c₁ * y = y * c₁ := fun y hy => by rw [hc₁]; exact cHom_commute hcen hT _ hy
  have hc₁2 : c₁ * c₁ = 1 := by rw [hc₁, ← map_mul, hTsq, map_one]
  obtain ⟨hE6, -, hK3, hfaithK, X', hX'inv, hcompl⟩ := centralizer_structure eV hE hdim hc₁c hc₁2 hc₁1
  obtain ⟨K, hKdef⟩ : ∃ K, K = LinearMap.ker ((c₁ : E →ₗ[ZMod 2] E) - LinearMap.id) := ⟨_, rfl⟩
  rw [← hKdef] at hK3 hfaithK hcompl
  have hKinv : ∀ y ∈ 𝓛, ∀ x ∈ K, y x ∈ K := by
    intro y hy x hx
    rw [hKdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero] at hx ⊢
    rw [CFSG.ASVolI.burnsideB49x_gl_apply_comm (hc₁c y hy), hx]
  have hrange : ∀ t : ↥T, cHom hcen hT t = 1 ∨ cHom hcen hT t = c₁ := fun t =>
    eq_one_or_eq_of_centralizer eV hE hdim hc₁c hc₁2 hc₁1 (fun y hy => cHom_commute hcen hT t hy)
      (by rw [hc₁, ← map_mul, ← map_mul, hTe.toIsMulCommutative.is_comm.comm])
  have hker : ∀ t : ↥T, t ∈ (cHom hcen hT).ker ↔ (t : E ≃ₗ[ZMod 2] E) ∈ T ⊓ 𝓛 := fun t => by
    rw [MonoidHom.mem_ker, cHom_eq_one_iff, Subgroup.mem_inf]
    exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
  have hkcard : Nat.card (cHom hcen hT).ker = Nat.card ↥(T ⊓ 𝓛) := Nat.card_congr
    { toFun := fun t => ⟨t.1, (hker t.1).1 t.2⟩
      invFun := fun x => ⟨⟨x, (Subgroup.mem_inf.1 x.2).1⟩, (hker ⟨x, (Subgroup.mem_inf.1 x.2).1⟩).2 x.2⟩
      left_inv := fun t => rfl
      right_inv := fun x => rfl }
  have hrcard : Nat.card (cHom hcen hT).range ≤ 2 := by
    have hsub : ((cHom hcen hT).range : Set (E ≃ₗ[ZMod 2] E)) ⊆ {1, c₁} := by
      rintro _ ⟨t, rfl⟩
      rcases hrange t with h | h <;> simp [h]
    calc Nat.card (cHom hcen hT).range
        = ((cHom hcen hT).range : Set (E ≃ₗ[ZMod 2] E)).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, c₁} : Set (E ≃ₗ[ZMod 2] E)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  have hcardT : Nat.card ↥T ≤ 2 * Nat.card ↥(T ⊓ 𝓛) := by
    have h1 : Nat.card ↥T = Nat.card (cHom hcen hT).range * Nat.card (cHom hcen hT).ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (cHom hcen hT)).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [h1, hkcard]
    exact Nat.mul_le_mul_right _ hrcard
  obtain ⟨P, hPdef⟩ : ∃ P : E →ₗ[ZMod 2] E, P = Submodule.projection K X' hcompl := ⟨_, rfl⟩
  have hPK : ∀ v, P v ∈ K := fun v => by rw [hPdef]; exact Submodule.projection_apply_mem hcompl v
  have hPleft : ∀ v ∈ K, P v = v := fun v hv => by
    rw [hPdef]; exact Submodule.projection_apply_of_mem_left hcompl hv
  have hPzero : ∀ v, P v = 0 ↔ v ∈ X' := fun v => by
    rw [hPdef]; exact Submodule.projection_apply_eq_zero_iff hcompl
  have hPy : ∀ y ∈ 𝓛, ∀ v, P (y v) = y (P v) := by
    intro y hy v
    have h1 : v - P v ∈ X' := (hPzero _).1 (by rw [map_sub, hPleft _ (hPK v), sub_self])
    have h2 := (hPzero _).2 (hX'inv y hy _ h1)
    rw [map_sub, map_sub, hPleft _ (hKinv y hy _ (hPK v)), sub_eq_zero] at h2
    exact h2
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup (↥K ≃ₗ[ZMod 2] ↥K),
      T₀ = ((T ⊓ 𝓛).subgroupOf 𝓛).map (resSub 𝓛 K hKinv) := ⟨_, rfl⟩
  have hmemT₀ : ∀ e ∈ T₀, ∃ y : ↥𝓛, (y : E ≃ₗ[ZMod 2] E) ∈ T ∧ resSub 𝓛 K hKinv y = e := by
    intro e he
    rw [hT₀] at he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 he
    exact ⟨y, (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1, rfl⟩
  have hT₀c : ∀ e ∈ T₀, ∀ e' ∈ T₀, e * e' = e' * e := by
    intro e he e' he'
    obtain ⟨y, hy, rfl⟩ := hmemT₀ e he
    obtain ⟨y', hy', rfl⟩ := hmemT₀ e' he'
    rw [← map_mul, ← map_mul]
    exact congrArg (resSub 𝓛 K hKinv) (Subtype.ext (hTcomm _ hy _ hy'))
  have hT₀2 : ∀ e ∈ T₀, e * e = 1 := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := hmemT₀ e he
    rw [← map_mul]
    have h0 := congrArg Subtype.val (hTsq ⟨(y : E ≃ₗ[ZMod 2] E), hy⟩)
    have h1 : y * y = 1 := Subtype.ext h0
    rw [h1, map_one]
  have hT₀card : Nat.card ↥T₀ = Nat.card ↥(T ⊓ 𝓛) := by
    rw [hT₀, Subgroup.card_map_of_injective (injective_resSub hKinv hfaithK)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h16 := card_mul_card_fix_le_sixteen hK3 hT₀c hT₀2
  have hx₁ : innerPart hT ⟨t₁, ht₁T⟩ ∈ 𝓛 := innerPart_mem hT _
  have hkey : innerPart hT ⟨t₁, ht₁T⟩ * c₁ = t₁ := by rw [hc₁]; exact innerPart_mul_cHom hcen hT _
  have hX't : X' ⊓ LinearMap.ker ((t₁ : E →ₗ[ZMod 2] E) - LinearMap.id) = ⊥ := by
    have h1 := inf_ker_mul_eq_bot (hX'inv _ hx₁) (hc₁c _ hx₁).symm hc₁2
      (by rw [← hKdef]; exact hcompl.disjoint.symm.eq_bot)
    rwa [hkey] at h1
  have hfix : Nat.card ↥(fixGL T) ≤ Nat.card ↥(CFSG.ASVolI.burnsideB49x_gl_fix T₀) := by
    have hmem : ∀ v ∈ fixGL T, (⟨P v, hPK v⟩ : ↥K) ∈ CFSG.ASVolI.burnsideB49x_gl_fix T₀ := by
      intro v hv
      refine CFSG.ASVolI.burnsideB49x_gl_mem_fix.2 fun e he => ?_
      obtain ⟨y, hy, rfl⟩ := hmemT₀ e he
      apply Subtype.ext
      rw [resSub_apply]
      show (y : E ≃ₗ[ZMod 2] E) (P v) = P v
      rw [← hPy _ y.2, mem_fixGL.1 hv _ hy]
    refine Nat.card_le_card_of_injective (fun v => ⟨⟨P v.1, hPK v.1⟩, hmem v.1 v.2⟩) fun v v' h => ?_
    have h1 : P v.1 = P v'.1 :=
      congrArg (fun w : ↥(CFSG.ASVolI.burnsideB49x_gl_fix T₀) => ((w : ↥K) : E)) h
    have h2 : (v : E) - v' ∈ X' := (hPzero _).1 (by rw [map_sub, h1, sub_self])
    have h3 : (v : E) - v' ∈ X' ⊓ LinearMap.ker ((t₁ : E →ₗ[ZMod 2] E) - LinearMap.id) := by
      refine Submodule.mem_inf.2 ⟨h2, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      show t₁ ((v : E) - v') = (v : E) - v'
      rw [map_sub, mem_fixGL.1 v.2 t₁ ht₁T, mem_fixGL.1 v'.2 t₁ ht₁T]
    rw [hX't, Submodule.mem_bot, sub_eq_zero] at h3
    exact Subtype.ext h3
  have hE64 : Nat.card E = 2 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hE6]
  have h32 : Nat.card E ≤ 2 * 16 := calc
    Nat.card E ≤ Nat.card ↥T * Nat.card ↥(fixGL T) := hoff
    _ ≤ (2 * Nat.card ↥(T ⊓ 𝓛)) * Nat.card ↥(CFSG.ASVolI.burnsideB49x_gl_fix T₀) :=
        Nat.mul_le_mul hcardT hfix
    _ = 2 * (Nat.card ↥T₀ * Nat.card ↥(CFSG.ASVolI.burnsideB49x_gl_fix T₀)) := by
        rw [hT₀card, mul_assoc]
    _ ≤ 2 * 16 := Nat.mul_le_mul_left _ h16
  rw [hE64] at h32
  norm_num at h32

theorem le_of_offender_of_cen [FiniteDimensional (ZMod 2) E] [IsSimpleGroup ↥𝓛]
    (eV : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥𝓛) (hcen : Subgroup.center ↥𝓛 = ⊥)
    (hE : commGL 𝓛 ⊤ = ⊤) {T : Subgroup (E ≃ₗ[ZMod 2] E)} (hTe : CFSG.IsElementaryAbelian 2 ↥T)
    (hT : ∀ t ∈ T, ∃ x ∈ 𝓛, ∀ y ∈ 𝓛, t * y * t⁻¹ = x * y * x⁻¹)
    (hcT : ∀ t ∈ T, (∀ y ∈ 𝓛, t * y = y * t) → t = 1)
    (hoff : Nat.card E ≤ Nat.card ↥T * Nat.card ↥(fixGL T)) : T ≤ 𝓛 := by
  classical
  haveI : Finite E := Module.finite_of_finite (ZMod 2)
  haveI := hTe
  have hTsq : ∀ t : ↥T, t * t = 1 := fun t => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (t : E ≃ₗ[ZMod 2] E) t.2)
  intro t₁ ht₁T
  by_contra ht₁L
  have hrk : finrank (ZMod 2) (LinearMap.range ((t₁ : E →ₗ[ZMod 2] E) - LinearMap.id)) ≤ 2 := by
    have h1 : 2 ^ finrank (ZMod 2) E ≤ 2 ^ (2 + finrank (ZMod 2) ↥(fixGL T)) := by
      have h2 := hoff.trans (Nat.mul_le_mul_right _ (card_le_four_of_inner eV hcen hTe hT hcT))
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixGL T)), Nat.card_zmod] at h2
      calc 2 ^ finrank (ZMod 2) E ≤ 4 * 2 ^ finrank (ZMod 2) ↥(fixGL T) := h2
        _ = 2 ^ (2 + finrank (ZMod 2) ↥(fixGL T)) := by norm_num [pow_add]
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    have h4 : fixGL T ≤ LinearMap.ker ((t₁ : E →ₗ[ZMod 2] E) - LinearMap.id) := fun v hv => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact mem_fixGL.1 hv t₁ ht₁T
    have h5 := Submodule.finrank_mono h4
    have h6 := LinearMap.finrank_range_add_finrank_ker ((t₁ : E →ₗ[ZMod 2] E) - LinearMap.id)
    omega
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = cHom hcen hT ⟨t₁, ht₁T⟩ := ⟨_, rfl⟩
  have hx₁ : innerPart hT ⟨t₁, ht₁T⟩ ∈ 𝓛 := innerPart_mem hT _
  have hkey : innerPart hT ⟨t₁, ht₁T⟩ * c₁ = t₁ := by rw [hc₁]; exact innerPart_mul_cHom hcen hT _
  have hx₁2 : innerPart hT ⟨t₁, ht₁T⟩ * innerPart hT ⟨t₁, ht₁T⟩ = 1 := by
    have h1 := congrArg Subtype.val (map_mul (innerHom hcen hT) ⟨t₁, ht₁T⟩ ⟨t₁, ht₁T⟩)
    rw [hTsq, map_one] at h1
    exact h1.symm
  have hx₁1 : innerPart hT ⟨t₁, ht₁T⟩ ≠ 1 := fun h =>
    ht₁L (by rw [hcT t₁ ht₁T ((innerPart_eq_one_iff hcen hT _).1 h)]; exact one_mem 𝓛)
  have hc₁c : ∀ y ∈ 𝓛, c₁ * y = y * c₁ := fun y hy => by rw [hc₁]; exact cHom_commute hcen hT _ hy
  have hc₁2 : c₁ * c₁ = 1 := by rw [hc₁, ← map_mul, hTsq, map_one]
  have hdim : finrank (ZMod 2) E ≤ 6 := by
    have h1 := finrank_le_three_mul_twisted eV hE hx₁ hx₁2 hx₁1 hc₁c hc₁2
    rw [hkey] at h1
    omega
  exact ht₁L (le_of_offender_of_finrank_le_six eV hcen hE hdim hTe hT hoff ht₁T)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
