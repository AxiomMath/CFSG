module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open Subgroup CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br
open scoped MatrixGroups

section Group

variable {G : Type} [Group G] {L L₂ : Subgroup G}

namespace IsPair

variable (hP : IsPair L L₂)
include hP

theorem mem_normalizer_of_map_eq {x : G} (h : L.map (MulAut.conj x).toMonoidHom = L) :
    x ∈ normalizer (L : Set G) := by
  by_contra hx
  exact hP.ne (h.symm.trans (hP.map_conj_of_not_mem hx).1)

theorem inv_not_mem {g : G} (hg : g ∉ normalizer (L : Set G)) : g⁻¹ ∉ normalizer (L : Set G) :=
  fun h => hg (by simpa using inv_mem h)

theorem normalizer_normal : (normalizer (L : Set G)).Normal := by
  refine ⟨fun x hx g => hP.mem_normalizer_of_map_eq ?_⟩
  have hx' := hP.map_conj_of_mem hx
  rw [map_conj_mul, map_conj_mul]
  by_cases hg : g ∈ normalizer (L : Set G)
  · rw [(hP.map_conj_of_mem (inv_mem hg)).1, hx'.1, (hP.map_conj_of_mem hg).1]
  · rw [(hP.map_conj_of_not_mem (hP.inv_not_mem hg)).1, hx'.2, (hP.map_conj_of_not_mem hg).2]

theorem inv_mul_mem {g h : G} (hg : g ∉ normalizer (L : Set G))
    (hh : h ∉ normalizer (L : Set G)) : g⁻¹ * h ∈ normalizer (L : Set G) := by
  refine hP.mem_normalizer_of_map_eq ?_
  rw [map_conj_mul, (hP.map_conj_of_not_mem hh).1, (hP.map_conj_of_not_mem (hP.inv_not_mem hg)).2]

end IsPair

end Group

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

theorem IsPair.apply_mem_sup_map (hP : IsPair L L₂) {U : Submodule (ZMod 2) V}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (normalizer (L : Set G)) U) {g₀ : G}
    (hg₀ : g₀ ∉ normalizer (L : Set G)) (g : G) {v : V} (hv : v ∈ U ⊔ U.map (ρ g₀)) :
    ρ g v ∈ U ⊔ U.map (ρ g₀) := by
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, ← Module.End.mul_apply, ← map_mul]
  have hmap : ∀ x ∈ normalizer (L : Set G), ∀ u ∈ U, ρ (g₀ * x) u ∈ U.map (ρ g₀) :=
    fun x hx u hu => ⟨ρ x u, hU x hx u hu, by rw [map_mul, Module.End.mul_apply]⟩
  by_cases hg : g ∈ normalizer (L : Set G)
  · have hgg₀ : g * g₀ ∉ normalizer (L : Set G) := fun h =>
      hg₀ (by simpa using mul_mem (inv_mem hg) h)
    have := hmap _ (hP.inv_mul_mem hg₀ hgg₀) b hb
    rw [mul_inv_cancel_left] at this
    exact add_mem (Submodule.mem_sup_left (hU g hg a ha)) (Submodule.mem_sup_right this)
  · have h2 : g * g₀ ∈ normalizer (L : Set G) := by
      simpa using hP.inv_mul_mem (hP.inv_not_mem hg) hg₀
    have := hmap _ (hP.inv_mul_mem hg₀ hg) a ha
    rw [mul_inv_cancel_left] at this
    exact add_mem (Submodule.mem_sup_right this) (Submodule.mem_sup_left (hU _ h2 b hb))

theorem IsPair.commOn_le_fixSub [Finite G] [IsSimpleGroup ↥L] (hP : IsPair L L₂)
    (hsup : fixSub ρ L ⊔ fixSub ρ L₂ = ⊤) : commOn ρ L ⊤ ≤ fixSub ρ L₂ := by
  rw [Replacement.commOn_le_iff]
  rintro l hl v -
  have hv : v ∈ fixSub ρ L ⊔ fixSub ρ L₂ := hsup ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 : ρ l (a + b) - (a + b) = ρ l b - b := by
    rw [map_add, ha l hl, add_sub_add_left_eq_sub]
  rw [h1]
  refine mem_fixSub.mpr fun k hk => ?_
  rw [map_sub, hb k hk, ← Module.End.mul_apply, ← map_mul, ← hP.commute hl hk, map_mul,
    Module.End.mul_apply, hb k hk]

theorem IsPair.isMinInv_commOn (hP : IsPair L L₂) (hirr : ρ.IsIrreducible)
    (hfix : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥) (hle : commOn ρ L ⊤ ≤ fixSub ρ L₂)
    (hnt : ∃ l ∈ L, ρ l ≠ 1) : IsMinInv ρ (normalizer (L : Set G)) (commOn ρ L ⊤) := by
  refine ⟨isInvariant_commOn_top le_rfl, ?_, fun C hCW hC hC0 => ?_⟩
  · obtain ⟨l, hl, hne⟩ := hnt
    obtain ⟨v, hv⟩ : ∃ v, ρ l v ≠ v := by
      by_contra hc
      push Not at hc
      exact hne (LinearMap.ext hc)
    intro h0
    apply hv
    have := Replacement.mem_commOn_of (ρ := ρ) hl (Submodule.mem_top (x := v))
    rwa [h0, Submodule.mem_bot, sub_eq_zero] at this
  · obtain ⟨g₀, hg₀⟩ := hP.exists_not_mem_normalizer
    have htop : C ⊔ C.map (ρ g₀) = ⊤ := by
      rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 _
          (fun g v hv => hP.apply_mem_sup_map hC hg₀ g hv) with h | h
      · exact absurd (eq_bot_iff.mpr (le_sup_left.trans h.le)) hC0
      · exact h
    refine le_antisymm hCW fun w hw => ?_
    have hw' : w ∈ C ⊔ C.map (ρ g₀) := htop ▸ Submodule.mem_top
    obtain ⟨c, hc, _, ⟨d, hd, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw'
    have hd0 : ρ g₀ d = 0 := by
      have h1 : ρ g₀ d ∈ fixSub ρ L := by
        have := apply_mem_fixSub_map ρ (hle (hCW hd)) g₀
        rwa [(hP.map_conj_of_not_mem hg₀).2] at this
      have h2 : ρ g₀ d ∈ fixSub ρ L₂ := by
        have : ρ g₀ d = (c + ρ g₀ d) - c := by abel
        rw [this]
        exact sub_mem (hle hw) (hle (hCW hc))
      have : ρ g₀ d ∈ fixSub ρ L ⊓ fixSub ρ L₂ := ⟨h1, h2⟩
      rwa [hfix, Submodule.mem_bot] at this
    rw [hd0, add_zero]
    exact hc

end Rep

theorem case_fixSub_ne_bot {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L L₂ : Subgroup G} (hP : IsPair L L₂) {F : Type} [Field F]
    [Fintype F] [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hL2 : IsL2 ↥L n) {t : G} (ht : t * t = 1) (ht1 : t ≠ 1)
    (htd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1)
    (hA : fixSub ρ L₂ ≠ ⊥) :
    (∀ g : G, g ∉ normalizer (L : Set G) →
        commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
      (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
        (∃ k : ℕ, n = 2 * k ∧
          (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
            SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
        (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)) := by
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup SL(2, F) := P22y.isSimpleGroup_sl2 h4
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hnt : ∃ l ∈ L, ρ l ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : SL(2, F))
    refine ⟨(e.symm g : G), (e.symm g).2, fun h => hg ?_⟩
    have h2 : e.symm g = 1 := Subtype.ext (hρ (h.trans (map_one ρ).symm))
    simpa using congrArg e h2
  have hfix := hP.fixSub_inf_eq_bot hirr hnt
  have hle := hP.commOn_le_fixSub (hP.fixSub_sup_eq_top hirr hA)
  have hmin := hP.isMinInv_commOn hirr hfix hle hnt
  have hWL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) := fun l hl => hmin.1 l (Subgroup.le_normalizer hl)
  have hmov : ∃ l ∈ L, ∃ a ∈ commOn ρ L ⊤, ρ l a ≠ a := by
    by_contra hc
    push Not at hc
    apply hmin.2.1
    rw [eq_bot_iff, ← hfix]
    exact fun w hw => ⟨fun l hl => hc l hl w hw, hle hw⟩
  have hdim := two_mul_le_finrank_of_moves ρ e (by omega) hFn hWL hmov
  have htN : t ∈ normalizer (L : Set G) := by
    by_contra htN
    have h1 : ∀ y ∈ commOn ρ L ⊤, ρ t y = y → y = 0 := by
      intro y hy hty
      have h2 := apply_mem_fixSub_map ρ (hle hy) t
      rw [(hP.map_conj_of_not_mem htN).2, hty] at h2
      have : y ∈ fixSub ρ L ⊓ fixSub ρ L₂ := ⟨h2, hle hy⟩
      rwa [hfix] at this
    have := finrank_le_disp ρ h1
    omega
  have hX : (∃ l ∈ L, t * l ≠ l * t) ∨ ∃ l ∈ L₂, t * l ≠ l * t := by
    by_contra hc
    push Not at hc
    have hcen : L ⊔ L₂ ≤ centralizer ({t} : Set G) := sup_le
      (fun l hl => mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hc.1 l hl)
      (fun l hl => mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hc.2 l hl)
    obtain ⟨Y, hY, hY0, hYd⟩ := exists_le_disp_of_commute ρ hρ ht1 (L := L ⊔ L₂)
      fun l hl => mem_centralizer_iff.mp (hcen hl) t (Set.mem_singleton t)
    have := hP.two_mul_le_finrank e (by omega) hFn hfix hY hY0
    omega
  obtain ⟨t', htN', ht', htd', hl₀⟩ : ∃ t' ∈ normalizer (L : Set G), t' * t' = 1 ∧
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t'}) ≤ n + 1 ∧
      ∃ l ∈ L, t' * l ≠ l * t' := by
    rcases hX with hX | ⟨l, hl, hne⟩
    · exact ⟨t, htN, ht, htd, hX⟩
    · obtain ⟨g₀, hg₀⟩ := hP.exists_not_mem_normalizer
      refine ⟨g₀ * t * g₀⁻¹, hP.normalizer_normal.conj_mem t htN g₀, ?_, ?_,
        g₀ * l * g₀⁻¹, hP.symm.conj_mem_of_not_mem (fun h => hg₀ (hP.mem_normalizer_iff.mp h)) hl,
        fun h => hne ?_⟩
      · calc g₀ * t * g₀⁻¹ * (g₀ * t * g₀⁻¹) = g₀ * (t * t) * g₀⁻¹ := by group
          _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
      · rw [finrank_repFixedSpace_conj ρ g₀ t]
        exact htd
      · calc t * l = g₀⁻¹ * (g₀ * t * g₀⁻¹ * (g₀ * l * g₀⁻¹)) * g₀ := by group
          _ = g₀⁻¹ * (g₀ * l * g₀⁻¹ * (g₀ * t * g₀⁻¹)) * g₀ := by rw [h]
          _ = l * t := by group
  refine ⟨fun g hg => by rw [(hP.map_conj_of_not_mem hg).1]; exact hle, ?_⟩
  rcases nat_or_orth_or_eight_or_split_sub ρ (Subgroup.le_normalizer) le_rfl hmin hWL hmov e hn
      hF htN' ht' hl₀ htd' with
    ⟨hLirr, hnat | ⟨s, hs, hsF, ho⟩ | ⟨h3, h8⟩⟩ |
      ⟨s, hs, hsF, hall, U, C, hU, hC, hUC, hinf, hU0, hC0⟩
  · exact Or.inl (natL2_of_isNaturalModule ρ hFn e hWL (restr ρ hWL) (fun _ _ => rfl) hnat)
  · exact Or.inr (Or.inl ⟨s, hs, Or.inl (secSum_one (natOmegaMinus4_of_isOrthModule ρ (by omega)
      hsF e hWL (restr ρ hWL) (fun _ _ => rfl) ho))⟩)
  · subst h3
    exact Or.inr (Or.inr ⟨rfl, hL2, secIrr_of_card ρ hWL
      (by rw [K147L2Fac.natCard_eq_two_pow, h8]) hLirr⟩)
  · have hUA : U ≤ commOn ρ L ⊤ := le_sup_left.trans hUC.le
    have hCA : C ≤ commOn ρ L ⊤ := le_sup_right.trans hUC.le
    obtain ⟨-, hoU⟩ := hall U hUA hU hU0
      fun h => hC0 (eq_bot_iff.mpr ((le_inf (hCA.trans h.ge) le_rfl).trans hinf.le))
    obtain ⟨-, hoC⟩ := hall C hCA hC hC0
      fun h => hU0 (eq_bot_iff.mpr ((le_inf le_rfl (hUA.trans h.ge)).trans hinf.le))
    exact Or.inr (Or.inl ⟨s, hs, Or.inr (secSum_two
      (natOmegaMinus4_of_isOrthModule ρ (by omega) hsF e hU (restr ρ hU) (fun _ _ => rfl) hoU)
      (natOmegaMinus4_of_isOrthModule ρ (by omega) hsF e hC (restr ρ hC) (fun _ _ => rfl) hoC)
      hUC hinf)⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
