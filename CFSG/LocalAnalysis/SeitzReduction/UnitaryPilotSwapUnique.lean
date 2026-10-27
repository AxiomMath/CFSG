module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Gen

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem iSup_blockSU_compl_pair_eq_top (hn : 6 ≤ n) :
    ⨆ (a : Fin n) (b : Fin n) (_ : a ≠ b), blockSU h ({a, b}ᶜ : Finset (Fin n)) = ⊤ := by
  rw [eq_top_iff, ← iSup_blockSU_card_eq_top h (m := 4) le_rfl (by omega)]
  refine iSup_le fun I => iSup_le fun hI => ?_
  obtain ⟨a, b, hab, ha, hb⟩ := LinearPilot.exists_two_index_notMem (S := I) (by omega)
  exact (blockSU_mono h (subset_compl_pair_iff.2 ⟨ha, hb⟩)).trans
    (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))

end Gen

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem le_swapNeighbourJoin_of_swap (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {A : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple A)
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hcard : Nat.card L ≤ Nat.card (A ⧸ center A)) : A ≤ swapNeighbourJoin e := by
  have := h.finite
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have : Group.IsPerfect A := ⟨hq.1⟩
  set δ := LinearPilot.linearSwapDiag hA with hδdef
  have hperf : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map]
    exact LinearPilot.commutator_map_eq_of_commutator_eq δ (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hle : δ.range ≤ L :=
    CFSG.SeitzReduction.std_perfect_le hset hOut htC ht hperf
      (LinearPilot.range_linearSwapDiag_le_centralizer htt hA)
  have hrange : δ.range = L := Subgroup.eq_of_le_of_card_ge hle
    (hcard.trans (LinearPilot.card_quotient_center_le_card_range_linearSwapDiag hA))
  have hmemL : ∀ x : A, δ x ∈ L := fun x => hle ⟨x, rfl⟩
  set π : A →* unitaryPSU h n := e.toMonoidHom.comp (δ.codRestrict L hmemL) with hπ
  have hπapp : ∀ x : A, π x = e ⟨δ x, hmemL x⟩ := fun x => rfl
  have hπs : Function.Surjective π := by
    intro z
    have hz : ((e.symm z : L) : G) ∈ δ.range := hrange ▸ (e.symm z).2
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    rw [hπapp]
    have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext hx
    rw [h1, MulEquiv.apply_symm_apply]
  have hπker : π.ker ≤ center A := by
    intro x hx
    apply LinearPilot.ker_linearSwapDiag_le_center hA
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hπapp] at hx
    have h1 : (⟨δ x, hmemL x⟩ : L) = 1 := by
      apply e.injective
      rw [hx, map_one]
    exact congrArg Subtype.val h1
  set C : ∀ a b : Fin n, a ≠ b → Subgroup A := fun a b _ =>
    perfectCore ((blockSU h ({a, b}ᶜ : Finset (Fin n))).comap π) with hC
  have hCnb : ∀ (a b : Fin n) (hab : a ≠ b), (C a b hab).map A.subtype ≤ neighbourCore e hab := by
    intro a b hab
    have hperfC : ⁅(C a b hab).map A.subtype, (C a b hab).map A.subtype⁆ =
        (C a b hab).map A.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperfC ?_
    set T : Subgroup A := (unitaryRootTorus h hab).comap π with hT
    have hCT : (C a b hab).map A.subtype ≤
        centralizer ((T.map A.subtype : Subgroup G) : Set G) := by
      refine LinearPilot.le_centralizer_of_commutator_le_center (M := A) (map_subtype_le _)
        hperfC ?_
      rw [Subgroup.commutator_le]
      rintro _ ⟨c, hc, rfl⟩ _ ⟨x, hx, rfl⟩
      have hcB : π c ∈ blockSU h ({a, b}ᶜ : Finset (Fin n)) :=
        CFSG.Quasithin.perfectCore_le ((blockSU h ({a, b}ᶜ : Finset (Fin n))).comap π) hc
      have hxT : π x ∈ unitaryRootTorus h hab := hx
      have hcomm : π ⁅c, x⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_centralizer_iff.1 (blockSU_compl_le_centralizer_unitaryRootTorus h hab hcB) _
          hxT).symm
      exact ⟨⁅c, x⁆, hπker hcomm, rfl⟩
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hw
    have hyL : y ∈ L := modelToG_le e _ hy
    obtain ⟨x, hx⟩ : y ∈ δ.range := hrange ▸ hyL
    have hxT : x ∈ T := by
      obtain ⟨z, hz, hzy⟩ := (mem_modelToG e).1 hy
      change π x ∈ unitaryRootTorus h hab
      have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext (hx.trans hzy.symm)
      rw [hπapp, h1, MulEquiv.apply_symm_apply]
      exact hz
    have h1 : (x : G) * c = c * x := mem_centralizer_iff.1 (hCT ⟨c, hc, rfl⟩) _ ⟨x, hxT, rfl⟩
    have h2 : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (hA ⟨x, x.2, rfl⟩) c c.2
    rw [← hx, hδdef, LinearPilot.linearSwapDiag_apply]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [h2]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [h1]
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hgen : (⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab) = ⊤ := by
    refine LinearPilot.eq_top_of_sup_center_eq_top_of_perfect ?_
    have hi : ∀ (a b : Fin n) (hab : a ≠ b),
        (C a b hab).map π = blockSU h ({a, b}ᶜ : Finset (Fin n)) := by
      intro a b hab
      rw [hC, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (Subgroup.isPerfect_iff.1 (isQuasisimple_blockSU_compl_pair h hn hab).1)]
    have hmap : (⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab).map π = ⊤ := by
      simp only [Subgroup.map_iSup]
      simp_rw [hi]
      exact iSup_blockSU_compl_pair_eq_top h hn
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup A) = (⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab) ⊔ π.ker := by
          rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
      _ ≤ (⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab) ⊔ center A :=
          sup_le_sup_left hπker _
  intro g hg
  have hmem : (⟨g, hg⟩ : A) ∈ ⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab :=
    hgen ▸ mem_top _
  have h2 : g ∈ (⨆ (a : Fin n) (b : Fin n) (hab : a ≠ b), C a b hab).map A.subtype :=
    ⟨⟨g, hg⟩, hmem, rfl⟩
  simp only [Subgroup.map_iSup] at h2
  rw [swapNeighbourJoin_def]
  exact (iSup_mono fun a => iSup_mono fun b => iSup_mono fun hab => hCnb a b hab) h2

theorem conjugate_eq_of_swap_unitary (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = swapNeighbourJoin e)
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    (g : G) (hswap : (CFSG.conjugate G₁ g).map (MulAut.conj t).toMonoidHom =
      CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g) :
    CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) g =
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv h (by omega)
    (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega) e
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  have hA : (CFSG.conjugate G₁ g).map (MulAut.conj t).toMonoidHom ≤
      centralizer (CFSG.conjugate G₁ g : Set G) := by
    rw [hswap]
    exact LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ g ⧸ center (CFSG.conjugate G₁ g)) := by
    rw [← Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ g).toEquiv, hcard₁]
  have hAle := le_swapNeighbourJoin_of_swap hset.standardSetting hOut e hn htC ht
    (LinearPilot.isQuasisimple_conjugate hq g) hA hcardA
  rw [← hsup] at hAle
  have htG₀ : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have hBle : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [← hswap]
    calc (CFSG.conjugate G₁ g).map (MulAut.conj t).toMonoidHom
        ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
          map_mono hAle
      _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
          F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
  have hle : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) g ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [CFSG.conjugate, Subgroup.map_sup]
    exact sup_le hAle hBle
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge

end Swap

section Center

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {t z : G} (ht : orderOf t = 2) (hz : z ∈ zpowers t) :
    z = 1 ∨ z = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, hk, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, hk, zpow_one]

theorem odd_card_center_of_swapFactors (hZL : center L = ⊥) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    Odd (Nat.card (center G₁)) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G₁) 2 h2
  set z' : G := ((z : G₁) : G) with hz'
  have hzG₁ : z' ∈ G₁ := (z : G₁).2
  have hzc : ∀ x ∈ G₁, z' * x = x * z' := fun x hx =>
    congrArg Subtype.val ((mem_center_iff.1 z.2 ⟨x, hx⟩).symm)
  have hzo : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzz : z' * z' = 1 := by rw [← sq, ← hzo, pow_orderOf_eq_one]
  have hzc' : ∀ x ∈ G₁, z' * (t * x * t⁻¹) = (t * x * t⁻¹) * z' := fun x hx =>
    mem_centralizer_iff.1 (h₁₂ ⟨x, hx, rfl⟩) z' hzG₁
  have hzL : z' ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    calc x * (t * x * t⁻¹) * z' = x * ((t * x * t⁻¹) * z') := by group
      _ = x * (z' * (t * x * t⁻¹)) := by rw [hzc' x hx]
      _ = (x * z') * (t * x * t⁻¹) := by group
      _ = (z' * x) * (t * x * t⁻¹) := by rw [hzc x hx]
      _ = z' * (x * (t * x * t⁻¹)) := by group
  have hδz : z' * (t * z' * t⁻¹) = 1 := by
    have hmem : (⟨_, hδ z' hzG₁⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro w
      apply Subtype.ext
      obtain ⟨x, hx, hxw⟩ := hsurj w w.2
      simp only [Subgroup.coe_mul]
      rw [← hxw]
      have hxz : x * z' = z' * x := (hzc x hx).symm
      have htxz : (t * x * t⁻¹) * (t * z' * t⁻¹) = (t * z' * t⁻¹) * (t * x * t⁻¹) := by
        calc (t * x * t⁻¹) * (t * z' * t⁻¹) = t * (x * z') * t⁻¹ := by group
          _ = t * (z' * x) * t⁻¹ := by rw [hxz]
          _ = (t * z' * t⁻¹) * (t * x * t⁻¹) := by group
      have hxt : x * (t * z' * t⁻¹) = (t * z' * t⁻¹) * x :=
        mem_centralizer_iff.1 (h₁₂ ⟨z', hzG₁, rfl⟩) x hx
      calc x * (t * x * t⁻¹) * (z' * (t * z' * t⁻¹))
          = x * ((t * x * t⁻¹) * z') * (t * z' * t⁻¹) := by group
        _ = x * (z' * (t * x * t⁻¹)) * (t * z' * t⁻¹) := by rw [hzc' x hx]
        _ = (x * z') * ((t * x * t⁻¹) * (t * z' * t⁻¹)) := by group
        _ = (z' * x) * ((t * z' * t⁻¹) * (t * x * t⁻¹)) := by rw [hxz, htxz]
        _ = z' * (x * (t * z' * t⁻¹)) * (t * x * t⁻¹) := by group
        _ = z' * ((t * z' * t⁻¹) * x) * (t * x * t⁻¹) := by rw [hxt]
        _ = z' * (t * z' * t⁻¹) * (x * (t * x * t⁻¹)) := by group
    rw [hZL, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hzt : z' ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : t * z' * t⁻¹ = z' := by
      calc t * z' * t⁻¹ = z' * (z' * (t * z' * t⁻¹)) := by
            rw [← mul_assoc, hzz, one_mul]
        _ = z' := by rw [hδz, mul_one]
    calc z' * t = (t * z' * t⁻¹) * t := by rw [h1]
      _ = t * z' := by group
  have hmem : z' ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hzL, hzt⟩
  rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
  · rw [h1, orderOf_one] at hzo
    omega
  ·
    obtain ⟨hp, hb, -⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
    apply hb
    have hab : G₁ ≤ centralizer (G₁ : Set G) := by
      intro x hx
      have hx' : t * x * t⁻¹ = x := by
        calc t * x * t⁻¹ = (z' * x) * t⁻¹ := by rw [← h1]
          _ = (x * z') * t⁻¹ := by rw [hzc x hx]
          _ = x := by rw [h1, mul_inv_cancel_right]
      rw [← hx']
      exact h₁₂ ⟨x, hx, rfl⟩
    rw [← hp, commutator_eq_bot_iff_le_centralizer.2 hab]

end Center

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem unique_of_swapFactors_unitary (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = swapNeighbourJoin e)
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    (hnorm : ∀ g : G, t ∈ normalizer (CFSG.conjugate G₁ g : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ g : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g : Set G) →
      False) :
    UnitarySwapRowUnique e t := by
  intro g₀ hg₀
  rw [← hsup] at hg₀ ⊢
  revert g₀
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv h (by omega)
    (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega) e
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  refine F4Pilot.unique_of_forall_conjugate_eq fun g htM => ?_
  have hM : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) g =
      CFSG.conjugate G₁ g ⊔ CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := LinearPilot.isQuasisimple_conjugate hq g
  have hqB := LinearPilot.isQuasisimple_conjugate (LinearPilot.isQuasisimple_map_conj hq t) g
  have hAB := LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with hAA | hswap
  ·
    rcases F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    · exfalso
      have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) g t
      have hAconj : (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g).map
          (MulAut.conj (g⁻¹ * t * g)⁻¹).toMonoidHom = CFSG.conjugate G₁ g :=
        F4Pilot.map_conj_eq_of_map_conj_inv_eq (by rw [inv_inv]; exact hBconj)
      have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ g) := by
        rw [← hcard₁, Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ g).toEquiv,
          Subgroup.card_eq_card_quotient_mul_card_subgroup (center (CFSG.conjugate G₁ g))]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      have hcardB : Nat.card L ≤
          Nat.card (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g) := by
        rw [← hBconj, Subgroup.card_map_of_injective (MulAut.conj _).injective]
        exact hcardA
      refine hnorm g (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA)
        (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB) ?_ ?_
      · exact LinearPilot.not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpA hcardA
          _ (hBconj ▸ hAB)
      · exact LinearPilot.not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpB hcardB
          _ (hAconj ▸ hBA)
    ·
      exfalso
      have hAB' : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) g = CFSG.conjugate G₁ g :=
        F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  · exact conjugate_eq_of_swap_unitary hset e hn htC ht hq h₁₂ hsup hδ hsurj g hswap

theorem unique_of_swapFactors_of_factorNormalAt (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hloc : ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A → Odd (Nat.card (center A)) →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
      ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
        t ∈ normalizer (A : Set G) →
        t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        t ∉ centralizer (A : Set G) →
        t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = swapNeighbourJoin e)
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    UnitarySwapRowUnique e t := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hodd := odd_card_center_of_swapFactors hset.center_eq_bot ht hKt hq h₁₂ hδ hsurj
  refine unique_of_swapFactors_unitary hset e hn htC ht hq h₁₂ hsup hδ hsurj
    fun g htA htB hnA hnB => ?_
  have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) g t
  have hoddA : Odd (Nat.card (center (CFSG.conjugate G₁ g))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr (LinearPilot.conjugateEquiv G₁ g)).toEquiv]
    exact hodd
  refine hloc (CFSG.conjugate G₁ g) (LinearPilot.isQuasisimple_conjugate hq g) hoddA
    (LinearPilot.exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj g) (g⁻¹ * t * g) ?_
    htA ?_ hnA ?_
  · rw [hBconj]
    exact LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ g
  · rw [hBconj]
    exact htB
  · rw [hBconj]
    exact hnB

end Unique

end CFSG.SeitzReduction.UnitaryPilot
