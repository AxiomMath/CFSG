module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityDerived
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open scoped commutatorElement

structure NonOrthSocle (X : Type) [Group X] (S : Subgroup X) : Prop where
  normal : S.Normal
  simple : IsSimpleGroup S
  index : S.index = 2
  centralizer : Subgroup.centralizer (S : Set X) = ⊥
  outer : ¬ IsPGroup 2 (Outer S)

namespace NonOrthSocle

variable {X : Type} [Group X] {S : Subgroup X}

theorem ne_bot (h : NonOrthSocle X S) : S ≠ ⊥ := by
  have := h.simple
  exact (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance

theorem ne_top (h : NonOrthSocle X S) : S ≠ ⊤ := by
  intro ht
  have := h.index
  rw [ht, Subgroup.index_top] at this
  exact absurd this (by norm_num)

theorem not_comm (h : NonOrthSocle X S) : ¬ ∀ a b : S, a * b = b * a := by
  intro hc
  apply h.ne_bot
  rw [eq_bot_iff, ← h.centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hc ⟨y, hy⟩ ⟨s, hs⟩)

theorem not_isSimpleGroup (h : NonOrthSocle X S) : ¬ IsSimpleGroup X := by
  intro hX
  have := h.normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hb | ht
  · exact h.ne_bot hb
  · exact h.ne_top ht

theorem commutator_le (h : NonOrthSocle X S) : commutator X ≤ S := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have hi := h.index
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hi,
    Subgroup.mul_mem_iff_of_index_two hi, Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff,
    inv_mem_iff]
  tauto

theorem not_isPerfect (h : NonOrthSocle X S) : commutator X ≠ ⊤ := fun ht =>
  h.ne_top (top_le_iff.mp (ht ▸ h.commutator_le))

theorem commutator_eq (h : NonOrthSocle X S) : commutator X = S := by
  have := h.simple
  have := h.normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((commutator X).subgroupOf S) with hb | ht
  · exfalso
    apply h.not_comm
    intro a b
    have hab : ⁅(a : X), (b : X)⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hmem : (⟨_, h.commutator_le hab⟩ : S) ∈ (commutator X).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr hab
    rw [hb, Subgroup.mem_bot] at hmem
    have h1 : ⁅(a : X), (b : X)⁆ = 1 := congrArg Subtype.val hmem
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · refine le_antisymm h.commutator_le fun s hs => ?_
    have hmem : (⟨s, hs⟩ : S) ∈ (commutator X).subgroupOf S := by
      rw [ht]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

theorem not_isSolvable (h : NonOrthSocle X S) : ¬ Group.IsSolvable X := by
  intro hX
  have := h.simple
  exact h.not_comm (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

theorem not_card_outer_dvd (h : NonOrthSocle X S) (k : ℕ) : ¬ Nat.card (Outer S) ∣ 2 ^ k :=
  fun hk => h.outer (IsPGroup.of_card_dvd_pow hk)

theorem le_of_normalizes (h : NonOrthSocle X S) {A : Subgroup X} (hA : A ≠ ⊥)
    (hSA : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) : S ≤ A := by
  have := h.simple
  have hN : (A.subgroupOf S).Normal :=
    ⟨fun a ha s => Subgroup.mem_subgroupOf.mpr (by
      simpa using hSA s s.2 a (Subgroup.mem_subgroupOf.mp ha))⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf S) with hb | ht
  · exfalso
    apply hA
    rw [eq_bot_iff, ← h.centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : s * a * s⁻¹ * a⁻¹ ∈ A := mul_mem (hSA s hs a ha) (inv_mem ha)
    have h2 : s * a * s⁻¹ * a⁻¹ ∈ S := by
      have := mul_mem hs (h.normal.conj_mem s⁻¹ (inv_mem hs) a)
      simpa [mul_assoc] using this
    have h3 : (⟨_, h2⟩ : S) ∈ A.subgroupOf S := Subgroup.mem_subgroupOf.mpr h1
    rw [hb, Subgroup.mem_bot] at h3
    have h4 : s * a * s⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h3
    calc s * a = (s * a * s⁻¹ * a⁻¹) * (a * s) := by group
      _ = a * s := by rw [h4, one_mul]
  · intro s hs
    have hmem : (⟨s, hs⟩ : S) ∈ A.subgroupOf S := by
      rw [ht]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

theorem false_of_wreathSym {L : Type} [Group L] [Nontrivial L] {m : ℕ}
    {S : Subgroup (WreathSym L m)} (h : NonOrthSocle _ S) {i j : Fin m} (hij : i ≠ j) : False := by
  let B : Subgroup (WreathSym L m) := (SemidirectProduct.inl).range
  let C : Fin m → Subgroup (WreathSym L m) := fun k =>
    ((SemidirectProduct.inl).comp (MonoidHom.mulSingle (fun _ => L) k)).range
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  have hsingle : ∀ k, Pi.mulSingle k x ≠ (1 : Fin m → L) := fun k hk =>
    hx (by simpa using congrFun hk k)
  have hBn : B.Normal := by
    change (SemidirectProduct.inl).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hB : S ≤ B := by
    refine h.le_of_normalizes ?_ fun s _ a ha => hBn.conj_mem a ha s
    intro hb
    have hmem : SemidirectProduct.inl (Pi.mulSingle i x) ∈ B := ⟨_, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hsingle i (SemidirectProduct.inl_injective (by rw [hmem, map_one]))
  have hC : ∀ k, S ≤ C k := by
    intro k
    refine h.le_of_normalizes ?_ ?_
    · intro hb
      have hmem : SemidirectProduct.inl (Pi.mulSingle k x) ∈ C k := ⟨x, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      exact hsingle k (SemidirectProduct.inl_injective (by rw [hmem, map_one]))
    · rintro s hs a ⟨y, rfl⟩
      obtain ⟨f, rfl⟩ := hB hs
      refine ⟨f k * y * (f k)⁻¹, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply, ← map_inv,
        ← map_mul]
      congr 1
      ext l
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Pi.mulSingle_eq_of_ne hl]
  have hbot : S ≤ ⊥ := by
    intro s hs
    obtain ⟨y, hy⟩ := hC i hs
    obtain ⟨z, hz⟩ := hC j hs
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply] at hy hz
    have hyz : Pi.mulSingle i y = (Pi.mulSingle j z : Fin m → L) :=
      SemidirectProduct.inl_injective (hy.trans hz.symm)
    have hy1 : y = 1 := by
      have := congrFun hyz i
      rwa [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at this
    rw [Subgroup.mem_bot, ← hy, hy1, Pi.mulSingle_one, map_one]
  exact h.ne_bot (le_bot_iff.mp hbot)

theorem false_of_perm {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} (h : NonOrthSocle _ S) :
    False := by
  by_cases hn : n ≤ 4
  · exact h.not_isSolvable (Equiv.Perm.isSolvable (by simpa using hn))
  · have hA := Equiv.Perm.eq_alternatingGroup_of_index_eq_two h.index
    apply h.not_card_outer_dvd 2
    rw [Nat.card_congr (equivalence (MulEquiv.subgroupCongr hA)).toEquiv]
    exact (CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n (by omega)).trans
      (by norm_num)

end NonOrthSocle

theorem nonempty_mulEquiv_of_surjective_of_comm_ker {D A B : Type*} [Group D] [Group A] [Group B]
    [IsSimpleGroup A] [IsSimpleGroup B] (α : D →* A) (σ : D →* B)
    (hα : Function.Surjective α) (hσ : Function.Surjective σ)
    (hcomm : ∀ x ∈ α.ker, ∀ y ∈ α.ker, x * y = y * x) (hB : ¬ ∀ a b : B, a * b = b * a) :
    Nonempty (A ≃* B) := by
  have h1 : α.ker ≤ σ.ker := by
    have := (MonoidHom.normal_ker α).map σ hσ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (α.ker.map σ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      apply hB
      intro a b
      have ha : a ∈ α.ker.map σ := ht ▸ Subgroup.mem_top a
      have hb : b ∈ α.ker.map σ := ht ▸ Subgroup.mem_top b
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have h2 : σ.ker ≤ α.ker := by
    have := (MonoidHom.normal_ker σ).map α hα
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (σ.ker.map α) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      obtain ⟨b, hb1⟩ := exists_ne (1 : B)
      obtain ⟨d, rfl⟩ := hσ b
      apply hb1
      have hd : α d ∈ σ.ker.map α := ht ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkd⟩ := hd
      have hk' : k⁻¹ * d ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkd, inv_mul_cancel]
      have h3 := h1 hk'
      rwa [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul] at h3
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (le_antisymm h1 h2)).trans
      (QuotientGroup.quotientKerEquivOfSurjective σ hσ))⟩

namespace ExtSetting

variable {G : Type} [Group G] [Finite G] {t : G} {M : Subgroup G} [M.Normal]

theorem nonOrthSocle (h : ExtSetting G t M) {X : Type} [Group X]
    (φ : X ≃* ↥(M ⊔ Subgroup.zpowers t)) : NonOrthSocle X (derivedSeries X 1) where
  normal := derivedSeries_normal X 1
  simple := h.isSimpleGroup_derivedSeries_one φ
  index := h.index_derivedSeries_one φ
  centralizer := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : ((φ x : ↥(M ⊔ Subgroup.zpowers t)) : G) ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro m hm
      obtain ⟨y, hy⟩ := φ.surjective ⟨m, Subgroup.mem_sup_left hm⟩
      have hyD : y ∈ derivedSeries X 1 := by
        rw [h.mem_derivedSeries_one_iff φ, hy]
        exact hm
      have h1 := congrArg (fun w => ((φ w : ↥(M ⊔ Subgroup.zpowers t)) : G)) (hx y hyD)
      simpa [hy] using h1
    rw [h.centralizer, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    apply φ.injective
    rw [map_one]
    exact Subtype.ext hx'
  outer := fun hP => h.not_isPGroup_outer (hP.of_equiv (equivalence (h.derivedEquiv φ)))

end ExtSetting

end CFSG.OddTranspositions.PartFour
