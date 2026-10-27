module

public import CFSG.Quasithin.EmptyFaithful.SzF53B1B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F53B1

section Pure

variable {G : Type*} [Group G]

theorem commutator_mem_of_quotient {X Q : Subgroup G}
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) {a a' b b' : G} (ha : a ∈ X) (ha' : a' ∈ X)
    (hb : b ∈ X) (hb' : b' ∈ X) (hQa : a⁻¹ * a' ∈ Q) (hQb : b⁻¹ * b' ∈ Q)
    (hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ Q) : a * b * a⁻¹ * b⁻¹ ∈ Q := by
  have hn : (Q.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQn
  have e1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥X) : ↥X ⧸ Q.subgroupOf X) =
      QuotientGroup.mk ⟨a', ha'⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hQa
  have e2 : (QuotientGroup.mk (⟨b, hb⟩ : ↥X) : ↥X ⧸ Q.subgroupOf X) =
      QuotientGroup.mk ⟨b', hb'⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hQb
  have e3 : (QuotientGroup.mk ((⟨a', ha'⟩ : ↥X) * ⟨b', hb'⟩ * (⟨a', ha'⟩ : ↥X)⁻¹ *
      (⟨b', hb'⟩ : ↥X)⁻¹) : ↥X ⧸ Q.subgroupOf X) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hc
  have e4 : (QuotientGroup.mk ((⟨a, ha⟩ : ↥X) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥X)⁻¹ *
      (⟨b, hb⟩ : ↥X)⁻¹) : ↥X ⧸ Q.subgroupOf X) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at e3 ⊢
    rw [e1, e2]
    exact e3
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at e4
  exact e4

theorem relIndex_conjSub (g : G) (N K : Subgroup G) :
    (conjSub g N).relIndex (conjSub g K) = N.relIndex K :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) N K
    (MulEquiv.injective (MulAut.conj g))

end Pure

section Hyp

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B1Hyp

theorem Ha_le_normalizer_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) :
    VZ S H ⊓ pCoreOf 2 M ≤ Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
  fun _ hg => h.Qb_le_normalizer_Qa2 hx hg.2

theorem Ha2_le_normalizer_Qa (h : B1Hyp H M S) {x : G} :
    conjSub x (VZ S H) ⊓ pCoreOf 2 M ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  fun _ hg => h.Qb_le_normalizer_Qa hg.2

theorem relIndex_R_Ha (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) {c : ℕ}
    (hc : Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) = c) :
    (VZ S H ⊓ conjSub x (VZ S H)).relIndex (VZ S H ⊓ pCoreOf 2 M) * c = 8 := by
  have h1 := Subgroup.relIndex_mul_card (VZ S H ⊓ conjSub x (VZ S H)) (VZ S H ⊓ pCoreOf 2 M)
  rw [inf_eq_left.mpr (h.R_le_Ha hx hxH), hc, h.card_Ha] at h1
  exact h1

theorem relIndex_R_Ha2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) {c : ℕ}
    (hc : Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) = c) :
    (VZ S H ⊓ conjSub x (VZ S H)).relIndex (conjSub x (VZ S H) ⊓ pCoreOf 2 M) * c = 8 := by
  have h1 := Subgroup.relIndex_mul_card (VZ S H ⊓ conjSub x (VZ S H))
    (conjSub x (VZ S H) ⊓ pCoreOf 2 M)
  rw [inf_eq_left.mpr (h.R_le_Ha2 hx hxH), hc, h.card_Ha2 hx] at h1
  exact h1

theorem relIndex_Qa2_Ha (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (conjSub x (pCoreOf 2 H)).relIndex ((VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H)) =
      (VZ S H ⊓ conjSub x (VZ S H)).relIndex (VZ S H ⊓ pCoreOf 2 M) := by
  rw [F1.relIndex_sup_eq_of_le_normalizer (h.Ha_le_normalizer_Qa2 hx),
    ← Subgroup.inf_relIndex_right, inf_comm, h.inf_Ha_Qa2 hx hxH]

theorem relIndex_Qa_Ha2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (pCoreOf 2 H).relIndex ((conjSub x (VZ S H) ⊓ pCoreOf 2 M) ⊔ pCoreOf 2 H) =
      (VZ S H ⊓ conjSub x (VZ S H)).relIndex (conjSub x (VZ S H) ⊓ pCoreOf 2 M) := by
  rw [F1.relIndex_sup_eq_of_le_normalizer h.Ha2_le_normalizer_Qa, ← Subgroup.inf_relIndex_right,
    inf_comm, h.inf_Ha2_Qa hx hxH]

theorem R_eq_commutator (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H)
    (h4 : Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) = 4) :
    VZ S H ⊓ conjSub x (VZ S H) = ⁅VZ S H ⊓ pCoreOf 2 M, conjSub x (VZ S H)⁆ ∧
      VZ S H ⊓ conjSub x (VZ S H) = ⁅conjSub x (VZ S H) ⊓ pCoreOf 2 M, VZ S H⁆ := by
  have hRn := h.R_normal hx hxH
  constructor
  · have hz2 := h.zfacts.conj x
    have hYS : VZ S H ⊓ pCoreOf 2 M ≤ conjSub x S :=
      inf_le_right.trans (h.Qb_le_conjSub_S hx)
    have hQ1 : pCoreOf 2 M ≤ Subgroup.normalizer
        ((conjSub x (pCoreOf 2 H) ⊔ (VZ S H ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (h.Qb_le_normalizer_Qa2 hx) h.Qb_le_normalizer_Ha
    have hQ2 : conjSub x (pCoreOf 2 H) ≤ Subgroup.normalizer
        ((conjSub x (pCoreOf 2 H) ⊔ (VZ S H ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      fun _ hg => Subgroup.le_normalizer (Subgroup.mem_sup_left hg)
    have hSN : conjSub x S ≤ Subgroup.normalizer
        ((conjSub x (pCoreOf 2 H) ⊔ (VZ S H ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      (h.sup_conj hx).2.le.trans (sup_le hQ2 hQ1)
    have hrel : (conjSub x (pCoreOf 2 H)).relIndex
        (conjSub x (pCoreOf 2 H) ⊔ (VZ S H ⊓ pCoreOf 2 M)) = 2 := by
      rw [sup_comm, h.relIndex_Qa2_Ha hx hxH]
      have := h.relIndex_R_Ha hx hxH h4
      omega
    rw [← pCoreOf_conjSub] at hSN hrel
    obtain ⟨-, hU⟩ := hz2.unique2 _ hYS hSN hrel
    have := hU (VZ S H ⊓ conjSub x (VZ S H)) inf_le_right
      (fun g hg => hRn (h.conjSub_S_le_M hx hg)) h4
    rw [this, Subgroup.commutator_comm]
  · have hYS : conjSub x (VZ S H) ⊓ pCoreOf 2 M ≤ S := inf_le_right.trans h.Qb_le_S
    have hQ1 : pCoreOf 2 M ≤ Subgroup.normalizer
        ((pCoreOf 2 H ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      F1.le_normalizer_sup h.Qb_le_normalizer_Qa (h.Qb_le_normalizer_Ha2 hx)
    have hQ2 : pCoreOf 2 H ≤ Subgroup.normalizer
        ((pCoreOf 2 H ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      fun _ hg => Subgroup.le_normalizer (Subgroup.mem_sup_left hg)
    have hSN : S ≤ Subgroup.normalizer
        ((pCoreOf 2 H ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M) : Subgroup G) : Set G) :=
      h.sup_Qa_Qb.symm.le.trans (sup_le hQ2 hQ1)
    have hrel : (pCoreOf 2 H).relIndex (pCoreOf 2 H ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M)) = 2 := by
      rw [sup_comm, h.relIndex_Qa_Ha2 hx hxH]
      have := h.relIndex_R_Ha2 hx hxH h4
      omega
    obtain ⟨-, hU⟩ := h.zfacts.unique2 _ hYS hSN hrel
    have := hU (VZ S H ⊓ conjSub x (VZ S H)) inf_le_left
      (fun g hg => hRn (h.S_le_M hg)) h4
    rw [this, Subgroup.commutator_comm]

theorem commutator_Vh_le_R_of (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H)
    {Z : Subgroup G}
    (ha : ∀ a ∈ VZ S H ⊓ pCoreOf 2 M, ∀ z ∈ Z, ⁅a, z⁆ ∈ VZ S H ⊓ conjSub x (VZ S H))
    (hb : ∀ b ∈ conjSub x (VZ S H) ⊓ pCoreOf 2 M, ∀ z ∈ Z,
      ⁅b, z⁆ ∈ VZ S H ⊓ conjSub x (VZ S H)) :
    ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M), Z⁆ ≤
      VZ S H ⊓ conjSub x (VZ S H) := by
  have hRn := h.R_normal hx hxH
  rw [Subgroup.commutator_le]
  intro v hv z hz
  have hHaN : VZ S H ⊓ pCoreOf 2 M ≤
      Subgroup.normalizer ((conjSub x (VZ S H) ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
    fun _ hg => h.Qb_le_normalizer_Ha2 hx hg.2
  obtain ⟨a, haH, b, hbH, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hHaN).mp hv
  have e : ⁅a * b, z⁆ = a * ⁅b, z⁆ * a⁻¹ * ⁅a, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have haM : a ∈ M := h.S_le_M (h.Za_le_S haH.1)
  refine (VZ S H ⊓ conjSub x (VZ S H)).mul_mem ?_ (ha a haH z hz)
  exact (Subgroup.mem_normalizer_iff.mp (hRn haM) _).mp (hb b hbH z hz)

theorem not_both_commutators_le_R (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    ¬ (⁅conjSub x (VZ S H), VZ S H ⊓ pCoreOf 2 M⁆ ≤ VZ S H ⊓ conjSub x (VZ S H) ∧
      ⁅VZ S H, conjSub x (VZ S H) ⊓ pCoreOf 2 M⁆ ≤ VZ S H ⊓ conjSub x (VZ S H)) := by
  rintro ⟨h1, h2⟩
  have hRn := h.R_normal hx hxH
  have hZa : VZ S H ≤ Subgroup.normalizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) :=
    fun _ hg => hRn (h.S_le_M (h.Za_le_S hg))
  have hZa2 : conjSub x (VZ S H) ≤
      Subgroup.normalizer ((VZ S H ⊓ conjSub x (VZ S H) : Subgroup G) : Set G) :=
    fun _ hg => hRn (h.conjSub_S_le_M hx (h.Za2_le_S2 x hg))
  have hone : (1 : G) ∈ VZ S H ⊓ conjSub x (VZ S H) := (VZ S H ⊓ conjSub x (VZ S H)).one_mem
  have hA : ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M), VZ S H⁆ ≤
      VZ S H ⊓ conjSub x (VZ S H) := by
    refine h.commutator_Vh_le_R_of hx hxH ?_ ?_
    · intro a ha z hz
      have : ⁅a, z⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (F7.isElemAbelian_comm h.zfacts.elemAbelian ha.1 hz)
      rw [this]
      exact hone
    · intro b hb z hz
      apply h2
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb hz
  have hB : ⁅(VZ S H ⊓ pCoreOf 2 M) ⊔ (conjSub x (VZ S H) ⊓ pCoreOf 2 M),
      conjSub x (VZ S H)⁆ ≤ VZ S H ⊓ conjSub x (VZ S H) := by
    refine h.commutator_Vh_le_R_of hx hxH ?_ ?_
    · intro a ha z hz
      apply h1
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ha hz
    · intro b hb z hz
      have : ⁅b, z⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (F7.isElemAbelian_comm (h.isElemAbelian_Za2 x) hb.1 hz)
      rw [this]
      exact hone
  apply h.not_commutator_Vh_le_R hx hxH
  exact (Subgroup.commutator_mono le_rfl (h.oTwoUpper_M_le_D hx hxH)).trans
    (commutator_sup_le hZa hZa2 hA hB)

theorem card_R (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) = 2 := by
  have h2 : 2 ≤ Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) := by
    have := Subgroup.card_le_of_le (h.Zb_le_R hx)
    rw [h.card_Zb] at this
    exact this
  have h4 := h.card_R_le_four hx hxH
  have hdvd : Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) ∣ 8 := by
    have := Subgroup.card_dvd_of_le (h.R_le_Ha hx hxH)
    rwa [h.card_Ha] at this
  have hne4 : Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) ≠ 4 := by
    intro h4'
    obtain ⟨e1, e2⟩ := h.R_eq_commutator hx hxH h4'
    apply h.not_both_commutators_le_R hx hxH
    constructor
    · rw [Subgroup.commutator_comm, ← e1]
    · rw [Subgroup.commutator_comm, ← e2]
  generalize Nat.card ↥(VZ S H ⊓ conjSub x (VZ S H)) = c at h2 h4 hdvd hne4
  interval_cases c <;> omega

theorem relIndex_Ha2_Qa (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (pCoreOf 2 H).relIndex ((conjSub x (VZ S H) ⊓ pCoreOf 2 M) ⊔ pCoreOf 2 H) = 4 := by
  rw [h.relIndex_Qa_Ha2 hx hxH]
  have := h.relIndex_R_Ha2 hx hxH (h.card_R hx hxH)
  omega

theorem relIndex_Ha_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (conjSub x (pCoreOf 2 H)).relIndex ((VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H)) = 4 := by
  rw [h.relIndex_Qa2_Ha hx hxH]
  have := h.relIndex_R_Ha hx hxH (h.card_R hx hxH)
  omega

theorem not_Ha2_le_Qa (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    ¬ conjSub x (VZ S H) ⊓ pCoreOf 2 M ≤ pCoreOf 2 H := by
  intro hle
  have h1 := h.relIndex_Ha2_Qa hx hxH
  rw [sup_eq_right.mpr hle, Subgroup.relIndex_self] at h1
  omega

theorem relIndex_Qa2_S2 (h : B1Hyp H M S) (x : G) :
    (conjSub x (pCoreOf 2 H)).relIndex (conjSub x S) = 8 := by
  rw [← h.relIndex_Qa_S]
  exact relIndex_conjSub x _ _

theorem exists_commutator_not_mem_Qa2 (h : B1Hyp H M S) (x : G) :
    ∃ a ∈ conjSub x S, ∃ b ∈ conjSub x S,
      a * b * a⁻¹ * b⁻¹ ∉ conjSub x (pCoreOf 2 H) := by
  obtain ⟨a, ha, b, hb, hnot⟩ := h.exists_commutator_not_mem_Qa
  refine ⟨x * a * x⁻¹, mul_mem_conjSub ha, x * b * x⁻¹, mul_mem_conjSub hb, fun hmem => hnot ?_⟩
  have e : x * a * x⁻¹ * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ =
      x * (a * b * a⁻¹ * b⁻¹) * x⁻¹ := by group
  rw [e] at hmem
  have := mem_conjSub.mp hmem
  simpa [mul_assoc] using this

theorem sup_Qa_inf_Qb_Qa2 (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) =
      (VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) := by
  have hHaQ : VZ S H ⊓ pCoreOf 2 M ≤ pCoreOf 2 H ⊓ pCoreOf 2 M :=
    inf_le_inf_right _ h.Za_le_Qa
  have hAK : (VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) ≤
      (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) := sup_le_sup_right hHaQ _
  have hQbS2 : pCoreOf 2 M ≤ conjSub x S := h.Qb_le_conjSub_S hx
  have hKS2 : (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) ≤ conjSub x S :=
    sup_le (inf_le_right.trans hQbS2) (h.Qa2_le_S2 x)
  have hAS2 : (VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) ≤ conjSub x S := hAK.trans hKS2
  have hQ2A : conjSub x (pCoreOf 2 H) ≤ (VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) :=
    le_sup_right
  have h2 : ((VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H)).relIndex (conjSub x S) = 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hQ2A hAS2
    rw [h.relIndex_Qa2_S2 x, h.relIndex_Ha_Qa2 hx hxH] at h1
    omega
  by_contra hne
  have hKA : ¬ (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) ≤
      (VZ S H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) := fun hle => hne (le_antisymm hle hAK)
  have hKeq : (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) = conjSub x S := by
    have := sup_eq_of_relIndex_two hAS2 h2 hKS2 hKA
    rwa [sup_eq_right.mpr hAK] at this
  have hQn : conjSub x S ≤ Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
    h.conjSub_S_le_normalizer_Qa2 x
  have hHaN : VZ S H ⊓ pCoreOf 2 M ≤ Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
    h.Ha_le_normalizer_Qa2 hx
  have hQQN : pCoreOf 2 H ⊓ pCoreOf 2 M ≤
      Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
    fun _ hg => h.Qb_le_normalizer_Qa2 hx hg.2
  have hcomm : ∀ s ∈ conjSub x S, ∀ t ∈ conjSub x S,
      s * t * s⁻¹ * t⁻¹ ∈ conjSub x (pCoreOf 2 H) := by
    refine commutator_mem_of_central_index_two hQn hQ2A h2 ?_
    intro a ha t ht
    have htK : t ∈ (pCoreOf 2 H ⊓ pCoreOf 2 M) ⊔ conjSub x (pCoreOf 2 H) := by
      rw [hKeq]; exact ht
    obtain ⟨h1, hh1, q1, hq1, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hHaN).mp ha
    obtain ⟨u, hu, q2, hq2, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hQQN).mp htK
    refine commutator_mem_of_quotient hQn (hAS2 ha) (inf_le_right.trans hQbS2 hh1) ht
      (inf_le_right.trans hQbS2 hu) ?_ ?_ ?_
    · have e : (h1 * q1)⁻¹ * h1 = q1⁻¹ := by group
      rw [e]
      exact (conjSub x (pCoreOf 2 H)).inv_mem hq1
    · have e : (u * q2)⁻¹ * u = q2⁻¹ := by group
      rw [e]
      exact (conjSub x (pCoreOf 2 H)).inv_mem hq2
    · have hc : u * h1 = h1 * u :=
        Subgroup.mem_centralizer_iff.mp (h.Za_le_centralizer_Qa hh1.1) u hu.1
      have e : ⁅h1, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
      rw [commutatorElement_def] at e
      rw [e]
      exact (conjSub x (pCoreOf 2 H)).one_mem
  obtain ⟨a, haS, b, hbS, hnot⟩ := h.exists_commutator_not_mem_Qa2 x
  exact hnot (hcomm a haS b hbS)

theorem Qa_eq_sup (h : B1Hyp H M S) {x : G} (hx : x ∈ M) (hxH : x ∉ H) :
    pCoreOf 2 H = (pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H := by
  have hTQb : pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H) ≤ pCoreOf 2 M := h.inf_Qa_Qa2_le hx hxH
  have hle : (pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H ≤ pCoreOf 2 H :=
    sup_le inf_le_left h.Za_le_Qa
  have c1 : Nat.card ↥(pCoreOf 2 H) = 2 * Nat.card ↥(pCoreOf 2 H ⊓ pCoreOf 2 M) := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 H ⊓ pCoreOf 2 M) (pCoreOf 2 H)
    rw [inf_eq_left.mpr (inf_le_left : pCoreOf 2 H ⊓ pCoreOf 2 M ≤ pCoreOf 2 H),
      h.relIndex_Qa_inf_Qb] at h1
    exact h1.symm
  have hQQN : pCoreOf 2 H ⊓ pCoreOf 2 M ≤
      Subgroup.normalizer (conjSub x (pCoreOf 2 H) : Set G) :=
    fun _ hg => h.Qb_le_normalizer_Qa2 hx hg.2
  have c2 : Nat.card ↥(pCoreOf 2 H ⊓ pCoreOf 2 M) =
      4 * Nat.card ↥(pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) := by
    have hri : (conjSub x (pCoreOf 2 H)).relIndex (pCoreOf 2 H ⊓ pCoreOf 2 M) = 4 := by
      rw [← F1.relIndex_sup_eq_of_le_normalizer hQQN, h.sup_Qa_inf_Qb_Qa2 hx hxH]
      exact h.relIndex_Ha_Qa2 hx hxH
    have h1 := Subgroup.relIndex_mul_card (conjSub x (pCoreOf 2 H)) (pCoreOf 2 H ⊓ pCoreOf 2 M)
    have e : conjSub x (pCoreOf 2 H) ⊓ (pCoreOf 2 H ⊓ pCoreOf 2 M) =
        pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H) :=
      le_antisymm (fun y hy => ⟨hy.2.1, hy.1⟩) (fun y hy => ⟨hy.2, hy.1, hTQb hy⟩)
    rw [hri, e] at h1
    exact h1.symm
  have hTN : pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H) ≤ Subgroup.normalizer (VZ S H : Set G) :=
    fun g hg => h.S_le_normalizer_Za (h.Qa_le_S hg.1)
  have c3 : Nat.card ↥((pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H) =
      8 * Nat.card ↥(pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) := by
    have h1 := Subgroup.relIndex_mul_card (VZ S H)
      ((pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H)
    have hZ : VZ S H ⊓ ((pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H) = VZ S H :=
      inf_eq_left.mpr le_sup_right
    rw [hZ, F1.relIndex_sup_eq_of_le_normalizer hTN, h.zfacts.card_eq] at h1
    have h2 := Subgroup.relIndex_mul_card (VZ S H) (pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H))
    have e : VZ S H ⊓ (pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) = VZ S H ⊓ conjSub x (VZ S H) := by
      rw [h.R_eq_Za_inf_Qa2 hx hxH]
      exact le_antisymm (fun y hy => ⟨hy.1, hy.2.2⟩) (fun y hy => ⟨hy.1, h.Za_le_Qa hy.1, hy.2⟩)
    rw [e, h.card_R hx hxH] at h2
    omega
  have hcard : Nat.card ↥(pCoreOf 2 H) ≤
      Nat.card ↥((pCoreOf 2 H ⊓ conjSub x (pCoreOf 2 H)) ⊔ VZ S H) := by omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end B1Hyp

end Hyp

end F53B1

end CFSG.Quasithin
