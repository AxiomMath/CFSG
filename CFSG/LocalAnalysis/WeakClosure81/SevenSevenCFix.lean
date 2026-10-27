module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section General

variable {G : Type} [Group G]

private theorem seven_seven_c_fix_commutator_mem_normalizer {A : Subgroup G} {v a : G}
    (hv : v ∈ Subgroup.normalizer (A : Set G)) (ha : a ∈ A) : ⁅a, v⁆ ∈ A := by
  have hmem : v * a⁻¹ * v⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hv a⁻¹).mp (A.inv_mem ha)
  rw [commutatorElement_def]
  rw [show a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) by group]
  exact A.mul_mem ha hmem

theorem commutator_mul_of_mem_normalizer {A : Subgroup G} {v : G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hv : v ∈ Subgroup.normalizer (A : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : ⁅a * b, v⁆ = ⁅a, v⁆ * ⁅b, v⁆ := by
  have hbA : ⁅b, v⁆ ∈ A := seven_seven_c_fix_commutator_mem_normalizer hv hb
  have haA : ⁅a, v⁆ ∈ A := seven_seven_c_fix_commutator_mem_normalizer hv ha
  have hconj : a * ⁅b, v⁆ * a⁻¹ = ⁅b, v⁆ := by
    rw [hAab a ha (⁅b, v⁆) hbA]
    group
  rw [show ⁅a * b, v⁆ = a * ⁅b, v⁆ * a⁻¹ * ⁅a, v⁆ by
    simp only [commutatorElement_def]; group, hconj]
  exact hAab (⁅b, v⁆) hbA (⁅a, v⁆) haA

private theorem seven_seven_c_fix_commutator_inv {A : Subgroup G} {v a : G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hv : v ∈ Subgroup.normalizer (A : Set G))
    (ha : a ∈ A) : ⁅a⁻¹, v⁆ = ⁅a, v⁆⁻¹ := by
  have hmul := commutator_mul_of_mem_normalizer hAab hv (A.inv_mem ha) ha
  have hone : ⁅a⁻¹ * a, v⁆ = 1 := by rw [inv_mul_cancel]; simp
  have hba : ⁅a⁻¹, v⁆ * ⁅a, v⁆ = 1 := by rw [← hmul, hone]
  have hca : ⁅a⁻¹, v⁆ ∈ A := seven_seven_c_fix_commutator_mem_normalizer hv (A.inv_mem ha)
  have hcb : ⁅a, v⁆ ∈ A := seven_seven_c_fix_commutator_mem_normalizer hv ha
  have hab : ⁅a, v⁆ * ⁅a⁻¹, v⁆ = 1 := by
    rw [hAab (⁅a, v⁆) hcb (⁅a⁻¹, v⁆) hca, hba]
  exact eq_inv_of_mul_eq_one_right hab

theorem card_eq_card_inf_centralizer_mul_card_image {A P : Subgroup G} {v : G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hv : v ∈ Subgroup.normalizer (A : Set G))
    (hP : P ≤ A) :
    Nat.card ↥P = Nat.card ↥(P ⊓ Subgroup.centralizer ({v} : Set G)) *
      Nat.card ↥{x : G | ∃ p ∈ P, x = ⁅p, v⁆} := by
  let ψ : ↥P →* ↥A :=
    { toFun := fun p =>
        ⟨⁅(p : G), v⁆, seven_seven_c_fix_commutator_mem_normalizer hv (hP p.2)⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := fun p q => by
        apply Subtype.ext
        exact commutator_mul_of_mem_normalizer hAab hv (hP p.2) (hP q.2) }
  have hker : ψ.ker = (P ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker]
    constructor
    · intro hp
      have hval : ((ψ p : ↥A) : G) = 1 := by rw [hp]; rfl
      have hp' : ⁅(p : G), v⁆ = 1 := hval
      have hcomm : Commute (p : G) v := (commutatorElement_eq_one_iff_commute).mp hp'
      refine Subgroup.mem_subgroupOf.mpr ⟨p.2, ?_⟩
      change (p : G) ∈ Subgroup.centralizer ({v} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ((commute_iff_eq (p : G) v).mp hcomm).symm
    · intro hp
      have hp' := Subgroup.mem_subgroupOf.mp hp
      have hcomm : Commute (p : G) v :=
        (commute_iff_eq (p : G) v).mpr
          (Subgroup.mem_centralizer_iff.mp hp'.2 v (by simp)).symm
      apply Subtype.ext
      change ⁅(p : G), v⁆ = 1
      exact (commutatorElement_eq_one_iff_commute).mpr hcomm
  have h1 : Nat.card ↥ψ.ker =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({v} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ _ ≤ P)).toEquiv
  have hset : ((ψ.range.map A.subtype : Subgroup G) : Set G) =
      {x : G | ∃ p ∈ P, x = ⁅p, v⁆} := by
    ext x
    constructor
    · intro hx
      change x ∈ ψ.range.map A.subtype at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨p, hp⟩ := hy
      refine ⟨(p : G), p.2, ?_⟩
      have hval := congrArg (fun z : ↥A => (z : G)) hp
      exact hval.symm
    · rintro ⟨p, hp, rfl⟩
      change ⁅p, v⁆ ∈ ψ.range.map A.subtype
      rw [Subgroup.mem_map]
      exact ⟨ψ ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, rfl⟩
  have h2 : Nat.card ↥ψ.range =
      Nat.card ↥{x : G | ∃ p ∈ P, x = ⁅p, v⁆} := by
    rw [← hset]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective ψ.range A.subtype A.subtype_injective).toEquiv
  rw [← Subgroup.card_ker_mul_card_range ψ, h1, h2]

theorem card_sup_eq_mul_card_of_commute {P Q : Subgroup G} (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hd : P ⊓ Q = ⊥) : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  let f : ↥P × ↥Q →* G :=
    P.subtype.noncommCoprod Q.subtype
      (fun p q => (commute_iff_eq (P.subtype p) (Q.subtype q)).mpr
        (hc (P.subtype p) p.2 (Q.subtype q) q.2))
  have hdisj : Disjoint P.subtype.range Q.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff_inf_le.mpr (le_of_eq hd)
  have hinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective P.subtype Q.subtype _).mpr
      ⟨P.subtype_injective, Q.subtype_injective, hdisj⟩
  have hrange : f.range = P ⊔ Q := by
    dsimp only [f]
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hcard : Nat.card ↥(P ⊔ Q) = Nat.card (↥P × ↥Q) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hcard, Nat.card_prod]

end General

section Fix

variable {G : Type} [Group G] [Finite G]


variable {V H E J V₁ V₂ V₃ A : Subgroup G}

private theorem seven_seven_c_fix_mul_comm_of_mem_iSub (h : Hyp73 V H E J) {a b : G}
    (ha : a ∈ iSub V H E) (hb : b ∈ iSub V H E) : a * b = b * a := by
  have hI := seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  exact congrArg Subtype.val (hI.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem coe_commutator_eq_image (h : Hyp73 V H E J) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hsmall : ∀ u ∈ U, ∀ w ∈ U, u ∉ iSub V H E → w ∉ iSub V H E → u * w ∈ iSub V H E)
    (hA : A ≤ iSub V H E) (hN : U ≤ Subgroup.normalizer (A : Set G)) {v : G} (hv : v ∈ U)
    (hvI : v ∉ iSub V H E) :
    ((⁅A, U⁆ : Subgroup G) : Set G) = {x : G | ∃ a ∈ A, x = ⁅a, v⁆} := by
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => seven_seven_c_fix_mul_comm_of_mem_iSub h (hA ha) (hA hb)
  have hvA : v ∈ Subgroup.normalizer (A : Set G) := hN hv
  have hv2 : v * v = 1 :=
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) hv
  let S : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, x = ⁅a, v⁆}
      one_mem' := ⟨1, A.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, A.mul_mem ha hb,
          (commutator_mul_of_mem_normalizer hAab hvA ha hb).symm⟩
      inv_mem' := by
        rintro x ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha,
          (seven_seven_c_fix_commutator_inv hAab hvA ha).symm⟩ }
  change ((⁅A, U⁆ : Subgroup G) : Set G) = (S : Set G)
  apply le_antisymm
  · change ⁅A, U⁆ ≤ S
    rw [Subgroup.commutator_le]
    intro a ha u hu
    by_cases huI : u ∈ iSub V H E
    · have hcomm : a * u = u * a :=
        seven_seven_c_fix_mul_comm_of_mem_iSub h (hA ha) huI
      have h1 : ⁅a, u⁆ = 1 :=
        (commutatorElement_eq_one_iff_commute).mpr ((commute_iff_eq a u).mpr hcomm)
      exact ⟨1, A.one_mem, by rw [h1]; simp [commutatorElement_def]⟩
    · have hi : v * u ∈ iSub V H E := hsmall v hv u hu hvI huI
      have hu_eq : u = v * (v * u) := by rw [← mul_assoc, hv2, one_mul]
      have hcomm_ai : ⁅a, v * u⁆ = 1 := by
        have h' : a * (v * u) = (v * u) * a :=
          seven_seven_c_fix_mul_comm_of_mem_iSub h (hA ha) hi
        exact (commutatorElement_eq_one_iff_commute).mpr
          ((commute_iff_eq a (v * u)).mpr h')
      have hcommu : ⁅a, u⁆ = ⁅a, v⁆ := by
        rw [hu_eq]
        rw [show ⁅a, v * (v * u)⁆ =
          ⁅a, v⁆ * (v * ⁅a, v * u⁆ * v⁻¹) by
            simp only [commutatorElement_def]; group]
        rw [hcomm_ai]
        simp
      exact ⟨a, ha, hcommu⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Subgroup.commutator_mem_commutator ha hv

theorem inf_centralizer_singleton_eq_inf_centralizer (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E)
    (hsmall : ∀ u ∈ U, ∀ w ∈ U, u ∉ iSub V H E → w ∉ iSub V H E → u * w ∈ iSub V H E)
    (hA : A ≤ iSub V H E) {v : G} (hv : v ∈ U) (hvI : v ∉ iSub V H E) :
    A ⊓ Subgroup.centralizer ({v} : Set G) = A ⊓ Subgroup.centralizer (U : Set G) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
    change a ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    by_cases huI : u ∈ iSub V H E
    · exact (seven_seven_c_fix_mul_comm_of_mem_iSub h (hA haA) huI).symm
    · have hvu : v * u ∈ iSub V H E := hsmall v hv u hu hvI huI
      have hv2 : v * v = 1 :=
        CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
          (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) hv
      have hu_eq : u = v * (v * u) := by rw [← mul_assoc, hv2, one_mul]
      have haCv : Commute a v :=
        (commute_iff_eq a v).mpr
          (Subgroup.mem_centralizer_iff.mp haC v (by simp)).symm
      have hai : Commute a (v * u) :=
        (commute_iff_eq a (v * u)).mpr
          (seven_seven_c_fix_mul_comm_of_mem_iSub h (hA haA) hvu)
      rw [hu_eq]
      exact (haCv.mul_right hai).symm
  · intro a ha
    obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
    change a ∈ Subgroup.centralizer ({v} : Set G)
    exact Subgroup.centralizer_le (by simpa using (Set.singleton_subset_iff.mpr hv)) haC

theorem inf_centralizer_eq_sup_commutator (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    A ⊓ Subgroup.centralizer (V₁ : Set G) = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ∧
      A ⊓ Subgroup.centralizer (V₂ : Set G) = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
  have hA1eq := (commutator_eq_inf h hc hA).1
  have hA2eq := (commutator_eq_inf h hc hA).2.1
  have hA1A : ⁅A, V₁⁆ ≤ A := hA1eq.trans_le inf_le_left
  have hA2A : ⁅A, V₂⁆ ≤ A := hA2eq.trans_le inf_le_left
  have hA1V : ⁅A, V₁⁆ ≤ V₁ := hA1eq.trans_le inf_le_right
  have hA2V : ⁅A, V₂⁆ ≤ V₂ := hA2eq.trans_le inf_le_right
  have hV1ab : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      ((isElemAbelian_of_mem_omegaSet h.elemAbelian hc.mem₁).1.is_comm.comm
        ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2ab : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      ((isElemAbelian_of_mem_omegaSet h.elemAbelian hc.mem₂).1.is_comm.comm
        ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm12 : ∀ u ∈ V₁, ∀ w ∈ V₂, u * w = w * u := by
    intro u hu w hw
    have hmem : ⁅u, w⁆ ∈ ⁅V₁, V₂⁆ := Subgroup.commutator_mem_commutator hu hw
    rw [hc.comm₁₂] at hmem
    exact (commute_iff_eq u w).mp
      ((commutatorElement_eq_one_iff_commute).mp (Subgroup.mem_bot.mp hmem))
  have hnotI₁ : ∃ v ∈ V₁, v ∉ iSub V H E := by
    by_contra hcon
    push Not at hcon
    exact (mem_omegaSet.mp hc.mem₁).choose_spec.2.2
      (le_trans (fun v hv => hcon v hv) (h.iSub_le.trans h.pcore_le))
  have hnotI₂ : ∃ v ∈ V₂, v ∉ iSub V H E := by
    by_contra hcon
    push Not at hcon
    exact (mem_omegaSet.mp hc.mem₂).choose_spec.2.2
      (le_trans (fun v hv => hcon v hv) (h.iSub_le.trans h.pcore_le))
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro a ha
      obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hfac⟩ :=
        exists_commutator_factorization h hc hA a haA
      obtain ⟨v₁, hv₁, hv₁I⟩ := hnotI₁
      have ha₁V : a₁ ∈ V₁ := hA1V ha₁
      have ha₂V : a₂ ∈ V₂ := hA2V ha₂
      have hva : Commute v₁ a :=
        (commute_iff_eq v₁ a).mpr
          (Subgroup.mem_centralizer_iff.mp haC v₁ hv₁)
      have hva₁ : Commute v₁ a₁ :=
        (commute_iff_eq v₁ a₁).mpr (hV1ab a₁ ha₁V v₁ hv₁).symm
      have hva₂ : Commute v₁ a₂ :=
        (commute_iff_eq v₁ a₂).mpr (hcomm12 v₁ hv₁ a₂ ha₂V)
      have ha3eq : a₃ = (a₁ * a₂)⁻¹ * a := by rw [← hfac]; group
      have ha3comm : v₁ * a₃ = a₃ * v₁ := by
        rw [ha3eq]
        exact (commute_iff_eq v₁ ((a₁ * a₂)⁻¹ * a)).mp
          ((hva₁.mul_right hva₂).inv_right.mul_right hva)
      have ha3one : a₃ = 1 :=
        (eq_one_of_mem_commutator_of_commute h hc hA).1 v₁ hv₁ hv₁I a₃ ha₃ ha3comm
      have hprod : a₁ * a₂ = a := by simpa [ha3one] using hfac
      rw [← hprod]
      exact Subgroup.mul_mem_sup ha₁ ha₂
    · refine sup_le (le_inf hA1A ?_) (le_inf hA2A ?_)
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hV1ab x (hA1V hx) y hy).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hcomm12 y hy x (hA2V hx)
  · apply le_antisymm
    · intro a ha
      obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hfac⟩ :=
        exists_commutator_factorization h hc hA a haA
      obtain ⟨v₂, hv₂, hv₂I⟩ := hnotI₂
      have ha₁V : a₁ ∈ V₁ := hA1V ha₁
      have ha₂V : a₂ ∈ V₂ := hA2V ha₂
      have hva : Commute v₂ a :=
        (commute_iff_eq v₂ a).mpr
          (Subgroup.mem_centralizer_iff.mp haC v₂ hv₂)
      have hva₁ : Commute v₂ a₁ :=
        (commute_iff_eq v₂ a₁).mpr (hcomm12 a₁ ha₁V v₂ hv₂).symm
      have hva₂ : Commute v₂ a₂ :=
        (commute_iff_eq v₂ a₂).mpr (hV2ab a₂ ha₂V v₂ hv₂).symm
      have ha3eq : a₃ = (a₁ * a₂)⁻¹ * a := by rw [← hfac]; group
      have ha3comm : v₂ * a₃ = a₃ * v₂ := by
        rw [ha3eq]
        exact (commute_iff_eq v₂ ((a₁ * a₂)⁻¹ * a)).mp
          ((hva₁.mul_right hva₂).inv_right.mul_right hva)
      have ha3one : a₃ = 1 :=
        (eq_one_of_mem_commutator_of_commute h hc hA).2 v₂ hv₂ hv₂I a₃ ha₃ ha3comm
      have hprod : a₁ * a₂ = a := by simpa [ha3one] using hfac
      rw [← hprod]
      exact Subgroup.mul_mem_sup ha₁ ha₂
    · refine sup_le (le_inf hA1A ?_) (le_inf hA2A ?_)
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm12 x (hA1V hx) y hy).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hV2ab x (hA2V hx) y hy).symm

private theorem seven_seven_c_fix_card_eq_of_inf_centralizer (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A)
    {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hN : U ≤ Subgroup.normalizer (A : Set G))
    (hCU : A ⊓ Subgroup.centralizer (U : Set G) = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) :
    Nat.card ↥A = Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, U⁆ := by
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => seven_seven_c_fix_mul_comm_of_mem_iSub h (hA.le_iSub ha) (hA.le_iSub hb)
  have hUnotI : ∃ v ∈ U, v ∉ iSub V H E := by
    by_contra hcon
    push Not at hcon
    exact (mem_omegaSet.mp hU).choose_spec.2.2
      (le_trans (fun v hv => hcon v hv) (h.iSub_le.trans h.pcore_le))
  obtain ⟨v, hv, hvI⟩ := hUnotI
  have hvA : v ∈ Subgroup.normalizer (A : Set G) := hN hv
  have hcard := card_eq_card_inf_centralizer_mul_card_image
    (A := A) (P := A) (v := v) hAab hvA le_rfl
  rw [inf_centralizer_singleton_eq_inf_centralizer h hU (hc.small U hU) hA.le_iSub hv hvI,
    hCU] at hcard
  have hset := coe_commutator_eq_image h hU (hc.small U hU) hA.le_iSub hN hv hvI
  rw [← hset] at hcard
  exact hcard

theorem card_commutator_eq_card_commutator_three (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    Nat.card ↥⁅A, V₁⁆ = Nat.card ↥⁅A, V₃⁆ ∧ Nat.card ↥⁅A, V₂⁆ = Nat.card ↥⁅A, V₃⁆ := by
  have hA1eq := (commutator_eq_inf h hc hA).1
  have hA2eq := (commutator_eq_inf h hc hA).2.1
  have hA3eq := (commutator_eq_inf h hc hA).2.2
  have hA1A : ⁅A, V₁⁆ ≤ A := hA1eq.trans_le inf_le_left
  have hA2A : ⁅A, V₂⁆ ≤ A := hA2eq.trans_le inf_le_left
  have hA3A : ⁅A, V₃⁆ ≤ A := hA3eq.trans_le inf_le_left
  have hN1 : V₁ ≤ Subgroup.normalizer (A : Set G) :=
    ((le_sup_left : V₁ ≤ V₁ ⊔ V₂).trans
      (le_sup_left : V₁ ⊔ V₂ ≤ (V₁ ⊔ V₂) ⊔ V₃)).trans hA.normalizes
  have hN2 : V₂ ≤ Subgroup.normalizer (A : Set G) :=
    ((le_sup_right : V₂ ≤ V₁ ⊔ V₂).trans
      (le_sup_left : V₁ ⊔ V₂ ≤ (V₁ ⊔ V₂) ⊔ V₃)).trans hA.normalizes
  have hcardA1 : Nat.card ↥A =
      Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, V₁⁆ :=
    seven_seven_c_fix_card_eq_of_inf_centralizer h hc hA hc.mem₁ hN1
      (inf_centralizer_eq_sup_commutator h hc hA).1
  have hcardA2 : Nat.card ↥A =
      Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, V₂⁆ :=
    seven_seven_c_fix_card_eq_of_inf_centralizer h hc hA hc.mem₂ hN2
      (inf_centralizer_eq_sup_commutator h hc hA).2
  have hA12A : ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ≤ A := sup_le hA1A hA2A
  have hAeq : A = (⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊔ ⁅A, V₃⁆ :=
    le_antisymm (le_sup_commutator h hc hA) (sup_le hA12A hA3A)
  have hcardA3 : Nat.card ↥A =
      Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, V₃⁆ := by
    conv_lhs => rw [hAeq]
    exact card_sup_eq_mul_card_of_commute
      (P := ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) (Q := ⁅A, V₃⁆)
      (fun p hp q hq => seven_seven_c_fix_mul_comm_of_mem_iSub h
        (hA.le_iSub (hA12A hp)) (hA.le_iSub (hA3A hq)))
      (by rw [inf_comm]; exact (commutator_inf_commutator_eq_bot h hc hA).2)
  have hpos : 0 < Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) :=
    Nat.card_pos (α := ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆))
  exact ⟨Nat.eq_of_mul_eq_mul_left hpos (hcardA1.symm.trans hcardA3),
    Nat.eq_of_mul_eq_mul_left hpos (hcardA2.symm.trans hcardA3)⟩

end Fix

end CFSG.LocalAnalysis.WeakClosure81
