module

public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commute_mk_of_commutator_mem {K : Type} [Group K] (N : Subgroup K) [N.Normal]
    {l m : K} (h : ⁅l, m⁆ ∈ N) : Commute (l : K ⧸ N) (m : K ⧸ N) := by
  have h1 : (QuotientGroup.mk' N) ⁅l, m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_commute.mp h1

theorem commutator_mem_of_commute_mk {K : Type} [Group K] (N : Subgroup K) [N.Normal]
    {l m : K} (h : Commute (l : K ⧸ N) (m : K ⧸ N)) : ⁅l, m⁆ ∈ N := by
  have h1 : ⁅(QuotientGroup.mk' N) l, (QuotientGroup.mk' N) m⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr h
  rw [← map_commutatorElement] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem eq_one_of_central_of_center_eq_bot {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂]
    (e : Q₁ ≃* Q₂) (hZ : Subgroup.center Q₂ = ⊥) {x : Q₁} (hx : ∀ g : Q₁, g * x = x * g) :
    x = 1 := by
  have hmem : e x ∈ Subgroup.center Q₂ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']
  rw [hZ, Subgroup.mem_bot] at hmem
  exact (map_eq_one_iff e e.injective).mp hmem

theorem mem_aschbacherSolvableCore_of_mem {K : Type} [Group K] [Finite K] {L : Subgroup K}
    {g : L} (h : (g : K) ∈ aschbacherSolvableCore 3 K) : g ∈ aschbacherSolvableCore 3 L := by
  have hsolv : Group.IsSolvable (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).1
  have hK3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hNsolv : Group.IsSolvable ((aschbacherSolvableCore 3 K).subgroupOf L) := by
    haveI := hsolv
    let f : ((aschbacherSolvableCore 3 K).subgroupOf L) →* aschbacherSolvableCore 3 K :=
      MonoidHom.codRestrict (L.subtype.comp ((aschbacherSolvableCore 3 K).subgroupOf L).subtype)
        (aschbacherSolvableCore 3 K) (fun n => Subgroup.mem_subgroupOf.mp n.2)
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    have h1 : ((f a : aschbacherSolvableCore 3 K) : K) =
        ((f b : aschbacherSolvableCore 3 K) : K) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hdvd : Nat.card ((aschbacherSolvableCore 3 K).subgroupOf L) ∣
      Nat.card (aschbacherSolvableCore 3 K) := by
    have h1 : Nat.card (((aschbacherSolvableCore 3 K).subgroupOf L).map L.subtype) =
        Nat.card ((aschbacherSolvableCore 3 K).subgroupOf L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at h1
    rw [← h1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hN3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 K).subgroupOf L) :=
    fun h3 => hK3 (h3.trans hdvd)
  have hle := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.2.1
  exact hle _ inferInstance hNsolv hN3 (Subgroup.mem_subgroupOf.mpr h)

theorem not_mem_aschbacherSolvableCore_of_pow_three {K : Type} [Group K] [Finite K] {x : K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∉ aschbacherSolvableCore 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  intro hx
  have hdvd := Subgroup.orderOf_dvd_natCard _ hx
  rw [orderOf_eq_prime hx3 hx1] at hdvd
  exact hK3 hdvd

theorem two_pow_mul_two_pow_mod_three (n : ℕ) : (2 ^ n * 2 ^ n) % 3 = 1 := by
  rw [← mul_pow]
  norm_num [Nat.pow_mod]

theorem commute_of_pow_relation {M : Type*} [Group M] {u v : M} {n : ℕ} (hv3 : v ^ 3 = 1)
    (huv : Commute u v) (ht : (u * v⁻¹) ^ (2 ^ n) = 1) {z : M} (hz : Commute u z) :
    Commute v z := by
  have hN : u ^ (2 ^ n) = v ^ (2 ^ n) := by
    have h1 : u ^ (2 ^ n) * (v⁻¹) ^ (2 ^ n) = 1 := by
      rw [← (huv.inv_right).mul_pow]
      exact ht
    rw [inv_pow] at h1
    exact (mul_eq_one_iff_eq_inv.mp h1).trans (inv_inv _)
  have hzv : Commute (v ^ (2 ^ n)) z := by
    rw [← hN]
    exact hz.pow_left _
  have hv : v = (v ^ (2 ^ n)) ^ (2 ^ n) := by
    rw [← pow_mul, pow_eq_pow_mod (2 ^ n * 2 ^ n) hv3, two_pow_mul_two_pow_mod_three, pow_one]
  have hzv' := hzv.pow_left (2 ^ n)
  rw [← hv] at hzv'
  exact hzv'


noncomputable abbrev step4bThetaQuot (C : Subgroup G) : C →* C ⧸ aschbacherSolvableCore 3 C :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 C)

theorem normalizes_core {C : Subgroup G} {L₀ : Subgroup C} {b : G} {Q : Subgroup G}
    (hL₀ : L₀ ∈ thetaComponents 3 C)
    (hZ : Subgroup.center ((L₀.map C.subtype : Subgroup G) ⧸
      aschbacherSolvableCore 3 (L₀.map C.subtype)) = ⊥)
    (hb : b ∈ L₀.map C.subtype) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hQ2 : IsPGroup 2 Q)
    (hQC : Q ≤ C) (hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) :
    Q ≤ Subgroup.normalizer ((L₀.map C.subtype : Subgroup G) : Set G) := by
  intro q hq
  by_contra hqN
  have hqC : q ∈ C := hQC hq
  obtain ⟨q₀, hq₀G⟩ : ∃ q₀ : C, (q₀ : G) = q := ⟨⟨q, hqC⟩, rfl⟩
  obtain ⟨L₁, hL₁def⟩ : ∃ L₁ : Subgroup C,
      L₁ = L₀.map (MulAut.conj q₀ : C ≃* C).toMonoidHom := ⟨_, rfl⟩
  have hL₁ : L₁ ∈ thetaComponents 3 C := by
    rw [hL₁def]
    exact map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj q₀ : C ≃* C) hL₀
  have hmL₁ : ∀ c ∈ L₀, q₀ * c * q₀⁻¹ ∈ L₁ := by
    intro c hc
    rw [hL₁def]
    exact Subgroup.mem_map_of_mem (MulAut.conj q₀ : C ≃* C).toMonoidHom hc
  have hne : L₀ ≠ L₁ := by
    intro h
    apply hqN
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ L₀.map C.subtype := hn
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hn'
    have hc' : q₀ * c * q₀⁻¹ ∈ L₀ := by
      rw [h]
      exact hmL₁ c hc
    have hEq : C.subtype (q₀ * c * q₀⁻¹) = q * C.subtype c * q⁻¹ := by
      rw [← hq₀G]
      rfl
    rw [← hEq]
    exact Subgroup.mem_map_of_mem C.subtype hc'
  have hcomm := CFSG.RankThree.PartTwo.Sec14.Item148HJ.commutator_le_of_mem_thetaComponents_of_ne
    hL₀ hL₁ hne
  have hcomm' : ∀ l ∈ L₀, ∀ m ∈ L₁, ⁅l, m⁆ ∈ aschbacherSolvableCore 3 C :=
    fun l hl m hm => hcomm (Subgroup.commutator_mem_commutator hl hm)
  have hcommute : ∀ l ∈ L₀, ∀ m ∈ L₁, Commute (step4bThetaQuot C l) (step4bThetaQuot C m) :=
    fun l hl m hm => commute_mk_of_commutator_mem _ (hcomm' l hl m hm)
  obtain ⟨b₀, hb₀, hb₀G⟩ := Subgroup.mem_map.mp hb
  have hb₀G' : (b₀ : G) = b := hb₀G
  have hb₀3 : b₀ ^ 3 = 1 := Subtype.ext (by simp [hb₀G', hb3])
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    apply hb1
    simpa [hb₀G'] using congrArg Subtype.val h
  have hcommuv : Commute (step4bThetaQuot C (q₀ * b₀ * q₀⁻¹)) (step4bThetaQuot C b₀) :=
    (hcommute b₀ hb₀ _ (hmL₁ b₀ hb₀)).symm
  have hv3 : (step4bThetaQuot C b₀) ^ 3 = 1 := by
    rw [← map_pow, hb₀3, map_one]
  have htG : ((q₀ * b₀ * q₀⁻¹ * b₀⁻¹ : C) : G) ∈ Q := by
    have hconv : ((q₀ * b₀ * q₀⁻¹ * b₀⁻¹ : C) : G) = q * (b * q⁻¹ * b⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb₀G', hq₀G, mul_assoc]
    rw [hconv]
    exact Q.mul_mem hq (hbQ q⁻¹ (Q.inv_mem hq))
  obtain ⟨n, hn⟩ := hQ2 ⟨_, htG⟩
  have ht : (q₀ * b₀ * q₀⁻¹ * b₀⁻¹) ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  have hT : (step4bThetaQuot C (q₀ * b₀ * q₀⁻¹) * (step4bThetaQuot C b₀)⁻¹) ^ (2 ^ n) = 1 := by
    rw [← map_inv, ← map_mul, ← map_pow, ht, map_one]
  have hl_central : ∀ l ∈ L₀, ⁅l, b₀⁆ ∈ aschbacherSolvableCore 3 C := by
    intro l hl
    have hz : Commute (step4bThetaQuot C (q₀ * b₀ * q₀⁻¹)) (step4bThetaQuot C l) :=
      (hcommute l hl _ (hmL₁ b₀ hb₀)).symm
    have h := commute_of_pow_relation hv3 hcommuv hT hz
    exact commutator_mem_of_commute_mk _ h.symm
  obtain ⟨b₀', hb₀'⟩ : ∃ x : L₀, (x : C) = b₀ := ⟨⟨b₀, hb₀⟩, rfl⟩
  have hcentral : ∀ g : L₀ ⧸ aschbacherSolvableCore 3 L₀,
      g * (b₀' : L₀ ⧸ aschbacherSolvableCore 3 L₀) =
        (b₀' : L₀ ⧸ aschbacherSolvableCore 3 L₀) * g := by
    intro g
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    refine Commute.eq (commute_mk_of_commutator_mem _ ?_)
    refine mem_aschbacherSolvableCore_of_mem ?_
    have hcomm0 : ((⁅g₀, b₀'⁆ : L₀) : C) = ⁅(g₀ : C), b₀⁆ := by
      simp [commutatorElement_def, hb₀']
    rw [hcomm0]
    exact hl_central g₀ g₀.2
  have hx₀ : (b₀' : L₀ ⧸ aschbacherSolvableCore 3 L₀) = 1 :=
    eq_one_of_central_of_center_eq_bot (Sec13.thetaQuotEquivSub C L₀) hZ hcentral
  rw [QuotientGroup.eq_one_iff] at hx₀
  have hb₀'3 : b₀' ^ 3 = 1 := Subtype.ext (by simp [hb₀', hb₀3])
  have hb₀'1 : b₀' ≠ 1 := by
    intro h
    apply hb₀1
    simpa [hb₀'] using congrArg Subtype.val h
  exact not_mem_aschbacherSolvableCore_of_pow_three hb₀'3 hb₀'1 hx₀

theorem normalizes {y b : G} {L' Q : Subgroup G} (hL' : L' ∈ thetaComponentsAt 3 y)
    (hZ : Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') = ⊥) (hb : b ∈ L') (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) (hQ2 : IsPGroup 2 Q) (hQy : Q ≤ Subgroup.centralizer ({y} : Set G))
    (hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) : Q ≤ Subgroup.normalizer (L' : Set G) := by
  obtain ⟨L₀, hL₀, hL'eq⟩ := hL'
  have hL'eq' : L' = L₀.map (Subgroup.centralizer ({y} : Set G)).subtype := hL'eq.symm
  rw [hL'eq'] at hZ hb ⊢
  exact normalizes_core hL₀ hZ hb hb3 hb1 hQ2 hQy hbQ

end CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof
