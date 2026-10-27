module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCom
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.J1Props.Extra
public import CFSG.Walter.Models
public import CFSG.Adapters.Certificate43Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup CFSG.Walter.J1Props

theorem s1667_kg_j1_equiv {J : Type} [Group J]
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic J .J1) :
    Nonempty (J ≃* walterJ1) := by
  obtain ⟨e0⟩ := hj1
  exact ⟨e0.trans CFSG.Walter.walterJ1EquivNative.symm⟩

theorem s1667_kg_j1_not_four_dvd_card_centralizer {y : walterJ1} (hy : orderOf y = 3) :
    ¬ 4 ∣ Nat.card (centralizer ({y} : Set walterJ1)) := by
  haveI := CFSG.Adapters.certificate43_holds
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h4
  have hP : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hy]
  let S : Sylow 3 walterJ1 :=
    (IsPGroup.of_card (n := 1) (by rw [hP]; norm_num) : IsPGroup 3 (zpowers y)).toSylow
      (not_dvd_index_of_card (Or.inl rfl) hP)
  have hS : (S : Subgroup walterJ1) = zpowers y := rfl
  have h2 := J2_normalizer_two_part (p := 3) (Or.inl rfl) S
  rw [hS] at h2
  obtain ⟨-, hdvd, -⟩ := isCyclic_normQuot (p := 3) (zpowers y) hP
  have hNC := card_normalizer_eq_mul (zpowers y)
  rw [centralizer_zpowers_eq] at hNC
  obtain ⟨s, -, hs⟩ := J2_inverted (p := 3) (by norm_num) S
  have hsy : s * y * s⁻¹ = y⁻¹ := hs y (by rw [hS]; exact mem_zpowers y)
  have hsN : s ∈ normalizer ((zpowers y : Subgroup walterJ1) : Set walterJ1) :=
    s1667_kg_mem_normalizer_zpowers_of_inv hsy
  have hq1 : Nat.card (normQuot (zpowers y)) ≠ 1 := by
    intro h1
    have hidx : ((centralizer ((zpowers y : Subgroup walterJ1) : Set walterJ1)).subgroupOf
        (normalizer ((zpowers y : Subgroup walterJ1) : Set walterJ1))).index = 1 := by
      rw [Subgroup.index_eq_card]
      exact h1
    have htop := Subgroup.index_eq_one.mp hidx
    have hsmem : (⟨s, hsN⟩ : normalizer ((zpowers y : Subgroup walterJ1) : Set walterJ1)) ∈
        (centralizer ((zpowers y : Subgroup walterJ1) : Set walterJ1)).subgroupOf
          (normalizer ((zpowers y : Subgroup walterJ1) : Set walterJ1)) := by
      rw [htop]
      trivial
    rw [Subgroup.mem_subgroupOf] at hsmem
    have hsc : s * y = y * s := mem_centralizer_zpowers_iff.mp hsmem
    have hyy : y⁻¹ = y := by rw [← hsy, hsc]; group
    have hy3 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    have hy1 : y = 1 := by
      have h22 : y * y = 1 := by
        calc y * y = y⁻¹ * y := by rw [hyy]
          _ = 1 := inv_mul_cancel y
      calc y = y ^ 3 := by rw [pow_succ, pow_two, h22, one_mul]
        _ = 1 := hy3
    rw [hy1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hq2 : Nat.card (normQuot (zpowers y)) = 2 := by
    have hd2 : Nat.card (normQuot (zpowers y)) ∣ 2 := by simpa using hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact absurd h hq1
    · exact h
  rw [hq2] at hNC
  have hC0 : Nat.card (centralizer ({y} : Set walterJ1)) ≠ 0 := Nat.card_pos.ne'
  rw [hNC, Nat.factorization_mul (by norm_num) hC0] at h2
  have h2' : 1 + (Nat.card (centralizer ({y} : Set walterJ1))).factorization 2 = 2 := by
    simpa [Nat.Prime.factorization_self Nat.prime_two] using h2
  have h4' : 2 ≤ (Nat.card (centralizer ({y} : Set walterJ1))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).mp (by simpa using h4)
  omega

theorem s1667_kg_j1_aut_mem_range {J : Type} [Group J]
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic J .J1) (α : MulAut J) :
    α ∈ (MulAut.conj : J →* MulAut J).range := by
  haveI := CFSG.Adapters.certificate43_holds
  obtain ⟨e⟩ := s1667_kg_j1_equiv hj1
  obtain ⟨g, hg⟩ := J3_aut (MulAut.congr e α)
  refine ⟨e.symm g, ?_⟩
  ext y
  apply e.injective
  have h := congrArg (fun φ : MulAut walterJ1 => φ (e y)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h.symm

theorem s1667_kg_j1_exists_inverting {J : Type} [Group J]
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic J .J1) {x : J} (hx : orderOf x = 3) :
    ∃ s : J, s ^ 2 = 1 ∧ s * x * s⁻¹ = x⁻¹ := by
  haveI := CFSG.Adapters.certificate43_holds
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := s1667_kg_j1_equiv hj1
  have hy : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hP : Nat.card (zpowers (e x)) = 3 := by rw [Nat.card_zpowers, hy]
  let S : Sylow 3 walterJ1 :=
    (IsPGroup.of_card (n := 1) (by rw [hP]; norm_num) : IsPGroup 3 (zpowers (e x))).toSylow
      (not_dvd_index_of_card (Or.inl rfl) hP)
  obtain ⟨t, ht2, ht⟩ := J2_inverted (p := 3) (by norm_num) S
  have hty : t * e x * t⁻¹ = (e x)⁻¹ := ht (e x) (mem_zpowers (e x))
  refine ⟨e.symm t, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  · apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hty

theorem s1667_kg_j1_comm_two {J : Type} [Group J]
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic J .J1) :
    ∀ P : Subgroup J, IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨e⟩ := s1667_kg_j1_equiv hj1
  intro P hP a ha b hb
  obtain ⟨S, hS⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have hcomm := CFSG.Walter.J1Props.hasAbelianSylowTwo S
  have h1 : e a ∈ (S : Subgroup walterJ1) := hS ⟨a, ha, rfl⟩
  have h2 : e b ∈ (S : Subgroup walterJ1) := hS ⟨b, hb, rfl⟩
  have h3 := congrArg Subtype.val (hcomm.is_comm.comm ⟨e a, h1⟩ ⟨e b, h2⟩)
  apply e.injective
  simpa using h3

theorem k67BPrimeOneAt_j1 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥)
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic ↥J .J1) : K67BPrimeOneAt Q J := by
  haveI := hJ
  intro x hxJ hx3 A hA hAx _ h4
  exfalso
  have hQJ : ∀ q : Q, q ∈ J := fun q =>
    (s1667_kg_mem_iff_conjNormal_mem_range J hC q).mpr (s1667_kg_j1_aut_mem_range hj1 _)
  have hAJ : A ≤ J := fun a _ => hQJ a
  obtain ⟨e⟩ := s1667_kg_j1_equiv hj1
  let x' : ↥J := ⟨x, hxJ⟩
  have hx'3 : orderOf (e x') = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe x').symm.trans hx3
  let A' : Subgroup walterJ1 := (A.subgroupOf J).map e.toMonoidHom
  have hcardA' : Nat.card A' = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv
  have hA'C : A' ≤ centralizer ({e x'} : Set walterJ1) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (a : Q) * x = x * (a : Q) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hAx (Subgroup.mem_subgroupOf.mp ha))
    have h2 : a * x' = x' * a := Subtype.ext h1
    change e a * e x' = e x' * e a
    rw [← map_mul, ← map_mul, h2]
  have hdvd : 4 ∣ Nat.card (centralizer ({e x'} : Set walterJ1)) :=
    (hcardA' ▸ s1667_kg_four_dvd_card hA h4).trans (Subgroup.card_dvd_of_le hA'C)
  exact s1667_kg_j1_not_four_dvd_card_centralizer hx'3 hdvd

theorem k67CaseIIIAt_j1 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥)
    (hj1 : CFSG.Blueprint.NativeSporadic.IsSporadic ↥J .J1) : K67CaseIIIAt Q J := by
  haveI := hJ
  intro x hxJ hx3 E _ hE4 hEJ hEx W _ _ _ _ hN
  let x' : ↥J := ⟨x, hxJ⟩
  have hx'3 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
  obtain ⟨s', hs'2, hs'x⟩ := s1667_kg_j1_exists_inverting hj1 hx'3
  have hsx : (s' : Q) * x * (s' : Q)⁻¹ = x⁻¹ := congrArg Subtype.val hs'x
  have hs2 : (s' : Q) ^ 2 = 1 := by simpa using congrArg Subtype.val hs'2
  have hsmem : (s' : Q) ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) :=
    s1667_kg_mem_normalizer_zpowers_of_inv hsx
  have hxmem : x ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers x)
  exact s1667_kg_false_of_inverting_involution
    (s1667_kg_comm_of_le J (s1667_kg_j1_comm_two hj1)) hx3 hs2 s'.2 hsx hE4 hEJ hEx
    (hN x hxmem).1 (hN _ hsmem).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
