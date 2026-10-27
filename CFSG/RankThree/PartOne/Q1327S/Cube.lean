module

public import CFSG.RankThree.PartOne.CTP.StrongPLinear

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne

variable {Q : Type} [Group Q] [Finite Q]

theorem commutative_of_card_cube {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : Nat.card P = p ^ 3) (Z : Subgroup P) (hZ : Z ≤ Subgroup.center P)
    (hZc : Nat.card Z = p ^ 2) : ∀ a b : P, a * b = b * a := by
  have h1 : Nat.card Z ∣ Nat.card (Subgroup.center P) := Subgroup.card_dvd_of_le hZ
  obtain ⟨m, hm⟩ := h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
  have h3 : Nat.card (P ⧸ Subgroup.center P) ∣ p := by
    refine ⟨m, ?_⟩
    have : p ^ 3 = Nat.card (P ⧸ Subgroup.center P) * (p ^ 2 * m) := by
      rw [← hP, h2, hm, hZc]
    have hp2 : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    have : p ^ 2 * p = p ^ 2 * (Nat.card (P ⧸ Subgroup.center P) * m) := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = _ := this
        _ = p ^ 2 * (Nat.card (P ⧸ Subgroup.center P) * m) := by ring
    exact Nat.eq_of_mul_eq_mul_left hp2 this
  have hcyc : IsCyclic (P ⧸ Subgroup.center P) := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h3 with h | h
    · have : Subsingleton (P ⧸ Subgroup.center P) := (Nat.card_eq_one_iff_unique.1 h).1
      infer_instance
    · exact isCyclic_of_prime_card (p := p) h
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center P)) (by simp [QuotientGroup.ker_mk'])
  exact fun a b => hcomm.is_comm.comm a b

theorem false_of_noncomm_cube {p : ℕ} (hp : p.Prime) {Ē : Subgroup Q}
    (hEcard : Nat.card Ē = p ^ 2) (hX3 : p ^ 3 ∣ Nat.card Q) (hX4 : ¬ p ^ 4 ∣ Nat.card Q)
    (hN : StrongP.HasNoncommPair p Q)
    (hcen : ∀ P : Subgroup Q, IsPGroup p P → Ē ≤ P → P ≤ Subgroup.centralizer (Ē : Set Q)) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have hX0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card Q).factorization p = 3 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp hX0).1 hX3
    have h2 : ¬ 4 ≤ (Nat.card Q).factorization p := fun h =>
      hX4 ((Nat.Prime.pow_dvd_iff_le_factorization hp hX0).2 h)
    omega
  have hEp : IsPGroup p Ē := IsPGroup.of_card hEcard
  obtain ⟨PE, hEPE⟩ := hEp.exists_le_sylow
  have hPEcard : Nat.card PE = p ^ 3 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hPEc : (PE : Subgroup Q) ≤ Subgroup.centralizer (Ē : Set Q) :=
    hcen PE PE.isPGroup' hEPE
  set Z : Subgroup PE := Ē.subgroupOf PE with hZ
  have hZc : Z ≤ Subgroup.center PE := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzE : (z : Q) ∈ Ē := Subgroup.mem_subgroupOf.1 hz
    have := Subgroup.mem_centralizer_iff.1 (hPEc w.2) (z : Q) hzE
    exact this.symm
  have hZcard : Nat.card Z = p ^ 2 := by
    rw [hZ, ← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEPE).toEquiv
  have hPEcomm : ∀ a b : PE, a * b = b * a :=
    commutative_of_card_cube (p := p) hPEcard Z hZc hZcard
  obtain ⟨x, y, hx, hy, hxy, hH⟩ := hN
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q PE P
  have hxP : x ∈ (P : Subgroup Q) := hHP (Subgroup.subset_closure (by simp))
  have hyP : y ∈ (P : Subgroup Q) := hHP (Subgroup.subset_closure (by simp))
  rw [← hg, Sylow.coe_subgroup_smul] at hxP hyP
  have e1 : (MulAut.conj g)⁻¹ • x ∈ PE := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hxP
  have e2 : (MulAut.conj g)⁻¹ • y ∈ PE := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hyP
  have key : ((MulAut.conj g)⁻¹ • x) * ((MulAut.conj g)⁻¹ • y) =
      ((MulAut.conj g)⁻¹ • y) * ((MulAut.conj g)⁻¹ • x) :=
    congrArg Subtype.val (hPEcomm ⟨_, e1⟩ ⟨_, e2⟩)
  simp only [MulAut.smul_def] at key
  rw [← map_mul, ← map_mul] at key
  exact hxy ((MulAut.conj g)⁻¹.injective key)

end CFSG.RankThree.PartOne.Q1327S
