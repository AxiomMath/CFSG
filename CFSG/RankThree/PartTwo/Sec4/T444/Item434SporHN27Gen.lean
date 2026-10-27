module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporHN

theorem isElemAbelian_closure_of_comm {Y : Type*} [Group Y] {S : Set Y}
    (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (h3 : ∀ x ∈ S, x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem exists_e81_of_e27_le {G : Type*} [Group G] [Finite G] {Q R D : Subgroup G} {z : G}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D)
    (hRQ : R ≤ Q) (hR : Nat.card R * 3 = Nat.card Q)
    (hgood : ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
      ∃ g : G, g * s * g⁻¹ ∈ D ∧ g * z * g⁻¹ ∈ D)
    {P : Subgroup G} (hPQ : P ≤ Q) (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup G, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hz : z ∈ P
  ·
    have hRQ3 : R.relIndex Q = 3 := by
      have h := Subgroup.relIndex_mul_card R Q
      rw [inf_of_le_left hRQ, ← hR] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (mul_comm _ _))
    have hRP : 9 ≤ Nat.card (R ⊓ P : Subgroup G) := by
      have h := Subgroup.relIndex_mul_card R P
      have hle : R.relIndex P ≤ 3 :=
        (Subgroup.relIndex_le_of_le_right (H := R) hPQ (by rw [hRQ3]; norm_num)).trans_eq hRQ3
      have := Nat.mul_le_mul_right (Nat.card (R ⊓ P : Subgroup G)) hle
      omega
    obtain ⟨s, hsRP, hsz⟩ : ∃ s ∈ R ⊓ P, s ∉ Subgroup.zpowers z := by
      by_contra hall
      push Not at hall
      have := Subgroup.card_le_of_le (show R ⊓ P ≤ Subgroup.zpowers z from fun s hs => hall s hs)
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1] at this
      omega
    obtain ⟨hsR, hsP⟩ := Subgroup.mem_inf.mp hsRP
    have hs3 : s ^ 3 = 1 := hP.2 s hsP
    obtain ⟨g, hgs, hgz⟩ := hgood s hsR hs3 hsz
    set E := D.map (MulAut.conj g⁻¹).toMonoidHom with hE
    have hmemE : ∀ x, g * x * g⁻¹ ∈ D → x ∈ E := fun x hx =>
      ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩
    have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hDe
    have hBE : Subgroup.closure {z, s} ≤ E := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hmemE _ hgz
      · exact hmemE _ hgs
    refine ⟨Subgroup.closure {z, s}, E, ?_, ?_, hEe, ?_, ?_⟩
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hz
      · exact hsP
    · rw [Asc83Table.card_closure_pair_eq_nine hz3 hs3 (hPab _ hz _ hsP) hz1 hsz]
    · rw [hE, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hD81
    · intro b hb d hd
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨b, hBE hb⟩ ⟨d, hd⟩)
  ·
    have hQz : ∀ x ∈ (P : Set G) ∪ {z}, x ∈ Q := by
      rintro x (hx | hx)
      · exact hPQ hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact hzQ
    have hEe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ((P : Set G) ∪ {z})) := by
      refine isElemAbelian_closure_of_comm ?_ ?_
      · rintro x hx y (hy | hy)
        · rcases hx with hx | hx
          · exact hPab x hx y hy
          · rw [Set.mem_singleton_iff.mp hx]
            exact (hzc y (hPQ hy)).symm
        · rw [Set.mem_singleton_iff.mp hy]
          exact hzc x (hQz x hx)
      · rintro x (hx | hx)
        · exact hP.2 x hx
        · rw [Set.mem_singleton_iff.mp hx]
          exact hz3
    set E := Subgroup.closure ((P : Set G) ∪ {z})
    have hPE : P ≤ E := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hzE : z ∈ E := Subgroup.subset_closure (Or.inr rfl)
    refine ⟨P, E, le_rfl, by rw [hP27]; norm_num, hEe, ?_, ?_⟩
    · have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
        rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hEe.2 x x.2)⟩
      obtain ⟨k, hk⟩ := hEp.exists_card_eq
      have hdvd : 27 ∣ Nat.card E := hP27 ▸ Subgroup.card_dvd_of_le hPE
      have hne : Nat.card E ≠ 27 := by
        intro h27
        have := Subgroup.eq_of_le_of_card_ge hPE (by rw [h27, hP27])
        exact hz (this ▸ hzE)
      rw [hk] at hdvd hne ⊢
      have h3k : 3 ^ 3 ∣ 3 ^ k := by simpa using hdvd
      have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3k
      have hk4 : 4 ≤ k := by
        by_contra hlt
        exact hne (by rw [show k = 3 by omega]; norm_num)
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    · intro b hb d hd
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨b, hPE hb⟩ ⟨d, hd⟩)

theorem exists_e81_of_e27 {G : Type*} [Group G] [Finite G] {Q R D : Subgroup G} {z : G}
    (hQ : Nat.card Q = 3 ^ (Nat.card G).factorization 3)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D)
    (hRQ : R ≤ Q) (hR : Nat.card R * 3 = Nat.card Q)
    (hgood : ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
      ∃ g : G, g * s * g⁻¹ ∈ D ∧ g * z * g⁻¹ ∈ D)
    {P : Subgroup G} (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup G, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hQ hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'27 : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27]
  obtain ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ :=
    exists_e81_of_e27_le hz3 hz1 hzQ hzc hDe hD81 hRQ hR hgood
      (Item434AltPerm.map_conj_inv_le hg) hP'e hP'27
  set c := (MulAut.conj g).toMonoidHom
  refine ⟨B.map c, E.map c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Item434AltPerm.map_conj_map_conj_inv P g]
    exact Subgroup.map_mono hBP
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hB9
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hEe
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, hBE b hb d hd]

end CFSG.RankThree.PartTwo.Sec4.Item434SporHN
