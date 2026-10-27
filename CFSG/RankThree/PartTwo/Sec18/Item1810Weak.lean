module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.SylowFusion
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item1810Act
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_self {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq_self {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : g * y * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨y, hy, by simp⟩
    rwa [h] at h1
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have e : y' = y := by simpa using hyy
    exact e ▸ hy'

variable {A M H : Subgroup G} {c : G}

theorem card_dvd_nine_of_le_lc (h184 : Item184_1) (hH : Sec18H G A M H c) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hQL : Q ≤ lc H c) : Nat.card Q ∣ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := SylowFusion.nonempty_quotient_lc h184 hH
  have hf := Sec20.factorization_three_of_nonempty_quotient e
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card (lc H c) := Subgroup.card_dvd_of_le hQL
  rw [hk] at hdvd ⊢
  have hle : k ≤ (Nat.card (lc H c)).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  rw [hf] at hle
  exact (Nat.pow_dvd_pow 3 hle).trans (by norm_num)

section Certified


theorem map_conj_eq_of_mem_normalizer_zpowers (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hH : Sec18H G A M H c)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {x : G} (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hxA : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj x).toMonoidHom = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNL := normalizer_zpowers_le_normalizer_lc h1842 hH
  have hBeq : A ⊓ lc H c = A ⊓ inSubgroup perfectResidual H := inf_lc_eq h1812 h184 hH
  have hB9 : Nat.card (A ⊓ lc H c : Subgroup G) = 9 := hBeq ▸ card_inf_of_sec18H h1812 h184 hH
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ lc H c) := by
    rw [hBeq]
    exact eq_zpowers_sup_of_sec18H h1812 h184 hH
  set B := A ⊓ lc H c with hB
  set φ := (MulAut.conj x).toMonoidHom with hφ
  have hLmap : (lc H c).map φ = lc H c := map_conj_eq_self (hNL hx)
  have hcmap : (Subgroup.zpowers c).map φ = Subgroup.zpowers c := map_conj_eq_self hx
  have hB'9 : Nat.card (B.map φ) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hB9]
  have hB'L : B.map φ ≤ lc H c := by
    rw [← hLmap]
    exact Subgroup.map_mono inf_le_right
  have hB'W : B.map φ ≤ Subgroup.normalizer (A : Set G) := (Subgroup.map_mono inf_le_left).trans hxA
  have hB'N : B.map φ ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_inf hB'W (hB'W.trans (hWc.trans hNL))
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hQp : IsPGroup 3 (B.map φ ⊔ B : Subgroup G) :=
    (hBp.map φ).to_sup_of_normal_right' hBp hB'N
  have hQ9 := card_dvd_nine_of_le_lc h184 hH hQp (sup_le hB'L inf_le_right)
  have hQle : Nat.card (B.map φ ⊔ B : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) hQ9
  have hBQ : B = B.map φ ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hB9]; exact hQle)
  have hB'Q : B.map φ = B.map φ ⊔ B :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hB'9]; exact hQle)
  have hB'B : B.map φ = B := hB'Q.trans hBQ.symm
  calc A.map φ = (Subgroup.zpowers c ⊔ B).map φ := by rw [← hAeq]
    _ = (Subgroup.zpowers c).map φ ⊔ B.map φ := Subgroup.map_sup _ _ _
    _ = A := by rw [hcmap, hB'B, ← hAeq]

theorem map_conj_eq_of_le_normalizer (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h1844 : Item184_4) (hH : Sec18H G A M H c)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {g : G} (hg : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hc3 := orderOf_eq_three_of_sec18H h184 hH
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hA'C := Sec11.le_centralizer_of_le_normalizer_zpowers hc3 (hAp.map _) (hg.trans hWc)
  have hy3 : (g⁻¹ * c * g) ^ 3 = 1 := by
    have e : g⁻¹ * c * g = MulAut.conj g⁻¹ c := by simp [MulAut.conj_apply]
    rw [e, ← map_pow, pow_three_eq_one_of_sec18H hH, map_one]
  have hyA : g⁻¹ * c * g ∈ A := by
    refine Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std hy3 fun a ha => ?_
    have h1 : g * a * g⁻¹ * c = c * (g * a * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hA'C ⟨a, ha, rfl⟩)
    calc a * (g⁻¹ * c * g) = g⁻¹ * (g * a * g⁻¹ * c) * g := by group
      _ = g⁻¹ * (c * (g * a * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * c * g * a := by group
  have hmem : (Subgroup.zpowers c).map (MulAut.conj g⁻¹).toMonoidHom ∈
      conjugatesIn (Subgroup.zpowers c) A := by
    refine ⟨⟨g⁻¹, rfl⟩, ?_⟩
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hyA
  rw [h1844 G A M H c hH] at hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_of_map_conj_eq_self (hweq.trans (map_conj_eq_self (hWc hw)))
  have hgc : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    simpa using (Subgroup.normalizer _).inv_mem hginv
  exact map_conj_eq_of_mem_normalizer_zpowers h1812 h184 h1842 hH hWc hgc hg

theorem map_conj_eq_of_isPGroup (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (h1844 : Item184_4) (h1846 : Item184_6) (hH : Sec18H G A M H c)
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {R : Subgroup G} (hR : IsPGroup 3 R) (hAR : A ≤ R) {g : G}
    (hg : A.map (MulAut.conj g).toMonoidHom ≤ R) : A.map (MulAut.conj g).toMonoidHom = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  obtain ⟨P, hP, hAP⟩ := exists_isSylowOf_ge (Subgroup.le_normalizer (H := A)) hAp
  have hPG := h1846 G A M H c hH P hP
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hPG le_top hR
  have hkA : A.map (MulAut.conj k⁻¹).toMonoidHom ≤ Subgroup.normalizer (A : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hk a (hAR ha)
    change k⁻¹ * a * k⁻¹⁻¹ ∈ _
    rw [inv_inv]
    exact hP.le h1
  have hkW : k ∈ Subgroup.normalizer (A : Set G) := by
    have h1 := mem_normalizer_of_map_conj_eq_self
      (map_conj_eq_of_le_normalizer h1812 h184 h1842 h1844 hH hWc hkA)
    simpa using (Subgroup.normalizer _).inv_mem h1
  have hRW : R ≤ Subgroup.normalizer (A : Set G) := by
    intro r hr
    have h1 : k⁻¹ * r * k ∈ Subgroup.normalizer (A : Set G) := hP.le (hk r hr)
    have h2 : r = k * (k⁻¹ * r * k) * k⁻¹ := by group
    rw [h2]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hkW h1)
      ((Subgroup.normalizer _).inv_mem hkW)
  exact map_conj_eq_of_le_normalizer h1812 h184 h1842 h1844 hH hWc (hg.trans hRW)

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
