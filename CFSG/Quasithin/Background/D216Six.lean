module

public import CFSG.Quasithin.Background.D2Y13
public import CFSG.Quasithin.Background.D2Z18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Six

variable {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)} {r : ℚ}

theorem d217_noncyclic_structure (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hrk : 1 < rk A) :
    r = 3 / 2 ∧ fittingOf X = pCoreOf 3 X ∧ IsElemAbelian 3 (fittingOf X) ∧ Nat.card A = 4 ∧
      X = pCoreOf 3 X ⊔ A ∧ fixV (pCoreOf 3 X) = ⊥ ∧
      ((∃ Pi : Fin 2 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
          Nat.card (fittingOf X) = 9) ∨
        (∃ Pi : Fin 3 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
          Nat.card (fittingOf X) = 27)) := by
  obtain ⟨h14A, hr, hrkall⟩ := D2_19 hV h hA hrk
  have hall := hall_of_D217 h hrkall
  have hW := fixV_pCoreOf_eq_bot hV h hall
  obtain ⟨-, hs⟩ := D2_22_structure hV h hA hrk
  have hcomm := hcomm_of_hall hV h hall
  have hexp := pCoreOf_pow_three hV (hall A hA)
  have hcardA : Nat.card A = 4 := (hall A hA).card_A hV
  rcases hs with ⟨Pi, d, hrg, hc, hXeq⟩ | ⟨Pi, d, hrg, hc, hXeq⟩
  · have hF := fittingOf_eq_pCoreOf_three hV h d hW
    refine ⟨hr, hF, ?_, hcardA, hXeq, hW, Or.inl ⟨Pi, d, hrg, ?_⟩⟩
    · rw [hF]
      exact ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩
    · rw [hF, d.card_P]
      norm_num
  · have hF := fittingOf_eq_pCoreOf_three hV h d hW
    refine ⟨hr, hF, ?_, hcardA, hXeq, hW, Or.inr ⟨Pi, d, hrg, ?_⟩⟩
    · rw [hF]
      exact ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩
    · rw [hF, d.card_P]
      norm_num

theorem Pfam_conj_of_mem_normalizer {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) {Y : Subgroup (MulAut V)}
    (hY : Y ∈ Pfam X) : conjBy g Y ∈ Pfam X := by
  obtain ⟨hYP, hYc, hYr⟩ := hY
  refine ⟨?_, by rw [card_conjBy]; exact hYc, by rw [rk_commV_conjBy]; exact hYr⟩
  intro x hx
  have h1 : g⁻¹ * x * g ∈ Y := mem_conjBy_iff.mp hx
  have h2 : g⁻¹ * x * g ∈ pCoreOf 3 X := hYP h1
  have h3 := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 3 X hg)
    (g⁻¹ * x * g)).mp h2
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h3

omit [Finite V] in
theorem isPGroup_of_card_dvd_of_odd {G : Type*} [Group G] {F : Subgroup G} {p a b : ℕ}
    (hp : p.Prime) (hodd : Odd (Nat.card F)) (hdvd : Nat.card F ∣ 2 ^ a * p ^ b) :
    IsPGroup p F := by
  have hcop : Nat.Coprime (Nat.card F) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  have h1 : Nat.card F ∣ p ^ b := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp h1
  have : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.of_card hi

theorem fitting_pgroup_of_concl (hH : D217Hyp X r) (hD : D217Concl X r) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (fittingOf X) := by
  have hodd : Odd (Nat.card (fittingOf X)) := odd_card_fittingOf hH.o2
  have hFle : Nat.card (fittingOf X) ∣ Nat.card X := Subgroup.card_dvd_of_le (fittingOf_le _)
  rcases hD with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hE, -⟩ | ⟨-, hexp, -⟩ | ⟨-, -, ⟨e⟩, -⟩ | ⟨hE, -⟩
  · refine ⟨3, Nat.prime_three, by norm_num, isPGroup_of_card_dvd_of_odd (a := 1) (b := 1)
      Nat.prime_three hodd ?_⟩
    rw [card_of_dihedral ⟨e⟩] at hFle
    simpa using hFle
  · refine ⟨5, Nat.prime_five, by norm_num, isPGroup_of_card_dvd_of_odd (a := 1) (b := 1)
      Nat.prime_five hodd ?_⟩
    rw [card_of_dihedral ⟨e⟩] at hFle
    simpa using hFle
  · exact ⟨3, Nat.prime_three, by norm_num, fun a => ⟨1, Subtype.ext (by
      simpa using hE.2 (a : MulAut V) a.2)⟩⟩
  · exact ⟨3, Nat.prime_three, by norm_num, fun a => ⟨1, Subtype.ext (by
      simpa using hexp (a : MulAut V) a.2)⟩⟩
  · refine ⟨3, Nat.prime_three, by norm_num, isPGroup_of_card_dvd_of_odd (a := 2) (b := 2)
      Nat.prime_three hodd ?_⟩
    have hc : Nat.card X = 36 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      have : Nat.card (DihedralGroup 3) = 6 := by
        rw [Nat.card_eq_fintype_card, DihedralGroup.card]
      rw [this]
    rw [hc] at hFle
    simpa using hFle
  · exact ⟨3, Nat.prime_three, by norm_num, fun a => ⟨1, Subtype.ext (by
      simpa using hE.2 (a : MulAut V) a.2)⟩⟩

end Six

end CFSG.Quasithin
