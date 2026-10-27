module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFin1
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmADefs
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmALift

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem model_of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K) {n p f : ℕ}
    (h : StatedClassicalModel K .PSL n p f) : StatedClassicalModel H .PSL n p f := by
  obtain ⟨hadm, F, hF, hFin, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, F, hF, hFin, hcard, ⟨e.trans e'⟩⟩

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Kπ (N K : Subgroup G) : ↥(K.subgroupOf (OppE 3 N)) →* LayerQ N :=
  (Lπ N).comp (K.subgroupOf (OppE 3 N)).subtype

theorem model_image {N K : Subgroup G} (hKL : K ≤ OppE 3 N)
    (hK : StatedClassicalModel K .PSL 2 2 2) :
    StatedClassicalModel (Kπ N K).range .PSL 2 2 2 := by
  have hinj : Function.Injective (Kπ N K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Lπ N (x : ↥(OppE 3 N)) = 1 := hx
    have h2 := (Lπ_eq_one_iff N _).mp h1
    have hKN : K ≤ N := hKL.trans (OppE_le N)
    have h3 : (x : G) ∈ K ⊓ Opp 3 N := ⟨x.2, h2⟩
    rw [inf_opp_eq_bot_of_l24 hKN hK] at h3
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3
  exact model_of_mulEquiv
    ((MonoidHom.ofInjective hinj).symm.trans (Subgroup.subgroupOfEquivOfLe hKL)) hK

theorem exists_fixed_square (hL34a : FF79KL34a) {b : G} (hb : b ^ 3 = 1)
    {U₁ U₂ : Subgroup G} (hU₁ : Nat.card U₁ = 9) (hbU₁ : b ∈ Nor U₁) (hbU₂ : b ∈ Nor U₂)
    (hU₁L : U₁ ≤ OppE 3 (CenS U₂))
    (hmodel : StatedClassicalModel (LayerQ (CenS U₂)) .PSL 3 2 2)
    (hK : StatedClassicalModel (OUpp 2 (OppE 3 (CenS U₂) ⊓ Cen b)) .PSL 2 2 2)
    (hodd : Odd (Nat.card (Opp 3 (CenS U₂)))) :
    ∃ p ∈ OppE 3 (CenS U₂), p ∈ Nor U₁ ∧ p ^ 4 = 1 ∧ p ^ 2 ≠ 1 ∧
      b * p ^ 2 * b⁻¹ = p ^ 2 := by
  set N := CenS U₂ with hN
  have hbN : b ∈ Nor N := nor_cenS_of_nor hbU₂
  have hbL : b ∈ Nor (OppE 3 N) := nor_OppE_of_nor hbN
  have hU3 : IsPGroup 3 U₁ := IsPGroup.of_card (n := 2) (by rw [hU₁]; norm_num)
  set β : MulAut (LayerQ N) := actE N ⟨b, hbN⟩ with hβdef
  have hβ3 : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow]
    have : (⟨b, hbN⟩ : ↥(Nor N)) ^ 3 = 1 := Subtype.ext hb
    rw [this, map_one]
  have hβl : ∀ (l l' : ↥(OppE 3 N)), (l' : G) = b * l * b⁻¹ → β (Lπ N l) = Lπ N l' :=
    fun l l' h => actE_Lπ N ⟨b, hbN⟩ l l' h
  have hconjmem : ∀ (l : G), l ∈ OppE 3 N → b * l * b⁻¹ ∈ OppE 3 N := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hbL l).mp hl
  have hS9 : Nat.card (Uπ hU₁L).range = 9 := (card_range_Uπ hU3 hU₁L).trans hU₁
  have hSb : ∀ s ∈ (Uπ hU₁L).range, β s ∈ (Uπ hU₁L).range := by
    rintro _ ⟨u, rfl⟩
    have hu' : b * (u : G) * b⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp hbU₁ u).mp u.2
    refine ⟨⟨b * u * b⁻¹, hu'⟩, ?_⟩
    exact (hβl (Subgroup.inclusion hU₁L u) _ rfl).symm
  have hKle : OUpp 2 (OppE 3 N ⊓ Cen b) ≤ OppE 3 N := (OUpp_le 2 _).trans inf_le_left
  have hKfix : ∀ x ∈ (Kπ N (OUpp 2 (OppE 3 N ⊓ Cen b))).range, β x = x := by
    rintro _ ⟨k, rfl⟩
    have hkc : (k : G) ∈ Cen b :=
      (OUpp_le 2 _ (show ((k : ↥(OppE 3 N)) : G) ∈ OUpp 2 (OppE 3 N ⊓ Cen b) from k.2)).2
    have hcomm : b * (k : G) * b⁻¹ = (k : G) := by
      have := Subgroup.mem_centralizer_iff.mp hkc b (Set.mem_singleton b)
      rw [this]; simp
    have := hβl (k : ↥(OppE 3 N)) (k : ↥(OppE 3 N)) hcomm.symm
    exact this
  obtain ⟨q, hqS, hβq, hq2, hq4⟩ := hL34a (LayerQ N) hmodel β hβ3 _ hS9 hSb
    ⟨_, model_image hKle hK, hKfix⟩
  obtain ⟨y, rfl⟩ := Lπ_surjective N q
  have hker : Nat.card (Lπ N).ker = Nat.card (Opp 3 N) := Nat.card_congr (kerLπEquiv N)
  refine ff79_lift_square hU₁L hU3 (Lπ N) (by rw [hker]; exact hodd)
    (by
      have := coprime_three_card_ker N
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp this) hb hbL hbU₁ β.toMonoidHom
    (fun l hl hl' => (hβl ⟨l, hl⟩ ⟨_, hl'⟩ rfl).symm) ⟨y, rfl⟩ ?_ hβq hq2 hq4
  intro u hu
  obtain ⟨u'', h⟩ := hqS _ ⟨⟨u, hu⟩, rfl⟩
  exact ⟨u'', u''.2, h.symm⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
