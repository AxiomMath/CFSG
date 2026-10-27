module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemWt3
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemWt12
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemA9

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open Subgroup CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec8.Item812Res12
open CFSG.Assembly.RankThreeEven (projSp)

set_option maxRecDepth 100000 in
theorem weight_cases : ∀ w : Fin 3 → ZMod 3, w ≠ 0 → ¬ (w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 2 ≠ 0) →
    (∃ k, w k ≠ 0 ∧ ∀ i, i ≠ k → w i = 0) ∨ (∃ l, w l = 0 ∧ ∀ i, i ≠ l → w i ≠ 0) := by
  decide +kernel

section Model


theorem cent_model {E Q : Subgroup H6} {v z : H6}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hv : v ∈ E) (hv1 : v ≠ 1)
    (hQv : Q ≤ Subgroup.centralizer ({v} : Set H6)) (hQ8 : Nat.card Q = 8) (hzQ : z ∈ Q)
    (hz1 : z ≠ 1) (hz : ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z) :
    ∃ g ∈ Subgroup.normalizer (E : Set H6), g * v = v * g ∧ (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
      ∃ e ∈ E, g * e * g⁻¹ ≠ e := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts_zH
  have hW := Item812Res5.card_wreathW_zH_eq_pow
  have h81 := card_wreathW_zH
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  obtain ⟨x, hx⟩ := Item812Res5.exists_map_conj_le_wreathW hW hEp
  set c : H6 →* H6 := (MulAut.conj x⁻¹).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj x⁻¹).injective
  have hcxy : ∀ y, c y = x⁻¹ * y * x := fun y => by simp [hc, MulAut.conj_apply]
  have hEA : E.map c = baseA zH :=
    eq_baseA_of_le_wreathW hf h81 hx (Item812Res5.isElemAbelian_map_hom c hE)
      (by rw [Subgroup.card_map_of_injective hcinj, hE27])
  have hvA : c v ∈ baseA zH := hEA ▸ ⟨v, hv, rfl⟩
  obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp hvA
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hv1
    apply hcinj
    rw [← hw, map_one]
    simp [vecElt]
  by_cases h3 : w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 2 ≠ 0
  ·
    obtain ⟨g', hg'N, hg'v, hg'3, e', he'A, hg'e⟩ := exists_g_wt3 h3.1 h3.2.1 h3.2.2
    set g : H6 := x * g' * x⁻¹ with hg
    have hcg : c g = g' := by
      rw [hcxy, hg]
      group
    refine ⟨g, ?_, ?_, ⟨1, ?_⟩, ?_⟩
    · refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have h1 : c e ∈ baseA zH := hEA ▸ ⟨e, he, rfl⟩
      have h2 : g' * c e * g'⁻¹ ∈ baseA zH := (Subgroup.mem_normalizer_iff.mp hg'N _).mp h1
      rw [← hEA] at h2
      obtain ⟨e₂, he₂, he₂eq⟩ := h2
      have : g * e * g⁻¹ = e₂ := by
        apply hcinj
        rw [he₂eq, map_mul c (g * e) g⁻¹, map_mul c g e, map_inv c g, hcg]
      rw [this]
      exact he₂
    · apply hcinj
      rw [map_mul c g v, map_mul c v g, hcg, ← hw]
      exact hg'v
    · apply hcinj
      rw [map_pow c g (3 ^ 1), hcg, map_one, pow_one]
      exact hg'3
    · rw [← hEA] at he'A
      obtain ⟨e, he, rfl⟩ := he'A
      refine ⟨e, he, fun h => hg'e ?_⟩
      have := congrArg c h
      rwa [map_mul c (g * e) g⁻¹, map_mul c g e, map_inv c g, hcg] at this
  ·
    exfalso
    have hx12 := weight_cases w hw0 h3
    have hQc : ∀ q ∈ Q.map c, q * vecElt zH w = vecElt zH w * q := by
      rintro _ ⟨q, hq, rfl⟩
      have hqv : q * v = v * q := Subgroup.mem_centralizer_singleton_iff.mp (hQv hq)
      rw [hw, ← map_mul, ← map_mul, hqv]
    refine no_wt12 hx12 hQc (by rw [Subgroup.card_map_of_injective hcinj, hQ8])
      (z := c z) ⟨z, hzQ, rfl⟩ (fun h => hz1 (hcinj (by rw [h, map_one]))) ?_
    rintro _ ⟨q, hq, rfl⟩ hq1
    have hq1' : q ≠ 1 := fun h => hq1 (by rw [h, map_one])
    rcases hz q hq hq1' with h | h
    · exact Or.inl (congrArg c h)
    · exact Or.inr (by rw [← map_pow, h])

end Model

section Final


theorem kF812U3Cent_holds : KF812U3Cent := by
  intro M _ _ hM E Q v hE hE27 hv hv1 hQv hQ8 ⟨z, hzQ, hz1, hz⟩
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact (a9_false e (hE.2 v hv) hv1 hQv hQ8 hzQ hz1 hz).elim
  · refine ⟨⟨e⟩, ?_⟩
    set e' : M ≃* H6 := e.trans sp62Equiv with he'
    set f : M →* H6 := e'.toMonoidHom with hf
    have hfi : Function.Injective f := e'.injective
    have hN : ∀ K : Subgroup M, Subgroup.normalizer ((K.map f : Subgroup H6) : Set H6) =
        (Subgroup.normalizer (K : Set M)).map f := fun K =>
      (Subgroup.map_equiv_normalizer_eq K e').symm
    have hEa : CFSG.Assembly.IsElemAbelian 3 (E.map f) :=
      Item812Res5.isElemAbelian_map_hom f hE
    have hQv' : Q.map f ≤ Subgroup.centralizer ({f v} : Set H6) := by
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_centralizer_singleton_iff.mp (hQv hq))
    obtain ⟨g', hg'N, hg'v, ⟨k, hk⟩, e₀', he₀'E, hg'e⟩ := cent_model hEa
      (by rw [Subgroup.card_map_of_injective hfi, hE27]) ⟨v, hv, rfl⟩
      (fun h => hv1 (hfi (by rw [h, map_one]))) hQv'
      (by rw [Subgroup.card_map_of_injective hfi, hQ8]) ⟨z, hzQ, rfl⟩
      (fun h => hz1 (hfi (by rw [h, map_one]))) (by
        rintro _ ⟨q, hq, rfl⟩ hq1
        have hq1' : q ≠ 1 := fun h => hq1 (by rw [h, map_one])
        rcases hz q hq hq1' with h | h
        · exact Or.inl (congrArg f h)
        · exact Or.inr (by rw [← map_pow, h]))
    rw [hN] at hg'N
    obtain ⟨g, hgN, rfl⟩ := hg'N
    refine ⟨g, hgN, hfi (by rw [map_mul, map_mul]; exact hg'v), ⟨k, hfi (by
      rw [map_pow, map_one]; exact hk)⟩, ?_⟩
    obtain ⟨e₀, he₀, rfl⟩ := he₀'E
    refine ⟨e₀, he₀, fun h => hg'e ?_⟩
    have := congrArg f h
    rwa [map_mul, map_mul, map_inv] at this

end Final

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
