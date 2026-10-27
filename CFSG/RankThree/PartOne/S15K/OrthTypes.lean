module

public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartOne.S15K.OrthBlockModel
public import CFSG.RankThree.PartOne.S15K.OrthLayer

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2 CFSG.ComponentClassification CFSG.GroupTheory.WeirSylow

variable {G : Type} [Group G] [Finite G]

theorem layerModelData_of_lifts_orth {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E I : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) (hK : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) (hq : 3 < Nat.card K)
    (hpq : p ∣ 2 ^ f - 1) (hEcard : Nat.card E = p ^ 3) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (φ : ↥I ≃* ProjOrthDerived Q) (a : ↥E → ProjOrthDerived Q) (hap : ∀ e, a e ^ p = 1)
    (hac : ∀ e : ↥E, MulAut.conj (a e) = actP φ ⟨(e : G), hEI e.2⟩)
    (hacomm : ∀ e e' : ↥E, a e * a e' = a e' * a e) (hao : ∀ e : ↥E, e ≠ 1 → orderOf (a e) = p)
    (hmul : ∀ e e' : ↥E, a (e * e') = a e * a e') : LayerModelData p E I := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := inferInstance
  intro b hb hb1
  set bE : ↥E := ⟨b, hb⟩ with hbE
  have hbne : bE ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨A, hA, hAcard, haA, habne⟩ := exists_plane_of_lifts hp hEcard a hap hacomm hmul hao bE hbne
  obtain ⟨x, Rep, n, C, -, -, -, -, hFam, hMod⟩ := exists_layerFamily_models hQ hT hdim hV hp hp5 hK
    hf1 hpq hq A hA hAcard (a bE) haA habne
  obtain ⟨Qf, h1, h2, h3, h4, hmem⟩ := layerData_clauses_of_family hp φ hEI a hap
    (compat_of_lifts φ hEI a hac) hacomm bE _ hFam
  refine ⟨_, Qf, h1, h2, h3, fun i => ?_⟩
  have hQ' : ∀ y : G, y ∈ Qf i ↔ ∃ hy : y ∈ I,
      φ.toMonoidHom ⟨y, hy⟩ ∈ (orthFamily Q (x : V ≃ₗ[K] V) Rep C i).map (MonoidHom.id _) := by
    intro y
    rw [hmem i y, Subgroup.map_id]
    rfl
  obtain ⟨e⟩ := nonempty_mulEquiv_of_transport φ.toMonoidHom φ.injective (MonoidHom.id _) hQ'
    (by rw [Subgroup.map_id]; exact fun y _ => ⟨φ.symm y, by simp⟩) (fun u _ h => h)
  exact BlockModel.of_mulEquiv e (hMod i)

section Rows

open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.LieType.Universal.Spin (quadMinus)

theorem layerModelData_of_orthMinus {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A) {f : ℕ} (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f - 1) {b c' : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c' ≠ 0)
    (φ₀ : ↥(lieGenerated p E) ≃* projOmegaMinus 3 (GaloisField 2 f) b c') :
    LayerModelData p E (lieGenerated p E) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 3 < Nat.card (GaloisField 2 f) := by
    rw [hK]
    have hpos : 0 < 2 ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have := Nat.le_of_dvd hpos hpq
    omega
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  let φ : ↥(lieGenerated p E) ≃* ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') :=
    φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c')
  have hOut := outPNice_of_projOmegaMinus
    (X := ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c')) hp (by omega) hf hbc
    (projOmegaMinusEquivOrth (GaloisField 2 f) b c').symm
  have hpI : p ∣ Nat.card (lieGenerated p E) := dvd_card_of_projOmegaMinus hf hbc φ₀ (Or.inl hpq)
  have hQ := polar_nondegenerate_quadMinus hbc
  have hT := exists_three_totSing_quadMinus (GaloisField 2 f) b c'
  have hdim : finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hV : ¬ IsPlusType (quadMinus 4 (GaloisField 2 f) b c') := not_isPlusType_quadMinus (by omega) hbc
  obtain ⟨a, hap, hac, hacomm, hao, hmul⟩ := orth_lifts h h13 hEA hQ hT hOut hpI φ
  exact layerModelData_of_lifts_orth hp h5 hQ hT hdim hV hK hf hq hpq hEcard
    (E_le_normalizer_lieGenerated hp) φ a hap hac hacomm hao hmul

theorem layerModelData_row3 {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E)
    (hout : Outcome152Three p E A (lieGenerated p E)) : LayerModelData p E (lieGenerated p E) := by
  obtain ⟨f, hf, hpq, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  exact layerModelData_of_orthMinus h h13 hEA hf hpq hbc φ₀

end Rows

end CFSG.RankThree.PartOne.S15K
