module

public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlock
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnit_position_ne
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦) (hU : GGMemberUnitary p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
      ¬ (f = 1 ∧ (n = 4 ∨ n = 6)) ∧ GGNSLocalHyp p B Bs K f n ψ ∧ ψ.range = X ∧ GGActsDiagonally (p := 2) (f := f) ψ Bs ∧
      ∃ ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs),
        (∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
          ((((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
            ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹) ∧
        (∀ a b : Fin n, a ≠ b →
          GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) ∧
        ∀ a b : Fin n, a ≠ b →
          ggRankOneIn X Bs ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
            (ggSuPairBlock K 2 f n a b).map ψ := by
  obtain ⟨lab, K, hKf, hKfin, hKchar, f, n, ψ, hlab, hnl, hfl, hcard, hn, hker, hrange, hdvd,
      hacts, -⟩ :=
    ggNSLie_cover_of_esu_pred
      (P := fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
      (fun _ _ hh => hh) hU
  have hne : ¬ (f = 1 ∧ (n = 4 ∨ n = 6)) := fun ⟨hf1, hn46⟩ =>
    hlab.2 ⟨by rw [← hfl]; exact hf1, by omega⟩
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have h : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_nbr hcfg (hX.imp_right (hcfg.2.2.2.1.2 X)) hcard hn hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds h
  have hr : (ψ.comp (MulAut.conj c).toMonoidHom).range = X := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, hrange]
  refine ⟨K, hKf, hKfin, hKchar, f, n, ψ.comp (MulAut.conj c).toMonoidHom, hne,
    h.comp_conj c, hr, hc, ?_⟩
  rw [← hr]
  obtain ⟨ε, hε, hrefl⟩ := ggNSDiag_automizer_perm (h.comp_conj c) hc
  exact ⟨ε, hε, hrefl, fun a b hab =>
    ggNSDiag_rankOne_block (h.comp_conj c) hc a b hab _ (fun s => by
      have := hε (Equiv.swap a b) s
      rwa [Equiv.swap_inv] at this)⟩

theorem ggQTwoDUnit_position
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦) (hU : GGMemberUnitary p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
      GGNSLocalHyp p B Bs K f n ψ ∧ ψ.range = X ∧ GGActsDiagonally (p := 2) (f := f) ψ Bs ∧
      ∃ ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs),
        (∀ (σ : Equiv.Perm (Fin n)) (s : ↥Bs),
          ((((ε σ : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
            ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹) ∧
        (∀ a b : Fin n, a ≠ b →
          GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) ∧
        ∀ a b : Fin n, a ≠ b →
          ggRankOneIn X Bs ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
            (ggSuPairBlock K 2 f n a b).map ψ := by
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, -, h⟩ := ggQTwoDUnit_position_ne hcfg hX hU
  exact ⟨K, hKf, hKfin, hKchar, f, n, ψ, h⟩

theorem ggQTwoDUnit_f_eq_one {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {a b : Fin n}
    (hab : a ≠ b) (h6 : Nat.card ↥((ggSuPairBlock K 2 f n a b).map ψ) = 6) : f = 1 := by
  have hcard := ggPhanNSAPairAux_card_map_pair ψ h.card h.ker (by have := h.four_le; omega) hab
  rw [h6] at hcard
  have hq : 2 ≤ 2 ^ f := by
    by_contra hlt
    have h1 : 2 ^ f ≤ 1 := by omega
    have h2 : (2 ^ f) ^ 2 ≤ 1 := by nlinarith [Nat.zero_le (2 ^ f)]
    have h3 : 1 < Nat.card K := Finite.one_lt_card
    rw [h.card] at h3
    omega
  have heq : 2 ^ f * ((2 ^ f) ^ 2 - 1) = 2 ^ 1 * ((2 ^ 1) ^ 2 - 1) := by
    rw [← hcard]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    (ggPhanNSAPairAux_card_fun_eq hq (by norm_num) heq)

end CFSG.StandardType.QTwo

end
