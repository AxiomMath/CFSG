module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4PartA
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Setting
public import CFSG.ClassicalGroups.Symplectic.ShortRootLineElt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.LieType.Universal.Symplectic
open TauCeti.GLSymplecticFin
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {G : Type} [Group G] {M Q Z B : Subgroup G}


theorem Ctx.exists_spin_input_of_negT
    (hNegT : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
      (N : Type) [AddCommGroup N] [Module K N] [FiniteDimensional K N]
      (BN : LinearMap.BilinForm K N)
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      4 ≤ Nat.card K → BN.IsAlt → BN.Nondegenerate → 4 ≤ finrank K N →
      ∀ (Qf : QuadraticForm K V), (∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) →
      ∀ (ρ : Gsp BN →* (V ≃ₗ[K] V)), (∀ g v, Qf (ρ g v) = Qf v) →
      ∀ (t₀ : Gsp BN), t₀ * t₀ = 1 → t₀ ≠ 1 →
      (finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0) →
      finrank K (LinearMap.range
        (((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1)) ≠ 1 →
      (finrank K N = 4 → ∃ v : N,
        BN v ((((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1) v) ≠ 0) →
      (∀ v : V, (∀ g, ρ g v = v) → v = 0) →
      commutatorSpace ρ.range = ⊤ →
      finrank K N = 6 ∧ finrank K V = 8 ∧
        ∀ U : AddSubgroup V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    [Finite G] [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {m x : ℕ} (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hK : Nat.card K = 2 ^ x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    m = 3 ∧ 4 ≤ Nat.card K ∧ finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 8 ∧
      (polarBilin (cmCommQf B φ)).Nondegenerate ∧
      ∃ (Θ : ↥(XbarH M Q Z B) →* StatedSp m K)
        (ψ : StatedSp m K →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))),
        Function.Surjective Θ ∧ (∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
        (∀ s, ψ (Θ s) = cmCommAct hc φ s) ∧
        (∀ g v, cmCommQf B φ (ψ g v) = cmCommQf B φ v) ∧
        (∀ W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ∀ w ∈ W, ψ g w ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
        ∀ r : RootSubgroupIndex m, (∀ i, r ≠ .positiveLong i) → (∀ i, r ≠ .negativeLong i) →
          ∀ c : K, c ≠ 0 → IsLongRootElement (cmCommQf B φ) (ψ (SpExtras.elt r c)) := by
  obtain ⟨-, Θ, ρV, -, hΘ, hΘk, hρV, hρQ, hC, hV, t₀, -, ht₀sq, ht₀1, hsieg, hT, hA2⟩ :=
    hc.exists_negT_input hLm ha2 hnT hD hK φ hφπ hφk hφQ
  have hq4 : 4 ≤ Nat.card K := hD.card ▸ hc.hyp.q4
  have hm2 : 2 ≤ m := (hLm.admissible).2.2.1
  have hnd := hc.cmCommQf_nondegenerate hD φ hφπ
  have hN4 : 4 ≤ finrank K (Fin m ⊕ Fin m → K) := by
    rw [finrank_spSpace]
    omega
  obtain ⟨h6, h8, hirr⟩ := hNegT K (Fin m ⊕ Fin m → K) (spForm m K)
    (cmComm M Q Z B K γ M₀ φ) hq4 spForm_isAlt spForm_nondegenerate hN4 (cmCommQf B φ) hnd ρV
    hρQ t₀ ht₀sq ht₀1 hsieg hT hA2 hC hV
  obtain ⟨h6', a₀, c₀, hac₀, hli₀, rfl⟩ := six_le_finrank_and_exists_lineElt hq4 spForm_isAlt
    spForm_nondegenerate hN4 (cmCommQf B φ) hnd ρV hρQ t₀ ht₀sq ht₀1 hsieg hT hA2
  have hs := i4Setting_of hq4 spForm_isAlt spForm_nondegenerate h6' (cmCommQf B φ) hnd ρV hρQ
    hac₀ hli₀ hsieg hC hV
  rw [finrank_spSpace] at h6
  have hpol : (polarBilin (cmCommQf B φ)).Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft fun x y hxy =>
      (polar_comm _ y x).trans hxy).mpr fun v hv => hnd v hv
  refine ⟨by omega, hq4, h8, hpol, Θ, ρV.comp (spEquiv (m := m) (K := K)).toMonoidHom, hΘ, hΘk,
    hρV, fun g v => hρQ _ v, fun W hW => ?_, fun r hr hr' c hc0 => ?_⟩
  · have hW' : ∀ g : Gsp (spForm m K), ∀ u ∈ W.toAddSubgroup, ρV g u ∈ W.toAddSubgroup := by
      intro g u hu
      simpa using hW ((spEquiv (m := m) (K := K)).symm g) u hu
    rcases hirr W.toAddSubgroup hW' with h0 | h1
    · left
      exact Submodule.toAddSubgroup_injective (h0.trans Submodule.bot_toAddSubgroup.symm)
    · right
      exact Submodule.toAddSubgroup_injective (h1.trans Submodule.top_toAddSubgroup.symm)
  · obtain ⟨a₁, b₁, hab, hli, heq⟩ := exists_lineElt_eq_spEquiv_elt r hr hr' hc0
    change IsLongRootElement (cmCommQf B φ) (ρV (spEquiv (SpExtras.elt r c)))
    rw [heq]
    exact hs.siegel a₁ b₁ hab hli

end CFSG.RankThree.GF2n.Stroth80
