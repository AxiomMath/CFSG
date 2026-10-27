module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofJCent
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def TwoLocalThree (D : Type*) [Group D] : Prop :=
  NoThetaNormal D ∧ ∃ (y : D) (T : Subgroup D), y ^ 3 = 1 ∧ y ∉ Subgroup.center D ∧ T ≠ ⊥ ∧
    IsPGroup 2 T ∧ y ∈ Subgroup.normalizer (T : Set D)

theorem TwoLocalThree.of_mulEquiv {D D' : Type*} [Group D] [Group D'] (e : D ≃* D')
    (h : TwoLocalThree D') : TwoLocalThree D := by
  obtain ⟨hθ, y, T, hy3, hyZ, hT1, hT2, hyT⟩ := h
  refine ⟨Item87Proof.NoThetaNormal.of_mulEquiv e hθ, e.symm y, T.map e.symm.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hy3, map_one]
  · intro hz
    apply hyZ
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h1 := hz (e.symm g)
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h1
  · intro h0
    apply hT1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h0
  · exact hT2.map _
  · rw [Subgroup.mem_normalizer_iff] at hyT ⊢
    intro z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨y * t * y⁻¹, (hyT t).mp ht, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨t, ht, hte⟩
      have hz : z = e.symm (y⁻¹ * t * y) := by
        apply e.injective
        have h1 : e.symm t = e.symm y * z * (e.symm y)⁻¹ := hte
        have h2 : t = y * e z * y⁻¹ := by
          apply e.symm.injective
          rw [h1]
          simp [map_mul, map_inv]
        rw [MulEquiv.apply_symm_apply, h2]
        group
      refine ⟨y⁻¹ * t * y, ?_, hz.symm⟩
      have := (hyT (y⁻¹ * t * y)).mpr (by rwa [show y * (y⁻¹ * t * y) * y⁻¹ = t by group])
      exact this


@[expose] def KF89G2TwoLocal : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 ^ m →
    TwoLocalThree (perfectResidual (adjointGroup .G2 k))

@[expose] def KF89Sp4TwoLocal : Prop :=
  ∀ (m : ℕ), 1 ≤ m → TwoLocalThree (perfectResidual (projSp 2 (GaloisField 2 m)))

@[expose] def KF89ReeTwoLocal : Prop :=
  ∀ (b : ℕ) (k : Type) [Field k] [Finite k] [CharP k ReeTag.F4.prime],
    Nat.card k = 2 ^ (2 * b + 1) → TwoLocalThree (perfectResidual (ReeTag.F4.reeGamma k b))


open Item812Res8

theorem kF89JTwoLocal_of (h84 : Pair84A) (hG : KF89G2TwoLocal) (hS : KF89Sp4TwoLocal)
    (hR : KF89ReeTwoLocal) : KF89JTwoLocal := by
  intro G _ _ A c L a b X n h
  have hk := h84 G A c L a b X n h
  have haN : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk with hk | hk
    · exact hk.mem_normalizer
    · exact hk.mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout : InducesOuterTheta a X := by
    rcases hk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨-, -, -, -, -, e', m, hem⟩ := h.mem_pairOmega
  have hm : 1 ≤ m := hem.2.2.1
  have htype := Item87Proof.isGammaType_of_isGammaIndex hem
  have hM : TwoLocalThree (perfectResidual (barCentralizer (Subgroup.zpowers a) X)) := by
    rcases htype with ⟨k, hk', hkm, ⟨e₀⟩⟩ | hD | ⟨q, hq2, hqe, hG2⟩ | hU | hSU | hSp
    ·
      have hRm := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
      obtain ⟨-, k₁, hk₁, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRm
      obtain ⟨b', k'', _, _, _, hk'', -, ⟨φ⟩⟩ :=
        exists_barCentralizer_mulEquiv_reeGamma' hk₁ hK (e₀.trans e₁) ha3 hout
      exact TwoLocalThree.of_mulEquiv (perfectResidualCongr φ) (hR b' k'' hk'')
    ·
      obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := h.gTwoPartner m (Or.inl hD)
      exact TwoLocalThree.of_mulEquiv (perfectResidualCongr φ) (hG m hm k hk)
    ·
      obtain ⟨k, _, _, hk, ⟨φ⟩⟩ :=
        h.gTwoPartner m (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG2))
      exact TwoLocalThree.of_mulEquiv (perfectResidualCongr φ) (hG m hm k hk)
    · exact (h.not_unitary (3 * m) (Or.inl hU)).elim
    · exact (h.not_unitary (3 * m) (Or.inr hSU)).elim
    ·
      obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := m) (by omega) ha3 hout hSp
      exact TwoLocalThree.of_mulEquiv (perfectResidualCongr ι) (hS m hm)
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq haN
    ⟨1, by rw [pow_one]; exact ha3⟩
  have hI : TwoLocalThree (imageModTheta X (sec8J X a)) := by
    have e₂ : imageModTheta X (sec8J X a) ≃*
        perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
      (MulEquiv.subgroupCongr himg).trans (inSubgroupPerfectResidualEquiv _)
    exact TwoLocalThree.of_mulEquiv e₂ hM
  have hJX : sec8J X a ≤ X := Subgroup.map_subtype_le _ |>.trans inf_le_left
  obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hJX hI.1
  obtain ⟨-, y, T, hy3, hyZ, hT1, hT2, hyT⟩ := TwoLocalThree.of_mulEquiv ψ hI
  exact ⟨y, T, hy3, hyZ, hT1, hT2, hyT⟩

end CFSG.RankThree.PartTwo.Sec8
