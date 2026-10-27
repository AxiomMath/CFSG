module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmKFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.ClassicalGroups.Orthogonal.IsometryConj
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGInnerDiagOnLabel.exists_twD_field_of_nonsplit
    {G : Type} [Group G] {p n : ℕ} {Bs L : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L) :
    ∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ Even n ∧
      GGInnerDiagOnLabel (fun p lab => lab = ⟨.twD, n, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, -, I, F, -, -, θ, ⟨hB, hf1, ht, hpq⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hf : 2 ≤ lab.n := by
    have hpos : 1 ≤ lab.n := hlab.1
    omega
  have hBn : lab.rank = n ∧
      (p ∣ 2 ^ lab.n - 1 ∨ Even n ∧ p ∣ 2 ^ lab.n + 1) := by
    simpa [GGSecFiveBCoordBLabel, ht] using hB
  have hev : Even n := by
    rcases hBn.2 with hm | ⟨hev, -⟩
    · exfalso
      have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
      have h2 : p ∣ 2 := by
        refine (Nat.dvd_add_right hm).mp ?_
        rwa [show 2 ^ lab.n - 1 + 2 = 2 ^ lab.n + 1 by omega]
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hev
  have heq : lab = ⟨.twD, n, lab.n⟩ := by
    rcases lab with ⟨t, r, f⟩
    dsimp at ht hBn ⊢
    subst t
    have hr : r = n := hBn.1
    subst r
    rfl
  have hrow : GGTBRowR5O1 p lab := by
    refine ⟨ht, ?_, ?_⟩
    · rw [hBn.1]
      exact hn
    · rw [hBn.1]
      exact hBn.2
  refine ⟨lab.n, hf, hpq, hev, hperf, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, -, hBsN, hind⟩
  exact ⟨hs, hna, θ, ⟨heq, hrow⟩, hBsN, hind⟩

theorem GGConfig.exists_omKFrame_of_twDNonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hB : B = Bs) {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {i0 : Fin n}
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L) :
    Even n ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)),
        2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ UnitaryFieldData 2 f K ∧
        ∃ π : Fin (n - 1 + 1) ≃ Fin n, π (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π κ χ := by
  classical
  have hp : p.Prime := hcfg.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨f, hf, hpq, hev, hL'⟩ := GGInnerDiagOnLabel.exists_twD_field_of_nonsplit hp hp2 hn hL
  obtain ⟨F, fieldF, finiteF, -, b, c, hF, hbc, -, hN, -, -, -, σ, -, Θ,
    -, -, hΘ, -, -, -, -, hZL, χL, -⟩ :=
    ggTBJOrthLeft_nativeModel_of_twD hcfg hB.symm hn hf hLB hL'
  letI : Field F := fieldF
  letI : Finite F := finiteF
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite (GaloisField 2 f)
  let φ : F ≃+* GaloisField 2 f :=
    FiniteField.ringEquivOfCardEq (K := F) (K' := GaloisField 2 f) (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card 2 f (by omega)])
  have hUF : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 (2 * f) (by omega)⟩
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := galoisAlgebra hUF
  have E : QuadExt (GaloisField 2 f) (GaloisField 2 (2 * f))
      (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) := galoisQuadExt hUF
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hirr : ∀ s : GaloisField 2 f, s ^ 2 + φ b * s + φ c ≠ 0 := by
    intro s hs
    apply hbc (φ.symm s)
    apply φ.injective
    rw [map_zero, ← hs]
    simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply]
  obtain ⟨eV⟩ := nonempty_normOmega_mulEquiv_minus E hodd hirr
  let eF : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (n - 1 + 1) F b c) ≃*
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (n - 1 + 1) (GaloisField 2 f) (φ b) (φ c)) :=
    ((CFSG.Adapters.RankTwoModelTransports.glCongr
        (ι := Fin (n - 1 + 1 - 1) ⊕ Fin (n - 1 + 1 - 1) ⊕ Fin 2) φ).subgroupMap
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (n - 1 + 1) F b c))).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl)))
  let e : ↥L ≃* normOmega E (n - 1) :=
    χL.symm.trans ((CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr
      (TableBOrth.qMinusIsometry (n - 1) b c)).trans
      ((CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
        (Q := CFSG.LieType.Universal.Spin.quadMinus (n - 1 + 1) F b c)
        (CFSG.LieType.Universal.Spin.coe_quadMinus (n - 1 + 1) F b c)).symm.trans
        (eF.trans eV.symm)))
  have hinner : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ := by
    intro b hb
    obtain ⟨⟨w, c⟩, hwc⟩ := Θ.surjective ⟨b, hb⟩
    refine ⟨(σ w : G), (σ w).2, fun k hk => ?_⟩
    have hb' : b = (σ w : G) * (c : G) := by
      rw [← hΘ w c, hwc]
    have hck : (c : G) * k = k * (c : G) :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 k hk).symm
    calc b * k * b⁻¹ = (σ w : G) * ((c : G) * k) * (c : G)⁻¹ * (σ w : G)⁻¹ := by
          rw [hb']
          group
      _ = (σ w : G) * (k * (c : G)) * (c : G)⁻¹ * (σ w : G)⁻¹ := by rw [hck]
      _ = (σ w : G) * k * (σ w : G)⁻¹ := by group
  obtain ⟨π, hπ, κ, χ, hframe⟩ := ggSecFiveBPermOmK_exists_frame_of_inner hp2 E hUF hpq
    (by omega : 3 ≤ n - 1) (by omega : n = n - 1 + 1) hcfg.2.1 hinner e eta hLB
  exact ⟨hev, hZL, hN, f, GaloisField 2 (2 * f), inferInstance, galoisAlgebra hUF,
    inferInstance, inferInstance, E, hf, hpq, hUF, π, hπ, κ, χ, hframe⟩

theorem GGSecFiveRouteCfg.exists_omKFrames_of_twDNonsplit {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {Q : Prop} (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (Q ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L) :
    Even n ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)),
        2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ UnitaryFieldData 2 f K ∧
        ∃ π : Fin (n - 1 + 1) ≃ Fin n, π (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π κ χ ∧
            ∀ {y : G} (hy : y ∈ Bs) {K' : Subgroup G} {j : Fin n},
              GGNbr p B x D J y K' → j ≠ i0 → (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) →
              ((ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom =
                  bCoordinateBlock n p j ∨
                (ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom =
                  dCoordinateBlock n p j) →
              ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
                w ∈ ggG0 p B x L D J ∧
                MulAut.congr eta (ggConjAut Bs hw) =
                  SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
                K' = L.map (MulAut.conj w).toMonoidHom ∧
                (ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom =
                  bCoordinateBlock n p j ∧
                (π.trans (Equiv.swap i0 j)) (Fin.last (n - 1)) = j ∧
                GGSecFiveBPermOmKFrame E Bs K' eta (π.trans (Equiv.swap i0 j))
                  ((MulAut.conj w).toMonoidHom.comp κ) χ := by
  have hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hP.1.2.2⟩, hP.2⟩) hLab
  obtain ⟨hev, hZL, hN, f, K, fieldK, algK, finK, charK, E, hf, hpq, hUF, π, hπ, κ, χ,
    hframe⟩ := GGConfig.exists_omKFrame_of_twDNonsplit hR.1.1 hB hn eta hLB hL
  refine ⟨hev, hZL, hN, f, K, fieldK, algK, finK, charK, E, hf, hpq, hUF, π, hπ, κ, χ,
    hframe, ?_⟩
  intro y hy K' j hnb hj hyj hAK
  obtain ⟨w, hw, hwG0, hact, hKw, hAKB⟩ :=
    hR.exists_ggG0_eq_map_conj_swap_of_sparse hB hn eta i0 hEta hLB hy hnb hj hyj hAK
  refine ⟨w, hw, hwG0, hact, hKw, hAKB, ?_, ?_⟩
  · rw [Equiv.trans_apply, hπ, Equiv.swap_apply_left]
  · rw [hKw]
    exact hframe.conj_transporter hw hact

theorem GGSecFiveRouteCfg.exists_omKFrames_of_twDNonsplit_of_bCoordSparse
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {Q : Prop} (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (Q ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    Even n ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)),
        2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ UnitaryFieldData 2 f K ∧
        ∃ π : Fin (n - 1 + 1) ≃ Fin n, π (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π κ χ ∧
            ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
              ∃ (hy : y ∈ Bs) (j : Fin n), j ≠ i0 ∧ (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∧
                ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
                  w ∈ ggG0 p B x L D J ∧
                  MulAut.congr eta (ggConjAut Bs hw) =
                    SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
                  K' = L.map (MulAut.conj w).toMonoidHom ∧
                  (ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom =
                    bCoordinateBlock n p j ∧
                  (π.trans (Equiv.swap i0 j)) (Fin.last (n - 1)) = j ∧
                  GGSecFiveBPermOmKFrame E Bs K' eta (π.trans (Equiv.swap i0 j))
                    ((MulAut.conj w).toMonoidHom.comp κ) χ := by
  obtain ⟨hev, hZL, hN, f, K, fieldK, algK, finK, charK, E, hf, hpq, hUF, π, hπ, κ, χ,
    hframe, hnbr⟩ := hR.exists_omKFrames_of_twDNonsplit hB hn eta i0 hEta hLB hLab
  refine ⟨hev, hZL, hN, f, K, fieldK, algK, finK, charK, E, hf, hpq, hUF, π, hπ, κ, χ,
    hframe, fun y K' hnb => ?_⟩
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  obtain ⟨j, hj, hyj, hAK⟩ :=
    GGSecFiveRouteCfg.nbr_axis_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB hn
      eta i0 hEta hLB hSparse hy hnb (hRM y K' hnb)
  exact ⟨hy, j, hj, hyj, hnbr hy hnb hj hyj hAK⟩

theorem GGSecFiveRouteCfg.exists_omKFrames_of_twDNonsplit_of_noDenseNbr
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {Q : Prop} (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (Q ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)) p Bs L)
    (hB : B = Bs)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hNoDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    Even n ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f)),
        2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ UnitaryFieldData 2 f K ∧
        ∃ π : Fin (n - 1 + 1) ≃ Fin n, π (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π κ χ ∧
            ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
              ∃ (hy : y ∈ Bs) (j : Fin n), j ≠ i0 ∧ (∀ k, k ≠ j → eta ⟨y, hy⟩ k = 1) ∧
                ∃ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)),
                  w ∈ ggG0 p B x L D J ∧
                  MulAut.congr eta (ggConjAut Bs hw) =
                    SpCoord.permAut (p := p) (Equiv.swap i0 j) ∧
                  K' = L.map (MulAut.conj w).toMonoidHom ∧
                  (ggAutomizer K' Bs).map (MulAut.congr eta).toMonoidHom =
                    bCoordinateBlock n p j ∧
                  (π.trans (Equiv.swap i0 j)) (Fin.last (n - 1)) = j ∧
                  GGSecFiveBPermOmKFrame E Bs K' eta (π.trans (Equiv.swap i0 j))
                    ((MulAut.conj w).toMonoidHom.comp κ) χ := by
  have hSparse : GGSecFiveBCoordSparse eta i0 D :=
    hR.bCoordSparse_of_no_denseNbr hX hTCJ hRig hTPn hA8 hraw hiso hFC hB hn eta i0 hEta hLB
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.1, hP.2⟩) hLab) hNoDense
  exact hR.exists_omKFrames_of_twDNonsplit_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw hiso hFC hB
    hn eta i0 hEta hLB hLab hSparse hRM

end CFSG.StandardType

end
