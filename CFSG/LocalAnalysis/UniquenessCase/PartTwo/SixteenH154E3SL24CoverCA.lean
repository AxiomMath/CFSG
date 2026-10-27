module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.Background.HStandard
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_coord {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : s16h_H5RowSL2 L U Z 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥L)
        (β : ↥U →* StdMod (Fin 2) K),
        Function.Surjective π ∧ Function.Surjective β ∧
        (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
        (∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (u : ↥U)
          (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
          β ⟨_, hu⟩ = natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (β u)) := by
  obtain ⟨-, hBN⟩ := hrow
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
      rfl rfl hπ
  refine ⟨K, hKf, hKfin, ?_, π, β, hπ.1, hβs, hβk, hβe⟩
  rw [hKcard]
  norm_num

theorem s16h_sl24_cover_rank_le {L : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K]
    {s : MulAut (StdMod (Fin 2) K)}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K} (hβs : Function.Surjective β)
    {n : MulAut W} (hnU' : ∀ u : ↥(commSub ⊤ L), n (u : W) ∈ commSub ⊤ L)
    (hβe : ∀ u : ↥(commSub ⊤ L), β ⟨n (u : W), hnU' u⟩ = s (β u)) :
    rkIdx (fixV (Subgroup.zpowers s)) ≤ rkIdx (fixV (Subgroup.zpowers n)) := by
  rw [rkIdx_fixV_zpowers, rkIdx_fixV_zpowers, commV_zpowers_eq_map, commV_zpowers_eq_map]
  set S : Subgroup W := (commSub ⊤ L).map (commHom n) with hS
  have hSU : S ≤ commSub ⊤ L := by
    intro x hx
    rw [hS] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact (commSub ⊤ L).mul_mem (hnU' ⟨u, hu⟩) ((commSub ⊤ L).inv_mem hu)
  have hSle : S ≤ (⊤ : Subgroup W).map (commHom n) := Subgroup.map_mono le_top
  have hset : (⊤ : Subgroup (StdMod (Fin 2) K)).map (commHom s) =
      (S.subgroupOf (commSub ⊤ L)).map β := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨u, rfl⟩ := hβs v
      refine Subgroup.mem_map.mpr
        ⟨⟨n (u : W), hnU' u⟩ * ⟨(u : W), u.2⟩⁻¹, ?_, ?_⟩
      · rw [hS]
        exact Subgroup.mem_map.mpr ⟨(u : W), u.2, rfl⟩
      · show β (⟨n (u : W), hnU' u⟩ * ⟨(u : W), u.2⟩⁻¹ : ↥(commSub ⊤ L)) =
          commHom s (β u)
        rw [map_mul, map_inv, hβe u]
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (show (x : W) ∈ S from hx)
      refine Subgroup.mem_map.mpr ⟨β ⟨w, hw⟩, Subgroup.mem_top _, ?_⟩
      have h1 : x = (⟨n (w : W) * (w : W)⁻¹,
          (commSub ⊤ L).mul_mem (hnU' ⟨w, hw⟩) ((commSub ⊤ L).inv_mem hw)⟩ :
            ↥(commSub ⊤ L)) := Subtype.ext hwx.symm
      rw [h1]
      show commHom s (β ⟨w, hw⟩) =
        β (⟨n (w : W) * (w : W)⁻¹, _⟩ : ↥(commSub ⊤ L))
      rw [show (⟨n (w : W) * (w : W)⁻¹, _⟩ : ↥(commSub ⊤ L)) =
        ⟨n (w : W), hnU' ⟨w, hw⟩⟩ * ⟨(w : W), hw⟩⁻¹ from rfl]
      rw [map_mul, map_inv, hβe ⟨w, hw⟩]
      rfl
  rw [hset]
  calc rk ((S.subgroupOf (commSub ⊤ L)).map β)
      ≤ rk (S.subgroupOf (commSub ⊤ L)) := by
        unfold rk
        exact padicValNat_two_le_of_dvd
          (Nat.card_pos (α := S.subgroupOf (commSub ⊤ L))).ne'
          (Subgroup.card_map_dvd _ _)
    _ = rk S := by
        unfold rk
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv]
    _ ≤ rk ((⊤ : Subgroup W).map (commHom n)) := rk_mono hSle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
