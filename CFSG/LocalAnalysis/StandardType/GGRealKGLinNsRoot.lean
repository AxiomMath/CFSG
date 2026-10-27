module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwist
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenCoverComp
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame
import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsC
import CFSG.LocalAnalysis.StandardType.GGKGForkVacuous
import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaRow
import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RealKGLinNs

open Matrix Polynomial CoordSL CFSG.Assembly Multiplicative SpCoord
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.StandardType.SlNsRootGen CFSG.StandardType.SuSplitRootGen CFSG.StandardType.RealKGCover

theorem ggKGRootDatum_projectiveSL {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) (h4 : 4 ≤ Nat.card K)
    (hperf : commutator (projectiveSL d K) = ⊤)
    (hsign : GGTorusSignedEltSC p (projectiveSL d K))
    (hlayer : ∀ a : projectiveSL d K, a ^ p = 1 → ∀ J : Subgroup (projectiveSL d K), ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set (projectiveSL d K)) →
        J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set (projectiveSL d K))))
    (r : ℕ) : GGKGRootDatum p r (projectiveSL d K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty K := ⟨0⟩
  haveI : Fintype K := Fintype.ofFinite K
  intro E hE h3 _ hsc
  have hZ : Subgroup.center (projectiveSL d K) = ⊥ := center_projectiveSL_eq_bot_charTwo
  have hcinj : Function.Injective
      (MulAut.conj : projectiveSL d K →* MulAut (projectiveSL d K)) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center (projectiveSL d K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun f : MulAut (projectiveSL d K) => f z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  let A : Subgroup (MulAut (projectiveSL d K)) := E.map MulAut.conj
  have hmemA : ∀ x, MulAut.conj x ∈ A ↔ x ∈ E := fun x =>
    ⟨fun h => by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      rwa [← hcinj hyx], fun h => Subgroup.mem_map_of_mem _ h⟩
  have hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K),
      ∀ l, φa ((MonoidHom.id (projectiveSL d K)) l) = (MonoidHom.id (projectiveSL d K)) (a l) := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨X, rfl⟩ := proj_surjective d K x
    exact ⟨_, ⟨Matrix.SpecialLinearGroup.toGL X, conjAut_toGL X⟩, fun l => rfl⟩
  have h3A : p ^ 3 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective hcinj]
    exact h3
  have hscA : GGTorusSelfCent p A := by
    intro n hn hnp
    refine (hmemA n).mpr (hsc n (fun e he => ?_) hnp)
    have h := hn _ ((hmemA e).mpr he)
    rw [MulAut.conj_apply] at h
    calc n * e = e * n * e⁻¹ * e := by rw [h]
      _ = e * n := by group
  obtain ⟨s, r', ε, φ, hφs, hφc, hs3, hM⟩ :=
    exists_isBlockTorusModel (g := g) (L' := projectiveSL d K)
      (ψ := MonoidHom.id (projectiveSL d K)) hp hp2 hpK hgd hC Function.surjective_id
      (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact Subgroup.one_mem _)
      hperf (TableB.isElemAbelian_map hE _) hAI h3A hscA
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) K) := ker_le_center_of φ hφc
  have hkerp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rcases Nat.eq_zero_or_pos d with hd0 | hd
    · subst hd0
      exact Subtype.ext (Matrix.ext fun i => i.elim0)
    have hzs : z ∈ scalars d K := by rw [scalars_eq_center]; exact hker hz
    obtain ⟨c, -, hcz⟩ := mem_scalars.mp hzs
    have hval : (c : K) ^ p = 1 := by
      have h3 : ((z ^ p : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩ = 1 := by
        simp [hzp]
      rw [Matrix.SpecialLinearGroup.coe_pow, hcz, Matrix.scalar_apply, Matrix.diagonal_pow,
        Matrix.diagonal_apply_eq] at h3
      simpa using h3
    have hc1 : c = 1 := Units.ext (by simpa using OrdPNS.eq_one_of_pow_eq_one hp hpK' hval)
    refine Subtype.ext ?_
    rw [hcz, hc1]
    simp
  let τ : (Fin s → Multiplicative (ZMod p)) →* projectiveSL d K :=
    (φ.comp (torusSL ε hC hCp)).comp (MulEquiv.funMultiplicative (Fin s) (ZMod p)).symm.toMonoidHom
  have hτapp : ∀ f, τ f = φ (torusSL ε hC hCp (ofAdd fun k => toAdd (f k))) := fun f => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    by_contra hne
    refine map_torusSL_ne_one (ε := ε) (hC := hC) (hCp := hCp) (φ := φ) hp2 hpK hgd hφc
      (t := fun k => toAdd (f k)) ?_ hf
    intro h0
    exact hne (funext fun k => by simpa using congrFun h0 k)
  have hτE : τ.range = E := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      rw [← hmemA]
      exact (hM.mem_iff hCp).mpr ⟨fun k => toAdd (f k), rfl⟩
    · intro hx
      obtain ⟨t, ht⟩ := (hM.mem_iff hCp).mp ((hmemA x).mpr hx)
      exact ⟨fun k => ofAdd (t k), (hcinj ht).symm⟩
  have hdata : ∀ i : OmPlusIdx s ⊕ Fin s, ∃ (w : SpecialLinearGroup (Fin d) K)
      (B : Subgroup (SpecialLinearGroup (Fin d) K)) (fm : (Fin s → ZMod p) → Fin s → ZMod p),
      w ∈ B ∧ (∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (fm t))) ∧
      IsComponentOf B (Subgroup.centralizer (torusFix (torusSL ε hC hCp) fm)) ∧
      p ∣ Nat.card B ∧
      ∀ f : Fin s → Multiplicative (ZMod p), fm (fun k => toAdd (f k)) =
        fun k => toAdd (Sum.elim (omPlusRefl p) sgnAut i f k) := by
    rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | m)
    · cases b
      · obtain ⟨w, hwB, hw⟩ := exists_swap_mem_pairBlock (g := g) ε hC hCp i j
        exact ⟨w, _, _, hwB, hw, isComponentOf_pairBlock_centralizer hp2 hgd hij.ne,
          dvd_natCard_pairBlock hp2 hpK hgd hij.ne, fun f => coord_swap i j f⟩
      · obtain ⟨w, hwB, hw⟩ := exists_sswap_mem_twistPairBlock ε hC hCp hζ hpK i j
        exact ⟨w, _, _, hwB, hw, isComponentOf_twistPairBlock_centralizer hp2 hpK hgd hζ hij.ne,
          dvd_natCard_twistPairBlock hp2 hpK hgd hζ hij.ne, fun f => coord_sswap hij f⟩
    · obtain ⟨w, hwB, hw⟩ := exists_neg_mem_zeroBlock ε hC hCp hζ hpK m
      exact ⟨w, _, _, hwB, hw, isComponentOf_zeroBlock_centralizer hp2 hpK hgd (Or.inl h4) m,
        dvd_natCard_zeroBlock hp2 hpK hgd m, fun f => coord_neg m f⟩
  choose wS B fm hwB hw hcompB hdvdB hfm using hdata
  obtain ⟨k, τ', hτ', hτ'E, -, -, hnorm⟩ := hsign E hE h3 hsc
  have hk : k = s := by
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) =
        Nat.card (Fin s → Multiplicative (ZMod p)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hτ').toEquiv,
        Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, hτ'E, hτE]
    rw [card_coord, card_coord] at h1
    exact Nat.pow_right_injective hp.two_le h1
  subst hk
  refine RealKGModelRoot.ggKGRootDatumAt_of_signedModel hp hp2 hτinj hτE hτ' hτ'E hnorm
    (fun i => φ (wS i)) (fun i => (B i).map φ) ?_ (fun i => Subgroup.mem_map_of_mem φ (hwB i)) ?_
    (fun i => dvd_card_map hp hkerp (hdvdB i)) fun a ha J hJ hJa => hlayer a (hE.2 a ha) J hJ hJa
  · intro i f
    rw [hτapp, hτapp, ← map_inv, ← map_mul, ← map_mul, hw i, hfm i f]
  · intro i
    have hset : τ '' {f | Sum.elim (omPlusRefl p) sgnAut i f = f} =
        φ '' torusFix (torusSL ε hC hCp) (fm i) := by
      ext x
      constructor
      · rintro ⟨f, hf, rfl⟩
        refine ⟨torusSL ε hC hCp (ofAdd fun k => toAdd (f k)),
          ⟨ofAdd fun k => toAdd (f k), ?_, rfl⟩, rfl⟩
        change fm i (fun k => toAdd (f k)) = fun k => toAdd (f k)
        rw [hfm i f]
        exact congrArg (fun f' : Fin k → Multiplicative (ZMod p) => fun k => toAdd (f' k)) hf
      · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨fun k => ofAdd (toAdd u k), ?_, rfl⟩
        have h2 := (hfm i (fun k => ofAdd (toAdd u k))).symm.trans hu
        funext k
        exact Multiplicative.toAdd.injective (congrFun h2 k)
    rw [hset]
    refine isComponentOf_map_centralizer hφs hker hkerp ?_ (hcompB i)
    rintro _ ⟨u, -, rfl⟩
    exact pow_torusSL (ε := ε) (hC := hC) (hCp := hCp) (MonoidHom.id _) (toAdd u)

end RealKGLinNs

open CFSG CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix Polynomial Multiplicative

private theorem isChevSimple_of_mulEquiv_lin {r : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : IsChevSimple r B) : IsChevSimple r A := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

private theorem commutator_projectiveSL_top {K : Type} [Field K] {d : ℕ} (hd : 3 ≤ d) :
    commutator (projectiveSL d K) = ⊤ := by
  have hSL := CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := K) hd
  rw [commutator_def] at hSL ⊢
  rw [← MonoidHom.range_eq_top.mpr (proj_surjective d K), MonoidHom.range_eq_map,
    ← Subgroup.map_commutator, hSL]

private theorem card_le_psl_small_lin {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1)
    (hd : 1 ≤ d) (hd5 : d ≤ 5) (E : Subgroup (projectiveSL d K)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  classical
  haveI : Nonempty K := ⟨0⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) (p := p) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζo := CoordSL.root_isPrimitiveRoot (g := g) hp hpK0 hgd
  have hCdet : (CoordSL.rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : (CoordSL.rootMat g) ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hker : (proj d K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K) := by
    intro x hx
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx
  have hcp : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) := by
    intro h
    exact hpK' (h.trans (card_center_specialLinear_dvd (by omega)))
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2) }
  have hV : ∀ v : ↥E, v ^ p = 1 := fun v => Subtype.ext (hE.2 v v.2)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime hp (proj_surjective d K) hker hcp
    (V := ↥E) hV E.subtype
  set S : Set (Matrix (Fin d) (Fin d) K) :=
    {x | ∃ e : ↥E, ((s e : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = x}
    with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have h1 : s e * s e' = s e' * s e := by rw [← map_mul, ← map_mul, mul_comm]
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, rfl⟩
    have h1 : (s e) ^ p = 1 := hsp e
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  obtain ⟨t, r, ε, A₀, hframe⟩ := CoordSL.exists_frame (g := g) hp hpK0 hgd S hSc hSp
  have hdim : (CoordSL.rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK0 hgd hpq
  have hτinj : Function.Injective (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp) :=
    CoordSL.frameHom_injective _ A₀ ε hCdet hCp (by rw [MonoidHom.ker_id]; exact bot_le)
      (by rw [hdim]; norm_num)
      (CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd)
  have hcard_range : Nat.card (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp).range = p ^ t := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coeSort_range hτinj,
      Fintype.card_multiplicative, Fintype.card_pi_const, ZMod.card]
  have hmem : ∀ e : ↥E, s e ∈ (CoordSL.frameHom (MonoidHom.id (Matrix.SpecialLinearGroup (Fin d) K))
      A₀ ε hCdet hCp).range := by
    intro e
    obtain ⟨k, hk⟩ := hframe _ ⟨e, rfl⟩
    refine ⟨ofAdd (fun i => (k i : ZMod p)), ?_⟩
    rw [CoordSL.frameHom_natCast, SLRep.ggFrame_apply, MonoidHom.id_apply]
    have hkSL : s e * A₀ = A₀ * SLNS.nsSL ε hCdet k := Subtype.ext hk
    rw [← hkSL]
    group
  have hcardE : Nat.card E ≤ Nat.card (CoordSL.frameHom (MonoidHom.id
      (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range := by
    refine Nat.card_le_card_of_injective
      (f := fun e : ↥E => (⟨s e, hmem e⟩ : (CoordSL.frameHom (MonoidHom.id
        (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range)) ?_
    intro a b hab
    apply Subtype.ext
    have h1 : s a = s b := congrArg Subtype.val hab
    calc (a : projectiveSL d K) = proj d K (s a) := (hs a).symm
      _ = proj d K (s b) := by rw [h1]
      _ = b := hs b
  have ht2 : t ≤ 2 := by
    have hcard : Fintype.card ((Fin (CoordSL.rootPB g).dim × Fin t) ⊕ Fin r) = d := by
      rw [← Fintype.card_fin d, ← Fintype.card_congr ε]
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hdim] at hcard
    omega
  calc Nat.card E ≤ Nat.card (CoordSL.frameHom (MonoidHom.id
        (Matrix.SpecialLinearGroup (Fin d) K)) A₀ ε hCdet hCp).range := hcardE
    _ = p ^ t := hcard_range
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos ht2

theorem ggTorusRootSL2_aNonsplit
    {K : Type} [Field K] [Finite K] {n d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF4 : 4 ≤ Nat.card K) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hd : 2 ≤ d)
    {lab : LargeEvenLabel}
    (hmark : MarkedModel lab (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    ∃ r, GGTorusLift p r (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) ∧
      GGTorusRootSL2 p r (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpK
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  let e := TypeA.recipeEquiv d K
  have hZpsl : Subgroup.center (projectiveSL d K) = ⊥ := SlNsRootGen.center_projectiveSL_eq_bot_charTwo
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hZpsl] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (e : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →* projectiveSL d K))
      e.injective).mp h1
  have hIp := NbrInnerMore.ggOutdiagPrime_linear (d := d) hp hpK' (by omega)
  have hlift : GGTorusLift p 0 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    TypeA.ggTorusLift_of_mulEquiv e
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by omega)))
  refine ⟨0, hlift, ?_⟩
  rcases lt_or_ge d 6 with hd5 | hd6
  · have hrk : ∀ E : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
      intro E hE
      have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
        Subgroup.card_map_of_injective e.injective
      have hE' : IsElemAbelian p (E.map e.toMonoidHom) := TableB.isElemAbelian_map hE _
      rw [← hcard]
      exact card_le_psl_small_lin hp hp2 hpK0 hpK (by omega) (by omega) _ hE'
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_pRank_le_two hp hIp hZ hrk hA).elim
  · have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK' (by omega))
    refine ggTorusRootSL2_of_rootDatum hp hIp hZ hcp (ggKGRootDatum_of_mulEquiv e ?_)
    have hchevR : IsChevSimple 2 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
        (isChevTwo_of_markedModel hmark)
    have hchev : IsChevSimple 2 (projectiveSL d K) := isChevSimple_of_mulEquiv_lin e.symm hchevR
    have hS : IsSimpleGroup (projectiveSL d K) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hchev
    refine RealKGLinNs.ggKGRootDatum_projectiveSL hp hp2 hpK hF4
      (commutator_projectiveSL_top (by omega))
      (ggKGLn_signedEltSC_projectiveSL hp hp2 hpK0 hpK (by omega)) (fun a hap J hJ hJa => ?_) 0
    by_cases hJb : J = ⊥
    · rw [hJb]
      exact bot_le
    have hnc : ∃ a b : projectiveSL d K, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply hJb
      rw [← hJ, eq_bot_iff]
      exact Subgroup.commutator_le.mpr fun x _ y _ => by
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcon x y
    exact ggKG_layer_of_chevSimple hS hnc hchev hp hp2 hap hJ hJa

private theorem ggRealRootSL2On_linearNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, htag, hpn⟩ := hs
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab (Or.inl htag) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl1 : 1 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hM ⊢
  obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have hp2 : p ≠ 2 := by omega
  have hF4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (by omega) hpK
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusRootSL2_aNonsplit hp hp2 hF4 hK hpn (by omega) hmark⟩

theorem ggRealRootSL2On_aNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .aNonsplit p lab :=
  fun p lab hp hlab hl hs =>
    ggRealRootSL2On_linearNonsplit p lab hp hlab hl ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem ggRealRootSL2On_aNonsplitDvd :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .aNonsplitDvd p lab :=
  fun p lab hp hlab hl hs =>
    ggRealRootSL2On_linearNonsplit p lab hp hlab hl ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem ggRealRootSL2On_dNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .dNonsplit p lab :=
  ggRealRootSL2On_dNonsplit_of_aNonsplit ggRealRootSL2On_aNonsplit

end CFSG.StandardType

end
