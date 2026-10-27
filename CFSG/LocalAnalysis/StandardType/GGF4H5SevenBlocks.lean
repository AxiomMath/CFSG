module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsB
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenCoverComp
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwist
public import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix Polynomial CoordSL Multiplicative SpCoord
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.StandardType.SlNsRootGen CFSG.StandardType.SuSplitRootGen CFSG.StandardType.RealKGModelRoot
open CFSG.Yardstones.Md0ec50421ce4

private theorem commutator_projectiveSL_seven_top :
    commutator (projectiveSL 7 (ZMod 2)) = ⊤ := by
  have hSL := CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le
    (K := ZMod 2) (n := 7) (by norm_num)
  rw [commutator_def] at hSL ⊢
  rw [← MonoidHom.range_eq_top.mpr (proj_surjective 7 (ZMod 2)), MonoidHom.range_eq_map,
    ← Subgroup.map_commutator, hSL]

private theorem signedEltSC_projectiveSL_seven :
    GGTorusSignedEltSC 3 (projectiveSL 7 (ZMod 2)) :=
  ggKGLn_signedEltSC_projectiveSL (d := 7) (p := 3) (K := ZMod 2)
    Nat.prime_three (by norm_num)
    (by decide)
    (by rw [Nat.card_zmod]) (by norm_num)

theorem ggKGComponentDatum_projectiveSL_seven :
    GGKGComponentDatum 3 3 (projectiveSL 7 (ZMod 2)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨Nat.prime_three.ne_zero⟩
  haveI : Nonempty (ZMod 2) := ⟨0⟩
  haveI : Fintype (ZMod 2) := Fintype.ofFinite (ZMod 2)
  intro E hE h3 _ hsc
  have hZ : Subgroup.center (projectiveSL 7 (ZMod 2)) = ⊥ :=
    SlNsRootGen.center_projectiveSL_eq_bot_charTwo
  have hcinj : Function.Injective
      (MulAut.conj : projectiveSL 7 (ZMod 2) →* MulAut (projectiveSL 7 (ZMod 2))) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center (projectiveSL 7 (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun f : MulAut (projectiveSL 7 (ZMod 2)) => f z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpK' : ¬ 3 ∣ Nat.card (ZMod 2) - 1 := by
    rw [Nat.card_zmod]
    decide
  have hpK0 : (3 : ZMod 2) ≠ 0 := by decide
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := ZMod 2) (p := 3) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ 3 = 1 :=
    (CoordSL.root_isPrimitiveRoot (K := ZMod 2) hp hpK0 hgd).pow_eq_one
  have hC : (rootMat g).det = 1 := CoordSL.det_rootMat (K := ZMod 2) hp hpK' hpK0 hgd
  have hCp : rootMat g ^ 3 = 1 := CoordSL.rootMat_pow_eq_one (K := ZMod 2) hp hpK0 hgd
  let A : Subgroup (MulAut (projectiveSL 7 (ZMod 2))) := E.map MulAut.conj
  have hmemA : ∀ x, MulAut.conj x ∈ A ↔ x ∈ E := fun x =>
    ⟨fun h => by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      rwa [← hcinj hyx], fun h => Subgroup.mem_map_of_mem _ h⟩
  have hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut 7 (ZMod 2)),
      ∀ l, φa ((MonoidHom.id (projectiveSL 7 (ZMod 2))) l) =
        (MonoidHom.id (projectiveSL 7 (ZMod 2))) (a l) := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨X, rfl⟩ := proj_surjective 7 (ZMod 2) x
    exact ⟨_, ⟨Matrix.SpecialLinearGroup.toGL X, conjAut_toGL X⟩, fun l => rfl⟩
  have h3A : 3 ^ 3 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective hcinj]
    exact h3
  have hscA : GGTorusSelfCent 3 A := by
    intro n hn hnp
    refine (hmemA n).mpr (hsc n (fun e he => ?_) hnp)
    have h := hn _ ((hmemA e).mpr he)
    rw [MulAut.conj_apply] at h
    calc n * e = e * n * e⁻¹ * e := by rw [h]
      _ = e * n := by group
  obtain ⟨s, r', ε, φ, hφs, hφc, hs3, hM⟩ :=
    SlNsRootGen.exists_isBlockTorusModel (g := g) (L' := projectiveSL 7 (ZMod 2))
      (ψ := MonoidHom.id (projectiveSL 7 (ZMod 2))) hp (by norm_num)
      (by rw [Nat.card_zmod]) hgd hC Function.surjective_id
      (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact Subgroup.one_mem _)
      commutator_projectiveSL_seven_top (TableB.isElemAbelian_map hE _) hAI h3A hscA
  have hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 7) (ZMod 2)) :=
    SlNsRootGen.ker_le_center_of φ hφc
  have hkerp : ∀ z ∈ φ.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hzp
    have hzs : z ∈ scalars 7 (ZMod 2) := by rw [scalars_eq_center]; exact hker hz
    obtain ⟨c, -, hcz⟩ := mem_scalars.mp hzs
    have hval : (c : ZMod 2) ^ 3 = 1 := by
      have h3' : ((z ^ 3 : SpecialLinearGroup (Fin 7) (ZMod 2)) :
          Matrix (Fin 7) (Fin 7) (ZMod 2)) ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1 := by
        simp [hzp]
      rw [Matrix.SpecialLinearGroup.coe_pow, hcz, Matrix.scalar_apply, Matrix.diagonal_pow,
        Matrix.diagonal_apply_eq] at h3'
      simpa using h3'
    have hc1 : c = 1 := Units.ext (by simpa using OrdPNS.eq_one_of_pow_eq_one hp hpK' hval)
    refine Subtype.ext ?_
    rw [hcz, hc1]
    simp
  let τ : (Fin s → Multiplicative (ZMod 3)) →* projectiveSL 7 (ZMod 2) :=
    (φ.comp (torusSL ε hC hCp)).comp
      (MulEquiv.funMultiplicative (Fin s) (ZMod 3)).symm.toMonoidHom
  have hτapp : ∀ f, τ f = φ (torusSL ε hC hCp (ofAdd fun k => toAdd (f k))) := fun f => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    by_contra hne
    refine map_torusSL_ne_one (ε := ε) (hC := hC) (hCp := hCp) (φ := φ) (p := 3)
      (by norm_num) (by rw [Nat.card_zmod]) hgd hφc (t := fun k => toAdd (f k)) ?_ hf
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
  have hdim2 : (rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two (p := 3) (K := ZMod 2) hp (by norm_num) hpK0 hgd
      (by rw [Nat.card_zmod])
  have hcardε : 7 = 2 * s + r' := by
    have h := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h
    rw [hdim2] at h
    simpa using h
  have hs_eq : s = 3 := by omega
  have hr_eq : r' = 1 := by omega
  have hr1 : 1 ≤ r' := by omega
  have hdata : ∀ i : OmPlusIdx s ⊕ Fin s, ∃ (w : SpecialLinearGroup (Fin 7) (ZMod 2))
      (B : Subgroup (SpecialLinearGroup (Fin 7) (ZMod 2))) (fm : (Fin s → ZMod 3) → Fin s → ZMod 3),
      w ∈ B ∧ (∀ t, w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (fm t))) ∧
      IsComponentOf B (Subgroup.centralizer (torusFix (torusSL ε hC hCp) fm)) ∧
      3 ∣ Nat.card B ∧
      ∀ f : Fin s → Multiplicative (ZMod 3), fm (fun k => toAdd (f k)) =
        fun k => toAdd (Sum.elim (omPlusRefl 3) sgnAut i f k) := by
    rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | m)
    · cases b
      · obtain ⟨w, hwB, hw⟩ := exists_swap_mem_pairBlock (g := g) ε hC hCp i j
        exact ⟨w, _, _, hwB, hw, SlNsRootGen.isComponentOf_pairBlock_centralizer
          (p := 3) (by norm_num) hgd hij.ne,
          SlNsRootGen.dvd_natCard_pairBlock (p := 3) (by norm_num) (by rw [Nat.card_zmod]) hgd hij.ne,
          fun f => RealKGCover.coord_swap i j f⟩
      · obtain ⟨w, hwB, hw⟩ := exists_sswap_mem_twistPairBlock ε hC hCp hζ (by rw [Nat.card_zmod]) i j
        exact ⟨w, _, _, hwB, hw, SlNsRootGen.isComponentOf_twistPairBlock_centralizer
          (p := 3) (by norm_num) (by rw [Nat.card_zmod]) hgd hζ hij.ne,
          SlNsRootGen.dvd_natCard_twistPairBlock (p := 3) (by norm_num) (by rw [Nat.card_zmod]) hgd hζ hij.ne,
          fun f => RealKGCover.coord_sswap hij f⟩
    · obtain ⟨w, hwB, hw⟩ := exists_neg_mem_zeroBlock ε hC hCp hζ (by rw [Nat.card_zmod]) m
      exact ⟨w, _, _, hwB, hw, SlNsRootGen.isComponentOf_zeroBlock_centralizer
        (p := 3) (by norm_num) (by rw [Nat.card_zmod]) hgd (Or.inr hr1) m,
        SlNsRootGen.dvd_natCard_zeroBlock (p := 3) (by norm_num) (by rw [Nat.card_zmod]) hgd m,
        fun f => RealKGCover.coord_neg m f⟩
  choose wS B fm hwB hw hcompB hdvdB hfm using hdata
  obtain ⟨k, τ', hτ', hτ'E, -, -, hnorm⟩ := signedEltSC_projectiveSL_seven E hE h3 hsc
  have hk : k = s := by
    have h1 : Nat.card (Fin k → Multiplicative (ZMod 3)) =
        Nat.card (Fin s → Multiplicative (ZMod 3)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hτ').toEquiv,
        Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, hτ'E, hτE]
    rw [RealKGCover.card_coord, RealKGCover.card_coord] at h1
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  subst hk
  refine RealKGModelRoot.ggKGComponentDatumAt_of_signedModel (p := 3) (k := k)
    Nat.prime_three (by norm_num) hτinj hτE hτ' hτ'E hnorm
    (fun i => φ (wS i)) (fun i => (B i).map φ) ?_ (fun i => Subgroup.mem_map_of_mem φ (hwB i)) ?_
    (fun i => RealKGCover.dvd_card_map (p := 3) Nat.prime_three hkerp (hdvdB i))
  · intro i f
    rw [hτapp, hτapp, ← map_inv, ← map_mul, ← map_mul, hw i, hfm i f]
  · intro i
    have hset : τ '' {f | Sum.elim (omPlusRefl 3) sgnAut i f = f} =
        φ '' torusFix (torusSL ε hC hCp) (fm i) := by
      ext x
      constructor
      · rintro ⟨f, hf, rfl⟩
        refine ⟨torusSL ε hC hCp (ofAdd fun k => toAdd (f k)),
          ⟨ofAdd fun k => toAdd (f k), ?_, rfl⟩, rfl⟩
        change fm i (fun k => toAdd (f k)) = fun k => toAdd (f k)
        rw [hfm i f]
        exact congrArg (fun f' : Fin k → Multiplicative (ZMod 3) => fun k => toAdd (f' k)) hf
      · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨fun k => ofAdd (toAdd u k), ?_, rfl⟩
        have h2 := (hfm i (fun k => ofAdd (toAdd u k))).symm.trans hu
        funext k
        exact Multiplicative.toAdd.injective (congrFun h2 k)
    rw [hset]
    refine RealKGCover.isComponentOf_map_centralizer hφs hker hkerp ?_ (hcompB i)
    rintro _ ⟨u, -, rfl⟩
    exact SlNsRootGen.pow_torusSL (ε := ε) (hC := hC) (hCp := hCp)
      (MonoidHom.id _) (toAdd u)

end CFSG.StandardType

end
