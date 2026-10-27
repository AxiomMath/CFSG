module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCount
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDefs
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
public import CFSG.LocalAnalysis.StandardType.GGLieM6cLifts
public import CFSG.LocalAnalysis.StandardType.GGLieM6cWitness
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

private def m6c_adjExp (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ℤ :=
  Tag.E6.cartan.adjugate.mulVec (fun i => (((x i).val : ℕ) : ℤ))

private theorem m6c_prod_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι)
    (ξ : G) (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem m6c_e6RootParams_zetaVec {L : Type} [Field L] (η : Lˣ)
    (hη : orderOf η = 9) (x : Fin Tag.E6.rank → ZMod 3) :
    e6RootParams (fun l => η ^ (m6c_adjExp x l)) =
      zetaVec (η ^ 3)
        (by rw [← pow_mul, show (3 * 3 : ℕ) = 9 from rfl, ← hη]; exact pow_orderOf_eq_one η) x := by
  funext j
  have hsymm : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j = Tag.E6.cartan j i :=
    fun i j => CFSG.LieType.SeitzGeneration.ExcWideThree.e6Cartan_symm' i j
  have hmul : Tag.E6.cartan.mulVec (m6c_adjExp x) =
      (3 : ℤ) • (fun i => (((x i).val : ℕ) : ℤ)) := by
    change Tag.E6.cartan.mulVec (Tag.E6.cartan.adjugate.mulVec
      (fun i => (((x i).val : ℕ) : ℤ))) = (3 : ℤ) • (fun i => (((x i).val : ℕ) : ℤ))
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, det_cartan_E6,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hexp : (∑ l, m6c_adjExp x l * Tag.E6.cartan l j) = 3 * ((x j).val : ℤ) := by
    have h1 : (∑ l, m6c_adjExp x l * Tag.E6.cartan l j) =
        (Tag.E6.cartan.mulVec (m6c_adjExp x)) j := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hsymm l j, mul_comm]
    rw [h1, hmul, Pi.smul_apply, smul_eq_mul]
  simp only [e6RootParams, zetaVec_apply]
  rw [show (∏ l, (η ^ m6c_adjExp x l) ^ Tag.E6.cartan l j) =
      ∏ l, η ^ (m6c_adjExp x l * Tag.E6.cartan l j) from by
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [zpow_mul]]
  rw [m6c_prod_zpow_sum, hexp]
  rw [show η ^ (3 * ((x j).val : ℤ)) = (η ^ 3) ^ (x j).val from by
    rw [← pow_mul]
    rw [show (3 : ℤ) * ((x j).val : ℤ) = ((3 * (x j).val : ℕ) : ℤ) by push_cast; ring]
    rw [zpow_natCast]]

private theorem m6c_torus_cube_root
    (t : ModGL Tag.E6 GGL) (ht : t ∈ torusGroup Tag.E6 GGL) :
    ∃ u : Fin Tag.E6.rank → GGLˣ, t = rootDiagUnit Tag.E6 (fun i => u i ^ 3) := by
  classical
  let T3 : Subgroup (ModGL Tag.E6 GGL) :=
    { carrier := {t | ∃ u : Fin Tag.E6.rank → GGLˣ,
        t = rootDiagUnit Tag.E6 (fun i => u i ^ 3)}
      one_mem' := ⟨1, by
        rw [← rootDiagUnit_one]
        exact congrArg (rootDiagUnit Tag.E6) (by funext i; simp)⟩
      mul_mem' := by
        rintro t t' ⟨u, rfl⟩ ⟨u', rfl⟩
        refine ⟨u * u', ?_⟩
        rw [← rootDiagUnit_mul]
        exact congrArg (rootDiagUnit Tag.E6)
          (by funext i; simp only [Pi.mul_apply, Pi.pow_apply, mul_pow])
      inv_mem' := by
        rintro t ⟨u, rfl⟩
        refine ⟨u⁻¹, ?_⟩
        rw [rootDiagUnit_inv]
        exact congrArg (rootDiagUnit Tag.E6)
          (by funext i; simp only [Pi.inv_apply, Pi.pow_apply, inv_pow]) }
  have hgen : ∀ p : Fin Tag.E6.rank × GGLˣ, torusElt Tag.E6 GGL p.1 p.2 ∈ T3 := by
    rintro ⟨i, s⟩
    obtain ⟨s', hs'⟩ := IsAlgClosed.exists_pow_nat_eq (s : GGL) (by norm_num : 0 < 3)
    have hs'0 : s' ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hs'
      exact s.ne_zero hs'.symm
    have hs3 : (Units.mk0 s' hs'0 : GGLˣ) ^ 3 = s := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hs']
    refine ⟨fun l => (Units.mk0 s' hs'0) ^ Tag.cartan Tag.E6 i l, ?_⟩
    rw [torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    have hpow : ((Units.mk0 s' hs'0 : GGLˣ) ^ Tag.cartan Tag.E6 i l) ^ 3 =
        ((Units.mk0 s' hs'0 : GGLˣ) ^ 3) ^ Tag.cartan Tag.E6 i l := by
      calc ((Units.mk0 s' hs'0 : GGLˣ) ^ Tag.cartan Tag.E6 i l) ^ 3
          = ((Units.mk0 s' hs'0 : GGLˣ) ^ Tag.cartan Tag.E6 i l) ^ (3 : ℤ) := rfl
        _ = (Units.mk0 s' hs'0 : GGLˣ) ^ (Tag.cartan Tag.E6 i l * 3) := by
            rw [← zpow_mul]
        _ = (Units.mk0 s' hs'0 : GGLˣ) ^ (3 * Tag.cartan Tag.E6 i l) := by
            rw [mul_comm (Tag.cartan Tag.E6 i l) 3]
        _ = ((Units.mk0 s' hs'0 : GGLˣ) ^ (3 : ℤ)) ^ Tag.cartan Tag.E6 i l := by
            rw [zpow_mul]
        _ = ((Units.mk0 s' hs'0 : GGLˣ) ^ 3) ^ Tag.cartan Tag.E6 i l := rfl
    rw [hpow, hs3]
  exact (Subgroup.closure_le T3).2 (by rintro _ ⟨p, rfl⟩; exact hgen p) ht

theorem not_abelianPreimage_of_regular
    (E : Subgroup (ModGL Tag.E6 GGL)) (hEa : E ≤ adjointGroup Tag.E6 GGL)
    (hEM : E ≤ monomialSubgroup Tag.E6 GGL) (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E)
    (A : Subgroup (WeylGroup Tag.E6))
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E, weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥) (hAg : ∀ i, gE6 i ∉ A) :
    ¬ GGLieAbelianPreimageE6 E := by
  classical
  intro hab
  have hAeq : A = ((weylQuotientHom Tag.E6 GGL).comp (Subgroup.inclusion hEM)).range := by
    ext w
    rw [hEA w]
    constructor
    · rintro ⟨e, he, hwe⟩
      exact ⟨⟨e, he⟩, hwe⟩
    · rintro ⟨e, hwe⟩
      exact ⟨e, e.2, hwe⟩
  have hAea : IsElemAbelian 3 A := by
    rw [hAeq]
    exact CFSG.StandardType.isElemAbelian_range
      (fun a b => Subtype.ext (CFSG.StandardType.TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 (a : ModGL Tag.E6 GGL) a.2))
      ((weylQuotientHom Tag.E6 GGL).comp (Subgroup.inclusion hEM))
  have hAg' : ∀ i, A ≠ Subgroup.zpowers (gE6 i) := by
    intro i h
    exact hAg i (h ▸ Subgroup.mem_zpowers (gE6 i))
  obtain ⟨a, haA, x, hx, hm⟩ := exists_pairing_witness A hAS hAea hA1 hAg
  haveI : NeZero (9 : GGL) := ⟨by
    intro h
    have hdvd : 2 ∣ 9 := (CharP.cast_eq_zero_iff GGL 2 9).mp h
    norm_num at hdvd⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot GGL 9
  have hζ₀9 : ζ₀ ^ 9 = 1 := hζ₀.pow_eq_one
  have hζ₀0 : ζ₀ ≠ 0 := by rintro rfl; simpa using hζ₀9
  let η : GGLˣ := Units.mk0 ζ₀ hζ₀0
  have hη : orderOf η = 9 := by
    rw [← orderOf_units, Units.val_mk0]
    exact hζ₀.eq_orderOf.symm
  have hζo : orderOf (η ^ 3) = 3 := by
    have h : (3 : ℕ) = orderOf η / 3 := by norm_num [hη]
    rw [h]
    exact (orderOf_pow_orderOf_div (by rw [hη]; norm_num)
      (by rw [hη]; exact ⟨3, rfl⟩)).trans h
  have hζ : (η ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show (3 * 3 : ℕ) = 9 from rfl, ← hη]
    exact pow_orderOf_eq_one η
  let d : ModGL Tag.E6 GGL := rootDiagUnit Tag.E6 (zetaVec (η ^ 3) hζ x)
  have hdE : d ∈ E :=
    CFSG.StandardType.E6NonToralThree.rootDiagUnit_zetaVec_mem hζo hζ hEM hE hcard hEA hAS
      hA1 hAg' hx
  obtain ⟨e, he, hwe⟩ := (hEA a).mp haA
  have hEm : e ∈ monomialSubgroup Tag.E6 GGL := hEM he
  obtain ⟨w, t, ht, het⟩ := monomialSubgroup_le_torusWeylCosets hEm
  have hmaps_w : MapsRootLines e w := by
    rw [het]
    simpa using (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep (R := GGL) w)
  have hmaps_a : MapsRootLines e a := by
    have h := mapsRootLines_weylQuotientHom (τ := Tag.E6) (R := GGL) ⟨e, hEm⟩
    rwa [hwe] at h
  have hwa : w = a := MapsRootLines.unique hmaps_w hmaps_a
  rw [hwa] at het
  obtain ⟨u, hu⟩ := m6c_torus_cube_root t ht
  let F0 : Finset GGL := insert (η : GGL) (Finset.univ.image (fun i => (u i : GGL)))
  obtain ⟨F, hFfin, hFsub, -⟩ := exists_finite_subfield_of_finset (K := ZMod 2) (L := GGL) F0
  have hηF : (η : GGL) ∈ F :=
    hFsub (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  have huF : ∀ i, (u i : GGL) ∈ F := fun i =>
    hFsub (Finset.mem_coe.2
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  let S : Finset (ModGL Tag.E6 GGL) := {e, d}
  have hS : (↑S : Set (ModGL Tag.E6 GGL)) ⊆ adjointGroup Tag.E6 GGL := by
    intro y hy
    simp only [Finset.mem_coe, S, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h
    · rw [h]; exact hEa he
    · rw [h]; exact hEa hdE
  haveI : Finite ↥F := hFfin
  obtain ⟨k, hkField, hkFinite, κ, ι, hcomp, hdesc⟩ :=
    exists_finite_subfield_lift_adjoint S hS ↥F F.subtype
  letI : Field k := hkField
  letI : Finite k := hkFinite
  obtain ⟨n, hnadj, hnb⟩ := hdesc e (by simp [S])
  obtain ⟨d', hd'adj, hd'⟩ := hdesc d (by simp [S])
  let ηu : (↥F)ˣ := Units.mk0 ⟨(η : GGL), hηF⟩ (by
    intro h; exact η.ne_zero (Subtype.ext_iff.mp h))
  let ηk : kˣ := Units.map κ.toMonoidHom ηu
  have hιη : Units.map ι.toMonoidHom ηk = η := by
    apply Units.ext
    change (ι.comp κ) (ηu : ↥F) = (η : GGL)
    rw [hcomp]
    rfl
  have hηk : orderOf ηk = 9 := by
    rw [orderOf_injective _ (Units.map_injective κ.injective) ηu]
    rw [← orderOf_units]
    rw [← orderOf_injective (F.subtype.toMonoidHom) F.subtype.injective (ηu : ↥F)]
    show orderOf (η : GGL) = 9
    rw [orderOf_units]
    exact hη
  let u' : Fin Tag.E6.rank → kˣ := fun i =>
    Units.map κ.toMonoidHom (Units.mk0 ⟨(u i : GGL), huF i⟩ (by
      intro h; exact (u i).ne_zero (Subtype.ext_iff.mp h)))
  have hιu' : ∀ i, Units.map ι.toMonoidHom (u' i) = u i := by
    intro i
    apply Units.ext
    change (ι.comp κ) ((Units.mk0 ⟨(u i : GGL), huF i⟩ _ : (↥F)ˣ) : ↥F) = (u i : GGL)
    rw [hcomp]
    rfl
  have ht' : baseChangeGL ι (rootDiagUnit Tag.E6 (fun i => (u' i) ^ 3)) = t := by
    rw [baseChangeGL_rootDiagUnit]
    rw [show (fun i => Units.map ι.toMonoidHom ((u' i) ^ 3)) = (fun i => (u i) ^ 3) from by
      funext i; rw [map_pow, hιu' i]]
    rw [← hu]
  let nb : ModGL Tag.E6 k :=
    rootDiagUnit Tag.E6 (fun i => (u' i) ^ 3) * canonicalRep (coxeterSystem Tag.E6) k a
  have hnb_eq : baseChangeGL ι nb = e := by
    dsimp only [nb]
    rw [map_mul, ht', baseChangeGL_canonicalRep, het]
  have hn_eq : n = nb := baseChangeGL_injective ι (by rw [hnb, hnb_eq])
  have hnmono : n ∈ monomialSubgroup Tag.E6 k := by
    rw [hn_eq]
    exact mul_mem
      (le_sup_left (a := torusGroup Tag.E6 k)
        (CFSG.StandardType.TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 u'))
      (canonicalRep_mem_monomialSubgroup (R := k) a)
  have hnmaps : MapsRootLines n a := by
    rw [hn_eq]
    exact mapsRootLines_mul_canonicalRep
      (CFSG.StandardType.TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 u') a
  let dcand : ModGL Tag.E6 k := rootDiagUnit Tag.E6 (e6RootParams (fun l => ηk ^ (m6c_adjExp x l)))
  have hdcand : baseChangeGL ι dcand = d := by
    dsimp only [dcand]
    rw [baseChangeGL_rootDiagUnit]
    rw [show (fun j => Units.map ι.toMonoidHom
          (e6RootParams (fun l => ηk ^ (m6c_adjExp x l)) j)) =
        e6RootParams (fun l => η ^ (m6c_adjExp x l)) from by
      rw [← CFSG.LieType.SeitzGeneration.ExcWideThree.e6RootParams_map']
      congr 1
      funext l
      rw [map_zpow, hιη]]
    rw [m6c_e6RootParams_zetaVec η hη x]
  have hd'_eq : d' = dcand := baseChangeGL_injective ι (by rw [hd', hdcand])
  have hcomm_ggl : e * d = d * e := CFSG.StandardType.TableB.IsElemAbelian.comm hE he hdE
  have hcomm : n * rootDiagUnit Tag.E6 (e6RootParams (fun l => ηk ^ (m6c_adjExp x l))) =
      rootDiagUnit Tag.E6 (e6RootParams (fun l => ηk ^ (m6c_adjExp x l))) * n := by
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, hnb]
    change e * baseChangeGL ι dcand = baseChangeGL ι dcand * e
    rw [hdcand, hcomm_ggl]
  obtain ⟨x₀, y₀, hx₀, hy₀, hnc⟩ :=
    e6_exists_noncommuting_lifts k ηk hηk n a hnadj hnmono hnmaps (m6c_adjExp x) hcomm hm
  have hxE : baseChangeGL ι (e6Isogeny k x₀ : ModGL Tag.E6 k) ∈ E := by
    rw [hx₀, hnb]
    exact he
  have hyE : baseChangeGL ι (e6Isogeny k y₀ : ModGL Tag.E6 k) ∈ E := by
    rw [hy₀]
    change baseChangeGL ι dcand ∈ E
    rw [hdcand]
    exact hdE
  rw [GGLieAbelianPreimageE6] at hab
  exact hnc (hab k ι x₀ y₀ hxE hyE)

end CFSG.StandardType.LieCore.M6c
