module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNormE

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

private theorem adAct_smul (w : WeylGroup .E6) (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 w (c • x) = c • adAct .E6 3 w x := by
  funext i
  simp only [adAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem e6Perm_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by
  ext i
  fin_cases i <;> rfl

private def autE6Word : List (Fin Tag.E6.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0] : List ℕ).map (Fin.ofNat 6)

private noncomputable def autE6W0 : WeylGroup .E6 := (autE6Word.map (simple .E6)).prod

private theorem list_prod_simple_smul (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    ((l.map (simple .E6)).prod) • v = l.foldr (fun i w => reflect .E6 i w) v := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.prod_cons, mul_smul, simple_smul, ih, List.foldr_cons]

private theorem autE6W0_smul_single (i : Fin Tag.E6.rank) :
    autE6W0 • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = -Pi.single (e6Rho i) 1 := by
  rw [autE6W0, list_prod_simple_smul]
  fin_cases i <;> decide +kernel

private theorem adAct_autE6W0_inv (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 autE6W0⁻¹ x = -(fun i => x (e6Rho i)) := by
  funext i
  simp only [adAct]
  rw [inv_inv, autE6W0_smul_single i]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_eq_single (e6Rho i) (fun b _ hb => by
        rw [Pi.single_apply, if_neg hb, Int.cast_zero, zero_mul]
        exact neg_zero)
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [Pi.single_apply, if_pos rfl, Int.cast_one, one_mul]
  rfl

private theorem graphExp_eq (k : ℕ) (y : Fin Tag.E6.rank → ZMod 3) :
    (fun i => y ((e6Rho ^ k) i)) = (-1 : ZMod 3) ^ k • adAct .E6 3 ((autE6W0⁻¹) ^ k) y := by
  induction k generalizing y with
  | zero => simp [adAct_one]
  | succ k ih =>
    have hcomp : (fun i => y ((e6Rho ^ (k + 1)) i)) =
        (fun i => (fun j => y (e6Rho j)) ((e6Rho ^ k) i)) := by
      funext i
      rw [pow_succ']
      rfl
    rw [hcomp, ih (fun j => y (e6Rho j))]
    have h1 : (fun j => y (e6Rho j)) = (-1 : ZMod 3) • adAct .E6 3 autE6W0⁻¹ y := by
      rw [adAct_autE6W0_inv y]
      funext j
      have key : ∀ a : ZMod 3, a = (-1 : ZMod 3) * (-a) := by intro a; revert a; decide
      exact key (y (e6Rho j))
    rw [h1, adAct_smul, ← adAct_mul, ← pow_succ, ← smul_assoc]
    rw [show (-1 : ZMod 3) ^ k • (-1 : ZMod 3) = (-1) ^ (k + 1) from by
      rw [smul_eq_mul, pow_succ]]

private noncomputable def e6DiagramMap : ModGL Tag.E6 K := diagramMap TwistTag.E6 K

private theorem e6DiagramMap_mul_rootDiagUnit (c : Fin Tag.E6.rank → Kˣ) :
    e6DiagramMap (K := K) * rootDiagUnit .E6 c =
      rootDiagUnit .E6 (fun i => c (e6Rho i)) * e6DiagramMap (K := K) := by
  show e6DiagramMap (K := K) * rootDiagUnit .E6 c =
    rootDiagUnit .E6 (fun i => c (e6Rho i)) * e6DiagramMap (K := K)
  rw [show (fun i => c (e6Rho i)) = (fun i => c (TwistTag.E6.perm.symm i)) from by
    funext i
    rw [show e6Rho = TwistTag.E6.perm from rfl]
    exact congrArg c (by rw [e6Perm_symm]; rfl)]
  exact E6_diagramMap_mul_rootDiagUnit c

private theorem e6DiagramMap_pow_conj_rootDiagUnit (k : ℕ) (c : Fin Tag.E6.rank → Kˣ) :
    (e6DiagramMap (K := K)) ^ k * rootDiagUnit .E6 c * ((e6DiagramMap (K := K)) ^ k)⁻¹ =
      rootDiagUnit .E6 (fun i => c ((e6Rho ^ k) i)) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have hstep : e6DiagramMap (K := K) * rootDiagUnit .E6 c * (e6DiagramMap (K := K))⁻¹ =
        rootDiagUnit .E6 (fun i => c (e6Rho i)) := by
      rw [e6DiagramMap_mul_rootDiagUnit]
      group
    rw [pow_succ, mul_inv_rev]
    rw [show e6DiagramMap (K := K) ^ k * e6DiagramMap (K := K) * rootDiagUnit .E6 c *
            ((e6DiagramMap (K := K))⁻¹ * (e6DiagramMap (K := K) ^ k)⁻¹) =
          e6DiagramMap (K := K) ^ k *
            (e6DiagramMap (K := K) * rootDiagUnit .E6 c * (e6DiagramMap (K := K))⁻¹) *
            (e6DiagramMap (K := K) ^ k)⁻¹ from by group]
    rw [hstep, ih]
    congr 1
    funext i
    rw [pow_succ']
    rfl

private theorem exactQ_mul_rootDiagUnit_mul_inv (ε : ℕ) (c : Fin Tag.E6.rank → Kˣ) :
    exactQ .E6 K ε * rootDiagUnit .E6 c * (exactQ .E6 K ε)⁻¹ =
      rootDiagUnit .E6 (fun i => c (exactPerm .E6 ε i)) := by
  rw [show exactPerm .E6 ε = (e6Rho ^ ε) from rfl]
  exact e6DiagramMap_pow_conj_rootDiagUnit ε c

private theorem exactNormalAut_mul_rootDiagAut (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (b : Fin Tag.E6.rank → Kˣ) :
    exactNormalAut .E6 K a σ ε * rootDiagAut .E6 K b =
      rootDiagAut .E6 K
        (fun i => Units.map σ.toRingHom.toMonoidHom (b (exactPerm .E6 ε i))) *
        exactNormalAut .E6 K a σ ε := by
  have hb' : rootDiagUnit .E6
        (fun i => Units.map σ.toRingHom.toMonoidHom (b (exactPerm .E6 ε i))) =
      rootDiagUnit .E6 a * exactQ .E6 K ε *
          Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit .E6 b) * (exactQ .E6 K ε)⁻¹ *
          (rootDiagUnit .E6 a)⁻¹ := by
    rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    rw [show rootDiagUnit .E6 a * exactQ .E6 K ε *
          rootDiagUnit .E6 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) * (exactQ .E6 K ε)⁻¹ *
          (rootDiagUnit .E6 a)⁻¹ =
        rootDiagUnit .E6 a *
          (exactQ .E6 K ε * rootDiagUnit .E6 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) *
            (exactQ .E6 K ε)⁻¹) * (rootDiagUnit .E6 a)⁻¹ from by group,
      exactQ_mul_rootDiagUnit_mul_inv]
    rw [NoOffE6Three.rootDiagUnit_mul_comm]
    group
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_exactNormalAut, coe_rootDiagAut, coe_rootDiagAut,
    coe_exactNormalAut, hb']
  simp only [map_mul, map_inv]
  group

private theorem exactNormalAut_conj_rootDiagAut (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (b : Fin Tag.E6.rank → Kˣ) :
    exactNormalAut .E6 K a σ ε * rootDiagAut .E6 K b * (exactNormalAut .E6 K a σ ε)⁻¹ =
      rootDiagAut .E6 K
        (fun i => Units.map σ.toRingHom.toMonoidHom (b (exactPerm .E6 ε i))) := by
  rw [exactNormalAut_mul_rootDiagAut (K := K) a σ ε b]
  group

private theorem exists_sigma_zetaVec (σ : K ≃+* K) {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) :
    ∃ f : ZMod 3, f ≠ 0 ∧ ∀ x : Fin Tag.E6.rank → ZMod 3,
      (fun i => Units.map σ.toRingHom.toMonoidHom (TableBExc.E6Three.zetaVec ζ hζ x i)) =
        TableBExc.E6Three.zetaVec ζ hζ (f • x) := by
  have hζprim : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.iff_orderOf.mpr hζo
  have hσζ3 : (Units.map σ.toRingHom.toMonoidHom ζ) ^ 3 = 1 := by
    rw [← map_pow, hζ, map_one]
  obtain ⟨i, hi3, hi⟩ :=
    hζprim.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 3 (Units.map σ.toRingHom.toMonoidHom ζ)).mpr hσζ3)
  have hσζ1 : Units.map σ.toRingHom.toMonoidHom ζ ≠ 1 := by
    intro h
    have h1 : σ (ζ : K) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h
      simpa using this
    have hζ1 : (ζ : K) = 1 := σ.injective (by rw [h1, map_one])
    have hζe : ζ = 1 := Units.ext hζ1
    rw [hζe, orderOf_one] at hζo
    omega
  have hi0 : i ≠ 0 := by
    intro hi0
    exact hσζ1 (by rw [← hi, hi0, pow_zero])
  have hσζ : Units.map σ.toRingHom.toMonoidHom ζ =
      zmodPowHom ζ hζ (Multiplicative.ofAdd (i : ZMod 3)) := by
    rw [← hi, zmodPowHom_apply]
    congr 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi3]
  have hf0 : (i : ZMod 3) ≠ 0 := by
    intro h
    exact hσζ1 (by rw [hσζ, h]; simp)
  have hζpow : ∀ y : ZMod 3, zmodPowHom ζ hζ (Multiplicative.ofAdd y) =
      (zmodPowHom ζ hζ (Multiplicative.ofAdd (1 : ZMod 3))) ^ y.val := by
    intro y
    rw [zmodPowHom_apply, zmodPowHom_apply,
      show (1 : ZMod 3).val = 1 from by decide, pow_one]
  have hkey : ∀ y : ZMod 3, Units.map σ.toRingHom.toMonoidHom
        (zmodPowHom ζ hζ (Multiplicative.ofAdd y)) =
      zmodPowHom ζ hζ (Multiplicative.ofAdd ((i : ZMod 3) * y)) := by
    intro y
    rw [hζpow y, map_pow]
    rw [show zmodPowHom ζ hζ (Multiplicative.ofAdd (1 : ZMod 3)) = ζ from by
      rw [zmodPowHom_apply, show (1 : ZMod 3).val = 1 from by decide, pow_one]]
    rw [hσζ]
    rw [← zpow_natCast, zmodPowHom_zpow, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
  refine ⟨(i : ZMod 3), hf0, fun x => ?_⟩
  funext j
  simpa only [TableBExc.E6Three.zetaVec, Pi.smul_apply, smul_eq_mul] using hkey (x j)

private theorem hypE6_smul_mem (c : ZMod 3) {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ NoOffRest.hypE6) :
    c • x ∈ NoOffRest.hypE6 :=
  NoOffRest.mem_hypE6.mpr (by rw [NoOffRest.kDotP_smul, NoOffRest.mem_hypE6.mp hx, mul_zero])

theorem eFrame_aut [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).AutOK := by
  intro α S hS hnorm
  obtain ⟨g, a, σ, ε, hnf⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
  obtain ⟨f, hf0, hfield⟩ := exists_sigma_zetaVec (K := K) σ hζo hζ
  let u : WeylGroup .E6 := (autE6W0⁻¹) ^ (ε : ℕ)
  let c : ZMod 3 := f * (-1 : ZMod 3) ^ (ε : ℕ)
  have hc : c ≠ 0 := by
    refine mul_ne_zero hf0 (pow_ne_zero _ ?_)
    decide
  have hαeq : α = MulAut.conj g * exactNormalAut .E6 K a σ ε := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_exactNormalAut]
    rw [hnf h]
    group
  have hEconj : ∀ x, exactNormalAut .E6 K a σ ε * (eFrame K ζ hζ).ad x *
      (exactNormalAut .E6 K a σ ε)⁻¹ =
      (eFrame K ζ hζ).ad (c • adAct .E6 3 u x) := by
    intro x
    have hx' : (fun i => x (exactPerm .E6 (ε : ℕ) i)) =
        (-1 : ZMod 3) ^ (ε : ℕ) • adAct .E6 3 u x := by
      rw [show u = (autE6W0⁻¹) ^ (ε : ℕ) from rfl]
      exact graphExp_eq (ε : ℕ) x
    rw [show (eFrame K ζ hζ).ad x = rootDiagAut .E6 K (zetaVec ζ hζ x) from rfl,
      exactNormalAut_conj_rootDiagAut,
      show (eFrame K ζ hζ).ad (c • adAct .E6 3 u x) =
        rootDiagAut .E6 K (zetaVec ζ hζ (c • adAct .E6 3 u x)) from rfl]
    congr 1
    calc (fun i => Units.map σ.toRingHom.toMonoidHom (zetaVec ζ hζ x (exactPerm .E6 (ε : ℕ) i)))
        = (fun i => Units.map σ.toRingHom.toMonoidHom
            (zetaVec ζ hζ (fun i => x (exactPerm .E6 (ε : ℕ) i)) i)) := rfl
      _ = zetaVec ζ hζ (f • (fun i => x (exactPerm .E6 (ε : ℕ) i))) :=
            hfield (fun i => x (exactPerm .E6 (ε : ℕ) i))
      _ = zetaVec ζ hζ (c • adAct .E6 3 u x) := by
            congr 1
            rw [hx', ← smul_smul]
  have hconj : ∀ x, α * (eFrame K ζ hζ).ad x * α⁻¹ =
      MulAut.conj g * (eFrame K ζ hζ).ad (c • adAct .E6 3 u x) * (MulAut.conj g)⁻¹ := by
    intro x
    rw [hαeq,
      show (MulAut.conj g * exactNormalAut .E6 K a σ ε) * (eFrame K ζ hζ).ad x *
          (MulAut.conj g * exactNormalAut .E6 K a σ ε)⁻¹ =
          MulAut.conj g * (exactNormalAut .E6 K a σ ε * (eFrame K ζ hζ).ad x *
            (exactNormalAut .E6 K a σ ε)⁻¹) * (MulAut.conj g)⁻¹ from by group,
      hEconj x]
  have hnormg : ∀ x ∈ S, ∃ y ∈ S,
      MulAut.conj g * (eFrame K ζ hζ).ad x * (MulAut.conj g)⁻¹ = (eFrame K ζ hζ).ad y := by
    intro z hz
    have hxS : c⁻¹ • adAct .E6 3 u⁻¹ z ∈ S := by
      rcases hS with rfl | rfl
      · exact Set.mem_univ _
      · exact hypE6_smul_mem c⁻¹ (NoOffRest.adAct_mem_hypE6 u⁻¹ hz)
    obtain ⟨y, hyS, hy⟩ := hnorm (c⁻¹ • adAct .E6 3 u⁻¹ z) hxS
    refine ⟨y, hyS, ?_⟩
    have hm : c • adAct .E6 3 u (c⁻¹ • adAct .E6 3 u⁻¹ z) = z := by
      rw [adAct_smul, ← adAct_mul, mul_inv_cancel, adAct_one, smul_smul, mul_inv_cancel₀ hc,
        one_smul]
    calc MulAut.conj g * (eFrame K ζ hζ).ad z * (MulAut.conj g)⁻¹
        = MulAut.conj g *
            (eFrame K ζ hζ).ad (c • adAct .E6 3 u (c⁻¹ • adAct .E6 3 u⁻¹ z)) *
            (MulAut.conj g)⁻¹ := by rw [hm]
      _ = α * (eFrame K ζ hζ).ad (c⁻¹ • adAct .E6 3 u⁻¹ z) * α⁻¹ := (hconj _).symm
      _ = (eFrame K ζ hζ).ad y := hy
  obtain ⟨u_g, hu_g⟩ := eFrame_norm (K := K) (ζ := ζ) hζ g S hS hnormg
  refine ⟨c, u_g * u, hc, fun x hx => ?_⟩
  have hmem : c • adAct .E6 3 u x ∈ S := by
    rcases hS with rfl | rfl
    · exact Set.mem_univ _
    · exact hypE6_smul_mem c (NoOffRest.adAct_mem_hypE6 u hx)
  calc α * (eFrame K ζ hζ).ad x * α⁻¹
      = MulAut.conj g * (eFrame K ζ hζ).ad (c • adAct .E6 3 u x) * (MulAut.conj g)⁻¹ :=
          hconj x
    _ = (eFrame K ζ hζ).ad (adAct .E6 3 u_g (c • adAct .E6 3 u x)) := hu_g _ hmem
    _ = (eFrame K ζ hζ).ad (c • adAct .E6 3 (u_g * u) x) := by
          exact congrArg (eFrame K ζ hζ).ad
            ((adAct_smul u_g c (adAct .E6 3 u x)).trans
              (congrArg (fun z => c • z) (adAct_mul u_g u x).symm))

end CFSG.StandardType.E6ThreeModel
