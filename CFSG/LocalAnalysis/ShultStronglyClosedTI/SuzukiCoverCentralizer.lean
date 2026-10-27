module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverInvariants
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem suzukiCoverRoot_normalizer (hm : 0 < m) :
    Subgroup.normalizer (suzukiCoverRoot m : Set G) =
      suzukiCoverRoot m ⊔ suzukiCoverTorus m := by
  let R := suzukiCoverRoot m
  let T := suzukiCoverTorus m
  let B := R ⊔ T
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + suzukiCoverTits m x * x ^ 2 + suzukiCoverTits m y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  rcases huppert_blackburn_XI_3_3 m hm (suzukiCoverTits m) (suzukiCoverTits_apply m) with
    ⟨hpres, _, _, _, _, _, _, hstabilizer⟩
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) linRep
  let ovoid : SubMulAction G (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact hpres g z hz }
  let : MulAction G ovoid := ovoid.mulAction
  let pinfO : ovoid := ⟨pinf, Or.inl rfl⟩
  have hB : B = MulAction.stabilizer G pinfO := by
    have hsup := (Subgroup.subgroupOf_sup (suzukiCoverRootGL_le m)
      (suzukiCoverTorusGL_le m)).symm
    change B = (suzukiCoverRootGL m ⊔ suzukiCoverTorusGL m).subgroupOf G at hsup
    rw [hsup]
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ suzukiCoverRootGL m ⊔ suzukiCoverTorusGL m ↔
      (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (hstabilizer g).symm
  have hRne : R ≠ ⊥ := by
    intro h
    have hc := (suzukiCoverRoot_structure m hm).2.1
    change Nat.card R = (2 ^ (2 * m + 1)) ^ 2 at hc
    rw [h, Subgroup.card_bot] at hc
    have hlarge : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_pow (by omega)
    nlinarith
  have hregular : ∀ a b : ovoid, a ≠ pinfO → b ≠ pinfO →
      ∃! r : R, (r : G) • a = b := by
    intro a b ha hb
    have ha' : (a : ℙ K (Fin 4 → K)) ≠ pinf := fun h => ha (Subtype.ext h)
    have hb' : (b : ℙ K (Fin 4 → K)) ≠ pinf := fun h => hb (Subtype.ext h)
    obtain ⟨r, hr, huniq⟩ := suzukiRootClosure_regular_on_ovoid_complement
      m (suzukiCoverTits m) (suzukiCoverTits_apply m) a.val b.val
      a.property b.property ha' hb'
    let rR : R := (suzukiCoverRootBridge m).symm r
    refine ⟨rR, Subtype.ext hr, ?_⟩
    intro s hs
    apply (suzukiCoverRootBridge m).injective
    exact huniq ((suzukiCoverRootBridge m) s) (congrArg Subtype.val hs)
  have hnormal : B ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer (suzukiCoverTorus_le_normalizer m)
  have hN := CFSG.BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl R pinfO
    ((le_sup_left : R ≤ B).trans hB.le) hRne hregular (hB.symm ▸ hnormal)
  exact hN.trans hB.symm

theorem suzukiCoverRoot_normalizer_decomposition (hm : 0 < m) (g : G)
    (hg : g ∈ Subgroup.normalizer (suzukiCoverRoot m : Set G)) :
    ∃ (r : suzukiCoverRoot m) (x : Kˣ),
      g = r.val * (suzukiCoverTorusHom m x).val := by
  rw [suzukiCoverRoot_normalizer m hm] at hg
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left
    (suzukiCoverRoot m) (suzukiCoverTorus m) (suzukiCoverTorus_le_normalizer m)
  have hprod : g ∈ (suzukiCoverRoot m : Set G) * (suzukiCoverTorus m : Set G) := by
    rw [← hset]
    exact hg
  obtain ⟨r, hr, t, ht, hrt⟩ := Set.mem_mul.mp hprod
  obtain ⟨x, hx⟩ := (suzukiCoverTorusHom_bijective m hm).2 ⟨t, ht⟩
  refine ⟨⟨r, hr⟩, x, ?_⟩
  rw [hx]
  exact hrt.symm

theorem suzukiCoverFirstCoord_inner (hm : 0 < m) (r z : suzukiCoverRoot m) :
    suzukiCoverFirstCoord m hm (r * z * r⁻¹) = suzukiCoverFirstCoord m hm z := by
  rw [map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

theorem suzukiCoverRoot_centralizer (hm : 0 < m) :
    Subgroup.centralizer (suzukiCoverRoot m : Set G) =
      (commutator (suzukiCoverRoot m)).map (suzukiCoverRoot m).subtype := by
  apply le_antisymm
  · intro g hg
    obtain ⟨r, x, hfactor⟩ := suzukiCoverRoot_normalizer_decomposition m hm g
      (Subgroup.centralizer_le_normalizer _ hg)
    let z := suzukiCoverRootElement m 1 0
    let az := coverNormalizerAction (suzukiCoverRoot m) (suzukiCoverTorus m)
      (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) z
    have hconj : r * az * r⁻¹ = z := by
      apply Subtype.ext
      change r.val * az.val * r.val⁻¹ = z.val
      dsimp only [az]
      rw [coverNormalizerAction_coe]
      have hc := Subgroup.mem_centralizer_iff.mp hg z.val z.property
      have heq : g * z.val * g⁻¹ = z.val := by rw [← hc, mul_inv_cancel_right]
      rw [hfactor, mul_inv_rev] at heq
      simpa only [mul_assoc] using heq
    have hx : (x : K) = 1 := by
      have h := congrArg (suzukiCoverFirstCoord m hm) hconj
      rw [suzukiCoverFirstCoord_inner] at h
      change suzukiCoverFirstCoord m hm az = suzukiCoverFirstCoord m hm z at h
      dsimp only [az, z] at h
      rw [suzukiCoverTorus_action_root, suzukiCoverFirstCoord_apply,
        suzukiCoverFirstCoord_apply] at h
      have h' := congrArg Multiplicative.toAdd h
      change (x : K) * 1 = 1 at h'
      simpa only [mul_one] using h'
    have hx1 : x = 1 := Units.ext hx
    have hgR : g ∈ suzukiCoverRoot m := by
      rw [hfactor, hx1, map_one, OneMemClass.coe_one, mul_one]
      exact r.property
    let gr : suzukiCoverRoot m := ⟨g, hgR⟩
    have hcenter : gr ∈ Subgroup.center (suzukiCoverRoot m) := by
      apply Subgroup.mem_center_iff.mpr
      intro s
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg s.val s.property)
    rw [← (suzukiCoverRoot_structure m hm).2.2.1] at hcenter
    exact Subgroup.mem_map.mpr ⟨gr, hcenter, rfl⟩
  · rintro g ⟨r, hr, rfl⟩
    rw [(suzukiCoverRoot_structure m hm).2.2.1] at hr
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hr (⟨s, hs⟩ : suzukiCoverRoot m))

end CFSG.ShultStronglyClosedTI
