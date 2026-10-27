module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalLeviA
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexOneCompl
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalVertexOneTransport
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalRigid
import CFSG.Quasithin.Recognition.St84.Gen.L2WeylComplement
import CFSG.Quasithin.Recognition.St84.Gen.SemidirectExtendConj
import CFSG.Quasithin.Recognition.St84.SemidirectRec
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
import CFSG.Quasithin.H13.J4Order

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i1)
open CFSG.QuasithinUnique.Setup.X6 (g2Index)


variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private noncomputable def conjAut {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : ↥Q ≃* ↥Q :=
  Q.normalizerMonoidHom ⟨g, hg⟩

private theorem conjAut_apply {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    (conjAut g hg x : G) = g * (x : G) * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨g, hg⟩ x

private theorem conjAut_trans {Q : Subgroup G} (g h : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hh : h ∈ Subgroup.normalizer (Q : Set G)) :
    (conjAut g hg).trans (conjAut h hh) =
      conjAut (h * g) (Subgroup.mul_mem (Subgroup.normalizer (Q : Set G)) hh hg) := by
  ext x
  rw [MulEquiv.trans_apply, conjAut_apply, conjAut_apply, conjAut_apply]
  group

private theorem conjAut_symm {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    (conjAut g hg).symm = conjAut g⁻¹ (Subgroup.inv_mem (Subgroup.normalizer (Q : Set G)) hg) := by
  ext x
  have h2 : g * ((conjAut g hg).symm x : G) * g⁻¹ = (x : G) := by
    have h3 := congrArg (fun y : ↥Q => (y : G)) ((conjAut g hg).apply_symm_apply x)
    rwa [conjAut_apply (g := g) (hg := hg)] at h3
  rw [conjAut_apply (g := g⁻¹) (hg := Subgroup.inv_mem _ hg), ← h2]
  group

private noncomputable def pCoreOfG2ParAEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}) where
  toFun x :=
    ⟨((x : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K),
      G2q.mem_pCoreOf_g2ParA_iff.mp x.2⟩
  invFun y :=
    ⟨⟨((y : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K),
        (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}).trans
          (posUnipotent_le_adjointGroup (τ := Tag.G2) (K := K)) y.2⟩,
      G2q.mem_pCoreOf_g2ParA_iff.mpr y.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

private theorem pCoreOfG2ParAEquiv_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (q : ↥(pCoreOf 2 (g2ParA K))) :
    ((pCoreOfG2ParAEquiv K q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
      ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) := rfl

private noncomputable def transportAut {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (e : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1)) :
    ↥(parabolicRadical Tag.G2 K {i1}) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
  iota.symm.trans (θ.symm.trans (e.trans (θ.trans iota)))

private theorem transportAut_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (e : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1))
    (x : ↥(parabolicRadical Tag.G2 K {i1})) :
    transportAut θ iota e x = iota (θ (e (θ.symm (iota.symm x)))) := rfl

private theorem transportAut_trans {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (e f : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1)) :
    (transportAut θ iota e).trans (transportAut θ iota f) =
      transportAut θ iota (e.trans f) := by
  refine MulEquiv.ext fun x => ?_
  change transportAut θ iota f (transportAut θ iota e x) =
    transportAut θ iota (e.trans f) x
  rw [transportAut_apply, transportAut_apply, transportAut_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem transportAut_symm {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (e : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1)) :
    (transportAut θ iota e).symm = transportAut θ iota e.symm := by
  refine MulEquiv.ext fun x => ?_
  apply (transportAut θ iota e).injective
  rw [MulEquiv.apply_symm_apply]
  rw [transportAut_apply, transportAut_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem transportAut_refl {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1})) :
    transportAut θ iota (MulEquiv.refl (↥(pCoreOf 2 L1))) =
      MulEquiv.refl (↥(parabolicRadical Tag.G2 K {i1})) := by
  refine MulEquiv.ext fun x => ?_
  rw [transportAut_apply]
  simp only [MulEquiv.refl_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem transportAut_conj_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {g : G} (hgP2 : g ∈ L2 ⊔ bigB L1 L2 S)
    (hgN : g ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (e : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1))
    (he : ∀ x : ↥(pCoreOf 2 L1), (e x : G) = g * (x : G) * g⁻¹)
    (x : ↥(parabolicRadical Tag.G2 K {i1})) :
    ((transportAut θ iota e x : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
      (((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) *
        (x : ModGL Tag.G2 K) *
          (((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K)⁻¹ := by
  classical
  set qa : ↥(pCoreOf 2 (g2ParA K)) := iota.symm x with hqa
  set q1 : ↥(pCoreOf 2 L1) := θ.symm qa with hq1
  have hiota_qa : iota qa = x := iota.apply_symm_apply x
  have hθ_q1 : θ q1 = qa := θ.apply_symm_apply qa
  have hval : ((transportAut θ iota e x : ↥(parabolicRadical Tag.G2 K {i1})) :
      ModGL Tag.G2 K) = ((θ (e q1) : ↥(pCoreOf 2 (g2ParA K))) : ModGL Tag.G2 K) := by
    dsimp only [transportAut]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply]
    rw [← hqa, ← hq1]
    exact hiota (θ (e q1))
  have harg : (⟨((e q1 : ↥(pCoreOf 2 L1)) : G), hQ1P (e q1).2⟩ :
      ↥(L2 ⊔ bigB L1 L2 S)) =
      ⟨g, hgP2⟩ * ⟨(q1 : G), hQ1P q1.2⟩ * ⟨g, hgP2⟩⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact he q1
  calc ((transportAut θ iota e x : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K)
      = ((θ (e q1) : ↥(pCoreOf 2 (g2ParA K))) : ModGL Tag.G2 K) := hval
    _ = ((ψ₂ ⟨((e q1 : ↥(pCoreOf 2 L1)) : G), hQ1P (e q1).2⟩ :
          ↥(g2ParB K)) : ModGL Tag.G2 K) := hθ (e q1)
    _ = ((ψ₂ (⟨g, hgP2⟩ * ⟨(q1 : G), hQ1P q1.2⟩ * ⟨g, hgP2⟩⁻¹) :
          ↥(g2ParB K)) : ModGL Tag.G2 K) := by rw [harg]
    _ = ((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ModGL Tag.G2 K) *
          ((ψ₂ ⟨(q1 : G), hQ1P q1.2⟩ : ↥(g2ParB K)) : ModGL Tag.G2 K) *
            (((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ModGL Tag.G2 K))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    _ = (((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) *
          (x : ModGL Tag.G2 K) *
            (((ψ₂ ⟨g, hgP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K)⁻¹ := by
        have hq1ψ : ((ψ₂ ⟨(q1 : G), hQ1P q1.2⟩ : ↥(g2ParB K)) : ModGL Tag.G2 K) =
            (x : ModGL Tag.G2 K) := by
          rw [← hθ q1, hθ_q1, ← hiota qa, hiota_qa]
        rw [hq1ψ]

private theorem transportAut_conj_pinnedX_r {K : Type} [Field K] [Finite K] [CharP K 2]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {x₁ : G} (hx₁P2 : x₁ ∈ L2 ⊔ bigB L1 L2 S)
    (hx₁N : x₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hx₁X : ∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) = x₁ →
      (((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        pinnedX Tag.G2 K g2r 1)
    (x : ↥(parabolicRadical Tag.G2 K {i1})) :
    ((transportAut θ iota (conjAut x₁ hx₁N) x : ↥(parabolicRadical Tag.G2 K {i1})) :
        ModGL Tag.G2 K) =
      pinnedX Tag.G2 K g2r 1 * (x : ModGL Tag.G2 K) * pinnedX Tag.G2 K g2r 1 := by
  have h1 := transportAut_conj_apply (ψ₂ := ψ₂) hQ1P θ hθ iota hiota hx₁P2 hx₁N
    (conjAut x₁ hx₁N) (fun z => conjAut_apply x₁ hx₁N z) x
  rw [h1, hx₁X ⟨x₁, hx₁P2⟩ rfl]
  have hXinv : (pinnedX Tag.G2 K g2r 1)⁻¹ = pinnedX Tag.G2 K g2r 1 := by
    rw [pinnedX_neg]
    simp only [CharTwo.neg_eq]
  rw [hXinv]

private theorem conjAut_trans_pow_three {Q : Subgroup G} (x w : G)
    (hxN : x ∈ Subgroup.normalizer (Q : Set G))
    (hwN : w ∈ Subgroup.normalizer (Q : Set G))
    (hcube : (w * x) ^ 3 = 1) :
    ((conjAut x hxN).trans (conjAut w hwN)).trans
        (((conjAut x hxN).trans (conjAut w hwN)).trans
          ((conjAut x hxN).trans (conjAut w hwN))) =
      MulEquiv.refl (↥Q) := by
  have hconj : (conjAut x hxN).trans (conjAut w hwN) =
      conjAut (w * x) (Subgroup.mul_mem (Subgroup.normalizer (Q : Set G)) hwN hxN) :=
    conjAut_trans x w hxN hwN
  rw [hconj]
  refine MulEquiv.ext fun z => ?_
  apply Subtype.ext
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.refl_apply]
  rw [conjAut_apply, conjAut_apply, conjAut_apply]
  calc (w * x) * ((w * x) * ((w * x) * (z : G) * (w * x)⁻¹) * (w * x)⁻¹) *
        (w * x)⁻¹
      = ((w * x) * (w * x) * (w * x)) * (z : G) *
          ((w * x) * (w * x) * (w * x))⁻¹ := by group
    _ = (z : G) := by
        rw [pow_three'] at hcube
        rw [hcube]
        group

private theorem transportAut_cube {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (ex ew : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1))
    (Ψe cre : ↥(parabolicRadical Tag.G2 K {i1}) ≃*
      ↥(parabolicRadical Tag.G2 K {i1}))
    (hΨe : Ψe = transportAut θ iota ew)
    (hcre : cre = transportAut θ iota ex)
    (heF3 : (ex.trans ew).trans ((ex.trans ew).trans (ex.trans ew)) =
      MulEquiv.refl (↥(pCoreOf 2 L1))) :
    ∀ x : ↥(parabolicRadical Tag.G2 K {i1}),
      Ψe.toMonoidHom (cre.toMonoidHom (Ψe.toMonoidHom (cre.toMonoidHom
        (Ψe.toMonoidHom (cre.toMonoidHom x))))) = x := by
  intro x
  rw [hΨe, hcre]
  have hF : (transportAut θ iota ex).trans (transportAut θ iota ew) =
      transportAut θ iota (ex.trans ew) := transportAut_trans θ iota ex ew
  have hX : (transportAut θ iota (ex.trans ew)).trans
      (transportAut θ iota (ex.trans ew)) =
      transportAut θ iota ((ex.trans ew).trans (ex.trans ew)) :=
    transportAut_trans θ iota (ex.trans ew) (ex.trans ew)
  have hF3 : ((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
      (((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
        ((transportAut θ iota ex).trans (transportAut θ iota ew))) =
      MulEquiv.refl (↥(parabolicRadical Tag.G2 K {i1})) := by
    calc ((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
          (((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
            ((transportAut θ iota ex).trans (transportAut θ iota ew)))
        = (transportAut θ iota (ex.trans ew)).trans
            ((transportAut θ iota (ex.trans ew)).trans
              (transportAut θ iota (ex.trans ew))) := by rw [hF]
      _ = (transportAut θ iota (ex.trans ew)).trans
            (transportAut θ iota ((ex.trans ew).trans (ex.trans ew))) := by rw [hX]
      _ = transportAut θ iota ((ex.trans ew).trans ((ex.trans ew).trans
            (ex.trans ew))) := transportAut_trans θ iota (ex.trans ew)
            ((ex.trans ew).trans (ex.trans ew))
      _ = MulEquiv.refl (↥(parabolicRadical Tag.G2 K {i1})) := by
            rw [heF3, transportAut_refl]
  change (((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
    (((transportAut θ iota ex).trans (transportAut θ iota ew)).trans
      ((transportAut θ iota ex).trans (transportAut θ iota ew)))) x = x
  rw [hF3]
  rfl

private theorem transportAut_torusASub {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {w₁ : G} (hw₁N : w₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hw₁C : w₁ ∈ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) :
    ∀ (s : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
      (y : ModGL Tag.G2 K) = G2q.dT s 1 * (x : ModGL Tag.G2 K) * (G2q.dT s 1)⁻¹ →
        ((transportAut θ iota (conjAut w₁ hw₁N)) y : ModGL Tag.G2 K) =
          G2q.dT s 1 * ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) *
            (G2q.dT s 1)⁻¹ := by
  intro s x y hy
  let aA : ↥(adjointGroup Tag.G2 K) := ⟨G2q.dT s 1, G2q.dT_mem_adjointGroup s 1⟩
  have haT : aA ∈ G2q.torusASub K := G2q.mem_torusASub_iff.2 ⟨s, rfl⟩
  have haB : aA ∈ g2ParB K := G2q.torusASub_le_g2ParB haT
  let aP : ↥(g2ParB K) := ⟨aA, haB⟩
  let uP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm aP
  have hψu : ψ₂ uP = aP := ψ₂.apply_symm_apply aP
  have huH0 : (uP : G) ∈ H ⊓ trivOTwoQuot L1 :=
    (hD.mem_trivOTwoQuot_iff_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard
      hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H uP).2 (by rw [hψu]; exact haT)
  have huB : (uP : G) ∈ bigB L1 L2 S := hHB (Subgroup.mem_inf.mp huH0).1
  have huN : (uP : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    hH.bigB_le_normalizer_pCoreOf_left huB
  have hwu : (uP : G) * w₁ = w₁ * (uP : G) :=
    Subgroup.mem_centralizer_iff.mp hw₁C (uP : G) huH0
  let eu : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1) := conjAut (uP : G) huN
  let ca : ↥(parabolicRadical Tag.G2 K {i1}) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
    transportAut θ iota eu
  have hca : ∀ z : ↥(parabolicRadical Tag.G2 K {i1}),
      (ca z : ModGL Tag.G2 K) = G2q.dT s 1 * (z : ModGL Tag.G2 K) * (G2q.dT s 1)⁻¹ := by
    intro z
    have h1 := transportAut_conj_apply (ψ₂ := ψ₂) hQ1P θ hθ iota hiota uP.2 huN
      eu (fun w => conjAut_apply (uP : G) huN w) z
    rw [h1, hψu]
  have hyca : y = ca x := Subtype.ext (by rw [hca x]; exact hy)
  have heu_ew : eu.trans (conjAut w₁ hw₁N) = (conjAut w₁ hw₁N).trans eu := by
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [conjAut_apply, conjAut_apply, conjAut_apply, conjAut_apply]
    calc w₁ * ((uP : G) * (z : G) * (uP : G)⁻¹) * w₁⁻¹
        = (w₁ * (uP : G)) * (z : G) * (w₁ * (uP : G))⁻¹ := by group
      _ = ((uP : G) * w₁) * (z : G) * ((uP : G) * w₁)⁻¹ := by rw [hwu]
      _ = (uP : G) * (w₁ * (z : G) * w₁⁻¹) * (uP : G)⁻¹ := by group
  have hcomm : (transportAut θ iota (conjAut w₁ hw₁N)) (ca x) =
      ca ((transportAut θ iota (conjAut w₁ hw₁N)) x) := by
    have hΨca : (transportAut θ iota (conjAut w₁ hw₁N)).trans ca =
        transportAut θ iota ((conjAut w₁ hw₁N).trans eu) :=
      transportAut_trans θ iota (conjAut w₁ hw₁N) eu
    have hcaΨ : ca.trans (transportAut θ iota (conjAut w₁ hw₁N)) =
        transportAut θ iota (eu.trans (conjAut w₁ hw₁N)) :=
      transportAut_trans θ iota eu (conjAut w₁ hw₁N)
    calc (transportAut θ iota (conjAut w₁ hw₁N)) (ca x) =
        (ca.trans (transportAut θ iota (conjAut w₁ hw₁N))) x := rfl
      _ = transportAut θ iota (eu.trans (conjAut w₁ hw₁N)) x := by rw [hcaΨ]
      _ = transportAut θ iota ((conjAut w₁ hw₁N).trans eu) x := by rw [heu_ew]
      _ = ((transportAut θ iota (conjAut w₁ hw₁N)).trans ca) x := by rw [hΨca]
      _ = ca ((transportAut θ iota (conjAut w₁ hw₁N)) x) := rfl
  change ((transportAut θ iota (conjAut w₁ hw₁N)) y : ModGL Tag.G2 K) =
    G2q.dT s 1 * ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) *
      (G2q.dT s 1)⁻¹
  rw [hyca, hcomm, hca ((transportAut θ iota (conjAut w₁ hw₁N)) x)]

private theorem transportAut_conj_levi_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {H : Subgroup G} {l : Kˣ} {w₁ : G}
    (hw₁N : w₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hw₁Inv : ∀ t ∈ H ⊓ L1, w₁ * t * w₁⁻¹ = t⁻¹)
    {uP : ↥(L2 ⊔ bigB L1 L2 S)}
    (huHL : (uP : G) ∈ H ⊓ L1)
    (huN : (uP : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    {aP : ↥(g2ParB K)} (hψu : ψ₂ uP = aP)
    (haP : ((aP : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      G2q.dT (l⁻¹ ^ 3) (l ^ 2)) :
    (∀ z : ↥(parabolicRadical Tag.G2 K {i1}),
      ((transportAut θ iota (conjAut (uP : G) huN)) z : ModGL Tag.G2 K) =
        G2q.dT (l⁻¹ ^ 3) (l ^ 2) * (z : ModGL Tag.G2 K) *
          (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹) ∧
    (∀ z : ↥(parabolicRadical Tag.G2 K {i1}),
      ((transportAut θ iota (conjAut (uP : G) huN)).symm z : ModGL Tag.G2 K) =
        (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ * (z : ModGL Tag.G2 K) *
          G2q.dT (l⁻¹ ^ 3) (l ^ 2)) ∧
    ((conjAut (uP : G) huN).trans (conjAut w₁ hw₁N) =
      (conjAut w₁ hw₁N).trans (conjAut (uP : G) huN).symm) := by
  let eu : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1) := conjAut (uP : G) huN
  let ca : ↥(parabolicRadical Tag.G2 K {i1}) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
    transportAut θ iota eu
  have hca : ∀ z : ↥(parabolicRadical Tag.G2 K {i1}),
      (ca z : ModGL Tag.G2 K) =
        G2q.dT (l⁻¹ ^ 3) (l ^ 2) * (z : ModGL Tag.G2 K) *
          (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ := by
    intro z
    have h1 := transportAut_conj_apply (ψ₂ := ψ₂) hQ1P θ hθ iota hiota uP.2 huN
      eu (fun w => conjAut_apply (uP : G) huN w) z
    rw [h1, hψu, haP]
  have hcasymm : ∀ z : ↥(parabolicRadical Tag.G2 K {i1}),
      (ca.symm z : ModGL Tag.G2 K) =
        (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ * (z : ModGL Tag.G2 K) *
          G2q.dT (l⁻¹ ^ 3) (l ^ 2) := by
    intro z
    have h3 : G2q.dT (l⁻¹ ^ 3) (l ^ 2) * (ca.symm z : ModGL Tag.G2 K) *
        (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ = (z : ModGL Tag.G2 K) := by
      have h4 := congrArg (fun w : ↥(parabolicRadical Tag.G2 K {i1}) =>
        (w : ModGL Tag.G2 K)) (ca.apply_symm_apply z)
      rwa [hca (ca.symm z)] at h4
    rw [← h3]
    group
  have hwu : w₁ * (uP : G) = (uP : G)⁻¹ * w₁ := by
    have h := hw₁Inv (uP : G) huHL
    calc w₁ * (uP : G) = (w₁ * (uP : G) * w₁⁻¹) * w₁ := by group
      _ = (uP : G)⁻¹ * w₁ := by rw [h]
  have heq : eu.trans (conjAut w₁ hw₁N) = (conjAut w₁ hw₁N).trans eu.symm := by
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [conjAut_apply, conjAut_apply, conjAut_symm]
    rw [conjAut_apply (g := (uP : G)⁻¹)
      (hg := Subgroup.inv_mem (Subgroup.normalizer (pCoreOf 2 L1 : Set G)) huN)]
    rw [conjAut_apply]
    calc w₁ * ((uP : G) * (z : G) * (uP : G)⁻¹) * w₁⁻¹
        = (w₁ * (uP : G)) * (z : G) * (w₁ * (uP : G))⁻¹ := by group
      _ = ((uP : G)⁻¹ * w₁) * (z : G) * ((uP : G)⁻¹ * w₁)⁻¹ := by rw [hwu]
      _ = (uP : G)⁻¹ * (w₁ * (z : G) * w₁⁻¹) * (uP : G)⁻¹⁻¹ := by
          rw [mul_inv_rev]
          group
  exact ⟨hca, hcasymm, heq⟩

private theorem transportAut_levi_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {w₁ : G} (hw₁N : w₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hw₁Inv : ∀ t ∈ H ⊓ L1, w₁ * t * w₁⁻¹ = t⁻¹) :
    ∀ (l : Kˣ) (x y : ↥(parabolicRadical Tag.G2 K {i1})),
      (y : ModGL Tag.G2 K) = G2q.dT (l⁻¹ ^ 3) (l ^ 2) * (x : ModGL Tag.G2 K) *
        (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ →
        ((transportAut θ iota (conjAut w₁ hw₁N)) y : ModGL Tag.G2 K) =
          (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ *
            ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) *
              G2q.dT (l⁻¹ ^ 3) (l ^ 2) := by
  intro l x y hy
  let aA : ↥(adjointGroup Tag.G2 K) :=
    ⟨G2q.dT (l⁻¹ ^ 3) (l ^ 2), G2q.dT_mem_adjointGroup _ _⟩
  have haT : aA ∈ torusSub Tag.G2 K ⊓ G2q.leviASub K :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (G2q.dT_mem_torusGroup _ _),
      G2q.mem_leviASub_of_eq_dT l rfl⟩
  have haB : aA ∈ g2ParB K := G2q.torusSub_inf_leviASub_le_g2ParB haT
  let aP : ↥(g2ParB K) := ⟨aA, haB⟩
  let uP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm aP
  have hψu : ψ₂ uP = aP := ψ₂.apply_symm_apply aP
  have huHL : (uP : G) ∈ H ⊓ L1 :=
    (hD.mem_inf_left_iff_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
      ψ₂ hψ₂Q hψ₂H uP).2 (by rw [hψu]; exact haT)
  have huL1 : (uP : G) ∈ L1 := (Subgroup.mem_inf.mp huHL).2
  have huN : (uP : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    le_normalizer_pCoreOf 2 L1 huL1
  obtain ⟨hca, hcasymm, heq⟩ :=
    transportAut_conj_levi_torus (H := H) (l := l) (w₁ := w₁) (uP := uP)
      (aP := aP) ψ₂ hQ1P θ hθ iota hiota hw₁N hw₁Inv huHL huN hψu
      (by dsimp only [aP, aA])
  have hyca : y = transportAut θ iota (conjAut (uP : G) huN) x :=
    Subtype.ext (by rw [hca x]; exact hy)
  have hcomm : (transportAut θ iota (conjAut w₁ hw₁N))
      (transportAut θ iota (conjAut (uP : G) huN) x) =
      (transportAut θ iota (conjAut (uP : G) huN)).symm
        ((transportAut θ iota (conjAut w₁ hw₁N)) x) := by
    have hcaΨ : (transportAut θ iota (conjAut (uP : G) huN)).trans
        (transportAut θ iota (conjAut w₁ hw₁N)) =
        transportAut θ iota ((conjAut (uP : G) huN).trans (conjAut w₁ hw₁N)) :=
      transportAut_trans θ iota (conjAut (uP : G) huN) (conjAut w₁ hw₁N)
    have hΨcasymm : (transportAut θ iota (conjAut w₁ hw₁N)).trans
        (transportAut θ iota (conjAut (uP : G) huN)).symm =
        transportAut θ iota ((conjAut w₁ hw₁N).trans (conjAut (uP : G) huN).symm) := by
      rw [show (transportAut θ iota (conjAut (uP : G) huN)).symm =
          transportAut θ iota (conjAut (uP : G) huN).symm from
        transportAut_symm θ iota (conjAut (uP : G) huN)]
      exact transportAut_trans θ iota (conjAut w₁ hw₁N) (conjAut (uP : G) huN).symm
    calc (transportAut θ iota (conjAut w₁ hw₁N))
          (transportAut θ iota (conjAut (uP : G) huN) x)
        = ((transportAut θ iota (conjAut (uP : G) huN)).trans
            (transportAut θ iota (conjAut w₁ hw₁N))) x := rfl
      _ = transportAut θ iota ((conjAut (uP : G) huN).trans
            (conjAut w₁ hw₁N)) x := by rw [hcaΨ]
      _ = transportAut θ iota ((conjAut w₁ hw₁N).trans
            (conjAut (uP : G) huN).symm) x := by rw [heq]
      _ = ((transportAut θ iota (conjAut w₁ hw₁N)).trans
            (transportAut θ iota (conjAut (uP : G) huN)).symm) x := by rw [hΨcasymm]
      _ = (transportAut θ iota (conjAut (uP : G) huN)).symm
            ((transportAut θ iota (conjAut w₁ hw₁N)) x) := rfl
  change ((transportAut θ iota (conjAut w₁ hw₁N)) y : ModGL Tag.G2 K) =
    (G2q.dT (l⁻¹ ^ 3) (l ^ 2))⁻¹ *
      ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) *
        G2q.dT (l⁻¹ ^ 3) (l ^ 2)
  rw [hyca, hcomm, hcasymm ((transportAut θ iota (conjAut w₁ hw₁N)) x)]

private theorem transportAut_center {K : Type} [Field K] [Finite K] [CharP K 2]
    (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    {w₁ : G} (hw₁L1 : w₁ ∈ L1)
    (hw₁N : w₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G)) :
    ∀ (c : K) (x : ↥(parabolicRadical Tag.G2 K {i1})),
      (x : ModGL Tag.G2 K) = pinnedX Tag.G2 K g2c c →
        ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) =
          pinnedX Tag.G2 K g2c c := by
  intro c x hx
  have hxZ' : (iota.symm x : ↥(adjointGroup Tag.G2 K)) ∈
      centerOf (pCoreOf 2 (g2ParA K)) := by
    rw [G2q.mem_centerOf_pCoreOf_g2ParA_iff]
    refine ⟨c, ?_⟩
    rw [← hiota (iota.symm x), iota.apply_symm_apply x, hx]
  let bP : ↥(g2ParB K) :=
    ⟨(iota.symm x : ↥(adjointGroup Tag.G2 K)),
      G2q.pCoreOf_g2ParA_le_g2ParB (iota.symm x).2⟩
  let zP : ↥(L2 ⊔ bigB L1 L2 S) := ψ₂.symm bP
  have hψz : ψ₂ zP = bP := ψ₂.apply_symm_apply bP
  have hzZ : (zP : G) ∈ centerOf (pCoreOf 2 L1) :=
    (G2qLocalData.mem_centerOf_left_iff_of_vertexTwo hH ψ₂ hψ₂Q zP).2 (by
      rw [hψz]
      exact hxZ')
  have hzL1 : (zP : G) ∈ centerOf L1 := by
    rwa [hD.center_left] at hzZ
  have hwz : w₁ * (zP : G) = (zP : G) * w₁ :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzL1).2 w₁ hw₁L1
  let q : ↥(pCoreOf 2 L1) := θ.symm (iota.symm x)
  have hqP2 : (q : G) ∈ L2 ⊔ bigB L1 L2 S := hQ1P q.2
  have hψqX : (((ψ₂ ⟨(q : G), hqP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
      ModGL Tag.G2 K) = (x : ModGL Tag.G2 K) := by
    rw [← hθ q]
    have hq : θ q = iota.symm x := θ.apply_symm_apply _
    rw [hq, ← hiota (iota.symm x), iota.apply_symm_apply x]
  have hψq : ψ₂ ⟨(q : G), hqP2⟩ = bP := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hψqX]
    change (x : ModGL Tag.G2 K) = (iota.symm x : ModGL Tag.G2 K)
    exact ((hiota (iota.symm x)).symm.trans (by rw [iota.apply_symm_apply])).symm
  have hzP' : (⟨(zP : G), hQ1P (Subgroup.mem_inf.mp hzZ).1⟩ :
      ↥(L2 ⊔ bigB L1 L2 S)) = zP := Subtype.ext rfl
  have hqeq : q = (⟨(zP : G), (Subgroup.mem_inf.mp hzZ).1⟩ : ↥(pCoreOf 2 L1)) := by
    have hqP : (⟨(q : G), hqP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) =
        (⟨(zP : G), hQ1P (Subgroup.mem_inf.mp hzZ).1⟩ : ↥(L2 ⊔ bigB L1 L2 S)) := by
      apply ψ₂.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [show ψ₂ ⟨(q : G), hqP2⟩ = bP from hψq, hzP', hψz]
    exact Subtype.ext (congrArg (fun w : ↥(L2 ⊔ bigB L1 L2 S) => (w : G)) hqP)
  have hewq : conjAut w₁ hw₁N q = q := by
    apply Subtype.ext
    rw [conjAut_apply, hqeq]
    rw [hwz]
    group
  have hΨx : ((transportAut θ iota (conjAut w₁ hw₁N)) x : ModGL Tag.G2 K) =
      (x : ModGL Tag.G2 K) := by
    rw [transportAut_apply]
    rw [show θ.symm (iota.symm x) = q from rfl, hewq]
    rw [show θ q = iota.symm x from θ.apply_symm_apply _, iota.apply_symm_apply x]
  rw [hΨx, hx]

private theorem partner_weyl_of_radA {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}))
    (hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))
    (ew : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1)) {w₁ : G}
    (hew : ∀ z : ↥(pCoreOf 2 L1), (ew z : G) = w₁ * (z : G) * w₁⁻¹)
    (hpartner : ∀ x : ↥(parabolicRadical Tag.G2 K {i1}),
      (transportAut θ iota ew x : ModGL Tag.G2 K) =
        weylElt Tag.G2 K g2ir 1 * (x : ModGL Tag.G2 K) *
          (weylElt Tag.G2 K g2ir 1)⁻¹) :
    ∃ n : ↥(adjointGroup Tag.G2 K), n ∈ G2q.leviASub K ∧
      ∀ x y : ↥(pCoreOf 2 L1), (y : G) = w₁ * (x : G) * w₁⁻¹ →
        (θ y : ↥(adjointGroup Tag.G2 K)) = n * (θ x) * n⁻¹ := by
  refine ⟨⟨weylElt Tag.G2 K g2ir 1,
    weylElt_mem_adjointGroup (τ := Tag.G2) (K := K) g2ir 1⟩, ?_, ?_⟩
  · exact G2q.weylElt_mem_leviASub
      (h := ⟨weylElt Tag.G2 K g2ir 1,
        weylElt_mem_adjointGroup (τ := Tag.G2) (K := K) g2ir 1⟩) rfl
  · intro x y hy
    have hyeq : y = ew x := Subtype.ext (by rw [hew x]; exact hy)
    let xa : ↥(parabolicRadical Tag.G2 K {i1}) := iota (θ x)
    have hxa : (xa : ModGL Tag.G2 K) = ((θ x : ↥(adjointGroup Tag.G2 K)) :
        ModGL Tag.G2 K) := hiota (θ x)
    have hΨxa : (transportAut θ iota ew xa : ModGL Tag.G2 K) =
        ((θ y : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) := by
      rw [transportAut_apply]
      have h1 : iota.symm xa = θ x := by
        apply iota.injective
        rw [show xa = iota (θ x) from rfl, iota.symm_apply_apply]
      rw [h1, θ.symm_apply_apply, hyeq]
      exact hiota (θ (ew x))
    have h := hpartner xa
    rw [hΨxa, hxa] at h
    exact Subtype.ext h

private theorem G2qLocalData.exists_weyl_vertexOne (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∃ x₁ w₁ : G,
      x₁ ∈ L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∧
      x₁ ∈ S ∧ x₁ ∉ pCoreOf 2 L1 ∧
      (∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) = x₁ →
        (((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
          pinnedX Tag.G2 K g2r 1) ∧
      w₁ ∈ L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∧
      (∀ t ∈ H ⊓ L1, w₁ * t * w₁⁻¹ = t⁻¹) ∧
      Subgroup.closure
        ((((L1 ⊓ Subgroup.centralizer
            ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊓
          Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w₁}) =
        (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ∧
      (w₁ * x₁) ^ 3 = 1 := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hfix : ∀ x ∈ pCoreOf 2 L1,
      (∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) → x = 1 :=
    hD.eq_one_of_mem_pCoreOf_left_of_commute hf hH h1 h2 hHB hSH hSinfH hHcard
      hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H
  obtain ⟨hsupQK, hinfQK, hHLK, -⟩ :=
    hD.vertexOne_complement hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hfix
  obtain ⟨x₁, hx₁K, hx₁S, hx₁Q, hx₁X⟩ :=
    hD.exists_mem_left_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
      ψ₂ hψ₂S hψ₂Q hψ₂H
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  letI := c1.field
  letI := c1.fintype
  haveI : CharP c1.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c1.card])
  have hTN : H ⊓ L1 ≤ Subgroup.normalizer (S : Set G) :=
    (inf_le_left.trans hHB).trans ((hD.bigB_le_normalizer hH h1 h2).trans inf_le_right)
  have hTcard : Nat.card ↥(H ⊓ L1) = Nat.card c1.F - 1 := by
    rw [(hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm).1, c1.card]
  obtain ⟨w₁, hw₁K, hw₁Inv, hw₁gen, hw₁cube⟩ :=
    exists_weyl_of_complement_pow_three (Q := pCoreOf 2 L1)
      (K := L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
      (T := H ⊓ L1) (S := S) (L := L1)
      c1.α c1.surj c1.ker (hD.le_left hH hf1 h1) c1.memS hsupQK hinfQK hHLK hTN hTcard
      (y := x₁) hx₁K hx₁S hx₁Q
  exact ⟨x₁, w₁, hx₁K, hx₁S, hx₁Q, hx₁X, hw₁K, hw₁Inv, hw₁gen, hw₁cube⟩

private theorem G2qLocalData.exists_partner_weyl (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    {x₁ w₁ : G}
    (hx₁K : x₁ ∈ L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
    (hx₁S : x₁ ∈ S) (hx₁Q : x₁ ∉ pCoreOf 2 L1)
    (hx₁X : ∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) = x₁ →
      (((ψ₂ y : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        pinnedX Tag.G2 K g2r 1)
    (hw₁K : w₁ ∈ L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
    (hw₁Inv : ∀ t ∈ H ⊓ L1, w₁ * t * w₁⁻¹ = t⁻¹)
    (hw₁cube : (w₁ * x₁) ^ 3 = 1) :
    ∃ n : ↥(adjointGroup Tag.G2 K), n ∈ G2q.leviASub K ∧
      ∀ x y : ↥(pCoreOf 2 L1), (y : G) = w₁ * (x : G) * w₁⁻¹ →
        (θ y : ↥(adjointGroup Tag.G2 K)) = n * (θ x) * n⁻¹ := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hf2 : 2 ≤ f := by omega
  have hK8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSL1 : S ≤ L1 := hD.le_left hH hf1 h1
  have hSL2 : S ≤ L2 := hD.le_right hH hf1 h2
  let iota : ↥(pCoreOf 2 (g2ParA K)) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
    pCoreOfG2ParAEquiv K
  have hiota : ∀ q : ↥(pCoreOf 2 (g2ParA K)),
      ((iota q : ↥(parabolicRadical Tag.G2 K {i1})) : ModGL Tag.G2 K) =
        ((q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) :=
    fun q => pCoreOfG2ParAEquiv_apply q
  have hw₁L1 : w₁ ∈ L1 := (Subgroup.mem_inf.mp hw₁K).1
  have hw₁N : w₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    le_normalizer_pCoreOf 2 L1 hw₁L1
  have hx₁L1 : x₁ ∈ L1 := (Subgroup.mem_inf.mp hx₁K).1
  have hx₁N : x₁ ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    le_normalizer_pCoreOf 2 L1 hx₁L1
  have hx₁P2 : x₁ ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_left (hSL2 hx₁S)
  have hw₁C : w₁ ∈ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hw₁K).2
  let ew : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1) := conjAut w₁ hw₁N
  let ex : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 L1) := conjAut x₁ hx₁N
  let Ψe : ↥(parabolicRadical Tag.G2 K {i1}) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
    transportAut θ iota ew
  let cre : ↥(parabolicRadical Tag.G2 K {i1}) ≃* ↥(parabolicRadical Tag.G2 K {i1}) :=
    transportAut θ iota ex
  have hcr : ∀ x : ↥(parabolicRadical Tag.G2 K {i1}),
      (cre.toMonoidHom x : ModGL Tag.G2 K) =
        pinnedX Tag.G2 K g2r 1 * (x : ModGL Tag.G2 K) * pinnedX Tag.G2 K g2r 1 :=
    fun x => transportAut_conj_pinnedX_r ψ₂ hQ1P θ hθ iota hiota hx₁P2 hx₁N hx₁X x
  have heF3 : (ex.trans ew).trans ((ex.trans ew).trans (ex.trans ew)) =
      MulEquiv.refl (↥(pCoreOf 2 L1)) :=
    conjAut_trans_pow_three x₁ w₁ hx₁N hw₁N hw₁cube
  have hcube := transportAut_cube θ iota ex ew Ψe cre rfl rfl heF3
  have hHrig := transportAut_torusASub hf2 hH hD h1 h2 hHB hSH hSinfH hHcard hHcomm hK
    ψ₂ hψ₂Q hψ₂S hψ₂H hQ1P θ hθ iota hiota hw₁N hw₁C
  have hTrig := transportAut_levi_torus hf2 hH hD h1 h2 hHB hSH hSinfH hHcard hHcomm hK
    ψ₂ hψ₂Q hψ₂H hQ1P θ hθ iota hiota hw₁N hw₁Inv
  have hcrig := transportAut_center hH hD ψ₂ hψ₂Q hQ1P θ hθ iota hiota hw₁L1 hw₁N
  have hpartner := G2q.radA_conj_eq_weyl (K := K) hK8 Ψe.toMonoidHom hHrig hTrig hcrig
    cre.toMonoidHom hcr hcube
  exact partner_weyl_of_radA θ iota hiota ew
    (fun z => conjAut_apply w₁ hw₁N z) hpartner

private theorem partner_of_psi₂ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (tP : ↥(L2 ⊔ bigB L1 L2 S)) {x y : ↥(pCoreOf 2 L1)}
    (hy : (y : G) = (tP : G) * (x : G) * (tP : G)⁻¹) :
    (θ y : ↥(adjointGroup Tag.G2 K)) =
      ((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * (θ x) *
        (((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))⁻¹) := by
  classical
  have hprod : (⟨(y : G), hQ1P y.2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) =
      tP * ⟨(x : G), hQ1P x.2⟩ * tP⁻¹ :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact hy)
  apply Subtype.ext
  calc ((θ y : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K)
      = (((ψ₂ ⟨(y : G), hQ1P y.2⟩ : ↥(g2ParB K)) :
          ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) := hθ y
    _ = (((ψ₂ (tP * ⟨(x : G), hQ1P x.2⟩ * tP⁻¹) : ↥(g2ParB K)) :
          ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) := by rw [hprod]
    _ = (((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) *
          ((((ψ₂ ⟨(x : G), hQ1P x.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
            ModGL Tag.G2 K)) *
          ((((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    _ = (((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) *
          ((θ x : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) *
          ((((ψ₂ tP : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K))⁻¹ := by
        rw [← hθ x]

private theorem closure_vertexOne {G : Type} [Group G] {K H0 N : Subgroup G} {w : G}
    (hw : Subgroup.closure (((K ⊓ N : Subgroup G) : Set G) ∪ {w}) = K) :
    Subgroup.closure (((K ⊓ N : Subgroup G) : Set G) ∪ (H0 : Set G) ∪ {w}) =
      K ⊔ H0 := by
  have hT : (((K ⊓ N : Subgroup G) : Set G) ∪ (H0 : Set G) ∪ {w}) =
      (((K ⊓ N : Subgroup G) : Set G) ∪ {w} ∪ (H0 : Set G)) := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [hT, Subgroup.closure_union, hw, Subgroup.closure_eq]

private theorem G2qLocalData.exists_partner_generators
    (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    {n : ↥(adjointGroup Tag.G2 K)} (hnR : n ∈ G2q.complA K) {w₁ : G}
    (hnpart : ∀ x y : ↥(pCoreOf 2 L1), (y : G) = w₁ * (x : G) * w₁⁻¹ →
      (θ y : ↥(adjointGroup Tag.G2 K)) = n * (θ x) * n⁻¹) :
    ∀ t ∈ ((((L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊓
        Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∪ {w₁}),
      ∃ t' ∈ G2q.complA K, ∀ x y : ↥(pCoreOf 2 L1), (y : G) = t * (x : G) * t⁻¹ →
        (θ y : ↥(adjointGroup Tag.G2 K)) = t' * (θ x) * t'⁻¹ := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hSL1 : S ≤ L1 := hD.le_left hH hf1 h1
  intro t ht
  rcases ht with (ht | ht) | ht
  · obtain ⟨htK, htN⟩ := Subgroup.mem_inf.mp ht
    obtain ⟨htL1, htC⟩ := Subgroup.mem_inf.mp htK
    have hborel : t ∈ borelOf L1 S := by
      rw [borelOf_eq_inf_of_le hSL1]
      exact ⟨htL1, htN⟩
    have htB : t ∈ bigB L1 L2 S :=
      (show borelOf L1 S ≤ bigB L1 L2 S from le_sup_left.trans le_sup_left) hborel
    have htP2 : t ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right htB
    have htcent : ∀ h ∈ H ⊓ trivOTwoQuot L1, h * t = t * h := by
      intro h hh
      exact Subgroup.mem_centralizer_iff.mp htC h hh
    refine ⟨((ψ₂ ⟨t, htP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)), ?_, ?_⟩
    · exact hD.mem_complA_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
        ψ₂ hψ₂S hψ₂Q hψ₂H ⟨t, htP2⟩ htB htcent
    · intro x y hy
      exact partner_of_psi₂ (x := x) (y := y) ψ₂ hQ1P θ hθ ⟨t, htP2⟩ hy
  · obtain ⟨htH, -⟩ := Subgroup.mem_inf.mp ht
    have htB : t ∈ bigB L1 L2 S := hHB htH
    have htP2 : t ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right htB
    have htcent : ∀ h ∈ H ⊓ trivOTwoQuot L1, h * t = t * h := by
      intro h hh
      exact hHcomm h (Subgroup.mem_inf.mp hh).1 t htH
    refine ⟨((ψ₂ ⟨t, htP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)), ?_, ?_⟩
    · exact hD.mem_complA_of_vertexTwo hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
        ψ₂ hψ₂S hψ₂Q hψ₂H ⟨t, htP2⟩ htB htcent
    · intro x y hy
      exact partner_of_psi₂ (x := x) (y := y) ψ₂ hQ1P θ hθ ⟨t, htP2⟩ hy
  · rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨n, hnR, hnpart⟩

private abbrev vertexOneR (L1 : Subgroup G) (H : Subgroup G) : Subgroup G :=
  (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
    (H ⊓ trivOTwoQuot L1)

private noncomputable def psiOne {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Subgroup G}
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K) :
    ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(g2ParA K) :=
  (MulEquiv.subgroupCongr hsupQR.symm).trans (ψ.trans (MulEquiv.subgroupCongr hQ'R'))

private theorem psiOne_val {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Subgroup G}
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K) :
    ∀ (x : G) (hx : x ∈ L1 ⊔ bigB L1 L2 S),
      ((psiOne ψ hsupQR hQ'R' ⟨x, hx⟩ : ↥(g2ParA K)) : ↥(adjointGroup Tag.G2 K)) =
        (ψ ⟨x, hsupQR.symm ▸ hx⟩ :
          ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) := by
  intro x hx
  dsimp only [psiOne]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : (MulEquiv.subgroupCongr hsupQR.symm ⟨x, hx⟩ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H)) =
      ⟨x, hsupQR.symm ▸ hx⟩ :=
    Subtype.ext (MulEquiv.subgroupCongr_apply hsupQR.symm ⟨x, hx⟩)
  rw [h1]
  exact MulEquiv.subgroupCongr_apply hQ'R' (ψ ⟨x, hsupQR.symm ▸ hx⟩)

private theorem psiOne_mem_pCoreOf_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Subgroup G}
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hψQ : ∀ x : ↥(pCoreOf 2 L1),
      ((ψ ⟨x, Subgroup.mem_sup_left x.2⟩ :
        ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) :
          ↥(adjointGroup Tag.G2 K)) = θ x) :
    ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      (psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)) ∈
        pCoreOf 2 (g2ParA K) := by
  intro x
  constructor
  · intro hx
    have h1 : (⟨(x : G), hsupQR.symm ▸ x.2⟩ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H)) =
        ⟨(x : G), Subgroup.mem_sup_left hx⟩ := Subtype.ext rfl
    rw [psiOne_val ψ hsupQR hQ'R' (x : G) x.2, h1, hψQ ⟨(x : G), hx⟩]
    exact (θ ⟨(x : G), hx⟩).2
  · intro hx
    obtain ⟨q, hq⟩ := θ.surjective
      ⟨(psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)), hx⟩
    have hxq : (ψ ⟨(x : G), hsupQR.symm ▸ x.2⟩ :
        ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) =
        (ψ ⟨(q : G), Subgroup.mem_sup_left q.2⟩ :
          ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) := by
      apply Subtype.ext
      calc ((ψ ⟨(x : G), hsupQR.symm ▸ x.2⟩ :
            ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) : ↥(adjointGroup Tag.G2 K))
          = (psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)) :=
            (psiOne_val ψ hsupQR hQ'R' (x : G) x.2).symm
        _ = (⟨(psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)), hx⟩ :
            ↥(pCoreOf 2 (g2ParA K))) := rfl
        _ = (θ q : ↥(pCoreOf 2 (g2ParA K))) := congrArg Subtype.val hq.symm
        _ = ((ψ ⟨(q : G), Subgroup.mem_sup_left q.2⟩ :
            ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) :
            ↥(adjointGroup Tag.G2 K)) := (hψQ q).symm
    have hxq' : (⟨(x : G), hsupQR.symm ▸ x.2⟩ :
        ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H)) =
        ⟨(q : G), Subgroup.mem_sup_left q.2⟩ := ψ.injective hxq
    have hxqG : (x : G) = (q : G) := congrArg Subtype.val hxq'
    rw [hxqG]
    exact q.2

private theorem psiOne_on_S_inf_K1 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf2 : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P2 : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P2 q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K)
    (hSP1 : S ≤ L1 ⊔ bigB L1 L2 S)
    (hSP2 : S ≤ L2 ⊔ bigB L1 L2 S)
    (hψpartner : ∀ r (hr : r ∈ vertexOneR L1 H), ∀ r' ∈ G2q.complA K,
      (∀ x y : ↥(pCoreOf 2 L1), (y : G) = r * (x : G) * r⁻¹ →
        (θ y : ↥(adjointGroup Tag.G2 K)) = r' * (θ x) * r'⁻¹) →
      (ψ ⟨r, Subgroup.mem_sup_right hr⟩ :
        ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K)) = r') :
    ∀ (s : G) (hsSK : s ∈ S ⊓
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))),
      (psiOne ψ hsupQR hQ'R'
        ⟨s, hSP1 (Subgroup.mem_inf.mp hsSK).1⟩ :
          ↥(adjointGroup Tag.G2 K)) =
        ((ψ₂ ⟨s, hSP2 (Subgroup.mem_inf.mp hsSK).1⟩ : ↥(g2ParB K)) :
          ↥(adjointGroup Tag.G2 K)) := by
  intro s hsSK
  obtain ⟨hsS, hsK⟩ := Subgroup.mem_inf.mp hsSK
  obtain ⟨hsL1, hsC⟩ := Subgroup.mem_inf.mp hsK
  have hSL1 : S ≤ L1 := hD.le_left hH (by omega) h1
  have hSL2 : S ≤ L2 := hD.le_right hH (by omega) h2
  have hsN : s ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer hsS
  have hborel : s ∈ borelOf L1 S := by
    rw [borelOf_eq_inf_of_le hSL1]
    exact ⟨hsL1, hsN⟩
  have hsB : s ∈ bigB L1 L2 S :=
    (show borelOf L1 S ≤ bigB L1 L2 S from le_sup_left.trans le_sup_left) hborel
  have hsP2 : s ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hsB
  have hscent : ∀ h ∈ H ⊓ trivOTwoQuot L1, h * s = s * h := by
    intro h hh
    exact Subgroup.mem_centralizer_iff.mp hsC h hh
  have haR : ((ψ₂ ⟨s, hsP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈
      G2q.complA K :=
    hD.mem_complA_of_vertexTwo hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
      ψ₂ hψ₂S hψ₂Q hψ₂H ⟨s, hsP2⟩ hsB hscent
  have hpart : ∀ x y : ↥(pCoreOf 2 L1), (y : G) = s * (x : G) * s⁻¹ →
      (θ y : ↥(adjointGroup Tag.G2 K)) =
        ((ψ₂ ⟨s, hsP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) * (θ x) *
          (((ψ₂ ⟨s, hsP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K))⁻¹) :=
    fun x y hy => partner_of_psi₂ (x := x) (y := y) ψ₂ hQ1P2 θ hθ ⟨s, hsP2⟩ hy
  have huniq := hψpartner s (Subgroup.mem_sup_left hsK)
    ((ψ₂ ⟨s, hsP2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) haR hpart
  rw [psiOne_val ψ hsupQR hQ'R' s (hSP1 hsS)]
  have heq : (⟨s, hsupQR.symm ▸ hSP1 hsS⟩ :
      ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H)) =
      ⟨s, Subgroup.mem_sup_right (Subgroup.mem_sup_left hsK)⟩ := Subtype.ext rfl
  rw [heq]
  exact huniq

private theorem vertexOne_s_decomp (hf2 : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1))
    {H : Subgroup G}
    (hsupQK : pCoreOf 2 L1 ⊔
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1) :
    S = pCoreOf 2 L1 ⊔
      (S ⊓ (L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))) := by
  have hSL1 : S ≤ L1 := hD.le_left hH (by omega) h1
  refine le_antisymm ?_ (sup_le hH.pCoreOf_le_left inf_le_left)
  intro z hz
  have hzL : z ∈ pCoreOf 2 L1 ⊔
      (L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) := by
    rw [hsupQK]
    exact hSL1 hz
  obtain ⟨q, hqQ, k, hkK, hqk⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := pCoreOf 2 L1)
      (K := L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))
      ((inf_le_left : (L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ≤ L1).trans
          (le_normalizer_pCoreOf 2 L1))).mp hzL
  have hkS : k ∈ S := by
    have hk : k = q⁻¹ * z := by rw [hqk]; group
    rw [hk]
    exact S.mul_mem (S.inv_mem (hH.pCoreOf_le_left hqQ)) hz
  have hkSK : k ∈ S ⊓ (L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) := Subgroup.mem_inf.mpr ⟨hkS, hkK⟩
  rw [hqk]
  exact (pCoreOf 2 L1 ⊔ (S ⊓ (L1 ⊓ Subgroup.centralizer
    ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)))).mul_mem
      (Subgroup.mem_sup_left hqQ) (Subgroup.mem_sup_right hkSK)

private theorem psiOne_maps_S_to_U {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf2 : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    {H : Subgroup G}
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hsupQK : pCoreOf 2 L1 ⊔
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1)
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K)
    (hSP1 : S ≤ L1 ⊔ bigB L1 L2 S)
    (hSP2 : S ≤ L2 ⊔ bigB L1 L2 S)
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      (psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₁s_eq : ∀ (s : G) (hsSK : s ∈ S ⊓
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))),
      (psiOne ψ hsupQR hQ'R'
        ⟨s, hSP1 (Subgroup.mem_inf.mp hsSK).1⟩ :
          ↥(adjointGroup Tag.G2 K)) =
        ((ψ₂ ⟨s, hSP2 (Subgroup.mem_inf.mp hsSK).1⟩ : ↥(g2ParB K)) :
          ↥(adjointGroup Tag.G2 K))) :
    ∀ (y : G) (hyS : y ∈ S),
      (psiOne ψ hsupQR hQ'R' ⟨y, hSP1 hyS⟩ : ↥(adjointGroup Tag.G2 K)) ∈
        posUnipotentSub Tag.G2 K := by
  intro y hyS
  have hSL1 : S ≤ L1 := hD.le_left hH (by omega) h1
  have hNK : S ⊓ (L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    inf_le_right.trans (inf_le_left.trans (le_normalizer_pCoreOf 2 L1))
  have hSdecomp : S = pCoreOf 2 L1 ⊔
      (S ⊓ (L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))) :=
    vertexOne_s_decomp (by omega) hH hD h1 hsupQK
  obtain ⟨q, hqQ, s, hsSK, hqs⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := pCoreOf 2 L1)
      (K := S ⊓ (L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G))) hNK).mp (hSdecomp ▸ hyS)
  have hQ1P1 : pCoreOf 2 L1 ≤ L1 ⊔ bigB L1 L2 S :=
    (hH.pCoreOf_le_left.trans hSL1).trans le_sup_left
  have hqP1 : q ∈ L1 ⊔ bigB L1 L2 S := hQ1P1 hqQ
  have hsP1 : s ∈ L1 ⊔ bigB L1 L2 S := hSP1 (Subgroup.mem_inf.mp hsSK).1
  have hQAU : pCoreOf 2 (g2ParA K) ≤ posUnipotentSub Tag.G2 K := by
    intro z hz
    rw [posUnipotentSub, Subgroup.mem_subgroupOf]
    exact (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1})
      (G2q.mem_pCoreOf_g2ParA_iff.mp hz)
  have hqU : (psiOne ψ hsupQR hQ'R' ⟨q, hqP1⟩ : ↥(adjointGroup Tag.G2 K)) ∈
      posUnipotentSub Tag.G2 K :=
    hQAU ((hψ₁Q ⟨q, hqP1⟩).mp hqQ)
  have hsU : (psiOne ψ hsupQR hQ'R' ⟨s, hsP1⟩ : ↥(adjointGroup Tag.G2 K)) ∈
      posUnipotentSub Tag.G2 K := by
    rw [hψ₁s_eq s hsSK]
    exact (hψ₂S ⟨s, hSP2 (Subgroup.mem_inf.mp hsSK).1⟩).mp
      (Subgroup.mem_inf.mp hsSK).1
  have hprod : (⟨y, hSP1 hyS⟩ : ↥(L1 ⊔ bigB L1 L2 S)) =
      ⟨q, hqP1⟩ * ⟨s, hsP1⟩ := Subtype.ext hqs
  rw [hprod, map_mul]
  simpa only [Subgroup.coe_mul] using Subgroup.mul_mem
    (posUnipotentSub Tag.G2 K) hqU hsU

private theorem psiOne_mem_s_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    (hD : G2qLocalData L1 L2 S f)
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    {H : Subgroup G}
    (hsupQK : pCoreOf 2 L1 ⊔
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1)
    (ψ : ↥(pCoreOf 2 L1 ⊔ vertexOneR L1 H) ≃*
      ↥(pCoreOf 2 (g2ParA K) ⊔ G2q.complA K))
    (hsupQR : pCoreOf 2 L1 ⊔ vertexOneR L1 H = L1 ⊔ bigB L1 L2 S)
    (hQ'R' : pCoreOf 2 (g2ParA K) ⊔ G2q.complA K = g2ParA K)
    (hSP1 : S ≤ L1 ⊔ bigB L1 L2 S)
    (hSP2 : S ≤ L2 ⊔ bigB L1 L2 S)
    (hSU : ∀ (y : G) (hyS : y ∈ S),
      (psiOne ψ hsupQR hQ'R' ⟨y, hSP1 hyS⟩ : ↥(adjointGroup Tag.G2 K)) ∈
        posUnipotentSub Tag.G2 K) :
    ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      (psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)) ∈
        posUnipotentSub Tag.G2 K := by
  have hUA : posUnipotentSub Tag.G2 K ≤ g2ParA K := by
    have hboreA : borelSub Tag.G2 K ≤ g2ParA K := by
      intro z hz
      rw [borelSub, Subgroup.mem_subgroupOf] at hz
      rw [g2ParA, Subgroup.mem_subgroupOf]
      exact borelGroup_le_parabolicSubgroup {g2Index 1} hz
    exact posUnipotentSub_le_borelSub.trans hboreA
  have hSmap : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      (psiOne ψ hsupQR hQ'R').toMonoidHom ≤
      (posUnipotentSub Tag.G2 K).subgroupOf (g2ParA K) := by
    rintro z ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (hSU (y : G) (Subgroup.mem_subgroupOf.mp hy))
  have hcardImage : Nat.card ↥((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      (psiOne ψ hsupQR hQ'R').toMonoidHom) = Nat.card ↥S := by
    rw [Subgroup.card_map_of_injective (psiOne ψ hsupQR hQ'R').injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP1).toEquiv
  have hcardS : Nat.card ↥S = Nat.card ↥(posUnipotentSub Tag.G2 K) :=
    Nat.card_congr (restrictEquiv ψ₂ hSP2 hψ₂S G2q.posUnipotentSub_le_g2ParB).toEquiv
  have hcardU : Nat.card ↥((posUnipotentSub Tag.G2 K).subgroupOf (g2ParA K)) =
      Nat.card ↥(posUnipotentSub Tag.G2 K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv
  have hSeq : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map
      (psiOne ψ hsupQR hQ'R').toMonoidHom =
      (posUnipotentSub Tag.G2 K).subgroupOf (g2ParA K) :=
    Subgroup.eq_of_le_of_card_ge hSmap (by rw [hcardImage, hcardU, hcardS])
  intro x
  constructor
  · intro hx
    exact hSU (x : G) hx
  · intro hx
    have hx' : (⟨(psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)),
        (psiOne ψ hsupQR hQ'R' x).2⟩ : ↥(g2ParA K)) ∈
        (posUnipotentSub Tag.G2 K).subgroupOf (g2ParA K) :=
      Subgroup.mem_subgroupOf.mpr hx
    have hmem : psiOne ψ hsupQR hQ'R' x ∈
        (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map
          (psiOne ψ hsupQR hQ'R').toMonoidHom := by
      rw [hSeq]
      exact hx'
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp hmem
    have hxs : s = x := (psiOne ψ hsupQR hQ'R').injective hse
    rw [← hxs]
    exact Subgroup.mem_subgroupOf.mp hs

private theorem exists_generators_T {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf2 : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K)
    (hQ1P2 : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S)
    (θ : ↥(pCoreOf 2 L1) ≃* ↥(pCoreOf 2 (g2ParA K)))
    (hθ : ∀ q : ↥(pCoreOf 2 L1),
      ((θ q : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P2 q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K))
    {n : ↥(adjointGroup Tag.G2 K)} (hnR : n ∈ G2q.complA K)
    {w₁ : G}
    (hw₁gen : Subgroup.closure
      (((((L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊓
        Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w₁})) =
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)))
    (hnpart : ∀ x y : ↥(pCoreOf 2 L1), (y : G) = w₁ * (x : G) * w₁⁻¹ →
      (θ y : ↥(adjointGroup Tag.G2 K)) = n * (θ x) * n⁻¹) :
    ∃ T : Set G, Subgroup.closure T = vertexOneR L1 H ∧
      ∀ t ∈ T, ∃ t' ∈ G2q.complA K, ∀ x y : ↥(pCoreOf 2 L1),
        (y : G) = t * (x : G) * t⁻¹ →
          (θ y : ↥(adjointGroup Tag.G2 K)) = t' * (θ x) * t'⁻¹ := by
  refine ⟨(((L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊓
        Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∪ {w₁}, ?_, ?_⟩
  · change Subgroup.closure
      ((((L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊓
          Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∪ {w₁}) =
      (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L1)
    exact closure_vertexOne hw₁gen
  · intro t ht
    exact hD.exists_partner_generators hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK
      ψ₂ hψ₂Q hψ₂S hψ₂H hQ1P2 θ hθ hnR hnpart t ht

private theorem G2qLocalData.exists_mulEquiv_vertexOne_of_hall
    (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K)
    (hψ₂H : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ H ↔
      (((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈
        torusGroup Tag.G2 K) :
    ∃ ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(g2ParA K),
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
        ((ψ₁ x : ↥(g2ParA K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K)) ∧
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
        ((ψ₁ x : ↥(g2ParA K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) := by
  classical
  have hf2 : 2 ≤ f := by omega
  let Q1 : Subgroup G := pCoreOf 2 L1
  let H0 : Subgroup G := H ⊓ trivOTwoQuot L1
  let K1 : Subgroup G := L1 ⊓ Subgroup.centralizer (H0 : Set G)
  let R : Subgroup G := K1 ⊔ H0
  let R' : Subgroup ↥(adjointGroup Tag.G2 K) := G2q.complA K
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  have hfix : ∀ x ∈ Q1, (∀ h ∈ H0, h * x * h⁻¹ = x) → x = 1 :=
    hD.eq_one_of_mem_pCoreOf_left_of_commute hf2 hH h1 h2 hHB hSH hSinfH hHcard
      hHcomm hK ψ₂ hψ₂S hψ₂Q hψ₂H
  obtain ⟨hsupQK, hinfQK, hHLK, hsupQR⟩ :=
    hD.vertexOne_complement hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hfix
  obtain ⟨hdisjQR, hRnorm, hfaithR⟩ :=
    hD.vertexOne_complement_semidirect hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hfix
  have hcardR := hD.card_vertexOne_complement hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hfix
  obtain ⟨x₁, w₁, hx₁K, hx₁S, hx₁Q, hx₁X, hw₁K, hw₁Inv, hw₁gen, hw₁cube⟩ :=
    hD.exists_weyl_vertexOne hf2 hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK ψ₂ hψ₂Q hψ₂S hψ₂H
  have hSL2 : S ≤ L2 := hD.le_right hH (by omega) h2
  have hQ1P2 : Q1 ≤ P2 :=
    (hH.pCoreOf_le_left.trans hSL2).trans (le_sup_left : L2 ≤ P2)
  let θ : ↥Q1 ≃* ↥(pCoreOf 2 (g2ParA K)) :=
    restrictEquiv ψ₂ hQ1P2 hψ₂Q G2q.pCoreOf_g2ParA_le_g2ParB
  have hθ : ∀ q : ↥Q1,
      (((θ q : ↥(pCoreOf 2 (g2ParA K))) : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
        (((ψ₂ ⟨(q : G), hQ1P2 q.2⟩ : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) :
          ModGL Tag.G2 K) := by
    intro q
    rw [show (θ q : ↥(pCoreOf 2 (g2ParA K))) =
        restrictEquiv ψ₂ hQ1P2 hψ₂Q G2q.pCoreOf_g2ParA_le_g2ParB q from rfl,
      restrictEquiv_apply]
  obtain ⟨n, hnL, hnpart⟩ :=
    hD.exists_partner_weyl hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm hK ψ₂ hψ₂Q hψ₂S
      hψ₂H hQ1P2 θ hθ hx₁K hx₁S hx₁Q hx₁X hw₁K hw₁Inv hw₁cube
  obtain ⟨T, hTgen, hTΘ⟩ := exists_generators_T hf2 hH hD h1 h2 hHB hSH hSinfH hHcard
    hHcomm hK ψ₂ hψ₂Q hψ₂S hψ₂H hQ1P2 θ hθ (Subgroup.mem_sup_left hnL) hw₁gen hnpart
  have hR'norm := G2q.complA_le_normalizer (K := K)
  have hdisj' : Disjoint (pCoreOf 2 (g2ParA K)) R' := G2q.disjoint_pCoreOf_complA
  have hfaith' : ∀ r ∈ R', (∀ x ∈ pCoreOf 2 (g2ParA K), r * x = x * r) → r = 1 :=
    fun r hr hc => G2q.eq_one_of_mem_complA_of_commute hr hc
  have hcard : Nat.card ↥R = Nat.card ↥R' := by
    rw [show Nat.card ↥R = Nat.card ↥((L1 ⊓ Subgroup.centralizer
      ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
        (H ⊓ trivOTwoQuot L1)) from rfl, hcardR, G2q.card_complA hK hf2]
  obtain ⟨ψ, hψQ, hψR, hψpartner⟩ := exists_mulEquiv_sup_of_conj
    hRnorm hdisjQR hR'norm hdisj' hfaithR hfaith' hcard θ hTgen hTΘ
  have hQ'R' : pCoreOf 2 (g2ParA K) ⊔ R' = g2ParA K := G2q.pCoreOf_sup_complA
  have hSP1 : S ≤ P1 := (hD.le_left hH (by omega) h1).trans le_sup_left
  have hSP2 : S ≤ P2 := (hD.le_right hH (by omega) h2).trans le_sup_left
  have hψ₁Q : ∀ x : ↥P1, (x : G) ∈ Q1 ↔
      (psiOne ψ hsupQR hQ'R' x : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K) :=
    psiOne_mem_pCoreOf_iff ψ hsupQR hQ'R' θ hψQ
  have hψ₁s_eq := psiOne_on_S_inf_K1 hf2 hH hD h1 h2 hHB hSH hSinfH hHcard hHcomm hK
    ψ₂ hψ₂Q hψ₂S hψ₂H hQ1P2 θ hθ ψ hsupQR hQ'R' hSP1 hSP2 hψpartner
  have hSU := psiOne_maps_S_to_U hf2 hH hD h1 h2 hK ψ₂ hψ₂Q hψ₂S hψ₂H hHB hSH hSinfH
    hHcard hHcomm hsupQK ψ hsupQR hQ'R' hSP1 hSP2 hψ₁Q hψ₁s_eq
  refine ⟨psiOne ψ hsupQR hQ'R', hψ₁Q, ?_⟩
  exact psiOne_mem_s_iff hD hK ψ₂ hψ₂S hsupQK ψ hsupQR hQ'R' hSP1 hSP2 hSU


theorem G2qLocalData.exists_mulEquiv_vertexOne (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(g2ParB K))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K))
    (hψ₂S : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ₂ x : ↥(g2ParB K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) :
    ∃ ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(g2ParA K),
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
        ((ψ₁ x : ↥(g2ParA K)) : ↥(adjointGroup Tag.G2 K)) ∈ pCoreOf 2 (g2ParA K)) ∧
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
        ((ψ₁ x : ↥(g2ParA K)) : ↥(adjointGroup Tag.G2 K)) ∈ posUnipotentSub Tag.G2 K) := by
  classical
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm, hψ₂H⟩ :=
    hD.exists_hall_of_vertexTwo hH h1 h2 hK ψ₂ hψ₂S
  exact hD.exists_mulEquiv_vertexOne_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
    hK ψ₂ hψ₂Q hψ₂S hψ₂H

end CFSG.Quasithin.F112R.St84

end
