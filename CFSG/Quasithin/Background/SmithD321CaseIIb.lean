module

public import CFSG.Quasithin.Background.SmithD321Q
public import CFSG.Quasithin.Background.SmithD310UInner
public import CFSG.Quasithin.Background.SmithD310UMat
public import CFSG.Quasithin.Background.F918XN2Aut
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.SmithD39TwoMod
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Open.StatedAPI
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.F918XY
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.GoldschmidtD35CoreOff3
public import CFSG.Quasithin.Background.SmithD310USetup
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Factor
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Walter.J1
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Quasithin.SmithD310U
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.F918X CFSG.QuasithinUnique
open scoped Pointwise

section IrrTop

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

private theorem iso_of_iso_map_injOn {A : Type*} [Group A] {Q₁ Q₂ : Type*} [CommGroup Q₁]
    [CommGroup Q₂] [MulDistribMulAction A Q₁] [MulDistribMulAction A Q₂] (θ : Q₁ →* Q₂)
    (hθ : ∀ (a : A) (x : Q₁), θ (a • x) = a • θ x) {S : Subgroup Q₁} (hS : XMod.IsInv A S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y) {L₁ L₂ : Subgroup Q₁} (h₁ : L₁ ≤ S)
    (h₂ : L₂ ≤ S) (h : XMod.Iso A (L₁.map θ) (L₂.map θ)) : XMod.Iso A L₁ L₂ := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θ hinj h₁
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θ hinj h₂
  refine ⟨e₁.trans (φ.trans e₂.symm), fun a l l' hll' => ?_⟩
  have hx : ∀ y : ↥(L₂.map θ), θ ((e₂.symm y : ↥L₂) : Q₁) = (y : Q₂) := fun y => by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have h1 : a • ((e₁ l : ↥(L₁.map θ)) : Q₂) = ((e₁ l' : ↥(L₁.map θ)) : Q₂) := by
    rw [he₁, he₁, ← hθ, hll']
  have h2 := hφ a _ _ h1
  apply hinj _ (hS a _ (h₂ (e₂.symm (φ (e₁ l))).2)) _ (h₂ (e₂.symm (φ (e₁ l'))).2)
  show θ (a • ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q₁)) = θ ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q₁)
  rw [hθ, hx, hx, h2]

theorem mem_irrPlusOn_of_le {X T : Subgroup G} {W W' : Subgroup V}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hWT : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W)
    (hWX : IsModInv X W) (hW'T : ∀ t ∈ T, ∀ w ∈ W', t • w ∈ W') (hWW' : W ≤ W')
    {I : Subgroup V} (hI : I ∈ IrrPlusOn X W T) : I ∈ IrrPlusOn X W' T := by
  have hI' : I ∈ IrrPlus X W' := ⟨hI.1.1.trans hWW', hI.1.2⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX hW'T hI').1 ?_
  rintro t ⟨ht, hiso⟩
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX hWT hI.1).2 hI t ⟨ht, ?_⟩
  have hle : modFix X W ≤ modFix X W' := XMod.fixed_mono hWW'
  let θ : V ⧸ modFix X W →* V ⧸ modFix X W' := QuotientGroup.map _ _ (MonoidHom.id V) hle
  have hθ : ∀ (a : ↥X) (x : V ⧸ modFix X W), θ (a • x) = a • θ x := by
    intro a x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hmap : ∀ J : Subgroup V, tilde X W' J = (tilde X W J).map θ := by
    intro J
    unfold tilde
    rw [Subgroup.map_map]
    rfl
  have hinj : ∀ x ∈ tilde X W W, ∀ y ∈ tilde X W W, θ x = θ y → x = y := by
    intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hx
    obtain ⟨u, hu, rfl⟩ := mem_tilde_iff.1 hy
    have h1 : (QuotientGroup.mk v : V ⧸ modFix X W') = QuotientGroup.mk u := hxy
    rw [QuotientGroup.eq] at h1 ⊢
    exact ⟨W.mul_mem (W.inv_mem hv) hu, h1.2⟩
  have hItW : t • I ≤ W := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x t I).1 hx
    exact hWT t ht i (hI.1.1 hi)
  rw [hmap, hmap] at hiso
  exact iso_of_iso_map_injOn θ hθ (isInv_tilde hWX) hinj (tilde_mono hItW)
    (tilde_mono hI.1.1) hiso

end IrrTop

section Nat3

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

private theorem exists_realizesVia_of_eq_top {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 3) {H : Subgroup (MulAut V)}
    (hH : H = ⊤) :
    ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥H, Function.Bijective π ∧
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H ⊤ ⊥ π := by
  subst hH
  obtain ⟨π, hπ⟩ := G64.realizesVia_top_of_card hV2 hcard
  exact ⟨π, SmithD310U.bijective_of_realizesVia hπ, hπ⟩

theorem exists_realizesVia_sl3_two (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ} {Vt : Subgroup Q}
    (hVt : ∀ l : ↥Λ, ∀ v ∈ Vt, l • v ∈ Vt) (hinj : Function.Injective (actAut Λ Vt hVt))
    (hcard : Nat.card ↥Vt = 8) (hΛ : Nat.card ↥Λ = 168) :
    ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥(actAut Λ Vt hVt).range,
      Function.Bijective π ∧
        (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia (actAut Λ Vt hVt).range ⊤ ⊥ π := by
  have : Finite ↥Vt := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hV2 : ∀ v : ↥Vt, v ^ 2 = 1 := fun v => Subtype.ext (hQ v)
  have hcard' : Nat.card ↥Vt = 2 ^ 3 := hcard
  refine exists_realizesVia_of_eq_top hV2 hcard' ?_
  obtain ⟨π₀, hπ₀⟩ := G64.realizesVia_top_of_card hV2 hcard'
  have hAut : Nat.card (MulAut ↥Vt) = 168 := by
    rw [← Subgroup.card_top,
      ← Nat.card_eq_of_bijective π₀ (SmithD310U.bijective_of_realizesVia hπ₀),
      card_statedSL_three_two]
  have : Finite (MulAut ↥Vt) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  apply Subgroup.eq_top_of_card_eq
  rw [hAut, ← hΛ]
  exact (Nat.card_congr (actEquiv hVt hinj).toEquiv).symm

end Nat3

section OneSide

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private theorem smul_isoSum_le_isoSum_smul {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (g : Γ) (V : Subgroup Q) :
    g • isoSum Λ V ≤ isoSum Λ (g • V) := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have h : ∀ T : Subgroup Q, g • T = T.map (MulDistribMulAction.toMonoidHom Q g) := fun T => rfl
  unfold isoSum
  rw [h, Subgroup.map_iSup]
  refine iSup_le fun x => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hx => ?_
  rw [← h]
  refine le_iSup₂_of_le (g * x * g⁻¹) ?_ ?_
  · rw [smul_smul, inv_mul_cancel_right, mul_smul]
    exact XMod.iso_smul hN g hx
  · rw [smul_smul (g * x * g⁻¹), inv_mul_cancel_right, mul_smul]

theorem smul_isoSum {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (g : Γ)
    (V : Subgroup Q) : g • isoSum Λ V = isoSum Λ (g • V) := by
  refine le_antisymm (smul_isoSum_le_isoSum_smul hΛ g V) ?_
  have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := g)).2
    (smul_isoSum_le_isoSum_smul hΛ g⁻¹ (g • V))
  rwa [smul_inv_smul, inv_smul_smul] at h

theorem nB_smul_of_comm [Finite Q] {P : Subgroup Γ} {a : Γ} (ha : ∀ x ∈ P, x * a = a * x)
    (S : Subgroup Q) : nB P (a • S) = nB P S := by
  have hmap : P.map (MulAut.conj a).toMonoidHom = P := by
    ext x
    rw [mem_conjMap]
    constructor
    · intro hx
      have e : a⁻¹ * x * a = x := by
        have h := ha _ hx
        rw [show a * (a⁻¹ * x * a) = x * a by group] at h
        exact mul_right_cancel h
      rwa [e] at hx
    · intro hx
      have e : a⁻¹ * x * a = x := by
        rw [mul_assoc, ha x hx, inv_mul_cancel_left]
      rwa [e]
  have h := nB_smul P a S
  rwa [hmap] at h

private theorem card_le_two_mul [Finite Γ] {P H : Subgroup Γ} {a : Γ}
    (hsplit : ∀ x ∈ P, x ∈ H ∨ a⁻¹ * x ∈ H) : Nat.card ↥P ≤ 2 * Nat.card ↥H := by
  classical
  let f : ↥P → ↥H × Bool := fun x =>
    if hx : (x : Γ) ∈ H then (⟨x, hx⟩, true)
    else (⟨a⁻¹ * x, (hsplit x x.2).resolve_left hx⟩, false)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : Γ) ∈ H <;> by_cases hy : (y : Γ) ∈ H <;> simp [f, hx, hy] at hxy
    · exact hxy
    · exact hxy
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at h

private theorem rk_le_succ [Finite Γ] {P H : Subgroup Γ} {a : Γ} (hP : IsPGroup 2 ↥P)
    (hHP : H ≤ P) (hsplit : ∀ x ∈ P, x ∈ H ∨ a⁻¹ * x ∈ H) : rk ↥P ≤ rk ↥H + 1 := by
  have h := card_le_two_mul hsplit
  rw [card_eq_two_pow_of_isPGroup hP, card_eq_two_pow_of_isPGroup (hP.to_le hHP),
    ← pow_succ'] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

private theorem isPGroup_of_mul_self {P : Subgroup Γ} (hP2 : ∀ a ∈ P, a * a = 1) :
    IsPGroup 2 ↥P :=
  isPGroup_two_of_sq_eq_one fun y => Subtype.ext (by rw [sq]; exact hP2 y y.2)

theorem one_side_matrix_count [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {Vt : Subgroup Q} (hV : XMod.IsIrr ↥Λ Vt)
    (hinj : Function.Injective (actAut Λ Vt hV.1))
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(actAut Λ Vt hV.1).range}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia (actAut Λ Vt hV.1).range ⊤ ⊥ π)
    (hrk : rk ↥Vt = 3) {s : Γ} (hs : ¬ XMod.Iso ↥Λ Vt (s • Vt)) {P : Subgroup Γ}
    (hP2 : ∀ a ∈ P, a * a = 1) (hPV : ∀ a ∈ P, a • Vt = Vt)
    (hPsV : ∀ a ∈ P, a • (s • Vt) = s • Vt) (hnc : ¬ P ≤ Subgroup.centralizer (Λ : Set Γ)) :
    1 + (rk ↥P - rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ))) ≤ nB P Vt + nB P (s • Vt) ∧
      rk ↥P - rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) ≤ 2 := by
  have hPg : ∀ a ∈ P, (s⁻¹ * a * s) • Vt = Vt := by
    intro a ha
    rw [mul_smul, mul_smul, hPsV a ha, inv_smul_smul]
  obtain ⟨S, hS2, hSc, hcard, hfix1, hfix2, hne⟩ := exists_matrices_abs hΛ hV.1 hinj
    (K := ZMod 2) (m := 1) (by rw [Nat.card_zmod]; norm_num) odd_one hπ hs hPV hPg hP2
  obtain ⟨x, hxS, hx1⟩ := hne hnc
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hmul := card_mul_le h2 hS2 hSc hxS hx1
  have hsq := card_le_sq h2 hS2 hSc
  have hPp := isPGroup_of_mul_self hP2
  rw [Nat.card_zmod, ← hfix1, ← hfix2, card_eq_two_pow hQ (Vt ⊓ XMod.fixed ↥P ⊤),
    card_eq_two_pow hQ (s • Vt ⊓ XMod.fixed ↥P ⊤)] at hmul
  rw [Nat.card_zmod] at hsq
  rw [card_eq_two_pow_of_isPGroup hPp, card_eq_two_pow_of_isPGroup (hPp.to_le inf_le_left)]
    at hcard
  have hle : rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) ≤ rk ↥P := rk_mono inf_le_left
  have hc1 : rk ↥(Vt ⊓ XMod.fixed ↥P ⊤) ≤ rk ↥Vt := rk_mono inf_le_left
  have hc2 : rk ↥(s • Vt ⊓ XMod.fixed ↥P ⊤) ≤ rk ↥(s • Vt) := rk_mono inf_le_left
  set C := Subgroup.centralizer (Λ : Set Γ)
  set e := rk ↥P - rk ↥(P ⊓ C) with he
  set c₁ := rk ↥(Vt ⊓ XMod.fixed ↥P ⊤)
  set c₂ := rk ↥(s • Vt ⊓ XMod.fixed ↥P ⊤)
  have hS : 2 ^ e ≤ Nat.card S := by
    have h3 : 2 ^ rk ↥P = 2 ^ rk ↥(P ⊓ C) * 2 ^ e := by
      rw [← pow_add, he, Nat.add_sub_cancel' hle]
    rw [h3] at hcard
    exact Nat.le_of_mul_le_mul_left hcard (by positivity)
  have he2 : e ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hS.trans hsq)
  have hexp : 2 ^ (1 + e + c₁ + c₂) ≤ 2 ^ 6 := by
    calc 2 ^ (1 + e + c₁ + c₂) = 2 * 2 ^ e * 2 ^ c₁ * 2 ^ c₂ := by ring
      _ ≤ 2 * Nat.card S * 2 ^ c₁ * 2 ^ c₂ := by gcongr
      _ ≤ 2 ^ 6 := hmul
  have h6 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hexp
  rw [rk_smul, hrk] at hc2
  refine ⟨?_, he2⟩
  unfold nB
  rw [rk_smul, hrk]
  omega

theorem one_side_count [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {Vt : Subgroup Q} (hV : XMod.IsIrr ↥Λ Vt)
    (hinj : Function.Injective (actAut Λ Vt hV.1))
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥(actAut Λ Vt hV.1).range}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia (actAut Λ Vt hV.1).range ⊤ ⊥ π)
    (hrk : rk ↥Vt = 3) {s : Γ} (hs : ¬ XMod.Iso ↥Λ Vt (s • Vt)) {k : ℕ}
    (hk : rk ↥(isoSum Λ Vt) = k * rk ↥Vt) (hk2 : 2 ≤ k)
    {P : Subgroup Γ} (hP2 : ∀ a ∈ P, a * a = 1)
    (hPV : ∀ a ∈ P, a • Vt = Vt ∨ a • Vt = s • Vt)
    (hPsV : ∀ a ∈ P, a • (s • Vt) = s • Vt ∨ a • (s • Vt) = Vt)
    (hnc : ¬ P ≤ Subgroup.centralizer (Λ : Set Γ)) :
    2 * (rk ↥P - rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ))) + 2 ≤
      nB P (isoSum Λ Vt ⊔ isoSum Λ (s • Vt)) := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have hsV : s • Vt ≠ Vt := fun h => hs (by rw [h]; exact XMod.Iso.refl Vt)
  have hs' : ¬ XMod.Iso ↥Λ (s • Vt) Vt := fun h =>
    hs (XMod.Iso.symm (XMod.isInv_smul_of_normalizes hN s hV.1) h)
  have hPp := isPGroup_of_mul_self hP2
  have hPinv : ∀ a ∈ P, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hP2 a ha)
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h := hPinv (x * y) (P.mul_mem hx hy)
    rw [mul_inv_rev, hPinv x hx, hPinv y hy] at h
    exact h.symm
  have hrks : rk ↥(s • Vt) = 3 := by rw [rk_smul, hrk]
  have hQs : isoSum Λ (s • Vt) = s • isoSum Λ Vt := (smul_isoSum hΛ s Vt).symm
  have hdisj : isoSum Λ Vt ⊓ s • isoSum Λ Vt = ⊥ := inf_isoSum_smul hΛ hV hs'
  have hrkQ : rk ↥(isoSum Λ Vt) = k * 3 := by rw [hk, hrk]
  have hinvQ : ∀ (b : Γ) (V : Subgroup Q), XMod.IsInv ↥Λ V → b • V = V →
      ∀ q ∈ isoSum Λ V, b • q ∈ isoSum Λ V := by
    intro b V hVi hb q hq
    have h1 : b • isoSum Λ V = isoSum Λ V := by rw [smul_isoSum hΛ b V, hb]
    rw [← h1]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  by_cases hcase : ∀ a ∈ P, a • Vt = Vt
  ·
    have hPsV' : ∀ a ∈ P, a • (s • Vt) = s • Vt := by
      intro a ha
      rcases hPsV a ha with h | h
      · exact h
      · exfalso
        apply hsV
        have h2 : a • (s • Vt) = a • Vt := by rw [h, hcase a ha]
        exact (smul_left_cancel_iff a).1 h2
    obtain ⟨hcnt, -⟩ := one_side_matrix_count hQ hΛ hV hinj hπ hrk hs hP2 hcase hPsV' hnc
    obtain ⟨k₁, hk₁, hk₁'⟩ := count_isoSum hQ hΛ hV hPp hcase
    obtain ⟨k₂, hk₂, hk₂'⟩ := count_isoSum hQ hΛ (isIrr_smul hN s hV) hPp hPsV'
    have e₁ : k₁ = k := by rw [hrkQ, hrk] at hk₁; omega
    have e₂ : k₂ = k := by rw [hQs, rk_smul, hrkQ, hrks] at hk₂; omega
    rw [e₁] at hk₁'
    rw [e₂] at hk₂'
    have hd : isoSum Λ Vt ⊓ isoSum Λ (s • Vt) = ⊥ := by rw [hQs]; exact hdisj
    rw [nB_sup_of_inf_eq_bot P (fun b hb => hinvQ b Vt hV.1 (hcase b hb))
      (fun b hb => hinvQ b (s • Vt) (XMod.isInv_smul_of_normalizes hN s hV.1) (hPsV' b hb)) hd]
    have h3 := Nat.mul_le_mul_right (nB P Vt) hk2
    have h4 := Nat.mul_le_mul_right (nB P (s • Vt)) hk2
    omega
  ·
    push Not at hcase
    obtain ⟨a₁, ha₁P, ha₁V⟩ := hcase
    have ha₁ : a₁ • Vt = s • Vt := (hPV a₁ ha₁P).resolve_left ha₁V
    set P₁ := P ⊓ MulAction.stabilizer Γ Vt
    have hP₁P : P₁ ≤ P := inf_le_left
    have hP₁V : ∀ b ∈ P₁, b • Vt = Vt := fun b hb => hb.2
    have hP₁sV : ∀ b ∈ P₁, b • (s • Vt) = s • Vt := by
      intro b hb
      rcases hPsV b hb.1 with h | h
      · exact h
      · exfalso
        apply hsV
        have h2 : b • (s • Vt) = b • Vt := by rw [h, hP₁V b hb]
        exact (smul_left_cancel_iff b).1 h2
    have hsplit : ∀ x ∈ P, x ∈ P₁ ∨ a₁⁻¹ * x ∈ P₁ := by
      intro x hx
      rcases hPV x hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · right
        refine ⟨P.mul_mem (P.inv_mem ha₁P) hx, ?_⟩
        show (a₁⁻¹ * x) • Vt = Vt
        rw [mul_smul, h, ← ha₁, inv_smul_smul]
    have ha₁2 : a₁ ^ 2 = 1 := by rw [sq]; exact hP2 a₁ ha₁P
    have hQa : a₁ • isoSum Λ Vt = isoSum Λ (s • Vt) := by rw [smul_isoSum hΛ a₁ Vt, ha₁]
    have hP₁Q : XMod.IsInv ↥P₁ (isoSum Λ Vt) := fun b q hq =>
      hinvQ b Vt hV.1 (hP₁V b b.2) q hq
    have hdisj₁ : isoSum Λ Vt ⊓ a₁ • isoSum Λ Vt = ⊥ := by rw [hQa, hQs]; exact hdisj
    have hidx := nB_index_two ha₁P ha₁2 hPc hP₁P hsplit hP₁Q hdisj₁
    rw [hQa] at hidx
    rw [hidx, hrkQ]
    have hrkP := rk_le_succ hPp hP₁P hsplit
    have hC₁ : rk ↥(P₁ ⊓ Subgroup.centralizer (Λ : Set Γ)) ≤
        rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) := rk_mono (inf_le_inf_right _ hP₁P)
    have hC₂ : rk ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) ≤ rk ↥P := rk_mono inf_le_left
    have hC₃ : rk ↥(P₁ ⊓ Subgroup.centralizer (Λ : Set Γ)) ≤ rk ↥P₁ := rk_mono inf_le_left
    by_cases hP₁C : P₁ ≤ Subgroup.centralizer (Λ : Set Γ)
    · have h1 : rk ↥(P₁ ⊓ Subgroup.centralizer (Λ : Set Γ)) = rk ↥P₁ := by
        rw [inf_eq_left.2 hP₁C]
      omega
    · obtain ⟨hcnt, he₂⟩ := one_side_matrix_count hQ hΛ hV hinj hπ hrk hs
        (fun b (hb : b ∈ P₁) => hP2 b hb.1) hP₁V hP₁sV hP₁C
      have hn : nB P₁ (s • Vt) = nB P₁ Vt := by
        rw [← ha₁]
        exact nB_smul_of_comm (fun x (hx : x ∈ P₁) => hPc x hx.1 a₁ ha₁P) Vt
      obtain ⟨k₁, hk₁, hk₁'⟩ := count_isoSum hQ hΛ hV (hPp.to_le hP₁P) hP₁V
      have e₁ : k₁ = k := by rw [hrkQ, hrk] at hk₁; omega
      rw [e₁] at hk₁'
      have h3 := Nat.mul_le_mul_right (nB P₁ Vt) hk2
      omega

end OneSide

section Compat

variable {Λ' Λ : Type*} [Group Λ'] [Group Λ] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction Λ' Q] [MulDistribMulAction Λ Q]

private theorem fixed_eq_of_surj (φ : Λ' → Λ) (hφ : Function.Surjective φ)
    (hact : ∀ (l : Λ') (q : Q), l • q = φ l • q) (S : Subgroup Q) :
    XMod.fixed Λ' S = XMod.fixed Λ S := by
  ext q
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun a => ?_⟩
    obtain ⟨a', rfl⟩ := hφ a
    rw [← hact]
    exact h a'
  · rintro ⟨hq, h⟩
    exact ⟨hq, fun a => by rw [hact]; exact h (φ a)⟩

end Compat

section SecML

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

local notation "ML" => M ⊓ Subgroup.normalizer (L : Set (MulAut W))

theorem ml_le_normalizer (hB : D321Base M Mp T L V t) :
    ML ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
  inf_le_left.trans hB.hD.hyp.Mp_normal

omit [Finite W] in
theorem ml_normal : ∀ g : ↥(ML), ∀ l ∈ L.subgroupOf (ML), g * l * g⁻¹ ∈ L.subgroupOf (ML) :=
  fun g _ hl => (Subgroup.mem_normalizer_iff.1 g.2.2 _).1 hl

theorem L_le_ml (hB : D321Base M Mp T L V t) : L ≤ ML :=
  le_inf hB.L_le Subgroup.le_normalizer

private theorem ml_act (hB : D321Base M Mp T L V t) :
    letI := qAct hB.hD.hyp.Mp_normal
    letI := qAct (ml_le_normalizer hB)
    ∃ φ : ↥(L.subgroupOf (ML)) → ↥(L.subgroupOf M), Function.Surjective φ ∧
      ∀ (l : ↥(L.subgroupOf (ML))) (q : W ⧸ modFix Mp (⊤ : Subgroup W)), l • q = φ l • q := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  refine ⟨fun l => ⟨⟨((l : ↥(ML)) : MulAut W), ((l : ↥(ML)).2.1)⟩, l.2⟩,
    fun l => ⟨⟨⟨((l : ↥M) : MulAut W), L_le_ml hB l.2⟩, l.2⟩, rfl⟩, fun l q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H w => rfl

theorem isIrr_ml (hB : D321Base M Mp T L V t) (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v) :
    letI := qAct (ml_le_normalizer hB)
    XMod.IsIrr ↥(L.subgroupOf (ML)) (tilde Mp ⊤ V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  obtain ⟨φ, hφ, hact⟩ := ml_act hB
  exact Z391.isIrr_of_surj φ hφ hact (hB.irr_L hVt)

private theorem simple_ml (hB : D321Base M Mp T L V t) : IsSimpleGroup ↥(L.subgroupOf (ML)) :=
  have := hB.hsimp
  MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe (L_le_ml hB))

private theorem card_L_ml (hB : D321Base M Mp T L V t) :
    Nat.card ↥(L.subgroupOf (ML)) = Nat.card ↥L :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (L_le_ml hB)).toEquiv

theorem injective_ml (hB : D321Base M Mp T L V t) (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v) :
    letI := qAct (ml_le_normalizer hB)
    Function.Injective (actAut (L.subgroupOf (ML)) (tilde Mp ⊤ V) (isIrr_ml hB hVt).1) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  have hs := simple_ml hB
  set f := actAut (L.subgroupOf (ML)) (tilde Mp ⊤ V) (isIrr_ml hB hVt).1 with hf
  rw [← MonoidHom.ker_eq_bot_iff]
  have := f.normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact h
  · exfalso
    have htriv : ∀ l (hl : l ∈ L), ∀ q ∈ tilde Mp ⊤ V, (⟨l, hB.L_le hl⟩ : ↥M) • q = q := by
      intro l hl q hq
      have hmem : (⟨⟨l, L_le_ml hB hl⟩, hl⟩ : ↥(L.subgroupOf (ML))) ∈ f.ker := by
        rw [h]; trivial
      have h1 := congrArg (fun φ : MulAut ↥(tilde Mp ⊤ V) => ((φ ⟨q, hq⟩ : ↥(tilde Mp ⊤ V)) :
        W ⧸ modFix Mp (⊤ : Subgroup W))) (MonoidHom.mem_ker.1 hmem)
      change ((⟨l, L_le_ml hB hl⟩ : ↥(ML)) • q) = q at h1
      induction q using QuotientGroup.induction_on with
      | H w => exact h1
    have hfix : tilde Mp ⊤ V ≤
        XMod.fixed ↥(Mp.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
      intro q hq
      refine ⟨trivial, fun a => ?_⟩
      obtain ⟨l, hl, l', hl', hll'⟩ := hB.exists_mul_of_mem_Mp (Subgroup.mem_subgroupOf.1 a.2)
      have e : ((a : ↥(Mp.subgroupOf M)) : ↥M) = ⟨l, hB.L_le hl⟩ * ⟨l', hB.Lt_le hl'⟩ :=
        Subtype.ext hll'
      have hl'q : (⟨l', hB.Lt_le hl'⟩ : ↥M) • q = q := by
        obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq
        change (QuotientGroup.mk (l' v) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk v
        rw [hVt v hv l' hl']
      show ((a : ↥(Mp.subgroupOf M)) : ↥M) • q = q
      rw [e, mul_smul, hl'q, htriv l hl q hq]
    rw [hB.fixed_eq_bot] at hfix
    exact hB.tilde_ne_bot (le_bot_iff.1 hfix)

private theorem card_tilde_eq (hcard : Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)) :
    Nat.card ↥(tilde Mp ⊤ V) = 8 := by
  set f := (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap V with hf
  have hs : Function.Surjective f :=
    (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap_surjective V
  have hker : f.ker = (fixV Mp).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk (x : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h1
      rwa [QuotientGroup.eq_one_iff, SmithD391.modFix_top_eq] at h2
    · intro h1
      apply Subtype.ext
      show (QuotientGroup.mk (x : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
      rwa [QuotientGroup.eq_one_iff, SmithD391.modFix_top_eq]
  have h1 := Subgroup.card_ker_mul_card_of_surjective hs
  rw [hker, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : fixV Mp ⊓ V ≤ V)).toEquiv,
    inf_comm, hcard] at h1
  have hpos : 0 < Nat.card ↥(V ⊓ fixV Mp) := Nat.card_pos
  have h2 : Nat.card ↥(V ⊓ fixV Mp) * Nat.card ↥(V.map (QuotientGroup.mk'
      (modFix Mp (⊤ : Subgroup W)))) = Nat.card ↥(V ⊓ fixV Mp) * 8 := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos h2

private theorem card_L_eq (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v)
    (hpsl : IsPSL 3 2 1 ↥(autSub L (orbSup T V))) : Nat.card ↥L = 168 := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  have hLV : L ≤ stabSub (orbSup T V) :=
    hB.L_le_Mp.trans ((le_sup_left : Mp ≤ Mp ⊔ T).trans
      ((n1_sup_le_stabSub_sec hB.hD.hyp).trans inf_le_left))
  have hfaith : L ⊓ centSub (orbSup T V) = ⊥ := by
    rw [eq_bot_iff]
    rintro l ⟨hl, hlc⟩
    have hinj := injective_ml hB hVt
    have h1 : actAut (L.subgroupOf (ML)) (tilde Mp ⊤ V) (isIrr_ml hB hVt).1
        ⟨⟨l, L_le_ml hB hl⟩, hl⟩ = 1 := by
      refine MulEquiv.ext fun q => Subtype.ext ?_
      obtain ⟨v, hv, hvq⟩ := mem_tilde_iff.1 q.2
      change ((⟨l, L_le_ml hB hl⟩ : ↥(ML)) • (q : W ⧸ modFix Mp (⊤ : Subgroup W))) =
        (q : W ⧸ modFix Mp (⊤ : Subgroup W))
      rw [← hvq]
      change (QuotientGroup.mk (l v) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk v
      rw [hlc v (le_orbSup T V hv)]
    have h2 := hinj (h1.trans (map_one _).symm)
    exact Subgroup.mem_bot.2 (congrArg (fun x : ↥(L.subgroupOf (ML)) =>
      ((x : ↥(ML)) : MulAut W)) h2)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hpsl
  rw [Nat.card_congr ((autSubEquivOfFaithful hLV hfaith).trans e).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

end SecML

section SecT

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

local notation "ML" => M ⊓ Subgroup.normalizer (L : Set (MulAut W))

omit [Finite W] in
private theorem smul_ne_bot {G : Type*} [Group G] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction G Q]
    (g : G) {H : Subgroup Q} (hH : H ≠ ⊥) : g • H ≠ ⊥ := by
  intro h
  apply hH
  rw [eq_bot_iff]
  intro x hx
  have h1 : g • x ∈ g • H := Subgroup.smul_mem_pointwise_smul x g H hx
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  have h2 := congrArg (g⁻¹ • ·) h1
  simpa using h2

private theorem T_le_normalizer_Mp (hD : D3Std M Mp T L V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hD.hyp.Mp_eq]
  exact le_normalizer_conjClosure L T

theorem mem_irrPlusOn_top (hD : D3Std M Mp T L V) : V ∈ IrrPlusOn Mp (⊤ : Subgroup W) T := by
  have hst : Mp ≤ stabSub (orbSup T V) :=
    (le_sup_left : Mp ≤ Mp ⊔ T).trans ((n1_sup_le_stabSub_sec hD.hyp).trans inf_le_left)
  exact mem_irrPlusOn_of_le (T_le_normalizer_Mp hD)
    (fun _ ht _ hw => mem_orbSup_of_mem_map ht hw) (fun a w hw => (hst a.2 w).2 hw)
    (fun _ _ _ _ => Subgroup.mem_top _) le_top hD.irrT

theorem iso_mp_of_iso_ml (hB : D321Base M Mp T L V t) {I₁ I₂ : Subgroup W}
    (h₁ : ∀ v ∈ I₁, ∀ y ∈ conjAutSub t L, y v = v) (h₂ : ∀ v ∈ I₂, ∀ y ∈ conjAutSub t L, y v = v)
    (h : letI := qAct (ml_le_normalizer hB)
      XMod.Iso ↥(L.subgroupOf (ML)) (tilde Mp ⊤ I₁) (tilde Mp ⊤ I₂)) :
    XMod.Iso ↥Mp (tilde Mp ⊤ I₁) (tilde Mp ⊤ I₂) := by
  let _j := qAct (ml_le_normalizer hB)
  obtain ⟨φ, hφ⟩ := h
  have key : ∀ (I : Subgroup W), (∀ v ∈ I, ∀ y ∈ conjAutSub t L, y v = v) →
      ∀ (a : ↥Mp) {b c : MulAut W} (hb : b ∈ L), c ∈ conjAutSub t L → (a : MulAut W) = b * c →
      ∀ q ∈ tilde Mp ⊤ I, a • q =
        (⟨⟨b, L_le_ml hB hb⟩, hb⟩ : ↥(L.subgroupOf (ML))) • q := by
    intro I hI a b c hb hc habc q hq
    obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq
    change (QuotientGroup.mk ((a : MulAut W) v) : W ⧸ modFix Mp (⊤ : Subgroup W)) =
      QuotientGroup.mk (b v)
    rw [habc, MulAut.mul_apply, hI v hv c hc]
  refine ⟨φ, fun a l l' hll' => ?_⟩
  obtain ⟨b, hb, c, hc, habc⟩ := hB.exists_mul_of_mem_Mp a.2
  rw [key I₁ h₁ a hb hc habc _ l.2] at hll'
  rw [key I₂ h₂ a hb hc habc _ (φ l).2]
  exact hφ _ l l' hll'

theorem not_iso_ml (hB : D321Base M Mp T L V t) (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v)
    {s : MulAut W} (hsT : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hdisj : tilde Mp ⊤ V ⊓ tilde Mp ⊤ (s • V) = ⊥) :
    letI := qAct (ml_le_normalizer hB)
    ¬ XMod.Iso ↥(L.subgroupOf (ML)) (tilde Mp ⊤ V)
      ((⟨s, hB.T_le hsT, hsN⟩ : ↥(ML)) • tilde Mp ⊤ V) := by
  let _j := qAct (ml_le_normalizer hB)
  intro hiso
  rw [smul_tildeQ (ml_le_normalizer hB)] at hiso
  have hsVt : ∀ v ∈ s • V, ∀ y ∈ conjAutSub t L, y v = v := by
    have h1 := fix_map hVt s
    rw [hB.conj_Lt_of_mem_normalizer (hB.T_le hsT) hsN] at h1
    exact h1
  have hmp := iso_mp_of_iso_ml hB hVt hsVt hiso
  have heq := tilde_smul_eq_of_iso_of_mem_irrPlusOn (T_le_normalizer_Mp hB.hD)
    (fun _ _ _ _ => Subgroup.mem_top _) (mem_irrPlusOn_top hB.hD) T.one_mem hsT
    (by rwa [one_smul])
  rw [one_smul] at heq
  rw [← heq, inf_idem] at hdisj
  exact hB.tilde_ne_bot hdisj

theorem tilde_eq_or_eq (hB : D321Base M Mp T L V t) {s x : MulAut W} (hsT : s ∈ T)
    (hxT : x ∈ T) (hle : tilde Mp ⊤ (x • V) ≤ tilde Mp ⊤ V ⊔ tilde Mp ⊤ (s • V)) :
    tilde Mp ⊤ (x • V) = tilde Mp ⊤ V ∨ tilde Mp ⊤ (x • V) = tilde Mp ⊤ (s • V) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hind := (sSupIndep_tilde_smul_of_mem_irrPlusOn (T_le_normalizer_Mp hB.hD)
    (fun _ _ _ _ => Subgroup.mem_top _) (mem_irrPlusOn_top hB.hD)).1
  set S := {c : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)) |
    ∃ r ∈ T, c = tilde Mp ⊤ (r • V)} with hSdef
  have hx : tilde Mp ⊤ (x • V) ∈ S := ⟨x, hxT, rfl⟩
  have h1 : tilde Mp ⊤ V ∈ S \ {tilde Mp ⊤ (x • V)} :=
    ⟨⟨1, T.one_mem, by rw [one_smul]⟩, fun h => hne1 h.symm⟩
  have h2 : tilde Mp ⊤ (s • V) ∈ S \ {tilde Mp ⊤ (x • V)} :=
    ⟨⟨s, hsT, rfl⟩, fun h => hne2 h.symm⟩
  have hsup : tilde Mp ⊤ V ⊔ tilde Mp ⊤ (s • V) ≤ sSup (S \ {tilde Mp ⊤ (x • V)}) :=
    sup_le (le_sSup h1) (le_sSup h2)
  have hdis := (hind hx).mono_right hsup
  have hbot : tilde Mp ⊤ (x • V) = ⊥ := by
    rw [← inf_eq_left.2 hle]
    exact hdis.eq_bot
  apply smul_ne_bot (⟨x, hB.T_le hxT⟩ : ↥M) hB.tilde_ne_bot
  rw [smul_tildeQ hB.hD.hyp.Mp_normal]
  exact hbot

end SecT

section SecIIb

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

local notation "ML" => M ⊓ Subgroup.normalizer (L : Set (MulAut W))

omit [Finite W] in
private theorem tilde_inf_tilde_eq_bot {U : Subgroup W} {s : MulAut W}
    (hsum : IsSumMod (U ⊓ fixV Mp) V (V.map s.toMonoidHom) U) :
    tilde Mp ⊤ V ⊓ tilde Mp ⊤ (s • V) = ⊥ := by
  obtain ⟨hU, hdis⟩ := hsum
  have hVU : V ≤ U := by rw [hU]; exact le_sup_left.trans le_sup_left
  have hsVU : V.map s.toMonoidHom ≤ U := by rw [hU]; exact le_sup_right.trans le_sup_left
  rw [eq_bot_iff]
  rintro q ⟨hq1, hq2⟩
  obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq1
  obtain ⟨v', hv', hvq⟩ := mem_tilde_iff.1 hq2
  have hz : v'⁻¹ * v ∈ fixV Mp := by
    rw [QuotientGroup.eq, SmithD391.modFix_top_eq] at hvq
    exact hvq
  have hv'U : v' ∈ U := hsVU hv'
  have hzC : v'⁻¹ * v ∈ U ⊓ fixV Mp := ⟨U.mul_mem (U.inv_mem hv'U) (hVU hv), hz⟩
  have hmem : v ∈ (V ⊔ U ⊓ fixV Mp) ⊓ (V.map s.toMonoidHom ⊔ U ⊓ fixV Mp) := by
    refine ⟨Subgroup.mem_sup_left hv, ?_⟩
    have e : v = v' * (v'⁻¹ * v) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hv' hzC
  have h1 := (hdis hmem).2
  rw [Subgroup.mem_bot]
  show (QuotientGroup.mk v : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
  rw [QuotientGroup.eq_one_iff, SmithD391.modFix_top_eq]
  exact h1

private theorem tilde_smul_eq_or_eq (hB : D321Base M Mp T L V t) {s : MulAut W} (hsT : s ∈ T)
    (hU : commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom) {x : MulAut W} (hxT : x ∈ T)
    (hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    tilde Mp ⊤ (x • V) = tilde Mp ⊤ V ∨ tilde Mp ⊤ (x • V) = tilde Mp ⊤ (s • V) := by
  refine tilde_eq_or_eq hB hsT hxT ?_
  have hVU : V ≤ commSub (orbSup T V) L := by rw [hU]; exact le_sup_left
  have hxU : (commSub (orbSup T V) L).map x.toMonoidHom = commSub (orbSup T V) L := by
    rw [← Z391.commSub_map_conj, mem_stabSub_iff_map_eq.1 (le_stabSub_orbSup T V hxT)]
    congr 1
    exact mem_normalizer_iff_conjAutSub.1 hxN
  have h1 : x • V ≤ V ⊔ V.map s.toMonoidHom := by
    rw [← hU, ← hxU]
    exact Subgroup.map_mono hVU
  have h2 := tilde_mono (X := Mp) (W := (⊤ : Subgroup W)) h1
  unfold tilde at h2 ⊢
  rw [Subgroup.map_sup] at h2
  exact h2

private theorem rk_add_rk_le {A X Y : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hX : X ≤ A)
    (hY : Y ≤ A) (hXY : X ⊓ Y = ⊥) : rk ↥X + rk ↥Y ≤ rk ↥A := by
  have h := B2F.rk_sup_add_rk_inf_of_commute (A := X) (B := Y)
    (fun a ha b hb => hA.1 a (hX ha) b (hY hb))
  rw [hXY, rk_bot] at h
  have h2 := rk_mono (sup_le hX hY)
  omega

private theorem exists_nat_ml (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v)
    (hpsl : IsPSL 3 2 1 ↥(autSub L (orbSup T V)))
    (hcard : Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)) :
    letI := qAct (ml_le_normalizer hB)
    ∃ π : ↥(StatedSL 3 (ZMod 2)) →*
        ↥(actAut (L.subgroupOf (ML)) (tilde Mp ⊤ V) (isIrr_ml hB hVt).1).range,
      Function.Bijective π ∧ (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia
        (actAut (L.subgroupOf (ML)) (tilde Mp ⊤ V) (isIrr_ml hB hVt).1).range ⊤ ⊥ π := by
  let _j := qAct (ml_le_normalizer hB)
  exact exists_realizesVia_sl3_two hB.quot_sq (isIrr_ml hB hVt).1 (injective_ml hB hVt)
    (card_tilde_eq hcard) ((card_L_ml hB).trans (card_L_eq hB hVt hpsl))

private theorem iso_or_iso_ml (hB : D321Base M Mp T L V t)
    (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v)
    (hpsl : IsPSL 3 2 1 ↥(autSub L (orbSup T V)))
    (hcard : Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)) {s : MulAut W} (hsT : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hdisj : tilde Mp ⊤ V ⊓ tilde Mp ⊤ (s • V) = ⊥) :
    letI := qAct (ml_le_normalizer hB)
    ∀ g : ↥(ML), XMod.Iso ↥(L.subgroupOf (ML)) (tilde Mp ⊤ V) (g • tilde Mp ⊤ V) ∨
      XMod.Iso ↥(L.subgroupOf (ML)) ((⟨s, hB.T_le hsT, hsN⟩ : ↥(ML)) • tilde Mp ⊤ V)
        (g • tilde Mp ⊤ V) := by
  let _j := qAct (ml_le_normalizer hB)
  obtain ⟨π, hπb, -⟩ := exists_nat_ml hB hVt hpsl hcard
  have htc := SLTwist.twoClassMod_of_equiv_statedSL_two (n := 3) (K := ZMod 2) (by norm_num)
    (Nat.card_zmod 2) (MulEquiv.ofBijective π hπb).symm
  exact iso_or_iso_of_twoClass ml_normal (isIrr_ml hB hVt).1 (injective_ml hB hVt) htc
    (not_iso_ml hB hVt hsT hsN hdisj)

private theorem two_le_mult (hB : D321Base M Mp T L V t) (htop : orbSup T V ≠ ⊤)
    (hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v) {s : MulAut W} (hsT : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hdich : letI := qAct (ml_le_normalizer hB)
      ∀ g : ↥(ML), XMod.Iso ↥(L.subgroupOf (ML)) (tilde Mp ⊤ V) (g • tilde Mp ⊤ V) ∨
        XMod.Iso ↥(L.subgroupOf (ML)) ((⟨s, hB.T_le hsT, hsN⟩ : ↥(ML)) • tilde Mp ⊤ V)
          (g • tilde Mp ⊤ V)) :
    letI := qAct (ml_le_normalizer hB)
    ∃ k, rk ↥(isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V)) = k * rk ↥(tilde Mp ⊤ V) ∧ 2 ≤ k := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  set sM : ↥(ML) := ⟨s, hB.T_le hsT, hsN⟩ with hsM
  have hirr := isIrr_ml hB hVt
  obtain ⟨k, hk, -⟩ := count_isoSum hB.quot_sq ml_normal hirr (A := (⊥ : Subgroup ↥(ML)))
    IsPGroup.of_bot (fun a ha => by rw [Subgroup.mem_bot.1 ha, one_smul])
  refine ⟨k, hk, ?_⟩
  by_contra hk2
  have hpos : 0 < rk ↥(tilde Mp ⊤ V) := by
    rcases Nat.eq_zero_or_pos (rk ↥(tilde Mp ⊤ V)) with h | h
    · exact absurd ((rk_eq_zero_iff hB.quot_sq).1 h) hB.tilde_ne_bot
    · exact h
  have hiso_eq : isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) = tilde Mp ⊤ V := by
    symm
    refine Subgroup.eq_of_le_of_card_ge self_le_isoSum ?_
    rw [card_eq_two_pow hB.quot_sq, card_eq_two_pow hB.quot_sq, hk]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hN := normalizes_whole (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (L.subgroupOf (ML)) ml_normal
  have hle_ml : ∀ g : ↥(ML), g • tilde Mp ⊤ V ≤ tilde Mp ⊤ V ⊔ sM • tilde Mp ⊤ V := by
    intro g
    rcases hdich g with h | h
    · exact le_sup_of_le_left ((le_isoSum (XMod.Iso.symm hirr.1 h)).trans hiso_eq.le)
    · refine le_sup_of_le_right ?_
      have hinv : XMod.IsInv ↥(L.subgroupOf (ML)) (sM • tilde Mp ⊤ V) :=
        XMod.isInv_smul_of_normalizes hN sM hirr.1
      have h1 : XMod.Iso ↥(L.subgroupOf (ML)) ((g * sM⁻¹) • (sM • tilde Mp ⊤ V))
          (sM • tilde Mp ⊤ V) := by
        rw [mul_smul, inv_smul_smul]
        exact XMod.Iso.symm hinv h
      have h2 := le_isoSum h1
      rw [mul_smul, inv_smul_smul] at h2
      refine h2.trans (le_of_eq ?_)
      rw [← smul_isoSum ml_normal sM, hiso_eq]
  have hW : ∀ g ∈ ML, tilde Mp ⊤ (g • V) ≤ tilde Mp ⊤ V ⊔ tilde Mp ⊤ (s • V) := by
    intro g hg
    have h1 := hle_ml ⟨g, hg⟩
    rw [smul_tildeQ (ml_le_normalizer hB), hsM, smul_tildeQ (ml_le_normalizer hB)] at h1
    exact h1
  have hsub : tilde Mp ⊤ V ⊔ tilde Mp ⊤ (s • V) ≤ tilde Mp ⊤ (orbSup T V) :=
    sup_le (tilde_mono (le_orbSup T V)) (tilde_mono (map_le_orbSup hsT))
  have hle_m : ∀ g ∈ M, tilde Mp ⊤ (g • V) ≤ tilde Mp ⊤ (orbSup T V) := by
    intro g hg
    by_cases hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))
    · exact (hW g ⟨hg, hgL⟩).trans hsub
    · have hg' : t⁻¹ * g ∈ ML :=
        ⟨M.mul_mem (M.inv_mem hB.t_mem) hg, hB.inv_mul_mem_normalizer hB.t_mem hg hB.htn hgL⟩
      have h1 := hW (t⁻¹ * g) hg'
      have e : tilde Mp ⊤ (g • V) =
          (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ ((t⁻¹ * g) • V) := by
        rw [smul_tildeQ hB.hD.hyp.Mp_normal, smul_smul]
        congr 2
        group
      rw [e]
      have h2 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := (⟨t, hB.t_mem⟩ : ↥M))).2 h1
      refine h2.trans ?_
      rw [Subgroup.smul_sup, smul_tildeQ hB.hD.hyp.Mp_normal, smul_tildeQ hB.hD.hyp.Mp_normal,
        smul_smul]
      exact sup_le (tilde_mono (map_le_orbSup hB.htT))
        (tilde_mono (map_le_orbSup (T.mul_mem hB.htT hsT)))
  have htopQ : (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤ tilde Mp ⊤ (orbSup T V) := by
    rw [← hB.gen]
    refine iSup_le fun g => ?_
    rw [smul_tildeQ hB.hD.hyp.Mp_normal]
    exact hle_m g g.2
  apply hB.not_le_orbSup htop
  intro w _
  have h1 : w ∈ (tilde Mp ⊤ (orbSup T V)).comap
      (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) :=
    htopQ (Subgroup.mem_top (QuotientGroup.mk w))
  rwa [comap_tilde, SmithD391.modFix_top_eq] at h1

omit [Finite W] in
private theorem rk_conjAutSub (g : MulAut W) (X : Subgroup (MulAut W)) :
    rk ↥(conjAutSub g X) = rk ↥X := by
  unfold rk conjAutSub
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite W] in
private theorem rk_subgroupOf {X K : Subgroup (MulAut W)} (h : X ≤ K) :
    rk ↥(X.subgroupOf K) = rk ↥X := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

omit [Finite W] in
private theorem subgroupOf_inf_centralizer {X K : Subgroup (MulAut W)} (hLK : L ≤ K) :
    X.subgroupOf K ⊓ Subgroup.centralizer ((L.subgroupOf K : Subgroup ↥K) : Set ↥K) =
      (X ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf K := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun l hl => congrArg Subtype.val (hc ⟨l, hLK hl⟩ hl)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun l hl => Subtype.ext (hc _ hl)⟩

private theorem conj_inv_mem_ml (hB : D321Base M Mp T L V t) {a : MulAut W} (haM : a ∈ M)
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut W))) : t⁻¹ * a * t ∈ ML := by
  refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hB.t_mem) haM) hB.t_mem, ?_⟩
  show t⁻¹ * a * t ∈ Subgroup.normalizer (L : Set (MulAut W))
  rw [mem_normalizer_iff_conjAutSub, conjAutSub_mul, conjAutSub_mul,
    hB.conj_Lt_of_mem_normalizer haM haN, conjAutSub_inv_conjAutSub]

private theorem nB_smul_conj (hB : D321Base M Mp T L V t) {A : Subgroup (MulAut W)} (hAM : A ≤ M)
    {g : MulAut W} (hg : g ∈ M) (hgA : conjAutSub g⁻¹ A ≤ M)
    (S : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) :
    letI := qAct hB.hD.hyp.Mp_normal
    nB (A.subgroupOf M) ((⟨g, hg⟩ : ↥M) • S) = nB ((conjAutSub g⁻¹ A).subgroupOf M) S := by
  let _i := qAct hB.hD.hyp.Mp_normal
  set gM : ↥M := ⟨g, hg⟩ with hgM
  have hset : gM • S ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤ =
      gM • (S ⊓ XMod.fixed ↥((conjAutSub g⁻¹ A).subgroupOf M) ⊤) := by
    ext q
    rw [Subgroup.mem_inf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_inf]
    constructor
    · rintro ⟨hq, -, hfix⟩
      refine ⟨hq, trivial, fun b => ?_⟩
      have hb : g * ((b : ↥M) : MulAut W) * g⁻¹ ∈ A := by
        have h1 := Subgroup.mem_subgroupOf.1 b.2
        rw [mem_conjAutSub_iff, inv_inv] at h1
        exact h1
      have hbM : (⟨g * ((b : ↥M) : MulAut W) * g⁻¹, hAM hb⟩ : ↥M) ∈ A.subgroupOf M :=
        Subgroup.mem_subgroupOf.2 hb
      have e : (b : ↥M) * gM⁻¹ = gM⁻¹ * ⟨g * ((b : ↥M) : MulAut W) * g⁻¹, hAM hb⟩ := by
        apply Subtype.ext
        show ((b : ↥M) : MulAut W) * g⁻¹ = g⁻¹ * (g * ((b : ↥M) : MulAut W) * g⁻¹)
        group
      show (b : ↥M) • gM⁻¹ • q = gM⁻¹ • q
      rw [smul_smul, e, mul_smul]
      exact congrArg (gM⁻¹ • ·) (hfix ⟨_, hbM⟩)
    · rintro ⟨hq, -, hfix⟩
      refine ⟨hq, trivial, fun a => ?_⟩
      have ha : g⁻¹ * ((a : ↥M) : MulAut W) * g ∈ conjAutSub g⁻¹ A := by
        rw [mem_conjAutSub_iff, inv_inv]
        have h1 := Subgroup.mem_subgroupOf.1 a.2
        simpa [mul_assoc] using h1
      have haM : (⟨g⁻¹ * ((a : ↥M) : MulAut W) * g, hgA ha⟩ : ↥M) ∈
          (conjAutSub g⁻¹ A).subgroupOf M := Subgroup.mem_subgroupOf.2 ha
      have h1 := hfix ⟨_, haM⟩
      have e : (⟨g⁻¹ * ((a : ↥M) : MulAut W) * g, hgA ha⟩ : ↥M) * gM⁻¹ = gM⁻¹ * (a : ↥M) := by
        apply Subtype.ext
        show g⁻¹ * ((a : ↥M) : MulAut W) * g * g⁻¹ = g⁻¹ * ((a : ↥M) : MulAut W)
        group
      change (⟨g⁻¹ * ((a : ↥M) : MulAut W) * g, hgA ha⟩ : ↥M) • gM⁻¹ • q = gM⁻¹ • q at h1
      rw [smul_smul, e, mul_smul] at h1
      have h2 := congrArg (gM • ·) h1
      have h3 : (a : ↥M) • q = q := by simpa using h2
      exact h3
  unfold nB
  rw [rk_smul, hset, rk_smul]

private theorem nB_ml_eq (hB : D321Base M Mp T L V t) {X : Subgroup (MulAut W)} (hX : X ≤ ML)
    (S : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) :
    (letI := qAct (ml_le_normalizer hB); nB (X.subgroupOf (ML)) S) =
      (letI := qAct hB.hD.hyp.Mp_normal; nB (X.subgroupOf M) S) := by
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  have hfix : XMod.fixed ↥(X.subgroupOf (ML)) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) =
      XMod.fixed ↥(X.subgroupOf M) ⊤ := by
    refine fixed_eq_of_surj (fun x => ⟨⟨((x : ↥(ML)) : MulAut W), (x : ↥(ML)).2.1⟩, x.2⟩)
      (fun x => ⟨⟨⟨((x : ↥M) : MulAut W), hX x.2⟩, x.2⟩, rfl⟩) (fun x q => ?_) ⊤
    induction q using QuotientGroup.induction_on with
    | H w => rfl
  unfold nB
  rw [hfix]

omit [Finite W] in
private theorem rk_eq_three_of_card {Q : Type*} [CommGroup Q] {S : Subgroup Q}
    (h : Nat.card ↥S = 8) :
    rk ↥S = 3 := by
  unfold rk
  rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

structure IIbSit (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W)
    (A : Subgroup (MulAut W)) (r : ℚ) (s : MulAut W) : Prop where
  hS : D321Sit M Mp T L V t A r
  hVt : ∀ v ∈ V, ∀ y ∈ conjAutSub t L, y v = v
  hsT : s ∈ T
  hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))
  hU : commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom
  hdisj : tilde Mp ⊤ V ⊓ tilde Mp ⊤ (s • V) = ⊥
  hpsl : IsPSL 3 2 1 ↥(autSub L (orbSup T V))
  hcard : Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)
  hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥

omit [Finite W] in
private theorem mem_conj_inv {X : Subgroup (MulAut W)} {x : MulAut W} :
    x ∈ conjAutSub t⁻¹ X ↔ t * x * t⁻¹ ∈ X := by
  rw [mem_conjAutSub_iff, inv_inv]

private theorem mem_centralizer_Mp (hB : D321Base M Mp T L V t) {x : MulAut W}
    (h1 : x ∈ Subgroup.centralizer (L : Set (MulAut W)))
    (h2 : x ∈ Subgroup.centralizer (conjAutSub t L : Set (MulAut W))) :
    x ∈ Subgroup.centralizer (Mp : Set (MulAut W)) := by
  rw [Subgroup.mem_centralizer_iff] at h1 h2 ⊢
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hz
  calc a * b * x = a * (b * x) := mul_assoc _ _ _
    _ = a * (x * b) := by rw [h2 b hb]
    _ = (a * x) * b := (mul_assoc _ _ _).symm
    _ = (x * a) * b := by rw [h1 a ha]
    _ = x * (a * b) := mul_assoc _ _ _

namespace IIbSit

variable {A : Subgroup (MulAut W)} {r : ℚ} {s : MulAut W} (h : IIbSit M Mp T L V t A r s)
include h

private theorem hB : D321Base M Mp T L V t := h.hS.toD321Base

private theorem perm {x : MulAut W} (hx : x ∈ ML) (hxT : x ∈ T) :
    letI := qAct (ml_le_normalizer h.hB)
    (⟨x, hx⟩ : ↥(ML)) • tilde Mp ⊤ V = tilde Mp ⊤ V ∨
      (⟨x, hx⟩ : ↥(ML)) • tilde Mp ⊤ V = (⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V := by
  let _j := qAct (ml_le_normalizer h.hB)
  rw [smul_tildeQ (ml_le_normalizer h.hB), smul_tildeQ (ml_le_normalizer h.hB)]
  exact tilde_smul_eq_or_eq h.hB h.hsT h.hU hxT hx.2

private theorem perm' {x : MulAut W} (hx : x ∈ ML) (hxT : x ∈ T) :
    letI := qAct (ml_le_normalizer h.hB)
    (⟨x, hx⟩ : ↥(ML)) • ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V) =
        (⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V ∨
      (⟨x, hx⟩ : ↥(ML)) • ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V) =
        tilde Mp ⊤ V := by
  let _j := qAct (ml_le_normalizer h.hB)
  have hxs : x * s ∈ ML := (ML).mul_mem hx ⟨h.hB.T_le h.hsT, h.hsN⟩
  rw [smul_smul]
  have e : (⟨x, hx⟩ : ↥(ML)) * ⟨s, h.hB.T_le h.hsT, h.hsN⟩ = ⟨x * s, hxs⟩ := rfl
  rw [e]
  exact (h.perm hxs (T.mul_mem hxT h.hsT)).symm

private theorem count {X : Subgroup (MulAut W)} (hXML : X ≤ ML) (hXT : X ≤ T)
    (hX2 : ∀ a ∈ X, a * a = 1) (hnc : ¬ X ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    letI := qAct (ml_le_normalizer h.hB)
    2 * (rk ↥X - rk ↥(X ⊓ Subgroup.centralizer (L : Set (MulAut W)))) + 2 ≤
      nB (X.subgroupOf (ML)) (isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
        isoSum (L.subgroupOf (ML)) ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V)) := by
  let _j := qAct (ml_le_normalizer h.hB)
  have hirr := isIrr_ml h.hB h.hVt
  obtain ⟨π, -, hπ⟩ := exists_nat_ml h.hB h.hVt h.hpsl h.hcard
  obtain ⟨k, hk, hk2⟩ := two_le_mult h.hB h.hS.htop h.hVt h.hsT h.hsN
    (iso_or_iso_ml h.hB h.hVt h.hpsl h.hcard h.hsT h.hsN h.hdisj)
  have hnc' : ¬ X.subgroupOf (ML) ≤
      Subgroup.centralizer ((L.subgroupOf (ML) : Subgroup ↥(ML)) : Set ↥(ML)) := by
    intro hle
    apply hnc
    intro x hx
    have h1 := hle (show (⟨x, hXML hx⟩ : ↥(ML)) ∈ X.subgroupOf (ML) from hx)
    rw [Subgroup.mem_centralizer_iff] at h1 ⊢
    intro l hl
    exact congrArg Subtype.val (h1 ⟨l, L_le_ml h.hB hl⟩ hl)
  have hc := one_side_count (Γ := ↥(ML)) h.hB.quot_sq ml_normal hirr (injective_ml h.hB h.hVt)
    hπ (rk_eq_three_of_card (card_tilde_eq h.hcard))
    (not_iso_ml h.hB h.hVt h.hsT h.hsN h.hdisj) hk hk2 (P := X.subgroupOf (ML))
    (fun a ha => Subtype.ext (hX2 _ ha)) (fun a ha => h.perm a.2 (hXT ha))
    (fun a ha => h.perm' a.2 (hXT ha)) hnc'
  rwa [subgroupOf_inf_centralizer (L_le_ml h.hB), rk_subgroupOf hXML,
    rk_subgroupOf (inf_le_left.trans hXML)] at hc

private theorem smul_le_tildeU (g : ↥(ML)) :
    letI := qAct (ml_le_normalizer h.hB)
    g • tilde Mp ⊤ V ≤ tilde Mp ⊤ (commV L) := by
  let _j := qAct (ml_le_normalizer h.hB)
  rw [smul_tildeQ (ml_le_normalizer h.hB)]
  refine tilde_mono ?_
  have h1 : (g : MulAut W) • V ≤ (g : MulAut W) • commV L :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (h.hB.V_le_commV h.hVt)
  refine h1.trans (le_of_eq ?_)
  change (commV L).map (g : MulAut W).toMonoidHom = commV L
  rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 g.2.2]

private theorem Y_le :
    letI := qAct (ml_le_normalizer h.hB)
    isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
        isoSum (L.subgroupOf (ML)) ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V) ≤
      tilde Mp ⊤ (commV L) := by
  let _j := qAct (ml_le_normalizer h.hB)
  refine sup_le (iSup₂_le fun g _ => h.smul_le_tildeU g) (iSup₂_le fun g _ => ?_)
  rw [smul_smul]
  exact h.smul_le_tildeU _

private theorem smul_Y_le {x : MulAut W} (hx : x ∈ ML) (hxT : x ∈ T) :
    letI := qAct (ml_le_normalizer h.hB)
    (⟨x, hx⟩ : ↥(ML)) • (isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
        isoSum (L.subgroupOf (ML)) ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V)) ≤
      isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
        isoSum (L.subgroupOf (ML)) ((⟨s, h.hB.T_le h.hsT, h.hsN⟩ : ↥(ML)) • tilde Mp ⊤ V) := by
  let _j := qAct (ml_le_normalizer h.hB)
  rw [Subgroup.smul_sup, smul_isoSum ml_normal, smul_isoSum ml_normal]
  refine sup_le ?_ ?_
  · rcases h.perm hx hxT with e | e <;> rw [e]
    · exact le_sup_left
    · exact le_sup_right
  · rcases h.perm' hx hxT with e | e <;> rw [e]
    · exact le_sup_right
    · exact le_sup_left

private theorem nonswap_false (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))) : False := by
  have hB := h.hB
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  have hAM := h.hS.A_le
  have hAML : A ≤ ML := le_inf hAM hAN
  have hAT := h.hS.hAT
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact h.hS.elemAb.2 a ha
  set B := conjAutSub t⁻¹ A with hBdef
  have hBA : ∀ x ∈ B, t * x * t⁻¹ ∈ A := fun x hx => mem_conj_inv.1 hx
  have hBe : ∀ x : MulAut W, x = t⁻¹ * (t * x * t⁻¹) * t := fun x => by group
  have hBML : B ≤ ML := fun x hx => by
    rw [hBe x]
    exact conj_inv_mem_ml hB (hAM (hBA x hx)) (hAN (hBA x hx))
  have hBT : B ≤ T := fun x hx => by
    rw [hBe x]
    exact T.mul_mem (T.mul_mem (T.inv_mem hB.htT) (hAT (hBA x hx))) hB.htT
  have hBM : B ≤ M := hBML.trans inf_le_left
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    rw [hBe x]
    have h1 := hA2 _ (hBA x hx)
    calc t⁻¹ * (t * x * t⁻¹) * t * (t⁻¹ * (t * x * t⁻¹) * t) =
        t⁻¹ * ((t * x * t⁻¹) * (t * x * t⁻¹)) * t := by group
      _ = 1 := by rw [h1]; group
  set sM : ↥(ML) := ⟨s, hB.T_le h.hsT, h.hsN⟩ with hsM
  set Y := isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
    isoSum (L.subgroupOf (ML)) (sM • tilde Mp ⊤ V) with hY
  set tM : ↥M := ⟨t, hB.t_mem⟩ with htM
  have hc1 : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) →
      2 * (rk ↥A - rk ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) + 2 ≤
        nB (A.subgroupOf M) Y := fun hnc => by
    have h1 := h.count hAML hAT hA2 hnc
    rwa [nB_ml_eq hB hAML] at h1
  have hc2 : ¬ B ≤ Subgroup.centralizer (L : Set (MulAut W)) →
      2 * (rk ↥B - rk ↥(B ⊓ Subgroup.centralizer (L : Set (MulAut W)))) + 2 ≤
        nB (A.subgroupOf M) (tM • Y) := fun hnc => by
    have h1 := h.count hBML hBT hB2 hnc
    rwa [nB_ml_eq hB hBML, ← nB_smul_conj hB hAM hB.t_mem hBM] at h1
  have hYA : ∀ x ∈ T, ∀ hx : x ∈ ML, ∀ y ∈ Y, (⟨x, hx.1⟩ : ↥M) • y ∈ Y := by
    intro x hxT hx y hy
    have h1 : (⟨x, hx.1⟩ : ↥M) • y = (⟨x, hx⟩ : ↥(ML)) • y := by
      induction y using QuotientGroup.induction_on with
      | H w => rfl
    rw [h1]
    exact h.smul_Y_le hx hxT (Subgroup.smul_mem_pointwise_smul _ _ _ hy)
  have hinv1 : ∀ b ∈ A.subgroupOf M, ∀ y ∈ Y, b • y ∈ Y := fun b hb y hy =>
    hYA _ (hAT hb) (hAML hb) y hy
  have hinv2 : ∀ b ∈ A.subgroupOf M, ∀ y ∈ tM • Y, b • y ∈ tM • Y := by
    intro b hb y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy ⊢
    have hb' : t⁻¹ * ((b : ↥M) : MulAut W) * t ∈ B := by
      rw [mem_conj_inv]
      have h1 : t * (t⁻¹ * ((b : ↥M) : MulAut W) * t) * t⁻¹ = ((b : ↥M) : MulAut W) := by group
      rw [h1]
      exact hb
    have h1 := hYA _ (hBT hb') (hBML hb') _ hy
    have e : tM⁻¹ • b • y = (⟨_, (hBML hb').1⟩ : ↥M) • tM⁻¹ • y := by
      rw [smul_smul, smul_smul]
      congr 1
      apply Subtype.ext
      show t⁻¹ * ((b : ↥M) : MulAut W) = t⁻¹ * ((b : ↥M) : MulAut W) * t * t⁻¹
      group
    rw [e]
    exact h1
  have hdisj : Y ⊓ tM • Y = ⊥ := by
    have h1 := hB.inf_tildeU h.hVt
    rw [eq_bot_iff, ← h1]
    exact inf_le_inf h.Y_le
      ((Subgroup.pointwise_smul_le_pointwise_smul_iff (a := tM)).2 h.Y_le)
  have hsum := nB_sup_of_inf_eq_bot (A.subgroupOf M) hinv1 hinv2 hdisj
  have hN := nB_mono (A.subgroupOf M) (le_top : Y ⊔ tM • Y ≤ ⊤)
  have hle := h.hS.nB_le
  have hrkB : rk ↥B = rk ↥A := rk_conjAutSub _ _
  have hcent : rk ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) +
      rk ↥(B ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≤ rk ↥A := by
    rw [← rk_conjAutSub t (B ⊓ _)]
    refine rk_add_rk_le h.hS.elemAb inf_le_left ?_ ?_
    · rintro x hx
      rw [mem_conjAutSub_iff] at hx
      have h1 := hBA _ hx.1
      have h2 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [h2] at h1
    · rw [eq_bot_iff]
      rintro x ⟨⟨hxA, hxL⟩, hx⟩
      replace hx : x ∈ conjAutSub t (B ⊓ Subgroup.centralizer (L : Set (MulAut W))) := hx
      replace hxL : x ∈ Subgroup.centralizer (L : Set (MulAut W)) := hxL
      rw [mem_conjAutSub_iff] at hx
      have hxLt : x ∈ Subgroup.centralizer (conjAutSub t L : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 := (Subgroup.mem_centralizer_iff.1 hx.2) _ (mem_conjAutSub_iff.1 hl)
        calc l * x = t * ((t⁻¹ * l * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
          _ = t * ((t⁻¹ * x * t) * (t⁻¹ * l * t)) * t⁻¹ := by rw [h1]
          _ = x * l := by group
      have hmem : x ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
        ⟨hxA, mem_centralizer_Mp hB hxL hxLt⟩
      rw [h.hAC] at hmem
      exact hmem
  have hpos := h.hS.rk_pos
  by_cases h1 : A ≤ Subgroup.centralizer (L : Set (MulAut W)) <;>
    by_cases h2 : B ≤ Subgroup.centralizer (L : Set (MulAut W))
  · rw [inf_eq_left.2 h1, inf_eq_left.2 h2, hrkB] at hcent
    omega
  · have hc := hc2 h2
    rw [inf_eq_left.2 h1] at hcent
    omega
  · have hc := hc1 h1
    rw [inf_eq_left.2 h2, hrkB] at hcent
    omega
  · have hc := hc1 h1
    have hc' := hc2 h2
    omega

private theorem smul_tildeU_eq {g : MulAut W} (hg : g ∈ ML) :
    letI := qAct h.hB.hD.hyp.Mp_normal
    (⟨g, hg.1⟩ : ↥M) • tilde Mp ⊤ (commV L) = tilde Mp ⊤ (commV L) := by
  let _i := qAct h.hB.hD.hyp.Mp_normal
  rw [smul_tildeQ h.hB.hD.hyp.Mp_normal]
  congr 1
  change (commV L).map g.toMonoidHom = commV L
  rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hg.2]

private theorem twelve_le_rk_tildeU : 12 ≤ rk ↥(tilde Mp ⊤ (commV L)) := by
  let _j := qAct (ml_le_normalizer h.hB)
  have hirr := isIrr_ml h.hB h.hVt
  obtain ⟨k, hk, hk2⟩ := two_le_mult h.hB h.hS.htop h.hVt h.hsT h.hsN
    (iso_or_iso_ml h.hB h.hVt h.hpsl h.hcard h.hsT h.hsN h.hdisj)
  set sM : ↥(ML) := ⟨s, h.hB.T_le h.hsT, h.hsN⟩
  have hniso := not_iso_ml h.hB h.hVt h.hsT h.hsN h.hdisj
  have hN := normalizes_whole (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (L.subgroupOf (ML))
    ml_normal
  have hniso' : ¬ XMod.Iso ↥(L.subgroupOf (ML)) (sM • tilde Mp ⊤ V) (tilde Mp ⊤ V) :=
    fun h' => hniso (XMod.Iso.symm (XMod.isInv_smul_of_normalizes hN sM hirr.1) h')
  have hinf := inf_isoSum_smul ml_normal hirr hniso'
  rw [smul_isoSum ml_normal sM] at hinf
  have h1 := rk_sup_add_rk_inf (isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V))
    (isoSum (L.subgroupOf (ML)) (sM • tilde Mp ⊤ V))
  have hrk3 : rk ↥(tilde Mp ⊤ V) = 3 := rk_eq_three_of_card (card_tilde_eq h.hcard)
  have e1 : rk ↥(isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V)) = k * 3 := by rw [hk, hrk3]
  have e2 : rk ↥(isoSum (L.subgroupOf (ML)) (sM • tilde Mp ⊤ V)) = k * 3 := by
    rw [← smul_isoSum ml_normal sM, rk_smul, e1]
  rw [hinf, rk_bot, e1, e2] at h1
  have h2 : rk ↥(isoSum (L.subgroupOf (ML)) (tilde Mp ⊤ V) ⊔
      isoSum (L.subgroupOf (ML)) (sM • tilde Mp ⊤ V)) ≤ rk ↥(tilde Mp ⊤ (commV L)) :=
    rk_mono h.Y_le
  omega

private theorem swap_false {a₀ : MulAut W} (ha₀ : a₀ ∈ A)
    (ha₀N : a₀ ∉ Subgroup.normalizer (L : Set (MulAut W))) : False := by
  have hB := h.hB
  let _i := qAct hB.hD.hyp.Mp_normal
  let _j := qAct (ml_le_normalizer hB)
  have hAM := h.hS.A_le
  have hAT := h.hS.hAT
  have hE := h.hS.elemAb
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hE.2 a ha
  set A₀ := A ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hA₀
  have hsplit : ∀ x ∈ A, x ∈ A₀ ∨ a₀⁻¹ * x ∈ A₀ := by
    intro x hx
    by_cases hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W))
    · exact Or.inl ⟨hx, hxN⟩
    · exact Or.inr ⟨A.mul_mem (A.inv_mem ha₀) hx,
        hB.inv_mul_mem_normalizer (hAM ha₀) (hAM hx) ha₀N hxN⟩
  have hAp : IsPGroup 2 ↥A := h.hS.isPGroup
  have hrkA : rk ↥A ≤ rk ↥A₀ + 1 := rk_le_succ hAp inf_le_left hsplit
  have hA₀C : A₀ ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxA, -⟩, hxL⟩
    replace hxL : x ∈ Subgroup.centralizer (L : Set (MulAut W)) := hxL
    have hsw := (hB.conj_swap (hAM ha₀) ha₀N).1
    have hxLt : x ∈ Subgroup.centralizer (conjAutSub t L : Set (MulAut W)) := by
      rw [← hsw, Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' := mem_conjAutSub_iff.1 hl
      have h1 := (Subgroup.mem_centralizer_iff.1 hxL) _ hl'
      have hc : a₀ * x = x * a₀ := hE.1 a₀ ha₀ x hxA
      have hc' : a₀⁻¹ * x = x * a₀⁻¹ := by
        calc a₀⁻¹ * x = a₀⁻¹ * (x * a₀) * a₀⁻¹ := by group
          _ = a₀⁻¹ * (a₀ * x) * a₀⁻¹ := by rw [hc]
          _ = x * a₀⁻¹ := by group
      calc l * x = a₀ * ((a₀⁻¹ * l * a₀) * (a₀⁻¹ * x * a₀)) * a₀⁻¹ := by group
        _ = a₀ * ((a₀⁻¹ * l * a₀) * x) * a₀⁻¹ := by
            rw [show a₀⁻¹ * x * a₀ = x by rw [hc']; group]
        _ = a₀ * (x * (a₀⁻¹ * l * a₀)) * a₀⁻¹ := by rw [h1]
        _ = a₀ * x * a₀⁻¹ * l := by group
        _ = x * l := by rw [hc]; group
    have hmem : x ∈ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) :=
      ⟨hxA, mem_centralizer_Mp hB hxL hxLt⟩
    rw [h.hAC] at hmem
    exact hmem
  have hA₀ML : A₀ ≤ ML := inf_le_inf_right _ hAM
  have hrkA₀ : rk ↥A₀ ≤ 3 := by
    set P₀ := A₀.subgroupOf (ML) with hP₀
    set sM : ↥(ML) := ⟨s, hB.T_le h.hsT, h.hsN⟩ with hsM
    set P₁ := P₀ ⊓ MulAction.stabilizer ↥(ML) (tilde Mp ⊤ V) with hP₁
    have hP₀2 : ∀ a ∈ P₀, a * a = 1 := fun a ha => Subtype.ext (hA2 _ ha.1)
    have hP₀p : IsPGroup 2 ↥P₀ := isPGroup_of_mul_self hP₀2
    have hrk01 : rk ↥P₀ ≤ rk ↥P₁ + 1 := by
      by_cases hex : ∃ a₁ ∈ P₀, a₁ • tilde Mp ⊤ V ≠ tilde Mp ⊤ V
      · obtain ⟨a₁, ha₁, ha₁V⟩ := hex
        have ha₁s : a₁ • tilde Mp ⊤ V = sM • tilde Mp ⊤ V :=
          (h.perm a₁.2 (hAT ha₁.1)).resolve_left ha₁V
        refine rk_le_succ hP₀p inf_le_left (a := a₁) fun x hx => ?_
        rcases h.perm x.2 (hAT hx.1) with hxV | hxV
        · exact Or.inl ⟨hx, hxV⟩
        · refine Or.inr ⟨P₀.mul_mem (P₀.inv_mem ha₁) hx, ?_⟩
          show (a₁⁻¹ * x) • tilde Mp ⊤ V = tilde Mp ⊤ V
          rw [mul_smul]
          change a₁⁻¹ • ((⟨_, x.2⟩ : ↥(ML)) • tilde Mp ⊤ V) = _
          rw [hxV, ← ha₁s, inv_smul_smul]
      · push Not at hex
        have hP : P₁ = P₀ := le_antisymm inf_le_left fun x hx => ⟨hx, hex x hx⟩
        rw [hP]
        omega
    have hrk1 : rk ↥P₁ ≤ 2 := by
      have hP₁0 : rk ↥(P₁ ⊓ Subgroup.centralizer
          ((L.subgroupOf (ML) : Subgroup ↥(ML)) : Set ↥(ML))) = 0 := by
        have h1 : P₁ ⊓ Subgroup.centralizer ((L.subgroupOf (ML) : Subgroup ↥(ML)) : Set ↥(ML)) ≤
            (A₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf (ML) := by
          rw [← subgroupOf_inf_centralizer (L_le_ml hB)]
          exact inf_le_inf_right _ inf_le_left
        rw [hA₀C, Subgroup.bot_subgroupOf] at h1
        rw [le_bot_iff.1 h1, rk_bot]
      by_cases hnc : P₁ ≤ Subgroup.centralizer
          ((L.subgroupOf (ML) : Subgroup ↥(ML)) : Set ↥(ML))
      · rw [inf_eq_left.2 hnc] at hP₁0
        omega
      · have hirr := isIrr_ml hB h.hVt
        obtain ⟨π, -, hπ⟩ := exists_nat_ml hB h.hVt h.hpsl h.hcard
        have hsV : sM • tilde Mp ⊤ V ≠ tilde Mp ⊤ V := by
          intro heq
          have h1 : tilde Mp ⊤ V ⊓ sM • tilde Mp ⊤ V = ⊥ := by
            rw [smul_tildeQ (ml_le_normalizer hB)]
            exact h.hdisj
          rw [heq, inf_idem] at h1
          exact hB.tilde_ne_bot h1
        obtain ⟨-, he⟩ := one_side_matrix_count (Γ := ↥(ML)) hB.quot_sq ml_normal hirr
          (injective_ml hB h.hVt) hπ (rk_eq_three_of_card (card_tilde_eq h.hcard))
          (not_iso_ml hB h.hVt h.hsT h.hsN h.hdisj) (P := P₁)
          (fun a ha => hP₀2 a ha.1) (fun a ha => ha.2)
          (fun a ha => by
            rcases h.perm' a.2 (hAT ha.1.1) with e | e
            · exact e
            · exfalso
              apply hsV
              have h2 : a • tilde Mp ⊤ V = tilde Mp ⊤ V := ha.2
              have h3 := e.trans h2.symm
              have h4 := congrArg (a⁻¹ • ·) h3
              simpa using h4) hnc
        omega
    have e : rk ↥P₀ = rk ↥A₀ := rk_subgroupOf hA₀ML
    omega
  set a₀M : ↥M := ⟨a₀, hAM ha₀⟩ with ha₀M
  have hUinv : XMod.IsInv ↥(A₀.subgroupOf M) (tilde Mp ⊤ (commV L)) := by
    intro b q hq
    have h1 := h.smul_tildeU_eq ((hA₀ML (show ((b : ↥M) : MulAut W) ∈ A₀ from b.2)))
    have h2 : ((b : ↥M)) • q ∈ ((b : ↥M)) • tilde Mp ⊤ (commV L) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hq
    rw [show ((b : ↥M)) = ⟨((b : ↥M) : MulAut W), (hA₀ML b.2).1⟩ from rfl, h1] at h2
    exact h2
  have hswapU : a₀M • tilde Mp ⊤ (commV L) = (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) := by
    rw [hB.smul_tildeU, smul_tildeQ hB.hD.hyp.Mp_normal]
    congr 1
    change (commV L).map a₀.toMonoidHom = commV (conjAutSub t L)
    rw [map_commV_conjAutSub, (hB.conj_swap (hAM ha₀) ha₀N).1]
  have hdisjU : tilde Mp ⊤ (commV L) ⊓ a₀M • tilde Mp ⊤ (commV L) = ⊥ := by
    rw [hswapU]
    exact hB.inf_tildeU h.hVt
  have hidx := nB_index_two (A := A.subgroupOf M) (A' := A₀.subgroupOf M) (a := a₀M) ha₀
    (Subtype.ext (hE.2 a₀ ha₀))
    (fun x hx y hy => Subtype.ext (hE.1 _ hx _ hy))
    (Subgroup.subgroupOf_mono M inf_le_left)
    (fun x hx => (hsplit _ hx).imp id id) hUinv hdisjU
  have hN := nB_mono (A.subgroupOf M)
    (le_top : tilde Mp ⊤ (commV L) ⊔ a₀M • tilde Mp ⊤ (commV L) ≤ ⊤)
  have hle := h.hS.nB_le
  have h12 := h.twelve_le_rk_tildeU
  omega

end IIbSit

theorem caseIIb_false {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
    (hc : D36cConcl Mp T L V t) (hne : commSub (orbSup T V) L ≠ V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) : False := by
  obtain ⟨hVt, -, -, hIII⟩ := hc
  obtain ⟨hpsl, ⟨s, hsT, hsN, hsV⟩, hall, hcard⟩ := hIII.resolve_left hne
  obtain ⟨hU, hsum⟩ := hall s hsT hsN hsV
  have h : IIbSit M Mp T L V t A r s :=
    ⟨hS, hVt, hsT, hsN, hU, tilde_inf_tilde_eq_bot hsum, hpsl, hcard, hAC⟩
  by_cases hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  · exact h.nonswap_false hAN
  · obtain ⟨a₀, ha₀, ha₀N⟩ := Set.not_subset.1 hAN
    exact h.swap_false ha₀ ha₀N

end SecIIb

end CFSG.Quasithin.SmithD321
