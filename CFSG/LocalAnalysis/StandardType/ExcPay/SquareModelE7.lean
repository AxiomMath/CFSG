module

public import CFSG.LocalAnalysis.StandardType.ExcPay.InnerSplit
public import CFSG.LocalAnalysis.StandardType.ExcPay.CardE7
public import CFSG.LocalAnalysis.StandardType.ExcPay.DatumE7
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
public import CFSG.LieType.AschbacherSeitz.RootGroupTransport
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AschbacherSeitz CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem exists_excPay_image_inf_E7 {G : Type} [Group G] {p f : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : Subgroup.center ↥X = ⊥) (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∃ E : Subgroup (adjointGroup .E7 (GaloisField 2 f)), IsElemAbelian p E ∧
      Nat.card E = Nat.card ↥(X ⊓ Bs : Subgroup G) ∧
      ∀ g : adjointGroup .E7 (GaloisField 2 f), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 →
        g ∈ E := by
  obtain ⟨-, hSCX⟩ := excPay_inner_split hBs hSC hZ hinn
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  let E : Subgroup (adjointGroup .E7 (GaloisField 2 f)) := A0.map κ.symm.toMonoidHom
  have hA0el : IsElemAbelian p A0 := (hBs.mono inf_le_right).comap X.subtype_injective
  refine ⟨E, hA0el.map κ.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := A0) (f := κ.symm.toMonoidHom) κ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  intro g hcent hgp
  have hgpX : ((κ g : ↥X) : G) ^ p = 1 := by
    simpa using congrArg (fun z : ↥X => (z : G))
      (show (κ g : ↥X) ^ p = 1 by rw [← map_pow, hgp, map_one])
  have hcentX : ∀ x ∈ X ⊓ Bs, (κ g : G) * x = x * (κ g : G) := by
    intro x hx
    let x' : ↥X := ⟨x, hx.1⟩
    have hx' : x' ∈ A0 := Subgroup.mem_subgroupOf.mpr hx
    have hmem : κ.symm x' ∈ E := Subgroup.mem_map.mpr ⟨x', hx', by simp⟩
    have h := hcent (κ.symm x') hmem
    have h' : ((κ g : ↥X) * x' : ↥X) = x' * κ g := by
      simpa using congrArg (fun z => κ z) h
    have h'' := congrArg (fun z : ↥X => (z : G)) h'
    simpa [x'] using h''
  have hy : (κ g : G) ∈ Bs := hSCX (κ g) (κ g).2 hcentX hgpX
  refine Subgroup.mem_map.mpr ⟨κ g, ?_, by simp⟩
  exact Subgroup.mem_subgroupOf.mpr ⟨(κ g).2, hy⟩


private theorem excPayN_fix_map_conj_inv {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L) :
    D.fix.map (MulAut.conj D.g0⁻¹).toMonoidHom = D.model := by
  have h := congrArg (fun H : Subgroup (ModGL τ L) =>
    H.map (MulAut.conj D.g0⁻¹).toMonoidHom) D.map_conj_model
  rw [Subgroup.map_map] at h
  have hcomp : (MulAut.conj D.g0⁻¹).toMonoidHom.comp (MulAut.conj D.g0).toMonoidHom =
      MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change (MulAut.conj D.g0⁻¹) ((MulAut.conj D.g0) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    group
  rw [hcomp, Subgroup.map_id] at h
  exact h.symm

private theorem excPayN_center_eq_bot {G : Type} [Group G] {f : ℕ} {X : Subgroup G}
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X) :
    Subgroup.center ↥X = ⊥ := by
  have h1 := Subgroup.map_center_eq κ.symm
  rw [center_adjointGroup_eq_bot] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ κ.symm.injective).1 h1

private theorem excPayN_card_inf {G : Type} [Group G] {p f : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Nat.card ↥(X ⊓ Bs : Subgroup G) = p ^ 7 := by
  obtain ⟨E, hEel, hcardE, hESC⟩ :=
    exists_excPay_image_inf_E7 hBs hSC (excPayN_center_eq_bot κ) κ hinn
  rw [← hcardE]
  exact card_eq_pow_seven_of_sc_E7 (K := GaloisField 2 f) hp hp5
    (by rw [GaloisField.card 2 f (by omega)]; exact hplus) E hEel hESC

private theorem excPayN_perfect_and_lie {f : ℕ} {Y : Type} [Group Y]
    (hf : 1 ≤ f) (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* Y) :
    commutator Y = ⊤ ∧
      CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .E7 0 2 f := by
  haveI hsc : Group.IsPerfect ↥(e7Data_valid.minGroup (GaloisField 2 f)) :=
    isPerfect_e7 _
  haveI hperfA : Group.IsPerfect ↥(adjointGroup .E7 (GaloisField 2 f)) :=
    Group.IsPerfect.ofSurjective (f := (e7EquivAlg f).toMonoidHom) (e7EquivAlg f).surjective
  haveI hperfY : Group.IsPerfect Y :=
    @Group.IsPerfect.ofSurjective ↥(adjointGroup .E7 (GaloisField 2 f)) Y _ _
      κ.toMonoidHom hperfA κ.surjective
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  let A' := ↥(adjointGroup .E7 (GaloisField 2 f))
  have hmod : CFSG.Blueprint.UntwistedChevalleyModel
      (A' ⧸ Subgroup.center A') .E7 (2 ^ f) :=
    ⟨GaloisField 2 f, inferInstance, inferInstance, hKcard, ⟨MulEquiv.refl _⟩⟩
  have hcm : CFSG.Blueprint.ChevalleyExceptionalModel
      (A' ⧸ Subgroup.center A') .E7 2 f := ⟨hadm, hmod⟩
  have hlieU : CFSG.Blueprint.LieModel (A' ⧸ Subgroup.center A') .E7 0 2 f :=
    Or.inr (Or.inl ⟨rfl, by decide, hcm⟩)
  have hcenterMap : (Subgroup.center A').map κ.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq κ
  let eQ : (A' ⧸ Subgroup.center A') ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center A') (Subgroup.center Y) κ hcenterMap
  exact CFSG.Blueprint.LieModel.of_mulEquiv eQ hlieU

private theorem excPayN_presG0 {G : Type} [Group G] [Finite G] {f : ℕ} {X : Subgroup G}
    (hf : 1 ≤ f) (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X) :
    ∃ ψ₀ : (ggU .E7 0 f).K →* G,
      ψ₀.range = X ∧ GGPresentsG0 X (ggU .E7 0 f).D .E7 0 f ψ₀ := by
  let φ : (ggU .E7 0 f).K →* adjointGroup .E7 (GaloisField 2 f) :=
    (e7EquivAlg f).toMonoidHom
  let ψ₀ : (ggU .E7 0 f).K →* G := X.subtype.comp (κ.toMonoidHom.comp φ)
  have hψrange : ψ₀.range = X := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (κ (φ k)).2
    · intro hx
      obtain ⟨a, ha⟩ := (e7EquivAlg f).surjective (κ.symm ⟨x, hx⟩)
      refine ⟨a, ?_⟩
      show ((κ (φ a) : ↥X) : G) = x
      rw [show φ a = κ.symm ⟨x, hx⟩ from ha, MulEquiv.apply_symm_apply]
  have hψinj : Function.Injective ψ₀ := by
    intro a b h
    have h1 : κ (φ a) = κ (φ b) := Subtype.ext h
    exact (e7EquivAlg f).injective (κ.injective h1)
  have hψker : ψ₀.ker ≤ Subgroup.center (ggU .E7 0 f).K := by
    rw [(MonoidHom.ker_eq_bot_iff ψ₀).mpr hψinj]
    exact bot_le
  obtain ⟨hcomm, hlie⟩ := excPayN_perfect_and_lie hf κ
  have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  have hrk : 2 ≤ (ggU .E7 0 f).D.rank := by
    rw [show (ggU .E7 0 f).D.rank = 7 from rfl]
    norm_num
  exact ⟨ψ₀, hψrange, ⟨⟨hadm, hrk⟩, ⟨hψrange, hψker⟩, hcomm, hlie⟩⟩

private theorem excPayN_bridgeTheta {G : Type} [Group G] [Finite G] {f : ℕ}
    {X : Subgroup G} {ht : GGExcFive .E7} (hf : 1 ≤ f)
    (hZ : Subgroup.center ↥X = ⊥)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X) :
    ∃ θ : ↥X →* ModGL (langTag .E7) GGL,
      Function.Injective θ ∧ θ.range = ⁅ggFixGp .E7 f, ggFixGp .E7 f⁆ := by
  obtain ⟨ψ₀, -, hpres⟩ := excPayN_presG0 hf κ
  obtain ⟨θ, -, hθker, hθrange, -⟩ :=
    LieCore.ggLieBridge_theta (t := .E7) (n := 0) (f := f) ht hf hpres
  exact ⟨θ, (MonoidHom.ker_eq_bot_iff θ).mp (by rw [hθker, hZ]), hθrange⟩

private theorem excPayN_exists_eta {G : Type} [Group G] {f p : ℕ} {X : Subgroup G}
    {ht : GGExcFive .E7} (M : GGDatumModel .E7 f p ht)
    {θ : ↥X →* ModGL (langTag .E7) GGL} (hθinj : Function.Injective θ)
    (hθrange : θ.range = ⁅ggFixGp .E7 f, ggFixGp .E7 f⁆) :
    ∃ η : ↥X ≃* ↥M.D.Γ,
      ∀ x : ↥X, (η x : ModGL (langTag .E7) GGL) = (MulAut.conj M.D.g0⁻¹) (θ x) := by
  let c : ModGL (langTag .E7) GGL →* ModGL (langTag .E7) GGL :=
    (MulAut.conj M.D.g0⁻¹).toMonoidHom
  let θ' : ↥X →* ModGL (langTag .E7) GGL := c.comp θ
  have hcinj : Function.Injective c := fun a b h =>
    (MulAut.conj M.D.g0⁻¹).injective h
  have hθ'inj : Function.Injective θ' := hcinj.comp hθinj
  have hfixmap : M.D.fix.map c = M.D.model := excPayN_fix_map_conj_inv M.D
  have hθ'range : θ'.range = M.D.Γ := by
    change (c.comp θ).range = M.D.Γ
    rw [MonoidHom.range_comp, hθrange, ← ggFixGp_eq_fix M.D M.hΦ,
      Subgroup.map_commutator, hfixmap]
    rfl
  let ψ : ↥X →* ↥M.D.Γ := θ'.codRestrict M.D.Γ (fun x => by
    have hx : θ' x ∈ θ'.range := ⟨x, rfl⟩
    rwa [hθ'range] at hx)
  have hψinj : Function.Injective ψ := fun a b h => hθ'inj (Subtype.ext_iff.mp h)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : ModGL (langTag .E7) GGL) ∈ θ'.range := by
      rw [hθ'range]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  let η : ↥X ≃* ↥M.D.Γ := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  refine ⟨η, ?_⟩
  intro x
  rfl

private theorem excPayN_torsion_closure (p : ℕ) :
    (powMonoidHom p).ker.map (rootDiagUnitHom (langTag .E7) GGL) =
      Subgroup.closure {z | ∃ a : Fin (langTag .E7).rank → GGLˣ,
        (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .E7) a = z} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.subset_closure ⟨a, ?_, rfl⟩
    intro i
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
    simpa [Pi.pow_apply] using congrFun ha i
  · rw [Subgroup.closure_le]
    rintro z ⟨a, ha, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    funext i
    simpa [Pi.pow_apply] using ha i

private theorem exists_excPayModel_E7_of_datum {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hf : 1 ≤ f) (hBs : IsElemAbelian p Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hdat : ∀ A : Subgroup (ModGL (langTag .E7) GGL), A ≤ ggFixGp .E7 f → IsElemAbelian p A →
      Nat.card A = Nat.card ↥(X ⊓ Bs : Subgroup G) →
      ∃ M : GGDatumModel .E7 f p ht,
        A.map (MulAut.conj M.D.g0⁻¹).toMonoidHom =
          Subgroup.closure {z | ∃ a : Fin (langTag .E7).rank → GGLˣ,
            (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .E7) a = z}) :
    ∃ (M : GGDatumModel .E7 f p ht) (η : ↥X ≃* ↥M.D.Γ),
      ∀ z : ModGL (langTag .E7) GGL,
        (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .E7) GGL) = z) ↔
          ∃ a : Fin (langTag .E7).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
            rootDiagUnit (langTag .E7) a = z := by
  classical
  have hZ : Subgroup.center ↥X = ⊥ := excPayN_center_eq_bot κ
  obtain ⟨θ, hθinj, hθrange⟩ := excPayN_bridgeTheta (ht := ht) hf hZ κ
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  let A : Subgroup (ModGL (langTag .E7) GGL) := A0.map θ
  have hA : A ≤ ggFixGp .E7 f := by
    calc A ≤ θ.range := Subgroup.map_le_range θ A0
      _ = ⁅ggFixGp .E7 f, ggFixGp .E7 f⁆ := hθrange
      _ ≤ ggFixGp .E7 f := Subgroup.commutator_le_self _
  have hA0el : IsElemAbelian p A0 := (hBs.mono inf_le_right).comap X.subtype_injective
  have hAel : IsElemAbelian p A := hA0el.map θ
  have hcardA : Nat.card A = Nat.card ↥(X ⊓ Bs : Subgroup G) := by
    rw [Subgroup.card_map_of_injective (K := A0) (f := θ) hθinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : (X ⊓ Bs : Subgroup G) ≤ X)).toEquiv
  obtain ⟨M, hM⟩ := hdat A hA hAel hcardA
  obtain ⟨η, hη⟩ := excPayN_exists_eta M hθinj hθrange
  refine ⟨M, η, ?_⟩
  have hTpS := excPayN_torsion_closure p
  intro z
  constructor
  · rintro ⟨x, hxBs, rfl⟩
    have hxmem : x ∈ A0 := Subgroup.mem_subgroupOf.mpr ⟨x.2, hxBs⟩
    have hzA : (MulAut.conj M.D.g0⁻¹) (θ x) ∈
        A.map (MulAut.conj M.D.g0⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨θ x, Subgroup.mem_map.mpr ⟨x, hxmem, rfl⟩, rfl⟩
    rw [hM, ← hTpS] at hzA
    obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hzA
    refine ⟨a, ?_, ?_⟩
    · intro i
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
      simpa [Pi.pow_apply] using congrFun ha i
    · rw [hη x]
      exact heq
  · rintro ⟨a, ha, rfl⟩
    have haP : a ∈ (powMonoidHom p).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      funext i
      simpa [Pi.pow_apply] using ha i
    have hzTp : rootDiagUnit (langTag .E7) a ∈
        (powMonoidHom p).ker.map (rootDiagUnitHom (langTag .E7) GGL) :=
      Subgroup.mem_map.mpr ⟨a, haP, rfl⟩
    rw [hTpS, ← hM] at hzTp
    obtain ⟨y, hyA, hy⟩ := Subgroup.mem_map.mp hzTp
    obtain ⟨x, hxmem, rfl⟩ := Subgroup.mem_map.mp hyA
    refine ⟨x, (Subgroup.mem_subgroupOf.mp hxmem).2, ?_⟩
    rw [hη x]
    exact hy

theorem exists_excPayModel_E7 {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .E7} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
      ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∃ (M : GGDatumModel .E7 f p ht) (η : ↥X ≃* ↥M.D.Γ),
      ∀ z : ModGL (langTag .E7) GGL,
        (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .E7) GGL) = z) ↔
          ∃ a : Fin (langTag .E7).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
            rootDiagUnit (langTag .E7) a = z := by
  have hinf : Nat.card ↥(X ⊓ Bs : Subgroup G) = p ^ 7 :=
    excPayN_card_inf hp hp5 hf hplus hBs hSC κ (fun b hb => (hinn b hb).2)
  exact exists_excPayModel_E7_of_datum hf hBs κ fun A hA hAel hcardA =>
    exists_datumModel_E7_of_card hp hp5 hf hplus A hA hAel (hcardA.trans hinf)

theorem exists_excPayModel_E7_of_toral {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) (hBs : IsElemAbelian p Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinf : p ^ 7 ≤ Nat.card ↥(X ⊓ Bs : Subgroup G))
    (htor : ∀ A : Subgroup (ModGL (langTag .E7) GGL), A ≤ ggFixGp .E7 f → IsElemAbelian p A →
      p ^ 7 ≤ Nat.card A → IsToralSubgroup .E7 GGL A) :
    ∃ (M : GGDatumModel .E7 f p ht) (η : ↥X ≃* ↥M.D.Γ),
      ∀ z : ModGL (langTag .E7) GGL,
        (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .E7) GGL) = z) ↔
          ∃ a : Fin (langTag .E7).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
            rootDiagUnit (langTag .E7) a = z :=
  exists_excPayModel_E7_of_datum hf hBs κ fun A hA hAel hcardA =>
    exists_datumModel_E7_of_toral hp hp3 hf hplus A hA hAel (hinf.trans_eq hcardA.symm)
      (htor A hA hAel (hinf.trans_eq hcardA.symm))

end CFSG.StandardType.ExcPay
