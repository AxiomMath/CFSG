module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Background.AutSubConj
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.D2Involutions
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.FFC5Two
public import CFSG.Quasithin.Background.FFC6P
public import CFSG.Quasithin.EmptyFaithful.SzF53MConj
public import CFSG.Quasithin.H13.A7Nat1233ModAbs
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import Certificates.Certificate7022
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_a7Four_restrictionData
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) :
    let W := Vtil V₀ V hV
    let H : Subgroup (MulAut W) := lBar V₀ V hV L
    let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
    H ≤ stabSub U₁ ∧ Nat.card ↥U₁ = 2 ^ 4 ∧
      Nat.card (autSub H U₁) = 2520 ∧ (∀ u : ↥U₁, u * u = 1) := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
  have hdata := s168e3_a7Four_spaceData c hrow
  have hHU : H ≤ stabSub U₁ :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant
      (CFSG.Quasithin.SmithD321.commSub_isInv (⊤ : Subgroup W) H)
  have hrowBot : A7Four H U₁ ⊥ := by
    have h := hrow
    rw [show U₁ ⊓ fixV H = ⊥ from hdata.fixedKernel_eq_bot] at h
    exact h
  have hcardH : Nat.card ↥H = 2520 :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four hrowBot
  have hcardU : Nat.card ↥U₁ = 2 ^ 4 := by
    have h16 := CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8.card_of_a7Four_bot hrowBot
    rw [h16]
    norm_num
  have hsqU : ∀ u : ↥U₁, u * u = 1 := fun u =>
    Subtype.ext (by
      have h := s15_Infra_vtil_sq_eq_one V₀ V hV (u : W)
      simpa [pow_two] using h)
  obtain ⟨α, hreal⟩ := hrowBot
  obtain ⟨π, hπ⟩ := hreal
  have hfaith : ∀ x ∈ H, (∀ u ∈ U₁, x u = u) → x = 1 :=
    FFC.faithful_on_of_realizes (FFC.a7Four_faithful α) hπ
  have hkerbot : H ⊓ centSub U₁ = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.1 hh
    let hH : ↥H := ⟨h, hhH⟩
    apply Subgroup.mem_bot.2
    show (h : MulAut W) = (1 : MulAut W)
    exact hfaith hH hH.2 (fun u hu => (mem_centSub.1 hhc) u hu)
  have hcardGamma : Nat.card (autSub H U₁) = 2520 := by
    have hcard := card_autSub_mul (A := H) (U := U₁) hHU
    rw [hkerbot, Subgroup.card_bot, mul_one, hcardH] at hcard
    exact hcard
  exact ⟨hHU, hcardU, hcardGamma, hsqU⟩

theorem s168e3_restrict_block_normalizer_mem_a7
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {v : G} (hvM : v ∈ D.M)
    (hvN : v ∈ normalizer (wSub V₀ V hV L : Set G)) :
    let U₁ : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
    let φ : MulAut (Vtil V₀ V hV) :=
      actTil V₀ V hV ⟨v,
        le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
          c.setting.hyp151.hyp125.pairFacts.le_normalizer₀ hvM⟩
    ∃ hφU : φ ∈ stabSub U₁,
      resHom U₁ ⟨φ, hφU⟩ ∈ autSub (lBar V₀ V hV L) U₁ := by
  classical
  dsimp only
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
  let vS : stabTil V₀ V :=
    ⟨v, le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
      c.setting.hyp151.hyp125.pairFacts.le_normalizer₀ hvM⟩
  let φ : MulAut W := actTil V₀ V hV vS
  have hdata := s168e3_a7Four_spaceData c hrow
  have hvn : v ∈ nBar D.M V₀ V hV L := by
    rw [← inf_normalizer_wSub_eq_nBar D c.setting.hyp151 hV]
    exact Subgroup.mem_inf.2 ⟨hvM, hvN⟩
  have hconjH : barSub V₀ V hV (conjSubgroup L v) = H :=
    (s15_Infra_mem_nBar_iff c.setting.hyp151.hyp125 hV hvM).1 hvn
  have hmapinv : H.map (MulAut.conj φ⁻¹).toMonoidHom = H := by
    have h := s15_Infra_barSub_conjSubgroup V₀ V hV
      (le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
        c.setting.hyp151.hyp125.pairFacts.le_normalizer₀ hvM) L
    rw [hconjH] at h
    exact h.symm
  have hφN : φ ∈ Subgroup.normalizer (H : Set (MulAut W)) := by
    have h1 : φ⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmapinv
    exact (Subgroup.inv_mem_iff (Subgroup.normalizer (H : Set (MulAut W)))).1 h1
  have hφU : φ ∈ stabSub U₁ := by
    refine mem_stabSub.2 fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · have h1 : φ⁻¹ (φ u) ∈ U₁ :=
        CFSG.Quasithin.SmithD321.commSub_stab (D := (⊤ : Subgroup W)) (K := H) (g := φ⁻¹)
          ((Subgroup.normalizer (H : Set (MulAut W))).inv_mem hφN)
          (fun w _ => Subgroup.mem_top w) (φ u) hu
      simpa using h1
    · exact CFSG.Quasithin.SmithD321.commSub_stab (D := (⊤ : Subgroup W)) (K := H) (g := φ)
        hφN (fun w _ => Subgroup.mem_top w) u hu
  obtain ⟨hHU, hcardU, hcardGamma, hsqU⟩ := s168e3_a7Four_restrictionData c hrow
  let t : MulAut U₁ := resHom U₁ ⟨φ, hφU⟩
  have hHmap : H.map (MulAut.conj φ).toMonoidHom = H :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hφN
  have htn : t ∈ Subgroup.normalizer (autSub H U₁ : Set (MulAut U₁)) := by
    refine (Subgroup.mem_normalizer_iff_map_conj_eq).2 ?_
    have h := CFSG.Quasithin.StabLat.autSub_map_conj_eq (X := H) (U := U₁) (t := φ) hφU
    rw [hHmap] at h
    exact h.symm
  have htGamma : t ∈ autSub H U₁ :=
    CFSG.Quasithin.H13.A7.mem_of_mem_normalizer_four hsqU hcardU hcardGamma htn
  exact ⟨hφU, htGamma⟩



theorem s168e3_block_involution_fixV_le_four_one
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {v : G} (hvM : v ∈ D.M) (hv2 : v * v = 1)
    (hvN : v ∈ normalizer (wSub V₀ V hV L : Set G)) :
    let φ : MulAut (Vtil V₀ V hV) :=
      actTil V₀ V hV ⟨v,
        le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
          c.setting.hyp151.hyp125.pairFacts.le_normalizer₀ hvM⟩
    Nat.card ↥(fixV (Subgroup.zpowers φ) ⊓ wTil V₀ V hV L) ≤ 4 ∨
      wTil V₀ V hV L ≤ fixV (Subgroup.zpowers φ) := by
  classical
  dsimp only
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let U₁ : Subgroup W := commSub (⊤ : Subgroup W) H
  let vS : stabTil V₀ V :=
    ⟨v, le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
      c.setting.hyp151.hyp125.pairFacts.le_normalizer₀ hvM⟩
  let φ : MulAut W := actTil V₀ V hV vS
  obtain ⟨hφU, htGamma⟩ := s168e3_restrict_block_normalizer_mem_a7 c hrow hvM hvN
  let t : MulAut U₁ := resHom U₁ ⟨φ, hφU⟩
  obtain ⟨hHU, hcardU, hcardGamma, hsqU⟩ := s168e3_a7Four_restrictionData c hrow
  have hφ2 : φ * φ = 1 := by
    dsimp [φ]
    rw [← map_mul]
    have hvS : vS * vS = 1 := Subtype.ext (by simpa [vS] using hv2)
    rw [hvS, map_one]
  have ht2 : t * t = 1 := by
    have hpair : (⟨φ, hφU⟩ : stabSub U₁) * ⟨φ, hφU⟩ = 1 := Subtype.ext (by simpa using hφ2)
    dsimp [t]
    rw [← map_mul, hpair, map_one]
  have hrkfix := rk_fixV_resHom (W := U₁) (g := φ) hφU
  have hcardfix : Nat.card ↥(fixV (Subgroup.zpowers t)) =
      Nat.card ↥(U₁ ⊓ fixV (Subgroup.zpowers φ)) := by
    rw [card_eq_two_pow (fun u => by simpa [pow_two] using hsqU u) (fixV (Subgroup.zpowers t)),
      card_eq_two_pow (fun w => s15_Infra_vtil_sq_eq_one V₀ V hV w)
        (U₁ ⊓ fixV (Subgroup.zpowers φ)), hrkfix]
  by_cases ht1 : t = 1
  · right
    intro u hu
    rw [mem_fixV_zpowers_iff]
    have h := congrArg (fun x : U₁ => (x : W)) (show t ⟨u, hu⟩ = ⟨u, hu⟩ by rw [ht1]; rfl)
    simpa [t, resHom_apply] using h
  · left
    have hle := CFSG.Quasithin.H13.A7.card_fixV_le_four_of_inv (W := ↥U₁)
      hsqU hcardU hcardGamma htGamma ht2 ht1
    rw [inf_comm]
    show Nat.card ↥(U₁ ⊓ fixV (Subgroup.zpowers φ)) ≤ 4
    rw [← hcardfix]
    exact hle


omit [Finite G] in
private theorem s168e3_conjSub_inv (V : Subgroup G) (h : G) :
    CFSG.Quasithin.conjSub h⁻¹ V = conjSubgroup V h := by
  ext x
  rw [CFSG.Quasithin.mem_conjSub, mem_conjSubgroup_iff]
  simp

private noncomputable def s168e3_intModConjOf (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g h : G) (hVh : conjSubgroup V h = conjSubgroup V g) :
    IntMod V hV ≃* IntMod (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) :=
  let e : ↥V ≃* ↥(conjSubgroup V g) :=
    (CFSG.Quasithin.F53Mod.mulEquivConjSub h⁻¹ V).trans
      (MulEquiv.subgroupCongr ((s168e3_conjSub_inv V h).trans hVh))
  MulEquiv.mk e.toEquiv e.map_mul'

omit [Finite G] in
@[simp] private theorem s168e3_intModConjOf_val (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g h : G) (hVh : conjSubgroup V h = conjSubgroup V g) (x : IntMod V hV) :
    (s168e3_intModConjOf V hV g h hVh x).val = h⁻¹ * x.val * h := by
  change (((CFSG.Quasithin.F53Mod.mulEquivConjSub h⁻¹ V).trans
      (MulEquiv.subgroupCongr ((s168e3_conjSub_inv V h).trans hVh)))
      ⟨x.val, x.property⟩).val = h⁻¹ * x.val * h
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    CFSG.Quasithin.F53Mod.coe_mulEquivConjSub]
  simp

omit [Finite G] in
@[simp] private theorem s168e3_intModConjOf_symm_val (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g h : G) (hVh : conjSubgroup V h = conjSubgroup V g)
    (y : IntMod (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g)) :
    ((s168e3_intModConjOf V hV g h hVh).symm y).val = h * y.val * h⁻¹ := by
  change ((CFSG.Quasithin.F53Mod.mulEquivConjSub h⁻¹ V).symm
      ((MulEquiv.subgroupCongr ((s168e3_conjSub_inv V h).trans hVh)).symm
        (⟨y.val, IntMod.val_mem y⟩ : ↥(conjSubgroup V g)))).val =
    h * y.val * h⁻¹
  have hf53 : ∀ z : ↥(CFSG.Quasithin.conjSub h⁻¹ V),
      ((CFSG.Quasithin.F53Mod.mulEquivConjSub h⁻¹ V).symm z).val =
        h * z.val * h⁻¹ := fun z => by
    dsimp [CFSG.Quasithin.F53Mod.mulEquivConjSub]
    rw [inv_inv]
  rw [hf53, MulEquiv.subgroupCongr_symm_apply]

omit [Finite G] in
private theorem s168e3_map_subgroupCongr {A B N M : Subgroup G} (hA : A = B) (hN : N = M)
    (hNA : N ≤ A) :
    (N.subgroupOf A).map (MulEquiv.subgroupCongr hA).toMonoidHom = M.subgroupOf B := by
  subst hA
  subst hN
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ((MulEquiv.subgroupCongr (rfl : A = A) x : ↥A) : G) ∈ N
    rw [MulEquiv.subgroupCongr_apply]
    exact hx
  · intro hy
    refine ⟨⟨y, hNA hy⟩, hy, ?_⟩
    apply Subtype.ext
    exact MulEquiv.subgroupCongr_apply (rfl : A = A) ⟨y, hNA hy⟩

omit [Finite G] in
private theorem s168e3_map_subgroupOf_intModConjOf
    (V : Subgroup G) (hV : IsElemAbelian 2 V) (g h : G)
    (hVh : conjSubgroup V h = conjSubgroup V g) (V₀ : Subgroup G) (hV₀V : V₀ ≤ V)
    (hV₀h : conjSubgroup V₀ h = conjSubgroup V₀ g) :
    (modNull V₀ V hV).map (s168e3_intModConjOf V hV g h hVh).toMonoidHom =
      modNull (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g) := by
  change (V₀.subgroupOf V).map (s168e3_intModConjOf V hV g h hVh).toMonoidHom =
    (conjSubgroup V₀ g).subgroupOf (conjSubgroup V g)
  change ((V₀.subgroupOf V).map
      (↑((CFSG.Quasithin.F53Mod.mulEquivConjSub h⁻¹ V).trans
        (MulEquiv.subgroupCongr ((s168e3_conjSub_inv V h).trans hVh))) :
        ↥V →* ↥(conjSubgroup V g))) =
    (conjSubgroup V₀ g).subgroupOf (conjSubgroup V g)
  rw [MulEquiv.toMonoidHom_trans, ← Subgroup.map_map,
    CFSG.Quasithin.F53Mod.map_subgroupOf_mulEquivConjSub]
  have hNA : CFSG.Quasithin.conjSub h⁻¹ V₀ ≤ CFSG.Quasithin.conjSub h⁻¹ V := by
    rw [s168e3_conjSub_inv V₀ h, s168e3_conjSub_inv V h]
    exact E3.conjSubgroup_mono_left h hV₀V
  simpa only [MulEquiv.toMonoidHom_eq_coe] using
    s168e3_map_subgroupCongr ((s168e3_conjSub_inv V h).trans hVh)
      ((s168e3_conjSub_inv V₀ h).trans hV₀h) hNA

private noncomputable def s168e3_tilConjOf (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g h : G) (hVh : conjSubgroup V h = conjSubgroup V g) (V₀ : Subgroup G)
    (hV₀V : V₀ ≤ V) (hV₀h : conjSubgroup V₀ h = conjSubgroup V₀ g) :
    Vtil V₀ V hV ≃* Vtil (conjSubgroup V₀ g) (conjSubgroup V g)
      (E3.isElemAbelian_conjSubgroup hV g) :=
  QuotientGroup.congr (modNull V₀ V hV)
    (modNull (conjSubgroup V₀ g) (conjSubgroup V g)
      (E3.isElemAbelian_conjSubgroup hV g))
    (s168e3_intModConjOf V hV g h hVh)
    (s168e3_map_subgroupOf_intModConjOf V hV g h hVh V₀ hV₀V hV₀h)

omit [Finite G] in
@[simp] private theorem s168e3_tilConjOf_mk (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g h : G) (hVh : conjSubgroup V h = conjSubgroup V g) (V₀ : Subgroup G)
    (hV₀V : V₀ ≤ V) (hV₀h : conjSubgroup V₀ h = conjSubgroup V₀ g) (x : IntMod V hV) :
    s168e3_tilConjOf V hV g h hVh V₀ hV₀V hV₀h (mkTil V₀ V hV x) =
      mkTil (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g)
        (s168e3_intModConjOf V hV g h hVh x) :=
  QuotientGroup.congr_mk _ _ _ _ x


@[expose] def A7FourBlockInvolutionBound (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  ∀ (g : G) (X : Subgroup G), X ∈ wConj D.M V₀ V hV L →
    ∀ (v : G), v ∈ conjSubgroup D.M g → v * v = 1 →
      v ∈ normalizer (conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g : Set G) →
      let hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
      let V₁g : Subgroup G := conjSubgroup (v1Sub D.M V₀ V hV L) g
      let Dg : Subgroup G := conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g
      ∀ (hstab : v ∈ stabTil V₁g (conjSubgroup V g)),
      let φ : MulAut (Vtil V₁g (conjSubgroup V g) hVg) :=
        actTil V₁g (conjSubgroup V g) hVg ⟨v, hstab⟩
      Nat.card ↥(fixV (Subgroup.zpowers φ) ⊓
        imgTil V₁g (conjSubgroup V g) hVg Dg) ≤ 4 ∨
        imgTil V₁g (conjSubgroup V g) hVg Dg ≤ fixV (Subgroup.zpowers φ)

private theorem s168e3_block_involutionBound_core
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {V₁ : Subgroup G} (hV₁ : V₁ = V₀) :
    ∀ (g : G) (X : Subgroup G), X ∈ wConj D.M V₀ V hV L →
      ∀ (v : G), v ∈ conjSubgroup D.M g → v * v = 1 →
        v ∈ normalizer (conjSubgroup (X ⊔ V₁) g : Set G) →
        let hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
        let V₁g : Subgroup G := conjSubgroup V₁ g
        let Dg : Subgroup G := conjSubgroup (X ⊔ V₁) g
        ∀ (hstab : v ∈ stabTil V₁g (conjSubgroup V g)),
        let φ : MulAut (Vtil V₁g (conjSubgroup V g) hVg) :=
          actTil V₁g (conjSubgroup V g) hVg ⟨v, hstab⟩
        Nat.card ↥(fixV (Subgroup.zpowers φ) ⊓
          imgTil V₁g (conjSubgroup V g) hVg Dg) ≤ 4 ∨
          imgTil V₁g (conjSubgroup V g) hVg Dg ≤ fixV (Subgroup.zpowers φ) := by
  subst V₁
  intro g X hX v hvM hv2 hvN
  classical
  obtain ⟨m, hm, hXeq⟩ := hX
  have hdata := s168e3_a7Four_spaceData c hrow
  rw [hXeq] at hvN ⊢
  dsimp only
  intro hstab
  let W := wSub V₀ V hV L
  let U₀ : Subgroup G := W ⊔ V₀
  let hh : G := m * g
  let Vg : Subgroup G := conjSubgroup V g
  let V₀g : Subgroup G := conjSubgroup V₀ g
  let Dg : Subgroup G := conjSubgroup U₀ hh
  have hpf := c.setting.hyp151.hyp125.pairFacts
  have h125 := c.setting.hyp151.hyp125
  have hV₀m : conjSubgroup V₀ m = V₀ :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hpf.le_normalizer₀ hm)
  have hmapU : conjSubgroup (W ⊔ V₀) m = conjSubgroup W m ⊔ conjSubgroup V₀ m :=
    Subgroup.map_sup _ _ _
  have hDg : conjSubgroup (conjSubgroup W m ⊔ V₀) g = Dg := by
    rw [← hV₀m, ← hmapU, conjSubgroup_conjSubgroup]
  rw [hDg] at hvN ⊢
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hpf.le_normalizer hm)
  have hVh : conjSubgroup V hh = Vg := by
    dsimp [hh, Vg]
    calc conjSubgroup V (m * g) = conjSubgroup (conjSubgroup V m) g :=
          (conjSubgroup_conjSubgroup V m g).symm
      _ = conjSubgroup V g := by rw [hVm]
  have hV₀h : conjSubgroup V₀ hh = V₀g := by
    dsimp [hh, V₀g]
    calc conjSubgroup V₀ (m * g) = conjSubgroup (conjSubgroup V₀ m) g :=
          (conjSubgroup_conjSubgroup V₀ m g).symm
      _ = conjSubgroup V₀ g := by rw [hV₀m]
  let hVg : IsElemAbelian 2 Vg := E3.isElemAbelian_conjSubgroup hV g
  let e := s168e3_intModConjOf V hV g hh hVh
  let qe : Vtil V₀ V hV ≃* Vtil V₀g Vg hVg :=
    s168e3_tilConjOf V hV g hh hVh V₀ hpf.le hV₀h
  let v0 : G := hh * v * hh⁻¹
  have hv0M : v0 ∈ D.M := by
    have hv : g * v * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hvM
    have e0 : v0 = m * (g * v * g⁻¹) * m⁻¹ := by
      dsimp [v0, hh]; group
    rw [e0]
    exact D.M.mul_mem (D.M.mul_mem hm hv) (D.M.inv_mem hm)
  have hv0sq : v0 * v0 = 1 := by
    dsimp [v0]
    rw [show hh * v * hh⁻¹ * (hh * v * hh⁻¹) = hh * (v * v) * hh⁻¹ by group, hv2]
    group
  have hv0N : v0 ∈ normalizer (W : Set G) := by
    have hconjDg : conjSubgroup Dg v = Dg :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hvN
    have hconjDg' : conjSubgroup (conjSubgroup U₀ hh) v = conjSubgroup U₀ hh := hconjDg
    have hconjU₀ : conjSubgroup U₀ v0 = U₀ := by
      have e0 : v0 = hh * v * hh⁻¹ := rfl
      rw [e0]
      calc conjSubgroup U₀ (hh * v * hh⁻¹)
          = conjSubgroup (conjSubgroup U₀ (hh * v)) hh⁻¹ :=
              (conjSubgroup_conjSubgroup U₀ (hh * v) hh⁻¹).symm
        _ = conjSubgroup (conjSubgroup (conjSubgroup U₀ hh) v) hh⁻¹ := by
              rw [(conjSubgroup_conjSubgroup U₀ hh v).symm]
        _ = conjSubgroup (conjSubgroup U₀ hh) hh⁻¹ := by rw [hconjDg']
        _ = conjSubgroup U₀ (hh * hh⁻¹) :=
              conjSubgroup_conjSubgroup U₀ hh hh⁻¹
        _ = U₀ := by rw [mul_inv_cancel, conjSubgroup_one]
    have hU0W : U₀ = W := sup_eq_left.mpr (s15_Two_le_wSub hV hpf.le L)
    rw [← hU0W]
    exact conjSubgroup_eq_iff_mem_normalizer.mp hconjU₀
  let φ0 : MulAut (Vtil V₀ V hV) :=
    actTil V₀ V hV ⟨v0, c.m_le_stabTil hv0M⟩
  let ψ : MulAut (Vtil V₀g Vg hVg) := actTil V₀g Vg hVg ⟨v, hstab⟩
  have hone := s168e3_block_involution_fixV_le_four_one c hrow hv0M hv0sq hv0N
  have hcomm : ∀ q : Vtil V₀ V hV, qe (φ0 q) = ψ (qe q) := by
    intro q
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    dsimp [φ0, ψ, qe, e]
    rw [actTil_mk, s168e3_tilConjOf_mk]
    rw [s168e3_tilConjOf_mk, actTil_mk]
    have hval : (s168e3_intModConjOf V hV g hh hVh
          (actStab V₀ V hV ⟨v0, c.m_le_stabTil hv0M⟩ x)).val =
        (actStab V₀g Vg hVg ⟨v, hstab⟩
          (s168e3_intModConjOf V hV g hh hVh x)).val := by
      simp only [s168e3_intModConjOf_val, actStab_apply_val]
      dsimp [v0]
      group
    have huv : s168e3_intModConjOf V hV g hh hVh
          (actStab V₀ V hV ⟨v0, c.m_le_stabTil hv0M⟩ x) =
        actStab V₀g Vg hVg ⟨v, hstab⟩
          (s168e3_intModConjOf V hV g hh hVh x) :=
      IntMod.val_injective hval
    rw [huv]
  have hUiff : ∀ q : Vtil V₀ V hV,
      q ∈ imgTil V₀ V hV U₀ ↔ qe q ∈ imgTil V₀g Vg hVg Dg := by
    intro q
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    dsimp [qe]
    rw [s168e3_tilConjOf_mk]
    simp only [mem_imgTil]
    constructor
    · rintro ⟨y, hyU, hyx⟩
      refine ⟨s168e3_intModConjOf V hV g hh hVh y, ?_, ?_⟩
      · rw [s168e3_intModConjOf_val]
        show hh⁻¹ * y.val * hh ∈ Dg
        rw [show Dg = conjSubgroup U₀ hh from rfl, mem_conjSubgroup_iff]
        show hh * (hh⁻¹ * y.val * hh) * hh⁻¹ ∈ U₀
        rw [show hh * (hh⁻¹ * y.val * hh) * hh⁻¹ = y.val by group]
        exact hyU
      ·
        have hq : mkTil V₀ V hV y = mkTil V₀ V hV x := hyx
        have hqe := congrArg (fun z => qe z) hq
        dsimp only [qe] at hqe
        rw [s168e3_tilConjOf_mk, s168e3_tilConjOf_mk] at hqe
        exact hqe
    · rintro ⟨z, hzDg, hzx⟩
      refine ⟨(s168e3_intModConjOf V hV g hh hVh).symm z, ?_, ?_⟩
      · rw [s168e3_intModConjOf_symm_val]
        show hh * z.val * hh⁻¹ ∈ U₀
        have hz : z.val ∈ conjSubgroup U₀ hh := by
          have : Dg = conjSubgroup U₀ hh := rfl
          rwa [this] at hzDg
        exact mem_conjSubgroup_iff.1 hz
      · apply qe.injective
        rw [s168e3_tilConjOf_mk, s168e3_tilConjOf_mk]
        simpa using hzx
  have hfixiff : ∀ q : Vtil V₀ V hV,
      q ∈ fixV (Subgroup.zpowers φ0) ↔ qe q ∈ fixV (Subgroup.zpowers ψ) := by
    intro q
    rw [mem_fixV_zpowers_iff, mem_fixV_zpowers_iff]
    constructor
    · intro hq
      rw [← hcomm q, hq]
    · intro hq
      apply qe.injective
      rw [hcomm q, hq]
  have hU0W : U₀ = W := sup_eq_left.mpr (s15_Two_le_wSub hV hpf.le L)
  have hU1eq : imgTil V₀ V hV U₀ = wTil V₀ V hV L := by
    rw [hU0W]
    have : imgTil V₀ V hV (wSub V₀ V hV L) = wTil V₀ V hV L := by
      rw [wSub, imgTil_preTil]
    exact this
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers φ0) ⊓ imgTil V₀ V hV U₀) =
      Nat.card ↥(fixV (Subgroup.zpowers ψ) ⊓ imgTil V₀g Vg hVg Dg) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun q => ⟨qe q.1, ?_⟩
        invFun := fun y => ⟨qe.symm y.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact Subgroup.mem_inf.2 ⟨(hfixiff q.1).1 (Subgroup.mem_inf.1 q.2).1,
        (hUiff q.1).1 (Subgroup.mem_inf.1 q.2).2⟩
    · refine Subgroup.mem_inf.2 ⟨(hfixiff (qe.symm y.1)).2 ?_,
        (hUiff (qe.symm y.1)).2 ?_⟩
      · simpa using (Subgroup.mem_inf.1 y.2).1
      · simpa using (Subgroup.mem_inf.1 y.2).2
    · intro q
      apply Subtype.ext
      simp
    · intro y
      apply Subtype.ext
      simp
  have hcont : imgTil V₀ V hV U₀ ≤ fixV (Subgroup.zpowers φ0) ↔
      imgTil V₀g Vg hVg Dg ≤ fixV (Subgroup.zpowers ψ) := by
    constructor
    · intro h y hy
      have hq : qe.symm y ∈ imgTil V₀ V hV U₀ :=
        (hUiff (qe.symm y)).2 (by simpa using hy)
      have hfix : qe.symm y ∈ fixV (Subgroup.zpowers φ0) := h hq
      simpa using ((hfixiff (qe.symm y)).1 hfix)
    · intro h q hq
      exact (hfixiff q).2 (h ((hUiff q).1 hq))
  change Nat.card ↥(fixV (Subgroup.zpowers ψ) ⊓ imgTil V₀g Vg hVg Dg) ≤ 4 ∨
    imgTil V₀g Vg hVg Dg ≤ fixV (Subgroup.zpowers ψ)
  rcases hone with h | h
  · left
    rw [← hcard]
    rw [← hU1eq] at h
    exact h
  · right
    rw [← hcont, hU1eq]
    exact h



theorem s168e3_block_involutionBound
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) :
    A7FourBlockInvolutionBound D V₀ V L hV := by
  have hdata := s168e3_a7Four_spaceData c hrow
  exact s168e3_block_involutionBound_core c hrow
    (V₁ := v1Sub D.M V₀ V hV L) hdata.v1Sub_eq



theorem s168e3_block_involution_fixV_le_four
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {g : G} {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    {v : G} (hvM : v ∈ conjSubgroup D.M g) (hv2 : v * v = 1)
    (hvN : v ∈ normalizer
      (conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g : Set G)) :
    let hVg : IsElemAbelian 2 (conjSubgroup V g) :=
      E3.isElemAbelian_conjSubgroup hV g
    let V₁g : Subgroup G := conjSubgroup (v1Sub D.M V₀ V hV L) g
    let Dg : Subgroup G := conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g
    ∀ (hstab : v ∈ stabTil V₁g (conjSubgroup V g)),
    let φ : MulAut (Vtil V₁g (conjSubgroup V g) hVg) :=
      actTil V₁g (conjSubgroup V g) hVg ⟨v, hstab⟩
    Nat.card ↥(fixV (Subgroup.zpowers φ) ⊓
      imgTil V₁g (conjSubgroup V g) hVg Dg) ≤ 4 ∨
      imgTil V₁g (conjSubgroup V g) hVg Dg ≤ fixV (Subgroup.zpowers φ) := by
  dsimp only
  intro hstab
  have hb := s168e3_block_involutionBound c hrow
  unfold A7FourBlockInvolutionBound at hb
  dsimp only at hb
  exact hb g X hX v hvM hv2 hvN hstab

theorem s168e3_block_comm_mem_v1Sub_of_hyperplane
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    {g : G} {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    {v : G} {K : Subgroup G}
    (hvM : v ∈ conjSubgroup D.M g) (hv2 : v * v = 1)
    (hvN : v ∈ normalizer
      (conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g : Set G))
    (hUK : conjSubgroup (v1Sub D.M V₀ V hV L) g ≤ K)
    (hKD : K ≤ conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g)
    (hmK : E3.mQuot (conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g) K = 1)
    (hfix : ∀ k ∈ K,
      v * k * v⁻¹ * k⁻¹ ∈ conjSubgroup (v1Sub D.M V₀ V hV L) g) :
    ∀ d ∈ conjSubgroup (X ⊔ v1Sub D.M V₀ V hV L) g,
      v * d * v⁻¹ * d⁻¹ ∈ conjSubgroup (v1Sub D.M V₀ V hV L) g := by
  classical
  intro d hdE
  obtain ⟨m, hm, rfl⟩ := hX
  have hdata := s168e3_a7Four_spaceData c hrow
  have h125 := c.setting.hyp151.hyp125
  let W := wSub V₀ V hV L
  let V₁ := v1Sub D.M V₀ V hV L
  let Vg : Subgroup G := conjSubgroup V g
  let hVg : IsElemAbelian 2 Vg := E3.isElemAbelian_conjSubgroup hV g
  let U : Subgroup G := conjSubgroup V₁ g
  let E : Subgroup G := conjSubgroup (conjSubgroup W m ⊔ V₁) g
  let hh : G := m * g
  have hWV : W ≤ V := preTil_le V₀ V hV _
  have hV₁V : V₁ ≤ V := s15_Infra_v1Sub_le h125 hV
  have hUeq : U = conjSubgroup V₁ hh := by
    dsimp [U, hh]
    rw [← conjSubgroup_conjSubgroup V₁ m g,
      s15_Infra_conjSubgroup_v1Sub h125 hV hm]
  have hVgeq : Vg = conjSubgroup V hh := by
    dsimp [Vg, hh]
    rw [← conjSubgroup_conjSubgroup V m g,
      conjSubgroup_eq_iff_mem_normalizer.mpr (h125.pairFacts.le_normalizer hm)]
  have hV₁m : V₁ = conjSubgroup V₁ m :=
    (s15_Infra_conjSubgroup_v1Sub h125 hV hm).symm
  have hEeq : E = conjSubgroup (W ⊔ V₁) hh := by
    dsimp only [E, hh]
    have hmap : conjSubgroup (W ⊔ V₁) m =
        conjSubgroup W m ⊔ conjSubgroup V₁ m := Subgroup.map_sup _ _ _
    calc conjSubgroup (conjSubgroup W m ⊔ V₁) g
        = conjSubgroup (conjSubgroup W m ⊔ conjSubgroup V₁ m) g := by
            nth_rewrite 1 [hV₁m]
            rfl
      _ = conjSubgroup (conjSubgroup (W ⊔ V₁) m) g := by rw [← hmap]
      _ = conjSubgroup (W ⊔ V₁) (m * g) := conjSubgroup_conjSubgroup _ _ _
  have hEU : E3.mQuot E U = gamma15 D.M V₀ V hV L := by
    rw [hEeq, hUeq]
    exact s15_FiveTen_mQuot_conj_v1Sub D h125 hV (L := L) hh
  have hE_V : E ≤ Vg := by
    rw [hEeq, hVgeq]
    exact E3.conjSubgroup_mono_left hh (sup_le hWV hV₁V)
  have hKU : K ≤ E := hKD
  have hvN0 : g * v * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hvM
  have hvV : v ∈ normalizer (Vg : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact mem_conjSubgroup_iff.2 (h125.pairFacts.le_normalizer hvN0)
  have hvV₁ : v ∈ normalizer (U : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact mem_conjSubgroup_iff.2 (s15_Infra_le_normalizer_v1Sub h125 hV hvN0)
  have hstab : v ∈ stabTil U Vg := Subgroup.mem_inf.2 ⟨hvV, hvV₁⟩
  have hb := hInv g (conjSubgroup W m) ⟨m, hm, rfl⟩ v
    (by simpa using hvM) hv2 (by simpa using hvN) hstab
  have hKK : K ≤ E := hKU
  have hmKU : E3.mQuot K U = 3 := by
    have hadd := E3.mQuot_add (V := E) (U := U) (U' := K) hUK hKD
    rw [hEU, hdata.gamma15_eq, hmK] at hadd
    omega
  have hrkK : rk ↥K = rk ↥U + 3 := by
    have h1 := E3.mQuot_add (V := K) (U := (⊥ : Subgroup G)) (U' := U) bot_le hUK
    rw [s15_FiveTen_mQuot_bot_eq_rk, s15_FiveTen_mQuot_bot_eq_rk, hmKU] at h1
    omega
  have hrkimg : rk ↥(imgTil U Vg hVg K) = 3 := by
    have hsub := s15_Infra_mSub_eq_rk_imgTil_add U Vg K hVg (hKD.trans hE_V)
    have hinf : K ⊓ U = U := inf_eq_right.mpr hUK
    dsimp only [mSub] at hsub
    rw [hinf] at hsub
    have h1 : rk ↥K = rk ↥(imgTil U Vg hVg K) + rk ↥U := hsub
    omega
  have hcardK8 : Nat.card ↥(imgTil U Vg hVg K) = 8 := by
    rw [card_eq_two_pow (fun q => s15_Infra_vtil_sq_eq_one U Vg hVg q)]
    rw [hrkimg]
    norm_num
  let φ : MulAut (Vtil U Vg hVg) := actTil U Vg hVg ⟨v, hstab⟩
  have hKfix : imgTil U Vg hVg K ≤ fixV (Subgroup.zpowers φ) := by
    intro q hq
    rw [mem_imgTil] at hq
    obtain ⟨x, hxK, rfl⟩ := hq
    rw [mem_fixV_zpowers_iff, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact hfix x.val hxK
  have hEimg : imgTil U Vg hVg K ≤ imgTil U Vg hVg E := by
    intro q hq
    rw [mem_imgTil] at hq ⊢
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨x, hKK hx, rfl⟩
  rcases hb with hle4 | htriv
  · have hle8 : 8 ≤ Nat.card ↥(fixV (Subgroup.zpowers φ) ⊓ imgTil U Vg hVg E) := by
      have hinj : Function.Injective
          (fun x : ↥(imgTil U Vg hVg K) =>
            (⟨x.1, le_inf hKfix hEimg x.2⟩ :
              ↥(fixV (Subgroup.zpowers φ) ⊓ imgTil U Vg hVg E))) := by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : ↥(fixV (Subgroup.zpowers φ) ⊓ imgTil U Vg hVg E) =>
            (z : Vtil U Vg hVg)) h
      have hle := Nat.card_le_card_of_injective _ hinj
      rwa [hcardK8] at hle
    have h84 : 8 ≤ 4 := le_trans hle8 hle4
    omega
  · have hdE' : mkTil U Vg hVg (IntMod.mk hVg ⟨d, hE_V hdE⟩) ∈
        imgTil U Vg hVg E :=
      (mem_imgTil U Vg hVg E (mkTil U Vg hVg (IntMod.mk hVg ⟨d, hE_V hdE⟩))).2
        ⟨IntMod.mk hVg ⟨d, hE_V hdE⟩, hdE, rfl⟩
    have hfixd := htriv hdE'
    rw [mem_fixV_zpowers_iff, actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfixd
    exact hfixd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
