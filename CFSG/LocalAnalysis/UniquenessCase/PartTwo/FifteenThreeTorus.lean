module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeL
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RTorus3_153 : Prop :=
  ∀ (S H : Type) [Group S] [Finite S] [Group H] [Finite H] (f : S →* H),
    Function.Injective f → f.range.Normal →
    (∀ x : H, (∀ y : S, x * f y = f y * x) → x = 1) →
    ((UC22.IsAlt S 6 ∨ UC22.IsAlt S 7 ∨ IsLn S 4 1) →
      (∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ 9) ∧
        ∀ A B : Subgroup H, IsElemAbelian 3 A → Nat.card A = 9 → IsElemAbelian 3 B →
          Nat.card B = 3 → ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A) ∧
    (IsOmegaMinus S 6 1 →
      (∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ 27) ∧
        ∀ A B : Subgroup H, IsElemAbelian 3 A → Nat.card A = 27 → IsElemAbelian 3 B →
          Nat.card B = 3 → ∃ h : H, B.map (MulAut.conj h).toMonoidHom ≤ A)

section Core

variable {D : Data G} {V₀ V L : Subgroup G}

private noncomputable def s15_Three_barHom (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil V₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M V₀ V hV
      exact actTil_mem_barSub V₀ V hV m.2 (hMs m.2))

private theorem s15_Three_barHom_surjective (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    Function.Surjective (s15_Three_barHom D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub V₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil V₀ V hV))
  rw [show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = actTil V₀ V hV g from
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem s15_Three_barHom_ker (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    (s15_Three_barHom D hV hMs).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))]
  constructor
  · intro hm
    refine ⟨m.2, hMs m.2, ?_⟩
    have h2 := congrArg Subtype.val hm
    change actTil V₀ V hV (Subgroup.inclusion hMs m) = 1 at h2
    rwa [show Subgroup.inclusion hMs m = (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) from
      Subtype.ext rfl] at h2
  · rintro ⟨-, hst, hact⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨(m : G), hMs m.2⟩ = 1
    rw [show (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) = ⟨(m : G), hst⟩ from Subtype.ext rfl]
    exact hact

private theorem s15_Three_normal_map_iff {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (L : Subgroup A) :
    (L.map f).Normal ↔ (L ⊔ f.ker).Normal := by
  rw [← Subgroup.normal_comap_iff_of_surjective hf, Subgroup.comap_map_eq]

private theorem s15_Three_MbarStar_centralizer (hAbs : RAbsIrr153) (D : Data G)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    ∀ x ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
      (∀ y ∈ lStar D.M V₀ V hV L, x * y = y * x) → x = 1 := by
  intro x hx hcomm
  have htop := s15_Three_wStar_eq_top D h1217 h hV hL hs
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV D.M x).1 hx
  have hstab : actTil (v1Sub D.M V₀ V hV L) V hV g ∈ stabSub (wStar D.M V₀ V hV L) := by
    intro u
    rw [htop]
    simp
  have hcomm1 : ∀ k ∈ lStar D.M V₀ V hV L,
      actTil (v1Sub D.M V₀ V hV L) V hV g * k =
        k * actTil (v1Sub D.M V₀ V hV L) V hV g := hcomm
  have hz := hAbs (vStar D.M V₀ V hV L) (s15_Infra_vtil_sq_eq_one _ V hV) ↥(lBar V₀ V hV L)
    (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) hperf _ hstab hcomm1
  ext z
  have hzW : z ∈ wStar D.M V₀ V hV L := by rw [htop]; trivial
  simpa using hz z hzW

private theorem s15_Three_starEquiv (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {X : Subgroup G} (hX : X ≤ D.M) :
    Nonempty (↥(barSub V₀ V hV X) ≃*
      ↥(barSub (v1Sub D.M V₀ V hV L) V hV X)) := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hMs0 : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  let f₀ : ↥X →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (hX.trans hMs0))
  let f₁ : ↥X →* MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV) :=
    (actTil (v1Sub D.M V₀ V hV L) V hV).comp
      (Subgroup.inclusion (hX.trans hMs1))
  have hrange₀ : f₀.range = barSub V₀ V hV X := by
    ext φ
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_barSub V₀ V hV X _).2
        ⟨Subgroup.inclusion (hX.trans hMs0) x, x.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgX, hg⟩ := (mem_barSub V₀ V hV X φ).1 hφ
      refine ⟨⟨(g : G), hgX⟩, ?_⟩
      change actTil V₀ V hV
        (Subgroup.inclusion (hX.trans hMs0) ⟨(g : G), hgX⟩) = φ
      rw [show Subgroup.inclusion (hX.trans hMs0) (⟨(g : G), hgX⟩ : ↥X) = g from
        Subtype.ext rfl, hg]
  have hrange₁ : f₁.range = barSub (v1Sub D.M V₀ V hV L) V hV X := by
    ext φ
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_barSub _ V hV X _).2
        ⟨Subgroup.inclusion (hX.trans hMs1) x, x.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgX, hg⟩ := (mem_barSub _ V hV X φ).1 hφ
      refine ⟨⟨(g : G), hgX⟩, ?_⟩
      change actTil (v1Sub D.M V₀ V hV L) V hV
        (Subgroup.inclusion (hX.trans hMs1) ⟨(g : G), hgX⟩) = φ
      rw [show Subgroup.inclusion (hX.trans hMs1) (⟨(g : G), hgX⟩ : ↥X) = g from
        Subtype.ext rfl, hg]
  have hker₀ : f₀.ker = (F11.CTilde D.M V₀ V).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hM]
    constructor
    · intro hx
      refine ⟨hX x.2, (hX.trans hMs0) x.2, ?_⟩
      change actTil V₀ V hV
        (Subgroup.inclusion (hX.trans hMs0) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs0) x =
        (⟨(x : G), (hX.trans hMs0) x.2⟩ : stabTil V₀ V) from Subtype.ext rfl]
      exact hx
    · rintro ⟨-, hst, h1⟩
      change actTil V₀ V hV (Subgroup.inclusion (hX.trans hMs0) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs0) x =
        (⟨(x : G), hst⟩ : stabTil V₀ V) from Subtype.ext rfl]
      exact h1
  have hker₁ : f₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hM]
    constructor
    · intro hx
      refine ⟨hX x.2, (hX.trans hMs1) x.2, ?_⟩
      change actTil (v1Sub D.M V₀ V hV L) V hV
        (Subgroup.inclusion (hX.trans hMs1) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs1) x =
        (⟨(x : G), (hX.trans hMs1) x.2⟩ :
          stabTil (v1Sub D.M V₀ V hV L) V) from Subtype.ext rfl]
      exact hx
    · rintro ⟨-, hst, h1⟩
      change actTil (v1Sub D.M V₀ V hV L) V hV
        (Subgroup.inclusion (hX.trans hMs1) x) = 1
      rw [show Subgroup.inclusion (hX.trans hMs1) x =
        (⟨(x : G), hst⟩ : stabTil (v1Sub D.M V₀ V hV L) V) from Subtype.ext rfl]
      exact h1
  have hker_eq : f₀.ker = f₁.ker := by
    rw [hker₀, hker₁, fifteen_two_cent D h1217 h hV]
  have e₀ : ↥X ⧸ f₀.ker ≃* ↥(barSub V₀ V hV X) :=
    (QuotientGroup.quotientKerEquivRange f₀).trans (MulEquiv.subgroupCongr hrange₀)
  have e₁ : ↥X ⧸ f₁.ker ≃*
      ↥(barSub (v1Sub D.M V₀ V hV L) V hV X) :=
    (QuotientGroup.quotientKerEquivRange f₁).trans (MulEquiv.subgroupCongr hrange₁)
  exact ⟨e₀.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans e₁)⟩

private theorem s15_Three_isAlt_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n : ℕ} (h : UC22.IsAlt X n) : UC22.IsAlt Y n :=
  h.elim fun f => ⟨e.symm.trans f⟩

private theorem s15_Three_isLn_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n a : ℕ} (h : IsLn X n a) : IsLn Y n a :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

private theorem s15_Three_isOmegaMinus_of_equiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsOmegaMinus X 6 1) : IsOmegaMinus Y 6 1 := by
  obtain ⟨h6, K, hK, hFin, b, c, hcard, hnc, ⟨f⟩⟩ := h
  exact ⟨h6, K, hK, hFin, b, c, hcard, hnc, ⟨e.symm.trans f⟩⟩

private theorem s15_Three_centralizes_v1 (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hV0 : V₀ = ⊥) : ∀ k ∈ L, ∀ x ∈ v1Sub D.M V₀ V hV L, k * x * k⁻¹ = x := by
  intro k hk x hx
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hxV : x ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hx
  have hkstab : k ∈ stabTil V₀ V := hMs (h.le hk)
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
    rw [mem_imgTil]
    exact ⟨IntMod.mk hV ⟨x, hxV⟩, hx, rfl⟩
  have hkbar : actTil V₀ V hV ⟨k, hkstab⟩ ∈
      barSub V₀ V hV (conjSubgroup L (1 : G)) := by
    rw [conjSubgroup_one]
    exact actTil_mem_barSub V₀ V hV hk hkstab
  have h1 := mem_fixV.mp (hfix hmem) (actTil V₀ V hV ⟨k, hkstab⟩) hkbar
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
  have hV0mem : ∀ e : G, e ∈ V₀ → e = 1 := by
    intro e he
    rw [hV0] at he
    exact Subgroup.mem_bot.mp he
  have h2 : k * x * k⁻¹ * x⁻¹ = 1 := hV0mem _ h1
  rw [mul_inv_eq_one] at h2
  exact h2

private theorem s15_Three_lift_torus (hT : RTable137) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (h1217 : R1217 D) (hN : CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian 3 E) {q : ℕ}
    (hEq : Nat.card E = 3 * q)
    (hbound : ∀ B : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
      IsElemAbelian 3 B → Nat.card B ≤ q)
    (hconj : ∀ A B : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
      IsElemAbelian 3 A → Nat.card A = q → IsElemAbelian 3 B → Nat.card B = 3 →
      ∃ h : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
        B.map (MulAut.conj h).toMonoidHom ≤ A)
    {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) :
    ∃ F : Subgroup G, F ≤ F11.CElt D.M V₀ v ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  let p1 : ↥D.M →* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := s15_Three_barHom D hV hMs1
  have hp1s : Function.Surjective p1 := s15_Three_barHom_surjective D hV hMs1
  have hp1k : p1.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M :=
    s15_Three_barHom_ker D hV hMs1
  set E' : Subgroup ↥D.M := E.subgroupOf D.M with hE'def
  have hE'el : IsElemAbelian 3 E' := by
    rw [hE'def]; exact IsElemAbelian.subgroupOf hE D.M
  have hE'card : Nat.card E' = 3 * q := by
    rw [hE'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEq]
  have hmapE : E'.map D.M.subtype = E := by
    rw [hE'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEM]
  have hmapker : p1.ker.map D.M.subtype =
      F11.CTilde D.M (v1Sub D.M V₀ V hV L) V := by
    rw [hp1k, Subgroup.subgroupOf_map_subtype, inf_eq_left]
    intro x hx
    exact ((mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).1 hx).1
  have hmapEN : (E' ⊓ p1.ker).map D.M.subtype =
      E ⊓ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V := by
    rw [Subgroup.map_inf _ _ _ D.M.subtype_injective, hmapE, hmapker]
  have hcardEN : Nat.card (E' ⊓ p1.ker : Subgroup ↥D.M) =
      Nat.card (E ⊓ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective D.M.subtype_injective, hmapEN]
  have hboundEN : Nat.card (E ⊓ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V : Subgroup G) ≤ 3 := by
    have hct := fifteen_two_cent D h1217 h hV
    have hN1 : CFSG.Open.pRank 3 (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) ≤ 1 := by
      rw [hct]; exact hN
    have hEel : IsElemAbelian 3 (E ⊓ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) :=
      hE.mono inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEel.isPGroup
    have hk1 : k ≤ CFSG.Open.pRank 3 (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) inf_le_right hEel hk
    calc Nat.card (E ⊓ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V : Subgroup G) = 3 ^ k := hk
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (le_trans hk1 hN1)
      _ = 3 := by norm_num
  have hEN' : Nat.card (E' ⊓ p1.ker : Subgroup ↥D.M) ≤ 3 := by
    rw [hcardEN]; exact hboundEN
  have hV2 : ∀ w : vStar D.M V₀ V hV L, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have htop := s15_Three_wStar_eq_top D h1217 h hV hL hs
  set z : vStar D.M V₀ V hV L :=
    mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩) with hz
  have hzW : z ∈ wStar D.M V₀ V hV L := by rw [htop]; trivial
  have hrank : 1 ≤ CFSG.Open.pRank 3 (lStar D.M V₀ V hV L ⊓
      MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z) :=
    (hT (vStar D.M V₀ V hV L) hV2 (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)
      ↥(lBar V₀ V hV L) hperf).1 z hzW
  obtain ⟨Y, hYle, hYel, hYcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
      (H := lStar D.M V₀ V hV L ⊓ MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z)
      (k := 1) hrank
  have hY3 : Nat.card Y = 3 := by rw [hYcard]; norm_num
  have hYleM : Y ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    (hYle.trans inf_le_left).trans (barSub_mono (v1Sub D.M V₀ V hV L) V hV h.le)
  set Y' : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    Y.subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) with hY'def
  have hY'el : IsElemAbelian 3 Y' := by
    rw [hY'def]; exact hYel.subgroupOf _
  have hY'3 : Nat.card Y' = 3 := by
    rw [hY'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleM).toEquiv, hY3]
  obtain ⟨F, m, hFel, hFcard, hFY, -⟩ :=
    s15_Three_lift_nine p1 hp1s hE'el hE'card hEN' hbound hconj hY'el hY'3
  refine ⟨F.map D.M.subtype, ?_, IsElemAbelian.map hFel D.M.subtype, ?_⟩
  · rintro x ⟨f, hfF, rfl⟩
    have hfY' : p1 f ∈ Y' := hFY hfF
    have hfY : (p1 f).1 ∈ Y := hfY'
    have hfstar : (p1 f).1 ∈ lStar D.M V₀ V hV L := (hYle hfY).1
    have hfstab : (p1 f).1 ∈
        MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z := (hYle hfY).2
    have hfixz : (p1 f).1 z = z := MulAction.mem_stabilizer_iff.1 hfstab
    have hxv : f.1 * v * f.1⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L := by
      have h1 : actTil (v1Sub D.M V₀ V hV L) V hV ⟨f.1, hMs1 f.2⟩ z = z := hfixz
      rw [hz, actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
      convert h1 using 2 <;> rfl
    have hf3 : f.1 ^ 3 = 1 := by
      have := hFel.2 f hfF
      simpa using congrArg Subtype.val this
    by_cases hV0 : V₀ = ⊥
    ·
      have hcent : ∀ w ∈ v1Sub D.M V₀ V hV L, f.1 * w * f.1⁻¹ = w := by
        obtain ⟨l, hlL, hlx⟩ :=
          (mem_barSub (v1Sub D.M V₀ V hV L) V hV L _).1 hfstar
        have hp1eq : p1 ⟨l.1, h.le hlL⟩ = p1 f := by
          apply Subtype.ext
          change actTil (v1Sub D.M V₀ V hV L) V hV ⟨l.1, hMs1 (h.le hlL)⟩ = (p1 f).1
          exact (congrArg (actTil (v1Sub D.M V₀ V hV L) V hV) (Subtype.ext rfl)).trans hlx
        have hxl_ker : f * ⟨l.1, h.le hlL⟩⁻¹ ∈ p1.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hp1eq, mul_inv_cancel]
        have hct0 : f.1 * l.1⁻¹ ∈ F11.CTilde D.M V₀ V := by
          have hh := hxl_ker
          rw [hp1k] at hh
          rw [fifteen_two_cent D h1217 h hV] at hh
          exact hh
        have hcentralW : ∀ w ∈ V, (f.1 * l.1⁻¹) * w * (f.1 * l.1⁻¹)⁻¹ = w := by
          obtain ⟨-, hst, hact⟩ :=
            (mem_cTilde_iff hV h.hyp125.pairFacts.le_normalizer).1 hct0
          intro w hw
          have h1 := (actTil_eq_one_iff V₀ V hV ⟨f.1 * l.1⁻¹, hst⟩).1 hact w hw
          have hV0mem : ∀ e : G, e ∈ V₀ → e = 1 := by
            intro e he
            rw [hV0] at he
            exact Subgroup.mem_bot.mp he
          have h3 : (f.1 * l.1⁻¹) * w * (f.1 * l.1⁻¹)⁻¹ * w⁻¹ = 1 := hV0mem _ h1
          rwa [mul_inv_eq_one] at h3
        have hlcent : ∀ w ∈ v1Sub D.M V₀ V hV L, l.1 * w * l.1⁻¹ = w :=
          s15_Three_centralizes_v1 h hV hV0 l.1 hlL
        intro w hw
        have hwV : w ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hw
        have h1 := hcentralW w hwV
        have h2 := hlcent w hw
        calc f.1 * w * f.1⁻¹ = ((f.1 * l.1⁻¹) * l.1) * w * ((f.1 * l.1⁻¹) * l.1)⁻¹ := by
              group
          _ = (f.1 * l.1⁻¹) * (l.1 * w * l.1⁻¹) * (f.1 * l.1⁻¹)⁻¹ := by group
          _ = (f.1 * l.1⁻¹) * w * (f.1 * l.1⁻¹)⁻¹ := by rw [h2]
          _ = w := h1
      have hfixv := s15_Three_cocycle_fixes hV (s15_Infra_v1Sub_le h.hyp125 hV) hcent
        ⟨1, hf3⟩ hxv
      refine ⟨f.2, ?_, ?_⟩
      · rw [hV0]
        rw [Subgroup.mem_normalizer_iff]
        intro a
        rw [Subgroup.mem_bot, Subgroup.mem_bot, mul_inv_eq_one]
        constructor
        · intro ha; rw [ha, mul_one]
        · intro ha
          exact mul_left_cancel (show D.M.subtype f * a = D.M.subtype f * 1 by rw [ha, mul_one])
      · rw [hV0, Subgroup.mem_bot, mul_inv_eq_one]
        exact hfixv
    · refine ⟨f.2, ?_, ?_⟩
      · exact h.hyp125.pairFacts.le_normalizer₀ f.2
      · rw [v1Sub_of_ne_bot D.M V₀ V hV L hV0] at hxv
        exact hxv
  · rw [Subgroup.card_map_of_injective D.M.subtype_injective, hFcard]

theorem s15_Three_O1a_of_torus (hT : RTable137) (hAbs : RAbsIrr153) (hTor : RTorus3_153)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hN : CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : ((UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
        IsLn ↥(lBar V₀ V hV L) 4 1) ∧ Nat.card E = 27) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧ Nat.card E = 81))
    {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) :
    ∃ F : Subgroup G, F ≤ F11.CElt D.M V₀ v ∧ CFSG.Open.IsElemAbelian 3 F ∧
      Nat.card F = 9 := by
  classical
  have hMs0 : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  let p0 : ↥D.M →* ↥(Mbar D.M V₀ V hV) := s15_Three_barHom D hV hMs0
  let p1 : ↥D.M →* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := s15_Three_barHom D hV hMs1
  have hp0s : Function.Surjective p0 := s15_Three_barHom_surjective D hV hMs0
  have hp1s : Function.Surjective p1 := s15_Three_barHom_surjective D hV hMs1
  have hp0k : p0.ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := s15_Three_barHom_ker D hV hMs0
  have hp1k : p1.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M :=
    s15_Three_barHom_ker D hV hMs1
  have hker_eq : p0.ker = p1.ker := by
    rw [hp0k, hp1k, fifteen_two_cent D h1217 h hV]
  let L1 : Subgroup ↥D.M := L.subgroupOf D.M
  have hnormBar : ((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono V₀ V hV h.le)).2
      (s15_Three_le_normalizer hs)
  have hmap0 : L1.map p0 = (barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      show (p0 m : MulAut (Vtil V₀ V hV)) ∈ barSub V₀ V hV L
      rw [show (p0 m : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨(m : G), hMs0 m.2⟩ from rfl]
      exact actTil_mem_barSub V₀ V hV hm (hMs0 m.2)
    · intro hx
      obtain ⟨g, hgL, hgx⟩ := (mem_barSub V₀ V hV L x.1).1 hx
      refine ⟨⟨g.1, h.le hgL⟩, ?_, ?_⟩
      · change g.1 ∈ L
        exact hgL
      · apply Subtype.ext
        show (p0 ⟨g.1, h.le hgL⟩ : MulAut (Vtil V₀ V hV)) = x.1
        rw [show (p0 ⟨g.1, h.le hgL⟩ : MulAut (Vtil V₀ V hV)) =
          actTil V₀ V hV ⟨g.1, hMs0 (h.le hgL)⟩ from rfl,
          show (⟨g.1, hMs0 (h.le hgL)⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl]
        exact hgx
  have hmap1 : L1.map p1 = (barSub (v1Sub D.M V₀ V hV L) V hV L).subgroupOf
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      show (p1 m : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) ∈
        barSub (v1Sub D.M V₀ V hV L) V hV L
      rw [show (p1 m : MulAut _) =
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨(m : G), hMs1 m.2⟩ from rfl]
      exact actTil_mem_barSub _ V hV hm (hMs1 m.2)
    · intro hx
      obtain ⟨g, hgL, hgx⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L x.1).1 hx
      refine ⟨⟨g.1, h.le hgL⟩, ?_, ?_⟩
      · change g.1 ∈ L
        exact hgL
      · apply Subtype.ext
        show (p1 ⟨g.1, h.le hgL⟩ : MulAut _) = x.1
        rw [show (p1 ⟨g.1, h.le hgL⟩ : MulAut _) =
          actTil (v1Sub D.M V₀ V hV L) V hV ⟨g.1, hMs1 (h.le hgL)⟩ from rfl,
          show (⟨g.1, hMs1 (h.le hgL)⟩ : ↥(stabTil (v1Sub D.M V₀ V hV L) V)) = g from
            Subtype.ext rfl]
        exact hgx
  have hnormStar : ((barSub (v1Sub D.M V₀ V hV L) V hV L).subgroupOf
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)).Normal := by
    have hLbarNormal : (L1.map p0).Normal := by rw [hmap0]; exact hnormBar
    have hpre0 : (L1 ⊔ p0.ker).Normal := (s15_Three_normal_map_iff p0 hp0s L1).1 hLbarNormal
    have hpre1 : (L1 ⊔ p1.ker).Normal := by rwa [hker_eq] at hpre0
    have hstarNormal : (L1.map p1).Normal := (s15_Three_normal_map_iff p1 hp1s L1).2 hpre1
    rw [← hmap1]; exact hstarNormal
  have hle : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono (v1Sub D.M V₀ V hV L) V hV h.le
  have hinj : Function.Injective (Subgroup.inclusion hle) := Subgroup.inclusion_injective hle
  have hnorm : (Subgroup.inclusion hle).range.Normal := by
    rw [Subgroup.inclusion_range]
    simpa only [lStar] using hnormStar
  have hcent : ∀ x : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV),
      (∀ y : ↥(lStar D.M V₀ V hV L),
        x * Subgroup.inclusion hle y = Subgroup.inclusion hle y * x) → x = 1 := by
    intro x hx
    refine Subtype.ext (s15_Three_MbarStar_centralizer hAbs D h1217 h hV hL hs hperf
      x.1 x.2 ?_)
    intro y hy
    have h1 := hx ⟨y, hy⟩
    simpa using congrArg Subtype.val h1
  have hTorData := hTor ↥(lStar D.M V₀ V hV L)
    ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (Subgroup.inclusion hle) hinj hnorm hcent
  obtain ⟨e⟩ := s15_Three_starEquiv D h1217 h hV (X := L) h.le
  let e' : ↥(lBar V₀ V hV L) ≃* ↥(lStar D.M V₀ V hV L) := e
  rcases hcard with ⟨hA, hEcard⟩ | ⟨hΩ, hEcard⟩
  · have hA'' : UC22.IsAlt ↥(lStar D.M V₀ V hV L) 6 ∨
        UC22.IsAlt ↥(lStar D.M V₀ V hV L) 7 ∨ IsLn ↥(lStar D.M V₀ V hV L) 4 1 := by
      rcases hA with h | h | h
      · exact Or.inl (s15_Three_isAlt_of_equiv e' h)
      · exact Or.inr (Or.inl (s15_Three_isAlt_of_equiv e' h))
      · exact Or.inr (Or.inr (s15_Three_isLn_of_equiv e' h))
    obtain ⟨hbound, hconj⟩ := hTorData.1 hA''
    exact s15_Three_lift_torus hT h hV hL hs hperf h1217 hN hEM hE
      (by rw [hEcard]) hbound hconj hv hv0
  · have hΩ' : IsOmegaMinus ↥(lStar D.M V₀ V hV L) 6 1 :=
      s15_Three_isOmegaMinus_of_equiv e' hΩ
    obtain ⟨hbound, hconj⟩ := hTorData.2 hΩ'
    exact s15_Three_lift_torus hT h hV hL hs hperf h1217 hN hEM hE
      (by rw [hEcard]) hbound hconj hv hv0

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
