module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.A1cModuleHomog
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement Pointwise

section Transport

variable {W : Type} [CommGroup W]

theorem n2_modFix_eq (Mp : Subgroup (MulAut W)) (VT : Subgroup W) :
    modFix Mp VT = VT ⊓ fixV Mp := by
  ext w
  simp only [XMod.mem_fixed, Subgroup.mem_inf, mem_fixV, Subtype.forall]
  rfl

private theorem n2_le_stabSub {Y : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ g ∈ Y, ∀ u ∈ U, g u ∈ U) : Y ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, h g hg u⟩
  have := h g⁻¹ (Y.inv_mem hg) _ hu
  simpa using this

@[expose] noncomputable def n2Iota (Mp : Subgroup (MulAut W)) (VT : Subgroup W) :
    Sec VT (VT ⊓ fixV Mp) →* W ⧸ modFix Mp VT :=
  QuotientGroup.map ((VT ⊓ fixV Mp).subgroupOf VT) (modFix Mp VT) VT.subtype
    (fun x hx => by
      rw [Subgroup.mem_comap, n2_modFix_eq]
      exact hx)

theorem n2Iota_mk (Mp : Subgroup (MulAut W)) (VT : Subgroup W) (x : ↥VT) :
    n2Iota Mp VT (QuotientGroup.mk x) = QuotientGroup.mk (x : W) := rfl

theorem n2Iota_injective (Mp : Subgroup (MulAut W)) (VT : Subgroup W) :
    Function.Injective (n2Iota Mp VT) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [n2Iota_mk, QuotientGroup.eq_one_iff, n2_modFix_eq] at hy
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy

theorem n2_map_iota_sec35Img (Mp : Subgroup (MulAut W)) {VT I : Subgroup W} (hI : I ≤ VT) :
    (sec35Img VT (VT ⊓ fixV Mp) I).map (n2Iota Mp VT) = tilde Mp VT I := by
  ext q
  unfold sec35Img
  rw [Subgroup.map_map, mem_tilde_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hI hv⟩, hv, rfl⟩

theorem n2_sec35Img_self (VT C : Subgroup W) : sec35Img VT C VT = ⊤ := by
  unfold sec35Img
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem n2_map_iota_top (Mp : Subgroup (MulAut W)) (VT : Subgroup W) :
    (⊤ : Subgroup (Sec VT (VT ⊓ fixV Mp))).map (n2Iota Mp VT) = tilde Mp VT VT := by
  rw [← n2_sec35Img_self VT (VT ⊓ fixV Mp), n2_map_iota_sec35Img Mp le_rfl]

variable {VT C : Subgroup W}

@[expose] noncomputable def n2Rho (VT C : Subgroup W) :
    ↥(stabSub VT ⊓ stabSub C) →* MulAut (Sec VT C) :=
  (quotHom (C.subgroupOf VT)).comp
    (((resHom VT).comp (Subgroup.inclusion inf_le_left)).codRestrict (stabSub (C.subgroupOf VT))
      (fun g => autSub_le_stabSub_subgroupOf (inf_le_right : stabSub VT ⊓ stabSub C ≤ stabSub C)
        (mem_autSub.2 ⟨⟨g, inf_le_left (a := stabSub VT) g.2⟩, g.2, rfl⟩)))

theorem n2Rho_mk (g : ↥(stabSub VT ⊓ stabSub C)) (w : ↥VT) :
    n2Rho VT C g (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨(g : MulAut W) (w : W), (inf_le_left (a := stabSub VT) g.2 w).2 w.2⟩ :=
  rfl

theorem n2_mem_autSec {Y : Subgroup (MulAut W)} (hY : Y ≤ stabSub VT ⊓ stabSub C)
    {φ : MulAut (Sec VT C)} :
    φ ∈ autSec Y VT C ↔ ∃ g : ↥(stabSub VT ⊓ stabSub C), (g : MulAut W) ∈ Y ∧ n2Rho VT C g = φ := by
  unfold autSec
  rw [mem_autQuot]
  constructor
  · rintro ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₀, hg₀Y, hg₀⟩ := mem_autSub.1 hg₁
    refine ⟨⟨g₀, hY hg₀Y⟩, hg₀Y, ?_⟩
    have e : (⟨resHom VT ⟨(g₀ : MulAut W), g₀.2⟩, (by rw [hg₀]; exact g₁.2)⟩ :
        stabSub (C.subgroupOf VT)) = g₁ := Subtype.ext hg₀
    rw [← e]
    rfl
  · rintro ⟨g, hgY, rfl⟩
    exact ⟨_, mem_autSub.2 ⟨⟨g, inf_le_left (a := stabSub VT) g.2⟩, hgY, rfl⟩, rfl⟩

theorem n2_map_rho_sec35Img (g : ↥(stabSub VT ⊓ stabSub C)) (I : Subgroup W) :
    (sec35Img VT C I).map (n2Rho VT C g).toMonoidHom =
      sec35Img VT C (I.map (g : MulAut W).toMonoidHom) := by
  have hgVT : (g : MulAut W) ∈ stabSub VT := inf_le_left (a := stabSub VT) g.2
  ext x
  unfold sec35Img
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨⟨(g : MulAut W) (w : W), (hgVT w).2 w.2⟩, ⟨(w : W), hw, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨v, hv, hvy⟩, rfl⟩
    have hvVT : v ∈ VT := (hgVT v).1 (by rw [MulEquiv.coe_toMonoidHom] at hvy; rw [hvy]; exact y.2)
    refine ⟨QuotientGroup.mk ⟨v, hvVT⟩, ⟨⟨v, hvVT⟩, hv, rfl⟩, ?_⟩
    change n2Rho VT C g (QuotientGroup.mk ⟨v, hvVT⟩) = QuotientGroup.mk y
    rw [n2Rho_mk]
    congr 1
    exact Subtype.ext hvy

end Transport

section General

private theorem n2_sSupIndep_of_map {G N : Type*} [Group G] [Group N] {f : G →* N}
    (hf : Function.Injective f) {S : Set (Subgroup G)} (h : sSupIndep (Subgroup.map f '' S)) :
    sSupIndep S := by
  intro a ha
  have h1 := h (Set.mem_image_of_mem _ ha)
  have h2 : (sSup (S \ {a})).map f ≤ sSup (Subgroup.map f '' S \ {a.map f}) := by
    rw [(Subgroup.gc_map_comap f).l_sSup]
    refine iSup₂_le fun b hb => le_sSup ⟨⟨b, hb.1, rfl⟩, fun hba => hb.2 ?_⟩
    exact Subgroup.map_injective hf hba
  have h3 : Disjoint (a.map f) ((sSup (S \ {a})).map f) := h1.mono_right h2
  rw [disjoint_iff] at h3 ⊢
  rw [← Subgroup.map_inf _ _ f hf] at h3
  exact Subgroup.map_injective hf (h3.trans (Subgroup.map_bot f).symm)

variable {A Q : Type*} [Group A] [CommGroup Q] [MulDistribMulAction A Q]

private theorem n2_iso_map {A₂ Q₂ : Type*} [Group A₂] [CommGroup Q₂] [MulDistribMulAction A₂ Q₂]
    {θ : Q →* Q₂} (hθ : Function.Injective θ) (hact : ∀ a₂ : A₂, ∃ a₁ : A, ∀ x, θ (a₁ • x) = a₂ • θ x)
    {L₁ L₂ : Subgroup Q} (h : XMod.Iso A L₁ L₂) : XMod.Iso A₂ (L₁.map θ) (L₂.map θ) := by
  obtain ⟨φ, hφ⟩ := h
  let e₁ := Subgroup.equivMapOfInjective L₁ θ hθ
  let e₂ := Subgroup.equivMapOfInjective L₂ θ hθ
  refine ⟨e₁.symm.trans (φ.trans e₂), fun a l l' hll' => ?_⟩
  have hx : θ ((e₁.symm l : ↥L₁) : Q) = (l : Q₂) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply L₁ θ hθ, MulEquiv.apply_symm_apply]
  have hx' : θ ((e₁.symm l' : ↥L₁) : Q) = (l' : Q₂) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply L₁ θ hθ, MulEquiv.apply_symm_apply]
  obtain ⟨a₁, ha₁⟩ := hact a
  have h1 : a₁ • ((e₁.symm l : ↥L₁) : Q) = ((e₁.symm l' : ↥L₁) : Q) := by
    apply hθ
    rw [ha₁, hx, hx', hll']
  have h2 := hφ a₁ (e₁.symm l) (e₁.symm l') h1
  show a • ((e₂ (φ (e₁.symm l)) : ↥(L₂.map θ)) : Q₂) = ((e₂ (φ (e₁.symm l')) : ↥(L₂.map θ)) : Q₂)
  rw [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply, ← ha₁, h2]

private theorem n2_fixed_eq_bot_of_irr {L : Subgroup Q} (hL : XMod.IsIrr A L)
    (hc : XMod.commOf A L = L) : XMod.fixed A L = ⊥ := by
  rcases hL.2.2 (XMod.fixed A L) (XMod.isInv_fixed L) bot_le (XMod.fixed_le L) with h | h
  · exact h
  · exfalso
    have hfix : L ≤ XMod.fixed A ⊤ := by
      intro l hl
      have hl' : l ∈ XMod.fixed A L := by rw [h]; exact hl
      exact ⟨trivial, hl'.2⟩
    have h2 : XMod.commOf A L = ⊥ := XMod.commOf_eq_bot_iff.2 hfix
    exact hL.2.1.ne (h2.symm.trans hc)

private theorem n2_fixed_smul_eq_bot {Tg : Type*} [Group Tg] [MulDistribMulAction Tg Q]
    (h : XMod.Normalizes A Tg Q) (t : Tg) {L : Subgroup Q} (hL : XMod.fixed A L = ⊥) :
    XMod.fixed A (t • L) = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨hq, hfix⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
  have h1 : t⁻¹ • q ∈ XMod.fixed A L := by
    refine ⟨hq, fun a => ?_⟩
    obtain ⟨a', ha'⟩ := h t a
    have e := ha' (t⁻¹ • q)
    rw [smul_inv_smul, hfix a'] at e
    calc a • t⁻¹ • q = t⁻¹ • t • a • t⁻¹ • q := (inv_smul_smul t _).symm
      _ = t⁻¹ • q := by rw [e]
  rw [hL, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc q = t • t⁻¹ • q := (smul_inv_smul t q).symm
    _ = 1 := by rw [h1, smul_one]

private theorem n2_fixed_sSup_eq_bot {S : Set (Subgroup Q)} (hfin : S.Finite) (hS : sSupIndep S)
    (hinv : ∀ s ∈ S, XMod.IsInv A s) (hfix : ∀ s ∈ S, XMod.fixed A s = ⊥) :
    XMod.fixed A (sSup S) = ⊥ := by
  suffices key : ∀ s : Set (Subgroup Q), s.Finite → s ⊆ S → XMod.fixed A (sSup s) = ⊥ from
    key S hfin le_rfl
  intro s hs
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _
    rw [sSup_empty, eq_bot_iff]
    exact XMod.fixed_le ⊥
  | @insert a s ha hs ih =>
    intro hsS
    have haS : a ∈ S := hsS (Set.mem_insert a s)
    have hsS' : s ⊆ S := (Set.subset_insert a s).trans hsS
    have hdis : Disjoint a (sSup s) := hS.disjoint_sSup haS hsS' ha
    have ih' := ih hsS'
    have hinvs : XMod.IsInv A (sSup s) := by
      rw [sSup_eq_iSup]
      exact XMod.isInv_iSup fun b => XMod.isInv_iSup fun hb => hinv b (hsS' hb)
    rw [sSup_insert, eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hy1
    have key : ∀ g : A, g • u = u ∧ g • v = v := by
      intro g
      have e := hy2 g
      rw [smul_mul'] at e
      have hmem : (g • u) * u⁻¹ ∈ a ⊓ sSup s := by
        refine ⟨a.mul_mem (hinv a haS g u hu) (a.inv_mem hu), ?_⟩
        have e2 : (g • u) * u⁻¹ = v * (g • v)⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul, eq_mul_inv_of_mul_eq e, mul_assoc, mul_comm u]
        rw [e2]
        exact (sSup s).mul_mem hv ((sSup s).inv_mem (hinvs g v hv))
      rw [hdis.eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact mul_left_cancel e
    have hu1 : u ∈ XMod.fixed A a := ⟨hu, fun g => (key g).1⟩
    have hv1 : v ∈ XMod.fixed A (sSup s) := ⟨hv, fun g => (key g).2⟩
    rw [hfix a haS, Subgroup.mem_bot] at hu1
    rw [ih', Subgroup.mem_bot] at hv1
    rw [hu1, hv1, mul_one]
    exact Subgroup.one_mem _

omit [CommGroup Q] [MulDistribMulAction A Q] in
private theorem n2_comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) (a b : G) :
    a * b = b * a := by
  have hinv : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_left (by rw [← sq, h])
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv a, hinv b]

end General

section Std

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem n2_hTX (hD : D3Std M Mp T L V) : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hD.hyp.Mp_eq]
  exact le_normalizer_conjClosure L T

omit [Finite W] in
private theorem n2_hW (T : Subgroup (MulAut W)) (V : Subgroup W) :
    ∀ t ∈ T, ∀ w ∈ orbSup T V, t • w ∈ orbSup T V := fun _ ht _ hw => mem_orbSup_of_mem_map ht hw

private theorem n2_hVinv (hD : D3Std M Mp T L V) : IsModInv Mp V := hD.irrT.1.2.1

private theorem n2_invVT (hD : D3Std M Mp T L V) :
    ∀ g ∈ Mp, ∀ w ∈ orbSup T V, g w ∈ orbSup T V := by
  have h : IsModInv Mp (⨆ y ∈ T, y • V) :=
    XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy => isModInv_smul (n2_hTX hD hy) (n2_hVinv hD)
  intro g hg w hw
  exact h ⟨g, hg⟩ w hw

theorem n2_Mp_le (hD : D3Std M Mp T L V) :
    Mp ≤ stabSub (orbSup T V) ⊓ stabSub (orbSup T V ⊓ fixV Mp) := by
  refine le_inf (n2_le_stabSub (n2_invVT hD)) (n2_le_stabSub fun g hg w hw => ?_)
  rw [hw.2 g hg]
  exact hw

theorem n2_T_le (hD : D3Std M Mp T L V) :
    T ≤ stabSub (orbSup T V) ⊓ stabSub (orbSup T V ⊓ fixV Mp) := by
  refine le_inf (le_stabSub_orbSup T V) (n2_le_stabSub fun t ht w hw =>
    ⟨mem_orbSup_of_mem_map ht hw.1, fun x hx => ?_⟩)
  have h1 : (t⁻¹ * x * t) w = w := hw.2 _ (inv_conj_mem_of_mem_normalizer (n2_hTX hD ht) hx)
  calc x (t w) = t ((t⁻¹ * x * t) w) := by simp [MulAut.mul_apply]
    _ = t w := by rw [h1]

omit [Finite W] in
theorem n2_iota_rho (Mp : Subgroup (MulAut W)) (VT : Subgroup W)
    (g : ↥(stabSub VT ⊓ stabSub (VT ⊓ fixV Mp))) (hg : (g : MulAut W) ∈ Mp)
    (x : Sec VT (VT ⊓ fixV Mp)) :
    n2Iota Mp VT (n2Rho VT (VT ⊓ fixV Mp) g x) = (⟨g, hg⟩ : ↥Mp) • n2Iota Mp VT x := by
  induction x using QuotientGroup.induction_on with
  | H w => rfl

private theorem n2_bwd (hD : D3Std M Mp T L V) (a : ↥Mp) :
    ∃ a₁ : ↥(autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp)),
      ∀ x, n2Iota Mp (orbSup T V) (a₁ • x) = a • n2Iota Mp (orbSup T V) x :=
  ⟨⟨n2Rho _ _ ⟨a, n2_Mp_le hD a.2⟩, (n2_mem_autSec (n2_Mp_le hD)).2 ⟨_, a.2, rfl⟩⟩,
    fun x => n2_iota_rho Mp (orbSup T V) ⟨a, n2_Mp_le hD a.2⟩ a.2 x⟩

omit [Finite W] in
private theorem n2_map_iota_conj
    (g : ↥(stabSub (orbSup T V) ⊓ stabSub (orbSup T V ⊓ fixV Mp))) (hg : (g : MulAut W) ∈ T) :
    ((sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map
        (n2Rho (orbSup T V) (orbSup T V ⊓ fixV Mp) g).toMonoidHom).map (n2Iota Mp (orbSup T V)) =
      tilde Mp (orbSup T V) ((g : MulAut W) • V) := by
  rw [n2_map_rho_sec35Img, n2_map_iota_sec35Img Mp (map_le_orbSup hg)]
  rfl

private theorem n2_image_family (hD : D3Std M Mp T L V) :
    Subgroup.map (n2Iota Mp (orbSup T V)) ''
        {S : Subgroup (Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)) |
          ∃ t ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
            S = (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map t.toMonoidHom} =
      {c | ∃ t ∈ T, c = tilde Mp (orbSup T V) (t • V)} := by
  ext c
  constructor
  · rintro ⟨S, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨g, hgT, rfl⟩ := (n2_mem_autSec (n2_T_le hD)).1 ht
    exact ⟨g, hgT, n2_map_iota_conj g hgT⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨_, (n2_mem_autSec (n2_T_le hD)).2 ⟨⟨t, n2_T_le hD ht⟩, ht, rfl⟩, rfl⟩,
      n2_map_iota_conj ⟨t, n2_T_le hD ht⟩ ht⟩

private theorem n2_fixed_tilde_eq_bot (hD : D3Std M Mp T L V) :
    XMod.fixed ↥Mp (tilde Mp (orbSup T V) (orbSup T V)) = ⊥ := by
  have hTX := n2_hTX hD
  have hW := n2_hW T V
  obtain ⟨hind, hsup⟩ := sSupIndep_tilde_smul_of_mem_irrPlusOn hTX hW hD.irrT
  have e : tilde Mp (orbSup T V) (orbSup T V) = tilde Mp (orbSup T V) (⨆ y ∈ T, y • V) := rfl
  rw [e, ← hsup]
  have : Finite (Subgroup (W ⧸ modFix Mp (orbSup T V))) :=
    Finite.of_injective (SetLike.coe : Subgroup (W ⧸ modFix Mp (orbSup T V)) → Set _)
      SetLike.coe_injective
  apply n2_fixed_sSup_eq_bot (Set.toFinite _) hind
  · rintro _ ⟨t, ht, rfl⟩
    exact isInv_tilde (isModInv_smul (hTX ht) (n2_hVinv hD))
  · rintro _ ⟨t, ht, rfl⟩
    let := quotAct hTX hW
    rw [← tilde_smul hTX hW ⟨t, ht⟩ V]
    obtain ⟨hirr, hc⟩ := isIrr_tilde hD.irrT.1
    exact n2_fixed_smul_eq_bot (normalizes_quot hTX hW) _ (n2_fixed_eq_bot_of_irr hirr hc)

end Std

section Fields

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem z35m_irr (hD : D3Std M Mp T L V) :
    XMod.IsIrr ↥(autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp))
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) := by
  have hι := n2Iota_injective Mp (orbSup T V)
  have himg := n2_map_iota_sec35Img Mp (le_orbSup T V)
  obtain ⟨⟨hinvt, hbot, hirrt⟩, -⟩ := isIrr_tilde hD.irrT.1
  have hmem : ∀ x, x ∈ sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V ↔
      n2Iota Mp (orbSup T V) x ∈ tilde Mp (orbSup T V) V := by
    intro x
    rw [← himg, Subgroup.mem_map_iff_mem hι]
  refine ⟨fun a x hx => ?_, ?_, fun J hJ _ hJV => ?_⟩
  · obtain ⟨g, hgMp, hga⟩ := (n2_mem_autSec (n2_Mp_le hD)).1 a.2
    rw [hmem] at hx ⊢
    change n2Iota Mp (orbSup T V) ((a : MulAut _) x) ∈ _
    rw [← hga, n2_iota_rho Mp (orbSup T V) g hgMp x]
    exact hinvt _ _ hx
  · rw [← Subgroup.map_lt_map_iff_of_injective hι, Subgroup.map_bot, himg]
    exact hbot
  · have hJinv : XMod.IsInv ↥Mp (J.map (n2Iota Mp (orbSup T V))) := by
      rintro a _ ⟨j, hj, rfl⟩
      obtain ⟨a₁, ha₁⟩ := n2_bwd hD a
      rw [← ha₁ j]
      exact Subgroup.mem_map_of_mem _ (hJ a₁ j hj)
    have hJle : J.map (n2Iota Mp (orbSup T V)) ≤ tilde Mp (orbSup T V) V :=
      himg ▸ Subgroup.map_mono hJV
    rcases hirrt _ hJinv bot_le hJle with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ hι).1 h
    · right
      exact Subgroup.map_injective hι (h.trans himg.symm)

theorem z35m_indep (hD : D3Std M Mp T L V) :
    sSupIndep {S : Subgroup (Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)) |
      ∃ t ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
        S = (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map t.toMonoidHom} := by
  apply n2_sSupIndep_of_map (n2Iota_injective Mp (orbSup T V))
  rw [n2_image_family hD]
  exact (sSupIndep_tilde_smul_of_mem_irrPlusOn (n2_hTX hD) (n2_hW T V) hD.irrT).1

theorem z35m_gen (hD : D3Std M Mp T L V) :
    orbSup (autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp))
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) = ⊤ := by
  have hι := n2Iota_injective Mp (orbSup T V)
  apply Subgroup.map_injective hι
  apply le_antisymm (Subgroup.map_mono le_top)
  rw [n2_map_iota_top]
  have e : tilde Mp (orbSup T V) (orbSup T V) =
      (⨆ t ∈ T, V.map t.toMonoidHom).map (QuotientGroup.mk' (modFix Mp (orbSup T V))) := rfl
  rw [e, Subgroup.map_iSup]
  refine iSup_le fun t => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ht => ?_
  have hρ := (n2_mem_autSec (n2_T_le hD)).2 ⟨⟨t, n2_T_le hD ht⟩, ht, rfl⟩
  calc (V.map t.toMonoidHom).map (QuotientGroup.mk' (modFix Mp (orbSup T V)))
      = tilde Mp (orbSup T V) (t • V) := rfl
    _ = ((sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map
          (n2Rho (orbSup T V) (orbSup T V ⊓ fixV Mp) ⟨t, n2_T_le hD ht⟩).toMonoidHom).map
          (n2Iota Mp (orbSup T V)) := (n2_map_iota_conj ⟨t, n2_T_le hD ht⟩ ht).symm
    _ ≤ _ := Subgroup.map_mono (map_le_orbSup hρ)

theorem z35m_fix (hD : D3Std M Mp T L V) :
    fixV (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp)) = ⊥ := by
  have hι := n2Iota_injective Mp (orbSup T V)
  rw [eq_bot_iff]
  intro x hx
  have h1 : n2Iota Mp (orbSup T V) x ∈ XMod.fixed ↥Mp (tilde Mp (orbSup T V) (orbSup T V)) := by
    refine ⟨?_, fun a => ?_⟩
    · rw [← n2_map_iota_top]
      exact Subgroup.mem_map_of_mem _ trivial
    · obtain ⟨a₁, ha₁⟩ := n2_bwd hD a
      rw [← ha₁ x]
      congr 1
      exact hx a₁ a₁.2
  rw [n2_fixed_tilde_eq_bot hD, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact hι (h1.trans (map_one _).symm)

theorem z35m_homog (hD : D3Std M Mp T L V) :
    ∀ s ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
      ∀ r ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
      XMod.Iso ↥(autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp))
        ((sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map s.toMonoidHom)
        ((sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map r.toMonoidHom) →
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map s.toMonoidHom =
        (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map r.toMonoidHom := by
  intro s hs r hr hiso
  obtain ⟨s', hs'T, rfl⟩ := (n2_mem_autSec (n2_T_le hD)).1 hs
  obtain ⟨r', hr'T, rfl⟩ := (n2_mem_autSec (n2_T_le hD)).1 hr
  have hι := n2Iota_injective Mp (orbSup T V)
  apply Subgroup.map_injective hι
  rw [n2_map_iota_conj s' hs'T, n2_map_iota_conj r' hr'T]
  apply tilde_smul_eq_of_iso_of_mem_irrPlusOn (n2_hTX hD) (n2_hW T V) hD.irrT hs'T hr'T
  rw [← n2_map_iota_conj s' hs'T, ← n2_map_iota_conj r' hr'T]
  exact n2_iso_map hι (n2_bwd hD) hiso

theorem z35m_nontriv (hD : D3Std M Mp T L V)
    (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) :
    ∀ s ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
      ∃ l ∈ conjAutSub s (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)),
        ∃ v ∈ sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V, l v ≠ v := by
  intro s hs
  obtain ⟨s', hs'T, rfl⟩ := (n2_mem_autSec (n2_T_le hD)).1 hs
  by_contra hcon'
  have hcon : ∀ l ∈ conjAutSub (n2Rho (orbSup T V) (orbSup T V ⊓ fixV Mp) s')
      (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)),
      ∀ v ∈ sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V, l v = v :=
    fun l hl v hv => by_contra fun h => hcon' ⟨l, hl, v, hv, h⟩
  have hLMp : L ≤ Mp := hD.hyp.Mp_eq ▸ le_conjClosure L T
  have hTX := n2_hTX hD
  have hexp := hD.hyp.exp
  have key : ∀ x ∈ L, ∀ y ∈ L, x ^ 2 * y = y * x ^ 2 := by
    intro x hx y hy
    have hxXs := n2_Mp_le hD (hLMp hx)
    have hmem : n2Rho _ _ s' * n2Rho _ _ ⟨x, hxXs⟩ * (n2Rho _ _ s')⁻¹ ∈
        conjAutSub (n2Rho (orbSup T V) (orbSup T V ⊓ fixV Mp) s')
          (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)) :=
      Subgroup.mem_map_of_mem _ ((n2_mem_autSec ((hLMp.trans (n2_Mp_le hD)))).2 ⟨⟨x, hxXs⟩, hx, rfl⟩)
    have htriv : ∀ v ∈ V, ((s' : MulAut W) * x * (s' : MulAut W)⁻¹) v * v⁻¹ ∈ fixV Mp := by
      intro v hv
      have hvVT : v ∈ orbSup T V := le_orbSup T V hv
      have h1 := hcon _ hmem (QuotientGroup.mk ⟨v, hvVT⟩) ⟨⟨v, hvVT⟩, hv, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul, n2Rho_mk] at h1
      have h2 := (mk_eq_mk_iff _ _).1 h1
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2.2
    have hl₀Mp : (s' : MulAut W) * x * (s' : MulAut W)⁻¹ ∈ Mp :=
      conj_mem_of_mem_normalizer (hTX hs'T) (hLMp hx)
    set l₀ : MulAut W := (s' : MulAut W) * x * (s' : MulAut W)⁻¹ with hl₀
    have hsq : ∀ v ∈ V, (l₀ ^ 2) v = v := by
      intro v hv
      have hlc : l₀ (l₀ v * v⁻¹) = l₀ v * v⁻¹ := htriv v hv l₀ hl₀Mp
      rw [map_mul, map_inv] at hlc
      have e1 : l₀ (l₀ v) = l₀ v * v⁻¹ * l₀ v := mul_inv_eq_iff_eq_mul.1 hlc
      have hw2 : l₀ v * l₀ v = 1 := by rw [← sq]; exact hexp _
      have hv2 : v * v = 1 := by rw [← sq]; exact hexp _
      rw [sq, MulAut.mul_apply, e1]
      calc l₀ v * v⁻¹ * l₀ v = (l₀ v * l₀ v) * v⁻¹ := by rw [mul_right_comm]
        _ = v⁻¹ := by rw [hw2, one_mul]
        _ = v := inv_eq_of_mul_eq_one_left hv2
    have hcomm := hC (l₀ ^ 2) (Mp.pow_mem hl₀Mp 2) hsq _
      (conj_mem_of_mem_normalizer (hTX hs'T) (hLMp hy))
    have e : l₀ ^ 2 = (s' : MulAut W) * x ^ 2 * (s' : MulAut W)⁻¹ := by rw [hl₀, sq, sq]; group
    rw [e] at hcomm
    have := congrArg (fun z => (s' : MulAut W)⁻¹ * z * (s' : MulAut W)) hcomm
    simpa [mul_assoc] using this
  obtain ⟨-, -, a, b, hab⟩ := hD.hyp.quasi
  apply hab
  apply n2_comm_of_sq_eq_one
  intro z
  induction z using QuotientGroup.induction_on with
  | H z =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact (key z z.2 y y.2).symm

theorem z35m_lt (hD : D3Std M Mp T L V) (hlt : V < orbSup T V) :
    sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V < ⊤ := by
  refine lt_top_iff_ne_top.2 fun htop => ?_
  have hle : orbSup T V ≤ V ⊔ (orbSup T V ⊓ fixV Mp) := by
    intro w hw
    have hx : (QuotientGroup.mk ⟨w, hw⟩ : Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)) ∈
        sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V := by
      rw [htop]
      trivial
    unfold sec35Img at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyw⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hy
    have h2 := QuotientGroup.eq.1 hyw
    rw [Subgroup.mem_subgroupOf] at h2
    have e : w = (y : W) * ((y : W)⁻¹ * w) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hy (by simpa using h2)
  have hcomm : modComm Mp V = V := hD.irrT.1.2.2.1
  have hCfix : orbSup T V ⊓ fixV Mp ≤ XMod.fixed ↥Mp (⊤ : Subgroup W) :=
    fun w hw => ⟨trivial, fun a => hw.2 a a.2⟩
  have h1 : orbSup T V ≤ modComm Mp (orbSup T V) := by
    refine orbSup_le fun t ht => ?_
    change t • V ≤ modComm Mp (orbSup T V)
    calc t • V = t • modComm Mp V := by rw [hcomm]
      _ = modComm Mp (t • V) := smul_modComm (n2_hTX hD ht) V
      _ ≤ modComm Mp (orbSup T V) := XMod.commOf_mono (map_le_orbSup ht)
  have h2 : modComm Mp (orbSup T V) ≤ V := by
    calc modComm Mp (orbSup T V) ≤ modComm Mp (V ⊔ (orbSup T V ⊓ fixV Mp)) := XMod.commOf_mono hle
      _ = modComm Mp V := XMod.commOf_sup_eq_of_le_fixed hCfix
      _ = V := hcomm
  exact hlt.not_ge (h1.trans h2)

end Fields


end CFSG.Quasithin
