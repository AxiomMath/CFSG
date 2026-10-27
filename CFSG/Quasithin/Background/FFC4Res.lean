module

public import CFSG.Quasithin.Background.FFCProdSplitBasic
public import CFSG.Quasithin.Background.FFC4Split
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Restriction

variable {V : Type} [CommGroup V]

@[expose] def resG {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂) :
    ↥G₂ →* MulAut ↥V₂ :=
  (resHom V₂).comp (Subgroup.inclusion hst)

theorem resG_apply {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂) (g : ↥G₂)
    (u : ↥V₂) : ((resG hst g u : ↥V₂) : V) = (g : MulAut V) (u : V) := rfl

theorem resG_injective {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) : Function.Injective (resG hst) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  show (g : MulAut V) = 1
  refine hfaith g g.2 fun v hv => ?_
  have := congrArg (fun φ : MulAut ↥V₂ => ((φ ⟨v, hv⟩ : ↥V₂) : V)) hg
  simpa [resG_apply] using this

theorem autSub_eq_range {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂) :
    autSub G₂ V₂ = (resG hst).range := by
  ext φ
  rw [mem_autSub, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1, hst g.2⟩, g.2, rfl⟩

@[expose] noncomputable def resEquiv {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hst : G₂ ≤ stabSub V₂) (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) :
    ↥G₂ ≃* ↥(autSub G₂ V₂) :=
  (MonoidHom.ofInjective (resG_injective hst hfaith)).trans
    (MulEquiv.subgroupCongr (autSub_eq_range hst).symm)

theorem resEquiv_apply {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) (g : ↥G₂) :
    ((resEquiv hst hfaith g : ↥(autSub G₂ V₂)) : MulAut ↥V₂) = resG hst g := rfl

theorem card_autSub_eq {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) :
    Nat.card ↥(autSub G₂ V₂) = Nat.card ↥G₂ :=
  Nat.card_congr (resEquiv hst hfaith).symm.toEquiv

theorem faithful_of_le {G₂ B : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) (hB : B ≤ G₂) :
    ∀ g ∈ B, (∀ v ∈ V₂, g v = v) → g = 1 := fun g hg => hfaith g (hB hg)


theorem card_fixV_eq_mul_autSub {V₂ V₁ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥)
    {B : Subgroup (MulAut V)} (hB : B ≤ stabSub V₂) (hBV₁ : ∀ b ∈ B, ∀ v ∈ V₁, b v = v) :
    Nat.card (fixV B) = Nat.card V₁ * Nat.card ↥(fixV (autSub B V₂)) := by
  have h₁ : ∀ b ∈ B, ∀ v ∈ V₁, b v ∈ V₁ := fun b hb v hv => by rw [hBV₁ b hb v hv]; exact hv
  have h₂ : ∀ b ∈ B, ∀ v ∈ V₂, b v ∈ V₂ := fun b hb v hv => (hB hb v).2 hv
  rw [card_fixV_of_decomp hsup hinf h₁ h₂]
  have e1 : V₁ ⊓ fixV B = V₁ := inf_eq_left.2 fun v hv b hb => hBV₁ b hb v hv
  have e2 : Nat.card ↥(V₂ ⊓ fixV B) = Nat.card ↥(fixV (autSub B V₂)) := by
    rw [← map_subtype_fixV_autSub hB, Subgroup.card_map_of_injective V₂.subtype_injective]
  rw [e1, e2]

theorem exists_autSub_eq {B : Subgroup (MulAut V)} {V₂ : Subgroup V} (hB : B ≤ stabSub V₂)
    {B'' : Subgroup (MulAut ↥V₂)} (h : B'' ≤ autSub B V₂) :
    ∃ B₀ : Subgroup (MulAut V), B₀ ≤ B ∧ autSub B₀ V₂ = B'' := by
  refine ⟨(B''.comap (resG hB)).map B.subtype, Subgroup.map_subtype_le _, ?_⟩
  have hrange := autSub_eq_range hB
  ext φ
  rw [mem_autSub]
  constructor
  · rintro ⟨g, ⟨b, hb, hbg⟩, rfl⟩
    have : resHom V₂ g = resG hB b := by
      have hbg' : (b : MulAut V) = g.1 := hbg
      have : g = Subgroup.inclusion hB b := Subtype.ext hbg'.symm
      rw [this]
      rfl
    rw [this]
    exact hb
  · intro hφ
    have hφ' : φ ∈ (resG hB).range := hrange ▸ h hφ
    obtain ⟨b, rfl⟩ := hφ'
    refine ⟨⟨b.1, hB b.2⟩, ⟨b, hφ, rfl⟩, rfl⟩

theorem isFFStarOffender_autSub {V₁ V₂ : Subgroup V} [Finite V] (hsup : V₁ ⊔ V₂ = ⊤)
    (hinf : V₁ ⊓ V₂ = ⊥) {G₂ : Subgroup (MulAut V)} (hst : G₂ ≤ stabSub V₂)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1) (hG₂V₁ : ∀ b ∈ G₂, ∀ v ∈ V₁, b v = v)
    {G B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) (hBG₂ : B ≤ G₂) :
    IsFFStarOffender (autSub G₂ V₂) (autSub B V₂) := by
  have hBst : B ≤ stabSub V₂ := hBG₂.trans hst
  have hBfaith := faithful_of_le hfaith hBG₂
  have hcardB : Nat.card ↥(autSub B V₂) = Nat.card ↥B := card_autSub_eq hBst hBfaith
  have hV₁pos : 0 < Nat.card V₁ := Nat.card_pos
  refine ⟨autSub_mono hBG₂ V₂, ?_, ?_, ?_⟩
  · intro hbot
    have h1 : Nat.card ↥(autSub B V₂) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcardB] at h1
    exact hB.2.1 (Subgroup.card_eq_one.1 h1)
  ·
    obtain ⟨hcomm, hsq⟩ := hB.2.2.1
    constructor
    · intro φ hφ ψ hψ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
      obtain ⟨h, hh, rfl⟩ := mem_autSub.1 hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm g hg h hh)
    · intro φ hφ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (hsq g hg)
      rw [this, map_one]
  · intro B'' hB''
    obtain ⟨B₀, hB₀B, rfl⟩ := exists_autSub_eq hBst hB''
    have hB₀st : B₀ ≤ stabSub V₂ := hB₀B.trans hBst
    have hB₀faith := faithful_of_le hBfaith hB₀B
    have h1 := hB.2.2.2 B₀ hB₀B
    have e0 := card_autSub_eq hB₀st hB₀faith
    have e1 := card_fixV_eq_mul_autSub hsup hinf hB₀st
      (fun b hb v hv => hG₂V₁ b (hBG₂ (hB₀B hb)) v hv)
    have e2 := card_fixV_eq_mul_autSub hsup hinf hBst
      (fun b hb v hv => hG₂V₁ b (hBG₂ hb) v hv)
    rw [e0, hcardB]
    rw [e1, e2] at h1
    have : Nat.card V₁ * (Nat.card ↥B₀ * Nat.card ↥(fixV (autSub B₀ V₂))) ≤
        Nat.card V₁ * (Nat.card ↥B * Nat.card ↥(fixV (autSub B V₂))) := by
      calc Nat.card V₁ * (Nat.card ↥B₀ * Nat.card ↥(fixV (autSub B₀ V₂)))
          = Nat.card ↥B₀ * (Nat.card V₁ * Nat.card ↥(fixV (autSub B₀ V₂))) := by ring
        _ ≤ Nat.card ↥B * (Nat.card V₁ * Nat.card ↥(fixV (autSub B V₂))) := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hV₁pos


end Restriction

section B53

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isQuotientOfSQTKTauCeti_of_b53 {G : Subgroup (MulAut V)} (h : B53Hyp G) :
    IsQuotientOfSQTKTauCeti ↥G := by
  obtain ⟨-, -, X, _, _, N, _, hX, ⟨e⟩⟩ := h
  exact ⟨X, inferInstance, inferInstance, hX.1, hX.2, e.symm.toMonoidHom.comp (QuotientGroup.mk' N),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)⟩

theorem b53_clause_of_isQuotientOfSQTKTauCeti {G : Type*} [Group G]
    (h : IsQuotientOfSQTKTauCeti G) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (N : Subgroup X) (_ : N.Normal),
      SQTKGroup X ∧ Nonempty (G ≃* X ⧸ N) := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  exact ⟨S, inferInstance, inferInstance, φ.ker, inferInstance, ⟨hst, hkg⟩,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm⟩⟩

omit [Finite V] in
theorem normal_of_commute {G G₁ G₂ : Subgroup (MulAut V)} (hsup : G₁ ⊔ G₂ = G)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) : (G₂.subgroupOf G).Normal := by
  have hle : G₂ ≤ G := hsup ▸ le_sup_right
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
  rw [← hsup]
  refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : a * x = x * a := hcomm a ha x hx
    rwa [h1, mul_inv_cancel_right]
  · intro hx
    have h := hcomm a ha _ hx
    have h' : a * (a * x * a⁻¹) = a * x := by
      calc a * (a * x * a⁻¹) = (a * x * a⁻¹) * a := h
        _ = a * x := by group
    have : a * x * a⁻¹ = x := mul_left_cancel h'
    rwa [this] at hx


theorem b53Hyp_autSub {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) (hinf : V₁ ⊓ V₂ = ⊥)
    {G G₂ : Subgroup (MulAut V)} (hGG₂ : G₂ ≤ G) (hnormal : (G₂.subgroupOf G).Normal)
    (hst : G₂ ≤ stabSub V₂) (hfaith : ∀ g ∈ G₂, (∀ v ∈ V₂, g v = v) → g = 1)
    (hG₂V₁ : ∀ b ∈ G₂, ∀ v ∈ V₁, b v = v) (hO2 : pCoreOf 2 G = ⊥)
    (hgen : G₂ = ⨆ (B : Subgroup (MulAut V)) (_ : IsFFStarOffender G B ∧ B ≤ G₂), B)
    (hq : IsQuotientOfSQTKTauCeti ↥G) : B53Hyp (autSub G₂ V₂) := by
  set e := resEquiv hst hfaith with he
  have hO2G₂ : pCoreOf 2 G₂ = ⊥ := by
    have hGnorm : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hGG₂).1 hnormal
    have : pCoreOf 2 G₂ ≤ pCoreOf 2 G :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₂).trans hGG₂)
        (hGnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G₂))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₂)
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hpc : CFSG.Open.pCore 2 ↥G₂ = ⊥ := by
    have h1 : (CFSG.Open.pCore 2 ↥G₂).map G₂.subtype = ⊥ := hO2G₂
    exact (Subgroup.map_eq_bot_iff_of_injective _ G₂.subtype_injective).1 h1
  have hO2' : pCoreOf 2 (autSub G₂ V₂) = ⊥ := by
    have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
    rw [hpc, Subgroup.map_bot] at h1
    show (CFSG.Open.pCore 2 ↥(autSub G₂ V₂)).map (autSub G₂ V₂).subtype = ⊥
    rw [← h1, Subgroup.map_bot]
  have hJ : autSub G₂ V₂ = ffJ (autSub G₂ V₂) := by
    refine le_antisymm ?_ (B6.ffJ_le _)
    let S : Subgroup ↥G₂ := (ffJ (autSub G₂ V₂)).comap (resG hst)
    have hSmap : G₂ ≤ S.map G₂.subtype := by
      refine hgen.le.trans (iSup₂_le fun B hB => ?_)
      intro b hb
      have hoff := isFFStarOffender_autSub hsup hinf hst hfaith hG₂V₁ hB.1 hB.2
      have hBst : B ≤ stabSub V₂ := hB.2.trans hst
      have hmem : resG hst ⟨b, hB.2 hb⟩ ∈ autSub B V₂ :=
        mem_autSub.2 ⟨⟨b, hBst hb⟩, hb, rfl⟩
      refine ⟨⟨b, hB.2 hb⟩, ?_, rfl⟩
      exact (B6.le_ffJ hoff) hmem
    intro φ hφ
    have hφ' : φ ∈ (resG hst).range := autSub_eq_range hst ▸ hφ
    obtain ⟨g, rfl⟩ := hφ'
    obtain ⟨g', hg', hgg'⟩ := hSmap g.2
    have : g' = g := Subtype.ext hgg'
    rw [this] at hg'
    exact hg'
  have hq' : IsQuotientOfSQTKTauCeti ↥(autSub G₂ V₂) :=
    IsQuotientOfSQTKTauCeti.of_mulEquiv e ((hq.of_le hGG₂))
  exact ⟨hO2', hJ, b53_clause_of_isQuotientOfSQTKTauCeti hq'⟩


end B53

section Split

variable {V : Type} [CommGroup V] [Finite V]

namespace B58Split

variable {G A G₁ G₂ F : Subgroup (MulAut V)} (h : B58Split G A G₁ G₂ F)

omit [Finite V] in
include h in
theorem stab : G₂ ≤ stabSub (fixV G₁) :=
  ProdSplit.stab h.comm

omit [Finite V] in
include h in
theorem faithful : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1 := by
  intro g hg hv
  ext v
  have hv' : v ∈ commV G₁ ⊔ fixV G₁ := by rw [h.dec_sup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv'
  rw [map_mul, h.triv₁ g hg y hy, hv z hz]
  rfl

omit [Finite V] in
include h in
theorem normal : (G₂.subgroupOf G).Normal := normal_of_commute h.sup h.comm

include h in
theorem b53 (hO2 : pCoreOf 2 G = ⊥) (hq : IsQuotientOfSQTKTauCeti ↥G) :
    B53Hyp (autSub G₂ (fixV G₁)) :=
  b53Hyp_autSub h.dec_sup h.dec_inf h.G₂_le h.normal h.stab h.faithful h.triv₁ hO2 h.gen₂ hq

include h in
theorem card_lt (hA : A ≠ ⊥) : Nat.card ↥(autSub G₂ (fixV G₁)) < Nat.card ↥G := by
  rw [card_autSub_eq h.stab h.faithful]
  by_contra hcon
  have heq : G₂ = G := Subgroup.eq_of_le_of_card_ge h.G₂_le (not_lt.1 hcon)
  have h1 : G₁ ≤ G₂ := heq ▸ h.G₁_le
  have h2 : G₁ = ⊥ := (inf_eq_left.2 h1).symm.trans h.inf
  exact hA (le_bot_iff.1 (h2 ▸ h.A_le))

omit [Finite V] in
include h in
theorem autSub_ne_bot (hne : G₂ ≠ ⊥) : autSub G₂ (fixV G₁) ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥(autSub G₂ (fixV G₁)) = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [card_autSub_eq h.stab h.faithful] at h1
  exact hne (Subgroup.card_eq_one.1 h1)

end B58Split

end Split

end FFC

end CFSG.Quasithin
