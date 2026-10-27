module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBSelfCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

theorem exists_glaLabel {X : Type} [Group X] {P : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => P lab)) :
    ∃ lab, P lab ∧ GLAMarking X (fun l _ _ _ _ _ => l = lab) := by
  obtain ⟨hc, lab, hl, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  exact ⟨lab, hP, hc, lab, hl, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨h1, h2, θ', _⟩ => ⟨h1, h2, θ', rfl⟩) hraw⟩

theorem exists_label_of_marking {G : Type} [Group G] (hG : IsSimpleGroup G)
    {P : LargeEvenLabel → Prop}
    (h : LargeEvenMarking (⊤ : Subgroup G) (fun lab _ _ _ _ _ => P lab)) :
    Subgroup.center (⊤ : Subgroup G) = ⊥ ∧ ∃ lab, P lab ∧
      GLAMarking (⊤ : Subgroup G) (fun l _ _ _ _ _ => l = lab) := by
  refine ⟨?_, exists_glaLabel h⟩
  obtain ⟨hc, lab, hl, hraw⟩ := h
  obtain ⟨R, _, I, F, -, ⟨a, b, hab⟩, θ, -⟩ := largeEvenRawDatum_exists hraw
  have hZG : Subgroup.center G = ⊥ := by
    rcases hG.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm a)
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm b)
      have hxy : x * y = y * x := Subtype.ext
        ((Subgroup.mem_center_iff.1 (show (y : G) ∈ Subgroup.center G by
          rw [h]; exact Subgroup.mem_top _)) (x : G))
      apply hab
      rw [← θ.apply_symm_apply a, ← θ.apply_symm_apply b, ← hx, ← hy, ← map_mul, ← map_mul,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  rw [eq_bot_iff]
  intro z hz
  have hzG : (z : G) ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, Subgroup.mem_top g⟩)
  rw [hZG] at hzG
  exact Subtype.ext hzG

@[expose] def E7TwoSelfCentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K E : Subgroup G), IsEm 7 K → Subgroup.center K = ⊥ →
    E ≤ K → IsElemAbelian 3 E → Nat.card E = 3 ^ 7 →
      K ⊓ Subgroup.centralizer (E : Set G) = E

theorem e7FrameSelfCent :
    Subgroup.centralizer
        ((TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range :
          Set (CFSG.Blueprint.Chevalley.adjointGroup .E7 (GaloisField 2 1))) ≤
      (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGF : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  exact (TableBExcTwoTB.centralizer_tE_frameE7 (by simpa using hGF)).le

section E7Label

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.GLTheoremA CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem exists_mulEquiv_adjointGroup_of_isLabel_E7'
    {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hlab : HasLabel K (fun l : GLALabel => l = lab)) (htag : lab.tag = .E7)
    (hZ : Subgroup.center K = ⊥) :
    Nonempty (K ≃* ↥(adjointGroup Tag.E7 (GaloisField 2 lab.n))) := by
  have hK : Rk2IsLabel K lab := hlab
  obtain ⟨-, hlam, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hn1 : 1 ≤ lab.n := hlam.1
  let e0 : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hM' : MarkedModel lab K := MarkedModel.of_mulEquiv e0 hM
  have hL : LieModel K .E7 0 2 lab.n := lieModel_of_markedModel_E7 htag hM'
  have hCEM : ChevalleyExceptionalModel K .E7 2 lab.n :=
    hL.chevalleyExceptionalModel (by decide)
  obtain ⟨F, hF, hFin, hcard, ⟨iso⟩⟩ := hCEM.2
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 lab.n) := Fintype.ofFinite _
  have hGFcard : Nat.card (GaloisField 2 lab.n) = 2 ^ lab.n :=
    GaloisField.card 2 lab.n (by omega)
  let φ : F ≃+* GaloisField 2 lab.n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGFcard, hcard])
  let eAQ : AdjointQuotient Tag.E7 F ≃* ↥(adjointGroup Tag.E7 F) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E7) (K := F))).trans
      QuotientGroup.quotientBot
  exact ⟨iso.trans (eAQ.trans (CFSG.TauCetiBridge.adjointGroupCongr φ))⟩

end E7Label

theorem e7TwoSelfCentInput_of_frame
    : E7TwoSelfCentInput := by
  have hT := e7FrameSelfCent
  intro G _ _ K E hm hZ hEK hE hcard
  obtain ⟨⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_glaLabel hm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGF : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  let E₂ := (E.subgroupOf K).map φ.toMonoidHom
  have hE₂ : IsElemAbelian 3 E₂ := (hE.subgroupOf K).map _
  have hc₂ : Nat.card E₂ = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hcard]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 (by simpa using hGF) hE₂ hc₂.ge
  refine le_antisymm ?_ (le_inf hEK fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
  · rintro g ⟨hgK, hgC⟩
    have hk : φ ⟨g, hgK⟩ ∈ E₂ := by
      have hz : c⁻¹ * φ ⟨g, hgK⟩ * c ∈
          (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range := by
        refine hT (Subgroup.mem_centralizer_iff.2 fun s hs => ?_)
        have hs' : c * s * c⁻¹ ∈ E₂ := by
          rw [hc]; exact ⟨s, hs, rfl⟩
        obtain ⟨⟨y, hyK⟩, hy, hys⟩ := hs'
        have hyE : y ∈ E := hy
        have hcomm : y * g = g * y := Subgroup.mem_centralizer_iff.1 hgC y hyE
        have h1 : φ ⟨y, hyK⟩ * φ ⟨g, hgK⟩ = φ ⟨g, hgK⟩ * φ ⟨y, hyK⟩ := by
          rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hcomm
        have hys' : φ ⟨y, hyK⟩ = c * s * c⁻¹ := hys
        rw [hys'] at h1
        calc s * (c⁻¹ * φ ⟨g, hgK⟩ * c)
            = c⁻¹ * ((c * s * c⁻¹) * φ ⟨g, hgK⟩) * c := by group
          _ = c⁻¹ * (φ ⟨g, hgK⟩ * (c * s * c⁻¹)) * c := by rw [h1]
          _ = c⁻¹ * φ ⟨g, hgK⟩ * c * s := by group
      rw [hc]
      refine ⟨_, hz, ?_⟩
      show c * (c⁻¹ * φ ⟨g, hgK⟩ * c) * c⁻¹ = _
      group
    obtain ⟨k, hkE, hkφ⟩ := hk
    have : k = ⟨g, hgK⟩ := φ.injective hkφ
    subst this
    exact hkE
  · exact congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem e7TwoSelfCentInput :
    E7TwoSelfCentInput :=
  e7TwoSelfCentInput_of_frame

@[expose] def GGPsiInput
    (m : ℕ) (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEm m (⊤ : Subgroup G) →
    ∃ ψ : (ggU t 0 1).K →* G, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (ggU t 0 1).K

theorem ggPsi_E8
    : GGPsiInput 8 .E8 := by
  intro G _ _ hG hm
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hG hm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_adjointGroup_of_isLabel_E8
    (lab := ⟨t, r, 1⟩) hlab ht hZ
  let φ : (ggU .E8 0 1).K ≃* G := e.symm.trans Subgroup.topEquiv
  exact ⟨φ.toMonoidHom, φ.surjective, by
    rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective]; exact bot_le⟩

theorem ggPsi_E7
    : GGPsiInput 7 .E7 := by
  intro G _ _ hG hm
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hG hm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  let φ : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 (GaloisField 2 1)) ≃* G :=
    e.symm.trans Subgroup.topEquiv
  let ψ : (ggU .E7 0 1).K →* G :=
    φ.toMonoidHom.comp (CFSG.LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 2 1))
  refine ⟨ψ, φ.surjective.comp
    (CFSG.LieType.Steinberg.Isogeny.e7Isogeny_surjective (GaloisField 2 1)), ?_⟩
  refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 (GaloisField 2 1)) ?_
  obtain ⟨g, hg⟩ := CFSG.LieType.Steinberg.Isogeny.exists_e7Isogeny_ne_one (GaloisField 2 1)
  exact ⟨g, fun h => hg (φ.injective (h.trans (map_one φ).symm))⟩

end CFSG.StandardType.FrameRoute
