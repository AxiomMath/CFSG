module

public import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

namespace FFC

namespace ProdSplit

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G G₁ G₂ : Subgroup (MulAut V)}

theorem ffJ_autSub [Finite V] (hsup : G₁ ⊔ G₂ = G) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hJ : G = ffJ G) : autSub G₂ (fixV G₁) ≤ ffJ (autSub G₂ (fixV G₁)) := by
  set V₂ := fixV G₁ with hV₂
  have hGst : G ≤ stabSub V₂ := stab_G hsup hcomm
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  have hgG : (g : MulAut V) ∈ ffJ G := hJ ▸ (hsup ▸ le_sup_right : G₂ ≤ G) hg
  have hmain : ∀ x : MulAut V, x ∈ ffJ G → ∃ hx : x ∈ stabSub V₂,
      resHom V₂ ⟨x, hx⟩ ∈ ffJ (autSub G₂ V₂) := by
    intro x hx
    unfold ffJ at hx
    refine Subgroup.iSup_induction _ hx (C := fun x => ∃ hx : x ∈ stabSub V₂,
      resHom V₂ ⟨x, hx⟩ ∈ ffJ (autSub G₂ V₂)) ?_ ?_ ?_
    · intro A x hxA
      refine Subgroup.iSup_induction _ hxA (C := fun x => ∃ hx : x ∈ stabSub V₂,
        resHom V₂ ⟨x, hx⟩ ∈ ffJ (autSub G₂ V₂)) ?_ ?_ ?_
      · intro hA x hxA
        have hxst : x ∈ stabSub V₂ := hGst (hA.1 hxA)
        refine ⟨hxst, ?_⟩
        by_cases hnt : A ≤ centSub V₂
        · have h1 : resHom V₂ ⟨x, hxst⟩ = 1 := by
            ext v
            exact hnt hxA v v.2
          rw [h1]
          exact (ffJ (autSub G₂ V₂)).one_mem
        · have hoff := B1Red.isFFStarOffender_autSub hA
            (fun a ha w hw => (hGst (hA.1 ha) w).2 hw) hnt
          rw [autSub_sup_eq hsup hcomm] at hoff
          have hmem : resHom V₂ ⟨x, hxst⟩ ∈ autSub A V₂ := mem_autSub.2 ⟨⟨x, hxst⟩, hxA, rfl⟩
          exact (B6.le_ffJ hoff) hmem
      · exact ⟨(stabSub V₂).one_mem, by
          have : resHom V₂ ⟨1, (stabSub V₂).one_mem⟩ = 1 := map_one _
          rw [this]
          exact (ffJ (autSub G₂ V₂)).one_mem⟩
      · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨(stabSub V₂).mul_mem hx hy, ?_⟩
        have : resHom V₂ ⟨x * y, (stabSub V₂).mul_mem hx hy⟩ =
            resHom V₂ ⟨x, hx⟩ * resHom V₂ ⟨y, hy⟩ := (map_mul (resHom V₂) ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ rfl
        rw [this]
        exact (ffJ (autSub G₂ V₂)).mul_mem hx' hy'
    · exact ⟨(stabSub V₂).one_mem, by
        have : resHom V₂ ⟨1, (stabSub V₂).one_mem⟩ = 1 := map_one _
        rw [this]
        exact (ffJ (autSub G₂ V₂)).one_mem⟩
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨(stabSub V₂).mul_mem hx hy, ?_⟩
      have : resHom V₂ ⟨x * y, (stabSub V₂).mul_mem hx hy⟩ =
          resHom V₂ ⟨x, hx⟩ * resHom V₂ ⟨y, hy⟩ := (map_mul (resHom V₂) ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ rfl
      rw [this]
      exact (ffJ (autSub G₂ V₂)).mul_mem hx' hy'
  obtain ⟨hx, hx'⟩ := hmain g hgG
  have : (⟨(g : MulAut V), hx⟩ : stabSub V₂) = g := rfl
  rw [this] at hx'
  exact hx'

theorem b53 [Finite V] (hsup : G₁ ⊔ G₂ = G) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hO2 : pCoreOf 2 G = ⊥)
    (hJ : G = ffJ G) (hq : IsQuotientOfSQTKTauCeti ↥G) : B53Hyp (autSub G₂ (fixV G₁)) := by
  set V₂ := fixV G₁ with hV₂
  have hG₂ : G₂ ≤ G := hsup ▸ le_sup_right
  set e := resEquiv (stab hcomm) hfaith with he
  have hO2G₂ : pCoreOf 2 G₂ = ⊥ := by
    have hGnorm : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hG₂).1 (normal_of_commute hsup hcomm)
    have : pCoreOf 2 G₂ ≤ pCoreOf 2 G :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₂).trans hG₂)
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
  have hq' : IsQuotientOfSQTKTauCeti ↥(autSub G₂ V₂) :=
    IsQuotientOfSQTKTauCeti.of_mulEquiv e ((hq.of_le hG₂))
  exact ⟨hO2', le_antisymm (ffJ_autSub hsup hcomm hJ) (B6.ffJ_le _),
    b53_clause_of_isQuotientOfSQTKTauCeti hq'⟩

theorem card_lt [Finite V] (hsup : G₁ ⊔ G₂ = G) (hinf : G₁ ⊓ G₂ = ⊥)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hG₁ : G₁ ≠ ⊥) :
    Nat.card ↥(autSub G₂ (fixV G₁)) < Nat.card ↥G := by
  rw [card_autSub_eq (stab hcomm) hfaith]
  by_contra hcon
  have heq : G₂ = G := Subgroup.eq_of_le_of_card_ge (hsup ▸ le_sup_right) (not_lt.1 hcon)
  have h1 : G₁ ≤ G₂ := heq ▸ hsup ▸ le_sup_left
  have h2 : G₁ = ⊥ := (inf_eq_left.2 h1).symm.trans hinf
  exact hG₁ h2

theorem autSub_ne_bot (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hfaith : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) (hne : G₂ ≠ ⊥) :
    autSub G₂ (fixV G₁) ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥(autSub G₂ (fixV G₁)) = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [card_autSub_eq (stab hcomm) hfaith] at h1
  exact hne (Subgroup.card_eq_one.1 h1)

end ProdSplit

end FFC

end CFSG.Quasithin
