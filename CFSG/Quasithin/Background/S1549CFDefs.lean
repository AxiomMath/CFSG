module

public import CFSG.Quasithin.Background.S1549CBasic
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

section Defs

variable {G : Type} [Group G]

abbrev ClaimC (T M V₁ H : Subgroup G) : Prop :=
  omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ ∧
      UH T M V₁ H ≤ centerOf (omegaOneOf (pCoreOf 2 H))

end Defs

section Gen

variable {G : Type*} [Group G]

theorem inv_conj_comm_iff (k a b : G) :
    (k⁻¹ * a * k) * (k⁻¹ * b * k) = (k⁻¹ * b * k) * (k⁻¹ * a * k) ↔ a * b = b * a := by
  constructor
  · intro h
    have := congrArg (fun x => k * x * k⁻¹) h
    have e1 : k * (k⁻¹ * a * k * (k⁻¹ * b * k)) * k⁻¹ = a * b := by group
    have e2 : k * (k⁻¹ * b * k * (k⁻¹ * a * k)) * k⁻¹ = b * a := by group
    rwa [e1, e2] at this
  · intro h
    have e1 : k⁻¹ * a * k * (k⁻¹ * b * k) = k⁻¹ * (a * b) * k := by group
    have e2 : k⁻¹ * b * k * (k⁻¹ * a * k) = k⁻¹ * (b * a) * k := by group
    rw [e1, e2, h]

theorem commutator_commutator_mem_of_abelian {B U N : Subgroup G} (hB : IsElemAbelian 2 B)
    (hUB : ⁅U, B⁆ ≤ B) : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ U,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ N := by
  intro b₁ hb₁ b₂ hb₂ u hu
  have hc0 : b₁ * u * b₁⁻¹ * u⁻¹ ∈ B := by
    have := Subgroup.commutator_mem_commutator hb₁ hu
    rw [Subgroup.commutator_comm] at this
    exact hUB this
  have := isElemAbelian_comm hB hb₂ hc0
  have e : b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ = 1 := by
    rw [this]; group
  rw [e]; exact N.one_mem

theorem mIdx_anti_right [Finite G] {X Y Y' : Subgroup G} (h : Y ≤ Y') :
    mIdx X Y' ≤ mIdx X Y := by
  unfold mIdx
  refine padicValNat_two_le_of_dvd ?_ (Subgroup.relIndex_dvd_of_le_left X h)
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem mIdx_inf_le_of_le [Finite G] {B B' Q : Subgroup G} (hB' : IsPGroup 2 B') (hB : B ≤ B') :
    mIdx B (B ⊓ Q) ≤ mIdx B' (B' ⊓ Q) := by
  have h2 : IsPGroup 2 B := hB'.to_le hB
  have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := B ⊓ Q) h2
  have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := B' ⊓ Q) hB'
  rw [Subgroup.inf_relIndex_left] at e1 e2
  have hne : Q.relIndex B' ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h3 : Q.relIndex B ≤ Q.relIndex B' := Subgroup.relIndex_le_of_le_right hB hne
  rw [e1, e2] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

section Tilde

variable [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem rk_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    rk (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) = mIdx B (B ⊓ pCoreOf 2 H) := by
  unfold rk mIdx
  rw [h.card_autOn_tilde hBH]

theorem rkIdx_fixV_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    @rkIdx ↥(tildeOf V₁ (conjClosure Vp H)) _
      (@fixV ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)))) =
      mIdx (conjClosure Vp H) (centralizerMod V₁ (conjClosure Vp H) B) := by
  have hŨ := h.isElemAbelian_tilde
  have hn := HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) hBH
  have c2 := card_fixV_autOn_eq hŨ hn
  have c3 := h.relIndex_tilde_fixV hBH
  have hmul := Subgroup.relIndex_mul_card (tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))
    (tildeOf V₁ (conjClosure Vp H))
  rw [inf_eq_left.mpr (inf_le_left : tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) ≤
      tildeOf V₁ (conjClosure Vp H))] at hmul
  have hmul2 := Subgroup.index_mul_card
    (@fixV ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian hŨ)
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))))
  rw [c2] at hmul2
  have hpos : 0 < Nat.card ↥(tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer
      (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) := Nat.card_pos
  have hidx := Nat.eq_of_mul_eq_mul_right hpos (hmul2.trans hmul.symm)
  unfold rkIdx mIdx
  rw [hidx, c3]

theorem rAV_le_one_of_rkIdx_le {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)}
    (h : rkIdx (fixV A) ≤ rk A) : rAV A ≤ 1 := by
  unfold rAV
  exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg _)

theorem isQuadratic_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G}
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ u ∈ conjClosure Vp H,
      b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹ ∈ V₁) :
    @IsQuadratic ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) := by
  refine isQuadratic_autOn_of_forall h.isElemAbelian_tilde ?_
  intro s₁ hs₁ s₂ hs₂ w hw
  obtain ⟨b₁, hb₁, rfl⟩ := mem_secImg.mp hs₁
  obtain ⟨b₂, hb₂, rfl⟩ := mem_secImg.mp hs₂
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
  have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁
      (b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹) = 1 :=
    secMk_eq_one_iff.mpr (by simpa using hquad b₁ hb₁ b₂ hb₂ u hu)
  simpa [map_mul, map_inv] using h1

theorem isA2_autOn_tilde (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H)
    (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 H) :
    @IsA2 ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
      (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) := by
  have hŨ := h.isElemAbelian_tilde
  have hBt : IsElemAbelian 2 (tildeOf V₁ B) := isElemAbelian_secImg hBel
  have hn := HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) hBH
  have hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (V₁ : Set G) := fun b hb =>
    h.H_normalizes_V₁ (hBH hb)
  refine ⟨autOn_le_autOn _ (secImg_mono hBH), ?_, isElemAbelian2_autOn hŨ hBt hn⟩
  refine autOn_ne_bot_of_not_le_centralizer hn ?_
  intro hle
  apply hnt
  intro b hb
  have hy : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (⟨b, hN b hb⟩ : Subgroup.normalizer
      (V₁ : Set G)) ∈ tildeOf V₁ B ⊓ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
    ⟨secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb, hle (secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb)⟩
  rw [h.tilde_inf_centralizer_pCoreOf hBH] at hy
  obtain ⟨b', ⟨hb'B, hb'Q⟩, hbb'⟩ := mem_secImg.mp hy
  have h1 := secMk_eq_secMk_iff.mp hbb'
  have hc : ((b' : G))⁻¹ * b ∈ pCoreOf 2 H := h.V₁_le_pCoreOf h1
  have e : b = (b' : G) * ((b' : G)⁻¹ * b) := by group
  rw [e]
  exact Subgroup.mul_mem _ hb'Q hc

end Tilde

section DH

variable [Finite G] {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem DH_le_centralizerMod_of_EH (h : HypF98 T V L V₁ Vp H) {B : Subgroup G}
    (hB : B ≤ F8.Uγ V H (g : G))
    (hf1 : ⁅F9.EH V Vp V₁ H (g : G), F8.Uγ V H (g : G)⁆ = ⊥) :
    F8.DH Vp V₁ H (g : G) ≤ centralizerMod V₁ (conjClosure Vp H) B := by
  intro u hu
  have hUV : conjClosure Vp H ≤ conjClosure V H :=
    conjClosure_mono h.Vp_le_V le_rfl
  have huE : u ∈ F9.EH V Vp V₁ H (g : G) := ⟨hUV hu.1, hu.2.1, hu.2.2⟩
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hf1 huE
  have hUQ := h.toHypF91.conjClosure_Vp_le_pCoreOf
  refine ⟨hu.1, h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hu.1)), fun x hx => ?_⟩
  have := Subgroup.mem_centralizer_iff.mp hcent x (hB hx)
  have e : u * x * u⁻¹ * x⁻¹ = 1 := by rw [← this]; group
  rw [e]; exact V₁.one_mem

theorem Eγ_eq_inf_pCoreOf (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    F9.Eγ V Vp V₁ H (g : G) = F8.Uγ V H (g : G) ⊓ pCoreOf 2 H := by
  have hVγH := h.Vγ_le_H s
  ext x
  rw [Subgroup.mem_inf, h.toHypF91.pCoreOf_eq_centralizerMod]
  constructor
  · rintro ⟨hx, hxN, hxc⟩
    exact ⟨hx, hVγH hx, hxN, hxc⟩
  · rintro ⟨hx, -, hxN, hxc⟩
    exact ⟨hx, hxN, hxc⟩

end DH

end Gen

end S1549C

end CFSG.Quasithin
