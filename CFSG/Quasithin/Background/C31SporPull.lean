module

public import CFSG.Quasithin.Background.C48SporPf
public import CFSG.Quasithin.Background.KGSchurMult2

public section

namespace CFSG.Quasithin.C31Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C48Spor

@[expose] noncomputable def equivOfKerEq {A B₁ B₂ : Type} [Group A] [Group B₁] [Group B₂]
    {f₁ : A →* B₁} {f₂ : A →* B₂} (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (hk : f₁.ker = f₂.ker) : B₁ ≃* B₂ :=
  (QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ h₂))

theorem isAlt_of_mulEquiv {n : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsAlt n A) :
    IsAlt n B :=
  h.map e.symm.trans

theorem isZ4Cubed_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsZ4Cubed A) :
    IsZ4Cubed B :=
  h.map e.symm.trans

theorem isSpecial2Group_of_mulEquiv {a b : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsSpecial2Group a b A) : IsSpecial2Group a b B := by
  obtain ⟨hc, hcomm, hq⟩ := h
  have hZ : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨?_, ?_, isE2_of_mulEquiv (QuotientGroup.congr _ _ e hZ) hq⟩
  · rw [← hZ, Subgroup.card_map_of_injective e.injective, hc]
  · rw [← hZ, ← hcomm, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]

theorem isSporadic_of_mulEquiv {s : TauCeti.SporadicName} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : IsSporadic s A) : IsSporadic s B :=
  IsSporadic.of_mulEquiv e h

theorem isPSL_of_mulEquiv {n p f : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsPSL n p f A) : IsPSL n p f B :=
  Setup.Family.statedClassicalModel_of_mulEquiv e h

theorem isPSU_of_mulEquiv {n p f : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsPSU n p f A) : IsPSU n p f B :=
  Setup.Family.statedClassicalModel_of_mulEquiv e h

@[expose] noncomputable def toImageModCenter {Γ : Type} [Group Γ] {K Y : Subgroup Γ}
    (hYK : Y ≤ K) : ↥Y →* ↥(imageModCenter K Y) :=
  ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hYK)).codRestrict _
    (fun y => Subgroup.mem_map_of_mem _ (show Subgroup.inclusion hYK y ∈ Y.subgroupOf K from y.2))

theorem toImageModCenter_surjective {Γ : Type} [Group Γ] {K Y : Subgroup Γ} (hYK : Y ≤ K) :
    Function.Surjective (toImageModCenter hYK) := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨k, hk⟩, hkY, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨⟨k, hkY⟩, rfl⟩

theorem mem_ker_toImageModCenter {Γ : Type} [Group Γ] {K Y : Subgroup Γ} (hYK : Y ≤ K) (y : ↥Y) :
    y ∈ (toImageModCenter hYK).ker ↔ (y : Γ) ∈ Subgroup.centralizer (K : Set Γ) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h2 : (QuotientGroup.mk' (Subgroup.center ↥K)) (Subgroup.inclusion hYK y) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h2
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => congrArg Subtype.val (h2 ⟨g, hg⟩)
  · intro h
    apply Subtype.ext
    change (QuotientGroup.mk' (Subgroup.center ↥K)) (Subgroup.inclusion hYK y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp h g g.2)

variable {G : Type} [Group G]

theorem imgHom_mem_centralizer_iff {H K Y : Subgroup G} (hK : CFSG.Open.IsComponentOf K H)
    (hYK : Y ≤ K) (y : ↥Y) :
    ((imgHom (N := sporN H K) (hYK.trans (K_le_sporX hK.1)) y : ↥(img (sporN H K) Y)) :
        ↥(sporX H K) ⧸ sporN H K) ∈ Subgroup.centralizer (img (sporN H K) K : Set _) ↔
      (y : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [← mem_ker_imgHom_iff (hYK.trans (K_le_sporX hK.1)) y, MonoidHom.mem_ker]
  constructor
  · intro hc
    have hmem : ((imgHom (N := sporN H K) (hYK.trans (K_le_sporX hK.1)) y : ↥(img _ Y)) :
        ↥(sporX H K) ⧸ sporN H K) ∈ img (sporN H K) K :=
      img_mono hYK (imgHom (N := sporN H K) (hYK.trans (K_le_sporX hK.1)) y).2
    have hz : (⟨_, hmem⟩ : ↥(img (sporN H K) K)) ∈ Subgroup.center ↥(img (sporN H K) K) :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
    rw [center_kStar_eq_bot hK, Subgroup.mem_bot] at hz
    exact Subtype.ext (congrArg (fun z : ↥(img (sporN H K) K) => (z : ↥(sporX H K) ⧸ sporN H K)) hz)
  · intro h1
    rw [h1]
    exact Subgroup.one_mem _

@[expose] noncomputable def imageModCenterEquiv {H K Y : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K H) (hYK : Y ≤ K) :
    ↥(imageModCenter K Y) ≃* ↥(imageModCenter (img (sporN H K) K) (img (sporN H K) Y)) :=
  equivOfKerEq (f₂ := (toImageModCenter (img_mono (N := sporN H K) hYK)).comp
      (imgHom (hYK.trans (K_le_sporX hK.1)))) (toImageModCenter_surjective hYK)
    ((toImageModCenter_surjective (img_mono hYK)).comp
      (imgHom_surjective (hYK.trans (K_le_sporX hK.1)))) (by
    ext y
    rw [mem_ker_toImageModCenter, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      mem_ker_toImageModCenter, imgHom_mem_centralizer_iff hK hYK])

variable [Finite G] {H R M L V K : Subgroup G}

theorem conjClosure_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    conjClosure (img (sporN H K) (conjClosure L M)) (img (sporN H K) M) =
      img (sporN H K) (conjClosure L M) := by
  rw [← img_conjClosure (M0_le_sporX h h31) (M_le_sporX h h31),
    conjClosure_eq_self (le_normalizer_conjClosure L M)]

theorem isExt_imageModCenter_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PV A → PV B)
    (hPY : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PY A → PY B)
    (hext : IsExt ↥(imageModCenter (img (sporN H K) K)
      (conjClosure (img (sporN H K) (conjClosure L M)) (img (sporN H K) M))) PV PY) :
    IsExt ↥(imageModCenter K (conjClosure L M)) PV PY := by
  rw [conjClosure_img h h31] at hext
  exact isExt_of_mulEquiv (imageModCenterEquiv hK h31.1).symm hPV hPY hext

theorem center_eq_bot_of_img (hK : CFSG.Open.IsComponentOf K H) (h31 : C31Basic H R M L V K)
    {s : TauCeti.SporadicName}
    (hs2 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 2 ↥(Subgroup.center K) → IsSporadic s (K ⧸ Subgroup.center K) →
        Subgroup.center K = ⊥)
    (hs : IsSporadic s ↥(img (sporN H K) K)) : Subgroup.center ↥K = ⊥ :=
  hs2 ↥K hK.2.2 (isPGroup_center_of h31.2.2)
    (IsSporadic.of_mulEquiv (kStarEquiv (K_le_sporX hK.1)).symm hs)

@[expose] noncomputable def m0Equiv (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hZ : Subgroup.center ↥K = ⊥) :
    ↥(conjClosure L M) ≃* ↥(img (sporN H K) (conjClosure L M)) :=
  MulEquiv.ofBijective (imgHom (M0_le_sporX h h31))
    ⟨imgHom_M0_injective h h31 hZ, imgHom_surjective _⟩

theorem isExt_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hZ : Subgroup.center ↥K = ⊥) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PV A → PV B)
    (hPY : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → PY A → PY B)
    (hext : IsExt ↥(conjClosure (img (sporN H K) (conjClosure L M)) (img (sporN H K) M)) PV PY) :
    IsExt ↥(conjClosure L M) PV PY := by
  rw [conjClosure_img h h31] at hext
  exact isExt_of_mulEquiv (m0Equiv h h31 hZ).symm hPV hPY hext

theorem c31Case3_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K)
    (h3 : C31Case3 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case3 H R M L V K := by
  obtain ⟨hs, he | he | he⟩ := h3
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inl
      (isExt_imageModCenter_of_img h hK h31 isE2_of_mulEquiv isPSL_of_mulEquiv he)⟩
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inr (Or.inl
      (isExt_imageModCenter_of_img h hK h31 isE2_of_mulEquiv isAlt_of_mulEquiv he))⟩
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inr (Or.inr
      (isExt_imageModCenter_of_img h hK h31 isE2_of_mulEquiv isPSL_of_mulEquiv he))⟩

theorem c31Case7_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K)
    (h7 : C31Case7 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case7 H R M L V K := by
  obtain ⟨hs, he | he⟩ := h7
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inl
      (isExt_imageModCenter_of_img h hK h31 isZ4Cubed_of_mulEquiv isPSL_of_mulEquiv he)⟩
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inr
      (isExt_imageModCenter_of_img h hK h31 isE2_of_mulEquiv isAlt_of_mulEquiv he)⟩

theorem c31Case9_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K)
    (h9 : C31Case9 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case9 H R M L V K := by
  obtain ⟨hs, he | he⟩ := h9
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inl
      (isExt_imageModCenter_of_img h hK h31 isSpecial2Group_of_mulEquiv isPSL_of_mulEquiv he)⟩
  · exact ⟨IsSporadic.of_mulEquiv (kStarQuotEquiv hK) hs, Or.inr
      (isExt_imageModCenter_of_img h hK h31 isE2_of_mulEquiv isPSU_of_mulEquiv he)⟩

theorem c31Case4_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hM23 : SchurMult2M23)
    (h4 : C31Case4 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case4 H R M L V K := by
  obtain ⟨hs, he | he | he⟩ := h4
  · have hZ := center_eq_bot_of_img hK h31 hM23 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inl
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isPSL_of_mulEquiv he)⟩
  · have hZ := center_eq_bot_of_img hK h31 hM23 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inl
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isAlt_of_mulEquiv he))⟩
  · have hZ := center_eq_bot_of_img hK h31 hM23 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inr
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isPSL_of_mulEquiv he))⟩

theorem c31Case5_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hM24 : SchurMult2M24)
    (h5 : C31Case5 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case5 H R M L V K := by
  obtain ⟨hs, he | he | he⟩ := h5
  · have hZ := center_eq_bot_of_img hK h31 hM24 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inl
      (isExt_of_img h h31 hZ isE2_of_mulEquiv (fun e h => isHat_of_mulEquiv e h) he)⟩
  · have hZ := center_eq_bot_of_img hK h31 hM24 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inl
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isPSL_of_mulEquiv he))⟩
  · have hZ := center_eq_bot_of_img hK h31 hM24 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inr
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isPSL_of_mulEquiv he))⟩

theorem c31Case6_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hJ4 : SchurMult2J4)
    (h6 : C31Case6 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case6 H R M L V K := by
  obtain ⟨hs, he | he | he⟩ := h6
  · have hZ := center_eq_bot_of_img hK h31 hJ4 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inl
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isSporadic_of_mulEquiv he)⟩
  · have hZ := center_eq_bot_of_img hK h31 hJ4 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inl
      (isExt_of_img h h31 hZ isSpecial2Group_of_mulEquiv isPSL_of_mulEquiv he))⟩
  · have hZ := center_eq_bot_of_img hK h31 hJ4 hs
    exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs, Or.inr (Or.inr
      (isExt_of_img h h31 hZ isE2_of_mulEquiv isPSL_of_mulEquiv he))⟩

theorem c31Case8_of_img (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (h31 : C31Basic H R M L V K) (hHe : SchurMult2He)
    (h8 : C31Case8 ⊤ (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) (conjClosure L M))
      (img (sporN H K) V) (img (sporN H K) K)) : C31Case8 H R M L V K := by
  obtain ⟨hs, he⟩ := h8
  have hZ := center_eq_bot_of_img hK h31 hHe hs
  exact ⟨IsSporadic.of_mulEquiv (kEquivKStar hK hZ).symm hs,
    isExt_of_img h h31 hZ isE2_of_mulEquiv (fun e h => isHat_of_mulEquiv e h) he⟩

end CFSG.Quasithin.C31Spor
