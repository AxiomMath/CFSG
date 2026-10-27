module

public import CFSG.Quasithin.Background.MS09.Theorem46
public import CFSG.Quasithin.Vol2.Ch3zSetup

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.Ch3z
  CFSG.Quasithin.MS09.Mod

variable {G : Type} [Group G] [Finite G]

theorem card_lt_autOn_fixV {K E B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hlt : (centralizerMod K E B).relIndex E < (centralizerMod K B E).relIndex B) :
    Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E) <
      Nat.card (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
          (secImg (Subgroup.normalizer (K : Set G)) K E)) *
        Nat.card (@fixV ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
          (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
            (secImg (Subgroup.normalizer (K : Set G)) K E))) := by
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  have c1 := card_autOn_secImg hBK hEK hBE
  have c2 := card_fixV_autOn_eq hE hn
  have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
  have hmul := Subgroup.relIndex_mul_card
    (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
      (secImg (Subgroup.normalizer (K : Set G)) K B :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
    (secImg (Subgroup.normalizer (K : Set G)) K E)
  rw [inf_eq_left.mpr inf_le_left] at hmul
  have hpos : 0 < Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓
      Subgroup.centralizer (secImg (Subgroup.normalizer (K : Set G)) K B :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := Nat.card_pos
  rw [c1, c2]
  calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
      = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
          (secImg (Subgroup.normalizer (K : Set G)) K E) *
        Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
    _ < (centralizerMod K B E).relIndex B *
        Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
      rw [c3]; exact Nat.mul_lt_mul_of_pos_right hlt hpos

theorem relIndex_le_of_minParabolic {G₂ T M₂ U L N A : Subgroup G} (hmp : MinParabolic G₂ T M₂)
    (hUT : U ≤ T) (hUe : IsElemAbelian 2 U) (hstep : IsChiefStep G₂ U L N)
    (hnc : ¬ IsCentralStep G₂ L N) (hAG₂ : A ≤ G₂) (hA2 : IsPGroup 2 A)
    (hquad : ⁅⁅N, A⁆, A⁆ ≤ L) :
    (centralizerMod L A N).relIndex A ≤ (centralizerMod L N A).relIndex N := by
  have hTG₂ : T ≤ G₂ := hmp.isSylow.1
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂L : G₂ ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUG₂).trans hG₂L
  have hE : IsElemAbelian 2 (chiefMod L N) := D15Proof.isElemAbelian_secImg_of_le hUe hNU
  by_contra hlt
  push Not at hlt
  have hstrong := card_lt_autOn_fixV hE hNL (hAG₂.trans hG₂L) (hAG₂.trans hG₂N) hlt
  let _ : CommGroup ↥(chiefMod L N) := commGroupOfElemAbelian hE
  set X := chiefAut G₂ L N with hX
  set B := autOn (secImg (Subgroup.normalizer (L : Set G)) L A) (chiefMod L N) with hB
  have hBX : B ≤ X := autOn_le_autOn _ (secImg_mono hAG₂)
  have hV : ∀ v : ↥(chiefMod L N), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hE.2 v v.2)
  have hmpX := chiefAut_minParabolic_top hmp hUT hstep hnc
  have hirr : ∀ W : Subgroup ↥(chiefMod L N),
      (⊤ : Subgroup ↥X) ≤ stabIn X.subtype W → W = ⊥ ∨ W = ⊤ := fun W hW =>
    chiefMod_irr hstep hUG₂ W fun x hx w hw => (hW (Subgroup.mem_top ⟨x, hx⟩) w).mpr hw
  have hnt : ¬ (⊤ : Subgroup ↥X) ≤ cenIn X.subtype ⊤ := by
    intro htop
    apply hnc
    intro g hg x hx
    have hgx : g * x * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hG₂N hg) x).mp hx
    have hfix := htop (Subgroup.mem_top ⟨chiefPsi hG₂L hG₂N ⟨g, hg⟩, chiefPsi_mem hG₂L hG₂N _⟩)
      (chiefIota hNL ⟨x, hx⟩) (Subgroup.mem_top _)
    change chiefPsi hG₂L hG₂N ⟨g, hg⟩ (chiefIota hNL ⟨x, hx⟩) = chiefIota hNL ⟨x, hx⟩ at hfix
    rw [chiefPsi_iota hG₂L hG₂N hNL ⟨g, hg⟩ ⟨x, hx⟩ hgx] at hfix
    have h1 : chiefIota hNL (⟨g * x * g⁻¹, hgx⟩ * (⟨x, hx⟩ : ↥N)⁻¹) = 1 := by
      rw [map_mul, map_inv, hfix, mul_inv_cancel]
    simpa using (chiefIota_eq_one_iff hNL _).mp h1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAG₂.trans hG₂L
  have hn : secImg (Subgroup.normalizer (L : Set G)) L A ≤
      Subgroup.normalizer (chiefMod L N : Set (SecQuot (Subgroup.normalizer (L : Set G)) L)) :=
    secImg_le_normalizer_secImg (K := L) (E := N) (X := A) (hAG₂.trans hG₂N)
  have hsec2 : IsPGroup 2 ↥(secImg (Subgroup.normalizer (L : Set G)) L A) :=
    (hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm).map _
  have hB2 : IsPGroup 2 ↥B :=
    (hsec2.of_equiv (Subgroup.subgroupOfEquivOfLe hn).symm).map _
  have hB'2 : IsPGroup 2 ↥(B.subgroupOf X) := hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBX).symm
  have hBq : IsQuadratic B := by
    refine isQuadratic_autOn_of_forall hE ?_
    intro s₁ hs₁ s₂ hs₂ w hw
    obtain ⟨b₁, hb₁, rfl⟩ := mem_secImg.mp hs₁
    obtain ⟨b₂, hb₂, rfl⟩ := mem_secImg.mp hs₂
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
    have hc : (b₁ : G) * u * (b₁ : G)⁻¹ * (u : G)⁻¹ ∈ ⁅N, A⁆ := by
      have := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hu hb₁)
      simpa [commutatorElement_def, mul_assoc] using this
    have hL : (b₂ : G) * ((b₁ : G) * u * (b₁ : G)⁻¹ * (u : G)⁻¹) * (b₂ : G)⁻¹ *
        ((b₁ : G) * u * (b₁ : G)⁻¹ * (u : G)⁻¹)⁻¹ ∈ L := by
      have := hquad (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hc hb₂))
      simpa [commutatorElement_def, mul_assoc] using this
    have h1 : secMk (Subgroup.normalizer (L : Set G)) L
        (b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹) = 1 :=
      secMk_eq_one_iff.mpr (by simpa using hL)
    simpa [map_mul, map_inv] using h1
  have hquadB : ∀ a ∈ B.subgroupOf X, ∀ b ∈ B.subgroupOf X, ∀ u : ↥(chiefMod L N),
      X.subtype a (X.subtype b u * u⁻¹) = X.subtype b u * u⁻¹ := by
    intro a ha b hb u
    have hmem : X.subtype b u * u⁻¹ ∈ commV B :=
      Subgroup.subset_closure ⟨_, Subgroup.mem_subgroupOf.mp hb, u, rfl⟩
    exact hBq hmem _ (Subgroup.mem_subgroupOf.mp ha)
  have key := Th46.relIndex_mul_card_fixIn_le_of_minParabolic (ρ := X.subtype) hmpX hV hirr hnt
    hB'2 hquadB
  have hcen : cenIn X.subtype (⊤ : Subgroup ↥(chiefMod L N)) = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    rw [Subgroup.mem_bot]
    exact Subtype.ext (MulEquiv.ext fun u => hg u (Subgroup.mem_top u))
  have hfix : fixIn X.subtype (B.subgroupOf X) ⊤ = fixV B := by
    ext u
    constructor
    · intro hu x hx
      exact hu.2 ⟨x, hBX hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    · intro hu
      exact ⟨Subgroup.mem_top u, fun g hg => hu _ (Subgroup.mem_subgroupOf.mp hg)⟩
  have hcard : Nat.card ↥(B.subgroupOf X) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  rw [hcen, inf_bot_eq, Subgroup.relIndex_bot_left, hcard, hfix] at key
  exact absurd key (not_le.mpr hstrong)

theorem d125_general {G₂ T M₂ U : Subgroup G} (hmp : MinParabolic G₂ T M₂) (hUT : U ≤ T)
    (hUe : IsElemAbelian 2 U) : D15Proof.D125 G₂ T U := by
  intro L N hstep hnc A hAT hAe hquad
  exact relIndex_le_of_minParabolic hmp hUT hUe hstep hnc (hAT.trans hmp.isSylow.1)
    (hmp.isSylow.2.1.to_le hAT) hquad

end CFSG.Quasithin.MS09

end
