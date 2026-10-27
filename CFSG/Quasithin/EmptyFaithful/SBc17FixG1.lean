module

public import CFSG.Quasithin.EmptyFaithful.SBc16GCard
public import CFSG.Quasithin.EmptyFaithful.SBc16GElt
public import CFSG.Quasithin.EmptyFaithful.SBc16GApply
public import CFSG.Quasithin.EmptyFaithful.SBc16F
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.SBc13Pair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

section Gen

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap3Fix (T K₁ K₂ : Subgroup G) : Prop :=
  ∀ x ∈ mcOf T, x ∈ Subgroup.normalizer (K₂ : Set G) → x ∈ Subgroup.normalizer (K₁ : Set G)

theorem gap3Fix_of_gap3Pair {T M H H₁ H₂ K₁ K₂ : Subgroup G} {s : G} (S : Setting146 G T M)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) (hgap : Gap3Pair T K₁ K₂) : Gap3Fix T K₁ K₂ := fun _ hx hxN =>
  CosetGeom.mem_normalizer_of_conjSub_eq
    (SBc13.conjSub_K₁_eq_of_conjSub_K₂_eq S hset hgap hx (conjSub_eq_of_mem_normalizer hxN))

theorem mem_normalizer_of_conjSub_le_sup {O X : Subgroup G} {y : G} (hO2 : IsPGroup 2 O)
    (hON : O ≤ Subgroup.normalizer (X : Set G)) (hperf : oTwoUpper X = X)
    (hle : conjSub y X ≤ O ⊔ X) : y ∈ Subgroup.normalizer (X : Set G) := by
  have hRN : O ⊔ X ≤ Subgroup.normalizer (X : Set G) := sup_le hON Subgroup.le_normalizer
  have hOup : oTwoUpper (O ⊔ X) ≤ X :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hRN) hO2 le_sup_left
      (by rw [sup_comm])
  have hperf' : oTwoUpper (conjSub y X) = conjSub y X := by
    rw [oTwoUpper_conjSub_P, hperf]
  have hle' : conjSub y X ≤ X :=
    calc conjSub y X = oTwoUpper (conjSub y X) := hperf'.symm
      _ ≤ oTwoUpper (O ⊔ X) := oTwoUpper_mono hle
      _ ≤ X := hOup
  exact CosetGeom.mem_normalizer_of_conjSub_eq
    (Subgroup.eq_of_le_of_card_ge hle' (by rw [SBc13.card_conjSub']))

theorem map_actHom_eq_iff {K X : Subgroup G} (hXK : X ≤ K)
    (hON : pCoreOf 2 K ≤ Subgroup.normalizer (X : Set G)) (hperf : oTwoUpper X = X) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    (imageOTwoQuot K X).map (SBc16.actHom K ⟨y, hy⟩).toMonoidHom = imageOTwoQuot K X ↔
      y ∈ Subgroup.normalizer (X : Set G) := by
  constructor
  · intro h
    have h1 : imageOTwoQuot K (conjSub y X) = imageOTwoQuot K X := by
      rw [← SBc16.map_actHom_imageOTwoQuot K hy hXK]
      exact h
    refine mem_normalizer_of_conjSub_le_sup (pCoreOf_isPGroup 2 K) hON hperf ?_
    intro z hz
    have hzX : y⁻¹ * z * y ∈ X := mem_conjSub.mp hz
    have hzK : z ∈ K := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * z * y)).mp (hXK hzX)
      have e : y * (y⁻¹ * z * y) * y⁻¹ = z := by group
      rwa [e] at h2
    have hzimg : (QuotientGroup.mk ⟨z, hzK⟩ : OTwoQuot K) ∈ imageOTwoQuot K (conjSub y X) :=
      mem_imageOTwoQuot_iff.mpr ⟨z, hzK, hz, rfl⟩
    rw [h1] at hzimg
    obtain ⟨x, hxK, hxX, hxz⟩ := mem_imageOTwoQuot_iff.mp hzimg
    have h3 : (⟨x, hxK⟩ : ↥K)⁻¹ * ⟨z, hzK⟩ ∈ CFSG.Open.pCore 2 ↥K := QuotientGroup.eq.mp hxz
    have h4 : x⁻¹ * z ∈ pCoreOf 2 K := (SBc16.mem_pCore_iff_coe K _).mp h3
    have e : z = x * (x⁻¹ * z) := by group
    rw [e]
    exact (pCoreOf 2 K ⊔ X).mul_mem (Subgroup.mem_sup_right hxX) (Subgroup.mem_sup_left h4)
  · intro h
    rw [SBc16.map_actHom_imageOTwoQuot K hy hXK, conjSub_eq_of_mem_normalizer h]

end Gen

section Data

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem mcOf_le_normalizer_oTwoUpper
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) :
    mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have := le_normalizer_conjClosure (oTwoUpper H) (mcOf T)
  rwa [hCz] at this

@[expose] noncomputable def psiHom (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ↥(mcOf T) →* MulAut (OTwoQuot (oTwoUpper H)) :=
  (SBc16.actHom (oTwoUpper H)).comp (Subgroup.inclusion hKG)

omit [Finite G] in
theorem psiHom_apply (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) (y : G)
    (hy : y ∈ mcOf T) : psiHom hKG ⟨y, hy⟩ = SBc16.actHom (oTwoUpper H) ⟨y, hKG hy⟩ := rfl

theorem exists_sigma_tau (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∃ σ τ : MulAut (OTwoQuot (oTwoUpper H)),
      σ ∈ (psiHom hKG).range ∧ τ ∈ (psiHom hKG).range ∧
      (∀ x ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂), σ x = x) ∧
      (∀ x ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁), σ x = x⁻¹) ∧
      (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)).map τ.toMonoidHom =
        imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂) ∧
      (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)).map τ.toMonoidHom =
        imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁) := by
  subst hp5
  have hTH : T ≤ H := hred.isHTM.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hTH.trans hHG
  obtain ⟨-, -, hidx₁⟩ := hdec.isSylowTwoOf_inf_H₁ S hred
  obtain ⟨s, hs, hsQ⟩ := exists_mem_not_mem_of_relIndex_two hidx₁
  have hsG : s ∈ mcOf T := hTG hs.1.1
  have hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hKG hsG
  have hss : s * s ∈ pCoreOf 2 H := by
    have hs'Q : s⁻¹ ∉ pCoreOf 2 H := fun hh => hsQ (by simpa using (pCoreOf 2 H).inv_mem hh)
    have := mul_inv_mem_of_relIndex_two hidx₁ hs (((T ⊓ H₀) ⊓ H₁).inv_mem hs) hsQ hs'Q
    simpa using this
  have htG : t ∈ mcOf T := hTG hdec.t_mem
  have htN : t ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hKG htG
  exact ⟨SBc16.actHom (oTwoUpper H) ⟨s, hsN⟩, SBc16.actHom (oTwoUpper H) ⟨t, htN⟩,
    ⟨⟨s, hsG⟩, rfl⟩, ⟨⟨t, htG⟩, rfl⟩, SBc16.actHom_fix_V₂ hdec hs.2 hsN,
    SBc16.actHom_inv_V₁ ⟨2, by norm_num⟩ hdec hs.2 hss hsQ hsN, SBc16.map_V₁ hdec htN,
    SBc16.map_V₂ hdec htN⟩

theorem noFive_range_of_relIndex_two (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) (hidx : H₀.relIndex H = 2) :
    ∀ α ∈ (psiHom hKG).range, orderOf α ≠ 5 := by
  obtain ⟨σ, τ, hσA, hτA, hσ₂, hσ₁, hτ₁, hτ₂⟩ := exists_sigma_tau S hp5 hred hdec hKG
  subst hp5
  have hTH : T ≤ H := hred.isHTM.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hTH.trans hHG
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hred.isHTM
  have hker : ∀ q : ↥(mcOf T), (q : G) ∈ pCoreOf 2 H → psiHom hKG q = 1 := by
    intro q hq
    obtain ⟨q, hqG⟩ := q
    rw [psiHom_apply]
    refine (SBc16.actHom_eq_one_iff _ _).mpr fun k hk => ?_
    refine (SBc16.mem_pCoreOf_oTwoUpper_iff H).mpr ⟨?_, ?_⟩
    · exact (oTwoUpper H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hKG hqG) k).mp hk)
        ((oTwoUpper H).inv_mem hk)
    · have hkN := le_normalizer_pCoreOf 2 H (oTwoUpper_le H hk)
      have h1 := (Subgroup.mem_normalizer_iff.mp hkN q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
      have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 H).mul_mem hq h1
  have h16 : ¬ 16 ∣ Nat.card (psiHom hKG).range :=
    SBc16.not_sixteen_dvd_card_range (psiHom hKG) hTsyl (hQT.trans hTG) hker
      (SBc16.card_T_eq S rfl hred hdec hidx)
  exact SBc16.noFiveD8_apply SBc16.noFiveD8 (V := OTwoQuot (oTwoUpper H))
    (SBc16.mul_comm_OTwoQuot_K S rfl hred hdec) (SBc16.card_OTwoQuot_K S rfl hred hdec)
    (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂))
    (SBc16.card_imageOTwoQuot_K hred hdec) (SBc16.card_imageOTwoQuot_K hred hdec.swap)
    (disjoint_iff.mp (SBc16.disjoint_imageOTwoQuot_K hdec)) (SBc16.imageOTwoQuot_sup_eq_top S hred hdec)
    (psiHom hKG).range σ τ hσA hτA hσ₂ hσ₁ hτ₁ hτ₂ h16

end Data

end SBc17

end CFSG.Quasithin
