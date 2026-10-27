module

public import CFSG.Quasithin.EmptyFaithful.S153D0Alt
public import CFSG.Quasithin.EmptyFaithful.S153D0Quot
public import CFSG.Quasithin.EmptyFaithful.S153D0Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Sgp153_le_normalizer_K (h : Hyp153 G T Mc M) :
    Sgp153 T V₁ ≤ Subgroup.normalizer
      ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) : Subgroup G) : Set G) := fun _ hg =>
  A4.mem_normalizer_of_conj_mem fun k hk =>
    ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M (h.T_le hg.1)) k).mp hk.1,
      conj_mem_centralizer hg.2 hk.2⟩

theorem Sgp153_le_normalizer_Yplus (h : Hyp153 G T Mc M) :
    Sgp153 T V₁ ≤ Subgroup.normalizer
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) : Set G) :=
  (Sgp153_le_normalizer_K h).trans (normalizer_le_normalizer_oTwoUpper _)

theorem comm_mem_pCoreOf_of_mem_R (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {r y : G} (hrR : r ∈ pCoreOf 2 (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔
      Sgp153 T V₁)) (hrS : r ∈ Sgp153 T V₁)
    (hy : y ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) :
    y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M := by
  set Yp : Subgroup G := oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) with hYp
  have hYpY : Yp ≤ Y153 Mc M := (oTwoUpper_le _).trans inf_le_left
  have hyN : y ∈ Subgroup.normalizer
      ((pCoreOf 2 (Yp ⊔ Sgp153 T V₁) : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy)
  have hd1 : y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 (Yp ⊔ Sgp153 T V₁) := by
    have h1 : y * r * y⁻¹ ∈ pCoreOf 2 (Yp ⊔ Sgp153 T V₁) :=
      (Subgroup.mem_normalizer_iff.mp hyN r).mp hrR
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hrR)
  have hd2 : y * r * y⁻¹ * r⁻¹ ∈ Yp := by
    have hrN := Sgp153_le_normalizer_Yplus (V₁ := V₁) h hrS
    have h1 : r * y⁻¹ * r⁻¹ ∈ Yp :=
      (Subgroup.mem_normalizer_iff.mp hrN _).mp (Subgroup.inv_mem _ hy)
    have e : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy h1
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (Yp ⊔ Sgp153 T V₁)) ⟨_, hd1⟩
  have hk' : (y * r * y⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact mem_of_cube_of_pow_two_pow (pCoreOf 2 M)
    (Hyp153.cube_mem_pCoreOf_M h113 h (hYpY hd2)) hk'

theorem star_commute_of_mem_R (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {r : G} (hrR : r ∈ pCoreOf 2 (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔
      Sgp153 T V₁)) (hrS : r ∈ Sgp153 T V₁) {u : OTwoQuot M}
    (hu : u ∈ imageOTwoQuot M (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))) :
    starOf h r hrS.1 * u = u * starOf h r hrS.1 := by
  obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  have hcomm := comm_mem_pCoreOf_of_mem_R h113 h hrR hrS hyY
  have hrM : r ∈ M := h.T_le hrS.1
  refine (mk_commute_iff (⟨r, hrM⟩ : ↥M) ⟨y, hyM⟩).2 ?_
  have e : ((⟨r, hrM⟩ * ⟨y, hyM⟩ * ⟨r, hrM⟩⁻¹ * ⟨y, hyM⟩⁻¹ : ↥M) : G) = (y * r * y⁻¹ * r⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  exact Subgroup.inv_mem _ hcomm

theorem nine_dvd_card_quot (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {X : Subgroup G}
    (hXY : X ≤ Y153 Mc M) (hr : CFSG.Open.pRank 3 X = 2) :
    9 ∣ Nat.card ↥(imageOTwoQuot M X) := by
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hXY
  rw [← Nat.card_congr φ.toEquiv]
  rcases h.struct_of_le h113 hXY hr with he | hp
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))]
    simp
  · rw [hp.2.1]
    exact ⟨3, by norm_num⟩

theorem R_le_of_case_two (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t)
    (hr : CFSG.Open.pRank 3 (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) = 2)
    (hsyl : IsSylowTwoOf (Sgp153 T V₁)
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁)) :
    pCoreOf 2 (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) ≤
      T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  classical
  set K : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK
  have hKY : K ≤ Y153 Mc M := inf_le_left
  have hYpY : oTwoUpper K ≤ Y153 Mc M := (oTwoUpper_le _).trans hKY
  obtain ⟨A, B, hc⟩ := exists_starCoords h113 h D
  set Ys : Subgroup (OTwoQuot M) := imageOTwoQuot M (Y153 Mc M) with hYs
  have hAK : A ∈ imageOTwoQuot M K := hc.A_mem
  have hAY : A ∈ Ys := imageOTwoQuot_mono hKY hAK
  have hBY : B ∈ Ys := hc.B_mem
  have hYpK : imageOTwoQuot M (oTwoUpper K) = imageOTwoQuot M K :=
    imageOTwoQuot_oTwoUpper_eq h113 h hKY
  rcases Zstar_structure h113 h hAY hBY hc.comm_mem hc.gen with hZ | ⟨hz1, -⟩
  ·
    exfalso
    have h9 := nine_dvd_card_quot h113 h hYpY hr
    have hle : imageOTwoQuot M (oTwoUpper K) ≤ Subgroup.zpowers A := by
      intro u hu
      rw [hYpK] at hu
      obtain ⟨j, c, hcZ, rfl⟩ := hc.genK u hu
      rw [hZ, Subgroup.mem_bot] at hcZ
      rw [hcZ, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers A) j
    have h3 : Nat.card ↥(imageOTwoQuot M (oTwoUpper K)) ∣ 3 := by
      refine (Subgroup.card_dvd_of_le hle).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (star_cube h113 h hAY)
    have := h9.trans h3
    omega
  ·
    intro r hrR
    have hrS : r ∈ Sgp153 T V₁ := pCoreOf_le_of_isSylowTwoOf hsyl hrR
    have hrT : r ∈ T := hrS.1
    have hρcomm : ∀ u ∈ imageOTwoQuot M (oTwoUpper K),
        starOf h r hrT * u = u * starOf h r hrT := fun u hu =>
      star_commute_of_mem_R h113 h hrR hrS hu
    have hzK : ⁅A, B⁆ ∈ imageOTwoQuot M K := Zstar_le_imageK h D hc.comm_mem
    have hρA : starOf h r hrT * A * (starOf h r hrT)⁻¹ = A := by
      have := hρcomm A (hYpK ▸ hAK)
      rw [this]
      group
    have hρz : starOf h r hrT * ⁅A, B⁆ * (starOf h r hrT)⁻¹ = ⁅A, B⁆ := by
      have := hρcomm ⁅A, B⁆ (hYpK ▸ hzK)
      rw [this]
      group
    obtain ⟨e₁, e₂, he₁, he₂, ⟨⟨cA, hcA, hA⟩, ⟨cB, hcB, hB⟩⟩, hconc⟩ := hc.sign r hrS
    have hAZ : A ∉ ZstarOf h := fun hA' => hc.A_ne ((MonoidHom.mem_ker).1 hA'.1)
    have hsign := sign_eq_one he₁ he₂ (star_cube h113 h hAY)
      (star_cube h113 h (hc.comm_mem.2)) hz1 hAZ hcA (Zstar_central h113 h hcB hAY)
      (Zstar_central h113 h hc.comm_mem hBY) hA hB hρA hρz
    exact ⟨hrT, hconc hsign.1 hsign.2⟩

end S153D

end CFSG.Quasithin
