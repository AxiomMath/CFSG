module

public import CFSG.Quasithin.EmptyFaithful.S152Y26
public import CFSG.Quasithin.EmptyFaithful.S152Y10
public import CFSG.Quasithin.EmptyFaithful.S152Y25

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem inf_pCoreOf_le_pCoreOf {X : Subgroup G} (hXM : X ≤ M) :
    X ⊓ pCoreOf 2 M ≤ pCoreOf 2 X := by
  refine BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, BorelTits.le_normalizer_pCoreOf 2 M (hXM hx)⟩
  · exact (BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right

theorem eq_one_of_odd_two_power {B : Type*} [Group B] {x : B} (ho : Odd (orderOf x)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    rw [hj, pow_succ] at ho
    exact (Nat.not_even_iff_odd.mpr ho) (by simp)

theorem not_le_Mc {Y₁ : Subgroup G}
    (hRY : rcOf Mc M ≤ Subgroup.normalizer (Y₁ : Set G))
    (hodd : ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u))
    (hact : ∃ ρ ∈ Rcs Mc M, ∃ a ∈ imageOTwoQuot M Y₁, ρ * a * ρ⁻¹ ≠ a) : ¬ Y₁ ≤ Mc := by
  intro hle
  obtain ⟨ρ, hρ, a, ha, hne⟩ := hact
  obtain ⟨r, hrM, hrR, rfl⟩ := mem_imageOTwoQuot_iff.mp hρ
  obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp ha
  apply hne
  have hyMc : y ∈ Mc ⊓ M := ⟨hle hyY, hyM⟩
  have hyN : y ∈ Subgroup.normalizer (rcOf Mc M : Set G) :=
    BorelTits.le_normalizer_pCoreOf 2 (Mc ⊓ M) hyMc
  have hc1 : y * r * y⁻¹ * r⁻¹ ∈ rcOf Mc M :=
    (rcOf Mc M).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN r).mp hrR) ((rcOf Mc M).inv_mem hrR)
  have hrN : r ∈ Subgroup.normalizer (Y₁ : Set G) := hRY hrR
  have hc2 : y * r * y⁻¹ * r⁻¹ ∈ Y₁ := by
    have : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
    rw [this]
    exact Y₁.mul_mem hyY ((Subgroup.mem_normalizer_iff.mp hrN y⁻¹).mp (Y₁.inv_mem hyY))
  have hcM : y * r * y⁻¹ * r⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hyM hrM) (M.inv_mem hyM)) (M.inv_mem hrM)
  have hmk : (QuotientGroup.mk ⟨y * r * y⁻¹ * r⁻¹, hcM⟩ : OTwoQuot M) = 1 := by
    obtain ⟨k, hk⟩ := (BorelTits.pCoreOf_isPGroup 2 (Mc ⊓ M)) ⟨_, hc1⟩
    have hk' : (y * r * y⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine eq_one_of_odd_two_power (hodd _ (mem_imageOTwoQuot_iff.mpr ⟨_, hcM, hc2, rfl⟩))
      (k := k) ?_
    rw [← QuotientGroup.mk_pow]
    have : (⟨y * r * y⁻¹ * r⁻¹, hcM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext hk'
    rw [this]
    rfl
  have hmk' : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) * QuotientGroup.mk ⟨r, hrM⟩ *
      (QuotientGroup.mk ⟨y, hyM⟩)⁻¹ * (QuotientGroup.mk ⟨r, hrM⟩)⁻¹ = 1 := by
    rw [← hmk]
    rfl
  set u : OTwoQuot M := QuotientGroup.mk ⟨y, hyM⟩
  set v : OTwoQuot M := QuotientGroup.mk ⟨r, hrM⟩
  have h1 : u * v = v * u := by
    calc u * v = (u * v * u⁻¹ * v⁻¹) * v * u := by group
      _ = v * u := by rw [hmk', one_mul]
  calc v * u * v⁻¹ = (u * v) * v⁻¹ := by rw [h1]
    _ = u := by group

section Star

variable (h : Data T Mc M)

include h

theorem imageOTwoQuot_inf_ker_eq_bot {Y₁ : Subgroup G}
    (hc : Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M) :
    imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥ := by
  rw [← imageOTwoQuot_inf_centralizer h, eq_bot_iff]
  intro u hu
  obtain ⟨x, hxM, hxY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  rw [Subgroup.mem_bot]
  exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM⟩).mpr (hc hxY)

theorem odd_orderOf_of_inf_ker_bot {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M) {n : ℕ} (hn : Odd n)
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥)
    (hex : ∀ a ∈ autOn Y₁ (V154 T Mc M), a ^ n = 1) :
    ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u) := by
  intro u hu
  have hπ : piStar h u ∈ autOn Y₁ (V154 T Mc M) := by
    rw [← map_piStar_imageOTwoQuot h hY₁]
    exact ⟨u, hu, rfl⟩
  have h1 : u ^ n ∈ imageOTwoQuot M Y₁ ⊓ (piStar h).ker :=
    ⟨(imageOTwoQuot M Y₁).pow_mem hu n, by
      show (piStar h) (u ^ n) = 1
      rw [map_pow]
      exact hex _ hπ⟩
  rw [hK, Subgroup.mem_bot] at h1
  exact Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one h1)

theorem card_imageOTwoQuot_eq {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M)
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥) :
    Nat.card (imageOTwoQuot M Y₁) = Nat.card (autOn Y₁ (V154 T Mc M)) := by
  let f : ↥(imageOTwoQuot M Y₁) →* MulAut (V154 T Mc M) :=
    (piStar h).comp (imageOTwoQuot M Y₁).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : (u : OTwoQuot M) ∈ imageOTwoQuot M Y₁ ⊓ (piStar h).ker := ⟨u.2, hu⟩
    rw [hK] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hrange : f.range = autOn Y₁ (V154 T Mc M) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_piStar_imageOTwoQuot h hY₁
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

theorem inf_centralizer_eq_pCoreOf {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M)
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥)
    (hodd : ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u)) :
    Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) = pCoreOf 2 Y₁ := by
  apply le_antisymm
  · intro y hy
    have hyM : y ∈ M := hY₁ hy.1
    have hu : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈
        imageOTwoQuot M Y₁ ⊓ (piStar h).ker :=
      ⟨mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hy.1, rfl⟩, (piStar_mk_eq_one_iff h hyM).mpr hy.2⟩
    rw [hK, Subgroup.mem_bot] at hu
    exact inf_pCoreOf_le_pCoreOf hY₁ ⟨hy.1, (mk_eq_one_iff_mem_pCoreOf ⟨y, hyM⟩).mp hu⟩
  · intro z hz
    have hzY : z ∈ Y₁ := BorelTits.pCoreOf_le 2 Y₁ hz
    have hzM : z ∈ M := hY₁ hzY
    refine ⟨hzY, ?_⟩
    obtain ⟨k, hk⟩ := (BorelTits.pCoreOf_isPGroup 2 Y₁) ⟨z, hz⟩
    have hz2 : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmk : (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) = 1 := by
      refine eq_one_of_odd_two_power (hodd _ (mem_imageOTwoQuot_iff.mpr ⟨z, hzM, hzY, rfl⟩))
        (k := k) ?_
      rw [← QuotientGroup.mk_pow]
      have : (⟨z, hzM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext hz2
      rw [this]
      rfl
    exact (piStar_mk_eq_one_iff h hzM).mp (by rw [hmk, map_one])

theorem isUniqueM_of_five (h5 : StageLemma15205) (hs : Setting152 T Mc M) {Y₁ : Subgroup G}
    (hY₁ : Y₁ ≤ M) (hnot : ¬ Y₁ ≤ Mc) : IsUniqueM (Y₁ ⊔ T) M := by
  refine ⟨⟨h.inM.1, sup_le hY₁ h.T_le⟩, fun M' hM' => ?_⟩
  have hT' : InM T M' := ⟨hM'.1, le_sup_right.trans hM'.2⟩
  rcases (h5 G T Mc M hs M').mp hT' with hM | hM
  · exact hM
  · exfalso
    exact hnot (by rw [← hM]; exact le_sup_left.trans hM'.2)

theorem Rcs_sq_eq_one (hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1) :
    ∀ s ∈ Rcs Mc M, s * s = 1 := by
  intro s hs
  have h1 : piStar h (s * s) = 1 := by
    rw [map_mul]
    exact hRe _ (by rw [← h.map_Rcs]; exact ⟨s, hs, rfl⟩)
  have h2 : s * s ∈ Rcs Mc M ⊓ (piStar h).ker := ⟨(Rcs Mc M).mul_mem hs hs, h1⟩
  rw [h.Rcs_inf_ker, Subgroup.mem_bot] at h2
  exact h2

theorem exists_nontrivial_action {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn Y₁ (V154 T Mc M), r * a * r⁻¹ ≠ a) :
    ∃ ρ ∈ Rcs Mc M, ∃ a ∈ imageOTwoQuot M Y₁, ρ * a * ρ⁻¹ ≠ a := by
  obtain ⟨r, hr, a, ha, hne⟩ := hact
  obtain ⟨s, hs, rfl⟩ := h.exists_Rcs_of_mem_autOn hr
  rw [← map_piStar_imageOTwoQuot h hY₁] at ha
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
  refine ⟨s, hs, u, hu, fun heq => hne ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, heq]

theorem quot_dihedral_of_star {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M)
    (hRY : rcOf Mc M ≤ Subgroup.normalizer (Y₁ : Set G)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥)
    (hcard : Nat.card (autOn Y₁ (V154 T Mc M)) = p)
    (hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn Y₁ (V154 T Mc M),
      r * a * r⁻¹ ≠ a) :
    Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* DihedralGroup p) := by
  have hA : Nat.card (imageOTwoQuot M Y₁) = p := (card_imageOTwoQuot_eq h hY₁ hK).trans hcard
  obtain ⟨e⟩ := nonempty_oTwoQuot_sup_dihedral hp2 hA (Rcs_sq_eq_one h hRe)
    (imageOTwoQuot_le_normalizer hRY) (exists_nontrivial_action h hY₁ hact)
  obtain ⟨e'⟩ := nonempty_oTwoQuot_equiv_image (sup_le hY₁ h.rc_le_M)
    (P' := imageOTwoQuot M Y₁ ⊔ Rcs Mc M)
    (imageOTwoQuot_sup hY₁ h.rc_le_M).symm
  exact ⟨e'.trans e⟩

theorem quot_sz_of_star (hFr : S152N2.Frobenius20IsSz2) {Y₁ : Subgroup G} (hY₁ : Y₁ ≤ M)
    (hRY : rcOf Mc M ≤ Subgroup.normalizer (Y₁ : Set G))
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥)
    (hcard : Nat.card (autOn Y₁ (V154 T Mc M)) = 5)
    (hRc : Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) = 4)
    {r : MulAut (V154 T Mc M)} (hr : r ∈ autOn (rcOf Mc M) (V154 T Mc M)) (hr4 : orderOf r = 4)
    (hinv : ∀ a ∈ autOn Y₁ (V154 T Mc M), r ^ 2 * a * (r ^ 2)⁻¹ = a⁻¹) :
    Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0)) := by
  have hA : Nat.card (imageOTwoQuot M Y₁) = 5 := (card_imageOTwoQuot_eq h hY₁ hK).trans hcard
  have hS : Nat.card (Rcs Mc M) = 4 :=
    (card_imageOTwoQuot_eq h h.rc_le_M h.Rcs_inf_ker).trans hRc
  obtain ⟨ρ, hρ, hρr⟩ := h.exists_Rcs_of_mem_autOn hr
  have hρ4 : orderOf ρ = 4 := by
    rw [← hr4, ← hρr]
    refine orderOf_eq_orderOf_iff.mpr fun n => ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [← map_pow, hn, map_one]
    · have h1 : ρ ^ n ∈ Rcs Mc M ⊓ (piStar h).ker :=
        ⟨(Rcs Mc M).pow_mem hρ n, by
          show (piStar h) (ρ ^ n) = 1
          rw [map_pow]
          exact hn⟩
      rw [h.Rcs_inf_ker, Subgroup.mem_bot] at h1
      exact h1
  have hinv' : ∀ a ∈ imageOTwoQuot M Y₁, ρ ^ 2 * a * (ρ ^ 2)⁻¹ = a⁻¹ := by
    intro a ha
    have hρ2 : ρ ^ 2 ∈ Rcs Mc M := (Rcs Mc M).pow_mem hρ 2
    have hmem : ρ ^ 2 * a * (ρ ^ 2)⁻¹ ∈ imageOTwoQuot M Y₁ :=
      (Subgroup.mem_normalizer_iff.mp (imageOTwoQuot_le_normalizer hRY hρ2) a).mp ha
    have hπa : piStar h a ∈ autOn Y₁ (V154 T Mc M) := by
      rw [← map_piStar_imageOTwoQuot h hY₁]
      exact ⟨a, ha, rfl⟩
    have h1 : piStar h (ρ ^ 2 * a * (ρ ^ 2)⁻¹ * a) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_pow, hρr, hinv _ hπa, inv_mul_cancel]
    have h2 : ρ ^ 2 * a * (ρ ^ 2)⁻¹ * a ∈ imageOTwoQuot M Y₁ ⊓ (piStar h).ker :=
      ⟨(imageOTwoQuot M Y₁).mul_mem hmem ha, h1⟩
    rw [hK, Subgroup.mem_bot] at h2
    exact eq_inv_of_mul_eq_one_left h2
  obtain ⟨e⟩ := nonempty_oTwoQuot_sup_sz hFr hA hS hρ hρ4 (imageOTwoQuot_le_normalizer hRY) hinv'
  obtain ⟨e'⟩ := nonempty_oTwoQuot_equiv_image (sup_le hY₁ h.rc_le_M)
    (P' := imageOTwoQuot M Y₁ ⊔ Rcs Mc M)
    (imageOTwoQuot_sup hY₁ h.rc_le_M).symm
  exact ⟨e'.trans e⟩

theorem isY1_of_star {Y₁ : Subgroup G} (hle : Y₁ ≤ yOf152 T Mc M)
    (hTY : T ≤ Subgroup.normalizer (Y₁ : Set G)) (heq : Y₁ = oTwoUpper Y₁)
    (hquot : IsSmallQuot152 (Y₁ ⊔ rcOf Mc M))
    (hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥)
    (hodd : ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u))
    (hunique : IsUniqueM (Y₁ ⊔ T) M) : IsY1 T Mc M Y₁ :=
  ⟨hle, hTY, heq, hquot, inf_centralizer_eq_pCoreOf h (hle.trans h.yOf_le_M) hK hodd, hunique⟩

end Star

end S152Y

end CFSG.Quasithin
