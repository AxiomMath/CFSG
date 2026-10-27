module

public import CFSG.Quasithin.EmptyFaithful.S146zUACore
public import CFSG.Quasithin.EmptyFaithful.S146zUAOdd
public import CFSG.Quasithin.EmptyFaithful.S146zUAMod

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.C1Pack CFSG.Quasithin.S146zU.UA
open scoped Pointwise

theorem closing_of_decomp {G : Type} [Group G] [Finite G] {T M H PQ H₀ H₁ H₂ : Subgroup G} {t : G}
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5) (hdec : IsDecP T M H 5 H₀ H₁ H₂ t)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hK₂ : conjSub s K₁ ∈ cComp (mcOf T))
    (hsT : s ∈ T) (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hD : ⁅⁅uOfL22 T M, K₁⁆, conjSub s K₁⁆ ≤ quasithinOmegaOneCenter T) :
    ∃ K₁' : Subgroup G, (K₁' = K₁ ∨ K₁' = conjSub s K₁) ∧ oTwoUpper H₁ ≤ K₁' ∧
      oTwoUpper H₂ ≤ conjSub s K₁' ∧
      ⁅uHi T M H H₁, conjSub s K₁'⁆ ≤ quasithinOmegaOneCenter T := by
  classical
  have hG := hypG S
  set K₂ : Subgroup G := conjSub s K₁ with hK₂def
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hsG : s ∈ mcOf T := S.isHTM_mcOf.1.1 hsT
  have hne : K₁ ≠ K₂ := fun h => hsN (CosetGeom.mem_normalizer_of_conjSub_eq h.symm)
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : K₂ ≤ mcOf T := le_of_mem_cComp hK₂
  obtain ⟨hcard₁, hsimple₁⟩ := card_image_eq hK₁ e
  have e₂ : Nonempty (OTwoQuot K₂ ≃* SBc16.L216) := by
    obtain ⟨e₁⟩ := e
    exact ⟨(SBc16.oTwoQuotConjEquiv s K₁).symm.trans e₁⟩
  obtain ⟨hcard₂, -⟩ := card_image_eq hK₂ e₂
  have P : CompPair (mcOf T) K₁ K₂ := CompPair.of_cComp hK₁ hK₂ hne hsimple₁
  have P' : CompPair (mcOf T) K₂ K₁ := P.symm
  obtain ⟨φ₁, hs₁, hker₁⟩ := hdec.exists_phi_gen
  obtain ⟨φ₂, hs₂, hker₂⟩ := hdec.swap.exists_phi_gen
  obtain ⟨x, y, hxH₁, hyH₂, hφx, hφy, hx5, hy5, hxy, hynot⟩ :=
    exists_commuting_pair (by norm_num : Nat.Prime 5) (by norm_num : (5 : ℕ) ≠ 2) hdec φ₁ hs₁ hker₁
      φ₂ hs₂ hker₂
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hH₁G : H₁ ≤ mcOf T := hH₁H.trans hHG
  have hH₂G : H₂ ≤ mcOf T := hH₂H.trans hHG
  have hxH : x ∈ H := hH₁H hxH₁
  have hyH : y ∈ H := hH₂H hyH₂
  have hxG : x ∈ mcOf T := hHG hxH
  have hyG : y ∈ mcOf T := hHG hyH
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx5)
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy5)
  have hz : oTwoUpper H ≤ K₁ ⊔ K₂ := (le_conjClosure _ _).trans hKz.le
  have hz' : oTwoUpper H ≤ K₂ ⊔ K₁ := by rw [sup_comm]; exact hz
  have hxK : x ∈ K₁ ⊔ K₂ := hz (mem_oTwoUpper_of_odd hxH hxodd)
  have hyK : y ∈ K₁ ⊔ K₂ := hz (mem_oTwoUpper_of_odd hyH hyodd)
  have hmul : (↑(K₁ ⊔ K₂) : Set G) = ↑K₁ * ↑K₂ :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₁ K₂ P.norm_left
  obtain ⟨k₁, hk₁, k₂, hk₂, hkx⟩ : ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, k₁ * k₂ = x := by
    have h' : x ∈ (↑K₁ * ↑K₂ : Set G) := by rw [← hmul]; exact hxK
    exact Set.mem_mul.mp h'
  obtain ⟨l₁, hl₁, l₂, hl₂, hly⟩ : ∃ l₁ ∈ K₁, ∃ l₂ ∈ K₂, l₁ * l₂ = y := by
    have h' : y ∈ (↑K₁ * ↑K₂ : Set G) := by rw [← hmul]; exact hyK
    exact Set.mem_mul.mp h'
  have hk₁G : k₁ ∈ mcOf T := hK₁G hk₁
  have hk₂G : k₂ ∈ mcOf T := hK₂G hk₂
  have hl₁G : l₁ ∈ mcOf T := hK₁G hl₁
  have hl₂G : l₂ ∈ mcOf T := hK₂G hl₂
  obtain ⟨n₁, hn₁def⟩ : ∃ n : OTwoQuot (mcOf T), n = qPi (mcOf T) ⟨k₁, hk₁G⟩ := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂def⟩ : ∃ n : OTwoQuot (mcOf T), n = qPi (mcOf T) ⟨k₂, hk₂G⟩ := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁def⟩ : ∃ n : OTwoQuot (mcOf T), n = qPi (mcOf T) ⟨l₁, hl₁G⟩ := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂def⟩ : ∃ n : OTwoQuot (mcOf T), n = qPi (mcOf T) ⟨l₂, hl₂G⟩ := ⟨_, rfl⟩
  have hn₁ : n₁ ∈ imageOTwoQuot (mcOf T) K₁ := by
    rw [hn₁def]; exact qPi_mem_image hk₁ hk₁G
  have hn₂ : n₂ ∈ imageOTwoQuot (mcOf T) K₂ := by
    rw [hn₂def]; exact qPi_mem_image hk₂ hk₂G
  have hm₁ : m₁ ∈ imageOTwoQuot (mcOf T) K₁ := by
    rw [hm₁def]; exact qPi_mem_image hl₁ hl₁G
  have hm₂ : m₂ ∈ imageOTwoQuot (mcOf T) K₂ := by
    rw [hm₂def]; exact qPi_mem_image hl₂ hl₂G
  have hπx : qPi (mcOf T) ⟨x, hxG⟩ = n₁ * n₂ := by
    have h' : (⟨x, hxG⟩ : ↥(mcOf T)) = ⟨k₁, hk₁G⟩ * ⟨k₂, hk₂G⟩ := Subtype.ext hkx.symm
    rw [h', map_mul, hn₁def, hn₂def]
  have hπy : qPi (mcOf T) ⟨y, hyG⟩ = m₁ * m₂ := by
    have h' : (⟨y, hyG⟩ : ↥(mcOf T)) = ⟨l₁, hl₁G⟩ * ⟨l₂, hl₂G⟩ := Subtype.ext hly.symm
    rw [h', map_mul, hm₁def, hm₂def]
  have hpow5 : ∀ {z : G} (hz : z ∈ mcOf T), z ^ 5 = 1 → qPi (mcOf T) ⟨z, hz⟩ ^ 5 = 1 := by
    intro z hz h5
    rw [← qPi_pow hz 5]
    have h' : (⟨z ^ 5, (mcOf T).pow_mem hz 5⟩ : ↥(mcOf T)) = 1 := Subtype.ext h5
    rw [h', map_one]
  have hπx5 : (n₁ * n₂) ^ 5 = 1 := by rw [← hπx]; exact hpow5 hxG hx5
  have hπy5 : (m₁ * m₂) ^ 5 = 1 := by rw [← hπy]; exact hpow5 hyG hy5
  obtain ⟨hn₁5, hn₂5⟩ := comp_pow_eq_one P.comm P.disj hn₁ hn₂ hπx5
  obtain ⟨hm₁5, hm₂5⟩ := comp_pow_eq_one P.comm P.disj hm₁ hm₂ hπy5
  have hπxy : qPi (mcOf T) ⟨x, hxG⟩ * qPi (mcOf T) ⟨y, hyG⟩ =
      qPi (mcOf T) ⟨y, hyG⟩ * qPi (mcOf T) ⟨x, hxG⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg (qPi (mcOf T)) (Subtype.ext hxy)
  rw [hπx, hπy] at hπxy
  obtain ⟨hnm₁, hnm₂⟩ := comp_comm_of_comm P.comm P.disj hn₁ hm₁ hn₂ hm₂ hπxy
  have hrot_ne : ∀ {Hi : Subgroup G} (φ : ↥Hi →* DihedralGroup 5) {z : G} (hz : z ∈ Hi),
      φ ⟨z, hz⟩ = DihedralGroup.r 1 → z ≠ 1 := by
    intro Hi φ z hz hφz hz1
    have h1 : φ ⟨z, hz⟩ = 1 := by
      have h' : (⟨z, hz⟩ : ↥Hi) = 1 := Subtype.ext hz1
      rw [h', map_one]
    rw [hφz] at h1
    have h2 : (DihedralGroup.r (1 : ZMod 5)) = DihedralGroup.r 0 := h1
    exact (by decide : (1 : ZMod 5) ≠ 0) (DihedralGroup.r.inj h2)
  have hπx1 : qPi (mcOf T) ⟨x, hxG⟩ ≠ 1 := fun h1 =>
    hrot_ne φ₁ hxH₁ hφx (eq_one_of_qPi_eq_one hxG h1 (by decide) hx5)
  have hY : ∀ v : UMod hG, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hcomm : ∀ a ∈ Lof hG K₁, ∀ b ∈ Lof hG K₂, a * b = b * a := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_mul, P.comm n hn m hm]
  have hD₁ : commV (Lof hG K₁) ≤ fixV (Lof hG K₂) := commV_Lof_le_fixV hG hK₁G hK₂G hD
  have h5₁ := Lof_h5 hG hcard₁
  have h5₂ := Lof_h5 hG hcard₂
  obtain ⟨a₁, ha₁def⟩ : ∃ a, a = rhoBar hG n₁ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂def⟩ : ∃ a, a = rhoBar hG n₂ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁def⟩ : ∃ a, a = rhoBar hG m₁ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂def⟩ : ∃ a, a = rhoBar hG m₂ := ⟨_, rfl⟩
  have ha₁ : a₁ ∈ Lof hG K₁ := ⟨n₁, hn₁, ha₁def.symm⟩
  have ha₂ : a₂ ∈ Lof hG K₂ := ⟨n₂, hn₂, ha₂def.symm⟩
  have hb₁ : b₁ ∈ Lof hG K₁ := ⟨m₁, hm₁, hb₁def.symm⟩
  have hb₂ : b₂ ∈ Lof hG K₂ := ⟨m₂, hm₂, hb₂def.symm⟩
  have ha₁5 : a₁ ^ 5 = 1 := by rw [ha₁def, ← map_pow, hn₁5, map_one]
  have ha₂5 : a₂ ^ 5 = 1 := by rw [ha₂def, ← map_pow, hn₂5, map_one]
  have hb₁5 : b₁ ^ 5 = 1 := by rw [hb₁def, ← map_pow, hm₁5, map_one]
  have hb₂5 : b₂ ^ 5 = 1 := by rw [hb₂def, ← map_pow, hm₂5, map_one]
  have hab₁ : a₁ * b₁ = b₁ * a₁ := by rw [ha₁def, hb₁def, ← map_mul, ← map_mul, hnm₁]
  have hab₂ : a₂ * b₂ = b₂ * a₂ := by rw [ha₂def, hb₂def, ← map_mul, ← map_mul, hnm₂]
  have hax : a₁ * a₂ = rhoBar hG (qPi (mcOf T) ⟨x, hxG⟩) := by
    rw [ha₁def, ha₂def, ← map_mul, hπx]
  have hby : b₁ * b₂ = rhoBar hG (qPi (mcOf T) ⟨y, hyG⟩) := by
    rw [hb₁def, hb₂def, ← map_mul, hπy]
  have hx : a₁ * a₂ ≠ 1 := by
    rw [hax]
    intro h1
    exact hπx1 (rhoBar_injective hG (h1.trans (map_one _).symm))
  have hy : b₁ * b₂ ∉ Subgroup.zpowers (a₁ * a₂) := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [hax, hby, ← map_zpow] at hi
    have hpi : qPi (mcOf T) ⟨x, hxG⟩ ^ i = qPi (mcOf T) ⟨y, hyG⟩ := rhoBar_injective hG hi
    have hz1 : (x ^ i)⁻¹ * y ∈ mcOf T :=
      (mcOf T).mul_mem ((mcOf T).inv_mem ((mcOf T).zpow_mem hxG i)) hyG
    have hπz : qPi (mcOf T) ⟨(x ^ i)⁻¹ * y, hz1⟩ = 1 := by
      have e' : (⟨(x ^ i)⁻¹ * y, hz1⟩ : ↥(mcOf T)) = (⟨x, hxG⟩ ^ i)⁻¹ * ⟨y, hyG⟩ := by
        apply Subtype.ext
        simp
      rw [e', map_mul, map_inv, map_zpow, hpi, inv_mul_cancel]
    have hxi5 : (x ^ i) ^ 5 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5, one_zpow]
    have hz5 : ((x ^ i)⁻¹ * y) ^ 5 = 1 := by
      have hc : Commute ((x ^ i)⁻¹) y := ((show Commute x y from hxy).zpow_left i).inv_left
      rw [hc.mul_pow, inv_pow, hxi5, inv_one, hy5, one_mul]
    have hz0 : (x ^ i)⁻¹ * y = 1 := eq_one_of_qPi_eq_one hz1 hπz (by decide) hz5
    exact hynot (Subgroup.mem_zpowers_iff.mpr ⟨i, (inv_mul_eq_one.mp hz0)⟩)
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  have hU2 : uHi T M H H₂ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₂H).trans (conjClosure_mono le_rfl hHG)
  have hX₁ne : Wsub hG (uHi T M H H₁) ≠ ⊥ := Wsub_ne_bot hG S hred hdec
  have hX₂ne : Wsub hG (uHi T M H H₂) ≠ ⊥ := Wsub_ne_bot hG S hred hdec.swap
  have hax' : a₁ * a₂ = rhoH hG ⟨x, hxG⟩ := hax
  have hby' : b₁ * b₂ = rhoH hG ⟨y, hyG⟩ := hby
  have hxX₂ : ∀ w ∈ Wsub hG (uHi T M H H₂), (a₁ * a₂) w = w := by
    intro w hw
    have hfix := (Wsub_le_fixV_iff hG hU2 hH₁G).mpr hdec.cent₂ hw
    rw [hax']
    exact (mem_fixV.mp hfix) (rhoH hG ⟨x, hxG⟩) ((mem_Lof hG).mpr ⟨⟨x, hxG⟩, hxH₁, rfl⟩)
  have hyX₁ : ∀ w ∈ Wsub hG (uHi T M H H₁), (b₁ * b₂) w = w := by
    intro w hw
    have hfix := (Wsub_le_fixV_iff hG hU1 hH₂G).mpr hdec.cent₁ hw
    rw [hby']
    exact (mem_fixV.mp hfix) (rhoH hG ⟨y, hyG⟩) ((mem_Lof hG).mpr ⟨⟨y, hyG⟩, hyH₂, rfl⟩)
  have hX₂y : ∀ w ∈ Wsub hG (uHi T M H H₂),
      ∃ u ∈ Wsub hG (uHi T M H H₂), w = (b₁ * b₂) u * u⁻¹ := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ :=
      exists_eq_mul_inv hG S hred hdec.swap φ₂ hker₂ (a := ⟨y, hyH₂⟩) hφy hyG w hw
    exact ⟨u, hu, by rw [hby']; exact hwu⟩
  have hX₁x : ∀ w ∈ Wsub hG (uHi T M H H₁),
      ∃ u ∈ Wsub hG (uHi T M H H₁), w = (a₁ * a₂) u * u⁻¹ := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ :=
      exists_eq_mul_inv hG S hred hdec φ₁ hker₁ (a := ⟨x, hxH₁⟩) hφx hxG w hw
    exact ⟨u, hu, by rw [hax']; exact hwu⟩
  have hcore := core hY hcomm hD₁ h5₁ h5₂ ha₁ hb₁ ha₂ hb₂ ha₁5 hb₁5 ha₂5 hb₂5 hab₁ hab₂ hx hy
    hX₁ne hX₂ne hxX₂ hyX₁ hX₂y hX₁x
  rcases hcore with ⟨ha₂1, hb₁1, hX₁c, -⟩ | ⟨ha₁1, hb₂1, hX₁c, -⟩
  ·
    have hn₂1 : n₂ = 1 :=
      rhoBar_injective hG (by rw [map_one, ← ha₂def, ha₂1])
    have hm₁1 : m₁ = 1 :=
      rhoBar_injective hG (by rw [map_one, ← hb₁def, hb₁1])
    have hxA : qPi (mcOf T) ⟨x, hxG⟩ ∈ imageOTwoQuot (mcOf T) K₁ := by
      rw [hπx, hn₂1, mul_one]
      exact hn₁
    have hyB : qPi (mcOf T) ⟨y, hyG⟩ ∈ imageOTwoQuot (mcOf T) K₂ := by
      rw [hπy, hm₁1, one_mul]
      exact hm₂
    have h1 : oTwoUpper H₁ ≤ K₁ := oTwoUpper_le_of_rotation P hH₁H hHG hz φ₁ hker₁ hxH₁ hφx hxA
    have h2 : oTwoUpper H₂ ≤ K₂ := oTwoUpper_le_of_rotation P' hH₂H hHG hz' φ₂ hker₂ hyH₂ hφy hyB
    have h3 : ⁅uHi T M H H₁, K₂⁆ ≤ quasithinOmegaOneCenter T :=
      (Wsub_le_fixV_iff hG hU1 hK₂G).mp (hX₁c.trans hD₁)
    exact ⟨K₁, Or.inl rfl, h1, h2, h3⟩
  ·
    have hn₁1 : n₁ = 1 :=
      rhoBar_injective hG (by rw [map_one, ← ha₁def, ha₁1])
    have hm₂1 : m₂ = 1 :=
      rhoBar_injective hG (by rw [map_one, ← hb₂def, hb₂1])
    have hxB : qPi (mcOf T) ⟨x, hxG⟩ ∈ imageOTwoQuot (mcOf T) K₂ := by
      rw [hπx, hn₁1, one_mul]
      exact hn₂
    have hyA : qPi (mcOf T) ⟨y, hyG⟩ ∈ imageOTwoQuot (mcOf T) K₁ := by
      rw [hπy, hm₂1, mul_one]
      exact hm₁
    have h1 : oTwoUpper H₁ ≤ K₂ := oTwoUpper_le_of_rotation P' hH₁H hHG hz' φ₁ hker₁ hxH₁ hφx hxB
    have h2 : oTwoUpper H₂ ≤ K₁ := oTwoUpper_le_of_rotation P hH₂H hHG hz φ₂ hker₂ hyH₂ hφy hyA
    have hD₂ : commV (Lof hG K₂) ≤ fixV (Lof hG K₁) := commV_le_fixV_symm hcomm hD₁
    have h3 : ⁅uHi T M H H₁, K₁⁆ ≤ quasithinOmegaOneCenter T :=
      (Wsub_le_fixV_iff hG hU1 hK₁G).mp (hX₁c.trans hD₂)
    have hss : conjSub s K₂ = K₁ :=
      SBc16.conjSub_conjSub_eq_of_mem_cComp hK₁ hK₂ hsG hsN
        (by rw [← hKz]; exact le_normalizer_conjClosure _ _)
    exact ⟨K₂, Or.inr rfl, h1, by rw [hss]; exact h2, by rw [hss]; exact h3⟩

end CFSG.Quasithin.S146zU
