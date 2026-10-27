module

public import CFSG.Quasithin.Background.E2SeventeenCore
public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G]

theorem exists_setting17 {H T M V : Subgroup G} (h : E2.Hyp28 H T M V) (hchar : CharTwo H)
    (hq : qhatOf (autI h.elem H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ))
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G)) (hV16 : Nat.card V = 2 ^ 4)
    (hsolv : Group.IsSolvable H) :
    ∃ (U : Subgroup G) (x z : G), E2.Setting17 H T M V U x z ∧
      E2.IsExtraspecialPlus 2 (E2.dpP H V U z) ∧
      ∃ φ : ↥(E2.dpI V z) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
        φ.ker = (E2.dpP H V U z).subgroupOf (E2.dpI V z) := by
  obtain ⟨U, x, z₀, d₀⟩ := E2.DihedralPair.exists_of_isSolvable h.minParabolic hsolv hchar h.le_T
    h.normal_T h.elem h.not_le_pCoreOf
  obtain ⟨z, -, hp, d⟩ := d₀.exists_prime_orderOf
  have hq' : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H) := hq.symm.le
  obtain ⟨hz3, hZ2, hCA, hext, hIP, φ, hφs, hφk⟩ := d.stage_one hp hV16 hq'
  have hUQ := d.le_pCoreOf hz3 hV16 hZ2 hCA
  exact ⟨U, x, z, ⟨d, h.minParabolic, hsolv, hres, hV16, hq', hz3, hZ2, hCA, hUQ⟩, hext, φ, hφs,
    hφk⟩

theorem perm_eq_one_of_sq : ∀ y : Equiv.Perm (Fin 3), y ^ 2 = 1 →
    (∀ σ : Equiv.Perm (Fin 3), (σ * y * σ⁻¹ * y) ^ 2 = 1) → y = 1 := by decide

theorem perm_sq_of_pow_two_pow {y : Equiv.Perm (Fin 3)} {k : ℕ} (h : y ^ 2 ^ k = 1) :
    y ^ 2 = 1 := by
  have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h3 : orderOf y ∣ 6 := by
    have := orderOf_dvd_natCard y
    rwa [gold_card_perm_fin_three] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h4 : 4 ∣ orderOf y := by
      rw [hj]
      exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ j))
    have : 4 ∣ 6 := h4.trans h3
    omega
  have : orderOf y ∣ 2 := by
    rw [hj]
    exact Nat.pow_dvd_pow 2 hj1
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem sq_eq_one_of_mem_pCoreOf {Y : Subgroup G} (φ : ↥Y →* Equiv.Perm (Fin 3)) {x : G}
    (hx : x ∈ pCoreOf 2 Y) : φ ⟨x, pCoreOf_le 2 Y hx⟩ ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨x, hx⟩
  have hk' : (⟨x, pCoreOf_le 2 Y hx⟩ : ↥Y) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  exact perm_sq_of_pow_two_pow (by rw [← map_pow, hk', map_one])

theorem map_eq_one_of_mem_pCoreOf {Y : Subgroup G} (φ : ↥Y →* Equiv.Perm (Fin 3))
    (hφs : Function.Surjective φ) {x : G} (hx : x ∈ pCoreOf 2 Y) :
    φ ⟨x, pCoreOf_le 2 Y hx⟩ = 1 := by
  refine perm_eq_one_of_sq _ (sq_eq_one_of_mem_pCoreOf φ hx) fun σ => ?_
  obtain ⟨w, rfl⟩ := hφs σ
  have hw : (w : G) * x * (w : G)⁻¹ ∈ pCoreOf 2 Y :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y w.2) x).mp hx
  have hmem : (w : G) * x * (w : G)⁻¹ * x ∈ pCoreOf 2 Y := (pCoreOf 2 Y).mul_mem hw hx
  have := sq_eq_one_of_mem_pCoreOf φ hmem
  have e : φ ⟨(w : G) * x * (w : G)⁻¹ * x, pCoreOf_le 2 Y hmem⟩ =
      φ w * φ ⟨x, pCoreOf_le 2 Y hx⟩ * (φ w)⁻¹ * φ ⟨x, pCoreOf_le 2 Y hx⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rwa [e] at this

variable {H T M V U : Subgroup G} {x z : G}

theorem dpP_le_pCoreOf (s : E2.Setting17 H T M V U x z) : E2.dpP H V U z ≤ pCoreOf 2 H := by
  refine sup_le s.UQ ?_
  rw [s.dp.Aeq]
  have h1 : cjSub z U ≤ cjSub z (pCoreOf 2 H) := cjSub_mono s.UQ
  rwa [cjSub_eq_of_mem_normalizer (s.QN s.dp.zH)] at h1

theorem dpP_eq_pCoreOf (s : E2.Setting17 H T M V U x z) (φ : ↥(E2.dpI V z) →* Equiv.Perm (Fin 3))
    (hφs : Function.Surjective φ) (hφk : φ.ker = (E2.dpP H V U z).subgroupOf (E2.dpI V z)) :
    E2.dpP H V U z = pCoreOf 2 (E2.dpI V z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPI : E2.dpP H V U z ≤ E2.dpI V z := s.dp.PR.trans inf_le_left
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 hPI s.dp.IP
      ((pCoreOf_isPGroup 2 H).to_le (dpP_le_pCoreOf s))
  · intro g hg
    have h1 := map_eq_one_of_mem_pCoreOf φ hφs hg
    have h2 : (⟨g, pCoreOf_le 2 _ hg⟩ : ↥(E2.dpI V z)) ∈ φ.ker := h1
    rw [hφk] at h2
    exact Subgroup.mem_subgroupOf.mp h2

theorem le_normalizer_dpP (s : E2.Setting17 H T M V U x z) (φ : ↥(E2.dpI V z) →* Equiv.Perm (Fin 3))
    (hφs : Function.Surjective φ) (hφk : φ.ker = (E2.dpP H V U z).subgroupOf (E2.dpI V z)) :
    H ≤ Subgroup.normalizer (E2.dpP H V U z : Set G) := by
  rw [dpP_eq_pCoreOf s φ hφs hφk, ← s.conjClosure_eq]
  exact (le_normalizer_conjClosure V H).trans (normalizer_le_normalizer_pCoreOf 2 _)

end Y15111

end CFSG.Quasithin
