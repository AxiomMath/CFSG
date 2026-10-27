module

public import CFSG.Quasithin.Vol2.Ch6NatRho
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem isSylowIn_T (h : Hyp611 G T M L V n) : IsSylowIn 2 T (L ⊔ T) :=
  E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
    le_sup_right le_top

theorem sup_le_normalizer_L (h : Hyp611 G T M L V n) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (h.T_le.trans h.normal)

theorem isSylowIn_TL (h : Hyp611 G T M L V n) : IsSylowIn 2 (T ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine h.isSylowIn_T.inf_normal le_sup_left ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact h.sup_le_normalizer_L

end Hyp611

namespace Hyp611Nat

noncomputable abbrev data (h : Hyp611Nat G T M L V n) : NatL2Data L V n := h.natural.data

@[expose] noncomputable def rhoTL (h : Hyp611Nat G T M L V n) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) h.data.K) :=
  ((T ⊓ L).subgroupOf L).map h.data.rho

theorem isPGroup_rhoTL (h : Hyp611Nat G T M L V n) : IsPGroup 2 ↥h.rhoTL := by
  rintro ⟨A, hA⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hA
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨(x : G), (Subgroup.mem_subgroupOf.mp hx).1⟩
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← map_pow]
  have : x ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  rw [this, map_one]

theorem odd_index_rhoTL (h : Hyp611Nat G T M L V n) : ¬ 2 ∣ h.rhoTL.index := by
  intro h2
  apply h.toHyp611.isSylowIn_TL.not_dvd_relIndex
  exact h2.trans (Subgroup.index_map_dvd _ h.data.rho_surjective)

theorem two_dvd_card_K (h : Hyp611Nat G T M L V n) : 2 ∣ Nat.card h.data.K := by
  rw [h.data.card]
  exact dvd_pow_self 2 (by have := h.two_le; omega)

theorem rhoTL_ne_bot (h : Hyp611Nat G T M L V n) : h.rhoTL ≠ ⊥ := by
  intro h0
  apply h.odd_index_rhoTL
  rw [h0, Subgroup.index_bot]
  rw [CFSG.GorensteinWalter.sl2_card_formula]
  exact h.two_dvd_card_K.trans (Dvd.intro _ rfl)

theorem exists_line (h : Hyp611Nat G T M L V n) :
    ∃ v : Fin 2 → h.data.K, v ≠ 0 ∧ h.rhoTL ≤ sl2Stab v := by
  obtain ⟨v, hv, hfix⟩ := exists_fixed_vector h.two_dvd_card_K h.rhoTL h.isPGroup_rhoTL
  exact ⟨v, hv, fun A hA => mem_sl2Stab.mpr (hfix A hA)⟩

theorem rhoTL_eq_stab (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K} (hv : v ≠ 0)
    (hle : h.rhoTL ≤ sl2Stab v) : h.rhoTL = sl2Stab v := by
  have hstab := card_sl2Stab hv
  have hdvd : Nat.card h.rhoTL ∣ Nat.card h.data.K := hstab ▸ Subgroup.card_dvd_of_le hle
  have hq : Nat.card h.data.K ∣ Nat.card h.rhoTL := by
    have h1 : Nat.card h.data.K ∣ Nat.card h.rhoTL * h.rhoTL.index := by
      rw [Subgroup.card_mul_index, CFSG.GorensteinWalter.sl2_card_formula]
      exact Dvd.intro _ rfl
    have hcop : Nat.Coprime (Nat.card h.data.K) h.rhoTL.index := by
      rw [h.data.card]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr
        (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h.odd_index_rhoTL)))
    exact hcop.dvd_of_dvd_mul_right h1
  have hcard : Nat.card h.rhoTL = Nat.card (sl2Stab v) := by
    rw [hstab]; exact Nat.dvd_antisymm hdvd hq
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem mem_ZS_iff (h : Hyp611Nat G T M L V n) (x : ↥V) :
    (x : G) ∈ ch6ZS T L V ↔ ∀ A ∈ h.rhoTL,
      (A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E x)) =
        Multiplicative.toAdd (h.data.E x) := by
  rw [show (x : G) ∈ ch6ZS T L V ↔
      (x : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)
    from ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩, h.data.fixed_iff inf_le_right x]
  constructor
  · intro hx A hA
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hA
    exact hx y (Subgroup.mem_subgroupOf.mp hy)
  · intro hx y hy
    exact hx _ (Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)

theorem mem_ZS_iff_line (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K} (hv : v ≠ 0)
    (hle : h.rhoTL ≤ sl2Stab v) (x : ↥V) :
    (x : G) ∈ ch6ZS T L V ↔ ∃ c : h.data.K, Multiplicative.toAdd (h.data.E x) = c • v := by
  rw [h.mem_ZS_iff x]
  constructor
  · intro hx
    exact fixed_eq_line h.rhoTL h.rhoTL_ne_bot hv (fun A hA => mem_sl2Stab.mp (hle hA)) hx
  · rintro ⟨c, hc⟩ A hA
    rw [hc, Matrix.mulVec_smul, mem_sl2Stab.mp (hle hA)]

theorem exists_stab_of_mem_S (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K} (hv : v ≠ 0)
    (hle : h.rhoTL ≤ sl2Stab v) {s : G} (hs : s ∈ ch6S T L V) :
    ∃ A ∈ sl2Stab v, ∀ w, h.data.conj ⟨s, h.toHyp611.T_le_normalizer hs.1⟩ w =
      (A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w := by
  have hsT : s ∈ T := hs.1
  have hsL : s ∈ Subgroup.normalizer (L : Set G) := h.normal (h.T_le hsT)
  let m : Subgroup.normalizer (V : Set G) := ⟨s, h.toHyp611.T_le_normalizer hs.1⟩
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear m hsL
  have hfixline : ∀ c : h.data.K, h.data.conj m (c • v) = c • v := by
    intro c
    set z : ↥V := h.data.E.symm (Multiplicative.ofAdd (c • v)) with hzdef
    have hEz : Multiplicative.toAdd (h.data.E z) = c • v := by simp [hzdef]
    have hz : (z : G) ∈ ch6ZS T L V := (h.mem_ZS_iff_line hv hle z).mpr ⟨c, hEz⟩
    rw [← hEz, ← h.data.toAdd_E_conj]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have hc := Subgroup.mem_centralizer_iff.mp hs.2 (z : G) hz
    show s * (z : G) * s⁻¹ = z
    calc s * (z : G) * s⁻¹ = (z : G) * s * s⁻¹ := by rw [← hc]
      _ = z := by group
  have hv1 : h.data.conj m v = v := by simpa using hfixline 1
  have hσid : ∀ c, σ c = c := by
    intro c
    have h1 := hσ c v
    rw [hfixline c, hv1] at h1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
    exact (mul_right_cancel₀ hi this).symm
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨s, hsT⟩
  have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ w, (h.data.conj m)^[2 ^ k] w = w := by
    intro w
    rw [← h.data.conj_pow]
    have : m ^ 2 ^ k = 1 := Subtype.ext (by simpa [m] using hsk)
    rw [this]
    exact h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) w
  exact exists_mem_sl2Stab_of_linear h.two_dvd_card_K (h.data.conj m)
    (fun c w => by rw [hσ, hσid]) hpow hv1

theorem exists_mem_TL_of_mem_S (h : Hyp611Nat G T M L V n) {s : G} (hs : s ∈ ch6S T L V) :
    ∃ t ∈ T ⊓ L, s * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hstab := h.rhoTL_eq_stab hv hle
  obtain ⟨A, hA, hAeq⟩ := h.exists_stab_of_mem_S hv hle hs
  set m : Subgroup.normalizer (V : Set G) := ⟨s, h.toHyp611.T_le_normalizer hs.1⟩ with hm
  rw [← hstab] at hA
  obtain ⟨t, ht, hρt⟩ := Subgroup.mem_map.mp hA
  have htTL : (t : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp ht
  refine ⟨t, htTL, ?_⟩
  let t' : Subgroup.normalizer (V : Set G) := ⟨t, h.data.le_normalizer t.2⟩
  have hct : ∀ w, h.data.conj t' w = h.data.conj m w := by
    intro w
    rw [h.data.conj_eq_rho t w, hρt, hAeq]
  have := h.data.mem_centralizer_of_conj_eq (m * t'⁻¹) fun w => by
    rw [h.data.conj_mul, ← hct, ← h.data.conj_mul, mul_inv_cancel]
    exact h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) w
  simpa [hm, t'] using this

theorem S_eq (h : Hyp611Nat G T M L V n) : ch6S T L V = (T ⊓ L) ⊔ ch6Q T V := by
  apply le_antisymm
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h.exists_mem_TL_of_mem_S hs
    have hq : s * t⁻¹ ∈ ch6Q T V := ⟨T.mul_mem hs.1 (T.inv_mem ht.1), hst⟩
    have : s = (s * t⁻¹) * t := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup hq ht
  · refine sup_le (le_inf inf_le_left ?_) (le_inf inf_le_left ?_)
    · intro t ht
      show t ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp hz.2 t ht).symm
    · intro t ht
      show t ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp ht.2 z hz.1

end Hyp611Nat

end CFSG.Quasithin.H13
