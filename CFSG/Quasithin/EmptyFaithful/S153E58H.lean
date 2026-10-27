module

public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.Quasithin.EmptyFaithful.S153E58A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

section Solvable

variable {W : Type} [CommGroup W] [Finite W]

theorem zpowers_involution_cases {G' : Type*} [Group G'] {a : G'} (ha2 : a ^ 2 = 1) {x : G'}
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul]
    simp [ha2]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul]
    simp [ha2]

omit [Finite W] in
theorem commV_stable_of_commute {a h : MulAut W} (hch : h * a = a * h) :
    ∀ r ∈ commV (Subgroup.zpowers a), h r ∈ commV (Subgroup.zpowers a) := by
  intro r hr
  unfold commV at hr ⊢
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, rfl⟩ := hx
    have hhb : h * b = b * h := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute h a from hch) m).eq
    refine Subgroup.subset_closure ⟨b, hb, h v, ?_⟩
    have : h (b v) = b (h v) := by
      have := DFunLike.congr_fun hhb v
      simpa using this
    rw [map_mul, this, map_inv]
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    rw [map_inv]
    exact Subgroup.inv_mem _ ih

omit [Finite W] in
theorem fix_eq_one_of_normal {H K : Subgroup (MulAut W)} (hHirr : IsIrrOn153 H ⊤)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hK1 : K ≠ ⊥) :
    ∀ x : W, (∀ k ∈ K, k x = x) → x = 1 := by
  have hF : IsInv H (fixIn K ⊤) := by
    intro h hh x hx
    rw [mem_fixIn] at hx ⊢
    refine ⟨Subgroup.mem_top _, fun k hk => ?_⟩
    have hk' : h⁻¹ * k * h ∈ K := by
      have := hKn h⁻¹ (H.inv_mem hh) k hk
      simpa using this
    have h1 := hx.2 _ hk'
    have : k (h x) = h ((h⁻¹ * k * h) x) := by
      simp [MulAut.mul_apply]
    rw [this, h1]
  rcases hHirr.2.2 (fixIn K ⊤) le_top hF with h | h
  · intro x hx
    have : x ∈ fixIn K ⊤ := mem_fixIn.2 ⟨Subgroup.mem_top _, hx⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hK1
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    apply MulEquiv.ext
    intro x
    have : x ∈ fixIn K ⊤ := by
      rw [h]
      exact Subgroup.mem_top x
    exact (mem_fixIn.1 this).2 k hk

theorem false_of_three_group (hW : ∀ w : W, w * w = 1) {K : Subgroup (MulAut W)} (hK3 : IsPGroup 3 ↥K)
    {a : MulAut W} (ha2 : a * a = 1) (hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hCK : ∀ k ∈ K, a * k * a⁻¹ = k → k = 1) (hfix : ∀ x : W, (∀ k ∈ K, k x = x) → x = 1)
    (hc4 : Nat.card ↥((⊤ : Subgroup W).map (phi a)) = 2 ^ 2) {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card W = 2 ^ (2 * (s + 2))) : False := by
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  have hinv := eq_inv_of_forall_ne ha2 hKa hCK
  obtain ⟨n, hn⟩ := hK3.exists_card_eq
  have hodd : Odd (Nat.card ↥K) := by
    rw [hn]
    exact Odd.pow (by decide)
  have h1 := card_le_sq_of_inverting hW hodd hinv hfix
  rw [hc4, hcard] at h1
  have h2 : 2 ^ (2 * (s + 2)) ≥ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h1
  omega

theorem false_of_L_five {H K D : Subgroup (MulAut W)} {a : MulAut W} (haH : a ∈ H) (hDH : D ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (ha2 : a ^ 2 = 1) (hDa : ∀ d ∈ D, d * a = a * d) (haD : a ∈ ⁅D, D⁆)
    (h5 : Nat.card ↥⁅K, Subgroup.zpowers a⁆ = 5) : False := by
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  have ha' : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have ha2' : a * a = 1 := by rw [← pow_two, ha2]
  set L : Subgroup (MulAut W) := ⁅K, Subgroup.zpowers a⁆ with hL
  have hgen : ∀ k ∈ K, ∀ b ∈ Subgroup.zpowers a, ⁅k, b⁆ ∈ K ∧ a * ⁅k, b⁆ * a⁻¹ = ⁅k, b⁆⁻¹ := by
    intro k hk b hb
    rcases zpowers_involution_cases ha2 hb with hb1 | hba
    · rw [hb1]
      simp
    · rw [hba]
      refine ⟨?_, ?_⟩
      · have h1 : a * k⁻¹ * a⁻¹ ∈ K := hKn a haH k⁻¹ (K.inv_mem hk)
        have : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact K.mul_mem hk h1
      · have e1 : a * ⁅k, a⁆ * a⁻¹ = a * k * a * k⁻¹ * (a⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        have e2 : a⁻¹ * a⁻¹ = 1 := by rw [ha']; exact ha2'
        have e3 : ⁅k, a⁆⁻¹ = a * k * a⁻¹ * k⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e1, e2, e3, mul_one]
        rw [ha']
  have hLinv : ∀ x ∈ L, x ∈ K ∧ a * x * a⁻¹ = x⁻¹ := by
    intro x hx
    rw [hL, Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, b, hb, rfl⟩ := hx
      exact hgen k hk b hb
    | one => exact ⟨K.one_mem, by simp⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨K.mul_mem ihx.1 ihy.1, ?_⟩
      have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [this, ihx.2, ihy.2, mul_inv_rev]
      exact hab _ (K.inv_mem ihx.1) _ (K.inv_mem ihy.1)
    | inv x _ ih =>
      refine ⟨K.inv_mem ih.1, ?_⟩
      have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [this, ih.2]
  have hLD : ∀ d ∈ D, ∀ x ∈ L, d * x * d⁻¹ ∈ L := by
    intro d hd x hx
    rw [hL, Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, b, hb, rfl⟩ := hx
      have hdb : d * b = b * d := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute d a from hDa d hd) m).eq
      have e : d * ⁅k, b⁆ * d⁻¹ = ⁅d * k * d⁻¹, b⁆ := by
        have hb' : d * b * d⁻¹ = b := by
          rw [hdb]
          group
        calc d * ⁅k, b⁆ * d⁻¹ = ⁅d * k * d⁻¹, d * b * d⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
          _ = ⁅d * k * d⁻¹, b⁆ := by rw [hb']
      rw [e]
      exact Subgroup.commutator_mem_commutator (hKn d (hDH hd) k hk) hb
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      rw [this]
      exact L.mul_mem ihx ihy
    | inv x _ ih =>
      have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
      rw [this]
      exact L.inv_mem ih
  have hDL : D ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun d hd =>
    mem_normalizer_of_forall' (hLD d hd)
  have hcyc : IsCyclic ↥L := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card (p := 5) h5
  let ρ : ↥D →* MulAut ↥L := (L.normalizerMonoidHom).comp (Subgroup.inclusion hDL)
  have hρ : ∀ (d : ↥D) (x : ↥L), (((ρ d) x : ↥L) : MulAut W) = (d : MulAut W) * x * (d : MulAut W)⁻¹ :=
    fun d x => rfl
  have hcomm : ∀ f g : MulAut ↥L, f * g = g * f := by
    intro f g
    apply (IsCyclic.mulAutMulEquiv ↥L).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have haD' : a ∈ D := by
    have : ⁅D, D⁆ ≤ D := Subgroup.commutator_le.2 fun x hx y hy =>
      D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)
    exact this haD
  have hker : ⁅D, D⁆ ≤ ρ.ker.map D.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥D), ⟨y, hy⟩⁆, (MonoidHom.mem_ker).2 ?_, rfl⟩
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  obtain ⟨d', hd'ker, hd'a⟩ := hker haD
  have hcent : ∀ x ∈ L, a * x * a⁻¹ = x := by
    intro x hx
    have h1 : ρ d' ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [MonoidHom.mem_ker.1 hd'ker]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [hρ] at h2
    have h3 : (d' : MulAut W) = a := hd'a
    rw [h3] at h2
    exact h2
  have hLne : L ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h5
    omega
  obtain ⟨x', hx'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hLne
  have hxL : (x' : MulAut W) ∈ L := x'.2
  have hx1 : (x' : MulAut W) ≠ 1 := fun h => hx' (Subtype.ext h)
  generalize (x' : MulAut W) = x at hxL hx1
  have hxx : x = x⁻¹ := by
    have h1 := hcent x hxL
    have h2 := (hLinv x hxL).2
    rw [h1] at h2
    exact h2
  have hx2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← hxx]
      _ = 1 := mul_inv_cancel x
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have hdvd5 : orderOf x ∣ 5 := by
    have := orderOf_dvd_natCard (⟨x, hxL⟩ : ↥L)
    rw [Subgroup.orderOf_mk, h5] at this
    exact this
  have : orderOf x ∣ Nat.gcd 2 5 := Nat.dvd_gcd hdvd2 hdvd5
  have h1 : orderOf x = 1 := by
    have : Nat.gcd 2 5 = 1 := by norm_num
    rw [this] at *
    exact Nat.dvd_one.1 ‹orderOf x ∣ 1›
  exact hx1 (orderOf_eq_one_iff.1 h1)

end Solvable

end S153E58

end CFSG.Quasithin
