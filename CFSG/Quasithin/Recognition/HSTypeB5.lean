module

public import CFSG.Quasithin.Recognition.HSTypeB4
public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

@[expose] def zpow2 (b : G) (a : ZMod 2) : G := if a = 1 then b else 1

@[expose] def hsCoord (b : Fin 4 → G) (v : SpV) : G :=
  zpow2 (b 0) (v 0) * zpow2 (b 1) (v 1) * zpow2 (b 2) (v 2) * zpow2 (b 3) (v 3)

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zpow2_add {b : G} (hb : b * b = 1) (a a' : ZMod 2) :
    zpow2 b (a + a') = zpow2 b a * zpow2 b a' := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases a' with rfl | rfl
  · simp [zpow2, h01]
  · simp [zpow2]
  · simp [zpow2]
  · rw [h11]
    simp [zpow2, h01, hb]

theorem zpow2_zero (b : G) : zpow2 b 0 = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [zpow2, h01]

theorem zpow2_one (b : G) : zpow2 b 1 = b := by simp [zpow2]

theorem zpow2_mem {X : Subgroup G} {b : G} (hb : b ∈ X) (a : ZMod 2) : zpow2 b a ∈ X := by
  unfold zpow2
  split_ifs
  · exact hb
  · exact X.one_mem

theorem hsCoord_mem {X : Subgroup G} {b : Fin 4 → G} (hb : ∀ k, b k ∈ X) (v : SpV) :
    hsCoord b v ∈ X := by
  unfold hsCoord
  have := fun k => zpow2_mem (hb k) (v k)
  exact X.mul_mem (X.mul_mem (X.mul_mem (this 0) (this 1)) (this 2)) (this 3)

theorem hsCoord_spE (b : Fin 4 → G) (k : Fin 4) : hsCoord b (spE k) = b k := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  fin_cases k <;> simp [hsCoord, spE, zpow2, h01]

theorem spForm_spE_eq : ∀ (j : Fin 4) (v : SpV), spForm (spE j) v =
    v 0 * spForm (spE j) (spE 0) + v 1 * spForm (spE j) (spE 1) +
      v 2 * spForm (spE j) (spE 2) + v 3 * spForm (spE j) (spE 3) := by
  decide

theorem spForm_eq_sum_left : ∀ (v u : SpV), spForm v u =
    v 0 * spForm (spE 0) u + v 1 * spForm (spE 1) u + v 2 * spForm (spE 2) u +
      v 3 * spForm (spE 3) u := by
  decide

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

section Coord

variable [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
  (hss : s * s = 1)
include h hsmemH hsnotK hss

theorem hsCoord_add {b : Fin 4 → G} (hb : ∀ k, b k ∈ hsB z s) (v w : SpV) :
    hsCoord b (v + w) = hsCoord b v * hsCoord b w := by
  have hbb : ∀ k, b k * b k = 1 := fun k => h.hsB_sq hsmemH hsnotK hss (hb k)
  have hm := fun k a => zpow2_mem (hb k) a
  have hc : ∀ x ∈ hsB z s, ∀ y ∈ hsB z s, x * y = y * x := fun x hx y hy =>
    h.hsB_comm hsmemH hsnotK hss hx hy
  have hcm : ∀ i j : Fin 4, ∀ a a' : ZMod 2, Commute (zpow2 (b i) a) (zpow2 (b j) a') :=
    fun i j a a' => hc _ (hm i a) _ (hm j a')
  unfold hsCoord
  simp only [Pi.add_apply, zpow2_add (hbb _)]
  rw [(hcm 0 1 (w 0) (v 1)).mul_mul_mul_comm,
    ((hcm 0 2 (w 0) (v 2)).mul_left (hcm 1 2 (w 1) (v 2))).mul_mul_mul_comm,
    (((hcm 0 3 (w 0) (v 3)).mul_left (hcm 1 3 (w 1) (v 3))).mul_left
      (hcm 2 3 (w 2) (v 3))).mul_mul_mul_comm]

end Coord

theorem hsChi_coord [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : G} (hx : x ∈ hsB z s)
    (hx1 : x ≠ 1) {b : Fin 4 → G} (hb : ∀ k, b k ∈ hsB z s) (v : SpV) :
    hsChi x (hsCoord b v) = v 0 * hsChi x (b 0) + v 1 * hsChi x (b 1) +
      v 2 * hsChi x (b 2) + v 3 * hsChi x (b 3) := by
  have hm := fun k a => zpow2_mem (X := hsB z s) (hb k) a
  have hz : ∀ (k : Fin 4) (a : ZMod 2), hsChi x (zpow2 (b k) a) = a * hsChi x (b k) := by
    intro k a
    rcases zmod2_cases a with rfl | rfl
    · rw [zpow2_zero, hsChi_one, zero_mul]
    · rw [zpow2_one, one_mul]
  have hmul := fun {y y' : G} (hy : y ∈ hsB z s) (hy' : y' ∈ hsB z s) =>
    h.hsChi_mul hsmemH hsnotK hss hg₀ hx hx1 hy hy'
  unfold hsCoord
  rw [hmul ((hsB z s).mul_mem ((hsB z s).mul_mem (hm 0 _) (hm 1 _)) (hm 2 _)) (hm 3 _),
    hmul ((hsB z s).mul_mem (hm 0 _) (hm 1 _)) (hm 2 _), hmul (hm 0 _) (hm 1 _),
    hz, hz, hz, hz]

theorem exists_s6Model [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    ∃ (Φ : SpV → G) (π : ↥(Subgroup.normalizer (hsB z s : Set G)) →* Equiv.Perm (Fin 6)),
      (∀ v, Φ v ∈ hsB z s) ∧ Function.Injective Φ ∧ (∀ v w, Φ (v + w) = Φ v * Φ w) ∧
      (∀ x ∈ hsB z s, ∃ v, Φ v = x) ∧ Φ (spE 0) = z ∧ Φ (spE 1) = s ∧
      (∀ u v, u ≠ 0 → (Φ v ∈ hsQ (Φ u) ↔ spForm u v = 0)) ∧
      Function.Surjective π ∧
      (∀ n : ↥(Subgroup.normalizer (hsB z s : Set G)), π n = 1 ↔ (n : G) ∈ hsB z s) ∧
      ∀ (n : ↥(Subgroup.normalizer (hsB z s : Set G))) (v : SpV),
        (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 (π n) v) := by
  classical
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzQs := h.z_not_mem_hsQ_s hsQ' hg₀
  have hB := h.hsB_symm hsmemH hsnotK hss hg₀
  obtain ⟨c, c', hc, hc', hc1, hcc'⟩ := h.exists_sympBasis hsmemH hsnotK hss hg₀
  have hCB : hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ≤ hsB z s := centralizer_le_hsB
  have hcB : c ∈ hsB z s := hCB hc.1
  have hc'B : c' ∈ hsB z s := hCB hc'.1
  have hc'1 : c' ≠ 1 := fun h1 => hcc' (h1 ▸ (hsQ c).one_mem)
  have hzB := h.z_mem_hsB hsmemH
  have hs1 : s ≠ 1 := fun h1 => hsQ' (h1 ▸ (hsQ z).one_mem)
  set b : Fin 4 → G := ![z, s, c, c'] with hbdef
  have hb : ∀ k, b k ∈ hsB z s := by
    intro k
    fin_cases k
    · exact hzB
    · exact s_mem_hsB
    · exact hcB
    · exact hc'B
  have hb1 : ∀ k, b k ≠ 1 := by
    intro k
    fin_cases k
    · exact h.z_ne_one
    · exact hs1
    · exact hc1
    · exact hc'1
  have hchi := fun {x y : G} (hx : x ∈ hsB z s) (hx1 : x ≠ 1) (hy : y ∈ hsB z s)
    (hy1 : y ≠ 1) => h.hsChi_symm hsmemH hsnotK hss hg₀ hx hx1 hy hy1
  have hzc : z ∈ hsQ c :=
    (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hcB hc1 hzB h.z_ne_one).mpr hc.1.1
  have hsc : s ∈ hsQ c :=
    (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hcB hc1 s_mem_hsB hs1).mpr hc.2.1
  have hzc' : z ∈ hsQ c' :=
    (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hc'B hc'1 hzB h.z_ne_one).mpr hc'.1.1
  have hsc' : s ∈ hsQ c' :=
    (h.mem_hsQ_symm_of_mem_hsB hsmemH hsnotK hss hg₀ hc'B hc'1 s_mem_hsB hs1).mpr hc'.2.1
  have hgram : ∀ j k, hsChi (b j) (b k) = spForm (spE j) (spE k) := by
    have e00 : hsChi z z = 0 := hsChi_eq_zero_iff.mpr h.mem_Q
    have e01 : hsChi z s = 1 := hsChi_eq_one_iff.mpr hsQ'
    have e02 : hsChi z c = 0 := hsChi_eq_zero_iff.mpr hc.1.1
    have e03 : hsChi z c' = 0 := hsChi_eq_zero_iff.mpr hc'.1.1
    have e10 : hsChi s z = 1 := hsChi_eq_one_iff.mpr hzQs
    have e11 : hsChi s s = 0 := hsChi_eq_zero_iff.mpr hs'.mem_Q
    have e12 : hsChi s c = 0 := hsChi_eq_zero_iff.mpr hc.2.1
    have e13 : hsChi s c' = 0 := hsChi_eq_zero_iff.mpr hc'.2.1
    have e20 : hsChi c z = 0 := hsChi_eq_zero_iff.mpr hzc
    have e21 : hsChi c s = 0 := hsChi_eq_zero_iff.mpr hsc
    have e22 : hsChi c c = 0 := h.hsChi_self hsmemH hsnotK hss hg₀ hcB hc1
    have e23 : hsChi c c' = 1 := hsChi_eq_one_iff.mpr hcc'
    have e30 : hsChi c' z = 0 := hsChi_eq_zero_iff.mpr hzc'
    have e31 : hsChi c' s = 0 := hsChi_eq_zero_iff.mpr hsc'
    have e32 : hsChi c' c = 1 := by rw [hchi hc'B hc'1 hcB hc1, e23]
    have e33 : hsChi c' c' = 0 := h.hsChi_self hsmemH hsnotK hss hg₀ hc'B hc'1
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [hbdef, e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31,
        e32, e33] <;> decide
  set Φ : SpV → G := hsCoord b with hΦ
  have hΦmem : ∀ v, Φ v ∈ hsB z s := hsCoord_mem hb
  have hΦadd : ∀ v w, Φ (v + w) = Φ v * Φ w := h.hsCoord_add hsmemH hsnotK hss hb
  have hΦsq : ∀ v, Φ v * Φ v = 1 := fun v => h.hsB_sq hsmemH hsnotK hss (hΦmem v)
  have hchib : ∀ j v, hsChi (b j) (Φ v) = spForm (spE j) v := by
    intro j v
    rw [hΦ, h.hsChi_coord hsmemH hsnotK hss hg₀ (hb j) (hb1 j) hb, hgram, hgram, hgram,
      hgram]
    exact (spForm_spE_eq j v).symm
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    have h0 : Φ (v + w) = 1 := by rw [hΦadd, hvw, hΦsq]
    have hvw0 : v + w = 0 := by
      refine spForm_nondeg _ fun k => ?_
      rw [spForm_comm, ← hchib, h0, hsChi_one]
    funext k
    have := congrFun hvw0 k
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rcases zmod2_cases (v k) with h1 | h1 <;> rcases zmod2_cases (w k) with h2 | h2 <;>
      rw [h1, h2] at this ⊢ <;> first | rfl | exact absurd this (by decide)
  have hΦ0 : Φ 0 = 1 := by
    have := hΦadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hΦsurj : ∀ x ∈ hsB z s, ∃ v, Φ v = x := by
    have := Fintype.ofFinite ↥(hsB z s)
    let Φ' : SpV → ↥(hsB z s) := fun v => ⟨Φ v, hΦmem v⟩
    have hinj : Function.Injective Φ' := fun v w hvw => hΦinj (congrArg Subtype.val hvw)
    have hcard : Fintype.card SpV = Fintype.card ↥(hsB z s) := by
      rw [← Nat.card_eq_fintype_card (α := ↥(hsB z s)), h.card_hsB hsmemH hsnotK hss]
      simp
    have hbij := (Fintype.bijective_iff_injective_and_card Φ').mpr ⟨hinj, hcard⟩
    intro x hx
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  have hpol : ∀ u v, u ≠ 0 → hsChi (Φ u) (Φ v) = spForm u v := by
    intro u v hu
    have hu1 : Φ u ≠ 1 := fun h1 => hu (hΦinj (h1.trans hΦ0.symm))
    rw [hΦ, h.hsChi_coord hsmemH hsnotK hss hg₀ (hΦmem u) hu1 hb]
    rw [hchi (hΦmem u) hu1 (hb 0) (hb1 0), hchi (hΦmem u) hu1 (hb 1) (hb1 1),
      hchi (hΦmem u) hu1 (hb 2) (hb1 2), hchi (hΦmem u) hu1 (hb 3) (hb1 3), hchib, hchib,
      hchib, hchib, spForm_comm u v]
    exact (spForm_eq_sum_left v u).symm
  set N := Subgroup.normalizer (hsB z s : Set G) with hN
  have hconjB : ∀ (n : ↥N) (v : SpV), (n : G) * Φ v * (n : G)⁻¹ ∈ hsB z s := fun n v =>
    (Subgroup.mem_normalizer_iff.mp n.2 _).mp (hΦmem v)
  have hspForm0 : ∀ w : SpV, spForm 0 w = 0 := by decide
  have hT : ∀ n : ↥N, ∃ σ : Equiv.Perm (Fin 6),
      ∀ v, (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 σ v) := by
    intro n
    choose T hT using fun v => hΦsurj _ (hconjB n v)
    have hTadd : ∀ v w, T (v + w) = T v + T w := by
      intro v w
      apply hΦinj
      rw [hT, hΦadd, hΦadd, hT, hT]
      group
    have hTne : ∀ v, v ≠ 0 → T v ≠ 0 := by
      intro v hv hTv
      apply hv
      apply hΦinj
      have h1 := hT v
      rw [hTv, hΦ0] at h1
      rw [hΦ0]
      calc Φ v = (n : G)⁻¹ * ((n : G) * Φ v * (n : G)⁻¹) * n := by group
        _ = 1 := by rw [← h1]; group
    have hT0 : T 0 = 0 := by
      apply hΦinj
      rw [hT, hΦ0]
      group
    have hTform : ∀ v w, spForm (T v) (T w) = spForm v w := by
      intro v w
      by_cases hv : v = 0
      · rw [hv, hT0, hspForm0, hspForm0]
      · rw [← hpol _ _ (hTne v hv), hT, hT, hsChi_conj, hpol _ _ hv]
    obtain ⟨σ, hσ⟩ := exists_actS6_of_isometry T hTadd hTform
    exact ⟨σ, fun v => by rw [← hT, hσ]⟩
  choose σf hσf using hT
  have hσmul : ∀ n m : ↥N, σf (n * m) = σf n * σf m := by
    intro n m
    apply actS6_injective
    intro v
    apply hΦinj
    rw [← hσf, actS6_mul, ← hσf, ← hσf]
    simp only [Subgroup.coe_mul]
    group
  let π : ↥N →* Equiv.Perm (Fin 6) := MonoidHom.mk' σf hσmul
  have hπ : ∀ n, π n = σf n := fun _ => rfl
  have hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ hsB z s := by
    intro n
    rw [hπ]
    constructor
    · intro h1
      rw [← h.centralizer_hsB hsmemH hsnotK hss hg₀]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨v, rfl⟩ := hΦsurj x hx
      have := hσf n v
      rw [h1, actS6_one] at this
      calc Φ v * n = (n : G) * Φ v * (n : G)⁻¹ * n := by rw [this]
        _ = n * Φ v := by group
    · intro hn
      apply actS6_injective
      intro v
      apply hΦinj
      rw [← hσf, actS6_one, h.hsB_comm hsmemH hsnotK hss hn (hΦmem v), mul_inv_cancel_right]
  have hBN : hsB z s ≤ N := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => (hsB z s).mul_mem
      ((hsB z s).mul_mem hx hy) ((hsB z s).inv_mem hx), fun hy => by
        have := (hsB z s).mul_mem ((hsB z s).mul_mem ((hsB z s).inv_mem hx) hy) hx
        simpa [mul_assoc] using this⟩
  have hkerπ : π.ker = (hsB z s).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hπsurj : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hkerπ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv,
      h.card_hsB hsmemH hsnotK hss, h.card_normalizer_hsB hsmemH hsnotK hss hg₀] at h1
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_perm, Nat.card_fin]
    have : (6 : ℕ).factorial = 720 := rfl
    omega
  refine ⟨Φ, π, hΦmem, hΦinj, hΦadd, hΦsurj, hsCoord_spE b 0, hsCoord_spE b 1, ?_, hπsurj,
    hker, fun n v => by rw [hπ]; exact hσf n v⟩
  intro u v hu
  rw [← hsChi_eq_zero_iff, hpol u v hu]

end HSSetting

end CFSG.Quasithin.HSType
