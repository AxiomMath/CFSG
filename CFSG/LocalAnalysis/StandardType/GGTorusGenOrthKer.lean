module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth

public section

namespace CFSG.StandardType.OrthTorusGen

private lemma cyclic_pgroup_zpowers_le_or_le {G : Type*} [Group G] {p k l : ℕ} (hp : p.Prime)
    {C : Subgroup G} [IsCyclic C] {x y : C} (hx : orderOf x = p ^ k) (hy : orderOf y = p ^ l) :
    Subgroup.zpowers x ≤ Subgroup.zpowers y ∨ Subgroup.zpowers y ≤ Subgroup.zpowers x := by
  have hx_fin : IsOfFinOrder x := orderOf_ne_zero_iff.mp
    (by rw [hx]; exact pow_ne_zero _ hp.ne_zero)
  have hy_fin : IsOfFinOrder y := orderOf_ne_zero_iff.mp
    (by rw [hy]; exact pow_ne_zero _ hp.ne_zero)
  have hx_card : Nat.card (Subgroup.zpowers x) = p ^ k := by rw [Nat.card_zpowers, hx]
  have hy_card : Nat.card (Subgroup.zpowers y) = p ^ l := by rw [Nat.card_zpowers, hy]
  by_cases hkl : k ≤ l
  · left
    haveI : Finite (Subgroup.zpowers x) := hx_fin.finite_zpowers
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    rw [hx_card, hy_card]
    exact Nat.pow_dvd_pow p hkl
  · right
    have hlk : l ≤ k := Nat.le_of_not_le hkl
    haveI : Finite (Subgroup.zpowers y) := hy_fin.finite_zpowers
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    rw [hy_card, hx_card]
    exact Nat.pow_dvd_pow p hlk

private lemma pow_prime_pred_ne_one_of_orderOf_eq_prime_pow {G : Type*} [Group G] {p e : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p ^ e) (he : 0 < e) :
    x ^ p ^ (e - 1) ≠ 1 := by
  intro h
  have hdvd : orderOf x ∣ p ^ (e - 1) := orderOf_dvd_of_pow_eq_one h
  rw [hx] at hdvd
  have hle : e ≤ e - 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hlt : e - 1 < e := Nat.sub_lt he Nat.zero_lt_one
  exact Nat.not_le.mpr hlt hle

private lemma orderOf_pow_mul_pow_eq_prime_pow {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime)
    {u v : G} (huv : Commute u v) (hu : orderOf u = p ^ e) (hv : orderOf v = p ^ e)
    (he : 0 < e) (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1)
    {a b : ℕ} (ha : a = 1 ∨ b = 1) :
    orderOf (u ^ a * v ^ b) = p ^ e := by
  let w := u ^ a * v ^ b
  have hw_comm : Commute (u ^ a) (v ^ b) := huv.pow_pow a b
  have hw_dvd : orderOf w ∣ p ^ e := by
    have h := hw_comm.orderOf_mul_dvd_lcm
    have hua : orderOf (u ^ a) ∣ p ^ e := by rw [← hu]; exact orderOf_pow_dvd a
    have hvb : orderOf (v ^ b) ∣ p ^ e := by rw [← hv]; exact orderOf_pow_dvd b
    have hlcm : Nat.lcm (orderOf (u ^ a)) (orderOf (v ^ b)) = p ^ e := by
      rcases ha with ha1 | hb1
      · rw [ha1, pow_one, hu]
        exact Nat.lcm_eq_left hvb
      · rw [hb1, pow_one, hv]
        exact Nat.lcm_eq_right hua
    rwa [hlcm] at h
  have hw_pow_e : w ^ (p ^ e) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hw_dvd
  have hw_pow_e1 : w ^ (p ^ (e - 1)) ≠ 1 := by
    intro h
    have h' : u ^ (a * p ^ (e - 1)) * v ^ (b * p ^ (e - 1)) = 1 := by
      calc
        u ^ (a * p ^ (e - 1)) * v ^ (b * p ^ (e - 1))
            = (u ^ a) ^ (p ^ (e - 1)) * (v ^ b) ^ (p ^ (e - 1)) := by rw [pow_mul, pow_mul]
        _ = (u ^ a * v ^ b) ^ (p ^ (e - 1)) := by rw [← hw_comm.mul_pow]
        _ = w ^ (p ^ (e - 1)) := rfl
        _ = 1 := h
    have hu1 : u ^ (a * p ^ (e - 1)) = 1 := hind _ _ h'
    rcases ha with ha1 | hb1
    · rw [ha1, one_mul] at hu1
      exact pow_prime_pred_ne_one_of_orderOf_eq_prime_pow hp hu he hu1
    · rw [hb1, one_mul] at h'
      have hv1 : v ^ (p ^ (e - 1)) = 1 := by
        rw [hu1, one_mul] at h'
        exact h'
      exact pow_prime_pred_ne_one_of_orderOf_eq_prime_pow hp hv he hv1
  have hw_pow_e' : w ^ p ^ ((e - 1) + 1) = 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt he)]
    exact hw_pow_e
  haveI : Fact p.Prime := ⟨hp⟩
  have := orderOf_eq_prime_pow hw_pow_e1 hw_pow_e'
  rwa [Nat.sub_add_cancel (Nat.succ_le_of_lt he)] at this

private lemma exists_pow_mul_pow_mem_ker_of_mem_zpowers_right {G H : Type*} [Group G] [Group H]
    {p e : ℕ} (hp : p.Prime) (φ : G →* H) {u v : G} (huv : Commute u v)
    (hu : orderOf u = p ^ e) (hv : orderOf v = p ^ e)
    (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1)
    (he : 0 < e) {m : ℕ} (hx_eq : φ u = (φ v) ^ m) :
    ∃ a b : ℕ, φ (u ^ a * v ^ b) = 1 ∧ orderOf (u ^ a * v ^ b) = p ^ e := by
  refine ⟨1, p ^ e - m % p ^ e, ?_, ?_⟩
  · have hφw : φ (u ^ 1 * v ^ (p ^ e - m % p ^ e)) =
        (φ v) ^ (m + (p ^ e - m % p ^ e)) := by
      rw [map_mul, map_pow, map_pow, pow_one, hx_eq, ← pow_add]
    have hmod : m + (p ^ e - m % p ^ e) = (m / p ^ e + 1) * p ^ e := by
      have hm_lt : m % p ^ e < p ^ e := Nat.mod_lt _ (pow_pos hp.pos e)
      nth_rewrite 1 [← Nat.div_add_mod' m (p ^ e)]
      rw [Nat.add_assoc, Nat.add_sub_cancel' hm_lt.le]
      ring
    have hφv_dvd : orderOf (φ v) ∣ p ^ e := by rw [← hv]; exact orderOf_map_dvd φ v
    have hφv_pow : (φ v) ^ (p ^ e) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact hφv_dvd
    have hpow : (φ v) ^ ((m / p ^ e + 1) * p ^ e) = 1 := by
      rw [mul_comm, pow_mul, hφv_pow, one_pow]
    rw [hφw, hmod, hpow]
  · exact orderOf_pow_mul_pow_eq_prime_pow hp huv hu hv he hind (Or.inl rfl)

private lemma exists_pow_mul_pow_mem_ker_of_mem_zpowers_left {G H : Type*} [Group G] [Group H]
    {p e : ℕ} (hp : p.Prime) (φ : G →* H) {u v : G} (huv : Commute u v)
    (hu : orderOf u = p ^ e) (hv : orderOf v = p ^ e)
    (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1)
    (he : 0 < e) {m : ℕ} (hy_eq : φ v = (φ u) ^ m) :
    ∃ a b : ℕ, φ (u ^ a * v ^ b) = 1 ∧ orderOf (u ^ a * v ^ b) = p ^ e := by
  refine ⟨p ^ e - m % p ^ e, 1, ?_, ?_⟩
  · have hφw : φ (u ^ (p ^ e - m % p ^ e) * v ^ 1) =
        (φ u) ^ ((p ^ e - m % p ^ e) + m) := by
      rw [map_mul, map_pow, map_pow, pow_one, hy_eq, ← pow_add]
    have hmod : (p ^ e - m % p ^ e) + m = (m / p ^ e + 1) * p ^ e := by
      have hm_lt : m % p ^ e < p ^ e := Nat.mod_lt _ (pow_pos hp.pos e)
      conv_lhs => arg 2; rw [← Nat.div_add_mod' m (p ^ e)]
      rw [Nat.add_comm (m / p ^ e * p ^ e) (m % p ^ e), ← Nat.add_assoc,
        Nat.add_comm (p ^ e - m % p ^ e) (m % p ^ e), Nat.add_sub_cancel' hm_lt.le]
      ring
    have hφu_dvd : orderOf (φ u) ∣ p ^ e := by rw [← hu]; exact orderOf_map_dvd φ u
    have hφu_pow : (φ u) ^ (p ^ e) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact hφu_dvd
    have hpow : (φ u) ^ ((m / p ^ e + 1) * p ^ e) = 1 := by
      rw [mul_comm, pow_mul, hφu_pow, one_pow]
    rw [hφw, hmod, hpow]
  · exact orderOf_pow_mul_pow_eq_prime_pow hp huv hu hv he hind (Or.inr rfl)

private lemma exists_pow_mul_pow_mem_ker_of_e_pos {G H : Type*} [Group G] [Group H] {p e : ℕ}
    (hp : p.Prime) (φ : G →* H) {u v : G} (huv : u * v = v * u)
    (hu : orderOf u = p ^ e) (hv : orderOf v = p ^ e)
    (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1)
    (he : 0 < e)
    (hcyc : IsCyclic ↥(Subgroup.closure ({φ u, φ v} : Set H))) :
    ∃ a b : ℕ, φ (u ^ a * v ^ b) = 1 ∧ orderOf (u ^ a * v ^ b) = p ^ e := by
  classical
  have hpne : p ≠ 0 := hp.ne_zero
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hpne
  have hphiu_dvd : orderOf (φ u) ∣ p ^ e := by rw [← hu]; exact orderOf_map_dvd φ u
  have hphiv_dvd : orderOf (φ v) ∣ p ^ e := by rw [← hv]; exact orderOf_map_dvd φ v
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hphiu_dvd
  obtain ⟨l, hl_le, hl_eq⟩ := (Nat.dvd_prime_pow hp).mp hphiv_dvd
  let C : Subgroup H := Subgroup.closure ({φ u, φ v} : Set H)
  have hCcyc : IsCyclic C := hcyc
  let x : C := ⟨φ u, Subgroup.subset_closure (by simp)⟩
  let y : C := ⟨φ v, Subgroup.subset_closure (by simp)⟩
  have hx_order : orderOf x = orderOf (φ u) := by
    rw [← Subgroup.orderOf_coe x]
  have hy_order : orderOf y = orderOf (φ v) := by
    rw [← Subgroup.orderOf_coe y]
  have hx_fin : IsOfFinOrder x :=
    orderOf_ne_zero_iff.mp (by rw [hx_order, hk_eq]; exact pow_ne_zero _ hp.ne_zero)
  have hy_fin : IsOfFinOrder y :=
    orderOf_ne_zero_iff.mp (by rw [hy_order, hl_eq]; exact pow_ne_zero _ hp.ne_zero)
  have hsub_cmp : Subgroup.zpowers x ≤ Subgroup.zpowers y ∨
      Subgroup.zpowers y ≤ Subgroup.zpowers x := by
    apply cyclic_pgroup_zpowers_le_or_le hp (C := C)
    · rw [hx_order, hk_eq]
    · rw [hy_order, hl_eq]
  rcases hsub_cmp with hle | hle
  · have hx_mem : x ∈ Subgroup.zpowers y := (Subgroup.zpowers_le).mp hle
    have hx_mem_image : x ∈ (Finset.range (orderOf y)).image (y ^ ·) :=
      (hy_fin.mem_zpowers_iff_mem_range_orderOf).mp hx_mem
    rw [Finset.mem_image] at hx_mem_image
    obtain ⟨m, hm_range, hm_eq⟩ := hx_mem_image
    have hx_eq : φ u = (φ v) ^ m := by
      have := congr_arg Subtype.val hm_eq
      simpa [x, y] using this.symm
    exact exists_pow_mul_pow_mem_ker_of_mem_zpowers_right hp φ huv hu hv hind he hx_eq
  · have hy_mem : y ∈ Subgroup.zpowers x := (Subgroup.zpowers_le).mp hle
    have hy_mem_image : y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
      (hx_fin.mem_zpowers_iff_mem_range_orderOf).mp hy_mem
    rw [Finset.mem_image] at hy_mem_image
    obtain ⟨m, hm_range, hm_eq⟩ := hy_mem_image
    have hy_eq : φ v = (φ u) ^ m := by
      have := congr_arg Subtype.val hm_eq
      simpa [x, y] using this.symm
    exact exists_pow_mul_pow_mem_ker_of_mem_zpowers_left hp φ huv hu hv hind he hy_eq

theorem exists_pow_mul_pow_mem_ker {G H : Type*} [Group G] [Group H] {p e : ℕ} (hp : p.Prime)
    (φ : G →* H) {u v : G} (huv : u * v = v * u) (hu : orderOf u = p ^ e)
    (hv : orderOf v = p ^ e) (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1)
    (hcyc : IsCyclic ↥(Subgroup.closure ({φ u, φ v} : Set H))) :
    ∃ a b : ℕ, φ (u ^ a * v ^ b) = 1 ∧ orderOf (u ^ a * v ^ b) = p ^ e := by
  classical
  by_cases he : e = 0
  · subst he
    have hp1 : p ^ (0 : ℕ) = 1 := pow_zero p
    have hu1 : u = 1 := by
      rw [← orderOf_eq_one_iff]
      exact hu.trans hp1
    have hv1 : v = 1 := by
      rw [← orderOf_eq_one_iff]
      exact hv.trans hp1
    refine ⟨0, 0, ?_, ?_⟩
    · rw [hu1, hv1]
      simp
    · rw [hu1, hv1]
      simp [hp1]
  · have he_pos : 0 < e := Nat.pos_of_ne_zero he
    exact exists_pow_mul_pow_mem_ker_of_e_pos hp φ huv hu hv hind he_pos hcyc

theorem eq_bot_or_eq_range_of_conj {G : Type*} [Group G] {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 3 ≤ r) (τ : (Fin r → Multiplicative (ZMod p)) →* G) {N : Set G}
    (hperm : ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ N, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (hdinv : ∀ i j : Fin r, i ≠ j → ∃ w ∈ N, ∀ f, w * τ f * w⁻¹ = τ (NbrOrth.dinv i j f))
    {B : Subgroup G} (hB : B ≤ τ.range) (hBN : ∀ w ∈ N, ∀ b ∈ B, w * b * w⁻¹ ∈ B) :
    B = ⊥ ∨ B = τ.range := by
  let F : Subgroup (Fin r → Multiplicative (ZMod p)) := B.comap τ
  have hinvF : ∀ i k, i ≠ k → ∀ f ∈ F, NbrOrth.dinv i k f ∈ F := by
    intro i k hik f hf
    obtain ⟨w, hwN, hw⟩ := hdinv i k hik
    rw [Subgroup.mem_comap] at hf ⊢
    rw [← hw f]
    exact hBN w hwN (τ f) hf
  have hpermF : ∀ j t u : Fin r, j ≠ t → j ≠ u → t ≠ u → ∀ f ∈ F,
      f ∘ ⇑(NbrOrth.swapComm j t u)⁻¹ ∈ F := by
    intro j t u _ _ _ f hf
    obtain ⟨w, hwN, hw⟩ := hperm (NbrOrth.swapComm j t u)
    rw [Subgroup.mem_comap] at hf ⊢
    simp only [SpCoord.permAut_apply] at hw
    rw [← hw f]
    exact hBN w hwN (τ f) hf
  rcases NbrOrth.eq_bot_or_eq_top_of_dinv hp hp2 hr F hinvF hpermF with hbot | htop
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    obtain ⟨f, rfl⟩ := (MonoidHom.mem_range).mp (hB hb)
    have hf : f ∈ F := by rwa [Subgroup.mem_comap]
    rw [hbot, Subgroup.mem_bot] at hf
    rw [hf]
    exact map_one τ
  · right
    refine le_antisymm hB ?_
    intro x hx
    obtain ⟨f, rfl⟩ := (MonoidHom.mem_range).mp hx
    have hf : f ∈ F := by rw [htop]; exact Subgroup.mem_top f
    exact (Subgroup.mem_comap).mp hf

end CFSG.StandardType.OrthTorusGen
