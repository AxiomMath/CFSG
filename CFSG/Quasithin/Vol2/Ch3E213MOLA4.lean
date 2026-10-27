module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA3

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution

variable {K : Type} [Group K]

theorem centralizer_two_map (φ : MulAut K) {z : K} {L : Subgroup K}
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set K), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ Subgroup.zpowers z) :
    ∀ c ∈ Subgroup.centralizer ((L.map φ.toMonoidHom : Subgroup K) : Set K), ∀ k : ℕ,
      c ^ 2 ^ k = 1 → c ∈ Subgroup.zpowers (φ z) := by
  intro c hc k hk
  have h1 : φ.symm c ∈ Subgroup.centralizer (L : Set K) := by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (φ x) ⟨x, hx, rfl⟩
  have h2 := hC _ h1 k (by rw [← map_pow, hk, map_one])
  have h3 : Subgroup.zpowers (φ z) = (Subgroup.zpowers z).map φ.toMonoidHom :=
    (MonoidHom.map_zpowers φ.toMonoidHom z).symm
  rw [h3]
  exact ⟨_, h2, by simp⟩

theorem commute_two_map (φ : MulAut K) {z : K} {L : Subgroup K}
    (hS : ∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ a ∈ L, ∀ b ∈ L, a * b ≠ b * a →
      y * a = a * y → y * b = b * y → y ∈ Subgroup.centralizer (L : Set K)) :
    ∀ y ∈ Subgroup.centralizer ({φ z} : Set K), ∀ a ∈ L.map φ.toMonoidHom,
      ∀ b ∈ L.map φ.toMonoidHom, a * b ≠ b * a → y * a = a * y → y * b = b * y →
      y ∈ Subgroup.centralizer ((L.map φ.toMonoidHom : Subgroup K) : Set K) := by
  rintro y hy _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab hya hyb
  have key : ∀ u w : K, φ u * w = w * φ u → u * φ.symm w = φ.symm w * u := fun u w h => by
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h
  have hy' : φ.symm y ∈ Subgroup.centralizer ({z} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact (key z y hy.symm).symm
  have h1 := hS _ hy' a ha b hb (fun h => hab (by rw [← map_mul, ← map_mul, h]))
    (key a y hya.symm).symm (key b y hyb.symm).symm
  rw [Subgroup.mem_centralizer_iff] at h1 ⊢
  rintro _ ⟨x, hx, rfl⟩
  have h2 := h1 x hx
  calc φ.toMonoidHom x * y = φ (x * φ.symm y) := by simp
    _ = φ (φ.symm y * x) := by rw [h2]
    _ = y * φ.toMonoidHom x := by simp

theorem inner_map (φ : MulAut K) {L : Subgroup K}
    (hInv : ∀ v : MulAut K, v * v = 1 → (∀ x ∈ L, v x = x) →
      v ∈ (MulAut.conj : K →* MulAut K).range) :
    ∀ v : MulAut K, v * v = 1 → (∀ x ∈ L.map φ.toMonoidHom, v x = x) →
      v ∈ (MulAut.conj : K →* MulAut K).range := by
  intro v hv2 hfix
  have hw2 : (φ⁻¹ * v * φ) * (φ⁻¹ * v * φ) = 1 := by
    calc (φ⁻¹ * v * φ) * (φ⁻¹ * v * φ) = φ⁻¹ * (v * v) * φ := by group
      _ = 1 := by rw [hv2]; group
  have hwfix : ∀ x ∈ L, (φ⁻¹ * v * φ) x = x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix (φ x) ⟨x, hx, rfl⟩, MulAut.inv_apply_self]
  obtain ⟨y, hy⟩ := hInv _ hw2 hwfix
  refine ⟨φ y, MulEquiv.ext fun x => ?_⟩
  have h1 := DFunLike.congr_fun hy (φ⁻¹ x)
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self] at h1
  have h2 := congrArg φ h1
  rw [MulAut.apply_inv_self, map_mul, map_mul, map_inv, MulAut.apply_inv_self] at h2
  rw [MulAut.conj_apply]
  exact h2

variable [Finite K]

theorem kfact_of_classical {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {z : K} {L : Subgroup K} (hL : IsClassicalSL2 F L z)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set K), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ Subgroup.zpowers z)
    (hS : ∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ a ∈ L, ∀ b ∈ L, a * b ≠ b * a →
      y * a = a * y → y * b = b * y → y ∈ Subgroup.centralizer (L : Set K))
    (hInv : ∀ v : MulAut K, v * v = 1 → (∀ x ∈ L, v x = x) →
      v ∈ (MulAut.conj : K →* MulAut K).range)
    (hconj : ∀ t : K, orderOf t = 2 → ∃ g : K, t = g * z * g⁻¹) (S : Sylow 2 K) :
    ∃ z' : K, orderOf z' = 2 ∧ E2P.zOf (S : Subgroup K) = Subgroup.zpowers z' ∧
      (∀ Q : Subgroup K, Q ≤ Subgroup.centralizer ({z'} : Set K) → IsPGroup 2 Q →
        Subgroup.centralizer ({z'} : Set K) ≤ Subgroup.normalizer (Q : Set K) →
        Q ≤ Subgroup.zpowers z') ∧
      ∀ v : MulAut K, orderOf v = 2 →
        (∀ x ∈ Subgroup.centralizer ({z'} : Set K), v x * x⁻¹ ∈ Subgroup.zpowers z') →
        v ∈ (MulAut.conj : K →* MulAut K).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htZ, ht2⟩ : ∃ t ∈ E2P.zOf (S : Subgroup K), orderOf t = 2 := by
    have hdvd : 2 ∣ Nat.card K := by
      rw [← hL.orderOf_eq_two]
      exact orderOf_dvd_natCard z
    have : Nontrivial (S : Subgroup K) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (S.ne_bot_of_dvd_card hdvd)
    have : Nontrivial (Subgroup.center (S : Subgroup K)) := S.isPGroup'.center_nontrivial
    have h2Z : 2 ∣ Nat.card (Subgroup.center (S : Subgroup K)) := by
      rcases (S.isPGroup'.to_subgroup (Subgroup.center _)).card_eq_or_dvd with h | h
      · exact absurd h Finite.one_lt_card.ne'
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
    refine ⟨((c : S) : K), ?_, ?_⟩
    · change ((c : S) : K) ∈ (S : Subgroup K) ⊓ Subgroup.centralizer ((S : Subgroup K) : Set K)
      refine Subgroup.mem_inf.mpr ⟨(c : S).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨s, hs⟩)
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  obtain ⟨g, hg⟩ := hconj t ht2
  have hφz : (MulAut.conj g) z = t := by rw [MulAut.conj_apply, hg]
  have hL' : IsClassicalSL2 F (L.map (MulAut.conj g).toMonoidHom) t := by
    have h1 := hL.conj g
    rwa [← hg] at h1
  have hC' := centralizer_two_map (MulAut.conj g) hC
  rw [hφz] at hC'
  have hS' := commute_two_map (MulAut.conj g) hS
  rw [hφz] at hS'
  have hInv' := inner_map (MulAut.conj g) hInv
  have : Group.IsPerfect (L.map (MulAut.conj g).toMonoidHom) := hL'.isPerfect h4
  refine ⟨t, ht2, zOf_eq_zpowers hodd hL' hC' hS' S htZ, fun Q hQz hQ2 hQn =>
    le_zpowers_of_normalized hodd h4 hL' hC' hQz hQ2 hQn, fun v hv hvz => ?_⟩
  refine hInv' v (by rw [← pow_two, ← hv, pow_orderOf_eq_one]) ?_
  exact fix_of_perfect hL'.le_centralizer v fun x hx => hvz x (hL'.le_centralizer hx)

end CFSG.Quasithin.Ch3E213M.OLA
