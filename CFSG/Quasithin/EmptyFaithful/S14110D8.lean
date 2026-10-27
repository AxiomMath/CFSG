module

public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin

open CFSG.Open DihedralGroup

section Dihedral

private theorem dihedral4_sq_ne_one_iff (g : DihedralGroup 4) :
    g ^ 2 ≠ 1 ↔ (g = r 1 ∨ g = r 3) := by
  revert g; decide

private theorem dihedral4_pow_four (g : DihedralGroup 4) : g ^ 4 = 1 := by
  revert g; decide

private theorem dihedral4_sr_mul_sr (i j : ZMod 4) : ∃ k, sr i * sr j = r k :=
  ⟨j - i, sr_mul_sr i j⟩

private theorem dihedral4_involution (g : DihedralGroup 4) (h2 : g ^ 2 = 1) (h1 : g ≠ 1)
    (hz : g ≠ r 2) : ∃ j, g = sr j := by
  revert g; decide

theorem mulAut_eq_one_of_dihedralFour {Q : Type*} [Group Q] (ι : Q →* DihedralGroup 4)
    (hι : Function.Injective ι) {zq : Q} (hzq : ι zq = r 2) (α : MulAut Q) (hαz : α zq = zq)
    {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1) : α = 1 := by
  have hpow : ∀ (k : ℕ) (q : Q), (α ^ k) q = (α^[k]) q := by
    intro k
    induction k with
    | zero => intro q; rfl
    | succ k ih => intro q; rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  have hm' : ∀ q : Q, α^[m] q = q := by
    intro q
    rw [← hpow, hαm, MulAut.one_apply]
  have hrot4 : ∀ q : Q, (ι q) ^ 2 ≠ 1 → α q = q := by
    intro q hq
    have hq' : (ι (α q)) ^ 2 ≠ 1 := by
      intro h
      apply hq
      have : ι ((α q) ^ 2) = 1 := by rw [map_pow, h]
      have h2 : (α q) ^ 2 = 1 := hι (by rw [this, map_one])
      have h3 : q ^ 2 = 1 := by
        apply α.injective
        rw [map_pow, h2, map_one]
      rw [← map_pow, h3, map_one]
    rcases (dihedral4_sq_ne_one_iff _).mp hq with h1 | h1 <;>
      rcases (dihedral4_sq_ne_one_iff _).mp hq' with h2 | h2
    · exact hι (by rw [h1, h2])
    ·
      have hinv : α q = q⁻¹ := hι (by rw [h2, map_inv, h1]; decide)
      have hαα : α (α q) = q := by rw [hinv, map_inv, hinv, inv_inv]
      obtain ⟨k, rfl⟩ := hm
      have hit : ∀ n : ℕ, α^[2 * n + 1] q = α q := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          have h2q : α^[2] q = q := by
            simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
            exact hαα
          rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Function.iterate_add_apply, h2q, ih]
      have := hm' q
      rw [hit k, hinv] at this
      have h5 : ι q⁻¹ = ι q := by rw [this]
      rw [map_inv, h1] at h5
      exact absurd h5 (by decide)
    · have hinv : α q = q⁻¹ := hι (by rw [h2, map_inv, h1]; decide)
      have hαα : α (α q) = q := by rw [hinv, map_inv, hinv, inv_inv]
      obtain ⟨k, rfl⟩ := hm
      have hit : ∀ n : ℕ, α^[2 * n + 1] q = α q := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          have h2q : α^[2] q = q := by
            simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
            exact hαα
          rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Function.iterate_add_apply, h2q, ih]
      have := hm' q
      rw [hit k, hinv] at this
      have h5 : ι q⁻¹ = ι q := by rw [this]
      rw [map_inv, h1] at h5
      exact absurd h5 (by decide)
    · exact hι (by rw [h1, h2])
  have hrot : ∀ q : Q, (∃ k, ι q = r k) → α q = q := by
    rintro q ⟨k, hk⟩
    by_cases hq : (ι q) ^ 2 = 1
    ·
      have key : ∀ k : ZMod 4, (r k : DihedralGroup 4) ^ 2 = 1 → r k = 1 ∨ r k = r 2 := by
        decide
      have hk' : ι q = 1 ∨ ι q = r 2 := by
        rw [hk] at hq ⊢
        exact key k hq
      rcases hk' with h | h
      · have : q = 1 := hι (by rw [h, map_one])
        rw [this, map_one]
      · have : q = zq := hι (by rw [h, hzq])
        rw [this, hαz]
    · exact hrot4 q hq
  have hrefl : ∀ q : Q, α q = q := by
    intro q
    rcases hq : ι q with k | i
    · exact hrot q ⟨k, hq⟩
    ·
      have hq2 : q ^ 2 = 1 := hι (by rw [map_pow, hq, map_one, sq, sr_mul_self])
      have hq1 : q ≠ 1 := fun h => by
        rw [h, map_one, DihedralGroup.one_def] at hq; exact absurd hq (fun h' => by cases h')
      have hqz : q ≠ zq := fun h => by rw [h, hzq] at hq; exact absurd hq (fun h' => by cases h')
      have hα2 : ι (α q) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hq2, map_one, map_one]
      have hα1 : ι (α q) ≠ 1 := fun h => hq1 (α.injective (hι (by rw [h, map_one, map_one])))
      have hαz' : ι (α q) ≠ r 2 := fun h => hqz (α.injective (hι (by rw [h, hαz, hzq])))
      obtain ⟨j, hj⟩ := dihedral4_involution _ hα2 hα1 hαz'
      set w := q⁻¹ * α q with hw
      have hwr : ∃ k, ι w = r k := by
        rw [hw, map_mul, map_inv, hq, hj]
        refine ⟨j - i, ?_⟩
        rw [inv_sr]
        exact sr_mul_sr i j
      have hαw : α w = w := hrot w hwr
      have hαq : α q = q * w := by rw [hw, mul_inv_cancel_left]
      have hit : ∀ n : ℕ, α^[n] q = q * w ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hαw, hαq, pow_succ', mul_assoc]
      have hwm : w ^ m = 1 := by
        have := hm' q
        rw [hit m] at this
        exact mul_eq_left.mp this
      have hw4 : w ^ 4 = 1 := hι (by rw [map_pow, dihedral4_pow_four, map_one])
      have hgcd : Nat.gcd m 4 = 1 := by
        obtain ⟨k, rfl⟩ := hm
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨k, rfl⟩)
      have hw1 : w = 1 := by
        have := (pow_gcd_eq_one (a := w) (m := m) (n := 4)).mpr ⟨hwm, hw4⟩
        rwa [hgcd, pow_one] at this
      rw [hw] at hw1
      exact (inv_mul_eq_one.mp hw1).symm
  ext q
  rw [hrefl q, MulAut.one_apply]

end Dihedral

variable {G : Type} [Group G] [Finite G]

theorem centralizer_omegaOneCenter_ne {T Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≠ T := by
  intro heq
  obtain ⟨M, hM, hne⟩ := h.exists_inM_ne
  exact hne (h.mc_unique M hM.1 (by rw [heq]; exact hM.2))

open CFSG.LieType.BorelTits in
theorem not_nonempty_mulEquiv_dihedralFour {T Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc) :
    ¬ Nonempty (T ≃* DihedralGroup 4) := by
  rintro ⟨φ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hcenD : ∀ g : DihedralGroup 4, (∀ k : DihedralGroup 4, g * k = k * g) ↔
      (g = 1 ∨ g = r 2) := by decide
  set zT : T := φ.symm (r 2) with hzT_def
  set z : G := (zT : G) with hz_def
  have hzT : z ∈ T := zT.2
  have hz1 : z ≠ 1 := by
    intro h1
    have : zT = 1 := Subtype.ext h1
    have h2 : φ zT = 1 := by rw [this, map_one]
    rw [hzT_def, MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide)
  have hz2 : z ^ 2 = 1 := by
    have : zT ^ 2 = 1 := φ.injective (by rw [map_pow, hzT_def, MulEquiv.apply_symm_apply, map_one]; decide)
    exact congrArg Subtype.val this
  have hzcen : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    have hc := (hcenD (r 2)).mpr (Or.inr rfl) (φ ⟨t, ht⟩)
    have : (⟨t, ht⟩ : T) * zT = zT * ⟨t, ht⟩ := φ.injective (by
      rw [map_mul, map_mul, hzT_def, MulEquiv.apply_symm_apply]; exact hc.symm)
    exact congrArg Subtype.val this
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro t ht; exact hzcen t ht
  have hzZ : z ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hzT, hzC⟩, hz2⟩
  set P : Subgroup G := Subgroup.zpowers z with hP
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hN
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ N := by
    have : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (P : Set G) := by
      rw [hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [this]
    exact Subgroup.centralizer_le_normalizer _
  have hTC : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzcen t ht
  have hTN : T ≤ N := hTC.trans hCN
  have hPp : IsPGroup 2 P := h.sylow.1.to_le (Subgroup.zpowers_le.mpr hzT)
  have hP1 : P ≠ ⊥ := fun hb => hz1 ((Subgroup.zpowers_eq_bot).mp hb)
  have hF : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N :=
    h.qtke.2.1 N ⟨P, hP1, hPp, rfl⟩ ⟨S, hS ▸ hTN⟩
  set Q : Subgroup G := pCoreOf 2 N with hQ
  have hQT : Q ≤ T := by
    have := pCoreOf_two_le_sylow N S (hS ▸ hTN)
    rwa [hS] at this
  have hzQ : z ∈ Q := by
    refine hF ⟨hTN hzT, ?_⟩
    show z ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hzcen q (hQT hq)
  have hodd : ∀ x ∈ Subgroup.centralizer ({z} : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf x = p → False := by
    intro x hx p hp hp2 hxp
    have hxN : x ∈ N := hCN hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 N hxN
    let β : MulAut Q := Q.normalizerMonoidHom ⟨x, hxQ⟩
    have hβ : ∀ q : Q, ((β q : Q) : G) = x * q * x⁻¹ :=
      fun q => Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨x, hxQ⟩ q
    let ι : Q →* DihedralGroup 4 := φ.toMonoidHom.comp (Subgroup.inclusion hQT)
    have hι : Function.Injective ι :=
      φ.injective.comp (Subgroup.inclusion_injective hQT)
    have hιz : ι ⟨z, hzQ⟩ = r 2 := by
      change φ (Subgroup.inclusion hQT ⟨z, hzQ⟩) = r 2
      have : Subgroup.inclusion hQT ⟨z, hzQ⟩ = zT := rfl
      rw [this, hzT_def, MulEquiv.apply_symm_apply]
    have hβz : β ⟨z, hzQ⟩ = ⟨z, hzQ⟩ := by
      apply Subtype.ext
      rw [hβ]
      have := Subgroup.mem_centralizer_singleton_iff.mp hx
      change x * z * x⁻¹ = z
      rw [this, mul_inv_cancel_right]
    have hβp : β ^ p = 1 := by
      have : (⟨x, hxQ⟩ : Subgroup.normalizer (Q : Set G)) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hxp, pow_orderOf_eq_one, Subgroup.coe_one]
      change Q.normalizerMonoidHom ⟨x, hxQ⟩ ^ p = 1
      rw [← map_pow, this, map_one]
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hβ1 := mulAut_eq_one_of_dihedralFour ι hι hιz β hβz hpodd hβp
    have hxC : x ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : ((β ⟨q, hq⟩ : Q) : G) = q := by rw [hβ1]; rfl
      rw [hβ] at h1
      calc q * x = (x * q * x⁻¹) * x := by rw [h1]
        _ = x * q := by group
    have hxQ' : x ∈ Q := hF ⟨hxN, hxC⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 N) ⟨x, hxQ'⟩
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hxp] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({z} : Set G)) := by
    apply IsPGroup.of_card (n := (Nat.card (Subgroup.centralizer ({z} : Set G))).primeFactorsList.length)
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro d hd hdvd
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({z} : Set G)) d hdvd
    exact hodd x x.2 d hd hd2 (by rw [← Subgroup.orderOf_coe] at hx; exact hx)
  have hCT : Subgroup.centralizer ({z} : Set G) = T := by
    have := S.is_maximal' hC2 (hS ▸ hTC)
    rw [this, hS]
  apply centralizer_omegaOneCenter_ne h
  apply le_antisymm
  · exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)).trans hCT.le
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (T : Set G) := by
      have hle : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
        unfold quasithinOmegaOneCenter
        rw [Subgroup.closure_le]
        exact fun w hw => hw.1.2
      exact hle hy
    exact (Subgroup.mem_centralizer_iff.mp hyC t ht).symm

end CFSG.Quasithin
