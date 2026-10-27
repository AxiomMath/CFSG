module

public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Gen

variable {G : Type} [Group G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_phi_gen (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ φ : ↥H₁ →* DihedralGroup p, Function.Surjective φ ∧
      ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let φ : ↥H₁ →* DihedralGroup p :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  refine ⟨φ, e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  show e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem IsDecP.exists_rotation_gen (hp : 1 < p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ a ∈ H₁, a ∉ pCoreOf 2 H ∧ a ^ p ∈ pCoreOf 2 H := by
  have : Fact (1 < p) := ⟨hp⟩
  have : NeZero p := ⟨by omega⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  refine ⟨a, a.2, fun hQ => ?_, ?_⟩
  · have := (hker a).mpr hQ
    rw [ha] at this
    have h1 : (DihedralGroup.r (1 : ZMod p)) = DihedralGroup.r 0 := this
    have h2 := DihedralGroup.r.inj h1
    exact one_ne_zero h2
  · have : φ (a ^ p) = 1 := by
      rw [map_pow, ha]
      exact DihedralGroup.r_one_pow_n
    exact (hker _).mp this

end Gen

section PQ

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.pq_le_gen (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) : PQ ≤ H₀ := by
  have hp1 : 1 < p := hred.prime.one_lt
  obtain ⟨a, haH₁, haQ, hap⟩ := h.exists_rotation_gen hp1
  have hTH : T ≤ H := hred.isHTM.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have haH : a ∈ H := h.le (h.le₁ haH₁)
  have haPT : a ∈ PQ ⊔ T := by rw [← hred.eq]; exact haH
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) haPT
  have hQPQ : pCoreOf 2 H ≤ PQ := hred.lt.le
  have hpPQ : a ^ p ∈ PQ := hQPQ hap
  have haPQ : a ∈ PQ := by
    have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((p : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hred.prime).mpr
        (Ne.symm hred.odd))
    obtain ⟨u, v, huv⟩ := hcop.symm
    have e : a = (a ^ p) ^ u * (a ^ 2 ^ k) ^ v := by
      have huv' : ((p : ℕ) : ℤ) * u + ((2 ^ k : ℕ) : ℤ) * v = 1 := by linarith [huv]
      have h1 : (a ^ p) ^ u * (a ^ 2 ^ k) ^ v =
          a ^ (((p : ℕ) : ℤ) * u + ((2 ^ k : ℕ) : ℤ) * v) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      rw [h1, huv', zpow_one]
    rw [e]
    exact PQ.mul_mem (PQ.zpow_mem hpPQ u) (PQ.zpow_mem hk v)
  have hHN : H ≤ Subgroup.normalizer ((H₀ ⊓ PQ : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨h.normal hx, hred.normal hx⟩
  rcases hred.minimal (H₀ ⊓ PQ) (le_inf (h.Q₁.trans h.le₁) hQPQ) inf_le_right hHN with hN | hN
  · exfalso
    apply haQ
    rw [← hN]
    exact ⟨h.le₁ haH₁, haPQ⟩
  · exact inf_eq_right.mp hN

end PQ

section Dihedral

theorem dih_rot_of_pow {n m : ℕ} (hm : Odd m) {d : DihedralGroup n} (hd : d ^ m = 1) :
    ∃ j : ZMod n, d = DihedralGroup.r j := by
  cases d with
  | r j => exact ⟨j, rfl⟩
  | sr i =>
    exfalso
    obtain ⟨k, rfl⟩ := hm
    have h2 : (DihedralGroup.sr i) ^ 2 = 1 := by
      rw [pow_two]; exact DihedralGroup.sr_mul_self i
    have : (DihedralGroup.sr i) ^ (2 * k + 1) = DihedralGroup.sr i := by
      rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [this] at hd
    have h3 : DihedralGroup.sr i = DihedralGroup.r 0 := hd.trans DihedralGroup.one_def
    cases h3

end Dihedral
section Rot

variable {G : Type} [Group G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.conj_rotation_aux (hp : p.Prime) (hp2 : p ≠ 2) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (φ : ↥H₁ →* DihedralGroup p) (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a : ↥H₁} (ha : φ a = DihedralGroup.r 1) {x : G} (hxH : x ∈ H)
    (hxN : x ∈ Subgroup.normalizer (H₁ : Set G)) (hx2 : x * x ∈ pCoreOf 2 H) :
    x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ pCoreOf 2 H ∨ x * (a : G) * x⁻¹ * (a : G) ∈ pCoreOf 2 H := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hQN : ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ ∈ pCoreOf 2 H := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hxH) q).mp hq
  have hconj : ∀ y : ↥H₁, x * (y : G) * x⁻¹ ∈ H₁ := fun y =>
    (Subgroup.mem_normalizer_iff.mp hxN y).mp y.2
  let c : ↥H₁ → ↥H₁ := fun y => ⟨x * (y : G) * x⁻¹, hconj y⟩
  have hc_mul : ∀ y z, c (y * z) = c y * c z := fun y z => Subtype.ext (by
    show x * ((y : G) * (z : G)) * x⁻¹ = x * (y : G) * x⁻¹ * (x * (z : G) * x⁻¹)
    group)
  have hc_pow : ∀ (y : ↥H₁) (n : ℕ), c (y ^ n) = c y ^ n := by
    intro y n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Subtype.ext (by simp [c])
    | succ n ih => rw [pow_succ, hc_mul, ih, pow_succ]
  have hc_ker : ∀ y, φ y = 1 → φ (c y) = 1 := fun y hy =>
    (hker _).mpr (hQN _ ((hker y).mp hy))
  have hap : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
  have hcap : φ (c a) ^ p = 1 := by
    rw [← map_pow, ← hc_pow]
    exact hc_ker _ hap
  obtain ⟨k, hk⟩ := dih_rot_of_pow hodd hcap
  have hm : φ (c a) = (φ a) ^ k.val := by
    rw [ha, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, hk]
  have hq₀ : φ (c a * (a ^ k.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, hm, mul_inv_cancel]
  have hca : c a = (c a * (a ^ k.val)⁻¹) * a ^ k.val := by group
  have hcc : φ (c (c a)) = (φ a) ^ (k.val * k.val) := by
    conv_lhs => rw [hca]
    rw [hc_mul, hc_pow, map_mul, hc_ker _ hq₀, one_mul, map_pow, hm, ← pow_mul]
  have hcc' : c (c a) = ⟨x * x, h.Q₁ hx2⟩ * a * ⟨x * x, h.Q₁ hx2⟩⁻¹ := Subtype.ext (by
    show x * (x * (a : G) * x⁻¹) * x⁻¹ = x * x * (a : G) * (x * x)⁻¹
    group)
  have hxx : φ ⟨x * x, h.Q₁ hx2⟩ = 1 := (hker _).mpr hx2
  have hcc2 : φ (c (c a)) = φ a := by
    rw [hcc', map_mul, map_mul, map_inv, hxx, one_mul, inv_one, mul_one]
  have hk1 : (1 : ZMod p) = k * k := by
    have e : φ a = (φ a) ^ (k.val * k.val) := hcc2.symm.trans hcc
    rw [ha, DihedralGroup.r_one_pow] at e
    have e' := DihedralGroup.r.inj e
    rw [e']
    simp
  have hkk : k = 1 ∨ k = -1 := mul_self_eq_one_iff.mp hk1.symm
  rcases hkk with hk1' | hk1'
  · left
    have : φ (c a * a⁻¹) = 1 := by
      rw [map_mul, map_inv, hk, hk1', ha, mul_inv_cancel]
    exact (hker _).mp this
  · right
    have : φ (c a * a) = 1 := by
      have h0 : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
      rw [map_mul, hk, hk1', ha, DihedralGroup.r_mul_r, h0]
      rfl
    exact (hker _).mp this

end Rot

section SupZ

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.le_sup_zpowers (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ : ↥H₁ →* DihedralGroup p)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥H₁} (ha : φ a = DihedralGroup.r 1) :
    PQ ≤ Subgroup.zpowers (a : G) ⊔ H₂ := by
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hred.odd
  have hpq : PQ ≤ H₀ := h.pq_le_gen S hred
  intro y hy
  have hyH₀ : y ∈ H₁ ⊔ H₂ := by rw [← h.sup]; exact hpq hy
  have hmul : (↑(H₁ ⊔ H₂) : Set G) = ↑H₁ * ↑H₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right H₁ H₂ h.H₁_le_normalizer_H₂
  have hy' : y ∈ (↑(H₁ ⊔ H₂) : Set G) := hyH₀
  rw [hmul] at hy'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := hred.pSec (y₁ * y₂) hy
  set Q := pCoreOf 2 H with hQ
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr (le_normalizer_pCoreOf 2 H)
  have hy₁H : y₁ ∈ H := h.le (h.le₁ hy₁)
  have hy₂H : y₂ ∈ H := h.le (h.le₂ hy₂)
  let π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H)
  have hπ1 : ∀ z : ↥H, π z = 1 ↔ (z : G) ∈ Q := fun z => by
    show (QuotientGroup.mk z : ↥H ⧸ Q.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : Commute (π ⟨y₁, hy₁H⟩) (π ⟨y₂, hy₂H⟩) := by
    have h1 : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Q := h.comm (Subgroup.commutator_mem_commutator hy₁ hy₂)
    have h2 : π (⟨y₁, hy₁H⟩ * ⟨y₂, hy₂H⟩ * ⟨y₁, hy₁H⟩⁻¹ * ⟨y₂, hy₂H⟩⁻¹) = 1 := (hπ1 _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm).mp h2
  have hn : π ⟨y₁, hy₁H⟩ ^ (p ^ k) * π ⟨y₂, hy₂H⟩ ^ (p ^ k) = 1 := by
    rw [← hcomm.mul_pow, ← map_mul, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hk)
  have hn' : y₁ ^ (p ^ k) * y₂ ^ (p ^ k) ∈ Q := by
    rw [← map_pow, ← map_pow, ← map_mul] at hn
    exact (hπ1 _).mp hn
  have hy₁n : y₁ ^ (p ^ k) ∈ Q := by
    have hy₂n : y₂ ^ (p ^ k) ∈ H₂ := H₂.pow_mem hy₂ _
    have h3 : y₁ ^ (p ^ k) ∈ H₂ := by
      have e : y₁ ^ (p ^ k) = (y₁ ^ (p ^ k) * y₂ ^ (p ^ k)) * (y₂ ^ (p ^ k))⁻¹ := by group
      rw [e]
      exact H₂.mul_mem (h.Q₂ hn') (H₂.inv_mem hy₂n)
    have h4 : y₁ ^ (p ^ k) ∈ H₁ ⊓ H₂ := ⟨H₁.pow_mem hy₁ _, h3⟩
    rwa [h.inf] at h4
  have hφn : φ ⟨y₁, hy₁⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (hker _).mpr (by simpa using hy₁n)
  obtain ⟨j, hj⟩ := dih_rot_of_pow (hodd.pow) hφn
  have hq : φ (⟨y₁, hy₁⟩ * (a ^ j.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ha, hj, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      mul_inv_cancel]
  have hqQ : y₁ * ((a : G) ^ j.val)⁻¹ ∈ Q := by simpa using (hker _).mp hq
  have e : y₁ * y₂ = (y₁ * ((a : G) ^ j.val)⁻¹) * (a : G) ^ j.val * y₂ := by group
  show y₁ * y₂ ∈ Subgroup.zpowers (a : G) ⊔ H₂
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (h.Q₂ hqQ))
    (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)))
    (Subgroup.mem_sup_right hy₂)

end SupZ

end CFSG.Quasithin
