module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.H13.A6.Aut20

open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] noncomputable def quotAut20 (Y : Type) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr (CFSG.pCore 2 Y) (CFSG.pCore 2 Y) σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem quotAut20_mk (Y : Type) [Group Y] (σ : MulAut Y) (y : Y) :
    quotAut20 Y σ (y : Y ⧸ CFSG.pCore 2 Y) = ((σ y : Y) : Y ⧸ CFSG.pCore 2 Y) := rfl

variable {G : Type} [Group G]

@[expose] noncomputable def act20 (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (ModO2 K) :=
  (quotAut20 ↥K).comp K.normalizerMonoidHom

theorem act20_mk (K : Subgroup G) (n : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    act20 K n (k : ModO2 K) =
      ((⟨(n : G) * k * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 k).mp k.2⟩ : ↥K) :
        ModO2 K) := by
  show quotAut20 ↥K (K.normalizerMonoidHom n) (k : ModO2 K) = _
  rw [quotAut20_mk]
  congr 1

section Inner

variable {Q : Type} [Group Q]

theorem mem_center_of_conj_eq_one20 {g : Q} (h : MulAut.conj g = 1) : g ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : g * x * g⁻¹ = x := by
    have := congrArg (fun φ : MulAut Q => φ x) h
    simpa [MulAut.conj_apply] using this
  calc x * g = g * x * g⁻¹ * g := by rw [hx]
    _ = g * x := by group

theorem conj_eq_one_of_mem_center20 {z : Q} (hz : z ∈ Subgroup.center Q) : MulAut.conj z = 1 := by
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hz x,
    mul_inv_cancel_right]

theorem conj_conj20 (φ : MulAut Q) (g : Q) : φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem inner_normal20 : (MulAut.conj : Q →* MulAut Q).range.Normal := by
  refine ⟨fun a ha φ => ?_⟩
  obtain ⟨g, rfl⟩ := ha
  exact ⟨φ g, (conj_conj20 φ g).symm⟩

theorem apply_mem_of_map_eq20 {S : Subgroup Q} {α : MulAut Q} (h : S.map α.toMonoidHom = S)
    {s : Q} (hs : s ∈ S) : α s ∈ S := by
  rw [← h]
  exact ⟨s, hs, rfl⟩

theorem mem_normalizer_of_map_eq20 [Finite Q] {S : Subgroup Q} {g : Q}
    (h : S.map (MulAut.conj g).toMonoidHom = S) : g ∈ Subgroup.normalizer (S : Set Q) := by
  refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => ?_, fun hs => ?_⟩
  · simpa [MulAut.conj_apply] using apply_mem_of_map_eq20 h hs
  · rw [← h] at hs
    obtain ⟨s', hs', he⟩ := hs
    have e : s' = s := by
      have he' : g * s' * g⁻¹ = g * s * g⁻¹ := by simpa [MulAut.conj_apply] using he
      simpa using he'
    exact e ▸ hs'

end Inner

section Sylow

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_of_le_normalizer20 {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) {u : Q}
    (hu : u ∈ Subgroup.normalizer (S : Set Q)) {k : ℕ} (hk : u ^ 2 ^ k = 1) : u ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers u) := by
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ S) :=
    IsPGroup.to_sup_of_normal_right' h2 hS.2.1 (Subgroup.zpowers_le.2 hu)
  have hSM : S ≤ Subgroup.zpowers u ⊔ S := le_sup_right
  have h1 := Subgroup.relIndex_mul_relIndex S (Subgroup.zpowers u ⊔ S) ⊤ hSM le_top
  have hodd : ¬ 2 ∣ S.relIndex (Subgroup.zpowers u ⊔ S) := fun h =>
    hS.2.2 (by
      have : S.relIndex ⊤ = (S.subgroupOf ⊤).index := rfl
      rw [← this, ← h1]
      exact h.mul_right _)
  have hidx : S.relIndex (Subgroup.zpowers u ⊔ S) = 1 := by
    obtain ⟨n, hn⟩ := hsup.index (S.subgroupOf (Subgroup.zpowers u ⊔ S))
    have hn' : S.relIndex (Subgroup.zpowers u ⊔ S) = 2 ^ n := hn
    rcases n with _ | n
    · simpa using hn'
    · exact absurd (hn' ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)) hodd
  have hle : Subgroup.zpowers u ⊔ S ≤ S := Subgroup.relIndex_eq_one.mp hidx
  exact hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))

theorem exists_mem_conj20 (hZ : Odd (Nat.card (Subgroup.center Q))) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) {α : MulAut Q} {k : ℕ} (hk : α ^ 2 ^ k = 1)
    (hαS : S.map α.toMonoidHom = S) {g : Q} (hg : α = MulAut.conj g) :
    ∃ u ∈ S, α = MulAut.conj u := by
  set m := Nat.card (Subgroup.center Q) with hm
  have hm0 : 0 < m := Nat.card_pos
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hZ)
  set N := m ^ Nat.totient (2 ^ k) with hN
  have hN1 : N ≡ 1 [MOD 2 ^ k] := Nat.ModEq.pow_totient hcop
  have hmN : m ∣ N := by
    have : 0 < Nat.totient (2 ^ k) := Nat.totient_pos.2 (pow_pos (by norm_num) k)
    exact dvd_pow_self m this.ne'
  refine ⟨g ^ N, ?_, ?_⟩
  ·
    have hcz : g ^ 2 ^ k ∈ Subgroup.center Q := by
      apply mem_center_of_conj_eq_one20
      rw [map_pow, ← hg, hk]
    have hz1 : (g ^ 2 ^ k) ^ m = 1 := by
      have h := orderOf_dvd_natCard (⟨g ^ 2 ^ k, hcz⟩ : ↥(Subgroup.center Q))
      rw [orderOf_dvd_iff_pow_eq_one] at h
      have h' := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have h2 : (g ^ N) ^ 2 ^ k = 1 := by
      obtain ⟨c, hc⟩ := hmN
      rw [← pow_mul, mul_comm, pow_mul, hc, pow_mul, hz1, one_pow]
    have hnorm : g ^ N ∈ Subgroup.normalizer (S : Set Q) := by
      refine Subgroup.pow_mem _ (mem_normalizer_of_map_eq20 ?_) N
      rw [← hg]
      exact hαS
    exact mem_of_le_normalizer20 hS hnorm h2
  ·
    rw [map_pow, ← hg]
    have hle : 1 ≤ N := Nat.one_le_pow _ _ hm0
    obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hle).1 hN1.symm
    have hNj : N = 2 ^ k * j + 1 := by omega
    rw [hNj, pow_succ, pow_mul, hk, one_pow, one_mul]


omit [Finite Q] in
theorem mul_pow_mul_inv_mem20 {J : Subgroup Q} {y s : Q} (hy : y ∈ Subgroup.normalizer (J : Set Q))
    (hs : s ∈ J) (m : ℕ) : (s * y) ^ m * (y ^ m)⁻¹ ∈ J := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hym : y ^ m ∈ Subgroup.normalizer (J : Set Q) := Subgroup.pow_mem _ hy m
    have e : (s * y) ^ (m + 1) * (y ^ (m + 1))⁻¹ =
        ((s * y) ^ m * (y ^ m)⁻¹) * (y ^ m * s * (y ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact J.mul_mem ih ((Subgroup.mem_normalizer_iff.mp hym s).mp hs)

theorem eq_one_of_two_three20 {M : Type} [Monoid M] {x : M} {a b : ℕ} (h2 : x ^ 2 ^ b = 1)
    (h3 : x ^ 3 ^ a = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ b) (3 ^ a) := Nat.Coprime.pow _ _ (by norm_num)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem eq_one_of_inv20 {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) {ξ ω : MulAut Q} {a b : ℕ}
    (hξ : ξ ^ 3 ^ a = 1) (hω : ω ^ 2 ^ b = 1) (hξS : S.map ξ.toMonoidHom = S) {u : Q}
    (hu : u ∈ S) (h : MulAut.conj u * ξ * (MulAut.conj u)⁻¹ = ω * ξ⁻¹) : ξ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinn : ξ ∈ (MulAut.conj : Q →* MulAut Q).range := by
    have := inner_normal20 (Q := Q)
    set q := QuotientGroup.mk' (MulAut.conj : Q →* MulAut Q).range with hq
    have hqu : q (MulAut.conj u) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩
    have h1 : q ξ * q ξ = q ω := by
      have := congrArg q h
      rw [map_mul, map_mul, map_inv, hqu, one_mul, inv_one, mul_one, map_mul, map_inv] at this
      rw [show q ξ * q ξ = q ω * (q ξ)⁻¹ * q ξ from by rw [← this], inv_mul_cancel_right]
    have h2 : q ξ ^ 2 ^ (b + 1) = 1 := by
      rw [pow_succ', pow_mul, sq, h1, ← map_pow, hω, map_one]
    have h3 : q ξ ^ 3 ^ a = 1 := by rw [← map_pow, hξ, map_one]
    exact (QuotientGroup.eq_one_iff _).1 (eq_one_of_two_three20 h2 h3)
  obtain ⟨k, rfl⟩ := hinn
  have hkN : k ∈ Subgroup.normalizer (S : Set Q) := mem_normalizer_of_map_eq20 hξS
  have hk3 : k ^ 3 ^ a ∈ Subgroup.center Q :=
    mem_center_of_conj_eq_one20 (by rw [map_pow, hξ])
  set w := u * k * u⁻¹ * k with hw
  have hcw : MulAut.conj w = ω := by
    have e : MulAut.conj w = (MulAut.conj u * MulAut.conj k * (MulAut.conj u)⁻¹) *
        MulAut.conj k := by
      rw [hw, map_mul, map_mul, map_mul, map_inv]
    rw [e, h, inv_mul_cancel_right]
  have hw2 : w ^ 2 ^ b ∈ Subgroup.center Q :=
    mem_center_of_conj_eq_one20 (by rw [map_pow, hcw, hω])
  set J := S ⊔ Subgroup.center Q with hJ
  have hkJ : k ∈ Subgroup.normalizer (J : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    have hfwd : ∀ g ∈ Subgroup.normalizer (S : Set Q), ∀ x ∈ J, g * x * g⁻¹ ∈ J := by
      intro g hg x hx
      rw [hJ, ← SetLike.mem_coe, Subgroup.mul_normal] at hx ⊢
      obtain ⟨s, hs, z, hz, rfl⟩ := hx
      refine ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp hs, z, hz, ?_⟩
      have hzc := Subgroup.mem_center_iff.mp hz
      calc g * s * g⁻¹ * z = g * s * (g⁻¹ * z) := by group
        _ = g * s * (z * g⁻¹) := by rw [hzc g⁻¹]
        _ = g * (s * z) * g⁻¹ := by group
    intro x
    refine ⟨hfwd k hkN x, fun hx => ?_⟩
    have := hfwd k⁻¹ (Subgroup.inv_mem _ hkN) _ hx
    simpa [mul_assoc] using this
  have hSJ : S ≤ J := le_sup_left
  have hZJ : Subgroup.center Q ≤ J := le_sup_right
  have hs₀ : u * (k * u⁻¹ * k⁻¹) ∈ S :=
    S.mul_mem hu ((Subgroup.mem_normalizer_iff.mp hkN u⁻¹).mp (S.inv_mem hu))
  have hwe : w = (u * (k * u⁻¹ * k⁻¹)) * k ^ 2 := by rw [hw, sq]; group
  have hk2 : k ^ (2 * 2 ^ b) ∈ J := by
    have h1 := mul_pow_mul_inv_mem20 (Subgroup.pow_mem _ hkJ 2) (hSJ hs₀) (2 ^ b)
    rw [← hwe, ← pow_mul] at h1
    have h2 := J.mul_mem (J.inv_mem h1) (hZJ hw2)
    simpa using h2
  have hkJ' : k ∈ J := by
    have hcop : Nat.Coprime (2 * 2 ^ b) (3 ^ a) := by
      rw [← pow_succ']
      exact Nat.Coprime.pow _ _ (by norm_num)
    have hbez := Nat.gcd_eq_gcd_ab (2 * 2 ^ b) (3 ^ a)
    rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
    have e : k = (k ^ (2 * 2 ^ b)) ^ Nat.gcdA (2 * 2 ^ b) (3 ^ a) *
        (k ^ 3 ^ a) ^ Nat.gcdB (2 * 2 ^ b) (3 ^ a) := by
      rw [← zpow_natCast, ← zpow_natCast (k), ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
        zpow_one]
    rw [e]
    exact J.mul_mem (J.zpow_mem hk2 _) (J.zpow_mem (hZJ hk3) _)
  rw [hJ, ← SetLike.mem_coe, Subgroup.mul_normal] at hkJ'
  obtain ⟨s, hs, z, hz, rfl⟩ := hkJ'
  have hcs : MulAut.conj (s * z) = MulAut.conj s := by
    rw [map_mul, conj_eq_one_of_mem_center20 hz, mul_one]
  obtain ⟨c, hc⟩ := hS.2.1 ⟨s, hs⟩
  have hs2 : s ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
  rw [hcs] at hξ ⊢
  exact eq_one_of_two_three20 (by rw [← map_pow, hs2, map_one]) hξ

end Sylow

theorem eq_one_of_perfect20 {Y : Type} [Group Y] [Group.IsPerfect Y] {τ : MulAut Y}
    (h : ∀ y : Y, y⁻¹ * τ y ∈ Subgroup.center Y) : τ = 1 := by
  let z : Y →* Y :=
    { toFun := fun s => s⁻¹ * τ s
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (h s)
        calc (s * t)⁻¹ * τ (s * t) = t⁻¹ * (s⁻¹ * τ s) * τ t := by
              rw [map_mul]
              group
          _ = s⁻¹ * τ s * (t⁻¹ * τ t) := by
              rw [ht t⁻¹]
              group }
  have hzc : ∀ s, z s ∈ Subgroup.center Y := h
  have hcomm : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab := Subgroup.mem_center_iff.mp (hzc a) (z b)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hab.symm
  have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * τ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

end CFSG.Quasithin.H13.A6.Aut20
