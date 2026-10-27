module

public import CFSG.Quasithin.Background.E2Basic
import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open CFSG.GroupTheory CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem eq_one_of_pow_eq_one_of_coprime {M : Type*} [Group M] {x : M} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : x ^ a = 1) (hb : x ^ b = 1) : x = 1 := by
  have h1 : orderOf x ∣ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf x ∣ b := orderOf_dvd_of_pow_eq_one hb
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hab h1 h2)

section Core

variable {Q : Type*} [Group Q] [Finite Q]

theorem eOne_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO2 : CFSG.Open.pCore 2 Q = ⊥)
    (h2P : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ CFSG.Open.pCore p Q) {B : Subgroup Q}
    (hB : Nat.card B = 2) (hPB : CFSG.Open.pCore p Q = ⁅CFSG.Open.pCore p Q, B⁆)
    {N : Subgroup Q} [N.Normal] (hNB : IsPGroup 2 ↥⁅B, N⁆) :
    N ≤ CFSG.Open.pCore p Q := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCore p Q with hP
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hPp : IsPGroup p P := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hcop2p : ∀ k m : ℕ, Nat.Coprime (2 ^ k) (p ^ m) := fun k m =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  obtain ⟨a, ha1, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).1 hB
  have hBa : ∀ b ∈ B, b = 1 ∨ b = (a : Q) := by
    intro b hb
    by_cases h : (⟨b, hb⟩ : B) = 1
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val (huniq _ h))
  have haa : (a : Q) * (a : Q) = 1 := by
    by_contra hne
    have h1 : a * a ≠ 1 := fun h => hne (congrArg Subtype.val h)
    have h2 : a * a = a := huniq _ h1
    exact ha1 (mul_left_cancel (h2.trans (mul_one a).symm))
  obtain ⟨hΦchar, hcomm, hD, -⟩ := frattini_elementary_quotient hPp
  have : (frattini ↥P).Characteristic := hΦchar
  set Φ := frattini ↥P with hΦ
  let γ : Q →* MulAut ↥P := MulAut.conjNormal
  have hγ : ∀ (q : Q) (x : ↥P), ((γ q x : ↥P) : Q) = q * x * q⁻¹ := fun q x =>
    MulAut.conjNormal_apply q x
  have hcommD : ∀ d e : ↥P ⧸ Φ, d * e = e * d := hcomm.is_comm.comm
  let β : MulAut (↥P ⧸ Φ) := quotientAutomorphism Φ (γ a)
  have hβ : ∀ x : ↥P, β (QuotientGroup.mk' Φ x) = QuotientGroup.mk' Φ (γ a x) :=
    quotientAutomorphism_apply Φ (γ a)
  let Dm : Subgroup (↥P ⧸ Φ) :=
    { carrier := {d | β d = d⁻¹}
      one_mem' := by simp
      mul_mem' := fun {d e} hd he => by
        have hd' : β d = d⁻¹ := hd
        have he' : β e = e⁻¹ := he
        show β (d * e) = (d * e)⁻¹
        rw [map_mul, hd', he', mul_inv_rev, hcommD]
      inv_mem' := fun {d} hd => by
        have hd' : β d = d⁻¹ := hd
        show β d⁻¹ = d⁻¹⁻¹
        rw [map_inv, hd'] }
  have hDm : ∀ x : ↥P, QuotientGroup.mk' Φ x ∈ Dm := by
    set Sm : Subgroup ↥P := Dm.comap (QuotientGroup.mk' Φ) with hSm
    have hgen : ∀ x ∈ P, ∀ b ∈ B, ⁅x, b⁆ ∈ Sm.map P.subtype := by
      intro x hx b hb
      rcases hBa b hb with rfl | rfl
      · simp only [commutatorElement_one_right]
        exact Subgroup.one_mem _
      · have hxa : ⁅x, (a : Q)⁆ ∈ P := by
          rw [commutatorElement_def]
          have h1 : (a : Q) * x⁻¹ * (a : Q)⁻¹ ∈ P := hPn.conj_mem _ (P.inv_mem hx) a
          have e : x * (a : Q) * x⁻¹ * (a : Q)⁻¹ = x * ((a : Q) * x⁻¹ * (a : Q)⁻¹) := by group
          rw [e]
          exact P.mul_mem hx h1
        refine ⟨⟨⁅x, (a : Q)⁆, hxa⟩, ?_, rfl⟩
        set x' : ↥P := ⟨x, hx⟩ with hx'
        have hy : (⟨⁅x, (a : Q)⁆, hxa⟩ : ↥P) = x' * (γ a x')⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hγ, hx', commutatorElement_def]
          group
        have hγγ : γ a (γ a x') = x' := by
          rw [← MulAut.mul_apply, ← map_mul, haa, map_one]
          rfl
        have hγy : γ a (⟨⁅x, (a : Q)⁆, hxa⟩ : ↥P) = γ a x' * x'⁻¹ := by
          rw [hy, map_mul, map_inv, hγγ]
        show β (QuotientGroup.mk' Φ ⟨⁅x, (a : Q)⁆, hxa⟩) =
          (QuotientGroup.mk' Φ ⟨⁅x, (a : Q)⁆, hxa⟩)⁻¹
        rw [hβ, hγy, hy]
        simp [map_mul, map_inv, mul_inv_rev]
    have hP' : P ≤ Sm.map P.subtype := by
      calc P = ⁅P, B⁆ := hPB
        _ ≤ Sm.map P.subtype := Subgroup.commutator_le.2 hgen
    intro x
    obtain ⟨y, hy, hyx⟩ := hP' x.2
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hinv : ∀ x : ↥P, β (QuotientGroup.mk' Φ x) = (QuotientGroup.mk' Φ x)⁻¹ := hDm
  have hF4 : ∀ z : ↥P, (z : Q) ∈ N → QuotientGroup.mk' Φ z = 1 := by
    intro z hzN
    have hcz : (a : Q) * (z : Q) * (a : Q)⁻¹ = (z : Q) := by
      have hc1 : ⁅(a : Q), (z : Q)⁆ ∈ ⁅B, N⁆ := Subgroup.commutator_mem_commutator a.2 hzN
      have hc2 : ⁅(a : Q), (z : Q)⁆ ∈ P := by
        rw [commutatorElement_def]
        exact P.mul_mem (hPn.conj_mem _ z.2 a) (P.inv_mem z.2)
      obtain ⟨k, hk⟩ := hNB ⟨_, hc1⟩
      obtain ⟨m, hm⟩ := hPp ⟨_, hc2⟩
      have h1 : ⁅(a : Q), (z : Q)⁆ = 1 :=
        eq_one_of_pow_eq_one_of_coprime (hcop2p k m) (congrArg Subtype.val hk)
          (congrArg Subtype.val hm)
      have h2 := commutatorElement_eq_one_iff_mul_comm.1 h1
      exact mul_inv_eq_iff_eq_mul.2 h2
    have hγz : γ a z = z := Subtype.ext (by rw [hγ]; exact hcz)
    have h1 := hinv z
    rw [hβ, hγz] at h1
    have h2 : (QuotientGroup.mk' Φ z) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel _
    exact eq_one_of_pow_eq_one_of_coprime ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
      h2 (hD _)
  have hker : ∀ n ∈ N, γ n ∈ (quotientAutomorphism Φ).ker := by
    intro n hn
    rw [mem_quotientAutomorphism_kernel]
    intro x
    have hz : (((γ n x) * x⁻¹ : ↥P) : Q) ∈ N := by
      rw [Subgroup.coe_mul, hγ, Subgroup.coe_inv]
      have e : n * (x : Q) * n⁻¹ * (x : Q)⁻¹ = n * ((x : Q) * n⁻¹ * (x : Q)⁻¹) := by group
      rw [e]
      exact N.mul_mem hn (Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hn) _)
    have h1 := hF4 _ hz
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hsolv : Group.IsSolvable Q := by
    have h2g : IsPGroup 2 (Q ⧸ P) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨k, hk⟩ := h2P x
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
    have : Group.IsNilpotent (Q ⧸ P) := h2g.isNilpotent
    have : Group.IsNilpotent ↥P := hPp.isNilpotent
    exact Group.isSolvable_of_ker_le_range P.subtype (QuotientGroup.mk' P) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hker2 : ∀ x ∈ N, ∀ m : ℕ, x ^ 2 ^ m = 1 → x = 1 := by
    intro x hx m hxm
    obtain ⟨j, hj⟩ := (frattini_automorphism_kernel hPp).2 ⟨γ x, hker x hx⟩
    have h1 : (γ x) ^ p ^ j = 1 := congrArg Subtype.val hj
    have h2 : (γ x) ^ 2 ^ m = 1 := by rw [← map_pow, hxm, map_one]
    have h3 : γ x = 1 := eq_one_of_pow_eq_one_of_coprime (hcop2p m j) h2 h1
    have hxc : x ∈ Subgroup.centralizer (P : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h4 := congrArg (fun φ : MulAut ↥P => ((φ ⟨y, hy⟩ : ↥P) : Q)) h3
      simp only [hγ, MulAut.one_apply] at h4
      calc y * x = (x * y * x⁻¹) * x := by rw [h4]
        _ = x * y := by group
    have hxP : x ∈ P := E2.centralizer_pCore_le hp h2P hO2 hsolv hxc
    obtain ⟨c, hc⟩ := hPp ⟨x, hxP⟩
    exact eq_one_of_pow_eq_one_of_coprime (hcop2p m c) hxm (congrArg Subtype.val hc)
  intro n hn
  obtain ⟨k, hk⟩ := h2P n
  obtain ⟨c, hc⟩ := hPp ⟨n ^ 2 ^ k, hk⟩
  have hc' : (n ^ 2 ^ k) ^ p ^ c = 1 := congrArg Subtype.val hc
  have hx : n ^ p ^ c ∈ N := N.pow_mem hn _
  have hx1 : n ^ p ^ c = 1 := by
    refine hker2 _ hx k ?_
    rw [← pow_mul, mul_comm, pow_mul]
    exact hc'
  exact E1.mem_of_pow_mem_of_coprime (hcop2p k c) hk (by rw [hx1]; exact P.one_mem)

theorem eOne_closed {B : Subgroup Q} (hE : E1.EOne Q B) {N : Subgroup Q} [N.Normal]
    (hNB : IsPGroup 2 ↥⁅B, N⁆) :
    IsSylowIn 2 (CFSG.Open.pCore 2 Q ⊓ N) N ∧ ¬ B ≤ N := by
  obtain ⟨p, hp, hp2, h22, -, hPB, hB2⟩ := hE
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Nb := N.map π with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hbar : IsPGroup 2 ↥⁅E1.barO2 Q B, Nb⁆ := by
    have : ⁅E1.barO2 Q B, Nb⁆ = (⁅B, N⁆).map π := by
      rw [E1.barO2, hNb, Subgroup.map_commutator]
    rw [this]
    exact hNB.map π
  have h2P : ∀ x : Q ⧸ CFSG.Open.pCore 2 Q,
      ∃ k : ℕ, x ^ 2 ^ k ∈ CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) := by
    intro x
    obtain ⟨y, rfl⟩ := hπs x
    obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP Q p) (fun q => by
        have hq : q ∈ E1.oTwoPTwo Q p := by rw [h22]; exact Subgroup.mem_top q
        exact hq) y
    refine ⟨k, ?_⟩
    have h1 : π (y ^ 2 ^ k) ∈ CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) := hk
    rwa [map_pow] at h1
  have hcore : Nb ≤ CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) :=
    eOne_core hp hp2 B6.pCore_quotient_pCore h2P hB2 hPB hbar
  have hpc : IsPGroup p ↥(CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup p
  have hnotdvd : ∀ {m : ℕ}, 2 ∣ p ^ m → False := fun {m} h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  refine ⟨⟨inf_le_right, (CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le inf_le_left, ?_⟩, ?_⟩
  · rw [Subgroup.inf_relIndex_right]
    have h1 := Subgroup.relIndex_ker N π
    rw [hπ, QuotientGroup.ker_mk'] at h1
    rw [h1]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hpc.to_le hcore)
    rw [hm]
    exact fun h => hnotdvd h
  · intro hBN
    have h2 : E1.barO2 Q B ≤ CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) :=
      (Subgroup.map_mono hBN).trans hcore
    have h3 := Subgroup.card_dvd_of_le h2
    rw [hB2] at h3
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hpc
    rw [hm] at h3
    exact hnotdvd h3

end Core

end E3

end CFSG.Quasithin
