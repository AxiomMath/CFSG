module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.Ch838

open CFSG.Assembly.LowTwoRank CFSG.BenderSuzuki.MatrixGroups

@[expose] def TwoNilpotent (A : Type*) [Group A] : Prop :=
  ∃ O : Subgroup A, O.Normal ∧ Odd (Nat.card O) ∧ ∀ a : A, ∃ k : ℕ, a ^ 2 ^ k ∈ O

theorem TwoNilpotent.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : TwoNilpotent A) : TwoNilpotent B := by
  obtain ⟨O, hO, hodd, h2⟩ := h
  refine ⟨O.map e.toMonoidHom, hO.map _ e.surjective, ?_, fun b => ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hodd
  · obtain ⟨k, hk⟩ := h2 (e.symm b)
    exact ⟨k, ⟨e.symm b ^ 2 ^ k, hk, by simp⟩⟩

theorem two_pow_succ_dvd_of_orderOf {A : Type*} [Group A] [Finite A] {a : A} {v : ℕ}
    (h : orderOf (a ^ 2 ^ v) = 2) : 2 ^ (v + 1) ∣ Nat.card A := by
  have h1 : a ^ 2 ^ (v + 1) = 1 := by
    have h0 := pow_orderOf_eq_one (a ^ 2 ^ v)
    rw [h] at h0
    rw [pow_succ, pow_mul]
    exact h0
  have h2 : a ^ 2 ^ v ≠ 1 := fun h' => by
    rw [h', orderOf_one] at h
    exact absurd h (by norm_num)
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hjv : j = v + 1 := by
    by_contra hne
    apply h2
    rw [← orderOf_dvd_iff_pow_eq_one, hj']
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← hjv, ← hj']
  exact orderOf_dvd_natCard a

theorem TwoNilpotent.of_normal_comm {A : Type*} [Group A] [Finite A] (N : Subgroup A)
    [hN : N.Normal] (hc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (h2 : ∀ a : A, ∃ k : ℕ, a ^ 2 ^ k ∈ N) :
    TwoNilpotent A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := (Nat.card N).factorization 2 with hv
  let φ : ↥N →* ↥N :=
    { toFun := fun a => a ^ 2 ^ v
      map_one' := one_pow _
      map_mul' := fun a b => (Commute.mul_pow (Subtype.ext (hc a a.2 b b.2)) _) }
  set O := φ.range.map N.subtype with hO
  have hmem : ∀ n ∈ N, n ^ 2 ^ v ∈ O := fun n hn => ⟨⟨n, hn⟩ ^ 2 ^ v, ⟨⟨n, hn⟩, rfl⟩, rfl⟩
  refine ⟨O, ⟨fun x hx g => ?_⟩, ?_, fun a => ?_⟩
  · obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hx
    have e : g * ((n ^ 2 ^ v : ↥N) : A) * g⁻¹ = (g * (n : A) * g⁻¹) ^ 2 ^ v := by
      rw [conj_pow, Subgroup.coe_pow]
    change g * ((n ^ 2 ^ v : ↥N) : A) * g⁻¹ ∈ O
    rw [e]
    exact hmem _ (hN.conj_mem _ n.2 g)
  · rw [hO, Subgroup.card_map_of_injective N.subtype_injective, Nat.odd_iff]
    by_contra hne
    have h2' : 2 ∣ Nat.card φ.range := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨⟨y, ⟨n, rfl⟩⟩, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    have hy' : orderOf (n ^ 2 ^ v) = 2 :=
      (Subgroup.orderOf_coe (⟨φ n, ⟨n, rfl⟩⟩ : ↥φ.range)).trans hy
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two
      (two_pow_succ_dvd_of_orderOf hy')
  · obtain ⟨k, hk⟩ := h2 a
    refine ⟨k + v, ?_⟩
    rw [pow_add, pow_mul]
    exact hmem _ hk

theorem TwoNilpotent.of_normal_odd {A : Type*} [Group A] [Finite A] (N : Subgroup A)
    [N.Normal] (hN : Odd (Nat.card N)) (hc : ∀ a b : A ⧸ N, a * b = b * a) :
    TwoNilpotent A := by
  obtain ⟨Ob, hOb, hodd, h2⟩ := TwoNilpotent.of_normal_comm (⊤ : Subgroup (A ⧸ N))
    (fun a _ b _ => hc a b) (fun a => ⟨0, by simp⟩)
  set π := QuotientGroup.mk' N with hπ
  refine ⟨Ob.comap π, hOb.comap _, ?_, fun a => ?_⟩
  · set ψ : ↥(Ob.comap π) →* A ⧸ N := π.comp (Ob.comap π).subtype with hψ
    have hrange : ψ.range = Ob := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), top_inf_eq]
    have hle : N ≤ Ob.comap π := fun x hx => by
      change π x ∈ Ob
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact Ob.one_mem
    have hker : Nat.card ψ.ker = Nat.card N := by
      have h1 : ψ.ker = N.subgroupOf (Ob.comap π) := by
        ext x
        simp [hψ, hπ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
      rw [h1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hcard : Nat.card ↥(Ob.comap π) = Nat.card N * Nat.card Ob := by
      rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, hrange, hker]
    rw [hcard]
    exact hN.mul hodd
  · obtain ⟨k, hk⟩ := h2 (π a)
    exact ⟨k, by simpa using hk⟩

theorem twoNilpotent_dihedral (n : ℕ) [NeZero n] : TwoNilpotent (DihedralGroup n) := by
  have key : ∀ g : DihedralGroup n,
      g * DihedralGroup.r 1 * g⁻¹ ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) := by
    rintro (i | i)
    · rw [DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r,
        show i + 1 + -i = 1 by ring]
      exact Subgroup.mem_zpowers _
    · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        show i - (i + 1) = -1 by ring, ← DihedralGroup.inv_r]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hN : (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (key g) k
  refine TwoNilpotent.of_normal_comm (Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)))
    (fun a ha b hb => ?_) fun a => ?_
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self _ i j).eq
  · rcases a with i | i
    · refine ⟨0, ?_⟩
      rw [pow_zero, pow_one, ← ZMod.natCast_zmod_val i, ← DihedralGroup.r_one_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · refine ⟨1, ?_⟩
      rw [pow_one, sq, DihedralGroup.sr_mul_self]
      exact Subgroup.one_mem _

theorem three_dvd_card_psl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    3 ∣ Nat.card (PSL2MatrixGroup (GaloisField p 1)) := by
  rw [CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField hp2 one_ne_zero]
  obtain ⟨q, rfl⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have e : (2 * q + 1) ^ 1 * ((2 * q + 1) ^ (2 * 1) - 1) / 2 = 2 * (q * (q + 1) * (2 * q + 1)) := by
    have h1 : (2 * q + 1) ^ (2 * 1) - 1 = 4 * (q * (q + 1)) := by
      have : (2 * q + 1) ^ (2 * 1) = 4 * (q * (q + 1)) + 1 := by ring
      omega
    rw [h1, pow_one]
    have : (2 * q + 1) * (4 * (q * (q + 1))) = 2 * (2 * (q * (q + 1) * (2 * q + 1))) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [e]
  refine Dvd.dvd.mul_left ?_ 2
  rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h | h | h
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _) _
  · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _

theorem twoNilpotent_of_psl2 {K : Type} [Group K] [Finite K]
    {p : ℕ} (hK : StatedClassicalModel K .PSL 2 p 1) (Y : Subgroup K)
    (hY3 : ¬ 3 ∣ Nat.card Y) : TwoNilpotent ↥Y := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := hK
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => hadm.2.2.2.1 (by rw [h, pow_one])
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set e' : K ≃* PSL2MatrixGroup F := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  set Y' := Y.map e'.toMonoidHom with hY'
  have eY : ↥Y ≃* ↥Y' := Y.equivMapOfInjective e'.toMonoidHom e'.injective
  have hcard : Nat.card ↥Y' = Nat.card ↥Y := (Nat.card_congr eY.toEquiv).symm
  suffices h : TwoNilpotent ↥Y' from h.of_mulEquiv eY.symm
  have hY3' : ¬ 3 ∣ Nat.card ↥Y' := hcard ▸ hY3
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF Y' with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hN, -, hNcard, hCcyc, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨eL⟩⟩ |
      ⟨m, hm, hmf, -⟩
  ·
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (@CFSG.IsElementaryAbelian.isPGroup p ↥Y' _ hel)
    exact ⟨⊤, inferInstance, by rw [Subgroup.card_top, hk]; exact hpodd.pow,
      fun _ => ⟨0, Subgroup.mem_top _⟩⟩
  ·
    exact TwoNilpotent.of_normal_comm ⊤ (fun a _ b _ => mul_comm' a b)
      (fun _ => ⟨0, Subgroup.mem_top _⟩)
  ·
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hz
      exact absurd hz Nat.card_pos.ne'
    have : NeZero z := ⟨hz0⟩
    exact (twoNilpotent_dihedral z).of_mulEquiv eD.symm
  · exfalso
    apply hY3'
    rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · exfalso
    apply hY3'
    rw [Nat.card_congr eS4.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · exfalso
    apply hY3'
    rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  ·
    refine TwoNilpotent.of_normal_odd N (by rw [hNcard]; exact hpodd.pow) fun a b => ?_
    have hmem : ∀ x : ↥Y', ∃ c ∈ C, (x : ↥Y' ⧸ N) = (c : ↥Y' ⧸ N) := by
      intro x
      have hx : x ∈ ((N ⊔ C : Subgroup ↥Y') : Set ↥Y') := by
        rw [hsup]
        exact Subgroup.mem_top x
      rw [Subgroup.normal_mul] at hx
      obtain ⟨n, hn, c, hc, rfl⟩ := hx
      refine ⟨c, hc, ?_⟩
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨c₁, hc₁, h₁⟩ := hmem x
    obtain ⟨c₂, hc₂, h₂⟩ := hmem y
    rw [h₁, h₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨c₁, hc₁⟩ : ↥C) ⟨c₂, hc₂⟩))
  · exfalso
    obtain rfl : m = 1 := Nat.dvd_one.mp hmf
    apply hY3'
    rw [Nat.card_congr eL.toEquiv]
    exact three_dvd_card_psl2 hp2
  · exfalso
    exact hm (by have := Nat.le_of_dvd one_pos hmf; omega)

end CFSG.Quasithin.H13.Ch838
