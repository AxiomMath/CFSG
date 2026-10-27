module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NQs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Nq

variable {G : Type} [Group G]

theorem seven_dvd_card_SL {m : ℕ} (hm : 3 ≤ m) :
    7 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  have : NeZero m := ⟨by omega⟩
  rw [Matrix.card_SL_field (𝔽 := ZMod 2) m, ZMod.card]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hmem : (⟨k, by omega⟩ : Fin (k + 3)) ∈ Finset.univ := Finset.mem_univ _
  refine dvd_trans ?_
    (Finset.dvd_prod_of_mem (fun i : Fin (k + 3) => 2 ^ (k + 3) - 2 ^ (i : ℕ)) hmem)
  show 7 ∣ 2 ^ (k + 3) - 2 ^ k
  have e : 2 ^ (k + 3) - 2 ^ k = 7 * 2 ^ k := Nat.sub_eq_of_eq_add (by ring)
  rw [e]
  exact dvd_mul_right 7 _

theorem seven_dvd_card_of_surjective {D : Type*} [Group D] [Finite D] {m : ℕ} (hm : 3 ≤ m)
    (π : D →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) (hπ : Function.Surjective π) :
    7 ∣ Nat.card D :=
  (seven_dvd_card_SL hm).trans (Subgroup.card_dvd_of_surjective (f := π) hπ)

theorem mem_oTwoZIn {L : Subgroup G} {x : G} :
    x ∈ oTwoZIn L ↔ ∃ hx : x ∈ L,
      (QuotientGroup.mk ⟨x, hx⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  unfold oTwoZIn preimageModTwoCore
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_oTwoZIn_iff_comm {K : Subgroup G} {x : G} :
    x ∈ oTwoZIn K ↔ x ∈ K ∧ ∀ w ∈ K, x * w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
  rw [mem_oTwoZIn]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun w hw => ?_⟩
    set a : ↥K := ⟨x, hx⟩
    set b : ↥K := ⟨w, hw⟩
    have h1 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk b)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h3 := (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem _ h1 (a * b)
    have e : a * b * ((b * a)⁻¹ * (a * b)) * (a * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by group
    rw [e] at h3
    exact ⟨_, h3, rfl⟩
  · rintro ⟨hx, hc⟩
    refine ⟨hx, Subgroup.mem_center_iff.mpr fun g => ?_⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
    set a : ↥K := ⟨x, hx⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨y, hy, hyx⟩ := hc b b.2
    have hy' : y ∈ CFSG.pCore 2 ↥K := by exact hy
    have hyab : y = a * b * a⁻¹ * b⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_subtype] at hyx
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hyx, a])
    have h3 := (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem _ hy' (a * b)⁻¹
    have e : (a * b)⁻¹ * (a * b * a⁻¹ * b⁻¹) * (a * b)⁻¹⁻¹ = (b * a)⁻¹ * (a * b) := by group
    rw [hyab, e] at h3
    exact h3

theorem pCoreOf_le_oTwoZIn (K : Subgroup G) : pCoreOf 2 K ≤ oTwoZIn K := fun x hx => by
  refine mem_oTwoZIn_iff_comm.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K hx, fun w hw => ?_⟩
  have h1 : w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hw) _).mp
      ((pCoreOf 2 K).inv_mem hx)
  have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 K).mul_mem hx h1

theorem le_normalizer_oTwoZIn {K X : Subgroup G} (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer (oTwoZIn K : Set G) := by
  intro g hg
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := hX hg
  have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hgK
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_oTwoZIn_iff_comm, mem_oTwoZIn_iff_comm]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgK x).mp hx, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) w).mp hw
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hgO _).mp (hc _ hw')
    have e : g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ := by group
    rwa [e] at h1
  · rintro ⟨hx, hc⟩
    have hx' : x ∈ K := by
      have h0 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) _).mp hx
      have e0 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e0] at h0
    refine ⟨hx', fun w hw => ?_⟩
    have hw' : g * w * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK w).mp hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgO) _).mp (hc _ hw')
    have e : g⁻¹ * (g * x * g⁻¹ * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹) * g⁻¹⁻¹ =
        x * w * x⁻¹ * w⁻¹ := by group
    rwa [e] at h1

theorem pCoreOf_sup_inf_le [Finite G] (K Q : Subgroup G) : pCoreOf 2 (K ⊔ Q) ⊓ K ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact Sec1216Gen.mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ Q) ((le_sup_left : K ≤ K ⊔ Q) hk))
    (Subgroup.le_normalizer hk)

theorem mem_oTwoZIn_of_mem_sup [Finite G] {K Q : Subgroup G}
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K)
    (h : k ∈ pCoreOf 2 (K ⊔ Q) ⊔ oTwoZIn K) : k ∈ oTwoZIn K := by
  have hZn : K ⊔ Q ≤ Subgroup.normalizer (oTwoZIn K : Set G) :=
    le_normalizer_oTwoZIn (sup_le Subgroup.le_normalizer hQK)
  rw [sup_comm] at h
  have hset := A4.coe_sup_eq_mul_of_mul_comm (mul_comm_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊔ Q)).trans hZn))
  have h2 : k ∈ ((oTwoZIn K ⊔ pCoreOf 2 (K ⊔ Q) : Subgroup G) : Set G) := h
  rw [hset] at h2
  obtain ⟨b, hb, a, ha, rfl⟩ := h2
  have hbK : b ∈ K := (mem_oTwoZIn_iff_comm.mp hb).1
  have haK : a ∈ K := by
    have : b⁻¹ * (b * a) ∈ K := K.mul_mem (K.inv_mem hbK) hk
    simpa using this
  exact (oTwoZIn K).mul_mem hb (pCoreOf_le_oTwoZIn K (pCoreOf_sup_inf_le K Q ⟨ha, haK⟩))

theorem alt_eq_one_of_mem_oTwoZIn {K : Subgroup G} {r : ℕ} (hr : 4 ≤ r)
    (α : ↥K →* alternatingGroup (Fin r)) (hα : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥K) {x : G} (hx : x ∈ oTwoZIn K) (hxK : x ∈ K) :
    α ⟨x, hxK⟩ = 1 := by
  obtain ⟨hx', hc⟩ := mem_oTwoZIn.mp hx
  have hcen : α ⟨x, hxK⟩ ∈ Subgroup.center (alternatingGroup (Fin r)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨w, rfl⟩ := hα g
    have h1 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk w)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, ← hk,
      MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h1
    exact h1
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; exact hr), Subgroup.mem_bot] at hcen
  exact hcen

theorem smul_eq_of_orderOf_seven {Γ α : Type*} [Group Γ] [MulAction Γ α] {g : Γ}
    (hg : orderOf g = 7) {a : α} {s : Finset α} (hs : s.card < 7) (hmem : ∀ i : ℕ, g ^ i • a ∈ s) :
    g • a = a := by
  classical
  let f : Fin 7 → ↥s := fun i => ⟨g ^ (i : ℕ) • a, hmem i⟩
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hs)
  have hfij' : g ^ (i : ℕ) • a = g ^ (j : ℕ) • a := congrArg Subtype.val hfij
  obtain ⟨d, hd0, hd7, hda⟩ : ∃ d : ℕ, 0 < d ∧ d < 7 ∧ g ^ d • a = a := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · refine ⟨(j : ℕ) - i, by omega, by omega, ?_⟩
      have e : g ^ (j : ℕ) = g ^ (i : ℕ) * g ^ ((j : ℕ) - i) := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_smul] at hfij'
      have := congrArg (fun y => (g ^ (i : ℕ))⁻¹ • y) hfij'
      simpa [inv_smul_smul] using this.symm
    · refine ⟨(i : ℕ) - j, by omega, by omega, ?_⟩
      have e : g ^ (i : ℕ) = g ^ (j : ℕ) * g ^ ((i : ℕ) - j) := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_smul] at hfij'
      have := congrArg (fun y => (g ^ (j : ℕ))⁻¹ • y) hfij'
      simpa [inv_smul_smul] using this
  have hst : g ^ d ∈ MulAction.stabilizer Γ a := hda
  have hpow : (g ^ d) ^ (d ^ 5) ∈ MulAction.stabilizer Γ a := Subgroup.pow_mem _ hst _
  have hmod : d * d ^ 5 % 7 = 1 := by interval_cases d <;> norm_num
  have e : (g ^ d) ^ (d ^ 5) = g := by
    rw [← pow_mul, ← pow_mod_orderOf, hg, hmod, pow_one]
  rw [e] at hpow
  exact hpow

open scoped Pointwise in
theorem false_of_orderOf_seven_mem_stabilizer {P : Finset (Finset (Fin 7))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (hc : Multiset.card sizes < 7) (hs : ∀ x ∈ sizes, x < 7)
    {σ : Equiv.Perm (Fin 7)} (hσ : orderOf σ = 7)
    (hst : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P) : False := by
  classical
  have hσP : σ • P = P := hst
  have hpowP : ∀ i : ℕ, σ ^ i • P = P := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, mul_smul, hσP, ih]
  have hPcard : P.card < 7 := by
    have h1 := congrArg Multiset.card hP.2.2.2
    rw [Multiset.card_map] at h1
    rw [Finset.card_def, h1]
    exact hc
  have hBfix : ∀ B ∈ P, σ • B = B := by
    intro B hB
    refine smul_eq_of_orderOf_seven hσ hPcard fun i => ?_
    rw [← hpowP i]
    exact Finset.smul_mem_smul_finset hB
  have hfix : ∀ x : Fin 7, σ x = x := by
    intro x
    have hx : x ∈ P.biUnion id := by rw [hP.2.2.1]; exact Finset.mem_univ x
    obtain ⟨B, hBP, hxB⟩ := Finset.mem_biUnion.mp hx
    have hBc : B.card < 7 := hs _ (hP.2.2.2 ▸ Multiset.mem_map_of_mem _ hBP)
    have hpowB : ∀ i : ℕ, σ ^ i • B = B := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, mul_smul, hBfix B hBP, ih]
    have := smul_eq_of_orderOf_seven hσ hBc (a := x) fun i => by
      rw [← hpowB i]
      exact Finset.smul_mem_smul_finset hxB
    exact this
  have h1 : σ = 1 := Equiv.ext hfix
  rw [h1, orderOf_one] at hσ
  omega

theorem false_of_orderOf_seven_commute_swap {n : ℕ} (hn : n ≤ 8) {σ τ : Equiv.Perm (Fin n)}
    (hσ : orderOf σ = 7) (hτ : τ.IsSwap) (hc : σ * τ = τ * σ) : False := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hτ
  have hcx : ∀ x, σ (Equiv.swap a b x) = Equiv.swap a b (σ x) := fun x => by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f x) hc
    simpa [Equiv.Perm.mul_apply] using this
  have hab' : ∀ x ∈ ({a, b} : Finset (Fin n)), σ x ∈ ({a, b} : Finset (Fin n)) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    by_contra hnot
    have hnot' := not_or.mp hnot
    have hs : Equiv.swap a b (σ x) = σ x := Equiv.swap_apply_of_ne_of_ne hnot'.1 hnot'.2
    have h1 := hcx x
    rw [hs] at h1
    rcases hx with rfl | rfl
    · rw [Equiv.swap_apply_left] at h1
      exact hab (σ.injective h1).symm
    · rw [Equiv.swap_apply_right] at h1
      exact hab (σ.injective h1)
  have hiter : ∀ x ∈ ({a, b} : Finset (Fin n)), ∀ i : ℕ, (σ ^ i) x ∈ ({a, b} : Finset (Fin n)) := by
    intro x hx i
    induction i with
    | zero => simpa using hx
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hab' _ ih
  have hcard2 : ({a, b} : Finset (Fin n)).card < 7 := by
    have := Finset.card_le_two (a := a) (b := b)
    omega
  have hfa : σ a = a := smul_eq_of_orderOf_seven hσ hcard2 (a := a)
    fun i => hiter a (by simp) i
  have hfb : σ b = b := smul_eq_of_orderOf_seven hσ hcard2 (a := b)
    fun i => hiter b (by simp) i
  have hpa : ∀ i : ℕ, (σ ^ i) a = a := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hfa]
  have hpb : ∀ i : ℕ, (σ ^ i) b = b := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hfb]
  have hfix : ∀ x : Fin n, σ x = x := by
    intro x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hfa
      · exact hfb
    · have hcard : (Finset.univ \ ({a, b} : Finset (Fin n))).card < 7 := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
          Finset.card_pair hab]
        omega
      refine smul_eq_of_orderOf_seven hσ hcard (a := x) fun i => ?_
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hmem => hx ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton, Equiv.Perm.smul_def] at hmem
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hmem with h | h
      · left
        exact (σ ^ i).injective (by rw [h, hpa])
      · right
        exact (σ ^ i).injective (by rw [h, hpb])
  have h1 : σ = 1 := Equiv.ext hfix
  rw [h1, orderOf_one] at hσ
  omega

theorem isSolvable_of_isBorelIn {Γ : Type} [Group Γ] [Finite Γ] {X B : Subgroup Γ}
    (h : CFSG.Quasithin.IsBorelIn X B) : Group.IsSolvable ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, rfl⟩ := h
  set B := X ⊓ Subgroup.normalizer (S : Set Γ) with hB
  have hSB : S ≤ B := le_inf hS.1 Subgroup.le_normalizer
  have hN : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr inf_le_right
  have hodd : Odd (Nat.card (↥B ⧸ S.subgroupOf B)) := by
    rw [← Subgroup.index_eq_card]
    have h1 := Subgroup.relIndex_mul_relIndex S B X hSB inf_le_left
    have h2 : ¬ 2 ∣ S.relIndex B := fun h2 =>
      hS.2.2 (show 2 ∣ S.relIndex X by rw [← h1]; exact dvd_mul_of_dvd_left h2 _)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have : Group.IsSolvable (↥B ⧸ S.subgroupOf B) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsNilpotent ↥(S.subgroupOf B) := (hS.2.1.comap_subtype).isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (S.subgroupOf B)

theorem false_of_perfect_le_solvable {Γ : Type*} [Group Γ] {D B : Subgroup Γ}
    (hD : ⁅D, D⁆ = D) (hDB : D ≤ B) [Group.IsSolvable ↥B] (h7 : 7 ∣ Nat.card ↥D) : False := by
  have : Group.IsSolvable ↥D :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDB)
  have h := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hD
  rw [h, Subgroup.card_bot] at h7
  norm_num at h7

theorem autOn_perfect {A U : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) : ⁅autOn A U, autOn A U⁆ = autOn A U := by
  have h1 : ⁅A.subgroupOf (Subgroup.normalizer (U : Set G)),
      A.subgroupOf (Subgroup.normalizer (U : Set G))⁆ =
        A.subgroupOf (Subgroup.normalizer (U : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (U : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAU, hA]
  unfold autOn
  rw [← Subgroup.map_commutator, h1]

theorem exists_orderOf_seven {Γ : Type*} [Group Γ] [Finite Γ] {D : Subgroup Γ}
    (h7 : 7 ∣ Nat.card ↥D) : ∃ x ∈ D, orderOf x = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

open scoped Pointwise in
theorem false_of_map_eq_stabilizer {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (e : ↥A ≃* Equiv.Perm (Fin 7)) {P : Finset (Finset (Fin 7))} {sizes : Multiset ℕ}
    (hP : IsPartitionOfType P sizes) (hc : Multiset.card sizes < 7) (hs : ∀ x ∈ sizes, x < 7)
    (hmap : (B.subgroupOf A).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7))
    {x : Γ} (hxB : x ∈ B) (hxA : x ∈ A) (hx : orderOf x = 7) : False := by
  have h1 : e ⟨x, hxA⟩ ∈
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) := by
    rw [← hmap]
    exact ⟨⟨x, hxA⟩, Subgroup.mem_subgroupOf.mpr hxB, rfl⟩
  have h2 : orderOf (e ⟨x, hxA⟩) = 7 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hx
  exact false_of_orderOf_seven_mem_stabilizer hP hc hs h2 h1.1

theorem card_quot_eq_of_surjective {K : Type*} [Group K] {Hq : Type*} [Group Hq] (α : K →* Hq)
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 K) :
    Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card Hq :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem seven_dvd_card_quot {K : Type*} [Group K] [Finite K] (h7 : 7 ∣ Nat.card K) :
    7 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K)
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  rw [h1, he] at h7
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right e (by norm_num)) h7

theorem false_of_relIndex_thirtyFive [Finite G] {M K : Subgroup G}
    (hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520) (hidx : M.relIndex K = 35)
    (h7 : 7 ∣ Nat.card ↥(M ⊓ K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex ⊥ (M ⊓ K) K bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right,
    hidx] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  rw [hq, he] at h2
  have h49 : 49 ∣ 2520 * 2 ^ e := by
    rw [← h2, ← h1]
    exact mul_dvd_mul h7 (by norm_num : 7 ∣ 35)
  have h3 := Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_right e (by norm_num : Nat.Coprime 49 2)) h49
  norm_num at h3

theorem false_of_caseB [Finite G] {K R U : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hC : (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    {r : ℕ} (hr5 : 5 ≤ r) (hr8 : r ≤ 8) (α : ↥K →* alternatingGroup (Fin r))
    (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥K) {t₀ : G} (ht₀R : t₀ ∈ R)
    (ht₀U : t₀ ∈ Subgroup.normalizer (U : Set G)) {σ : Equiv.Perm (Fin r)} (hσ : σ.IsSwap)
    (hσc : ∀ (k : G) (hk : k ∈ K) (hk' : t₀ * k * t₀⁻¹ ∈ K),
      ((α ⟨t₀ * k * t₀⁻¹, hk'⟩ : alternatingGroup (Fin r)) : Equiv.Perm (Fin r)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin r)) * σ⁻¹)
    {l : G} (hlK : l ∈ K) (hlU : l ∈ Subgroup.normalizer (U : Set G))
    (hord : orderOf (conjAct U ⟨l, hlU⟩) = 7)
    (hcomm : conjAct U ⟨l, hlU⟩ * conjAct U ⟨t₀, ht₀U⟩ =
      conjAct U ⟨t₀, ht₀U⟩ * conjAct U ⟨l, hlU⟩) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hA : ∀ (g : G) (hg : g ∈ K), g ∈ Subgroup.centralizer (U : Set G) → α ⟨g, hg⟩ = 1 :=
    fun g hg hgC => alt_eq_one_of_mem_oTwoZIn (by omega) α hα hk
      (mem_oTwoZIn_of_mem_sup hRK hg (hC ⟨(le_sup_left : K ≤ K ⊔ R) hg, hgC⟩)) hg
  have hk1 : t₀ * l⁻¹ * t₀⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hRK ht₀R) _).mp (K.inv_mem hlK)
  have hgU : l * (t₀ * l⁻¹ * t₀⁻¹) ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ hlU (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₀U (Subgroup.inv_mem _ hlU))
      (Subgroup.inv_mem _ ht₀U))
  have hgC : l * (t₀ * l⁻¹ * t₀⁻¹) ∈ Subgroup.centralizer (U : Set G) := by
    have e : (⟨l * (t₀ * l⁻¹ * t₀⁻¹), hgU⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨l, hlU⟩ * (⟨t₀, ht₀U⟩ * (⟨l, hlU⟩ : ↥(Subgroup.normalizer (U : Set G)))⁻¹ *
          (⟨t₀, ht₀U⟩ : ↥(Subgroup.normalizer (U : Set G)))⁻¹) := rfl
    have h1 : conjAct U ⟨l * (t₀ * l⁻¹ * t₀⁻¹), hgU⟩ = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← mul_assoc, ← mul_assoc, hcomm]
      group
    exact A4.conjAct_eq_one_iff.mp h1
  have h1 := hA _ (K.mul_mem hlK hk1) hgC
  have e1 : (⟨l * (t₀ * l⁻¹ * t₀⁻¹), K.mul_mem hlK hk1⟩ : ↥K) =
      ⟨l, hlK⟩ * ⟨t₀ * l⁻¹ * t₀⁻¹, hk1⟩ := rfl
  rw [e1, map_mul] at h1
  have h2 := hσc l⁻¹ (K.inv_mem hlK) hk1
  have e2 : (⟨l⁻¹, K.inv_mem hlK⟩ : ↥K) = (⟨l, hlK⟩ : ↥K)⁻¹ := rfl
  rw [e2, map_inv] at h2
  set p : Equiv.Perm (Fin r) := (α ⟨l, hlK⟩ : Equiv.Perm (Fin r)) with hp
  have h1' : p * (σ * p⁻¹ * σ⁻¹) = 1 := by
    have h3 := congrArg (fun a : alternatingGroup (Fin r) => (a : Equiv.Perm (Fin r))) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h3
    rw [h2] at h3
    simpa [hp] using h3
  have hcomm' : p * σ = σ * p := by
    calc p * σ = p * (σ * p⁻¹ * σ⁻¹) * (σ * p) := by group
      _ = σ * p := by rw [h1', one_mul]
  have hp7 : p ^ 7 = 1 := by
    have hl7U : l ^ 7 ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ hlU 7
    have h3 : conjAct U ⟨l ^ 7, hl7U⟩ = 1 := by
      have e : (⟨l ^ 7, hl7U⟩ : ↥(Subgroup.normalizer (U : Set G))) = ⟨l, hlU⟩ ^ 7 := rfl
      rw [e, map_pow, ← hord, pow_orderOf_eq_one]
    have h4 := hA (l ^ 7) (K.pow_mem hlK 7) (A4.conjAct_eq_one_iff.mp h3)
    have e : (⟨l ^ 7, K.pow_mem hlK 7⟩ : ↥K) = ⟨l, hlK⟩ ^ 7 := rfl
    rw [e, map_pow] at h4
    have h5 := congrArg (fun a : alternatingGroup (Fin r) => (a : Equiv.Perm (Fin r))) h4
    simpa [hp] using h5
  have hp1 : p ≠ 1 := by
    intro hp1
    have h5 : α ⟨l, hlK⟩ = 1 := Subtype.ext hp1
    have h6 : (⟨l, hlK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by rw [← hk]; exact h5
    obtain ⟨e, he⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, h6⟩
    have h7 : l ^ 2 ^ e = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) he
      simpa using this
    have h8 : conjAct U ⟨l, hlU⟩ ^ 2 ^ e = 1 := by
      rw [← map_pow]
      have e' : (⟨l, hlU⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 2 ^ e = 1 := Subtype.ext h7
      rw [e', map_one]
    have h9 := orderOf_dvd_of_pow_eq_one h8
    rw [hord] at h9
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h9))
    omega
  exact false_of_orderOf_seven_commute_swap hr8 (orderOf_eq_prime hp7 hp1) hσ hcomm'

end Sec1211Nq

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

variable (S) in
include S in
theorem le_normalizer_Q {R : Subgroup G}
    (hR : IsSylowTwoOf R (Subgroup.normalizer (L : Set G) ⊓
      Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hQR : T ⊓ Subgroup.centralizer (V : Set G) ≤ R) :
    R ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have hRM : R ≤ Subgroup.normalizer (L : Set G) := hR.1.trans inf_le_left
  have hRQ : R ⊓ Subgroup.centralizer (V : Set G) = T ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_antisymm ?_ (le_inf hQR inf_le_right)
    exact (A4.isSylowTwoOf_iff_maximal.mp S.isSylowTwoOf_Q).2.2 _ (inf_le_inf_right _ hRM)
      (hR.2.1.to_le inf_le_left) (le_inf hQR inf_le_right)
  intro r hr
  rw [← hRQ]
  exact Sec1216Gen.mem_normalizer_inf (Subgroup.le_normalizer hr)
    (normalizer_le_normalizer_centralizer V (S.le_normalizer (hRM hr)))

theorem seven_dvd_card_lv (F : Frame S m) (hm : 3 ≤ m) :
    7 ∣ Nat.card ↥(Sec1216Lv.lv L (a₀ * c₀)) :=
  Sec1211Nq.seven_dvd_card_of_surjective hm _ (psi_lv_surjective F)

variable (S) in
theorem false_of_autOn_eq (h331 : Stmt3_3_1) (F : Frame S m) (hm : 3 ≤ m) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hlt : Sec1216Lv.lv L (a₀ * c₀) < K)
    (hKn : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {U : Subgroup G}
    (hKU : K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ Subgroup.normalizer (U : Set G))
    (hC : (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⊓ Subgroup.centralizer (U : Set G) ≤
      pCoreOf 2 (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⊔ oTwoZIn K)
    (hPX : autOn ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)) ⊓ K)
      U = autOn K U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  set Mv := M ⊓ H with hMvdef
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hKU
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) :=
    (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem))).trans hKn
  have hCK : ∀ k ∈ K, k ∈ Subgroup.centralizer (U : Set G) → k ∈ oTwoZIn K := fun k hk hkC =>
    Sec1211Nq.mem_oTwoZIn_of_mem_sup hQK hk (hC ⟨(le_sup_left : K ≤ K ⊔ Q) hk, hkC⟩)
  have hfac : ∀ k ∈ K, ∃ y ∈ Mv ⊓ K, y⁻¹ * k ∈ oTwoZIn K := by
    intro k hk
    have h1 : conjAct U ⟨k, hKN hk⟩ ∈ autOn K U :=
      Subgroup.mem_map.mpr ⟨⟨k, hKN hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [← hPX] at h1
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp h1
    have hyMK : (y : G) ∈ Mv ⊓ K := Subgroup.mem_subgroupOf.mp hy
    refine ⟨y, hyMK, hCK _ (K.mul_mem (K.inv_mem hyMK.2) hk) ?_⟩
    have h2 : conjAct U (y⁻¹ * ⟨k, hKN hk⟩) = 1 := by
      rw [map_mul, map_inv, hyk, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp h2
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hmk
  set A : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((Mv ⊓ K).subgroupOf K).map mk with hAdef
  have hZc : ∀ z : ↥K, (z : G) ∈ oTwoZIn K → mk z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro z hz
    obtain ⟨hz', hc⟩ := Sec1211Nq.mem_oTwoZIn.mp hz
    exact hc
  have hAn : A.Normal := by
    constructor
    rintro _ ⟨y, hy, rfl⟩ g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) g
    obtain ⟨y', hy', hz⟩ := hfac k k.2
    have hzK : y'⁻¹ * (k : G) ∈ K := K.mul_mem (K.inv_mem hy'.2) k.2
    have hcen := hZc ⟨_, hzK⟩ hz
    have hk : k = ⟨y', hy'.2⟩ * ⟨_, hzK⟩ := Subtype.ext (by simp)
    rw [hk, map_mul]
    have hcomm : mk ⟨_, hzK⟩ * mk y * (mk ⟨_, hzK⟩)⁻¹ = mk y := by
      rw [(Subgroup.mem_center_iff.mp hcen (mk y)).symm, mul_inv_cancel_right]
    rw [show mk ⟨y', hy'.2⟩ * mk ⟨_, hzK⟩ * mk y * (mk ⟨y', hy'.2⟩ * mk ⟨_, hzK⟩)⁻¹ =
        mk ⟨y', hy'.2⟩ * (mk ⟨_, hzK⟩ * mk y * (mk ⟨_, hzK⟩)⁻¹) * (mk ⟨y', hy'.2⟩)⁻¹ by group,
      hcomm, ← map_inv, ← map_mul, ← map_mul]
    have hy2 : (y : G) ∈ Mv ⊓ K := hy
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Mv ⊓ K).mul_mem ((Mv ⊓ K).mul_mem hy' hy2) ((Mv ⊓ K).inv_mem hy')
  have hAtop : A = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hAn with h | h
    · exact h
    · exfalso
      have htop : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) g
        obtain ⟨y', hy', hz⟩ := hfac k k.2
        have hzK : y'⁻¹ * (k : G) ∈ K := K.mul_mem (K.inv_mem hy'.2) k.2
        have hk : k = ⟨y', hy'.2⟩ * ⟨_, hzK⟩ := Subtype.ext (by simp)
        rw [hk, map_mul]
        exact Subgroup.mul_mem _ (h ⟨⟨y', hy'.2⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩)
          (hZc _ hz)
      have hsub : Subsingleton ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸
          Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      have hnt := hq.2.1.toNontrivial
      exact not_nontrivial_iff_subsingleton.mpr hsub hnt
  have hQ2 : IsPGroup 2 Q := S.hyp.sylow.1.to_le inf_le_left
  have hCV : Subgroup.centralizer (V : Set G) ≤ H :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.v_mem)
  have hQMv : Q ≤ Mv := le_inf (inf_le_left.trans S.hTL) (inf_le_right.trans hCV)
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQMv hQ2
  have hyp0 := S.hypC23_of_le h331 F hm le_rfl (Sec1216Lv.lv_le_centralizer L _) hR
    (hR.1.trans inf_le_right) hQR
  have hOH : pCoreOf 2 H ≤ Q := c2_1_pCore_le hyp0.radical
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hMvN : Mv ≤ Subgroup.normalizer (Lv : Set G) :=
    Sec1216Lv.le_normalizer_lv inf_le_left inf_le_right
  apply not_le_normalizer_of_lt F (by omega) hK hlt
  intro k hk
  have h1 : mk ⟨k, hk⟩ ∈ A := hAtop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := h1
  rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyk
  have hyMv : (y : G) ∈ Mv := (Subgroup.mem_subgroupOf.mp hy).1
  have hO : ((y⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
    exact ⟨_, hyk, rfl⟩
  have hO' : (y : G)⁻¹ * k ∈ Subgroup.normalizer (Lv : Set G) := by
    have := hMvN (hQMv (hOH (hOK hO)))
    simpa using this
  have e : k = (y : G) * ((y : G)⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hMvN hyMv) hO'

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
