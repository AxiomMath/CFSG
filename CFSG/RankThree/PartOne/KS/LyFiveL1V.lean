module

public import CFSG.RankThree.PartOne.KS.PlaneWitnessClass
public import CFSG.RankThree.Native.LyFiveLocal
public import CFSG.RankThree.PartOne.KS.LyFiveX

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.RankThree.Native Subgroup
open scoped Pointwise

@[expose] def sylowSub {G : Type*} [Group G] (a : G) (Q M : Subgroup G) (ha : a ∈ M)
    (hQN : (Q.subgroupOf M).Normal) : Subgroup G :=
  haveI := hQN
  ((Subgroup.zpowers (⟨a, ha⟩ : M)) ⊔ Q.subgroupOf M).map M.subtype

theorem mem_sylowSub {G : Type*} [Group G] {a : G} {Q M : Subgroup G} {ha : a ∈ M}
    {hQN : (Q.subgroupOf M).Normal} {g : G} (hQM : Q ≤ M) :
    g ∈ sylowSub a Q M ha hQN ↔ ∃ m : ℤ, ∃ q ∈ Q, g = a ^ m * q := by
  have := hQN
  unfold sylowSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ ((Subgroup.zpowers (⟨a, ha⟩ : M) ⊔ Q.subgroupOf M : Subgroup M) : Set M) := hy
    rw [Subgroup.mul_normal] at hy'
    obtain ⟨h, hh, n, hn, rfl⟩ := hy'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine ⟨m, n.1, Subgroup.mem_subgroupOf.mp hn, ?_⟩
    simp
  · rintro ⟨m, q, hq, rfl⟩
    refine ⟨(⟨a, ha⟩ : M) ^ m * ⟨q, hQM hq⟩, ?_, by simp⟩
    have : ((⟨a, ha⟩ : M) ^ m * ⟨q, hQM hq⟩ : M) ∈
        ((Subgroup.zpowers (⟨a, ha⟩ : M) : Set M) * (Q.subgroupOf M : Set M)) :=
      ⟨_, Subgroup.zpow_mem_zpowers _ _, ⟨q, hQM hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [← Subgroup.mul_normal] at this
    exact this

theorem mem_sylowSub_iff_nf {G : Type*} [Group G] {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 5} (hQ : FiveQRel x v ω) {a : G} (hax : a ^ 5 = x)
    {M : Subgroup G} {ha : a ∈ M} (hQM : fiveQ x v ≤ M)
    {hQN : ((fiveQ x v).subgroupOf M).Normal} {g : G} :
    g ∈ sylowSub a (fiveQ x v) M ha hQN ↔ ∃ k : ℕ, k < 5 ∧ ∃ c e, g = a ^ k * fiveNF x v c e := by
  rw [mem_sylowSub hQM]
  constructor
  · rintro ⟨m, q, hq, rfl⟩
    obtain ⟨r, j, hr, hmj⟩ : ∃ (r : ℕ) (j : ℤ), r < 5 ∧ m = 5 * j + r :=
      ⟨(m % 5).toNat, m / 5, by omega, by omega⟩
    have hc : Commute (x ^ j) (a ^ r) := by
      rw [← hax]; exact (Commute.pow_pow_self a 5 r).zpow_left j
    have e1 : a ^ m = x ^ j * a ^ r := by
      subst hmj; rw [zpow_add, zpow_mul]; simp [hax]
    have hxq : x ^ j * q ∈ fiveQ x v :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ FiveQRel.x_mem j) hq
    obtain ⟨c, e, hce⟩ := hQ.mem_range_nf hxq
    refine ⟨r, hr, c, e, ?_⟩
    calc a ^ m * q = (x ^ j * a ^ r) * q := by rw [e1]
      _ = (a ^ r * x ^ j) * q := by rw [hc.eq]
      _ = a ^ r * (x ^ j * q) := mul_assoc _ _ _
      _ = a ^ r * fiveNF x v c e := by rw [hce]
  · rintro ⟨k, -, c, e, rfl⟩
    exact ⟨k, fiveNF x v c e, FiveQRel.nf_mem c e, by simp⟩

theorem natCast_eq_of_val_eq (z : ZMod 5) (n : ℕ) (h : n = z.val) : (n : ZMod 5) = z := by
  rw [h]; exact ZMod.natCast_zmod_val z

theorem exists_fiveDigits (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    ∃ q < 3125, fiveDigits q = (c, e) := by
  have hc := ZMod.val_lt c
  have h0 := ZMod.val_lt (e 0)
  have h1 := ZMod.val_lt (e 1)
  have h2 := ZMod.val_lt (e 2)
  have h3 := ZMod.val_lt (e 3)
  obtain ⟨q, hq⟩ : ∃ q : ℕ,
      q = c.val + 5 * ((e 0).val + 5 * ((e 1).val + 5 * ((e 2).val + 5 * (e 3).val))) := ⟨_, rfl⟩
  refine ⟨q, by omega, ?_⟩
  refine Prod.ext ?_ (funext fun i => ?_)
  · show ((q % 5 : ℕ) : ZMod 5) = c
    exact natCast_eq_of_val_eq _ _ (by omega)
  · show (((q / 5 ^ (i.val + 1)) % 5 : ℕ) : ZMod 5) = e i
    fin_cases i
    · exact natCast_eq_of_val_eq _ _ (by simp; omega)
    · exact natCast_eq_of_val_eq _ _ (by simp; omega)
    · exact natCast_eq_of_val_eq _ _ (by simp; omega)
    · exact natCast_eq_of_val_eq _ _ (by simp; omega)

theorem card_J_factorization_five :
    (Nat.card J).factorization 5 = 6 := by
  rw [card_J, show (51765179004000000 : ℕ) = 5 ^ 6 * 3312971456256 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_eq_of_enum {G : Type*} [Group G] (V : Subgroup G) (u : ℕ → G) (N : ℕ)
    (hmem : ∀ g, g ∈ V ↔ ∃ n < N, g = u n) (hinj : ∀ n < N, ∀ n' < N, u n = u n' → n = n') :
    Nat.card V = N := by
  let f : Fin N → V := fun n => ⟨u n.val, (hmem _).2 ⟨n.val, n.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun n n' h => Fin.ext (hinj n.val n.2 n'.val n'.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨n, hn, rfl⟩ := (hmem g).1 hg
    exact ⟨⟨n, hn⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem conj_comp {G : Type*} [Group G] (g g' w u r : G) (e : ℕ) (hne : g⁻¹ * w * g = u)
    (hg' : g' * u * g'⁻¹ = r ^ e) : g' * g⁻¹ * w * (g' * g⁻¹)⁻¹ = r ^ e := by
  rw [← hg', ← hne]
  group

@[expose] noncomputable def uEl (n : ℕ) : J :=
  lyFiveAJ ^ (n / 3125) *
    fiveNF lyFiveXJ lyFiveVJ (fiveDigits (n % 3125)).1 (fiveDigits (n % 3125)).2

theorem fiveDigits_val (q : ℕ) : (fiveDigits q).1.val = q % 5 ∧
    ∀ i : Fin 4, ((fiveDigits q).2 i).val = q / 5 ^ (i.val + 1) % 5 := by
  refine ⟨?_, fun i => ?_⟩ <;> simp [fiveDigits, ZMod.val_natCast, Nat.mod_mod]

theorem fiveDigits_inj {q q' : ℕ} (hq : q < 3125) (hq' : q' < 3125)
    (h : fiveDigits q = fiveDigits q') : q = q' := by
  obtain ⟨c, e⟩ := fiveDigits_val q
  obtain ⟨c', e'⟩ := fiveDigits_val q'
  have hc : q % 5 = q' % 5 := by rw [← c, ← c', h]
  have he : ∀ i : Fin 4, q / 5 ^ (i.val + 1) % 5 = q' / 5 ^ (i.val + 1) % 5 := fun i => by
    rw [← e, ← e', h]
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : q / 625 % 5 = q' / 625 % 5 := by simpa using h3
  norm_num at h0 h1 h2
  omega

theorem uEl_inj :
    ∀ n < 15625, ∀ n' < 15625, uEl n = uEl n' → n = n' := by
  have hQ := lyFiveQRelJ
  have key : ∀ k k' : ℕ, k' ≤ k → k < 5 → ∀ N N' : J, N ∈ fiveQ lyFiveXJ lyFiveVJ →
      N' ∈ fiveQ lyFiveXJ lyFiveVJ → lyFiveAJ ^ k * N = lyFiveAJ ^ k' * N' → k = k' ∧ N = N' := by
    intro k k' hkk hk N N' hN hN' h
    have hj : lyFiveAJ ^ (k - k') = N' * N⁻¹ := by
      have e : lyFiveAJ ^ k = lyFiveAJ ^ k' * lyFiveAJ ^ (k - k') := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_assoc] at h
      have h2 := mul_left_cancel h
      rw [← h2, mul_inv_cancel_right]
    have hmem : lyFiveAJ ^ (k - k') ∈ fiveQ lyFiveXJ lyFiveVJ := by
      rw [hj]; exact Subgroup.mul_mem _ hN' (Subgroup.inv_mem _ hN)
    have h5 := hQ.pow_five_of_mem hmem
    rw [← pow_mul, show k - k' = (k - k') by rfl, mul_comm, pow_mul] at h5
    have hx : lyFiveXJ ^ (k - k') = 1 := h5
    rw [hQ.x_pow_eq_one_iff] at hx
    have hkk' : k - k' = 0 := by
      have := (ZMod.natCast_eq_zero_iff (k - k') 5).1 hx
      omega
    refine ⟨by omega, ?_⟩
    rw [hkk', pow_zero] at hj
    have := congrArg (· * N) hj
    simp only [one_mul, inv_mul_cancel_right] at this
    exact this
  intro n hn n' hn' h
  unfold uEl at h
  have hN := FiveQRel.nf_mem (x := lyFiveXJ) (v := lyFiveVJ) (fiveDigits (n % 3125)).1
    (fiveDigits (n % 3125)).2
  have hN' := FiveQRel.nf_mem (x := lyFiveXJ) (v := lyFiveVJ) (fiveDigits (n' % 3125)).1
    (fiveDigits (n' % 3125)).2
  have hk : n / 3125 = n' / 3125 ∧ fiveNF lyFiveXJ lyFiveVJ (fiveDigits (n % 3125)).1
      (fiveDigits (n % 3125)).2 = fiveNF lyFiveXJ lyFiveVJ (fiveDigits (n' % 3125)).1
      (fiveDigits (n' % 3125)).2 := by
    rcases le_total (n' / 3125) (n / 3125) with hle | hle
    · exact key _ _ hle (by omega) _ _ hN hN' h
    · obtain ⟨a1, a2⟩ := key _ _ hle (by omega) _ _ hN' hN h.symm
      exact ⟨a1.symm, a2.symm⟩
  obtain ⟨hk1, hk2⟩ := hk
  have hd := hQ.nf_injective hk2
  have hq := fiveDigits_inj (Nat.mod_lt n (by norm_num)) (Nat.mod_lt n' (by norm_num))
    (Prod.ext (congrArg Prod.fst hd) (congrArg Prod.snd hd))
  omega

theorem exists_V :
    ∃ V : Subgroup J, (∀ g, g ∈ V ↔ ∃ n < 15625, g = uEl n) ∧ Nat.card V = 15625 := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := lyFiveMRelJ.local_structure lyFiveCertJ
  have ha : lyFiveAJ ∈ Subgroup.closure ({lyFiveAJ, lyFiveBJ} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  let V : Subgroup J := sylowSub lyFiveAJ (fiveQ lyFiveXJ lyFiveVJ)
    (Subgroup.closure ({lyFiveAJ, lyFiveBJ} : Set J)) ha h6
  have hmem : ∀ g, g ∈ V ↔ ∃ n < 15625, g = uEl n := by
    intro g
    have hax : lyFiveAJ ^ 5 = lyFiveXJ := rfl
    rw [mem_sylowSub_iff_nf (G := J) lyFiveQRelJ hax h5]
    constructor
    · rintro ⟨k, hk, c, e, rfl⟩
      obtain ⟨q, hq, hqe⟩ := exists_fiveDigits c e
      refine ⟨k * 3125 + q, by omega, ?_⟩
      unfold uEl
      have e1 : (k * 3125 + q) / 3125 = k := by omega
      have e2 : (k * 3125 + q) % 3125 = q := by omega
      rw [e1, e2, hqe]
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n / 3125, by omega, _, _, rfl⟩
  exact ⟨V, hmem, card_eq_of_enum V uEl 15625 hmem uEl_inj⟩

theorem lyFiveYJ_pow5 :
    (lyFiveVJ 0 * lyFiveVJ 1) ^ 5 = 1 :=
  FiveQRel.pow_five_of_mem lyFiveQRelJ
    (Subgroup.mul_mem _ (FiveQRel.v_mem (x := lyFiveXJ) (v := lyFiveVJ) 0)
      (FiveQRel.v_mem (x := lyFiveXJ) (v := lyFiveVJ) 1))

theorem eq_one_of_conj_eq_one {G : Type*} [Group G] (g w : G) (h : g⁻¹ * w * g = 1) : w = 1 := by
  calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem conj_pow_five {G : Type*} [Group G] (g w : G) (h : w ^ 5 = 1) : (g⁻¹ * w * g) ^ 5 = 1 := by
  have := conj_pow (a := g⁻¹) (b := w) (i := 5)
  rw [inv_inv] at this
  rw [this, h]; group

theorem cover_of_enum {G : Type} [Group G] [Finite G] (hfac : (Nat.card G).factorization 5 = 6)
    (R : Set G) (V : Subgroup G) (u : ℕ → G) (hmem : ∀ g, g ∈ V ↔ ∃ n < 15625, g = u n)
    (hinj : ∀ n < 15625, ∀ n' < 15625, u n = u n' → n = n')
    (hcov : ∀ n < 15625, u n ≠ 1 → u n ^ 5 = 1 →
      ∃ g' : G, ∃ r ∈ R, ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧ g' * u n * g'⁻¹ = r ^ e) :
    ∀ w : G, orderOf w = 5 → ∃ g : G, ∃ r ∈ R, ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧ g * w * g⁻¹ = r ^ e := by
  have hVcard : Nat.card V = 15625 := card_eq_of_enum V u 15625 hmem hinj
  have hp : Nat.Prime 5 := Nat.prime_five
  have hcard : Nat.card V = 5 ^ (Nat.card (⊤ : Subgroup G)).factorization 5 := by
    rw [hVcard, Subgroup.card_top, hfac]; norm_num
  have hSyl := exists_sylow_of_card hp (le_top : V ≤ ⊤) hcard
  intro w hw
  obtain ⟨g, -, hgV⟩ := exists_conj_mem_sylow hp hSyl (Subgroup.mem_top w) hw
  obtain ⟨n, hn, hne⟩ := (hmem _).mp hgV
  have hw5 : w ^ 5 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have h5 : u n ^ 5 = 1 := by
    have := conj_pow_five g w hw5
    rw [hne] at this
    exact this
  have h1 : u n ≠ 1 := by
    intro h
    have hw1 : w = 1 := eq_one_of_conj_eq_one g w (hne.trans h)
    rw [hw1, orderOf_one] at hw
    omega
  obtain ⟨g', r, hr, e, he1, he4, hg'⟩ := hcov n hn h1 h5
  exact ⟨g' * g⁻¹, r, hr, e, he1, he4, conj_comp g g' w (u n) r e hne hg'⟩

theorem l1_final :
    ∀ w : J, orderOf w = 5 → ∃ g : J, ∃ r ∈ ({lyFiveXJ, lyFiveVJ 0 * lyFiveVJ 1} : Set J),
      ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧ g * w * g⁻¹ = r ^ e := by
  obtain ⟨V, hVmem, -⟩ := exists_V
  have hcov := ly_five_facts.2.2.2.2.2
  have e : ∀ n, Omega.fiveEl n = uEl n := fun n => by
    unfold Omega.fiveEl uEl
    rw [fiveA_eq, fiveX_eq, fiveV_eq]
  simp only [e, fiveX_eq, fiveY_eq] at hcov
  exact cover_of_enum card_J_factorization_five _ V uEl hVmem uEl_inj hcov

end CFSG.RankThree.PartOne.LyFive
