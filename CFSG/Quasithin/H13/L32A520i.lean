module

public import CFSG.Quasithin.H13.L32A520h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Holt
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

abbrev c0 (H Y : Subgroup G) : Subgroup G := centralizerSection H Y (pCoreOf 2 Y)

abbrev c1 (T L V H Y : Subgroup G) : Subgroup G :=
  centralizerSection H (l1 T L V ⊔ pCoreOf 2 Y) (pCoreOf 2 Y) ⊓
    centralizerSection H Y (l1 T L V ⊔ pCoreOf 2 Y)

abbrev dT (T L V H Y : Subgroup G) : Subgroup G := T ⊓ c1 T L V H Y

abbrev g1 (T L V H Y : Subgroup G) : Subgroup G :=
  c1 T L V H Y ⊓ Subgroup.normalizer ((dT T L V H Y : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_normalizer_cs {M X Z : Subgroup G} {g : G} (hgM : g ∈ Subgroup.normalizer (M : Set G))
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    g ∈ Subgroup.normalizer ((centralizerSection M X Z : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ Subgroup.normalizer (M : Set G) →
      g' ∈ Subgroup.normalizer (X : Set G) → g' ∈ Subgroup.normalizer (Z : Set G) →
      ∀ m ∈ centralizerSection M X Z, g' * m * g'⁻¹ ∈ centralizerSection M X Z := by
    intro g' h1 h2 h3 m hm
    obtain ⟨hmM, hmX, hmZ, hm⟩ := mem_centralizerSection.mp hm
    refine mem_centralizerSection.mpr ⟨(Subgroup.mem_normalizer_iff.mp h1 m).mp hmM,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer h2) m).mp hmX,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer h3) m).mp hmZ,
      fun x hx => ?_⟩
    have hx' : g'⁻¹ * x * g' ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem h2) x).mp hx
      simpa using this
    have h := hm _ hx'
    have e : x * (g' * m * g'⁻¹) * x⁻¹ * (g' * m * g'⁻¹)⁻¹ =
        g' * ((g'⁻¹ * x * g') * m * (g'⁻¹ * x * g')⁻¹ * m⁻¹) * g'⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp h3 _).mp h
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact key g hgM hgX hgZ m
  · intro hm
    have := key g⁻¹ (inv_mem hgM) (inv_mem hgX) (inv_mem hgZ) _ hm
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_zpowers_sup_cases {Q : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (Q : Set G)) (ha3 : a ^ 3 ∈ Q)
    (hb : b ∈ Subgroup.zpowers a ⊔ Q) : b ∈ Q ∨ a⁻¹ * b ∈ Q ∨ a * b ∈ Q := by
  rw [sup_comm] at hb
  obtain ⟨q, hq, c, hc, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (Subgroup.zpowers_le.mpr haN)).mp hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hdecomp : a ^ m = a ^ (m % 3) * (a ^ 3) ^ (m / 3) := by
    rw [← zpow_natCast a 3, ← zpow_mul, ← zpow_add]
    congr 1
    omega
  have h3 : (a ^ 3) ^ (m / 3) ∈ Q := Q.zpow_mem ha3 _
  have hnn : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have hlt : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  have haq : a * q * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp haN q).mp hq
  have haq' : a⁻¹ * q * a ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) q).mp hq
    simpa using this
  rw [hdecomp]
  interval_cases hr : m % 3
  · left
    rw [zpow_zero, one_mul]
    exact Q.mul_mem hq h3
  · right; left
    rw [zpow_one, show a⁻¹ * (q * (a * (a ^ 3) ^ (m / 3))) = (a⁻¹ * q * a) * (a ^ 3) ^ (m / 3) by
      group]
    exact Q.mul_mem haq' h3
  · right; right
    rw [show a * (q * (a ^ (2 : ℤ) * (a ^ 3) ^ (m / 3))) =
      (a * q * a⁻¹) * a ^ 3 * (a ^ 3) ^ (m / 3) by group]
    exact Q.mul_mem (Q.mul_mem haq ha3) h3

omit [Finite G] in
theorem sq_mem_cs {A Q : Subgroup G} (hQA : Q ≤ A) (hA3 : Q.relIndex A = 3)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hcube : ∀ a ∈ A, a ^ 3 ∈ Q) {h : G}
    (hhA : h ∈ Subgroup.normalizer (A : Set G)) (hhQ : h ∈ Subgroup.normalizer (Q : Set G))
    {a : G} (ha : a ∈ A) : a * (h * h) * a⁻¹ * (h * h)⁻¹ ∈ Q := by
  have hconjQ : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hhQ q).mp hq
  have key : ∀ b ∈ A, b⁻¹ * ((h * h) * b * (h * h)⁻¹) ∈ Q := by
    intro b hb
    by_cases hbQ : b ∈ Q
    · have h2 : (h * h) * b * (h * h)⁻¹ ∈ Q := by
        rw [show h * h * b * (h * h)⁻¹ = h * (h * b * h⁻¹) * h⁻¹ by group]
        exact hconjQ _ (hconjQ b hbQ)
      exact Q.mul_mem (Q.inv_mem hbQ) h2
    · have hc : h * b * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hhA b).mp hb
      have hA : A = Subgroup.zpowers b ⊔ Q := by
        have hle : Subgroup.zpowers b ⊔ Q ≤ A := sup_le (Subgroup.zpowers_le.mpr hb) hQA
        have hm := Subgroup.relIndex_mul_relIndex _ _ _
          (le_sup_right : Q ≤ Subgroup.zpowers b ⊔ Q) hle
        rw [hA3] at hm
        have hd : Q.relIndex (Subgroup.zpowers b ⊔ Q) ∣ 3 := ⟨_, hm.symm⟩
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
        · exact absurd ((Subgroup.relIndex_eq_one.mp h1)
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))) hbQ
        · rw [h1] at hm
          have h2 : (Subgroup.zpowers b ⊔ Q).relIndex A = 1 := by omega
          exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle
      have hbN : b ∈ Subgroup.normalizer (Q : Set G) := hAQ hb
      rcases mem_zpowers_sup_cases hbN (hcube b hb) (hA ▸ hc) with h1 | h1 | h1
      · exfalso
        apply hbQ
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hhQ) _).mp h1
        simpa [mul_assoc] using this
      ·
        have e : b⁻¹ * ((h * h) * b * (h * h)⁻¹) =
            (b⁻¹ * (h * b * h⁻¹)) * (h * (b⁻¹ * (h * b * h⁻¹)) * h⁻¹) := by group
        rw [e]
        exact Q.mul_mem h1 (hconjQ _ h1)
      ·
        have e : b⁻¹ * ((h * h) * b * (h * h)⁻¹) =
            (b⁻¹ * (b * (h * b * h⁻¹))⁻¹ * b) * (h * (b * (h * b * h⁻¹)) * h⁻¹) := by group
        rw [e]
        have hb' : b⁻¹ * (b * (h * b * h⁻¹))⁻¹ * b ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hbN) _).mp (Q.inv_mem h1)
          simpa using this
        exact Q.mul_mem hb' (hconjQ _ h1)
  have h1 := key a⁻¹ (A.inv_mem ha)
  simpa [mul_assoc] using h1

omit [Finite G] in
theorem not_dvd_index_of_fusionIsSylowIn [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : fusionIsSylowIn p P K) : ¬ p ∣ (P.subgroupOf K).index := by
  obtain ⟨R, hR⟩ := exists_sylow_map_eq_of_fusionIsSylowIn h
  have e : (R : Subgroup K) = P.subgroupOf K := by
    rw [← hR]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  rw [← e]
  exact R.not_dvd_index

theorem fusionIsSylowIn_of_isSylowTwoOf {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    fusionIsSylowIn 2 S H := by
  refine ⟨h.1, h.2.1, fun P hPH hP hSP => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := Subgroup.relIndex_mul_relIndex S P H hSP hPH
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : S.relIndex P ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card (S.subgroupOf P)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hj) hSP
  · exfalso
    apply h.2.2
    change 2 ∣ S.relIndex H
    rw [← hm, hj, pow_succ]
    exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _

omit [Finite G] in
theorem mul_pow_mem_of_mem {N : Subgroup G} {n g : G} (hn : n ∈ N)
    (hg : g ∈ Subgroup.normalizer (N : Set G)) : ∀ k : ℕ, (n * g) ^ k * (g ^ k)⁻¹ ∈ N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (n * g) ^ (k + 1) * (g ^ (k + 1))⁻¹ =
        ((n * g) ^ k * (g ^ k)⁻¹) * (g ^ k * n * (g ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ih ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hg k) n).mp hn)

omit [Finite G] in
theorem c1_le_H (T L V H Y : Subgroup G) : c1 T L V H Y ≤ H :=
  inf_le_left.trans (centralizerSection_le_left _ _ _)

namespace E9Ctx

variable {T L V H Y : Subgroup G} (C : E9Ctx T L V H Y)
include C

theorem HL1Q : H ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 Y : Subgroup G) : Set G) :=
  C.H_le_N_L1Q.1

theorem H_le_N_c0 : H ≤ Subgroup.normalizer ((c0 H Y : Subgroup G) : Set G) := fun _ hh =>
  mem_normalizer_cs (Subgroup.le_normalizer hh) (C.HY hh) (C.HQ hh)

theorem H_le_N_c1 : H ≤ Subgroup.normalizer ((c1 T L V H Y : Subgroup G) : Set G) := fun _ hh =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨mem_normalizer_cs (Subgroup.le_normalizer hh) (C.HL1Q hh) (C.HQ hh),
      mem_normalizer_cs (Subgroup.le_normalizer hh) (C.HY hh) (C.HL1Q hh)⟩

theorem c0_le_c1 : c0 H Y ≤ c1 T L V H Y := fun h hh => by
  obtain ⟨hH, hY, hQ, hc⟩ := mem_centralizerSection.mp hh
  exact Subgroup.mem_inf.mpr
    ⟨mem_centralizerSection.mpr ⟨hH, C.HL1Q hH, hQ, fun x hx => hc x (C.L1Q_le hx)⟩,
      mem_centralizerSection.mpr ⟨hH, hY, C.HL1Q hH, fun y hy => Subgroup.mem_sup_right (hc y hy)⟩⟩

theorem Y_le_c0 : Y ≤ c0 H Y := fun y hy =>
  mem_centralizerSection.mpr ⟨C.YH hy, Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 Y hy,
    fun x hx => C.comm x hx y hy⟩

theorem c0_le_N_K : c0 H Y ≤ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) := fun h hh => by
  obtain ⟨-, -, -, hc⟩ := mem_centralizerSection.mp hh
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  have h1 := hc k⁻¹ (kY_le T V Y (inv_mem hk))
  rw [show h * k * h⁻¹ = k * (k⁻¹ * h * k⁻¹⁻¹ * h⁻¹) by group]
  exact mul_mem hk (C.Q_le_K h1)

theorem c1_inf_le_c0 {h : G} (hh : h ∈ c1 T L V H Y)
    (hK : h ∈ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G)) : h ∈ c0 H Y := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hH, -, hQ, hc1⟩ := mem_centralizerSection.mp h1
  obtain ⟨-, hY, -, hc2⟩ := mem_centralizerSection.mp h2
  refine mem_centralizerSection.mpr ⟨hH, hY, hQ, fun y hy => ?_⟩
  have hy' : y ∈ kY T V Y ⊔ (l1 T L V ⊔ pCoreOf 2 Y) := by rw [C.K_sup]; exact hy
  obtain ⟨κ, hκ, ℓ, hℓ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (C.L1Q_le.trans C.Y_le_N_K)).mp hy'
  have hκY := kY_le T V Y hκ
  have e : κ * ℓ * h * (κ * ℓ)⁻¹ * h⁻¹ =
      κ * (ℓ * h * ℓ⁻¹ * h⁻¹) * κ⁻¹ * (κ * h * κ⁻¹ * h⁻¹) := by group
  rw [e]
  refine mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hκY) _).mp
    (hc1 ℓ hℓ)) ?_
  rw [← C.K_inf]
  refine ⟨?_, hc2 κ hκY⟩
  have h3 : h * κ⁻¹ * h⁻¹ ∈ kY T V Y := (Subgroup.mem_normalizer_iff.mp hK _).mp (inv_mem hκ)
  rw [show κ * h * κ⁻¹ * h⁻¹ = κ * (h * κ⁻¹ * h⁻¹) by group]
  exact mul_mem hκ h3

theorem odd_mem_c1 {h : G} (hh : h ∈ H) (hodd : Odd (orderOf h)) : h ∈ c1 T L V H Y := by
  have hmem := A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hodd)
  rw [pow_two] at hmem
  refine (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)) hmem
  · refine mem_centralizerSection.mpr ⟨mul_mem hh hh, mul_mem (C.HL1Q hh) (C.HL1Q hh),
      mul_mem (C.HQ hh) (C.HQ hh), fun a ha => ?_⟩
    exact sq_mem_cs le_sup_right C.L1Q3 (C.L1Q_le.trans (le_normalizer_pCoreOf 2 Y))
      (fun a ha => C.Y3 a (C.L1Q_le ha)) (C.HL1Q hh) (C.HQ hh) ha
  · refine mem_centralizerSection.mpr ⟨mul_mem hh hh, mul_mem (C.HY hh) (C.HY hh),
      mul_mem (C.HL1Q hh) (C.HL1Q hh), fun a ha => ?_⟩
    exact sq_mem_cs C.L1Q_le C.L1QY3 C.Y_le_N_L1Q (fun a ha => Subgroup.mem_sup_right (C.Y3 a ha))
      (C.HY hh) (C.HL1Q hh) ha

theorem exists_c1_not_c0 : ∃ y ∈ c1 T L V H Y, y ∉ c0 H Y ∧ ∃ n : ℕ, y ^ 3 ^ n = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₃, -, hS⟩ := exists_fusionIsSylowIn_ge (p := 3) IsPGroup.of_bot (bot_le : ⊥ ≤ H)
  by_contra hall
  push Not at hall
  have hSK : S₃ ≤ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) := fun s hs => by
    by_contra hsK
    obtain ⟨n, hn⟩ := hS.2.1 ⟨s, hs⟩
    have hn' : s ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hodd : Odd (orderOf s) :=
      Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hn')
    exact hall s (C.odd_mem_c1 (hS.1 hs) hodd) (fun h0 => hsK (C.c0_le_N_K h0)) n hn'
  apply not_dvd_index_of_fusionIsSylowIn hS
  rw [← C.H_le_N_L1Q.2]
  exact Subgroup.index_dvd_of_le fun s hs =>
    Subgroup.mem_subgroupOf.mpr (hSK (Subgroup.mem_subgroupOf.mp hs))

theorem Q_le_D : pCoreOf 2 Y ≤ dT T L V H Y :=
  le_inf C.QT ((pCoreOf_le 2 Y).trans (C.Y_le_c0.trans C.c0_le_c1))

theorem D_le_c0 : dT T L V H Y ≤ c0 H Y := fun _ hd => C.c1_inf_le_c0 hd.2 (C.T_le_N_K hd.1)

theorem D_sylow_c1 : fusionIsSylowIn 2 (dT T L V H Y) (c1 T L V H Y) :=
  fusionIsSylowIn_inf_of_le_normalizer' (fusionIsSylowIn_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.TH)) (c1_le_H T L V H Y) C.H_le_N_c1

theorem D_sylow_c0 : fusionIsSylowIn 2 (dT T L V H Y) (c0 H Y) :=
  ⟨C.D_le_c0, C.D_sylow_c1.2.1, fun P hP hPp hDP =>
    C.D_sylow_c1.2.2 P (hP.trans C.c0_le_c1) hPp hDP⟩

theorem D_sylow_g1 : fusionIsSylowIn 2 (dT T L V H Y) (g1 T L V H Y) :=
  ⟨le_inf inf_le_right Subgroup.le_normalizer, C.D_sylow_c1.2.1, fun P hP hPp hDP =>
    C.D_sylow_c1.2.2 P (hP.trans inf_le_left) hPp hDP⟩

theorem T_le_N_D : T ≤ Subgroup.normalizer ((dT T L V H Y : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, C.H_le_N_c1 (C.TH ht)⟩

theorem Y_le_N_D : Y ≤ Subgroup.normalizer ((dT T L V H Y : Subgroup G) : Set G) := fun y hy =>
  Subgroup.mem_normalizer_fintype fun d hd => by
    have h1 := (mem_centralizerSection.mp (C.D_le_c0 hd)).2.2.2 y hy
    rw [show y * d * y⁻¹ = (y * d * y⁻¹ * d⁻¹) * d by group]
    exact mul_mem (C.Q_le_D h1) hd

theorem Y_le_g1 : Y ≤ g1 T L V H Y := le_inf (C.Y_le_c0.trans C.c0_le_c1) C.Y_le_N_D

theorem T_le_N_g1 : T ≤ Subgroup.normalizer ((g1 T L V H Y : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨C.H_le_N_c1 (C.TH ht), Subgroup.le_normalizer (C.T_le_N_D ht)⟩

theorem g1_le_N_c0 : g1 T L V H Y ≤ Subgroup.normalizer ((c0 H Y : Subgroup G) : Set G) :=
  fun _ hg => C.H_le_N_c0 (c1_le_H T L V H Y hg.1)

theorem exists_g1_three : ∃ r ∈ g1 T L V H Y, r ∉ c0 H Y ∧ ∃ n : ℕ, r ^ 3 ^ n = 1 := by
  obtain ⟨y, hy1, hy0, n, hyn⟩ := C.exists_c1_not_c0
  obtain ⟨c, hc, hcy⟩ :=
    exists_mul_mem_normalizer C.D_sylow_c0 (C.H_le_N_c0 (c1_le_H T L V H Y hy1))
  set g := c⁻¹ * y with hgdef
  have hg1 : g ∈ g1 T L V H Y :=
    ⟨(c1 T L V H Y).mul_mem ((c1 T L V H Y).inv_mem (C.c0_le_c1 hc)) hy1, hcy⟩
  have hg0 : g ∉ c0 H Y := fun h => hy0 (by
    rw [show y = c * g by rw [hgdef]; group]
    exact mul_mem hc h)
  have hgn : g ^ 3 ^ n ∈ c0 H Y := by
    have key := mul_pow_mem_of_mem (inv_mem hc) (C.H_le_N_c0 (c1_le_H T L V H Y hy1)) (3 ^ n)
    rw [hyn, inv_one, mul_one] at key
    exact key
  set o := orderOf g with ho
  have ho0 : o ≠ 0 := (orderOf_pos g).ne'
  have hcopm : Nat.Coprime 3 (ordCompl[3] o) := Nat.coprime_ordCompl Nat.prime_three ho0
  refine ⟨g ^ ordCompl[3] o, pow_mem hg1 _, fun h => hg0 ?_, o.factorization 3, ?_⟩
  · obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left n hcopm)
    have e : g = (g ^ 3 ^ n) ^ u * (g ^ ordCompl[3] o) ^ v := by
      calc g = g ^ (u * ((3 ^ n : ℕ) : ℤ) + v * ((ordCompl[3] o : ℕ) : ℤ)) := by
            rw [huv, zpow_one]
        _ = _ := by
          rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [e]
    exact (c0 H Y).mul_mem ((c0 H Y).zpow_mem hgn u) ((c0 H Y).zpow_mem h v)
  · rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, ho, pow_orderOf_eq_one]

theorem exists_R1 : ∃ R₁ : Subgroup G, fusionIsSylowIn 3 R₁ (g1 T L V H Y) ∧
    T ≤ Subgroup.normalizer ((dT T L V H Y ⊔ R₁ : Subgroup G) : Set G) ∧
    Y ≤ dT T L V H Y ⊔ R₁ ∧ ¬ R₁ ≤ c0 H Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, -, hP₀⟩ := exists_fusionIsSylowIn_ge (p := 3) IsPGroup.of_bot (bot_le : ⊥ ≤ Y)
  have hYQP : pCoreOf 2 Y ⊔ P₀ = Y := by
    have hle : pCoreOf 2 Y ⊔ P₀ ≤ Y := sup_le (pCoreOf_le 2 Y) hP₀.1
    have hm1 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : P₀ ≤ pCoreOf 2 Y ⊔ P₀) hle
    have hm2 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left : pCoreOf 2 Y ≤ _ ⊔ P₀) hle
    rw [C.card] at hm2
    have hnd := not_dvd_index_of_fusionIsSylowIn hP₀
    change ¬ 3 ∣ P₀.relIndex Y at hnd
    have hd : (pCoreOf 2 Y ⊔ P₀).relIndex Y ∣ 3 ^ 2 :=
      ⟨(pCoreOf 2 Y).relIndex (pCoreOf 2 Y ⊔ P₀), by rw [mul_comm, hm2]; norm_num⟩
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    rcases i with _ | i
    · rw [pow_zero] at hi'
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hi')
    · exfalso
      apply hnd
      rw [← hm1, hi', pow_succ]
      exact Dvd.dvd.mul_left (dvd_mul_left 3 _) _
  obtain ⟨R₀, hPR, hR₀⟩ := exists_fusionIsSylowIn_ge hP₀.2.1 (hP₀.1.trans C.Y_le_g1)
  set X₀ : Subgroup G := dT T L V H Y ⊔ R₀ with hX₀
  have hYX₀ : Y ≤ X₀ := by
    rw [← hYQP]
    exact sup_le (C.Q_le_D.trans le_sup_left) (hPR.trans le_sup_right)
  have hconjD : ∀ g ∈ g1 T L V H Y, conjSub g (dT T L V H Y) = dT T L V H Y :=
    fun g hg => conjSub_eq_iff.mpr hg.2
  have hX₀g : ∀ g ∈ g1 T L V H Y, conjSub g X₀ = dT T L V H Y ⊔ conjSub g R₀ := fun g hg => by
    rw [hX₀, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hconjD g hg]
  set Ω : Set (Subgroup G) := {X | ∃ g ∈ g1 T L V H Y, X = conjSub g X₀} with hΩ
  have hodd : ¬ 2 ∣ Nat.card Ω := by
    rw [show Nat.card Ω = _ from card_conjOrbit (g1 T L V H Y) X₀]
    intro h2
    apply not_dvd_index_of_fusionIsSylowIn C.D_sylow_g1
    exact h2.trans (Subgroup.index_dvd_of_le fun d hd => Subgroup.mem_subgroupOf.mpr
      (Subgroup.le_normalizer ((le_sup_left : dT T L V H Y ≤ X₀) (Subgroup.mem_subgroupOf.mp hd))))
  have hΩT : ∀ t ∈ T, ∀ X ∈ Ω, conjSub t X ∈ Ω := by
    rintro t ht _ ⟨g, hg, rfl⟩
    have htg : t * g * t⁻¹ ∈ g1 T L V H Y :=
      (Subgroup.mem_normalizer_iff.mp (C.T_le_N_g1 ht) g).mp hg
    have hR' : fusionIsSylowIn 3 (conjSub t R₀) (g1 T L V H Y) :=
      fusionIsSylowIn_map_conj' hR₀ (C.T_le_N_g1 ht)
    obtain ⟨g₂, hg₂, hg₂R⟩ := exists_mem_conj_of_fusionIsSylowIn hR₀ hR'
    have hcR : conjSub t R₀ = conjSub g₂ R₀ := by
      ext x
      rw [hg₂R x, mem_conjSub]
    have htX : conjSub t X₀ = conjSub g₂ X₀ := by
      rw [hX₀g g₂ hg₂, hX₀, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_eq_iff.mpr (C.T_le_N_D ht), hcR]
    refine ⟨t * g * t⁻¹ * g₂, mul_mem htg hg₂, ?_⟩
    calc conjSub t (conjSub g X₀) = conjSub (t * g * t⁻¹) (conjSub t X₀) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub (t * g * t⁻¹ * g₂) X₀ := by rw [htX, ← conjSub_mul]
  obtain ⟨X, ⟨g, hg, rfl⟩, hTX⟩ := exists_le_normalizer_of_odd C.S.hyp.fsu.sylow.1 Ω hΩT hodd
  have hR₁ := fusionIsSylowIn_map_conj' hR₀ (Subgroup.le_normalizer hg)
  refine ⟨conjSub g R₀, hR₁, ?_, ?_, ?_⟩
  · rw [← hX₀g g hg]
    exact hTX
  · rw [← hX₀g g hg, ← conjSub_eq_iff.mpr (C.HY (c1_le_H T L V H Y hg.1))]
    exact Subgroup.map_mono hYX₀
  · intro hle
    obtain ⟨r, hr1, hr0, n, hrn⟩ := C.exists_g1_three
    have hrp : IsPGroup 3 (Subgroup.zpowers r) := by
      rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨n, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hrn, one_zpow]
    obtain ⟨R', hrR', hR'⟩ := exists_fusionIsSylowIn_ge hrp (Subgroup.zpowers_le.mpr hr1)
    obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hR₁ hR'
    have h1 : k⁻¹ * r * k ∈ c0 H Y := hle ((hkR r).mp (hrR' (Subgroup.mem_zpowers r)))
    apply hr0
    have := (Subgroup.mem_normalizer_iff.mp (C.g1_le_N_c0 hk) _).mp h1
    simpa [mul_assoc] using this

end E9Ctx

end CFSG.Quasithin.H13.L32A
