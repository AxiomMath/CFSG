module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_of_dvd_eight {a b : ℕ} (ha : a ∣ 8) (hb : b ∣ a) (h : a ≡ b [MOD 5]) : a = b := by
  have ha8 : a ≤ 8 := Nat.le_of_dvd (by norm_num) ha
  have hb8 : b ≤ a := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos ha (by norm_num)) hb
  unfold Nat.ModEq at h
  interval_cases a <;> interval_cases b <;> simp_all

theorem comm_mem_of_pow_five [Finite G] {X L N : Subgroup G} (hs : IsSec X L N)
    (hcard : L.relIndex N ∣ 8) {g : G} (hg : g ∈ X)
    (h5 : ∀ y ∈ N, g ^ 5 * y * (g ^ 5)⁻¹ * y⁻¹ ∈ L) :
    ∀ y ∈ N, g * y * g⁻¹ * y⁻¹ ∈ L := by
  have hfin : Finite hs.W := by
    have := hs.normal_subgroupOf
    exact (inferInstance : Finite (↥N ⧸ L.subgroupOf N))
  set σ : MulAut hs.W := hs.conjHom ⟨g, hg⟩ with hσ
  have hσ5 : σ ^ 5 = 1 := by
    have hc : ((⟨g, hg⟩ ^ 5 : ↥X) : G) = g ^ 5 := SubgroupClass.coe_pow _ 5
    rw [hσ, ← map_pow]
    exact hs.conjHom_eq_one fun x hx => by rw [hc]; exact h5 x hx
  set P : Subgroup (MulAut hs.W) := Subgroup.zpowers σ
  have hP : IsPGroup 5 P := by
    intro p
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp p.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hσ5, one_zpow]
    rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := hP.card_modEq_card_fixedPoints hs.W
  let F : Subgroup hs.W :=
    { carrier := {a | σ a = a}
      one_mem' := map_one σ
      mul_mem' := fun {a b} ha hb => by
        show σ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show σ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hFix : MulAction.fixedPoints P hs.W = (F : Set hs.W) := by
    ext a
    constructor
    · intro ha
      exact ha ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro ha p
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp p.2
      have ha' : σ a = a := ha
      show (p : MulAut hs.W) a = a
      rw [← hk]
      have hfix : ∀ n : ℕ, (σ ^ n) a = a := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, ha', ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]; exact hfix n
      · rw [zpow_neg, zpow_natCast]
        conv_lhs => rw [← hfix n]
        exact (σ ^ n).symm_apply_apply a
  have hcardW : Nat.card hs.W = L.relIndex N := rfl
  have hcardF : Nat.card (MulAction.fixedPoints P hs.W) = Nat.card F := by
    rw [hFix]; rfl
  rw [hcardF, hcardW] at hmod
  have hdvd : Nat.card F ∣ L.relIndex N := by
    rw [← hcardW]; exact Subgroup.card_subgroup_dvd_card F
  have heq := eq_of_dvd_eight hcard hdvd hmod
  have htop : F = ⊤ := (Subgroup.card_eq_iff_eq_top F).mp (by rw [← heq, hcardW])
  intro y hy
  rw [← sec_fix_iff hs ⟨g, hg⟩ ⟨y, hy⟩]
  have : hs.proj ⟨y, hy⟩ ∈ F := htop ▸ Subgroup.mem_top _
  exact this

@[expose] def commHom {K Z : Subgroup G} {v : G} (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hv : ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ Z) :
    ↥K →* ↥Z where
  toFun k := ⟨(k : G) * v * (k : G)⁻¹ * v⁻¹, hv k k.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    apply Subtype.ext
    have hb := hv b b.2
    have ha := hv a a.2
    show ((a * b : ↥K) : G) * v * ((a * b : ↥K) : G)⁻¹ * v⁻¹ =
      ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹)
    have e2 : ((a * b : ↥K) : G) * v * ((a * b : ↥K) : G)⁻¹ * v⁻¹ =
        (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹ *
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [e2, hKZ a a.2 _ hb, mul_assoc _ (a : G) (a : G)⁻¹, mul_inv_cancel, mul_one]
    exact hZ _ hb _ ha

theorem commHom_eq_one_iff {K Z : Subgroup G} {v : G} (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hv : ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ Z) (k : ↥K) :
    commHom hKZ hZ hv k = 1 ↔ (k : G) * v = v * k := by
  constructor
  · intro h1
    have h2 : (k : G) * v * (k : G)⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : (k : G) * v * (k : G)⁻¹ = v := mul_inv_eq_one.mp h2
    calc (k : G) * v = (k : G) * v * (k : G)⁻¹ * k := by group
      _ = v * k := by rw [h3]
  · intro h1
    apply Subtype.ext
    show (k : G) * v * (k : G)⁻¹ * v⁻¹ = 1
    rw [h1]; group

theorem relIndex_centralizer_dvd [Finite G] {K Z : Subgroup G} {v : G}
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hv : ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ ∈ Z) :
    (Subgroup.centralizer ({v} : Set G)).relIndex K ∣ Nat.card Z := by
  have hker : (commHom hKZ hZ hv).ker = (Subgroup.centralizer ({v} : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      commHom_eq_one_iff]
  unfold Subgroup.relIndex
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem commutator_le_of_relIndex_two {N K X : Subgroup G} (h2 : N.relIndex K = 2)
    (hK : X ≤ Subgroup.normalizer (K : Set G)) (hN : X ≤ Subgroup.normalizer (N : Set G)) :
    ⁅K, X⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro k hk x hx
  have hxk : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK hx) k).mp hk
  rw [commutatorElement_def]
  have e : k * x * k⁻¹ * x⁻¹ = (k⁻¹)⁻¹ * (x * k * x⁻¹)⁻¹ := by group
  rw [e]
  by_cases hkN : k ∈ N
  · have h1 : x * k * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hN hx) k).mp hkN
    exact N.mul_mem (by simpa using hkN) (N.inv_mem h1)
  · have h1 : x * k * x⁻¹ ∉ N := fun h' => hkN ((Subgroup.mem_normalizer_iff.mp (hN hx) k).mpr h')
    refine inv_mul_mem_of_relIndex_two h2 (K.inv_mem hk) (K.inv_mem hxk) ?_ ?_
    · exact fun h' => hkN (by simpa using N.inv_mem h')
    · exact fun h' => h1 (by simpa using N.inv_mem h')

theorem core_S5SylF : ∀ τ ∈ S5SylF, (∀ σ : Perm (Fin 5), σ 4 = 4 → σ * τ * σ⁻¹ ∈ S5SylF) →
    τ ∈ S5TF := by
  decide +kernel

@[expose] def c5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def t3 : Perm (Fin 5) := c5 * swap 0 1 * c5⁻¹ * (swap 0 1)⁻¹

theorem c5_pow_five : c5 ^ 5 = 1 := by decide +kernel

theorem t3_four : t3 4 = 4 := by decide +kernel

theorem fix_t3 : ∀ w : orth.W, w ∈ spanF (commGensF orth S5SylF Finset.univ) →
    orth.act t3 w = w → ∀ b ∈ S5SylF, orth.act b w = w := by
  decide +kernel

theorem exists_gen : ∃ c : orth.W, (∀ σ ∈ S5ThatF, orth.act σ c = c) ∧
    ∀ w : orth.W, w ∈ spanF (commGensF orth S5SylF Finset.univ) → ∃ a b d : Bool,
      w = (if a then orth.act (swap 0 1) c * c⁻¹ else 1) *
        (if b then orth.act (swap 1 2) c * c⁻¹ else 1) *
        (if d then orth.act (swap 2 3) c * c⁻¹ else 1) := by
  decide +kernel

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20B
