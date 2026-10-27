module

public import CFSG.Quasithin.H13.A6S1514
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem K4L_mul : ∀ σ ∈ K4L, ∀ τ ∈ K4L, σ * τ ∈ K4L := by decide +kernel

theorem K4L_inv : ∀ σ ∈ K4L, σ⁻¹ ∈ K4L := by decide +kernel

theorem K4L_sq : ∀ σ ∈ K4L, σ * σ = 1 := by decide +kernel

theorem c012_not_K4L : swap (0 : Fin 6) 1 * swap 1 2 ∉ K4L := by decide +kernel

@[expose] def A4At (σ : Perm (Fin 6)) : Prop :=
  σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 →
    (σ ∈ K4L ∨ swap 0 1 * swap 1 2 * (swap 0 1 * swap 1 2) * σ ∈ K4L ∨
      swap 0 1 * swap 1 2 * σ ∈ K4L) ∧ ∀ τ ∈ K4L, σ * τ * σ⁻¹ ∈ K4L

instance (σ : Perm (Fin 6)) : Decidable (A4At σ) := by unfold A4At; infer_instance

theorem a4At_all : ∀ σ : Perm (Fin 6), A4At σ := by
  decide +kernel

@[expose] def K4sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ K4L}
  mul_mem' := fun {a b} ha hb => K4L_mul a ha b hb
  one_mem' := List.mem_cons_self
  inv_mem' := fun {a} ha => K4L_inv a ha

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem perfect_Q : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr S.h13.faithful.1.2.1.2.1
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  infer_instance

omit S in
theorem odd_card_center_Q :
    Odd (Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  have hzc : Subgroup.zpowers (z : Q) ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr z.2
  have hN : (Subgroup.zpowers (z : Q)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.mp (hzc hn) g
    rw [this, mul_inv_cancel_right]
    exact hn
  have hP : IsPGroup 2 (Subgroup.zpowers (z : Q)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe, hz]
  have hle : Subgroup.zpowers (z : Q) ≤ CFSG.pCore 2 Q := le_sSup ⟨hN, hP⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff,
    Subgroup.zpowers_eq_bot] at hle
  have hz1 : z = 1 := Subtype.ext hle
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem card_center_Q : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1 ∨
    Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := by
  obtain ⟨e⟩ := S.centralQuot
  have := S.perfect_Q
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  let π : Q →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6) (by norm_num)
    (by norm_num) π hπ hker.le (hker ▸ odd_card_center_Q)).2 (Or.inl rfl)
  rwa [hker] at h

theorem center_Q_eq_bot (hhat : ¬ IsHatA6 L) : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  rcases S.card_center_Q with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exact absurd ⟨S.perfect_Q, h, S.centralQuot⟩ hhat

theorem inf_centralizer_le_pCoreOf (hhat : ¬ IsHatA6 L) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := S.centralizer_le_o2Z hy
  rw [SetLike.mem_coe, Subgroup.mem_comap, S.center_Q_eq_bot hhat, Subgroup.mem_bot,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact (mem_pCore_iff x).1 hx

@[expose] noncomputable def L1K4 : Subgroup G :=
  ((K4sub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype) ⊓ S.L1

theorem mem_L1K4 {x : G} : x ∈ S.L1K4 ↔ ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
    S.frame.ρ ⟨x, hx⟩ ∈ K4L ∧ x ∈ S.L1 := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
    exact ⟨y.2, hy, hyL⟩
  · rintro ⟨hx, hK, hL⟩
    exact ⟨⟨⟨x, hx⟩, hK, rfl⟩, hL⟩

theorem L1_le_L : S.L1 ≤ L := S.L1_le.trans inf_le_left

theorem isPGroup_L1K4 (hhat : ¬ IsHatA6 L) : IsPGroup 2 S.L1K4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, hx⟩
  obtain ⟨hxN, hK, hL⟩ := S.mem_L1K4.1 hx
  have hsq : S.frame.ρ (⟨x, hxN⟩ * ⟨x, hxN⟩) = 1 := by
    rw [map_mul]
    exact K4L_sq _ hK
  have hC := (S.rho_eq_one_iff _).1 hsq
  have hO : x * x ∈ pCoreOf 2 L :=
    S.inf_centralizer_le_pCoreOf hhat ⟨S.L1_le_L (S.L1.mul_mem hL hL), hC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hO⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : (x * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  show x ^ 2 ^ (k + 1) = 1
  rw [pow_succ', pow_mul, ← hk', sq]

theorem L1_le_normalizer_L1K4 : S.L1 ≤ Subgroup.normalizer (S.L1K4 : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun l hl x hx => ?_
  obtain ⟨hxN, hK, hL⟩ := S.mem_L1K4.1 hx
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L hl)
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨l, hlN⟩) hl
  refine S.mem_L1K4.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN) (Subgroup.inv_mem _ hlN),
    ?_, S.L1.mul_mem (S.L1.mul_mem hl hL) (S.L1.inv_mem hl)⟩
  have e : (⟨l * x * l⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN)
      (Subgroup.inv_mem _ hlN)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact (a4At_all _ h4 h5 hs).2 _ hK

theorem L1K4_le (hhat : ¬ IsHatA6 L) : S.L1K4 ≤ pCoreOf 2 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    S.L1_le_normalizer_L1K4 (S.isPGroup_L1K4 hhat)

theorem mem_pCoreOf_L1_of_K4
    (hhat : ¬ IsHatA6 L) {x : ↥(Subgroup.normalizer (V : Set G))}
    (hx : (x : G) ∈ S.L1) (hK : S.frame.ρ x ∈ K4L) : (x : G) ∈ pCoreOf 2 S.L1 :=
  S.L1K4_le hhat (S.mem_L1K4.2 ⟨x.2, hK, hx⟩)

theorem exists_L1_c012_cube (hhat : ¬ IsHatA6 L) :
    ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
      S.frame.ρ g = swap 0 1 * swap 1 2 ∧ (g : G) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_c012
  have h3 : ((c ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 S.L1 :=
    S.mem_pCoreOf_L1_of_K4 hhat (S.L1.pow_mem hcL 3)
      (by rw [map_pow, hc, c012_facts.2.2]; decide)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1 ⟨_, h3⟩
  have hk' : ((c : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨c ^ 4 ^ k, by simpa using S.L1.pow_mem hcL (4 ^ k), ?_, ?_⟩
  · rw [map_pow, hc, pow_four_pow_of_cube c012_facts.2.2]
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]

@[expose] noncomputable def cL1
    (hhat : ¬ IsHatA6 L) : ↥(Subgroup.normalizer (V : Set G)) :=
  Classical.choose (S.exists_L1_c012_cube hhat)

theorem cL1_mem (hhat : ¬ IsHatA6 L) : (S.cL1 hhat : G) ∈ S.L1 :=
  (Classical.choose_spec (S.exists_L1_c012_cube hhat)).1

theorem cL1_rho
    (hhat : ¬ IsHatA6 L) : S.frame.ρ (S.cL1 hhat) = swap 0 1 * swap 1 2 :=
  (Classical.choose_spec (S.exists_L1_c012_cube hhat)).2.1

theorem cL1_cube (hhat : ¬ IsHatA6 L) : (S.cL1 hhat : G) ^ 3 = 1 :=
  (Classical.choose_spec (S.exists_L1_c012_cube hhat)).2.2

theorem cL1_not_mem
    (hhat : ¬ IsHatA6 L) : (S.cL1 hhat : G) ∉ pCoreOf 2 S.L1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.L1 ⟨_, h⟩
  have hk' : (S.cL1 hhat : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (S.cL1 hhat : G) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (S.cL1_cube hhat)) (orderOf_dvd_of_pow_eq_one hk')
  have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  have := S.cL1_rho hhat
  have h3 : S.cL1 hhat = 1 := Subtype.ext h1
  rw [h3, map_one] at this
  exact absurd this.symm (by decide)

theorem L1_decomp (hhat : ¬ IsHatA6 L) {x : G} (hx : x ∈ S.L1) :
    x ∈ pCoreOf 2 S.L1 ∨ (S.cL1 hhat : G) * S.cL1 hhat * x ∈ pCoreOf 2 S.L1 ∨
      (S.cL1 hhat : G) * x ∈ pCoreOf 2 S.L1 := by
  obtain ⟨xn, rfl⟩ : ∃ xn : ↥(Subgroup.normalizer (V : Set G)), (xn : G) = x :=
    ⟨⟨x, S.frame.L_le (S.L1_le_L hx)⟩, rfl⟩
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 hx
  have hc := S.cL1_mem hhat
  rcases (a4At_all _ h4 h5 hs).1 with h | h | h
  · exact Or.inl (S.mem_pCoreOf_L1_of_K4 hhat hx h)
  · refine Or.inr (Or.inl ?_)
    exact S.mem_pCoreOf_L1_of_K4 hhat (x := S.cL1 hhat * S.cL1 hhat * xn)
      (S.L1.mul_mem (S.L1.mul_mem hc hc) hx) (by rw [map_mul, map_mul, S.cL1_rho]; exact h)
  · refine Or.inr (Or.inr ?_)
    exact S.mem_pCoreOf_L1_of_K4 hhat (x := S.cL1 hhat * xn) (S.L1.mul_mem hc hx)
      (by rw [map_mul, S.cL1_rho]; exact h)

end Setting4

end CFSG.Quasithin.H13.A6
