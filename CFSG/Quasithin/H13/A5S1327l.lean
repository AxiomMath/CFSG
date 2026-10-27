module

public import CFSG.Quasithin.H13.A5S1327k
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Quasithin.Background.E2SolvStruct

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem SL2_cube_mem : ∀ x y : S1417.SL2, x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 →
    y = 1 ∨ y = x ∨ y = x⁻¹ := by
  decide

section Natural

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem natL2_mem_zpowers (hN : ActsAsNaturalL2 L U) {x y : MulAut W} (hx : x ∈ L)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ∈ L) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers x := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : (e ⟨x, hx⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : L) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have h2 : e ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hx1
    have h' : (⟨x, hx⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have h3 : (e ⟨y, hy⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : L) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  rcases SL2_cube_mem _ _ h1 h2 h3 with h | h | h
  · have h' : (⟨y, hy⟩ : L) = 1 := e.injective (by rw [h, map_one])
    rw [show y = 1 from congrArg Subtype.val h']
    exact Subgroup.one_mem _
  · have h' : (⟨y, hy⟩ : L) = ⟨x, hx⟩ := e.injective h
    rw [show y = x from congrArg Subtype.val h']
    exact Subgroup.mem_zpowers x
  · have h' : (⟨y, hy⟩ : L) = (⟨x, hx⟩ : L)⁻¹ := e.injective (by rw [h, map_inv])
    rw [show y = x⁻¹ from congrArg Subtype.val h']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)

theorem natL2_fix_eq_one (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    {x : MulAut W} (hx : x ∈ L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : W} (hu : u ∈ U)
    (hxu : x u = u) : u = 1 := by
  by_contra hu1
  have hodd : Odd (orderOf x) := by
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  exact hx1 (S1417.eq_one_of_odd_of_fixed hN hst hx hodd hu hu1 hxu)

end Natural

theorem mem_of_sq_mem_of_odd' {M : Type*} [Group M] {S : Subgroup M} {g : M} (hsq : g * g ∈ S)
    (hodd : Odd (orderOf g)) : g ∈ S := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : g = (g * g) ^ (m + 1) := by
    have : g ^ (orderOf g + 1) = g := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    calc g = g ^ (orderOf g + 1) := this.symm
      _ = g ^ (2 * (m + 1)) := by congr 1; omega
      _ = (g * g) ^ (m + 1) := by rw [pow_mul, sq]
  rw [h1]
  exact S.pow_mem hsq _

theorem mem_of_pow_two_pow_mem_of_odd {M : Type*} [Group M] {S : Subgroup M} {g : M}
    (hodd : Odd (orderOf g)) {k : ℕ} (hk : g ^ 2 ^ k ∈ S) : g ∈ S := by
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    have e : (g ^ 2 ^ k) * (g ^ 2 ^ k) = g ^ 2 ^ (k + 1) := by
      rw [← pow_add, pow_succ, mul_two]
    have hodd' : Odd (orderOf (g ^ 2 ^ k)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd _)
    have hsq : g ^ 2 ^ k * g ^ 2 ^ k ∈ S := by rw [e]; exact hk
    exact mem_of_sq_mem_of_odd' hsq hodd'

@[expose] def commHomAut {W : Type*} [CommGroup W] (g : MulAut W) : W →* W where
  toFun w := g w * w⁻¹
  map_one' := by simp
  map_mul' v w := by rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem commHomAut_apply {W : Type*} [CommGroup W] (g : MulAut W) (w : W) :
    commHomAut g w = g w * w⁻¹ := rfl

section Blocks

variable {G : Type} [Group G] {U : Subgroup G} (hU : IsElemAbelian 2 U)

theorem mem_autI_twoResidual_of_odd [Finite G] {H : Subgroup G} {φ : MulAut (IntMod U hU)}
    (hφ : φ ∈ autI hU H) (hodd : Odd (orderOf φ)) : φ ∈ autI hU (twoResidual H) := by
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hU).1 hφ
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H hgH
  refine mem_of_pow_two_pow_mem_of_odd hodd (k := k) ?_
  rw [← map_pow]
  refine (mem_autI hU).2 ⟨g ^ 2 ^ k, ?_, rfl⟩
  rw [twoResidual_eq_oTwoUpper']
  simpa using hk

structure TwoBlocks (H T : Subgroup G) (K₁ K₂ : Subgroup (MulAut (IntMod U hU))) : Prop where
  ne : K₁ ≠ K₂
  eqJ : autI hU (thompsonJ H) = K₁ ⊔ K₂
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  inf : K₁ ⊓ K₂ = ⊥
  swap : ∃ t ∈ autI hU T, B1.conjAut t K₁ = K₂
  nat₁ : ActsAsNaturalL2 K₁ (commV K₁)
  nat₂ : ActsAsNaturalL2 K₂ (commV K₂)
  commV_inf : commV K₁ ⊓ commV K₂ = ⊥
  resid : twoResidual H ≤ thompsonJ H
  fix_sup : fixV (autI hU (twoResidual H)) ⊔ (commV K₁ ⊔ commV K₂) = ⊤
  fix_inf : fixV (autI hU (twoResidual H)) ⊓ (commV K₁ ⊔ commV K₂) = ⊥
  le_norm : H ≤ Subgroup.normalizer (U : Set G)

theorem exists_twoBlocks [Finite G] {H T M : Subgroup G} (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hred : IsTwoReducedIn H U) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (U : Set G))
    (hS3 : ¬ Nonempty (↥(autI hU H) ≃* Equiv.Perm (Fin 3))) :
    ∃ K₁ K₂, TwoBlocks hU H T K₁ K₂ := by
  classical
  obtain ⟨hres, I, hcard, heq, hcomm, hind, htr, hnat, hsup, hinf, hindV⟩ :=
    E2_3_one_of_isSolvable hU h hsolv hSQT hred hJ
  rcases hcard with h1 | h2
  · exfalso
    obtain ⟨K, rfl⟩ := Finset.card_eq_one.mp h1
    apply hS3
    refine nonempty_autI_equiv_perm3 hU hred h.isSylow hres (L₀ := K) ?_
      (hnat K (Finset.mem_singleton_self K))
    rw [heq, Finset.iSup_singleton]
  obtain ⟨K₁, K₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
  have hK₁ : K₁ ∈ ({K₁, K₂} : Finset _) := Finset.mem_insert_self _ _
  have hK₂ : K₂ ∈ ({K₁, K₂} : Finset _) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hne' : ¬ K₂ = K₁ := fun h => hne h.symm
  have hind₁ := hind K₁ hK₁
  simp only [Finset.iSup_insert, Finset.iSup_singleton, ne_eq, not_true_eq_false, iSup_false,
    bot_sup_eq, hne', not_false_eq_true, iSup_true] at hind₁
  have hindV₁ := hindV K₁ hK₁
  simp only [Finset.iSup_insert, Finset.iSup_singleton, ne_eq, not_true_eq_false, iSup_false,
    bot_sup_eq, hne', not_false_eq_true, iSup_true] at hindV₁
  simp only [Finset.iSup_insert, Finset.iSup_singleton] at heq hsup hinf
  exact ⟨K₁, K₂, ⟨hne, heq, hcomm K₁ hK₁ K₂ hK₂ hne, hind₁, htr K₁ hK₁ K₂ hK₂, hnat K₁ hK₁,
    hnat K₂ hK₂, hindV₁, hres, hsup, hinf, hred.2.1⟩⟩

namespace TwoBlocks

variable {hU} {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))}
  (B : TwoBlocks hU H T K₁ K₂)
include B

theorem comm' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (B.comm b hb a ha).symm

theorem apply_eq₁ {k : MulAut (IntMod U hU)} (hk : k ∈ K₁) {u : IntMod U hU}
    (hu : u ∈ commV K₂) : k u = u :=
  S1417.apply_eq_of_mem_commV_of_commute B.comm B.commV_inf hk hu

theorem apply_eq₂ {k : MulAut (IntMod U hU)} (hk : k ∈ K₂) {u : IntMod U hU}
    (hu : u ∈ commV K₁) : k u = u :=
  S1417.apply_eq_of_mem_commV_of_commute B.comm' (by rw [inf_comm]; exact B.commV_inf) hk hu

theorem sup_le_autI : K₁ ⊔ K₂ ≤ autI hU H := by
  rw [← B.eqJ]
  exact autI_mono hU (thompsonJ_le_self H)

theorem autI_twoResidual_le : autI hU (twoResidual H) ≤ K₁ ⊔ K₂ := by
  rw [← B.eqJ]
  exact autI_mono hU B.resid

theorem odd_decomp {y : MulAut (IntMod U hU)} (hy : y ∈ K₁ ⊔ K₂) (hodd : Odd (orderOf y)) :
    ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, y = k₁ * k₂ ∧ k₁ ^ 3 = 1 ∧ k₂ ^ 3 = 1 := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute B.comm hy
  have hcomm : k₁ * k₂ = k₂ * k₁ := B.comm k₁ hk₁ k₂ hk₂
  set n := orderOf (k₁ * k₂) with hn
  have hpow : k₁ ^ n * k₂ ^ n = 1 := by
    rw [← Commute.mul_pow hcomm]
    exact pow_orderOf_eq_one _
  have hk₁n : k₁ ^ n = 1 := by
    have h1 : k₁ ^ n ∈ K₁ ⊓ K₂ := ⟨K₁.pow_mem hk₁ n, by
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact K₂.inv_mem (K₂.pow_mem hk₂ n)⟩
    rw [B.inf, Subgroup.mem_bot] at h1
    exact h1
  have hk₂n : k₂ ^ n = 1 := by
    rw [hk₁n, one_mul] at hpow
    exact hpow
  have hodd₁ : Odd (orderOf k₁) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hk₁n)
  have hodd₂ : Odd (orderOf k₂) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hk₂n)
  exact ⟨k₁, hk₁, k₂, hk₂, rfl,
    OfourStruct.cube_of_odd (S1417.card_of_actsAsNaturalL2 B.nat₁).1 hk₁ hodd₁,
    OfourStruct.cube_of_odd (S1417.card_of_actsAsNaturalL2 B.nat₂).1 hk₂ hodd₂⟩

theorem autI_twoResidual_eq [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1) :
    autI hU (twoResidual H) = Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ := by
  have hodd3 : ∀ y : MulAut (IntMod U hU), y ^ 3 = 1 → Odd (orderOf y) := fun y hy => by
    have h3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  apply le_antisymm
  ·
    suffices hsuff : ∀ x ∈ oTwoUpper H, ∀ hxN : x ∈ Subgroup.normalizer (U : Set G),
        convI hU ⟨x, hxN⟩ ∈ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ by
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
      rw [twoResidual_eq_oTwoUpper'] at hg
      exact hsuff g hg g.2
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hxN
      have hφH : convI hU ⟨x, hxN⟩ ∈ autI hU H := convI_mem_autI hU hx.1 hxN
      have hodd : Odd (orderOf (convI hU ⟨x, hxN⟩)) := by
        refine Odd.of_dvd_nat hx.2 ?_
        have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨k₁, hk₁, k₂, hk₂, he, hk₁3, hk₂3⟩ := B.odd_decomp
        (B.autI_twoResidual_le (mem_autI_twoResidual_of_odd hU hφH hodd)) hodd
      rw [he]
      exact Subgroup.mul_mem_sup (natL2_mem_zpowers B.nat₁ hy₁ hy₁3 hy₁1 hk₁ hk₁3)
        (natL2_mem_zpowers B.nat₂ hy₂ hy₂3 hy₂1 hk₂ hk₂3)
    | one =>
      intro hN
      have e : (⟨1, hN⟩ : ↥(Subgroup.normalizer (U : Set G))) = 1 := rfl
      rw [e, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxyN
      have hxN : x ∈ Subgroup.normalizer (U : Set G) := B.le_norm (oTwoUpper_le H hx)
      have hyN : y ∈ Subgroup.normalizer (U : Set G) := B.le_norm (oTwoUpper_le H hy)
      have e : (⟨x * y, hxyN⟩ : ↥(Subgroup.normalizer (U : Set G))) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ (ihx hxN) (ihy hyN)
    | inv x hx ihx =>
      intro hxN'
      have hxN : x ∈ Subgroup.normalizer (U : Set G) := B.le_norm (oTwoUpper_le H hx)
      have e : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (U : Set G))) = (⟨x, hxN⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ (ihx hxN)
  · refine sup_le ?_ ?_
    · exact (Subgroup.zpowers_le).2 (mem_autI_twoResidual_of_odd hU
        (B.sup_le_autI (Subgroup.mem_sup_left hy₁)) (hodd3 y₁ hy₁3))
    · exact (Subgroup.zpowers_le).2 (mem_autI_twoResidual_of_odd hU
        (B.sup_le_autI (Subgroup.mem_sup_right hy₂)) (hodd3 y₂ hy₂3))

theorem card_autI_twoResidual [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1) :
    Nat.card (autI hU (twoResidual H)) = 9 := by
  rw [B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1]
  have hc : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂, a * b = b * a := fun a ha b hb =>
    B.comm a ((Subgroup.zpowers_le).2 hy₁ ha) b ((Subgroup.zpowers_le).2 hy₂ hb)
  have hinf : Subgroup.zpowers y₁ ⊓ Subgroup.zpowers y₂ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← B.inf]
    exact inf_le_inf ((Subgroup.zpowers_le).2 hy₁) ((Subgroup.zpowers_le).2 hy₂)
  have h := B2F.card_sup_mul_card_inf_of_commute hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime hy₁3 hy₁1, orderOf_eq_prime hy₂3 hy₂1] at h
  exact h

theorem autI_twoResidual_comm_cube [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1) :
    (∀ a ∈ autI hU (twoResidual H), ∀ b ∈ autI hU (twoResidual H), a * b = b * a) ∧
      ∀ a ∈ autI hU (twoResidual H), a ^ 3 = 1 := by
  rw [B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1]
  have hc : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂, a * b = b * a := fun a ha b hb =>
    B.comm a ((Subgroup.zpowers_le).2 hy₁ ha) b ((Subgroup.zpowers_le).2 hy₂ hb)
  have hcyc : ∀ (y : MulAut (IntMod U hU)), ∀ a ∈ Subgroup.zpowers y,
      ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    rintro y _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self y i j).eq
  have hpow : ∀ (y : MulAut (IntMod U hU)), y ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers y, a ^ 3 = 1 := by
    rintro y hy _ ⟨i, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨p, hp, q, hq, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc ha
    obtain ⟨p', hp', q', hq', rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc hb
    calc p * q * (p' * q') = (p * p') * (q * q') := by
          rw [mul_assoc, ← mul_assoc q, ← hc p' hp' q hq]; group
      _ = (p' * p) * (q' * q) := by rw [hcyc y₁ p hp p' hp', hcyc y₂ q hq q' hq']
      _ = p' * q' * (p * q) := by rw [mul_assoc, ← mul_assoc p, hc p hp q' hq']; group
  · obtain ⟨p, hp, q, hq, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc ha
    rw [(Commute.mul_pow (hc p hp q hq) 3), hpow y₁ hy₁3 p hp, hpow y₂ hy₂3 q hq, one_mul]

theorem exists_inv_mem_K1 [Finite G]
    (hsyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ H))) :
    ∃ s ∈ autI hU T, s ∈ K₁ ∧ s ^ 2 = 1 ∧ s ≠ 1 := by
  rw [B.eqJ] at hsyl
  have hn₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut (IntMod U hU))) := by
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    exact Subgroup.centralizer_le_normalizer (s := (K₁ : Set (MulAut (IntMod U hU))))
      (Subgroup.mem_centralizer_iff.mpr fun a ha => B.comm a ha b hb)
  have hS₁ := A4.isSylowTwoOf_inf_normal hsyl le_sup_left hn₁
  have hcard := S1417.card_eq_two_of_isSylowTwoOf hS₁ (S1417.card_of_actsAsNaturalL2 B.nat₁).1
  obtain ⟨s, hs, hs1, -⟩ := S1417.exists_eq_of_card_eq_two hcard
  have hs2 : s ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(autI hU (thompsonJ T) ⊓ K₁)) (x := ⟨s, hs⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  exact ⟨s, autI_mono hU (thompsonJ_le_self T) hs.1, hs.2, hs2, hs1⟩

theorem eq_of_normalized [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1)
    {s : MulAut (IntMod U hU)} (hsT : s ∈ autI hU T) (hsK : s ∈ K₁) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) {t : MulAut (IntMod U hU)} (htT : t ∈ autI hU T) (ht : B1.conjAut t K₁ = K₂)
    {Y : Subgroup (MulAut (IntMod U hU))} (hY : Y ≤ autI hU (twoResidual H)) (hY1 : Y ≠ ⊥)
    (hTY : autI hU T ≤ Subgroup.normalizer (Y : Set (MulAut (IntMod U hU)))) :
    Y = autI hU (twoResidual H) := by
  have hL := B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  have hc : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂, a * b = b * a := fun a ha b hb =>
    B.comm a ((Subgroup.zpowers_le).2 hy₁ ha) b ((Subgroup.zpowers_le).2 hy₂ hb)
  have hpow : ∀ (y : MulAut (IntMod U hU)), y ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers y, a ^ 3 = 1 := by
    rintro y hy _ ⟨i, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hconj : ∀ g ∈ autI hU T, ∀ x ∈ Y, g * x * g⁻¹ ∈ Y := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTY hg) x).mp hx
  have ht₁ : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂ := fun x hx => by
    rw [← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hx
  have ht₂ : ∀ x ∈ K₂, t⁻¹ * x * t⁻¹⁻¹ ∈ K₁ := fun x hx => by
    rw [← ht, B1.mem_conjAut] at hx
    simpa [mul_assoc] using hx
  have hcube : ∀ x : MulAut (IntMod U hU), x ^ 3 = 1 → ∀ g : MulAut (IntMod U hU),
      (g * x * g⁻¹) ^ 3 = 1 := fun x hx g => by
    rw [conj_pow, hx]; group
  have hne1 : ∀ x : MulAut (IntMod U hU), x ≠ 1 → ∀ g : MulAut (IntMod U hU),
      g * x * g⁻¹ ≠ 1 := fun x hx g h => hx (by
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this, h]; group)
  have hfrom₁ : y₁ ∈ Y → Y = autI hU (twoResidual H) := by
    intro h1
    refine le_antisymm hY ?_
    rw [hL]
    refine sup_le ((Subgroup.zpowers_le).2 h1) ?_
    have hty : t * y₁ * t⁻¹ ∈ Y := hconj t htT y₁ h1
    have := natL2_mem_zpowers B.nat₂ (ht₁ y₁ hy₁) (hcube y₁ hy₁3 t) (hne1 y₁ hy₁1 t) hy₂ hy₂3
    exact (Subgroup.zpowers_le).2 ((Subgroup.zpowers_le).2 hty this)
  have hfrom₂ : y₂ ∈ Y → Y = autI hU (twoResidual H) := by
    intro h2
    apply hfrom₁
    have hty : t⁻¹ * y₂ * t⁻¹⁻¹ ∈ Y := hconj t⁻¹ ((autI hU T).inv_mem htT) y₂ h2
    have := natL2_mem_zpowers B.nat₁ (ht₂ y₂ hy₂) (hcube y₂ hy₂3 t⁻¹) (hne1 y₂ hy₂1 t⁻¹) hy₁
      hy₁3
    exact (Subgroup.zpowers_le).2 hty this
  obtain ⟨b, hbY, hb1⟩ : ∃ b ∈ Y, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY1 (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
  have hbL : b ∈ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ := hL ▸ hY hbY
  obtain ⟨p, hp, q, hq, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc hbL
  have hpK : p ∈ K₁ := (Subgroup.zpowers_le).2 hy₁ hp
  have hqK : q ∈ K₂ := (Subgroup.zpowers_le).2 hy₂ hq
  by_cases hp1 : p = 1
  · subst hp1
    rw [one_mul] at hbY hb1
    exact hfrom₂ ((Subgroup.zpowers_le).2 hbY
      (natL2_mem_zpowers B.nat₂ hqK (hpow y₂ hy₂3 q hq) hb1 hy₂ hy₂3))
  ·
    have hsp : s * p * s⁻¹ = p⁻¹ := OfourStruct.conj_inv_cube B.nat₁ hsK hs2 hs1 hpK
      (hpow y₁ hy₁3 p hp)
    have hsq : s * q * s⁻¹ = q := by
      rw [B.comm s hsK q hqK]; group
    have hmem : s * (p * q) * s⁻¹ * (p * q)⁻¹ ∈ Y :=
      Y.mul_mem (hconj s hsT _ hbY) (Y.inv_mem hbY)
    have he : s * (p * q) * s⁻¹ * (p * q)⁻¹ = p := by
      have h1 : s * (p * q) * s⁻¹ = (s * p * s⁻¹) * (s * q * s⁻¹) := by group
      rw [h1, hsp, hsq]
      have hp3 := hpow y₁ hy₁3 p hp
      calc p⁻¹ * q * (p * q)⁻¹ = p⁻¹ * (q * q⁻¹) * p⁻¹ := by group
        _ = p := by
          rw [mul_inv_cancel, mul_one, ← sq, inv_pow]
          calc (p ^ 2)⁻¹ = (p ^ 2)⁻¹ * p ^ 3 := by rw [hp3, mul_one]
            _ = p := by group
    rw [he] at hmem
    exact hfrom₁ ((Subgroup.zpowers_le).2 hmem
      (natL2_mem_zpowers B.nat₁ hpK (hpow y₁ hy₁3 p hp) hp1 hy₁ hy₁3))

theorem two_mul_card_lt [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1)
    {a : MulAut (IntMod U hU)} (ha2 : a ^ 2 = 1) (h₁ : a * y₁ * a⁻¹ = y₁⁻¹)
    (h₂ : a * y₂ * a⁻¹ = y₂⁻¹) {S : Subgroup (IntMod U hU)} (hS : ∀ w ∈ S, a w = w) :
    2 * Nat.card S < Nat.card (IntMod U hU) := by
  by_contra hle
  push Not at hle
  set δ := commHomAut a with hδ
  have hker : S ≤ δ.ker := fun w hw => by
    rw [MonoidHom.mem_ker, hδ, commHomAut_apply, hS w hw, mul_inv_cancel]
  have hW := Subgroup.card_mul_index δ.ker
  rw [Subgroup.index_ker] at hW
  have hSk : Nat.card S ≤ Nat.card δ.ker := Subgroup.card_le_of_le hker
  have hkpos : 0 < Nat.card δ.ker := Nat.card_pos
  have hR2 : Nat.card δ.range ≤ 2 := by
    by_contra h
    push Not at h
    have : Nat.card δ.ker * 3 ≤ Nat.card δ.ker * Nat.card δ.range := Nat.mul_le_mul_left _ h
    omega
  have haa : ∀ w, a (a w) = w := fun w => by
    have := congrArg (fun φ : MulAut (IntMod U hU) => φ w) ha2
    simpa [pow_two] using this
  have key : ∀ (K : Subgroup (MulAut (IntMod U hU))) (y : MulAut (IntMod U hU)),
      ActsAsNaturalL2 K (commV K) → y ∈ K → y ^ 3 = 1 → y ≠ 1 → a * y * a⁻¹ = y⁻¹ →
      δ.range ≤ commV K := by
    intro K y hN hy hy3 hy1 hay
    have hst : ∀ l ∈ K, ∀ u ∈ commV K, l u ∈ commV K := fun l hl u hu => commV_stable K hl hu
    set δy := commHomAut y with hδy
    set R' := δ.range ⊔ δ.range.map y.toMonoidHom with hR'
    have hya : y * a = a * y⁻¹ := by
      calc y * a = (a * y * a⁻¹)⁻¹ * a := by rw [hay, inv_inv]
        _ = a * y⁻¹ := by group
    have hyy : y⁻¹ * y⁻¹ = y := by
      calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * y ^ 3 := by rw [hy3, mul_one]
        _ = y := by group
    have hyay : y * a * y⁻¹ = a * y := by
      rw [hya, mul_assoc, hyy]
    have hyay' : ∀ w, y (a (y⁻¹ w)) = a (y w) := fun w => by
      have := congrArg (fun φ : MulAut (IntMod U hU) => φ w) hyay
      simpa [MulAut.mul_apply] using this
    have hle1 : (commV K).map δy ≤ R' := by
      rintro _ ⟨u, hu, rfl⟩
      have e : δy u = δ (a (y u)) * y.toMonoidHom (δ (y⁻¹ u)) := by
        rw [hδy, commHomAut_apply, hδ, commHomAut_apply, commHomAut_apply, haa]
        simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.apply_inv_self]
        rw [hyay' u]
        group
      rw [e]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, ⟨_, rfl⟩, rfl⟩
    have hinj : Set.InjOn δy (commV K) := by
      intro u hu v hv huv
      have h1 : δy (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
      rw [hδy, commHomAut_apply] at h1
      have h2 : y (u * v⁻¹) = u * v⁻¹ := mul_inv_eq_one.mp h1
      have h3 := natL2_fix_eq_one hN hst hy hy3 hy1 ((commV K).mul_mem hu ((commV K).inv_mem hv)) h2
      exact mul_inv_eq_one.mp h3
    have hcard1 : Nat.card ((commV K).map δy) = 4 := by
      have h := Nat.card_image_of_injOn hinj
      have h4 : Nat.card ((commV K : Set (IntMod U hU))) = 4 := (S1417.card_of_actsAsNaturalL2 hN).2
      have h5 : Nat.card ((commV K).map δy) = Nat.card (δy '' (commV K : Set (IntMod U hU))) := by
        rw [← Subgroup.coe_map]; rfl
      rw [h5, h, h4]
    have hcardR' : Nat.card R' ≤ 4 := by
      have hc := B2F.card_sup_mul_card_inf_of_commute (A := δ.range)
        (B := δ.range.map y.toMonoidHom) (fun x _ z _ => mul_comm x z)
      have hm : Nat.card (δ.range.map y.toMonoidHom) = Nat.card δ.range :=
        Subgroup.card_map_of_injective y.injective
      have hpos : 0 < Nat.card ↥(δ.range ⊓ δ.range.map y.toMonoidHom) := Nat.card_pos
      rw [hm] at hc
      have : Nat.card R' ≤ Nat.card δ.range * Nat.card δ.range := by
        calc Nat.card R' ≤ Nat.card R' * Nat.card ↥(δ.range ⊓ δ.range.map y.toMonoidHom) :=
              Nat.le_mul_of_pos_right _ hpos
          _ = _ := hc
      nlinarith
    have heq : (commV K).map δy = R' := Subgroup.eq_of_le_of_card_ge hle1 (by omega)
    have hle2 : (commV K).map δy ≤ commV K := by
      rintro _ ⟨u, hu, rfl⟩
      exact (commV K).mul_mem (hst y hy u hu) ((commV K).inv_mem hu)
    exact (le_sup_left.trans heq.symm.le).trans hle2
  have hR₁ := key K₁ y₁ B.nat₁ hy₁ hy₁3 hy₁1 h₁
  have hR₂ := key K₂ y₂ B.nat₂ hy₂ hy₂3 hy₂1 h₂
  have hbot : δ.range = ⊥ := le_bot_iff.mp (B.commV_inf ▸ le_inf hR₁ hR₂)
  have ha1 : a = 1 := by
    ext w
    have : δ w = 1 := by
      have : δ w ∈ δ.range := ⟨w, rfl⟩
      rw [hbot] at this
      exact this
    rw [hδ, commHomAut_apply] at this
    simpa using mul_inv_eq_one.mp this
  rw [ha1] at h₁
  have : y₁ ^ 2 = 1 := by
    have h' : y₁ = y₁⁻¹ := by simpa using h₁
    calc y₁ ^ 2 = y₁ * y₁ := sq y₁
      _ = y₁ * y₁⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel y₁
  apply hy₁1
  calc y₁ = y₁ ^ 3 * (y₁ ^ 2)⁻¹ := by group
    _ = 1 := by rw [hy₁3, this, inv_one, mul_one]

end TwoBlocks

end Blocks

end CFSG.Quasithin.H13.A5
