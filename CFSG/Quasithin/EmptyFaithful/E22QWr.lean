module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.E22PGen
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type} [Group G]

structure Wr (p : ℕ) (T M J₁ J₂ : Subgroup G) (z₁ : G) : Prop where
  sylow : IsSylowIn 2 T ⊤
  p_prime : p.Prime
  p_mod : p % 8 = 1 ∨ p % 8 = 7
  p_ge : 7 ≤ p
  psl₁ : IsPSL 2 p 1 ↥J₁
  comm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a
  disj : J₁ ⊓ J₂ = ⊥
  normal_X : (J₁ ⊔ J₂).Normal
  gen : J₁ ⊔ J₂ ⊔ T = ⊤
  cent : Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) = ⊥
  o2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥
  perm : ∀ t ∈ T, conjSub t J₁ = J₁ ∨ conjSub t J₁ = J₂
  swap : ∃ t ∈ T, conjSub t J₁ = J₂
  z₁_mem : z₁ ∈ J₁
  z₁_ord : orderOf z₁ = 2
  z₁_central : ∀ s ∈ T ⊓ Subgroup.normalizer (J₁ : Set G), z₁ * s = s * z₁
  cen_fact : ∀ y ∈ J₁, (∀ x ∈ J₁, x * z₁ = z₁ * x → x * y = y * x) → y = 1 ∨ y = z₁
  coatom : IsCoatom M
  solv : Group.IsSolvable ↥M
  T_le : T ≤ M
  M_J₁ : M ⊓ J₁ = Subgroup.centralizer ({z₁} : Set G) ⊓ J₁
  M_X : M ⊓ (J₁ ⊔ J₂) ≤ (M ⊓ J₁) ⊔ (M ⊓ J₂)

private theorem nonab_of_isPSL_two {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h : IsPSL 2 p 1 X) : ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h).2
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
  have hcard : Nat.card X = p ^ 1 * ((p ^ 1) ^ 2 - 1) / Nat.gcd 2 (p ^ 1 - 1) := by
    rw [Nat.card_congr eK.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    norm_num
  by_contra hcon
  push Not at hcon
  let _ : CommGroup X := { ‹Group X› with mul_comm := hcon }
  have hpr : (Nat.card X).Prime := IsSimpleGroup.prime_card (α := X)
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := by
    have := hp.eq_two_or_odd.resolve_left (by omega)
    exact ⟨p / 2, by omega⟩
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  have e2 : Nat.gcd 2 (2 * k + 1 - 1) = 2 := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  simp only [pow_one] at hcard
  rw [e1, e2] at hcard
  have hc : Nat.card X = (2 * k + 1) * (2 * k * (k + 1)) := by
    rw [hcard]
    exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  exact Nat.not_prime_mul (by omega) (by intro hb; nlinarith) (hc ▸ hpr)

namespace Wr

variable {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}

theorem tau_eq (h : Wr p T M J₁ J₂ z₁) (A : Subgroup G) :
    E1.tauOf ⊤ T A = T ⊓ Subgroup.centralizer (A : Set G) := by
  ext t
  rw [E1.mem_tauOf_of_le le_top, h.o2, Subgroup.mem_inf]
  constructor
  · rintro ⟨ht, hc⟩
    refine ⟨ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hc a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · rintro ⟨ht, hc⟩
    refine ⟨ht, fun a ha => ?_⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hc a ha).symm

private theorem J₂_le_centralizer (h : Wr p T M J₁ J₂ z₁) :
    J₂ ≤ Subgroup.centralizer (J₁ : Set G) :=
  fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => h.comm a ha b hb

private theorem J₁_le_centralizer (h : Wr p T M J₁ J₂ z₁) :
    J₁ ≤ Subgroup.centralizer (J₂ : Set G) :=
  fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (h.comm a ha b hb).symm

private theorem X_le_normalizer₁ (h : Wr p T M J₁ J₂ z₁) :
    J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₁ : Set G) :=
  sup_le Subgroup.le_normalizer
    (h.J₂_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))

private theorem X_le_normalizer₂ (h : Wr p T M J₁ J₂ z₁) :
    J₁ ⊔ J₂ ≤ Subgroup.normalizer (J₂ : Set G) :=
  sup_le (h.J₁_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
    Subgroup.le_normalizer

variable [Finite G]

set_option linter.unusedSectionVars false

theorem J₁_normal_in_X (h : Wr p T M J₁ J₂ z₁) : (J₁.subgroupOf (J₁ ⊔ J₂)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.X_le_normalizer₁

theorem J₂_normal_in_X (h : Wr p T M J₁ J₂ z₁) : (J₂.subgroupOf (J₁ ⊔ J₂)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr h.X_le_normalizer₂

theorem sylow_X (h : Wr p T M J₁ J₂ z₁) : IsSylowIn 2 (T ⊓ (J₁ ⊔ J₂)) (J₁ ⊔ J₂) := by
  have hN : (⊤ : Subgroup G) ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_X]
  have hX := B6.isSylowTwoOf_inf_normal
    (⟨h.sylow.1, h.sylow.2.1, h.sylow.2.2⟩ : QuasithinUnique.IsSylowTwoOf T ⊤) le_top hN
  exact ⟨hX.1, hX.2.1, hX.2.2⟩

theorem sylow_J₁ (h : Wr p T M J₁ J₂ z₁) : IsSylowIn 2 (T ⊓ J₁) J₁ := by
  have hX := h.sylow_X
  have hJ := B6.isSylowTwoOf_inf_normal
    (⟨hX.1, hX.2.1, hX.2.2⟩ : QuasithinUnique.IsSylowTwoOf (T ⊓ (J₁ ⊔ J₂)) (J₁ ⊔ J₂))
    le_sup_left h.X_le_normalizer₁
  rw [inf_assoc, inf_eq_right.mpr (le_sup_left : J₁ ≤ J₁ ⊔ J₂)] at hJ
  exact ⟨hJ.1, hJ.2.1, hJ.2.2⟩

theorem sylow_J₂ (h : Wr p T M J₁ J₂ z₁) : IsSylowIn 2 (T ⊓ J₂) J₂ := by
  have hX := h.sylow_X
  have hJ := B6.isSylowTwoOf_inf_normal
    (⟨hX.1, hX.2.1, hX.2.2⟩ : QuasithinUnique.IsSylowTwoOf (T ⊓ (J₁ ⊔ J₂)) (J₁ ⊔ J₂))
    le_sup_right h.X_le_normalizer₂
  rw [inf_assoc, inf_eq_right.mpr (le_sup_right : J₂ ≤ J₁ ⊔ J₂)] at hJ
  exact ⟨hJ.1, hJ.2.1, hJ.2.2⟩

theorem TX_eq (h : Wr p T M J₁ J₂ z₁) : T ⊓ (J₁ ⊔ J₂) = (T ⊓ J₁) ⊔ (T ⊓ J₂) := by
  have hle : (T ⊓ J₁) ⊔ (T ⊓ J₂) ≤ T ⊓ (J₁ ⊔ J₂) :=
    sup_le (inf_le_inf_left T le_sup_left) (inf_le_inf_left T le_sup_right)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hX : Nat.card ↥(J₁ ⊔ J₂) = Nat.card ↥J₁ * Nat.card ↥J₂ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer J₁ J₂
      (h.J₂_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
      (disjoint_iff.mpr h.disj)
  have hS : Nat.card ↥((T ⊓ J₁) ⊔ (T ⊓ J₂)) = Nat.card ↥(T ⊓ J₁) * Nat.card ↥(T ⊓ J₂) := by
    refine CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ ?_ ?_
    · intro b hb
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
      exact h.comm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2
    · rw [disjoint_iff, eq_bot_iff, ← h.disj]
      exact inf_le_inf inf_le_right inf_le_right
  have h1 := h.sylow_J₁.card_eq
  have h2 := h.sylow_J₂.card_eq
  have hX' := h.sylow_X.card_eq
  have hpos1 : Nat.card ↥J₁ ≠ 0 := Nat.card_pos.ne'
  have hpos2 : Nat.card ↥J₂ ≠ 0 := Nat.card_pos.ne'
  rw [hX', hS, h1, h2, hX, Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply, pow_add]

theorem psl₂ (h : Wr p T M J₁ J₂ z₁) : IsPSL 2 p 1 ↥J₂ := by
  obtain ⟨t, -, ht⟩ := h.swap
  let e : ↥J₁ ≃* ↥J₂ :=
    (Subgroup.equivMapOfInjective J₁ (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr (show J₁.map (MulAut.conj t).toMonoidHom = J₂ from ht))
  exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h.psl₁

theorem simple₁ (h : Wr p T M J₁ J₂ z₁) : IsSimpleGroup ↥J₁ :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h.psl₁).2

theorem simple₂ (h : Wr p T M J₁ J₂ z₁) : IsSimpleGroup ↥J₂ :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h.psl₂).2

theorem nonab₁ (h : Wr p T M J₁ J₂ z₁) : ∃ a b : ↥J₁, a * b ≠ b * a :=
  nonab_of_isPSL_two h.p_prime h.p_ge h.psl₁

theorem nonab₂ (h : Wr p T M J₁ J₂ z₁) : ∃ a b : ↥J₂, a * b ≠ b * a :=
  nonab_of_isPSL_two h.p_prime h.p_ge h.psl₂

theorem exists_not_cent (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hA : A ≠ ⊥) :
    ¬ A ≤ Subgroup.centralizer (J₁ : Set G) ∨ ¬ A ≤ Subgroup.centralizer (J₂ : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hA
  have hA' : A ≤ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  rw [h.cent] at hA'
  exact le_bot_iff.mp hA'

private theorem J₁_ne_J₂ (h : Wr p T M J₁ J₂ z₁) : J₁ ≠ J₂ := by
  intro heq
  have hbot : J₁ = ⊥ := by
    have := h.disj
    rwa [← heq, inf_idem] at this
  have : Nontrivial ↥J₁ := (h.simple₁).toNontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot J₁).mp this) hbot

private theorem perm₂ (h : Wr p T M J₁ J₂ z₁) {s : G} (hs : s ∈ T) :
    conjSub s J₂ = J₁ ∨ conjSub s J₂ = J₂ := by
  obtain ⟨t, ht, htJ⟩ := h.swap
  have hst := h.perm (s * t) (T.mul_mem hs ht)
  rwa [conjSub_mul, htJ] at hst

private theorem conj_iff (h : Wr p T M J₁ J₂ z₁) {s : G} (hs : s ∈ T) :
    conjSub s J₁ = J₁ ↔ conjSub s J₂ = J₂ := by
  have hne := h.J₁_ne_J₂
  rcases h.perm s hs with h1 | h1 <;> rcases h.perm₂ hs with h2 | h2
  · exact absurd ((conjSub_inj s).mp (h1.trans h2.symm)) hne
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h3 => absurd (h1.symm.trans h3).symm hne, fun h3 => absurd (h2.symm.trans h3) hne⟩
  · exact absurd ((conjSub_inj s).mp (h1.trans h2.symm)) hne

theorem normalizer_eq (h : Wr p T M J₁ J₂ z₁) :
    T ⊓ Subgroup.normalizer (J₁ : Set G) = T ⊓ Subgroup.normalizer (J₂ : Set G) := by
  ext s
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hs, hn⟩
    exact ⟨hs, conjSub_eq_iff_mem_normalizer.mp
      ((h.conj_iff hs).mp (conjSub_eq_iff_mem_normalizer.mpr hn))⟩
  · rintro ⟨hs, hn⟩
    exact ⟨hs, conjSub_eq_iff_mem_normalizer.mp
      ((h.conj_iff hs).mpr (conjSub_eq_iff_mem_normalizer.mpr hn))⟩

theorem swapW (h : Wr p T M J₁ J₂ z₁) : ∃ z₂ : G, Wr p T M J₂ J₁ z₂ := by
  obtain ⟨t, htT, htJ⟩ := h.swap
  have htM : t ∈ M := h.T_le htT
  have hmem₂ : ∀ y : G, y ∈ J₂ ↔ t⁻¹ * y * t ∈ J₁ := fun y => by
    rw [← htJ, mem_conjSub_iff]
  have hconj : ∀ x : G, x ∈ J₁ → t * x * t⁻¹ ∈ J₂ := fun x hx => htJ ▸ mem_conjSub_of_mem hx
  refine ⟨t * z₁ * t⁻¹, ?_⟩
  refine
    { sylow := h.sylow
      p_prime := h.p_prime
      p_mod := h.p_mod
      p_ge := h.p_ge
      psl₁ := h.psl₂
      comm := fun a ha b hb => (h.comm b hb a ha).symm
      disj := by rw [inf_comm J₂ J₁]; exact h.disj
      normal_X := by rw [sup_comm J₂ J₁]; exact h.normal_X
      gen := by rw [sup_comm J₂ J₁]; exact h.gen
      cent := by rw [sup_comm J₂ J₁]; exact h.cent
      o2 := h.o2
      perm := fun s hs => (h.perm₂ hs).symm
      swap := ⟨t⁻¹, T.inv_mem htT, ?_⟩
      z₁_mem := hconj z₁ h.z₁_mem
      z₁_ord := ?_
      z₁_central := ?_
      cen_fact := ?_
      coatom := h.coatom
      solv := h.solv
      T_le := h.T_le
      M_J₁ := ?_
      M_X := ?_ }
  · rw [← htJ, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact h.z₁_ord
  · intro s hs
    obtain ⟨hsT, hsN⟩ := Subgroup.mem_inf.mp hs
    have hs' : t⁻¹ * s * t ∈ T ⊓ Subgroup.normalizer (J₁ : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem (T.inv_mem htT) hsT) htT, ?_⟩
      rw [← conjSub_eq_iff_mem_normalizer, conjSub_mul, conjSub_mul, htJ,
        conjSub_eq_iff_mem_normalizer.mpr hsN, ← htJ, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have key := h.z₁_central _ hs'
    calc t * z₁ * t⁻¹ * s = t * (z₁ * (t⁻¹ * s * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * s * t) * z₁) * t⁻¹ := by rw [key]
      _ = s * (t * z₁ * t⁻¹) := by group
  · intro y hy hcen
    have hy' : t⁻¹ * y * t ∈ J₁ := (hmem₂ y).mp hy
    have hres := h.cen_fact (t⁻¹ * y * t) hy' (fun x hx hxz => by
      have hx₂ : t * x * t⁻¹ ∈ J₂ := hconj x hx
      have hc : t * x * t⁻¹ * (t * z₁ * t⁻¹) = t * z₁ * t⁻¹ * (t * x * t⁻¹) := by
        calc t * x * t⁻¹ * (t * z₁ * t⁻¹) = t * (x * z₁) * t⁻¹ := by group
          _ = t * (z₁ * x) * t⁻¹ := by rw [hxz]
          _ = t * z₁ * t⁻¹ * (t * x * t⁻¹) := by group
      have h3 := hcen _ hx₂ hc
      calc x * (t⁻¹ * y * t) = t⁻¹ * (t * x * t⁻¹ * y) * t := by group
        _ = t⁻¹ * (y * (t * x * t⁻¹)) * t := by rw [h3]
        _ = t⁻¹ * y * t * x := by group)
    have hy_eq : y = t * (t⁻¹ * y * t) * t⁻¹ := by group
    rcases hres with h1 | h1
    · left
      calc y = t * (t⁻¹ * y * t) * t⁻¹ := hy_eq
        _ = 1 := by rw [h1]; group
    · right
      calc y = t * (t⁻¹ * y * t) * t⁻¹ := hy_eq
        _ = t * z₁ * t⁻¹ := by rw [h1]
  · ext y
    have hM : y ∈ M ↔ t⁻¹ * y * t ∈ M := by
      constructor
      · intro hy
        exact M.mul_mem (M.mul_mem (M.inv_mem htM) hy) htM
      · intro hy
        have hy' := M.mul_mem (M.mul_mem htM hy) (M.inv_mem htM)
        have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
        rwa [e] at hy'
    have hcz : t * z₁ * t⁻¹ * y = y * (t * z₁ * t⁻¹) ↔
        z₁ * (t⁻¹ * y * t) = t⁻¹ * y * t * z₁ := by
      constructor
      · intro hc
        calc z₁ * (t⁻¹ * y * t) = t⁻¹ * (t * z₁ * t⁻¹ * y) * t := by group
          _ = t⁻¹ * (y * (t * z₁ * t⁻¹)) * t := by rw [hc]
          _ = t⁻¹ * y * t * z₁ := by group
      · intro hc
        calc t * z₁ * t⁻¹ * y = t * (z₁ * (t⁻¹ * y * t)) * t⁻¹ := by group
          _ = t * (t⁻¹ * y * t * z₁) * t⁻¹ := by rw [hc]
          _ = y * (t * z₁ * t⁻¹) := by group
    have key := Subgroup.ext_iff.mp h.M_J₁ (t⁻¹ * y * t)
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq] at key ⊢
    rw [hM, hmem₂ y, hcz]
    exact key
  · rw [sup_comm J₂ J₁, sup_comm (M ⊓ J₂) (M ⊓ J₁)]
    exact h.M_X

end Wr

theorem inEFor_of_star {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G} [Finite G]
    (h : Wr p T M J₁ J₂ z₁)
    (hs : ∀ Ω : Set (Subgroup G), E1.IsInvColl ⊤ Ω → ∀ A ∈ Ω, A ≤ T → A ≠ ⊥ →
      ∃ A' ∈ Ω, A' ≤ T ∧ ∃ K : Subgroup G, E1.IsE 1 ⊤ T A' K ∧ ¬ K ≤ M) :
    E1.InEFor 1 ⊤ T := by
  intro Ω hΩ
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥
  · obtain ⟨A, hA, hAT, hA1⟩ := hex
    obtain ⟨A', hA', hA'T, K, hK, hKM⟩ := hs Ω hΩ A hA hAT hA1
    have hMX := E1.le_eGen_sup_normalizer_of_isSolvable h.sylow h.T_le h.solv hΩ
    have hKX := (E1.le_eGen hA' hA'T hK).trans (le_sup_left :
      E1.eGen 1 ⊤ T Ω ≤ E1.eGen 1 ⊤ T Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)))
    have hlt : M < E1.eGen 1 ⊤ T Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) :=
      lt_of_le_of_ne hMX fun h' => hKM (h' ▸ hKX)
    exact h.coatom.2 _ hlt
  · push Not at hex
    have hW : E1.weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
      exact (hex A hA hAT).le
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]

@[expose] def WrCore : Prop :=
  ∀ (p : ℕ) (G : Type) [Group G] [Finite G] (T M J₁ J₂ : Subgroup G) (z₁ : G),
    Wr p T M J₁ J₂ z₁ → E1.InEFor 1 ⊤ T

end CFSG.Quasithin.E2.E22N
