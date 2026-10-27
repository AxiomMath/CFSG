module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20ya

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Stab

variable {X Γ : Type} [Group X] [Group Γ]

@[expose] def uc22pwtStab (ρ : Γ →* MulAut X) (A : Subgroup X) : Subgroup Γ where
  carrier := {g | ∀ x, x ∈ A ↔ ρ g x ∈ A}
  mul_mem' := by
    intro a b ha hb x
    rw [map_mul, MulAut.mul_apply]
    exact (hb x).trans (ha _)
  one_mem' := fun x => by
    rw [map_one]
    exact Iff.rfl
  inv_mem' := by
    intro a ha x
    have h := ha (ρ a⁻¹ x)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h
    exact h.symm

@[expose] def uc22pwtResAut (ρ : Γ →* MulAut X) (A : Subgroup X) (g : ↥(uc22pwtStab ρ A)) :
    MulAut ↥A where
  toFun x := ⟨ρ g x, (g.2 x).1 x.2⟩
  invFun x := ⟨ρ (g : Γ)⁻¹ x, ((uc22pwtStab ρ A).inv_mem g.2 x).1 x.2⟩
  left_inv x := Subtype.ext (by
    show ρ (g : Γ)⁻¹ (ρ (g : Γ) x) = x
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
  right_inv x := Subtype.ext (by
    show ρ (g : Γ) (ρ (g : Γ)⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
  map_mul' x y := Subtype.ext (by
    show ρ g ((x : X) * y) = ρ g x * ρ g y
    exact map_mul _ _ _)

@[expose] def uc22pwtRes (ρ : Γ →* MulAut X) (A : Subgroup X) : ↥(uc22pwtStab ρ A) →* MulAut ↥A where
  toFun := uc22pwtResAut ρ A
  map_one' := by
    ext x
    show ρ ((1 : ↥(uc22pwtStab ρ A)) : Γ) x = x
    rw [Subgroup.coe_one, map_one, MulAut.one_apply]
  map_mul' g g' := by
    ext x
    show ρ ((g * g' : ↥(uc22pwtStab ρ A)) : Γ) x = ρ g (ρ g' x)
    rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]

end Stab

section Quasisimple

theorem uc22pwt_quasisimple_normal {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

theorem uc22pwt_nc_of_quasisimple {X : Type*} [Group X] {A : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥A) {K : Subgroup X} (hKA : K ≤ A)
    (hKn : ∀ x ∈ A, ∀ y ∈ K, x * y * x⁻¹ ∈ K) :
    (∀ y ∈ K, ∀ x ∈ A, y * x = x * y) ∨ A ≤ K := by
  have hN : (K.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKn g g.2 n hn⟩
  rcases uc22pwt_quasisimple_normal hq hN with h | h
  · right
    intro x hx
    have : (⟨x, hx⟩ : ↥A) ∈ K.subgroupOf A := by rw [h]; trivial
    exact this
  · left
    intro y hy x hx
    have hy' : (⟨y, hKA hy⟩ : ↥A) ∈ K.subgroupOf A := hy
    have := Subgroup.mem_center_iff.1 (h hy') ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm

end Quasisimple

section Generation

theorem uc22pwt_gen_of_normal {X : Type*} [Group X] {A N H : Subgroup X} {w : X}
    (hNA : N ≤ A) (hw : w ∈ A) (hw2 : w ^ 2 = 1) (hgen : N ⊔ zpowers w = A)
    (hNC : ∀ K : Subgroup X, K ≤ A → (∀ x ∈ A, ∀ y ∈ K, x * y * x⁻¹ ∈ K) →
      (∀ y ∈ K, ∀ x ∈ A, y * x = x * y) ∨ A ≤ K)
    (hnc : ∃ x ∈ N, ∃ y ∈ A, x * y ≠ y * x) (hNH : N ≤ H)
    (hwH : ∀ n ∈ N, w * n * w⁻¹ ∈ H) : A ≤ H := by
  have e : w * w = 1 := by rw [← sq]; exact hw2
  have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right e
  set K : Subgroup X := N ⊔ N.map (MulAut.conj w).toMonoidHom with hK
  have hconjN : ∀ n ∈ N, w * n * w⁻¹ ∈ K := fun n hn =>
    Subgroup.mem_sup_right ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hKA : K ≤ A := by
    refine sup_le hNA ?_
    rintro _ ⟨n, hn, rfl⟩
    show w * n * w⁻¹ ∈ A
    exact A.mul_mem (A.mul_mem hw (hNA hn)) (A.inv_mem hw)
  have hKH : K ≤ H := by
    refine sup_le hNH ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hwH n hn
  have hwK : ∀ x ∈ K, w * x * w⁻¹ ∈ K := by
    have hle : K ≤ K.comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (fun n hn => hconjN n hn) ?_
      rintro _ ⟨n, hn, rfl⟩
      show w * (w * n * w⁻¹) * w⁻¹ ∈ K
      have h1 : w * (w * n * w⁻¹) * w⁻¹ = n := by
        rw [hinv]
        calc w * (w * n * w) * w = (w * w) * n * (w * w) := by group
          _ = n := by rw [e]; group
      rw [h1]
      exact Subgroup.mem_sup_left hn
    exact fun x hx => hle hx
  have hwnorm : w ∈ normalizer (K : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hwK x hx, fun hx => ?_⟩
    have h2 := hwK _ hx
    have h3 : w * (w * x * w⁻¹) * w⁻¹ = x := by
      rw [hinv]
      calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
        _ = x := by rw [e]; group
    rwa [h3] at h2
  have hAnorm : A ≤ normalizer (K : Set X) := by
    rw [← hgen]
    exact sup_le (fun n hn => Subgroup.le_normalizer (Subgroup.mem_sup_left hn))
      (Subgroup.zpowers_le.2 hwnorm)
  have hKn : ∀ x ∈ A, ∀ y ∈ K, x * y * x⁻¹ ∈ K := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hAnorm hx) y).1 hy
  rcases hNC K hKA hKn with hc | hAK
  · obtain ⟨x, hx, y, hy, hne⟩ := hnc
    exact (hne (hc x (Subgroup.mem_sup_left hx) y hy)).elim
  · exact hAK.trans hKH

end Generation

section Pair

variable {X : Type} [Group X] [Finite X]

theorem uc22pwt_le_normalizer_of_comm {A B : Subgroup X} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ normalizer (B : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h a ha x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h a⁻¹ (A.inv_mem ha) _ hx
    have h2 : x = a * x * a⁻¹ := by
      have h3 : x * a⁻¹ = (a * x * a⁻¹) * a⁻¹ := by
        calc x * a⁻¹ = a⁻¹ * (a * x * a⁻¹) := by group
          _ = (a * x * a⁻¹) * a⁻¹ := h1
      exact mul_right_cancel h3
    rw [h2]
    exact hx

theorem uc22pwt_exists_mul_of_comm {A B : Subgroup X} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b :=
  uc22pws_exists_mul_of_mem_sup (uc22pwt_le_normalizer_of_comm h) hx

theorem uc22pwt_isMulCommutative {X : Type*} [Group X] {H : Subgroup X}
    (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : IsMulCommutative H :=
  Subgroup.le_centralizer_iff_isMulCommutative.1 fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => h y hy x hx

structure UC22pwtPair (h h' : X) (m a b : ℕ) (α : Set ℕ) : Prop where
  comm : Commute h h'
  ord : orderOf h = m
  ord' : orderOf h' = m
  disj : ∀ i j : ℤ, h ^ i = h' ^ j → h ^ i = 1
  sqf : Squarefree m
  odd : Odd m
  ab : a * b = m
  cop : Nat.Coprime a b
  pr : ∀ p : ℕ, p.Prime → p ∣ m → (p ∈ α ↔ p ∣ a)

@[expose] def uc22pwtE (h h' : X) (a b : ℕ) : Subgroup X :=
  zpowers (h ^ a) ⊔ zpowers (h' ^ a) ⊔ zpowers (h ^ b * h' ^ b)

theorem uc22pwtE_le_M (h h' : X) (a b : ℕ) : uc22pwtE h h' a b ≤ zpowers h ⊔ zpowers h' := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_trans (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) a)) le_sup_left
  · exact le_trans (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers h') a)) le_sup_right
  · exact Subgroup.zpowers_le.2 (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) b))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers h') b)))

theorem uc22pwtE_ha_mem (h h' : X) (a b : ℕ) : h ^ a ∈ uc22pwtE h h' a b :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem uc22pwtE_ha'_mem (h h' : X) (a b : ℕ) : h' ^ a ∈ uc22pwtE h h' a b :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem uc22pwtE_d_mem (h h' : X) (a b : ℕ) : h ^ b * h' ^ b ∈ uc22pwtE h h' a b :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

namespace UC22pwtPair

variable {h h' : X} {m a b : ℕ} {α : Set ℕ} (P : UC22pwtPair h h' m a b α)

include P

theorem isMulCommutative_M : IsMulCommutative ↥(zpowers h ⊔ zpowers h') := by
  have key : ∀ x ∈ zpowers h ⊔ zpowers h', ∃ s t : ℤ, x = h ^ s * h' ^ t := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := uc22pwt_exists_mul_of_comm (A := zpowers h) (B := zpowers h')
      (fun a ha b hb => by
        obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (P.comm.zpow_zpow s t).eq) hx
    obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨s, t, rfl⟩
  refine uc22pwt_isMulCommutative fun x hx y hy => ?_
  obtain ⟨s, t, rfl⟩ := key x hx
  obtain ⟨s', t', rfl⟩ := key y hy
  have hAC : Commute (h ^ s) (h ^ s') := (Commute.refl h).zpow_zpow s s'
  have hAD : Commute (h ^ s) (h' ^ t') := P.comm.zpow_zpow s t'
  have hBC : Commute (h' ^ t) (h ^ s') := P.comm.symm.zpow_zpow t s'
  have hBD : Commute (h' ^ t) (h' ^ t') := (Commute.refl h').zpow_zpow t t'
  exact (Commute.mul_left (Commute.mul_right hAC hAD) (Commute.mul_right hBC hBD)).eq

theorem exists_zpow_of_mem_M {x : X} (hx : x ∈ zpowers h ⊔ zpowers h') :
    ∃ s t : ℤ, x = h ^ s * h' ^ t := by
  obtain ⟨y, hy, z, hz, rfl⟩ := uc22pwt_exists_mul_of_comm (A := zpowers h) (B := zpowers h')
    (fun a ha b hb => by
      obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (P.comm.zpow_zpow s t).eq) hx
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨s, t, rfl⟩

theorem pow_m : h ^ m = 1 := by
  rw [← P.ord]
  exact pow_orderOf_eq_one h

theorem pow_m' : h' ^ m = 1 := by
  rw [← P.ord']
  exact pow_orderOf_eq_one h'

theorem exists_exps_of_mem_E {x : X} (hx : x ∈ uc22pwtE h h' a b) :
    ∃ i j k : ℤ, x = h ^ ((a : ℤ) * i + b * k) * h' ^ ((a : ℤ) * j + b * k) := by
  have hM := P.isMulCommutative_M
  have h1 : zpowers (h ^ a) ⊔ zpowers (h' ^ a) ≤ zpowers h ⊔ zpowers h' :=
    sup_le (le_trans (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) a)) le_sup_left)
      (le_trans (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers h') a)) le_sup_right)
  have h2 : zpowers (h ^ b * h' ^ b) ≤ zpowers h ⊔ zpowers h' :=
    Subgroup.zpowers_le.2 (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) b))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers h') b)))
  obtain ⟨y, hy, z, hz, rfl⟩ := uc22pws_exists_mul_of_mem_sup (uc22pws_le_normalizer hM h1 h2) hx
  have h3 : zpowers (h ^ a) ≤ zpowers h ⊔ zpowers h' := le_trans le_sup_left h1
  have h4 : zpowers (h' ^ a) ≤ zpowers h ⊔ zpowers h' := le_trans le_sup_right h1
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := uc22pws_exists_mul_of_mem_sup (uc22pws_le_normalizer hM h3 h4) hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₁
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₂
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨i, j, k, ?_⟩
  have hc : Commute (h' ^ a) (h ^ b) := (P.comm.symm.pow_pow a b)
  rw [(P.comm.pow_pow b b).mul_zpow k]
  have e1 : (h ^ a) ^ i = h ^ ((a : ℤ) * i) := by rw [← zpow_natCast, ← zpow_mul]
  have e2 : (h' ^ a) ^ j = h' ^ ((a : ℤ) * j) := by rw [← zpow_natCast, ← zpow_mul]
  have e3 : (h ^ b) ^ k = h ^ ((b : ℤ) * k) := by rw [← zpow_natCast, ← zpow_mul]
  have e4 : (h' ^ b) ^ k = h' ^ ((b : ℤ) * k) := by rw [← zpow_natCast, ← zpow_mul]
  rw [e1, e2, e3, e4, zpow_add, zpow_add]
  have hc2 : Commute (h' ^ ((a : ℤ) * j)) (h ^ ((b : ℤ) * k)) := P.comm.symm.zpow_zpow _ _
  calc h ^ ((a : ℤ) * i) * h' ^ ((a : ℤ) * j) * (h ^ ((b : ℤ) * k) * h' ^ ((b : ℤ) * k))
      = h ^ ((a : ℤ) * i) * h ^ ((b : ℤ) * k) * (h' ^ ((a : ℤ) * j) * h' ^ ((b : ℤ) * k)) :=
        hc2.mul_mul_mul_comm _ _
    _ = _ := rfl

theorem isMulCommutative_E : IsMulCommutative ↥(uc22pwtE h h' a b) :=
  uc22pws_isMulCommutative_of_le P.isMulCommutative_M (uc22pwtE_le_M h h' a b)

theorem pow_m_of_mem_E {x : X} (hx : x ∈ uc22pwtE h h' a b) : x ^ m = 1 := by
  obtain ⟨i, j, k, rfl⟩ := P.exists_exps_of_mem_E hx
  have e1 : ∀ s : ℤ, (h ^ s) ^ m = 1 := fun s => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, P.pow_m, one_zpow]
  have e2 : ∀ s : ℤ, (h' ^ s) ^ m = 1 := fun s => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, P.pow_m', one_zpow]
  rw [(P.comm.zpow_zpow _ _).mul_pow, e1, e2, one_mul]

theorem odd_card_E : Odd (Nat.card (uc22pwtE h h' a b)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (uc22pwtE h h' a b) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.1 hodd
  obtain ⟨y, hy, hyo⟩ := uc22pws_exists_orderOf Nat.prime_two h2
  have : 2 ∣ m := hyo ▸ orderOf_dvd_of_pow_eq_one (P.pow_m_of_mem_E hy)
  exact (Nat.not_even_iff_odd.2 P.odd) (even_iff_two_dvd.2 this)

theorem card_E_dvd : Nat.card (uc22pwtE h h' a b) ∣ m * m := by
  let μ : ↥(zpowers h) × ↥(zpowers h') →* X :=
    (zpowers h).subtype.noncommCoprod (zpowers h').subtype (fun x y => by
      obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 y.2
      show Commute (x : X) (y : X)
      rw [← hs, ← ht]
      exact P.comm.zpow_zpow s t)
  have hle : uc22pwtE h h' a b ≤ μ.range := by
    intro x hx
    obtain ⟨i, j, k, rfl⟩ := P.exists_exps_of_mem_E hx
    exact ⟨(⟨h ^ ((a : ℤ) * i + b * k), Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩⟩,
      ⟨h' ^ ((a : ℤ) * j + b * k), Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩⟩), rfl⟩
  calc Nat.card (uc22pwtE h h' a b) ∣ Nat.card μ.range := Subgroup.card_dvd_of_le hle
    _ ∣ Nat.card (↥(zpowers h) × ↥(zpowers h')) :=
      Subgroup.card_dvd_of_surjective (f := μ.rangeRestrict) μ.rangeRestrict_surjective
    _ = m * m := by rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, P.ord, P.ord']

theorem rank_E : ∀ p : ℕ, p.Prime → ∃ Q : Sylow p ↥(uc22pwtE h h' a b),
    IsElemAbelian p (Q : Subgroup ↥(uc22pwtE h h' a b)) ∧ Nat.card Q ≤ p ^ 2 := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥(uc22pwtE h h' a b) := P.isMulCommutative_E
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(uc22pwtE h h' a b)) := inferInstance
  refine ⟨Q, ⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
    have hk' : ((x : uc22pwtE h h' a b) : X) ^ (p ^ k) = 1 := by
      have := congrArg (fun z : ↥Q => ((z : uc22pwtE h h' a b) : X)) hk
      simpa using this
    have hdvd1 : orderOf ((x : uc22pwtE h h' a b) : X) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd2 : orderOf ((x : uc22pwtE h h' a b) : X) ∣ m :=
      orderOf_dvd_of_pow_eq_one (P.pow_m_of_mem_E x.2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have h2 : p * p ∣ m := by
        refine dvd_trans ?_ (hj ▸ hdvd2)
        rw [← pow_two]
        exact pow_dvd_pow p (by omega)
      have := P.sqf p h2
      exact hp.not_isUnit this
    have hdp : orderOf ((x : uc22pwtE h h' a b) : X) ∣ p := by
      rw [hj]
      calc p ^ j ∣ p ^ 1 := pow_dvd_pow p hj1
        _ = p := pow_one p
    exact Subtype.ext (orderOf_dvd_iff_pow_eq_one.1 hdp)
  · rw [Sylow.card_eq_multiplicity]
    have hm0 : m ≠ 0 := P.ord ▸ (orderOf_pos h).ne'
    have hc0 : Nat.card (uc22pwtE h h' a b) ≠ 0 := Nat.card_pos.ne'
    have hf : (Nat.card (uc22pwtE h h' a b)).factorization p ≤ 2 := by
      have h1 : (Nat.card (uc22pwtE h h' a b)).factorization p ≤ (m * m).factorization p :=
        (Nat.factorization_le_iff_dvd hc0 (mul_ne_zero hm0 hm0)).2 P.card_E_dvd p
      rw [Nat.factorization_mul hm0 hm0] at h1
      have h2 : m.factorization p ≤ 1 := P.sqf.natFactorization_le_one p
      simp only [Finsupp.add_apply] at h1
      omega
    exact Nat.pow_le_pow_right hp.pos hf

theorem piSet_E : piSet (uc22pwtE h h' a b) = {p | p.Prime ∧ p ∣ m} := by
  have hm0 : m ≠ 0 := P.ord ▸ (orderOf_pos h).ne'
  ext p
  constructor
  · rintro ⟨hp, hdvd⟩
    exact ⟨hp, (hp.dvd_mul.1 (hdvd.trans P.card_E_dvd)).elim id id⟩
  · rintro ⟨hp, hpm⟩
    haveI : Fact p.Prime := ⟨hp⟩
    refine ⟨hp, ?_⟩
    have hab : p ∣ a ∨ p ∣ b := hp.dvd_mul.1 (P.ab ▸ hpm)
    have hy : ∃ y ∈ uc22pwtE h h' a b, orderOf y = p := by
      rcases hab with hpa | hpb
      · obtain ⟨a', ha'⟩ := hpa
        have hmpq : m = p * (a' * b) := by rw [← P.ab, ha', mul_assoc]
        have hq0 : a' * b ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hmpq
          exact hm0 hmpq
        set y : X := (h ^ b * h' ^ b) ^ a' with hy
        have hy1 : y = h ^ (b * a') * h' ^ (b * a') := by
          rw [hy, (P.comm.pow_pow b b).mul_pow, ← pow_mul, ← pow_mul]
        refine ⟨y, Subgroup.pow_mem _ (uc22pwtE_d_mem h h' a b) a', ?_⟩
        have hyp : y ^ p = 1 := by
          rw [hy1, (P.comm.pow_pow _ _).mul_pow, ← pow_mul, ← pow_mul]
          have : b * a' * p = m := by rw [hmpq]; ring
          rw [this, P.pow_m, P.pow_m', one_mul]
        refine orderOf_eq_prime hyp ?_
        intro hy0
        rw [hy1] at hy0
        have h1 : h ^ ((b * a' : ℕ) : ℤ) = h' ^ (-((b * a' : ℕ) : ℤ)) := by
          rw [zpow_natCast, zpow_neg, zpow_natCast]
          exact eq_inv_of_mul_eq_one_left hy0
        have h2 : h ^ ((b * a' : ℕ) : ℤ) = 1 := P.disj _ _ h1
        rw [zpow_natCast] at h2
        have h3 : m ∣ b * a' := P.ord ▸ orderOf_dvd_of_pow_eq_one h2
        have h4 : p * (a' * b) ≤ b * a' := by
          rw [← hmpq]
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [mul_comm]; exact hq0)) h3
        have h5 : 0 < a' * b := Nat.pos_of_ne_zero hq0
        have h6 : p * (a' * b) ≤ 1 * (a' * b) :=
          calc p * (a' * b) ≤ b * a' := h4
            _ = 1 * (a' * b) := by ring
        exact absurd (Nat.le_of_mul_le_mul_right h6 h5) (by have := hp.two_le; omega)
      · obtain ⟨b', hb'⟩ := hpb
        have hmpq : m = a * b' * p := by rw [← P.ab, hb']; ring
        have hq : m / p = a * b' := by
          rw [hmpq, Nat.mul_div_cancel _ hp.pos]
        refine ⟨h ^ (m / p), ?_, ?_⟩
        · have : h ^ (m / p) = (h ^ a) ^ b' := by rw [hq, ← pow_mul]
          rw [this]
          exact Subgroup.pow_mem _ (uc22pwtE_ha_mem h h' a b) b'
        · have := orderOf_pow_orderOf_div (x := h) (n := p) (by rw [P.ord]; exact hm0)
            (by rw [P.ord]; exact hpm)
          rwa [P.ord] at this
    obtain ⟨y, hyE, hyo⟩ := hy
    exact hyo ▸ Subgroup.orderOf_dvd_natCard _ hyE

theorem mem_diag_of_primes {x : X} (hx : x ∈ uc22pwtE h h' a b)
    (hα : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ α) : x ∈ zpowers (h ^ b * h' ^ b) := by
  have hm0 : m ≠ 0 := P.ord ▸ (orderOf_pos h).ne'
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hab0 := P.ab
    rw [zero_mul] at hab0
    exact hm0 hab0.symm
  obtain ⟨i, j, k, hxe⟩ := P.exists_exps_of_mem_E hx
  have hom : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one (P.pow_m_of_mem_E hx)
  have hpa : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∣ a := fun p hp hpo =>
    (P.pr p hp (hpo.trans hom)).1 (hα p hp hpo)
  have hcop : Nat.Coprime (orderOf x) b := by
    refine Nat.coprime_of_dvd fun p hp hpo hpb => ?_
    have := Nat.eq_one_of_dvd_coprimes P.cop (hpa p hp hpo) hpb
    exact hp.one_lt.ne' this
  have hoa : orderOf x ∣ a := hcop.dvd_of_dvd_mul_right (P.ab ▸ hom)
  have hxa : x ^ a = 1 := orderOf_dvd_iff_pow_eq_one.1 hoa
  set s : ℤ := (a : ℤ) * i + b * k with hs
  set t : ℤ := (a : ℤ) * j + b * k with ht
  have e1 : (h ^ s) ^ a = h ^ (s * a) := by rw [← zpow_natCast, ← zpow_mul]
  have e2 : (h' ^ t) ^ a = h' ^ (t * a) := by rw [← zpow_natCast, ← zpow_mul]
  have hx2 : h ^ (s * a) * h' ^ (t * a) = 1 := by
    rw [← e1, ← e2, ← (P.comm.zpow_zpow s t).mul_pow, ← hxe]
    exact hxa
  have hh : h ^ (s * a) = 1 := by
    apply P.disj (s * a) (-(t * a))
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hx2
  have hh' : h' ^ (t * a) = 1 := by
    rw [hh, one_mul] at hx2
    exact hx2
  have hm' : (m : ℤ) = (a : ℤ) * b := by rw [← P.ab]; push_cast; ring
  have hms : (m : ℤ) ∣ s * a := by
    rw [← P.ord]
    exact orderOf_dvd_iff_zpow_eq_one.2 hh
  have hmt : (m : ℤ) ∣ t * a := by
    rw [← P.ord']
    exact orderOf_dvd_iff_zpow_eq_one.2 hh'
  have hcopz : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.2 P.cop.symm
  have hbs : (b : ℤ) ∣ s := by
    have h1 : (a : ℤ) * b ∣ a * s := by
      rw [← hm', mul_comm (a : ℤ) s]
      exact hms
    exact (mul_dvd_mul_iff_left (by exact_mod_cast ha0)).1 h1
  have hbt : (b : ℤ) ∣ t := by
    have h1 : (a : ℤ) * b ∣ a * t := by
      rw [← hm', mul_comm (a : ℤ) t]
      exact hmt
    exact (mul_dvd_mul_iff_left (by exact_mod_cast ha0)).1 h1
  have hbi : (b : ℤ) ∣ i := by
    have h1 : (b : ℤ) ∣ (a : ℤ) * i := by
      have h2 : (b : ℤ) ∣ s - b * k := dvd_sub hbs (dvd_mul_right _ _)
      have e : s - b * k = a * i := by rw [hs]; ring
      rwa [e] at h2
    exact hcopz.dvd_of_dvd_mul_left h1
  have hbj : (b : ℤ) ∣ j := by
    have h1 : (b : ℤ) ∣ (a : ℤ) * j := by
      have h2 : (b : ℤ) ∣ t - b * k := dvd_sub hbt (dvd_mul_right _ _)
      have e : t - b * k = a * j := by rw [ht]; ring
      rwa [e] at h2
    exact hcopz.dvd_of_dvd_mul_left h1
  have hA : h ^ ((a : ℤ) * i) = 1 := by
    obtain ⟨i₁, hi₁⟩ := hbi
    have : (a : ℤ) * i = (m : ℤ) * i₁ := by rw [hi₁, hm']; ring
    rw [this, zpow_mul, zpow_natCast, P.pow_m, one_zpow]
  have hB : h' ^ ((a : ℤ) * j) = 1 := by
    obtain ⟨j₁, hj₁⟩ := hbj
    have : (a : ℤ) * j = (m : ℤ) * j₁ := by rw [hj₁, hm']; ring
    rw [this, zpow_mul, zpow_natCast, P.pow_m', one_zpow]
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [hxe, (P.comm.pow_pow b b).mul_zpow k, zpow_add, zpow_add, hA, hB, one_mul, one_mul,
    ← zpow_natCast h b, ← zpow_natCast h' b, ← zpow_mul, ← zpow_mul]

end UC22pwtPair

end Pair

section Ctx

variable {X Γ : Type} [Group X] [Group Γ]

@[expose] def uc22pwtStab2 (ρ : Γ →* MulAut X) (A₁ A₂ : Subgroup X) : Subgroup Γ :=
  uc22pwtStab ρ A₁ ⊓ uc22pwtStab ρ A₂

theorem mem_uc22pwtStab2 {ρ : Γ →* MulAut X} {A₁ A₂ : Subgroup X} {g : Γ} :
    g ∈ uc22pwtStab2 ρ A₁ A₂ ↔
      (∀ x, x ∈ A₁ ↔ ρ g x ∈ A₁) ∧ (∀ x, x ∈ A₂ ↔ ρ g x ∈ A₂) :=
  Iff.rfl

structure UC22pwtCtx (ρ : Γ →* MulAut X) (τ : Γ) (U A₁ A₂ : Subgroup X) : Prop where
  comm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a
  sup : A₁ ⊔ A₂ = ⊤
  swap₁ : ∀ x, x ∈ A₁ ↔ ρ τ x ∈ A₂
  swap₂ : ∀ x, x ∈ A₂ ↔ ρ τ x ∈ A₁
  perm : ∀ g : Γ, g ∈ uc22pwtStab2 ρ A₁ A₂ ∨ τ⁻¹ * g ∈ uc22pwtStab2 ρ A₁ A₂
  Uinv : ∀ (g : Γ) (x : X), x ∈ U ↔ ρ g x ∈ U
  Usplit : U ≤ (U ⊓ A₁) ⊔ (U ⊓ A₂)

end Ctx

section Elem

variable {X Γ : Type} [Group X] [Group Γ]

structure UC22pwtElem {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X}
    (C : UC22pwtCtx ρ τ U A₁ A₂) (h w₁ : X) (m a b : ℕ) (α : Set ℕ) : Prop where
  h_mem : h ∈ A₁
  ord : orderOf h = m
  sqf : Squarefree m
  odd : Odd m
  ab : a * b = m
  cop : Nat.Coprime a b
  pr : ∀ p : ℕ, p.Prime → p ∣ m → (p ∈ α ↔ p ∣ a)
  ex : ∃ p : ℕ, p.Prime ∧ p ∣ m
  Z : ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ Nat.card (Subgroup.center ↥A₁)
  hnorm : ∀ u ∈ U ⊓ A₁, h * u * h⁻¹ ∈ U ⊓ A₁ ∧ h⁻¹ * u * h ∈ U ⊓ A₁
  hinv : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ρ g h ∈ zpowers h ⊔ (U ⊓ A₁)
  halpha : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ρ g (h ^ b) * (h ^ b)⁻¹ ∈ U ⊓ A₁
  w_mem : w₁ ∈ A₁
  w_sq : w₁ ^ 2 = 1
  w_inv : w₁ * h * w₁⁻¹ = h⁻¹
  w_gen : (normalizer ((U ⊓ A₁ : Subgroup X) : Set X) ⊓ A₁) ⊔ zpowers w₁ = A₁
  nc : ∀ K : Subgroup X, K ≤ A₁ → (∀ x ∈ A₁, ∀ y ∈ K, x * y * x⁻¹ ∈ K) →
    (∀ y ∈ K, ∀ x ∈ A₁, y * x = x * y) ∨ A₁ ≤ K

end Elem

end CFSG.LocalAnalysis.UniquenessCase.UC22
