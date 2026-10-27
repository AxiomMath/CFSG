module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

private theorem s16c11_routefg_card_coe_mul_mul_card_inf (C N : Subgroup H) :
    Nat.card ((C : Set H) * (N : Set H)) * Nat.card (C ⊓ N : Subgroup H) =
      Nat.card C * Nat.card N := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient N (C : Set H)
  have himg : Nat.card ((C : Set H).image ((↑) : H → H ⧸ N)) = N.relIndex C := by
    have horb : MulAction.orbit C ((1 : H) : H ⧸ N) =
        (C : Set H).image ((↑) : H → H ⧸ N) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : H), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer C ((1 : H) : H ⧸ N) = N.subgroupOf C := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : H) : H ⧸ N)) = ((a : H) : H ⧸ N) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        have := N.inv_mem h
        simpa using this
      · intro h
        have := N.inv_mem h
        simpa using this
    have := MulAction.index_stabilizer C ((1 : H) : H ⧸ N)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := C)
  rw [inf_comm N C] at h2
  rw [h1, himg]
  calc Nat.card N * N.relIndex C * Nat.card (C ⊓ N : Subgroup H)
      = Nat.card N * (N.relIndex C * Nat.card (C ⊓ N : Subgroup H)) := by ring
    _ = Nat.card C * Nat.card N := by rw [h2]; ring

private theorem s16c11_routefg_padicValNat_le_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0)
    (h : a ∣ b) : padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd (p := p) (n := a)).trans h)

theorem s16c11_padicValNat_card_le_of_set_mul {X C N : Subgroup H}
    (h : (X : Set H) = (C : Set H) * (N : Set H)) (p : ℕ) [Fact p.Prime] :
    padicValNat p (Nat.card ↥X) ≤ padicValNat p (Nat.card ↥C) + padicValNat p (Nat.card ↥N) := by
  have hcard : Nat.card ↥X * Nat.card (C ⊓ N : Subgroup H) = Nat.card ↥C * Nat.card ↥N := by
    have h1 := s16c11_routefg_card_coe_mul_mul_card_inf (H := H) C N
    rw [← h] at h1
    exact h1
  have hdvd : Nat.card ↥X ∣ Nat.card ↥C * Nat.card ↥N :=
    ⟨Nat.card (C ⊓ N : Subgroup H), hcard.symm⟩
  calc padicValNat p (Nat.card ↥X)
      ≤ padicValNat p (Nat.card ↥C * Nat.card ↥N) :=
        s16c11_routefg_padicValNat_le_of_dvd (p := p)
          (Nat.mul_pos Nat.card_pos Nat.card_pos).ne' hdvd
    _ = padicValNat p (Nat.card ↥C) + padicValNat p (Nat.card ↥N) :=
        padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne'

theorem s16c11_not_isCyclic_of_exponent {p : ℕ} (hp : p.Prime) {P : Subgroup H}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hcard : p ^ 2 ∣ Nat.card ↥P) : ¬ IsCyclic ↥P := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have horder : orderOf g = Nat.card ↥P := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hexp (g : H) g.2, Subgroup.coe_one]
  have hp_dvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have horder_dvd : Nat.card ↥P ∣ p := by rwa [← horder]
  have hp2_dvd : p ^ 2 ∣ p := hcard.trans horder_dvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2_dvd
  nlinarith [hp.two_le]

theorem s16c11_le_of_normal_pGroup_of_set_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S P X C N : Subgroup H} (hS : IsPGroup 2 ↥S) (hP : IsPGroup p ↥P)
    (hSP : S ≤ normalizer (P : Set H)) (hX : X = P ⊔ S)
    (hfac : (X : Set H) = (C : Set H) * (N : Set H)) (hCP : C ⊓ P = ⊥) : P ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPX : P ≤ X := by rw [hX]; exact le_sup_left
  have hSX : S ≤ X := by rw [hX]; exact le_sup_right
  have hCX : C ≤ X := by
    intro c hc
    have hmem : c ∈ (C : Set H) * (N : Set H) := ⟨c, hc, 1, N.one_mem, mul_one c⟩
    rw [← hfac] at hmem
    exact hmem
  have hNX : N ≤ X := by
    intro n hn
    have hmem : n ∈ (C : Set H) * (N : Set H) := ⟨1, C.one_mem, n, hn, one_mul n⟩
    rw [← hfac] at hmem
    exact hmem
  have hXn : X ≤ normalizer (P : Set H) := by
    rw [hX]
    exact sup_le Subgroup.le_normalizer hSP
  have hPS : (X : Set H) = (P : Set H) * (S : Set H) := by
    rw [hX]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P S hSP
  have hvS0 : padicValNat p (Nat.card ↥S) = 0 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hS
    rw [hn, padicValNat_prime_prime_pow n hp2]
  have hvXle : padicValNat p (Nat.card ↥X) ≤
      padicValNat p (Nat.card ↥P) + padicValNat p (Nat.card ↥S) :=
    s16c11_padicValNat_card_le_of_set_mul hPS p
  have hvPX : padicValNat p (Nat.card ↥P) ≤ padicValNat p (Nat.card ↥X) :=
    s16c11_routefg_padicValNat_le_of_dvd (p := p) (Nat.card_pos (α := ↥X)).ne'
      (Subgroup.card_dvd_of_le hPX)
  have hvX : padicValNat p (Nat.card ↥X) = padicValNat p (Nat.card ↥P) := by
    refine le_antisymm ?_ hvPX
    rw [hvS0, add_zero] at hvXle
    exact hvXle
  have key : ∀ R : Subgroup H, R ≤ X → IsPGroup p ↥R → R ≤ P := by
    intro R hRX hR
    have hPR : R ≤ normalizer (P : Set H) := hRX.trans hXn
    have hsup : IsPGroup p ↥(P ⊔ R) := IsPGroup.to_sup_of_normal_left' hP hR hPR
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hsup
    have hdvd : Nat.card ↥(P ⊔ R) ∣ Nat.card ↥X :=
      Subgroup.card_dvd_of_le (sup_le hPX hRX)
    have hvle : padicValNat p (Nat.card ↥(P ⊔ R)) ≤ padicValNat p (Nat.card ↥X) :=
      s16c11_routefg_padicValNat_le_of_dvd (p := p) (Nat.card_pos (α := ↥X)).ne' hdvd
    have hcard_sup : Nat.card ↥(P ⊔ R) ≤ Nat.card ↥P := by
      have hvP : Nat.card ↥P = p ^ padicValNat p (Nat.card ↥P) := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
        rw [hk, padicValNat.prime_pow]
      rw [hm, hvP, ← hvX]
      refine Nat.pow_le_pow_right hp.pos ?_
      rw [hm, padicValNat.prime_pow] at hvle
      exact hvle
    have hEq : P ⊔ R = P :=
      (Subgroup.eq_of_le_of_card_ge (H := P) (K := P ⊔ R) le_sup_left hcard_sup).symm
    exact le_sup_right.trans (le_of_eq hEq)
  have hvC0 : padicValNat p (Nat.card ↥C) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hpdvd
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hpdvd
    have hcC : (c : H) ∈ C := c.2
    have hsubX : Subgroup.zpowers (c : H) ≤ X :=
      (Subgroup.zpowers_le.mpr hcC).trans hCX
    have hpgrp : IsPGroup p ↥(Subgroup.zpowers (c : H)) := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]
      simp
    have hleP := key (Subgroup.zpowers (c : H)) hsubX hpgrp
    have hcP : (c : H) ∈ P := hleP (Subgroup.mem_zpowers (c : H))
    have hcbot : (c : H) ∈ (C ⊓ P : Subgroup H) := ⟨hcC, hcP⟩
    rw [hCP, Subgroup.mem_bot] at hcbot
    have hone : c = 1 := Subtype.ext hcbot
    rw [hone, orderOf_one] at hc
    exact hp.ne_one hc.symm
  have hvCN : padicValNat p (Nat.card ↥X) ≤
      padicValNat p (Nat.card ↥C) + padicValNat p (Nat.card ↥N) :=
    s16c11_padicValNat_card_le_of_set_mul hfac p
  have hvPN : padicValNat p (Nat.card ↥P) ≤ padicValNat p (Nat.card ↥N) := by
    calc padicValNat p (Nat.card ↥P)
        = padicValNat p (Nat.card ↥X) := hvX.symm
      _ ≤ padicValNat p (Nat.card ↥C) + padicValNat p (Nat.card ↥N) := hvCN
      _ = padicValNat p (Nat.card ↥N) := by rw [hvC0, zero_add]
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := ↥N)
  let Q' : Subgroup H := (Q : Subgroup ↥N).map N.subtype
  have hQ'leN : Q' ≤ N := Subgroup.map_subtype_le _
  have hQ'X : Q' ≤ X := hQ'leN.trans hNX
  have hQ'grp : IsPGroup p ↥Q' := Q.isPGroup'.map N.subtype
  have hQ'card : Nat.card ↥Q' = p ^ padicValNat p (Nat.card ↥N) := by
    rw [show Q' = (Q : Subgroup ↥N).map N.subtype from rfl,
      Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity Q,
      Nat.factorization_def _ hp]
  have hPcard : Nat.card ↥P = p ^ padicValNat p (Nat.card ↥P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk, padicValNat.prime_pow]
  have hle : Nat.card ↥P ≤ Nat.card ↥Q' := by
    rw [hPcard, hQ'card]
    exact Nat.pow_le_pow_right hp.pos hvPN
  have hQ'P : Q' ≤ P := key Q' hQ'X hQ'grp
  have hQ'eq : Q' = P := Subgroup.eq_of_le_of_card_ge hQ'P hle
  rw [← hQ'eq]
  exact hQ'leN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo