module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec8SectionOrder
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GroupTheory.SteinbergBY (isPGroup_inSubgroup_pCore)
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_irred_W1V1 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) (hC : Conc83 hc n t) :
    ∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m ∧ (n = 11 ∧ m = 3 ∨ n = 17 ∧ m = 4) ∧
      Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 ^ m) ∧
      Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ (2 * m + 2) ∧
      ∀ U : Subgroup G, Sec8V1 M Q Z B t r ≤ U → U ≤ Sec8W1 M Q Z B t r →
        (∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ U = U) →
        U = Sec8V1 M Q Z B t r ∨ U = Sec8W1 M Q Z B t r := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨m, hn11, hmSp⟩ : ∃ m : ℕ, (n = 11 ∧ m = 3 ∨ n = 17 ∧ m = 4) ∧ SpMNat hc t m := by
    rcases hC with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨3, Or.inl ⟨h1, rfl⟩, h2⟩
    · exact ⟨4, Or.inr ⟨h1, rfl⟩, h2⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8W1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).2 hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8V1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).1 hy
  have h53b := h53.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53c := h53.2.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  obtain ⟨a, han, hV1c, hWc⟩ := sec83_count_A h53 sec8InvStatement_holds hs5 hr hpts
  have ha1 : a = 1 := by
    rcases hn11 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h2 <;> subst h1 <;> omega
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hpos : 0 < Nat.card ↥(Sec8V1 M Q Z B t r) := Nat.card_pos
  have hWV : Nat.card ↥(Sec8W1 M Q Z B t r) =
      Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 ^ m) := by
    rw [hWc, ha1, one_mul]
  refine ⟨m, hm2, hmSp, hn11, hWV, hV1c, ?_⟩
  intro U hIU hUP hUinv
  obtain ⟨-, b, hb⟩ := sec8_invariant_section (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (P := Sec8W1 M Q Z B t r) (I := Sec8V1 M Q Z B t r) (L₁ := LB M Q B)
    (L₂ := LB M Q (conjSubgroup r B))
    (A₁ := (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (A₂ := (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) (U := U) φ
    hpts.range (by omega) hpts.ker hP hI h53b.2 h53c hLR hLCR hpts.uu' hpts.u_ne_zero hpts.hL
    hL2 (fun y hy => hQN (hc.sq_mem_Q_of_mem_LB hy)) hrR (hc.LB_conj hrM).symm hIU hUP hUinv
  rw [hpts.card] at hb
  have hle : Nat.card ↥U ≤ Nat.card ↥(Sec8W1 M Q Z B t r) := Subgroup.card_le_of_le hUP
  rw [hb, hWV] at hle
  have h1 : Nat.card Z ^ (2 ^ m * b) ≤ Nat.card Z ^ (2 ^ m) :=
    Nat.le_of_mul_le_mul_left hle hpos
  have h2 : 2 ^ m * b ≤ 2 ^ m := (Nat.pow_le_pow_iff_right hq2).mp h1
  have hb1 : b ≤ 1 := by
    by_contra hb2
    have : 2 ^ m * 2 ≤ 2 ^ m * b := Nat.mul_le_mul_left _ (by omega)
    have : 0 < 2 ^ m := by positivity
    omega
  interval_cases b
  · left
    exact (Subgroup.eq_of_le_of_card_ge hIU (by rw [hb]; simp)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hUP (by rw [hb, hWV]; simp)

end CFSG.RankThree.GF2n.Stroth80
