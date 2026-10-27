module

public import CFSG.Sporadic.Fi24I301.Elements
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
import CFSG.RankThree.GF2n.Parrott.Section1Extraspecial
import CFSG.LargeExtraspecial.DWTim79.Bridge
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Solv

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
  CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.Sporadic.Fi24 (J)

section Generic

theorem conj_pow_eq_of_conj {G : Type*} [Group G] {c d z : G} (hz : d * z = z * d)
    (h : d * c * d⁻¹ = z * c) (n : ℕ) : d ^ n * c * (d ^ n)⁻¹ = z ^ n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdz : d * z ^ n = z ^ n * d := ((show Commute d z from hz).pow_right n).eq
    calc d ^ (n + 1) * c * (d ^ (n + 1))⁻¹ = d * (d ^ n * c * (d ^ n)⁻¹) * d⁻¹ := by group
      _ = d * z ^ n * c * d⁻¹ := by rw [ih]; group
      _ = z ^ n * (d * c * d⁻¹) := by rw [hdz]; group
      _ = z ^ (n + 1) * c := by rw [h, pow_succ, mul_assoc]

theorem mem_centralizer_singleton_subtype_iff {G : Type*} [Group G] {C : Subgroup G} {c d : C} :
    c ∈ Subgroup.centralizer ({d} : Set C) ↔
      (c : G) ∈ Subgroup.centralizer ({(d : G)} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← Subtype.val_inj, Subgroup.coe_mul, Subgroup.coe_mul]

theorem map_subtype_inf_centralizer {G : Type*} [Group G] {C : Subgroup G} (Q : Subgroup C)
    (d : C) : Q.map C.subtype ⊓ Subgroup.centralizer ({(d : G)} : Set G) =
      (Q ⊓ Subgroup.centralizer ({d} : Set C)).map C.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hcd⟩
    exact ⟨c, ⟨hc, mem_centralizer_singleton_subtype_iff.2 hcd⟩, rfl⟩
  · rintro ⟨c, ⟨hc, hcd⟩, rfl⟩
    exact ⟨⟨c, hc, rfl⟩, mem_centralizer_singleton_subtype_iff.1 hcd⟩

end Generic

theorem fi24Phi_mem_fi24P (k : ↥fi24K) : fi24Phi k ∈ fi24P := by
  have key : ∀ x ∈ Subgroup.closure ({fi24Sa, fi24Sb} : Set (Equiv.Perm (Fin 504))),
      ∀ hx : x ∈ fi24K, fi24Phi ⟨x, hx⟩ ∈ fi24P := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
      intro hx
      rcases ht with rfl | rfl
      · rw [fi24Phi_Sa, fi24P_eq]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [fi24Phi_Sb, fi24P_eq]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one =>
      intro hx
      rw [show (⟨1, hx⟩ : ↥fi24K) = 1 from rfl, map_one]
      exact fi24P.one_mem
    | mul x y hx' hy' ihx ihy =>
      intro hxy
      have hx2 : x ∈ fi24K := by rw [fi24K_eq]; exact hx'
      have hy2 : y ∈ fi24K := by rw [fi24K_eq]; exact hy'
      rw [show (⟨x * y, hxy⟩ : ↥fi24K) = ⟨x, hx2⟩ * ⟨y, hy2⟩ from rfl, map_mul]
      exact fi24P.mul_mem (ihx hx2) (ihy hy2)
    | inv x hx' ihx =>
      intro hxi
      have hx2 : x ∈ fi24K := by rw [fi24K_eq]; exact hx'
      rw [show (⟨x⁻¹, hxi⟩ : ↥fi24K) = (⟨x, hx2⟩ : ↥fi24K)⁻¹ from rfl, map_inv]
      exact fi24P.inv_mem (ihx hx2)
  have hk : (k : Equiv.Perm (Fin 504)) ∈ Subgroup.closure {fi24Sa, fi24Sb} := by
    rw [← fi24K_eq]
    exact k.2
  exact key k hk k.2

section D


theorem dJC_pow_three : (⟨dJ, xJ_mem 0⟩ : ↥fi24C) ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow]; exact xJ_pow_three (i := 0) (by norm_num))

theorem rowR0_fi24_eq :
    CFSG.LocalAnalysis.GLTheoremA.H301.rowR0Of dJ (fi24QC.map fi24C.subtype) =
      (fi24QC ⊓ Subgroup.centralizer ({⟨dJ, xJ_mem 0⟩} : Set ↥fi24C)).map fi24C.subtype :=
  map_subtype_inf_centralizer fi24QC ⟨dJ, xJ_mem 0⟩

theorem card_fi24N_inf_centralizer_dJ :
    Nat.card ↥(fi24N ⊓ Subgroup.centralizer
      ({fi24Rho ⟨dJ, xJ_mem 0⟩} : Set (Equiv.Perm (Fin 504)))) = 256 := by
  rw [fi24Rho_xJ 0, fi24KLetterG_eq]
  exact rowFacts.2.2.2.2.1

end D

section Rho


theorem comm_of_fi24Rho_comm {c d : ↥fi24C} (hd : d ^ 3 = 1)
    (h : fi24Rho c * fi24Rho d = fi24Rho d * fi24Rho c) : c * d = d * c := by
  obtain ⟨z, hz⟩ : ∃ z : ↥fi24C, z = ⟨fi24R2, fi24R2_mem_C⟩ := ⟨_, rfl⟩
  have hzd : d * z = z * d := by
    rw [hz]
    exact Subtype.ext ((Subgroup.mem_centralizer_singleton_iff (G := J)).1 d.2)
  have hz1 : z ≠ 1 := by
    rw [hz]
    exact fun h1 => fi24R2_ne_one (congrArg Subtype.val h1)
  have hzz : z * z = 1 := by
    rcases (fi24Rho_eq_one_iff (z * z)).1 (by rw [map_mul, hz, fi24Rho_z, one_mul]) with h1 | h1
    · exact h1
    · rw [← hz] at h1
      exact absurd (mul_left_cancel (a := z) (by rw [mul_one]; exact h1)) hz1
  have hk : fi24Rho (d * c * d⁻¹ * c⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← h]
    group
  rcases (fi24Rho_eq_one_iff _).1 hk with h1 | h1
  · calc c * d = (d * c * d⁻¹ * c⁻¹)⁻¹ * (d * c) := by group
      _ = d * c := by rw [h1, inv_one, one_mul]
  · exfalso
    rw [← hz] at h1
    have h2 : d * c * d⁻¹ = z * c := by
      calc d * c * d⁻¹ = d * c * d⁻¹ * c⁻¹ * c := by group
        _ = z * c := by rw [h1]
    have h3 := @conj_pow_eq_of_conj ↥fi24C inferInstance c d z hzd h2 3
    rw [hd, inv_one, one_mul, mul_one] at h3
    have h5 : z ^ 3 = 1 := mul_right_cancel (b := c) (by rw [one_mul]; exact h3.symm)
    have h6 : z ^ 3 = z := by
      rw [pow_succ, pow_two, hzz, one_mul]
    exact hz1 (h6.symm.trans h5)


theorem card_fi24QC_inf_centralizer {d : ↥fi24C} (hd : d ^ 3 = 1)
    (hN : Nat.card ↥(fi24N ⊓ Subgroup.centralizer
      ({fi24Rho d} : Set (Equiv.Perm (Fin 504)))) = 256) :
    Nat.card ↥(fi24QC ⊓ Subgroup.centralizer ({d} : Set ↥fi24C)) = 2 ^ 9 := by
  have hX : fi24QC ⊓ Subgroup.centralizer ({d} : Set ↥fi24C) =
      (fi24N ⊓ Subgroup.centralizer ({fi24Rho d} : Set (Equiv.Perm (Fin 504)))).comap fi24Rho := by
    ext c
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact and_congr Iff.rfl
      ⟨fun hc => by simpa only [map_mul] using congrArg fi24Rho hc, comm_of_fi24Rho_comm hd⟩
  have hle : fi24N ⊓ Subgroup.centralizer ({fi24Rho d} : Set (Equiv.Perm (Fin 504))) ≤
      fi24Rho.range := by
    rw [fi24Rho_range_card.1]
    exact inf_le_left.trans (fi24N_le_fi24K fi24_twoBKCheck)
  rw [hX, card_comap_of_le_range _ _ hle, fi24Rho_range_card.2, hN]
  norm_num

theorem card_rowR0_fi24 :
    Nat.card ↥(CFSG.LocalAnalysis.GLTheoremA.H301.rowR0Of dJ (fi24QC.map fi24C.subtype)) =
      2 ^ 9 := by
  rw [rowR0_fi24_eq, Subgroup.card_map_of_injective fi24C.subtype_injective]
  exact card_fi24QC_inf_centralizer dJC_pow_three card_fi24N_inf_centralizer_dJ

end Rho

section C


theorem isSolvable_centralizer_fi24C {d : ↥fi24C}
    (hQ : Nat.card ↥(fi24QC ⊓ Subgroup.centralizer ({d} : Set ↥fi24C)) = 2 ^ 9)
    (hP : Nat.card ↥(fi24P ⊓ Subgroup.centralizer
      ({fi24Psi d} : Set (Equiv.Perm (Fin 378)))) = 5832) :
    Group.IsSolvable ↥(Subgroup.centralizer ({d} : Set ↥fi24C)) := by
  haveI := fi24C_finite
  have hmemQ : ∀ c : ↥fi24C, c ∈ fi24QC ↔ fi24Psi c = 1 := fun c => by
    rw [fi24QC_eq, Subgroup.mem_comap, MonoidHom.mem_ker]
    rfl
  let f : ↥(Subgroup.centralizer ({d} : Set ↥fi24C)) →* Equiv.Perm (Fin 378) :=
    fi24Psi.comp (Subgroup.centralizer ({d} : Set ↥fi24C)).subtype
  have hker : Nat.card f.ker = 2 ^ 9 := by
    rw [← hQ]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨(hmemQ _).2 (MonoidHom.mem_ker.1 x.2), x.1.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).2⟩,
          MonoidHom.mem_ker.2 ((hmemQ _).1 (Subgroup.mem_inf.1 y.2).1)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hrange : f.range ≤
      fi24P ⊓ Subgroup.centralizer ({fi24Psi d} : Set (Equiv.Perm (Fin 378))) := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show fi24Phi (fi24RhoK x.1) ∈ fi24P
      exact fi24Phi_mem_fi24P _
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show fi24Psi x.1 * fi24Psi d = fi24Psi d * fi24Psi x.1
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 x.2]
  have hdvd : Nat.card ↥(Subgroup.centralizer ({d} : Set ↥fi24C)) ∣ 2 ^ 12 * 3 ^ 6 := by
    rw [← Subgroup.card_ker_mul_card_range f, hker]
    have h1 := Subgroup.card_dvd_of_le hrange
    rw [hP] at h1
    calc 2 ^ 9 * Nat.card f.range ∣ 2 ^ 9 * 5832 := Nat.mul_dvd_mul_left _ h1
      _ = 2 ^ 12 * 3 ^ 6 := by norm_num
  exact CFSG.LocalAnalysis.GLTheoremA.H301.isSolvable_of_pow_two_mul_three 12 6 fun g =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard g).trans hdvd)


theorem rowR0_fi24_extraspecial :
    CFSG.LocalAnalysis.GLTheoremA.S8.IsExtraSpec2
      (CFSG.LocalAnalysis.GLTheoremA.H301.rowR0Of dJ (fi24QC.map fi24C.subtype)) := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  haveI := fi24C_finite
  haveI := fi24QC_extraspecial
  have hR : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (fi24QC.map fi24C.subtype) := by
    refine (CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 _).1 ?_
    exact (CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_map_iff fi24QC fi24C.subtype
      fi24C.subtype_injective).2 (CFSG.IsExtraspecial.isExtraspecialPGroup (p := 2) (P := ↥fi24QC))
  have hP : IsPGroup 3 (Subgroup.zpowers dJ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_dJ, pow_one])
  have hPne : Subgroup.zpowers dJ ≠ ⊥ := Subgroup.zpowers_ne_bot.2 dJ_ne_one
  have hNP : Subgroup.zpowers dJ ≤
      Subgroup.normalizer ((fi24QC.map fi24C.subtype : Subgroup J) : Set J) := by
    haveI := fi24QC_normal
    rw [Subgroup.zpowers_le]
    have h := Subgroup.le_normalizer_map (H := fi24QC) fi24C.subtype
    rw [Subgroup.normalizer_eq_top] at h
    exact h ⟨⟨dJ, xJ_mem 0⟩, Subgroup.mem_top _, rfl⟩
  have hcent : Subgroup.centralizer ((Subgroup.zpowers dJ : Subgroup J) : Set J) =
      Subgroup.centralizer ({dJ} : Set J) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hc := card_rowR0_fi24
  rw [CFSG.LocalAnalysis.GLTheoremA.H301.rowR0Of] at hc ⊢
  rcases CFSG.RankThree.GF2n.Parrott.prop5_centralizer Nat.prime_three (by norm_num) hR hP hPne
    hNP with h | h
  · rw [hcent] at h
    exact (CFSG.LargeExtraspecial.DWTim79.timmesfeldIsExtraspecial_iff_isExtraspecialPGroup _).2
      ((CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 _).2 h)
  · exfalso
    rw [hcent] at h
    have h2 : Nat.card ↥((Subgroup.center ↥(fi24QC.map fi24C.subtype)).map
        (fi24QC.map fi24C.subtype).subtype) = 2 := by
      rw [← hR.2.1]
      exact hR.2.2
    rw [h, h2] at hc
    norm_num at hc

theorem isSolvable_centralizer_dJ_inf
    (hP : Nat.card ↥(fi24P ⊓ Subgroup.centralizer
      ({fi24Psi ⟨dJ, xJ_mem 0⟩} : Set (Equiv.Perm (Fin 378)))) = 5832) :
    Group.IsSolvable ↥(Subgroup.centralizer ({dJ} : Set J) ⊓ fi24C) := by
  haveI := isSolvable_centralizer_fi24C
    (card_fi24QC_inf_centralizer dJC_pow_three card_fi24N_inf_centralizer_dJ) hP
  let f : ↥(Subgroup.centralizer ({(⟨dJ, xJ_mem 0⟩ : ↥fi24C)} : Set ↥fi24C)) →*
      ↥(Subgroup.centralizer ({dJ} : Set J) ⊓ fi24C) :=
    (fi24C.subtype.comp (Subgroup.centralizer _).subtype).codRestrict _ fun x => by
      have hx := mem_centralizer_singleton_subtype_iff.1 x.2
      exact Subgroup.mem_inf.2 ⟨hx, x.1.2⟩
  refine Group.isSolvable_of_surjective (f := f) fun y => ?_
  have hy := Subgroup.mem_inf.1 y.2
  exact ⟨⟨⟨y.1, hy.2⟩, mem_centralizer_singleton_subtype_iff.2 hy.1⟩, rfl⟩

end C

end CFSG.Sporadic.Fi24I301
