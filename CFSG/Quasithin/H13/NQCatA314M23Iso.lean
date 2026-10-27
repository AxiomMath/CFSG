module

public import CFSG.Quasithin.H13.NQCatA314M22Iso
public import Certificates.Certificate7187
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Fischer CFSG.Open CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.Vol2Native.A312L PermLat

theorem closure_le_range_rho4 {b : List (Perm (Fin 16))} (hb : ∀ g ∈ b, g ∈ rho4.range) :
    Subgroup.closure {g | g ∈ b} ≤ rho4.range :=
  (Subgroup.closure_le _).mpr fun g hg => hb g hg

theorem k4_equiv_of_diagExt {n d : ℕ} {a : List (Perm (Fin n))} {b : List (Perm (Fin 16))}
    (hc : diagExtOK (RN.enc : Perm (Fin n) → RN n) (RN.enc : Perm (Fin 16) → RN 16) d a b 960
      960 = true)
    (hb : Subgroup.closure {g | g ∈ b} ≤ rho4.range) :
    Nonempty (↥K4 ≃* ↥(Subgroup.closure {g | g ∈ a})) := by
  obtain ⟨hA, hB, V, hVn, -, -, ⟨e⟩⟩ := exists_ext_of_diagExt (rawIsEnc n) (rawIsEnc 16) hc
  have hV : V = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [Nat.card_congr e.toEquiv, hA, hB] at h
    exact Subgroup.eq_bot_of_card_eq V (by omega)
  let e' : ↥(Subgroup.closure {g | g ∈ a}) ≃* ↥(Subgroup.closure {g | g ∈ b}) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hV.symm)).trans e
  have hR : Subgroup.closure {g | g ∈ b} = rho4.range :=
    Subgroup.eq_of_le_of_card_ge hb (by
      rw [hB, ← Nat.card_congr (MonoidHom.ofInjective rho4_injective).toEquiv, card_K4])
  exact ⟨(MonoidHom.ofInjective rho4_injective).trans ((MulEquiv.subgroupCongr hR.symm).trans
    e'.symm)⟩

@[expose] def k2A : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![0, 1, 1; 1, F4.ω, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    apply f4_ext
    decide⟩

@[expose] def k2B : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![1, 1, 1; F4.ω, ⟨3⟩, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    apply f4_ext
    decide⟩

theorem k2A_mem : k2A ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem k2B_mem : k2B ∈ K4 := ⟨rfl, rfl, rfl⟩

theorem rho4_aslA : M23Asl.aslA = [rho4 ⟨k1M22, k1M22_mem⟩, rho4 ⟨k2A, k2A_mem⟩] := by
  decide

theorem rho4_aslB : M23Asl.aslB = [rho4 ⟨k1M22, k1M22_mem⟩, rho4 ⟨k2B, k2B_mem⟩] := by
  decide

theorem closure_aslA_le : Subgroup.closure {g | g ∈ M23Asl.aslA} ≤ rho4.range := by
  refine closure_le_range_rho4 fun g hg => ?_
  rw [rho4_aslA] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem closure_aslB_le : Subgroup.closure {g | g ∈ M23Asl.aslB} ≤ rho4.range := by
  refine closure_le_range_rho4 fun g hg => ?_
  rw [rho4_aslB] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem m23Asl_facts :
    M23Asl.sgPerms.map M23Asl.tabP = CFSG.Quasithin.H.MathieuLat.m23STabs ∧
      Nat.card (Subgroup.closure {g | g ∈ M23Asl.yaGens}) = 1920 ∧
      Nat.card (Subgroup.closure {g | g ∈ M23Asl.ybGens}) = 1920 ∧
      evalW [CFSG.Sporadic.Schreier.m23PermA, CFSG.Sporadic.Schreier.m23PermB] M23Asl.wb ∉
        Subgroup.closure {g | g ∈ M23Asl.yaGens} ∧
      Subgroup.closure {g | g ∈ M23Asl.aaGens} ≤ Subgroup.closure {g | g ∈ M23Asl.yaGens} ∧
      Subgroup.closure {g | g ∈ M23Asl.abGens} ≤ Subgroup.closure {g | g ∈ M23Asl.ybGens} ∧
      Nonempty (↥K4 ≃* ↥(Subgroup.closure {g | g ∈ M23Asl.aaGens})) ∧
      Nonempty (↥K4 ≃* ↥(Subgroup.closure {g | g ∈ M23Asl.abGens})) := by
  have hc : M23Asl.check = true := Certificates.certificate7187
  simp only [M23Asl.check, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hya⟩, hyas⟩, hyb⟩, hybs⟩, hnot⟩, haa⟩, hab⟩, hda⟩, hdb⟩ := hc
  have hcl : ∀ (gens : List (Perm (Fin 23))) (_ : closedH (gens.map RN.enc)
      (elts (RN.enc : Perm (Fin 23) → RN 23) 32 gens) = true)
      (_ : (elts (RN.enc : Perm (Fin 23) → RN 23) 32 gens).size = 1920),
      Nat.card (Subgroup.closure {g | g ∈ gens}) = 1920 := by
    intro gens h1 h2
    exact (card_closure_of_closedH (rawIsEnc 23) gens 32 h1).trans h2
  have hle : ∀ (gens A : List (Perm (Fin 23))) (_ : closedH (gens.map RN.enc)
      (elts (RN.enc : Perm (Fin 23) → RN 23) 32 gens) = true)
      (_ : ∀ g ∈ A, (elts (RN.enc : Perm (Fin 23) → RN 23) 32 gens).contains (RN.enc g) = true),
      Subgroup.closure {g | g ∈ A} ≤ Subgroup.closure {g | g ∈ gens} := by
    intro gens A h1 h2
    rw [Subgroup.closure_le]
    intro g hg
    exact (mem_closure_iff_H (rawIsEnc 23) gens 32 h1 g).mpr
      (Std.HashSet.contains_iff_mem.mp (h2 g hg))
  refine ⟨hs, hcl _ hya hyas, hcl _ hyb hybs, fun hmem => ?_, hle _ _ hya haa, hle _ _ hyb hab,
    k4_equiv_of_diagExt hda closure_aslA_le, k4_equiv_of_diagExt hdb closure_aslB_le⟩
  have h1 : (elts (RN.enc : Perm (Fin 23) → RN 23) 32 M23Asl.yaGens).contains
      (RN.enc (evalW [CFSG.Sporadic.Schreier.m23PermA, CFSG.Sporadic.Schreier.m23PermB]
        M23Asl.wb)) = true :=
    Std.HashSet.contains_iff_mem.mpr
      ((mem_closure_iff_H (rawIsEnc 23) M23Asl.yaGens 32 hya _).mp hmem)
  rw [h1] at hnot
  exact Bool.false_ne_true hnot.symm

end CFSG.Quasithin.H13.NQCat.A314D
