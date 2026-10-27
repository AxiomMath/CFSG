module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.HPsi
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SigmaCheck
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaMain

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
open CFSG.Quasithin.J2Cz

theorem evalWord_tl_eq {X : Type*} [Group X] (t : Fin 7 → X) (r : List (Fin 7 × Bool)) :
    ThreeLocal.evalWord t r = evalWord t r := by
  unfold ThreeLocal.evalWord evalWord
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;> rfl

theorem evalWord_update_of_not_mem {X : Type*} [Group X] (t : Fin 7 → X) (β : X)
    {r : List (Fin 7 × Bool)} (hr : ∀ x ∈ r, x.1 ≠ 6) :
    evalWord (Function.update t 6 β) r = evalWord t r := by
  rw [← evalWord_tl_eq, ← evalWord_tl_eq]
  exact ThreeLocal.evalWord_congr fun x hx => Function.update_of_ne (hr x hx) _ _

theorem evalWord_map_hom {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (t : Fin 7 → X)
    (r : List (Fin 7 × Bool)) : evalWord (fun i => f (t i)) r = f (evalWord t r) := by
  unfold evalWord
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;> simp

theorem j3WordsRest_cases : ∀ r ∈ j3WordsRest, r ∈ relsH ∨ r ∈ relsA2 ∨ r ∈ mixedRels := by
  decide

theorem d8Rels_sub : ∀ r ∈ ThreeLocal.d8Rels, r ∈ relsH := by
  decide

theorem relsH_letters : ∀ r ∈ relsH, ∀ x ∈ r, x.1 ≠ 6 := by
  decide

theorem relsA2_eq : relsA2 = ThreeLocal.a2Rels := rfl

theorem modelTuple_two_ne_one : modelTuple 2 ≠ 1 := by
  intro h
  have h1 : (modelTuple 2).left = (1 : Model).left := by rw [h]
  revert h1
  decide +kernel

theorem mem_relsA2_r20 : [((6 : Fin 7), false), (6, false), (0, false), (2, true)] ∈ relsA2 := by
  decide

theorem mem_relsA2_r21 :
    [((6 : Fin 7), false), (3, true), (6, false), (3, true), (0, false)] ∈ relsA2 := by
  decide

theorem IsTypeH2.exists_letters
    {G : Type} [Group G] [Finite G] {z : G} (h : IsTypeH2 G z)
    (hone : involutionClassCount G = 1) :
    ∃ e : Fin 7 → G, (∀ r ∈ j3WordsRest, FreeGroup.lift e (FreeGroup.mk r) = 1) ∧
      Subgroup.closure (e '' {i : Fin 7 | i.val ≠ 6}) = Subgroup.centralizer ({z} : Set G) ∧
      e 3 = z ∧ e 6 ∉ Subgroup.centralizer ({z} : Set G) ∧
      e 0 ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf (e 0) = 3 := by
  obtain ⟨ψ, hψinj, hψrange, hψmem, hψz⟩ := exists_H_psi h
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set e₀ : Fin 7 → G := fun i => ψ (modelTuple7 i) with he₀
  have hH : ∀ r ∈ relsH, evalWord e₀ r = 1 := by
    intro r hr
    rw [he₀, evalWord_map_hom, eq_one_of_check (modelTuple_relsH r hr), map_one]
  have hD8 : ∀ r ∈ ThreeLocal.d8Rels, ThreeLocal.evalWord e₀ r = 1 := fun r hr => by
    rw [evalWord_tl_eq]; exact hH r (d8Rels_sub r hr)
  have h0 : e₀ 0 = ψ (modelTuple 0) := rfl
  have h3 : e₀ 3 = z := hψz
  have hy : e₀ 0 ∈ C := hψmem _
  have hy3 : orderOf (e₀ 0) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [h0]
    apply orderOf_eq_prime
    · rw [← map_pow, pow_three, ← mul_assoc, modelTuple_zero_cube, map_one]
    · intro h1
      exact modelTuple_zero_ne_one (hψinj (h1.trans (map_one ψ).symm))
  have hz1 : e₀ 3 ≠ 1 := by rw [h3]; exact h.ne_one
  obtain ⟨β, -, hβ⟩ := CFSG.Quasithin.IsTypeH2.exists_beta_of_quotient h hone hD8 hy hy3 hz1
  have hβ' : ∀ r ∈ relsA2, evalWord (Function.update e₀ 6 β) r = 1 := fun r hr => by
    rw [← evalWord_tl_eq]; exact hβ r (relsA2_eq ▸ hr)
  have hmixed := mixed_rels_of_beta ψ hψinj e₀ (fun i _ => rfl)
    (fun g hg => hψrange g (by rw [h3] at hg; exact hg)) β hβ'
  set e := Function.update e₀ 6 β with he
  have hei : ∀ i : Fin 7, i ≠ 6 → e i = e₀ i := fun i hi => Function.update_of_ne hi _ _
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [lift_mk_eq_evalWord]
    rcases j3WordsRest_cases r hr with h1 | h1 | h1
    · rw [evalWord_update_of_not_mem e₀ β (relsH_letters r h1)]
      exact hH r h1
    · exact hβ' r h1
    · exact hmixed r h1
  ·
    have himg : e '' {i : Fin 7 | i.val ≠ 6} = ψ '' Set.range modelTuple := by
      ext g
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi6 : i.val < 6 := by have := i.2; simp only [Set.mem_ofPred_eq] at hi; omega
        refine ⟨modelTuple ⟨i.val, hi6⟩, ⟨_, rfl⟩, ?_⟩
        rw [hei i (fun h6 => hi (by rw [h6]; rfl))]
        simp [he₀, modelTuple7, hi6]
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        refine ⟨⟨k.val, by omega⟩, by simp only [Set.mem_ofPred_eq]; omega, ?_⟩
        rw [hei _ (fun h6 => by have := congrArg Fin.val h6; simp at this; omega)]
        simp [he₀, modelTuple7, k.2]
    rw [himg, ← MonoidHom.map_closure, closure_modelTuple, ← MonoidHom.range_eq_map]
    ext g
    exact ⟨fun ⟨m, hm⟩ => hm ▸ hψmem m, hψrange g⟩
  · rw [hei 3 (by decide)]
    exact h3
  ·
    intro hβC
    have hβC' : β * z = z * β := Subgroup.mem_centralizer_singleton_iff.mp
      (by rw [he, Function.update_self] at hβC; exact hβC)
    have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq
    have r20 := hβ' _ mem_relsA2_r20
    have r21 := hβ' _ mem_relsA2_r21
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.cond_true,
      Bool.cond_false, mul_one] at r20 r21
    have e6 : e 6 = β := Function.update_self _ _ _
    rw [e6, hei 0 (by decide), hei 2 (by decide)] at r20
    rw [e6, hei 0 (by decide), hei 3 (by decide), h3] at r21
    replace r20 : β⁻¹ * β⁻¹ * (e₀ 0)⁻¹ * e₀ 2 = 1 := by simpa only [mul_assoc] using r20
    replace r21 : β⁻¹ * z * β⁻¹ * z * (e₀ 0)⁻¹ = 1 := by simpa only [mul_assoc] using r21
    have hbinv : β⁻¹ * z = z * β⁻¹ := by
      calc β⁻¹ * z = β⁻¹ * (z * β) * β⁻¹ := by group
        _ = β⁻¹ * (β * z) * β⁻¹ := by rw [hβC']
        _ = z * β⁻¹ := by group
    have hb2 : β⁻¹ * β⁻¹ = e₀ 0 := by
      have : β⁻¹ * z * β⁻¹ * z * (e₀ 0)⁻¹ = β⁻¹ * β⁻¹ * (e₀ 0)⁻¹ := by
        calc β⁻¹ * z * β⁻¹ * z * (e₀ 0)⁻¹ = β⁻¹ * (z * β⁻¹) * z * (e₀ 0)⁻¹ := by group
          _ = β⁻¹ * (β⁻¹ * z) * z * (e₀ 0)⁻¹ := by rw [hbinv]
          _ = β⁻¹ * β⁻¹ * (z * z) * (e₀ 0)⁻¹ := by group
          _ = β⁻¹ * β⁻¹ * (e₀ 0)⁻¹ := by rw [hzz, mul_one]
      rw [this] at r21
      calc β⁻¹ * β⁻¹ = β⁻¹ * β⁻¹ * (e₀ 0)⁻¹ * e₀ 0 := by group
        _ = e₀ 0 := by rw [r21, one_mul]
    have hx : e₀ 2 = 1 := by
      calc e₀ 2 = (β⁻¹ * β⁻¹ * (e₀ 0)⁻¹)⁻¹ * (β⁻¹ * β⁻¹ * (e₀ 0)⁻¹ * e₀ 2) := by group
        _ = (β⁻¹ * β⁻¹ * (e₀ 0)⁻¹)⁻¹ := by rw [r20, mul_one]
        _ = 1 := by rw [hb2, mul_inv_cancel, inv_one]
    exact modelTuple_two_ne_one (hψinj (hx.trans (map_one ψ).symm))
  · rw [hei 0 (by decide)]
    exact hy
  · rw [hei 0 (by decide)]
    exact hy3

end CFSG.Quasithin.Kleidman
