module

public import CFSG.LocalAnalysis.StandardType.GGP3LineGlue
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitness

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggLWlinedata (XL : List (List ℤ)) (n : ℕ) (R : List (List ℤ)) (ψ₀ : List ℕ) (k₀ : ℕ)
    (ψγ : List ℕ) (kγ : ℕ) (j : ℕ) : Bool :=
  let N := n + 1
  let g₀ := ggLWword XL ψ₀ (ggLWunit N k₀)
  let c₀ := ggLWwordR XL ψ₀ (ggLWunit N k₀)
  let g := ggLWword XL ψγ (ggLWunit N kγ)
  let cγ := ggLWwordR XL ψγ (ggLWunit N kγ)
  let s := c₀.getD n 0 + cγ.getD n 0
  let a₀ := c₀.getD n 0
  let w := List.zipWith (fun x y => (s - a₀) * x - a₀ * y) g₀ g
  let c := List.zipWith (fun x y => (s - a₀) * x - a₀ * y) c₀ cγ
  let ρ := ggLWunit N j
  let m := ggLWdot c (XL.map fun row => ggLWdot row ρ)
  let U := List.zipWith (fun r x => s * s * r - m * x) ρ w
  decide (j < n) && R.all fun v => decide ((12 : ℕ) % ggLWminors U (v ++ [0]) = 0)

private theorem lwl_hX_symm {Λ Λ' : Type} (e : Λ ≃ Λ')
    {X : Matrix (Option Λ) (Option Λ) ℤ} {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j) :
    ∀ i j, X (Option.map e.symm i) (Option.map e.symm j) = X' i j := by
  intro i j
  have h := hX (Option.map e.symm i) (Option.map e.symm j)
  rw [show Option.map e (Option.map e.symm i) = i from by simp,
    show Option.map e (Option.map e.symm j) = j from by simp] at h
  exact h.symm

private theorem lwl_pair_comp {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']
    (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j)
    (c : Option Λ → ℤ) (ρ : Option Λ → ℤ) :
    (∑ i' : Option Λ', c ((Equiv.optionCongr e).symm i') *
        ∑ j' : Option Λ', X' i' j' * ρ ((Equiv.optionCongr e).symm j'))
      = ∑ i : Option Λ, c i * ∑ j : Option Λ, X i j * ρ j := by
  rw [← Equiv.sum_comp (Equiv.optionCongr e)
    (fun i' : Option Λ' => c ((Equiv.optionCongr e).symm i') *
      ∑ j' : Option Λ', X' i' j' * ρ ((Equiv.optionCongr e).symm j'))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Equiv.symm_apply_apply]
  congr 1
  rw [← Equiv.sum_comp (Equiv.optionCongr e)
    (fun j' : Option Λ' =>
      X' (Equiv.optionCongr e i) j' * ρ ((Equiv.optionCongr e).symm j'))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Equiv.symm_apply_apply, Equiv.optionCongr_apply, Equiv.optionCongr_apply, hX i j]

theorem ggLineTest_of_equiv {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] (e : Λ ≃ Λ') {X : Matrix (Option Λ) (Option Λ) ℤ}
    {X' : Matrix (Option Λ') (Option Λ') ℤ}
    (hX : ∀ i j, X' (Option.map e i) (Option.map e j) = X i j) {p : ℕ}
    (h : GGLineTest X p) : GGLineTest X' p := by
  obtain ⟨ψ, k, ρ, hρ, ha, hnp⟩ := h
  have hX' := lwl_hX_symm e hX
  refine ⟨ψ.map (Option.map e), Option.map e k, ρ ∘ (Equiv.optionCongr e).symm, ?_, ?_, ?_⟩
  · have h := lw_coroots_mem e.symm hX' hρ
    simpa only [Equiv.optionCongr_symm] using h
  · have hword := lw_sWordR_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← lw_single_comp' e k] at hword
    have hnone := congrFun hword none
    simp only [Function.comp_apply] at hnone
    have hφnone : (Equiv.optionCongr e).symm none = none := rfl
    rw [hφnone] at hnone
    rw [hnone, ha]
  · intro v' hv' r hcon
    refine hnp (v' ∘ (Equiv.optionCongr e)) (lw_coroots_mem e hX hv') r ?_
    have hword := lw_sWord_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← lw_single_comp' e k] at hword
    have hwordR := lw_sWordR_comp e hX ψ (Pi.single k (1 : ℤ))
    rw [← lw_single_comp' e k] at hwordR
    have hp := lwl_pair_comp e hX (ggSWordR X ψ (Pi.single k (1 : ℤ))) ρ
    funext i
    have h1 := congrFun hcon ((Equiv.optionCongr e) i)
    simp only [Function.comp_apply] at h1 ⊢
    rw [← h1]
    have hρi : (ρ ((Equiv.optionCongr e).symm ((Equiv.optionCongr e) i)) : ZMod p)
        = (ρ i : ZMod p) := by
      rw [Equiv.symm_apply_apply]
    have hwi : (ggSWord X' (ψ.map (Option.map e)) (Pi.single (Option.map e k) (1 : ℤ))
          ((Equiv.optionCongr e) i) : ZMod p)
        = (ggSWord X ψ (Pi.single k (1 : ℤ)) i : ZMod p) := by
      rw [hword]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have hE : (∑ i' : Option Λ', ggSWordR X' (ψ.map (Option.map e))
            (Pi.single (Option.map e k) (1 : ℤ)) i' *
            ∑ j : Option Λ', X' i' j * ρ ((Equiv.optionCongr e).symm j))
        = ∑ i' : Option Λ, ggSWordR X ψ (Pi.single k (1 : ℤ)) i' *
            ∑ j : Option Λ, X i' j * ρ j := by
      rw [hwordR]
      simpa only [Function.comp_apply] using hp
    rw [hρi, hwi, hE]

theorem ggLineTest_of_data {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n)
    (hC : ∀ j, C j j = 2) (R : List (List ℤ)) (ψ₀ : List ℕ) (k₀ : ℕ) (ψγ : List ℕ) (kγ : ℕ)
    (j : ℕ) (hclosed : ggLWclosed (ggLWmatC C) n R = true)
    (hdata : ggLWdata (ggLWmat (ggAttachCartan C k)) n R ψ₀ k₀ ψγ kγ = true)
    (hline : ggLWlinedata (ggLWmat (ggAttachCartan C k)) n R ψ₀ k₀ ψγ kγ j = true)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLineTest (ggAttachCartan C k) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set XL : List (List ℤ) := ggLWmat (ggAttachCartan C k) with hXL
  have hd := hdata
  simp only [ggLWdata, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
  set g₀ : List ℤ := ggLWword XL ψ₀ (ggLWunit (n + 1) k₀) with hg₀
  set c₀ : List ℤ := ggLWwordR XL ψ₀ (ggLWunit (n + 1) k₀) with hc₀
  set g : List ℤ := ggLWword XL ψγ (ggLWunit (n + 1) kγ) with hg
  set cγ : List ℤ := ggLWwordR XL ψγ (ggLWunit (n + 1) kγ) with hcγ
  set s : ℤ := c₀.getD n 0 + cγ.getD n 0 with hs
  set a₀ : ℤ := c₀.getD n 0 with ha₀
  set w : List ℤ := List.zipWith (fun x y => (s - a₀) * x - a₀ * y) g₀ g with hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hψ0, hψγ⟩, hk0⟩, hkγ⟩, hp1⟩, hp2⟩, hs0⟩, h12⟩, hmin⟩ := hd
  have hl := hline
  simp only [ggLWlinedata, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hl
  obtain ⟨hjn, hlinemin⟩ := hl
  set ρl : List ℤ := ggLWunit (n + 1) j with hρl
  set cl : List ℤ := List.zipWith (fun x y => (s - a₀) * x - a₀ * y) c₀ cγ with hcl
  set ml : ℤ := ggLWdot cl (XL.map fun row => ggLWdot row ρl) with hml
  set Ul : List ℤ := List.zipWith (fun r x => s * s * r - ml * x) ρl w with hUl
  have hlen0 : (ggLWunit (n + 1) k₀).length = n + 1 := by
    simp only [ggLWunit, List.length_map, List.length_range]
  have hlenγ : (ggLWunit (n + 1) kγ).length = n + 1 := by
    simp only [ggLWunit, List.length_map, List.length_range]
  have hg0len : g₀.length = n + 1 := by rw [hg₀, lw_word_length, hlen0]
  have hglen : g.length = n + 1 := by rw [hg, lw_word_length, hlenγ]
  have hc0len : c₀.length = n + 1 := by rw [hc₀, lw_wordR_length, hlen0]
  have hcγlen : cγ.length = n + 1 := by rw [hcγ, lw_wordR_length, hlenγ]
  have hwlen : w.length = n + 1 := by rw [hw, List.length_zipWith, hg0len, hglen, min_self]
  have hρllen : ρl.length = n + 1 := by
    rw [hρl]
    simp only [ggLWunit, List.length_map, List.length_range]
  have hcllen : cl.length = n + 1 := by
    rw [hcl, List.length_zipWith, hc0len, hcγlen, min_self]
  have hUlen : Ul.length = n + 1 := by
    rw [hUl, List.length_zipWith, hρllen, hwlen, min_self]
  have hXdiag : ∀ o : Option (Fin n), ggAttachCartan C k o o = 2 := by
    intro o
    rcases o with _ | i
    · exact ggAttachCartan_none_none C k
    · exact hC i
  have hg0 : ggSWord (ggAttachCartan C k) (ψ₀.map (ggLWnode n)) (Pi.single (ggLWnode n k₀) 1)
      = lw_vecOf g₀ := by
    rw [← lw_unit_bridge k₀ hk0]
    have h := lw_sWord_bridge (ggAttachCartan C k) ψ₀ hψ0 (ggLWunit (n + 1) k₀) hlen0
    rwa [← hXL, ← hg₀] at h
  have hgγ : ggSWord (ggAttachCartan C k) (ψγ.map (ggLWnode n)) (Pi.single (ggLWnode n kγ) 1)
      = lw_vecOf g := by
    rw [← lw_unit_bridge kγ hkγ]
    have h := lw_sWord_bridge (ggAttachCartan C k) ψγ hψγ (ggLWunit (n + 1) kγ) hlenγ
    rwa [← hXL, ← hg] at h
  have hc0 : ggSWordR (ggAttachCartan C k) (ψ₀.map (ggLWnode n)) (Pi.single (ggLWnode n k₀) 1)
      = lw_vecOf c₀ := by
    rw [← lw_unit_bridge k₀ hk0]
    have h := lw_sWordR_bridge (ggAttachCartan C k) ψ₀ hψ0 (ggLWunit (n + 1) k₀) hlen0
    rwa [← hXL, ← hc₀] at h
  have hcγ : ggSWordR (ggAttachCartan C k) (ψγ.map (ggLWnode n)) (Pi.single (ggLWnode n kγ) 1)
      = lw_vecOf cγ := by
    rw [← lw_unit_bridge kγ hkγ]
    have h := lw_sWordR_bridge (ggAttachCartan C k) ψγ hψγ (ggLWunit (n + 1) kγ) hlenγ
    rwa [← hXL, ← hcγ] at h
  have hP1 : (∑ i, ∑ j', ggSWordR (ggAttachCartan C k) (ψ₀.map (ggLWnode n))
        (Pi.single (ggLWnode n k₀) 1) i * ggAttachCartan C k i j'
        * ggSWord (ggAttachCartan C k) (ψγ.map (ggLWnode n))
          (Pi.single (ggLWnode n kγ) 1) j') = -2 := by
    rw [hc0, hgγ, lw_pair_bridge (ggAttachCartan C k) c₀ g hc0len hglen, ← hXL]
    exact hp1
  have hP2 : (∑ i, ∑ j', ggSWordR (ggAttachCartan C k) (ψγ.map (ggLWnode n))
        (Pi.single (ggLWnode n kγ) 1) i * ggAttachCartan C k i j'
        * ggSWord (ggAttachCartan C k) (ψ₀.map (ggLWnode n))
          (Pi.single (ggLWnode n k₀) 1) j') = -2 := by
    rw [hcγ, hg0, lw_pair_bridge (ggAttachCartan C k) cγ g₀ hcγlen hg0len, ← hXL]
    exact hp2
  have h2s_ne : ((2 * s : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hdvd : (p : ℤ) ∣ 2 * s := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * s) p).mp h
    have hdiv12 : (2 * s : ℤ) ∣ 12 := Int.dvd_of_emod_eq_zero h12
    have hp12 : (p : ℤ) ∣ 12 := dvd_trans hdvd hdiv12
    have hp12' : p ∣ 12 := by exact_mod_cast hp12
    exact lw_prime_not_dvd_12 hp h5 hp12'
  let m : ℕ := ((a₀ : ZMod p) * ((2 * s : ℤ) : ZMod p)⁻¹).val
  have hm : ((m : ℕ) : ZMod p) = (a₀ : ZMod p) * ((2 * s : ℤ) : ZMod p)⁻¹ :=
    ZMod.natCast_zmod_val _
  have h2ms : (2 : ZMod p) * (m : ZMod p) * (s : ZMod p) = (a₀ : ZMod p) := by
    rw [hm]
    field_simp [h2s_ne]
    push_cast
    ring
  let T : List (Option (Fin n)) :=
    ψγ.map (ggLWnode n) ++ [ggLWnode n kγ] ++ (ψγ.map (ggLWnode n)).reverse ++
      ψ₀.map (ggLWnode n) ++ [ggLWnode n k₀] ++ (ψ₀.map (ggLWnode n)).reverse
  let ψw : List (Option (Fin n)) := (List.replicate m T).flatten ++ ψ₀.map (ggLWnode n)
  obtain ⟨hword, hwordR⟩ := ggAffinePair_word_gen (ggAttachCartan C k) hXdiag
    (ggLWnode n k₀) (ggLWnode n kγ) (ψ₀.map (ggLWnode n)) (ψγ.map (ggLWnode n)) hP1 hP2 m
  have hw_point : ∀ i : Option (Fin n),
      lw_vecOf w i = (s - a₀) * lw_vecOf g₀ i - a₀ * lw_vecOf g i := by
    intro i
    rcases i with _ | a
    · rw [lw_node_none w, lw_node_none g₀, lw_node_none g, hw]
      exact lw_w_point g₀ g _ s a₀ rfl hg0len hglen (le_refl n)
    · rw [lw_node_some w a, lw_node_some g₀ a, lw_node_some g a, hw]
      exact lw_w_point g₀ g _ s a₀ rfl hg0len hglen (le_of_lt a.2)
  have hcl_point : ∀ i : Option (Fin n),
      lw_vecOf cl i = (s - a₀) * lw_vecOf c₀ i - a₀ * lw_vecOf cγ i := by
    intro i
    rcases i with _ | a
    · rw [lw_node_none cl, lw_node_none c₀, lw_node_none cγ, hcl]
      exact lw_w_point c₀ cγ _ s a₀ rfl hc0len hcγlen (le_refl n)
    · rw [lw_node_some cl a, lw_node_some c₀ a, lw_node_some cγ a, hcl]
      exact lw_w_point c₀ cγ _ s a₀ rfl hc0len hcγlen (le_of_lt a.2)
  have hcor : ggSWord (ggAttachCartan C k) ψw (Pi.single (ggLWnode n k₀) 1)
      = lw_vecOf g₀ - (2 * (m : ℤ)) • (lw_vecOf g₀ + lw_vecOf g) := by
    rw [hword, hg0, hgγ]
  have hcorR : ggSWordR (ggAttachCartan C k) ψw (Pi.single (ggLWnode n k₀) 1)
      = lw_vecOf c₀ - (2 * (m : ℤ)) • (lw_vecOf c₀ + lw_vecOf cγ) := by
    rw [hwordR, hc0, hcγ]
  have hs_cor : ∀ i : Option (Fin n),
      (s : ZMod p) * ((ggSWordR (ggAttachCartan C k) ψw
        (Pi.single (ggLWnode n k₀) 1) i : ℤ) : ZMod p)
        = ((lw_vecOf cl i : ℤ) : ZMod p) := by
    intro i
    rw [hcorR, hcl_point i]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    exact lw_h2ms_identity h2ms _ _
  have hs_w : ∀ i : Option (Fin n),
      (s : ZMod p) * ((ggSWord (ggAttachCartan C k) ψw
        (Pi.single (ggLWnode n k₀) 1) i : ℤ) : ZMod p)
        = ((lw_vecOf w i : ℤ) : ZMod p) := by
    intro i
    rw [hcor, hw_point i]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    exact lw_h2ms_identity h2ms _ _
  have hpair : (s : ZMod p) *
      (((∑ i : Option (Fin n),
          ggSWordR (ggAttachCartan C k) ψw (Pi.single (ggLWnode n k₀) 1) i *
            ∑ j' : Option (Fin n),
              ggAttachCartan C k i j' * lw_vecOf ρl j') : ℤ) : ZMod p)
      = (ml : ZMod p) := by
    rw [hml, hXL, ← lw_pair_bridge (ggAttachCartan C k) cl ρl hcllen hρllen]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_assoc, ← hs_cor i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    ring
  have hs_ne : (s : ZMod p) ≠ 0 := by
    intro h
    apply h2s_ne
    push_cast
    rw [h]
    ring
  have ha_zero : ((ggSWordR (ggAttachCartan C k) ψw
      (Pi.single (ggLWnode n k₀) 1) none : ℤ) : ZMod p) = 0 := by
    have h1 := hs_cor (none : Option (Fin n))
    have hcl_none : lw_vecOf cl (none : Option (Fin n)) = 0 := by
      rw [lw_node_none (n := n) cl, hcl,
        lw_w_point c₀ cγ _ s a₀ rfl hc0len hcγlen (le_refl n), hs, ha₀]
      ring
    rw [hcl_none, Int.cast_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hs_ne
  refine ⟨ψw, ggLWnode n k₀, lw_vecOf ρl, ?_, ha_zero, ?_⟩
  · refine ⟨[], ⟨j, hjn⟩, ?_⟩
    rw [hρl, lw_unit_bridge j (le_of_lt hjn),
      show ggLWnode n j = some ⟨j, hjn⟩ from dif_pos hjn]
    rfl
  · intro v hv r hcon
    obtain ⟨l, hlR, hll, hleq⟩ := lw_mem_R C k R hclosed v hv
    set root : Option (Fin n) → ℤ :=
      ggSWordR (ggAttachCartan C k) ψw (Pi.single (ggLWnode n k₀) 1) with hroot
    set wvf : Option (Fin n) → ℤ :=
      ggSWord (ggAttachCartan C k) ψw (Pi.single (ggLWnode n k₀) 1) with hwvf
    set Pz : ZMod p := (((∑ i' : Option (Fin n), root i' *
        ∑ j' : Option (Fin n), ggAttachCartan C k i' j' * lw_vecOf ρl j') : ℤ) : ZMod p) with hPz
    have hpair' : (s : ZMod p) * Pz = (ml : ZMod p) := by
      rw [hPz, hroot]
      exact hpair
    have hcon' : (fun i : Option (Fin n) => (lw_vecOf ρl i : ZMod p)
          - Pz * (wvf i : ZMod p)) = fun i => (r : ZMod p) * (v i : ZMod p) := hcon
    have hvec : ∀ a ≤ n, ((lw_vecOf ρl (ggLWnode n a) : ZMod p)
          - Pz * (wvf (ggLWnode n a) : ZMod p))
        = (r : ZMod p) * (((l ++ [0]).getD a 0 : ℤ) : ZMod p) := by
      intro a ha
      have h := congrFun hcon' (ggLWnode n a)
      rw [hleq] at h
      simpa only [lw_node (l ++ [0]) ha] using h
    have hpoint : ∀ a ≤ n, ((Ul.getD a 0 : ℤ) : ZMod p)
        = ((s : ZMod p) * (s : ZMod p) * (r : ZMod p)) *
            (((l ++ [0]).getD a 0 : ℤ) : ZMod p) := by
      intro a ha
      have hUl_a : ((Ul.getD a 0 : ℤ) : ZMod p)
          = (s : ZMod p) * (s : ZMod p) * ((ρl.getD a 0 : ℤ) : ZMod p)
            - (ml : ZMod p) * ((w.getD a 0 : ℤ) : ZMod p) := by
        rw [hUl, lw_zipWith_getD_of_lt (fun r x => s * s * r - ml * x) ρl w
          (by rw [hρllen]; omega) (by rw [hwlen]; omega)]
        push_cast
        ring
      have hkey_node : (s : ZMod p) * (s : ZMod p)
            * (lw_vecOf ρl (ggLWnode n a) : ZMod p)
            - (ml : ZMod p) * (lw_vecOf w (ggLWnode n a) : ZMod p)
          = ((s : ZMod p) * (s : ZMod p) * (r : ZMod p)) *
              (((l ++ [0]).getD a 0 : ℤ) : ZMod p) := by
        have hsw := hs_w (ggLWnode n a)
        have hva := hvec a ha
        have hstep : (s : ZMod p) * (s : ZMod p)
              * (lw_vecOf ρl (ggLWnode n a) : ZMod p)
              - (ml : ZMod p) * (lw_vecOf w (ggLWnode n a) : ZMod p)
            = (s : ZMod p) * (s : ZMod p)
              * ((lw_vecOf ρl (ggLWnode n a) : ZMod p)
                - Pz * (wvf (ggLWnode n a) : ZMod p)) := by
          rw [← hpair', ← hsw]
          ring
        rw [hstep, hva]
        ring
      have hkey := hkey_node
      rw [lw_node ρl ha, lw_node w ha] at hkey
      rw [hUl_a]
      exact hkey
    have hmin_dvd : p ∣ ggLWminors Ul (l ++ [0]) := by
      apply lw_minors_dvd_of_minors
      intro i j' hi hj hij
      have hi' : i ≤ n := by rw [hUlen] at hi; omega
      have hj' : j' ≤ n := by rw [hUlen] at hj; omega
      have hUi := hpoint i hi'
      have hUj := hpoint j' hj'
      have hzero : (((Ul.getD i 0 * (l ++ [0]).getD j' 0
          - Ul.getD j' 0 * (l ++ [0]).getD i 0 : ℤ)) : ZMod p) = 0 := by
        rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, hUi, hUj]
        ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero
    have h12' : ggLWminors Ul (l ++ [0]) ∣ 12 :=
      Nat.dvd_iff_mod_eq_zero.mpr (hlinemin l hlR)
    exact lw_prime_not_dvd_12 hp h5 (dvd_trans hmin_dvd h12')
