
module

public import CFSG.Monster.B.Fischer.Fi22GraphBoundBase

public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public import CFSG.Sporadic.FischerOddCore.RefineSpec
public import CFSG.Monster.B.Fischer.Fi22CoverBase1

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

theorem fi22Nbr_facts :
    AdjFacts 3510 fi22OrigArrs fi22Nbr fi22N0List :=
  adjFacts_of_adjOK fi22GraphBound_check.1

theorem fi22Nbr_inv
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ fi22P) : NbrInv fi22Nbr σ :=
  fi22Nbr_facts.inv_of_mem_closure rep_fi22OrigArrs_nat (fi22P_eq_closure_gens ▸ hσ)

theorem mem_fi22N0List
    (i : Fin 3510) : (i : ℕ) ∈ fi22N0List ↔ i ∈ fi22N0 := by
  rw [fi22N0List, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    rep_fi22OuterZ i]
  simp only [fi22N0, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h0, hz⟩
    exact ⟨fun h => h0 (by rw [h]; rfl), Fin.ext hz⟩
  · rintro ⟨h0, hz⟩
    exact ⟨i.2, fun h => h0 (Fin.ext h), by rw [hz]⟩

theorem fi22Nbr_zero (i : Fin 3510) :
    (i : ℕ) ∈ fi22Nbr[((0 : Fin 3510) : ℕ)]! ↔ i ∈ fi22N0 := by
  rw [Fin.val_zero, fi22Nbr_facts.root, mem_fi22N0List]

theorem fi22Nbr_symm
    {x y : Fin 3510} (h : (y : ℕ) ∈ fi22Nbr[(x : ℕ)]!) :
    (x : ℕ) ∈ fi22Nbr[(y : ℕ)]! := by
  obtain ⟨g, hg, hgx⟩ := fi22P_exists_smul x 0
  have hinv := fi22Nbr_inv hg
  have h1 := (hinv x y).1 h
  rw [hgx, Fin.val_zero] at h1
  have h2 := fi22Nbr_facts.root_symm _ h1
  rw [hinv y x, hgx, Fin.val_zero]
  exact h2

theorem fi22Nbr_adj
    (x y : Fin 3510) : (y : ℕ) ∈ fi22Nbr[(x : ℕ)]! ↔ fi22Graph.Adj x y := by
  rw [fi22Graph_adj]
  constructor
  · intro h
    obtain ⟨g, hg, hgx⟩ := fi22P_exists_smul 0 x
    have hinv := fi22Nbr_inv (fi22P.inv_mem hg)
    have h1 := (hinv x y).1 h
    have hx0 : g⁻¹ x = 0 := by rw [← hgx, perm_inv_apply_self]
    rw [hx0, fi22Nbr_zero] at h1
    exact ⟨g, hg, g⁻¹ y, h1, Or.inl ⟨hgx, perm_apply_inv_self g y⟩⟩
  · rintro ⟨g, hg, i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ((fi22Nbr_inv hg) 0 i).1 ((fi22Nbr_zero i).2 hi)
    · exact fi22Nbr_symm (((fi22Nbr_inv hg) 0 i).1 ((fi22Nbr_zero i).2 hi))

theorem nbrInv_of_aut
    (σ : fi22Graph ≃g fi22Graph) : NbrInv fi22Nbr σ.toEquiv := by
  intro x y
  rw [fi22Nbr_adj, fi22Nbr_adj]
  exact σ.map_rel_iff.symm

theorem colMap_of_stab
    {s : ℕ} {σ : fi22Graph ≃g fi22Graph} (hσ : σ ∈ fi22GraphStab s) :
    ColMap 3510 (colourT 3510 fi22Nbr (idA 3510) (fi22GraphBase.take s) 4)
      (colourT 3510 fi22Nbr (idA 3510) (fi22GraphBase.take s) 4) σ.toEquiv := by
  have hpre : ∀ x ∈ fi22GraphBase.take s, x < 3510 :=
    fun x hx => fi22GraphBase_lt (List.mem_of_mem_take hx)
  have h := colourT_map fi22Nbr_facts.point (nbrInv_of_aut σ) rep_idA
    (by rw [mul_one, one_mul]) hpre 4
  have hmap : (fi22GraphBase.take s).map (permNat σ.toEquiv) = fi22GraphBase.take s := by
    conv_rhs => rw [← List.map_id (fi22GraphBase.take s)]
    refine List.map_congr_left fun v hv => ?_
    obtain ⟨j, hj, hjv⟩ := fi22GraphBase_take (v := ⟨v, hpre v hv⟩) hv
    have hfix := mem_fi22GraphStab.1 hσ j hj
    rw [hjv] at hfix
    rw [permNat_lt _ (hpre v hv), id]
    exact congrArg Fin.val hfix
  rwa [hmap] at h

theorem fi22GraphStab_orbit
    {s : ℕ} (hs : s < 6) :
    (MulAction.orbit (fi22GraphStab s) (fi22GraphBasePt s)).ncard ≤
      fi22GraphOrbitBounds.getD s 0 := by
  have hb := fi22GraphBound_check.2
  rw [boundsOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
  have hc := allLt_spec hb.1.2 (by simpa [fi22GraphBase] using hs)
  rw [beq_iff_eq, cellCount_eq] at hc
  rw [← hc]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  rw [← fi22GraphBasePt_val (by omega)]
  exact colMap_of_stab hσ (fi22GraphBasePt s)

theorem fi22GraphStab_six :
    fi22GraphStab 6 = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hc := colMap_of_stab hσ
  have hb := fi22GraphBound_check.2
  rw [boundsOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
  have ht : fi22GraphBase.take 6 = fi22GraphBase := rfl
  rw [ht] at hc
  exact RelIso.ext fun v => colInj_injective hb.2 (hc v)

theorem CTUC_Fi22_graph_automorphism_order_bound :
    Nat.card (fi22Graph ≃g fi22Graph) ≤ 129123503308800 ∧
    (∀ s < 6, (MulAction.orbit (fi22GraphStab s) (fi22GraphBasePt s)).ncard ≤
      fi22GraphOrbitBounds.getD s 0) ∧
    fi22GraphStab 6 = ⊥ ∧
    (∀ (s : ℕ) (σ : fi22Graph ≃g fi22Graph),
      σ ∈ fi22GraphStab s ↔ ∀ j < s, σ (fi22GraphBasePt j) = fi22GraphBasePt j) := by
  refine ⟨?_, fun s hs => fi22GraphStab_orbit hs, fi22GraphStab_six,
    fun s σ => mem_fi22GraphStab⟩
  have h := card_le_prod_of_stabChain (G := fi22Graph ≃g fi22Graph) fi22GraphBasePt
    (fun s => fi22GraphOrbitBounds.getD s 0) 6 (fun s hs => fi22GraphStab_orbit hs)
    fi22GraphStab_six
  refine h.trans (le_of_eq ?_)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  rfl

end CFSG.Monster.B.Fischer
