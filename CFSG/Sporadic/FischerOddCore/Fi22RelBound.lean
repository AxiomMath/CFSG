module

public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public import CFSG.Monster.B.Fischer.Fi22GraphBound
public import CFSG.Monster.B.Fischer.Fi22ModelBase1
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowBase

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer
open scoped Pointwise

@[expose] def fi22AutG : Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {σ | ∀ x y, fi22Graph.Adj x y ↔ fi22Graph.Adj (σ x) (σ y)}
  mul_mem' {σ τ} hσ hτ x y := (hτ x y).trans (hσ (τ x) (τ y))
  one_mem' _ _ := Iff.rfl
  inv_mem' {σ} hσ x y := by
    rw [hσ (σ⁻¹ x) (σ⁻¹ y), perm_apply_inv_self, perm_apply_inv_self]

theorem mem_fi22AutG {σ : Equiv.Perm (Fin 3510)} :
    σ ∈ fi22AutG ↔ ∀ x y, fi22Graph.Adj x y ↔ fi22Graph.Adj (σ x) (σ y) :=
  Iff.rfl

theorem nbrInv_of_mem_fi22AutG
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ fi22AutG) :
    NbrInv fi22Nbr σ := fun x y => by
  rw [fi22Nbr_adj, fi22Nbr_adj]
  exact hσ x y

theorem mem_fi22AutG_of_nbrInv
    {σ : Equiv.Perm (Fin 3510)} (h : NbrInv fi22Nbr σ) :
    σ ∈ fi22AutG := fun x y => by
  rw [← fi22Nbr_adj, ← fi22Nbr_adj]
  exact h x y

@[expose] def fi22K (k : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  fi22AutG ⊓ Subgroup.centralizer {fi22ExtRep k}

theorem fi22K_admissible
    {k : ℕ} {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ fi22K k) :
    NbrInv fi22Nbr σ ∧ σ * fi22ExtRep k = fi22ExtRep k * σ :=
  ⟨nbrInv_of_mem_fi22AutG hσ.1, Subgroup.mem_centralizer_singleton_iff.1 hσ.2⟩

theorem nbrInv_of_img {n : ℕ} {nbr : Array (List ℕ)} {g : Array ℕ} {G : Equiv.Perm (Fin n)}
    (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (hg : Rep n g G)
    (himg : ∀ x < n, nbr[g[x]!]! = imgSorted g nbr[x]!) : NbrInv nbr G := by
  intro x y
  rw [← hg x, himg x x.2, mem_imgSorted]
  constructor
  · intro hy
    exact ⟨y, hy, hg y⟩
  · rintro ⟨p, hp, hpy⟩
    have hpn := (hnbr x).lt p hp
    rw [hg.apply hpn] at hpy
    have : (⟨p, hpn⟩ : Fin n) = y := G.injective (Fin.ext hpy)
    rw [← this]
    exact hp

theorem fi22U_nbrInv :
    NbrInv fi22Nbr fi22U :=
  nbrInv_of_img fi22Nbr_facts.point rep_fi22U fun x hx => by
    simpa using allLt_spec fi22RelBound_check.1 hx

theorem fi22R_le_AutG :
    fi22R ≤ fi22AutG := by
  rw [fi22R, Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact mem_fi22AutG_of_nbrInv fi22U_nbrInv
  · exact mem_fi22AutG_of_nbrInv (fi22Nbr_inv hg)

theorem card_fi22K_le_of_boundsOK
    {c : ℕ} (hc : c < 5) (hc0 : 0 < c)
    (hok : fi22RelBoundOK c = true) :
    Nat.card (fi22K (fi22CentCases.getD c 0)) ≤ (fi22CentRefBounds.getD (c - 1) []).prod := by
  have hk : fi22CentCases.getD c 0 < 6 := by interval_cases c <;> decide
  have hpts : ∀ x ∈ fi22CentRefPoints.getD (c - 1) [], x < 3510 :=
    fi22RelBound_check.2.2.2.2 (c - 1) (by omega)
  exact (card_le_of_boundsOK (K := fi22K (fi22CentCases.getD c 0)) fi22Nbr_facts.point
    (rep_fi22ExtRep hk) (fun σ hσ => fi22K_admissible hσ) (by norm_num) hpts hok).2.2

theorem CTUC_Fi22_involution_relational_graph_bounds :
    fi22R ≤ fi22AutG ∧ Nat.card (fi22K 1) ≤ 106168320 ∧ Nat.card (fi22K 3) ≤ 6635520 ∧
    Nat.card (fi22K 4) ≤ 2090188800 ∧ Nat.card (fi22K 5) ≤ 5806080 ∧
    fi22CentC ∈ fi22R ∧ fi22CentC ∉ fi22P ∧
      fi22CentC * fi22ExtRep 1 = fi22ExtRep 1 * fi22CentC := by
  obtain ⟨-, h1, h2, h3, -⟩ := fi22RelBound_check
  have hrepC : Rep 3510 (fi22CentArr 79) fi22CentC := rep_fi22CentPerm (by norm_num)
  have b1 := card_fi22K_le_of_boundsOK (c := 1) (by norm_num) (by norm_num) fi22RelBound_check1
  have b2 := card_fi22K_le_of_boundsOK (c := 2) (by norm_num) (by norm_num) fi22RelBound_check2
  have b3 := card_fi22K_le_of_boundsOK (c := 3) (by norm_num) (by norm_num) fi22RelBound_check3
  have b4 := card_fi22K_le_of_boundsOK (c := 4) (by norm_num) (by norm_num) fi22RelBound_check4
  rw [show fi22CentCases.getD 1 0 = 1 from rfl,
    show (fi22CentRefBounds.getD (1 - 1) []).prod = 106168320 from rfl] at b1
  rw [show fi22CentCases.getD 2 0 = 3 from rfl,
    show (fi22CentRefBounds.getD (2 - 1) []).prod = 6635520 from rfl] at b2
  rw [show fi22CentCases.getD 3 0 = 4 from rfl,
    show (fi22CentRefBounds.getD (3 - 1) []).prod = 2090188800 from rfl] at b3
  rw [show fi22CentCases.getD 4 0 = 5 from rfl,
    show (fi22CentRefBounds.getD (4 - 1) []).prod = 5806080 from rfl] at b4
  refine ⟨fi22R_le_AutG, b1, b2, b3, b4,
    (mem_fi22R_iff _).2 (Or.inr ((fi22InP_iff (rep_compA rep_fi22U hrepC)).1 h2)),
    fun hm => ?_, eq_of_eqA (rep_compA hrepC (rep_fi22ExtRep (by norm_num)))
      (rep_compA (rep_fi22ExtRep (by norm_num)) hrepC) h3⟩
  rw [(fi22InP_iff hrepC).2 hm] at h1
  exact Bool.noConfusion h1

end CFSG.Sporadic.FischerOddCore
