module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 11.3

This file contains the Section 11 Theorem 11.3 statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_conjBy_le_centralizer_self
    {A0 A : Subgroup G} (hA0A : A0 ≤ A) [IsMulCommutative A] (g : G) :
    A0.conjBy g ≤ Subgroup.centralizer (A0.conjBy g : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, hx_eq⟩
  rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, hy_eq⟩
  have hxA : x0 ∈ A := hA0A hx0
  have hyA : y0 ∈ A := hA0A hy0
  have hcomm : x0 * y0 = y0 * x0 := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := A)).comm ⟨x0, hxA⟩ ⟨y0, hyA⟩)
  calc
    y * x = g * (y0 * x0) * g⁻¹ := by
      rw [← hx_eq, ← hy_eq]
      simp [MulAut.conj_apply]
    _ = g * (x0 * y0) * g⁻¹ := by rw [← hcomm]
    _ = x * y := by
      rw [← hx_eq, ← hy_eq]
      simp [MulAut.conj_apply]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section11_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
    {H R : Subgroup G} (hRnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hinf : H ⊓ R = ⊥) :
    (H.subgroupOf (R ⊔ H)).IsComplement' (R.subgroupOf (R ⊔ H)) := by
  let S : Subgroup G := R ⊔ H
  let Hs : Subgroup S := H.subgroupOf S
  let Rs : Subgroup S := R.subgroupOf S
  haveI : Hs.Normal := by
    simpa [S, Hs] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := R) (N := H) hRnorm)
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    apply Subtype.ext
    have hxinf : ((x : S) : G) ∈ H ⊓ R := ⟨hxH, hxR⟩
    have hxbot : ((x : S) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hinf] using hxinf
    simpa using hxbot
  · rw [Set.eq_univ_iff_forall]
    intro x
    have htop : Hs ⊔ Rs = ⊤ := by
      calc
        Hs ⊔ Rs = (H ⊔ R).subgroupOf S := by
          symm
          simpa [S, Hs, Rs] using
            (Subgroup.subgroupOf_sup (A := H) (A' := R) (B := S)
              le_sup_right le_sup_left)
        _ = ⊤ := by
          exact Subgroup.subgroupOf_eq_top.mpr (by simp [S, sup_comm])
    have hx_top : x ∈ Hs ⊔ Rs := by simp [htop]
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := Hs) (t := Rs)).1 hx_top with
      ⟨h, hhH, r, hrR, hmul⟩
    exact ⟨h, hhH, r, hrR, hmul⟩

omit [IsMinCE G] in
public theorem CFSG.section11_obtain_g_and_A_le_Mg
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    ∃ g : G, g ∈ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ∧
      g ∉ M ∧ A ≤ M.conjBy g := by
  have hPamb_le_M : section10AmbientSylowSubgroup M P ≤ M :=
    section11_ambientSylow_le M P
  obtain ⟨g, hgN, hgM⟩ :
      ∃ g : G, g ∈ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ∧ g ∉ M := by
    by_contra h
    apply h11.not_normalizer_ambient_sylow_le
    intro x hxN
    by_contra hxM
    exact h ⟨x, hxN, hxM⟩
  have hA_conj_inv_le_Pamb : A.conjBy g⁻¹ ≤ section10AmbientSylowSubgroup M P := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem (Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G)) hgN) a).1
        (h11.A_le_ambient_sylow haA)
  have hA_conj_inv_le_M : A.conjBy g⁻¹ ≤ M :=
    hA_conj_inv_le_Pamb.trans hPamb_le_M
  have hA_le_Mg : A ≤ M.conjBy g := by
    simpa using
      (section11_le_conjBy_inv_of_conjBy_le
        (G := G) (H := A) (K := M) (g := g⁻¹) hA_conj_inv_le_M)
  exact ⟨g, hgN, hgM, hA_le_Mg⟩

/-- Theorem 11.3. -/
public theorem CFSG.theorem_11_3
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    Group.IsNilpotent (section10Msigma M) := by
  classical
  let K : Subgroup G := section10Msigma M
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M P
  have hPamb_le_M : Pamb ≤ M := by
    simpa [Pamb] using section11_ambientSylow_le M P
  obtain ⟨g, hgN, hgM, hA_le_Mg⟩ := section11_obtain_g_and_A_le_Mg h11
  have hgN' : g ∈ Subgroup.normalizer (Pamb : Set G) := by simpa [Pamb] using hgN
  let R : Subgroup G := A0.conjBy g
  let S : Subgroup G := R ⊔ K
  have hK_le_M : K ≤ M := by
    simpa [K] using section11_msigma_le M
  have hR_le_Pamb : R ≤ Pamb := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, haA0, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgN' a).1
      (h11.A_le_ambient_sylow (h11.A0_le_A haA0))
  have hR_le_M : R ≤ M := hR_le_Pamb.trans hPamb_le_M
  have hS_le_M : S ≤ M := by
    simpa [S] using (sup_le hR_le_M hK_le_M)
  have hR_norm_K : R ≤ Subgroup.normalizer (K : Set G) :=
    hR_le_M.trans (by simpa [K] using section11_msigma_le_normalizer M)
  have hfixG : subgroupCentralizerIn K R = ⊥ := by
    simpa [subgroupCentralizerIn, K, R] using
      (corollary_11_2_b (M := M) (A0 := A0) (A := A) (p := p) (P := P)
        h11 (g := g) hgM hA_le_Mg)
  rcases h11.A_rank_two with ⟨_hAcard, hAelem⟩
  letI : IsMulCommutative A := hAelem.toIsMulCommutative
  have hR_le_cent : R ≤ Subgroup.centralizer (R : Set G) := by
    simpa [R] using section11_conjBy_le_centralizer_self
      (G := G) (A0 := A0) (A := A) h11.A0_le_A g
  have hKRinf_bot : K ⊓ R = ⊥ := by
    apply le_bot_iff.mp
    have hle : K ⊓ R ≤ subgroupCentralizerIn K R := by
      intro x hx
      exact ⟨hx.1, hR_le_cent hx.2⟩
    simpa [hfixG] using hle
  have hsolvS : IsSolvable S :=
    section11_solvable_of_le_maximal h11.maximal hS_le_M
  have hoddS : Odd (Nat.card S) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card S)
  have hKsub_normal : (K.subgroupOf S).Normal := by
    simpa [S] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := R) (N := K) hR_norm_K)
  have hKRcomp :
      (K.subgroupOf S).IsComplement' (R.subgroupOf S) := by
    simpa [S] using
      section11_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := K) (R := R) hR_norm_K hKRinf_bot
  have hRprime : Nat.Prime (Nat.card (R.subgroupOf S)) := by
    have hRcard : Nat.card R = p.val := by
      simpa [R, section11_card_conjBy A0 g] using h11.A0_prime_order.2
    have hRsubcard : Nat.card (R.subgroupOf S) = p.val := by
      exact (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := S) le_sup_left).toEquiv).trans hRcard
    simpa [hRsubcard] using p.property
  have hfixS :
      subgroupCentralizerIn (K.subgroupOf S) (R.subgroupOf S) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq S K R le_sup_left]
    simp [hfixG]
  have hnilKsub : Group.IsNilpotent (K.subgroupOf S) :=
    theorem_3_7 (G := S) (K.subgroupOf S) (R.subgroupOf S)
      hsolvS hoddS hKsub_normal hKRcomp hRprime hfixS
  let e : K.subgroupOf S ≃* K :=
    Subgroup.subgroupOfEquivOfLe (H := K) (K := S) le_sup_right
  exact (by
    simpa [K] using
      (Group.nilpotent_of_mulEquiv (G := K.subgroupOf S) (G' := K) (_h := hnilKsub) e))

end Section11
