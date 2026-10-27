module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EightTame
public import CFSG.RankThree.GF2n.Stroth80.Sec7TameCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularCard
public import CFSG.RankThree.GF2n.Stroth80.Sec710Point

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix


theorem step76EightTamePoint_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hZV : Sec7ZVStatement) : Step76EightTamePointStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g hg hΓ htame
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hcardInf := sec7_card_inf_conj_of_tame h34 hZV hc hs h4 hZ0 hg htame
  obtain ⟨K, fK, finK, hK, hnat⟩ := h4
  haveI : CharP K 2 := sec7ctr_charP hc hK
  have hm3 : 3 ≤ 4 := by norm_num
  have hnat' := hnat
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  haveI : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 4 ⊕ Fin 4 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hX := addCommutantScalar_statedOmegaPlus hm3 (K := K)
  have hW : ∀ x y : (Fin 4 ⊕ Fin 4) → K, x ≠ 0 → y ≠ 0 → quadPlus 4 K x = quadPlus 4 K y →
      ∃ A ∈ StatedOmega (StatedQuadPlus 4 K),
        ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ x = y :=
    fun a d ha hd hxy => statedOmegaPlus_exists_mulVec_eq hm3 ha hd hxy
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hV
  let S : Set (Fin 4 ⊕ Fin 4 → K) :=
    {u | ∃ k : ↥V, (k : G) ∈ conjSubgroup g V ∧ secVec ψ k = u}
  have hZV' : Z ≤ V := sec39_Z_le_Vt
  have hZg : Z ≤ conjSubgroup g V := hc.Z_le_conjSubgroup hZV' hg
  have h0S : (0 : Fin 4 ⊕ Fin 4 → K) ∈ S :=
    ⟨⟨1, V.one_mem⟩, (conjSubgroup g V).one_mem, (secVec_eq_zero_iff ψ _).mpr Z.one_mem⟩
  have haddS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    exact ⟨k * k', (conjSubgroup g V).mul_mem hk hk', secVec_mul ψ k k'⟩
  have hsmulS : ∀ (c : K) (a : Fin 4 ⊕ Fin 4 → K), a ∈ S → c • a ∈ S := by
    rintro c _ ⟨k, hk, rfl⟩
    obtain ⟨w, hw, hwπ⟩ := hc.exists_smul_mem_inf_conj hglob hg (θ.symm c)
      (Subgroup.mem_inf.mpr ⟨k.2, hk⟩)
    obtain ⟨hwV, hwg⟩ := Subgroup.mem_inf.mp hw
    refine ⟨⟨w, hwV⟩, hwg, ?_⟩
    have := hθ (θ.symm c) k ⟨w, hwV⟩ hwπ
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hSV : (V ⊓ conjSubgroup g V) ≤ V := inf_le_left
  let χ : ↥V →* Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
    (ψ : ↥V ⧸ Z.subgroupOf V →* Multiplicative (Fin 4 ⊕ Fin 4 → K)).comp
      (QuotientGroup.mk' (Z.subgroupOf V))
  have hχker : χ.ker = Z.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker]
    show ψ (QuotientGroup.mk x) = 1 ↔ x ∈ Z.subgroupOf V
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hmapcard := card_inf_mul_card_map (L := V ⊓ conjSubgroup g V) (R := V) (N := Z) hSV χ hχker
  have hZinf : (V ⊓ conjSubgroup g V) ⊓ Z = Z := inf_eq_right.mpr (le_inf hZV' hZg)
  rw [hZinf] at hmapcard
  have hSmap : Nat.card S = Nat.card ↥(((V ⊓ conjSubgroup g V).subgroupOf V).map χ) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : S => (⟨Multiplicative.ofAdd (u : Fin 4 ⊕ Fin 4 → K), ?_⟩ :
        ↥(((V ⊓ conjSubgroup g V).subgroupOf V).map χ)))
      ⟨?_, ?_⟩)
    · obtain ⟨k, hk, hku⟩ := u.2
      refine Subgroup.mem_map.mpr ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hk⟩, ?_⟩
      show Multiplicative.ofAdd (secVec ψ k) = Multiplicative.ofAdd (u : Fin 4 ⊕ Fin 4 → K)
      rw [hku]
    · intro u u' h
      apply Subtype.ext
      have := congrArg (fun z => Multiplicative.toAdd z.1) h
      simpa using this
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      obtain ⟨hkV, hkg⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)
      refine ⟨⟨Multiplicative.toAdd y, k, hkg, ?_⟩, Subtype.ext ?_⟩
      · show Multiplicative.toAdd (ψ (QuotientGroup.mk k)) = Multiplicative.toAdd y
        rw [← hky]
        rfl
      · rfl
  have hScard : Nat.card K ^ 4 ≤ Nat.card S := by
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have h1 : Nat.card Z ^ 5 ≤ Nat.card Z * Nat.card S := by
      rw [hSmap, hmapcard]
      exact hcardInf
    rw [hK]
    have : Nat.card Z * Nat.card Z ^ 4 ≤ Nat.card Z * Nat.card S := by
      rw [← pow_succ']
      exact h1
    exact Nat.le_of_mul_le_mul_left this hZpos
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hcard3 : Nat.card K ^ 3 < Nat.card S :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right hq1 (by norm_num)) hScard
  obtain ⟨u, huS, hu0, hQu⟩ := sec7_exists_singular_of_card (quadPlus 4 K) S h0S haddS hsmulS hcard3
  obtain ⟨k, hk, hku⟩ := huS
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inl ⟨4, hm3, hnat'⟩⟩
  exact exists_point_le_of_singular h34 hRoot hc hs5 hnatSO hK (ElemMatrixIso.plus hm3)
    (nondegenerate_polarBilin_quadPlus 4 K) h3 hX hW φ hφ hker ψ hψ hg hu0 hQu ⟨k, hk, hku⟩

end CFSG.RankThree.GF2n.Stroth80
