module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpDer
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpVec
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode

public section

namespace CFSG.StandardType.TwoThreeOrth

open Matrix Module CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section General

variable {G : Type*} [Group G]

theorem commutatorElement_eq_of_commute {a a' d d' : G} (h1 : Commute a a') (h2 : Commute a d)
    (h3 : Commute a d') (h4 : Commute a' d) (h5 : Commute a' d') :
    a * d * (a' * d') * (a * d)⁻¹ * (a' * d')⁻¹ = d * d' * d⁻¹ * d'⁻¹ := by
  have hX : Commute a (d * a' * d' * d⁻¹) :=
    ((h2.mul_right h1).mul_right h3).mul_right h2.inv_right
  have hY : Commute a' (d * d' * d⁻¹ * d'⁻¹) :=
    (((h4.mul_right h5).mul_right h4.inv_right).mul_right h5.inv_right)
  have e1 : a * d * (a' * d') * (a * d)⁻¹ * (a' * d')⁻¹ =
      (a * (d * a' * d' * d⁻¹) * a⁻¹) * d'⁻¹ * a'⁻¹ := by group
  have e2 : d * a' * d' * d⁻¹ * d'⁻¹ * a'⁻¹ = a' * (d * d' * d⁻¹ * d'⁻¹) * a'⁻¹ := by
    have h1' : d * a' = a' * d := h4.eq.symm
    have h2' : d' * a' = a' * d' := h5.eq.symm
    have h3' : d⁻¹ * a' = a' * d⁻¹ := h4.inv_right.eq.symm
    calc d * a' * d' * d⁻¹ * d'⁻¹ * a'⁻¹ = (d * a') * d' * d⁻¹ * d'⁻¹ * a'⁻¹ := rfl
      _ = a' * d * d' * d⁻¹ * d'⁻¹ * a'⁻¹ := by rw [h1']
      _ = a' * (d * d' * d⁻¹ * d'⁻¹) * a'⁻¹ := by group
  rw [e1, hX.mul_inv_cancel, e2, hY.mul_inv_cancel]

theorem largeEvenLayer_eq_of_commutator_commutator_mem {H D : Subgroup G} (hDH : D ≤ H)
    (hDn : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D)
    (hcomm : ∀ g ∈ ⁅H, H⁆, ∀ g' ∈ ⁅H, H⁆, g * g' * g⁻¹ * g'⁻¹ ∈ D)
    (hD : CFSG.IsQuasisimple D) : LargeEvenLayer H = D ∧ IsComponentOf D H := by
  have hcompD : IsComponentOf D H := by
    refine ⟨hDH, IsSubnormal.step hDH ?_ (IsSubnormal.refl H),
      (TableBSymp.isQuasisimple_iff _).mpr hD⟩
    rw [Subgroup.normal_subgroupOf_iff hDH]
    intro d h hd hh
    exact hDn h hh d hd
  have hle : ∀ K' : Subgroup G, IsComponentOf K' H → K' ≤ D := by
    intro K' hK'
    have hK'q : CFSG.IsQuasisimple K' := (TableBSymp.isQuasisimple_iff _).mp hK'.2.2
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    have h2 : ⁅⁅K', K'⁆, ⁅K', K'⁆⁆ ≤ D := by
      refine le_trans (Subgroup.commutator_mono (Subgroup.commutator_mono hK'.1 hK'.1)
        (Subgroup.commutator_mono hK'.1 hK'.1)) ?_
      rw [Subgroup.commutator_le]
      intro g hg g' hg'
      rw [commutatorElement_def]
      exact hcomm g hg g' hg'
    rwa [hK'perf, hK'perf] at h2
  exact ⟨le_antisymm (sSup_le fun K' hK' => hle K' hK') (le_sSup hcompD), hcompD⟩

end General

section Fixed

variable {K : Type} [Field K] {n : ℕ}

theorem eq_zero_of_mulVec_eq_self {g : StatedSp n K} (k : Fin n)
    (h1 : mat n K g *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inr k) 1)
    (h2 : mat n K g *ᵥ Pi.single (Sum.inr k) 1 =
      Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr k) 1)
    {v : Fin n ⊕ Fin n → K} (hv : mat n K g *ᵥ v = v) :
    v (Sum.inl k) = 0 ∧ v (Sum.inr k) = 0 := by
  have e1 := form_mulVec g v (Pi.single (Sum.inl k) 1)
  rw [hv, h1] at e1
  have e2 := form_mulVec g v (Pi.single (Sum.inr k) 1)
  rw [hv, h2, form_add_right] at e2
  have e3 : form v (Pi.single (Sum.inl k) 1) = 0 := by linear_combination e2
  have e4 : form v (Pi.single (Sum.inr k) 1) = 0 := by rw [e1, e3]
  rw [form_single_right] at e3 e4
  simp only [par_inl, par_inr, sgn_inl, sgn_inr, mul_one, mul_neg, neg_eq_zero] at e3 e4
  exact ⟨e4, e3⟩

end Fixed

section One

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}

omit [Finite K] in
theorem commutator_mem_of_mem_centralizer_nsElt (hK : Nat.card K = 2)
    {x x' : StatedSp (k + 1) K} (hx : x ∈ Subgroup.centralizer {nsElt (K := K) 0})
    (hx' : x' ∈ Subgroup.centralizer {nsElt (K := K) 0}) :
    x * x' * x⁻¹ * x'⁻¹ ∈ ⁅complSp K (0 : Fin (k + 1)), complSp K 0⁆ := by
  obtain ⟨a, ha, d, hd, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
    (Subgroup.mem_centralizer_singleton_iff.mp hx)
  obtain ⟨a', ha', d', hd', rfl⟩ := exists_eq_mul_of_commute_nsElt hK
    (Subgroup.mem_centralizer_singleton_iff.mp hx')
  have hAD : ∀ b ∈ nsTorusSp K (0 : Fin (k + 1)), ∀ e ∈ complSp K (0 : Fin (k + 1)),
      Commute b e := fun b hb e he =>
    (Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 he) b hb)
  have hAA : Commute a a' :=
    Subgroup.mem_centralizer_iff.mp (nsTorusSp_le_centralizer_self 0 ha') a ha
  rw [commutatorElement_eq_of_commute hAA (hAD a ha d hd) (hAD a ha d' hd') (hAD a' ha' d hd)
    (hAD a' ha' d' hd'), ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hd hd'

theorem layer_centralizer_nsElt_zero (hK : Nat.card K = 2) (hk : 2 ≤ k) :
    LargeEvenLayer (Subgroup.centralizer {nsElt (K := K) (n := k + 1) 0}) =
        ⁅complSp K (0 : Fin (k + 1)), complSp K 0⁆ ∧
      IsComponentOf ⁅complSp K (0 : Fin (k + 1)), complSp K 0⁆
        (Subgroup.centralizer {nsElt (K := K) (n := k + 1) 0}) := by
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem ?_
    (fun g hg h hh => commutator_mem_of_mem_centralizer_nsElt hK hg hh)
    (isQuasisimple_commutator_of_mulEquiv hK hk (complSpEquiv (K := K) 0))
  intro j hj
  have hjD : j ∈ complSp K (0 : Fin (k + 1)) := Subgroup.commutator_le_self _ hj
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 hjD) _
    (nsElt_mem_nsTorusSp 0)).symm

theorem mem_suppGroup_of_commute_nsElt_zero (hK : Nat.card K = 2) (hk : 2 ≤ k)
    {s : StatedSp (k + 1) K} (hs : s ∈ Subgroup.centralizer {nsElt (K := K) 0})
    (hsD : ∀ j ∈ ⁅complSp K (0 : Fin (k + 1)), complSp K 0⁆, s * j = j * s) :
    s ∈ suppGroup (coords (0 : Fin (k + 1))) := by
  obtain ⟨a, ha, d, hd, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
    (Subgroup.mem_centralizer_singleton_iff.mp hs)
  have hd1 : d = 1 := by
    refine eq_one_of_commute_commutator_of_mulEquiv hK hk (complSpEquiv (K := K) 0) hd
      fun j hj => ?_
    have hjD : j ∈ complSp K (0 : Fin (k + 1)) := Subgroup.commutator_le_self _ hj
    have hc : a * j = j * a :=
      Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 hjD) a ha
    have h1 := hsD j hj
    have : a * (d * j) = a * (j * d) := by
      calc a * (d * j) = a * d * j := by group
        _ = j * (a * d) := h1
        _ = (j * a) * d := by group
        _ = a * (j * d) := by rw [← hc]; group
    exact mul_left_cancel this
  rw [hd1, mul_one, ← range_longBlock]
  exact nsTorusSp_le_longRootSp2 0 ha

end One

end CFSG.StandardType.TwoThreeOrth
