module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Deg

@[expose] def IsSS (Q : Type*) [Group Q] : Prop :=
  ∀ N : Subgroup Q, N.Normal →
    N ⊓ Subgroup.centralizer (N : Set Q) = ⊥ ∧ N ⊔ Subgroup.centralizer (N : Set Q) = ⊤

variable {Q : Type*} [Group Q]

theorem IsSS.normal_of_conj_closed (hQ : IsSS Q) {N M : Subgroup Q} [N.Normal] (hMN : M ≤ N)
    (h : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) : M.Normal := by
  refine ⟨fun m hm g => ?_⟩
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Subgroup.mem_sup_of_normal_left.mp ((hQ N inferInstance).2 ▸ Subgroup.mem_top g)
  have hzm : m * z = z * m := Subgroup.mem_centralizer_iff.mp hz m (hMN hm)
  have e : g * m * g⁻¹ = y * m * y⁻¹ := by
    rw [← hyz]
    calc y * z * m * (y * z)⁻¹ = y * (z * m) * z⁻¹ * y⁻¹ := by group
      _ = y * (m * z) * z⁻¹ * y⁻¹ := by rw [hzm]
      _ = y * m * y⁻¹ := by group
  rw [e]
  exact h y hy m hm

theorem IsSS.subgroup_of_normal (hQ : IsSS Q) (N : Subgroup Q) [N.Normal] : IsSS N := by
  intro M hM
  set M' : Subgroup Q := M.map N.subtype with hM'
  have hM'n : M'.Normal := by
    refine hQ.normal_of_conj_closed (N := N) (Subgroup.map_subtype_le M) ?_
    rintro _ hn _ ⟨m, hm, rfl⟩
    exact ⟨⟨_, hn⟩ * m * ⟨_, hn⟩⁻¹, hM.conj_mem m hm ⟨_, hn⟩, by simp⟩
  obtain ⟨h1, h2⟩ := hQ M' hM'n
  constructor
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxM, hxC⟩ := hx
    have hmem : (x : Q) ∈ M' ⊓ Subgroup.centralizer (M' : Set Q) := by
      refine ⟨⟨x, hxM, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxC m hm)
    rw [h1, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨m, hm, c, hc, hmc⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (h2 ▸ Subgroup.mem_top (y : Q))
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hmc' : (m₀ : Q) * c = (y : Q) := hmc
    have hcN : c ∈ N := by
      have : c = ((m₀ : N) : Q)⁻¹ * y := by rw [← hmc']; group
      rw [this]
      exact mul_mem (inv_mem m₀.2) y.2
    have hc₀ : (⟨c, hcN⟩ : N) ∈ Subgroup.centralizer (M : Set N) := by
      refine Subgroup.mem_centralizer_iff.mpr fun m₁ hm₁ => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp hc (m₁ : Q) ⟨m₁, hm₁, rfl⟩
    have hy : y = m₀ * ⟨c, hcN⟩ := Subtype.ext hmc'.symm
    rw [hy]
    exact Subgroup.mul_mem_sup hm₀ hc₀

theorem IsSS.isPerfect (hQ : IsSS Q) : Group.IsPerfect Q := by
  obtain ⟨-, h2⟩ := hQ (commutator Q) inferInstance
  set L := Subgroup.centralizer (commutator Q : Set Q) with hL
  have hLn : L.Normal := Subgroup.normal_centralizer
  obtain ⟨h3, -⟩ := hQ L hLn
  have hLab : L ≤ Subgroup.centralizer (L : Set Q) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : y ∈ L := hy
    have h4 : ⁅y, x⁆ ∈ commutator Q ⊓ L := by
      refine ⟨?_, ?_⟩
      · rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem hy' hx) (L.inv_mem hy')) (L.inv_mem hx)
    have h5 : commutator Q ⊓ L = ⊥ := by
      obtain ⟨h1, -⟩ := hQ (commutator Q) inferInstance
      exact h1
    rw [h5, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4
  have hL0 : L = ⊥ := by
    rw [eq_bot_iff, ← h3]
    exact le_inf le_rfl hLab
  rw [hL0, sup_bot_eq] at h2
  exact ⟨h2⟩

theorem IsSS.eq_bot_of_normal_solvable (hQ : IsSS Q) (N : Subgroup Q) [N.Normal]
    [Group.IsSolvable N] : N = ⊥ := by
  have hp : Group.IsPerfect N := (hQ.subgroup_of_normal N).isPerfect
  by_contra hne
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  exact Group.IsPerfect.not_isSolvable N inferInstance

theorem layer_quotient_eq_top {H : Type*} [Group H] [Finite H] (hK : oStar H = ⊤) :
    CFSG.layer (H ⧸ CFSG.solvableRadical H) = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical H))) hK
  rwa [oStar_eq_comap_layer,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem isSS_of_oStar_eq_top {H : Type*} [Group H] [Finite H] (hK : oStar H = ⊤) :
    IsSS (H ⧸ CFSG.solvableRadical H) := by
  have hss : IsSemisimple (⊤ : Subgroup (H ⧸ CFSG.solvableRadical H)) := by
    have := isSemisimple_layer (solvableRadical_quotient (G := H))
    rwa [layer_quotient_eq_top hK] at this
  intro N hN
  have hp := hss.isDirectPair_of_normal (le_top : N ≤ ⊤) Subgroup.normal_subgroupOf
  rw [top_inf_eq] at hp
  exact ⟨hp.inf_eq_bot, hp.sup_eq⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Deg
