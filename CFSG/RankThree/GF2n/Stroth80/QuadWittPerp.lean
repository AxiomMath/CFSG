module

public import CFSG.RankThree.GF2n.Stroth80.QuadWitt
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag_le finrank_span_inl_image
  finrank_span_image_lt)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_singular_perp_not_mem [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {r : ℕ} (hV : finrank K V = 2 * r)
    (hT : ∃ T : Submodule K V, finrank K T = r ∧ ∀ x ∈ T, Q x = 0)
    {S : Submodule K V} (hS : ∀ x ∈ S, Q x = 0) (hlt : finrank K S < r) :
    ∃ v : V, Q v = 0 ∧ (∀ x ∈ S, polar Q v x = 0) ∧ v ∉ S := by
  set t := finrank K S
  set u := Module.finBasis K S
  set Wf : ℕ → Submodule K V :=
    fun i => span K ((fun j : Fin t => (u j : V)) '' {j | (j : ℕ) < i})
  have hli : LinearIndependent K (fun j : Fin t => (u j : V)) :=
    u.linearIndependent.map' S.subtype (ker_subtype S)
  have hWd : ∀ i ≤ t, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
  have hWm : ∀ i < t, Wf i ≤ Wf (i + 1) := fun i _ =>
    span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hWt : Wf t ≤ S := span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
  obtain ⟨b, hbQ, -, hbB, hbW, -⟩ := orthogonal_geometry_split_Witt_flags_aux hQ hV hT t
    hlt.le Wf hWd hWm (fun x hx => hS x (hWt hx))
  have hWS : Wf t = S := eq_of_le_of_finrank_eq hWt (by rw [hWd t le_rfl])
  have hSspan : S = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < t})) := by
    rw [← hWS, hbW t le_rfl]
  have hi₀ : t < r := hlt
  refine ⟨b (.inl ⟨t, hi₀⟩), (hbQ _).1, fun x hx => ?_, fun hmem => ?_⟩
  · have hker : span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < t})) ≤
        LinearMap.ker (polarBilin Q (b (.inl ⟨t, hi₀⟩))) := by
      rw [span_le]
      rintro _ ⟨_, ⟨j, _, rfl⟩, rfl⟩
      exact LinearMap.mem_ker.2 (by rw [polarBilin_apply_apply]; exact (hbB _ j).1)
    rw [hSspan] at hx
    have h := hker hx
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at h
  · rw [hSspan] at hmem
    have hnot : (Sum.inl ⟨t, hi₀⟩ : Fin r ⊕ Fin r) ∉
        Sum.inl '' {j : Fin r | (j : ℕ) < t} := by
      rintro ⟨j, hj, hji⟩
      have hj' : j = ⟨t, hi₀⟩ := Sum.inl_injective hji
      subst hj'
      exact lt_irrefl t hj
    exact b.linearIndependent.notMem_span_image hnot hmem

end CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem card_ge_of_perp_singular [Finite K] (M₀ : QuadModel QF V K γ)
    (hyp : ∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
      ∀ x ∈ S₂, M₀.Qf x = 0)
    {w : ℕ} (hdim : Module.finrank K M₀.E = 2 * w) {U : AddSubgroup M₀.E}
    (hU : ∀ e ∈ U, M₀.Qf e = 0)
    (hperp : ∀ v : M₀.E, (∀ u ∈ U, M₀.B v u = 0) → M₀.Qf v = 0 → v ∈ U) :
    Nat.card K ^ w ≤ Nat.card U := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hpolar : ∀ x y, QuadraticMap.polar M₀.toQuadraticForm x y = M₀.B x y :=
    polar_toQuadraticForm M₀
  have hBeq : QuadraticMap.polarBilin M₀.toQuadraticForm = M₀.B := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [QuadraticMap.polarBilin_apply_apply, hpolar]
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [B_comm, hy f, neg_zero]
  have hnd' : (QuadraticMap.polarBilin M₀.toQuadraticForm).Nondegenerate := by
    rw [hBeq]
    exact hnd
  obtain ⟨S₁, S₂, hS, hS₁, hS₂⟩ := hyp
  obtain ⟨S, hSdef⟩ : ∃ S : Submodule K M₀.E, S = Submodule.span K (U : Set M₀.E) :=
    ⟨_, rfl⟩
  have hSmem : ∀ u ∈ U, u ∈ S := fun u hu => by
    rw [hSdef]
    exact Submodule.subset_span (SetLike.mem_coe.2 hu)
  have hSs : ∀ x ∈ S, M₀.Qf x = 0 := by
    rw [hSdef]
    intro x hx
    exact (toQuadraticForm_apply M₀ x).symm.trans
      (CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span (Q := M₀.toQuadraticForm)
        (S := (U : Set M₀.E)) (fun u hu => (toQuadraticForm_apply M₀ u).trans (hU u hu))
        (fun u hu v hv => by
          rw [polar_toQuadraticForm]
          exact B_eq_zero_of_singular M₀ hU hu hv) hx)
  have hSs' : ∀ x ∈ S, M₀.toQuadraticForm x = 0 := fun x hx =>
    (toQuadraticForm_apply M₀ x).trans (hSs x hx)
  have hle : Module.finrank K S ≤ w := by
    have h := two_mul_finrank_le_of_totallySingular M₀ S hSs
    omega
  have hge : w ≤ Module.finrank K S := by
    by_contra hlt
    have h1 := two_mul_finrank_le_of_totallySingular M₀ S₁ hS₁
    have h2 := two_mul_finrank_le_of_totallySingular M₀ S₂ hS₂
    have hsum := Submodule.finrank_add_eq_of_isCompl hS
    have hT : ∃ T : Submodule K M₀.E, Module.finrank K T = w ∧
        ∀ x ∈ T, M₀.toQuadraticForm x = 0 :=
      ⟨S₁, by omega, fun x hx => (toQuadraticForm_apply M₀ x).trans (hS₁ x hx)⟩
    obtain ⟨v, hQv, hvperp, hvS⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_singular_perp_not_mem hnd' hdim hT hSs'
        (by omega)
    have hBv : ∀ u ∈ U, M₀.B v u = 0 := fun u hu => by
      have h := hvperp u (hSmem u hu)
      rwa [polar_toQuadraticForm] at h
    have hQv' : M₀.Qf v = 0 := (toQuadraticForm_apply M₀ v).symm.trans hQv
    exact hvS (hSmem v (hperp v hBv hQv'))
  have hfin : Module.finrank K S = w := le_antisymm hle hge
  have hSU : ∀ s ∈ S, s ∈ U := fun s hs => hperp s
    (fun u hu => B_eq_zero_of_singular M₀ (U := S.toAddSubgroup) hSs hs (hSmem u hu))
    (hSs s hs)
  have hcard : Nat.card S = Nat.card K ^ Module.finrank K S :=
    Module.natCard_eq_pow_finrank
  rw [hfin] at hcard
  have hinj : Nat.card S ≤ Nat.card U :=
    Nat.card_le_card_of_injective (fun s : S => (⟨s.1, hSU s.1 s.2⟩ : ↥U))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥U => (z : M₀.E)) h))
  exact (le_of_eq hcard.symm).trans hinj

end CFSG.RankThree.GF2n.Tim79.QuadModel
