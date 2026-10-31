module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.NatCard

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 1.3: the Fitting subgroup is self-centralizing (solvable case)

In a finite solvable group `G`, the centralizer of `F(G)` is contained in `F(G)`.
-/

universe u

public theorem CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    {G : Type u} [Group G] {ι : Sort*} {P : Subgroup G} (S : ι → Subgroup G)
    (hS : ∀ i, P ≤ Subgroup.centralizer (S i : Set G)) :
    P ≤ Subgroup.centralizer (((⨆ i, S i) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.iSup_eq_closure] at hy
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
    exact (Subgroup.mem_centralizer_iff.mp (hS i hx)) z hzi
  · simp
  · intro a b _ha _hb hax hbx
    calc
      a * b * x = a * (b * x) := by simp [mul_assoc]
      _ = a * (x * b) := by rw [hbx]
      _ = (a * x) * b := by simp [mul_assoc]
      _ = (x * a) * b := by rw [hax]
      _ = x * (a * b) := by simp [mul_assoc]
  · intro a _ha hax
    exact ((commute_iff_eq a x).2 hax).inv_left.eq

public theorem CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    {G : Type u} [Group G] [Finite G] {P : Subgroup G}
    (h : ∀ q : (Nat.card G).primeFactors.attach,
      P ≤ Subgroup.centralizer (pCore q.1.1 G : Set G)) :
    P ≤ Subgroup.centralizer (fittingSubgroup G : Set G) := by
  rw [fitting_eq_sup_pCore]
  exact subgroup_le_centralizer_iSup_of_le_centralizer
    (fun q : (Nat.card G).primeFactors.attach => pCore q.1.1 G) h

public theorem CFSG.fitting_pCore_le_sylow
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) :
    pCore p G ≤ (S : Subgroup G) := by
  have hsup_p : IsPGroup p (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) := by
    exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup G))
      (K := pCore p G) S.isPGroup' (pCore_isPGroup (G := G) (p := p))
  have hEq : (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) = (S : Subgroup G) :=
    S.is_maximal' hsup_p le_sup_left
  exact sup_eq_left.mp hEq

public theorem CFSG.pSubgroup_le_centralizer_pCore_of_cyclic_sylow_fitting
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hPp : IsPGroup p P)
    (hcycSylow : ∀ S : Sylow p G, IsCyclic (S : Subgroup G)) :
    P ≤ Subgroup.centralizer (pCore p G : Set G) := by
  classical
  obtain ⟨S, hP_le_S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hPp
  have hcore_le_S : pCore p G ≤ (S : Subgroup G) :=
    fitting_pCore_le_sylow S
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyCore
  have hxS : x ∈ (S : Subgroup G) := hP_le_S hxP
  have hyS : y ∈ (S : Subgroup G) := hcore_le_S hyCore
  have : IsMulCommutative (S : Subgroup G) := by
    have : IsCyclic (S : Subgroup G) := hcycSylow S
    exact IsCyclic.isMulCommutative
  exact setLike_mul_comm (s := (S : Subgroup G)) hyS hxS

public theorem CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G) :
    Subgroup.centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G := by
  classical
  -- Strong induction on the cardinality.
  let P : ℕ → Prop :=
    fun n =>
      ∀ (H : Type u) [Group H] [Finite H],
        Nat.card H = n →
          Group.IsSolvable H →
            Subgroup.centralizer (fittingSubgroup H : Set H) ≤ fittingSubgroup H

  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H _instHGroup _instHFinite hcard hsolvH
    classical
    let _ : Group.IsSolvable H := hsolvH

    let F : Subgroup H := fittingSubgroup H
    let C : Subgroup H := Subgroup.centralizer (F : Set H)

    have _ : F.Normal := by
      simpa [F] using (inferInstance : (fittingSubgroup H).Normal)
    have _ : C.Normal := by
      simpa [C, F] using
        (inferInstance : (Subgroup.centralizer (fittingSubgroup H) : Subgroup H).Normal)

    by_cases hCtop : C = ⊤
    · -- If `C = ⊤`, then `F` is central, hence `F = ⊤`.
      have hF_le_center : F ≤ Subgroup.center H := by
        intro f hf
        refine Subgroup.mem_center_iff.2 ?_
        intro g
        have hgC : g ∈ C := by simp [C, hCtop]
        have hgComm :=
          (Subgroup.mem_centralizer_iff (g := g) (s := (F : Set H))).1 hgC f hf
        simpa using hgComm.symm

      let π : H →* H ⧸ F := QuotientGroup.mk' F
      have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective F

      let Nbar : Subgroup (H ⧸ F) := fittingSubgroup (H ⧸ F)
      let N : Subgroup H := Nbar.comap π

      have hN_le_F : N ≤ F := by
        -- `N` is normal nilpotent in `H`, hence `N ≤ F`.
        have _ : N.Normal := (inferInstance : Nbar.Normal).comap π
        have hN_nil : Group.IsNilpotent (↥N) := by
          -- `N` is a central extension of the nilpotent group `Nbar`.
          let f : N →* Nbar :=
            (π.comp N.subtype).codRestrict Nbar (by intro x; exact x.property)
          have hfker : f.ker ≤ Subgroup.center N := by
            intro x hx
            have hxπ : π x.1 = 1 := by
              have : f x = 1 := by simpa [MonoidHom.mem_ker] using hx
              calc
                π x.1 = (f x : H ⧸ F) := by rfl
                _ = ((1 : Nbar) : H ⧸ F) := congrArg Subtype.val this
                _ = 1 := rfl
            have hxF : x.1 ∈ F := (QuotientGroup.eq_one_iff (N := F) x.1).1 hxπ
            have hxCenterH : x.1 ∈ Subgroup.center H := hF_le_center hxF
            refine Subgroup.mem_center_iff.2 ?_
            intro y
            apply Subtype.ext
            simpa using (Subgroup.mem_center_iff.mp hxCenterH) (y : H)
          exact Subgroup.isNilpotent_of_ker_le_center f hfker
        exact le_sSup
          (show N ∈ {M : Subgroup H | M.Normal ∧ Group.IsNilpotent M} from
            ⟨inferInstance, (by simpa using hN_nil)⟩)

      have hF_le_N : F ≤ N := by
        intro f hf
        have hπf : π f = 1 := (QuotientGroup.eq_one_iff (N := F) f).2 hf
        have : π f ∈ Nbar := by simp [Nbar, hπf]
        simpa [N, Subgroup.mem_comap] using this

      have hN_eq_F : N = F := le_antisymm hN_le_F hF_le_N

      have hNbar_bot : Nbar = ⊥ := by
        have hNmap : N.map π = Nbar := by
          simpa [N] using
            (Subgroup.map_comap_eq_self_of_surjective (f := π) hπ_surj Nbar)
        calc
          Nbar = N.map π := hNmap.symm
          _ = F.map π := by simp [hN_eq_F]
          _ = ⊥ := by simp [π]

      have hcardQ : Nat.card (H ⧸ F) = 1 := by
        let _ : Group.IsSolvable (H ⧸ F) := by infer_instance
        have hfit_bot : fittingSubgroup (H ⧸ F) = ⊥ := by simpa [Nbar] using hNbar_bot
        exact (fitting_eq_bot_iff_card_eq_one_of_solvable (G := (H ⧸ F))).1 hfit_bot

      have hsubQ : Subsingleton (H ⧸ F) := (Nat.card_eq_one_iff_unique.mp hcardQ).1
      have hF_top : F = ⊤ := (QuotientGroup.subsingleton_iff (N := F)).1 hsubQ
      simp [F, hF_top]

    · -- If `C` is proper, apply the IH to `C` to show `C` is nilpotent, hence `C ≤ F`.
      have hcardC_lt : Nat.card (↥C) < n := by
        have hx : ∃ x : H, x ∉ C := by
          by_contra h
          have hall : ∀ x : H, x ∈ C := by
            intro x
            by_contra hx
            exact h ⟨x, hx⟩
          have : C = ⊤ := by
            ext x
            constructor
            · intro _; simp
            · intro _; exact hall x
          exact hCtop this
        rcases hx with ⟨x, hx⟩
        have hlt : Nat.card (↥C) < Nat.card H := by
          simpa [C] using (Finite.card_subtype_lt (p := fun h : H => h ∈ C) hx)
        simpa [hcard] using hlt

      have hIH_C :
          Subgroup.centralizer (fittingSubgroup (↥C) : Set (↥C)) ≤ fittingSubgroup (↥C) :=
        (ih (Nat.card (↥C)) hcardC_lt) (↥C) rfl (by infer_instance)

      have hcentC_top :
          Subgroup.centralizer (fittingSubgroup (↥C) : Set (↥C)) = ⊤ := by
        apply top_le_iff.1
        intro c _
        -- The image of `fittingSubgroup C` in `H` is normal nilpotent, hence lies in `F`.
        have hfitC_le_F : fittingSubgroupOf (G := H) C ≤ F := by
          have hnorm : (fittingSubgroupOf (G := H) C).Normal :=
            fittingSubgroupOf_normal (G := H) C (by infer_instance)
          have hnil : Group.IsNilpotent (fittingSubgroupOf (G := H) C) :=
            fittingSubgroupOf_isNilpotent (G := H) C
          exact le_sSup ⟨hnorm, hnil⟩

        refine (Subgroup.mem_centralizer_iff
          (g := c) (s := (fittingSubgroup (↥C) : Set (↥C)))).2 ?_
        intro f hf
        have hfF : (f : H) ∈ F := by
          have hfIn : (f : H) ∈ fittingSubgroupOf (G := H) C := by
            simpa [fittingSubgroupOf] using (Subgroup.mem_map_of_mem C.subtype hf)
          exact hfitC_le_F hfIn

        have hcC : (c : H) ∈ Subgroup.centralizer (F : Set H) := by
          change (c : H) ∈ C
          exact c.property
        have hcomm :=
          (Subgroup.mem_centralizer_iff (g := (c : H)) (s := (F : Set H))).1 hcC (f : H) hfF
        apply Subtype.ext
        simpa using hcomm

      have hfitC_top : fittingSubgroup (↥C) = ⊤ := by
        have : (⊤ : Subgroup (↥C)) ≤ fittingSubgroup (↥C) := by
          simpa [hcentC_top] using hIH_C
        exact (top_le_iff).1 this

      have _ : Group.IsNilpotent (↥C) := by
        have _ : Group.IsNilpotent (fittingSubgroup (↥C)) := by infer_instance
        let e : (fittingSubgroup (↥C)) ≃* (↥C) :=
          (MulEquiv.subgroupCongr hfitC_top).trans (Subgroup.topEquiv : (⊤ : Subgroup (↥C)) ≃* (↥C))
        exact Group.nilpotent_of_mulEquiv (G := fittingSubgroup (↥C)) (G' := (↥C)) e

      have hC_le_F : C ≤ F :=
        le_sSup
          (show C ∈ {M : Subgroup H | M.Normal ∧ Group.IsNilpotent M} from
            ⟨inferInstance, (by infer_instance)⟩)

      simpa [C, F] using hC_le_F

  have : P (Nat.card G) := hP (Nat.card G)
  simpa using this G rfl hsolv
