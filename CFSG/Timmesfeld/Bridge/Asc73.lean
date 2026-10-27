module

public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Bridge.Asc73Edgeless
public import CFSG.Timmesfeld.Bridge.Asc73Lemma7
public import CFSG.Timmesfeld.Bridge.Connectivity
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

@[expose] def TheoremTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
    InvolutionPointLocalEmbedding H z → InvolutionPointCentralSylow z →
      fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z))

theorem fusionStronglyEmbedded_of_subgroupOf_top {X : Type*} [Group X] [Finite X]
    {H : Subgroup X} (h : fusionStronglyEmbedded (H.subgroupOf (⊤ : Subgroup X))) :
    fusionStronglyEmbedded H := by
  have hmap := h.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  have himage : (H.subgroupOf (⊤ : Subgroup X)).map
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = H := by
    change (H.subgroupOf (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype = H
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  rwa [himage] at hmap

variable {G : Type} [Group G] {D : Set G}

section Class

variable (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hodd : OddAcross D)
  (hdisc : Disconnected D)
include hN hD hodd hdisc

theorem involutionPointClass_eq {z : G} (hz : z ∈ D) : involutionPointClass z = D := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    simpa [rightConjugateElem] using hN g⁻¹ z hz
  · intro hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_of_disconnected_of_odd hD hodd hdisc hz hy)
    exact ⟨c⁻¹, by simp [rightConjugateElem]⟩

theorem involutionPointHull_eq_top (hgen : Subgroup.closure D = ⊤) {z : G} (hz : z ∈ D) :
    involutionPointHull z = ⊤ := by
  rw [involutionPointHull, involutionPointClass_eq hN hD hodd hdisc hz, hgen]

theorem localInvolutionPointHull_eq {z : G} (hz : z ∈ D) (u : G) :
    localInvolutionPointHull z u = subL D (Subgroup.centralizer ({u} : Set G)) := by
  rw [localInvolutionPointHull, involutionPointClass_eq hN hD hodd hdisc hz]

end Class

theorem mem_rightConjugate_compStab_iff (hN : IsNormalSet D) (hD : IsInvolutionSet D)
    (hodd : OddAcross D) {z : G} (hz : z ∈ D) (g : G) :
    z ∈ rightConjugate (compStab hN z) g ↔ g ∈ compStab hN z := by
  rw [rightConjugate, Subgroup.conjBy]
  exact mem_map_conj_inv_iff.trans (conj_mem_compStab_iff hN hD hodd hz g)

section Restrict

variable {K : Subgroup G}

theorem isNormalSet_subD (hN : IsNormalSet D) : IsNormalSet (subD D K) := by
  intro g x hx
  show ((g * x * g⁻¹ : subL D K) : G) ∈ D
  simpa using hN g x hx

theorem isInvolutionSet_subD (hD : IsInvolutionSet D) : IsInvolutionSet (subD D K) := by
  intro x hx
  rw [← Subgroup.orderOf_coe]
  exact hD.orderOf_eq_two hx

theorem closure_subD : Subgroup.closure (subD D K) = ⊤ := by
  have hset : subD D K = ((↑) : subL D K → G) ⁻¹' (D ∩ (K : Set G)) := by
    ext x
    exact ⟨fun h => ⟨h, subL_le K x.2⟩, fun h => h.1⟩
  rw [hset]
  exact Subgroup.closure_closure_coe_preimage

theorem noPolar_subD (hnp : Moufang.NoPolar D) : Moufang.NoPolar (subD D K) := by
  intro x hx y hy hxy hne
  show ((x * y : subL D K) : G) ∈ D
  exact hnp x hx y hy (hxy.map (subL D K).subtype) (fun h => hne (Subtype.ext h))

end Restrict

theorem fusionStronglyEmbedded_local [Finite G] (hN : IsNormalSet D) (hD : IsInvolutionSet D)
    (hodd : OddAcross D) (hnp : Moufang.NoPolar D) (hdisc : Disconnected D)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card G → Asc73For Y)
    (hcen : ∀ x : G, x ∈ Subgroup.center G → orderOf x = 2 → False) {z : G} (hz : z ∈ D)
    {u : G} (hu : orderOf u = 2) (huz : Commute u z)
    (hCu : ¬ Subgroup.centralizer ({u} : Set G) ≤ compStab hN z) :
    fusionStronglyEmbedded ((compStab hN z).subgroupOf (localInvolutionPointHull z u)) := by
  rw [localInvolutionPointHull_eq hN hD hodd hdisc hz]
  set K := Subgroup.centralizer ({u} : Set G) with hK
  obtain ⟨g, hgK, hgH⟩ := IsConcreteLE.not_le_iff_exists.1 hCu
  have hzK : z ∈ K := Subgroup.mem_centralizer_singleton_iff.2 huz.eq.symm
  have hw : g * z * g⁻¹ ∈ D := hN g z hz
  have hwK : g * z * g⁻¹ ∈ K := K.mul_mem (K.mul_mem hgK hzK) (K.inv_mem hgK)
  have hzL : z ∈ subL D K := Subgroup.subset_closure ⟨hz, hzK⟩
  have hwL : g * z * g⁻¹ ∈ subL D K := Subgroup.subset_closure ⟨hw, hwK⟩
  have hnr : ¬ Reach D z (g * z * g⁻¹) := hgH
  have hLtop : subL D K ≠ ⊤ := by
    intro hL
    refine hcen u (Subgroup.mem_center_iff.2 fun y => ?_) hu
    have hyK : y ∈ K := subL_le K (hL ▸ Subgroup.mem_top y)
    exact Subgroup.mem_centralizer_singleton_iff.1 hyK
  have hcard : Nat.card (subL D K) < Nat.card G :=
    calc Nat.card (subL D K) < Nat.card (⊤ : Subgroup G) :=
          Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hLtop)
      _ = Nat.card G := Subgroup.card_top
  have hdiscL : Disconnected (subD D K) :=
    ⟨⟨z, hzL⟩, hz, ⟨g * z * g⁻¹, hwL⟩, hw, fun h => hnr (reach_of_reach_subD h)⟩
  have hSE := hIH (subL D K) hcard (subD D K) (isNormalSet_subD hN) (isInvolutionSet_subD hD)
    closure_subD (noPolar_subD hnp) hdiscL ⟨z, hzL⟩ hz
  refine fusionStronglyEmbedded.of_le ((fusionStronglyEmbedded_iff _).2 hSE) ?_ ?_
  · intro l hl
    rw [Subgroup.mem_subgroupOf, mem_compStab_iff]
    simpa using reach_of_reach_subD hl
  · intro htop
    have hmem : (⟨g * z * g⁻¹, hwL⟩ : subL D K) ∈ (compStab hN z).subgroupOf (subL D K) :=
      htop ▸ Subgroup.mem_top _
    exact hnr (reach_of_mem_compStab_of_odd hN hD hodd hz hw (Subgroup.mem_subgroupOf.1 hmem))

theorem asc73For_of_smaller (h2 : TheoremTwoStatement) (hS : SchurNarrowInput) [Finite G]
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card G → Asc73For Y) :
    Asc73For G := by
  intro D hN hD hgen hnp hdisc z hz
  have hodd := oddAcross_of_noPolar hN hD hnp
  by_cases hedge : ∀ x ∈ D, ∀ y ∈ D, Commute x y → x = y
  · exact isStronglyEmbeddedOrder_of_edgeless hN hD hodd hgen hdisc hedge hz
  push Not at hedge
  obtain ⟨a, ha, b, hb, hab, hne⟩ := hedge
  have hcen : ∀ x : G, x ∈ Subgroup.center G → orderOf x = 2 → False := fun x hxc hx2 =>
    false_of_mem_center hS hN hD hgen hnp hdisc ha hb hne hab hIH hxc hx2
  have hclass : ∀ x ∈ D, ∀ y ∈ D, IsConj x y := fun x hx y hy =>
    isConj_of_disconnected_of_odd hD hodd hdisc hx hy
  have hloc : InvolutionPointLocalEmbedding (compStab hN z) z :=
    { proper := compStab_ne_top_of_odd hN hD hodd hdisc hz
      distinguished_mem := mem_compStab_self hN z
      distinguished_order := hD.orderOf_eq_two hz
      unique_containment := mem_rightConjugate_compStab_iff hN hD hodd hz
      local_embedding := fun u hu huz hCu =>
        fusionStronglyEmbedded_local hN hD hodd hnp hdisc hIH hcen hz hu huz hCu }
  have hcs : InvolutionPointCentralSylow z := by
    obtain ⟨S, hzS, hSz⟩ := exists_sylow_le_centralizer hN hD hnp hclass hz
    exact ⟨S, hzS, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hSz s s.2).eq⟩
  have h := h2 G (compStab hN z) z hloc hcs
  rw [involutionPointHull_eq_top hN hD hodd hdisc hgen hz] at h
  exact (fusionStronglyEmbedded_iff _).1 (fusionStronglyEmbedded_of_subgroupOf_top h)

theorem asc73For_of (h2 : TheoremTwoStatement) (hS : SchurNarrowInput) (G : Type) [Group G]
    [Finite G] : Asc73For G := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → Asc73For G from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn
    exact asc73For_of_smaller h2 hS fun Y _ _ hY => ih _ (hn ▸ hY) Y rfl

theorem asc73Input_of (h2 : TheoremTwoStatement) (hS : SchurNarrowInput) : Asc73Input :=
  fun G _ _ D hN hD hgen hnp hdisc d hd =>
    asc73For_of h2 hS G D hN (IsRootInvolutionSet.isInvolutionSet hD) hgen hnp hdisc d hd

theorem reach_of_reach_preimage (L : Subgroup G) {a b : L}
    (h : Reach (((↑) : L → G) ⁻¹' D) a b) : Reach D (a : G) (b : G) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih => exact reach_trans ih (reach_of_commute hbc.1 hbc.2.1 (hbc.2.2.map L.subtype))

theorem exists_fusionStronglyEmbedded_closure (h2 : TheoremTwoStatement) (hS : SchurNarrowInput)
    [Finite G] (hN : IsNormalSet D) (hD : IsInvolutionSet D) (hnp : Moufang.NoPolar D)
    (hdisc : Disconnected D) :
    ∃ M : Subgroup (Subgroup.closure D), fusionStronglyEmbedded M := by
  set L := Subgroup.closure D with hL
  set DL : Set L := ((↑) : L → G) ⁻¹' D with hDL
  have hNL : IsNormalSet DL := by
    intro g x hx
    show ((g * x * g⁻¹ : L) : G) ∈ D
    simpa using hN g x hx
  have hDL2 : IsInvolutionSet DL := by
    intro x hx
    rw [← Subgroup.orderOf_coe]
    exact hD.orderOf_eq_two hx
  have hnpL : Moufang.NoPolar DL := by
    intro x hx y hy hxy hne
    show ((x * y : L) : G) ∈ D
    exact hnp x hx y hy (hxy.map L.subtype) (fun h => hne (Subtype.ext h))
  obtain ⟨x, hx, y, hy, hxy⟩ := hdisc
  have hxL : x ∈ L := Subgroup.subset_closure hx
  have hyL : y ∈ L := Subgroup.subset_closure hy
  have hdiscL : Disconnected DL :=
    ⟨⟨x, hxL⟩, hx, ⟨y, hyL⟩, hy, fun h => hxy (reach_of_reach_preimage L h)⟩
  exact ⟨_, (fusionStronglyEmbedded_iff _).2 (asc73For_of h2 hS L DL hNL hDL2
    Subgroup.closure_closure_coe_preimage hnpL hdiscL ⟨x, hxL⟩ hx)⟩

end CFSG.Timmesfeld.Bridge
