module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

import Mathlib.Order.Atoms.Finite
import Mathlib.Order.RelSeries

namespace CFSG
end CFSG
open CFSG

section Proposition12

open scoped commutatorElement
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- The centralizer of a chief factor relative to `H` equals `H` intersected with the centralizer relative to the full group. -/
public lemma CFSG.centralizerOfChiefFactor_eq_inf_top (H : Subgroup G) (cf : ChiefFactor G) :
    centralizerOfChiefFactor (G := G) H cf =
      H ⊓ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  ext g
  simp [centralizerOfChiefFactor]

/-- The Fitting subgroup of a subgroup `H` is contained in `H`. -/
public lemma CFSG.fittingSubgroupOf_le (H : Subgroup G) : fittingSubgroupOf (G := G) H ≤ H := by
  simpa [fittingSubgroupOf] using
    (Subgroup.map_subtype_le (H := H) (K := fittingSubgroup (↥H)))

/-- A normal nilpotent subgroup `N` of `H` is contained in the Fitting subgroup of `H`. -/
public lemma CFSG.le_fittingSubgroupOf_of_normal_nilpotent {H N : Subgroup G} (hHN : N ≤ H)
    (hN_norm : N.Normal) (hN_nil : Group.IsNilpotent N) :
    N ≤ fittingSubgroupOf (G := G) H := by
  classical
  have hN_H_norm : (N.subgroupOf H).Normal :=
    (Subgroup.Normal.subgroupOf (G := G) (hH := hN_norm) H)
  haveI : Group.IsNilpotent (N.subgroupOf H) := by
    let e := (Subgroup.subgroupOfEquivOfLe (G := G) (H := N) (K := H) hHN).symm
    have : Group.IsNilpotent (↥N) := hN_nil
    exact Group.nilpotent_of_mulEquiv (G := N) (G' := N.subgroupOf H) e
  have hle_in_H : N.subgroupOf H ≤ fittingSubgroup (↥H) :=
    le_sSup ⟨hN_H_norm, (inferInstance : Group.IsNilpotent (N.subgroupOf H))⟩
  have hmap_le : (N.subgroupOf H).map H.subtype ≤ fittingSubgroupOf (G := G) H :=
    Subgroup.map_mono hle_in_H
  simpa [fittingSubgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHN] using hmap_le

/-- Mapping a chief factor centralizer to a quotient preserves the centralizer condition. -/
public lemma CFSG.centralizerOfChiefFactor_map_mk' (H : Subgroup G) (M : Subgroup G) [M.Normal]
    (cf : ChiefFactor (G ⧸ M)) :
    (centralizerOfChiefFactor (G := G) H (ChiefFactor.comapMk' (G := G) M cf)).map
        (QuotientGroup.mk' M) ≤
      centralizerOfChiefFactor (G := G ⧸ M) (H := H.map (QuotientGroup.mk' M)) cf := by
  classical
  intro x hx
  rcases Subgroup.mem_map.1 hx with ⟨g, hg, rfl⟩
  have hg' :
      g ∈ centralizerOfChiefFactor (G := G) H (ChiefFactor.comapMk' (G := G) M cf) := hg
  refine (mem_centralizerOfChiefFactor
    (G := G ⧸ M) (H := H.map (QuotientGroup.mk' M)) (cf := cf)
      (g := (QuotientGroup.mk' M) g)).2 ?_
  have hgH : g ∈ H :=
    (mem_centralizerOfChiefFactor (G := G) (H := H)
      (cf := ChiefFactor.comapMk' (G := G) M cf) (g := g)).1 hg' |>.1
  have hgHmap : (QuotientGroup.mk' M) g ∈ H.map (QuotientGroup.mk' M) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' M) hgH
  refine ⟨hgHmap, ?_⟩
  intro u hu
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective M u
  have hu0 : u0 ∈ (ChiefFactor.comapMk' (G := G) M cf).U := by
    simpa [ChiefFactor.comapMk', Subgroup.mem_comap] using hu
  have hcomm0 :
      ⁅g, u0⁆ ∈ (ChiefFactor.comapMk' (G := G) M cf).V :=
    (mem_centralizerOfChiefFactor (G := G) (H := H)
      (cf := ChiefFactor.comapMk' (G := G) M cf) (g := g)).1 hg' |>.2 u0 hu0
  have : (QuotientGroup.mk' M) (⁅g, u0⁆) ∈ cf.V := by
    simpa [ChiefFactor.comapMk', Subgroup.mem_comap] using hcomm0
  simpa [map_commutatorElement] using this

variable [Finite G]

/-- The Fitting subgroup of a subgroup `H` is nilpotent. -/
public lemma CFSG.fittingSubgroupOf_isNilpotent (H : Subgroup G) :
    Group.IsNilpotent (fittingSubgroupOf (G := G) H) := by
  classical
  haveI : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  change Group.IsNilpotent ((fittingSubgroup (↥H)).map H.subtype)
  let e : fittingSubgroup (↥H) ≃* (fittingSubgroup (↥H)).map H.subtype :=
    Subgroup.equivMapOfInjective (f := H.subtype) (fittingSubgroup (↥H)) H.subtype_injective
  exact Group.nilpotent_of_mulEquiv e

/-- If `H` is normal in `G`, then its Fitting subgroup, viewed inside `G`, lies in `F(G)`. -/
public lemma CFSG.fittingSubgroupOf_le_fittingSubgroup (H : Subgroup G) (hH : H.Normal) :
    fittingSubgroupOf (G := G) H ≤ fittingSubgroup G := by
  have hF_norm : (fittingSubgroupOf (G := G) H).Normal :=
    fittingSubgroupOf_normal (G := G) H hH
  have hF_nil : Group.IsNilpotent (fittingSubgroupOf (G := G) H) :=
    fittingSubgroupOf_isNilpotent (G := G) H
  exact le_sSup ⟨hF_norm, hF_nil⟩

/-- The centralizer of a chief factor `cf` relative to `H`, viewed as a subgroup of `H`.
This is used when forming intersections "inside `H`". -/
@[expose] public def CFSG.centralizerOfChiefFactorIn (H : Subgroup G) (cf : ChiefFactor G) : Subgroup H :=
  (centralizerOfChiefFactor (G := G) H cf).comap H.subtype

/-- Given a nontrivial normal subgroup `N` of a finite group `G`, there exists a proper normal
subgroup `M` of `G` contained in `N` which is maximal with respect to this property (i.e., `N/M`
is a chief factor of `G`). -/
public lemma CFSG.exists_maximal_normal_lt (N : Subgroup G) (hN_ne_bot : N ≠ ⊥) :
    ∃ (M : Subgroup G), M.Normal ∧ M < N ∧ ∀ (M' : Subgroup G), M'.Normal → M < M' → M' ≤ N → M' = N := by
  let S : Set (Subgroup G) := {M : Subgroup G | M.Normal ∧ M < N}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊥, ?_, ?_⟩
    · infer_instance
    · exact hN_ne_bot.bot_lt
  rcases hS_fin.exists_maximal hS_nonempty with ⟨M, hM, hM_max⟩
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro M' hM'_norm hM_lt_M' hM'_le_N
  by_cases hM'_N : M' = N
  · exact hM'_N
  · have hM'_lt_N : M' < N := lt_of_le_of_ne hM'_le_N hM'_N
    have hM'_S : M' ∈ S := ⟨hM'_norm, hM'_lt_N⟩
    have h_le : M ≤ M' := le_of_lt hM_lt_M'
    have hM'_le_M : M' ≤ M := hM_max hM'_S h_le
    have h_eq : M = M' := le_antisymm h_le hM'_le_M
    exact absurd h_eq (ne_of_lt hM_lt_M')

/-- Given normal subgroups `B < A` of a finite group `G`, there exists a proper normal
subgroup `C` of `G` with `B ≤ C < A` which is maximal with respect to this property
(i.e., `A/C` is a chief factor of `G`). -/
public lemma CFSG.exists_maximal_normal_lt_containing_B (A B : Subgroup G) (hB : B.Normal)
    (hAB : B < A) : ∃ (C : Subgroup G), C.Normal ∧ B ≤ C ∧ C < A ∧
      ∀ (D : Subgroup G), D.Normal → B ≤ D → C < D → D ≤ A → D = A := by
  let S : Set (Subgroup G) := {C : Subgroup G | C.Normal ∧ B ≤ C ∧ C < A}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := ⟨B, hB, le_rfl, hAB⟩
  rcases hS_fin.exists_maximal hS_nonempty with ⟨C, hC, hC_max⟩
  refine ⟨C, hC.1, hC.2.1, hC.2.2, ?_⟩
  intro D hD_norm hBD hCD hDA
  by_cases hDA' : D = A
  · exact hDA'
  · have hD_lt_A : D < A := lt_of_le_of_ne hDA hDA'
    have hD_S : D ∈ S := ⟨hD_norm, hBD, hD_lt_A⟩
    have h_le : C ≤ D := le_of_lt hCD
    have hD_le_C : D ≤ C := hC_max hD_S h_le
    have h_eq : C = D := le_antisymm h_le hD_le_C
    exact absurd h_eq (ne_of_lt hCD)

/-- Construct a chief series from `N` to `1`: a descending chain `N = N_0 > N_1 > ... > N_r = 1`
of normal subgroups of `G` where each `N_i/N_{i+1}` is a chief factor. -/
public lemma CFSG.exists_chief_series_from_to (N : Subgroup G) (hN : N.Normal) :
    ∃ (r : ℕ) (f : ℕ → Subgroup G), f 0 = N ∧ f r = ⊥ ∧ (∀ i ≤ r, (f i).Normal) ∧
      (∀ i < r, IsChiefFactor (f (i+1)) (f i)) := by
  classical
  let P : ℕ → Prop := fun n => ∀ (N' : Subgroup G), Nat.card N' = n → N'.Normal →
    ∃ (r : ℕ) (f : ℕ → Subgroup G), f 0 = N' ∧ f r = ⊥ ∧ (∀ i ≤ r, (f i).Normal) ∧
      (∀ i < r, IsChiefFactor (f (i+1)) (f i))
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n IH N' hcard_N' hN'_norm
    by_cases hN'_bot : N' = ⊥
    · subst hN'_bot
      refine ⟨0, λ _ => ⊥, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro i hi; simp
      · intro i hi; omega
    · have hN'_ne_bot : N' ≠ ⊥ := hN'_bot
      rcases exists_maximal_normal_lt N' hN'_ne_bot with ⟨M, hM_norm, hM_lt_N', hM_max⟩
      have h_card_M : Nat.card M < Nat.card N' := by
        have hM_lt_N'_set : (M : Set G) ⊂ (N' : Set G) := by
          refine ⟨λ x hx => hM_lt_N'.le hx, ?_⟩
          intro h_eq
          apply hM_lt_N'.ne
          exact SetLike.coe_injective (Set.Subset.antisymm (λ x hx => hM_lt_N'.le hx) h_eq)
        have hN'_fin : ((N' : Set G)).Finite := by
          have h_univ : (Set.univ : Set G).Finite := Set.finite_univ
          exact h_univ.subset (Set.subset_univ _)
        have h_card := Set.Finite.card_lt_card hN'_fin hM_lt_N'_set
        simpa using h_card
      have h_card_M_lt_n : Nat.card M < n := by
        rw [← hcard_N']
        exact h_card_M
      rcases IH (Nat.card M) h_card_M_lt_n M rfl hM_norm with ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩
      refine ⟨r+1, λ i => if i = 0 then N' else f (i-1), ?_, ?_, ?_, ?_⟩
      · simp
      · simp [hfr]
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0; exact hN'_norm
        · have : i-1 ≤ r := by omega
          have h_norm := hf_norm (i-1) this
          simpa [hi0] using h_norm
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          have h_f1_eq_M : (λ i => if i = 0 then N' else f (i-1)) 1 = M := by simp [hf0]
          have h_f0_eq_N' : (λ i => if i = 0 then N' else f (i-1)) 0 = N' := by simp
          rw [h_f1_eq_M, h_f0_eq_N']
          refine ⟨hM_norm, hN'_norm, hM_lt_N', ?_⟩
          intro K hK_norm hMK hKN'
          by_cases h_eq : K = M
          · left; exact h_eq
          · right
            have hM_lt_K : M < K := lt_of_le_of_ne hMK (Ne.symm h_eq)
            exact hM_max K hK_norm hM_lt_K hKN'
        · have hi1 : i-1 < r := by
            omega
          have h_chief := hf_chief (i-1) hi1
          have : (i-1 : ℕ) + 1 = i := by omega
          simpa [hi0, this] using h_chief
  let n : ℕ := Nat.card N
  have hn : Nat.card N = n := rfl
  have hPn : P n := Nat.strong_induction_on n hP
  exact hPn N hn hN

/-- The normal subgroups of `G` contained in `K`, packaged as a bounded order. -/
private abbrev CFSG.NormalBelow (K : Subgroup G) :=
  {L : Subgroup G // L ≤ K ∧ L.Normal}


private instance CFSG.normalBelowOrderBot (K : Subgroup G) :
    OrderBot (NormalBelow (G := G) K) where
  bot := ⟨⊥, by exact ⟨bot_le, inferInstance⟩⟩
  bot_le L := by
    change (⊥ : Subgroup G) ≤ L.1
    simp

private instance CFSG.normalBelowOrderTop (K : Subgroup G) [K.Normal] :
    OrderTop (NormalBelow (G := G) K) where
  top := ⟨K, by exact ⟨le_rfl, inferInstance⟩⟩
  le_top L := by
    change (L.1 : Subgroup G) ≤ K
    exact L.2.1

private instance CFSG.normalBelowBoundedOrder (K : Subgroup G) [K.Normal] :
    BoundedOrder (NormalBelow (G := G) K) :=
  { normalBelowOrderBot (G := G) K, normalBelowOrderTop (G := G) K with }


end Proposition12

section Proposition12RestrictedConverse

open scoped commutatorElement
open scoped IsMulCommutative

universe u

private def CFSG.subgroupToMap_local
    {G H : Type u} [Group G] [Group H] (f : G →* H) (N : Subgroup G) :
    (↥N) →* (↥(N.map f)) :=
  (f.comp N.subtype).codRestrict (N.map f) (by
    intro x
    exact Subgroup.mem_map_of_mem f x.property)

private theorem CFSG.card_quotient_lt_of_ne_bot_local
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) (hN_ne_bot : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  classical
  have hN_one_lt : 1 < Nat.card (↥N) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card (↥N) := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := N))
  have : Nat.card (G ⧸ N) * 1 < Nat.card (G ⧸ N) * Nat.card (↥N) :=
    Nat.mul_lt_mul_of_pos_left hN_one_lt (Nat.card_pos (α := G ⧸ N))
  simpa [hcard] using this

private theorem CFSG.comap_fittingSubgroupOf_map_le_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G] {H M : Subgroup G} [M.Normal]
    (hH : H.Normal) (hM_le_H : M ≤ H) (hH_le_centM : H ≤ Subgroup.centralizer (M : Set G)) :
    (fittingSubgroupOf (G := G ⧸ M) (H.map (QuotientGroup.mk' M))).comap (QuotientGroup.mk' M) ≤
      fittingSubgroupOf (G := G) H := by
  classical
  let π : G →* G ⧸ M := QuotientGroup.mk' M
  let Hbar : Subgroup (G ⧸ M) := H.map π
  let P : Subgroup G := (fittingSubgroupOf (G := G ⧸ M) Hbar).comap π
  have hHbar : Hbar.Normal := hH.map π (QuotientGroup.mk'_surjective M)
  have hP_le_H : P ≤ H := by
    intro x hx
    have hxHbar : π x ∈ Hbar :=
      (fittingSubgroupOf_le (G := G ⧸ M) Hbar) hx
    have hxH : x ∈ Hbar.comap π := hxHbar
    have hcomap_eq : Hbar.comap π = H := by
      simp [Hbar, π, sup_eq_right.2 hM_le_H]
    simpa [P, hcomap_eq] using hxH
  have hM_le_centH : M ≤ Subgroup.centralizer (H : Set G) :=
    (Subgroup.le_centralizer_iff (H := H) (K := M)).1 hH_le_centM
  have hP_normal : P.Normal :=
    (fittingSubgroupOf_normal (G := G ⧸ M) (H := Hbar) hHbar).comap π
  have hP_map : P.map π = fittingSubgroupOf (G := G ⧸ M) Hbar := by
    simpa [P] using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := π) (QuotientGroup.mk'_surjective M)
        (fittingSubgroupOf (G := G ⧸ M) Hbar))
  have hPmap_nil : Group.IsNilpotent (↥(P.map π)) := by
    rw [hP_map]
    exact fittingSubgroupOf_isNilpotent (G := G ⧸ M) Hbar
  let _ : Group.IsNilpotent (↥(P.map π)) := hPmap_nil
  have hker_le_center :
      (subgroupToMap_local (G := G) π P).ker ≤ Subgroup.center P := by
    intro x hx
    have hx1 : π x.1 = 1 := by
      simpa [subgroupToMap_local, MonoidHom.mem_ker] using hx
    have hxM : x.1 ∈ M := (QuotientGroup.eq_one_iff (N := M) x.1).1 hx1
    have hxcent : x.1 ∈ Subgroup.centralizer (H : Set G) := hM_le_centH hxM
    refine (Subgroup.mem_center_iff).2 ?_
    intro y
    have hyH : (y : G) ∈ H := hP_le_H y.2
    ext
    simpa using (Subgroup.mem_centralizer_iff.mp hxcent _ hyH)
  have hP_nil : Group.IsNilpotent P :=
    Subgroup.isNilpotent_of_ker_le_center (subgroupToMap_local (G := G) π P) hker_le_center
  exact le_fittingSubgroupOf_of_normal_nilpotent (G := G) (H := H) (N := P)
    hP_le_H hP_normal hP_nil

/-- Restricted converse direction in Proposition 1.2: a normal subgroup lies in its Fitting subgroup
whenever it centralizes every chief factor whose upper term lies in that Fitting subgroup. -/
public theorem CFSG.normal_le_fittingSubgroupOf_of_centralizes_restricted_chiefFactors_of_card :
    ∀ n : ℕ, ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G],
      ∀ (H : Subgroup G), H.Normal ->
        Nat.card H = n ->
          (∀ cf : ChiefFactor G, cf.U ≤ fittingSubgroupOf (G := G) H ->
            H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf) ->
          H ≤ fittingSubgroupOf (G := G) H := by
  intro n
  refine Nat.strongRecOn
    (motive := fun n =>
      ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G],
        ∀ (H : Subgroup G), H.Normal ->
          Nat.card H = n ->
            (∀ cf : ChiefFactor G, cf.U ≤ fittingSubgroupOf (G := G) H ->
              H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf) ->
            H ≤ fittingSubgroupOf (G := G) H)
    n (fun n ih => by
  intro G _ _ _ H hH hcard hchief
  classical
  by_cases hH_bot : H = ⊥
  · simp [hH_bot]
  · obtain ⟨M, hM_norm, hM_le_H, hM_ne_bot, hM_min⟩ :=
      exists_minimal_normal_le (G := G) H hH hH_bot
    haveI : M.Normal := hM_norm
    haveI : IsMinimalNormal M := {
      minimal := by
        intro L _instL hL_le_M
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        · exact Or.inr (hM_min L inferInstance hL_le_M hL_bot)
    }
    have hM_nil : Group.IsNilpotent M := by
      letI : IsMulCommutative M := minimalNormal_solvable_isMulCommutative M
      exact CommGroup.isNilpotent (G := M)
    have hM_le_fitH : M ≤ fittingSubgroupOf (G := G) H :=
      le_fittingSubgroupOf_of_normal_nilpotent (G := G) (H := H) (N := M)
        hM_le_H hM_norm hM_nil
    let cfM : ChiefFactor G := chiefFactorBot (G := G) M hM_norm hM_ne_bot hM_min
    have hcfM_U_eq : cfM.U = M := rfl
    have hcfM_V_eq : cfM.V = ⊥ := rfl
    have hcfM_U : cfM.U ≤ fittingSubgroupOf (G := G) H := by
      rw [hcfM_U_eq]
      exact hM_le_fitH
    have hH_cent_cfM :
        H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cfM :=
      hchief cfM hcfM_U
    have hcfM_comm : ⁅H, cfM.U⁆ ≤ cfM.V := by
      exact
        (le_centralizerOfChiefFactor_iff
          (G := G) (H := (⊤ : Subgroup G)) (N := H) (cf := cfM)).1 hH_cent_cfM |>.2
    have hcommHM : ⁅H, M⁆ ≤ (⊥ : Subgroup G) := by
      rw [← hcfM_U_eq, ← hcfM_V_eq]
      exact hcfM_comm
    have hH_le_centM : H ≤ Subgroup.centralizer (M : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := H) (H₂ := M)).1
        (le_bot_iff.mp hcommHM)
    let π : G →* G ⧸ M := QuotientGroup.mk' M
    let Hbar : Subgroup (G ⧸ M) := H.map π
    have hHbar : Hbar.Normal := hH.map π (QuotientGroup.mk'_surjective M)
    have hMsub_ne_bot : M.subgroupOf H ≠ ⊥ := by
      intro hbot
      have hmap_eq : (M.subgroupOf H).map H.subtype = M := by
        simp [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hM_le_H]
      have : M = ⊥ := by
        rw [← hmap_eq, hbot, Subgroup.map_bot]
      exact hM_ne_bot this
    have hcard_Hbar_lt : Nat.card Hbar < n := by
      have hlt : Nat.card Hbar < Nat.card H := by
        rw [show Nat.card Hbar = Nat.card (H ⧸ M.subgroupOf H) by
          simpa [Hbar, π] using natCard_map_mk'_eq H M]
        exact card_quotient_lt_of_ne_bot_local (G := ↥H) (N := M.subgroupOf H) hMsub_ne_bot
      simpa [hcard] using hlt
    have hfitbar_comap_le_fitH :
        (fittingSubgroupOf (G := G ⧸ M) Hbar).comap π ≤ fittingSubgroupOf (G := G) H :=
      comap_fittingSubgroupOf_map_le_fittingSubgroupOf
        (G := G) (H := H) (M := M) hH hM_le_H hH_le_centM
    have hchiefbar :
        ∀ cf : ChiefFactor (G ⧸ M), cf.U ≤ fittingSubgroupOf (G := G ⧸ M) Hbar →
          Hbar ≤ centralizerOfChiefFactor
            (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) cf := by
      intro cf hcfU
      have hpreU :
          (ChiefFactor.comapMk' (G := G) M cf).U ≤
            (fittingSubgroupOf (G := G ⧸ M) Hbar).comap π := by
        simpa [ChiefFactor.comapMk'] using (Subgroup.comap_mono hcfU)
      have hcf_preimage :
          (ChiefFactor.comapMk' (G := G) M cf).U ≤ fittingSubgroupOf (G := G) H :=
        hpreU.trans hfitbar_comap_le_fitH
      have hH_cent_preimage :
          H ≤ centralizerOfChiefFactor
            (G := G) (⊤ : Subgroup G) (ChiefFactor.comapMk' (G := G) M cf) :=
        hchief _ hcf_preimage
      have hmap_le :
          Hbar ≤
            (centralizerOfChiefFactor
              (G := G) (⊤ : Subgroup G) (ChiefFactor.comapMk' (G := G) M cf)).map π := by
        simpa [Hbar] using (Subgroup.map_mono hH_cent_preimage)
      have hcent_map :
          (centralizerOfChiefFactor
            (G := G) (⊤ : Subgroup G) (ChiefFactor.comapMk' (G := G) M cf)).map π ≤
            centralizerOfChiefFactor
              (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) cf := by
        have htmp :=
          centralizerOfChiefFactor_map_mk' (G := G) (H := (⊤ : Subgroup G)) (M := M) cf
        simpa [π, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective M)] using htmp
      exact hmap_le.trans hcent_map
    have hHbar_le_fitbar :
        Hbar ≤ fittingSubgroupOf (G := G ⧸ M) Hbar := by
      have h :
          ∀ {K : Type u} [Group K] [Finite K] [Group.IsSolvable K],
            ∀ (L : Subgroup K), L.Normal ->
              Nat.card L = Nat.card Hbar ->
                (∀ cf : ChiefFactor K, cf.U ≤ fittingSubgroupOf (G := K) L ->
                  L ≤ centralizerOfChiefFactor (G := K) (⊤ : Subgroup K) cf) ->
                L ≤ fittingSubgroupOf (G := K) L :=
        ih (Nat.card Hbar) hcard_Hbar_lt
      exact @h (G ⧸ M) _ _ inferInstance Hbar hHbar rfl hchiefbar
    have hH_le_fitbar_comap :
        H ≤ (fittingSubgroupOf (G := G ⧸ M) Hbar).comap π := by
      intro x hx
      have hxbar : π x ∈ Hbar := Subgroup.mem_map_of_mem π hx
      exact (Subgroup.comap_mono hHbar_le_fitbar) hxbar
    exact hH_le_fitbar_comap.trans hfitbar_comap_le_fitH
  )

/-- Restricted converse direction in Proposition 1.2. -/
public theorem CFSG.normal_le_fittingSubgroupOf_of_centralizes_restricted_chiefFactors
    {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (H : Subgroup G) (hH : H.Normal)
    (hchief :
      ∀ cf : ChiefFactor G, cf.U ≤ fittingSubgroupOf (G := G) H →
        H ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf) :
    H ≤ fittingSubgroupOf (G := G) H :=
  normal_le_fittingSubgroupOf_of_centralizes_restricted_chiefFactors_of_card
    (Nat.card H) (G := G) H hH rfl hchief

end Proposition12RestrictedConverse

open scoped IsMulCommutative

/-
**Kind**: Theorem
**Note**: Proposition 1.2
**Stmt**:
Let $G$ be a finite solvable group and that $G'$ is a normal subgroup of $G$.
Let $D$ be the set of all chief factors $U/V$ of $G$.
Let $D'$ be the set of all chief factors $U/V$ of $G$ for which $U \subset F(G')$.
Then
\[ F(G') = \bigcap_{U/V \in D} C_{G'}(U/V) = \bigcap_{U/V \in D'} C_{G'}(U/V). \]
-/
set_option maxHeartbeats 4000000 in
public theorem CFSG.proposition_1_2 {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (H : Subgroup G) (hH : H.Normal) :
    fittingSubgroupOf (G := G) H =
        sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) ∧
      fittingSubgroupOf (G := G) H =
        (sInf (centralizerOfChiefFactorIn (G := G) H ''
          {cf : ChiefFactor G | cf.U ≤ fittingSubgroupOf (G := G) H})).map H.subtype := by
  classical
  let F : Subgroup G := fittingSubgroupOf (G := G) H
  have hF_le_H : F ≤ H := fittingSubgroupOf_le (G := G) H
  have hF_norm : F.Normal := fittingSubgroupOf_normal (G := G) H hH
  have hF_nil : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent (G := G) H
  letI : Group.IsSolvable G := hsolv

  -- FIRST EQUALITY
  have hF_le_all : F ≤ sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) := by
    have hF_le_all' : ∀ cf : ChiefFactor G, F ≤ centralizerOfChiefFactor (G := G) H cf := by
      intro cf
      have hF_le_top : F ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
        normal_nilpotent_le_centralizerOfChiefFactor_top (G := G) hsolv F hF_norm hF_nil cf
      have h_eq : centralizerOfChiefFactor (G := G) H cf = H ⊓ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
        centralizerOfChiefFactor_eq_inf_top (G := G) (H := H) (cf := cf)
      rw [h_eq]
      exact le_inf hF_le_H hF_le_top
    rw [sInf_centralizerOfChiefFactor_univ_eq_iInf (G := G) (H := H)]
    exact le_iInf hF_le_all'

  have hall_le_F : sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) ≤ F := by
    rw [sInf_centralizerOfChiefFactor_univ_eq_iInf (G := G) (H := H)]
    let I : Subgroup G := ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf
    have hI_le_H : I ≤ H := by
      by_cases h_nonempty : Nonempty (ChiefFactor G)
      · rcases h_nonempty with ⟨cf⟩
        have hI_le_cf : I ≤ centralizerOfChiefFactor (G := G) H cf := iInf_le _ cf
        have hcf_le_H : centralizerOfChiefFactor (G := G) H cf ≤ H := by
          simp [centralizerOfChiefFactor]
        exact hI_le_cf.trans hcf_le_H
      · have hsub : Subsingleton G := by
          have : ¬ Nontrivial G := by
            intro hnt
            obtain ⟨M, hM_norm, hM_ne_bot, hmin⟩ := exists_minimal_normal (G := G) hsolv hnt
            exact h_nonempty ⟨chiefFactorBot (G := G) M hM_norm hM_ne_bot hmin⟩
          exact not_nontrivial_iff_subsingleton.mp this
        have hHtop : H = ⊤ := by
          ext g; constructor; intro _; trivial; intro _; have : g = 1 := Subsingleton.elim g 1; simp [this]
        simp [hHtop]
    have hI_norm : I.Normal := by
      refine Subgroup.normal_iInf_normal (fun cf => ?_)
      exact centralizerOfChiefFactor_normal (G := G) (H := H) hH cf
    have hI_nil : Group.IsNilpotent I := by
      have hI_le_baer : I ≤ baer (G := G) := by
        refine le_iInf (fun cf => ?_)
        have h_cf_le : centralizerOfChiefFactor (G := G) H cf ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
          intro g hg
          exact (mem_centralizerOfChiefFactor (H := (⊤ : Subgroup G)) (cf := cf) (g := g)).2
            ⟨by simp, (mem_centralizerOfChiefFactor (H := H) (cf := cf) (g := g)).1 hg |>.2⟩
        have h1 : (⨅ cf' : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf') ≤
            centralizerOfChiefFactor (G := G) H cf := iInf_le _ cf
        exact h1.trans h_cf_le
      haveI : Group.IsNilpotent (baer (G := G)) := baer_nilpotent (G := G) hsolv
      let J : Subgroup (↥(baer (G := G))) := I.subgroupOf (baer (G := G))
      haveI : Group.IsNilpotent J := by infer_instance
      let e := Subgroup.subgroupOfEquivOfLe (G := G) (H := I) (K := baer (G := G)) hI_le_baer
      exact Group.nilpotent_of_mulEquiv (G := J) (G' := I) e
    exact le_fittingSubgroupOf_of_normal_nilpotent (G := G) (H := H) (N := I) hI_le_H hI_norm hI_nil

  have hall_eq_F : F = sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) :=
    le_antisymm hF_le_all hall_le_F

  -- SECOND EQUALITY
  by_cases hS_empty : ∀ cf : ChiefFactor G, ¬ cf.U ≤ F
  · have hF_bot : F = ⊥ := by
      by_contra! hF_ne_bot
      rcases exists_minimal_normal_le (G := G) F hF_norm hF_ne_bot with ⟨M, hM_norm, hM_le_F, hM_ne_bot, hM_min⟩
      have hM_chief : IsChiefFactor ⊥ M :=
        { normal_K := by infer_instance
          normal_H := hM_norm
          lt := hM_ne_bot.bot_lt
          is_maximal := by
            intro K hK_norm hK_le hK_M
            by_cases hK_bot : K = ⊥
            · exact Or.inl hK_bot
            · exact Or.inr (hM_min K hK_norm hK_M hK_bot) }
      let cf : ChiefFactor G := ⟨⊥, M, hM_chief⟩
      exact hS_empty cf hM_le_F
    have hH_bot : H = ⊥ := by
      by_contra! hH_ne_bot
      rcases exists_minimal_normal_le (G := G) H hH hH_ne_bot with ⟨M, hM_norm, hM_le_H, hM_ne_bot, hM_min⟩
      haveI : IsMinimalNormal M :=
        { minimal := fun K hK_norm hK_le => by
            by_cases hK_bot : K = ⊥
            · exact Or.inl hK_bot
            · exact Or.inr (hM_min K hK_norm hK_le hK_bot) }
      letI : Group.IsSolvable (↥M) := by infer_instance
      have hM_abelian : IsMulCommutative (↥M) := minimalNormal_solvable_isMulCommutative M
      have hM_nil : Group.IsNilpotent M := by
        haveI : IsMulCommutative (↥M) := hM_abelian
        exact CommGroup.isNilpotent (G := M)
      have hM_le_F : M ≤ F := le_fittingSubgroupOf_of_normal_nilpotent hM_le_H hM_norm hM_nil
      have : M = ⊥ := le_bot_iff.mp (hM_le_F.trans (by simp [hF_bot]))
      exact hM_ne_bot this
    have hRHS_bot : (sInf (centralizerOfChiefFactorIn (G := G) H ''
        {cf : ChiefFactor G | cf.U ≤ F})).map H.subtype = ⊥ := by
      have h_empty : {cf : ChiefFactor G | cf.U ≤ F} = (∅ : Set (ChiefFactor G)) := by
        ext cf; simp [hS_empty cf]
      calc
        (sInf (centralizerOfChiefFactorIn (G := G) H '' {cf | cf.U ≤ F})).map H.subtype
            = (sInf (centralizerOfChiefFactorIn (G := G) H '' ∅)).map H.subtype := by rw [h_empty]
        _ = (sInf (∅ : Set (Subgroup H))).map H.subtype := by simp
        _ = (⊤ : Subgroup H).map H.subtype := by simp
        _ = H := by
          simpa [Subgroup.range_subtype] using (MonoidHom.range_eq_map H.subtype).symm
        _ = ⊥ := hH_bot
    have h_main : fittingSubgroupOf (G := G) H = sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) :=
      hall_eq_F
    have h_second : fittingSubgroupOf (G := G) H = (sInf (centralizerOfChiefFactorIn (G := G) H ''
        {cf : ChiefFactor G | cf.U ≤ F})).map H.subtype := by
      calc
        fittingSubgroupOf (G := G) H = F := rfl
        _ = ⊥ := hF_bot
        _ = (sInf (centralizerOfChiefFactorIn (G := G) H '' {cf : ChiefFactor G | cf.U ≤ F})).map H.subtype := by
          symm; exact hRHS_bot
    exact ⟨h_main, h_second⟩
  · push Not at hS_empty
    rcases hS_empty with ⟨cf0, hcf0⟩

    have h_centralizing_le_F (N : Subgroup G) (hN_norm : N.Normal) (hN_le_H : N ≤ H)
        (hN_centralizes : ∀ cf : ChiefFactor G, cf.U ≤ F → N ≤ centralizerOfChiefFactor (G := G) H cf) :
        N ≤ F := by
      by_contra! hN_not_le_F
      -- Choose K of minimal cardinality among {K normal, K ≤ N, K ⊈ F}
      let T : Set (Subgroup G) := {K | K.Normal ∧ K ≤ N ∧ ¬ K ≤ F}
      have hT_nonempty : T.Nonempty := ⟨N, hN_norm, le_rfl, hN_not_le_F⟩
      have hT_fin : T.Finite := Set.toFinite T
      have hK_exists : ∃ K ∈ T, ∀ K' ∈ T, Nat.card K ≤ Nat.card K' := by
        let h_cards : Set ℕ := {n | ∃ (K : Subgroup G), K ∈ T ∧ Nat.card K = n}
        have h_cards_nonempty : h_cards.Nonempty := by
          rcases hT_nonempty with ⟨K, hK⟩
          refine ⟨Nat.card K, ?_⟩
          dsimp [h_cards]; exact ⟨K, hK, rfl⟩
        let n := Nat.find h_cards_nonempty
        have hn : n ∈ h_cards := Nat.find_spec h_cards_nonempty
        have hn' : ∃ (K : Subgroup G), K ∈ T ∧ Nat.card K = n := by
          dsimp [h_cards] at hn; exact hn
        rcases hn' with ⟨K, hK, hcard⟩
        refine ⟨K, hK, λ K' hK' => ?_⟩
        have hcard' : Nat.card K' ∈ h_cards := by
          dsimp [h_cards]; exact ⟨K', hK', rfl⟩
        have hn_min : n ≤ Nat.card K' := Nat.find_min' h_cards_nonempty hcard'
        simpa [hcard] using hn_min
      rcases hK_exists with ⟨K, hK, hK_min_card⟩
      rcases hK with ⟨hK_norm, hK_le_N, hK_not_le_F⟩
      have hK_ne_bot : K ≠ ⊥ := by
        intro hK_bot; apply hK_not_le_F; simp [hK_bot]
      rcases exists_chief_series_from_to K hK_norm with ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩
      have hr_pos : 0 < r := by
        by_contra! h
        have h_r0 : r = 0 := by omega
        have hf0_bot : f 0 = ⊥ := by simpa [h_r0] using hfr
        rw [hf0_bot] at hf0
        exact hK_ne_bot hf0.symm
      have hK1_lt_K : f 1 < K := by
        have h_lt := (hf_chief 0 hr_pos).lt
        rw [hf0] at h_lt; exact h_lt
      have hK1_le_F : f 1 ≤ F := by
        by_cases h : f 1 ≤ F; exact h
        have h1_le_r : 1 ≤ r := Nat.succ_le_of_lt hr_pos
        have hK1_T : f 1 ∈ T := ⟨hf_norm 1 h1_le_r, hK1_lt_K.le.trans hK_le_N, h⟩
        have h_card_lt : Nat.card (f 1) < Nat.card K := by
          have h_lt_set : (f 1 : Set G) ⊂ (K : Set G) := by
            refine ⟨λ x hx => hK1_lt_K.le hx, ?_⟩
            intro h_eq; apply hK1_lt_K.ne
            exact SetLike.coe_injective (Set.Subset.antisymm (λ x hx => hK1_lt_K.le hx) h_eq)
          have hK_fin : (K : Set G).Finite :=
            Set.Finite.subset (Set.finite_univ (α := G)) (Set.subset_univ _)
          have h_card := Set.Finite.card_lt_card hK_fin h_lt_set
          simpa using h_card
        have h_card_contra : Nat.card K ≤ Nat.card (f 1) := hK_min_card (f 1) hK1_T
        linarith
      have h_fi_le_F : ∀ i, 1 ≤ i → i ≤ r → f i ≤ F := by
        intro i hi1 hir
        induction i with
        | zero => exfalso; omega
        | succ i ih =>
          by_cases hi_succ_eq_1 : i.succ = 1
          · have htemp : f (i.succ) = f 1 := by rw [hi_succ_eq_1]
            rw [htemp]
            exact hK1_le_F
          · have hi_ge1 : 1 ≤ i := by omega
            have hi_le_r : i ≤ r := by omega
            have hfi_F : f i ≤ F := ih hi_ge1 hi_le_r
            have hi_lt_r : i < r := by
              have : i.succ ≤ r := hir; omega
            have h_lt : f (i.succ) < f i := (hf_chief i hi_lt_r).lt
            exact h_lt.le.trans hfi_F
      have h_centralized : ∀ i, 2 ≤ i → i ≤ r → ⁅K, f (i-1)⁆ ≤ f i := by
        intro i hi2 hir
        have hi1' : 1 ≤ i - 1 := by omega
        have hir' : i-1 ≤ r := by omega
        have h_fi1_le_F : f (i-1) ≤ F := h_fi_le_F (i-1) hi1' hir'
        have hi_lt_r : i-1 < r := by
          have : i ≤ r := hir; omega
        have h_chief : IsChiefFactor (f i) (f (i-1)) := by
          simpa [show (i-1 : ℕ) + 1 = i by omega] using hf_chief (i-1) hi_lt_r
        let cf : ChiefFactor G := ⟨f i, f (i-1), h_chief⟩
        have h_cf_U_le_F : cf.U ≤ F := h_fi1_le_F
        have hN_cent : N ≤ centralizerOfChiefFactor (G := G) H cf := hN_centralizes cf h_cf_U_le_F
        have hK_cent : K ≤ centralizerOfChiefFactor (G := G) H cf := hK_le_N.trans hN_cent
        have h_comm : ⁅K, f (i-1)⁆ ≤ f i :=
          (le_centralizerOfChiefFactor_iff (G := G) (H := H) (N := K) (cf := cf)).mp hK_cent |>.2
        exact h_comm
      have h_chief0 : IsChiefFactor (f 1) K := by
        simpa [hf0] using hf_chief 0 hr_pos
      haveI : (f 1).Normal := h_chief0.normal_K
      have hK1_le_K : f 1 ≤ K := hK1_lt_K.le
      haveI : ((f 1).subgroupOf K).Normal :=
        Subgroup.Normal.subgroupOf (G := G) (hH := h_chief0.normal_K) K
      let π : G →* G ⧸ f 1 := QuotientGroup.mk' (f 1)
      let Uq : Subgroup (G ⧸ f 1) := K.map π
      have h_abelian_Uq : IsMulCommutative (↥Uq) := by
        haveI : Uq.Normal := h_chief0.normal_H.map π (QuotientGroup.mk'_surjective (f 1))
        haveI : IsMinimalNormal Uq :=
          chiefFactor_quotient_isMinimalNormal (G := G) ⟨f 1, K, h_chief0⟩
        letI : Group.IsSolvable (G ⧸ f 1) := by infer_instance
        letI : Group.IsSolvable (↥Uq) := by infer_instance
        exact minimalNormal_solvable_isMulCommutative (G := G ⧸ f 1) Uq
      have h_comm1 : ⁅K, K⁆ ≤ f 1 := by
        have h_self_centralizing : Uq ≤ Subgroup.centralizer (Uq : Set (G ⧸ f 1)) :=
          (Subgroup.le_centralizer_iff_isMulCommutative (K := Uq)).mpr h_abelian_Uq
        have h_comm_Uq : ⁅Uq, Uq⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          exact h_self_centralizing
        have h_comm_map : (⁅K, K⁆).map π = ⊥ := by
          calc
            (⁅K, K⁆).map π = ⁅K.map π, K.map π⁆ := Subgroup.map_commutator (f := π) (H₁ := K) (H₂ := K)
            _ = ⁅Uq, Uq⁆ := rfl
            _ = ⊥ := h_comm_Uq
        have h_comm_le_ker : ⁅K, K⁆ ≤ π.ker :=
          (Subgroup.map_eq_bot_iff (f := π) (H := ⁅K, K⁆)).mp h_comm_map
        have h_ker_eq : π.ker = f 1 := QuotientGroup.ker_mk' (f 1)
        rw [h_ker_eq] at h_comm_le_ker
        exact h_comm_le_ker
      have h_central_series : ∀ i, i < r → ⁅K, f i⁆ ≤ f (i+1) := by
        intro i hi
        by_cases hi0 : i = 0
        · rw [hi0, hf0]; exact h_comm1
        · have hi_ge2 : 2 ≤ i+1 := by omega
          have hi1_le_r : i+1 ≤ r := by omega
          have h := h_centralized (i+1) hi_ge2 hi1_le_r
          simpa [Subgroup.commutator_comm (H₁ := f i) (H₂ := K)] using h
      have h_fi_le_K : ∀ i ≤ r, f i ≤ K := by
        intro i hi
        induction i with
        | zero => rw [hf0]
        | succ i ih =>
          have hi_le_r : i ≤ r := by omega
          have hi_lt_r : i < r := by omega
          have h_lt : f (i+1) < f i := (hf_chief i hi_lt_r).lt
          exact h_lt.le.trans (ih hi_le_r)
      have hK_nilpotent : Group.IsNilpotent K := by
        rw [Subgroup.nilpotent_iff_lowerCentralSeries (G := K)]
        have h_lcs_le : ∀ i, i ≤ r →
            (⊤ : Subgroup K).lowerCentralSeries i ≤ (f i).subgroupOf K := by
          intro i hi
          induction i with
          | zero => simp [hf0]
          | succ i ih =>
            have hi_succ_le_r : i.succ ≤ r := hi
            have hi_le_r : i ≤ r := by omega
            have hi_lt_r : i < r := by omega
            have h_central : ⁅K, f i⁆ ≤ f (i+1) := h_central_series i hi_lt_r
            have h_fi1_le_K : f (i+1) ≤ K := h_fi_le_K (i+1) hi_succ_le_r
            have h_fi_le_K' : f i ≤ K := h_fi_le_K i hi_le_r
            have h_top_map : (⊤ : Subgroup (↥K)).map K.subtype = K := by ext x; simp
            calc
              (⊤ : Subgroup K).lowerCentralSeries (i+1) =
                  ⁅(⊤ : Subgroup K).lowerCentralSeries i, ⊤⁆ := rfl
              _ ≤ ⁅(f i).subgroupOf K, ⊤⁆ := Subgroup.commutator_mono (ih hi_le_r) (le_refl _)
              _ ≤ (f (i+1)).subgroupOf K := by
                have h_map_ineq : Subgroup.map K.subtype (⁅(f i).subgroupOf K, ⊤⁆) ≤ Subgroup.map K.subtype ((f (i+1)).subgroupOf K) := by
                  calc
                    Subgroup.map K.subtype (⁅(f i).subgroupOf K, ⊤⁆)
                        = ⁅Subgroup.map K.subtype ((f i).subgroupOf K), Subgroup.map K.subtype (⊤ : Subgroup (↥K))⁆ :=
                      Subgroup.map_commutator (f := K.subtype) (H₁ := (f i).subgroupOf K) (H₂ := ⊤)
                    _ = ⁅f i ⊓ K, K⁆ := by
                      simp [Subgroup.subgroupOf_map_subtype, h_top_map]
                    _ = ⁅f i, K⁆ := by simp [h_fi_le_K']
                    _ = ⁅K, f i⁆ := Subgroup.commutator_comm _ _
                    _ ≤ f (i+1) := h_central
                    _ = Subgroup.map K.subtype ((f (i+1)).subgroupOf K) := by simp [h_fi1_le_K]
                exact (Subgroup.map_le_map_iff_of_injective (f := K.subtype) K.subtype_injective).mp h_map_ineq
        have h_lcs_r : (⊤ : Subgroup K).lowerCentralSeries r = ⊥ := by
          apply eq_bot_iff.mpr
          calc
            (⊤ : Subgroup K).lowerCentralSeries r ≤ (f r).subgroupOf K :=
              h_lcs_le r (le_refl r)
            _ = (⊥ : Subgroup G).subgroupOf K := by rw [hfr]
            _ = ⊥ := by simp
        exact ⟨r, h_lcs_r⟩
      have hK_le_F : K ≤ F :=
        le_fittingSubgroupOf_of_normal_nilpotent (hK_le_N.trans hN_le_H) hK_norm hK_nilpotent
      exact hK_not_le_F hK_le_F

    let I_res : Subgroup G := ⨅ (cf : ChiefFactor G) (_ : cf.U ≤ F), centralizerOfChiefFactor (G := G) H cf
    have hI_res_norm : I_res.Normal := by
      refine Subgroup.normal_iInf_normal (fun cf => ?_)
      refine Subgroup.normal_iInf_normal (fun h => ?_)
      exact centralizerOfChiefFactor_normal (G := G) (H := H) hH cf
    have hI_res_le_H : I_res ≤ H := by
      have hI_res_le_cf0 : I_res ≤ centralizerOfChiefFactor (G := G) H cf0 := by
        have h1 : I_res ≤ ⨅ (_ : cf0.U ≤ F), centralizerOfChiefFactor (G := G) H cf0 :=
          iInf_le (fun cf' : ChiefFactor G => ⨅ (_ : cf'.U ≤ F), centralizerOfChiefFactor (G := G) H cf') cf0
        exact h1.trans (iInf_le (fun (_ : cf0.U ≤ F) => centralizerOfChiefFactor (G := G) H cf0) hcf0)
      have h_cf0_le_H : centralizerOfChiefFactor (G := G) H cf0 ≤ H := by
        simp [centralizerOfChiefFactor]
      exact hI_res_le_cf0.trans h_cf0_le_H
    have hI_res_centralizes : ∀ cf : ChiefFactor G, cf.U ≤ F → I_res ≤ centralizerOfChiefFactor (G := G) H cf := by
      intro cf hcf
      have h1 : I_res ≤ ⨅ (_ : cf.U ≤ F), centralizerOfChiefFactor (G := G) H cf :=
        iInf_le (fun cf' : ChiefFactor G => ⨅ (_ : cf'.U ≤ F), centralizerOfChiefFactor (G := G) H cf') cf
      exact h1.trans (iInf_le (fun (_ : cf.U ≤ F) => centralizerOfChiefFactor (G := G) H cf) hcf)

    have hI_res_le_F : I_res ≤ F :=
      h_centralizing_le_F I_res hI_res_norm hI_res_le_H hI_res_centralizes

    have hF_le_I_res : F ≤ I_res := by
      have hF_centralizes : ∀ cf : ChiefFactor G, cf.U ≤ F → F ≤ centralizerOfChiefFactor (G := G) H cf := by
        intro cf hcf
        have hF_le_top : F ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
          normal_nilpotent_le_centralizerOfChiefFactor_top (G := G) hsolv F hF_norm hF_nil cf
        have h_eq : centralizerOfChiefFactor (G := G) H cf = H ⊓ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
          centralizerOfChiefFactor_eq_inf_top (G := G) (H := H) (cf := cf)
        rw [h_eq]
        exact le_inf hF_le_H hF_le_top
      refine le_iInf (fun cf => ?_)
      refine le_iInf (fun hcf => ?_)
      exact hF_centralizes cf hcf

    have hF_eq_I_res : F = I_res := le_antisymm hF_le_I_res hI_res_le_F

    have h_rhs_eq_I_res : (sInf (centralizerOfChiefFactorIn (G := G) H ''
        {cf : ChiefFactor G | cf.U ≤ F})).map H.subtype = I_res := by
      let S : Set (ChiefFactor G) := {cf | cf.U ≤ F}
      let I_res' : Subgroup H := sInf (centralizerOfChiefFactorIn (G := G) H '' S)
      have h_map_eq (cf : S) : (centralizerOfChiefFactorIn (G := G) H cf).map H.subtype =
          centralizerOfChiefFactor (G := G) H cf := by
        dsimp [centralizerOfChiefFactorIn]
        have h_sub : centralizerOfChiefFactor (G := G) H cf ≤ H := by
          simp [centralizerOfChiefFactor]
        ext x; constructor
        · rintro ⟨y, hy, rfl⟩
          have hy' := (Subgroup.mem_comap (f := H.subtype) (K := centralizerOfChiefFactor (G := G) H cf)).mp hy
          exact hy'
        · intro hx
          refine ⟨⟨x, h_sub hx⟩, ?_, rfl⟩
          change x ∈ centralizerOfChiefFactor (G := G) H cf
          exact hx
      have hI_res'_le_I_res : I_res'.map H.subtype ≤ I_res := by
        refine le_iInf (fun cf => ?_)
        refine le_iInf (fun hcf => ?_)
        have hI_res'_le_cf : I_res' ≤ centralizerOfChiefFactorIn (G := G) H cf := by
          apply sInf_le; exact ⟨cf, hcf, rfl⟩
        calc
          I_res'.map H.subtype ≤ (centralizerOfChiefFactorIn (G := G) H cf).map H.subtype :=
            Subgroup.map_mono hI_res'_le_cf
          _ = centralizerOfChiefFactor (G := G) H cf := by
            simpa using h_map_eq ⟨cf, hcf⟩
      have hI_res_le_I_res' : I_res ≤ I_res'.map H.subtype := by
        have hI_res_comap_le : I_res.comap H.subtype ≤ I_res' := by
          refine le_sInf ?_
          intro K hK
          rcases hK with ⟨cf, hcf, rfl⟩
          have hI_res_le_cf : I_res ≤ centralizerOfChiefFactor (G := G) H cf :=
            hI_res_centralizes cf hcf
          intro x hx
          have hx_val : (x : G) ∈ I_res := by
            change (x : G) ∈ I_res at hx
            exact hx
          have hx_cf : (x : G) ∈ centralizerOfChiefFactor (G := G) H cf := hI_res_le_cf hx_val
          exact (Subgroup.mem_comap (f := H.subtype)).mpr hx_cf
        calc
          I_res = (I_res.comap H.subtype).map H.subtype := by
            ext x; constructor
            · intro hx; have hxH : x ∈ H := hI_res_le_H hx
              refine ⟨⟨x, hxH⟩, ?_, rfl⟩; simpa [Subgroup.mem_subgroupOf] using hx
            · rintro ⟨y, hy, rfl⟩
              change (y : G) ∈ I_res at hy
              exact hy
          _ ≤ I_res'.map H.subtype := Subgroup.map_mono hI_res_comap_le
      exact le_antisymm hI_res'_le_I_res hI_res_le_I_res'

    have h_goal : F = (sInf (centralizerOfChiefFactorIn (G := G) H ''
        {cf : ChiefFactor G | cf.U ≤ F})).map H.subtype :=
      hF_eq_I_res.trans h_rhs_eq_I_res.symm
    refine ⟨hall_eq_F, ?_⟩
    simpa [F] using h_goal

public theorem CFSG.isNilpotent_of_le_centralizerOfChiefFactor
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (H : Subgroup G) (hH : H.Normal)
    (hcent : ∀ cf : ChiefFactor G, H ≤ centralizerOfChiefFactor (G := G) H cf) :
    Group.IsNilpotent H := by
  classical
  have hH_le_iInf :
      H ≤ ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf := by
    exact le_iInf hcent
  have hsInf_univ :
      sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) =
        ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf :=
    sInf_centralizerOfChiefFactor_univ_eq_iInf (G := G) (H := H)
  have hH_le_F : H ≤ fittingSubgroupOf (G := G) H := by
    have hprop := (proposition_1_2 (G := G) hsolv H hH).1
    calc
      H ≤ ⨅ cf : ChiefFactor G, centralizerOfChiefFactor (G := G) H cf := hH_le_iInf
      _ = sInf (centralizerOfChiefFactor (G := G) H '' (Set.univ : Set (ChiefFactor G))) := by
        rw [hsInf_univ]
      _ = fittingSubgroupOf (G := G) H := hprop.symm
  have hF_le_H : fittingSubgroupOf (G := G) H ≤ H := fittingSubgroupOf_le (G := G) H
  have hF_eq : fittingSubgroupOf (G := G) H = H := le_antisymm hF_le_H hH_le_F
  let e : fittingSubgroupOf (G := G) H ≃* H := MulEquiv.subgroupCongr hF_eq
  haveI : Group.IsNilpotent (fittingSubgroupOf (G := G) H) :=
    fittingSubgroupOf_isNilpotent (G := G) H
  exact Group.nilpotent_of_mulEquiv e
