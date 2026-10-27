module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIBase
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOffNatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

private theorem vtype_of_mem_nbrs_K {H M : Subgroup G} {u v : Geo H M} (h : v ∈ nbrs u) :
    vtype v = !vtype u := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
  cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all

omit [Finite G] in
private theorem isPGroup_of_elem {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsPGroup 2 E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

section Local

variable (F : Frame L1 L2 S D X)
include F

theorem relIndex_inf_Qv_le_four {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) {U : Subgroup G} (hU : U ≤ Qv δ) : (U ⊓ Qv x).relIndex U ≤ 4 := by
  have hA := Amal.of_frame F
  rw [Subgroup.inf_relIndex_left]
  have hn : Qv δ ≤ Subgroup.normalizer (Qv x : Set G) :=
    (hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ)).trans (le_normalizer_pCoreOf 2 (stab x))
  have h1 := F1.relIndex_sup_eq_of_le_normalizer hn
  have h2 := relIndex_Qv_sup_Qv F hx hδ
  rw [h1] at h2
  rw [← h2]
  exact Subgroup.relIndex_le_of_le_right hU (by rw [h2]; norm_num)

theorem ZFaithful_of_true (hT1 : ConfigT1 L1 L2 S) {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) : ZFaithful x := by
  rcases frame_dichotomy F x with h | h
  · have := (hT1 x).mp h; rw [hx] at this; exact absurd this (by decide)
  · exact h

end Local

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem natA_of_W_le (hW : ∀ μ ∈ nbrs α', Zv μ ≤ Qv β) :
    ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → NatA x := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hαβ : β ∈ nbrs α := hc.adj
  have hβα : α ∈ nbrs β := mem_nbrs_symm hαβ
  obtain ⟨μ, hμ, hA0μ⟩ := t1II_exists_nbr F hT1 hc hII
  have hμt : vtype μ = true := by rw [vtype_of_mem_nbrs_K hμ, hα']; rfl
  have hα'μ : α' ∈ nbrs μ := mem_nbrs_symm hμ
  set A0 : Subgroup G := Zv α ⊓ Qv α' with hA0
  have hZα2 := hA.isElemAbelian_Zv α
  have hZμ2 := hA.isElemAbelian_Zv μ
  have hZμβ : Zv μ ≤ Qv β := hW μ hμ
  have hZμα : Zv μ ≤ stab α := hZμβ.trans (hA.Qv_le_stab_of_mem_nbrs hβα)
  have hZαα' : Zv α ≤ stab α' := (hA.Zv_le_Vn hβα).trans hVβ
  have hfα := ZFaithful_of_true F hT1 hα
  have hfμ := ZFaithful_of_true F hT1 hμt
  obtain ⟨a, haA, haQ⟩ : ∃ a ∈ A0, a ∉ Qv μ := by
    by_contra h; push Not at h; exact hA0μ fun a ha => h a ha
  have haZ : a ∈ Zv α := (Subgroup.mem_inf.mp haA).1
  have haα' : a ∈ Qv α' := (Subgroup.mem_inf.mp haA).2
  have haμ : a ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hμ haα'
  have hQCμ : Qv μ ≤ Subgroup.centralizer (Zv μ : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hy).2 q hq).symm
  have hfaithμ := not_stab_le_centralizer_Zv F hT1 hμt
  have ha2 : a ^ 2 ^ 1 ∈ Qv μ := by rw [pow_one, hZα2.2 a haZ]; exact one_mem _
  have hN := four_le_relIndex_A F hμt hZμ2 (hA.stab_le_normalizer_Zv μ) hQCμ hfaithμ haμ haQ ha2
  have hle1 : Zv μ ⊓ Qv α ≤ Zv μ ⊓ Subgroup.centralizer {a} := by
    refine le_inf inf_le_left fun v hv => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α haZ).2 v
      (Subgroup.mem_inf.mp hv).2)
  have hp1 := Subgroup.relIndex_le_of_le_left (L := Zv μ) hle1 Subgroup.index_ne_zero_of_finite
  have hp2 := relIndex_inf_Qv_le_four F hα hαβ hZμβ
  have hp : (Zv μ ⊓ Qv α).relIndex (Zv μ) = 4 := by omega
  have hq4 := relIndex_inf_Qv_le_four F hμt hα'μ (show A0 ≤ Qv α' from inf_le_right)
  have hA02 : IsElemAbelian 2 A0 := ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (by
      have := congrArg Subtype.val (hZα2.1.is_comm.comm ⟨x, (Subgroup.mem_inf.mp x.2).1⟩
        ⟨y, (Subgroup.mem_inf.mp y.2).1⟩)
      exact this), fun x hx => hZα2.2 x (Subgroup.mem_inf.mp hx).1⟩
  have hidxα : A0.relIndex (Zv α) ≤ 2 := by
    have := relIndex_inf_Qv_le_two F hα' hZαα' hZα2
    exact this
  by_cases hq : (A0 ⊓ Qv μ).relIndex A0 ≤ 2
  ·
    have hle2 : A0 ⊓ Qv μ ≤ Zv α ⊓ Subgroup.centralizer (Zv μ : Set G) := by
      refine le_inf ((inf_le_left.trans inf_le_left)) fun v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ ht).2 v
        (Subgroup.mem_inf.mp hv).2).symm
    have hmul := Subgroup.relIndex_mul_relIndex (A0 ⊓ Qv μ) A0 (Zv α) inf_le_left inf_le_left
    have hidx : (Zv α ⊓ Subgroup.centralizer (Zv μ : Set G)).relIndex (Zv α) ≤
        (Zv μ ⊓ Qv α).relIndex (Zv μ) := by
      have h3 := Subgroup.relIndex_le_of_le_left (L := Zv α) hle2 Subgroup.index_ne_zero_of_finite
      rw [hp]
      have : (A0 ⊓ Qv μ).relIndex (Zv α) ≤ 4 := by
        rw [← hmul]; exact (Nat.mul_le_mul hq hidxα).trans (by norm_num)
      omega
    have hAnt : ∃ t ∈ Zv μ, ∃ v ∈ Zv α, t * v ≠ v * t := by
      by_contra h
      push Not at h
      have hle : Zv μ ≤ Qv α := hA.le_Qv_of_ZFaithful hfα hZμα (isPGroup_of_elem hZμ2)
        fun t ht => Subgroup.mem_centralizer_iff.mpr fun v hv => (h t ht v hv).symm
      have : (Zv μ ⊓ Qv α).relIndex (Zv μ) = 1 := by
        rw [inf_eq_left.mpr hle, Subgroup.relIndex_self]
      omega
    have hpg : IsPGroup 2 ((Zv μ).subgroupOf (stab α)) := (isPGroup_of_elem hZμ2).comap_subtype
    obtain ⟨hNα, -, -⟩ := H3_natA F hT1 hα hZμα hpg hAnt hidx
    exact fun x hx => hNα.of_vtype_eq (hα.trans hx.symm)
  ·
    have hq4' : (A0 ⊓ Qv μ).relIndex A0 = 4 := by
      have hd : (A0 ⊓ Qv μ).relIndex A0 ∣ Nat.card A0 := Subgroup.index_dvd_card _
      have : ∃ m, (A0 ⊓ Qv μ).relIndex A0 = 2 ^ m := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_elem hA02)
        rw [hk] at hd
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
        exact ⟨m, hm⟩
      obtain ⟨m, hm⟩ := this
      rw [hm] at hq4 hq ⊢
      have hm2 : m ≤ 2 := by
        by_contra h; push Not at h
        have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
        omega
      interval_cases m <;> simp_all
    have hidx : (Zv μ ⊓ Subgroup.centralizer (A0 : Set G)).relIndex (Zv μ) ≤
        (A0 ⊓ Qv μ).relIndex A0 := by
      have hle3 : Zv μ ⊓ Qv α ≤ Zv μ ⊓ Subgroup.centralizer (A0 : Set G) := by
        refine le_inf inf_le_left fun v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (Subgroup.mem_centralizer_iff.mp
          (hA.Zv_le_centerOf_Qv α (Subgroup.mem_inf.mp hw).1).2 v (Subgroup.mem_inf.mp hv).2).symm
      have h3 := Subgroup.relIndex_le_of_le_left (L := Zv μ) hle3 Subgroup.index_ne_zero_of_finite
      omega
    have hAμ : A0 ≤ stab μ := (inf_le_right : A0 ≤ Qv α').trans (hA.Qv_le_stab_of_mem_nbrs hμ)
    have hAnt : ∃ t ∈ A0, ∃ v ∈ Zv μ, t * v ≠ v * t := by
      by_contra h
      push Not at h
      have hle : A0 ≤ Qv μ := hA.le_Qv_of_ZFaithful hfμ hAμ (isPGroup_of_elem hA02)
        fun t ht => Subgroup.mem_centralizer_iff.mpr fun v hv => (h t ht v hv).symm
      exact hA0μ hle
    have hpg : IsPGroup 2 (A0.subgroupOf (stab μ)) := (isPGroup_of_elem hA02).comap_subtype
    obtain ⟨hNμ, -, -⟩ := H3_natA F hT1 hμt hAμ hpg hAnt hidx
    exact fun x hx => hNμ.of_vtype_eq (hμt.trans hx.symm)

end CaseII

end CFSG.Quasithin.Kleidman.F204
