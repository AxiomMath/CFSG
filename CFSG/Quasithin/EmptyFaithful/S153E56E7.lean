module

public import CFSG.Quasithin.EmptyFaithful.S153E56E2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E56e

open CFSG.Quasithin.S153E

section Count

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem centerOf_U (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hU : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc)) :
    centerOf (UH153 T M V₁ Mc) = quasithinOmegaOneCenter T := by
  have hc : Subgroup.center ↥(UH153 T M V₁ Mc) =
      (quasithinOmegaOneCenter T).subgroupOf (UH153 T M V₁ Mc) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro g'
      have hu' : (g' : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
        U_le_centralizer_Z cx g'.2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hu' x hx).symm
    · rw [@CFSG.IsExtraspecial.center_order_p 2 ↥(UH153 T M V₁ Mc) _ hU,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_U cx)).toEquiv]
      exact cx.c.hyp.lemma_15_3_2_two.2.ge
  apply le_antisymm
  · intro u hu
    have hmem : (⟨u, hu.1⟩ : ↥(UH153 T M V₁ Mc)) ∈ Subgroup.center ↥(UH153 T M V₁ Mc) := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hu.2 g' g'.2)
    rw [hc, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  · intro z hz
    refine ⟨Z_le_U cx hz, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (U_le_centralizer_Z cx hu) z hz).symm

theorem Z_le_V (cx : Ctx15350 T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ VZ T M :=
  cx.c.hyp.Z_le_VZ

theorem card_Z' (cx : Ctx15350 T Mc M V₁ V₂ t) (y : G) :
    Nat.card (conjSubgroup (quasithinOmegaOneCenter T) y) = 2 := by
  rw [card_conjSubgroup]
  exact S153E57.Z_card cx

theorem index_F (H : Hyps56 cx N₁ N₂ g s y) :
    (Fgp153 T M V₁ Mc y).relIndex (UH153 T M V₁ Mc) = 2 := by
  obtain ⟨z, hz⟩ := exists_ZGen cx
  have hV := cx.c.hyp.elemAbelian
  have hcenter := centerOf_U cx H.c.h55.1
  have hY : IsElemAbelian 2 (conjSubgroup (quasithinOmegaOneCenter T) y) :=
    isElemAbelian_of_card_eq_two (card_Z' cx y)
  have hcomm : ⁅UH153 T M V₁ Mc, conjSubgroup (quasithinOmegaOneCenter T) y⁆ ≤
      quasithinOmegaOneCenter T := by
    rw [Subgroup.commutator_le]
    intro u hu w hw
    exact commutator_U_mem cx hu (Z'_le_U H hw)
  have hCX : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (UH153 T M V₁ Mc : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp (U_le_centralizer_Z cx hu) x hx).symm
  have hCY : quasithinOmegaOneCenter T ≤
      Subgroup.centralizer (conjSubgroup (quasithinOmegaOneCenter T) y : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    exact B2F.isElemAbelian_comm hV (Z'_le_V H hw) (Z_le_V cx hx)
  have h := relIndex_eq_of_commutator_le hY (S153E57.Z_card cx) hcomm hCX hCY
  rw [← F_eq cx y] at h
  rw [h]
  have hbot : conjSubgroup (quasithinOmegaOneCenter T) y ⊓
      Subgroup.centralizer (UH153 T M V₁ Mc : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    rcases (hz.mem_conj_iff y).1 hx1 with h1 | h1
    · exact h1
    · exfalso
      have hxU : x ∈ UH153 T M V₁ Mc := Z'_le_U H hx1
      have hxc : x ∈ centerOf (UH153 T M V₁ Mc) := ⟨hxU, hx2⟩
      rw [hcenter] at hxc
      rcases hz.mem_Z_iff.1 hxc with h2 | h2
      · apply hz.ne
        have : y⁻¹ * z * y = 1 := by rw [← h1]; exact h2
        calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
          _ = 1 := by rw [this]; group
      · exact zp_ne H hz (h1.symm.trans h2)
  rw [hbot, Subgroup.relIndex_bot_left]
  exact card_Z' cx y

theorem card_F_eq (H : Hyps56 cx N₁ N₂ g s y) :
    Nat.card (Fgp153 T M V₁ Mc y) = 2 ^ (2 * s + 4) := by
  have hFU : Fgp153 T M V₁ Mc y ≤ UH153 T M V₁ Mc := by
    rw [F_eq cx y]
    exact inf_le_left
  have h := Subgroup.relIndex_mul_card (Fgp153 T M V₁ Mc y) (UH153 T M V₁ Mc)
  rw [inf_eq_left.2 hFU, index_F H, card_U H] at h
  have h2 : (2 : ℕ) ^ (2 * s + 5) = 2 * 2 ^ (2 * s + 4) := by ring
  rw [h2] at h
  omega

theorem commutator_U'_mem (cx : Ctx15350 T Mc M V₁ V₂ t) {u u' : G}
    (hu : u ∈ conjSubgroup (UH153 T M V₁ Mc) y) (hu' : u' ∈ conjSubgroup (UH153 T M V₁ Mc) y) :
    u * u' * u⁻¹ * u'⁻¹ ∈ conjSubgroup (quasithinOmegaOneCenter T) y := by
  rw [mem_conjSubgroup_iff] at hu hu' ⊢
  have := commutator_U_mem cx hu hu'
  have e1 : y * (u * u' * u⁻¹ * u'⁻¹) * y⁻¹ =
      (y * u * y⁻¹) * (y * u' * y⁻¹) * (y * u * y⁻¹)⁻¹ * (y * u' * y⁻¹)⁻¹ := by group
  rw [e1]
  exact this

theorem E_le_cent (H : Hyps56 cx N₁ N₂ g s y) :
    Egp153 T M V₁ Mc y ≤ conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G) :=
  le_inf (E_le_U' H) fun _ he => Subgroup.mem_centralizer_iff.2 fun _ he' => E_comm H he' he

theorem cent_E_card (H : Hyps56 cx N₁ N₂ g s y) :
    ∃ a : ℕ, a * 2 = Nat.card (Egp153 T M V₁ Mc y) ∧
      a * Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
        Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G)) = 2 ^ (2 * s + 5) := by
  have hcenter := centerOf_U cx H.c.h55.1
  have hEabel := isElemAbelian_E H
  have hcomm : ⁅conjSubgroup (UH153 T M V₁ Mc) y, Egp153 T M V₁ Mc y⁆ ≤
      conjSubgroup (quasithinOmegaOneCenter T) y := by
    rw [Subgroup.commutator_le]
    intro u hu e he
    exact commutator_U'_mem cx hu (E_le_U' H he)
  have hCX : conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Subgroup.centralizer (conjSubgroup (UH153 T M V₁ Mc) y : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp (U'_le_centralizer_Z' cx y hu) x hx).symm
  have hCY : conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    exact (Subgroup.mem_centralizer_iff.mp (U'_le_centralizer_Z' cx y (E_le_U' H he)) x hx).symm
  have h := relIndex_eq_of_commutator_le hEabel (card_Z' cx y) hcomm hCX hCY
  have hEC : Egp153 T M V₁ Mc y ⊓ Subgroup.centralizer (conjSubgroup (UH153 T M V₁ Mc) y : Set G) =
      conjSubgroup (quasithinOmegaOneCenter T) y := by
    apply le_antisymm
    · rintro e ⟨heE, heC⟩
      rw [mem_conjSubgroup_iff]
      have heU' := E_le_U' H heE
      rw [mem_conjSubgroup_iff] at heU'
      have hmem : y * e * y⁻¹ ∈ centerOf (UH153 T M V₁ Mc) := by
        refine ⟨heU', Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
        have hu' : y⁻¹ * u * y ∈ conjSubgroup (UH153 T M V₁ Mc) y := by
          rw [mem_conjSubgroup_iff]
          have e1 : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
          rw [e1]
          exact hu
        have h1 := Subgroup.mem_centralizer_iff.mp heC _ hu'
        calc u * (y * e * y⁻¹) = y * ((y⁻¹ * u * y) * e) * y⁻¹ := by group
          _ = y * (e * (y⁻¹ * u * y)) * y⁻¹ := by rw [h1]
          _ = (y * e * y⁻¹) * u := by group
      rw [hcenter] at hmem
      exact hmem
    · intro x hx
      exact ⟨Z'_le_E H hx, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (U'_le_centralizer_Z' cx y hu) x hx).symm⟩
  rw [hEC] at h
  have hZ'E : conjSubgroup (quasithinOmegaOneCenter T) y ≤ Egp153 T M V₁ Mc y := Z'_le_E H
  have e1 := Subgroup.relIndex_mul_card (conjSubgroup (quasithinOmegaOneCenter T) y)
    (Egp153 T M V₁ Mc y)
  rw [inf_eq_left.2 hZ'E, card_Z' cx y] at e1
  have e2 := Subgroup.relIndex_mul_card
    (conjSubgroup (UH153 T M V₁ Mc) y ⊓ Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G))
    (conjSubgroup (UH153 T M V₁ Mc) y)
  rw [inf_eq_left.2 inf_le_left, h, card_conjSubgroup, card_U H] at e2
  exact ⟨_, e1, e2⟩

theorem card_E_sq_le (H : Hyps56 cx N₁ N₂ g s y) :
    Nat.card (Egp153 T M V₁ Mc y) * Nat.card (Egp153 T M V₁ Mc y) ≤
      2 * 2 ^ (2 * s + 5) := by
  obtain ⟨a, hae, hac⟩ := cent_E_card H
  have e3 : Nat.card (Egp153 T M V₁ Mc y) ≤ Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
      Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G)) := Subgroup.card_le_of_le (E_le_cent H)
  calc Nat.card (Egp153 T M V₁ Mc y) * Nat.card (Egp153 T M V₁ Mc y)
      = (a * 2) * Nat.card (Egp153 T M V₁ Mc y) := by rw [hae]
    _ ≤ (a * 2) * Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
        Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G)) := Nat.mul_le_mul_left _ e3
    _ = 2 * (a * Nat.card ↥(conjSubgroup (UH153 T M V₁ Mc) y ⊓
        Subgroup.centralizer (Egp153 T M V₁ Mc y : Set G))) := by ring
    _ = 2 * 2 ^ (2 * s + 5) := by rw [hac]

end Count

end S153E56e

end CFSG.Quasithin
