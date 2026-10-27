module

public import CFSG.Walter.Cited.CentralSplit
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.A5S1517
public import CFSG.Quasithin.H13.NParamLiftS5
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open Equiv

@[expose] def c5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem c5_props : Perm.sign c5 = 1 ∧ c5 4 ≠ 4 := by decide

theorem InK4_iff_mem_v0list : ∀ σ : Perm (Fin 5), InK4 σ ↔ σ ∈ E1.LiftS5.v0list := by
  decide +kernel

theorem InK4_commutator_of_fix4 : ∀ σ τ : Perm (Fin 5), σ.sign = 1 → τ.sign = 1 → σ 4 = 4 →
    τ 4 = 4 → InK4 (σ * τ * σ⁻¹ * τ⁻¹) := by
  decide +kernel

theorem card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]; rfl

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem rho_four_of_mem_borel {x : G} (hx : x ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) :
    Set G)) : S.frame.ρ ⟨x, S.frame.L_le hx.1⟩ 4 = 4 := by
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hx.1
  have hsign : (S.frame.ρ ⟨x, hxN⟩).sign = 1 := (S.frame.image_L _).1 ⟨_, hx.1, rfl⟩
  refine fix4_of_normalizes_K4 _ hsign fun τ hτ => ?_
  obtain ⟨t, htTL, rfl⟩ := S.K4_TL τ hτ
  have hxt : x * t * x⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hx.2 t).mp htTL
  have hxtN : x * t * x⁻¹ ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hxt.1
  have := S.InK4_of_mem_TL ⟨_, hxtN⟩ hxt
  have e : (⟨x * t * x⁻¹, hxtN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨x, hxN⟩ * t * (⟨x, hxN⟩)⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_inv] at this

theorem mem_TL_of_InK4 {x : G} (hxL : x ∈ L)
    (hx : InK4 (S.frame.ρ ⟨x, S.frame.L_le hxL⟩)) : x ∈ T ⊓ L :=
  ⟨S.mem_T_of_InK4 ⟨x, S.frame.L_le hxL⟩ (Subgroup.mem_sup_left hxL) hx, hxL⟩

theorem rankOneAt_L : RankOneAt L (T ⊓ L) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    intro h
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L c5).2 c5_props.1
    have hgB : (g : G) ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [h]; exact hgL
    have h4 := S.rho_four_of_mem_borel hgB
    have e : (⟨(g : G), S.frame.L_le hgB.1⟩ : ↥(Subgroup.normalizer (V : Set G))) = g := rfl
    rw [e, hg] at h4
    exact c5_props.2 h4
  ·
    intro M hTM hML hMne
    set ρL : ↥L →* Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le) with hρL
    have hρL : ∀ (x : G) (hx : x ∈ L), ρL ⟨x, hx⟩ = S.frame.ρ ⟨x, S.frame.L_le hx⟩ :=
      fun _ _ => rfl
    set P : Subgroup (Perm (Fin 5)) := (M.subgroupOf L).map ρL with hPdef
    have hVP : E1.LiftS5.V0 ≤ P := by
      intro σ hσ
      have hσK : InK4 σ := (InK4_iff_mem_v0list σ).2 hσ
      obtain ⟨t, htTL, rfl⟩ := S.K4_TL σ hσK
      exact ⟨⟨(t : G), htTL.2⟩, hTM htTL, rfl⟩
    rcases E1.LiftS5.le_normalizer_or_alt_le E1.LiftS5.V0_le_alternatingGroup
      E1.LiftS5.card_V0 hVP with hN | hA
    · intro m hm
      refine E1.LiftS5.mem_normalizer_of_conj_le fun t ht => ?_
      have hmL : m ∈ L := hML hm
      have hρm : ρL ⟨m, hmL⟩ ∈ Subgroup.normalizer (E1.LiftS5.V0 : Set (Perm (Fin 5))) :=
        hN ⟨⟨m, hmL⟩, hm, rfl⟩
      have hmt : m * t * m⁻¹ ∈ L := L.mul_mem (L.mul_mem hmL ht.2) (L.inv_mem hmL)
      refine S.mem_TL_of_InK4 hmt ?_
      have h1 : InK4 (S.frame.ρ ⟨t, S.frame.L_le ht.2⟩) := S.InK4_of_mem_TL _ ht
      rw [InK4_iff_mem_v0list] at h1 ⊢
      have h2 := (Subgroup.mem_normalizer_iff.mp hρm (S.frame.ρ ⟨t, S.frame.L_le ht.2⟩)).mp
        (show _ ∈ E1.LiftS5.V0 from h1)
      have e : (⟨m * t * m⁻¹, S.frame.L_le hmt⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨m, S.frame.L_le hmL⟩ * ⟨t, S.frame.L_le ht.2⟩ * (⟨m, S.frame.L_le hmL⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact h2
    · exfalso
      apply hMne
      refine le_antisymm hML fun l hl => ?_
      have hsign : (S.frame.ρ ⟨l, S.frame.L_le hl⟩).sign = 1 :=
        (S.frame.image_L _).1 ⟨_, hl, rfl⟩
      obtain ⟨⟨m, hmL⟩, hm, hρ⟩ := hA (Perm.mem_alternatingGroup.mpr hsign)
      have hmM : m ∈ M := hm
      have hml : m⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hmL) hl
      have hker : InK4 (S.frame.ρ ⟨m⁻¹ * l, S.frame.L_le hml⟩) := by
        have e : (⟨m⁻¹ * l, S.frame.L_le hml⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            (⟨m, S.frame.L_le hmL⟩)⁻¹ * ⟨l, S.frame.L_le hl⟩ := rfl
        rw [e, map_mul, map_inv, ← hρL m hmL, hρ, inv_mul_cancel]
        exact Or.inl rfl
      have h1 := hTM (S.mem_TL_of_InK4 hml hker)
      have : l = m * (m⁻¹ * l) := by group
      rw [this]
      exact M.mul_mem hmM h1
  ·
    intro x hx y hy
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hx.1 hy.1) (L.inv_mem hx.1)) (L.inv_mem hy.1)
    refine S.mem_TL_of_InK4 hxy ?_
    have e : (⟨x * y * x⁻¹ * y⁻¹, S.frame.L_le hxy⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, S.frame.L_le hx.1⟩ * ⟨y, S.frame.L_le hy.1⟩ * (⟨x, S.frame.L_le hx.1⟩)⁻¹ *
          (⟨y, S.frame.L_le hy.1⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact InK4_commutator_of_fix4 _ _ ((S.frame.image_L _).1 ⟨_, hx.1, rfl⟩)
      ((S.frame.image_L _).1 ⟨_, hy.1, rfl⟩) (S.rho_four_of_mem_borel hx)
      (S.rho_four_of_mem_borel hy)

theorem isRankOneListed_L : IsRankOneListed (oTwoQuot ↥L) := by
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff L _).1 S.a5
  have hc : CFSG.pCore 2 ↥L = CFSG.Open.pCore 2 ↥L := CFSG.pCore_eq_open (↥L) 2
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨e'⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 card_alt_five
  refine Or.inl ⟨2, by norm_num, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans e).trans e'

end Setting

end CFSG.Quasithin.H13.A5
