module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem mem_of_tv_mem {F : Type} [Field F] (ψ : SpecialLinearGroup (Fin 3) F →* G)
    {H : Subgroup G} (h01 : ∀ c : F, ψ (tv 0 1 c) ∈ H) (h10 : ∀ c : F, ψ (tv 1 0 c) ∈ H)
    (h12 : ∀ c : F, ψ (tv 1 2 c) ∈ H) (h21 : ∀ c : F, ψ (tv 2 1 c) ∈ H)
    (x : SpecialLinearGroup (Fin 3) F) : ψ x ∈ H := by
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) ≤ H.comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    have hcomm : ∀ {a b : SpecialLinearGroup (Fin 3) F}, ψ a ∈ H → ψ b ∈ H → ψ ⁅a, b⁆ ∈ H :=
      fun ha hb => by
        rw [map_commutatorElement, commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    show ψ _ ∈ H
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [← tv_of_ne]; exact h01 c
    · have e := SpecialLinearGroup.commutatorElement_transvection
        (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide) hij c 1
      rw [mul_one] at e
      rw [← e]
      exact hcomm (by rw [← tv_of_ne]; exact h01 c) (by rw [← tv_of_ne]; exact h12 1)
    · rw [← tv_of_ne]; exact h10 c
    · exact absurd rfl hij
    · rw [← tv_of_ne]; exact h12 c
    · have e := SpecialLinearGroup.commutatorElement_transvection
        (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide) hij c 1
      rw [mul_one] at e
      rw [← e]
      exact hcomm (by rw [← tv_of_ne]; exact h21 c) (by rw [← tv_of_ne]; exact h10 1)
    · rw [← tv_of_ne]; exact h21 c
    · exact absurd rfl hij
  have hx : x ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    trivial
  exact hle hx

theorem commuting_subgroupOf {H X Y : Subgroup G} (h : Commuting X Y) :
    Commuting (X.subgroupOf H) (Y.subgroupOf H) := fun x hx y hy =>
  Subtype.ext (h x (Subgroup.mem_subgroupOf.1 hx) y (Subgroup.mem_subgroupOf.1 hy))

theorem _root_.CFSG.Timmesfeld.ARS.IsConfig.exists_hom_A [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {m : ℕ} (hm : 3 ≤ m) {A B : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) A B) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G,
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          B k) ∧ Ψ.range = ⨆ k, (A k ⊔ B k) ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  set H := ⨆ k, (A k ⊔ B k) with hH
  have hAH : ∀ k, A k ≤ H := fun k => le_sup_left.trans (le_iSup (fun k => A k ⊔ B k) k)
  have hBH : ∀ k, B k ≤ H := fun k => le_sup_right.trans (le_iSup (fun k => A k ⊔ B k) k)
  have hρH : ∀ k x, ρ k x ∈ H := by
    intro k x
    have hx : x ∈ upperUnipotent F ⊔ lowerUnipotent F := by
      rw [NaturalModule.upperUnipotent_sup_lowerUnipotent]
      trivial
    have hmem : ρ k x ∈ (upperUnipotent F ⊔ lowerUnipotent F).map (ρ k) := ⟨x, hx, rfl⟩
    rw [Subgroup.map_sup, (hρ k).2.1, (hρ k).2.2] at hmem
    exact sup_le (hAH k) (hBH k) hmem
  let ρ' : Fin m → SpecialLinearGroup (Fin 2) F →* H := fun k => (ρ k).codRestrict H (hρH k)
  have hcomp : ∀ k, H.subtype.comp (ρ' k) = ρ k := fun k => MonoidHom.ext fun _ => rfl
  have hρ' : ∀ k, (upperUnipotent F).map (ρ' k) = (A k).subgroupOf H ∧
      (lowerUnipotent F).map (ρ' k) = (B k).subgroupOf H := by
    intro k
    refine ⟨Subgroup.map_injective H.subtype_injective ?_,
      Subgroup.map_injective H.subtype_injective ?_⟩
    · rw [Subgroup.map_map, hcomp, Subgroup.map_subgroupOf_eq_of_le (hAH k)]
      exact (hρ k).2.1
    · rw [Subgroup.map_map, hcomp, Subgroup.map_subgroupOf_eq_of_le (hBH k)]
      exact (hρ k).2.2
  have hedge' : ∀ i j, edgeA m i j → ∃ ψ : SpecialLinearGroup (Fin 3) F →* H, ∀ c,
      ψ (tv 0 1 c) = ρ' i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ' i (tv 1 0 c) ∧
      ψ (tv 1 2 c) = ρ' j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ' j (tv 1 0 c) := by
    intro i j hij
    obtain ⟨ψ, hψ⟩ := hedge i j hij
    have hψH : ∀ x, ψ x ∈ H := mem_of_tv_mem ψ (fun c => (hψ c).1 ▸ hρH i _)
      (fun c => (hψ c).2.1 ▸ hρH i _) (fun c => (hψ c).2.2.1 ▸ hρH j _)
      (fun c => (hψ c).2.2.2 ▸ hρH j _)
    exact ⟨ψ.codRestrict H hψH, fun c => ⟨Subtype.ext (hψ c).1, Subtype.ext (hψ c).2.1,
      Subtype.ext (hψ c).2.2.1, Subtype.ext (hψ c).2.2.2⟩⟩
  have hnonadj' : ∀ i j, i ≠ j → ¬ edgeA m i j → ¬ edgeA m j i →
      Commuting ((A i).subgroupOf H) ((A j).subgroupOf H) ∧
      Commuting ((A i).subgroupOf H) ((B j).subgroupOf H) ∧
      Commuting ((B i).subgroupOf H) ((A j).subgroupOf H) ∧
      Commuting ((B i).subgroupOf H) ((B j).subgroupOf H) := by
    intro i j hij h1 h2
    obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    exact ⟨commuting_subgroupOf c1, commuting_subgroupOf c2, commuting_subgroupOf c3,
      commuting_subgroupOf c4⟩
  have hgen' : ⨆ k, ((A k).subgroupOf H ⊔ (B k).subgroupOf H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hk : ∀ k, ((A k).subgroupOf H ⊔ (B k).subgroupOf H).map H.subtype = A k ⊔ B k :=
      fun k => by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hAH k),
          Subgroup.map_subgroupOf_eq_of_le (hBH k)]
    rw [iSup_congr hk]
  have hnt' : ∃ k, ∃ a ∈ (A k).subgroupOf H, a ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
    exact ⟨⟨0, by omega⟩, ⟨a, hAH _ ha⟩, Subgroup.mem_subgroupOf.2 ha,
      fun e => ha1 (congrArg Subtype.val e)⟩
  obtain ⟨Ψ', hΨA, hΨB, hsurj, hker⟩ := exists_surjective_of_rho
    (D := SpecialLinear.rootDatum m F)
    (CurtisTits.curtisTitsConclusion_specialLinear
      ⟨Nat.prime_two, hf, by omega, fun h => by injection h; omega,
        fun h => by injection h; omega⟩ hF hm)
    (leviConePresented_specialLinear m F) (simplyLacedLevis_specialLinear m F) hnonadj' ρ' hρ'
    hedge' hgen' hnt'
  refine ⟨f, hf, hcard, H.subtype.comp Ψ', fun k => ?_, fun k => ?_, ?_, ?_⟩
  · rw [← Subgroup.map_map, hΨA k, Subgroup.map_subgroupOf_eq_of_le (hAH k)]
  · rw [← Subgroup.map_map, hΨB k, Subgroup.map_subgroupOf_eq_of_le (hBH k)]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · intro x hx
    refine hker ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact H.subtype_injective (by rw [map_one]; exact hx)

omit [Group G] in
theorem center_SL4_eq_bot (f : ℕ) :
    Subgroup.center (SpecialLinearGroup (Fin 4) (GaloisField 2 f)) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h1 : (r - 1) ^ (2 ^ 2) = 0 := by
    rw [sub_pow_char_pow, one_pow]
    norm_num [hr]
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

theorem _root_.CFSG.Timmesfeld.ARS.IsConfig.exists_injective_A3 [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {A B : Fin 3 → Subgroup G} (hX : IsConfig R (edgeA 3) A B) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G, Function.Injective Ψ ∧
        (∀ k, ((SpecialLinear.rootDatum 3 (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((SpecialLinear.rootDatum 3 (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          B k) ∧ Ψ.range = ⨆ k, (A k ⊔ B k) := by
  obtain ⟨f, hf, hcard, Ψ, hΨA, hΨB, hrange, hker⟩ := hX.exists_hom_A hR hiso le_rfl
  refine ⟨f, hf, hcard, Ψ, (MonoidHom.ker_eq_bot_iff Ψ).1 (eq_bot_iff.2 ?_), hΨA, hΨB, hrange⟩
  rw [← center_SL4_eq_bot f]
  exact hker

end CaseB

end CFSG.Timmesfeld.ARS
