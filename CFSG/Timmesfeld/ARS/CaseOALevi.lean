module

public import CFSG.Timmesfeld.ARS.CaseENatural
public import CFSG.Timmesfeld.ARS.CaseOAFrame
public import CFSG.Timmesfeld.ARS.Sec9Orbits

public section

open scoped commutatorElement
open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.LieType.Universal


namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA


section SL2

variable (F : Type) [Field F]

theorem rootGroup_SL2_single :
    (SpecialLinear.rootDatum 1 F).rootGroup (Pi.single (0 : Fin 1) 1) = upperUnipotent F := by
  change SpecialLinear.rootGroup 1 F (Pi.single 0 1) = upperUnipotent F
  have h01 : (0 : Fin (1 + 1)) ≠ 1 := by decide
  rw [SpecialLinear.rootGroup_eq 1 F h01 (by rw [SpecialLinear.toStd_single]; rfl)]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    rw [SpecialLinearGroup.transvectionHom_apply, ← CFSG.Timmesfeld.tv_of_ne h01]
    exact CFSG.Timmesfeld.ARS.Linear.tv_mem_upperUnipotent F _
  · intro hg
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).1 hg
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd, ← CFSG.Timmesfeld.tv_of_ne h01,
      CFSG.Timmesfeld.ARS.Linear.upperElt_eq_tv]

theorem rootGroup_SL2_neg_single :
    (SpecialLinear.rootDatum 1 F).rootGroup (-Pi.single (0 : Fin 1) 1) = lowerUnipotent F := by
  change SpecialLinear.rootGroup 1 F (-Pi.single 0 1) = lowerUnipotent F
  have h10 : (1 : Fin (1 + 1)) ≠ 0 := by decide
  rw [SpecialLinear.rootGroup_eq 1 F h10
    (by rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]; rfl)]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    rw [SpecialLinearGroup.transvectionHom_apply, ← CFSG.Timmesfeld.tv_of_ne h10]
    exact CFSG.Timmesfeld.ARS.Linear.tv_mem_lowerUnipotent F _
  · intro hg
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff F).1 hg
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd, ← CFSG.Timmesfeld.tv_of_ne h10,
      CFSG.Timmesfeld.ARS.Linear.lowerElt_eq_tv]

theorem eq_or_eq_neg_of_mem_roots_SL2 {γ : Fin 1 → ℤ}
    (hγ : γ ∈ (SpecialLinear.rootDatum 1 F).roots) : γ = Pi.single 0 1 ∨ γ = -Pi.single 0 1 := by
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots (SpecialLinear.isFiniteType_A 1) ∅ := hγ
  rw [SpecialLinear.roots_eq] at hγ'
  obtain ⟨i, j, hij, hγ''⟩ := hγ'
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · left
    apply SpecialLinear.toStd_injective 1
    rw [hγ'', SpecialLinear.toStd_single]
    rfl
  · right
    apply SpecialLinear.toStd_injective 1
    rw [hγ'', SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]
    rfl
  · exact absurd rfl hij

end SL2

section Levi

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne

theorem levi_eq_sup : levi R A A₀ = gen Δ₁ ⊔ gen Δ₂ := by
  refine le_antisymm (levi_le_sup_of_card_two h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne)
    (sup_le (Sec9.gen_le_levi fun _ hX => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX)
      (Sec9.gen_le_levi fun _ hX => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX))

theorem exists_eq_mul_of_mem_levi {v : G} (hv : v ∈ levi R A A₀) :
    ∃ v₁ ∈ gen Δ₁, ∃ v₂ ∈ gen Δ₂, v = v₁ * v₂ := by
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  have hle : gen Δ₁ ≤ Subgroup.normalizer ((gen Δ₂ : Subgroup G) : Set G) :=
    (commuting_iff_le_centralizer.1 hc.symm).trans (Subgroup.centralizer_le_normalizer _)
  rw [levi_eq_sup h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hv
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
  exact ⟨v₁, hv₁, v₂, hv₂, rfl⟩

theorem exists_compFrame_sl2 {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂)
    (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) :
    ∃ n : ℕ, ∃ Ψ : SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 n) →* G,
      CompFrame R A A₀ (SpecialLinear.rootDatum 1 (GaloisField 2 n))
        (SpecialLinear.weylRep 1 (GaloisField 2 n)) (SpecialLinear.torus 1 (GaloisField 2 n)) Ψ ∧
      (∀ g, Ψ g ∈ gen Δ₂) ∧ (∀ v ∈ gen Δ₂, ∃ g, Ψ g = v) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup
        (Pi.single (0 : Fin 1) 1)).map Ψ = P₂ ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup
        (-Pi.single (0 : Fin 1) 1)).map Ψ = Q₂ := by
  have := h.finite
  have hR := h.root
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  obtain ⟨n, -, -, φ, hφP, hφQ⟩ := hPQ₂.exists_mulEquiv_SL2' hR (hl₂ hP₂).1.1
  set Ψ : SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 n) →* G :=
    (P₂ ⊔ Q₂).subtype.comp φ.symm.toMonoidHom with hΨ
  have hback : ∀ {X : Subgroup G} {Y : Subgroup (SpecialLinearGroup (Fin 2) (GaloisField 2 n))},
      X ≤ P₂ ⊔ Q₂ → (X.subgroupOf (P₂ ⊔ Q₂)).map φ.toMonoidHom = Y → Y.map Ψ = X := by
    intro X Y hXL hXY
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    have hY : Y.map φ.symm.toMonoidHom = X.subgroupOf (P₂ ⊔ Q₂) := by
      rw [← hXY, Subgroup.map_map, e, Subgroup.map_id]
    rw [hΨ, ← Subgroup.map_map, hY, Subgroup.map_subgroupOf_eq_of_le hXL]
  have hPΨ : ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup
      (Pi.single (0 : Fin 1) 1)).map Ψ = P₂ := by
    rw [rootGroup_SL2_single]
    exact hback le_sup_left hφP
  have hQΨ : ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup
      (-Pi.single (0 : Fin 1) 1)).map Ψ = Q₂ := by
    rw [rootGroup_SL2_neg_single]
    exact hback le_sup_right hφQ
  have hrange : ∀ g, Ψ g ∈ gen Δ₂ := fun g => by
    rw [hgen₂]
    exact (φ.symm g).2
  have hsurj : ∀ v ∈ gen Δ₂, ∃ g, Ψ g = v := by
    intro v hv
    rw [hgen₂] at hv
    exact ⟨φ ⟨v, hv⟩, by simp [hΨ]⟩
  have hV₂ : gen Δ₂ ≤ levi R A A₀ :=
    Sec9.gen_le_levi fun _ hX => hl₂ hX
  have hct := SpecialLinear.isCTGroupDatum 1 (GaloisField 2 n)
  have hk : ∀ k : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 n)).rank,
      ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup (Pi.single k 1)).map Ψ = P₂ ∧
        ((SpecialLinear.rootDatum 1 (GaloisField 2 n)).rootGroup (-Pi.single k 1)).map Ψ = Q₂ := by
    intro k
    obtain rfl : k = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.1 k.2)
    exact ⟨hPΨ, hQΨ⟩
  refine ⟨n, Ψ, ⟨hct, SpecialLinear.steinbergExtras 1 (GaloisField 2 n), rfl, fun γ hγ => ?_,
    fun g => hV₂ (hrange g), fun v hv => ?_, fun k => ?_⟩, hrange, hsurj, hPΨ, hQΨ⟩
  · refine map_rootGroup_mem_leviSet hct hR rfl Ψ (fun g => hV₂ (hrange g)) (fun k => ?_) hγ
    rw [(hk k).1]
    exact hl₂ hP₂
  · obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_eq_mul_of_mem_levi h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hv
    obtain ⟨g, rfl⟩ := hsurj v₂ hv₂
    have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
    refine ⟨g, v₁, fun y => hc v₁ hv₁ _ (hrange y), ?_⟩
    exact (hc v₁ hv₁ _ (hrange g)).eq
  · rw [(hk k).1, (hk k).2]
    exact hPQ₂

end Levi

end CaseOA

end CFSG.Timmesfeld.ARS
