module

public import CFSG.Milestones.ASVolI.F411.SwapRed
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data
public import CFSG.RankThree.PartTwo.KFacts.AutG2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.RankThree.PartTwo.KFacts

theorem burnsideF411a_inner_of_borel {Y : Type*} [Group Y] {U H : Subgroup Y}
    {F : Subgroup (MulAut Y)}
    (hnf : ∀ α : MulAut Y, (∀ x : Y, α x ∈ U ↔ x ∈ U) →
      ∃ g ∈ Subgroup.normalizer (U : Set Y), ∃ σ ∈ F, α = MulAut.conj g * σ)
    (hBeq : ∀ g ∈ Subgroup.normalizer (U : Set Y), ∃ u ∈ U, ∃ h ∈ H, g = u * h)
    (hFH : ∀ σ ∈ F, ∀ h ∈ H, σ h ∈ H) (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hHU : H ≤ Subgroup.normalizer (U : Set Y)) (hUH : ∀ x ∈ U, x ∈ H → x = 1)
    (hFf : ∀ σ ∈ F, (∀ h ∈ H, σ h = h) → σ = 1)
    (β : MulAut Y) (h1 : ∀ x, β x ∈ U ↔ x ∈ U) (h2 : ∀ h ∈ H, β h * h⁻¹ ∈ U) :
    ∃ g : Y, β = MulAut.conj g := by
  obtain ⟨g, hg, τ, hτ, rfl⟩ := hnf β h1
  obtain ⟨u₀, hu₀, h₀, hh₀, rfl⟩ := hBeq g hg
  have hfix : ∀ h ∈ H, τ h = h := by
    intro h hh
    have hτh : τ h ∈ H := hFH τ hτ h hh
    have hc := h2 h hh
    rw [MulAut.mul_apply, MulAut.conj_apply] at hc
    have hcomm : h₀ * τ h = τ h * h₀ := hHc h₀ hh₀ (τ h) hτh
    have e1 : u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by
      calc u₀ * h₀ * τ h * (u₀ * h₀)⁻¹ * h⁻¹ = u₀ * (h₀ * τ h) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by group
        _ = u₀ * (τ h * h₀) * h₀⁻¹ * u₀⁻¹ * h⁻¹ := by rw [hcomm]
        _ = u₀ * τ h * u₀⁻¹ * h⁻¹ := by group
    rw [e1] at hc
    have hu1 : h * u₀ * h⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hHU hh) u₀).1 hu₀
    have hmem : τ h * h⁻¹ ∈ U := by
      have e2 : τ h * h⁻¹ = u₀⁻¹ * (u₀ * τ h * u₀⁻¹ * h⁻¹) * (h * u₀ * h⁻¹) := by group
      rw [e2]
      exact U.mul_mem (U.mul_mem (U.inv_mem hu₀) hc) hu1
    exact mul_inv_eq_one.1 (hUH _ hmem (H.mul_mem hτh (H.inv_mem hh)))
  rw [hFf τ hτ hfix, mul_one]
  exact ⟨u₀ * h₀, rfl⟩

theorem burnsideF411a_pCoreOf_map {G E : Type} [Group G] [Group E] {f : G →* E}
    (hf : Function.Injective f) (p : ℕ) (X : Subgroup G) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem burnsideF411a_conjNormal_injective {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hC : Subgroup.centralizer (Gp : Set E) = ⊥) :
    Function.Injective (MulAut.conjNormal : E →* MulAut ↥Gp) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨n, hn⟩ : ↥Gp) : E)) hx
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc n * x = (x * n * x⁻¹) * x := by rw [h1]
    _ = x * n := by group

section G2

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF411a_g2_F_U : ∀ σ ∈ (g2FieldHom K).range, ∀ x : ↥(adjointGroup Tag.G2 K),
    σ x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K := by
  rintro _ ⟨σ, rfl⟩ x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_g2FieldHom]
  exact entrywise_mem_posUnipotent_iff σ x.1

theorem burnsideF411a_g2_F_H : ∀ σ ∈ (g2FieldHom K).range, ∀ h ∈ torusSub Tag.G2 K,
    σ h ∈ torusSub Tag.G2 K := by
  rintro _ ⟨σ, rfl⟩ h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [coe_g2FieldHom]
  exact entrywise_mem_torusGroup σ hh

theorem burnsideF411a_g2_H_comm : ∀ a ∈ torusSub Tag.G2 K, ∀ b ∈ torusSub Tag.G2 K,
    a * b = b * a := by
  intro a ha b hb
  exact Subtype.ext ((triangular_borel_structure.{0, 0} Tag.G2 K).1 a.1 ha b.1 hb)

theorem burnsideF411a_g2_H_le : torusSub Tag.G2 K ≤ Subgroup.normalizer
    ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have := Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_posUnipotent hh) u.1
  exact this

theorem burnsideF411a_g2_U_inf_H : ∀ x ∈ posUnipotentSub Tag.G2 K, x ∈ torusSub Tag.G2 K →
    x = 1 := by
  intro x hx hxH
  have : x ∈ posUnipotentSub Tag.G2 K ⊓ torusSub Tag.G2 K := ⟨hx, hxH⟩
  rw [posUnipotentSub_inf_torusSub] at this
  exact Subgroup.mem_bot.mp this

theorem burnsideF411a_g2_B_eq : ∀ g ∈ Subgroup.normalizer
    ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)), ∃ u ∈ posUnipotentSub Tag.G2 K,
        ∃ h ∈ torusSub Tag.G2 K, g = u * h := by
  intro g hg
  rw [normalizer_subgroupOf_eq' posUnipotent_le_adjointGroup,
    (borel_self_normalizers Tag.G2 K).1] at hg
  have hg' : g ∈ (borelSub Tag.G2 K : Set ↥(adjointGroup Tag.G2 K)) := hg
  rw [borelSub_eq_mul, borelSub_inf_monomialSub] at hg'
  obtain ⟨u, hu, h, hh, rfl⟩ := hg'
  exact ⟨u, hu, h, hh, rfl⟩

theorem burnsideF411a_g2_F_faithful : ∀ σ ∈ (g2FieldHom K).range,
    (∀ h ∈ torusSub Tag.G2 K, σ h = h) → σ = 1 := by
  rintro _ ⟨σ₀, rfl⟩ hfix
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
  have key : ∀ a : Fin Tag.G2.rank → Kˣ,
      (fun i => Units.map σ₀.toRingHom.toMonoidHom (a i)) = a := by
    intro a
    obtain ⟨-, hT, hC, -⟩ := hrest B hB a
    have hd : (⟨rootDiagUnit Tag.G2 a, hC⟩ : ↥(adjointGroup Tag.G2 K)) ∈ torusSub Tag.G2 K := hT
    have h1 := congrArg (fun x : ↥(adjointGroup Tag.G2 K) => (x : ModGL Tag.G2 K))
      (hfix _ hd)
    simp only [coe_g2FieldHom, entrywise_rootDiagUnit] at h1
    apply rootDiagAutHom_injective (τ := Tag.G2) (K := K)
    refine MulEquiv.ext fun g => Subtype.ext ?_
    show ((rootDiagAut Tag.G2 K _ g : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      ((rootDiagAut Tag.G2 K a g : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K)
    rw [coe_rootDiagAut, coe_rootDiagAut, h1]
  have hu : ∀ u : Kˣ, σ₀ (u : K) = u := by
    intro u
    have := congrFun (key fun _ => u) ⟨0, by decide⟩
    simpa using congrArg Units.val this
  have hσ : σ₀ = 1 := by
    refine RingEquiv.ext fun c => ?_
    by_cases hc : c = 0
    · subst hc
      simp
    · exact hu (Units.mk0 c hc)
  rw [hσ, map_one]

variable [Finite K]

theorem burnsideF411a_g2_normal_form (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (α : MulAut ↥(adjointGroup Tag.G2 K))
    (hα : ∀ x, α x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K) :
    ∃ g ∈ Subgroup.normalizer ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K)), ∃ σ ∈ (g2FieldHom K).range, α = MulAut.conj g * σ := by
  obtain ⟨g, σ₀, hα'⟩ := (g2_automorphism_normal_form hK3 hK4).1 α
  refine ⟨g, ?_, g2FieldHom K σ₀, ⟨σ₀, rfl⟩, hα'⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : (MulAut.conj g) y = α ((g2FieldHom K σ₀)⁻¹ y) := by
    rw [hα', MulAut.mul_apply, MulAut.apply_inv_self]
  have h1 := hα ((g2FieldHom K σ₀)⁻¹ y)
  have h2 := burnsideF411a_g2_F_U (g2FieldHom K σ₀) ⟨σ₀, rfl⟩ ((g2FieldHom K σ₀)⁻¹ y)
  rw [MulAut.apply_inv_self] at h2
  rw [← MulAut.conj_apply, e, h1]
  exact h2

theorem burnsideF411a_g2_inner_of_borel (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (β : MulAut ↥(adjointGroup Tag.G2 K))
    (h1 : ∀ x, β x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K)
    (h2 : ∀ h ∈ torusSub Tag.G2 K, β h * h⁻¹ ∈ posUnipotentSub Tag.G2 K) :
    ∃ g : ↥(adjointGroup Tag.G2 K), β = MulAut.conj g :=
  burnsideF411a_inner_of_borel (burnsideF411a_g2_normal_form hK3 hK4) burnsideF411a_g2_B_eq
    burnsideF411a_g2_F_H burnsideF411a_g2_H_comm burnsideF411a_g2_H_le burnsideF411a_g2_U_inf_H
    burnsideF411a_g2_F_faithful β h1 h2

theorem burnsideF411a_g2_pCoreOf_borelSub (p : ℕ) [Fact p.Prime] [CharP K p] :
    pCoreOf p (borelSub Tag.G2 K) = posUnipotentSub Tag.G2 K := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
  obtain ⟨P, hP⟩ := (exceptional_ordinary_Sylow_opposition Tag.G2 K p w₀ hw₀).1
  have hUB : posUnipotentSub Tag.G2 K ≤ borelSub Tag.G2 K := posUnipotentSub_le_borelSub
  have hBN : borelSub Tag.G2 K ≤ Subgroup.normalizer
      ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
        Set ↥(adjointGroup Tag.G2 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1 normal_posUnipotentSub
  have hUp : IsPGroup p (posUnipotentSub Tag.G2 K) := by
    have h := P.isPGroup'
    rw [hP] at h
    exact h
  apply le_antisymm
  · have hp : IsPGroup p ((posUnipotentSub Tag.G2 K ⊔ pCoreOf p (borelSub Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K))) :=
      IsPGroup.to_sup_of_normal_left' hUp (burnsideF411_pCoreOf_isPGroup _)
        ((burnsideF411_pCoreOf_le _).trans hBN)
    have heq : (posUnipotentSub Tag.G2 K ⊔ pCoreOf p (borelSub Tag.G2 K) :
        Subgroup ↥(adjointGroup Tag.G2 K)) = P :=
      P.is_maximal' hp (by rw [hP]; exact le_sup_left)
    rw [hP] at heq
    calc pCoreOf p (borelSub Tag.G2 K)
        ≤ posUnipotentSub Tag.G2 K ⊔ pCoreOf p (borelSub Tag.G2 K) := le_sup_right
      _ = posUnipotentSub Tag.G2 K := heq
  · exact burnsideF411_le_pCoreOf hUB hBN hUp

theorem burnsideF411a_g2_key {E : Type} [Group E] {p : ℕ} {Gp M₁ M₂ : Subgroup E}
    (hN : Gp.Normal) (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) (χ : ↥(adjointGroup Tag.G2 K) ≃* ↥Gp)
    (hB : Gp ⊓ (M₁ ⊓ M₂) = (borelSub Tag.G2 K).map (Gp.subtype.comp χ.toMonoidHom))
    (hU : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) =
      (posUnipotentSub Tag.G2 K).map (Gp.subtype.comp χ.toMonoidHom)) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ (p ^ k) = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hN
  intro r hr _ _ hcomm
  set ι : ↥(adjointGroup Tag.G2 K) →* E := Gp.subtype.comp χ.toMonoidHom with hιdef
  have hι : Function.Injective ι := Gp.subtype_injective.comp χ.injective
  have hrN : r ∈ Subgroup.normalizer (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) : Set E) :=
    burnsideF411_le_normalizer_pCoreOf_inf p hN (M₁ ⊓ M₂) hr
  set β : MulAut ↥(adjointGroup Tag.G2 K) := (MulAut.congr χ).symm (MulAut.conjNormal r)
    with hβdef
  have hβ : ∀ x, ι (β x) = r * ι x * r⁻¹ := by
    intro x
    simp [hβdef, hιdef, MulAut.congr_symm_apply, MulAut.conjNormal_apply]
  have hmemU : ∀ x, x ∈ posUnipotentSub Tag.G2 K ↔ ι x ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hU]
    exact (Subgroup.mem_map_iff_mem hι).symm
  have h1 : ∀ x, β x ∈ posUnipotentSub Tag.G2 K ↔ x ∈ posUnipotentSub Tag.G2 K := by
    intro x
    rw [hmemU, hmemU, hβ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (ι x)).symm
  have h2 : ∀ h ∈ torusSub Tag.G2 K, β h * h⁻¹ ∈ posUnipotentSub Tag.G2 K := by
    intro h hh
    rw [hmemU, map_mul, map_inv, hβ]
    have hb : ι h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hB]
      exact ⟨h, Subgroup.subgroupOf_mono _ torusGroup_le_borelGroup hh, rfl⟩
    exact hcomm (ι h) hb
  obtain ⟨g, hg⟩ := burnsideF411a_g2_inner_of_borel hK3 hK4 β h1 h2
  have hrg : (MulAut.conjNormal r : MulAut ↥Gp) = MulAut.conjNormal ((χ g : ↥Gp) : E) := by
    rw [MulAut.conjNormal_val]
    have e1 : (MulAut.conjNormal r : MulAut ↥Gp) = MulAut.congr χ β := by
      rw [hβdef, MulEquiv.apply_symm_apply]
    rw [e1, hg]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [burnsideF411a_conjNormal_injective hC hrg]
  exact (χ g).2

end G2

end CFSG.ASVolI
