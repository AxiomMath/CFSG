module

public import CFSG.Quasithin.MS93.S37Loc

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] {α : ↥L →* ↥(StatedSp 2 F)} (hsurj : Function.Surjective α)
  (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
    α false 1)
include h hsurj hnat

theorem kerL_le_centralizer (hVU : Vq M L = Uq M T L) {y : ↥L} (hy : α y = 1) :
    (y : G) ∈ Subgroup.centralizer (Uq M T L : Set G) := by
  have hyQ := mem_pCoreOf_of_alpha_eq_one (Sp4NatData.ofIsSum hsurj hnat) h hVU y.2
    (by rw [Sp4NatData.ofIsSum_α]; exact hy)
  exact Subgroup.centralizer_le (Uq_le_Z0q h.L_le) (h.pCoreOf_le_centralizer_Z0q hyQ)

theorem exists_piL (hVU : Vq M L = Uq M T L) :
    ∃ π : ↥(StatedSp 2 F) →* ↥(autOn L (Uq M T L)), Function.Surjective π ∧
    ∀ m : ↥L, ((π (α m) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨m, hnat.1 m.2⟩ := by
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := hnat.1
  let χ : ↥L →* ↥(autOn L (Uq M T L)) :=
    ((conjAct (Uq M T L)).comp (Subgroup.inclusion hLU)).codRestrict (autOn L (Uq M T L))
      (fun m => Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hLU m, m.2, rfl⟩)
  have hker : α.ker ≤ χ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct (Uq M T L) (Subgroup.inclusion hLU m) = 1
    apply InternalSec.conjAct_eq_one_of_mem_centralizer
    exact kerL_le_centralizer h hsurj hnat hVU hm
  let π := (QuotientGroup.lift α.ker χ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm.toMonoidHom
  have hπa : ∀ m, π (α m) = χ m := by
    intro m
    have e : (QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α m) =
        QuotientGroup.mk m := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift α.ker χ hker
      ((QuotientGroup.quotientKerEquivOfSurjective α hsurj).symm (α m)) = χ m
    rw [e, QuotientGroup.lift_mk]
  refine ⟨π, fun x => ?_, fun m => by rw [hπa]; rfl⟩
  obtain ⟨g, hgL, hgx⟩ := Setup.mem_autOn_iff.1 x.2
  refine ⟨α ⟨g, hgL⟩, ?_⟩
  rw [hπa]
  apply Subtype.ext
  rw [← hgx]
  rfl

omit h [Finite G] in
theorem realizesVia_natL [IsMulCommutative ↥(Uq M T L)]
    {π : ↥(StatedSp 2 F) →* ↥(autOn L (Uq M T L))} (hπs : Function.Surjective π)
    (hπa : ∀ m : ↥L, ((π (α m) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨m, hnat.1 m.2⟩) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia (autOn L (Uq M T L)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) π := by
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := hnat.1
  obtain ⟨-, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := id hnat
  let β₁ : ↥(Uq M T L) →* Multiplicative (Fin 2 ⊕ Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0)
      map_one' := by simp
      map_mul' := fun u v => by simp }
  have hβ₁ : ∀ u, β₁ u = Multiplicative.ofAdd (Multiplicative.toAdd (β₀ u) 0) := fun _ => rfl
  have hβ₁s : Function.Surjective β₁ := by
    intro x
    obtain ⟨u, hu⟩ := hβ₀s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd x)
    exact ⟨u, by rw [hβ₁, hu]; rfl⟩
  have hβ₁k : ∀ u, β₁ u = 1 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro u
    have e1 : β₁ u = 1 ↔ β₀ u = 1 := by
      constructor
      · intro h1
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        exact congrArg Multiplicative.toAdd h1
      · intro h1
        rw [hβ₁, h1]
        rfl
    rw [e1, ← MonoidHom.mem_ker, hβ₀k, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hβ₁e : ∀ (m : ↥L) (u v : ↥(Uq M T L)), (v : G) = m * u * m⁻¹ →
      β₁ v = Multiplicative.ofAdd ((((α m : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β₁ u)) := by
    intro m u v huv
    have := hβ₀e m u v huv 0
    rw [hβ₁, hβ₁, this]
    simp [moduleAct]
  have hY : L ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hLU (le_normalizer_centralizer Subgroup.le_normalizer)
  have hstab := InternalSec.autOn_le_stabSub hY
  refine ⟨hπs, le_top, bot_le, fun _ _ _ => Subgroup.mem_top _, fun x z hz => (hstab x.2 z).2 hz,
    (FFModel.nat_isActionModel _).sec_inv, (FFModel.nat_isActionModel _).ker_inv, ?_⟩
  let β : ↥(⊤ : Subgroup ↥(Uq M T L)) →* (FFModel.nat (StatedSp 2 F)).Sec :=
    (QuotientGroup.mk' _).comp
      (Subgroup.topEquiv.symm.toMonoidHom.comp (β₁.comp (⊤ : Subgroup ↥(Uq M T L)).subtype))
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥(Uq M T L)),
      β u = QuotientGroup.mk ⟨β₁ u, Subgroup.mem_top _⟩ := fun _ => rfl
  refine ⟨β, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨⟨x, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hβ₁s x
    exact ⟨⟨u, Subgroup.mem_top _⟩, by rw [hβ]; congr 1; exact Subtype.ext hu⟩
  · rw [hβ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show β₁ u ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → F))) ↔ _
    rw [Subgroup.mem_bot, hβ₁k, Subgroup.mem_subgroupOf]
  · rw [hβ] at hum ⊢
    have h3 : (⟨β₁ u, Subgroup.mem_top _⟩ : ↥(FFModel.nat (StatedSp 2 F)).sec) = m := by
      have h1 := QuotientGroup.eq.1 hum
      exact inv_mul_eq_one.1 (Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)))
    subst h3
    congr 1
    apply Subtype.ext
    obtain ⟨m₀, rfl⟩ := hsurj γ
    have hval : ((((π (α m₀) : ↥(autOn L (Uq M T L))) : MulAut ↥(Uq M T L))
        (u : ↥(Uq M T L)) : ↥(Uq M T L)) : G) =
          (m₀ : G) * ((u : ↥(Uq M T L)) : G) * (m₀ : G)⁻¹ := by
      rw [hπa]
      exact InternalSec.coe_conjAct_apply _ _
    exact hβ₁e m₀ (u : ↥(Uq M T L)) _ hval

theorem lift_L [Fintype F] (hVU : Vq M L = Uq M T L) {k : ℕ} (hk : 1 ≤ k)
    (hF : Fintype.card F = 2 ^ k) :
    Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ k ∧
      ∀ l ∈ L, ∀ u ∈ Uq M T L, l * u * l⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
        l * u * l⁻¹ = u := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hF]
  have := Sp4L.isMulCommutative_uq h
  have hLU : L ≤ Subgroup.normalizer (Uq M T L : Set G) := hnat.1
  obtain ⟨π, hπs, hπa⟩ := exists_piL h hsurj hnat hVU
  have hreal := realizesVia_natL hsurj hnat hπs hπa
  have hV : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hcommL : commV (autOn L (Uq M T L)) = ⊤ :=
    InternalSec.commV_autOn_eq_top hLU h.commutator_uq
  have hCL : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn L (Uq M T L)) := InternalSec.le_fixV_autOn inf_le_right
  obtain ⟨hcardC, hlift⟩ := Sp4L.lift_of_realizes hFn hk hV hCL hcommL hreal
  refine ⟨?_, ?_⟩
  · have e : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) =
        Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective (Uq M T L).subtype_injective]
    rw [← e]
    exact hcardC
  · intro m hm u hu hmu
    have hx : conjAct (Uq M T L) ⟨m, hLU hm⟩ ∈ autOn L (Uq M T L) :=
      Setup.mem_autOn_iff.2 ⟨⟨m, hLU hm⟩, hm, rfl⟩
    have hval : ((conjAct (Uq M T L) ⟨m, hLU hm⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) = m * u * m⁻¹ :=
      InternalSec.coe_conjAct_apply _ _
    have hxw : conjAct (Uq M T L) ⟨m, hLU hm⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈
        (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
      rw [Subgroup.mem_subgroupOf]
      show ((conjAct (Uq M T L) ⟨m, hLU hm⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) * u⁻¹ ∈ _
      rw [hval]
      exact hmu
    have := hlift _ hx ⟨u, hu⟩ hxw
    rw [← hval, this]

end CFSG.Quasithin.MS93.S37
