module

public import CFSG.Quasithin.MS93.M15Lift
public import CFSG.Quasithin.MS93.S4L5Flat

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Lift

variable (h : PUHyp M T L) {A : Subgroup G} (hAM : A ≤ M) {F : Type} [Field F]
  {φ : ↥A →* ↥(StatedSp 2 F)}
  (hnat : IsSumOfNaturalModulesVia A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
    φ false 1)
include h hAM hnat

theorem ker_le_centralizer_uq (x : ↥A) (hx : φ x = 1) :
    (x : G) ∈ Subgroup.centralizer (Uq M T L : Set G) := by
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hnat
  refine S34D.mem_centralizer_of_coord_id_sp h hβk (hAM x.2) (f := id) (fun u v huv => ?_)
    (fun _ => rfl)
  have := hβe x u v huv 0
  rw [hx] at this
  simpa [moduleAct] using this

theorem exists_pi_of_le (hsurj : Function.Surjective φ) :
    ∃ π : ↥(StatedSp 2 F) →* ↥(autOn A (Uq M T L)), Function.Surjective π ∧
    ∀ x : ↥A, ((π (φ x) : ↥(autOn A (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨x, le_normalizer_Uq h.le_normalizer (hAM x.2)⟩ := by
  have hAU : A ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hAM.trans (le_normalizer_Uq h.le_normalizer)
  let χ : ↥A →* ↥(autOn A (Uq M T L)) :=
    ((conjAct (Uq M T L)).comp (Subgroup.inclusion hAU)).codRestrict (autOn A (Uq M T L))
      (fun x => Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hAU x, x.2, rfl⟩)
  have hker : φ.ker ≤ χ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show conjAct (Uq M T L) (Subgroup.inclusion hAU x) = 1
    apply InternalSec.conjAct_eq_one_of_mem_centralizer
    exact ker_le_centralizer_uq h hAM hnat x hx
  let π := (QuotientGroup.lift φ.ker χ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.toMonoidHom
  have hπa : ∀ x, π (φ x) = χ x := by
    intro x
    have e : (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm (φ x) =
        QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift φ.ker χ hker
      ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm (φ x)) = χ x
    rw [e, QuotientGroup.lift_mk]
  refine ⟨π, fun y => ?_, fun x => by rw [hπa]; rfl⟩
  obtain ⟨g, hgA, hgy⟩ := Setup.mem_autOn_iff.1 y.2
  refine ⟨φ ⟨g, hgA⟩, ?_⟩
  rw [hπa]
  apply Subtype.ext
  rw [← hgy]
  rfl

theorem realizesVia_of_le (hsurj : Function.Surjective φ) [IsMulCommutative ↥(Uq M T L)]
    {π : ↥(StatedSp 2 F) →* ↥(autOn A (Uq M T L))} (hπs : Function.Surjective π)
    (hπa : ∀ x : ↥A, ((π (φ x) : ↥(autOn A (Uq M T L))) : MulAut ↥(Uq M T L)) =
      conjAct (Uq M T L) ⟨x, le_normalizer_Uq h.le_normalizer (hAM x.2)⟩) :
    (FFModel.nat (StatedSp 2 F)).RealizesVia (autOn A (Uq M T L)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L)) π := by
  obtain ⟨-, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hnat
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
  have hβ₁e : ∀ (x : ↥A) (u v : ↥(Uq M T L)), (v : G) = x * u * x⁻¹ →
      β₁ v = Multiplicative.ofAdd ((((φ x : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β₁ u)) := by
    intro x u v huv
    have := hβ₀e x u v huv 0
    rw [hβ₁, hβ₁, this]
    simp [moduleAct]
  have hY : A ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    hAM.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
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
    obtain ⟨x₀, rfl⟩ := hsurj γ
    have hval : ((((π (φ x₀) : ↥(autOn A (Uq M T L))) : MulAut ↥(Uq M T L))
        (u : ↥(Uq M T L)) : ↥(Uq M T L)) : G) =
        (x₀ : G) * ((u : ↥(Uq M T L)) : G) * (x₀ : G)⁻¹ := by
      rw [hπa]
      exact InternalSec.coe_conjAct_apply _ _
    exact hβ₁e x₀ (u : ↥(Uq M T L)) _ hval

theorem lift_of_le (hLA : L ≤ A)
    (hAC : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (A : Set G))
    (hsurj : Function.Surjective φ) [Fintype F] {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ k) {x : G} (hx : x ∈ A) {u : G} (hu : u ∈ Uq M T L)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) : x * u * x⁻¹ = u := by
  have := Sp4L.isMulCommutative_uq h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  have hAU : A ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hAM.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨π, hπs, hπa⟩ := exists_pi_of_le h hAM hnat hsurj
  have hreal := realizesVia_of_le h hAM hnat hsurj hπs hπa
  have hV : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hUA : ⁅Uq M T L, A⁆ = Uq M T L :=
    le_antisymm (commutator_le_left_of_le_normalizer hAU)
      (h.commutator_uq.symm.le.trans (Subgroup.commutator_mono le_rfl hLA))
  have hcomm := InternalSec.commV_autOn_eq_top hAU hUA
  have hCA : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn A (Uq M T L)) :=
    InternalSec.le_fixV_autOn hAC
  obtain ⟨-, hlift⟩ := Sp4L.lift_of_realizes hFn hk hV hCA hcomm hreal
  have hmem : conjAct (Uq M T L) ⟨x, hAU hx⟩ ∈ autOn A (Uq M T L) :=
    InternalSec.conjAct_mem_autOn hAU hx
  have hval : ((conjAct (Uq M T L) ⟨x, hAU hx⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) = x * u * x⁻¹ :=
    InternalSec.coe_conjAct_apply _ _
  have hz : conjAct (Uq M T L) ⟨x, hAU hx⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ ∈
      (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    rw [Subgroup.mem_subgroupOf]
    show ((conjAct (Uq M T L) ⟨x, hAU hx⟩ ⟨u, hu⟩ : ↥(Uq M T L)) : G) * u⁻¹ ∈ _
    rw [hval]
    exact hxu
  have := hlift _ hmem ⟨u, hu⟩ hz
  rw [← hval, this]

end Lift

theorem uq_inf_centralizer_le_centralizer_flat (h : PUHyp M T L) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) := by
  intro c hc
  have hle : L ⊔ pCoreOf 2 M ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun q hq => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.mem_centralizer_iff.mp (S34F.pCoreOf_le_centralizer_Uq h hq) c hc.1
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) c (Set.mem_singleton c)).symm

theorem lift_flat_sp (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hsurj : Function.Surjective φ)
    (hnat : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card F = 2 ^ k) {x : G} (hx : x ∈ L ⊔ pCoreOf 2 M)
    {u : G} (hu : u ∈ Uq M T L) (hxu : x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    x * u * x⁻¹ = u :=
  lift_of_le h (sup_le h.L_le (pCoreOf_le' M)) hnat le_sup_left
    (uq_inf_centralizer_le_centralizer_flat h) hsurj hk hcard hx hu hxu

theorem IsSp4UEven.lift_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) {x : G}
    (hx : x ∈ L ⊔ pCoreOf 2 M) {u : G} (hu : u ∈ Uq M T L)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) : x * u * x⁻¹ = u := by
  obtain ⟨m, F, _, _, φ, hm, hcard, hφs, hφ⟩ := IsSp4UEven.exists_natural_flat h hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  exact lift_flat_sp h hφs hφ (by omega) hcard' hx hu hxu

end CFSG.Quasithin.MS93.S4L
