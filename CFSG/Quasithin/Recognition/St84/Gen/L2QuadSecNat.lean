module

public import CFSG.CGT.Timmesfeld75.L2Defs
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
import CFSG.RankThree.GF2n.QuadraticSection
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
import CFSG.Quasithin.Background.Basic
import CFSG.Quasithin.Background.F1Amalgam
import CFSG.Quasithin.Background.F1Borel
import CFSG.Quasithin.Background.F2Equiv
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n (SectionModule exists_sectionModule)
open scoped Matrix MatrixGroups commutatorElement

section QuadSec

variable {G : Type} [Group G] {L Q Z : Subgroup G} {F : Type} [Field F] {α : ↥L →* SL(2, F)}

private theorem quadSec_conj_mem (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hQL : Q ≤ L) :
    ∀ a ∈ L, ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun a ha x hx =>
  (hker (⟨a, ha⟩ * ⟨x, hQL hx⟩ * (⟨a, ha⟩ : ↥L)⁻¹)).1 (by
    rw [map_mul, map_mul, (hker ⟨x, hQL hx⟩).2 hx, mul_one, map_inv, mul_inv_cancel])

private theorem quadSec_upperUnipotent_le_utri : CFSG.Timmesfeld.upperUnipotent F ≤ utri F :=
  (Subgroup.closure_le _).2 fun _ hg => mem_utri_iff_eq_unitri.2 hg

private theorem quadSec_exists_utri (hα : Function.Surjective α) {g : SL(2, F)}
    (hg : g ∈ CFSG.Timmesfeld.upperUnipotent F) : ∃ s : ↥L, α s = g ∧ α s ∈ utri F := by
  obtain ⟨s, rfl⟩ := hα g
  exact ⟨s, rfl, quadSec_upperUnipotent_le_utri hg⟩

private theorem quadSec_quadratic (S : SectionModule L Q Z α) (hα : Function.Surjective α)
    (hLQ : ∀ a ∈ L, ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (hquad : ∀ s s' : ↥L, α s ∈ utri F → α s' ∈ utri F → ∀ x ∈ Q,
      ⁅(s : G), ⁅(s' : G), x⁆⁆ ∈ Z) :
    ∀ a ∈ CFSG.Timmesfeld.upperUnipotent F, ∀ a' ∈ CFSG.Timmesfeld.upperUnipotent F,
      ∀ v : S.W, a' • (a • v - v) = a • v - v := by
  intro a ha a' ha' v
  obtain ⟨s, rfl, hs⟩ := quadSec_exists_utri hα ha
  obtain ⟨s', rfl, hs'⟩ := quadSec_exists_utri hα ha'
  obtain ⟨x, rfl⟩ := S.surjective v
  let y : ↥Q := ⟨(s : G) * x * (s : G)⁻¹, hLQ s s.2 x x.2⟩
  have hd : α s • S.π x - S.π x = S.π (y * x⁻¹) := by
    rw [S.smul_eq s x y rfl, S.map_mul, S.map_inv, sub_eq_add_neg]
  have e : ((y * x⁻¹ : ↥Q) : G) = ⁅(s : G), (x : G)⁆ := by
    simp [y, commutatorElement_def, mul_assoc]
  rw [hd, S.smul_eq_iff_commutator_mem hLQ, e]
  exact hquad s' s hs' hs x x.2

private def quadSecSub (S : SectionModule L Q Z α) (θ : (Fin 2 → F) →+ S.W) : Subgroup G where
  carrier := {y | ∃ hy : y ∈ Q, S.π ⟨y, hy⟩ ∈ θ.range}
  one_mem' := ⟨one_mem Q, AddMonoidHom.mem_range.2 ⟨0, (map_zero θ).trans S.map_one.symm⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h := add_mem ha' hb'
    rw [← S.map_mul] at h
    exact h
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h := neg_mem ha'
    rw [← S.map_inv] at h
    exact h

private theorem mem_quadSecSub {S : SectionModule L Q Z α} {θ : (Fin 2 → F) →+ S.W} {y : G} :
    y ∈ quadSecSub S θ ↔ ∃ hy : y ∈ Q, S.π ⟨y, hy⟩ ∈ θ.range :=
  Iff.rfl

private noncomputable def quadSecCoord (S : SectionModule L Q Z α) {θ : (Fin 2 → F) →+ S.W}
    (hinj : Function.Injective θ) (y : ↥(quadSecSub S θ)) : Fin 2 → F :=
  (AddMonoidHom.ofInjective hinj).symm ⟨_, (mem_quadSecSub.1 y.2).snd⟩

private theorem apply_quadSecCoord (S : SectionModule L Q Z α) {θ : (Fin 2 → F) →+ S.W}
    (hinj : Function.Injective θ) (y : ↥(quadSecSub S θ)) :
    θ (quadSecCoord S hinj y) = S.π ⟨y, (mem_quadSecSub.1 y.2).fst⟩ :=
  AddMonoidHom.apply_ofInjective_symm hinj _

private theorem le_normalizer_quadSecSub (S : SectionModule L Q Z α)
    (hLQ : ∀ a ∈ L, ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) {θ : (Fin 2 → F) →+ S.W}
    (hθ : ∀ (g : SL(2, F)) (v : Fin 2 → F), θ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = g • θ v) :
    L ≤ Subgroup.normalizer (quadSecSub S θ : Set G) := by
  have hconj : ∀ l ∈ L, ∀ y ∈ quadSecSub S θ, l * y * l⁻¹ ∈ quadSecSub S θ := by
    intro l hl y hy
    obtain ⟨hyQ, v, hv⟩ := mem_quadSecSub.1 hy
    refine mem_quadSecSub.2 ⟨hLQ l hl y hyQ,
      AddMonoidHom.mem_range.2 ⟨(α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ v, ?_⟩⟩
    rw [hθ, hv]
    exact S.smul_eq ⟨l, hl⟩ ⟨y, hyQ⟩ ⟨l * y * l⁻¹, hLQ l hl y hyQ⟩ rfl
  intro l hl
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨hconj l hl y, fun h => ?_⟩
  convert hconj l⁻¹ (inv_mem hl) _ h using 1
  group

private theorem quadSec_exists_natSec (S : SectionModule L Q Z α) (hZQ : Z ≤ Q)
    (hLQ : ∀ a ∈ L, ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) {θ : (Fin 2 → F) →+ S.W}
    (hinj : Function.Injective θ)
    (hθ : ∀ (g : SL(2, F)) (v : Fin 2 → F), θ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = g • θ v)
    {w : G} (hwQ : w ∈ Q) (he : θ ![1, 0] = S.π ⟨w, hwQ⟩) :
    ∃ E : Subgroup G, Z ≤ E ∧ E ≤ Q ∧ w ∈ E ∧ L ≤ Subgroup.normalizer (E : Set G) ∧
      ∃ β : ↥E →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
        β.ker = Z.subgroupOf E ∧
        (∀ l : ↥L, ∀ u v : ↥E, (v : G) = l * u * l⁻¹ →
          Multiplicative.toAdd (β v) =
            (α l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) ∧
        ∀ hwE : w ∈ E, Multiplicative.toAdd (β ⟨w, hwE⟩) = ![1, 0] := by
  have hb := apply_quadSecCoord S hinj
  have hmul : ∀ y z, quadSecCoord S hinj (y * z) = quadSecCoord S hinj y + quadSecCoord S hinj z :=
    fun y z => hinj (by
      rw [map_add, hb, hb, hb]
      exact S.map_mul ⟨y, (mem_quadSecSub.1 y.2).fst⟩ ⟨z, (mem_quadSecSub.1 z.2).fst⟩)
  let β : ↥(quadSecSub S θ) →* Multiplicative (Fin 2 → F) :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd (quadSecCoord S hinj y)) fun y z =>
      congrArg Multiplicative.ofAdd (hmul y z)
  refine ⟨quadSecSub S θ,
    fun z hz => mem_quadSecSub.2 ⟨hZQ hz, AddMonoidHom.mem_range.2 ⟨0, ?_⟩⟩,
    fun y hy => (mem_quadSecSub.1 hy).fst,
    mem_quadSecSub.2 ⟨hwQ, AddMonoidHom.mem_range.2 ⟨_, he⟩⟩,
    le_normalizer_quadSecSub S hLQ hθ, β, fun v => ?_, ?_, fun l u v huv => ?_, fun hwE => ?_⟩
  · rw [map_zero, (S.eq_zero_iff ⟨z, hZQ hz⟩).2 hz]
  · obtain ⟨x, hx⟩ := S.surjective (θ (Multiplicative.toAdd v))
    have hxE : (x : G) ∈ quadSecSub S θ :=
      mem_quadSecSub.2 ⟨x.2, AddMonoidHom.mem_range.2 ⟨_, hx.symm⟩⟩
    refine ⟨⟨x, hxE⟩, ?_⟩
    show Multiplicative.ofAdd (quadSecCoord S hinj ⟨x, hxE⟩) = v
    exact (congrArg Multiplicative.ofAdd (hinj ((hb ⟨x, hxE⟩).trans hx))).trans (ofAdd_toAdd v)
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (quadSecCoord S hinj y) = 1 ↔ (y : G) ∈ Z
    rw [ofAdd_eq_one, ← map_eq_zero_iff θ hinj, hb]
    exact S.eq_zero_iff _
  · show quadSecCoord S hinj v = (α l : Matrix (Fin 2) (Fin 2) F) *ᵥ quadSecCoord S hinj u
    refine hinj ?_
    rw [hθ, hb, hb]
    exact (S.smul_eq l ⟨u, (mem_quadSecSub.1 u.2).fst⟩ ⟨v, (mem_quadSecSub.1 v.2).fst⟩ huv).symm
  · exact hinj ((hb ⟨w, hwE⟩).trans he.symm)

end QuadSec

theorem exists_isNatSecOf_closure_of_quadratic {G : Type} [Group G]
    {L Q Z : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hQL : Q ≤ L)
    (hZQ : Z ≤ Q) (hZL : L ≤ Subgroup.normalizer (Z : Set G))
    (hQQ : ⁅Q, Q⁆ ≤ Z)
    (hfix : ∀ x ∈ Q, (∀ l ∈ L, ⁅l, x⁆ ∈ Z) → x ∈ Z)
    (hquad : ∀ s s' : ↥L, α s ∈ utri F → α s' ∈ utri F → ∀ x ∈ Q,
      ⁅(s : G), ⁅(s' : G), x⁆⁆ ∈ Z)
    {w : G} (hwQ : w ∈ Q) (hwZ : w ∉ Z) (hw : ∀ s : ↥L, α s ∈ utri F → ⁅(s : G), w⁆ ∈ Z) :
    ∃ E : Subgroup G, Z ≤ E ∧ E ≤ Q ∧ w ∈ E ∧ L ≤ Subgroup.normalizer (E : Set G) ∧
      ∃ β : ↥E →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
        β.ker = Z.subgroupOf E ∧
        (∀ l : ↥L, ∀ u v : ↥E, (v : G) = l * u * l⁻¹ →
          Multiplicative.toAdd (β v) =
            (α l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) ∧
        ∀ hwE : w ∈ E, Multiplicative.toAdd (β ⟨w, hwE⟩) = ![1, 0] := by
  have hLQ := quadSec_conj_mem hker hQL
  have hQQ' : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z := fun x hx y hy =>
    hQQ (Subgroup.commutator_mem_commutator hx hy)
  obtain ⟨S⟩ := exists_sectionModule α hα hZQ hQQ' hLQ
    (fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hZL ha) x).mp hx)
    fun a ha x hx => hQQ' _ ((hker a).1 ha) x hx
  have hfix' : ∀ v : S.W, (∀ g : SL(2, F), g • v = v) → v = 0 := by
    intro v hv
    obtain ⟨x, rfl⟩ := S.surjective v
    exact (S.eq_zero_iff x).2 (hfix x x.2 fun l hl =>
      (S.smul_eq_iff_commutator_mem hLQ ⟨l, hl⟩ x).1 (hv _))
  have hw' : ∀ g ∈ CFSG.Timmesfeld.upperUnipotent F, g • S.π ⟨w, hwQ⟩ = S.π ⟨w, hwQ⟩ := by
    intro g hg
    obtain ⟨s, rfl, hs⟩ := quadSec_exists_utri hα hg
    exact (S.smul_eq_iff_commutator_mem hLQ s ⟨w, hwQ⟩).2 (hw s hs)
  obtain ⟨θ, hinj, -, he, hθ⟩ := CFSG.Timmesfeld.ARS.exists_natural_of_quadratic hfix'
    (quadSec_quadratic S hα hLQ hquad) hw' fun h => hwZ ((S.eq_zero_iff _).1 h)
  exact quadSec_exists_natSec S hZQ hLQ hinj hθ hwQ he

end CFSG.Quasithin.F112R.St84

end
