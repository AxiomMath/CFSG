module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderOthers
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sec
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.Offender (weight commGL fixGL)
open CFSG.QuasithinUnique.Setup.Lift (ComponentOffenderOutput NaturalAlt Lbar Abar)
open CFSG.QuasithinUnique.Setup.Layer (fixIn actOn isInvariant_sup_subgroup)
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem exists_mulEquiv_sl2_of_isL2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ Nonempty (X ≃* SL(2, F)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)⟩⟩

theorem apply_mem_fixSub_of_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {z : V} (hz : z ∈ fixSub ρ L) : ρ g z ∈ fixSub ρ L := by
  intro l hl
  have hc : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) l).1 hl
    simpa using this
  calc ρ l (ρ g z) = ρ g (ρ (g⁻¹ * l * g) z) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, glRep_apply_inv]
    _ = ρ g z := by rw [hz _ hc]

theorem apply_eq_self_of_sub_mem_fixSub {L : Subgroup G} [IsSimpleGroup ↥L]
    (hUL : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤) (hnt : ¬ commOn ρ L ⊤ ≤ fixSub ρ L)
    {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hxU : ∀ u ∈ commOn ρ L ⊤, ρ x u - u ∈ fixSub ρ L) : ∀ u ∈ commOn ρ L ⊤, ρ x u = u := by
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) := isInvariant_commOn_top hLN
  have hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤ ⊓ fixSub ρ L) := fun l hl z hz =>
    ⟨hY l hl z hz.1, apply_mem_fixSub_of_mem_normalizer (hLN hl) hz.2⟩
  have hnt' : ∃ l ∈ L, ∃ y ∈ commOn ρ L ⊤, ρ l y - y ∉ commOn ρ L ⊤ ⊓ fixSub ρ L := by
    by_contra h
    push Not at h
    apply hnt
    rw [← hUL]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, y, hy, rfl⟩
    exact (h l hl y hy).2
  have hxk : x ∈ secKer ρ (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) :=
    ⟨fun y hy => ⟨Submodule.sub_mem _ (commOn_top_mapsTo hx hy) hy, hxU y hy⟩,
      fun z hz => ⟨commOn_top_mapsTo hx hz.1, apply_mem_fixSub_of_mem_normalizer hx hz.2⟩,
      fun z hz => ⟨commOn_top_mapsTo (inv_mem hx) hz.1,
        apply_mem_fixSub_of_mem_normalizer (inv_mem hx) hz.2⟩⟩
  have hcomm := commute_of_mem_secKer hY hZ hnt' hx hxk
  intro u hu
  rw [← hUL] at hu
  refine Submodule.span_induction (p := fun w _ => ρ x w = w) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨l, hl, v, hv, rfl⟩
    have hlz : ρ l (ρ x v - v) = ρ x v - v := hxU v hv l hl
    rw [map_sub, ← glRep_mul_apply, ← hcomm l hl, glRep_mul_apply]
    have e : ρ x v = v + (ρ x v - v) := by abel
    rw [e, map_add, hlz]
    abel
  · exact map_zero _
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro c a _ ha
    rw [map_smul, ha]

theorem commOn_facts_of_mem_calP [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) [IsSimpleGroup ↥L] {A : Subgroup G} (hA : A ∈ calP ρ) (hLA : ⁅L, A⁆ ≠ ⊥) :
    commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ ∧ ¬ commOn ρ L ⊤ ≤ fixSub ρ L := by
  have hUL := commOn_commOn_eq (ρ := ρ) (isElementaryAbelian_of_mem_calP hA)
    (le_normalizer_of_mem_calP hρ hL hA) (commutator_eq_self_of_mem_calP hρ hL hA hLA)
  refine ⟨hUL, fun hle => ?_⟩
  have h0 : commOn ρ L ⊤ = ⊥ := by
    rw [← hUL, commOn_eq_bot_iff]
    intro l hl u hu
    exact hle hu l hl
  have hL1 : L = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    apply hρ
    ext w
    simp [(commOn_eq_bot_iff.1 h0) l hl w Submodule.mem_top]
  exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance hL1

theorem exists_componentOffenderOutput
    [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn : 2 ≤ n) (hX : IsL2 ↥L n) {A : Subgroup G} (hA : A ∈ calP ρ)
    (hLA : ⁅L, A⁆ ≠ ⊥) :
    ∃ (B : Subgroup G) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)),
      B ≤ A ∧ IsBestOffenderOn ρ B (commOn ρ L ⊤) ∧ IsQuadraticOn ρ B (commOn ρ L ⊤) ∧
      ¬ B ≤ cenOn ρ B (commOn ρ L ⊤) ∧
      (∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ L ⊤) →
        ∃ k ∈ L, ∃ u ∈ commOn ρ L ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u)) ∧
      TransportGL ρ L B hinv ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Fintype (ℙ F (Fin 2 → F)))
        (_ : DecidableEq (ℙ F (Fin 2 → F))), Fintype.card F = 2 ^ n ∧
        ∃ α : (↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⧸
            Subgroup.center ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)) ≃* SL(2, F),
          ComponentOffenderOutput (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)
            (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B) n α
            (commGL (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⊤) := by
  classical
  haveI hLs : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  obtain ⟨B, hinv, hBA, hbest, hquad, hBU, hmov, hT⟩ := exists_transportGL hρ hL hLs hA hLA
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_mulEquiv_sl2_of_isL2 hX
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨e, -⟩ := hT.iso
  let α := ((QuotientGroup.quotientMulEquivOfEq hT.center).trans QuotientGroup.quotientBot).trans
    (e.symm.trans eF)
  exact ⟨B, hinv, hBA, hbest, hquad, hBU, hmov, hT, F, inferInstance, inferInstance, inferInstance,
    inferInstance, hF', α, (CFSG.QuasithinUnique.Setup.Lift.minimal_even_SL2_component_offender hT.comp hn
      hF' α hT.le hT.elem hT.ne_bot hT.off hT.strict hT.comm).1⟩

section Natural

variable {L B : Subgroup G} {L₁ B₁ : Subgroup (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤))}
  {n : ℕ} {F : Type} [Field F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {α : (↥L₁ ⧸ Subgroup.center ↥L₁) ≃* SL(2, F)}

theorem mem_fixIn_iff (e : ↥L ≃* ↥L₁)
    (he : ∀ (l : ↥L) (u : ↥(commOn ρ L ⊤)), (((e l : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ l u)
    (w : ↥(commGL L₁ ⊤)) :
    w ∈ fixIn L₁ (commGL L₁ ⊤) ↔ ∀ l ∈ L, ρ l (((w : ↥(commOn ρ L ⊤))) : V) = (w : ↥(commOn ρ L ⊤)) := by
  rw [CFSG.QuasithinUnique.Setup.Layer.mem_fixIn]
  constructor
  · intro h l hl
    have h1 := congrArg Subtype.val (h _ (e ⟨l, hl⟩).2)
    rw [he] at h1
    exact h1
  · intro h y hy
    obtain ⟨l, hl⟩ := e.surjective ⟨y, hy⟩
    apply Subtype.ext
    have h1 := he l (w : ↥(commOn ρ L ⊤))
    rw [hl] at h1
    rw [h1]
    exact h l l.2

theorem actOn_mk_val (hout : ComponentOffenderOutput L₁ B₁ n α (commGL L₁ ⊤)) {S : Subgroup _}
    (hS : S ≤ L₁ ⊔ B₁) (s : ↥S) (w : ↥(commGL L₁ ⊤)) :
    ∃ hw : ((s : _ ≃ₗ[ZMod 2] _) (w : ↥(commOn ρ L ⊤))) ∈ commGL L₁ ⊤,
      actOn L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A) S hS s
          (Submodule.Quotient.mk w) = Submodule.Quotient.mk ⟨_, hw⟩ := by
  refine ⟨isInvariant_sup_subgroup hout.inv_L hout.inv_A _ (hS s.2) _ w.2, ?_⟩
  show CFSG.QuasithinUnique.Setup.Layer.actW L₁ B₁ (commGL L₁ ⊤) hout.A_norm
    (isInvariant_sup_subgroup hout.inv_L hout.inv_A) ⟨s, hS s.2⟩ (Submodule.Quotient.mk w) = _
  rw [CFSG.QuasithinUnique.Setup.Layer.actW_mk]
  congr 1

theorem natL2_of_naturalAlt [Finite F] (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* ↥L₁)
    (he : ∀ (l : ↥L) (u : ↥(commOn ρ L ⊤)), (((e l : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ l u)
    (hcen : Subgroup.center ↥L₁ = ⊥) (hI : commGL L₁ ⊤ = ⊤)
    (hout : ComponentOffenderOutput L₁ B₁ n α (commGL L₁ ⊤))
    {θ : ↥(Lbar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A)) ≃* SL(2, F)}
    (hnat : NaturalAlt (Lbar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A))
      (Abar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A)) θ) :
    NatL2 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) n := by
  classical
  obtain ⟨-, β, hβ, -⟩ := hnat
  have hmemI : ∀ y : ↥(commOn ρ L ⊤), y ∈ commGL L₁ ⊤ := fun y => by rw [hI]; exact Submodule.mem_top
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (commOn ρ L ⊤).subtype
    (Submodule.ker_subtype _)
  have hru : ∀ (u : V) (hu : u ∈ commOn ρ L ⊤), r u = ⟨u, hu⟩ := fun u hu =>
    LinearMap.congr_fun hr ⟨u, hu⟩
  let toI : V →ₗ[ZMod 2] ↥(commGL L₁ ⊤) := LinearMap.codRestrict _ r fun v => hmemI _
  let ψ : V →+ (Fin 2 → F) :=
    β.toAddMonoidHom.comp ((fixIn L₁ (commGL L₁ ⊤)).mkQ.toAddMonoidHom.comp toI.toAddMonoidHom)
  have hψ : ∀ (u : V) (hu : u ∈ commOn ρ L ⊤),
      ψ u = β (Submodule.Quotient.mk ⟨⟨u, hu⟩, hmemI _⟩) := by
    intro u hu
    show β ((fixIn L₁ (commGL L₁ ⊤)).mkQ (toI u)) = _
    have h1 : toI u = ⟨⟨u, hu⟩, hmemI _⟩ := Subtype.ext (hru u hu)
    rw [h1]
    rfl
  have hinj : Function.Injective (actOn L₁ B₁ (commGL L₁ ⊤) hout.A_norm
      (isInvariant_sup_subgroup hout.inv_L hout.inv_A) L₁ le_sup_left).rangeRestrict := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_rangeRestrict, hout.kernel_L, hcen]
  let ψ₀ : ↥L₁ ≃* ↥(Lbar L₁ B₁ (commGL L₁ ⊤) hout.A_norm
      (isInvariant_sup_subgroup hout.inv_L hout.inv_A)) :=
    MulEquiv.ofBijective _ ⟨hinj, MonoidHom.rangeRestrict_surjective _⟩
  let φ : ↥L ≃* ↥(StatedSL 2 F) :=
    e.trans (ψ₀.trans (θ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)))
  refine ⟨F, inferInstance, inferInstance, hF, isInvariant_commOn_top Subgroup.le_normalizer,
    fun l hl z hz => by rw [hz.2 l hl]; exact hz, inf_le_left, φ, ψ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hψ x hx.1, (Submodule.Quotient.mk_eq_zero _).2
      ((mem_fixIn_iff e he ⟨⟨x, hx.1⟩, hmemI _⟩).2 hx.2), map_zero]
  · intro x hx h0
    rw [hψ x hx, EmbeddingLike.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
      mem_fixIn_iff e he] at h0
    exact ⟨hx, h0⟩
  · intro y
    obtain ⟨w, rfl⟩ := β.surjective y
    obtain ⟨⟨⟨x, hx⟩, hxI⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨x, hx, hψ x hx⟩
  · intro h x hx
    have hhx : ρ h x ∈ commOn ρ L ⊤ := commOn_top_mapsTo (Subgroup.le_normalizer h.2) hx
    obtain ⟨hw, hk⟩ := actOn_mk_val hout (le_sup_left : L₁ ≤ L₁ ⊔ B₁) (e h) ⟨⟨x, hx⟩, hmemI _⟩
    have key : (Submodule.Quotient.mk ⟨⟨ρ h x, hhx⟩, hmemI _⟩ :
        ↥(commGL L₁ ⊤) ⧸ fixIn L₁ (commGL L₁ ⊤)) =
        (ψ₀ (e h)).1 (Submodule.Quotient.mk ⟨⟨x, hx⟩, hmemI _⟩) := by
      show _ = actOn L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A)
        L₁ le_sup_left (e h) _
      rw [hk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact (he h ⟨x, hx⟩).symm
    rw [hψ _ hhx, key, hβ, hψ x hx]
    rfl

theorem exists_eq_apply_of_naturalAlt [IsSimpleGroup ↥L]
    (hUL : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤) (hnt : ¬ commOn ρ L ⊤ ≤ fixSub ρ L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (e : ↥L ≃* ↥L₁)
    (he : ∀ (l : ↥L) (u : ↥(commOn ρ L ⊤)), (((e l : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ l u)
    (hB : ∀ b ∈ B, ∃ y ∈ B₁, ∀ u : ↥(commOn ρ L ⊤), ((y u : ↥(commOn ρ L ⊤)) : V) = ρ b u)
    (hI : commGL L₁ ⊤ = ⊤) (hout : ComponentOffenderOutput L₁ B₁ n α (commGL L₁ ⊤))
    {θ : ↥(Lbar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A)) ≃* SL(2, F)}
    (hnat : NaturalAlt (Lbar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A))
      (Abar L₁ B₁ (commGL L₁ ⊤) hout.A_norm (isInvariant_sup_subgroup hout.inv_L hout.inv_A)) θ) :
    ∀ b ∈ B, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ b u = ρ l u := by
  intro b hb
  obtain ⟨y, hyB, hy⟩ := hB b hb
  have hmemI : ∀ v : ↥(commOn ρ L ⊤), v ∈ commGL L₁ ⊤ := fun v => by rw [hI]; exact Submodule.mem_top
  obtain ⟨y', hy'⟩ := MonoidHom.mem_range.1 (hnat.1 (MonoidHom.mem_range.2 ⟨⟨y, hyB⟩, rfl⟩))
  obtain ⟨l, rfl⟩ := e.surjective y'
  have h1 : ∀ v ∈ commOn ρ L ⊤, ρ b v - ρ l v ∈ fixSub ρ L := by
    intro v hv
    have h2 := congrArg (fun f : (↥(commGL L₁ ⊤) ⧸ fixIn L₁ (commGL L₁ ⊤)) ≃ₗ[ZMod 2] _ =>
      f (Submodule.Quotient.mk ⟨⟨v, hv⟩, hmemI _⟩)) hy'
    obtain ⟨hw1, hk1⟩ := actOn_mk_val hout (le_sup_left : L₁ ≤ L₁ ⊔ B₁) (e l) ⟨⟨v, hv⟩, hmemI _⟩
    obtain ⟨hw2, hk2⟩ := actOn_mk_val hout (le_sup_right : B₁ ≤ L₁ ⊔ B₁) ⟨y, hyB⟩ ⟨⟨v, hv⟩, hmemI _⟩
    rw [hk1, hk2, Submodule.Quotient.eq, mem_fixIn_iff e he] at h2
    intro l' hl'
    have h3 := h2 l' hl'
    simp only [Submodule.coe_sub, he, hy] at h3
    rw [← neg_sub, map_neg, h3]
  have hx : (l : G)⁻¹ * b ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer l.2)) (hBN hb)
  have hxU : ∀ v ∈ commOn ρ L ⊤, ρ ((l : G)⁻¹ * b) v - v ∈ fixSub ρ L := by
    intro v hv
    have e1 : ρ ((l : G)⁻¹ * b) v - v = ρ (l : G)⁻¹ (ρ b v - ρ l v) := by
      rw [map_sub, glRep_mul_apply, glRep_inv_apply]
    rw [e1, h1 v hv _ (inv_mem l.2)]
    exact h1 v hv
  have h4 := apply_eq_self_of_sub_mem_fixSub hUL hnt hx hxU
  refine ⟨l, l.2, fun u hu => ?_⟩
  have h5 := h4 u hu
  rw [glRep_mul_apply] at h5
  calc ρ b u = ρ (l : G) (ρ (l : G)⁻¹ (ρ b u)) := (glRep_apply_inv ρ _ _).symm
    _ = ρ l u := by rw [h5]

end Natural

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
