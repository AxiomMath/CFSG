module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
public import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped LinearAlgebra.Projectivization

structure LinearPointAction (G X : Type*) [Group G] [MulAction G X] (q : ℕ) (α β : X)
    (U T : Subgroup G) : Prop where
  card_eq : Nat.card X = q + 1
  isMultiplyPretransitive : MulAction.IsMultiplyPretransitive G X 2
  ne : α ≠ β
  sup_eq_stabilizer : U ⊔ T = MulAction.stabilizer G α
  stabilizer_le_normalizer : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G)
  inf_eq_bot : U ⊓ T = ⊥
  stabilizer_inf_stabilizer : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β = T
  isCyclic : IsCyclic T
  card_T : Nat.card T = q - 1
  exists_sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = U
  card_U : Nat.card U = q
  isElemAbelian : IsElemAbelian 2 U
  regular : ∀ x y : X, x ≠ α → y ≠ α → ∃! g : U, (g : G) • x = y
  stronglyEmbedded : fusionStronglyEmbedded (MulAction.stabilizer G α)
  orderOf_eq_two_iff : ∀ g ∈ MulAction.stabilizer G α, orderOf g = 2 ↔ g ∈ U ∧ g ≠ 1
  involution_commute : ∀ g ∈ MulAction.stabilizer G α, ∀ h ∈ MulAction.stabilizer G α,
    orderOf g = 2 → orderOf h = 2 → g * h = h * g
  ncard_involutions : {g | g ∈ MulAction.stabilizer G α ∧ orderOf g = 2}.ncard = q - 1
  swap : ∀ w : G, w • α = β → w • β = α → orderOf w = 2 ∧ ∀ t ∈ T, w * t * w⁻¹ = t⁻¹

section Model

universe u

variable {K : Type u} [Field K] [Finite K] {f : ℕ}

theorem linearPointAction_psl2 (hcard : Nat.card K = 2 ^ f) :
    LinearPointAction (PSL2MatrixGroup K) (ℙ K (Fin 2 → K)) (2 ^ f) (psl2ProjectiveInfinity K)
      (psl2ProjectiveZero K) (psl2UpperUnipotentSubgroup K) (torus K) := by
  let : CharP K 2 := charP_two_of_card hcard
  have hU : psl2UpperUnipotentSubgroup K ≤ psl2Borel K := psl2UpperUnipotent_le_borel
  refine
    { card_eq := by
        rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hcard]
      isMultiplyPretransitive := psl2_projectiveLine_two_pretransitive K
      ne := infinity_ne_zero
      sup_eq_stabilizer := rootGroup_sup_torus
      stabilizer_le_normalizer := (psl2UpperUnipotent_normalizer_eq_borel K).ge
      inf_eq_bot := rootGroup_inf_torus
      stabilizer_inf_stabilizer := torus_eq_borel_inf_stabilizer_zero.symm
      isCyclic := torus_isCyclic
      card_T := by rw [card_torus, hcard]
      exists_sylow := exists_sylow_eq_rootGroup hcard
      card_U := (psl2UpperUnipotentSubgroup_card K).trans hcard
      isElemAbelian := rootGroup_isElemAbelian
      regular := fun _ _ hx hy => rootGroup_regular hx hy
      stronglyEmbedded := psl2Borel_stronglyEmbedded hcard
      orderOf_eq_two_iff := fun g hg => borel_orderOf_eq_two_iff hg
      involution_commute := fun g hg h hh hg2 hh2 =>
        (rootGroup_commute ((borel_orderOf_eq_two_iff hg).mp hg2).1
          ((borel_orderOf_eq_two_iff hh).mp hh2).1).eq
      ncard_involutions := ?_
      swap := fun w h₁ h₂ =>
        ⟨orderOf_eq_two_of_swap h₁ h₂, fun t ht => (torus_conj_of_swap h₁ h₂ ht).2⟩ }
  have hset : {g | g ∈ MulAction.stabilizer (PSL2MatrixGroup K) (psl2ProjectiveInfinity K) ∧
      orderOf g = 2} = (psl2UpperUnipotentSubgroup K : Set (PSL2MatrixGroup K)) \ {1} := by
    ext g
    constructor
    · rintro ⟨hg, hg2⟩
      exact ⟨((borel_orderOf_eq_two_iff hg).mp hg2).1, ((borel_orderOf_eq_two_iff hg).mp hg2).2⟩
    · rintro ⟨hgU, hg1⟩
      exact ⟨hU hgU, (borel_orderOf_eq_two_iff (hU hgU)).mpr ⟨hgU, hg1⟩⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
  change Nat.card (psl2UpperUnipotentSubgroup K) - 1 = 2 ^ f - 1
  rw [psl2UpperUnipotentSubgroup_card, hcard]

end Model

namespace LinearPointAction

variable {G X : Type*} [Group G] [MulAction G X] {q : ℕ} {α β : X} {U T : Subgroup G}

theorem le_stabilizer_left (h : LinearPointAction G X q α β U T) :
    U ≤ MulAction.stabilizer G α :=
  h.sup_eq_stabilizer ▸ le_sup_left

theorem le_stabilizer_right (h : LinearPointAction G X q α β U T) :
    T ≤ MulAction.stabilizer G α :=
  h.sup_eq_stabilizer ▸ le_sup_right

theorem normalizer_eq_stabilizer (h : LinearPointAction G X q α β U T) (hq : 1 < q) :
    Subgroup.normalizer (U : Set G) = MulAction.stabilizer G α := by
  refine le_antisymm (fun g hg => ?_) h.stabilizer_le_normalizer
  by_contra hgα
  rw [MulAction.mem_stabilizer_iff] at hgα
  have hfix : ∀ u ∈ U, u • g • α = g • α := fun u hu => by
    have hu' : g⁻¹ * u * g ∈ U := by
      rw [Subgroup.mem_normalizer_iff] at hg
      exact (hg _).2 (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
    have := h.le_stabilizer_left hu'
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff] at this
    exact this
  obtain ⟨u₀, -, huniq⟩ := h.regular _ _ hgα hgα
  have hU : ∀ u : U, u = 1 := fun u =>
    (huniq u (hfix u u.2)).trans (huniq 1 (one_smul _ _)).symm
  have hcard : Nat.card U = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun u v => (hU u).trans (hU v).symm⟩, ⟨1⟩⟩
  rw [h.card_U] at hcard
  omega

theorem le_twoRank [Finite G] {n : ℕ} (h : LinearPointAction G X (2 ^ n) α β U T) :
    n ≤ twoRank G :=
  CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G U h.isElemAbelian n h.card_U

theorem of_equiv {Y : Type*} [MulAction G Y] (h : LinearPointAction G X q α β U T) (f : X ≃ Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    LinearPointAction G Y q (f α) (f β) U T := by
  have hsmul : ∀ (g : G) (x : X) (y : Y), g • f x = y ↔ g • x = f.symm y := fun g x y => by
    rw [← hf, Equiv.eq_symm_apply]
  have hstab : ∀ x : X, MulAction.stabilizer G (f x) = MulAction.stabilizer G x := fun x => by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hsmul, Equiv.symm_apply_apply]
  refine
    { card_eq := by rw [← h.card_eq, Nat.card_congr f]
      isMultiplyPretransitive := ?_
      ne := f.injective.ne h.ne
      sup_eq_stabilizer := by rw [hstab]; exact h.sup_eq_stabilizer
      stabilizer_le_normalizer := by rw [hstab]; exact h.stabilizer_le_normalizer
      inf_eq_bot := h.inf_eq_bot
      stabilizer_inf_stabilizer := by rw [hstab, hstab]; exact h.stabilizer_inf_stabilizer
      isCyclic := h.isCyclic
      card_T := h.card_T
      exists_sylow := h.exists_sylow
      card_U := h.card_U
      isElemAbelian := h.isElemAbelian
      regular := fun x y hx hy => ?_
      stronglyEmbedded := by rw [hstab]; exact h.stronglyEmbedded
      orderOf_eq_two_iff := by rw [hstab]; exact h.orderOf_eq_two_iff
      involution_commute := by rw [hstab]; exact h.involution_commute
      ncard_involutions := by rw [hstab]; exact h.ncard_involutions
      swap := fun w h₁ h₂ => ?_ }
  · rw [MulAction.is_two_pretransitive_iff]
    intro x y x' y' hxy hxy'
    obtain ⟨g, hg₁, hg₂⟩ := (MulAction.is_two_pretransitive_iff.1 h.isMultiplyPretransitive)
      (f.symm.injective.ne hxy) (f.symm.injective.ne hxy')
    refine ⟨g, ?_, ?_⟩
    · rw [← f.apply_symm_apply x, hsmul]
      exact hg₁
    · rw [← f.apply_symm_apply y, hsmul]
      exact hg₂
  · have hx' : f.symm x ≠ α := fun e => hx (by rw [← e, Equiv.apply_symm_apply])
    have hy' : f.symm y ≠ α := fun e => hy (by rw [← e, Equiv.apply_symm_apply])
    obtain ⟨g, hg, huniq⟩ := h.regular _ _ hx' hy'
    refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
    · beta_reduce
      rw [← f.apply_symm_apply x, hsmul]
      exact hg
    · beta_reduce at hg' ⊢
      rw [← f.apply_symm_apply x, hsmul] at hg'
      exact hg'
  · rw [hsmul, Equiv.symm_apply_apply] at h₁ h₂
    exact h.swap w h₁ h₂

theorem faithfulSMul_of_equiv {Y : Type*} [MulAction G Y] [FaithfulSMul G X] (f : X ≃ Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) : FaithfulSMul G Y :=
  ⟨fun {g₁ g₂} hg => eq_of_smul_eq_smul fun x => f.injective (by rw [hf, hf, hg])⟩

theorem map {G' Y : Type*} [Group G'] [MulAction G' Y] [Finite G]
    (h : LinearPointAction G X q α β U T) (e : G ≃* G') (f : X ≃ Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = e g • f x) :
    LinearPointAction G' Y q (f α) (f β) (U.map e.toMonoidHom) (T.map e.toMonoidHom) := by
  have : Finite G' := Finite.of_equiv G e.toEquiv
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hsmul : ∀ (g : G') (y y' : Y), g • y = y' ↔ e.symm g • f.symm y = f.symm y' :=
    fun g y y' => by
      rw [← f.apply_eq_iff_eq, hf, e.apply_symm_apply, f.apply_symm_apply, f.apply_symm_apply]
  have hstab : ∀ x : X,
      MulAction.stabilizer G' (f x) = (MulAction.stabilizer G x).map e.toMonoidHom := fun x => by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, f.symm_apply_apply, Subgroup.mem_map_equiv,
      MulAction.mem_stabilizer_iff]
  have hord : ∀ g : G', orderOf (e.symm g) = orderOf g := fun g => MulEquiv.orderOf_eq e.symm g
  refine
    { card_eq := by rw [← h.card_eq, Nat.card_congr f]
      isMultiplyPretransitive := ?_
      ne := f.injective.ne h.ne
      sup_eq_stabilizer := by rw [hstab, ← h.sup_eq_stabilizer, Subgroup.map_sup]
      stabilizer_le_normalizer := by
        rw [hstab, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.map_mono h.stabilizer_le_normalizer
      inf_eq_bot := by rw [← Subgroup.map_inf_eq _ _ _ hinj, h.inf_eq_bot, Subgroup.map_bot]
      stabilizer_inf_stabilizer := by
        rw [hstab, hstab, ← Subgroup.map_inf_eq _ _ _ hinj, h.stabilizer_inf_stabilizer]
      isCyclic := ?_
      card_T := by rw [Subgroup.card_map_of_injective hinj, h.card_T]
      exists_sylow := ?_
      card_U := by rw [Subgroup.card_map_of_injective hinj, h.card_U]
      isElemAbelian :=
        CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U h.isElemAbelian e.toMonoidHom
      regular := fun y y' hy hy' => ?_
      stronglyEmbedded := by rw [hstab]; exact h.stronglyEmbedded.map_mulEquiv e
      orderOf_eq_two_iff := fun g hg => ?_
      involution_commute := fun g hg k hk hg2 hk2 => ?_
      ncard_involutions := ?_
      swap := fun w h₁ h₂ => ?_ }
  · rw [MulAction.is_two_pretransitive_iff]
    intro y₁ y₂ y₃ y₄ h₁₂ h₃₄
    obtain ⟨k, hk₁, hk₂⟩ := (MulAction.is_two_pretransitive_iff.1 h.isMultiplyPretransitive)
      (f.symm.injective.ne h₁₂) (f.symm.injective.ne h₃₄)
    exact ⟨e k, (hsmul _ _ _).2 (by rw [e.symm_apply_apply]; exact hk₁),
      (hsmul _ _ _).2 (by rw [e.symm_apply_apply]; exact hk₂)⟩
  · have := h.isCyclic
    exact isCyclic_of_surjective (T.equivMapOfInjective _ hinj) (MulEquiv.surjective _)
  · obtain ⟨P, hP⟩ := h.exists_sylow
    exact ⟨P.mapSurjective hsurj, by rw [Sylow.coe_mapSurjective, hP]⟩
  · have hx : f.symm y ≠ α := fun h' => hy (by rw [← h', f.apply_symm_apply])
    have hx' : f.symm y' ≠ α := fun h' => hy' (by rw [← h', f.apply_symm_apply])
    obtain ⟨u, hu, huniq⟩ := h.regular _ _ hx hx'
    refine ⟨⟨e.toMonoidHom u, Subgroup.mem_map_of_mem _ u.2⟩, ?_, fun g hg => ?_⟩
    · change e u • y = y'
      rw [hsmul, e.symm_apply_apply]
      exact hu
    · have hgU : e.symm g ∈ U := Subgroup.mem_map_equiv.1 g.2
      have hgu : e.symm g = u := congrArg Subtype.val (huniq ⟨_, hgU⟩ ((hsmul _ _ _).1 hg))
      refine Subtype.ext ?_
      change (g : G') = e u
      rw [← hgu, MulEquiv.apply_symm_apply]
  · rw [hstab, Subgroup.mem_map_equiv] at hg
    rw [← hord, h.orderOf_eq_two_iff _ hg, Subgroup.mem_map_equiv]
    exact and_congr_right fun _ => not_congr (MulEquiv.map_eq_one_iff e.symm)
  · rw [hstab, Subgroup.mem_map_equiv] at hg hk
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.involution_commute _ hg _ hk (by rw [hord]; exact hg2) (by rw [hord]; exact hk2)
  · have hset : {g : G' | g ∈ MulAction.stabilizer G' (f α) ∧ orderOf g = 2} =
        e '' {k : G | k ∈ MulAction.stabilizer G α ∧ orderOf k = 2} := by
      ext g
      refine ⟨fun ⟨hg, hg2⟩ => ⟨e.symm g, ⟨?_, by rw [hord]; exact hg2⟩, e.apply_symm_apply g⟩,
        ?_⟩
      · rw [hstab, Subgroup.mem_map_equiv] at hg
        exact hg
      · rintro ⟨k, ⟨hk, hk2⟩, rfl⟩
        refine ⟨?_, by rw [MulEquiv.orderOf_eq]; exact hk2⟩
        rw [hstab]
        exact Subgroup.mem_map_of_mem _ hk
    rw [hset, Set.ncard_image_of_injective _ e.injective, h.ncard_involutions]
  · rw [hsmul, f.symm_apply_apply, f.symm_apply_apply] at h₁ h₂
    obtain ⟨hw2, hinv⟩ := h.swap _ h₁ h₂
    refine ⟨by rw [← hord]; exact hw2, fun t ht => e.symm.injective ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinv _ (Subgroup.mem_map_equiv.1 ht)

theorem of_mulEquiv {H : Type*} [Group H] [Finite H] [MulAction H X] {U T : Subgroup H}
    (h : LinearPointAction H X q α β U T) (e : H ≃* G)
    (he : ∀ (g : G) (x : X), g • x = e.symm g • x) :
    LinearPointAction G X q α β (U.map e.toMonoidHom) (T.map e.toMonoidHom) :=
  h.map e (Equiv.refl X) fun k x => by
    rw [Equiv.refl_apply, Equiv.refl_apply, he, e.symm_apply_apply]

theorem conj [Finite G] (h : LinearPointAction G X q α β U T) (g : G) :
    LinearPointAction G X q (g • α) (g • β) (U.map (MulAut.conj g).toMonoidHom)
      (T.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g) (MulAction.toPerm g) fun k x => by
    rw [MulAction.toPerm_apply, MulAction.toPerm_apply, MulAut.conj_apply, smul_smul, smul_smul,
      inv_mul_cancel_right]

theorem faithfulSMul_of_mulEquiv {H : Type*} [Group H] [MulAction H X] [FaithfulSMul H X]
    (e : H ≃* G) (he : ∀ (g : G) (x : X), g • x = e.symm g • x) : FaithfulSMul G X :=
  ⟨fun {g₁ g₂} hg => e.symm.injective (eq_of_smul_eq_smul fun x => by rw [← he, ← he, hg])⟩

theorem exists_equiv_quotient (h : LinearPointAction G X q α β U T) :
    ∃ f : X ≃ G ⧸ MulAction.stabilizer G α,
      (∀ (g : G) (x : X), f (g • x) = g • f x) ∧ f α = QuotientGroup.mk 1 := by
  have := MulAction.isPretransitive_of_is_two_pretransitive (h2 := h.isMultiplyPretransitive)
  have hbij : Function.Bijective (MulAction.ofQuotientStabilizer G α) := by
    refine ⟨MulAction.injective_ofQuotientStabilizer G α, fun x => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α x
    exact ⟨QuotientGroup.mk g, hg⟩
  let φ := Equiv.ofBijective _ hbij
  refine ⟨φ.symm, fun g x => ?_, ?_⟩
  · rw [Equiv.symm_apply_eq]
    change g • x = MulAction.ofQuotientStabilizer G α (g • φ.symm x)
    rw [MulAction.ofQuotientStabilizer_smul]
    exact congrArg (g • ·) (φ.apply_symm_apply x).symm
  · rw [Equiv.symm_apply_eq]
    exact (one_smul G α).symm

theorem exists_quotient (h : LinearPointAction G X q α β U T) {B : Subgroup G}
    (hB : MulAction.stabilizer G α = B) :
    ∃ β' : G ⧸ B, LinearPointAction G (G ⧸ B) q (QuotientGroup.mk 1) β' U T ∧
      (FaithfulSMul G X → FaithfulSMul G (G ⧸ B)) := by
  subst hB
  obtain ⟨f, hf, hfα⟩ := h.exists_equiv_quotient
  exact ⟨f β, hfα ▸ h.of_equiv f hf, fun _ => faithfulSMul_of_equiv f hf⟩

end LinearPointAction

section Transport

universe u

theorem twoRank_eq_of_mulEquiv_psl2 {G : Type*} [Group G] [Finite G] {K : Type u} [Field K]
    [Finite K] {f : ℕ} (hcard : Nat.card K = 2 ^ f) (e : G ≃* PSL2MatrixGroup K) :
    twoRank G = f := by
  rw [← twoRank_eq hcard]
  exact le_antisymm
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective e.toMonoidHom e.injective)
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective e.symm.toMonoidHom e.symm.injective)

theorem linearPointAction_cosets_of_mulEquiv {G : Type*} [Group G] {K : Type u} [Field K]
    [Finite K] {f : ℕ} (hcard : Nat.card K = 2 ^ f) (e : G ≃* PSL2MatrixGroup K)
    (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      LinearPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (2 ^ f)
        (QuotientGroup.mk 1) β Q T ∧
      FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  let _ : MulAction G (ℙ K (Fin 2 → K)) := MulAction.compHom _ e.toMonoidHom
  have he : ∀ (g : G) (x : ℙ K (Fin 2 → K)), g • x = e.symm.symm g • x := fun _ _ => rfl
  have h := (linearPointAction_psl2 hcard).of_mulEquiv e.symm he
  have hfaith : FaithfulSMul G (ℙ K (Fin 2 → K)) :=
    LinearPointAction.faithfulSMul_of_mulEquiv e.symm he
  obtain ⟨P, hP⟩ := h.exists_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hU : ((psl2UpperUnipotentSubgroup K).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = ((g • P : Sylow 2 G) : Subgroup G) := by
    rw [← hP]
    ext x
    rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have h' := h.conj g
  rw [hU] at h'
  have hq : 1 < 2 ^ f :=
    Nat.one_lt_two_pow (BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hcard)
  obtain ⟨β, hβ, hβfaith⟩ := h'.exists_quotient (h'.normalizer_eq_stabilizer hq).symm
  exact ⟨_, β, hβ, hβfaith hfaith⟩

theorem linearPointAction_cosets_of_mulEquiv_psl2 {G : Type*} [Group G] {n : ℕ}
    (e : G ≃* PSL2BinaryMatrixGroup n) (hn : 2 ≤ n) (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      LinearPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (2 ^ n)
        (QuotientGroup.mk 1) β Q T ∧
      FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :=
  linearPointAction_cosets_of_mulEquiv (GaloisField.card 2 n (by omega)) e Q

theorem twoRank_eq_of_mulEquiv_psl2Binary {G : Type*} [Group G] [Finite G] {n : ℕ}
    (e : G ≃* PSL2BinaryMatrixGroup n) (hn : 1 ≤ n) : twoRank G = n :=
  twoRank_eq_of_mulEquiv_psl2 (GaloisField.card 2 n (by omega)) e

end Transport

end CFSG.ShultStronglyClosedTI.LinearModel
