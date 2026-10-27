module

public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiModel

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open CFSG.BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization

structure SuzukiPointAction (G X : Type*) [Group G] [MulAction G X] (q : ℕ) (α β : X)
    (U T : Subgroup G) : Prop where
  card_eq : Nat.card X = q ^ 2 + 1
  isMultiplyPretransitive : MulAction.IsMultiplyPretransitive G X 2
  ne : α ≠ β
  sup_eq_stabilizer : U ⊔ T = MulAction.stabilizer G α
  stabilizer_le_normalizer : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G)
  inf_eq_bot : U ⊓ T = ⊥
  stabilizer_inf_stabilizer : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β = T
  isCyclic : IsCyclic T
  card_T : Nat.card T = q - 1
  exists_sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = U
  card_U : Nat.card U = q ^ 2
  regular : ∀ x y : X, x ≠ α → y ≠ α → ∃! g : U, (g : G) • x = y
  stronglyEmbedded : fusionStronglyEmbedded (MulAction.stabilizer G α)
  involution_mem_center : ∀ g ∈ MulAction.stabilizer G α, orderOf g = 2 →
    g ∈ U ∧ ∀ h ∈ U, h * g = g * h
  ncard_involutions : {g | g ∈ MulAction.stabilizer G α ∧ orderOf g = 2}.ncard = q - 1
  exists_elemAbelian : ∃ E : Subgroup G, E ≤ U ∧ IsElemAbelian 2 E ∧ Nat.card E = q
  swap : ∀ w : G, w • α = β → w • β = α → orderOf w = 2 ∧ ∀ t ∈ T, w * t * w⁻¹ = t⁻¹

section Model

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiPointAction_suzukiGroup
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SuzukiPointAction (suzukiGroup a K) (suzukiOmegaSub hK) (2 ^ (2 * a + 1))
      ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩
      ⟨suzukiLine a K 0 0, suzukiLine_mem_suzukiOmega a K 0 0⟩ (suzukiU a K) (suzukiT a K) := by
  have hB : MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) = suzukiB a K :=
    (suzuki_ovoid_stabilizer hK).2
  have hval : ∀ (g : suzukiGroup a K) (x : suzukiOmegaSub hK),
      ((g • x : suzukiOmegaSub hK) : ℙ K (Fin 4 → K)) = g • (x : ℙ K (Fin 4 → K)) :=
    fun g x => SubMulAction.val_smul g x
  refine
    { card_eq := ?_
      isMultiplyPretransitive := (suzuki_ovoid_double_transitivity hK).2.2.1
      ne := fun h => suzukiLine_ne_suzukiInfty (a := a) 0 0 (congrArg Subtype.val h).symm
      sup_eq_stabilizer := hB.symm
      stabilizer_le_normalizer := hB ▸ sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
      inf_eq_bot := suzukiU_inf_suzukiT hK
      stabilizer_inf_stabilizer := by
        rw [SubMulAction.stabilizer_of_subMul, SubMulAction.stabilizer_of_subMul]
        exact suzuki_two_point_stabilizer hK
      isCyclic := isCyclic_suzukiT
      card_T := (suzuki_borel_structure hK).2.2.1
      exists_sylow := exists_sylow_eq_suzukiU hK
      card_U := (suzuki_unipotent_structure hK).2.1
      regular := fun x y hx hy => ?_
      stronglyEmbedded := hB ▸ fusionStronglyEmbedded_suzukiB hK
      involution_mem_center := fun g hg hord => ?_
      ncard_involutions := hB ▸ ncard_involutions_suzukiB hK
      exists_elemAbelian :=
        ⟨suzukiZ0 a K, suzukiZ0_le_suzukiU, isElemAbelian_suzukiZ0 hK, card_suzukiZ0 hK⟩
      swap := fun w h₁ h₂ => ?_ }
  · rw [← (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2, ← Nat.card_coe_set_eq]
    rfl
  · have hx' : (x : ℙ K (Fin 4 → K)) ∈ suzukiOmega a K \ {suzukiInfty K} :=
      ⟨x.2, fun h => hx (Subtype.ext h)⟩
    have hy' : (y : ℙ K (Fin 4 → K)) ∈ suzukiOmega a K \ {suzukiInfty K} :=
      ⟨y.2, fun h => hy (Subtype.ext h)⟩
    obtain ⟨g, hg, huniq⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hx' _ hy'
    refine ⟨g, Subtype.ext (by rw [hval]; exact hg), fun g' hg' => huniq g' ?_⟩
    beta_reduce at hg' ⊢
    rw [← hval, hg']
  · rw [hB] at hg
    obtain ⟨v, -, rfl⟩ := (mem_suzukiB_and_orderOf_eq_two_iff hK).1 ⟨hg, hord⟩
    refine ⟨suzukiSElt_mem_suzukiU a K 0 v, fun h hh => ?_⟩
    obtain ⟨u, w, rfl⟩ := (mem_suzukiU_iff hK).1 hh
    exact (suzukiSElt_zero_commute hK v u w).symm
  · have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    rw [hval] at h₁' h₂'
    exact ⟨orderOf_eq_two_of_swap hK h₁' h₂', fun t ht => conj_eq_inv_of_swap hK h₁' h₂' ht⟩

theorem faithfulSMul_suzukiOmegaSub
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) :=
  (suzuki_ovoid_faithful ha hK).2

end Model

namespace SuzukiPointAction

variable {G X : Type*} [Group G] [MulAction G X] {q : ℕ} {α β : X} {U T : Subgroup G}

theorem le_stabilizer_left (h : SuzukiPointAction G X q α β U T) :
    U ≤ MulAction.stabilizer G α :=
  h.sup_eq_stabilizer ▸ le_sup_left

theorem le_stabilizer_right (h : SuzukiPointAction G X q α β U T) :
    T ≤ MulAction.stabilizer G α :=
  h.sup_eq_stabilizer ▸ le_sup_right

theorem normalizer_eq_stabilizer (h : SuzukiPointAction G X q α β U T) (hq : 1 < q) :
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
  have : 1 < q ^ 2 := one_lt_pow₀ hq two_ne_zero
  omega

theorem le_twoRank [Finite G] {n : ℕ} (h : SuzukiPointAction G X (2 ^ n) α β U T) :
    n ≤ twoRank G := by
  obtain ⟨E, -, hE, hcard⟩ := h.exists_elemAbelian
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G E hE n hcard

theorem of_equiv {Y : Type*} [MulAction G Y] (h : SuzukiPointAction G X q α β U T) (f : X ≃ Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    SuzukiPointAction G Y q (f α) (f β) U T := by
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
      regular := fun x y hx hy => ?_
      stronglyEmbedded := by rw [hstab]; exact h.stronglyEmbedded
      involution_mem_center := by rw [hstab]; exact h.involution_mem_center
      ncard_involutions := by rw [hstab]; exact h.ncard_involutions
      exists_elemAbelian := h.exists_elemAbelian
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
    (h : SuzukiPointAction G X q α β U T) (e : G ≃* G') (f : X ≃ Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = e g • f x) :
    SuzukiPointAction G' Y q (f α) (f β) (U.map e.toMonoidHom) (T.map e.toMonoidHom) := by
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
      regular := fun y y' hy hy' => ?_
      stronglyEmbedded := by rw [hstab]; exact h.stronglyEmbedded.map_mulEquiv e
      involution_mem_center := fun g hg hg2 => ?_
      ncard_involutions := ?_
      exists_elemAbelian := ?_
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
    obtain ⟨hgU, hcomm⟩ := h.involution_mem_center _ hg (by rw [hord]; exact hg2)
    refine ⟨Subgroup.mem_map_equiv.2 hgU, fun k hk => e.symm.injective ?_⟩
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_map_equiv.1 hk)
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
  · obtain ⟨E, hEU, hE, hcard⟩ := h.exists_elemAbelian
    exact ⟨E.map e.toMonoidHom, Subgroup.map_mono hEU,
      CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map E hE e.toMonoidHom,
      by rw [Subgroup.card_map_of_injective hinj, hcard]⟩
  · rw [hsmul, f.symm_apply_apply, f.symm_apply_apply] at h₁ h₂
    obtain ⟨hw2, hinv⟩ := h.swap _ h₁ h₂
    refine ⟨by rw [← hord]; exact hw2, fun t ht => e.symm.injective ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinv _ (Subgroup.mem_map_equiv.1 ht)

theorem of_mulEquiv {H : Type*} [Group H] [Finite H] [MulAction H X] {U T : Subgroup H}
    (h : SuzukiPointAction H X q α β U T) (e : H ≃* G)
    (he : ∀ (g : G) (x : X), g • x = e.symm g • x) :
    SuzukiPointAction G X q α β (U.map e.toMonoidHom) (T.map e.toMonoidHom) :=
  h.map e (Equiv.refl X) fun k x => by
    rw [Equiv.refl_apply, Equiv.refl_apply, he, e.symm_apply_apply]

theorem conj [Finite G] (h : SuzukiPointAction G X q α β U T) (g : G) :
    SuzukiPointAction G X q (g • α) (g • β) (U.map (MulAut.conj g).toMonoidHom)
      (T.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g) (MulAction.toPerm g) fun k x => by
    rw [MulAction.toPerm_apply, MulAction.toPerm_apply, MulAut.conj_apply, smul_smul, smul_smul,
      inv_mul_cancel_right]

theorem faithfulSMul_of_mulEquiv {H : Type*} [Group H] [MulAction H X] [FaithfulSMul H X]
    (e : H ≃* G) (he : ∀ (g : G) (x : X), g • x = e.symm g • x) : FaithfulSMul G X :=
  ⟨fun {g₁ g₂} hg => e.symm.injective (eq_of_smul_eq_smul fun x => by rw [← he, ← he, hg])⟩

theorem exists_equiv_quotient (h : SuzukiPointAction G X q α β U T) :
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

theorem exists_quotient (h : SuzukiPointAction G X q α β U T) {B : Subgroup G}
    (hB : MulAction.stabilizer G α = B) :
    ∃ β' : G ⧸ B, SuzukiPointAction G (G ⧸ B) q (QuotientGroup.mk 1) β' U T ∧
      (FaithfulSMul G X → FaithfulSMul G (G ⧸ B)) := by
  subst hB
  obtain ⟨f, hf, hfα⟩ := h.exists_equiv_quotient
  exact ⟨f β, hfα ▸ h.of_equiv f hf, fun _ => faithfulSMul_of_equiv f hf⟩

end SuzukiPointAction

section Transport

variable {a : ℕ} {K : Type} [Field K] [Finite K]

def suzukiGroupEquivSuzukiMatrixGroup (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiGroup a K ≃* SuzukiMatrixGroup a :=
  (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    ((glaSzFieldEquiv (binaryFieldEquiv (2 * a + 1) (by omega) hK) a).trans
      ((glaSzCanonicalEquivNative a).trans (suzukiCoverNativeEquiv a)))

theorem twoRank_eq_of_mulEquiv {G : Type*} [Group G] [Finite G]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : G ≃* suzukiGroup a K) : twoRank G = 2 * a + 1 := by
  rw [← twoRank_suzukiGroup hK]
  exact le_antisymm
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective e.toMonoidHom e.injective)
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective e.symm.toMonoidHom e.symm.injective)

theorem twoRank_eq_of_mulEquiv_suzukiMatrixGroup
    {G : Type*} [Group G] [Finite G] (m : ℕ)
    (e : G ≃* SuzukiMatrixGroup m) : twoRank G = 2 * m + 1 :=
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  twoRank_eq_of_mulEquiv hK (e.trans (suzukiGroupEquivSuzukiMatrixGroup hK).symm)

theorem suzukiPointAction_cosets_of_mulEquiv {G : Type*} [Group G]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : G ≃* suzukiGroup a K) (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      SuzukiPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))
        (2 ^ (2 * a + 1)) (QuotientGroup.mk 1) β Q T ∧
      (1 ≤ a → FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  let _ : MulAction G (suzukiOmegaSub hK) := MulAction.compHom _ e.toMonoidHom
  have he : ∀ (g : G) (x : suzukiOmegaSub hK), g • x = e.symm.symm g • x := fun _ _ => rfl
  have h := (suzukiPointAction_suzukiGroup hK).of_mulEquiv e.symm he
  have hfaith : 1 ≤ a → FaithfulSMul G (suzukiOmegaSub hK) := fun ha => by
    have := faithfulSMul_suzukiOmegaSub ha hK
    exact SuzukiPointAction.faithfulSMul_of_mulEquiv e.symm he
  obtain ⟨P, hP⟩ := h.exists_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hU : ((suzukiU a K).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      ((g • P : Sylow 2 G) : Subgroup G) := by
    rw [← hP]
    ext x
    rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have h' := h.conj g
  rw [hU] at h'
  obtain ⟨β, hβ, hβfaith⟩ :=
    h'.exists_quotient (h'.normalizer_eq_stabilizer (Nat.one_lt_two_pow (by omega))).symm
  exact ⟨_, β, hβ, fun ha => hβfaith (hfaith ha)⟩

theorem suzukiPointAction_cosets_of_mulEquiv_suzukiMatrixGroup
    {G : Type*} [Group G] (m : ℕ)
    (e : G ≃* SuzukiMatrixGroup m) (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      SuzukiPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))
        (2 ^ (2 * m + 1)) (QuotientGroup.mk 1) β Q T ∧
      (1 ≤ m → FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))) :=
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  suzukiPointAction_cosets_of_mulEquiv hK (e.trans (suzukiGroupEquivSuzukiMatrixGroup hK).symm) Q

theorem suzukiPointAction_cosets_of_mulEquiv_sz
    {G : Type*} [Group G] (a : ℕ) (e : G ≃* Sz a)
    (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      SuzukiPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))
        (2 ^ (2 * a + 1)) (QuotientGroup.mk 1) β Q T ∧
      (1 ≤ a → FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G))) :=
  suzukiPointAction_cosets_of_mulEquiv_suzukiMatrixGroup a (e.trans (suzukiCoverNativeEquiv a)) Q

theorem suzukiPointAction_cosets_of_suzukiModel
    {G : Type} [Group G] {p f : ℕ}
    (hG : SuzukiModel G p f) (Q : Sylow 2 G) :
    ∃ (T : Subgroup G) (β : G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      SuzukiPointAction G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (2 ^ f)
        (QuotientGroup.mk 1) β Q T ∧
      FaithfulSMul G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hG
  obtain ⟨T, β, hβ, hfaith⟩ := suzukiPointAction_cosets_of_mulEquiv hcard e Q
  exact ⟨T, β, hβ, hfaith ha⟩

end Transport

end CFSG.ShultStronglyClosedTI.SuzukiModel
