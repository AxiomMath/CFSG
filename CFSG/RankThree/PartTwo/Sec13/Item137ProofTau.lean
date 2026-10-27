module

public import CFSG.RankThree.PartTwo.Sec13.Item137
public import CFSG.RankThree.PartTwo.Sec21.Notation
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.Asc83Table.GL23
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

section Irreducible

variable {G : Type} [Group G]

theorem eq_bot_or_eq_top_of_map_eq {B : Subgroup G} [Finite B]
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h9 : Nat.card B = 9) {τ : MulAut B}
    (h4 : τ ^ 4 = 1) (h2 : τ ^ 2 ≠ 1) {D : Subgroup B} (hD : D.map τ.toMonoidHom = D) :
    D = ⊥ ∨ D = ⊤ := by
  have key : ∀ φ : MulAut B, φ • D = D.map φ.toMonoidHom := fun φ => by
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hT : ∀ φ ∈ MulAction.stabilizer (MulAut B) D, D.map φ.toMonoidHom = D := fun φ hφ =>
    (key φ).symm.trans (MulAction.mem_stabilizer_iff.mp hφ)
  have hτ : τ ∈ MulAction.stabilizer (MulAut B) D :=
    MulAction.mem_stabilizer_iff.mpr ((key τ).trans hD)
  exact isIrreducibleOn_of_order_four hB h9 hτ h4 h2 D hT

end Irreducible

section Quaternion

variable {G : Type} [Group G]

theorem quaternion_eq_one_or (q : QuaternionGroup 2) :
    q = 1 ∨ q = QuaternionGroup.a 2 ∨ q ^ 2 = QuaternionGroup.a 2 := by
  revert q
  decide

theorem eq_one_of_quaternion_apply_eq_self {B : Subgroup G} [Finite B]
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h9 : Nat.card B = 9)
    {f : QuaternionGroup 2 →* MulAut B} (hf : Function.Injective f) {q : QuaternionGroup 2}
    (hq : q ≠ 1) {y : B} (hy : f q y = y) : y = 1 := by
  have h12 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by decide
  have hz : f (QuaternionGroup.a 2) y = y := by
    rcases quaternion_eq_one_or q with h1 | h2 | h2
    · exact absurd h1 hq
    · rw [← h2]
      exact hy
    · rw [← h2, map_pow, pow_two]
      change f q (f q y) = y
      rw [hy, hy]
  set τ := f (QuaternionGroup.a 1) with hτ
  have hτ2 : τ ^ 2 = f (QuaternionGroup.a 2) := by rw [hτ, ← map_pow, h12]
  have h4 : τ ^ 4 = 1 := by
    rw [hτ, ← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
  have h2 : τ ^ 2 ≠ 1 := by
    rw [hτ2]
    intro h1
    exact absurd (hf (h1.trans (map_one f).symm)) (by decide)
  set C : Subgroup B := (f (QuaternionGroup.a 2)).toMonoidHom.eqLocus (MonoidHom.id B) with hC
  have hmemC : ∀ x : B, x ∈ C ↔ f (QuaternionGroup.a 2) x = x := fun x => Iff.rfl
  have hCle : C.map τ.toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hmemC] at hx
    rw [hmemC]
    change f (QuaternionGroup.a 2) (τ x) = τ x
    have hx' : (τ ^ 2) x = x := by rw [hτ2]; exact hx
    rw [← hτ2]
    calc (τ ^ 2) (τ x) = τ ((τ ^ 2) x) := by rw [pow_two]; rfl
      _ = τ x := by rw [hx']
  have hCeq : C.map τ.toMonoidHom = C :=
    Subgroup.eq_of_le_of_card_ge hCle (by rw [Subgroup.card_map_of_injective τ.injective])
  rcases eq_bot_or_eq_top_of_map_eq hB h9 h4 h2 hCeq with hbot | htop
  · have : y ∈ C := (hmemC y).mpr hz
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply h2
    rw [hτ2]
    ext x
    have : x ∈ C := htop ▸ Subgroup.mem_top x
    rw [(hmemC x).mp this]
    rfl

theorem exists_quaternion_apply_eq {B : Subgroup G} [Finite B]
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h9 : Nat.card B = 9)
    {f : QuaternionGroup 2 →* MulAut B} (hf : Function.Injective f) {y₀ y₁ : B} (h0 : y₀ ≠ 1)
    (h1 : y₁ ≠ 1) : ∃ q : QuaternionGroup 2, f q y₀ = y₁ := by
  classical
  let φ : QuaternionGroup 2 → {y : B // y ≠ 1} := fun q =>
    ⟨f q y₀, fun h => h0 ((f q).injective (h.trans (map_one (f q)).symm))⟩
  have hinj : Function.Injective φ := by
    intro q q' hqq'
    have h : f q y₀ = f q' y₀ := congrArg Subtype.val hqq'
    have h' : f (q'⁻¹ * q) y₀ = y₀ := by
      rw [map_mul, MulAut.mul_apply, h, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    by_contra hne
    have hq : q'⁻¹ * q ≠ 1 := fun h1 => hne (by rw [inv_mul_eq_one] at h1; exact h1.symm)
    exact h0 (eq_one_of_quaternion_apply_eq_self hB h9 hf hq h')
  have hcard : Nat.card (QuaternionGroup 2) = Nat.card {y : B // y ≠ 1} := by
    have := Fintype.ofFinite B
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, h9]
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2 ⟨y₁, h1⟩
  exact ⟨q, congrArg Subtype.val hq⟩

end Quaternion

section Config

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {c : G}

theorem exists_quaternion_hom (hc3 : c ^ 3 = 1) (hcL : c ∉ L)
    (hLc : ∀ l ∈ L, l * c = c * l) (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L))
    (eGL : Sec4.autIn L E ≃* GL (Fin 2) (ZMod 3)) :
    ∃ f : QuaternionGroup 2 →* MulAut (E ⊓ L : Subgroup G), Function.Injective f ∧
      ∀ q, f q ∈ Sec4.autIn L (E ⊓ L) := by
  have hYeq : (Subgroup.zpowers c ⊔ (E ⊓ L)) ⊓ L = E ⊓ L :=
    zpowers_sup_inf_eq hc3 hcL inf_le_right (fun y hy => (hLc y hy.2).symm)
  obtain ⟨e₁⟩ := nonempty_autIn_sup_equiv hLc hYeq
  rw [← hEdec] at e₁
  refine ⟨(Sec4.autIn L (E ⊓ L)).subtype.comp
      (e₁.toMonoidHom.comp (eGL.symm.toMonoidHom.comp CFSG.RankThree.Asc83Table.quatHom)),
    Subtype.val_injective.comp (e₁.injective.comp (eGL.symm.injective.comp
      CFSG.RankThree.Asc83Table.quatHom_injective)), fun q => (e₁ _).2⟩

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_inf (hLc : ∀ l ∈ L, l * c = c * l)
    (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L)) {u : G} (huL : u ∈ L)
    (huB : u ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) :
    u ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at huB ⊢
  rw [hEdec, Subgroup.map_sup, huB, MonoidHom.map_zpowers]
  congr 2
  change u * c * u⁻¹ = c
  rw [hLc u huL, mul_inv_cancel_right]

theorem exists_conj_eq_of_ne_one (hc3 : c ^ 3 = 1) (hcL : c ∉ L)
    (hLc : ∀ l ∈ L, l * c = c * l) (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L))
    (hB : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L)) (h9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (eGL : Sec4.autIn L E ≃* GL (Fin 2) (ZMod 3)) {y₀ y₁ : G} (hy₀ : y₀ ∈ E ⊓ L)
    (hy₁ : y₁ ∈ E ⊓ L) (h0 : y₀ ≠ 1) (h1 : y₁ ≠ 1) :
    ∃ w ∈ L, w ∈ Subgroup.normalizer (E : Set G) ∧ w * y₀ * w⁻¹ = y₁ := by
  obtain ⟨f, hf, hfL⟩ := exists_quaternion_hom hc3 hcL hLc hEdec eGL
  obtain ⟨q, hq⟩ := exists_quaternion_apply_eq hB h9 hf (y₀ := ⟨y₀, hy₀⟩) (y₁ := ⟨y₁, hy₁⟩)
    (fun h => h0 (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
  obtain ⟨w, hwN, hwL, hw⟩ := Sec4.mem_autIn_iff.mp (hfL q)
  refine ⟨w, hwL, mem_normalizer_of_mem_normalizer_inf hLc hEdec hwL hwN, ?_⟩
  have := congrArg Subtype.val hq
  rw [← hw, Sec4.normalizerMonoidHom_apply_coe] at this
  exact this

theorem exists_tau_of_autIn_gl (hc3 : c ^ 3 = 1) (hcL : c ∉ L) (hLc : ∀ l ∈ L, l * c = c * l)
    (hEdec : E = Subgroup.zpowers c ⊔ (E ⊓ L)) (hB : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L))
    (h9 : Nat.card (E ⊓ L : Subgroup G) = 9) (eGL : Sec4.autIn L E ≃* GL (Fin 2) (ZMod 3)) :
    ∃ u ∈ L, u ∈ Subgroup.normalizer (E : Set G) ∧
      (∀ v ∈ E, u * v * u⁻¹ ∈ Subgroup.zpowers v → v ∈ Subgroup.zpowers c) ∧
      ∀ v ∈ E, u ^ 4 * v * (u ^ 4)⁻¹ = v := by
  obtain ⟨f, hf, hfL⟩ := exists_quaternion_hom hc3 hcL hLc hEdec eGL
  set τ := f (QuaternionGroup.a 1) with hτ
  have h4 : τ ^ 4 = 1 := by
    rw [hτ, ← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
  have h2 : τ ^ 2 ≠ 1 := by
    rw [hτ, ← map_pow]
    intro h1
    exact absurd (hf (h1.trans (map_one f).symm)) (by decide)
  obtain ⟨u, huN, huL, hu⟩ := Sec4.mem_autIn_iff.mp (hfL (QuaternionGroup.a 1))
  have huτ : ∀ y : (E ⊓ L : Subgroup G), ((τ y : (E ⊓ L : Subgroup G)) : G) = u * y * u⁻¹ := by
    intro y
    rw [hτ, ← hu, Sec4.normalizerMonoidHom_apply_coe]
  have huE := mem_normalizer_of_mem_normalizer_inf hLc hEdec huL huN
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hLc y hy.2).symm k).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hdecomp : ∀ v ∈ E, ∃ (i : ℤ) (y : G), y ∈ E ⊓ L ∧ v = c ^ i * y := by
    intro v hv
    have hv' : v ∈ ((Subgroup.zpowers c ⊔ (E ⊓ L) : Subgroup G) : Set G) := hEdec ▸ hv
    rw [hset] at hv'
    obtain ⟨a, ha, y, hy, rfl⟩ := hv'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨i, y, hy, rfl⟩
  have huc : ∀ i : ℤ, u * c ^ i * u⁻¹ = c ^ i := fun i => by
    rw [(Commute.zpow_right (show Commute u c from hLc u huL) i).eq, mul_inv_cancel_right]
  refine ⟨u, huL, huE, ?_, ?_⟩
  · intro v hv hvu
    obtain ⟨i, y, hy, rfl⟩ := hdecomp v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
    have hcy : Commute (c ^ i) y := Commute.zpow_left (hLc y hy.2).symm i
    have hconj : u * (c ^ i * y) * u⁻¹ = c ^ i * (u * y * u⁻¹) := by
      rw [show u * (c ^ i * y) * u⁻¹ = (u * c ^ i * u⁻¹) * (u * y * u⁻¹) by group, huc]
    have hpow : (c ^ i * y) ^ k = c ^ (i * k) * y ^ k := by rw [hcy.mul_zpow, zpow_mul]
    rw [hconj, hpow] at hk
    have huyL : u * y * u⁻¹ ∈ L := L.mul_mem (L.mul_mem huL hy.2) (L.inv_mem huL)
    have hmem : (u * y * u⁻¹) * (y ^ k)⁻¹ ∈ Subgroup.zpowers c ⊓ L := by
      refine ⟨?_, L.mul_mem huyL (L.inv_mem (L.zpow_mem hy.2 k))⟩
      have : (u * y * u⁻¹) * (y ^ k)⁻¹ = c ^ (i * k) * (c ^ i)⁻¹ := by
        have := hk
        calc (u * y * u⁻¹) * (y ^ k)⁻¹ = (c ^ i)⁻¹ * (c ^ i * (u * y * u⁻¹)) * (y ^ k)⁻¹ := by
              group
          _ = (c ^ i)⁻¹ * (c ^ (i * k) * y ^ k) * (y ^ k)⁻¹ := by rw [this]
          _ = c ^ (i * k) * (c ^ i)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers c _)
        (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c _))
    rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    set D : Subgroup (E ⊓ L : Subgroup G) := Subgroup.zpowers ⟨y, hy⟩ with hD
    have hDle : D.map τ.toMonoidHom ≤ D := by
      rw [Subgroup.map_le_iff_le_comap, hD, Subgroup.zpowers_le]
      change τ ⟨y, hy⟩ ∈ Subgroup.zpowers (⟨y, hy⟩ : (E ⊓ L : Subgroup G))
      refine ⟨k, Subtype.ext ?_⟩
      rw [huτ, hmem]
      simp
    have hDeq : D.map τ.toMonoidHom = D :=
      Subgroup.eq_of_le_of_card_ge hDle (by rw [Subgroup.card_map_of_injective τ.injective])
    rcases eq_bot_or_eq_top_of_map_eq hB h9 h4 h2 hDeq with hbot | htop
    · have hy1 : (⟨y, hy⟩ : (E ⊓ L : Subgroup G)) = 1 := by
        rw [← Subgroup.mem_bot, ← hbot]
        exact Subgroup.mem_zpowers _
      have : y = 1 := congrArg Subtype.val hy1
      rw [this, mul_one]
      exact Subgroup.zpow_mem_zpowers c i
    · exfalso
      have hcardD : Nat.card D = 9 := by
        rw [htop, Subgroup.card_top, h9]
      have hy3 : (⟨y, hy⟩ : (E ⊓ L : Subgroup G)) ^ 3 = 1 := Subtype.ext (by simpa using hB.2 y hy)
      have hle3 : Nat.card D ≤ 3 := by
        rw [hD, Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy3)
      omega
  · intro v hv
    obtain ⟨i, y, hy, rfl⟩ := hdecomp v hv
    have hτ4 : ∀ x : (E ⊓ L : Subgroup G), ((τ ^ 4) x : G) = u ^ 4 * x * (u ^ 4)⁻¹ := by
      intro x
      rw [hτ, ← hu, ← map_pow, Sec4.normalizerMonoidHom_apply_coe]
      simp
    have hy4 : u ^ 4 * y * (u ^ 4)⁻¹ = y := by
      have := hτ4 ⟨y, hy⟩
      rw [h4] at this
      exact this.symm
    have hu4c : u ^ 4 * c ^ i * (u ^ 4)⁻¹ = c ^ i := by
      rw [(Commute.zpow_right (Commute.pow_left (show Commute u c from hLc u huL) 4) i).eq,
        mul_inv_cancel_right]
    calc u ^ 4 * (c ^ i * y) * (u ^ 4)⁻¹ =
          (u ^ 4 * c ^ i * (u ^ 4)⁻¹) * (u ^ 4 * y * (u ^ 4)⁻¹) := by group
      _ = c ^ i * y := by rw [hu4c, hy4]

end Config

end CFSG.RankThree.PartTwo.Sec13
