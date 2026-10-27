module

public import CFSG.Quasithin.Background.E6TwentyThreeP
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.Quasithin.Background.E6EightSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G]

structure InspHyp (Y E X : Subgroup G) (a z : G) : Prop where
  quasi : CFSG.IsQuasisimple ↥Y
  list : Lemma115Cases Y z
  elem : IsElemAbelian 2 E
  norm : E ≤ Subgroup.normalizer (Y : Set G)
  mem : a ∈ E
  not_cent : ¬ Y ≤ Subgroup.centralizer ({a} : Set G)
  comp : IsComponentIn X (Y ⊓ Subgroup.centralizer ({a} : Set G))
  a6 : Nonempty (↥X ≃* alternatingGroup (Fin 6))
  star : ∀ b ∈ E, ¬ Y ≤ Subgroup.centralizer ({b} : Set G) →
    ∃ S : Subgroup G, IsSylowIn 2 S (Y ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      E ≤ Subgroup.centralizer (S : Set G)

namespace InspHyp

variable {Y E X : Subgroup G} {a z : G} (h : InspHyp Y E X a z)
include h

theorem mul_self_eq_one {b : G} (hb : b ∈ E) : b * b = 1 := by
  rw [← pow_two]
  exact h.elem.2 b hb

theorem mul_comm_of_mem {b c : G} (hb : b ∈ E) (hc : c ∈ E) : b * c = c * b := by
  exact congrArg Subtype.val (h.elem.1.is_comm.comm (⟨b, hb⟩ : ↥E) ⟨c, hc⟩)

theorem commutator_eq : ⁅Y, Subgroup.zpowers a⁆ = Y :=
  (Id2519.commutator_dichotomy h.quasi (h.norm h.mem)).resolve_right h.not_cent

theorem card_X : Nat.card ↥X = 360 := Id2519.IsA6.card_eq h.a6

theorem patterns [Finite G] (hT : Id2519.TabIdent) :
    IsPGroup 2 (Subgroup.center ↥Y) ∧
      X = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (Y ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      (Id2519.PatSp4 Y X ∨ Id2519.PatL5 Y X ∨ Id2519.PatHS Y X a ∨ Id2519.PatA8 Y X a) := by
  obtain ⟨h1, h2, -, -, h5⟩ := hT G Y X a h.quasi ⟨z, h.list⟩ (h.norm h.mem)
    (h.mul_self_eq_one h.mem) h.commutator_eq h.comp (Or.inr (Or.inr h.a6))
  exact ⟨h1, h2, h5 h.a6⟩

theorem false_of_sylow [Finite G] (hC : E68CentComp) {S : Subgroup G} (hS : IsSylowIn 2 S Y)
    (hES : E ≤ Subgroup.centralizer (S : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haS : a ∈ Subgroup.centralizer (S : Set G) := hES h.mem
  have ha2 : a ^ 2 = 1 := h.elem.2 a h.mem
  set R := S ⊔ Subgroup.zpowers a with hRdef
  have hSa : S ≤ Subgroup.centralizer ({a} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haS s hs)
  have hRa : R ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le hSa (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hza : IsPGroup 2 (Subgroup.zpowers a) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha2) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; rfl)
  have hzS : Subgroup.zpowers a ≤ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun s => ?_)
    have hsa : ∀ s : G, s ∈ S → a * s * a⁻¹ = s := fun s hs => by
      rw [(Subgroup.mem_centralizer_iff.mp haS s hs).symm]
      group
    constructor
    · intro hs
      rw [hsa s hs]
      exact hs
    · intro hs
      have h1 : a⁻¹ * (a * s * a⁻¹) * a = s := by group
      have h2 : a⁻¹ * (a * s * a⁻¹) * a ∈ S := by
        have hc : a⁻¹ ∈ Subgroup.centralizer (S : Set G) := Subgroup.inv_mem _ haS
        rw [show a⁻¹ * (a * s * a⁻¹) * a = a⁻¹ * (a * s * a⁻¹) * a⁻¹⁻¹ by group]
        rw [(Subgroup.mem_centralizer_iff.mp hc _ hs).symm]
        simpa using hs
      rwa [h1] at h2
  have hR2 : IsPGroup 2 R := hS.isPGroup.to_sup_of_normal_left' hza hzS
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le (hS.le.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr (h.norm h.mem))
  have hSR : S ≤ R ⊓ Y := le_inf le_sup_left hS.le
  have hsyl : IsSylowTwoOf (R ⊓ Y) Y := by
    refine ⟨inf_le_right, hR2.to_le inf_le_left, fun hdvd => hS.not_dvd_relIndex ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex S (R ⊓ Y) Y hSR inf_le_right
    exact hdvd.trans (Dvd.intro_left _ hmul)
  have hnc : a ∉ Subgroup.centralizer (Y : Set G) := fun ha =>
    h.not_cent fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ha y hy)
  have hyp : E68CentHyp Y R a :=
    { quasisimple := h.quasi
      isPGroup := hR2
      normalizer := hRY
      sylow := hsyl
      mem := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      central := fun r hr => (Subgroup.mem_centralizer_singleton_iff.mp (hRa hr)).symm
      sq := ha2
      not_mem := hnc }
  have hconc := hC G Y R X z a h.list hyp h.comp
  have h60 := hconc.2
  rw [h.card_X] at h60
  exact absurd h60 (by norm_num)

theorem factorization_le [Finite G] {b : G} (hb : b ∈ E)
    (hbY : ¬ Y ≤ Subgroup.centralizer ({b} : Set G)) :
    (Nat.card ↥(Y ⊓ Subgroup.centralizer ({b} : Set G))).factorization 2 ≤
      (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hES⟩ := h.star b hb hbY
  have haS : ∀ s ∈ S, a * s = s * a := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp (hES h.mem) s hs).symm
  have h1 := card_le_twoPart_centralizer (hS.le.trans inf_le_left) hS.isPGroup haS
  rw [hS.card_eq] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem exists_sylow_a : ∃ T : Subgroup G,
    IsSylowIn 2 T (Y ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      E ≤ Subgroup.centralizer (T : Set G) :=
  h.star a h.mem h.not_cent

end InspHyp

section Action

variable {Y : Subgroup G} {Q : Type*} [Group Q] (π : ↥Y →* Q) (hπ : Function.Surjective π)
  (hker : π.ker = Subgroup.center ↥Y)

@[expose] noncomputable def quotAction : ↥(Subgroup.normalizer (Y : Set G)) →* MulAut Q :=
  (Id2519.Tab.quotActHom π hπ hker).comp Y.normalizerMonoidHom

theorem quotAction_apply (n : ↥(Subgroup.normalizer (Y : Set G))) (y y' : ↥Y)
    (hy : (y' : G) = n * y * (n : G)⁻¹) : quotAction π hπ hker n (π y) = π y' := by
  have hc : Y.normalizerMonoidHom n y = y' := Subtype.ext (by
    rw [hy, Subgroup.normalizerMonoidHom_apply_apply_coe])
  rw [quotAction, MonoidHom.comp_apply, Id2519.Tab.quotActHom_apply, hc]

theorem quotAction_eq_one_iff (hY : Group.IsPerfect ↥Y) (n : ↥(Subgroup.normalizer (Y : Set G))) :
    quotAction π hπ hker n = 1 ↔ (n : G) ∈ Subgroup.centralizer (Y : Set G) := by
  rw [quotAction, MonoidHom.comp_apply, ← map_one (Id2519.Tab.quotActHom π hπ hker),
    (Id2519.Tab.quotActHom_injective π hπ hker hY).eq_iff, ← MonoidHom.mem_ker,
    Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem ker_quotAction (hY : Group.IsPerfect ↥Y) :
    (quotAction π hπ hker).ker =
      (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, quotAction_eq_one_iff π hπ hker hY, Subgroup.mem_subgroupOf]

theorem card_map_quotAction (hY : Group.IsPerfect ↥Y) {H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card ↥((H.subgroupOf (Subgroup.normalizer (Y : Set G))).map (quotAction π hπ hker)) =
      (H ⊓ Subgroup.centralizer (Y : Set G)).relIndex H := by
  rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf hH,
    ← ker_quotAction π hπ hker hY, Subgroup.relIndex_ker]

theorem mem_centralizer_iff_quotAction (hc : Subgroup.center ↥Y = ⊥)
    (x : ↥(Subgroup.normalizer (Y : Set G))) (y : ↥Y) :
    (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ↔ quotAction π hπ hker x (π y) = π y := by
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hc]
  obtain ⟨y', hy'⟩ : ∃ y' : ↥Y, (y' : G) = x * y * (x : G)⁻¹ :=
    ⟨Y.normalizerMonoidHom x y, Subgroup.normalizerMonoidHom_apply_apply_coe Y x y⟩
  rw [quotAction_apply π hπ hker x y y' hy', hinj.eq_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hyx
    apply Subtype.ext
    rw [hy', ← hyx]
    group
  · intro hyy
    have h1 : ((y' : ↥Y) : G) = y := congrArg Subtype.val hyy
    rw [hy'] at h1
    calc (y : G) * x = x * y * (x : G)⁻¹ * x := by rw [h1]
      _ = x * y := by group

end Action

end CFSG.Quasithin.E6
