module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G]

theorem sylowTwoOf_of_card_mul [Finite G] {S H : Subgroup G} (hSH : S ≤ H) (hp : IsPGroup 2 S)
    {m : ℕ} (hm : ¬ 2 ∣ m) (hc : Nat.card H = Nat.card S * m) : IsSylowTwoOf S H := by
  refine ⟨hSH, hp, ?_⟩
  have h := Subgroup.relIndex_mul_card S H
  rw [inf_of_le_left hSH, hc] at h
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h1 : S.relIndex H = m := Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  show ¬ 2 ∣ S.relIndex H
  rw [h1]
  exact hm

theorem sylowTwoOf_of_le {P S H : Subgroup G} (hP : IsSylowTwoOf P H) (hPS : P ≤ S) (hSH : S ≤ H)
    (hp : IsPGroup 2 S) : IsSylowTwoOf S H := by
  refine ⟨hSH, hp, fun hdvd => hP.2.2 ?_⟩
  exact hdvd.trans (Subgroup.relIndex_dvd_of_le_left H hPS)

theorem sylowTwoOf_subgroupOf {S X C : Subgroup G} (h : IsSylowTwoOf S X) (hXC : X ≤ C) :
    IsSylowTwoOf (S.subgroupOf C) (X.subgroupOf C) := by
  have hSC : S ≤ C := h.1.trans hXC
  refine ⟨fun x hx => h.1 hx, h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm, fun hd => ?_⟩
  apply h.2.2
  have e : (S.subgroupOf C).relIndex (X.subgroupOf C) = S.relIndex X :=
    Subgroup.relIndex_subgroupOf hXC
  have hd' : 2 ∣ (S.subgroupOf C).relIndex (X.subgroupOf C) := hd
  rw [e] at hd'
  exact hd'

theorem mem_centralizer_singleton_subgroup {H : Subgroup G} (x y : H) :
    x ∈ Subgroup.centralizer ({y} : Set H) ↔
      (x : G) ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Generic

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_centralizer_invF (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ↥(F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a}) =
      (2 ^ (2 * a + 1)) ^ 10 * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  exact h

theorem S4_le_centralizer_invF (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    S4 K a ≤ F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} :=
  (reeGamma_inf_centralizer_invE_invF ha hK).2.2.1 ▸ le_sup_left

theorem leviN_three_le_centralizer_invF (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i3 ≤ F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} :=
  (reeGamma_inf_centralizer_invE_invF ha hK).2.2.1 ▸ le_sup_right

theorem odd_sq_sub_one (a : ℕ) : ¬ 2 ∣ (2 ^ (2 * a + 1)) ^ 2 - 1 := by
  have h1 : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
  have h2 : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  omega

theorem sylow_invF_modgl (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSylowTwoOf (F4.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer {invF K a})
      (F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a}) := by
  obtain ⟨-, -, hC, hdisj, -⟩ := reeGamma_inf_centralizer_invE_invF ha hK
  have hP : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) :=
    isPGroup_reeFixedPosUnipotent ha hK
  have hV3N : rootV K a .i3 ≤ leviN K a .i3 := rootV_le_leviN hK .i3
  have hV3P : rootV K a .i3 ≤ F4.reeFixedPosUnipotent K a := rootV_le_sylowP hK .i3
  have hS4P : S4 K a ≤ F4.reeFixedPosUnipotent K a := rootJoin_le_sylowP hK _
  have hnorm : rootV K a .i3 ≤ Subgroup.normalizer (S4 K a : Set (ModGL F4.tag K)) :=
    hV3P.trans (S4_spec hK).2.2.2
  have hdis : Disjoint (S4 K a) (rootV K a .i3) :=
    Disjoint.mono_right hV3N (disjoint_iff.2 hdisj)
  have hcard : Nat.card ↥(S4 K a ⊔ rootV K a .i3) = (2 ^ (2 * a + 1)) ^ 10 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdis,
      (S4_spec hK).2.2.1, card_rootV hK]
    simp only [Idx.isSz, Bool.false_eq_true, ↓reduceIte, pow_one]
    rw [← pow_succ]
  have hle : S4 K a ⊔ rootV K a .i3 ≤ F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} :=
    sup_le (S4_le_centralizer_invF ha hK)
      (hV3N.trans (leviN_three_le_centralizer_invF ha hK))
  have hleP : S4 K a ⊔ rootV K a .i3 ≤
      F4.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer {invF K a} :=
    le_inf (sup_le hS4P hV3P) fun x hx => (hle hx).2
  have hSyl := sylowTwoOf_of_card_mul hle (hP.to_le (sup_le hS4P hV3P)) (odd_sq_sub_one a)
    (by rw [card_centralizer_invF ha hK, hcard])
  exact sylowTwoOf_of_le hSyl hleP
    (inf_le_inf_right _ (reeFixedPosUnipotent_le_reeGamma (t := F4) (K := K) (a := a)))
    (hP.to_le inf_le_left)

theorem coe_zg (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((zg hK : Gm K a) : ModGL F4.tag K) = invE K a := rfl

theorem coe_tg (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((tg hK : Gm K a) : ModGL F4.tag K) = invF K a := rfl

theorem mem_centralizer_tg (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Gm K a} :
    x ∈ Subgroup.centralizer ({tg hK} : Set (Gm K a)) ↔
      (x : ModGL F4.tag K) ∈ Subgroup.centralizer {invF K a} := by
  rw [mem_centralizer_singleton_subgroup, coe_tg]

theorem sylow_tg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSylowTwoOf (Ug K a ⊓ Subgroup.centralizer ({tg hK} : Set (Gm K a)))
      (Subgroup.centralizer ({tg hK} : Set (Gm K a))) := by
  have h := sylowTwoOf_subgroupOf (C := F4.reeGamma K a) (sylow_invF_modgl ha hK)
    (inf_le_left : F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} ≤ F4.reeGamma K a)
  have e1 : (F4.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer {invF K a}).subgroupOf
      (F4.reeGamma K a) = Ug K a ⊓ Subgroup.centralizer ({tg hK} : Set (Gm K a)) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Ug, mem_centralizer_tg hK]
  have e2 : (F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a}).subgroupOf (F4.reeGamma K a) =
      Subgroup.centralizer ({tg hK} : Set (Gm K a)) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_tg hK]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [e1, e2] at h
  exact h

end Model

end CFSG.Quasithin.H13.F431.TwoF4
