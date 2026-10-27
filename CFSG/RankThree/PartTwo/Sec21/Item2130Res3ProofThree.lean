module

public import CFSG.RankThree.PartTwo.Sec4.Statements426
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec9.Item95
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item2130Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_of_mem_thetaComponentsIn (h48 : Sec4.Item4_8) (h426 : Sec4.Item4_26Theta)
    (hst : PartTwoStanding G) {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA81 : Nat.card A = 3 ^ 4) {b c : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hcA : c ∈ A)
    (hc1 : c ≠ 1) {I : Subgroup G}
    (hI : I ∈ thetaComponentsIn
      (Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G)))
    (hIZ : inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) = Subgroup.zpowers b)
    {n : ℕ} (hn : 1 ≤ n) (hISL : Sec4.IsSLThreePiAt (lBar I) (2 ^ n)) :
    ∃ Y ∈ thetaComponentsAt 3 b, I ≤ Y ∧
      (Y = I ⊔ inSubgroup (aschbacherSolvableCore 3) Y ∨
        ∃ m : ℕ, 1 ≤ m ∧ Sec4.IsSLThreePiAt (lBar Y) (2 ^ (3 * m)) ∧
          Sec4.IsSLThreePiAt (lBar I) (2 ^ m)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcb : c * b = b * c := hcomm c hcA b hbA
  set D := Subgroup.centralizer ({b} : Set G) with hD
  have hS4 : SectionFourHyp ↥D :=
    hst.toTheoremFourHyp.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hb1)
  set c' : ↥D := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hcb⟩ with hc'
  set Z₂ := Subgroup.centralizer ({c'} : Set ↥D) with hZ₂
  set CB := Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G) with hCB
  have hZ₂map : Z₂.map D.subtype = CB := by
    rw [hZ₂, SteinbergBY.map_subtype_centralizer_singleton D c', hCB,
      Subgroup.centralizer_closure]
    ext x
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    tauto
  obtain ⟨hICB, hI₁⟩ := mem_thetaComponentsIn_iff.mp hI
  let ψ : ↥CB ≃* ↥Z₂ := (MulEquiv.subgroupCongr hZ₂map.symm).trans
    (Z₂.equivMapOfInjective D.subtype D.subtype_injective).symm
  have hψ : (D.subtype.comp Z₂.subtype).comp ψ.toMonoidHom = CB.subtype := by
    ext x
    have h1 := (Z₂.equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hZ₂map.symm x)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  set T₂ := (I.subgroupOf CB).map ψ.toMonoidHom with hT₂
  have hT₂mem : T₂ ∈ thetaComponents 3 ↥Z₂ :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three ψ hI₁
  set K' := T₂.map Z₂.subtype with hK'
  have hK'at : K' ∈ thetaComponentsAt 3 c' := ⟨T₂, hT₂mem, rfl⟩
  have hK'map : K'.map D.subtype = I := by
    rw [hK', hT₂, Subgroup.map_map, Subgroup.map_map, hψ,
      Subgroup.map_subgroupOf_eq_of_le hICB]
  have hID : I ≤ D := hK'map ▸ Subgroup.map_subtype_le K'
  have hAD : A ≤ D := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
  have hA'el : IsElemAbelian 3 (A.subgroupOf D) := Sec10.Sec10XProof.isElemAbelian_subgroupOf D hAe
  have hA'card : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf D) = 3 ^ n :=
    ⟨4, by norm_num, by rw [Sec10.Sec10XProof.card_subgroupOf_of_le hAD, hA81]⟩
  have hc'1 : c' ≠ 1 := fun h1 => hc1 (congrArg Subtype.val h1)
  obtain ⟨X₀, hX₀, hK'X₀⟩ := h48 ↥D hS4 (A.subgroupOf D) hA'el hA'card c'
    (Subgroup.mem_subgroupOf.mpr hcA) hc'1 K' hK'at
  obtain ⟨hK'Z, hK'θ⟩ := PartOne.mem_thetaComponentsAt_iff.mp hK'at
  have hle : K' ≤ X₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D) := le_inf hK'X₀ hK'Z
  have hK'in : K' ∈ thetaComponentsIn (X₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D)) :=
    ⟨K'.subgroupOf _, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle
      inf_le_right hK'θ, Subgroup.map_subgroupOf_eq_of_le hle⟩
  have hc'3 : orderOf c' = 3 :=
    (Subgroup.orderOf_mk c _).trans (orderOf_eq_prime (hAe.2 c hcA) hc1)
  let eK : ↥K' ≃* ↥I :=
    (K'.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hK'map)
  have hK'SL : Sec4.IsSLThreePiAt (K' ⧸ aschbacherSolvableCore 3 K') (2 ^ n) :=
    Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eK).symm hISL
  have htype : Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K')
        (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') Blueprint.NativeSporadic.M22 ∨
      Sec4.IsSLThreePi (K' ⧸ aschbacherSolvableCore 3 K') :=
    Or.inr (Or.inr (Or.inr ⟨2 ^ n, hK'SL⟩))
  have hK'eq : K' = I.subgroupOf D := by
    rw [← hK'map, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hYmap : (K' ⊓ Subgroup.centralizer (K' : Set ↥D)).map D.subtype =
      I ⊓ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.map_inf_eq _ _ D.subtype D.subtype_injective, hK'map, hK'eq,
      Sec10.Sec10XProof.centralizer_subgroupOf hID, Subgroup.subgroupOf_map_subtype,
      inf_comm (Subgroup.centralizer (I : Set G)) D, ← inf_assoc, inf_eq_left.mpr hID]
  have hpmap : (inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D))).map
      D.subtype = inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) := by
    rw [SteinbergBY.map_inSubgroup_pCore_of_injective 3 D.subtype D.subtype_injective, hYmap]
  have hZne' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≠ ⊥ := by
    intro hbot
    have h1 := hpmap
    rw [hbot, Subgroup.map_bot, hIZ] at h1
    apply hb1
    have h2 : b ∈ (⊥ : Subgroup G) := h1 ▸ Subgroup.mem_zpowers b
    exact Subgroup.mem_bot.mp h2
  have hZ' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≤
      Subgroup.center ↥D := by
    intro w hw
    have hwG : (w : G) ∈ inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) :=
      hpmap ▸ ⟨w, hw, rfl⟩
    rw [hIZ] at hwG
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwG
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgb : (g : G) * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    simp only [Subgroup.coe_mul, ← hk]
    exact (Commute.zpow_right hgb k).eq
  set Y := X₀.map D.subtype with hY
  have hYmem : Y ∈ thetaComponentsAt 3 b := ⟨X₀, hX₀, rfl⟩
  have hIY : I ≤ Y := hK'map ▸ Subgroup.map_mono hK'X₀
  let eX : ↥X₀ ≃* ↥Y := X₀.equivMapOfInjective D.subtype D.subtype_injective
  refine ⟨Y, hYmem, hIY, ?_⟩
  rcases h426 ↥D hS4 X₀ hX₀ c' hc'3 K' hK'in htype hZne' hZ' with h1 | ⟨m, hm, hX₀m, hK'm⟩ |
    ⟨-, hK'A6⟩
  ·
    left
    have h2 := congrArg (Subgroup.map D.subtype) h1
    rw [Subgroup.map_sup, hK'map, ← inSubgroup_theta_map_subtype] at h2
    exact h2
  ·
    exact Or.inr ⟨m, hm, Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eX) hX₀m,
      Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eK) hK'm⟩
  ·
    exact absurd hK'SL (Sec13.not_isSLThreePiAt_two_pow (Sec13.card_eq_of_isTripleCover_six hK'A6)
      hn)

end Item2130Res3Proof

open Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21
