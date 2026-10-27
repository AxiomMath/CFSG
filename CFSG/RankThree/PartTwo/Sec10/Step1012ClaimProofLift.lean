module

import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec9.Item95
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
public import CFSG.RankThree.PartTwo.Sec4.Statements426

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory

namespace Step1012ClaimProof

theorem card_of_isSLThreePiAt_four {Y : Type} [Group Y] (hY : Sec4.IsSLThreePiAt Y 4) :
    Nat.card Y = 60480 := by
  obtain ⟨F, _, _, ⟨hF, -, ⟨e⟩⟩ | ⟨hF, h3, -⟩⟩ := hY
  · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hF]
    norm_num
  · norm_num at h3

theorem eq_two_of_isSLThreePiAt {Y : Type} [Group Y] (hY : Sec4.IsSLThreePiAt Y 4) {n : ℕ}
    (hn : 1 ≤ n) (hYn : Sec4.IsSLThreePiAt Y (2 ^ n)) : n = 2 := by
  have hc := card_of_isSLThreePiAt_four hY
  obtain ⟨F, _, _, ⟨hF, h3, ⟨e⟩⟩ | ⟨hF, h3, ⟨e⟩⟩⟩ := hYn
  · have hc' := Nat.card_congr e.toEquiv
    rw [hc, CFSG.SectionRank.OddCover.card_statedSL_three, hF] at hc'
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · norm_num at hc'
      · rfl
    · have hq : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      have h1 : 512 ≤ (2 ^ n) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
      have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
        have := Nat.pow_le_pow_left hq 2
        omega
      have h4 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * n)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    have hc' := Nat.card_congr e.toEquiv
    rw [hc, CFSG.SectionRank.OddCover.card_statedSU_three (p := 2) (f := n) hF] at hc'
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num at hc'
    · have hq : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      have h1 : 512 ≤ (2 ^ n) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
      have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
        have := Nat.pow_le_pow_left hq 2
        omega
      have h4 : 513 ≤ (2 ^ n) ^ 3 + 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {e : G}
  {R : Subgroup G}

theorem exists_mem_thetaComponentsAt_of_K (h48 : Sec4.Item4_8) (h426 : Sec4.Item4_26Theta)
    (h97 : Sec9.Item97) (h : Sec10Std G A c L e R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn
      (Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G)))
    (htype : Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZ : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.centralizer (Subgroup.centralizer ({d} : Set G) : Set G)) :
    ∃ X ∈ thetaComponentsAt 3 d, K ≤ X ∧
      (Sec4.IsSLThreePiAt (X ⧸ aschbacherSolvableCore 3 X) 4 ∨
        Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) (alternatingGroup (Fin 6)) ∨
        Sec4.IsSLThreePiAt (X ⧸ aschbacherSolvableCore 3 X) 64 ∨
        (Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) Blueprint.NativeSporadic.ON ∧
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L e R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hed : e * d = d * e := h.comm h.a_mem hdA
  set D := Subgroup.centralizer ({d} : Set G) with hD
  have hS4 : SectionFourHyp ↥D :=
    h.toTheoremFourHyp.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hd1)
  set e' : ↥D := ⟨e, Subgroup.mem_centralizer_singleton_iff.mpr hed⟩ with he'
  set Z₂ := Subgroup.centralizer ({e'} : Set ↥D) with hZ₂
  set CB := Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G) with hCB
  have hZ₂map : Z₂.map D.subtype = CB := by
    rw [hZ₂, SteinbergBY.map_subtype_centralizer_singleton D e', hCB,
      Subgroup.centralizer_closure]
    ext x
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    tauto
  obtain ⟨hKCB, hK₁⟩ := mem_thetaComponentsIn_iff.mp hK
  let ψ : ↥CB ≃* ↥Z₂ := (MulEquiv.subgroupCongr hZ₂map.symm).trans
    (Z₂.equivMapOfInjective D.subtype D.subtype_injective).symm
  have hψ : (D.subtype.comp Z₂.subtype).comp ψ.toMonoidHom = CB.subtype := by
    ext x
    have h1 := (Z₂.equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hZ₂map.symm x)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  set T₂ := (K.subgroupOf CB).map ψ.toMonoidHom with hT₂
  have hT₂mem : T₂ ∈ thetaComponents 3 ↥Z₂ :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three ψ hK₁
  set K' := T₂.map Z₂.subtype with hK'
  have hK'at : K' ∈ thetaComponentsAt 3 e' := ⟨T₂, hT₂mem, rfl⟩
  have hK'map : K'.map D.subtype = K := by
    rw [hK', hT₂, Subgroup.map_map, Subgroup.map_map, hψ,
      Subgroup.map_subgroupOf_eq_of_le hKCB]
  have hKD : K ≤ D := hK'map ▸ Subgroup.map_subtype_le K'
  have hAD : A ≤ D := Sec10XProof.le_centralizer_of_mem h hdA
  have hA'el : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf D) :=
    Sec10XProof.isElemAbelian_subgroupOf D h.mem_partTwoF.1
  have hA'card : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf D) = 3 ^ n :=
    ⟨3, le_rfl, by rw [Sec10XProof.card_subgroupOf_of_le hAD, h.card_eq]; norm_num⟩
  have he'1 : e' ≠ 1 := fun h1 => h.a_ne_one (congrArg Subtype.val h1)
  obtain ⟨X₀, hX₀, hK'X₀⟩ := h48 ↥D hS4 (A.subgroupOf D) hA'el hA'card e'
    (Subgroup.mem_subgroupOf.mpr h.a_mem) he'1 K' hK'at
  obtain ⟨hK'Z, hK'θ⟩ := PartOne.mem_thetaComponentsAt_iff.mp hK'at
  have hle : K' ≤ X₀ ⊓ Subgroup.centralizer ({e'} : Set ↥D) := le_inf hK'X₀ hK'Z
  have hK'in : K' ∈ thetaComponentsIn (X₀ ⊓ Subgroup.centralizer ({e'} : Set ↥D)) :=
    ⟨K'.subgroupOf _, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle
      inf_le_right hK'θ, Subgroup.map_subgroupOf_eq_of_le hle⟩
  have he'3 : orderOf e' = 3 :=
    (Subgroup.orderOf_mk e _).trans (orderOf_eq_prime (h.pow_three h.a_mem) h.a_ne_one)
  let eK : ↥K' ≃* ↥K :=
    (K'.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hK'map)
  have htype' : Sec4.IsSLThreePiAt (K' ⧸ aschbacherSolvableCore 3 K') 4 ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') (alternatingGroup (Fin 6)) := by
    rcases htype with hSL | hA6
    · exact Or.inl (Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eK).symm hSL)
    · exact Or.inr (Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK).symm hA6)
  have htype'' : Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K')
        (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') Blueprint.NativeSporadic.M22 ∨
      Sec4.IsSLThreePi (K' ⧸ aschbacherSolvableCore 3 K') := by
    rcases htype' with hSL | hA6
    · exact Or.inr (Or.inr (Or.inr ⟨4, hSL⟩))
    · exact Or.inl hA6
  have hK'eq : K' = K.subgroupOf D := by
    rw [← hK'map, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hYmap : (K' ⊓ Subgroup.centralizer (K' : Set ↥D)).map D.subtype =
      K ⊓ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.map_inf_eq _ _ D.subtype D.subtype_injective, hK'map, hK'eq,
      Sec10XProof.centralizer_subgroupOf hKD, Subgroup.subgroupOf_map_subtype,
      inf_comm (Subgroup.centralizer (K : Set G)) D, ← inf_assoc, inf_eq_left.mpr hKD]
  have hpmap : (inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D))).map
      D.subtype = inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [SteinbergBY.map_inSubgroup_pCore_of_injective 3 D.subtype D.subtype_injective, hYmap]
  have hZne' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≠ ⊥ := by
    intro hb
    apply hZne
    rw [← hpmap, hb, Subgroup.map_bot]
  have hZ' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≤
      Subgroup.center ↥D := by
    intro w hw
    have hwG : (w : G) ∈ inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) :=
      hpmap ▸ ⟨w, hw, rfl⟩
    have h1 := hZ hwG
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 g g.2)
  set X := X₀.map D.subtype with hX
  have hXmem : X ∈ thetaComponentsAt 3 d := ⟨X₀, hX₀, rfl⟩
  have hKX : K ≤ X := hK'map ▸ Subgroup.map_mono hK'X₀
  let eX : ↥X₀ ≃* ↥X := X₀.equivMapOfInjective D.subtype D.subtype_injective
  refine ⟨X, hXmem, hKX, ?_⟩
  rcases h426 ↥D hS4 X₀ hX₀ e' he'3 K' hK'in htype'' hZne' hZ' with h1 | ⟨n, hn, hX₀n, hK'n⟩ |
    ⟨hON, hK'A6⟩
  ·
    obtain ⟨f⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hK'X₀ h1
    let f' : K' ⧸ aschbacherSolvableCore 3 K' ≃* X ⧸ aschbacherSolvableCore 3 X :=
      f.trans (Sec14.quotThetaEquiv eX)
    rcases htype' with hSL | hA6
    · exact Or.inl (Sec9.isSLThreePiAt_of_mulEquiv f' hSL)
    · exact Or.inr (Or.inl (Sec13.isTripleCover_of_mulEquiv f' hA6))
  ·
    rcases htype' with hSL | hA6
    · have hn2 := eq_two_of_isSLThreePiAt hSL hn hK'n
      subst hn2
      exact Or.inr (Or.inr (Or.inl (Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eX)
        hX₀n)))
    · exact absurd hK'n (Sec13.not_isSLThreePiAt_two_pow (Sec13.card_eq_of_isTripleCover_six hA6)
        hn)
  · exact Or.inr (Or.inr (Or.inr ⟨Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eX) hON,
      Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK) hK'A6⟩))

end Step1012ClaimProof

end CFSG.RankThree.PartTwo.Sec10
