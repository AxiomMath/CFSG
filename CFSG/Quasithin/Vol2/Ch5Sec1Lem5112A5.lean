module

public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.H13.A7Nat1238QTabList
public import CFSG.Quasithin.Background.A3Structure39Odd
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def A314OverList (X : Type) [Group X] : Prop :=
  (IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7))) ∨
    (IsPSL 2 5 2 X ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      IsPSL 2 p 1 X) ∨
    (∃ s : Bool, IsPSLEps3 s 5 1 X ∨ IsSLEps3 s 5 X) ∨ (IsPSL 3 5 1 X ∨ IsSL3 5 X) ∨
    (IsSporadic .M22 X ∨ IsHat X (NativeSporadic.Carrier .M22)) ∨ IsSporadic .M23 X ∨
    IsSporadic .J1 X ∨ IsSporadic .J2 X ∨ IsSporadic .J4 X ∨ IsSporadic .HS X ∨
    IsSporadic .Ru X

@[expose] def A314NotLie2 : Prop :=
  (∀ (X : Type) [Group X] [Finite X], A314OverList X → ¬ IsLieTypeChar2 X) ∧
    ∀ (X : Type) [Group X], IsLieTypeChar2 X → IsSimpleGroup (X ⧸ Subgroup.center X)

theorem IsLieTypeChar2.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLieTypeChar2 X) : IsLieTypeChar2 Y := by
  obtain ⟨t, n, f, hadm, hm⟩ := h
  exact ⟨t, n, f, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hm⟩

theorem isRank2LieChar2_of_a314One {Y : Type} [Group Y]
    (h : IsPSL 3 2 2 Y ∨ IsSL3 4 Y ∨ IsPSp4 2 2 Y ∨ IsG2 2 2 Y ∨ Is3D4 2 2 Y) :
    IsRank2LieChar2 Y := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨2, Or.inl ⟨by norm_num, h⟩⟩
  · exact Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩
  · exact Or.inl ⟨2, Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))⟩
  · exact Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩)))⟩
  · exact Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, h⟩))))⟩

theorem nontrivial_sl2 {p : ℕ} [Fact (2 < p)] :
    Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  refine ⟨⟨-1, 1, fun h => ?_⟩⟩
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h1
  exact ZMod.neg_one_ne_one h1

theorem not_isSimpleGroup_sl2 {p : ℕ} [hp : Fact (2 < p)] :
    ¬ IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  intro hs
  have hNe : NeZero p := ⟨by have := hp.out; omega⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · have hmem : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      ext i j
      simp [Matrix.SpecialLinearGroup.coe_neg]
    rw [h, Subgroup.mem_bot] at hmem
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hmem
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h1
    exact ZMod.neg_one_ne_one h1
  · let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let l : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have hu : u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      rw [h]
      exact Subgroup.mem_top u
    have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p))) (Subgroup.mem_center_iff.mp hu l)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
    have h4 := congrFun (congrFun h3 0) 0
    have : Fact (1 < p) := ⟨by have := hp.out; omega⟩
    simp [u, l, Matrix.mul_apply, Fin.sum_univ_two] at h4

theorem false_of_a314Thirteen {Γ : Type} [Group Γ] [Finite Γ] {B L : Subgroup Γ}
    (hBL : B < L) (hB5 : IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B))
    (hLeq : L = B ⊔ oddCoreSub L) (hq : CFSG.Open.IsQuasisimple ↥L) : False := by
  classical
  set N : Subgroup ↥L := CFSG.oddCore ↥L with hN
  have hNn : N.Normal := inferInstance
  have hsup : B.subgroupOf L ⊔ N = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBL.le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hLeq.symm
  have hperf : (⊤ : Subgroup ↥L) ≤ ⁅(⊤ : Subgroup ↥L), ⊤⁆ := by
    rw [← commutator_def, hq.1]
  obtain ⟨-, hsimple⟩ := hq
  have := hsimple
  have hNmap : (N.map (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have key : ∀ U : Subgroup ↥L, U ⊔ Subgroup.center ↥L = ⊤ → (⊤ : Subgroup ↥L) ≤ U := by
    intro U hU
    have hmem : ∀ x : ↥L, ∃ u ∈ U, ∃ z ∈ Subgroup.center ↥L, u * z = x := by
      intro x
      have hx : x ∈ ((U ⊔ Subgroup.center ↥L : Subgroup ↥L) : Set ↥L) := by
        rw [hU]
        exact Subgroup.mem_top x
      rw [Subgroup.mul_normal] at hx
      exact Set.mem_mul.mp hx
    refine hperf.trans ((Subgroup.commutator_le).mpr fun x _ y _ => ?_)
    obtain ⟨u₁, hu₁, z₁, hz₁, rfl⟩ := hmem x
    obtain ⟨u₂, hu₂, z₂, hz₂, rfl⟩ := hmem y
    have h1 : z₁ * (u₂ * z₂) = (u₂ * z₂) * z₁ :=
      (Subgroup.mem_center_iff.mp hz₁ (u₂ * z₂)).symm
    have h2 : z₂ * u₁⁻¹ = u₁⁻¹ * z₂ := (Subgroup.mem_center_iff.mp hz₂ u₁⁻¹).symm
    have e : ⁅u₁ * z₁, u₂ * z₂⁆ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ :=
      calc ⁅u₁ * z₁, u₂ * z₂⁆ = u₁ * (z₁ * (u₂ * z₂)) * z₁⁻¹ * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = u₁ * ((u₂ * z₂) * z₁) * z₁⁻¹ * u₁⁻¹ * z₂⁻¹ * u₂⁻¹ := by rw [h1]
        _ = u₁ * u₂ * (z₂ * u₁⁻¹) * z₂⁻¹ * u₂⁻¹ := by group
        _ = u₁ * u₂ * (u₁⁻¹ * z₂) * z₂⁻¹ * u₂⁻¹ := by rw [h2]
        _ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by group
    rw [e]
    exact U.mul_mem (U.mul_mem (U.mul_mem hu₁ hu₂) (U.inv_mem hu₁)) (U.inv_mem hu₂)
  rcases hNmap.eq_bot_or_eq_top with h | h
  ·
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hBZ : B.subgroupOf L ⊔ Subgroup.center ↥L = ⊤ :=
      eq_top_iff.mpr (hsup.ge.trans (sup_le_sup_left h _))
    have hLB := key _ hBZ
    apply hBL.ne
    apply le_antisymm hBL.le
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ B.subgroupOf L := hLB (Subgroup.mem_top _)
    exact Subgroup.mem_subgroupOf.mp this
  ·
    have hNZ : N ⊔ Subgroup.center ↥L = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥L)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hNtop : N = ⊤ := eq_top_iff.mpr (key _ hNZ)
    have hodd : Odd (Nat.card ↥L) := by
      have h0 := A38.odd_card_oddCore ↥L
      rw [← hN, hNtop, Subgroup.card_top] at h0
      exact h0
    have hoddB : Odd (Nat.card ↥B) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hBL.le)
    have hOB : CFSG.oddCore ↥B = ⊤ :=
      eq_top_iff.mpr (le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hoddB⟩)
    obtain ⟨e5⟩ := hB5
    have : Subsingleton (↥B ⧸ CFSG.oddCore ↥B) := by
      rw [hOB]
      exact QuotientGroup.subsingleton_quotient_top
    have : Fact (2 < 5) := ⟨by norm_num⟩
    have := nontrivial_sl2 (p := 5)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    exact hab (e5.symm.injective (Subsingleton.elim _ _))

namespace EmbLoc

variable {G : Type} [Group G] [Finite G]
variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem a5_cases (hF : A314Facts) (hNL : A314NotLie2)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (hL2 : LieModel (O2Q K) .PSL 2 2 2) :
    IsRank2LieChar2 (O2Q Kh) ∨
      (¬ IsLieTypeChar2 (O2Q Kh) ∧
        A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) := by
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
  have hA : IsAlt 5 (↥(modO2Image X K) ⧸ CFSG.solvableRadical ↥(modO2Image X K)) :=
    A7.isAlt_quot_solvableRadical_of_surj ⟨eA⟩ (barMap_surjective l.le_X)
      (isPGroup_ker_barMap _)
  have hTL : IsSylowTwoOf (o2Img X S ⊓ modO2Image X Kh) (modO2Image X Kh) :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp l.hatBar_cComp) l.sylowBar
  have hB1 : modO2Image X K ∈ lFamily (o2Img X S ⊓ modO2Image X Kh) :=
    cComp_mem_of_le l.bar_lFamily le_sup_left (sup_le_sup_left inf_le_left _)
  have hlt := l.bar_lt
  obtain ⟨eH⟩ := l.hat_equiv
  have hL' := l.hatBar_cComp
  have h314 : A314Statement (o2Img X S) (modO2Image X K) (modO2Image X Kh) := by
    rcases l.cases h312 with hc | hnq
    · exact A314.of_case hF ⟨l.bar_lFamily, hlt, hTL, hB1, hA⟩ hc
    · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
      rcases A314.nonquasi_case (h36 _ hQ _ hL') (A312.not_quasisimple_of_nonquasi hnq) hlt hA
        hnq with h13 | h14
      · unfold A314Statement
        iterate 12 right
        left
        exact h13
      · unfold A314Statement
        iterate 13 right
        exact h14
  have hnl : ∀ (hL : ¬ IsLieTypeChar2 ↥(modO2Image X Kh)),
      IsRank2LieChar2 (O2Q Kh) ∨
        (¬ IsLieTypeChar2 (O2Q Kh) ∧
          A314Statement (o2Img X S) (o2Img X K) (o2Img X Kh)) :=
    fun hL => Or.inr ⟨fun h => hL (IsLieTypeChar2.of_mulEquiv eH h), h314⟩
  have hlist : A314OverList ↥(modO2Image X Kh) → ¬ IsLieTypeChar2 ↥(modO2Image X Kh) :=
    hNL.1 _
  have h314' := h314
  unfold A314Statement at h314'
  rcases h314' with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, h4, -⟩ | ⟨-, h5, -⟩ |
      ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ | ⟨-, h11, -⟩ |
      ⟨-, -, h12, -⟩ | ⟨hB5, hLeq⟩ | ⟨-, h14⟩
  · exact Or.inl (IsRank2LieChar2.of_mulEquiv eH.symm (isRank2LieChar2_of_a314One h1))
  · exact hnl (hlist (Or.inl h2))
  · exact hnl (hlist (Or.inr (Or.inl h3)))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inl h4))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h9)))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h10))))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h11)))))))))))
  · exact hnl (hlist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h12)))))))))))
  · refine hnl fun hLie => ?_
    have hs := hNL.2 _ hLie
    exact false_of_a314Thirteen hlt hB5 hLeq ⟨by
      have : Group.IsPerfect ↥(modO2Image X Kh) := A36A.isPerfect_of_mem_cComp hL'
      exact this.commutator_eq_top, hs⟩
  ·
    obtain ⟨p, hp, hp5, -, ⟨eSL⟩⟩ := h14
    refine hnl fun hLie => ?_
    have hs := hNL.2 _ hLie
    have : Group.IsPerfect ↥(modO2Image X Kh) := A36A.isPerfect_of_mem_cComp hL'
    have : IsSimpleGroup (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh)) := hs
    have hq : CFSG.IsQuasisimple ↥(modO2Image X Kh) := by
      have : Group.IsPerfect (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      have hnc := Group.IsPerfect.not_isMulCommutative
        (↥(modO2Image X Kh) ⧸ Subgroup.center ↥(modO2Image X Kh))
      refine ⟨inferInstance, hs, ?_⟩
      by_contra hall
      push Not at hall
      exact hnc ⟨⟨hall⟩⟩
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
    obtain ⟨hFO, -, hcases, -, -⟩ := (h36 _ hQ _ hL').2.1
    have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with rfl | ho
      · norm_num at hp5
      · rcases hp.two_le.lt_or_eq with h2 | h2
        · exact h2
        · subst h2
          exact absurd ho (by decide)
    have : Fact (2 < p) := ⟨hp2⟩
    rcases hcases with ⟨hgF, -⟩ | ⟨hFZ, -, -⟩
    ·
      have hOtop : CFSG.oddCore ↥(modO2Image X Kh) = ⊤ := by
        rw [← hFO, ← hgF, A36A.generalizedFitting_eq_top hq]
      have : Subsingleton (↥(modO2Image X Kh) ⧸ CFSG.oddCore ↥(modO2Image X Kh)) := by
        rw [hOtop]
        exact QuotientGroup.subsingleton_quotient_top
      have := nontrivial_sl2 (p := p)
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
      exact hab (eSL.symm.injective (Subsingleton.elim _ _))
    ·
      have hOZ : CFSG.oddCore ↥(modO2Image X Kh) = Subgroup.center ↥(modO2Image X Kh) :=
        hFO.symm.trans hFZ
      have : IsSimpleGroup (↥(modO2Image X Kh) ⧸ CFSG.oddCore ↥(modO2Image X Kh)) :=
        (QuotientGroup.quotientMulEquivOfEq hOZ).isSimpleGroup
      exact not_isSimpleGroup_sl2 (p := p) (eSL.symm.isSimpleGroup)

end EmbLoc

end CFSG.Quasithin.H13
