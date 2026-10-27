module

public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.Quasithin.Background.E2TenKG
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

namespace Pair

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem isSz_of_mulEquiv {A B : Type} [Group A] [Group B] {n : ℕ} (e : A ≃* B) (h : IsSz n B) :
    IsSz n A := by
  obtain ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨f⟩⟩ := h
  exact ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨e.trans f⟩⟩

theorem center_commutator_seven
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Pair X T M V g) {n : ℕ} (hn : 1 < n)
    (hY : IsPSL 2 2 n (StarQuot M X) ∨ IsSz n (StarQuot M X))
    [((PP M V X g).subgroupOf X).Normal] :
    (Subgroup.center ↥(commutator (Xbar M V X g)) = ⊥ ∨
      (IsSz 3 (StarQuot M X) ∧ ∀ z ∈ Subgroup.center ↥(commutator (Xbar M V X g)), z * z = 1)) ∧
    ∀ l ∈ commutator (Xbar M V X g),
      l * l ∈ (Subgroup.center ↥(commutator (Xbar M V X g))).map
        (commutator (Xbar M V X g)).subtype → l * l = 1 := by
  have hXs := isSimpleGroup_of_psl_or_sz hY
  have hXp := commutator_eq_top_of_psl_or_sz hn hY
  have hXna := nonabelian_of_psl_or_sz hn hY
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator (Xbar M V X g ⧸ Jbar M V X g) = ⊤ := commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g) := MulEquiv.isSimpleGroup e
  have hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := h.Jbar_le_center
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator _ hJc hS hsimp hna
  set Lb := commutator (Xbar M V X g) with hLb
  have : Group.IsPerfect ↥Lb := hLq.1
  set eX : ↥Lb ⧸ Subgroup.center ↥Lb ≃* StarQuot M X := eL.trans e
  have hcase : Subgroup.center ↥Lb = ⊥ ∨
      (IsSz 3 (StarQuot M X) ∧ ∀ z ∈ Subgroup.center ↥Lb, z * z = 1) := by
    rcases hY with hY | hY
    · left
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · have hZ2 := sq_eq_one_of_mem_center_isPSL_two hY eX
        have hP2 : IsPGroup 2 (Subgroup.center ↥Lb) := fun z =>
          ⟨1, Subtype.ext (by simpa [pow_two] using hZ2 z z.2)⟩
        obtain ⟨e5⟩ := nonempty_alt_five_of_isPSL_two hY
        obtain ⟨v₁, hv₁, v₂, hv₂, h₁, h₂, h₁₂⟩ := h.exists_two_Vbar hsimp hna
        exact center_commutator_eq_bot_of_alt_five _ hKG3 hJc hS hsimp hna (e.trans e5) hP2
          h.Vbar_sq hv₁ hv₂ h₁ h₂ h₁₂
      · exact center_eq_bot_of_isPSL hn3 hY eX
    · by_cases hn3 : n = 3
      · subst hn3
        exact Or.inr ⟨hY, sq_eq_one_of_mem_center_isSz_three hY eX⟩
      · exact Or.inl (center_eq_bot_of_isSz hn3 hY eX)
  have hlift : ∀ l ∈ Lb, l * l ∈ (Subgroup.center ↥Lb).map Lb.subtype → l * l = 1 := by
    by_cases hb : Subgroup.center ↥Lb = ⊥
    · exact lift_of_center_eq_bot hb
    · obtain ⟨hSz, hZ2⟩ := hcase.resolve_left hb
      exact lift_of_involutions_lift hZ2 (hKG1 ↥Lb hLq hb (isSz_of_mulEquiv eX hSz)).1
  exact ⟨hcase, hlift⟩

theorem e2_10_seven
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Pair X T M V g) {n : ℕ} (hn : 1 < n)
    (hY : IsPSL 2 2 n (StarQuot M X) ∨ IsSz n (StarQuot M X)) :
    kerIn M X = pCoreOf 2 X ∧
      (∃ E : Subgroup G, PP M V X g ≤ E ∧ E ≤ X ∧ (∀ x ∈ E, x ^ 2 ∈ PP M V X g) ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ PP M V X g) ∧
        ⁅E, oTwoUpper X⁆ ≤ PP M V X g ∧
        E ⊓ (oTwoUpper X ⊔ PP M V X g) = PP M V X g ∧
        E ⊔ (oTwoUpper X ⊔ PP M V X g) = X) ∧
      ((pCoreOf 2 (oTwoUpper X ⊔ PP M V X g) = PP M V X g ∧
          ∃ (_ : ((PP M V X g).subgroupOf (oTwoUpper X ⊔ PP M V X g)).Normal),
            Nonempty (↥(oTwoUpper X ⊔ PP M V X g) ⧸
                (PP M V X g).subgroupOf (oTwoUpper X ⊔ PP M V X g) ≃* StarQuot M X)) ∨
        ∃ Z : Subgroup G, PP M V X g ≤ Z ∧ Z ≤ oTwoUpper X ⊔ PP M V X g ∧
          (∀ z ∈ Z, ∃ k : ℕ, z ^ 2 ^ k ∈ PP M V X g) ∧
          ⁅Z, oTwoUpper X ⊔ PP M V X g⁆ ≤ PP M V X g ∧
          ⁅oTwoUpper X ⊔ PP M V X g, oTwoUpper X ⊔ PP M V X g⁆ ⊔ PP M V X g =
            oTwoUpper X ⊔ PP M V X g ∧
          ∃ (_ : (Z.subgroupOf (oTwoUpper X ⊔ PP M V X g)).Normal),
            IsSz 3 (↥(oTwoUpper X ⊔ PP M V X g) ⧸
              Z.subgroupOf (oTwoUpper X ⊔ PP M V X g))) := by
  have hXs := isSimpleGroup_of_psl_or_sz hY
  have hXp := commutator_eq_top_of_psl_or_sz hn hY
  have hXna := nonabelian_of_psl_or_sz hn hY
  have := h.normal_P
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator (Xbar M V X g ⧸ Jbar M V X g) = ⊤ := commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g) := MulEquiv.isSimpleGroup e
  have hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := h.Jbar_le_center
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator _ hJc hS hsimp hna
  set Lb := commutator (Xbar M V X g) with hLb
  have : Group.IsPerfect ↥Lb := hLq.1
  set eX : ↥Lb ⧸ Subgroup.center ↥Lb ≃* StarQuot M X := eL.trans e
  obtain ⟨hcase, hlift⟩ := h.center_commutator_seven hKG1 hKG3 hn hY
  obtain ⟨hZ, hsq, hJ⟩ := h.center_quot_facts hXs hXp hXna hlift
  have hLJ := commutator_sup_eq_top _ hS
  have hZc := map_center_commutator_eq _ hJc hS hsimp hna
  set Zc := (Subgroup.center ↥Lb).map Lb.subtype with hZcdef
  have hJ2 : ∀ j ∈ Jbar M V X g, j * j = 1 := fun j hj => hsq j (hZ ▸ hj)
  have hsqL : ∀ x : Xbar M V X g, x * x ∈ Lb := by
    intro x
    obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hLJ ▸ Subgroup.mem_top x)
    have hjc := Subgroup.mem_center_iff.1 (hJc hj)
    have e1 : l * j * (l * j) = l * l * (j * j) := by
      calc l * j * (l * j) = l * (j * l) * j := by group
        _ = l * (l * j) * j := by rw [hjc l]
        _ = l * l * (j * j) := by group
    rw [e1, hJ2 j hj, mul_one]
    exact Lb.mul_mem hl hl
  have hH := h.oTwoUpper_sup_P_eq hLq.1 hsqL
  have hZcJ : Zc ≤ Jbar M V X g := hZc ▸ inf_le_right
  have hZcL : Zc ≤ Lb := hZc ▸ inf_le_left
  obtain ⟨Eb, hEJ, hEZ, hEZJ⟩ := exists_compl_of_central hJc hJ2 hZcJ
  have hEc : Eb ≤ Subgroup.center (Xbar M V X g) := hEJ.trans hJc
  refine ⟨hJ.symm, ⟨pre M V X g Eb, h.P_le_pre _, pre_le_X _, ?_, ?_,
    commutator_pre_le hEc (oTwoUpper_le X), ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨hxX, hxE⟩ := mem_pre.1 hx
    have hx2 : x ^ 2 ∈ X := X.pow_mem hxX 2
    rw [← piX_eq_one_iff hx2]
    have e1 : (⟨x ^ 2, hx2⟩ : X) = ⟨x, hxX⟩ * ⟨x, hxX⟩ := Subtype.ext (pow_two x)
    rw [e1, map_mul]
    exact hJ2 _ (hEJ hxE)
  · intro x hx y hy
    obtain ⟨hxX, hxE⟩ := mem_pre.1 hx
    obtain ⟨hyX, -⟩ := mem_pre.1 hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX)) (X.inv_mem hyX)
    rw [← piX_eq_one_iff hc]
    have e1 : (⟨x * y * x⁻¹ * y⁻¹, hc⟩ : X) =
        ⟨x, hxX⟩ * ⟨y, hyX⟩ * (⟨x, hxX⟩ : X)⁻¹ * (⟨y, hyX⟩ : X)⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← Subgroup.mem_center_iff.1 (hEc hxE), mul_inv_cancel_right, mul_inv_cancel]
  · rw [hH]
    refine le_antisymm (fun x hx => ?_) (le_inf (h.P_le_pre _) (h.P_le_pre _))
    obtain ⟨hxX, hxE⟩ := mem_pre.1 hx.1
    obtain ⟨hxX', hxL⟩ := mem_pre.1 hx.2
    have h1 : piX M V X g ⟨x, hxX⟩ ∈ Eb ⊓ Zc := ⟨hxE, by rw [hZc]; exact ⟨hxL, hEJ hxE⟩⟩
    rw [hEZ, Subgroup.mem_bot] at h1
    exact (piX_eq_one_iff hxX).1 h1
  · rw [hH]
    refine le_antisymm (sup_le (pre_le_X _) (pre_le_X _)) (fun x hxX => ?_)
    have hx : piX M V X g ⟨x, hxX⟩ ∈ Eb ⊔ Lb := by
      have h1 : Eb ⊔ Lb = ⊤ := by
        rw [eq_top_iff, ← hLJ, sup_le_iff]
        refine ⟨le_sup_right, ?_⟩
        rw [← hEZJ]
        exact sup_le le_sup_left (hZcL.trans le_sup_right)
      rw [h1]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, l, hl, hal⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) a
    have hyE : (y : G) ∈ pre M V X g Eb := mem_pre.2 ⟨y.2, ha⟩
    have hz : (y : G)⁻¹ * x ∈ pre M V X g Lb := by
      refine mem_pre.2 ⟨X.mul_mem (X.inv_mem y.2) hxX, ?_⟩
      have e1 : (⟨(y : G)⁻¹ * x, X.mul_mem (X.inv_mem y.2) hxX⟩ : X) = y⁻¹ * ⟨x, hxX⟩ :=
        Subtype.ext rfl
      rw [e1, map_mul, map_inv, ← hal]
      simpa using hl
    have e2 : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hyE hz
  · rw [hH]
    by_cases hb : Subgroup.center ↥Lb = ⊥
    · left
      let eLX : ↥Lb ≃* StarQuot M X :=
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hb.symm)).trans eX
      have hsimpL : IsSimpleGroup ↥Lb := MulEquiv.isSimpleGroup eLX
      refine ⟨h.pCoreOf_pre_eq hsimpL hLq.1, ?_⟩
      obtain ⟨hN, ⟨eQ⟩⟩ := exists_quot_equiv (M := M) (V := V) (g := g) Lb
      exact ⟨hN, ⟨eQ.trans eLX⟩⟩
    · right
      obtain ⟨hSz, hZ2⟩ := hcase.resolve_left hb
      refine ⟨pre M V X g Zc, h.P_le_pre _, pre_mono hZcL, ?_, ?_, ?_, ?_⟩
      · intro z hz
        obtain ⟨hzX, hzZ⟩ := mem_pre.1 hz
        refine ⟨1, ?_⟩
        have hz2 : z ^ 2 ^ 1 ∈ X := X.pow_mem hzX _
        rw [← piX_eq_one_iff hz2]
        have e1 : (⟨z ^ 2 ^ 1, hz2⟩ : X) = ⟨z, hzX⟩ * ⟨z, hzX⟩ := Subtype.ext (by simp [pow_two])
        rw [e1, map_mul]
        obtain ⟨c, hc, hcz⟩ := hzZ
        rw [← hcz]
        exact congrArg Subtype.val (hZ2 c hc)
      · rw [Subgroup.commutator_le]
        intro z hz y hy
        obtain ⟨hzX, hzZ⟩ := mem_pre.1 hz
        obtain ⟨hyX, hyL⟩ := mem_pre.1 hy
        have hc : ⁅z, y⁆ ∈ X := by
          rw [commutatorElement_def]
          exact X.mul_mem (X.mul_mem (X.mul_mem hzX hyX) (X.inv_mem hzX)) (X.inv_mem hyX)
        rw [← piX_eq_one_iff hc]
        have e1 : (⟨⁅z, y⁆, hc⟩ : X) = ⁅(⟨z, hzX⟩ : X), ⟨y, hyX⟩⁆ := Subtype.ext rfl
        rw [e1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        obtain ⟨c, hc, hcz⟩ := hzZ
        have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨_, hyL⟩)
        rw [← hcz]
        exact this.symm
      · refine le_antisymm (sup_le (Subgroup.commutator_le.2 fun a ha b hb => ?_)
          (h.P_le_pre _)) ?_
        · rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
            (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
        intro x hx
        obtain ⟨hxX, hxL⟩ := mem_pre.1 hx
        have hLL : ⁅Lb, Lb⁆ = Lb := by
          rw [← Subgroup.map_subtype_commutator, hLq.1.commutator_eq_top,
            ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        have hxL' : piX M V X g ⟨x, hxX⟩ ∈ ⁅Lb, Lb⁆ := by rw [hLL]; exact hxL
        have himg : ⁅Lb, Lb⁆ ≤ (⁅pre M V X g Lb, pre M V X g Lb⁆.subgroupOf X).map
            (piX M V X g) := by
          rw [Subgroup.commutator_le]
          intro a ha b hb'
          obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) a
          obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) b
          refine ⟨⁅a', b'⁆, Subgroup.mem_subgroupOf.2 ?_, map_commutatorElement _ _ _⟩
          exact Subgroup.commutator_mem_commutator (mem_pre.2 ⟨a'.2, ha⟩) (mem_pre.2 ⟨b'.2, hb'⟩)
        obtain ⟨y, hy0, hyx⟩ := himg hxL'
        have hy : (y : G) ∈ ⁅pre M V X g Lb, pre M V X g Lb⁆ := hy0
        have hP : (y : G)⁻¹ * x ∈ PP M V X g := by
          have h1 := QuotientGroup.eq.1 hyx
          rw [Subgroup.mem_subgroupOf] at h1
          simpa using h1
        have e2 : x = (y : G) * ((y : G)⁻¹ * x) := by group
        rw [e2]
        exact Subgroup.mul_mem_sup hy hP
      · have hZcL' : Zc.subgroupOf Lb = Subgroup.center ↥Lb :=
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
        have : (Zc.subgroupOf Lb).Normal := by
          rw [hZcL']
          infer_instance
        obtain ⟨hN, ⟨eQ⟩⟩ := exists_quot_equiv_pre (M := M) (V := V) (g := g) (A := Lb) (B := Zc)
        exact ⟨hN, isSz_of_mulEquiv (eQ.trans ((QuotientGroup.quotientMulEquivOfEq hZcL').trans
          eX)) hSz⟩

theorem center_seven
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Pair X T M V g) {n : ℕ} (hn : 1 < n)
    (hY : IsPSL 2 2 n (StarQuot M X) ∨ IsSz n (StarQuot M X))
    [((PP M V X g).subgroupOf X).Normal] :
    Subgroup.center (Xbar M V X g) = Jbar M V X g ∧
      (∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1) ∧ pCoreOf 2 X = kerIn M X :=
  h.center_quot_facts (isSimpleGroup_of_psl_or_sz hY) (commutator_eq_top_of_psl_or_sz hn hY)
    (nonabelian_of_psl_or_sz hn hY) (h.center_commutator_seven hKG1 hKG3 hn hY).2

end Pair

end E2

theorem ASInputs.as_E_2_10_seven_of
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One) :
    ASInputs.AS_E_2_10_seven := by
  intro G _ _ X T M V g h ⟨n, hn, hY⟩
  exact h.e2_10_seven hKG1 hKG3 hn hY

end CFSG.Quasithin
