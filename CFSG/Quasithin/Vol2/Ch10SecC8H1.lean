module

public import CFSG.Quasithin.Vol2.Ch10SecC8Z
public import CFSG.Quasithin.Vol2.Ch10SecC8H1A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem indecomp_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    [IsMulCommutative ↥(fsuUL T L I)] (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    {A B : Subgroup G} (hA : A ≤ fsuUL T L I) (hB : B ≤ fsuUL T L I)
    (hAL : L ≤ Subgroup.normalizer (A : Set G)) (hBL : L ≤ Subgroup.normalizer (B : Set G))
    (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = fsuUL T L I) : A = ⊥ ∨ B = ⊥ := by
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hinv : ∀ {C : Subgroup G}, L ≤ Subgroup.normalizer (C : Set G) →
      ∀ g ∈ autOn L (fsuUL T L I), ∀ c ∈ C.subgroupOf (fsuUL T L I),
        g c ∈ C.subgroupOf (fsuUL T L I) := by
    intro C hC g hg c hc
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    change (x : G) * c * (x : G)⁻¹ ∈ C
    exact (Subgroup.mem_normalizer_iff.mp (hC hxL) _).mp hc
  have hinf : A.subgroupOf (fsuUL T L I) ⊓ B.subgroupOf (fsuUL T L I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
    rw [hAB, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hsup' : A.subgroupOf (fsuUL T L I) ⊔ B.subgroupOf (fsuUL T L I) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ (↑(A ⊔ B) : Set G) := by rw [hsup]; exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A B
      (le_normalizer_of_le_fsuVM hyp (hB.trans hV1V) (hA.trans hV1V))] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    have e : x = ⟨a, hA ha⟩ * ⟨b, hB hb⟩ := Subtype.ext hab.symm
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb)
  have hbot : ∀ {C : Subgroup G}, C ≤ fsuUL T L I → C.subgroupOf (fsuUL T L I) = ⊥ → C = ⊥ := by
    intro C hC h
    rw [eq_bot_iff]
    intro c hc
    have h1 : (⟨c, hC hc⟩ : ↥(fsuUL T L I)) ∈ C.subgroupOf (fsuUL T L I) :=
      Subgroup.mem_subgroupOf.mpr hc
    rw [h, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
  rcases isIndecompModule_fsuUL h37 h38 hyp h1011 D _ _ (hinv hAL) (hinv hBL) hinf hsup' with
    h | h
  · exact Or.inl (hbot hA h)
  · exact Or.inr (hbot hB h)

theorem mem_sup_centralizer_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {z : G}
    (hz : z ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))) :
    z ∈ fsuUL T L I ⊔ (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
      Subgroup.centralizer (L : Set G)) := by
  by_contra hzn
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 := (card_fsuUL h37 h38 hyp h1011 h484 D hnat hne).1
  have hX1 := L_le_centralizerSection_fsuUL h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV1X := hV1V.trans (fsuVM_le_omegaOneCenterOf hyp)
  have hXc : ∀ a ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)),
      ∀ b ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)), a * b = b * a :=
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb
  have hzV1 : z ∉ fsuUL T L I := fun h => hzn (Subgroup.mem_sup_left h)
  have hz2 : z ^ 2 = 1 := A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_of_comm hXc hV1X (Subgroup.zpowers_le.mpr hz)
  have hcomm : ⁅⁅fsuVM T L I, L⁆, L⁆ = ⁅fsuVM T L I, L⁆ := commutator_fsuUL_eq hyp
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = fsuUL T L I ⊔ Subgroup.zpowers z := ⟨_, rfl⟩
  have hYX : Y ≤ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :=
    hYdef ▸ sup_le hV1X (Subgroup.zpowers_le.mpr hz)
  have hV1Y : fsuUL T L I ≤ Y := hYdef ▸ le_sup_left
  have hYL : ∀ y ∈ Y, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ fsuUL T L I := by
    intro y hy l hl
    have h1 := (hX1 hl).2.2.2 y (hYX hy)
    have e : l * y * l⁻¹ * y⁻¹ = (y * l * y⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact (fsuUL T L I).inv_mem h1
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_conj_mem fun l hl y hy => by
    have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem (hV1Y (hYL y hy l hl)) hy
  have hCY : ∀ y ∈ Y, y ∈ Subgroup.centralizer (L : Set G) → y ∈ fsuUL T L I := by
    intro y hy hyc
    have hy' := hy
    rw [hYdef] at hy'
    obtain ⟨v, hv, h | h⟩ := mem_sup_zpowers hzN hz2 hy'
    · exact h ▸ hv
    · exfalso
      apply hzn
      have e : z = v⁻¹ * y := by rw [h]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((fsuUL T L I).inv_mem hv))
        (Subgroup.mem_sup_right ⟨hYX hy, hyc⟩)
  have hcard : Nat.card Y = 32 := by
    rw [hYdef, card_sup_zpowers hzV1 hz2 hzN, h16]
  have hsub : IsSubnormal L (fsuL0 T L ⊔ T) :=
    IsSubnormal.step (SecA.le_fsuL0 T L) (SecA.normal_fsuL0 hyp.fsu.maximal.1)
      (IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le (SecA.fsuL0_le_fsuM T L) (SecA.le_fsuM T L))) (IsSubnormal.refl _))
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (Y : Set G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ((A4.pCoreOf_le_of_subnormal 2 hsub).trans ?_).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hYX))
    rw [← (h1027 G T L I hyp).2]
    exact Q_le_centralizer_omegaOne T _
  have hCL : ∀ l ∈ L, l ∈ Subgroup.centralizer (Y : Set G) ↔
      l ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    intro l hl
    refine ⟨fun h => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1Y) h, fun h => ?_⟩
    have hLN : L ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer (fsuUL T L I : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf' Subgroup.le_normalizer
        (SecA.le_normalizer_centralizer (le_normalizer_fsuUL T L I))
    rcases le_pCoreOf_or_eq_of_normal hyp.fsu.faithful.1.2.1.2.1
        (SecB.isSimpleGroup_of_LBarL32 h3.1) inf_le_left hLN with h' | h'
    · exact hO2 (h' ⟨hl, h⟩)
    · exfalso
      have h1 : ⁅fsuUL T L I, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact Subgroup.le_centralizer_iff.mpr (inf_eq_left.mp h')
      have h2 : fsuUL T L I = ⊥ := by
        rw [← h1]
        exact hcomm.symm
      rw [h2, Subgroup.card_bot] at h16
      norm_num at h16
  obtain ⟨ψ, hψ⟩ := exists_autOnEquiv hLY (le_normalizer_fsuUL T L I) hCL
  have hYc : IsMulCommutative ↥Y := ⟨⟨fun a b => Subtype.ext (hXc a (hYX a.2) b (hYX b.2))⟩⟩
  have hsq : ∀ y : ↥Y, y ^ 2 = 1 :=
    fun y => Subtype.ext (A4.sq_eq_one_of_mem_omegaOneCenterOf (hYX y.2))
  have hiso : Nonempty (↥(autOn L Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨ψ.trans (MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm⟩
  have hind : ∀ A B : Subgroup ↥Y, (∀ g ∈ autOn L Y, ∀ a ∈ A, g a ∈ A) →
      (∀ g ∈ autOn L Y, ∀ b ∈ B, g b ∈ B) → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥ := by
    intro A B hA hB hAB hABt
    have hmapL : ∀ {C : Subgroup ↥Y}, (∀ g ∈ autOn L Y, ∀ c ∈ C, g c ∈ C) →
        L ≤ Subgroup.normalizer (C.map Y.subtype : Set G) := by
      intro C hC
      refine le_normalizer_of_conj_mem fun l hl c hc => ?_
      obtain ⟨c, hc, rfl⟩ := hc
      exact ⟨_, hC _ (SecB.mem_autOn_iff.mpr ⟨⟨l, hLY hl⟩, hl, rfl⟩) c hc, rfl⟩
    have hA'L := hmapL hA
    have hB'L := hmapL hB
    have hA'Y : A.map Y.subtype ≤ Y := Subgroup.map_subtype_le A
    have hB'Y : B.map Y.subtype ≤ Y := Subgroup.map_subtype_le B
    have hinf' : A.map Y.subtype ⊓ B.map Y.subtype = ⊥ := by
      rw [← Subgroup.map_inf_eq _ _ _ Y.subtype_injective, hAB, Subgroup.map_bot]
    have hsup' : A.map Y.subtype ⊔ B.map Y.subtype = Y := by
      rw [← Subgroup.map_sup, hABt, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hcV1 : ∀ {C : Subgroup G}, C ≤ Y → ⁅C, L⁆ ≤ fsuUL T L I := by
      intro C hC
      rw [Subgroup.commutator_le]
      intro c hc l hl
      rw [commutatorElement_def]
      exact (hX1 hl).2.2.2 c (hYX (hC hc))
    have hYL' : ⁅Y, L⁆ ≤ ⁅A.map Y.subtype, L⁆ ⊔ ⁅B.map Y.subtype, L⁆ := by
      rw [Subgroup.commutator_le]
      intro y hy l hl
      have hy' : y ∈ (↑(A.map Y.subtype ⊔ B.map Y.subtype) : Set G) := by rw [hsup']; exact hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (le_normalizer_of_comm hXc (hA'Y.trans hYX) (hB'Y.trans hYX))] at hy'
      obtain ⟨a, ha, b, hb, rfl⟩ := hy'
      have hbl : ⁅b, l⁆ ∈ fsuUL T L I := hcV1 hB'Y (Subgroup.commutator_mem_commutator hb hl)
      have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
        simp only [commutatorElement_def]
        group
      have e2 : a * ⁅b, l⁆ * a⁻¹ = ⁅b, l⁆ := by
        rw [hXc a (hYX (hA'Y ha)) _ (hV1X hbl), mul_inv_cancel_right]
      rw [e, e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hb hl))
        (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hl))
    have hV1sup : ⁅A.map Y.subtype, L⁆ ⊔ ⁅B.map Y.subtype, L⁆ = fsuUL T L I := by
      apply le_antisymm (sup_le (hcV1 hA'Y) (hcV1 hB'Y))
      calc fsuUL T L I = ⁅fsuUL T L I, L⁆ := hcomm.symm
        _ ≤ ⁅Y, L⁆ := Subgroup.commutator_mono hV1Y le_rfl
        _ ≤ _ := hYL'
    have hA1A : ⁅A.map Y.subtype, L⁆ ≤ A.map Y.subtype := commutator_le_left_of_le_normalizer hA'L
    have hB1B : ⁅B.map Y.subtype, L⁆ ≤ B.map Y.subtype := commutator_le_left_of_le_normalizer hB'L
    have hA1B1 : ⁅A.map Y.subtype, L⁆ ⊓ ⁅B.map Y.subtype, L⁆ = ⊥ :=
      le_bot_iff.mp (hinf' ▸ inf_le_inf hA1A hB1B)
    have hcent : ∀ {C : Subgroup G}, C ≤ Y → ⁅C, L⁆ = ⊥ → C ≤ fsuUL T L I := by
      intro C hC h c hc
      refine hCY c (hC hc) (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
      have h1 := Subgroup.commutator_mem_commutator hc hl
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rcases indecomp_fsuUL h37 h38 hyp h1011 D (hcV1 hA'Y) (hcV1 hB'Y)
        (SecA.le_normalizer_commutator hA'L Subgroup.le_normalizer)
        (SecA.le_normalizer_commutator hB'L Subgroup.le_normalizer) hA1B1 hV1sup with h | h
    · left
      have hle : A.map Y.subtype ≤ B.map Y.subtype := by
        refine (hcent hA'Y h).trans ?_
        rw [← hV1sup, h, bot_sup_eq]
        exact hB1B
      have h1 : A.map Y.subtype = ⊥ := le_bot_iff.mp (hinf' ▸ le_inf le_rfl hle)
      exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h1
    · right
      have hle : B.map Y.subtype ≤ A.map Y.subtype := by
        refine (hcent hB'Y h).trans ?_
        rw [← hV1sup, h, sup_bot_eq]
        exact hA1A
      have h1 : B.map Y.subtype = ⊥ := le_bot_iff.mp (hinf' ▸ le_inf hle le_rfl)
      exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h1
  have hU : ∀ g : ↥(autOn L Y), ∀ u ∈ (fsuUL T L I).subgroupOf Y,
      (g : MulAut ↥Y) u ∈ (fsuUL T L I).subgroupOf Y := by
    rintro ⟨g, hg⟩ u hu
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    change (x : G) * u * (x : G)⁻¹ ∈ fsuUL T L I
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_fsuUL T L I hxL) _).mp hu
  have hfixZ : ∀ x ∈ L, ∀ u : G, u ∈ Subgroup.centralizer (fsuL0 T L : Set G) →
      x * u * x⁻¹ = u := by
    intro x hx u hu
    rw [Subgroup.mem_centralizer_iff.mp hu x (SecA.le_fsuL0 T L hx), mul_inv_cancel_right]
  have hZ : ∀ g : ↥(autOn L Y), ∀ u ∈ (fsuUL T L I ⊓
      Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf Y,
      (g : MulAut ↥Y) u ∈
        (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf Y := by
    rintro ⟨g, hg⟩ u hu
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    change (x : G) * u * (x : G)⁻¹ ∈ _
    rw [hfixZ x hxL u hu.2]
    exact hu
  let e : ↥(⊤ : Subgroup ↥(fsuUL T L I)) ≃* ↥((fsuUL T L I).subgroupOf Y) :=
    Subgroup.topEquiv.trans (Subgroup.subgroupOfEquivOfLe hV1Y).symm
  have he : ∀ u : ↥(⊤ : Subgroup ↥(fsuUL T L I)),
      (((e u : ↥((fsuUL T L I).subgroupOf Y)) : ↥Y) : G) = ((u : ↥(fsuUL T L I)) : G) :=
    fun u => rfl
  have hnatY : BinaryNaturalSL (autOn L Y) ((fsuUL T L I).subgroupOf Y)
      ((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf Y) 3 1 := by
    obtain ⟨K, hF, hfin, hcardK, π, hπ⟩ := hnat
    refine ⟨K, hF, hfin, hcardK, ψ.symm.toMonoidHom.comp π,
      realizesVia_transport hπ ψ.symm e (fun u => ?_) (fun u hu => ?_) hU hZ
        (fun g u hu => ?_)⟩
    · rw [Subgroup.mem_subgroupOf, he]
      exact ⟨fun h => h.2, fun h => ⟨(u : ↥(fsuUL T L I)).2, h⟩⟩
    · rw [Subgroup.mem_subgroupOf] at hu ⊢
      exact hu.1
    · obtain ⟨x, hxL, hgx⟩ := SecB.mem_autOn_iff.mp g.2
      have hg : g = ⟨conjAct (fsuUL T L I) ⟨x, le_normalizer_fsuUL T L I hxL⟩,
          SecB.mem_autOn_iff.mpr ⟨⟨x, le_normalizer_fsuUL T L I hxL⟩, hxL, rfl⟩⟩ :=
        Subtype.ext hgx.symm
      have hψg : ψ.symm g = ⟨conjAct Y ⟨x, hLY hxL⟩,
          SecB.mem_autOn_iff.mpr ⟨⟨x, hLY hxL⟩, hxL, rfl⟩⟩ := by
        rw [MulEquiv.symm_apply_eq, hg]
        exact (hψ x hxL).symm
      rw [hψg]
      apply Subtype.ext
      change (x : G) * (((e u : ↥((fsuUL T L I).subgroupOf Y)) : ↥Y) : G) * (x : G)⁻¹ = _
      rw [he, he]
      subst hg
      rfl
  have hsec : ∃ W₁ W₂ : Subgroup ↥Y, W₁ ≤ W₂ ∧ W₁ ≤ fixV (autOn L Y) ∧
      commV (autOn L Y) ≤ W₂ ∧ BinaryNaturalSL (autOn L Y) W₂ W₁ 3 1 := by
    refine ⟨(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf Y,
      (fsuUL T L I).subgroupOf Y, fun u hu => ?_, fun u hu => ?_, ?_, hnatY⟩
    · rw [Subgroup.mem_subgroupOf] at hu ⊢
      exact hu.1
    · rw [mem_fixV]
      intro g hg
      obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
      rw [Subgroup.mem_subgroupOf] at hu
      apply Subtype.ext
      exact hfixZ x hxL u hu.2
    · rw [commV, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, rfl⟩
      obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hYL y y.2 x hxL
  have h := h484 ↥Y hsq (autOn L Y) hiso hind hsec
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC
