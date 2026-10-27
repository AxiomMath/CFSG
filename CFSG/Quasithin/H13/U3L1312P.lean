module

public import CFSG.Quasithin.H13.U3L1312B
public import CFSG.Quasithin.H13.U3L1312M
public import CFSG.Quasithin.H13.U3G2Img
public import CFSG.Quasithin.H13.U3P33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G]

theorem conj_s0L_eq
    {j : GL (Fin 6) (ZMod 2)} {jc jci : List ℕ}
    (hj : (j : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat jc)
    (hji : ((j⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat jci)
    {k k' : ℕ} (hk : k < 64) (hk' : k' < 64) (h : mul6 (mul6 jc (s0m k)) jci = s0m k') :
    glLin j * s0L k * (glLin j)⁻¹ = s0L k' := by
  ext w : 1
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← map_inv, glLin_vecOf hji, s0L_vecOf hk,
    glLin_vecOf hj, s0L_vecOf hk', ← h]
  simp only [← colMat_mulVec_vecOf, colMat_mul6, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem isA1_map_conj
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) {m : ℕ} (hmE : ofMask m = IE E)
    (hm8 : (ofMask m).card = 8) {j : GL (Fin 6) (ZMod 2)} {jc jci : List ℕ}
    (hj : (j : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat jc)
    (hji : ((j⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat jci)
    (hfw : ∀ k < 64, m.testBit k = true → ∃ k' < 64,
      a1mask.testBit k' = true ∧ mul6 (mul6 jc (s0m k)) jci = s0m k') :
    IsA1 (E.map (MulAut.conj (glLin j)).toMonoidHom) := by
  classical
  have hmem : ∀ k < 64, s0L k ∈ E ↔ m.testBit k = true := fun k hk => by
    have h1 : k ∈ IE E ↔ k ∈ ofMask m := by rw [hmE]
    rw [mem_IE, ofMask, Finset.mem_filter, Finset.mem_range] at h1
    exact ⟨fun h => (h1.1 ⟨hk, h⟩).2, fun h => (h1.2 ⟨hk, h⟩).2⟩
  set E' := E.map (MulAut.conj (glLin j)).toMonoidHom with hE'
  have hE'S : E' ≤ S0L := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_S0L.1 (hE he)
    obtain ⟨k', hk', -, hkk⟩ := hfw k hk ((hmem k hk).1 he)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_s0L_eq hj hji hk hk' hkk]
    exact mem_S0L.2 ⟨k', hk', rfl⟩
  have hsub : IE E' ⊆ ofMask a1mask := by
    intro k' hk'
    obtain ⟨hk'64, ⟨e, he, hee⟩⟩ := mem_IE.1 hk'
    obtain ⟨k, hk, rfl⟩ := mem_S0L.1 (hE he)
    obtain ⟨k'', hk'', hbit, hkk⟩ := hfw k hk ((hmem k hk).1 he)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_s0L_eq hj hji hk hk'' hkk] at hee
    have := s0L_inj hk'' hk'64 hee
    subst this
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk'64, hbit⟩
  have hcard : (IE E').card = 8 := by
    rw [← card_eq_IE hE'S, hE', Subgroup.card_map_of_injective (MulAut.conj (glLin j)).injective,
      card_eq_IE hE, ← hmE, hm8]
  have ha8 : (ofMask a1mask).card = 8 := good_codes.2.2.1
  exact ⟨hE'S, (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, ha8])).symm⟩

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem imgL_cjSub
    (S : HullSetting G T L V z) {l : G} (hl : l ∈ normalizer (V : Set G)) (X : Subgroup G) :
    S.imgL (cjSub l X) =
      (S.imgL X).map (MulAut.conj (glLin (S.rho ⟨l, hl⟩))).toMonoidHom := by
  ext g
  rw [S.mem_imgL, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxN, hxX, rfl⟩
    have hx' : l⁻¹ * x * l ∈ X := mem_cjSub.1 hxX
    have hx'N : l⁻¹ * x * l ∈ normalizer (V : Set G) := mul_mem (mul_mem (inv_mem hl) hxN) hl
    refine ⟨glLin (S.rho ⟨l⁻¹ * x * l, hx'N⟩), S.glLin_rho_mem_imgL hx' hx'N, ?_⟩
    have e : (⟨x, hxN⟩ : normalizer (V : Set G)) =
        ⟨l, hl⟩ * ⟨l⁻¹ * x * l, hx'N⟩ * (⟨l, hl⟩ : normalizer (V : Set G))⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  · rintro ⟨e, he, rfl⟩
    obtain ⟨x, hxN, hxX, rfl⟩ := S.mem_imgL.1 he
    have hx'N : l * x * l⁻¹ ∈ normalizer (V : Set G) := mul_mem (mul_mem hl hxN) (inv_mem hl)
    refine ⟨l * x * l⁻¹, hx'N, mem_cjSub.2 (by simpa [mul_assoc] using hxX), ?_⟩
    have e : (⟨l * x * l⁻¹, hx'N⟩ : normalizer (V : Set G)) =
        ⟨l, hl⟩ * ⟨x, hxN⟩ * (⟨l, hl⟩ : normalizer (V : Set G))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]

theorem pairEq_of_isA1
    (S : HullSetting G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hXab : IsElemAbelian 2 X) (hX64 : Nat.card X = 64) (hle : ⁅V, X⁆ ≤ V ⊓ X)
    (hA : IsA1 (S.imgL X)) : PairEq V X S.V₃ := by
  have hVab := isElemAbelian_of_isElementaryAbelian' V
  have hC : V ⊓ centralizer (X : Set G) = S.V₃ := by
    rw [S.inf_centralizer_eq hXN, hA.linFix_eq, S.V₃_eq_pullSub]
  have h3 : S.V₃ ≤ ⁅V, X⁆ := by
    intro c hc
    rw [S.V₃_eq_pullSub] at hc
    obtain ⟨hcV, hcP⟩ := mem_pullSub.1 hc
    obtain ⟨e, he, w, hew⟩ := hA.exists_sub_eq hcP
    obtain ⟨n, hnN, hnX, rfl⟩ := S.mem_imgL.1 he
    have hvV : elOf S.Φ w ∈ V := elOf_mem w
    have h1 := S.phi_comm hnN hvV
    rw [phi_elOf w, hew] at h1
    have h2 : n * elOf S.Φ w * n⁻¹ * (elOf S.Φ w)⁻¹ = c := phi_injective' _ hcV h1
    rw [← h2, commutator_comm]
    have := commutator_mem_commutator hnX hvV
    rwa [commutatorElement_def] at this
  have hVX : V ⊓ X ≤ V ⊓ centralizer (X : Set G) :=
    inf_le_inf_left _ (B2F.le_centralizer_self hXab)
  have heq1 : ⁅V, X⁆ = S.V₃ := le_antisymm (hle.trans (hVX.trans hC.le)) h3
  have heq2 : V ⊓ X = S.V₃ := le_antisymm (hVX.trans hC.le) (h3.trans hle)
  refine ⟨heq2, heq1, hC, ?_⟩
  have hle4 : S.V₃ ≤ X ⊓ centralizer (V : Set G) := by
    rw [← heq2]
    exact le_inf inf_le_right (inf_le_left.trans (B2F.le_centralizer_self hVab))
  refine (Subgroup.eq_of_le_of_card_ge hle4 ?_).symm
  rw [S.card_V₃]
  have h1 := S.card_imgL hXN
  rw [hA.card] at h1
  have h2 := relIndex_mul_card (X ⊓ centralizer (V : Set G)) X
  rw [inf_eq_left.2 (inf_le_left : X ⊓ centralizer (V : Set G) ≤ X), hX64, ← h1] at h2
  omega

theorem exists_pos_of_isA1
    (S : HullSetting G T L V z) {X : Subgroup G} (hA : IsA1 (S.imgL X)) {x : G} (hx : x ∈ X)
    (hxN : x ∈ normalizer (V : Set G)) :
    ∃ k < 64, a1mask.testBit k = true ∧ glLin (S.rho ⟨x, hxN⟩) = s0L k := by
  obtain ⟨k, hk, hkx⟩ := (mem_iff_IE hA.1).1 (S.glLin_rho_mem_imgL hx hxN)
  rw [← hA.2] at hk
  obtain ⟨hk64, hbit⟩ := Finset.mem_filter.1 hk
  exact ⟨k, Finset.mem_range.1 hk64, hbit, hkx⟩

theorem v1Of_eq_of_isA1
    (S : HullSetting G T L V z) {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hP : PairEq V X S.V₃) (hA : IsA1 (S.imgL X)) : v1Of V X = S.V₁ := by
  obtain ⟨hq4, hq5, hq6, hq7, hq8, hq9⟩ := z_codes
  apply le_antisymm
  · rw [S.V₁_eq_pullSub]
    refine (closure_le _).2 ?_
    rintro c ⟨y, ⟨hyV, x', hx'X, hx'C, hx'y⟩, x, ⟨hxX, y', hy'V, hy'C, hy'x⟩, rfl⟩
    obtain ⟨c₀, hc₀, hyc⟩ := exists_vecOf (S.Φ (Additive.ofMul (⟨y, hyV⟩ : V)))
    obtain ⟨k', hk', hk'a, hk'e⟩ := S.exists_pos_of_isA1 hA hx'X (hXN hx'X)
    obtain ⟨k, hk, hka, hke⟩ := S.exists_pos_of_isA1 hA hxX (hXN hxX)
    have hk'0 : k' ≠ 0 := by
      rintro rfl
      apply hx'C
      rw [mem_centralizer_V_iff (hXN hx'X) (S.rho_spec _)]
      apply glLin.injective
      rw [hk'e, s0L_zero, map_one]
    have hfix' : vapp (s0m k') c₀ = c₀ := by
      have h1 := (S.comm_iff_fix (hXN hx'X) hyV).1 hx'y
      rw [hk'e, ← hyc, s0L_vecOf hk'] at h1
      exact vecOf_injective (vapp_s0m_lt hk' c₀) hc₀ h1
    have h5 := v5_codes k' hk' hk'a hk'0 c₀ hc₀ hfix'
    obtain ⟨c₁, hc₁, hyc₁⟩ := exists_vecOf (S.Φ (Additive.ofMul (⟨y', hy'V⟩ : V)))
    have hc₁3 : v3mask.testBit c₁ = false := by
      cases h : v3mask.testBit c₁
      · rfl
      · exfalso
        apply hy'C
        have : y' ∈ V ⊓ centralizer (X : Set G) := by
          rw [hP.2.2.1, S.V₃_eq_pullSub]
          exact mem_pullSub.2 ⟨hy'V, by rw [← hyc₁]; exact (hasMask_V3sub' c₁ hc₁).2 h⟩
        exact this.2
    have hfix : vapp (s0m k) c₁ = c₁ := by
      have h1 := (S.comm_iff_fix (hXN hxX) hy'V).1 hy'x.symm
      rw [hke, ← hyc₁, s0L_vecOf hk] at h1
      exact vecOf_injective (vapp_s0m_lt hk c₁) hc₁ h1
    have h6 := u5_codes k hk hka c₁ hc₁ hc₁3 hfix
    have h7 := v1_codes k hk h6 c₀ hc₀ h5
    refine (comm_mem_pullSub (hXN hxX) (S.rho_spec _) hyV V1sub).2 ?_
    rw [hke, ← hyc, s0L_vecOf hk, sub_eq_add_W6, ← vecOf_xor]
    exact (hasMask_V1sub _ (Nat.xor_lt_two_pow (n := 6) (vapp_s0m_lt hk c₀) hc₀)).2 h7
  ·
    rw [S.V₁_eq, zpowers_le]
    obtain ⟨x₀, hx₀N, hx₀X, hx₀e⟩ := S.mem_imgL.1 (s0L_mem_of_mask hA.2 (by norm_num) hq4)
    obtain ⟨x₁, hx₁N, hx₁X, hx₁e⟩ := S.mem_imgL.1 (s0L_mem_of_mask hA.2 (by norm_num) hq5)
    have hy₀ : elOf S.Φ (vecOf 3) ∈ gen5 V X := by
      refine ⟨elOf_mem _, x₁, hx₁X, fun hC => ?_, ?_⟩
      · have h1 := (mem_centralizer_V_iff hx₁N (S.rho_spec _)).1 hC
        have h2 : s0L 34 = s0L 0 := by rw [← hx₁e, h1, map_one, s0L_zero]
        exact absurd (s0L_inj (by norm_num) (by norm_num) h2) (by norm_num)
      · refine (S.comm_iff_fix hx₁N (elOf_mem _)).2 ?_
        rw [hx₁e, phi_elOf, s0L_vecOf (by norm_num), hq6]
    have hx₀g : x₀ ∈ gen5 X V := by
      refine ⟨hx₀X, elOf S.Φ (vecOf 7), elOf_mem _, fun hC => ?_, ?_⟩
      · have h1 : elOf S.Φ (vecOf 7) ∈ V ⊓ centralizer (X : Set G) := ⟨elOf_mem _, hC⟩
        rw [hP.2.2.1, S.V₃_eq_pullSub, elOf_mem_pullSub, hasMask_V3sub' 7 (by norm_num), hq8]
          at h1
        exact absurd h1 (by decide)
      · refine ((S.comm_iff_fix hx₀N (elOf_mem _)).2 ?_).symm
        rw [hx₀e, phi_elOf, s0L_vecOf (by norm_num), hq7]
    have hmem : elOf S.Φ (vecOf 3) * x₀ * (elOf S.Φ (vecOf 3))⁻¹ * x₀⁻¹ ∈ v1Of V X :=
      subset_closure ⟨_, hy₀, x₀, hx₀g, rfl⟩
    have hz : x₀ * elOf S.Φ (vecOf 3) * x₀⁻¹ * (elOf S.Φ (vecOf 3))⁻¹ = z := by
      have h1 := S.phi_comm hx₀N (elOf_mem (Φ := S.Φ) (vecOf 3))
      rw [phi_elOf, hx₀e, s0L_vecOf (by norm_num), sub_eq_add_W6, ← vecOf_xor, hq9,
        ← S.phi_z] at h1
      exact phi_injective' _ S.hzV h1
    have h2 : (elOf S.Φ (vecOf 3) * x₀ * (elOf S.Φ (vecOf 3))⁻¹ * x₀⁻¹)⁻¹ = z :=
      calc (elOf S.Φ (vecOf 3) * x₀ * (elOf S.Φ (vecOf 3))⁻¹ * x₀⁻¹)⁻¹
          = x₀ * elOf S.Φ (vecOf 3) * x₀⁻¹ * (elOf S.Φ (vecOf 3))⁻¹ := by group
        _ = z := hz
    have h3 := inv_mem hmem
    rwa [h2] at h3

end HullSetting

end CFSG.Quasithin.H13.U3
