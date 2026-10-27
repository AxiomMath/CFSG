module

public import CFSG.RankThree.PartTwo.Sec11.Item116Coords
public import CFSG.RankThree.PartTwo.Sec11.LStarL3Facts
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.KFacts.K72OutL3
public import CFSG.RankThree.PartTwo.Sec8.Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem isInnerAut_commutator_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {σ τ : MulAut X}
    (hσ : σ ∈ P) (hτ : τ ∈ P) : KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.isInnerAut_commutator_of_isoLThreeMinusPi hn hL σ τ
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact KFacts.isInnerAut_commutator_of_mulEquiv_psl2 e hP hσ hτ

@[expose] def Item116Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ →
            ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A,
              x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure {c, d}

section Transfer

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def innerPreimage (L : Subgroup G) : Subgroup G :=
  ((MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range.comap
    ((Sec4.thetaQuotMulAut L).comp (Sec4.compAction L))).map
      (Subgroup.normalizer (L : Set G)).subtype

theorem mem_innerPreimage_iff {L : Subgroup G} {z : G} :
    z ∈ innerPreimage L ↔ ∃ hz : z ∈ Subgroup.normalizer (L : Set G),
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨z, hz⟩) ∈
        (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
          MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
  constructor
  · rintro ⟨⟨z', hz'⟩, hmem, rfl⟩
    exact ⟨hz', hmem⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨⟨z, hz⟩, hmem, rfl⟩

theorem le_normalizer_of_eq_closure {A R : Subgroup G}
    (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}) :
    R ≤ Subgroup.normalizer (A : Set G) := by
  intro r hr
  apply mem_normalizer_of_forall_conj_mem
  intro u hu
  rw [hΩ] at hu ⊢
  have hle : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} ≤
      (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).comap (MulAut.conj r⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyR, hy3⟩
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · change r⁻¹ * y * r⁻¹⁻¹ ∈ R
      exact R.mul_mem (R.mul_mem (R.inv_mem hr) hyR) (R.inv_mem (R.inv_mem hr))
    · change (r⁻¹ * y * r⁻¹⁻¹) ^ 3 = 1
      rw [conj_pow, hy3]
      group
  have h1 : (MulAut.conj r⁻¹).toMonoidHom u ∈ Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} :=
    hle hu
  change r⁻¹ * u * r⁻¹⁻¹ ∈ Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} at h1
  rwa [inv_inv] at h1

theorem false_of_fusion_trivial (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hRG : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤)
    (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1})
    (hfus : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure {c, d}) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have hc1 := h.ne_one
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hR3 : IsPGroup 3 R := hRG.isPGroup
  have hRC : R ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_le_normalizer_zpowers hco hR3 h.isSylowOf.le
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_of_le_centralizer h45 hG hc3 hc1 hR3 hRC L h.mem_thetaComponentsAt
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have hAR : A ≤ R := by
    rw [hΩ, Subgroup.closure_le]
    rintro y ⟨hy, -⟩
    exact hy
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcdU : Subgroup.closure ({c, d} : Set G) ≤ innerPreimage L := by
    have hdLL : d ∈ L := by
      have : d ∈ A ⊓ L := by
        rw [hdL]
        exact Subgroup.mem_zpowers d
      exact this.2
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    · have hcCL : c ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr
        fun l hl => (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
      have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.centralizer_le_normalizer _ hcCL
      refine mem_innerPreimage_iff.mpr ⟨hcN, ⟨1, ?_⟩⟩
      have h1 : Sec4.compAction L ⟨c, hcN⟩ = 1 := by
        ext x
        rw [Sec4.compAction, Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply,
          ← (Subgroup.mem_centralizer_iff.mp hcCL x x.2), mul_inv_cancel_right]
      rw [h1, map_one, map_one]
    · refine mem_innerPreimage_iff.mpr ⟨Subgroup.le_normalizer hdLL, ?_⟩
      rw [thetaQuotMulAut_compAction_of_mem L hdLL]
      exact ⟨_, rfl⟩
  have hRcard : Nat.card R = 3 ^ (Nat.card G).factorization 3 := by
    rw [hRG.card_eq, Subgroup.card_top]
  set P : Sylow 3 G := Sylow.ofCard R hRcard with hPdef
  have hP : (P : Subgroup G) = R := Sylow.coe_ofCard R hRcard
  refine Sec8.rank3II_transfer_false hG P (U := innerPreimage L) (r := a) ?_ ?_ ?_ ?_ ?_
  ·
    intro x hx u hu
    rw [hP] at hx
    obtain ⟨huN, hinn⟩ := mem_innerPreimage_iff.mp hu
    have hxN := hRL hx
    have hxuN : x * u * x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN huN) (Subgroup.inv_mem _ hxN)
    refine mem_innerPreimage_iff.mpr ⟨hxuN, ?_⟩
    have h1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x * u * x⁻¹, hxuN⟩) =
        ρ ⟨x, hxN⟩ * ρ ⟨u, huN⟩ * (ρ ⟨x, hxN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    obtain ⟨ℓ, hℓ⟩ := hinn
    refine ⟨ρ ⟨x, hxN⟩ ℓ, ?_⟩
    rw [← KFacts.mul_mulAutConj_mul_inv, hℓ]
    rfl
  ·
    intro x hx y hy
    rw [hP] at hx hy
    have hxN := hRL hx
    have hyN := hRL hy
    have hxyN : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hyN)
        (Subgroup.inv_mem _ hxN)) (Subgroup.inv_mem _ hyN)
    refine mem_innerPreimage_iff.mpr ⟨hxyN, ?_⟩
    set Q : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
      (R.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ with hQ
    have hQ3 : IsPGroup 3 Q := (hR3.comap_subtype (K := Subgroup.normalizer (L : Set G))).map ρ
    have hxQ : ρ ⟨x, hxN⟩ ∈ Q := ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hyQ : ρ ⟨y, hyN⟩ ∈ Q := ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h1 := isInnerAut_commutator_of_isList1016 h.isList1016 hQ3 hxQ hyQ
    have h2 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x * y * x⁻¹ * y⁻¹, hxyN⟩) =
        ρ ⟨x, hxN⟩ * ρ ⟨y, hyN⟩ * (ρ ⟨x, hxN⟩)⁻¹ * (ρ ⟨y, hyN⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact h1
  ·
    rw [hP]
    exact hAR h.a_mem
  ·
    intro ha
    obtain ⟨haN, hinn⟩ := mem_innerPreimage_iff.mp ha
    obtain ⟨haN', hout⟩ := h.toHyp81.inducesOuterTheta
    exact hout hinn
  ·
    intro k g hg
    rw [hP] at hg
    have hakA : a ^ k ∈ A := A.pow_mem h.a_mem k
    have hgA : g⁻¹ * a ^ k * g ∈ A := by
      rw [hΩ]
      refine Subgroup.subset_closure ⟨hg, ?_⟩
      rw [show g⁻¹ * a ^ k * g = g⁻¹ * a ^ k * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hexp _ hakA]
      group
    obtain ⟨w, hwW, hweq⟩ := exists_mem_normalizer_conj_eq hRG hΩ hcomm hexp hakA hgA
    rw [hweq]
    exact hcdU (hfus w hwW _ hakA)

end Transfer

theorem item116_of (h97 : Sec9.Item97) (h98 : Sec9.Item98) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hF : Item116Fusion) : Item116 := by
  intro G _ _ A c L a R Y h B hBA hcard hWirr
  obtain ⟨hWB, hirr⟩ := hWirr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := h.toTheoremFourHyp
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have h27 := h.card_eq
  have hB9 : Nat.card B = 9 := by omega
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  obtain ⟨d, hdL, hdo, hA⟩ := Sec10.exists_inf_eq_zpowers h97 h.toHyp91
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    exact absurd hdo (by norm_num)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L h.mem_thetaComponentsAt
  have hLA : ∀ l ∈ L, l ∈ Subgroup.normalizer (A : Set G) →
      ∀ u ∈ A, l * u * l⁻¹ * u⁻¹ ∈ Subgroup.zpowers d := by
    intro l hlL hlW u hu
    rw [← hdL]
    refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlW u).mp hu) (A.inv_mem hu), ?_⟩
    rw [show l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) by group]
    exact L.mul_mem hlL ((Subgroup.mem_normalizer_iff.mp (hAL hu) _).mp (L.inv_mem hlL))
  obtain ⟨l₀, ⟨hl₀L, hl₀W⟩, ⟨k, hk⟩, x₀, hx₀A, hx₀⟩ :=
    lStarTransvection_of_item97 h97 G A c L a R Y h
  obtain ⟨l₁, ⟨hl₁L, hl₁W⟩, hl₁d⟩ := lStarInverting_of_item97 h97 G A c L a R Y h d hdL
  have hl₀c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₀L hl₀W
  have hl₁c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₁L hl₁W
  have hl₀d : l₀ * d * l₀⁻¹ = d := by
    have h1 : l₀ * d * l₀⁻¹ ∈ Subgroup.zpowers d := by
      rw [← hdL]
      exact ⟨(Subgroup.mem_normalizer_iff.mp hl₀W d).mp hdAL.1,
        L.mul_mem (L.mul_mem hl₀L hdAL.2) (L.inv_mem hl₀L)⟩
    rw [Sec12.commute_of_conj_mem_zpowers hdo h1 hk, mul_inv_cancel_right]
  have hH : ∀ y ∈ Subgroup.normalizer (A : Set G),
      y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        y * d * y⁻¹ ∈ Subgroup.zpowers d := by
    intro y hyW hyH
    have hyL := Sec10.hwNormalizesL_of h97 G A c L a R h.toHyp91 ⟨hyH, hyW⟩
    rw [← hdL]
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyW d).mp hdAL.1,
      (Subgroup.mem_normalizer_iff.mp hyL d).mp hdAL.2⟩
  have hdB : d ∈ B := mem_of_hyperplane hexp h27 hBA hB9 hdAL.1 (hWB hl₀W) hl₀d
    (hLA l₀ hl₀L hl₀W) ⟨x₀, hx₀A, hx₀⟩
  by_cases hcB : c ∈ B
  ·
    have hdc : d ∉ Subgroup.zpowers c := by
      intro hdc
      have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
        rw [hA, Subgroup.closure_le]
        have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy | hy <;> rw [hy]
        · exact hc
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.zpowers_le.mpr hc hdc
      have h1 := Subgroup.card_le_of_le hle
      have h2 := Sec10.card_closure_pair_le (hcomm c hcA a h.a_mem) (hexp c hcA) (hexp a h.a_mem)
      rw [h27] at h1
      omega
    have hcdB : Subgroup.closure ({c, d} : Set G) = B := by
      have hle : Subgroup.closure ({c, d} : Set G) ≤ B := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy <;> rw [hy]
        · exact hcB
        · exact hdB
      have h1 : Subgroup.zpowers c ≤ Subgroup.closure ({c, d} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      have h9 := Sec9.three_mul_card_le_of_le_of_ne hA3 (hle.trans hBA) h1 (fun h => hdc (by
        rw [h]
        exact Subgroup.subset_closure (by simp)))
      rw [Nat.card_zpowers, hco] at h9
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hB9]; omega)
    have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
      ⟨⟨⟨fun x y => Subtype.ext (hcomm _ (hBA x.2) _ (hBA y.2))⟩⟩, fun x hx => hexp x (hBA hx)⟩
    obtain ⟨S, hSW, hSc⟩ := exists_isSylowOf_le_normalizer hBe hB9 hWB hirr hcB hc1
    obtain ⟨hΩ, -⟩ := item113_of h97 (item112_of h97 h98 h45 h48) h45 h48 G A c L a R Y h
    have hRW := le_normalizer_of_eq_closure hΩ
    have hRHW : CFSG.ABGLocalTools.IsSylowOf 3 R
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G)) := by
      have := h.isSylowOf_inf
      rwa [inf_eq_left.mpr hRW] at this
    have hSHW := hSW.of_le (le_inf hSc hSW.le) inf_le_right
    have hRWs : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (A : Set G)) :=
      CFSG.ABGLocalTools.isSylowOf_of_card hRW (by rw [hRHW.card_eq, ← hSHW.card_eq, hSW.card_eq])
    have hRG := isSylowOf_top_of_isSylowOf_normalizer hRWs hΩ
    have hWB' : Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
      rw [hcdB]
      exact hWB
    have hirr' : Sec21.IsIrreducibleOn
        (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) := by
      rw [hcdB]
      exact hirr
    exact false_of_fusion_trivial h45 h hdL hRG hΩ (hF G A c L a R Y h d hdL hWB' hirr' hRG)
  ·
    have hw₀ : ∃ w₀ ∈ Subgroup.normalizer (A : Set G), w₀ * d * w₀⁻¹ ∉ Subgroup.zpowers d := by
      by_contra hcon
      push Not at hcon
      rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hdB)
          (fun w hw _ => Sec10.mem_normalizer_zpowers_of_conj_mem (hcon w hw)) with h1 | h1
      · exact hd1 (by rw [← Subgroup.mem_bot, ← h1]; exact Subgroup.mem_zpowers d)
      · have h3 : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hdo]
        rw [h1, hB9] at h3
        norm_num at h3
    obtain ⟨w₀, hw₀W, hw₀d⟩ := hw₀
    exact false_of_not_mem_hyperplane hexp hcomm h27 hBA hB9 hcA hcB hdB hd1 hl₀W hl₁W hw₀W
      (hWB hw₀W) hl₀c hl₀d (hLA l₀ hl₀L hl₀W) ⟨x₀, hx₀A, hx₀⟩ hl₁c hl₁d (hLA l₁ hl₁L hl₁W) hw₀d hH

end CFSG.RankThree.PartTwo.Sec11
