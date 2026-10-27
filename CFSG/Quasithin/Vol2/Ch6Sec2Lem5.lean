module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp611Nat

theorem mem_centralizer_V_of_mem_S_ch62 {n : ℕ} (h : Hyp611Nat G T M L V n) {s u : G}
    (hs : s ∈ ch6S T L V) (huV : u ∈ V) (huZ : u ∉ ch6ZS T L V) (hsu : s * u = u * s) :
    s ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨A, hA, hsA⟩ := h.exists_stab_of_mem_S hv hle hs
  set w := Multiplicative.toAdd (h.data.E ⟨u, huV⟩) with hw
  have hdet : det2 v w ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := exists_eq_smul_of_det2_eq_zero hv h0
    exact huZ ((h.mem_ZS_iff_line hv hle ⟨u, huV⟩).mpr ⟨c, hc⟩)
  have hAw : (A : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w = w := by
    rw [← hsA, hw, h.data.conj_apply]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show s * u * s⁻¹ = u
    rw [hsu, mul_inv_cancel_right]
  have hA1 : A = 1 := eq_one_of_basis hdet (mem_sl2Stab.mp hA) hAw
  apply h.data.mem_centralizer_of_conj_eq ⟨s, h.toHyp611.T_le_normalizer hs.1⟩
  intro w'
  rw [hsA, hA1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

end Hyp611Nat

omit [Finite G] in
theorem isKleinFour_of_card_four_ch62 {X : Subgroup G} (h4 : Nat.card X = 4)
    (hsq : ∀ x ∈ X, x ^ 2 = 1) : IsKleinFour ↥X := by
  refine ⟨h4, ?_⟩
  have hsq' : ∀ x : ↥X, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hsq x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq') with
    h1 | h1
  · have : Subsingleton ↥X := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_of_subsingleton (1 : ↥X)
    omega
  · exact h1

theorem relIndex_centralizer_le_two_ch62 {P X : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (h4 : Nat.card X = 4)
    (hsq : ∀ x ∈ X, x ^ 2 = 1) :
    (P ⊓ Subgroup.centralizer (X : Set G)).relIndex P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := isKleinFour_of_card_four_ch62 h4 hsq
  have h6 : Nat.card (MulAut ↥X) = 6 := CFSG.GorensteinWalter.kleinFourAut_card ↥X
  have hcardA := card_autOn_eq_relIndex (V := X) hPX
  have hdvd6 : (P ⊓ Subgroup.centralizer (X : Set G)).relIndex P ∣ 6 := by
    rw [← hcardA, ← h6]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨c, hc⟩ := hP.exists_card_eq
  have hdvd2 : (P ⊓ Subgroup.centralizer (X : Set G)).relIndex P ∣ 2 ^ c :=
    hc ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  rw [hd] at hdvd6 ⊢
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · interval_cases d <;> norm_num
  · have h4' : 2 ^ 2 ∣ 2 ^ d := pow_dvd_pow 2 hd2
    have := h4'.trans hdvd6
    norm_num at this

theorem card_le_of_isSylowIn_ch62 {P S H : Subgroup G} (hS : IsSylowIn 2 S H) (hPH : P ≤ H)
    (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card S := by
  obtain ⟨x, -, hle⟩ := F7.isSylowTwoOf_exists_conj_le hS hPH hP
  calc Nat.card P ≤ Nat.card (conjSub x S) := Subgroup.card_le_of_le hle
    _ = Nat.card S := Subgroup.card_map_of_injective (MulAut.conj x).injective

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_ZS_four : Nat.card (ch6ZS T L V) = 4 := by
  rw [h.toHyp611Nat.card_ZS]; norm_num

theorem relIndex_S_le_two : (ch6S T L V).relIndex T ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := fun x hx =>
    h.toHyp611Nat.T_le_normalizer_ZS hx
  have := relIndex_centralizer_le_two_ch62 h.sylow.1 hTN h.card_ZS_four
    (fun x hx => h.toHyp611.isElemAbelian.2 x hx.1)
  exact this

theorem card_centralizer_mul_four_le (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) {U : Subgroup G}
    (hUV : U ≤ V) (hU4 : Nat.card U = 4) (hne : U ≠ ch6ZS T L V) :
    Nat.card ↥(T ⊓ Subgroup.centralizer (U : Set G)) * 4 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, huU, huZ⟩ : ∃ u ∈ U, u ∉ ch6ZS T L V := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [hU4, h.card_ZS_four]))
  set X := T ⊓ Subgroup.centralizer (U : Set G) with hX
  have hSX : ch6S T L V ⊓ X ≤ ch6Q T V := by
    rintro s ⟨hsS, hsT, hsU⟩
    refine ⟨hsT, h.toHyp611Nat.mem_centralizer_V_of_mem_S_ch62 hsS (hUV huU) huZ ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hsU u huU).symm
  have h1 := Subgroup.relIndex_mul_card (ch6S T L V) X
  have h2 : (ch6S T L V).relIndex X ≤ (ch6S T L V).relIndex T :=
    Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card ↥(ch6S T L V ⊓ X) ≤ Nat.card (ch6Q T V) := Subgroup.card_le_of_le hSX
  have h8 := h.relIndex_Q_T h331 h615
  have hQT : 8 * Nat.card ↥(ch6Q T V) = Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card (ch6Q T V) T
    rw [h8, inf_of_le_left (inf_le_left : ch6Q T V ≤ T)] at this
    exact this
  have hS2 := h.relIndex_S_le_two
  have : Nat.card ↥X ≤ 2 * Nat.card (ch6Q T V) := by
    rw [← h1]
    exact Nat.mul_le_mul (h2.trans hS2) h3
  omega

theorem lemma_6_2_5_four (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {g : G}
    (hg : ch6ZS T L V ≤ conjSubgroup V g) : conjSubgroup V g = V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := ch6ZS T L V with hZ
  set U₁ := conjSubgroup Z g⁻¹ with hU₁
  have hU₁V : U₁ ≤ V := by
    have := conjSubgroup_mono_left g⁻¹ hg
    rwa [conjSubgroup_conj_inv] at this
  have hU₁4 : Nat.card U₁ = 4 := by rw [card_conjSubgroup, h.card_ZS_four]
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    have : Nat.card U₁ = 1 := by rw [h0, Subgroup.card_bot]
    omega
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 2 (bot_le : ⊥ ≤ M ⊓ Subgroup.normalizer (U₁ : Set G))
    IsPGroup.of_bot
  obtain ⟨m, hm, hPT⟩ := h.toHyp611.exists_conj_sylow
    (hP.le.trans (h.toHyp611Nat.normalizer_le hU₁1 hU₁V)) hP.isPGroup
  set U₂ := conjSubgroup U₁ m with hU₂
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm.2
  have hmM : m ∈ M := hm.1
  have hU₂V : U₂ ≤ V := by
    have := conjSubgroup_mono_left m hU₁V
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hmV] at this
  have hU₂4 : Nat.card U₂ = 4 := by rw [card_conjSubgroup, hU₁4]
  have hU₂Z : U₂ = conjSubgroup Z (g⁻¹ * m) := by rw [hU₂, hU₁, conjSubgroup_conjSubgroup]
  have hNM : M ⊓ Subgroup.normalizer (U₂ : Set G) =
      conjSubgroup (M ⊓ Subgroup.normalizer (U₁ : Set G)) m := by
    rw [conjSubgroup_inf, conjSubgroup_normalizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hmM)]
  have hPm : conjSubgroup P m ≤ T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hPT hx)
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have := congrArg (fun z => m⁻¹ * z * m) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy
  have hSyl₂ : IsSylowIn 2 (T ⊓ Subgroup.normalizer (U₂ : Set G))
      (M ⊓ Subgroup.normalizer (U₂ : Set G)) := by
    have hPm' : IsSylowIn 2 (conjSubgroup P m) (M ⊓ Subgroup.normalizer (U₂ : Set G)) := by
      rw [hNM]
      refine ⟨conjSubgroup_mono_left m hP.le, hP.isPGroup.map _, ?_⟩
      unfold conjSubgroup
      rw [Subgroup.relIndex_map_map_of_injective _ _
        (fun a b hab => (MulAut.conj m⁻¹).injective hab)]
      exact hP.not_dvd_relIndex
    refine ⟨inf_le_inf_right _ h.T_le, h.sylow.1.to_le inf_le_left, fun h2 =>
      hPm'.not_dvd_relIndex (h2.trans (Subgroup.relIndex_dvd_of_le_left _ ?_))⟩
    exact le_inf hPm (hPm'.le.trans inf_le_right)
  set T' := conjSubgroup T (g⁻¹ * m) with hT'
  have hT'N : T' ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hU₂Z, hT', ← conjSubgroup_normalizer]
    exact conjSubgroup_mono_left _ (h.toHyp611Nat.T_le_normalizer_ZS)
  have hT'card : Nat.card T' = Nat.card T := card_conjSubgroup T _
  have hT'2 : IsPGroup 2 T' := h.sylow.1.map _
  have hU₂eq : U₂ = Z := by
    by_contra hne
    by_cases hC : Subgroup.centralizer (U₂ : Set G) ≤ Subgroup.normalizer (V : Set G)
    ·
      have hCM : Subgroup.centralizer (U₂ : Set G) ≤ M := hC.trans (h.normalizer_V_le h432)
      have hsylC : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (U₂ : Set G)) ⊓
          (M ⊓ Subgroup.centralizer (U₂ : Set G))) (M ⊓ Subgroup.centralizer (U₂ : Set G)) :=
        A4.isSylowTwoOf_inf_normal hSyl₂ (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
          (fun x hx => A4.mem_normalizer_inf (Subgroup.le_normalizer hx.1)
            (mem_normalizer_centralizer_ch62 hx.2))
      have hTC : (T ⊓ Subgroup.normalizer (U₂ : Set G)) ⊓ (M ⊓ Subgroup.centralizer (U₂ : Set G)) =
          T ⊓ Subgroup.centralizer (U₂ : Set G) := by
        ext x
        simp only [Subgroup.mem_inf]
        exact ⟨fun hx => ⟨hx.1.1, hx.2.2⟩, fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _
          hx.2⟩, h.T_le hx.1, hx.2⟩⟩
      rw [hTC] at hsylC
      have h1 := card_le_of_isSylowIn_ch62 hsylC
        (P := T' ⊓ Subgroup.centralizer (U₂ : Set G))
        (fun x hx => ⟨hCM hx.2, hx.2⟩) (hT'2.to_le inf_le_left)
      have h2 := relIndex_centralizer_le_two_ch62 hT'2 hT'N hU₂4
        (fun x hx => h.toHyp611.isElemAbelian.2 x (hU₂V hx))
      have h3 := Subgroup.relIndex_mul_card (T' ⊓ Subgroup.centralizer (U₂ : Set G)) T'
      rw [inf_of_le_left (inf_le_left : T' ⊓ Subgroup.centralizer (U₂ : Set G) ≤ T')] at h3
      have h4 := h.card_centralizer_mul_four_le h331 h615 hU₂V hU₂4 hne
      have hpos : 0 < Nat.card T := Nat.card_pos
      nlinarith
    ·
      have hm2 : mQuot V U₂ = 2 := by
        have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
        have h1 := card_eq_two_pow_mul hV2 hU₂V
        rw [h.natural.card_eq, hU₂4] at h1
        have : 2 ^ mQuot V U₂ = 4 := by omega
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4] at this
        exact Nat.pow_right_injective le_rfl this
      obtain ⟨t, -, -, -, ⟨-, -, -, -, hNsyl, hidx⟩, -⟩ :=
        h.lemma_6_2_4_one_five h331 h432 h615 h6110 hE612 hU₂V hm2 hC hSyl₂
      have h1 := card_le_of_isSylowIn_ch62 hNsyl hT'N hT'2
      rw [hT'card] at h1
      have heq : T ⊓ Subgroup.normalizer (U₂ : Set G) = T :=
        Subgroup.eq_of_le_of_card_ge inf_le_left h1 |>.symm ▸ rfl
      rw [heq, Subgroup.relIndex_self] at hidx
      exact absurd hidx (by norm_num)
  have hgm : g⁻¹ * m ∈ Subgroup.normalizer (Z : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← hU₂Z, hU₂eq]
  have hgmV : g⁻¹ * m ∈ Subgroup.normalizer (V : Set G) := h.normalizer_ZS_le h432 hgm
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.mul_mem _ hgmV (Subgroup.inv_mem _ hmV)
    simpa using Subgroup.inv_mem _ this
  exact conjSubgroup_eq_iff_mem_normalizer.mpr hgV

theorem exists_conj_ZS_le_of_hyperplane {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : Y.relIndex V = 2) : ∃ l ∈ L, conjSubgroup (ch6ZS T L V) l ≤ Y := by
  classical
  set D := h.data with hD
  have hK4 : Nat.card D.K = 4 := by rw [D.card]; norm_num
  set EY := D.addSub Y with hEYdef
  have hEY : EY.index = 2 := by rw [hEYdef, D.index_addSub hYV, hY]
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : D.K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set D.K) ⊆ {0, 1} := fun c _ => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · exact Or.inr (hcon c hc)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, hK4] at this
    have h2 : ({0, 1} : Set D.K).ncard ≤ 2 :=
      (Set.ncard_insert_le 0 {1}).trans (by rw [Set.ncard_singleton])
    omega
  let mω : (Fin 2 → D.K) →+ (Fin 2 → D.K) :=
    { toFun := fun w => ω • w
      map_zero' := smul_zero ω
      map_add' := fun a b => smul_add ω a b }
  have hmω : Function.Surjective mω := fun w => ⟨ω⁻¹ • w, by
    show ω • (ω⁻¹ • w) = w
    rw [smul_smul, mul_inv_cancel₀ hω0, one_smul]⟩
  set Y' := EY ⊓ EY.comap mω with hY'
  have hidx : Y'.index ≤ 4 := by
    calc Y'.index ≤ EY.index * (EY.comap mω).index := AddSubgroup.index_inf_le
      _ = 2 * 2 := by rw [hEY, AddSubgroup.index_comap_of_surjective _ hmω, hEY]
      _ = 4 := rfl
  obtain ⟨y, hyY', hy0⟩ : ∃ y ∈ Y', y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Y' = ⊥ := (AddSubgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, AddSubgroup.index_bot] at hidx
    have : Nat.card (Fin 2 → D.K) = 16 := by rw [Nat.card_fun, Nat.card_fin, hK4]; norm_num
    omega
  let ly : D.K →+ (Fin 2 → D.K) :=
    { toFun := fun c => c • y
      map_zero' := zero_smul _ y
      map_add' := fun a b => add_smul a b y }
  set S := EY.comap ly with hS
  have h1S : (1 : D.K) ∈ S := by
    show (1 : D.K) • y ∈ EY
    rw [one_smul]
    exact hyY'.1
  have hωS : ω ∈ S := hyY'.2
  have hStop : S = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    have hdvd : Nat.card S ∣ 4 := hK4 ▸ AddSubgroup.card_addSubgroup_dvd_card S
    have h3 : 3 ≤ Nat.card S := by
      have hfin : ({0, 1, ω} : Finset D.K).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hω1)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, Ne.symm hω0⟩
      have hsub : (({0, 1, ω} : Finset D.K) : Set D.K) ⊆ (S : Set D.K) := by
        intro c hc
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl
        · exact S.zero_mem
        · exact h1S
        · exact hωS
      calc 3 = ({0, 1, ω} : Finset D.K).card := hfin.symm
        _ = (({0, 1, ω} : Finset D.K) : Set D.K).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ (S : Set D.K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card S := Nat.card_coe_set_eq _ |>.symm
    rw [hK4]
    have : Nat.card S ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hline : ∀ c : D.K, c • y ∈ EY := fun c => by
    have : c ∈ S := hStop ▸ AddSubgroup.mem_top c
    exact this
  set U := D.subOf (Submodule.span D.K {y}).toAddSubgroup with hUdef
  have hUmem : ∀ u (hu : u ∈ V), u ∈ U ↔
      ∃ c : D.K, Multiplicative.toAdd (D.E ⟨u, hu⟩) = c • y := by
    intro u hu
    rw [hUdef, D.mem_subOf]
    constructor
    · rintro ⟨hu', hmem⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨hu, Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩⟩
  obtain ⟨l, hl, hUl⟩ := h.toHyp611Nat.exists_conj_ZS_of_line (D.subOf_le _) hy0 hUmem
  refine ⟨l, hl, hUl ▸ fun u hu => ?_⟩
  have huV : u ∈ V := D.subOf_le _ hu
  obtain ⟨c, hc⟩ := (hUmem u huV).mp hu
  have := hline c
  rw [← hc] at this
  exact (D.toAdd_mem_addSub ⟨u, huV⟩).mp this

theorem lemma_6_2_5_six (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : Y.relIndex V = 2) {g : G} (hYg : Y ≤ conjSubgroup V g) : conjSubgroup V g = V := by
  obtain ⟨l, hl, hle⟩ := h.exists_conj_ZS_le_of_hyperplane hYV hY
  have h1 : ch6ZS T L V ≤ conjSubgroup V (g * l⁻¹) := by
    have := conjSubgroup_mono_left l⁻¹ (hle.trans hYg)
    rwa [conjSubgroup_conj_inv, conjSubgroup_conjSubgroup] at this
  have h2 := h.lemma_6_2_5_four h331 h432 h615 h6110 hE612 h1
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hl
  calc conjSubgroup V g = conjSubgroup (conjSubgroup V (g * l⁻¹)) l := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    _ = conjSubgroup V l := by rw [h2]
    _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr hlV

end Hyp6Sec2

end CFSG.Quasithin.H13
