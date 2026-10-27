module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Helpers

variable {G : Type} [Group G]

private theorem thompsonJ_le' (T : Subgroup G) : thompsonJ T ≤ T :=
  iSup₂_le fun _ hA => hA.1

private theorem eOf_le_centerOf (T : Subgroup G) : eOf T ≤ centerOf (thompsonJ T) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem eOf_comm {T : Subgroup G} {a b : G} (ha : a ∈ eOf T) (hb : b ∈ eOf T) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf T ha).2 b (eOf_le_centerOf T hb).1).symm

private theorem eOf_le (T : Subgroup G) : eOf T ≤ T :=
  fun _ hx => thompsonJ_le' T (eOf_le_centerOf T hx).1

private theorem omegaOneCenter_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

private theorem omegaOneCenter_le_eOf [Finite G] (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ eOf T := by
  rw [eOf, ← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.closure_mono ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  exact ⟨⟨hzT, Subgroup.centralizer_le (thompsonJ_le' T) hzC⟩, hz2⟩

private theorem omegaOneCenter_le_baum (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ baum T := by
  intro z hz
  have hz' := omegaOneCenter_le_center T hz
  exact ⟨hz'.1, Subgroup.centralizer_le (eOf_le T) hz'.2⟩

private theorem isYFamily_basic {T Y : Subgroup G} (hY : IsYFamily T Y) :
    Y = oTwoUpper Y ∧ T ≤ Subgroup.normalizer (Y : Set G) ∧ pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
  rcases hY.1 with h | h
  · exact ⟨h.1, h.2.1, h.2.2.1⟩
  · exact ⟨h.1, h.2.1, h.2.2.1.2⟩

private theorem exists_inM_of_isYFamily [Finite G] {T Y : Subgroup G} (hY : IsYFamily T Y) :
    ∃ M : Subgroup G, InM T M ∧ Y ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hP⟩ := isYFamily_basic hY
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Y ⊔ T) : Set G)) :=
    ⟨pCoreOf 2 (Y ⊔ T), hP, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge h2
  have hYT := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T)).trans hle
  exact ⟨M, ⟨hM, le_sup_right.trans hYT⟩, le_sup_left.trans hYT⟩

private theorem not_le_of_isYFamily {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hY : IsYFamily T Y) : ¬ Y ≤ T := by
  intro hYT
  have h1 : (pCoreOf 2 Y).relIndex Y = 1 :=
    Subgroup.relIndex_eq_one.mpr (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
      Subgroup.le_normalizer (hT.to_le hYT))
  rcases hY.1 with h | h
  · obtain ⟨-, -, -, p, hp, -, -, hidx, -⟩ := h
    have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    have hp3 : 1 < p ^ 3 := Nat.one_lt_pow three_ne_zero hp.one_lt
    rw [h1] at hidx
    omega
  · obtain ⟨-, -, -, p, hp, -, hidx⟩ := h
    rw [h1] at hidx
    exact hp.one_lt.ne hidx

private theorem relIndex_ne_zero' [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := fun h =>
  (Nat.card_pos (α := K)).ne' (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_card H K))

private theorem exists_ne_one_mem_centralizer [Finite G] {S V : Subgroup G} (hS : IsPGroup 2 S)
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hV : 2 ∣ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S V :=
    { smul := fun s v => ⟨(s : G) * v * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSV s.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by
        change ((1 : S) : G) * v * ((1 : S) : G)⁻¹ = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        change ((a * b : S) : G) * v * ((a * b : S) : G)⁻¹ =
          (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]) }
  have h1 : (1 : V) ∈ MulAction.fixedPoints S V := fun s => Subtype.ext (by
    change (s : G) * 1 * (s : G)⁻¹ = 1
    simp)
  obtain ⟨v, hv, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV h1
  refine ⟨v, v.2, fun h => hne (Subtype.ext h.symm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h : (s : G) * v * s⁻¹ = v := congrArg Subtype.val (hv ⟨s, hs⟩)
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem oTwoUpper_sup_eq {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = oTwoUpper Y) :
    oTwoUpper (Y ⊔ T) = Y := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hY).symm
  have hx' : x ∈ ((Y ⊔ T : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY] at hx'
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hTY ht) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

end Helpers

private theorem relIndex_inf_centralizer_eq_two {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (h3 : Stmt1542Three G T) (h8 : Stmt1548 G T) (h12 : Stmt15412 G T)
    {Y : Subgroup G} (hY : IsYFamily T Y) :
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (Y : Set G)).relIndex
      (quasithinOmegaOneCenter T) = 2 := by
  set Z := quasithinOmegaOneCenter T
  have hne1 : (Z ⊓ Subgroup.centralizer (Y : Set G)).relIndex Z ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    have hZY : Z ≤ Subgroup.centralizer (Y : Set G) := hle.trans inf_le_right
    rcases hY.1 with hXi | -
    · exact (h3 Y hXi).1 (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZY)
    · exact not_le_of_isYFamily hT hY ((Subgroup.le_centralizer_iff.mp hZY).trans h8.le)
  have hle2 : (Z ⊓ Subgroup.centralizer (Y : Set G)).relIndex Z ≤ 2 := by
    obtain ⟨-, hTY, -⟩ := isYFamily_basic hY
    obtain ⟨M, hM, hYM⟩ := exists_inM_of_isYFamily hY
    obtain ⟨-, -, -, -, -, ⟨-, -, hE, hEinf⟩, h6, -⟩ := (h12 M hM).2 Y hY hYM
    set EY := eCentOf T Y
    have hZE : Z ≤ eOf T := omegaOneCenter_le_eOf T
    have h1 : (Z ⊓ Subgroup.centralizer (Y : Set G)).relIndex Z ≤ (Z ⊓ EY).relIndex Z :=
      Subgroup.relIndex_le_of_le_left (inf_le_inf_left Z inf_le_right) (relIndex_ne_zero' _ _)
    refine h1.trans ?_
    rcases h6 with ⟨-, -, hidx⟩ |
      ⟨-, -, Y₁, Y₂, hYeq, -, -, -, -, -, hVinf, hc₁, -, -, -, hS₁, -, ⟨t, ht, hYt⟩, hidx, -⟩
    ·
      rw [Subgroup.inf_relIndex_left]
      exact (Subgroup.relIndex_le_of_le_right hZE (relIndex_ne_zero' _ _)).trans hidx.le
    ·
      set VM := VZ T M
      set S := baum T
      set V₁ := ⁅VM, Y₁⁆ with hV₁
      set V₂ := ⁅VM, Y₂⁆ with hV₂
      set C := ⁅VM, Y⁆ ⊓ Subgroup.centralizer (S : Set G)
      set C₁ := V₁ ⊓ Subgroup.centralizer (S : Set G)
      have hTVM : T ≤ Subgroup.normalizer (VM : Set G) :=
        hM.2.trans (le_normalizer_conjClosure _ _)
      have hST : S ≤ T := inf_le_left
      have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
      have hY₁Y : Y₁ ≤ Y := hYeq ▸ le_sup_left
      have hY₂Y : Y₂ ≤ Y := hYeq ▸ le_sup_right
      have hV₁V : V₁ ≤ ⁅VM, Y⁆ := Subgroup.commutator_mono le_rfl hY₁Y
      have hV₂V : V₂ ≤ ⁅VM, Y⁆ := Subgroup.commutator_mono le_rfl hY₂Y
      have hSV₁ : S ≤ Subgroup.normalizer (V₁ : Set G) := fun s hs =>
        A4.mem_normalizer_commutator (hTVM (hST hs)) (hS₁ hs)
      obtain ⟨c, hcV₁, hc1, hcS⟩ :=
        exists_ne_one_mem_centralizer (hT.to_le hST) hSV₁ (by rw [hc₁]; norm_num)
      have hEY_le : EY ≤ eOf T := hE ▸ le_sup_left
      have hC_le : C ≤ eOf T := hE ▸ le_sup_right
      have hC₁C : C₁ ≤ C := inf_le_inf_right _ hV₁V
      have hEYC₁ : EY ⊔ C₁ ≤ eOf T := sup_le hEY_le (hC₁C.trans hC_le)
      have hnot : ¬ C₁ ≤ EY := by
        intro hle
        have hcmem : c ∈ EY ⊓ C := ⟨hle ⟨hcV₁, hcS⟩, hC₁C ⟨hcV₁, hcS⟩⟩
        rw [hEinf, Subgroup.mem_bot] at hcmem
        exact hc1 hcmem
      have hk1 : EY.relIndex (EY ⊔ C₁) ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        exact fun h => hnot (le_sup_right.trans h)
      have hk0 := relIndex_ne_zero' EY (EY ⊔ C₁)
      have htower := Subgroup.relIndex_mul_relIndex EY (EY ⊔ C₁) (eOf T) le_sup_left hEYC₁
      rw [hidx] at htower
      have hm : (EY ⊔ C₁).relIndex (eOf T) ≤ 2 := by
        have h2 : 2 * (EY ⊔ C₁).relIndex (eOf T) ≤
            EY.relIndex (EY ⊔ C₁) * (EY ⊔ C₁).relIndex (eOf T) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hV₁₂ : V₁.map (MulAut.conj t).toMonoidHom = V₂ := by
        rw [hV₁, hV₂, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hTVM ht), ← hYt]
      have hkey : Z ⊓ (EY ⊔ C₁) ≤ EY := by
        rintro z ⟨hzZ, hz⟩
        have hC₁N : C₁ ≤ Subgroup.normalizer (EY : Set G) := by
          refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact eOf_comm (hEY_le he) (hC_le (hC₁C hx))
        have hz' : z ∈ ((EY ⊔ C₁ : Subgroup G) : Set G) := hz
        rw [Subgroup.coe_mul_of_right_le_normalizer_left EY C₁ hC₁N] at hz'
        obtain ⟨e, he, c', hc', rfl⟩ := Set.mem_mul.mp hz'
        have htz : t * (e * c') * t⁻¹ = e * c' := by
          rw [Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_center T hzZ).2 t ht,
            mul_inv_cancel_right]
        have htP : t ∈ Subgroup.normalizer (eOf T : Set G) :=
          normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv _
            (normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer ht))
        have htCY : t ∈ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) :=
          normalizer_le_normalizer_of_map_mulEquiv
            (F := fun X => Subgroup.centralizer (X : Set G)) centralizer_map_mulEquiv Y (hTY ht)
        have htCS : t ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
          normalizer_le_normalizer_of_map_mulEquiv
            (F := fun X => Subgroup.centralizer (X : Set G)) centralizer_map_mulEquiv S (hTS ht)
        have hte : t * e * t⁻¹ ∈ EY :=
          ⟨(Subgroup.mem_normalizer_iff.mp htP e).mp he.1,
            (Subgroup.mem_normalizer_iff.mp htCY e).mp he.2⟩
        have hc'V₂ : t * c' * t⁻¹ ∈ V₂ := by
          rw [← hV₁₂]
          exact ⟨c', hc'.1, by simp⟩
        have htc : t * c' * t⁻¹ ∈ C :=
          ⟨hV₂V hc'V₂, (Subgroup.mem_normalizer_iff.mp htCS c').mp hc'.2⟩
        have hrel : e⁻¹ * (t * e * t⁻¹) = c' * (t * c' * t⁻¹)⁻¹ := by
          have h1 : t * e * t⁻¹ = e * c' * (t * c' * t⁻¹)⁻¹ := by
            rw [← htz]
            group
          rw [h1]
          group
        have hmem : c' * (t * c' * t⁻¹)⁻¹ ∈ EY ⊓ C :=
          ⟨hrel ▸ EY.mul_mem (EY.inv_mem he) hte, C.mul_mem (hC₁C hc') (C.inv_mem htc)⟩
        rw [hEinf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
        have hc'V₂' : c' ∈ V₂ := by
          rw [hmem]
          exact hc'V₂
        have hc'1 : c' = 1 := by
          have hc'm : c' ∈ V₁ ⊓ V₂ := ⟨hc'.1, hc'V₂'⟩
          rwa [hVinf, Subgroup.mem_bot] at hc'm
        rw [hc'1, mul_one]
        exact he
      have heq : Z ⊓ EY = Z ⊓ (EY ⊔ C₁) :=
        le_antisymm (inf_le_inf_left Z le_sup_left) (le_inf inf_le_left hkey)
      rw [heq, Subgroup.inf_relIndex_left]
      exact (Subgroup.relIndex_le_of_le_right hZE (relIndex_ne_zero' _ _)).trans hm
  have := relIndex_ne_zero' (Z ⊓ Subgroup.centralizer (Y : Set G)) Z
  omega

theorem stmt15414_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h3 : Stmt1542Three G T) (h7 : Stmt1547 G T)
    (h8 : Stmt1548 G T) (h11 : Stmt15411 G T) (h12 : Stmt15412 G T) : Stmt15414 G T := by
  intro hnot
  have hT : IsPGroup 2 T := hyp.sylow.1
  have h1 : ∀ Y : Subgroup G, IsYFamily T Y →
      (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (Y : Set G)).relIndex
        (quasithinOmegaOneCenter T) = 2 :=
    fun Y hY => relIndex_inf_centralizer_eq_two hT h3 h8 h12 hY
  refine ⟨h1, ?_⟩
  set Z := quasithinOmegaOneCenter T
  have hZ2 : Nat.card Z ≠ 2 := by
    intro h2
    rcases h7 h2 with ⟨-, Mf, -, -, -, -, hMf, hall⟩ | h
    · exact (h11 Mf hMf).2.2.1 ⟨Mf, hMf, hall⟩
    · exact hnot h
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
  obtain ⟨⟨X, hX, hXM₁⟩, hall₁⟩ := h12 M₁ ⟨hM₁, h8.ge.trans hCM₁⟩
  obtain ⟨⟨Y, hY, hYM₂⟩, hall₂⟩ := h12 M₂ ⟨hM₂, h8.ge.trans hCM₂⟩
  obtain ⟨-, -, hU₁, -⟩ := hall₁ X hX hXM₁
  obtain ⟨-, -, hU₂, -⟩ := hall₂ Y hY hYM₂
  have hW : (Z ⊓ Subgroup.centralizer (X : Set G)) ⊓ (Z ⊓ Subgroup.centralizer (Y : Set G)) =
      ⊥ := by
    by_contra hWne
    set W := (Z ⊓ Subgroup.centralizer (X : Set G)) ⊓ (Z ⊓ Subgroup.centralizer (Y : Set G))
    have hWZ : W ≤ Z := inf_le_left.trans inf_le_left
    have hZT := omegaOneCenter_le_center T
    have hW2 : IsPGroup 2 W := hT.to_le (hWZ.trans (hZT.trans inf_le_left))
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (⟨W, hWne, hW2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (W : Set G)))
    have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.le_centralizer_iff.mp (hWZ.trans (hZT.trans inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _)
    have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.le_centralizer_iff.mp (inf_le_left.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hYW : Y ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.le_centralizer_iff.mp (inf_le_right.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
    have e₁ := hU₁.2 M' ⟨hM', (sup_le hXW hTW).trans hNM'⟩
    have e₂ := hU₂.2 M' ⟨hM', (sup_le hYW hTW).trans hNM'⟩
    exact hne (e₁.symm.trans e₂)
  have hle : Nat.card Z ≤ 2 * 2 := by
    have h := Subgroup.relIndex_inf_le (H := Z ⊓ Subgroup.centralizer (X : Set G))
      (K := Z ⊓ Subgroup.centralizer (Y : Set G)) (L := Z)
    rwa [hW, Subgroup.relIndex_bot_left, h1 X hX, h1 Y hY] at h
  have hdvd : 2 ∣ Nat.card Z := by
    have h := Subgroup.relIndex_dvd_card (Z ⊓ Subgroup.centralizer (X : Set G)) Z
    rwa [h1 X hX] at h
  have hpos : 0 < Nat.card Z := Nat.card_pos
  omega

theorem stmt15416_of (h311 : Input311Solvable) {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T)
    (h12 : Stmt15412 G T) : Stmt15416 G T := by
  intro M hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 T := hyp.sylow.1
  obtain ⟨⟨Y, hY, hYM⟩, hall⟩ := h12 M hM
  obtain ⟨-, -, hU, -, hSyl, -, -, N, hN⟩ := hall Y hY hYM
  obtain ⟨hYO, hTY, hP⟩ := isYFamily_basic hY
  set S := baum T
  have hST : S ≤ T := inf_le_left
  have hS2 : IsPGroup 2 S := hT.to_le hST
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTne : T ≠ ⊥ := by
    have := hyp.simple
    exact sylow_ne_bot hyp.nonabelian (hT.toSylow hyp.sylow.2)
  have hSne : S ≠ ⊥ := by
    intro h
    apply quasithinOmegaOneCenter_ne_bot hT hTne
    rw [eq_bot_iff, ← h]
    exact omegaOneCenter_le_baum T
  have hSO : S ≤ pCoreOf 2 (Subgroup.normalizer (S : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hS2
  have hH₁ : InH T (Subgroup.normalizer (S : Set G)) :=
    ⟨hTS, fun h => hSne (le_bot_iff.mp (h ▸ hSO))⟩
  have hH₂ : InH T (Y ⊔ T) := ⟨le_sup_right, hP⟩
  have hSyl' : IsSylowTwoOf S (oTwoUpper (Y ⊔ T) ⊔ S) := by
    rw [oTwoUpper_sup_eq hT hTY hYO]
    exact hSyl
  have hsolvYT : Group.IsSolvable ↥(Y ⊔ T) := by
    have := h2 M hM
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hU.1.2)
  obtain ⟨R₀, hR₀, hR₀S, hle⟩ := h311 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    (Subgroup.normalizer (S : Set G)) (Y ⊔ T) S hH₁ hH₂ hsolvYT ⟨N, hN.uniqueMax⟩ hSne hST hSyl'
    le_rfl
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
    (⟨R₀, hR₀, hS2.to_le hR₀S, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R₀ : Set G)))
  have hM'M : M' = M := hU.2 M' ⟨hM', (le_sup_right.trans hle).trans hNM'⟩
  rw [← hM'M]
  exact (le_sup_left.trans hle).trans hNM'

end CFSG.Quasithin.EmptyFaithfulMultiple
