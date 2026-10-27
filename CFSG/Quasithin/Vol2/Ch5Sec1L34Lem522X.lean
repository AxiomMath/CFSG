module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522Y
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OrthFix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

theorem exists_eq_conj_of_coprime_six {X : Type} [Group X] (hX : LieModel X .PSL 3 2 2)
    {φ : MulAut X} (hcop : Nat.Coprime (orderOf φ) 6) : ∃ x : X, φ = MulAut.conj x := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hcardT : Nat.card (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 12 := by
    rw [SemidirectProduct.card, LinearThreeFourOuter.card_units_eq_three hk, Nat.card_prod]
    simp
  set φ' := MulAut.congr e φ with hφ'
  have hord' : orderOf φ' = orderOf φ := orderOf_injective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective φ
  have hΨ1 : Ψ φ' = 1 := by
    have h1 : orderOf (Ψ φ') ∣ orderOf φ' := orderOf_map_dvd Ψ φ'
    have h2 : orderOf (Ψ φ') ∣ 12 := by
      have : Finite (kˣ ⋊[LinearThreeFourOuter.inversionAction kˣ]
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
        Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
      rw [← hcardT]
      exact orderOf_dvd_natCard _
    have hc12 : Nat.Coprime (orderOf φ') 12 := by
      rw [hord']
      have h12 : (12 : ℕ) = 6 * 2 := by norm_num
      rw [h12]
      exact Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc12) h2
    exact orderOf_eq_one_iff.mp this
  have hmem : φ' ∈ Ψ.ker := hΨ1
  rw [hker] at hmem
  obtain ⟨x', hx'⟩ := hmem
  refine ⟨e.symm x', ?_⟩
  apply (MulAut.congr e).injective
  rw [← hφ', ← hx', CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    e.apply_symm_apply]

section General

variable {G : Type} [Group G]

theorem quotConjAut_of_mem {X : Subgroup G} (k : ↥X) :
    quotConjAut X ⟨k, Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (QuotientGroup.mk k : O2Q X) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [quotConjAut_mk, MulAut.conj_apply]
    rfl

theorem le_normalizer_sup_of_le {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)]

theorem normalizer_le_normalizer_closure_coprime (C : Subgroup G) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer
      (Subgroup.closure {x | x ∈ C ∧ Nat.Coprime (orderOf x) 6} : Set G) := by
  rw [Subgroup.le_normalizer_closure_iff]
  rintro t ht x ⟨hx, hxo⟩
  refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp ht x).mp hx, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj t) x
  rw [MulAut.conj_apply] at this
  rwa [this]

theorem odd_orderOf_of_coprime_six {x : G} (h : Nat.Coprime (orderOf x) 6) : Odd (orderOf x) :=
  Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) h)

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem Hyp5_1_14.exists_mul_mem_of_coprime_six (h : Hyp5_1_14 G T M L V H B D n) {g : G}
    (hg : g ∈ Subgroup.normalizer (oTwoUpper H : Set G)) (hcop : Nat.Coprime (orderOf g) 6) :
    ∃ k ∈ oTwoUpper H, g * k⁻¹ ∈ centralizerModO2 (oTwoUpper H) := by
  set K := oTwoUpper H with hKdef
  set g' : ↥(Subgroup.normalizer (K : Set G)) := ⟨g, hg⟩ with hg'
  have h1 : orderOf (quotConjAut K g') ∣ orderOf g := by
    have := orderOf_map_dvd (quotConjAut K) g'
    rwa [hg', Subgroup.orderOf_mk] at this
  obtain ⟨q, hq⟩ := exists_eq_conj_of_coprime_six h.l34 (Nat.Coprime.coprime_dvd_left h1 hcop)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k, k.2, ?_⟩
  have h2 : quotConjAut K (g' * ⟨k, Subgroup.le_normalizer k.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hq, quotConjAut_of_mem, mul_inv_cancel]
  exact mem_centralizerModO2_of_quotConjAut_eq_one h2

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem mem_centralizerModO2_of_coprime_six (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (h510 : Stmt5_1_10) (h516 : Stmt5_1_16) (h521 : Stmt5_1_21)
    (hnot : ¬ Concl5_1_14_four T L V B D n) {g : G}
    (hgC : g ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G))
    (hcop : Nat.Coprime (orderOf g) 6) : g ∈ centralizerModO2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hyp := s.hyp.hyp
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  set K := oTwoUpper H with hKdef
  set CK := centralizerModO2 K with hCKdef
  set X := Subgroup.closure {x | x ∈ C ∧ Nat.Coprime (orderOf x) 6} with hXdef
  have hCM := s.centralizer_le_normalizer h5114
  have hXC : X ≤ C := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hgX : g ∈ X := Subgroup.subset_closure ⟨hgC, hcop⟩
  have hMCK := normalizer_le_normalizer_centralizerModO2 K
  have hTM : T ≤ Subgroup.normalizer (K : Set G) := s.hyp.T_le_Mp
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (s.T_le_normalizer_V₂ hF)
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    hTC.trans (normalizer_le_normalizer_closure_coprime C)
  set W := K ⊓ (X ⊔ CK) with hWdef
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_inf hTM (le_normalizer_sup_of_le hTX (hTM.trans hMCK))
  have hWTH : W ⊔ T ≤ H := sup_le (inf_le_left.trans (oTwoUpper_le H)) hyp.hStar.1.1
  by_cases hWTM : W ⊔ T ≤ M
  ·
    obtain ⟨k, hkK, hck⟩ := s.hyp.exists_mul_mem_of_coprime_six (hCM hgC) hcop
    have hkW : k ∈ W := by
      refine ⟨hkK, ?_⟩
      have e : k = (g * k⁻¹)⁻¹ * g := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (CK.inv_mem hck))
        (Subgroup.mem_sup_left hgX)
    have hkMH : k ∈ M ⊓ H :=
      ⟨hWTM (Subgroup.mem_sup_left hkW), hWTH (Subgroup.mem_sup_left hkW)⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hh.sylow.1
    have hk6 : orderOf k ∣ 2 ^ a * 3 := by
      have := orderOf_dvd_natCard (⟨k, hkMH⟩ : ↥(M ⊓ H))
      rwa [Subgroup.orderOf_mk, hyp.card_inf_eq s.hyp.notation59, ha,
        s.hyp.card_B_eq_three h510] at this
    have hkM : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
    have hpow : ∀ j : ℕ, g ^ j * (k ^ j)⁻¹ ∈ CK := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hkj : k ^ j ∈ Subgroup.normalizer (CK : Set G) :=
          hMCK ((Subgroup.normalizer _).pow_mem hkM j)
        have h1 : k ^ j * (g * k⁻¹) * (k ^ j)⁻¹ ∈ CK :=
          (Subgroup.mem_normalizer_iff.mp hkj _).mp hck
        have e : g ^ (j + 1) * (k ^ (j + 1))⁻¹ =
            (g ^ j * (k ^ j)⁻¹) * (k ^ j * (g * k⁻¹) * (k ^ j)⁻¹) := by
          rw [pow_succ, pow_succ]; group
        rw [e]
        exact CK.mul_mem ih h1
    have hkm : k ^ orderOf g ∈ CK := by
      have := hpow (orderOf g)
      rw [pow_orderOf_eq_one, one_mul] at this
      simpa using CK.inv_mem this
    have hcop' : Nat.Coprime (orderOf g) (orderOf k) := by
      refine Nat.Coprime.coprime_dvd_right hk6 (Nat.Coprime.mul_right ?_ ?_)
      · exact Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
      · exact Nat.Coprime.coprime_dvd_right (by norm_num) hcop
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop'
    have hkCK : k ∈ CK := by
      rw [← hu]
      exact CK.pow_mem hkm u
    have e : g = (g * k⁻¹) * k := by group
    rw [e]
    exact CK.mul_mem hck hkCK
  ·
    exfalso
    have hO : pCoreOf 2 (W ⊔ T) ≠ ⊥ := by
      intro hb
      apply hyp.hStar.1.2
      have hle := CFSG.Quasithin.pCoreOf_le_pCoreOf_of_sylow hWTH hh.sylow.1 le_sup_right
        (hh.isSylowTwoOf hyp.hStar.1.1).2.2
      rw [hb] at hle
      exact le_bot_iff.mp hle
    have heq := hyp.hStar.2.2 (W ⊔ T) ⟨le_sup_right, hO⟩ hWTH hWTM
    have hKW : K ≤ W := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxH, hxo⟩
      exact mem_of_odd_of_mem_sup hh.sylow.1 hTW (by rw [heq]; exact hxH) hxo
    have hKXC : K ≤ X ⊔ CK := hKW.trans inf_le_right
    have h9K : 9 ∣ Nat.card K := by
      obtain ⟨E, hE9, -, -⟩ := l34ElemNineFact _ s.hyp.l34
      have h1 : 9 ∣ Nat.card (O2Q K) := hE9 ▸ Subgroup.card_subgroup_dvd_card E
      exact h1.trans (Subgroup.index_dvd_card _)
    have h3CK : ¬ 3 ∣ Nat.card ↥CK :=
      (h516 G T M L V H B D n hyp s.hyp.notation59 s.hyp.module s.hyp.l34).1
    have hidxK : 9 ∣ CK.relIndex K := by
      have e1 := CK.relIndex_mul_card K
      rw [← e1] at h9K
      have hcop9 : Nat.Coprime 9 (Nat.card ↥(CK ⊓ K)) := by
        have h1 : Nat.card ↥(CK ⊓ K) ∣ Nat.card ↥CK := Subgroup.card_dvd_of_le inf_le_left
        have h2 : Nat.Coprime 3 (Nat.card ↥(CK ⊓ K)) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => h3CK (h3.trans h1)
        have h3 : (9 : ℕ) = 3 ^ 2 := by norm_num
        rw [h3]
        exact Nat.Coprime.pow_left 2 h2
      exact hcop9.dvd_of_dvd_mul_right h9K
    have hKCK : K ≤ Subgroup.normalizer (CK : Set G) := Subgroup.le_normalizer.trans hMCK
    have hXCK : X ≤ Subgroup.normalizer (CK : Set G) := (hXC.trans hCM).trans hMCK
    have hdvd1 : CK.relIndex (K ⊔ CK) ∣ CK.relIndex (X ⊔ CK) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex CK (K ⊔ CK) (X ⊔ CK) le_sup_right
        (sup_le hKXC le_sup_right))
    rw [B6.relIndex_sup_eq_of_le_normalizer hKCK, B6.relIndex_sup_eq_of_le_normalizer hXCK]
      at hdvd1
    have hdvd2 : CK.relIndex X ∣ Nat.card X := Dvd.intro _ (CK.relIndex_mul_card X)
    exact s.not_nine_dvd_card h5114 hF h516 h521 hnot
      (hidxK.trans (hdvd1.trans (hdvd2.trans (Subgroup.card_dvd_of_le hXC))))

theorem le_normalizer_X (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h521 : Stmt5_1_21) (hnot : ¬ Concl5_1_14_four T L V B D n) :
    oTwoUpper H ≤ Subgroup.normalizer (Subgroup.closure
      {x | x ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) ∧ Nat.Coprime (orderOf x) 6} :
        Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  set C := Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) with hCdef
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set X := Subgroup.closure {x | x ∈ C ∧ Nat.Coprime (orderOf x) 6} with hXdef
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (s.T_le_normalizer_V₂ hF)
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    hTC.trans (normalizer_le_normalizer_closure_coprime C)
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf s.hyp.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  have hQT : Q ≤ T := (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK).trans inf_le_left
  have hQX : Q ≤ Subgroup.normalizer (X : Set G) := hQT.trans hTX
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 K
  rw [hXdef, Subgroup.le_normalizer_closure_iff]
  rintro k hk x ⟨hxC, hxo⟩
  have hxCK := s.mem_centralizerModO2_of_coprime_six h5114 hF h510 h516 h521 hnot hxC hxo
  have hmem : k * x * k⁻¹ ∈ X ⊔ Q := by
    have hc : x * k * x⁻¹ * k⁻¹ ∈ Q := hxCK.2.2 k hk
    have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Q.inv_mem hc))
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hxC, hxo⟩))
  have hodd : Odd (orderOf (k * x * k⁻¹)) := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact odd_orderOf_of_coprime_six hxo
  exact mem_of_odd_of_mem_sup hQ2 hQX hmem hodd

end Setup521

theorem stmt5_1_22_one_X_of (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h520 : Stmt5_1_20) (h521 : Stmt5_1_21) : Stmt5_1_22_one_X := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp hN hV hK h4 hD₃ h3 hZ₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨h, hD₃, h3, (h520 G T M L V H B D n hyp hN hV hK h4 D₃ hD₃ h3).1, hZ₁⟩
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  set G₂ := Subgroup.normalizer (V₂ : Set G) with hG₂def
  set X := Subgroup.closure {x | x ∈ C ∧ Nat.Coprime (orderOf x) 6} with hXdef
  have hCG₂ : G₂ ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer le_rfl
  have hG₂X : G₂ ≤ Subgroup.normalizer (X : Set G) :=
    hCG₂.trans (normalizer_le_normalizer_closure_coprime C)
  have hKX := s.le_normalizer_X h5114 hF h510 h516 h521 h4
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := (s.T_le_normalizer_V₂ hF).trans hG₂X
  have hD₃X : D₃ ≤ Subgroup.normalizer (X : Set G) :=
    (le_normalizer_conjClosure Z₁ D₃).trans hG₂X
  have hXC : X ≤ C := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hXG₂ : X ≤ G₂ := hXC.trans (Subgroup.centralizer_le_normalizer _)
  have hO : pCoreOf 2 X = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
      ⟨pCoreOf 2 X, hne, pCoreOf_isPGroup 2 X, rfl⟩
    obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
    have hXN := normalizer_le_normalizer_pCoreOf 2 X
    have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
      rw [h.H_eq_sup]
      exact sup_le (hKX.trans hXN) (hTX.trans hXN)
    have hM'eq := (h.isUniqueM h5114).2 M' ⟨hM', hHN.trans hle'⟩
    exact s.not_le ((hD₃X.trans hXN).trans (hM'eq ▸ hle'))
  set R := pCoreOf 2 G₂ with hRdef
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 G₂
  have hG₂R : G₂ ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 G₂
  have hRG₂ : R ≤ G₂ := pCoreOf_le 2 G₂
  have hXR : X ⊓ R = ⊥ := by
    have hle : X ⊓ R ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer (hXG₂.trans hG₂R)) (hR2.to_le inf_le_right)
    rw [hO] at hle
    exact le_bot_iff.mp hle
  have hchar : CharTwo G₂ := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
    have hT : (S : Subgroup G) ≤ G₂ := by rw [hS]; exact s.T_le_normalizer_V₂ hF
    obtain ⟨z, hz, hz1⟩ := s.exists_z
    have hV₂ne : V₂ ≠ ⊥ := fun hb' => hz1 (by
      have := (le_conjClosure Z₁ D₃) hz
      rw [← hV₂def, hb'] at this
      exact Subgroup.mem_bot.mp this)
    have hloc : IsTwoLocal G₂ :=
      ⟨V₂, hV₂ne, isPGroup_of_isElemAbelian s.isElemAbelian_V₂, rfl⟩
    exact charTwo_of_le hh.qtke.2.1 S hT le_rfl ⟨hT, pCoreOf_ne_bot_of_isTwoLocal hloc⟩
  have hX1 : ∀ g ∈ C, Nat.Coprime (orderOf g) 6 → g = 1 := by
    intro g hgC hcop
    have hgX : g ∈ X := Subgroup.subset_closure ⟨hgC, hcop⟩
    have hgR : g ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 : g * r * g⁻¹ * r⁻¹ ∈ X := by
        have : r * g⁻¹ * r⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hG₂X (hRG₂ hr)) _).mp (X.inv_mem hgX)
        have e : g * r * g⁻¹ * r⁻¹ = g * (r * g⁻¹ * r⁻¹) := by group
        rw [e]
        exact X.mul_mem hgX this
      have h2 : g * r * g⁻¹ * r⁻¹ ∈ R := by
        have : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hG₂R (hXG₂ hgX)) r).mp hr
        exact R.mul_mem this (R.inv_mem hr)
      have h3 : g * r * g⁻¹ * r⁻¹ = 1 := by
        have : g * r * g⁻¹ * r⁻¹ ∈ X ⊓ R := ⟨h1, h2⟩
        rw [hXR] at this
        exact Subgroup.mem_bot.mp this
      calc r * g = (g * r * g⁻¹ * r⁻¹)⁻¹ * (g * r) := by group
        _ = g * r := by rw [h3, inv_one, one_mul]
    have hgR' : g ∈ R := hchar ⟨hXG₂ hgX, hgR⟩
    have : g ∈ X ⊓ R := ⟨hgX, hgR'⟩
    rw [hXR] at this
    exact Subgroup.mem_bot.mp this
  intro x hx
  induction hN' : orderOf x using Nat.strong_induction_on generalizing x with
  | _ N ih =>
    have hpos := orderOf_pos x
    by_cases h2 : 2 ∣ orderOf x
    · have hx2 : orderOf (x ^ 2) = orderOf x / 2 := orderOf_pow_of_dvd (by norm_num) h2
      obtain ⟨a, b, hab⟩ := ih (orderOf x / 2) (by omega) (x ^ 2) (C.pow_mem hx 2) hx2
      refine ⟨a + 1, b, ?_⟩
      rw [← hab, ← pow_mul]
      congr 1
      ring
    · by_cases h3' : 3 ∣ orderOf x
      · have hx3 : orderOf (x ^ 3) = orderOf x / 3 := orderOf_pow_of_dvd (by norm_num) h3'
        obtain ⟨a, b, hab⟩ := ih (orderOf x / 3) (by omega) (x ^ 3) (C.pow_mem hx 3) hx3
        refine ⟨a, b + 1, ?_⟩
        rw [← hab, ← pow_mul]
        congr 1
        ring
      · refine ⟨0, 0, ?_⟩
        have hcop : Nat.Coprime (orderOf x) 6 := by
          have h6 : (6 : ℕ) = 2 * 3 := by norm_num
          rw [h6]
          exact Nat.Coprime.mul_right
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3').symm
        simp [hX1 x hx hcop]

theorem stmt5_1_22_one_of (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h520 : Stmt5_1_20) (h521 : Stmt5_1_21) : Stmt5_1_22_one :=
  stmt5_1_22_one_of_inputs h5114 hF h520 (stmt5_1_22_one_Y_of h5114 hF h510 h516 h520 h521)
    (stmt5_1_22_one_X_of h5114 hF h510 h516 h520 h521)

theorem stmt5_1_22_of (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) (h510 : Stmt5_1_10)
    (h516 : Stmt5_1_16) (h519 : Stmt5_1_19) (h520 : Stmt5_1_20) (h521 : Stmt5_1_21) :
    Stmt5_1_22 :=
  stmt5_1_22_of_inputs h5114 h510 h519 h520 h521
    (stmt5_1_22_one_of h5114 hF h510 h516 h520 h521) hF orthKernelFact l34BorelFact

end Setting

end CFSG.Quasithin.H13
