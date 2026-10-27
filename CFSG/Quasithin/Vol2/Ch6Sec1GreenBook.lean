module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise MatrixGroups

theorem card_sq_eq_one_quaternion :
    (Finset.univ.filter fun x : QuaternionGroup 2 => x ^ 2 = 1).card = 2 := by decide

theorem card_le_two_of_quaternion {A : Subgroup (QuaternionGroup 2)}
    (hA : ∀ x ∈ A, x ^ 2 = 1) : Nat.card A ≤ 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  refine le_of_le_of_eq ?_ card_sq_eq_one_quaternion
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective (fun x : A => (⟨(x : QuaternionGroup 2), by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hA x x.2⟩ : (Finset.univ.filter fun x : QuaternionGroup 2 => x ^ 2 = 1)))
  intro x y hxy
  apply Subtype.ext
  simpa using congrArg Subtype.val hxy

theorem false_of_isQ8D8_of_elemAbelian {P : Type} [Group P] (hP : IsQ8D8 P) {A : Subgroup P}
    (hA : ∀ x ∈ A, x ^ 2 = 1) (hcard : Nat.card A = 16) : False := by
  obtain ⟨h32, Q, -, -, ⟨eQ⟩, -⟩ := hP
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [h32]; norm_num)
  have hQ8 : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hAidx : A.index = 2 := by
    have := A.card_mul_index
    rw [hcard, h32] at this
    omega
  have h1 : (A ⊓ Q).relIndex Q ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    calc A.relIndex Q ≤ A.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right]; omega)
      _ = 2 := by rw [Subgroup.relIndex_top_right, hAidx]
  have h2 := card_mul_relIndex_of_le (inf_le_right : A ⊓ Q ≤ Q)
  rw [hQ8] at h2
  have h4 : 4 ≤ Nat.card ↥(A ⊓ Q) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(A ⊓ Q) * (A ⊓ Q).relIndex Q ≤ 3 * 2 :=
      Nat.mul_le_mul (by omega) h1
    omega
  set B : Subgroup (QuaternionGroup 2) := ((A ⊓ Q).subgroupOf Q).map eQ.toMonoidHom with hB
  have hBsq : ∀ x ∈ B, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : (y : P) ∈ A ⊓ Q := hy
    have hy2 : (y : P) ^ 2 = 1 := hA _ hy'.1
    have : y ^ 2 = 1 := Subtype.ext (by simpa using hy2)
    simp [← map_pow, this]
  have hcB : Nat.card B = Nat.card ↥(A ⊓ Q) := by
    rw [hB, Subgroup.card_map_of_injective eQ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have := card_le_two_of_quaternion hBsq
  omega

@[expose] def cycle012 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem orderOf_cycle012 : orderOf cycle012 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · decide
  · decide

theorem cycle012_pow_ne_one {k : ℕ} (hk : ¬ 3 ∣ k) : cycle012 ^ k ≠ 1 := by
  intro h
  exact hk (orderOf_cycle012 ▸ orderOf_dvd_of_pow_eq_one h)

theorem cycle012_pow_fix (k : ℕ) (i : Fin 5) :
    (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2)
        (((cycle012 ^ k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i) =
      (![0, 0, 0, 1, 1] : Fin 5 → ZMod 2) i := by
  rw [← pow_mod_orderOf, orderOf_cycle012]
  have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 3) <;> revert i <;> decide

theorem mem_evenWeight_sum {m : ℕ} {x : Fin m → ZMod 2} : x ∈ evenWeight m ↔ ∑ i, x i = 0 := by
  unfold evenWeight
  rw [AddMonoidHom.mem_ker]
  rfl

theorem card_evenWeight_five' : Nat.card (evenWeight 5) = 16 := by
  classical
  have : Nat.card (evenWeight 5) =
      (Finset.univ.filter fun x : Fin 5 → ZMod 2 => ∑ i, x i = 0).card := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun x => by simp [mem_evenWeight_sum]
  rw [this]
  decide

@[expose] def evenWeightVec : evenWeight 5 :=
  ⟨![0, 0, 0, 1, 1], by rw [mem_evenWeight_sum]; decide⟩

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp611Nat

theorem V_le_pCoreOf_L {n : ℕ} (h : Hyp611Nat G T M L V n) : V ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : V ≤ L := by
    have hVN : V ≤ Subgroup.normalizer (L : Set G) :=
      h.toHyp611.le_T.trans h.T_le_normalizer_L
    have h1 := Subgroup.le_normalizer_iff_commutator_le_left.mp hVN
    rw [← h.comm_eq, Subgroup.commutator_comm]
    exact h1
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL h.toHyp611.L_le_normalizer
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian)

theorem V_le_blockU {n : ℕ} (h : Hyp611Nat G T M L V n) : V ≤ blockU L := by
  rw [← h.comm_eq]
  exact Subgroup.commutator_mono h.V_le_pCoreOf_L le_rfl

theorem inf_centralizer_L_eq_bot {n : ℕ} (h : Hyp611Nat G T M L V n) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hN : L ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := by
    intro l hl
    refine Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.toHyp611.L_le_normalizer hl, ?_⟩
    exact F7.normalizer_le_normalizer_centralizer _ (Subgroup.le_normalizer hl)
  rcases h.natural.irreducible _ inf_le_left hN with h0 | h0
  · exact h0
  · exfalso
    have hVC : V ≤ Subgroup.centralizer (L : Set G) := by
      rw [← h0]
      exact inf_le_right
    have h1 : ⁅V, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVC
    rw [h.comm_eq] at h1
    exact h.toHyp611.ne_bot h1

theorem false_of_isAltType (h : Hyp611Nat G T M L V 2) (hA : IsAltType L 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hαs, -, β, -, hβk, hβe⟩ := hA
  have hVU := h.V_le_blockU
  have hVZ : ∀ v ∈ V, v ∈ blockZ L → v = 1 := by
    intro v hv hvZ
    have : v ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hv, hvZ.2⟩
    rw [h.inf_centralizer_L_eq_bot] at this
    exact this
  let f : ↥V → Multiplicative (evenWeight 5) := fun v => β ⟨v, hVU v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h1 : β (⟨v, hVU v.2⟩ * (⟨w, hVU w.2⟩ : blockU L)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr hvw
    have h2 : (((⟨v, hVU v.2⟩ * (⟨w, hVU w.2⟩ : blockU L)⁻¹ : blockU L)) : G) ∈ blockZ L := by
      have := MonoidHom.mem_ker.mpr h1
      rw [hβk, Subgroup.mem_subgroupOf] at this
      exact this
    have h3 := hVZ _ (V.mul_mem v.2 (V.inv_mem w.2)) h2
    apply Subtype.ext
    exact mul_inv_eq_one.mp h3
  have hcardV : Nat.card V = 16 := by
    rw [h.natural.card_eq]
    norm_num
  have hcardD : Nat.card (Multiplicative (evenWeight 5)) = 16 := by
    rw [← card_evenWeight_five']
    exact Nat.card_congr Multiplicative.toAdd
  have hfb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hcardV, hcardD])
  obtain ⟨v, hv⟩ := hfb.2 (Multiplicative.ofAdd evenWeightVec)
  obtain ⟨ℓ₀, hℓ₀⟩ := hαs cycle012
  obtain ⟨k, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ℓ₀).ne' 2 (by norm_num)
  set ℓ := ℓ₀ ^ 2 ^ k with hℓ
  have hαℓ : α ℓ = cycle012 ^ 2 ^ k := by rw [hℓ, map_pow, hℓ₀]
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  have hℓord : orderOf ℓ = m := by
    rw [hℓ, orderOf_pow_of_dvd (by positivity : 0 < 2 ^ k).ne' ⟨m, hord⟩, hord,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hℓodd : Odd (orderOf ℓ) := by
    rw [hℓord]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
  have hαℓ1 : α ℓ ≠ 1 := by
    rw [hαℓ]
    refine cycle012_pow_ne_one fun h3 => ?_
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hvmem : (ℓ : G) * v * (ℓ : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.toHyp611.L_le_normalizer ℓ.2) v).mp v.2
  have hfix : f ⟨_, hvmem⟩ = f v := by
    have he := hβe ℓ ⟨v, hVU v.2⟩ ⟨(ℓ : G) * v * (ℓ : G)⁻¹, hVU hvmem⟩ rfl
    have hv' : Multiplicative.toAdd (β ⟨v, hVU v.2⟩) = evenWeightVec := by
      have := congrArg Multiplicative.toAdd hv
      exact this
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    show ((Multiplicative.toAdd (β ⟨_, hVU hvmem⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β ⟨v, hVU v.2⟩) : evenWeight 5) : Fin 5 → ZMod 2) i
    rw [he i, hv', hαℓ]
    exact cycle012_pow_fix (2 ^ k) i
  have hcomm : (ℓ : G) * v * (ℓ : G)⁻¹ = v := congrArg Subtype.val (hf hfix)
  have hv1 : v ≠ 1 := by
    intro h1
    have h2 : f v = 1 := by
      show β ⟨v, hVU v.2⟩ = 1
      have : (⟨v, hVU v.2⟩ : blockU L) = 1 := Subtype.ext (by rw [h1]; rfl)
      rw [this, map_one]
    rw [hv] at h2
    have h3 := congrArg (fun x => ((Multiplicative.toAdd x : evenWeight 5) : Fin 5 → ZMod 2) 3)
      h2
    simp [evenWeightVec] at h3
  set D := h.data with hD
  have hvC : (v : G) ∈ Subgroup.centralizer ((Subgroup.zpowers (ℓ : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (ℓ : G) v := by
      show (ℓ : G) * v = v * ℓ
      calc (ℓ : G) * v = (ℓ : G) * v * (ℓ : G)⁻¹ * ℓ := by group
        _ = v * ℓ := by rw [hcomm]
    exact (hc.zpow_left j).eq
  have hρfix := (D.fixed_iff (Subgroup.zpowers_le.mpr ℓ.2) v).mp hvC ℓ (Subgroup.mem_zpowers _)
  have : CharP D.K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num : 1 ≤ 2) D.card
  have hρ1 : D.rho ℓ ≠ 1 := by
    intro hρ
    have hℓC : (ℓ : G) ∈ Subgroup.centralizer (V : Set G) :=
      (D.mem_ker_rho_iff ℓ).mp (MonoidHom.mem_ker.mpr hρ)
    have hℓO : (ℓ : G) ∈ pCoreOf 2 (L ⊔ T) := by
      rw [← h.toHyp5_0_1.sup_inf_centralizer_eq h.module]
      exact ⟨Subgroup.mem_sup_left ℓ.2, hℓC⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))) ⟨ℓ, hℓO⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hj
    rw [hj] at hℓodd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hℓodd) ((Nat.even_pow' hj0).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact hαℓ1 (by rw [hj, map_one])
  have hρodd : Odd (orderOf (D.rho ℓ)) := Odd.of_dvd_nat hℓodd (orderOf_map_dvd _ _)
  have hdet := det_sub_one_ne_zero_of_odd (D.rho ℓ) hρ1 hρodd
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Multiplicative.toAdd (D.E v), ?_, ?_⟩
  · intro h0
    apply hv1
    have : D.E v = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl
    rw [← map_one D.E] at this
    exact D.E.injective this
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hρfix, sub_self]

theorem false_of_isQ8D8_of_le (h : Hyp611Nat G T M L V 2) {P : Subgroup G} (hVP : V ≤ P)
    (hQ : IsQ8D8 ↥P) : False := by
  refine false_of_isQ8D8_of_elemAbelian hQ (A := V.subgroupOf P) ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    apply Subtype.ext
    simpa using h.toHyp611.isElemAbelian.2 _ hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv, h.natural.card_eq]
    norm_num

theorem isL2Quot_L (h : Hyp611Nat G T M L V 2) : IsL2Quot 2 (oTwoQuot ↥L) := by
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* oTwoQuot ↥L :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)
  obtain ⟨e'⟩ := isL2Quot_of_lieModel (by norm_num) h.lie
  exact ⟨e.symm.trans e'⟩

theorem card_oTwoQuot_L (h : Hyp611Nat G T M L V 2) : Nat.card (oTwoQuot ↥L) = 60 := by
  rw [h.isL2Quot_L.card (by norm_num)]
  norm_num

theorem not_isSolvable_L (h : Hyp611Nat G T M L V 2) : ¬ Group.IsSolvable ↥L := by
  intro hsolv
  set D := h.data
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) D.K) :=
    Group.isSolvable_of_surjective D.rho_surjective
  have hcard : Nat.card D.K = 4 := by rw [D.card]; norm_num
  have : CharP D.K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num : 1 ≤ 2) D.card
  rcases CFSG.Quasithin.SL2Model.card_two_or_exists_sq_ne_one (F := D.K) with h2 | ⟨c, hc0, hc1⟩
  · omega
  · have hperf := Matrix.SL2.commutator_eq_top hc0 hc1
    have hdet : (!![(1 : D.K), 1; 0, 1] : Matrix (Fin 2) (Fin 2) D.K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      simp
    have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) D.K) :=
      ⟨⟨⟨!![1, 1; 0, 1], hdet⟩, 1, fun h1 => by
        have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) D.K =>
          (A : Matrix (Fin 2) (Fin 2) D.K) 0 1) h1
        simp at this⟩⟩
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (Matrix.SpecialLinearGroup (Fin 2) D.K)).ne hperf

end Hyp611Nat

omit [Finite G] in
theorem card_oTwoQuot_of_s3 {P₁ : Subgroup G}
    (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))) : Nat.card (oTwoQuot ↥P₁) = 6 := by
  obtain ⟨e⟩ := hS3
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem borelOf_eq_of_s3 {P₁ S : Subgroup G} (hsyl : IsSylowTwoOf (S ⊓ P₁) P₁)
    (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))) : borelOf P₁ S = S ⊓ P₁ := by
  have hcard : Nat.card (OTwoQuot P₁) = 2 ^ 1 * 3 := card_oTwoQuot_of_s3 hS3
  unfold borelOf
  exact inf_normalizer_eq_of_card_quot hsyl le_rfl Nat.prime_three (by decide) hcard

theorem isQuasithinSub_of_qtke' (hK : quasithinIsQTKECat G) (X : Subgroup G) :
    IsQuasithinSub X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro p hp hp2 R hRX hR1 hR2
  refine pRank_le_two_of_pCoreOf_ne_bot hK ?_ hp hp2
  intro h0
  apply hR1
  rw [eq_bot_iff, ← h0]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hRX Subgroup.le_normalizer)
    inf_le_right hR2

namespace Hyp611Nat

theorem borelL_le_normalizer_ZS {n : ℕ} (h : Hyp611Nat G T M L V n) :
    borelL T L ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  intro x hx
  apply mem_normalizer_of_conjSub_le'
  apply le_of_eq
  show conjSub x (V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) =
    V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)
  rw [conjSub_inf, conjSub_centralizer', conjSub_eq_of_mem_normalizer'
    (h.toHyp611.L_le_normalizer hx.1), conjSub_eq_of_mem_normalizer' hx.2]

theorem hyp111_of_s3_parabolic (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V 2)
    {D P₁ : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hP₁ZS : P₁ ≤ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hTP : T ≤ Subgroup.normalizer (P₁ : Set G)) (hDP : D ≤ Subgroup.normalizer (P₁ : Set G))
    (hP₁M : ¬ P₁ ≤ M) (hsyl : IsSylowTwoOf (T ⊓ P₁) P₁)
    (hS3 : Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3))) : Hyp111 L P₁ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hEven := h.qtke.2.1
  have hbP : borelOf P₁ T = T ⊓ P₁ := borelOf_eq_of_s3 hsyl hS3
  have hbL : borelOf L T = D ⊔ (T ⊓ L) := (h.toHyp5_0_1.borelL_eq_sup hD).symm
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le_normalizer_L
  have hLTc : CharTwo (L ⊔ T) := by
    refine charTwo_of_inH hEven P ⟨hP ▸ le_sup_right, fun h0 => ?_⟩
    apply h.toHyp611.ne_bot
    rw [eq_bot_iff, ← h0]
    exact h.toHyp611.le_pCoreOf
  have hXZ : P₁ ⊔ T ⊔ borelOf L T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    sup_le (sup_le hP₁ZS h.T_le_normalizer_ZS) h.borelL_le_normalizer_ZS
  have hZT : ch6ZS T L V ≤ T := (inf_le_left : ch6ZS T L V ≤ V).trans h.toHyp611.le_T
  have hXc : CharTwo (P₁ ⊔ T ⊔ borelOf L T) := by
    refine charTwo_of_inH hEven P ⟨hP ▸ (le_sup_right.trans le_sup_left), fun h0 => ?_⟩
    have hZ : ch6ZS T L V ≤ pCoreOf 2 (P₁ ⊔ T ⊔ borelOf L T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hZT.trans (le_sup_right.trans le_sup_left)) hXZ
        (B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono inf_le_left
          h.toHyp611.isElemAbelian))
    rw [h0] at hZ
    exact h.ZS_ne_bot (le_bot_iff.mp hZ)
  refine ⟨⟨inferInstance, h.sylow.1, hTL, h.toHyp611.isSylowIn_TL,
      Or.inl ⟨2, by norm_num, h.isL2Quot_L⟩, ?_, ?_⟩,
    ⟨inferInstance, h.sylow.1, hTP, hsyl, ?_, ?_, hXc⟩, ?_⟩
  · rw [hbP]
    exact inf_le_left.trans hTL
  · rw [hbP, sup_of_le_left ((inf_le_left : T ⊓ P₁ ≤ T).trans le_sup_right)]
    exact hLTc
  · obtain ⟨e⟩ := hS3
    exact isRankOneListed_perm_three e
  · rw [hbL]
    exact sup_le hDP (inf_le_left.trans hTP)
  ·
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ P₁ ⊔ T) : Set G)) :=
      ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
    have hG0 : L ⊔ P₁ ⊔ T ≤ K :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hle
    have hKM : K = M := (h.toHyp611.isUniqueM h432).2 K
      ⟨hK, sup_le (le_sup_left.trans (le_sup_left.trans hG0)) (le_sup_right.trans hG0)⟩
    exact hP₁M (hKM ▸ (le_sup_right.trans (le_sup_left.trans hG0)))

end Hyp611Nat

end CFSG.Quasithin.H13
