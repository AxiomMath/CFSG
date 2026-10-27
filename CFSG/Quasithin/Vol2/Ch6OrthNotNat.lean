module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Vol2.Ch6OrthIrred
public import CFSG.Quasithin.Vol2.Ch6Remark612

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative commutatorElement Matrix
open CFSG.Quasithin.JonesParshall

variable {G : Type} [Group G]

theorem IsOrthCh5.exists_not_conj_ch6 {L V : Subgroup G} {n : ℕ} (h : IsOrthCh5 L V n) :
    ∃ v₁ v₂ : ↥V, v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ ∀ ℓ ∈ L, ℓ * (v₁ : G) * ℓ⁻¹ ≠ v₂ := by
  obtain ⟨m, rfl, hLV, _, _⟩ := id h
  obtain ⟨F, _, _, _, hF, eρ, E, hE⟩ := h.exists_equiv
  have hE11 : Multiplicative.ofAdd (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) ∈
      hermSub m (Fin 2) F := by
    show (frobPow m !![(1 : F), 0; 0, 0])ᵀ = !![1, 0; 0, 0]
    have h0 : (0 : F) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow, h0]
  have h1H : Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F) ∈ hermSub m (Fin 2) F := by
    show (frobPow m (1 : Matrix (Fin 2) (Fin 2) F))ᵀ = 1
    have h0 : (0 : F) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow, h0]
  set v₁ := E.symm ⟨_, hE11⟩ with hv₁
  set v₂ := E.symm ⟨_, h1H⟩ with hv₂
  have hEv₁ : ((E v₁ : ↥(hermSub m (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
      Multiplicative.ofAdd !![1, 0; 0, 0] := by rw [hv₁, MulEquiv.apply_symm_apply]
  have hEv₂ : ((E v₂ : ↥(hermSub m (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
      Multiplicative.ofAdd 1 := by rw [hv₂, MulEquiv.apply_symm_apply]
  refine ⟨v₁, v₂, ?_, ?_, fun ℓ hℓ heq => ?_⟩
  · intro h0
    have := congrArg (fun w => Multiplicative.toAdd
      ((E w : ↥(hermSub m (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 0 0) h0
    simp only [hEv₁, map_one] at this
    exact one_ne_zero this
  · intro h0
    have := congrArg (fun w => Multiplicative.toAdd
      ((E w : ↥(hermSub m (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 0 0) h0
    simp only [hEv₂, map_one] at this
    exact one_ne_zero this
  ·
    have hmem : conjAct V ⟨ℓ, hLV hℓ⟩ ∈ autOn L V := mem_autOn_iff.mpr ⟨⟨ℓ, hLV hℓ⟩, hℓ, rfl⟩
    set γ := eρ.symm ⟨_, hmem⟩ with hγ
    have hγ' : ((eρ γ : ↥(autOn L V)) : MulAut ↥V) = conjAct V ⟨ℓ, hLV hℓ⟩ := by
      rw [hγ, MulEquiv.apply_symm_apply]
    have hconj : ((eρ γ : ↥(autOn L V)) : MulAut ↥V) v₁ = v₂ := by
      rw [hγ']
      apply Subtype.ext
      rw [conjAct_apply_coe]
      exact heq
    have h1 := hE γ v₁
    rw [hconj, hEv₂, hEv₁] at h1
    have h2 := congrArg (fun X => (Multiplicative.toAdd X).det) h1
    simp only [toAdd_ofAdd] at h2
    have h3 : ((γ : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, 0] *
        (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ).det = 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      simp [Matrix.det_fin_two]
    rw [h3, Matrix.det_one] at h2
    exact one_ne_zero h2

theorem IsNatQuotCh5.exists_conj_mul_mem_ch6 {L N : Subgroup G} {n : ℕ} (h : IsNatQuotCh5 L N n)
    {x y : G} (hx : x ∈ N) (hy : y ∈ N) (hxC : x ∉ Subgroup.centralizer (L : Set G))
    (hyC : y ∉ Subgroup.centralizer (L : Set G)) :
    ∃ ℓ ∈ L, (ℓ * x * ℓ⁻¹) * y⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := h.1
  obtain ⟨K, _, _, -, π, Y, hπs, -, hYk, hYe⟩ := h.exists_coord
  have hYx : Multiplicative.toAdd (Y ⟨x, hx⟩) ≠ 0 := fun h0 => hxC ((hYk _).mp h0)
  have hYy : Multiplicative.toAdd (Y ⟨y, hy⟩) ≠ 0 := fun h0 => hyC ((hYk _).mp h0)
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq _ _ hYx hYy
  obtain ⟨ℓN, hℓL, hℓ⟩ := mem_autOn_iff.mp (π (slToStated A)).2
  refine ⟨ℓN, hℓL, ?_⟩
  have hw : (ℓN : G) * x * (ℓN : G)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp ℓN.2 x).mp hx
  have h1 := hYe (slToStated A) ⟨x, hx⟩
  rw [slToStated_coe, hA] at h1
  have h2 : ((π (slToStated A) : ↥(autOn L N)) : MulAut ↥N) ⟨x, hx⟩ =
      ⟨(ℓN : G) * x * (ℓN : G)⁻¹, hw⟩ := by
    rw [← hℓ]
    apply Subtype.ext
    rw [conjAct_apply_coe]
  rw [h2] at h1
  have h3 : Y (⟨(ℓN : G) * x * (ℓN : G)⁻¹, hw⟩ * ⟨y, hy⟩⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, h1, toAdd_one, add_neg_cancel]
  exact (hYk _).mp h3

theorem IsOrthCh5.false_of_isNatQuot_ch6 {L V N : Subgroup G} {n k : ℕ} (h : IsOrthCh5 L V n)
    (hVN : V ≤ N) (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hN : IsNatQuotCh5 L N k) :
    False := by
  obtain ⟨v₁, v₂, hv₁, hv₂, hnc⟩ := h.exists_not_conj_ch6
  have hLV := h.le_normalizer
  have hnotC : ∀ v : ↥V, v ≠ 1 → (v : G) ∉ Subgroup.centralizer (L : Set G) :=
    fun v hv hvC => hv (Subtype.ext (by
      have hmem : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hvC⟩
      rw [hC] at hmem
      exact hmem))
  obtain ⟨ℓ, hℓL, hmem⟩ := hN.exists_conj_mul_mem_ch6 (hVN v₁.2) (hVN v₂.2) (hnotC v₁ hv₁)
    (hnotC v₂ hv₂)
  apply hnc ℓ hℓL
  have hV' : ℓ * (v₁ : G) * ℓ⁻¹ * (v₂ : G)⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hℓL) _).mp v₁.2) (V.inv_mem v₂.2)
  have hboth : ℓ * (v₁ : G) * ℓ⁻¹ * (v₂ : G)⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hV', hmem⟩
  rw [hC, Subgroup.mem_bot] at hboth
  exact mul_inv_eq_one.mp hboth

theorem IsOrthCh5.false_of_sumTwo_ch6 [Finite G] {L V W : Subgroup G} {n k : ℕ}
    (h : IsOrthCh5 L V n) (hn : 2 ≤ n) (hVW : V ≤ W)
    (hW : IsSumOfTwo L W (fun X => IsNatModCh5 L X k))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : False := by
  obtain ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, h₁, h₂⟩ := hW
  obtain ⟨v₁, v₂, hv₁, hv₂, hnc⟩ := h.exists_not_conj_ch6
  have hLV := h.le_normalizer
  have hW₁W : W₁ ≤ W := hsup ▸ le_sup_left
  have hW₂W : W₂ ≤ W := hsup ▸ le_sup_right
  have hLV1 : L ≤ Subgroup.normalizer ((V ⊓ W₁ : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLV hl, hL₁ hl⟩
  rcases h.irreducible_ch6 hn (V ⊓ W₁) inf_le_left hLV1 with h0 | h0
  ·
    have hW₁N : W₁ ≤ Subgroup.normalizer (W₂ : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        rw [hWab a (hW₁W ha) b (hW₂W hb), mul_inv_cancel_right]
        exact hb
      · intro hb
        have hb' : b = a⁻¹ * (a * b * a⁻¹) * a := by group
        have hc : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ :=
          hWab _ (W.inv_mem (hW₁W ha)) _ (hW₂W hb)
        rw [hb', hc, inv_mul_cancel_right]
        exact hb
    have hdec : ∀ v : ↥V, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = (v : G) := by
      intro v
      have hvW : (v : G) ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by rw [hsup]; exact hVW v.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂ hW₁N] at hvW
      obtain ⟨a, ha, b, hb, hab⟩ := hvW
      exact ⟨a, ha, b, hb, hab⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec v₁
    obtain ⟨a₂, ha₂, b₂, hb₂, hab₂⟩ := hdec v₂
    have hb_ne : ∀ (v : ↥V) (a b : G), a ∈ W₁ → b ∈ W₂ → a * b = (v : G) → v ≠ 1 → b ≠ 1 := by
      intro v a b ha hb hab hv h1
      apply hv
      rw [h1, mul_one] at hab
      apply Subtype.ext
      have hmem : (v : G) ∈ V ⊓ W₁ := ⟨v.2, hab ▸ ha⟩
      rw [h0, Subgroup.mem_bot] at hmem
      exact hmem
    obtain ⟨ℓ, hℓL, hℓb⟩ := h₂.exists_conj_eq hb₁ hb₂ (hb_ne v₁ a₁ b₁ ha₁ hb₁ hab₁ hv₁)
      (hb_ne v₂ a₂ b₂ ha₂ hb₂ hab₂ hv₂)
    apply hnc ℓ hℓL
    set x := ℓ * (v₁ : G) * ℓ⁻¹ * (v₂ : G)⁻¹ with hx
    have hxV : x ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hℓL) _).mp v₁.2) (V.inv_mem v₂.2)
    have hℓa : ℓ * a₁ * ℓ⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hℓL) a₁).mp ha₁
    have hxW₁ : x = (ℓ * a₁ * ℓ⁻¹) * a₂⁻¹ := by
      have e1 : ℓ * (v₁ : G) * ℓ⁻¹ = (ℓ * a₁ * ℓ⁻¹) * b₂ := by
        rw [← hab₁, ← hℓb]
        group
      rw [hx, e1, ← hab₂, mul_inv_rev]
      have hc : b₂ * b₂⁻¹ = 1 := mul_inv_cancel b₂
      have hcomm : b₂ * a₂⁻¹ = a₂⁻¹ * b₂ :=
        hWab _ (hW₂W hb₂) _ (W.inv_mem (hW₁W ha₂))
      calc ℓ * a₁ * ℓ⁻¹ * b₂ * (b₂⁻¹ * a₂⁻¹) = ℓ * a₁ * ℓ⁻¹ * (b₂ * b₂⁻¹) * a₂⁻¹ := by group
        _ = ℓ * a₁ * ℓ⁻¹ * a₂⁻¹ := by rw [hc, mul_one]
    have hmem : x ∈ V ⊓ W₁ := ⟨hxV, hxW₁ ▸ W₁.mul_mem hℓa (W₁.inv_mem ha₂)⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  ·
    have hVW₁ : V ≤ W₁ := (le_of_eq h0.symm).trans inf_le_right
    rcases h₁.irreducible V hVW₁ hLV with h1 | h1
    · have hmem : (v₁ : G) ∈ (⊥ : Subgroup G) := h1 ▸ v₁.2
      exact hv₁ (Subtype.ext (Subgroup.mem_bot.mp hmem))
    · subst h1
      obtain ⟨ℓ, hℓL, hℓ⟩ := h₁.exists_conj_eq v₁.2 v₂.2 (fun h' => hv₁ (Subtype.ext h'))
        (fun h' => hv₂ (Subtype.ext h'))
      exact hnc ℓ hℓL hℓ

variable [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem commutator_eq_and_inf_of_orth_ch6 (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n)
    (hn : 2 ≤ n) : ⁅V, L⁆ = V ∧ V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hLV := h.L_le_normalizer
  have hVL : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv))
  have hLc : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hLV Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  · rcases horth.irreducible_ch6 hn ⁅V, L⁆ hVL hLc with h0 | h0
    · exact absurd h0 h.module.2.2
    · exact h0
  · have hLC : L ≤ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hLV hl, F7.normalizer_le_normalizer_centralizer _ (Subgroup.le_normalizer hl)⟩
    rcases horth.irreducible_ch6 hn (V ⊓ Subgroup.centralizer (L : Set G)) inf_le_left hLC with
      h0 | h0
    · exact h0
    · exfalso
      apply h.module.2.2
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv l hl
      have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
        have hv' : v ∈ V ⊓ Subgroup.centralizer (L : Set G) := by rw [h0]; exact hv
        exact hv'.2
      rw [Subgroup.mem_bot, commutatorElement_def,
        (Subgroup.mem_centralizer_iff.mp hvC l hl).symm]
      group

theorem omegaOne_le_of_orth_ch6 (h512 : Stmt5_1_2) (h513 : Stmt5_1_3) (h : Hyp611 G T M L V n)
    (horth : IsOrthCh5 L V n) (hn : 2 < n) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set R := omegaOneCenterOf Q with hRdef
  have hQ : ch6Q T V = Q := h.centralizer_eq
  have hRZ : R ≤ centerOf Q := A4.omegaOneCenterOf_le_centerOf Q
  have hQLT : Q ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hRN : L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf X)
        (fun φ X => omegaOneCenterOf_map_mulEquiv φ X) _)
  have hRe : IsElemAbelian 2 R := B2F.isElemAbelian_omegaOneCenterOf Q
  have hVR : V ≤ R := by
    intro v hv
    have hvC : v ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [← hQ] at hq
      exact (Subgroup.mem_centralizer_iff.mp hq.2 v hv).symm
    exact Subgroup.subset_closure ⟨⟨h.le_pCoreOf hv, hvC⟩, h.isElemAbelian.2 v hv⟩
  have hRred : IsTwoReducedIn (L ⊔ T) R := by
    refine ⟨hRZ.trans (inf_le_left.trans hQLT), hRN, hRe, fun D hDH hHD hD => ?_⟩
    have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
      h.toHyp5_0_1.sup_inf_centralizer_le_pCoreOf h.sup_le_normalizer h.module.2.2
    have hD2 : IsPGroup 2 D := by
      intro d
      obtain ⟨k, hk⟩ := hD d d.2
      have hkV : (d : G) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.centralizer_le hVR hk
      have hkQ : (d : G) ^ 2 ^ k ∈ Q := hCV ⟨(L ⊔ T).pow_mem (hDH d.2) _, hkV⟩
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hkQ⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_add, pow_mul]
      exact hj'
    have hDQ : D ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDH hHD hD2
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRZ hr).2 d (hDQ hd)).symm
  have hRL : ⁅R, L⁆ ≠ ⊥ := fun h0 => h.module.2.2 (by
    rw [eq_bot_iff, ← h0]
    exact Subgroup.commutator_mono hVR le_rfl)
  have hRmod : IsCh5Module T L R :=
    ⟨hRred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hRred).2, hRL⟩
  have hR611 : Hyp611 G T M L R n :=
    { toHyp5_0_1 := h.toHyp5_0_1
      module := hRmod
      not_a5 := fun hc => absurd hc.1 (by omega)
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }
  obtain ⟨hVLc, hVC⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth (by omega)
  rcases ((stmt6_1_2 h512 h513) G T M L R n hR611).1 with hsum | hnat | ⟨-, hRorth⟩
  · exact (horth.false_of_sumTwo_ch6 (by omega) hVR hsum
      (fun a ha b hb => B2F.isElemAbelian_comm hRe ha hb)).elim
  · have hVRc : V ≤ ⁅R, L⁆ := hVLc ▸ Subgroup.commutator_mono hVR le_rfl
    exact (horth.false_of_isNatQuot_ch6 hVRc hVC hnat).elim
  · rcases hRorth.irreducible_ch6 (by omega) V hVR h.L_le_normalizer with h0 | h0
    · exact absurd h0 h.ne_bot
    · exact h0 ▸ le_rfl

end Hyp611

end CFSG.Quasithin.H13
