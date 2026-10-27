module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.Quasithin.H13.A5S1327f

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped MatrixGroups IsMulCommutative

theorem SL2_eq_one_of_fix_of_odd {F : Type*} [Field F] [CharP F 2] (γ : SL(2, F))
    (hodd : Odd (orderOf γ)) {x : Fin 2 → F} (hx : x ≠ 0)
    (hγx : (γ : Matrix (Fin 2) (Fin 2) F).mulVec x = x) : γ = 1 := by
  have h2F : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h1 : ((γ : Matrix (Fin 2) (Fin 2) F) - 1).mulVec x = 0 := by
    rw [Matrix.sub_mulVec, hγx, Matrix.one_mulVec, sub_self]
  have h2 : ((γ : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, h1⟩
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det = 1 := γ.2
  rw [Matrix.det_fin_two] at h2 hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply, Fin.isValue] at h2
  simp only [show ((0 : Fin 2) = 1) = False by decide, show ((1 : Fin 2) = 0) = False by decide,
    ite_false, sub_zero] at h2
  set a := (γ : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (γ : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (γ : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (γ : Matrix (Fin 2) (Fin 2) F) 1 1
  have hs : a + d = 0 := by linear_combination hdet - h2 + h2F
  have e00 : a * a + b * c = 1 := by linear_combination a * hs - hdet - h2F
  have e01 : a * b + b * d = 0 := by linear_combination b * hs
  have e10 : c * a + d * c = 0 := by linear_combination c * hs
  have e11 : c * b + d * d = 1 := by linear_combination d * hs - hdet - h2F
  have hsq : γ ^ 2 = 1 := by
    ext i j
    rw [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
        Fin.zero_eta, Fin.mk_one]
    · simp only [ite_true]; exact e00
    · simp only [show ((0 : Fin 2) = 1) = False by decide, ite_false]; exact e01
    · simp only [show ((1 : Fin 2) = 0) = False by decide, ite_false]; exact e10
    · simp only [ite_true]; exact e11
  have hcop : Nat.Coprime (orderOf γ) 2 := Nat.coprime_two_right.mpr hodd
  exact eq_one_of_pow_coprime hsq (pow_orderOf_eq_one γ) hcop.symm

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem L1_le_centralizer_Z (h512 : Stmt5_1_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    S.L1 ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  have hJV := S.thompsonJ_not_le_centralizer h5172 hH hHZ
  have hLTH : InH T (L ⊔ T) := ⟨le_sup_right, S.maximal.1.2.2.2⟩
  have hF : CharTwo (L ⊔ T) := S.charTwo_of_inH hLTH
  obtain ⟨-, hWel, hWred⟩ : conjClosure Z (L ⊔ T) ≤ pCoreOf 2 (L ⊔ T) ⊓
      Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧ IsElemAbelian 2 (conjClosure Z (L ⊔ T)) ∧
      IsTwoReducedIn (L ⊔ T) (conjClosure Z (L ⊔ T)) :=
    conjClosure_isTwoReducedIn_of_charTwo S.sylow_LT hF le_rfl
  set W := conjClosure Z (L ⊔ T) with hWdef
  have hzZ : S.z ∈ Z := S.z_mem_omegaOneCenter
  have hVW : V ≤ W := by
    rw [← S.conjClosure_V1_L]
    refine conjClosure_le fun l hl v hv => ?_
    have hvZ : v ∈ Z := by
      rcases S.mem_V1.1 hv with rfl | rfl
      · exact Z.one_mem
      · exact hzZ
    exact Subgroup.subset_closure ⟨l, Subgroup.mem_sup_left hl, v, hvZ, rfl⟩
  have hWL : ⁅W, L⁆ ≠ ⊥ := fun h => S.isCh5Module.2.2
    (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hVW le_rfl))
  have hW5 : IsCh5Module T L W :=
    ⟨hWred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hWred).2, hWL⟩
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    le_sup_left.trans (le_normalizer_conjClosure Z (L ⊔ T))
  rcases h512 G T _ L W 2 S.hyp501 hW5 with h1 | ⟨-, h2⟩ | ⟨-, -, h3, -, h3'⟩
  ·
    exact absurd ((h1.1.trans inf_le_right).trans (Subgroup.centralizer_le hVW)) hJV
  ·
    exfalso
    have hTLsyl : IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal S.sylow_LT le_sup_left (sup_le Subgroup.le_normalizer S.T_le_NL)
    obtain ⟨F, _, _, _, -, ψ', Y, -, hYk, hYe, -⟩ := h2.exists_sylowCoord hTLsyl
    obtain ⟨g, hgL₁, hg⟩ := S.exists_L1_c3p
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hlL : ((g : G) ^ 2 ^ k) ∈ L := L.pow_mem (S.L1_le_L hgL₁) _
    have hodd : Odd (orderOf ((g : G) ^ 2 ^ k)) := by
      have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
      rw [orderOf_pow' _ h2k, Subgroup.orderOf_coe, hkm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    have hρl : S.frame.ρ (g ^ 2 ^ k) = c3p ^ 2 ^ k := by rw [map_pow, hg]
    have hρl1 : S.frame.ρ (g ^ 2 ^ k) ≠ 1 := by
      rw [hρl]
      intro h
      have h3 : orderOf c3p = 3 := orderOf_eq_prime c3p_cube (by decide)
      have hdvd : orderOf c3p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
      rw [h3] at hdvd
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
    have hlz : ((g : G) ^ 2 ^ k) * S.z * ((g : G) ^ 2 ^ k)⁻¹ = S.z := by
      have := (S.conj_eq_iff (g ^ 2 ^ k) ⟨S.z, S.z_mem_V⟩).2 (by
        rw [S.psi_z, hρl]
        refine pact_W4 ?_
        have : ∀ n : ℕ, (c3p ^ n) 4 = 4 := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, c3p_four, ih]
        exact this _)
      simpa using this
    set l : ↥L := ⟨(g : G) ^ 2 ^ k, hlL⟩ with hldef
    set γ := ψ' (autHom hLW l) with hγ
    have hγodd : Odd (orderOf γ) := by
      refine Odd.of_dvd_nat hodd ?_
      rw [hγ, MulEquiv.orderOf_eq]
      refine (orderOf_map_dvd _ _).trans ?_
      rw [hldef, Subgroup.orderOf_mk]
    set w₀ : ↥W := ⟨S.z, hVW S.z_mem_V⟩ with hw₀
    have hfix : ((autHom hLW l : ↥(autOn L W)) : MulAut ↥W) w₀ = w₀ := by
      apply Subtype.ext
      rw [autHom_apply_coe]
      exact hlz
    have hY := hYe (autHom hLW l) w₀
    rw [hfix] at hY
    by_cases hY0 : Multiplicative.toAdd (Y w₀) = 0
    · have h1 : Y w₀ = 1 := by
        rw [← ofAdd_toAdd (Y w₀), hY0, ofAdd_zero]
      have hzC := (hYk w₀).1 h1
      have hzb : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, hzC⟩
      rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzb
      exact S.z_ne_one hzb
    · have hγ1 : γ = 1 := SL2_eq_one_of_fix_of_odd γ hγodd hY0 hY.symm
      have hl1 : autHom hLW l = 1 := by
        rw [hγ] at hγ1
        exact (map_eq_one_iff ψ' ψ'.injective).mp hγ1
      have hlC := Subgroup.centralizer_le hVW (mem_centralizer_of_autHom_eq_one hLW hl1)
      exact hρl1 (S.frame.rho_eq_one_of_mem _ hlC)
  ·
    obtain ⟨hinf, hsup⟩ := h3
    have hcard : Nat.card ↥⁅W, L⁆ = 16 := by
      obtain ⟨-, hc, π, hπ⟩ := h3'
      have h1 := FFC.card_eq_of_realizes FFC.symDn_ker_five hπ
      rw [Subgroup.card_top, Subgroup.card_bot, one_mul] at h1
      rw [h1]
      exact FFC.card_coreMod_five
    have hWLV : ⁅W, L⁆ = V := by
      have hVle : V ≤ ⁅W, L⁆ := by
        calc V = ⁅V, L⁆ := S.irr.2.2.2.1.symm
          _ ≤ ⁅W, L⁆ := Subgroup.commutator_mono hVW le_rfl
      exact (Subgroup.eq_of_le_of_card_ge hVle (by rw [hcard, S.card_V])).symm
    rw [hWLV] at hinf hsup
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    have hz'W : z' ∈ W := le_conjClosure Z (L ⊔ T) hz'
    have hVC : V ≤ Subgroup.normalizer
        ((W ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      intro v hv
      refine Subgroup.centralizer_le_normalizer (s := ((W ⊓ Subgroup.centralizer
        ((L ⊔ T : Subgroup G) : Set G) : Subgroup G) : Set G))
        (Subgroup.mem_centralizer_iff.mpr fun c hc => ?_)
      exact B2F.isElemAbelian_comm hWel hc.1 (hVW hv)
    have hz'' : z' ∈ ((V ⊔ (W ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)) :
        Subgroup G) : Set G) := by rw [hsup]; exact hz'W
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVC] at hz''
    obtain ⟨v, hv, c, hc, hvc⟩ := hz''
    have hvc' : v * c = z' := hvc
    rw [← hvc'] at hz' ⊢
    have hlL : l ∈ L := S.L1_le_L hl
    have hlc : l * c = c * l :=
      Subgroup.mem_centralizer_iff.mp hc.2 l (Subgroup.mem_sup_left hlL)
    have hvT : ∀ t ∈ T, t * v * t⁻¹ = v := by
      intro t ht
      have h1 : t * (v * c) * t⁻¹ = v * c := by
        have := Subgroup.mem_centralizer_iff.mp
          ((mem_quasithinOmegaOneCenter_iff.mp hz').2.1) t ht
        rw [this]; group
      have h2 : t * c * t⁻¹ = c := by
        have := Subgroup.mem_centralizer_iff.mp hc.2 t (Subgroup.mem_sup_right ht)
        rw [this]; group
      calc t * v * t⁻¹ = t * (v * c) * t⁻¹ * (t * c * t⁻¹)⁻¹ := by group
        _ = v * c * c⁻¹ := by rw [h1, h2]
        _ = v := by group
    have hvV1 : v ∈ S.V1 := S.mem_V1_of_fixed hv hvT
    have hlv : l * v * l⁻¹ = v := by
      rcases S.mem_V1.1 hvV1 with rfl | rfl
      · group
      · exact S.conj_z_of_normalizes (S.L1_le_NV1 hl)
    calc v * c * l = v * (l * c) := by rw [hlc]; group
      _ = (l * v * l⁻¹) * l * c := by rw [hlv]; group
      _ = l * (v * c) := by group

end Setting

end CFSG.Quasithin.H13.A5
