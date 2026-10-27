module

public import CFSG.Quasithin.Background.HParabL34Gen
public import CFSG.Quasithin.Background.HB82L34

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Parab
  CFSG.LieType.Multipliers
open scoped commutatorElement

theorem vM_mul_self (t : ℕ) : sM (4 * t) * sM (4 * t) = 1 := by
  have h : fc (4 * t) = 0 := f4_eq_of_code (by show 4 * t % 4 = 0; omega)
  show um (fc (4 * t)) (fc (4 * t / 4)) (fc (4 * t / 16)) *
    um (fc (4 * t)) (fc (4 * t / 4)) (fc (4 * t / 16)) = 1
  rw [h, um_mul, add_self_F4, zero_mul, add_zero, add_self_F4, add_self_F4]
  exact um_zero

@[expose] def vG (t : ℕ) : GL (Fin 3) F4 := ⟨sM (4 * t), sM (4 * t), vM_mul_self t, vM_mul_self t⟩

theorem vM_mul {s t : ℕ} (hs : s < 16) (ht : t < 16) :
    sM (4 * s) * sM (4 * t) = sM (4 * (s ^^^ t)) :=
  mcode_injective (qw_mul_code s hs t ht)

@[expose] def QWG : Subgroup (GL (Fin 3) F4) where
  carrier := {g | ∃ t < 16, g = vG t}
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s ^^^ t, Nat.xor_lt_two_pow (n := 4) hs ht, Units.ext (vM_mul hs ht)⟩
  one_mem' := ⟨0, by norm_num, Units.ext (mcode_injective qw_zero_code).symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, Units.ext rfl⟩

@[expose] noncomputable def QW9 : Subgroup (MulAut W9) := QWG.map rho9

theorem rho9_vG_mem {t : ℕ} (ht : t < 16) : rho9 (vG t) ∈ QW9 := ⟨vG t, ⟨t, ht, rfl⟩, rfl⟩

theorem mem_QW9 {φ : MulAut W9} : φ ∈ QW9 ↔ ∃ t < 16, rho9 (vG t) = φ := by
  constructor
  · rintro ⟨g, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact rho9_vG_mem ht

theorem rho9_vG_eq (t : ℕ) : rho9 (vG t) = rho9 (sG (4 * t)) := congrArg rho9 (Units.ext rfl)

theorem cols_vG {t : ℕ} (ht : t < 16) :
    cols ((vG t : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = colsS1.getD (4 * t) [] :=
  cols_s (4 * t) (by omega)

theorem fixV_QW9 : fixV QW9 = U0 := by
  ext w
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 w
  have hm' : m < 512 := lt_of_lt_of_eq hm (by norm_num)
  have hq := qw_fix m hm'
  constructor
  · intro hw
    have hall : ((List.range 16).all fun t => actM (colsS1.getD (4 * t) []) m == m) = true := by
      rw [List.all_eq_true]
      intro t htr
      have ht := List.mem_range.1 htr
      have h1 : toW 9 (actM (colsS1.getD (4 * t) []) m) = toW 9 m :=
        (rho9_toW_cols (vG t) (cols_vG ht) hm').symm.trans (hw _ (rho9_vG_mem ht))
      exact beq_iff_eq.2 (toW_inj (lt_of_lt_of_eq (by rw [← cols_vG ht]; exact actM_cols_lt _ hm')
        (by norm_num)) hm h1)
    rw [hq, List.contains_iff_mem] at hall
    exact toW_mem_maskSub hall
  · rintro ⟨m', hm'', he⟩
    have hmm : m' = m := toW_inj (combos_lt U0Basis_lt m' hm'') hm he
    subst hmm
    intro φ hφ
    obtain ⟨t, ht, rfl⟩ := mem_QW9.1 hφ
    have hall : ((List.range 16).all fun t => actM (colsS1.getD (4 * t) []) m' == m') = true := by
      rw [hq, List.contains_iff_mem]
      exact hm''
    have h2 := List.all_eq_true.1 hall t (List.mem_range.2 ht)
    rw [beq_iff_eq] at h2
    rw [← he]
    exact (rho9_toW_cols (vG t) (cols_vG ht) hm').trans (congrArg (toW 9) h2)

@[expose] def kc2G (i : ℕ) : GL (Fin 3) F4 :=
  if i < 4 then ⁅vG (2 ^ i), x2G⁆ else ⁅vG (2 ^ (i - 4)), y2G⁆

theorem coe_kc2G (i : ℕ) : ((kc2G i : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = kc2M i := by
  show ((if i < 4 then ⁅vG (2 ^ i), x2G⁆ else ⁅vG (2 ^ (i - 4)), y2G⁆ : GL (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) = if i < 4 then sM (4 * 2 ^ i) * x2M * sM (4 * 2 ^ i) * x2Mi
      else sM (4 * 2 ^ (i - 4)) * y2M * sM (4 * 2 ^ (i - 4)) * y2Mi
  split_ifs
  · show ((vG (2 ^ i) * x2G * (vG (2 ^ i))⁻¹ * x2G⁻¹ : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    rfl
  · show ((vG (2 ^ (i - 4)) * y2G * (vG (2 ^ (i - 4)))⁻¹ * y2G⁻¹ : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    rfl

theorem coe_kc2Gs : ((List.range 8).map kc2G).map Units.val = (List.range 8).map kc2M := by
  rw [List.map_map]
  exact List.map_congr_left fun i _ => coe_kc2G i

theorem QW9_le_comm : QW9 ≤ ⁅QW9, P2⁆ := by
  intro φ hφ
  obtain ⟨t, ht, rfl⟩ := mem_QW9.1 hφ
  have hw : wGL ((List.range 8).map kc2G) (qwComms.getD t []) = vG t := by
    apply Units.ext
    rw [coe_wGL, coe_kc2Gs]
    exact mcode_injective (qwComm_code t ht)
  rw [← hw]
  refine rho9_wGL_mem (fun g hg => ?_) _
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  have hi8 := List.mem_range.1 hi
  unfold kc2G
  split_ifs with h4
  · rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (rho9_vG_mem (by interval_cases i <;> norm_num)) x2_mem_P2
  · rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (rho9_vG_mem (by interval_cases i <;> norm_num)) y2_mem_P2

theorem mem_P2_of_cols {g : GL (Fin 3) F4} {w : List ℕ}
    (h : cols (g : Matrix (Fin 3) (Fin 3) F4) = cols (wM [x2M, y2M] w)) : rho9 g ∈ P2 := by
  have e : rho9 g = rho9 (wGL [x2G, y2G] w) := rho9_eq_of_cols (by rw [h, coe_wGL]; rfl)
  rw [e]
  refine rho9_wGL_mem (fun g hg => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact x2_mem_P2
  · exact y2_mem_P2

theorem S1_le_P2 : S1 ≤ P2 := by
  intro φ hφ
  obtain ⟨p, hp, rfl⟩ := mem_S1.1 hφ
  exact mem_P2_of_cols ((cols_sG hp).trans (s2Word_ok p hp).symm)

theorem actsBy_rho9_x2 : ActsBy (rho9 x2G) (p2Cols 0) :=
  actsBy_rho9 cols_x2.1 rfl

theorem actsBy_rho9_y2 : ActsBy (rho9 y2G) (p2Cols 1) :=
  actsBy_rho9 cols_x2.2.1 rfl

theorem le_card_P2 : 960 ≤ Nat.card P2 := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  have hgen : ∀ gi : ℕ, ∃ g ∈ P2, ActsBy g (p2Cols gi) := by
    intro gi
    by_cases hg : gi = 0
    · rw [hg]
      exact ⟨_, x2_mem_P2, actsBy_rho9_x2⟩
    · have e : p2Cols gi = p2Cols 1 := by
        unfold p2Cols
        rw [ite_eq_right hg]
        rfl
      rw [e]
      exact ⟨_, y2_mem_P2, actsBy_rho9_y2⟩
  have hlt : ∀ gi, ∀ x ∈ p2Cols gi, x < 2 ^ 9 := by
    intro gi x hx
    unfold p2Cols at hx
    split_ifs at hx <;> revert x <;> decide
  have h := le_card_of_tree (K := P2) (tupKey 9 9 id9 p2Us) p2Act (fun gi m => by
      rintro ⟨φ, hφ, rfl⟩
      obtain ⟨g, hg, hga⟩ := hgen gi
      exact ⟨g * φ, P2.mul_mem hg hφ, tupKey_mul hga (hlt gi)
        (M := fun m => m < 2 ^ 9) (fun m hm => id9_ok m hm) p2Us
        fun u _ => (maskOf_spec _).1⟩)
    ⟨1, P2.one_mem, by
      rw [tupKey_one p2Us (by decide), p2Us_start]⟩ p2Tree_ok
  rwa [p2Tree_length] at h

theorem card_stab_U0_le :
    Nat.card ↥(img9 ⊓ stabSub U0) ≤ 960 := by
  have hmem : ∀ i < [rhoA9, rhoB9].length, [rhoA9, rhoB9].getD i 1 ∈ img9 := by
    intro i hi
    rcases i with _ | _ | i
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp at hi
  have hact : ∀ i < [rhoA9, rhoB9].length,
      ActsBy ([rhoA9, rhoB9].getD i 1) ([l9A, l9B].getD i []) := by
    intro i hi
    rcases i with _ | _ | i
    · exact actsBy_rhoA9
    · exact actsBy_rhoB9
    · simp at hi
  have h := card_stab_le_of_orb hmem hact (d := U0Basis) (st := u0Steps)
    (fun e he => by simpa using u0Steps_lt e he) u0_orb_lt u0_orb_nodup
  rw [u0_orb_length, card_img9] at h
  have h' : 21 * Nat.card ↥(img9 ⊓ stabSub U0) ≤ 20160 := h
  omega

theorem stab_U0_eq : img9 ⊓ stabSub U0 = P2 := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  exact (Subgroup.eq_of_le_of_card_ge P2_le (card_stab_U0_le.trans le_card_P2)).symm

theorem card_P2 : Nat.card P2 = 960 :=
  le_antisymm (stab_U0_eq ▸ card_stab_U0_le) le_card_P2

theorem perfectCore_stab_U0 :
    perfectCore (img9 ⊓ stabSub U0) = P2 := by
  rw [stab_U0_eq, perfectCore_eq_self_of_perfect commutator_P2]

theorem pCoreOf_P2_le : pCoreOf 2 P2 ≤ QW9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  set N := CFSG.Open.pCore 2 ↥P2 with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hT : Nat.card (S1.subgroupOf P2) = 2 ^ (Nat.card ↥P2).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S1_le_P2).toEquiv, card_S1, card_P2,
      factorization_960]
    norm_num
  let T : Sylow 2 ↥P2 := Sylow.ofCard (S1.subgroupOf P2) hT
  have hNT : N ≤ (T : Subgroup ↥P2) := hNp.le_sylow_of_normal T
  have hS1 : ∀ n ∈ N, (n : MulAut W9) ∈ S1 := fun n hn => Subgroup.mem_subgroupOf.1 (hNT hn)
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨p, hp, hpn⟩ := mem_S1.1 (hS1 n hn)
  by_cases hp4 : p % 4 = 0
  · refine mem_QW9.2 ⟨p / 4, by omega, ?_⟩
    rw [rho9_vG_eq, show 4 * (p / 4) = p by omega]
    exact hpn
  · exfalso
    set xL : ↥P2 := ⟨rho9 x2G, x2_mem_P2⟩
    have hy : xL⁻¹ * n * xL⁻¹⁻¹ ∈ N := hNn.conj_mem n hn xL⁻¹
    obtain ⟨q, hq, hqn⟩ := mem_S1.1 (hS1 _ hy)
    have e : rho9 (sG q) = rho9 (x2G⁻¹ * sG p * x2G) := by
      rw [hqn, map_mul, map_mul, map_inv, hpn]
      simp [xL]
    have e2 := cols_eq_of_rho9_eq e
    rw [cols_sG hq] at e2
    apply s2_conj p hp hp4
    rw [show cols (x2Mi * sM p * x2M) = colsS1.getD q [] from e2.symm]
    have hlen : q < colsS1.length := by
      have : colsS1.length = 64 := rfl
      omega
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen

theorem parab_std {X₀ : Subgroup (MulAut W9)}
    (hX : fixV X₀ = U0) (hQ : QW9 ≤ X₀) :
    Nat.card ↥(perfectCore (img9 ⊓ stabSub (fixV X₀))) = 960 ∧
      pCoreOf 2 (perfectCore (img9 ⊓ stabSub (fixV X₀))) ≤
        ⁅X₀, perfectCore (img9 ⊓ stabSub (fixV X₀))⁆ := by
  rw [hX, perfectCore_stab_U0]
  exact ⟨card_P2, pCoreOf_P2_le.trans (QW9_le_comm.trans (Subgroup.commutator_mono hQ le_rfl))⟩

end CFSG.Quasithin.H.L34Z
