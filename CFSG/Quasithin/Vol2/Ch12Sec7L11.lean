module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative commutatorElement

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_le_of_autOn_le {V R D : Subgroup G} (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hDN : D ≤ Subgroup.normalizer (V : Set G)) (hle : autOn R V ≤ autOn D V)
    (hVD : V ≤ Subgroup.normalizer (D : Set G)) : ⁅V, R⁆ ≤ D := by
  have hVRD : ⁅V, R⁆ ≤ ⁅V, D⁆ := by
    refine Subgroup.commutator_le.2 fun v hv r hr => ?_
    have ha : A4.actionOn V R hRN ⟨r, hr⟩ ∈ autOn D V :=
      hle ((A4.mem_autOn_iff hRN).2 ⟨⟨r, hr⟩, rfl⟩)
    obtain ⟨d, hd⟩ := (A4.mem_autOn_iff hDN).1 ha
    have hdv : (d : G) * v⁻¹ * (d : G)⁻¹ = r * v⁻¹ * r⁻¹ := by
      have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v⁻¹, V.inv_mem hv⟩ : ↥V) : G)) hd
      simpa [A4.actionOn_apply_coe] using this
    have e : ⁅v, r⁆ = ⁅v, (d : G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) := by group
        _ = v * ((d : G) * v⁻¹ * (d : G)⁻¹) := by rw [hdv]
        _ = v * d * v⁻¹ * (d : G)⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hv d.2
  refine hVRD.trans (Subgroup.commutator_le.2 fun v hv d hd => ?_)
  rw [commutatorElement_def]
  exact D.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVD hv) d).1 hd) (D.inv_mem hd)

theorem autOn_eq_R2_of_conj_le (h1222 : Stmt12_2_2) (h3 : Lemma12_7_3) (h10 : Lemma12_7_10)
    {T L V : Subgroup G} {t : G} (hS : Setting1273 G T L V t) {g : G}
    (hAT : conjSubgroup V g ≤ T) (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    autOn (conjSubgroup V g) V = autOn (R2 T L V) V := by
  obtain ⟨hcomm, -, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hs : sParam hVe = 2 := (h10 G T L V t hS).2.1.2 hVe
  have hAN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTV
  have hinf : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) = conjSubgroup V g :=
    inf_of_le_left hAN
  have hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hVe := by
    rw [hinf, mQuot_self, hs]
    norm_num
  have hmem := e3_10_two hVe hb hnc
  rw [hinf, mQuot_self, hs, Nat.sub_zero] at hmem
  have hmem' : autOn (conjSubgroup V g) V ∈ aSet 2 (autOn T V) :=
    ⟨A4.autOn_mono hAT, hmem.2⟩
  rw [(h3 G T L V hS.hyp).1] at hmem'
  exact hmem'

theorem conj_V_le_centralizer (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) (h3 : Lemma12_7_3)
    (h4 : Lemma12_7_4) (h9 : Lemma12_7_9) (h10 : Lemma12_7_10) {T L V : Subgroup G} {t : G}
    (hS : Setting1273 G T L V t) {g : G} (hAT : conjSubgroup V g ≤ T) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hV64, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  set A := conjSubgroup V g with hAdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTV
  by_contra hAC
  have hnc : ⁅V, A⁆ ≠ ⊥ := by
    intro h
    apply hAC
    exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)
  have hR := autOn_eq_R2_of_conj_le h1222 h3 h10 hS hAT hnc
  obtain ⟨-, -, -, -, ⟨-, -, hR4, -, -, hVR⟩, -, -⟩ := h2 G T L V hS.hyp
  have hRN := R2_le_normalizer h1222 hS.hyp
  have hidx : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 4 := by
    rw [← card_autOn_eq_relIndex hAN, hR, hR4]
  have hV2 := isPGroup_V hS.hyp
  have hA2 : IsPGroup 2 A := isPGroup_conjSubgroup hV2 g
  have hm : mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 2 := by
    have h := relIndex_eq_two_pow hA2 (A ⊓ Subgroup.centralizer (V : Set G))
    rw [hidx] at h
    have h' : (2 : ℕ) ^ 2 = 2 ^ mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) := by
      rw [← h]
      norm_num
    exact (Nat.pow_right_injective (le_refl 2) h').symm
  have hr := (h10 G T L V t hS).2.1.1
  have hCN : Subgroup.centralizer ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
    by_contra hnot
    have h1 := rParam_le_mQuot (inf_le_left : A ⊓ Subgroup.centralizer (V : Set G) ≤ A) hnot
    rw [hAdef, rParam_conj, ← hAdef, hm] at h1
    exact absurd (lt_of_lt_of_le hr h1) (by norm_num)
  have hVA : V ≤ Subgroup.normalizer (A : Set G) := by
    refine le_trans ?_ hCN
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 v hv).symm
  have hV2A : V2 T L V ≤ A := by
    rw [← hVR]
    exact comm_le_of_autOn_le hRN hAN hR.ge hVA
  obtain ⟨-, -, -, h4t, -⟩ := (h4 G T L V hS.hyp).2 t hS.t_mem hS.orbit_t
  obtain ⟨W, ⟨-, hWV2, l, hl, rfl⟩⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h4t]; norm_num)
  have ht : t ∈ Vt L t := le_conjClosure _ _ (Subgroup.mem_zpowers t)
  have hlt : l * t * l⁻¹ ∈ A := hV2A (hWV2 ⟨t, ht, rfl⟩)
  have htA : t ∈ conjSubgroup A l := by
    rw [mem_conjSubgroup_iff]
    exact hlt
  rw [hAdef, conjSubgroup_conjSubgroup] at htA
  have hAl := (h9 G T L V t hS).2.2 _ htA
  have hlN : l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.inv_mem _ (hS.hyp.hyp.irrPlus.2.2.1 hl)
  have hAV : A = V := by
    have h1 : conjSubgroup (conjSubgroup V (g * l)) l⁻¹ = conjSubgroup V l⁻¹ := by rw [hAl]
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel_right] at h1
    rw [hAdef, h1, conjSubgroup_inv_eq_map, map_conj_of_mem_normalizer
      (by simpa using hlN)]
  apply hnc
  rw [hAV, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨w, hw⟩ : ↥V) ⟨v, hv⟩)

end S127

open S127 in
theorem lemma12_7_11_of (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight)
    (h2 : Lemma12_7_2) (h3 : Lemma12_7_3) (h4 : Lemma12_7_4) (h9 : Lemma12_7_9)
    (h10 : Lemma12_7_10) : Lemma12_7_11 := by
  intro G _ _ T L V t hS
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hVe : IsElemAbelian 2 V := ⟨hcomm, fun v hv => sq_eq_one_of_mem hS.hyp.hyp hv⟩
  have hW : wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (mQuot_eq_zero_iff (isPGroup_conjSubgroup (isPGroup_V hS.hyp) g) hAg).1 hm
    rw [hAeq] at hAT ⊢
    exact le_inf hAT (conj_V_le_centralizer h1222 h2 h3 h4 h9 h10 hS hAT)
  have hw : 0 < wParam T V := by
    refine lt_of_lt_of_le (show (0 : ℕ∞) < 1 by norm_num) (le_iInf₂ fun j hj => ?_)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd hW hj
    · exact_mod_cast hj0
  have hrk : 0 < rk ↥V := by
    rw [rk, hV64, padicValNat.prime_pow]
    norm_num
  refine ⟨hW, hw, ?_⟩
  exact (e3_34_two hVe (hypE322 h1222 hS.hyp) (isUniqueM_centralizer h331 h3228 h1222 hS.hyp)
    hrk (by exact_mod_cast hw)).1

end CFSG.Quasithin.H13
