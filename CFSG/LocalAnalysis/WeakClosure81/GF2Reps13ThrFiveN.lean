module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNU
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrIso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Frobenius
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_case_five_N (h : Cfg133 A t 5) :
    ∃ L : Subgroup (MulAut W), L ≤ pCoreOf 5 A ∧ Conc4_133 A t L ∧ IsCyclicOrd ↥L 5 ∧
      rk ↥(commSub ⊤ L) = 4 ∧ ∀ n ∈ pCoreOf 5 A, L.map (MulAut.conj n).toMonoidHom = L := by
  classical
  let O : Subgroup (MulAut W) := pCoreOf 5 A
  let P : Subgroup (MulAut W) := ⁅O, Subgroup.zpowers t⁆
  let U : Subgroup W := commSub ⊤ P
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  obtain ⟨hPO, hPp, hPne, hnP, hcP, hOn⟩ := s13_P_facts h
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htord : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  have hcardP : Nat.card P = 5 :=
    (w4Lem13_1_holds W hW2 t htord h.hrk 5 P Nat.prime_five hPp hPne hnP hcP).2
      (Or.inl (by norm_num))
  have hcne : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥ := by rw [hcP]; exact hPne
  obtain ⟨x, hxP, hxord, hxinv⟩ :=
    exists_inverted_orderOf_eq_prime htt Nat.prime_five hPp hnP hcne
  have hzxle : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.mpr hxP
  have hzeq : Subgroup.zpowers x = P := by
    refine Subgroup.eq_of_le_of_card_ge hzxle ?_
    rw [Nat.card_zpowers, hxord, hcardP]
  have hPinv : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    rw [← hzeq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hconj : MulAut.conj t x = x⁻¹ := by rw [MulAut.conj_apply, hxinv]
    calc t * x ^ k * t⁻¹ = MulAut.conj t (x ^ k) := (MulAut.conj_apply t (x ^ k)).symm
      _ = (MulAut.conj t x) ^ k := map_zpow (MulAut.conj t) x k
      _ = (x⁻¹) ^ k := by rw [hconj]
      _ = (x ^ k)⁻¹ := by rw [inv_zpow]
  have hPP : ∀ y ∈ P, ∀ x ∈ P, y * x * y⁻¹ ∈ P :=
    fun y hy x hx => P.mul_mem (P.mul_mem hy hx) (P.inv_mem hy)
  have hUstab : StableUnder P U :=
    stableUnder_commSub (H := P) (X := P) hPP (fun y hy w hw => Subgroup.mem_top (y w))
  have ht_norm : t ∈ Subgroup.normalizer (P : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnP y hy, fun hy => ?_⟩
    have hmem : t * (t * y * t⁻¹) * t⁻¹ ∈ P := hnP (t * y * t⁻¹) hy
    have hyy : t * (t * y * t⁻¹) * t⁻¹ = y := by
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left htt]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt]; simp
    rwa [hyy] at hmem
  have hZconj : ∀ y ∈ Subgroup.zpowers t, ∀ x ∈ P, y * x * y⁻¹ ∈ P := by
    intro y hy x hx
    have hnorm : y ∈ Subgroup.normalizer (P : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr ht_norm hy
    exact (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx
  have hUt : ∀ u ∈ U, t u ∈ U := by
    have hstab := stableUnder_commSub (H := Subgroup.zpowers t) (X := P) hZconj
      (fun y hy w hw => Subgroup.mem_top (y w))
    intro u hu
    exact hstab t (Subgroup.mem_zpowers t) u hu
  have hOstab : StableUnder O U :=
    stableUnder_commSub (H := O) (X := P) hOn (fun y hy w hw => Subgroup.mem_top (y w))
  have hPodd : Odd (Nat.card P) := by rw [hcardP]; norm_num
  have hUfixX : U ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
    rw [inf_comm, hzeq]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hPodd
  have hUfixP : U ⊓ fixV P = ⊥ := by
    rw [hzeq] at hUfixX
    exact hUfixX
  have hX5 : IsElemAbelianOfRank 5 1 ↥P :=
    w16g_isElemAbelianOfRank_one_of_card Nat.prime_five hcardP
  have hcost : rk ↥U = 2 * rk ↥(commSub U (Subgroup.zpowers t)) :=
    s13_cost_inverted h.hW htord Nat.prime_five (by norm_num) (by norm_num) hX5 hPinv
      hUstab hUt hUfixP
  have hcomm_le : commSub U (Subgroup.zpowers t) ≤ commSub ⊤ (Subgroup.zpowers t) :=
    commSub_mono le_top le_rfl
  have hrk_t_le : rk ↥(commSub U (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono hcomm_le) h.hrk
  have hrkU_le : rk ↥U ≤ 6 := by
    rw [hcost]
    omega
  have hdvdU := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.dParam_dvd_rk
    hW2 Nat.prime_five (by norm_num) hxord (fun m hm => hUstab x hxP m hm) hUfixX
  have hrkU_ne : rk ↥U ≠ 0 := by
    intro h0
    have hbot : U = ⊥ := (rk_eq_zero_iff hW2).mp h0
    have hfix_top : (⊤ : Subgroup W) ≤ fixV P := (commSub_eq_bot_iff).mp hbot
    have hPbot : P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      apply MulEquiv.ext
      intro w
      exact (mem_fixV.mp (hfix_top (Subgroup.mem_top w))) y hy
    exact hPne hPbot
  have hd5 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.dParam 5 = 4 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.dParam_eq_of_small.2.1
  have hrkU : rk ↥U = 4 := by
    have hdvd : (4 : ℕ) ∣ rk ↥U := by
      have hd := hdvdU
      rwa [hd5] at hd
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k ≤ 1 := by omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact hrkU_ne hk
    have hk_eq : k = 1 := by omega
    simp [hk, hk_eq]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcycP : IsCyclic ↥P := isCyclic_of_prime_card (p := 5) hcardP
  have hiso : IsEntireIsotypic P U := s13_isotypic_commSub h.hW hPodd
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have h0 : rk ↥U = 0 := by rw [hbot, rk_bot]
    omega
  have hirr : IsIrrOn O U ⊥ := by
    refine ⟨bot_lt_iff_ne_bot.mpr hUbot, hOstab, ?_, ?_⟩
    · intro y hy u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    · intro J hJ _ hJU
      by_cases hJbot : J = ⊥
      · exact Or.inl hJbot
      · refine Or.inr ?_
        have hJfix : J ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
          refine le_bot_iff.mp ?_
          calc J ⊓ fixV (Subgroup.zpowers x) ≤ U ⊓ fixV (Subgroup.zpowers x) :=
                inf_le_inf hJU le_rfl
            _ = ⊥ := hUfixX
        have hJdvd := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.dParam_dvd_rk
          hW2 Nat.prime_five (by norm_num) hxord (fun m hm => hJ x (hPO hxP) m hm) hJfix
        have hJrk_le : rk ↥J ≤ 4 := by
          rw [← hrkU]; exact rk_mono hJU
        have hJrk_ne : rk ↥J ≠ 0 := fun h0 => hJbot ((rk_eq_zero_iff hW2).mp h0)
        have hJdvd4 : (4 : ℕ) ∣ rk ↥J := by
          have hd := hJdvd
          rwa [hd5] at hd
        obtain ⟨k, hk⟩ := hJdvd4
        have hk1 : k ≤ 1 := by omega
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hk
          exact hJrk_ne hk
        have hk_eq : k = 1 := by omega
        have hJrk : rk ↥J = 4 := by
          simp [hk, hk_eq]
        exact eq_of_le_of_rk_le hW2 hJU (by omega)
  have hsSup : sSupIndep (conjSubs A U) :=
    sSupIndep_conjSubs_of_isotypic h.hW A O P (s13_pCore_facts A 5).2.1
      (s13_pCore_facts A 5).1 hPO U hirr hiso
  refine ⟨P, hPO, ?_, ⟨hcycP, hcardP⟩, hrkU, fun n hn => s13_map_conj_eq_of_normalizes hOn hn⟩
  exact ⟨5, Nat.prime_five, hPO, hcne, hsSup, Or.inr (Or.inl ⟨⟨hcycP, hcardP⟩, hrkU⟩)⟩

end CFSG.LocalAnalysis.WeakClosure81
