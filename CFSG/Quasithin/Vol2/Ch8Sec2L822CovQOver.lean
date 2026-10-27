module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQDef
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovArith
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP3
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3ListNum

public section

namespace CFSG.Quasithin.H13

theorem five_dvd_card_of_onto_A5_cv {Q : Type} [Group Q] [Finite Q] {Kt P : Subgroup Q} (hKP : Kt ≤ P)
    (φ : ↥Kt →* ↥(alternatingGroup (Fin 5))) (hφ : Function.Surjective φ) : 5 ∣ Nat.card P := by
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφ
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, Subgroup.card_top, card_alternatingGroup_five_kz3] at h
  have h5K : 5 ∣ Nat.card ↥Kt := by
    rw [← h]
    exact Dvd.dvd.mul_left (by norm_num) _
  exact dvd_trans h5K (Subgroup.card_dvd_of_le hKP)

theorem cover_Q_false_M24 (hov : OverSylow2M24Cov)
    {Q : Type} [Group Q] [Finite Q] (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24))
    {S P Kt B : Subgroup Q} {yt : Q} (hd : CoverQData Q S P Kt B yt) : False := by
  have hcQ : Nat.card Q = 2 ^ 10 * 239085 := by
    obtain ⟨e⟩ := hQ
    exact (Nat.card_congr e.toEquiv).trans
      ((CFSG.Sporadic.Mathieu.card_M24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040).trans
        (by norm_num))
  have hS1024 : Nat.card S = 1024 :=
    (card_two_subgroup_of_card_cv S hd.S2 hd.Sodd hcQ (by norm_num)).trans (by norm_num)
  obtain ⟨φ, hφs, -⟩ := hd.Kphi
  have h5 : 5 ∣ Nat.card P := five_dvd_card_of_onto_A5_cv hd.KP φ hφs
  exact false_of_M24_cover_cv hov hQ P S hd.S2 hS1024 hd.SP h5 hd.P9

theorem cover_Q_false_He (hov : OverSylow2HeCov)
    {Q : Type} [Group Q] [Finite Q] (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    {S P Kt B : Subgroup Q} {yt : Q} (hd : CoverQData Q S P Kt B yt) : False := by
  have hcQ : Nat.card Q = 2 ^ 10 * 3935925 := by
    obtain ⟨e⟩ := hQ
    exact (Nat.card_congr e.toEquiv).trans
      ((CFSG.Sporadic.He.card_He : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200).trans
        (by norm_num))
  have hS1024 : Nat.card S = 1024 :=
    (card_two_subgroup_of_card_cv S hd.S2 hd.Sodd hcQ (by norm_num)).trans (by norm_num)
  obtain ⟨φ, hφs, -⟩ := hd.Kphi
  have h5 : 5 ∣ Nat.card P := five_dvd_card_of_onto_A5_cv hd.KP φ hφs
  exact false_of_He_cover_cv hov hQ P S hd.S2 hS1024 hd.SP h5 hd.P9

end CFSG.Quasithin.H13
