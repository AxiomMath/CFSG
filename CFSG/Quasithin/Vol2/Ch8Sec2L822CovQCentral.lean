module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQDef
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP1
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovZ
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1b
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3ListNum
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLie
public import CFSG.Quasithin.Background.SmithC27RHat6Lin

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

theorem cover_Q_false_central {Q : Type} [Group Q] [Finite Q] {S P Kt B : Subgroup Q} {yt : Q}
    (hd : CoverQData Q S P Kt B yt) (hZ : ¬ 27 ∣ Nat.card (Q ⧸ Subgroup.center Q)) : False := by
  have hBq : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1080 :=
    CFSG.Quasithin.SmithC27.card_of_isHat_alt6 hd.Bhat
  have h27 : 27 ∣ Nat.card ↥B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hBq]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hu3 : (⟨yt, hd.ytB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hd.yt3)
  have hu1 : (⟨yt, hd.ytB⟩ : ↥B) ∉ CFSG.pCore 2 ↥B := by
    intro hmem
    have h1 : (⟨yt, hd.ytB⟩ : ↥B) = 1 :=
      kzEqOnePowThreeMem_kz3 CFSG.pCore_isPGroup hu3 hmem
    have hyt : yt = 1 := congrArg Subtype.val h1
    obtain ⟨φ, -, hφy⟩ := hd.Kphi
    apply hφy
    have h2 : (⟨yt, hd.ytK⟩ : ↥Kt) = 1 := Subtype.ext hyt
    rw [h2, map_one]
  have hker0 : ∀ b ∈ (B.subtype : ↥B →* Q).ker, b ∈ CFSG.pCore 2 ↥B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hb1 : b = 1 := Subtype.ext hb
    rw [hb1]
    exact (CFSG.pCore 2 ↥B).one_mem
  have hcen : yt ∈ Subgroup.center Q :=
    central_image_of_hat_cv (B := ↥B) (N₀ := Q) B.subtype (CFSG.pCore 2 ↥B) CFSG.pCore_isPGroup hker0
      hd.Bhat.2.1 h27 hZ (⟨yt, hd.ytB⟩ : ↥B) hu3 hd.ytc hu1
  obtain ⟨φ, hφs, hφy⟩ := hd.Kphi
  have hker : ∀ d ∈ (MonoidHom.id Q).ker, ∃ n : ℕ, d ^ (2 ^ n) = 1 := by
    intro d hd'
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hd'
    exact ⟨0, by simp [hd']⟩
  have hnorm : ∀ d ∈ Kt, (MonoidHom.id Q) d * (MonoidHom.id Q) yt * ((MonoidHom.id Q) d)⁻¹ ∈
      Subgroup.zpowers ((MonoidHom.id Q) yt) := by
    intro d _
    simp only [MonoidHom.id_apply]
    rw [Subgroup.mem_center_iff.1 hcen d, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers yt
  exact false_of_centrality_trap_cv (D := Q) Kt (kzTopCommutatorOfPerfect_kz3 hd.Kperf) φ hφs yt hd.ytK hd.yt3
    hφy (MonoidHom.id Q) hker hnorm

theorem cover_Q_false_hat7 {Q : Type} [Group Q] [Finite Q] {S P Kt B : Subgroup Q} {yt : Q}
    (hd : CoverQData Q S P Kt B yt) (hQ : CFSG.Quasithin.IsHat Q (alternatingGroup (Fin 7))) : False := by
  apply cover_Q_false_central hd
  obtain ⟨-, -, ⟨e⟩⟩ := hQ
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven_kz3]
  norm_num

theorem cover_Q_false_su35 {Q : Type} [Group Q] [Finite Q] {S P Kt B : Subgroup Q} {yt : Q}
    (hd : CoverQData Q S P Kt B yt) (hQ : CFSG.Quasithin.IsSU3 5 Q) : False := by
  apply cover_Q_false_central hd
  rw [CFSG.Quasithin.H13.NotLie.card_su35_quot hQ]
  norm_num

theorem cover_Q_false_hatM22 {Q : Type} [Group Q] [Finite Q] {S P Kt B : Subgroup Q} {yt : Q}
    (hM22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520)
    (hd : CoverQData Q S P Kt B yt)
    (hQ : CFSG.Quasithin.IsHat Q CFSG.Blueprint.NativeSporadic.M22) : False := by
  apply cover_Q_false_central hd
  obtain ⟨-, -, ⟨e⟩⟩ := hQ
  rw [Nat.card_congr e.toEquiv, hM22]
  norm_num

end CFSG.Quasithin.H13
