module

public import CFSG.Quasithin.Vol2.Ch9Sec3FFBList
public import CFSG.Quasithin.H13.A7Nat1238QTabA314
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

namespace CFSG.Quasithin.H13.Ch9.FFB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {X : Type} [Group X] [Finite X]

structure CmpHyp (L : Subgroup Q) (X : Type) [Group X] [Finite X] : Prop where
  quasi : CFSG.IsQuasisimple ↥L
  center_odd : Odd (Nat.card (Subgroup.center ↥L))
  map : ∃ π : ↥L →* X, Function.Surjective π ∧ π.ker ≤ Subgroup.center ↥L ∧ π.ker ≠ ⊤
  list : B56QuasisimpleList X
  quasiX : CFSG.IsQuasisimple X
  dvd60 : 60 ∣ Nat.card X

namespace CmpHyp

theorem false_of_card (hc : CmpHyp L X) {k D : ℕ} (hL : Nat.card ↥L = 2 ^ k * D) (hD : Odd D)
    (hchk : b56Chk k (fun c => c % 15 == 0 && D % c == 0) = true)
    (h315 : D % 315 ≠ 0 ∨ (k ≠ 3 ∧ k ≠ 6)) : False := by
  obtain ⟨π, hπ, hker, -⟩ := hc.map
  obtain ⟨hodd, hcard⟩ := A7.odd_card_ker_of_le_center hc.center_odd hπ hker
  obtain ⟨a, d, hd, hXd⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := X)).ne'
  have h1 : 2 ^ a * (d * Nat.card π.ker) = 2 ^ k * D := by
    rw [← hL, ← hcard, hXd]
    ring
  obtain ⟨rfl, hdD⟩ := eq_of_two_pow_mul_odd (hd.mul hodd) hD h1
  have h15 : 15 ∣ d := by
    have h := (Dvd.intro_left 4 rfl : 15 ∣ 60).trans hc.dvd60
    rw [hXd] at h
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right a (by norm_num)) h
  have hdvd : d ∣ D := ⟨Nat.card π.ker, hdD.symm⟩
  have hP : (fun c => c % 15 == 0 && D % c == 0) d = true := by
    simp [Nat.mod_eq_zero_of_dvd h15, Nat.mod_eq_zero_of_dvd hdvd]
  rcases b56_of_chk hc.list hc.quasiX hc.dvd60 hXd hd hP hchk with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
  · rcases h315 with h | h
    · exact h (Nat.mod_eq_zero_of_dvd hdvd)
    · exact h.1 rfl
  · rcases h315 with h | h
    · exact h (Nat.mod_eq_zero_of_dvd hdvd)
    · exact h.2 rfl

omit [Finite Q] in
theorem nonempty_mulEquiv_of_simple (hc : CmpHyp L X) (hs : IsSimpleGroup ↥L) :
    Nonempty (↥L ≃* X) := by
  obtain ⟨π, hπ, -, hne⟩ := hc.map
  have hk : π.ker = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker).resolve_right hne
  exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπ⟩⟩

omit [Finite Q] in
theorem card_eq_of_simple (hc : CmpHyp L X) (hs : IsSimpleGroup ↥L) :
    Nat.card X = Nat.card ↥L := by
  obtain ⟨e⟩ := hc.nonempty_mulEquiv_of_simple hs
  exact (Nat.card_congr e.toEquiv).symm

omit [Finite Q] in
theorem false_of_psl34 (hc : CmpHyp L X) (hL : IsPSL 3 2 2 ↥L) : False := by
  obtain ⟨eL⟩ := hc.nonempty_mulEquiv_of_simple
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hL).2
  obtain ⟨-, F, _, _, hF, ⟨e3⟩⟩ := hL
  have hcL : Nat.card ↥L = 2 ^ 6 * 315 := by
    rw [Nat.card_congr e3.toEquiv,
      Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3) (by norm_num), hF]
    decide
  have hXc : Nat.card X = 2 ^ 6 * 315 := (Nat.card_congr eL.toEquiv).symm.trans hcL
  rcases b56_of_chk hc.list hc.quasiX hc.dvd60 hXc (by decide) (P := fun c => c == 315)
      (by decide) (by decide) with ⟨h, -⟩ | ⟨-, -, ⟨e4⟩⟩
  · omega
  · exact B69.not_equiv_sl_four_psl_three (K := ZMod 2) (F := F) (by simp) (by rw [hF]; norm_num)
      ((eL.trans e4).trans ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.trans
        ((CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two (by simp) (by norm_num)).trans
          (B69.statedProjEquivProjectiveSL 4 (ZMod 2)).symm))) e3

theorem cmp_one (hc : CmpHyp L X)
    (hL : IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L) :
    IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L := by
  rcases hL with hL | hL | hL | hL | hL
  · exact (hc.false_of_psl34 hL).elim
  · exact Or.inl hL
  · exact Or.inr (Or.inl hL)
  · exact Or.inr (Or.inr hL)
  · exfalso
    have hcL : Nat.card ↥L = 2 ^ 24 * 4041335025 := by
      have h := Timmesfeld.card_chevalleyExceptionalModel_two hL
      simp only at h
      rw [h]
      decide
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)

theorem cmp_two (hc : CmpHyp L X)
    (hL : IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) : IsAlt 7 X := by
  rcases hL with hA | ⟨-, hZ3, ⟨eZ⟩⟩
  · obtain ⟨eA⟩ := hA
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨eL⟩ := hc.nonempty_mulEquiv_of_simple eA.isSimpleGroup
    exact ⟨eL.symm.trans eA⟩
  · obtain ⟨π, hπ, hker, -⟩ := hc.map
    have hcard := Subgroup.card_ker_mul_card_of_surjective hπ
    have hk3 : Nat.card π.ker ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h3
    ·
      exfalso
      have hcL : Nat.card ↥L = 2 ^ 3 * 945 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
        rw [Nat.card_congr eZ.toEquiv, card_alternatingGroup1527d 7 (by norm_num), hZ3] at h
        rw [h]
        decide
      have hXc : Nat.card X = 2 ^ 3 * 945 := by
        rw [h1, one_mul] at hcard
        rw [hcard, hcL]
      rcases b56_of_chk hc.list hc.quasiX hc.dvd60 hXc (by decide) (P := fun c => c == 945)
          (by decide) (by decide) with ⟨-, h, -⟩ | ⟨h, -⟩ <;> omega
    ·
      have hkZ : π.ker = Subgroup.center ↥L :=
        Subgroup.eq_of_le_of_card_ge hker (by rw [h3, hZ3])
      exact ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkZ).trans eZ)⟩

theorem false_of_cmp_three (h314 : A314Facts) (hc : CmpHyp L X)
    (hL : IsPSL 2 5 2 ↥L ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      IsPSL 2 p 1 ↥L) : False := by
  rcases hL with hL | ⟨p, hp, hp5, hp8, hL⟩
  · have hcL : Nat.card ↥L = 2 ^ 3 * 975 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num), hF]
      decide
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · have hp11 := A7.eleven_le_of_sq_mod_five hp hp5
    obtain ⟨hs, -, hcL⟩ := h314.model.2.2 p hp (by omega) ↥L hL
    have hXc := hc.card_eq_of_simple hs
    rw [hcL] at hXc
    obtain ⟨w, hw, hpw⟩ : ∃ w, Odd w ∧ p ^ 2 - 1 = 8 * w := by
      obtain ⟨j, hj⟩ : ∃ j, p = 8 * j + p % 8 := ⟨p / 8, (Nat.div_add_mod p 8).symm⟩
      rcases hp8 with h | h <;> rw [h] at hj <;> subst hj
      · exact ⟨8 * j ^ 2 + 6 * j + 1, ⟨4 * j ^ 2 + 3 * j, by ring⟩, by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring⟩
      · exact ⟨8 * j ^ 2 + 10 * j + 3, ⟨4 * j ^ 2 + 5 * j + 1, by ring⟩, by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring⟩
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hm : p * (p ^ 2 - 1) / 2 = 2 ^ 2 * (p * w) := by
      rw [hpw, show p * (8 * w) = 2 * (2 ^ 2 * (p * w)) by ring]
      exact Nat.mul_div_cancel_left _ two_pos
    have h15 : p * w ≠ 15 := by
      intro h
      have hp15 : p ∣ 15 := ⟨w, h.symm⟩
      have := Nat.le_of_dvd (by norm_num) hp15
      interval_cases p <;> omega
    rcases b56_of_chk hc.list hc.quasiX hc.dvd60 (hXc.trans hm) (hpodd.mul hw)
        (P := fun c => c != 15) (by simpa using h15) (by decide) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem false_of_cmp_three_five (hc : CmpHyp L X)
    (hL : (IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L) ∨ IsPSU 3 5 1 ↥L ∨ IsSU3 5 ↥L) : False := by
  rcases hL with (hL | hL) | hL | hL
  · have hcL : Nat.card ↥L = 2 ^ 5 * 11625 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3) (by norm_num), hF]
      decide
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · have hcL : Nat.card ↥L = 2 ^ 5 * 11625 := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
      decide
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · have hcL : Nat.card ↥L = 2 ^ 4 * 7875 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL
      rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) Nat.prime_five le_rfl hF
          (by norm_num)]
      decide
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
    set S := CFSG.Assembly.LowTwoRank.StatedSU 3 5 F with hSdef
    set N := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf S with hN
    have hP : Nat.card (S ⧸ N) = 126000 := by
      have h := Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) (p := 5) (f := 1)
        Nat.prime_five le_rfl (by rw [hF]; norm_num) (by norm_num : 2 ≤ 3)
      simp only [pow_one] at h
      rw [show Nat.card (S ⧸ N) = Nat.card (CFSG.Assembly.LowTwoRank.StatedProj S) from rfl,
        h]
      decide
    have hS : Nat.card ↥S = 126000 * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hP]
    have hNodd : Odd (Nat.card N) := by
      have hNZ : N.map e.symm.toMonoidHom ≤ Subgroup.center ↥L := by
        rintro _ ⟨n, hn, rfl⟩
        have hcn := A7.statedScalars_subgroupOf_le_center S hn
        rw [Subgroup.mem_center_iff] at hcn ⊢
        intro y
        apply e.injective
        simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
        exact hcn (e y)
      have h1 := Subgroup.card_dvd_of_le hNZ
      rw [Subgroup.card_map_of_injective e.symm.injective] at h1
      exact Odd.of_dvd_nat hc.center_odd h1
    have hN24 : Nat.card N ∣ 24 := by
      have h1 : Nat.card N ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F) := by
        rw [← Subgroup.card_map_of_injective S.subtype_injective, hN,
          Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F) ∣ 24 := by
        have h3 := Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F))
        rw [Nat.card_units, hF] at h3
        exact h3
      exact h1.trans h2
    have hN3 : Nat.card N ∣ 3 :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hNodd))
        (show Nat.card N ∣ 2 ^ 3 * 3 from hN24)
    have hcL : Nat.card ↥L = 2 ^ 4 * 7875 ∨ Nat.card ↥L = 2 ^ 4 * 23625 := by
      rw [Nat.card_congr e.toEquiv, hS]
      rcases (Nat.dvd_prime Nat.prime_three).mp hN3 with h | h <;> rw [h]
      · exact Or.inl (by norm_num)
      · exact Or.inr (by norm_num)
    rcases hcL with hcL | hcL
    · exact hc.false_of_card hcL (by decide) (by decide) (by decide)
    · exact hc.false_of_card hcL (by decide) (by decide) (by decide)

theorem false_of_cmp_sporadic
    (hc : CmpHyp L X)
    (hL : (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) ∨
      IsSporadic .M23 ↥L ∨ IsSporadic .J1 ↥L ∨ IsSporadic .J2 ↥L ∨ IsSporadic .J4 ↥L ∨
      IsSporadic .HS ↥L ∨ IsSporadic .Ru ↥L) : False := by
  rcases hL with (hM | ⟨-, hZ3, ⟨e⟩⟩) | hM | hM | hM | hM | hM | hM
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 7 * 3465 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · have hcL : Nat.card ↥L = 2 ^ 7 * 10395 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      have h2 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
        CFSG.Sporadic.Mathieu.card_M22
      rw [Nat.card_congr e.toEquiv, h2, hZ3] at h1
      rw [h1]
      norm_num
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 7 * 79695 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card CFSG.Blueprint.NativeSporadic.M23 = _
      rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
      exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
        CFSG.M23.M23Group.card_M23
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 3 * 21945 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 7 * 4725 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 21 * 41377816699065 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 9 * 86625 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)
  · obtain ⟨e⟩ := hM
    have hcL : Nat.card ↥L = 2 ^ 14 * 8906625 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    exact hc.false_of_card hcL (by decide) (by decide) (by decide)

theorem cmp
    (h314 : A314Facts) (hc : CmpHyp L X) {T B : Subgroup Q} (h : A314Statement T B L)
    (hBL : B < L) : IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ IsAlt 7 X := by
  obtain ⟨h13, h14⟩ := A7.not_a314_nonquasi hBL hc.quasi hc.center_odd
  unfold A314Statement at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13' | h14'
  · obtain ⟨-, -, hL, -⟩ := h1
    rcases hc.cmp_one hL with hL | hL | hL
    · exact Or.inl hL
    · exact Or.inr (Or.inl hL)
    · exact Or.inr (Or.inr (Or.inl hL))
  · obtain ⟨-, hL, -⟩ := h2
    exact Or.inr (Or.inr (Or.inr (hc.cmp_two hL)))
  · obtain ⟨-, hL⟩ := h3
    exact (hc.false_of_cmp_three h314 hL).elim
  · obtain ⟨-, ⟨s, hL⟩, -⟩ := h4
    cases s
    · exact (hc.false_of_cmp_three_five (Or.inr hL)).elim
    · exact (hc.false_of_cmp_three_five (Or.inl hL)).elim
  · obtain ⟨-, hL, -⟩ := h5
    exact (hc.false_of_cmp_three_five (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h6
    exact (hc.false_of_cmp_sporadic (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h7
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inl hL))).elim
  · obtain ⟨-, hL, -⟩ := h8
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inl hL)))).elim
  · obtain ⟨-, hL, -⟩ := h9
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inr (Or.inl hL))))).elim
  · obtain ⟨-, -, hL⟩ := h10
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))).elim
  · obtain ⟨-, hL, -⟩ := h11
    exact (hc.false_of_cmp_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))))).elim
  · obtain ⟨-, -, hL, -⟩ := h12
    exact (hc.false_of_cmp_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL))))))).elim
  · exact (h13 h13'.2).elim
  · obtain ⟨-, p, hp, -, hp8, hL⟩ := h14'
    exact (h14 p hp (by omega) hL).elim

end CmpHyp

end CFSG.Quasithin.H13.Ch9.FFB
