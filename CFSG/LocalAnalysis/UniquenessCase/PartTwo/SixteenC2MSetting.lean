module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def s16c2m_FamilyJ {W : Type} [CommGroup W] (L L₀ : Subgroup (MulAut W))
    (J₀ J₁ : Subgroup W) : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ IsSym ↥L₀ n ∧ IsAlt ↥L n ∧ 4 ≤ rk ↥J₀ ∧
      AlternatingNatural L J₀ ⊥ n ∧ AlternatingNatural L J₁ ⊥ n) ∨
    (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ IsLn ↥L₀ m 1 ∧ IsLn ↥L m 1 ∧
      BinaryNaturalSL L J₀ ⊥ m 1 ∧ BinaryNaturalSL L J₁ ⊥ m 1 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) L ⊤ ⊥ 2) ∨
    (IsSpn ↥L₀ 6 1 ∧ IsSpn ↥L 6 1 ∧ 4 ≤ rk ↥J₀ ∧ NatSpn L J₀ ⊥ 6 1 ∧ NatSpn L J₁ ⊥ 6 1) ∨
    (IsOMinus ↥L₀ 6 1 ∧ IsOmegaMinus ↥L 6 1 ∧ 4 ≤ rk ↥J₀ ∧
      NatOmegaMinus L J₀ ⊥ 6 1 ∧ NatOmegaMinus L J₁ ⊥ 6 1) ∨
    (IsOMinus ↥L₀ 8 1 ∧ IsOmegaMinus ↥L 8 1 ∧ 4 ≤ rk ↥J₀ ∧
      NatOmegaMinus L J₀ ⊥ 8 1 ∧ NatOmegaMinus L J₁ ⊥ 8 1)

variable {G : Type} [Group G] [Finite G]

private theorem s16c2m_center_of_isSym_three {A : Type} [Group A] (h : IsSym A 3) :
    ∀ κ : A, (∀ y : A, y * κ = κ * y) → κ = 1 := by
  obtain ⟨e⟩ := h
  intro κ hκ
  have hc : ∀ y : Equiv.Perm (Fin 3), y * e κ = e κ * y := by
    intro y
    have h1 := congrArg e (hκ (e.symm y))
    simpa using h1
  have hs : ∀ σ : Equiv.Perm (Fin 3), (∀ y : Equiv.Perm (Fin 3), y * σ = σ * y) → σ = 1 := by
    decide
  exact e.injective (by rw [hs _ hc, map_one])

theorem s16c2m_setting (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h2 : Case168_2 D V₀ V hV L) :
    ∃ (L₀ : Subgroup (MulAut (Vtil V₀ V hV))) (J₀ J₁ : Subgroup (Vtil V₀ V hV)),
      Cfg2Setting (Mbar D.M V₀ V hV) (lBar V₀ V hV L) J₀ J₁ ∧
      lBar V₀ V hV L ≤ Mbar D.M V₀ V hV ∧ kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV ∧
      (∀ k ∈ kBar D.M V₀ V hV L, ∀ l ∈ lBar V₀ V hV L, k * l = l * k) ∧
      IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
      lBar V₀ V hV L ≤ L₀ ∧
      Z391.EndUnitsTrivial (lBar V₀ V hV L) J₀ ∧ Z391.EndUnitsTrivial (lBar V₀ V hV L) J₁ ∧
      s16c2m_FamilyJ (lBar V₀ V hV L) L₀ J₀ J₁ := by
  have hK : IsSym ↥(kBar D.M V₀ V hV L) 3 := h2.1
  obtain ⟨L₀, hI, hfam⟩ := h2.2.1
  have key : ∃ J₀ J₁ : Subgroup (Vtil V₀ V hV),
      J₀ ∈ irrSet (lBar V₀ V hV L) ∧ J₁ ∈ irrSet (lBar V₀ V hV L) ∧
      J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ ∧
      Z391.EndUnitsTrivial (lBar V₀ V hV L) J₀ ∧ Z391.EndUnitsTrivial (lBar V₀ V hV L) J₁ ∧
      s16c2m_FamilyJ (lBar V₀ V hV L) L₀ J₀ J₁ := by
    rcases hfam with ⟨n, hn5, hn11, hL₀, hL, hsum⟩ | ⟨m, hm3, hm5, hL₀, hL, hsum⟩ |
        ⟨hL₀, hL, hsum⟩ | ⟨hL₀, hL, hsum⟩ | ⟨hL₀, hL, hsum⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      have hrk : 4 ≤ rk ↥J₀ := by
        rcases Nat.even_or_odd n with ⟨r, hr⟩ | ho
        · have := s16c1610_le_rk_alternatingNatural (by omega) hN₀
          omega
        · have := s16c1610_rk_alternatingNatural_odd ho hN₀
          omega
      exact ⟨J₀, J₁, s16c167_mem_irrSet_alt hn5 hN₀, s16c167_mem_irrSet_alt hn5 hN₁, hinf, hsup,
        s16c167_endUnits_alt hn5 hN₀, s16c167_endUnits_alt hn5 hN₁,
        Or.inl ⟨n, hn5, hn11, hL₀, hL, hrk, hN₀, hN₁⟩⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      exact ⟨J₀, J₁, s16c167_mem_irrSet_ln (by omega) hN₀, s16c167_mem_irrSet_ln (by omega) hN₁,
        hinf, hsup, s16c167_endUnits_ln hm3 hN₀, s16c167_endUnits_ln hm3 hN₁,
        Or.inr (Or.inl ⟨m, hm3, hm5, hL₀, hL, hN₀, hN₁, hsum⟩)⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      have hrk : 4 ≤ rk ↥J₀ := by
        have := s16c1610_rk_natSpn hN₀
        omega
      exact ⟨J₀, J₁, s16c167_mem_irrSet_sp (by norm_num) hN₀,
        s16c167_mem_irrSet_sp (by norm_num) hN₁, hinf, hsup,
        s15k_abs_endUnits_sp (by norm_num) hN₀, s15k_abs_endUnits_sp (by norm_num) hN₁,
        Or.inr (Or.inr (Or.inl ⟨hL₀, hL, hrk, hN₀, hN₁⟩))⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      have hrk : 4 ≤ rk ↥J₀ := by
        have := s16c1610_rk_natOmegaMinus (by norm_num) hN₀
        omega
      exact ⟨J₀, J₁, s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₀,
        s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₁, hinf, hsup,
        s15k_abs_endUnits_omegaMinus (by norm_num) hN₀,
        s15k_abs_endUnits_omegaMinus (by norm_num) hN₁,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨hL₀, hL, hrk, hN₀, hN₁⟩)))⟩
    · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
      have hrk : 4 ≤ rk ↥J₀ := by
        have := s16c1610_rk_natOmegaMinus (by norm_num) hN₀
        omega
      exact ⟨J₀, J₁, s16c167_mem_irrSet_omegaMinus (Or.inr rfl) hN₀,
        s16c167_mem_irrSet_omegaMinus (Or.inr rfl) hN₁, hinf, hsup,
        s15k_abs_endUnits_omegaMinus (by norm_num) hN₀,
        s15k_abs_endUnits_omegaMinus (by norm_num) hN₁,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨hL₀, hL, hrk, hN₀, hN₁⟩)))⟩
  obtain ⟨J₀, J₁, hJ0, hJ1, hinf, hsup, hE₀, hE₁, hfamJ⟩ := key
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16c167_cfg2_simple D h2
  have hfix : fixV (lBar V₀ V hV L) = ⊥ := s16c167_cfg2_fix D h2
  have hLbot : lBar V₀ V hV L ≠ ⊥ := by
    haveI := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hall : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    refine top_le_iff.1 (hsup.symm.le.trans (sup_le ?_ ?_))
    · calc J₀ = commSub J₀ (lBar V₀ V hV L) := hJ0.1.symm
        _ ≤ commSub ⊤ (lBar V₀ V hV L) := commSub_mono le_top le_rfl
    · calc J₁ = commSub J₁ (lBar V₀ V hV L) := hJ1.1.symm
        _ ≤ commSub ⊤ (lBar V₀ V hV L) := commSub_mono le_top le_rfl
  have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hc.setting.hyp151.le
  have hnorm : ∀ x ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = lBar V₀ V hV L := by
    obtain ⟨t, -, -, -, -, hW136⟩ := hc.conc
    exact s16c167_cfg2_normal hLbot hall hW136
  have hcenter : ∀ κ ∈ kBar D.M V₀ V hV L,
      (∀ y ∈ kBar D.M V₀ V hV L, y * κ = κ * y) → κ = 1 := by
    intro κ hκ hcomm
    have h1 := s16c2m_center_of_isSym_three hK ⟨κ, hκ⟩ (fun y => Subtype.ext (hcomm y y.2))
    simpa using congrArg Subtype.val h1
  have hperf : ⁅lBar V₀ V hV L, lBar V₀ V hV L⁆ = lBar V₀ V hV L :=
    s16c167_cfg2_perfect hLX hsimple rfl hcenter
  have F : Cfg2Setting (Mbar D.M V₀ V hV) (lBar V₀ V hV L) J₀ J₁ :=
    ⟨hW, hnorm, hsimple, hperf, hfix, hJ0, hJ1, hinf, hsup⟩
  have hKX : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    fun _ hx => (Subgroup.mem_inf.1 hx).1
  have hKL : ∀ k ∈ kBar D.M V₀ V hV L, ∀ l ∈ lBar V₀ V hV L, k * l = l * k := by
    intro k hk l hl
    rw [kBar, Subgroup.mem_inf] at hk
    exact ((Subgroup.mem_centralizer_iff.1 hk.2) l hl).symm
  have hKL0 : ∀ k ∈ kBar D.M V₀ V hV L, ∀ l ∈ L₀, k * l = l * k := by
    intro k hk l hl
    have hkcent : k ∈ Subgroup.centralizer (L₀ : Set (MulAut (Vtil V₀ V hV))) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hI.1) hk
    exact (Subgroup.mem_centralizer_iff.1 hkcent l hl).symm
  have hle : lBar V₀ V hV L ≤ L₀ := by
    intro x hx
    have hxsup : x ∈ kBar D.M V₀ V hV L ⊔ L₀ := hI.2.2.symm ▸ hLX hx
    obtain ⟨κ, hκ, l, hl, hκl⟩ := s16c2m_exists_mul_of_mem_sup hKL0 hxsup
    have hκc : ∀ y ∈ kBar D.M V₀ V hV L, y * κ = κ * y := by
      intro y hy
      have hyx : y * x = x * y := hKL y hy x hx
      have hyl : y * l = l * y := hKL0 y hy l hl
      have hκeq : κ = x * l⁻¹ := by rw [← hκl]; group
      rw [hκeq]
      calc y * (x * l⁻¹) = (y * x) * l⁻¹ := by group
        _ = (x * y) * l⁻¹ := by rw [hyx]
        _ = x * (y * l⁻¹) := by group
        _ = x * (l⁻¹ * y) := by rw [(Commute.inv_right (show Commute y l from hyl)).eq]
        _ = (x * l⁻¹) * y := by group
    have hκ1 : κ = 1 := hcenter κ hκ hκc
    rw [← hκl, hκ1, one_mul]
    exact hl
  exact ⟨L₀, J₀, J₁, F, hLX, hKX, hKL, hK, hI, hle, hE₀, hE₁, hfamJ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
