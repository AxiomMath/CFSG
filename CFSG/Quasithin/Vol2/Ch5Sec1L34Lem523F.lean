module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Thm4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Abstract

variable {W : Type*} [CommGroup W] [Finite W]

theorem false_of_le_of_isSolvable (hW : ∀ w : W, w ^ 2 = 1) {X C A : Subgroup (MulAut W)}
    {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r < 2) (hA : A ∈ QhatStar X)
    (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set (MulAut W)))
    (hO2 : pCoreOf 2 X = ⊥) (h3 : ¬ 3 ∣ Nat.card C) (hsolv : Group.IsSolvable ↥C)
    (hAC : A ≤ C) : False := by
  classical
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hA2p : IsPGroup 2 ↥A := hA2.2.2.isPGroup
  have hCp : ∀ p : ℕ, p.Prime → pCoreOf p C ≤ pCoreOf p X := fun p hp => by
    have : Fact p.Prime := ⟨hp⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p ((pCoreOf_le p C).trans hCX)
      (hXC.trans (normalizer_le_normalizer_pCoreOf p C)) (pCoreOf_isPGroup p C)
  have hcore : ∀ p : ℕ, p.Prime → p ∣ Nat.card C →
      pCoreOf p C ≤ Subgroup.centralizer (A : Set (MulAut W)) := by
    intro p hp hpC
    have : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst hp2
      have hle := hCp 2 hp
      rw [hO2] at hle
      exact hle.trans bot_le
    · have hbot : ⁅pCoreOf p X, A⁆ = ⊥ := by
        by_contra hne
        obtain ⟨h35, h5, -⟩ := D2_13 hW hr hA hp2 rfl hne
        rcases h35 with rfl | rfl
        · exact h3 hpC
        · have e := (h5 rfl).1
          rw [e] at hr2
          exact lt_irrefl _ hr2
      exact (hCp p hp).trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  set A' := A.subgroupOf C with hA'
  have hFA : CFSG.fittingSubgroup ↥C ≤ Subgroup.centralizer (A' : Set ↥C) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxC : (x : MulAut W) ∈ pCoreOf (p : ℕ) C := by
      refine ⟨x, ?_, rfl⟩
      assumption
    have hpC : (p : ℕ) ∣ Nat.card C := Nat.dvd_of_mem_primeFactors p.2
    have hc := Subgroup.mem_centralizer_iff.mp
      (hcore p (Nat.prime_of_mem_primeFactors p.2) hpC hxC) a (Subgroup.mem_subgroupOf.mp ha)
    exact Subtype.ext hc
  have hA'F : A' ≤ CFSG.fittingSubgroup ↥C :=
    (Subgroup.le_centralizer_iff.mpr hFA).trans
      (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hA'2 : IsPGroup 2 ↥A' := hA2p.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  have hA'O : A' ≤ CFSG.pCore 2 ↥C :=
    (le_inf le_rfl hA'F).trans (CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore A'
      (CFSG.fittingSubgroup ↥C) 2 Nat.prime_two hA'2 CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent)
  have hAO : A ≤ pCoreOf 2 C := by
    intro a ha
    refine ⟨⟨a, hAC ha⟩, ?_, rfl⟩
    exact hA'O (Subgroup.mem_subgroupOf.mpr ha)
  have hAX := hAO.trans (hCp 2 Nat.prime_two)
  rw [hO2, le_bot_iff] at hAX
  exact hA2.2.1 hAX

end Abstract

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

theorem autOn_le_normalizer_autOn_of_normalizes {Γ : Type*} [Group Γ] [Finite Γ]
    {X Y W : Subgroup Γ} (hXY : X ≤ Subgroup.normalizer (Y : Set Γ)) :
    autOn X W ≤ Subgroup.normalizer (autOn Y W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXY

theorem commutator_mem_centralizer_of_mem_centralizer_autOn {Γ : Type*} [Group Γ]
    {W Y : Subgroup Γ} {x : Γ} (hxN : x ∈ Subgroup.normalizer (W : Set Γ))
    (hac : conjAct W ⟨x, hxN⟩ ∈ Subgroup.centralizer (autOn Y W : Set (MulAut ↥W)))
    {k : Γ} (hk : k ∈ Y) (hkN : k ∈ Subgroup.normalizer (W : Set Γ)) :
    x * k * x⁻¹ * k⁻¹ ∈ Subgroup.centralizer (W : Set Γ) := by
  have hl : conjAct W ⟨k, hkN⟩ ∈ autOn Y W :=
    Subgroup.mem_map.mpr ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hac _ hl
  have hg1 : conjAct W (⟨x, hxN⟩ * ⟨k, hkN⟩ * ⟨x, hxN⟩⁻¹ * ⟨k, hkN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := conjAct_coe_apply W (⟨x, hxN⟩ * ⟨k, hkN⟩ * ⟨x, hxN⟩⁻¹ * ⟨k, hkN⟩⁻¹) ⟨w, hw⟩
  rw [hg1, MulAut.one_apply] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have h2 := congrArg (· * (x * k * x⁻¹ * k⁻¹)) h1
  simp only [inv_mul_cancel_right] at h2
  exact h2

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem almostSpecialHyp_G₁ (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    AlmostSpecialHyp (conjClosure Z₁ D₃) Z₁ ⊥ T (Subgroup.centralizer (Z₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hTG₁ : T ≤ Subgroup.centralizer (Z₁ : Set G) :=
    s.hyp.hyp.hStar.1.1.trans (s.H_le_centralizer h5114)
  have hl1 : lOne (⊥ : Subgroup G) Z₁ = ⊥ := le_bot_iff.mp ((oTwoUpper_le _).trans inf_le_left)
  have hZ1T : Z₁ ≤ T := s.Z₁_le_Z.trans (quasithinOmegaOneCenter_le_self T)
  have hZ1O : Z₁ ≤ pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZ1T.trans hTG₁)
      (Subgroup.centralizer_le_normalizer _) (hh.sylow.1.to_le hZ1T)
  have hO₁ : pCoreOf 2 (Subgroup.centralizer (Z₁ : Set G)) ≠ ⊥ := fun hb => by
    have := hZ1O hz
    rw [hb, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hSG₁ : (S : Subgroup G) ≤ Subgroup.centralizer (Z₁ : Set G) := by rw [hS]; exact hTG₁
  exact
    { elemAbelian := s.isElemAbelian_V₂
      ne_bot := fun hb => hz1 (by rw [hb] at hz; exact Subgroup.mem_bot.mp hz)
      le_V := le_conjClosure Z₁ D₃
      oTwo_eq := (le_bot_iff.mp (oTwoUpper_le ⊥)).symm
      V_le_T := s.V₂_le_T
      T_le_normV₁ := s.T_le_normalizer_Z₁
      T_le_normV := s.T_le_normalizer_V₂ hF
      T_le_normL := fun t _ => Subgroup.mem_normalizer_iff.mpr fun x => by
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro hx
          have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
          rw [e, hx]
          group
      sylow_LT := by
        rw [bot_sup_eq]
        exact hh.isSylowTwoOf le_rfl
      H_le := Subgroup.centralizer_le_normalizer _
      lOne_sup_le := by
        rw [hl1, bot_sup_eq]
        exact hTG₁
      sylow_H := hh.isSylowTwoOf hTG₁
      charTwo := charTwo_of_le hh.qtke.2.1 S hSG₁ le_rfl ⟨hSG₁, hO₁⟩
      irred := by
        rw [hl1, bot_sup_eq]
        exact ⟨s.Z₁_lt_V₂ hz hz1 hd hd1 h5114, s.T_le_normalizer_V₂ hF, s.T_le_normalizer_Z₁,
          fun W hW1 hW2 _ => s.eq_or_eq hz hz1 hd hd1 h5114 hF hW1 hW2⟩ }

end Setup521

end Setting

end CFSG.Quasithin.H13
