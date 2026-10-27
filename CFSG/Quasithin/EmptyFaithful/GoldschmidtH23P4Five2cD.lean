module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Five2cSN
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Main

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_odd_of_isSylowTwoOf {P S K : Subgroup G} (hS : IsSylowTwoOf S P) (hSK : S ≤ K)
    (hodd : ∀ x ∈ P, Odd (orderOf x) → x ∈ K) : P ≤ K := by
  have h : S ⊔ oTwoUpper P = P := by
    have := sup_twoResidual_eq hS
    rwa [F6.twoResidual_eq_oTwoUpper] at this
  rw [← h]
  refine sup_le hSK ?_
  unfold oTwoUpper
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxP, hxo⟩
  exact hodd x hxP hxo

omit [Finite G] in
theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {x : G} (hxA : x ∈ A)
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hxB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hxB h]
  refine and_congr_left fun _ => ?_
  constructor
  · intro hh
    exact A.mul_mem (A.mul_mem hxA hh) (A.inv_mem hxA)
  · intro hh
    have := A.mul_mem (A.mul_mem (A.inv_mem hxA) hh) hxA
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_inf_of_mem_cMod {L K : Subgroup G} (hQK : pCoreOf 2 L ≤ K) {y : G}
    (hy : y ∈ SBc17.cMod L) : y ∈ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  have key : ∀ z ∈ SBc17.cMod L, ∀ h ∈ K ⊓ L, z * h * z⁻¹ ∈ K ⊓ L := by
    intro z hz h hh
    obtain ⟨hzN, hzc⟩ := SBc17.mem_cMod.mp hz
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hzN h).mp hh.2⟩
    have hc : ⁅z, h⁆ ∈ pCoreOf 2 L := by
      have := hzc h hh.2
      have e : ⁅z, h⁆ = ⁅h, z⁆⁻¹ := (commutatorElement_inv h z).symm
      rw [e]
      exact (pCoreOf 2 L).inv_mem this
    have e : z * h * z⁻¹ = ⁅z, h⁆ * h := by simp [commutatorElement_def]
    rw [e]
    exact K.mul_mem (hQK hc) hh.1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key y hy h hh, fun hh => ?_⟩
  have := key y⁻¹ ((SBc17.cMod L).inv_mem hy) _ hh
  simpa [mul_assoc] using this

omit [Finite G] in
theorem conjAct_mem_autOn_of_mem {X V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hxX : x ∈ X) :
    conjAct V ⟨x, hx⟩ ∈ autOn X V :=
  mem_autOn_iff_exists.mpr ⟨x, hx, hxX, rfl⟩

omit [Finite G] in
theorem odd_orderOf_conjAct {V : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (ho : Odd (orderOf x)) : Odd (orderOf (conjAct V ⟨x, hx⟩)) := by
  have h1 := orderOf_map_dvd (conjAct V) (⟨x, hx⟩ : Subgroup.normalizer (V : Set G))
  rw [Subgroup.orderOf_mk] at h1
  exact ho.of_dvd_nat h1

theorem five2c_false_of_factor {T Mc M Z₁ Z₂ V₁ V₂ L Y : Subgroup G}
    (hC : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) (h3 : Case15122Three M Mc Z₁ L)
    (hYN : Y ≤ Subgroup.normalizer (L : Set G)) (hYc : Y ≤ SBc17.cMod L)
    (hfac : ∀ n ∈ M ⊓ g1_1516 Z₁, Odd (orderOf n) → ∃ y ∈ Y, y⁻¹ * n ∈ mZ1516 Mc Z₁) :
    False := by
  obtain ⟨-, -, hpar, hne, -, -, hgen⟩ := h3
  have hTM : T ≤ M := hC.ctx.mf.1.1.2
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := hC.h20.sylow
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ :=
    le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans hC.ctx.qtfe.t_le_mc)
  have hQML : pCoreOf 2 L ≤ mZ1516 Mc Z₁ := hsyl.pCoreOf_le.trans (inf_le_left.trans hSMZ)
  have hodd : ∀ n ∈ M ⊓ L, Odd (orderOf n) → n ∈ mZ1516 Mc Z₁ ⊓ L := by
    intro n hn hno
    have hnL : n ∈ L := hn.2
    have hnG1 : n ∈ g1_1516 Z₁ := le_of_mem_cComp hC.hL.comp hnL
    obtain ⟨y, hyY, hcMZ⟩ := hfac n ⟨hn.1, hnG1⟩ hno
    have hcNL : y⁻¹ * n ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hYN hyY)) (Subgroup.le_normalizer hnL)
    have hnN2 : n ∈ Subgroup.normalizer ((mZ1516 Mc Z₁ ⊓ L : Subgroup G) : Set G) := by
      have e : n = y * (y⁻¹ * n) := by group
      rw [e]
      exact Subgroup.mul_mem _ (mem_normalizer_inf_of_mem_cMod hQML (hYc hyY))
        (mem_normalizer_inf_of_mem hcMZ hcNL)
    exact mem_of_mem_normalizer_isParabolic2 hpar hnL hnN2
  have hSL_P : s1516 T Z₁ ⊓ L ≤ M ⊓ L := inf_le_inf_right L ((s1516_le T Z₁).trans hTM)
  have hSylP : IsSylowTwoOf (s1516 T Z₁ ⊓ L) (M ⊓ L) := by
    refine isSylowTwoOf_of_card_eq hSL_P hsyl.isPGroup (le_antisymm ?_ ?_)
    · exact card_le_twoPart hSL_P hsyl.isPGroup
    · rw [hsyl.card_eq]
      exact twoPart_mono inf_le_right
  have hP : M ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L :=
    le_of_odd_of_isSylowTwoOf hSylP (le_inf (inf_le_left.trans hSMZ) inf_le_right) hodd
  have hsup : (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = mZ1516 Mc Z₁ ⊓ L := sup_eq_left.mpr hP
  exact hne (hsup.symm.trans hgen)

theorem factor_of_prime_o2 {T Mc M Z₁ Z₂ V₁ V₂ Y : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (hX : Setting1516Extra T Mc M Z₁) (h5 : Ce15Six T Mc M 5)
    (hYM : Y ≤ M ⊓ g1_1516 Z₁) (hY5 : IsPGroup 5 Y) (hVY : ⁅V₂, Y⁆ = V₂) :
    ∀ n ∈ M ⊓ g1_1516 Z₁, Odd (orderOf n) → ∃ y ∈ Y, y⁻¹ * n ∈ mZ1516 Mc Z₁ := by
  have hSet := hC.setting
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    rw [hSet.hV]
    exact le_normalizer_VZ T M
  have hZV : (quasithinOmegaOneCenter T : Set G) ⊆ (V154 T Mc M : Set G) := by
    rw [hSet.hV]
    exact le_conjClosure _ _
  have hCV : Subgroup.centralizer (V154 T Mc M : Set G) ≤ Mc :=
    fun x hx => hC.qtfe.centralizer_le_mc (Subgroup.centralizer_le hZV hx)
  have hYle : autOn Y (V154 T Mc M) ≤
      oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)) := by
    intro φ hφ
    obtain ⟨y, hyN, hyY, rfl⟩ := mem_autOn_iff_exists.mp hφ
    exact mem_oTwoUpper_of_odd (conjAct_mem_autOn_of_mem hyN (hYM hyY))
      (odd_orderOf_conjAct hyN (odd_orderOf_of_isPGroup_five hY5 y hyY))
  have hYne : autOn Y (V154 T Mc M) ≠ ⊥ := by
    intro hbot
    have hYcent : Y ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
      intro y hy
      have hyN := hMN (hYM hy).1
      have h1 := conjAct_mem_autOn_of_mem (X := Y) hyN hy
      rw [hbot, Subgroup.mem_bot] at h1
      exact A4.conjAct_eq_one_iff.mp h1
    have hV2c : V₂ ≤ Subgroup.centralizer (Y : Set G) := by
      intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact ((Subgroup.mem_centralizer_iff.mp (hYcent hy)) v (hSet.v2_le hv)).symm
    have hcomm : ⁅V₂, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hV2c
    rw [hcomm] at hVY
    have h16 := (hSet.ranks_six ⟨5, Or.inr rfl, h5⟩).2.1
    rw [← hVY] at h16
    simp at h16
  have hprime : (Nat.card (oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)))).Prime :=
    hX.prime_o2
  have hYeq : autOn Y (V154 T Mc M) = oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)) := by
    have : Fact (Nat.card (oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)))).Prime := ⟨hprime⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((autOn Y (V154 T Mc M)).subgroupOf
        (oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)))) with h | h
    · exfalso
      apply hYne
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_self.mp (h.mono_right hYle)
    · exact le_antisymm hYle (Subgroup.subgroupOf_eq_top.mp h)
  intro n hn hno
  have hnN : n ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hMN hn.1
  have hbar : conjAct (V154 T Mc M) ⟨n, hnN⟩ ∈
      oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)) :=
    mem_oTwoUpper_of_odd (conjAct_mem_autOn_of_mem hnN hn) (odd_orderOf_conjAct hnN hno)
  rw [← hYeq] at hbar
  obtain ⟨y, hyN, hyY, hyeq⟩ := mem_autOn_iff_exists.mp hbar
  refine ⟨y, hyY, ?_⟩
  have hcN : y⁻¹ * n ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hnN
  have hcc : y⁻¹ * n ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
    rw [← A4.conjAct_eq_one_iff (g := ⟨y⁻¹ * n, hcN⟩)]
    have e : (⟨y⁻¹ * n, hcN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
        (⟨y, hyN⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ * ⟨n, hnN⟩ := rfl
    rw [e, map_mul, map_inv, hyeq, inv_mul_cancel]
  exact ⟨(g1_1516 Z₁).mul_mem ((g1_1516 Z₁).inv_mem (hYM hyY).2) hn.2, hCV hcc⟩

theorem five2c_false {T Mc M Z₁ Z₂ V₁ V₂ L Y : Subgroup G}
    (hC : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) (hX : Setting1516Extra T Mc M Z₁)
    (h5 : Ce15Six T Mc M 5)
    (h3 : Case15122Three M Mc Z₁ L) (hYM : Y ≤ M ⊓ g1_1516 Z₁) (hY5 : IsPGroup 5 Y)
    (hVY : ⁅V₂, Y⁆ = V₂) (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hYc : Y ≤ SBc17.cMod L) : False :=
  five2c_false_of_factor hC h3 hYN hYc (factor_of_prime_o2 hC.ctx hX h5 hYM hY5 hVY)

end CFSG.Quasithin.H23P4
