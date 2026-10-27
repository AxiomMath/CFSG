module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveMinimal
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem o2Trivial_autI_of_calC {M K V : Subgroup G} (hV : IsElemAbelian 2 V) (hK : K ∈ calC M)
    (hKN : K ≤ normalizer (V : Set G)) (hKV : ⁅K, V⁆ ≠ ⊥)
    (hOV : pCoreOf 2 K ≤ centralizer (V : Set G)) : O2Trivial (autI hV K) := by
  intro P hPB hPN hP2
  let f : ↥K →* MulAut (IntMod V hV) := convHom hV K hKN
  have hrange : f.range = autI hV K := range_convHom hV K hKN
  have hPle : P ≤ f.range := by rw [hrange]; exact hPB
  let Q : Subgroup ↥K := P.comap f
  have hPmap : Q.map f = P := Subgroup.map_comap_eq_self hPle
  have hBker : CFSG.pCore 2 ↥K ≤ f.ker := by
    rw [show f = convHom hV K hKN from rfl, ker_convHom]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, hOV ?_⟩
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.mem_map_of_mem _ hx
  have hBQ : CFSG.pCore 2 ↥K ≤ Q := hBker.trans (Subgroup.ker_le_comap f P)
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let N : Subgroup (Bar2 K) := Q.map π
  let fr : ↥K →* ↥(autI hV K) :=
    f.codRestrict (autI hV K) fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  have hQeq : Q = (P.subgroupOf (autI hV K)).comap fr := by
    ext x
    simp [Q, fr, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hQnormal : Q.Normal := by
    rw [hQeq]
    exact hPN.comap fr
  have hNnormal : N.Normal := hQnormal.map π (QuotientGroup.mk'_surjective _)
  have : N.Normal := hNnormal
  have : Finite (MulAut (IntMod V hV)) :=
    Finite.of_injective (fun e : MulAut (IntMod V hV) => (e : IntMod V hV → IntMod V hV))
      (fun e₁ e₂ h => DFunLike.ext e₁ e₂ fun x => congrFun h x)
  rcases CFSG.CGT.PushingUpLit.CGT6.Diag.Cons.normal_le_center_or_eq_top hK.2.2 N with
    hNcent | hNtop
  · let g : Bar2 K →* MulAut (IntMod V hV) := QuotientGroup.lift (CFSG.pCore 2 ↥K) f hBker
    have hg : g.comp π = f := QuotientGroup.lift_comp_mk' _ f hBker
    have hNmap : N.map g = P := by
      rw [show N.map g = Q.map (g.comp π) by rw [Subgroup.map_map], hg, hPmap]
    have hPdvdN : Nat.card P ∣ Nat.card N := hNmap ▸ Subgroup.card_map_dvd (H := N) g
    have hoddN : Odd (Nat.card N) :=
      (uc22p20p_odd_center_bar2 ↥K).of_dvd_nat (Subgroup.card_dvd_of_le hNcent)
    have hoddP : Odd (Nat.card P) := hoddN.of_dvd_nat hPdvdN
    have : Subsingleton ↥P :=
      CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd (G := ↥P) hP2 hoddP
    refine (Subgroup.eq_bot_iff_forall P).2 fun p hp => ?_
    have h1 : (⟨p, hp⟩ : ↥P) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h1
  · have hQtop : Q = ⊤ := by
      have h1 : Q ⊔ CFSG.pCore 2 ↥K = ⊤ := by
        have h := Subgroup.comap_map_eq (f := π) Q
        rw [show Q.map π = N from rfl, hNtop, Subgroup.comap_top,
          QuotientGroup.ker_mk'] at h
        exact h.symm
      rw [sup_eq_left.mpr hBQ] at h1
      exact h1
    have hPtop : P = autI hV K := by
      rw [← hPmap, hQtop, Subgroup.map_top, hrange]
    have hP2' : IsPGroup 2 ↥(autI hV K) := hPtop ▸ hP2
    have hne : autI hV K ≠ ⊥ := by
      intro hbot
      exact hKV (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((autI_eq_bot_iff hV hKN).1 hbot))
    have : Nontrivial ↥(autI hV K) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hperf : Group.IsPerfect ↥(autI hV K) := by
      have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK.2.1
      have h := Group.IsPerfect.range f
      rwa [range_convHom] at h
    exact absurd hP2'.isNilpotent (Group.IsPerfect.not_isNilpotent ↥(autI hV K))

theorem twoReduced_of_min_of_o2Trivial_autI {D : Data G} {K V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hKM : K ≤ D.M) (hKN : D.M ≤ normalizer (K : Set G))
    (hMV : D.M ≤ normalizer (V : Set G)) (hVU : V ≤ D.U) (hKV : ⁅K, V⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
      ⁅K, W⁆ ≠ ⊥ → W = V)
    (hB : O2Trivial (autI hV K)) : TwoReduced D.M V := by
  intro R hRM hMR hCR hIdx
  set C : Subgroup G := Subgroup.centralizer (V : Set G)
  have hKleN : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMV
  have hRleN : R ≤ Subgroup.normalizer (V : Set G) := hRM.trans hMV
  have hA2 : IsPGroup 2 (autI hV R) := by
    obtain ⟨n, hn⟩ := hIdx
    apply IsPGroup.of_card (n := n)
    rw [card_autI_eq hV hRleN]
    have hsub : (R ⊓ C).subgroupOf R = C.subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [show (R ⊓ C).relIndex R = ((R ⊓ C).subgroupOf R).index from rfl, hsub, hn]
  have hI_normal : ((autI hV (K ⊓ R)).subgroupOf (autI hV K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (autI_mono hV inf_le_left)]
    refine (Subgroup.le_normalizer_iff).2 fun a ha b hb => ?_
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 ha
    obtain ⟨k, hk, rfl⟩ := (mem_autI hV).1 hb
    refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, ?_⟩
    · refine ⟨K.mul_mem (K.mul_mem hgK hk.1) (K.inv_mem hgK), ?_⟩
      exact (Subgroup.mem_normalizer_iff.1 (hMR (hKM hgK)) (k : G)).1 hk.2
    · simp
  have hI2 : IsPGroup 2 (autI hV (K ⊓ R)) := hA2.to_le (autI_mono hV inf_le_right)
  have hIbot : autI hV (K ⊓ R) = ⊥ :=
    hB (autI hV (K ⊓ R)) (autI_mono hV inf_le_left) hI_normal hI2
  have hKC : K ⊓ R ≤ C :=
    (autI_eq_bot_iff hV (inf_le_left.trans hKleN)).1 hIbot
  have hcommKR : ⁅K, R⁆ ≤ K ⊓ R := by
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hRM.trans hKN)
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKM.trans hMR)
  have hcomm : ⁅K, R⁆ ≤ C := hcommKR.trans hKC
  obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ C := by
    by_contra h
    push Not at h
    exact hKV (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  by_contra hRle
  set Vfix : Subgroup G := V ⊓ Subgroup.centralizer (R : Set G)
  have hVfixU : Vfix ≤ D.U := inf_le_left.trans hVU
  have hVfixM : D.M ≤ Subgroup.normalizer (Vfix : Set G) := fun m hm =>
    CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMR hm) (hMV hm)
  have hVfix_le : Vfix ≤ V := inf_le_left
  have hVfix_ne : Vfix ≠ V := by
    intro h
    apply hRle
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvfix : v ∈ Vfix := by rw [h]; exact hv
    exact ((Subgroup.mem_inf.1 hvfix).2 r hr).symm
  have hKVfix : ⁅K, Vfix⁆ = ⊥ := by
    by_contra hne
    exact hVfix_ne (hmin Vfix hVfixU hVfixM hVfix_le hne)
  have hKFix : K ≤ Subgroup.centralizer (Vfix : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKVfix
  have hAB : ∀ a ∈ autI hV R, ∀ b ∈ autI hV K, a * b = b * a :=
    CFSG.Quasithin.H13.autOn_commute (by rwa [Subgroup.commutator_comm] at hcomm)
  have hW2 : IsPGroup 2 (IntMod V hV) :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV
  have hkN : (k : G) ∈ Subgroup.normalizer (V : Set G) := hKleN hkK
  let kN : Subgroup.normalizer (V : Set G) := ⟨k, hkN⟩
  have hb : convI hV kN ∈ autI hV K := convI_mem_autI hV hkK hkN
  have hfix : ∀ w : IntMod V hV, (∀ a ∈ autI hV R, a w = w) → convI hV kN w = w := by
    intro w hw
    have hwCR : w.val ∈ Subgroup.centralizer (R : Set G) :=
      (mem_fixV_autI hV hRleN w).1 hw
    have hwVfix : w.val ∈ Vfix := ⟨w.val_mem, hwCR⟩
    refine IntMod.val_injective ?_
    rw [convI_apply_val]
    have hcent := Subgroup.mem_centralizer_iff.1 (hKFix hkK) w.val hwVfix
    rw [← hcent]
    change w.val * k * k⁻¹ = w.val
    group
  have h1 : convI hV kN = 1 :=
    CFSG.GroupTheory.eq_one_of_forall_fixed_of_commute (p := 2) hW2 hA2 hAB hB hb hfix
  exact hkC ((convI_eq_one_iff hV kN).1 h1)

theorem exists_inCalW_min_of_normal {D : Data G} {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKN : D.M ≤ normalizer (K : Set G)) (hUT : UniqueMax D.M (K ⊔ D.T))
    (hKZ : ⁅K, D.Z⁆ ≠ ⊥) :
    ∃ V : Subgroup G, ∃ hV : IsElemAbelian 2 V, V ≤ D.U ∧ D.M ≤ normalizer (V : Set G) ∧
      ⁅K, V⁆ ≠ ⊥ ∧
      (∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
        ⁅K, W⁆ ≠ ⊥ → W = V) ∧
      InCalW D.M D.T V ∧ pCoreOf 2 K ≤ centralizer (V : Set G) ∧
      IsBasicModule (Mbar D.M ⊥ V hV) ∧ O2Trivial (Mbar D.M ⊥ V hV) := by
  obtain ⟨V, hVU, hMV, hKV, hmin⟩ := S17.seventeen_fiftyfive_min_base hKZ
  have hKM : K ≤ D.M := hK.1.le
  have hVM : V ≤ D.M := hVU.trans (uc22p22e_uCore_le D.sylowM.le)
  have hVel : IsElemAbelian 2 V :=
    uc22p22n_isElemAbelian_of_le hVU (uc22p22e_inCalV_U D).2.2.2
  have hVne : V ≠ ⊥ := by
    intro h
    exact hKV (by rw [h, Subgroup.commutator_bot_right])
  have h8 : 8 ≤ Nat.card V := by
    by_contra hlt
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hVel)
    have h4 : Nat.card V ≤ 4 := by
      rw [hn] at hlt ⊢
      have h2 : n ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ n := by omega
        have h4 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
        omega
      exact Nat.pow_le_pow_right (by norm_num) h2
    have hcent := CFSG.SeitzReduction.LinearPilot.le_centralizer_of_perfect_of_card_le_four
      hK.2.1 (hKM.trans hMV) h4
    exact hKV (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  have hVinCalV : InCalV D.M V := ⟨hVne, hVM, hMV, hVel⟩
  have hVinCalV1 : InCalV1 D.M D.T V :=
    inCalV1_of_commutator_ne_bot hVinCalV hK hKN hUT hKV
  have hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    S17.seventeen_fiftyfive_min_pCore_le_centralizer hK hVU
  have hB : O2Trivial (autI hVel K) :=
    o2Trivial_autI_of_calC hVel hK (hKM.trans hMV) hKV hOV
  have hTwo : TwoReduced D.M V :=
    twoReduced_of_min_of_o2Trivial_autI hVel hKM hKN hMV hVU hKV hmin hB
  have hW : InCalW D.M D.T V := ⟨hVinCalV1, h8, hTwo⟩
  have hBasic : IsBasicModule (Mbar D.M ⊥ V hVel) :=
    S17.seventeen_fiftyfive_min_isBasicModule hVel hKM hMV hVU hKV hmin
  have hO2 : O2Trivial (Mbar D.M ⊥ V hVel) :=
    S17.o2Trivial_mbar_of_twoReduced hVel hMV hTwo
  exact ⟨V, hVel, hVU, hMV, hKV, hmin, hW, hOV, hBasic, hO2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
