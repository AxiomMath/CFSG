module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvolutionProduct
public import CFSG.LocalAnalysis.WeakClosure81.SevenThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem config17_26a_II_false_of_center
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V)
    (hKF2 : Inputs1719.K_J2_involution_product) (hJ2 : IsSpor (Bar2 L) .J2)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hAO : ¬ A ≤ pCoreOf 2 (L ⊔ D.T))
    (hAO2 : (pCoreOf 2 (L ⊔ D.T)).relIndex A ≤ 2)
    (hZ : A ⊓ centerOf (E3.wClos A 2 (pCoreOf 2 (L ⊔ D.T))) ≠ ⊥) : False := by
  classical
  have hV0el : IsElemAbelian 2 V₀ := c.hyp125.pairFacts.elemAbelian₀
  rw [E3.mem_gammaSet_iff] at hA
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hVg2 : IsPGroup 2 (conjSubgroup V₀ g) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup' hV0el g)
  have hAeq : A = conjSubgroup V₀ g := (E3.mQuot_eq_zero_iff hVg2 hAg).mp hmq
  have hAel : IsElemAbelian 2 A := by rw [hAeq]; exact isElemAbelian_conjSubgroup' hV0el g
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    apply hZ
    have hAbot : A = ⊥ := by
      rw [hAeq, hbot]
      simp [conjSubgroup]
    rw [hAbot]
    simp
  have hTI0 : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.2.2.2.1
  let H : Subgroup G := L ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  let W : Subgroup G := E3.wClos A 2 Q
  let E : Subgroup G := centerOf W
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hEH : E ≤ H := (inf_le_left.trans (E3.wClos_le (V := A) 2 Q)).trans hQH
  have hHnormW : H ≤ Subgroup.normalizer (W : Set G) :=
    hHnormQ.trans (E3.normalizer_le_normalizer_wClos (V := A) (i := 2) Q)
  have hHnormE : H ≤ Subgroup.normalizer (E : Set G) :=
    hHnormW.trans (E3.normalizer_le_normalizer_centerOf W)
  have hEab : IsMulCommutative ↥E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.1 b.2.2 (a : G) a.2.1
  have hAω : A ∈ omegaSet V₀ H E := by
    refine ⟨g, hAeq, ?_, hAO⟩
    rw [inf_comm]
    exact hZ
  have hAH : A ≤ H := hAT.trans le_sup_right
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := Set.not_subset.1 hAO
  have ha₀H : a₀ ∈ H := hAH ha₀A
  have hQA2 : Q.relIndex A = 2 := by
    have h2 : Q.relIndex A ≤ 2 := hAO2
    have h1 : Q.relIndex A ≠ 1 := fun h => hAO (Subgroup.relIndex_eq_one.1 h)
    have h0 : Q.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hsupA : A ≤ Q ⊔ Subgroup.zpowers a₀ :=
    CFSG.QuasithinUnique.le_sup_zpowers_of_relIndex_two hQA2 ha₀A ha₀Q
  set Y : Subgroup (MulAut (Vtil V₀ V c.hyp125.isElemAbelian)) :=
    barSub V₀ V c.hyp125.isElemAbelian H with hYdef
  set K : Subgroup ↥Y := (barSub V₀ V c.hyp125.isElemAbelian L).subgroupOf Y with hKdef
  set f : ↥H →* ↥Y := gap17_25_action c.hyp125 c with hfdef
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
    gap17_25_barSub_L_ne_bot c h20 hC117
  have hKn : K.Normal := gap17_25_barSub_normal c hMnorm
  have hKspor : IsSpor ↥K .J2 := gap17_25_barSub_isSpor c hJ2 hL1
  have hsurj : Function.Surjective f := gap17_25_action_surjective c
  set a : ↥Y := f ⟨a₀, ha₀H⟩ with hadef
  have haa : a * a = 1 := by
    have hxx : (⟨a₀, ha₀H⟩ : ↥H) * ⟨a₀, ha₀H⟩ = 1 := by
      apply Subtype.ext
      have h := hAel.2 a₀ ha₀A
      simpa [pow_two] using h
    rw [hadef, ← map_mul, hxx, map_one]
  have haQ' : a ∉ Subgroup.centralizer (K : Set ↥Y) := by
    intro hc
    have hmem : (⟨a₀, ha₀H⟩ : ↥H) ∈ (Subgroup.centralizer (K : Set ↥Y)).comap f := hc
    have hN : ((Subgroup.centralizer (K : Set ↥Y)).comap f).Normal :=
      Subgroup.Normal.comap Subgroup.normal_centralizer f
    have hpg : IsPGroup 2 ↥((Subgroup.centralizer (K : Set ↥Y)).comap f) :=
      gap17_25_comap_centralizer_isPGroup c h20 hC117 hJ2
    have hcore : ((Subgroup.centralizer (K : Set ↥Y)).comap f).map H.subtype ≤ Q :=
      Subgroup.map_mono (CFSG.LieType.BorelTits.le_pCore 2 hN hpg)
    exact ha₀Q (hcore (Subgroup.mem_map.mpr ⟨⟨a₀, ha₀H⟩, hmem, rfl⟩))
  have hnc : ∃ k ∈ K, a * k ≠ k * a := by
    by_contra h
    apply haQ'
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    by_contra hne
    exact h ⟨k, hk, fun h' => hne h'.symm⟩
  obtain ⟨y, hyK, hy4⟩ := hKF2 ↥Y K hKn hKspor a haa hnc
  obtain ⟨x, hx⟩ := hsurj y
  rw [← hx] at hy4
  have hxH : (x : G) ∈ H := x.2
  have hQxnorm : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hHnormQ hxH
  have hAxQ : ¬ conjSubgroup A x ≤ Q := by
    intro hle
    apply hAO
    have hQinv : conjSubgroup Q (x : G)⁻¹ = Q :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (inv_mem hQxnorm)
    have hAeqx : A = conjSubgroup (conjSubgroup A x) (x : G)⁻¹ := by
      rw [E3.conjSubgroup_conj_inv]
    rw [hAeqx]
    exact (E3.conjSubgroup_mono_left (x : G)⁻¹ hle).trans (le_of_eq hQinv)
  have hAxE : E ⊓ conjSubgroup A x ≠ ⊥ := by
    intro hbot
    apply hZ
    have hmap := Subgroup.map_inf_eq A E (MulAut.conj ((x : G)⁻¹)).toMonoidHom
      (MulAut.conj ((x : G)⁻¹)).injective
    have hfix : E.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom = E := by
      simpa [conjSubgroup] using
        (conjSubgroup_eq_iff_mem_normalizer.mpr (hHnormE hxH))
    have hzero : conjSubgroup (A ⊓ E) (x : G) = ⊥ := by
      rw [show conjSubgroup (A ⊓ E) (x : G) =
          (A ⊓ E).map (MulAut.conj ((x : G)⁻¹)).toMonoidHom from rfl, hmap, hfix, inf_comm]
      exact hbot
    have hAE : A ⊓ E = ⊥ := by
      have := congrArg (fun U => conjSubgroup U (x : G)⁻¹) hzero
      rw [E3.conjSubgroup_conj_inv] at this
      simpa [conjSubgroup] using this
    exact hAE
  have hAxω : conjSubgroup A x ∈ omegaSet V₀ H E := by
    refine ⟨g * (x : G), ?_, hAxE, hAxQ⟩
    rw [hAeq, conjSubgroup_conjSubgroup]
  set e : G := (x : G)⁻¹ * a₀ * (x : G) with hedef
  have heAx : e ∈ conjSubgroup A x := by
    rw [mem_conjSubgroup_iff]
    show (x : G) * e * (x : G)⁻¹ ∈ A
    rw [hedef]
    have : (x : G) * ((x : G)⁻¹ * a₀ * (x : G)) * (x : G)⁻¹ = a₀ := by group
    rw [this]
    exact ha₀A
  have heH : e ∈ H := by
    rw [hedef]
    exact mul_mem (mul_mem (inv_mem hxH) (hAH ha₀A)) hxH
  have heQ : e ∉ Q := by
    intro he
    apply ha₀Q
    have hmem : (x : G) * e * (x : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hQxnorm e).mp he
    rwa [show (x : G) * e * (x : G)⁻¹ = a₀ by rw [hedef]; group] at hmem
  have hQxA : Q.relIndex (conjSubgroup A x) = 2 := by
    have hQxconj : conjSubgroup Q (x : G) = Q :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hQxnorm
    have hinj : Function.Injective (MulAut.conj ((x : G)⁻¹)).toMonoidHom := by
      simpa using (MulAut.conj ((x : G)⁻¹)).injective
    have hrel := Subgroup.relIndex_map_map_of_injective Q A hinj
    rw [show Q.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom = Q from hQxconj] at hrel
    exact hrel.trans hQA2
  have hsupAx : conjSubgroup A x ≤ Q ⊔ Subgroup.zpowers e :=
    CFSG.QuasithinUnique.le_sup_zpowers_of_relIndex_two hQxA heAx heQ
  have hzle : Subgroup.zpowers e ≤ Subgroup.closure ({a₀, e} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl))
  have hzle₀ : Subgroup.zpowers a₀ ≤ Subgroup.closure ({a₀, e} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl rfl))
  have hleSup : A ⊔ conjSubgroup A x ≤ Subgroup.closure ({a₀, e} : Set G) ⊔ Q := by
    refine sup_le ?_ ?_
    · calc A ≤ Q ⊔ Subgroup.zpowers a₀ := hsupA
        _ ≤ Subgroup.closure ({a₀, e} : Set G) ⊔ Q := by
            rw [sup_comm]
            exact sup_le_sup hzle₀ le_rfl
    · calc conjSubgroup A x ≤ Q ⊔ Subgroup.zpowers e := hsupAx
        _ ≤ Subgroup.closure ({a₀, e} : Set G) ⊔ Q := by
            rw [sup_comm]
            exact sup_le_sup hzle le_rfl
  have hmem : a₀ * e ∈ H := mul_mem (hAH ha₀A) heH
  let z : ↥H := ⟨a₀ * e, hmem⟩
  have hzEq : orderOf z = orderOf (a₀ * e) := Subgroup.orderOf_mk _ _
  have hfz : f z = a * ((f x)⁻¹ * a * f x) := by
    change f ⟨a₀ * e, hmem⟩ = a * ((f x)⁻¹ * a * f x)
    have h1 : (⟨a₀ * e, hmem⟩ : ↥H) =
        (⟨a₀, ha₀H⟩ : ↥H) * ⟨e, heH⟩ := Subtype.ext rfl
    have h2 : (⟨e, heH⟩ : ↥H) =
        (⟨(x : G)⁻¹, H.inv_mem hxH⟩ : ↥H) *
          (⟨a₀, ha₀H⟩ : ↥H) * ⟨x, x.2⟩ := Subtype.ext rfl
    have h3 : f ⟨(x : G)⁻¹, H.inv_mem hxH⟩ = (f x)⁻¹ := by
      rw [show (⟨(x : G)⁻¹, H.inv_mem hxH⟩ : ↥H) = (⟨x, x.2⟩ : ↥H)⁻¹
        from Subtype.ext rfl, map_inv]
    rw [h1, map_mul, h2, map_mul, map_mul, h3]
  have h4 : orderOf (f z) = 4 := by
    rw [hfz]
    exact hy4
  by_cases hP : IsPGroup 2 (Subgroup.closure ({a₀, e} : Set G))
  ·
    have hnorm : Subgroup.closure ({a₀, e} : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
      refine (Subgroup.closure_le (K := Subgroup.normalizer (Q : Set G))).mpr ?_
      intro z hz
      rcases hz with rfl | rfl
      · exact hHnormQ (hAH ha₀A)
      · exact hHnormQ heH
    have hsupP : IsPGroup 2 ↥(Subgroup.closure ({a₀, e} : Set G) ⊔ Q) :=
      IsPGroup.to_sup_of_normal_right' hP hQ2 hnorm
    have hPsup : IsPGroup 2 ↥(A ⊔ conjSubgroup A x) := hsupP.to_le hleSup
    obtain ⟨a1, b1, hUa, hUb, hNΩ⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet hTI0 hEab hAω hAxω
    have hN : A ⊓ Subgroup.normalizer (conjSubgroup A x : Set G) ≠ ⊥ := by
      rwa [← hUa, ← hUb] at hNΩ
    have hcomm : a₀ * e = e * a₀ :=
      commute_of_isPGroup_sup hV0el hTI0 ⟨a1, hUa⟩ ⟨b1, hUb⟩ hN hPsup
        a₀ ha₀A e heAx
    have ha2 : a₀ * a₀ = 1 := by
      have h := hAel.2 a₀ ha₀A
      simpa [pow_two] using h
    have he2 : e * e = 1 := by
      have h := (isElemAbelian_conjSubgroup' hAel x).2 e heAx
      simpa [pow_two] using h
    have hsq : (a₀ * e) * (a₀ * e) = 1 := by
      calc (a₀ * e) * (a₀ * e) = a₀ * (e * a₀) * e := by group
        _ = a₀ * (a₀ * e) * e := by rw [← hcomm]
        _ = (a₀ * a₀) * (e * e) := by group
        _ = 1 := by rw [ha2, he2, mul_one]
    have hdvd : orderOf (a₀ * e) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hsq' : (f z) ^ 2 = 1 := by
      rw [← map_pow]
      have hz2 : z ^ 2 = 1 := by
        apply Subtype.ext
        simpa [z, pow_two] using hsq
      rw [hz2, map_one]
    have hdiv : orderOf (f z) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq'
    rw [h4] at hdiv
    obtain ⟨c, hc⟩ := hdiv
    omega
  ·
    have hodd : Odd (orderOf (a₀ * e)) :=
      seven_three_A hV0el hTI0 hEab hAω hAxω ha₀A heAx hP
    have hdiv : orderOf (f z) ∣ orderOf (a₀ * e) := by
      rw [← hzEq]
      exact orderOf_map_dvd f z
    rw [h4] at hdiv
    obtain ⟨k, hk⟩ := Odd.of_dvd_nat hodd hdiv
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
