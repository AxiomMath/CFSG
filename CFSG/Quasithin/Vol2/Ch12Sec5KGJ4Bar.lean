module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Lat
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Out
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.Quasithin.H13.S125KG.J4

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Fam
open CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.A312M24 (G24)

@[expose] noncomputable def bar
    (A : Subgroup J) : Subgroup G24 := (A.subgroupOf Hj).map fHj

theorem mem_of_bar
    {A : Subgroup J} (hEA : Eg uJ 11 ≤ A) {h : J} (hh : h ∈ Hj)
    (hb : fHj ⟨h, hh⟩ ∈ bar A) : h ∈ A := by
  obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp hb
  have hk : a⁻¹ * ⟨h, hh⟩ ∈ fHj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [ker_fHj, Subgroup.mem_subgroupOf] at hk
  have ha' : (a : J) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have e : h = (a : J) * ((a⁻¹ * ⟨h, hh⟩ : ↥Hj) : J) := by simp
  rw [e]
  exact A.mul_mem ha' (hEA hk)

theorem bar_mono
    {A B : Subgroup J} (h : A ≤ B) : bar A ≤ bar B := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, h ha, rfl⟩

theorem bar_le_iff
    {A B : Subgroup J} (hEB : Eg uJ 11 ≤ B) (hA : A ≤ Hj) :
    bar A ≤ bar B ↔ A ≤ B :=
  ⟨fun h a ha => mem_of_bar hEB (hA ha) (h ⟨⟨a, hA ha⟩, ha, rfl⟩), bar_mono⟩

theorem card_bar
    {A : Subgroup J} (hEA : Eg uJ 11 ≤ A) (hA : A ≤ Hj) :
    Nat.card A = 2 ^ 11 * Nat.card (bar A) := by
  have hM := j4Facts.mat
  set f := fHj.comp (A.subgroupOf Hj).subtype with hf
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have hr : f.range = bar A := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hk : Nat.card f.ker = 2 ^ 11 := by
    have e : f.ker = ((Eg uJ 11).subgroupOf Hj).subgroupOf (A.subgroupOf Hj) := by
      rw [hf, ← MonoidHom.comap_ker, ker_fHj]
      rfl
    rw [e, ← card_Eg_uJ hM]
    refine Nat.card_congr ((Subgroup.subgroupOfEquivOfLe ?_).toEquiv.trans
      (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).toEquiv)
    intro x hx
    exact hEA (Subgroup.mem_subgroupOf.mp hx)
  rw [hr, hk] at h1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, ← h1]

theorem bar_sup
    {A B : Subgroup J} (hA : A ≤ Hj) (hB : B ≤ Hj) : bar (A ⊔ B) = bar A ⊔ bar B := by
  rw [bar, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

@[expose] noncomputable def lift
    (Y : Subgroup G24) : Subgroup J := (Y.comap fHj).map Hj.subtype

theorem lift_le_Hj
    (Y : Subgroup G24) : lift Y ≤ Hj := Subgroup.map_subtype_le _

theorem Eg_le_lift
    (Y : Subgroup G24) : Eg uJ 11 ≤ lift Y := by
  intro x hx
  have hxH : x ∈ Hj := Eg_le_Hj hx
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  have hk : (⟨x, hxH⟩ : ↥Hj) ∈ fHj.ker := by rw [ker_fHj]; exact hx
  show fHj ⟨x, hxH⟩ ∈ Y
  rw [MonoidHom.mem_ker.mp hk]
  exact Y.one_mem

theorem subgroupOf_lift
    (Y : Subgroup G24) : (lift Y).subgroupOf Hj = Y.comap fHj :=
  Subgroup.comap_map_eq_self_of_injective Hj.subtype_injective _

theorem bar_lift
    (Y : Subgroup G24) : bar (lift Y) = Y := by
  rw [bar, subgroupOf_lift]
  exact Subgroup.map_comap_eq_self_of_surjective fHj_surjective Y

theorem le_lift_iff
    {A : Subgroup J} (hA : A ≤ Hj) (Y : Subgroup G24) :
    A ≤ lift Y ↔ bar A ≤ Y := by
  rw [← bar_le_iff (Eg_le_lift Y) hA, bar_lift]

theorem isSylowTwoOf_bar_P0
    : IsSylowTwoOf (bar P0) ⊤ := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have hc := card_bar Eg_le_P0 P0_le_Hj
  rw [card_P0 hM hF] at hc
  have h10 : Nat.card (bar P0) = 2 ^ 10 := by omega
  refine K1.isSylowTwoOf_top_iff.mpr ⟨IsPGroup.of_card h10, ?_⟩
  have h1 := Subgroup.card_mul_index (bar P0)
  rw [h10, CFSG.Sporadic.Mathieu.card_M24] at h1
  have h2 : (bar P0).index = 239085 := by omega
  rw [h2]
  norm_num

theorem bar_inSubgroup_perfectResidual
    {N : Subgroup J} (hNH : N ≤ Hj) :
    bar (CFSG.inSubgroup CFSG.perfectResidual N) =
      CFSG.inSubgroup CFSG.perfectResidual (bar N) := by
  have h1 := map_inSubgroup_perfectResidual Hj.subtype (N.subgroupOf Hj)
  rw [Subgroup.map_subgroupOf_eq_of_le hNH] at h1
  have h2 : (CFSG.inSubgroup CFSG.perfectResidual N).subgroupOf Hj =
      CFSG.inSubgroup CFSG.perfectResidual (N.subgroupOf Hj) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective Hj.subtype_injective _
  rw [bar, h2, map_inSubgroup_perfectResidual fHj (N.subgroupOf Hj)]
  rfl

theorem bar_oTwoUpper
    {D : Subgroup J} (hDH : D ≤ Hj) : bar (oTwoUpper D) = oTwoUpper (bar D) := by
  have h1 := map_oTwoUpper_eq Hj.subtype (D.subgroupOf Hj) fun x _ hx =>
    ⟨0, by rw [pow_zero, pow_one]; exact Hj.subtype_injective (hx.trans (map_one _).symm)⟩
  rw [Subgroup.map_subgroupOf_eq_of_le hDH] at h1
  have h2 : (oTwoUpper D).subgroupOf Hj = oTwoUpper (D.subgroupOf Hj) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective Hj.subtype_injective _
  rw [bar, h2, map_oTwoUpper_eq fHj (D.subgroupOf Hj)]
  · rfl
  · intro x _ hx
    obtain ⟨n, hn⟩ := isPGroup_ker_fHj ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem bar_le_normalizer
    {M A : Subgroup J} (hMN : M ≤ Subgroup.normalizer (A : Set J)) :
    bar M ≤ Subgroup.normalizer (bar A : Set G24) := by
  have h1 : M.subgroupOf Hj ≤ Subgroup.normalizer ((A.subgroupOf Hj : Subgroup ↥Hj) : Set ↥Hj) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hMN (Subgroup.mem_subgroupOf.mp hm)) a
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map fHj)

theorem config63_bar
    {N D : Subgroup J} (hc : Config63 P0 N D) (hNH : N ≤ Hj) :
    Config63 (bar P0) (bar N) (bar D) := by
  obtain ⟨hSD, hDN, hNc, hDc, hnot⟩ := hc
  have hE : Eg uJ 11 ≤ P0 := Eg_le_P0
  have hcP := card_bar hE P0_le_Hj
  have hcN := card_bar (hE.trans (hSD.trans hDN)) hNH
  have hcD := card_bar (hE.trans hSD) (hDN.trans hNH)
  have hNiH : CFSG.inSubgroup CFSG.perfectResidual N ≤ Hj :=
    (Subgroup.map_subtype_le _).trans hNH
  refine ⟨bar_mono hSD, bar_mono hDN, ?_, ?_, fun h => hnot ?_⟩
  · refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 11) ?_
    rw [← hcN, hNc, hcP]
    ring
  · refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 11) ?_
    rw [← hcD, hDc, hcP]
    ring
  · rw [← bar_inSubgroup_perfectResidual hNH, ← bar_sup hNiH P0_le_Hj] at h
    exact (bar_le_iff (hE.trans le_sup_right) (hDN.trans hNH)).mp h

theorem eq_of_card_63
    {S A B : Subgroup G24} (hS : IsSylowTwoOf S ⊤) (hA : S ≤ A) (hB : S ≤ B)
    (hcA : Nat.card A = 63 * 1024) (hcB : Nat.card B = 63 * 1024) : A = B := by
  obtain ⟨ψ, hψ⟩ := M24.exists_equiv ⟨MulEquiv.refl G24⟩ hS
  have key : ∀ Z : Subgroup G24, S ≤ Z → Nat.card Z = 63 * 1024 →
      Z.map ψ.toMonoidHom = M24.kgCtx.Y 2 := by
    intro Z hZ hcZ
    obtain ⟨j, hj, h, hcard⟩ := M24.exists_member_map ψ hψ hZ
    rw [hcZ] at hcard
    rw [h]
    interval_cases j <;> first | (simp at hcard; done) | exact M24.member_lt (by norm_num)
  apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rw [key A hA hcA, key B hB hcB]

theorem le_Hj_of_card
    {Y : Subgroup J} (hP : P0 ≤ Y) (h5 : ¬ 5 ∣ Nat.card Y) : Y ≤ Hj := by
  have hF : J4Facts := j4Facts
  have h5M2 : 5 ∣ Nat.card J4M2.M2 := by rw [J4M2.card_M2 hF]; norm_num
  rcases over_P0 hP with h | h | h | h
  · exfalso
    apply h5
    rw [h, Subgroup.card_top]
    exact h5M2.trans (Subgroup.card_subgroup_dvd_card _)
  · exact h
  · exact le_Hj_of_le_M3 hP h h5
  · exfalso
    exact h5 (h ▸ h5M2)

theorem N_eq_NV
    {N : Subgroup J} (hP : P0 ≤ N) (hc : Nat.card N = 2 ^ 21 * 63) : N = J4Rad.NV := by
  have hNH : N ≤ Hj := le_Hj_of_card hP (by rw [hc]; norm_num)
  have hNVH : J4Rad.NV ≤ Hj := inf_le_left
  have hPNV : P0 ≤ J4Rad.NV := H13.KGT3J4.P0_le_NV
  have hE : Eg uJ 11 ≤ P0 := Eg_le_P0
  have h1 := card_bar (hE.trans hP) hNH
  have h2 := card_bar (hE.trans hPNV) hNVH
  rw [hc] at h1
  rw [card_NV] at h2
  norm_num at h1 h2
  have hb : bar N = bar J4Rad.NV := eq_of_card_63 isSylowTwoOf_bar_P0 (bar_mono hP)
    (bar_mono hPNV) (by omega) (by omega)
  exact le_antisymm ((bar_le_iff (hE.trans hPNV) hNH).mp hb.le)
    ((bar_le_iff (hE.trans hP) hNVH).mp hb.ge)

theorem normalizer_inf_le
    {N D : Subgroup J} (hc : Config63 P0 N D) (hNH : N ≤ Hj) :
    Subgroup.normalizer (oTwoUpper D : Set J) ⊓ Hj ≤ N := by
  have hE : Eg uJ 11 ≤ N := Eg_le_P0.trans (hc.1.trans hc.2.1)
  have hDH : D ≤ Hj := hc.2.1.trans hNH
  have hα := M24.kg125AlphaM24 G24 ⟨MulEquiv.refl G24⟩ (bar P0) (bar N) (bar D)
    isSylowTwoOf_bar_P0 (config63_bar hc hNH)
  rw [← bar_oTwoUpper hDH] at hα
  intro z hz
  have hzH : z ∈ Hj := hz.2
  refine mem_of_bar hE hzH (hα ?_)
  have h1 := bar_le_normalizer (M := Subgroup.normalizer (oTwoUpper D : Set J) ⊓ Hj)
    (A := oTwoUpper D) inf_le_left
  exact h1 ⟨⟨z, hzH⟩, hz, rfl⟩

theorem alpha_J
    {N D : Subgroup J} (hc : Config63 P0 N D) :
    Subgroup.normalizer (oTwoUpper D : Set J) ≤ N := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  obtain ⟨hSD, hDN, hNc, hDc, hnot⟩ := hc
  have hc' : Config63 P0 N D := ⟨hSD, hDN, hNc, hDc, hnot⟩
  have hNc' : Nat.card N = 2 ^ 21 * 63 := by rw [hNc, card_P0 hM hF]; ring
  have hNV : N = J4Rad.NV := N_eq_NV (hSD.trans hDN) hNc'
  have hNH : N ≤ Hj := hNV ▸ inf_le_left
  have hDH : D ≤ Hj := hDN.trans hNH
  set Z := Subgroup.normalizer (oTwoUpper D : Set J) with hZ
  have hDZ : D ≤ Z :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_oTwoUpper D)
  have hZH : Z ⊓ Hj ≤ N := normalizer_inf_le hc' hNH
  have hcardle : ∀ A : Subgroup J, A ≤ N → Nat.card A ≤ 2 ^ 21 * 63 := fun A hA =>
    hNc' ▸ Subgroup.card_le_of_le hA
  rcases over_P0 (hSD.trans hDZ) with h | h | h | h
  ·
    exfalso
    have := hcardle Hj (by rw [h, top_inf_eq] at hZH; exact hZH)
    rw [card_Hj hF] at this
    norm_num at this
  · exact (le_inf le_rfl h).trans hZH
  ·
    refine (le_inf le_rfl ?_).trans hZH
    have hOD : oTwoUpper D ≤ D := oTwoUpper_le D
    have hfixb : ∀ y ∈ oTwoUpper D, y • (basePt : J ⧸ Hj) = basePt := fun y hy =>
      smul_basePt_eq_self_iff.mpr (hDH (hOD hy))
    have honly : ∀ w ∈ X5, (∀ y ∈ oTwoUpper D, y • w = w) → w = basePt := by
      intro w hw hwfix
      by_contra hwb
      apply hnot
      have hall : ∀ y ∈ oTwoUpper D, ∀ w' ∈ X5, y • w' = w' := by
        intro y hy w' hw'
        by_cases hwb' : w' = basePt
        · rw [hwb']
          exact hfixb y hy
        obtain ⟨e, he, hew⟩ := E_transitive_X5 hF hw hwb hw' hwb'
        have heD : e ∈ D := hSD (Eg_le_P0 he)
        have hy' : e⁻¹ * y * e ∈ oTwoUpper D := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDZ heD)) y).mp hy
          simpa using this
        rw [← hew]
        calc y • e • w = e • (e⁻¹ * y * e) • w := by
              rw [← mul_smul, ← mul_smul]
              group
          _ = e • w := by rw [hwfix _ hy']
      have hOK : oTwoUpper D ≤ J4M3.KL := fun y hy =>
        Subgroup.mem_inf.mpr ⟨h (hDZ (hOD hy)), (mem_fixingSubgroup_iff J).mpr (hall y hy)⟩
      have hKN : J4M3.KL ≤ CFSG.inSubgroup CFSG.perfectResidual N :=
        le_inSubgroup_perfectResidual_of_le (hNV ▸ KL_le_NV) commutator_KL.ge
      have hD2 : oTwoUpper D ⊔ P0 = D := oTwoUpper_sup_eq hSD (IsPGroup.of_card (card_P0 hM hF))
        hDc
      rw [← hD2]
      exact sup_le_sup_right (hOK.trans hKN) _
    intro z hz
    have hzX : z • basePt ∈ X5 := ⟨z, h hz, rfl⟩
    refine smul_basePt_eq_self_iff.mp (honly _ hzX fun y hy => ?_)
    have hy' : z⁻¹ * y * z ∈ oTwoUpper D := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hz) y).mp hy
      simpa using this
    calc y • z • basePt = z • (z⁻¹ * y * z) • basePt := by
          rw [← mul_smul, ← mul_smul]
          group
      _ = z • basePt := by rw [hfixb _ hy']
  ·
    exfalso
    have := hcardle (J4M2.M2 ⊓ Hj) (by rw [← h]; exact hZH)
    rw [card_M2_inf_Hj] at this
    norm_num at this

theorem kg125AlphaJ4 :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J4) →
      ∀ S N D : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
        Subgroup.normalizer (oTwoUpper D : Set X) ≤ N := by
  intro X _ _ hX S N D hS hc
  obtain ⟨e⟩ := hX
  exact alpha_of_sylow (isSylowTwoOf_P0) (fun N D hc => alpha_J hc)
    ⟨e.trans (seedEquiv j4Facts.mat)⟩ hS hc

theorem eq_top_of_j4
    {X : Type} [Group X] {K₀ : Subgroup X} [K₀.Normal]
    (hK₀ : Nonempty (↥K₀ ≃* NativeSporadic.J4))
    (hC : Subgroup.centralizer (K₀ : Set X) ≤ K₀) : K₀ = ⊤ := by
  obtain ⟨e⟩ := hK₀
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := H13.Ch4.j4OutTrivial_holds ↥K₀ ⟨e⟩ (MulAut.conjNormal x)
  have hconj : ∀ y : ↥K₀, x * (y : X) * x⁻¹ = (k : X) * y * (k : X)⁻¹ := by
    intro y
    have h3 := congrArg Subtype.val (hk y)
    rw [MulAut.conjNormal_apply] at h3
    simpa using h3
  have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hconj ⟨y, hy⟩
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [← h1]
      _ = (k : X)⁻¹ * x * y := by group
  have := K₀.mul_mem k.2 (hC hc)
  simpa using this

theorem gamma_J :
    27 ∣ Nat.card ↥(sSup {H : Subgroup J | P0 ≤ H ∧ Group.IsSolvable ↥H}) := by
  obtain ⟨φ, hφ⟩ := M24.exists_equiv ⟨MulEquiv.refl G24⟩ isSylowTwoOf_bar_P0
  set W : ℕ → Subgroup G24 := fun j => (M24.kgCtx.Y j).comap φ.toMonoidHom with hW
  have hSW : ∀ j, bar P0 ≤ W j := fun j => by
    rw [hW, ← Subgroup.map_le_iff_le_comap, hφ]
    exact M24.kgCtx.S_le_Y j
  have hP : ∀ j, P0 ≤ lift (W j) := fun j => (le_lift_iff P0_le_Hj _).mpr (hSW j)
  have hcard : ∀ j < 13, Nat.card ↥(lift (W j)) =
      2 ^ 11 * ([1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 * 1024) := by
    intro j hj
    rw [card_bar (Eg_le_lift _) (lift_le_Hj _), bar_lift, hW, card_comap_mulEquiv,
      ← M24.member_lt hj, M24.card_member hj.le]
  have hsolv : ∀ j < 13, [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 = 3 →
      Group.IsSolvable ↥(lift (W j)) := by
    intro j hj h3
    refine isSolvable_of_card_eq_two_pow_mul_three (k := 21) ((hcard j hj).trans ?_)
    rw [h3]
    norm_num
  have hAB : lift (W 7) ⊔ lift (W 9) ≤ sSup {H : Subgroup J | P0 ≤ H ∧ Group.IsSolvable ↥H} :=
    sup_le (le_sSup ⟨hP 7, hsolv 7 (by norm_num) rfl⟩) (le_sSup ⟨hP 9, hsolv 9 (by norm_num) rfl⟩)
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAB)
  rw [card_bar ((Eg_le_lift _).trans le_sup_left) (sup_le (lift_le_Hj _) (lift_le_Hj _)),
    bar_sup (lift_le_Hj _) (lift_le_Hj _), bar_lift, bar_lift]
  apply Dvd.dvd.mul_left
  obtain ⟨j, hj, h, hc⟩ := M24.exists_member_map φ hφ ((hSW 7).trans le_sup_left)
  have hmap : (W 7 ⊔ W 9).map φ.toMonoidHom = M24.kgCtx.Y 7 ⊔ M24.kgCtx.Y 9 := by
    rw [Subgroup.map_sup, hW,
      Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective,
      Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective]
  rw [hmap] at h
  have h7 : M24.kgCtx.Y 7 ≤ memberOrTop 13 M24.kgCtx.Y j := by
    rw [← h]
    exact le_sup_left
  have h9 : M24.kgCtx.Y 9 ≤ memberOrTop 13 M24.kgCtx.Y j := by
    rw [← h]
    exact le_sup_right
  rw [hc]
  rcases M24.mem_of_Y7_le hj h7 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (M24.not_Y9_le (by simp) h9).elim
  · norm_num
  · exact (M24.not_Y9_le (by simp) h9).elim
  · exact (M24.not_Y9_le (by simp) h9).elim
  · exact (M24.not_Y9_le (by simp) h9).elim
  · norm_num

theorem kg125GammaJ4 :
    KG125GammaJ4 := by
  intro X _ _ K₀ _ hK₀ hC _ S hS
  have hK := eq_top_of_j4 hK₀ hC
  obtain ⟨e⟩ := hK₀
  rw [card_sSup_solvable_eq (isSylowTwoOf_P0)
    ⟨((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm)).trans e).trans
      (seedEquiv j4Facts.mat)⟩ hS]
  exact gamma_J

end CFSG.Quasithin.H13.S125KG.J4
