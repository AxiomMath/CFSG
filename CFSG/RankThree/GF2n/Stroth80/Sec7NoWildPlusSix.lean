module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7TypeSec
public import CFSG.RankThree.GF2n.Stroth80.Sec7ConjSection
public import CFSG.RankThree.GF2n.Stroth80.Sec7FormOnRange
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommFormFormula
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step2
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommForm
public import CFSG.RankThree.GF2n.Stroth80.Sec7NoInvariantFormProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem no_wild_plus6_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp : OmegaPlusNat hc t 3)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z)
    (hx2 : x ^ 2 ∈ Q)
    (hQx : ∃ g ∈ M, ∀ w ∈ Q, ⁅x, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  by_contra hex
  push Not at hex
  obtain ⟨Md, iD, iA, κ, hκ, S, hSA, hS2, hSw⟩ :=
    exists_conj_section_data h52a hA h310chi hc hs hxM hxt hxV hx2
  haveI : Finite Md := hκ.finite
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hWn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun r hr y hy =>
    conj_mem_Wt (hQM (hRM hr)) (hc.Rt_normalizes_Vt ht hr) hy
  have hVn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      r * y * r⁻¹ ∈ Vt M (LB M Q B) B Z t := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) y).mp hy
  have hRZ : ∀ r ∈ Rt M (LB M Q B) t, ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro r hr z hz
    have := Subgroup.mem_centralizer_iff.mp (hc.Rt_le_H0 t hr).2 z hz
    rw [← this]
    group
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hQM hxM) y).mp hy
  have h52c : Stroth52cStatement := stroth_5_2c_of_chi h310chi
  obtain ⟨lam, hlam⟩ := n12Lam_holds G M Q Z B hc
  obtain ⟨hZQ, hZc, hcomm, hsq⟩ := n12Q_holds G M Q Z B hc
  have hnd := n12Lemma1_holds G M Q Z B hc lam hlam
  have hW2 := (n12Lemma2_of h34 h52c G M Q Z B hc n t hs).2 lam hlam
  have hrad := lamOrth_radical_le lam hZQ hZc hcomm hsq hnd hZV hVW hWQ hW2
  have hVW1 : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅v, w⁆ = 1 := by
    intro v hv w hw
    have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact this
  obtain ⟨β, hβA, hβnd, hβκ⟩ :=
    exists_commForm_WV_formula lam hZQ hZc hcomm hZV hVW hWQ hVW1 hκ hRZ hWn hrad
  have hsurj : ∀ a : Md, ∃ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      Multiplicative.toAdd (κ w) = a := by
    intro a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    exact ⟨w, by rw [hw]; rfl⟩
  have hSβ : ∀ a b : Md, β (S a) (S b) = β a b := by
    intro a b
    obtain ⟨w, rfl⟩ := hsurj a
    obtain ⟨w', rfl⟩ := hsurj b
    obtain ⟨u, hu1, hu2⟩ := hSw w
    obtain ⟨u', hu1', hu2'⟩ := hSw w'
    have e1 : S (Multiplicative.toAdd (κ w)) = Multiplicative.toAdd (κ u) := by
      rw [hu2, toAdd_ofAdd]
    have e2 : S (Multiplicative.toAdd (κ w')) = Multiplicative.toAdd (κ u') := by
      rw [hu2', toAdd_ofAdd]
    rw [e1, e2, hβκ u u', hβκ w w']
    have hwQ : (w : G) ∈ Q := hWQ w.2
    have hwQ' : (w' : G) ∈ Q := hWQ w'.2
    have eU : (⟨(u : G), hWQ u.2⟩ : ↥Q) = ⟨x * (w : G) * x⁻¹, hxQ _ hwQ⟩ := Subtype.ext hu1
    have eU' : (⟨(u' : G), hWQ u'.2⟩ : ↥Q) = ⟨x * (w' : G) * x⁻¹, hxQ _ hwQ'⟩ :=
      Subtype.ext hu1'
    rw [eU, eU']
    exact comm2_conj_eq lam hcomm x hxQ hxZ ⟨(w : G), hwQ⟩ ⟨(w' : G), hwQ'⟩
  let T : Md →+ Md := S + AddMonoidHom.id Md
  have hTa : ∀ a, T a = S a + a := fun a => rfl
  have h2 : ∀ a : Md, a + a = 0 := hκ.two
  have hTT : ∀ a, T (T a) = 0 := by
    intro a
    rw [hTa, hTa, map_add, hS2]
    have e : a + S a + (S a + a) = (a + a) + (S a + S a) := by abel
    rw [e, h2, h2, add_zero]
  have hTA : ∀ (r : ↥(Rt M (LB M Q B) t)) (a : Md), r • T a = T (r • a) := by
    intro r a
    rw [hTa, hTa, hSA, smul_add]
  have hself : ∀ a b : Md, β (T a) b = β a (T b) := by
    intro a b
    rw [hTa, hTa, map_add β, AddMonoidHom.add_apply, map_add (β a)]
    have h1 := hSβ (S a) b
    rw [hS2] at h1
    rw [h1]
  have hTκ : ∀ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ c : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      (c : G) = ⁅x, (w : G)⁆ ∧
        κ c = Multiplicative.ofAdd (T (Multiplicative.toAdd (κ w))) := by
    intro w
    obtain ⟨u, hu1, hu2⟩ := hSw w
    refine ⟨u * w⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      simp only [commutatorElement_def]
    · rw [map_mul, map_inv, hu2, hTa, ofAdd_add]
      have hneg : Multiplicative.ofAdd (Multiplicative.toAdd (κ w)) =
          (Multiplicative.ofAdd (Multiplicative.toAdd (κ w)))⁻¹ := by
        rw [← ofAdd_neg]
        congr 1
        exact (neg_eq_of_add_eq_zero_left (h2 _)).symm
      rw [ofAdd_toAdd] at hneg ⊢
      rw [← hneg]
  obtain ⟨P, hVP, hPW, hPsec⟩ := exists_secSub_eq hVW hκ T.range
  have hmemP : ∀ y : ↥(Wt Q (Vt M (LB M Q B) B Z t)), (y : G) ∈ P ↔
      Multiplicative.toAdd (κ y) ∈ T.range := fun y => by
    rw [← hPsec]
    exact (toAdd_mem_secSub_iff hκ hVP y).symm
  have hPn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ P, r * y * r⁻¹ ∈ P := by
    intro r hr y hy
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := hPW hy
    have hrW : r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hWn r hr y hyW
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    have h1 := hκ.act ⟨r, hr⟩ ⟨y, hyW⟩ ⟨r * y * r⁻¹, hrW⟩ rfl
    refine (hmemP ⟨r * y * r⁻¹, hrW⟩).mpr ?_
    rw [h1, toAdd_ofAdd]
    refine ⟨(⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) • a, ?_⟩
    rw [← hTA, ha]
  have hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P := by
    intro r hr
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : r⁻¹ * y * r ∈ P := mem_conjSubgroup.mp hy
      have := hPn r hr _ hy'
      simpa [mul_assoc] using this
    · rw [mem_conjSubgroup]
      have := hPn r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr) y hy
      simpa using this
  have hVPlt : Vt M (LB M Q B) B Z t < P := by
    obtain ⟨w0, hw0, hw0V⟩ := hex
    refine lt_of_le_of_ne hVP fun h => hw0V ?_
    obtain ⟨c, hc1, hc2⟩ := hTκ ⟨w0, hw0⟩
    have : (c : G) ∈ P := (hmemP c).mpr (by
      rw [hc2, toAdd_ofAdd]
      exact ⟨_, rfl⟩)
    rw [h, ← hc1]
    exact this
  obtain ⟨g, hg, hQg⟩ := hQx
  have hPle : P ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro y hy
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := hPW hy
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    obtain ⟨w, rfl⟩ := hsurj a
    obtain ⟨c, hc1, hc2⟩ := hTκ w
    have h1 : κ ⟨y, hyW⟩ = κ c := by
      rw [hc2, ha, ofAdd_toAdd]
    have h2 : y * (c : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := (hκ.eq_iff ⟨y, hyW⟩ c).mp h1
    have e : y = (y * (c : G)⁻¹) * (c : G) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right ?_)
    rw [hc1]
    exact hQg _ (hWQ w.2)
  have hcardP : Nat.card ↥P ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
    Nat.card_mono (Set.toFinite _) hPle
  have h1 := card_sup_conj_mul_le hc sec39_Z_le_Vt (hc.Vt_le_Q t) hg
  have hV3 := n12N_card_V hc t 3 (by norm_num) (Or.inl hp)
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hPbound : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 6 := by
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc Nat.card ↥P * Nat.card ↥Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊔
          conjSubgroup g (Vt M (LB M Q B) B Z t)) * Nat.card ↥Z :=
        Nat.mul_le_mul_right _ hcardP
      _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t) := h1
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * (Nat.card ↥Z * Nat.card ↥Z ^ (2 * 3)) := by
        rw [← hV3]
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 6 * Nat.card ↥Z := by ring
  obtain ⟨k, hk⟩ := ((sec7WVSecCard_of hA hPts h52a h52b) G M Q Z B hc n t hs P hVP hPW hPR 3
    (by norm_num)).2 hp (le_refl 3)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hk6 : 2 ^ (3 - 1) * k ≤ 6 := by
    have h3 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 ^ (3 - 1) * k) ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 6 := hk ▸ hPbound
    have h4 := Nat.le_of_mul_le_mul_left h3 hVpos
    exact (Nat.pow_le_pow_iff_right hq).mp h4
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hcardle : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact (ne_of_lt hVPlt) (Subgroup.eq_of_le_of_card_ge hVPlt.le hcardle)
  have hk1 : k = 1 := by
    norm_num at hk6
    omega
  subst hk1
  obtain ⟨r₀, hr₀, hdP⟩ := oppDecomp_of_invariant_section hA hPts h52a h52b hc hs hVPlt.le hPW hPR
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r₀ B) = conjSubgroup r₀ (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr₀.mem)
  have hL2R : LB M Q (conjSubgroup r₀ B) ≤ Rt M (LB M Q B) t :=
    le_sup_right.trans hr₀.gen.ge
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r₀ hr₀.mem hr₀.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV3)
    subst hmm
    have hsecP : SecHyp (Rt M (LB M Q B) t) P (Vt M (LB M Q B) B Z t) :=
      SecHyp.of_isOppDecomp hdP hPn hVn
    obtain ⟨Y, iY, iYD, κ', hκ', hkerY⟩ :=
      exists_sectionModule_ker hker hsecP (fun k hk y hy => hWN k hk y (hPW hy))
    haveI : Finite Y := hκ'.finite
    have hdec := isCompl_fixedSub_of_isOppDecomp hPn hκ' hdP hLR hL2R
    have hPcard := natCard_eq_of_isSecMod hVPlt.le hκ'
    have hYcard : Nat.card Y = Nat.card K ^ 4 := by
      rw [hKZ]
      have e : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 ^ (3 - 1) * 1) =
          Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Y := by
        rw [← hk, hPcard]
      have e' := Nat.eq_of_mul_eq_mul_left hVpos e
      norm_num at e'
      exact e'.symm
    obtain ⟨ι, hι_inj, hιA, -, hιrange⟩ := exists_secMod_embedding hκ hκ' hVP hPW hPn
    obtain ⟨γ, hγA, hγnd⟩ := exists_form_on_range β hβnd T hself hβA hTA ι hι_inj hιA
      (hιrange.trans hPsec)
    exact noInvariantForm_frame_hom (hKZ ▸ (by omega : 4 ≤ Nat.card Z)) φ hrange hu hu' hu0 huu'
      Y hκ'.two hkerY ((LB M Q B).subgroupOf (Rt M (LB M Q B) t))
      ((LB M Q (conjSubgroup r₀ B)).subgroupOf (Rt M (LB M Q B) t))
      (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hdec hYcard ⟨γ, hγA, hγnd⟩
  · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV3)
    have hMinusM : OmegaMinusNat hc t 3 := by
      rw [← hmm]
      exact ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩
    exact omegaSignStatement_holds G M Q Z B hc t 3 (by norm_num) hp hMinusM

end CFSG.RankThree.GF2n.Stroth80
