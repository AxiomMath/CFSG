module

public import CFSG.Quasithin.Vol2.Ch10SecE9HeA
public import CFSG.Quasithin.Vol2.Ch10SecE9ZN
public import CFSG.Quasithin.Vol2.Ch10SecE9T
public import CFSG.Quasithin.Vol2.Ch10SecE9W

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9He

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}

theorem not_pCoreOf_le_centralizer_of_he
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    {P J : Subgroup G} (hXL0 : oTwoUpper P ≤ fsuL0 T L) (hXJ : oTwoUpper P ≤ J)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) (hJc : CharTwo J) (hV2 : quasithinV2 J = ⊥)
    {x₃ : G} (hx₃ : x₃ ∈ oTwoUpper P) (hx₃3 : orderOf x₃ = 3) :
    ¬ pCoreOf 2 J ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hRV
  have hVJ : fsuVM T L I ≤ Subgroup.normalizer (J : Set G) := (SecA.fsuVM_le_T hyp).trans hTJ
  have hJR : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hRV' : ⁅pCoreOf 2 J, fsuVM T L I⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRV
  have h1 : ⁅⁅J, pCoreOf 2 J⁆, fsuVM T L I⁆ = ⊥ := by
    have hle : ⁅J, pCoreOf 2 J⁆ ≤ pCoreOf 2 J := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hJR
    exact eq_bot_iff.mpr ((Subgroup.commutator_mono hle le_rfl).trans hRV'.le)
  have h2 : ⁅⁅pCoreOf 2 J, fsuVM T L I⁆, J⁆ = ⊥ := by
    rw [hRV', Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hVJle : ⁅fsuVM T L I, J⁆ ≤ J := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVJ
  have hodd : ∀ x ∈ oTwoUpper P, Odd (orderOf x) →
      x ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro x hx hxo
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hcVJ : x * v * x⁻¹ * v⁻¹ ∈ ⁅fsuVM T L I, J⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator (hXJ hx) hv
      rwa [commutatorElement_def] at this
    have hcR' : x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have := Subgroup.commutator_mem_commutator hcVJ hr
      rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    have hcR : x * v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 J := hJc ⟨hVJle hcVJ, hcR'⟩
    have hcV : x * v * x⁻¹ * v⁻¹ ∈ fsuVM T L I := by
      have hxV := SecA.fsuL0_le_normalizer_fsuVM T L I (hXL0 hx)
      exact (fsuVM T L I).mul_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv)
        ((fsuVM T L I).inv_mem hv)
    have hc2 : (x * v * x⁻¹ * v⁻¹) ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 _ hcV
    have hcx : x * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * x := by
      have hmem : x * v * x⁻¹ * v⁻¹ ∈ Subgroup.closure
          {z | z ∈ pCoreOf 2 J ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) ∧ z ^ 2 = 1} :=
        Subgroup.subset_closure ⟨⟨hcR, hcR'⟩, hc2⟩
      have hV : ⁅x * v * x⁻¹ * v⁻¹, x⁆ ∈ quasithinV2 J :=
        Subgroup.commutator_mem_commutator hmem (hXJ hx)
      rw [hV2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hV
      exact hV.symm
    exact (E9.commute_of_commutator hxo hcx hc2).symm
  have hXV : oTwoUpper P ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    (Subgroup.closure_le _).mpr fun x ⟨hxP, hxo⟩ => hodd x (mem_oTwoUpper_of_odd hxP hxo) hxo
  have hx₃O : x₃ ∈ pCoreOf 2 (fsuL0 T L ⊔ T) :=
    SecA.inf_centralizer_le_pCoreOf_sup h37 h38 hyp ⟨Subgroup.mem_sup_left (hXL0 hx₃), hXV hx₃⟩
  have h4 := SecD.eq_one_of_odd_of_mem (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hx₃O
    (by rw [hx₃3]; decide)
  rw [h4, orderOf_one] at hx₃3
  omega

variable {A K E : Subgroup L32.Γ}

theorem pCoreOf_le_T1_of_he (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {J : Subgroup G}
    (hXJ : XOf T L Ψ A ≤ J) (hRT : pCoreOf 2 J ≤ T) : pCoreOf 2 J ≤ T1 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro r hr
  have hrT := hRT hr
  refine ⟨hrT, ?_⟩
  by_contra hrn
  obtain ⟨a, haK, haE⟩ : ∃ a ∈ K, a ∉ E := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun a ha => hcon a ha : K ≤ E)
    rw [hD.cardK, hD.cardE] at this
    omega
  have hmem : (a, (1 : L32.Γ)) ∈ imgIn Ψ (XOf T L Ψ A) := by
    rw [imgIn_XOf h hD]
    exact ⟨haK, K.one_mem⟩
  obtain ⟨x, hxL0, hxX, hxΨ⟩ := mem_imgIn.mp hmem
  have hrX : r ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := (isXi_XOf h hD).2.1 hrT
  have hJR : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hcX : x * r * x⁻¹ * r⁻¹ ∈ XOf T L Ψ A := by
    have h1 : r * x⁻¹ * r⁻¹ ∈ XOf T L Ψ A :=
      (Subgroup.mem_normalizer_iff.mp hrX _).mp ((XOf T L Ψ A).inv_mem hxX)
    have e : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
    rw [e]
    exact (XOf T L Ψ A).mul_mem hxX h1
  have hcR : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 J := by
    have h1 : x * r * x⁻¹ ∈ pCoreOf 2 J :=
      (Subgroup.mem_normalizer_iff.mp (hJR (hXJ hxX)) r).mp hr
    exact (pCoreOf 2 J).mul_mem h1 ((pCoreOf 2 J).inv_mem hr)
  have hXR : XOf T L Ψ A ⊓ pCoreOf 2 J ≤ pCoreOf 2 (XOf T L Ψ A) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun y hy => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_right)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hJR (hXJ hy)⟩
  have hc := hXR ⟨hcX, hcR⟩
  rw [pCoreOf_XOf h hD] at hc
  obtain ⟨hcL0, hcE⟩ := mem_preIn.mp hc.2
  have hrL0 : r ∈ Subgroup.normalizer (fsuL0 T L : Set G) := SecA.le_fsuM T L hrT
  have hrn' : r⁻¹ ∉ Subgroup.normalizer (L : Set G) := by
    intro h'
    apply hrn
    have h'' := (Subgroup.normalizer (L : Set G)).inv_mem h'
    rwa [inv_inv] at h''
  have hconj : CFSG.conjugate L r⁻¹ = CFSG.conjugate L t :=
    SecA.conjugate_eq_of_not_mem h.h37 h.h38 h.hyp h.ht h.htn (T.inv_mem hrT) hrn'
  obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_fsuL0 h hxL0
  have hlL0 := SecA.le_fsuL0 T L hl
  have hl'L0 := SecA.conjugate_le_fsuL0 h.ht hl'
  have hΨx : Ψ ⟨l * l', hxL0⟩ = Ψ ⟨l, hlL0⟩ * Ψ ⟨l', hl'L0⟩ := by
    rw [← map_mul]; rfl
  have hl'1 : Ψ ⟨l', hl'L0⟩ = 1 := by
    have h1 := h.hC.onL l hlL0 hl
    have h2 := h.hC.onLt l' hl'L0 hl'
    rw [hxΨ] at hΨx
    have h3 := congrArg Prod.snd hΨx
    simp only [Prod.snd_mul, h1, one_mul] at h3
    exact Prod.ext h2 h3.symm
  have hl'O : l' ∈ pCoreOf 2 (fsuL0 T L) := (h.hC.ker _).mp hl'1
  have hy1 : r * l⁻¹ * r⁻¹ ∈ CFSG.conjugate L t := by
    rw [← hconj, SecA.mem_conjugate_iff]
    simpa [mul_assoc] using L.inv_mem hl
  have hy2 : r * l'⁻¹ * r⁻¹ ∈ pCoreOf 2 (fsuL0 T L) :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (fsuL0 T L) hrL0) _).mp
      ((pCoreOf 2 (fsuL0 T L)).inv_mem hl'O)
  have hy1L0 := SecA.conjugate_le_fsuL0 h.ht hy1
  have hy2L0 := CFSG.LieType.BorelTits.pCoreOf_le 2 (fsuL0 T L) hy2
  have hxL0' : l * l' ∈ fsuL0 T L := hxL0
  have e : (⟨l * l' * r * (l * l')⁻¹ * r⁻¹, hcL0⟩ : ↥(fsuL0 T L)) =
      ⟨l * l', hxL0'⟩ * ⟨r * l'⁻¹ * r⁻¹, hy2L0⟩ * ⟨r * l⁻¹ * r⁻¹, hy1L0⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hfst := hcE.1
  rw [e, map_mul, map_mul, (h.hC.ker ⟨r * l'⁻¹ * r⁻¹, hy2L0⟩).mpr hy2, mul_one, Prod.fst_mul,
    h.hC.onLt _ hy1L0 hy1, mul_one, hxΨ] at hfst
  exact haE hfst

theorem exists_mem_fsuUL_of_he (h : MaxCtx T L I t Ψ c) {J : Subgroup G}
    (hRT1 : pCoreOf 2 J ≤ T1 T L) (hTJ : T ≤ Subgroup.normalizer (J : Set G))
    (hRV : ¬ pCoreOf 2 J ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hV2 : quasithinV2 J = ⊥) :
    ∃ w ∈ fsuUL T L I, w ≠ 1 ∧ J ≤ Subgroup.centralizer ({w} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 J with hRdef
  have hRT : R ≤ T := hRT1.trans inf_le_left
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := hTJ.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hT1V : T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I))
      inf_le_right
  have hRV1 : ¬ R ≤ Subgroup.centralizer (fsuUL T L I : Set G) := by
    intro hR1
    apply hRV
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := SecA.exists_mul_of_mem_fsuVM h.h37 h.h38 h.hyp h.ht h.htn hv
    have hra : a * r = r * a := Subgroup.mem_centralizer_iff.mp (hR1 hr) a ha
    have hrb : b * r = r * b := by
      rw [SecA.mem_conjugate_iff] at hb
      have htr : t * r * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hTR h.ht) r).mp hr
      have h1 := Subgroup.mem_centralizer_iff.mp (hR1 htr) _ hb
      have h2 : t * (b * r) * t⁻¹ = t * (r * b) * t⁻¹ := by
        calc t * (b * r) * t⁻¹ = t * b * t⁻¹ * (t * r * t⁻¹) := by group
          _ = t * r * t⁻¹ * (t * b * t⁻¹) := h1
          _ = t * (r * b) * t⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    calc a * b * r = a * (b * r) := by group
      _ = a * (r * b) := by rw [hrb]
      _ = (a * r) * b := by group
      _ = r * a * b := by rw [hra]
      _ = r * (a * b) := by group
  obtain ⟨r, hr, hrV1⟩ := Set.not_subset.mp hRV1
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hrV1
  push Not at hrV1
  obtain ⟨v, hv, hvr⟩ := hrV1
  have hcV1 : r * v * r⁻¹ * v⁻¹ ∈ fsuUL T L I :=
    (fsuUL T L I).mul_mem ((Subgroup.mem_normalizer_iff.mp (hT1V (hRT1 hr)) v).mp hv)
      ((fsuUL T L I).inv_mem hv)
  have hvT : v ∈ T := SecA.fsuVM_le_T h.hyp (SecA.fsuUL_le_fsuVM T L I hv)
  have hcR : r * v * r⁻¹ * v⁻¹ ∈ R := by
    have h1 : v * r⁻¹ * v⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hTR hvT) _).mp (R.inv_mem hr)
    have e : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
    rw [e]
    exact R.mul_mem hr h1
  have hc1 : r * v * r⁻¹ * v⁻¹ ≠ 1 := by
    intro h1
    apply hvr
    calc v * r = (r * v * r⁻¹ * v⁻¹)⁻¹ * (r * v) := by group
      _ = r * v := by rw [h1, inv_one, one_mul]
  have hN : fsuUL T L I ⊓ R ≠ ⊥ := fun hb => hc1 (by
    have : r * v * r⁻¹ * v⁻¹ ∈ fsuUL T L I ⊓ R := ⟨hcV1, hcR⟩
    rwa [hb, Subgroup.mem_bot] at this)
  have hRN : R ≤ Subgroup.normalizer ((fsuUL T L I ⊓ R : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hT1V (hRT1 hy), Subgroup.le_normalizer hy⟩
  obtain ⟨w, hwN, hw1, hwC⟩ := SecA.exists_ne_one_mem_centralizer
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) inf_le_right hRN hN
  refine ⟨w, hwN.1, hw1, fun j hj => ?_⟩
  have hw2 : w ^ 2 = 1 :=
    (SecA.isElemAbelian_fsuVM h.hyp).2 w (SecA.fsuUL_le_fsuVM T L I hwN.1)
  have hmem : w ∈ Subgroup.closure
      {z | z ∈ pCoreOf 2 J ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) ∧ z ^ 2 = 1} :=
    Subgroup.subset_closure ⟨⟨hwN.2, hwC⟩, hw2⟩
  have hV : ⁅w, j⁆ ∈ quasithinV2 J := Subgroup.commutator_mem_commutator hmem hj
  rw [hV2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hV
  exact Subgroup.mem_centralizer_singleton_iff.mpr hV.symm

theorem inf_le_T1_of_he (h : MaxCtx T L I t Ψ c) (hCV : fsuCVM T L I = ⊥) {w : G}
    (hw : w ∈ fsuUL T L I) (hw1 : w ≠ 1) {J : Subgroup G}
    (hJw : J ≤ Subgroup.centralizer ({w} : Set G)) : T ⊓ J ≤ T1 T L := by
  rintro s ⟨hsT, hsJ⟩
  refine ⟨hsT, ?_⟩
  by_contra hsn
  have hsw : s * w * s⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hJw hsJ)
    rw [this, mul_inv_cancel_right]
  have hconj : CFSG.conjugate L s = CFSG.conjugate L t :=
    SecA.conjugate_eq_of_not_mem h.h37 h.h38 h.hyp h.ht h.htn hsT hsn
  have hV : CFSG.conjugate (fsuUL T L I) s = CFSG.conjugate (fsuUL T L I) t := by
    rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L hsT),
      SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L h.ht), hconj]
  have hw2 : w ∈ CFSG.conjugate (fsuUL T L I) t := by
    rw [← hV, SecA.mem_conjugate_iff, hsw]
    exact hw
  have hwC := SecA.inf_conjugate_le_fsuCVM h.hyp h.ht h.htn ⟨hw, hw2⟩
  rw [hCV, Subgroup.mem_bot] at hwC
  exact hw1 hwC

theorem heReduce_aux
    (hNoHe : NoHeLStarF) (h128 : Lemma128Four) (h331 : Stmt3_3_1) (h : MaxCtx T L I t Ψ c)
    (hD : ParData A K E) {H J : Subgroup G} (hH : InH (XOf T L Ψ A ⊔ T) H) (hJ : J ∈ cComp H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) (hXJ : XOf T L Ψ A ≤ J)
    (he : Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    ¬ J ≤ fsuM T L ∧ T ⊓ J ≤ T1 T L ∧
      ∃ w ∈ ⁅fsuVM T L I, L⁆, w ≠ 1 ∧ J ≤ Subgroup.centralizer ({w} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp := h.hyp
  have hTH : T ≤ H := le_sup_right.trans hH.1
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) := hTH.trans hHJ
  have hJc := charTwo_of_he hyp hTH hH.2 hJ
  have hRT := pCoreOf_le_of_he hyp hTH hJ hHJ
  have hV2 := quasithinV2_eq_bot_of_he hNoHe h128 hyp hTH hH.2 hJ hHJ he
  have hZJ := commutator_conjClosure_eq_bot_of_he hNoHe h128 hyp hTH hH.2 hJ hHJ he
  have h3X : 3 ∣ Nat.card ↥(XOf T L Ψ A) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, relIndex_XOf h hD]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  have hy3 : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hXL0 := XOf_le_fsuL0 h hD
  have hJM := not_le_fsuM_of_he h he (hXJ y.2) (hXL0 y.2) hy3
  have hCV := fsuCVM_eq_bot_of_he h331 hyp hJM hZJ
  have hRV := not_pCoreOf_le_centralizer_of_he h.h37 h.h38 hyp hXL0 hXJ hTJ hJc hV2 y.2 hy3
  have hRT1 := pCoreOf_le_T1_of_he h hD hXJ hRT
  obtain ⟨w, hw, hw1, hJw⟩ := exists_mem_fsuUL_of_he h hRT1 hTJ hRV hV2
  exact ⟨hJM, inf_le_T1_of_he h hCV hw hw1 hJw, w, hw, hw1, hJw⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.E9He

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem heReduce_of
    (hNoHe : NoHeLStarF) (h128 : Lemma128Four) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) : HeReduce := by
  intro G _ _ T L I hyp h3 P hP hTP H hH J hJ hHJ hXJ he
  obtain ⟨t, Ψ, c, h⟩ := exists_maxCtx h37 h38 hyp h3
  rcases maximal_classify h37 h38 hyp h.ht h.htn h.hC hP hTP with rfl | rfl
  · exact E9He.heReduce_aux hNoHe h128 h331 h parData_a hH hJ hHJ hXJ he
  · exact E9He.heReduce_aux hNoHe h128 h331 h parData_b hH hJ hHJ hXJ he

end CFSG.Quasithin.Vol2.Ch10.SecB
