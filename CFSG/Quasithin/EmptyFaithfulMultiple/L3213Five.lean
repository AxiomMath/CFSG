module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Reduced
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Aut
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Frattini

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits
open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_map_comap_actionOn {V X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    {E : Subgroup (MulAut V)} {g : G} :
    g ∈ (E.comap (A4.actionOn V X hXV)).map X.subtype ↔
      ∃ hg : g ∈ X, conjAct V ⟨g, hXV hg⟩ ∈ E := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem conjAct_mem_commutator_autOn {V X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hQ : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G)) {φ : G}
    (hφ : φ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X) (hφN : φ ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨φ, hφN⟩ ∈ ⁅autOn X V, autOn X V⁆ := by
  set P := (⁅autOn X V, autOn X V⁆.comap (A4.actionOn V X hXV)).map X.subtype with hP
  have hle : ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ P := by
    refine sup_le (Subgroup.commutator_le.mpr fun x hx y hy => ?_) (fun c hc => ?_)
    · refine (mem_map_comap_actionOn hXV).mpr
        ⟨commutator_le_self X (Subgroup.commutator_mem_commutator hx hy), ?_⟩
      have e : (⟨⁅x, y⁆, hXV (commutator_le_self X (Subgroup.commutator_mem_commutator hx hy))⟩ :
          Subgroup.normalizer (V : Set G)) = ⁅(⟨x, hXV hx⟩ : Subgroup.normalizer (V : Set G)),
            ⟨y, hXV hy⟩⁆ := Subtype.ext (by simp [commutatorElement_def])
      rw [e, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        ⟨⟨x, hXV hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
        ⟨⟨y, hXV hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · refine (mem_map_comap_actionOn hXV).mpr ⟨pCoreOf_le 2 X hc, ?_⟩
      rw [A4.conjAct_eq_one_iff.mpr (hQ hc)]
      exact Subgroup.one_mem _
  obtain ⟨_, hφE⟩ := (mem_map_comap_actionOn hXV).mp (hle hφ)
  exact hφE

section Finite

variable [Finite G] {T X : Subgroup G}

theorem autOn_vOf_facts (hT : quasithinIsSylowTwo T) (hX : IsXi T X) {p : ℕ}
    (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) :
    autOn X (vOf T X) ≤ autOn (X ⊔ T) (vOf T X) ∧
      autOn (X ⊔ T) (vOf T X) ≤
        Subgroup.normalizer (autOn X (vOf T X) : Set (MulAut (vOf T X))) ∧
      (∀ y ∈ autOn X (vOf T X), y ^ p = 1) ∧
      ∀ g ∈ autOn (X ⊔ T) (vOf T X), ∃ k : ℕ, g ^ 2 ^ k ∈ autOn X (vOf T X) := by
  set V := vOf T X with hVdef
  have hXTV : X ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_vOf hX
  have hXVN : X ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hXTV
  have hTVN : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hXTV
  have hconj : ∀ g h : Subgroup.normalizer (V : Set G), conjAct V g * conjAct V h *
      (conjAct V g)⁻¹ = conjAct V (g * h * g⁻¹) := fun g h => by simp
  have hXbN : autOn (X ⊔ T) V ≤ Subgroup.normalizer (autOn X V : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * x * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_of_isXi hX
      (Subgroup.mem_subgroupOf.mp hg)) x).mp (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨A4.autOn_mono le_sup_left, hXbN, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    refine A4.conjAct_eq_one_iff.mpr ?_
    have hxp := pCoreOf_le_centralizer_vOf hX (hpow x (Subgroup.mem_subgroupOf.mp hx))
    simpa using hxp
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ ((X ⊔ T : Subgroup G) : Set G) := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hX.2.1] at hg'
    obtain ⟨x, hx, t, ht, he⟩ := hg'
    have hgxt : g = ⟨x, hXVN hx⟩ * ⟨t, hTVN ht⟩ := Subtype.ext he.symm
    obtain ⟨k, hk⟩ := hT.1 ⟨t, ht⟩
    have hk' : (⟨t, hTVN ht⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have htX : conjAct V ⟨t, hTVN ht⟩ ∈ Subgroup.normalizer (autOn X V : Set (MulAut V)) :=
      hXbN ⟨⟨t, hTVN ht⟩, Subgroup.mem_subgroupOf.mpr (le_sup_right (a := X) ht), rfl⟩
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq
      (⟨⟨x, hXVN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩ : conjAct V ⟨x, hXVN hx⟩ ∈ autOn X V)
      htX (2 ^ k)
    refine ⟨k, ?_⟩
    rw [hgxt, map_mul, hxe, ← map_pow, hk', map_one, mul_one]
    exact hx'

end Finite

theorem prime_eq_three_or_five {G : Type} [Group G] [Finite G] {T X : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h4 : Stmt1542Four G T) (hX : IsXi T X)
    (hM : IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))) (hsolv : Group.IsSolvable X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) :
    p = 3 ∨ p = 5 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, h5⟩ := autOn_vOf_facts hyp.sylow hX hpow
  have hV := isElemAbelian_vOf T X
  have hq := qhatInt_vOf_le_two hyp h4 hX hM hsolv
  have hO2 := pCoreOf_autOn_vOf_eq_bot hyp.sylow hX hsolv (vOf_ne_bot hyp hX hM)
  let _ := commGroupOfElemAbelian hV
  have hVsq : ∀ v : vOf T X, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  exact (d2_13_data hVsq hp2 hq hO2 h1 h2
    (fun y => ⟨1, Subtype.ext (by simpa using h3 y y.2)⟩) h5).1

theorem prime_dvd_aut_eq_two_or_five {G : Type} [Group G] [Finite G] {T X : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h4 : Stmt1542Four G T) (hX : IsXi T X)
    (hM : IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))) (hsolv : Group.IsSolvable X)
    (hpow : ∀ x ∈ X, x ^ 5 ∈ pCoreOf 2 X)
    (hidx : (pCoreOf 2 X).relIndex X = 5 ^ 2 ∨
      ((pCoreOf 2 X).relIndex X = 5 ^ 3 ∧ ¬ ⁅X, X⁆ ≤ pCoreOf 2 X)) :
    ∀ q : ℕ, q.Prime →
      q ∣ (sectionCentralizer X (pCoreOf 2 X)).relIndex
        (Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G)) →
      q = 2 ∨ q = 5 := by
  intro q hq hqd
  by_contra hq25
  push Not at hq25
  obtain ⟨hq2, hq5⟩ := hq25
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := hyp.sylow
  obtain ⟨h, hhX, hhR, hhC, b, hhb⟩ := exists_pow_eq_one_not_mem_sectionCentralizer hT hX hqd
  set V := vOf T X with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_vOf T X
  have hVne : V ≠ ⊥ := vOf_ne_bot hyp hX hM
  have hXTV : X ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_vOf hX
  have hXVN : X ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hXTV
  have hTVN : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hXTV
  have hhV : h ∈ Subgroup.normalizer (V : Set G) :=
    A4.mem_normalizer_commutator (normalizer_le_normalizer_omegaOneCenterOf _ hhR) hhX
  have hQV : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := pCoreOf_le_centralizer_vOf hX
  have hR := inf_centralizer_vOf_le hX hsolv hVne
  have hq' := qhatInt_vOf_le_two hyp h4 hX hM hsolv
  have hO2 := pCoreOf_autOn_vOf_eq_bot hT hX hsolv hVne
  obtain ⟨hXsXb, hXbN, hXsexp, hXb2⟩ := autOn_vOf_facts hT hX hpow
  have hcardXs' : Nat.card (autOn X V) = (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X :=
    card_autOn_eq_relIndex hXVN
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X)
    (X ⊓ Subgroup.centralizer (V : Set G)) X (le_inf (pCoreOf_le 2 X) hQV) inf_le_left
  have hdvd : (X ⊓ Subgroup.centralizer (V : Set G)).relIndex X ∣ (pCoreOf 2 X).relIndex X :=
    Dvd.intro_left _ hmul
  let _ := commGroupOfElemAbelian hV
  set Xb := autOn (X ⊔ T) V with hXb
  set Xs := autOn X V with hXs
  have hVsq : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hconj : ∀ g k : Subgroup.normalizer (V : Set G), conjAct V g * conjAct V k *
      (conjAct V g)⁻¹ = conjAct V (g * k * g⁻¹) := fun g k => by simp
  have hxs : ∀ {x : G} (hx : x ∈ X), conjAct V ⟨x, hXVN hx⟩ ∈ Xs := fun hx =>
    ⟨⟨_, hXVN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hXs5 : IsPGroup 5 Xs := fun y => ⟨1, Subtype.ext (by simpa using hXsexp y y.2)⟩
  have hO5 : pCoreOf 5 Xb = Xs := by
    refine le_antisymm (fun y hy => ?_) (le_pCoreOf_of_le_normalizer 5 hXsXb hXbN hXs5)
    obtain ⟨k, hk⟩ := hXb2 y (pCoreOf_le 5 Xb hy)
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 5 Xb ⟨y, hy⟩
    have hj' : y ^ 5 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact mem_of_pow_mem_of_pow_mem (Nat.Coprime.pow k j (by norm_num)) hk (hj' ▸ Xs.one_mem)
  have hXsF : Xs ≤ fittingOf Xb := le_fittingOf_of_normal hXsXb hXs5
    (fun x hx g hg => (Subgroup.mem_normalizer_iff.mp (hXbN hx) g).mp hg)
  have hcardXs : Nat.card Xs ≤ 125 := by
    rw [hcardXs']
    have hpos : 0 < (pCoreOf 2 X).relIndex X := by
      rcases hidx with hi | ⟨hi, -⟩ <;> rw [hi] <;> norm_num
    have h125 : (pCoreOf 2 X).relIndex X ≤ 125 := by
      rcases hidx with hi | ⟨hi, -⟩ <;> rw [hi] <;> norm_num
    exact (Nat.le_of_dvd hpos hdvd).trans h125
  have hnab : Nat.card Xs = 125 → ∃ a ∈ Xs, ∃ c ∈ Xs, a * c ≠ c * a := by
    intro h125
    rw [hcardXs'] at h125
    rcases hidx with hi | ⟨hi, hnc⟩
    · rw [hi, h125] at hdvd
      norm_num at hdvd
    · rw [hi, h125] at hmul
      have h1 : (pCoreOf 2 X).relIndex (X ⊓ Subgroup.centralizer (V : Set G)) = 1 := by omega
      have hle : X ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 X :=
        Subgroup.relIndex_eq_one.mp h1
      by_contra hcon
      push Not at hcon
      apply hnc
      rw [Subgroup.commutator_le]
      intro x hx y hy
      apply hle
      refine ⟨commutator_le_self X (Subgroup.commutator_mem_commutator hx hy), ?_⟩
      have h2 : conjAct V ⁅(⟨x, hXVN hx⟩ : Subgroup.normalizer (V : Set G)), ⟨y, hXVN hy⟩⁆ =
          1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcon _ (hxs hx) _ (hxs hy)
      have h3 := A4.conjAct_eq_one_iff.mp h2
      simpa [commutatorElement_def] using h3
  have hno3 : ∀ Y₁ Y₂ Y₃ : Subgroup (MulAut V), Y₁ ∈ Xk Xb 2 → Y₂ ∈ Xk Xb 2 →
      Y₃ ∈ Xk Xb 2 → Y₁ ≤ Xs → Y₂ ≤ Xs → Y₃ ≤ Xs → Y₁ ≠ Y₂ → Y₁ ≠ Y₃ → Y₂ ≠ Y₃ → False :=
    fun _ _ _ h₁ h₂ h₃ hY₁ hY₂ hY₃ h12 h13 h23 =>
      false_of_three_mem_Xk hVsq hXs5 hcardXs hnab h₁ h₂ h₃ hY₁ hY₂ hY₃ h12 h13 h23
  have hcen : ∀ a ∈ Xs, ∀ c ∈ ⁅Xs, Xs⁆, a * c = c * a := by
    have hle : ⁅Xs, Xs⁆ ≤ Subgroup.centralizer (Xs : Set (MulAut V)) := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_commutatorElement, ← commutatorElement_eq_one_iff_mul_comm,
        ← map_commutatorElement]
      refine A4.conjAct_eq_one_iff.mpr (hQV ?_)
      have hxy : ((⁅x, y⁆ : Subgroup.normalizer (V : Set G)) : G) ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X := by
        refine Subgroup.mem_sup_left ?_
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
          (Subgroup.mem_subgroupOf.mp hy)
        simpa [commutatorElement_def] using this
      have h1 := xi_commutator_mem_of_mem_frattini hX (Subgroup.mem_subgroupOf.mp hz) hxy
      simpa [commutatorElement_def] using h1
    intro a ha c hc
    exact Subgroup.mem_centralizer_iff.mp (hle hc) a ha
  obtain ⟨-, h5⟩ := d2_13_data hVsq (by norm_num : (5 : ℕ) ≠ 2) hq' hO2 hXsXb hXbN hXs5 hXb2
  obtain ⟨A, hAQ, hDcard, hDrk⟩ := h5 rfl
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := hAQ
  set D := ⁅pCoreOf 5 Xb, A⁆ with hDdef
  have hDO5 : D ≤ pCoreOf 5 Xb :=
    commutator_le_left_of_le_normalizer (hA2.le.trans (le_normalizer_pCoreOf 5 Xb))
  have hDXs : D ≤ Xs := hO5 ▸ hDO5
  have hDXk : D ∈ Xk Xb 2 := ⟨hDXs.trans hXsF, by rw [hDcard], by rw [hDrk]⟩
  set hh := conjAct V ⟨h, hhV⟩ with hhh
  have hho : Odd (orderOf hh) := by
    have h1 : hh ^ q ^ b = 1 := by
      rw [hhh, ← map_pow]
      have : (⟨h, hhV⟩ : Subgroup.normalizer (V : Set G)) ^ q ^ b = 1 :=
        Subtype.ext (by simpa using hhb)
      rw [this, map_one]
    exact (Odd.pow (hq.odd_of_ne_two hq2)).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hhXs : ∀ y ∈ Xs, hh * y * hh⁻¹ ∈ Xs := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hhh, hconj]
    refine ⟨⟨h, hhV⟩ * x * ⟨h, hhV⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hhX x).mp (Subgroup.mem_subgroupOf.mp hx)
  set E : Subgroup (MulAut V) := ⨆ (Y : Subgroup (MulAut V)) (_ : Y ∈ Xk Xb 2 ∧ Y ≤ Xs), Y
    with hE
  have hEXs : E ≤ Xs := iSup₂_le fun Y hY => hY.2
  have hDE : D ≤ E := le_iSup₂_of_le (f := fun (Y : Subgroup (MulAut V))
    (_ : Y ∈ Xk Xb 2 ∧ Y ≤ Xs) => Y) D ⟨hDXk, hDXs⟩ le_rfl
  have hhE : ∀ e ∈ E, hh * e = e * hh := by
    have hle : E ≤ Subgroup.centralizer ({hh} : Set (MulAut V)) := by
      refine iSup₂_le fun Y hY y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro g rfl
      exact commute_of_mem_Xk hXsF hno3 hho hhXs hY.1 hY.2 y hy
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (hle he) hh rfl
  have hTE : ∀ t (ht : t ∈ T), ∀ e ∈ E,
      conjAct V ⟨t, hTVN ht⟩ * e * (conjAct V ⟨t, hTVN ht⟩)⁻¹ ∈ E := by
    intro t ht
    set th := conjAct V ⟨t, hTVN ht⟩ with hth
    have hthXb : th ∈ Xb :=
      ⟨⟨t, hTVN ht⟩, Subgroup.mem_subgroupOf.mpr (le_sup_right (a := X) ht), rfl⟩
    have hle : E ≤ E.comap (MulAut.conj th).toMonoidHom := by
      refine iSup₂_le fun Y hY => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_iSup₂_of_le (f := fun (Y : Subgroup (MulAut V))
        (_ : Y ∈ Xk Xb 2 ∧ Y ≤ Xs) => Y) (conjBy th Y)
        ⟨conjBy_mem_Xk hthXb hY.1, fun z hz => ?_⟩ le_rfl
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXbN hthXb) _).mp (hY.2 (mem_conjBy_iff.mp hz))
      simpa [mul_assoc] using h1
    intro e he
    have := hle he
    simpa [MulAut.conj_apply] using this
  set Et := (E.comap (A4.actionOn V X hXVN)).map X.subtype with hEt
  have hEtX : Et ≤ X := Subgroup.map_subtype_le _
  have hTEt : T ≤ Subgroup.normalizer (Et : Set G) := by
    intro t ht
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨hgX, hgE⟩ := (mem_map_comap_actionOn hXVN).mp hg
    have htg : t * g * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hX.2.1 ht) g).mp hgX
    refine (mem_map_comap_actionOn hXVN).mpr ⟨htg, ?_⟩
    have h1 := hTE t ht _ hgE
    rw [hconj] at h1
    exact h1
  have hΦX : ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ X := sup_le (commutator_le_self X) (pCoreOf_le 2 X)
  have hTΦ : T ≤ Subgroup.normalizer ((Et ⊔ (⁅X, X⁆ ⊔ pCoreOf 2 X) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hTEt ht, mem_normalizer_frattini (hX.2.1 ht)⟩
  obtain ⟨-, -, -, -, -, -, -, -, hirr⟩ := id hX
  rcases hirr _ le_sup_right (sup_le hEtX hΦX) hTΦ with hcase | hcase
  ·
    have hEle : E ≤ ⁅Xs, Xs⁆ := by
      intro e he
      obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hXVN).mp (hEXs he)
      have hxEt : (x : G) ∈ Et := (mem_map_comap_actionOn hXVN).mpr ⟨x.2, he⟩
      have hxΦ : (x : G) ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X := hcase ▸ Subgroup.mem_sup_left hxEt
      exact conjAct_mem_commutator_autOn hXVN hQV hxΦ (hXVN x.2)
    have hD := eq_bot_of_le_commutator hO5 hA2 hXsexp hcen (hDE.trans hEle)
    rw [← hDdef] at hD
    rw [hD, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  ·
    apply hhC
    have hΦN : Et ≤ Subgroup.normalizer ((⁅X, X⁆ ⊔ pCoreOf 2 X : Subgroup G) : Set G) :=
      fun e he => mem_normalizer_frattini (Subgroup.le_normalizer (hEtX he))
    have hcomm : ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X := by
      intro x hx
      rw [← hcase, sup_comm] at hx
      obtain ⟨φ, hφ, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hΦN).1 hx
      obtain ⟨heX, heE⟩ := (mem_map_comap_actionOn hXVN).mp he
      have h1 : h * φ * h⁻¹ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_frattini hhX) φ).mp hφ
      have h2 : h * e * h⁻¹ * e⁻¹ ∈ ⁅X, X⁆ ⊔ pCoreOf 2 X := by
        refine hR ⟨X.mul_mem ((Subgroup.mem_normalizer_iff.mp hhX e).mp heX) (X.inv_mem heX), ?_⟩
        have h3 := hhE _ heE
        have h4 : conjAct V (⟨h, hhV⟩ * ⟨e, hXVN heX⟩ * ⟨h, hhV⟩⁻¹ * ⟨e, hXVN heX⟩⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hhh, h3]
          group
        have h5 := A4.conjAct_eq_one_iff.mp h4
        simpa using h5
      have e1 : h * (φ * e) * h⁻¹ * (φ * e)⁻¹ =
          (h * φ * h⁻¹) * (h * e * h⁻¹ * e⁻¹) * φ⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ hφ)
    have hcop : Nat.Coprime (q ^ b) 5 :=
      Nat.Coprime.pow_left b ((Nat.coprime_primes hq (by norm_num)).mpr hq5)
    exact ⟨hhX, normalizer_le_normalizer_pCoreOf 2 X hhX,
      xi_commutator_mem_pCoreOf_of_coprime hX hpow hcop hhb hhX hcomm⟩

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
