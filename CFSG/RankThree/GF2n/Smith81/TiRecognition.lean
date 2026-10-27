module

public import CFSG.RankThree.GF2n.Smith81.TiFStar

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem factorization_two_eq_of_odd {N k m : ℕ} (h : N = 2 ^ k * m) (hm : Odd m) :
    N.factorization 2 = k := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hodd : ¬ 2 ∣ m := by
    intro h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

section RootImage

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem rootSet_image (φ : Y →* Y') (hφ : Function.Injective φ) (D : Set Y) (d : Y) :
    CFSG.Timmesfeld.rootSet (φ '' D) (φ d) = φ '' CFSG.Timmesfeld.rootSet D d := by
  have hc : ∀ a b : Y, Commute (φ a) (φ b) ↔ Commute a b := by
    intro a b
    simp only [Commute, SemiconjBy, ← map_mul, hφ.eq_iff]
  ext e'
  constructor
  · rintro ⟨⟨e, heD, rfl⟩, h⟩
    refine ⟨e, ⟨heD, fun f hf => ?_⟩, rfl⟩
    rw [← hc, ← hc]
    exact h (φ f) ⟨f, hf, rfl⟩
  · rintro ⟨e, ⟨heD, h⟩, rfl⟩
    refine ⟨⟨e, heD, rfl⟩, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rw [hc, hc]
    exact h f hf

theorem rootGroup_image (φ : Y →* Y') (hφ : Function.Injective φ) (D : Set Y) (d : Y) :
    CFSG.Timmesfeld.rootGroup (φ '' D) (φ d) = (CFSG.Timmesfeld.rootGroup D d).map φ := by
  rw [CFSG.Timmesfeld.rootGroup, CFSG.Timmesfeld.rootGroup, rootSet_image φ hφ,
    MonoidHom.map_closure]

theorem card_rootGroup_image (φ : Y →* Y') (hφ : Function.Injective φ) (D : Set Y) (d : Y) :
    Nat.card (CFSG.Timmesfeld.rootGroup (φ '' D) (φ d)) =
      Nat.card (CFSG.Timmesfeld.rootGroup D d) := by
  rw [rootGroup_image φ hφ, Subgroup.card_map_of_injective hφ]

end RootImage

section RootZ

variable [Finite G] {M Q Z : Subgroup G}

theorem commute_iff_mem_Q (H : StrothHyp M Q Z) (hT : TIFusion M Q Z) {z a f : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (ha : a ∈ Z) (ha1 : a ≠ 1) (hf : IsConj z f) : Commute a f ↔ f ∈ Q := by
  constructor
  · intro hc
    have hfM : f ∈ M := mem_M_of_commute_Z H ha ha1 hc.symm.eq
    obtain ⟨c, hcf⟩ := isConj_iff.mp hf
    rw [← hcf] at hfM ⊢
    exact hT c z hz hz1 hfM
  · intro hfQ
    exact Z_central H ha hfQ

theorem rootSet_eq_Z_sharp (H : StrothHyp M Q Z) (hT : TIFusion M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.cls z) z = {e | e ∈ Z ∧ e ≠ 1} := by
  ext e
  constructor
  · rintro ⟨heD, hcomm⟩
    have he1 : e ≠ 1 := by
      intro h
      have : IsConj z 1 := h ▸ heD
      exact hz1 (isConj_one_left.mp this)
    refine ⟨?_, he1⟩
    have hQc : Q ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [H.gen]
      refine iSup₂_le fun g hgQ => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hw1 : w = 1
      · rw [hw1]; simp
      · have hwQ : w ∈ Q := hgQ hw
        have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp hw
        have hw1' : g⁻¹ * w * g ≠ 1 := by
          intro h
          apply hw1
          have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
          rw [this, h]; group
        obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hw' hw1'
        have hwD : w ∈ CFSG.Timmesfeld.CorB.cls z := by
          refine isConj_iff.mpr ⟨g * m, ?_⟩
          calc g * m * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
            _ = w := by rw [hm]; group
        have hzw : Commute z w := (Z_central H hz hwQ : z * w = w * z)
        exact ((hcomm w hwD).2 hzw).symm.eq
    rw [← H.centralizer_Q]
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQc hf)
  · rintro ⟨heZ, he1⟩
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 heZ he1
    refine ⟨isConj_iff.mpr ⟨m, hm⟩, fun f hf => ?_⟩
    rw [commute_iff_mem_Q H hT hz hz1 heZ he1 hf, commute_iff_mem_Q H hT hz hz1 hz hz1 hf]

theorem rootGroup_eq_Z (H : StrothHyp M Q Z) (hT : TIFusion M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) z = Z := by
  rw [CFSG.Timmesfeld.rootGroup, rootSet_eq_Z_sharp H hT hz hz1]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun e he => he.1
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, hx1⟩

theorem card_rootGroup_cls (H : StrothHyp M Q Z) (hT : TIFusion M Q Z) {z w : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hw : w ∈ CFSG.Timmesfeld.CorB.cls z) :
    Nat.card (CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) w) = Nat.card Z := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hw
  have hcj := CFSG.Timmesfeld.rootGroup_conj (D := CFSG.Timmesfeld.CorB.cls z) ⟨z, rfl⟩ c z
  rw [hcj, Subgroup.card_map_of_injective (MulAut.conj c).injective, rootGroup_eq_Z H hT hz hz1]

theorem exists_mem_Z_ne (H : StrothHyp M Q Z) (z : G) : ∃ τ ∈ Z, τ ≠ 1 ∧ τ ≠ z := by
  by_contra hno
  push Not at hno
  have hsub : (Z : Set G) ⊆ {1, z} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hno x hx hx1)
  have h1 : Nat.card (Z : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    exact this.trans ((Set.ncard_insert_le 1 {z}).trans (by simp [Set.ncard_singleton]))
  have h2 : Nat.card Z ≤ 2 := h1
  have := H.q4
  omega

theorem exists_noncommuting_cls (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ d ∈ CFSG.Timmesfeld.CorB.cls z, ∃ e ∈ CFSG.Timmesfeld.CorB.cls z, d ∈ Q ∧ e ∈ Q ∧
      ¬ Commute d e := by
  by_contra hno
  push Not at hno
  obtain ⟨B, hc⟩ := exists_ctx_of_strothHyp H
  have hQgen : Q ≤ Subgroup.closure {w | w ∈ CFSG.Timmesfeld.CorB.cls z ∧ w ∈ Q} := by
    refine H.gen.le.trans (iSup₂_le fun g hgQ => ?_)
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]; exact Subgroup.one_mem _
    · refine Subgroup.subset_closure ⟨?_, hgQ hw⟩
      have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp hw
      have hw1' : g⁻¹ * w * g ≠ 1 := by
        intro h
        apply hw1
        have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        rw [this, h]; group
      obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hw' hw1'
      refine isConj_iff.mpr ⟨g * m, ?_⟩
      calc g * m * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
        _ = w := by rw [hm]; group
  have hQc : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := CFSG.Timmesfeld.commute_of_mem_closure (S := {w | w ∈ CFSG.Timmesfeld.CorB.cls z ∧
      w ∈ Q}) (S' := {w | w ∈ CFSG.Timmesfeld.CorB.cls z ∧ w ∈ Q})
      (fun d hd e he => hno d hd.1 e he.1 hd.2 he.2) (hQgen hv) (hQgen hu)
    exact this.eq
  rw [H.centralizer_Q] at hQc
  have hBQ : B ≤ Q := hc.le
  have hBZ : B ≤ Z := hBQ.trans hQc
  obtain ⟨g, hg⟩ := hc.conj
  have hcard : Nat.card Z ≤ Nat.card B := by rw [hg, card_conjSubgroup]
  exact hc.ne (Subgroup.eq_of_le_of_card_ge hBZ hcard)

theorem exists_orderOf_mul_eq_four (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ d ∈ CFSG.Timmesfeld.CorB.cls z, ∃ e ∈ CFSG.Timmesfeld.CorB.cls z, orderOf (d * e) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, e, he, hdQ, heQ, hde⟩ := exists_noncommuting_cls H hz hz1
  have hsq : ∀ w ∈ CFSG.Timmesfeld.CorB.cls z, w * w = 1 := by
    intro w hw
    obtain ⟨c, rfl⟩ := isConj_iff.mp hw
    have hzz : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hdd := hsq d hd
  have hee := hsq e he
  have hcomm : ⁅d, e⁆ = (d * e) ^ 2 := by
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    rw [commutatorElement_def, hdi, hei, pow_two]
    group
  have hZc : ⁅d, e⁆ ∈ Z := comm_mem_Z H hdQ heQ
  have h2 : (d * e) ^ 2 ≠ 1 := by
    rw [← hcomm]
    intro h
    exact hde (commutatorElement_eq_one_iff_mul_comm.mp h)
  have h4 : (d * e) ^ (2 ^ (1 + 1)) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, ← hcomm]
    exact Z_sq H hZc
  refine ⟨d, hd, e, he, ?_⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) h4
  simpa using this

theorem Z_le_normalClosure (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Z ≤ Subgroup.normalClosure ({z} : Set G) := by
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]; exact Subgroup.one_mem _
  · obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hw hw1
    rw [← hm]
    have hzU : z ∈ Subgroup.normalClosure ({z} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton z)
    exact Subgroup.normalClosure_normal.conj_mem z hzU m

theorem Q_le_normalClosure (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Q ≤ Subgroup.normalClosure ({z} : Set G) := by
  refine H.gen.le.trans (iSup₂_le fun g _ => ?_)
  intro w hw
  have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp hw
  have := Subgroup.normalClosure_normal.conj_mem _ (Z_le_normalClosure H hz hz1 hw') g
  simpa [mul_assoc] using this

end RootZ

abbrev CorBQuot {X : Type} [Group X] (t : X) : Type :=
  ↥(Subgroup.normalClosure ({t} : Set X)) ⧸ Subgroup.center ↥(Subgroup.normalClosure ({t} : Set X))

@[expose] def CorBQuotClass {X : Type} [Group X] (t : X) : Set (CorBQuot t) :=
  QuotientGroup.mk' (Subgroup.center ↥(Subgroup.normalClosure ({t} : Set X))) ''
    CFSG.Timmesfeld.CorB.clsIn t

@[expose] def RankTwoOutcome (Y : Type) [Group Y] (D : Set Y) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ (∃ d ∈ D, Nat.card (CFSG.Timmesfeld.rootGroup D d) = 2 ^ f) ∧
      CFSG.Blueprint.LieModel Y .PSL 3 2 f) ∨
    (∃ f : ℕ, 2 ≤ f ∧ (∃ d ∈ D, Nat.card (CFSG.Timmesfeld.rootGroup D d) = 2 ^ f) ∧
      CFSG.Blueprint.LieModel Y .G2 0 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ (∃ d ∈ D, Nat.card (CFSG.Timmesfeld.rootGroup D d) = 2 ^ f) ∧
      CFSG.Blueprint.LieModel Y .trialityD4 0 2 f) ∨
    CFSG.Blueprint.LieModel Y .PSU 3 3 1

@[expose] def CorBRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), CFSG.Timmesfeld.CorB.Setup t →
    (∃ τ ∈ CFSG.Timmesfeld.CorB.conjCent t, τ ≠ t) →
    (∃ d ∈ CFSG.Timmesfeld.CorB.cls t, ∃ e ∈ CFSG.Timmesfeld.CorB.cls t, orderOf (d * e) = 4) →
    (∃ d ∈ CorBQuotClass t, ∃ e ∈ CFSG.Timmesfeld.rootSet (CorBQuotClass t) d, e ≠ d) →
    RankTwoOutcome (CorBQuot t) (CorBQuotClass t)

@[expose] def TiLieOrders : Prop :=
  (∀ (Y : Type) [Group Y] (f : ℕ), CFSG.Blueprint.LieModel Y .PSL 3 2 f →
      (Nat.card Y).factorization 2 = 3 * f) ∧
    (∀ (Y : Type) [Group Y] (f : ℕ), CFSG.Blueprint.LieModel Y .G2 0 2 f →
      (Nat.card Y).factorization 2 = 6 * f) ∧
    (∀ (Y : Type) [Group Y] (f : ℕ), CFSG.Blueprint.LieModel Y .trialityD4 0 2 f →
      (Nat.card Y).factorization 2 = 12 * f) ∧
    (∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .PSU 3 3 1 →
      (Nat.card Y).factorization 2 = 5)

section Recog

variable [Finite G] {M Q Z : Subgroup G}

theorem image_clsIn (z : G) :
    (Subgroup.normalClosure ({z} : Set G)).subtype '' CFSG.Timmesfeld.CorB.clsIn z =
      CFSG.Timmesfeld.CorB.cls z := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hx
    exact ⟨⟨x, CFSG.Timmesfeld.CorB.cls_subset z hx⟩, hx, rfl⟩

theorem tiRecognition (hCorB : CorBRankTwo) (hOrd : TiLieOrders) (H : StrothHyp M Q Z)
    (hT : TIFusion M Q Z) {n : ℕ} (hn : 1 ≤ n) (hw : Width Q Z n) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      (CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 f ∨
        CFSG.Blueprint.LieModel (FStar G) .G2 0 2 f ∨
        CFSG.Blueprint.LieModel (FStar G) .trialityD4 0 2 f) := by
  classical
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  have hS := corB_setup_of_tiFusion H hT hz hz1
  obtain ⟨τ, hτZ, hτ1, hτz⟩ := exists_mem_Z_ne H z
  have hpair : ∃ τ' ∈ CFSG.Timmesfeld.CorB.conjCent z, τ' ≠ z := by
    refine ⟨τ, ⟨?_, ?_⟩, hτz⟩
    · exact Z_central H hτZ (H.Z_normal.1 hz)
    · obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hτZ hτ1
      exact isConj_iff.mpr ⟨m, hm⟩
  have h4 := exists_orderOf_mul_eq_four H hz hz1
  obtain ⟨hFU, hcomp⟩ := generalizedFitting_eq_normalClosure H hz hz1
  have hcen := center_normalClosure_eq_bot H hz hz1
  set U := Subgroup.normalClosure ({z} : Set G) with hU
  let ι : ↥U →* CorBQuot z := QuotientGroup.mk' (Subgroup.center ↥U)
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  let e : ↥U ≃* CorBQuot z := MulEquiv.ofBijective ι ⟨hι, QuotientGroup.mk'_surjective _⟩
  have hzU : z ∈ U := Subgroup.subset_normalClosure (Set.mem_singleton z)
  have hτU : τ ∈ U := Z_le_normalClosure H hz hz1 hτZ
  have hτc : IsConj z τ := by
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hτZ hτ1
    exact isConj_iff.mpr ⟨m, hm⟩
  have hlarge : ∃ d ∈ CorBQuotClass z, ∃ e' ∈ CFSG.Timmesfeld.rootSet (CorBQuotClass z) d,
      e' ≠ d := by
    let uz : ↥U := ⟨z, hzU⟩
    let uτ : ↥U := ⟨τ, hτU⟩
    have huz : uz ∈ CFSG.Timmesfeld.CorB.clsIn z := IsConj.refl z
    have hτroot : τ ∈ CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.cls z) z := by
      rw [rootSet_eq_Z_sharp H hT hz hz1]
      exact ⟨hτZ, hτ1⟩
    have hroot_in : uτ ∈ CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.clsIn z) uz := by
      have h1 := rootSet_image U.subtype U.subtype_injective (CFSG.Timmesfeld.CorB.clsIn z) uz
      rw [image_clsIn z] at h1
      have h2 : τ ∈ U.subtype '' CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.clsIn z) uz := by
        rw [← h1]
        exact hτroot
      obtain ⟨u', hu', hu'τ⟩ := h2
      have : u' = uτ := Subtype.ext hu'τ
      rwa [this] at hu'
    refine ⟨ι uz, ⟨uz, huz, rfl⟩, ι uτ, ?_, ?_⟩
    · rw [CorBQuotClass, rootSet_image ι hι]
      exact ⟨uτ, hroot_in, rfl⟩
    · intro h
      exact hτz (congrArg Subtype.val (hι h))
  have hout := hCorB G z hS hpair h4 hlarge
  have hcardZ : ∀ d ∈ CorBQuotClass z,
      Nat.card (CFSG.Timmesfeld.rootGroup (CorBQuotClass z) d) = Nat.card Z := by
    rintro d ⟨u, hu, rfl⟩
    rw [CorBQuotClass, card_rootGroup_image ι hι]
    have h1 := card_rootGroup_image U.subtype U.subtype_injective
      (CFSG.Timmesfeld.CorB.clsIn z) u
    rw [image_clsIn z] at h1
    rw [← h1]
    exact card_rootGroup_cls H hT hz hz1 hu
  let e' : CorBQuot z ≃* ↥(generalizedFitting G) :=
    e.symm.trans (MulEquiv.subgroupCongr hFU.symm)
  obtain ⟨f₀, k₀, hf₀, -⟩ := H.cp
  rcases hout with ⟨f, -, ⟨d, hd, hdc⟩, hL⟩ | ⟨f, -, ⟨d, hd, hdc⟩, hL⟩ |
      ⟨f, -, ⟨d, hd, hdc⟩, hL⟩ | hL
  · exact ⟨f, (hcardZ d hd).symm.trans hdc,
      Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e' hL)⟩
  · exact ⟨f, (hcardZ d hd).symm.trans hdc,
      Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e' hL))⟩
  · exact ⟨f, (hcardZ d hd).symm.trans hdc,
      Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e' hL))⟩
  · exfalso
    have hLU : CFSG.Blueprint.LieModel ↥U .PSU 3 3 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL
    have h5 := hOrd.2.2.2 ↥U hLU
    have hQU : Nat.card Q ∣ Nat.card U :=
      Subgroup.card_dvd_of_le (Q_le_normalClosure H hz hz1)
    have hf2 : 2 ≤ f₀ := by
      by_contra hlt
      have h1 := H.q4
      rw [hf₀] at h1
      interval_cases f₀ <;> simp at h1
    have hne : Nat.card U ≠ 0 := Nat.card_pos.ne'
    have hpow : 2 ^ (f₀ * (2 * n + 1)) ∣ Nat.card U := by
      have : Nat.card Q = 2 ^ (f₀ * (2 * n + 1)) := by
        rw [hw, hf₀, ← pow_mul]
      rw [this] at hQU
      exact hQU
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hpow
    rw [h5] at hle
    nlinarith

theorem Q_le_generalizedFitting (H : StrothHyp M Q Z) : Q ≤ generalizedFitting G := by
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  rw [(generalizedFitting_eq_normalClosure H hz hz1).1]
  exact Q_le_normalClosure H hz hz1

theorem tiFamily (hCorB : CorBRankTwo) (hOrd : TiLieOrders) (H : StrothHyp M Q Z)
    (hT : TIFusion M Q Z) {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 4) (hw : Width Q Z n)
    (h1 : n = 1 → ¬ Nat.card Z ^ 6 ∣ Nat.card G)
    (h2 : n = 2 → ¬ Nat.card Z ^ 12 ∣ Nat.card G) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      ((n = 1 ∧ CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 f) ∨
        (n = 2 ∧ CFSG.Blueprint.LieModel (FStar G) .G2 0 2 f) ∨
        (n = 4 ∧ CFSG.Blueprint.LieModel (FStar G) .trialityD4 0 2 f)) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
  obtain ⟨f, hf, hfam⟩ := tiRecognition hCorB hOrd H hT hn1 hw
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have h4 := H.q4
    rw [hf] at h4
    interval_cases f <;> simp at h4
  have hQF := Q_le_generalizedFitting H
  have hQdvd : Nat.card Q ∣ Nat.card (FStar G) := Subgroup.card_dvd_of_le hQF
  have hFG : Nat.card (FStar G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hFne : Nat.card (FStar G) ≠ 0 := Nat.card_pos.ne'
  have hQ : Nat.card Q = 2 ^ (f * (2 * n + 1)) := by rw [hw, hf, ← pow_mul]
  have hZ : Nat.card Z = 2 ^ f := hf
  have hle : f * (2 * n + 1) ≤ (Nat.card (FStar G)).factorization 2 := by
    have : 2 ^ (f * (2 * n + 1)) ∣ Nat.card (FStar G) := hQ ▸ hQdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hFne).mp this
  have hdvd : ∀ k : ℕ, k * f ≤ (Nat.card (FStar G)).factorization 2 →
      Nat.card Z ^ k ∣ Nat.card G := by
    intro k hk
    have : 2 ^ (k * f) ∣ Nat.card (FStar G) :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hFne).mpr hk
    rw [hZ, ← pow_mul, mul_comm f k]
    exact this.trans hFG
  refine ⟨f, hf, ?_⟩
  rcases hfam with hL | hL | hL
  · have h := hOrd.1 _ f hL
    rw [h] at hle
    have : 2 * n + 1 ≤ 3 := by nlinarith
    have hn1' : n = 1 := by omega
    exact Or.inl ⟨hn1', hL⟩
  · have h := hOrd.2.1 _ f hL
    rw [h] at hle
    have : 2 * n + 1 ≤ 6 := by nlinarith
    rcases hn with rfl | rfl | rfl
    · exact absurd (hdvd 6 (by rw [h])) (h1 rfl)
    · exact Or.inr (Or.inl ⟨rfl, hL⟩)
    · omega
  · have h := hOrd.2.2.1 _ f hL
    rw [h] at hle
    rcases hn with rfl | rfl | rfl
    · exact absurd (hdvd 6 (by rw [h]; omega)) (h1 rfl)
    · exact absurd (hdvd 12 (by rw [h])) (h2 rfl)
    · exact Or.inr (Or.inr ⟨rfl, hL⟩)

end Recog


end CFSG.RankThree.GF2n.Smith81
