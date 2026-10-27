module

public import CFSG.Quasithin.Vol2.KGFactC31J4Set
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4HjPerf
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFinal
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Red
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31Hex

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

theorem exists_surj_map {G Q : Type*} [Group G] [Group Q] (κ : G →* A)
    (hκ : Function.Injective κ) {K H : Subgroup G} (φ : ↥H →* Q) (hφ : Function.Surjective φ)
    (hker : φ.ker = K.subgroupOf H) :
    ∃ ψ : ↥(H.map κ) →* Q, Function.Surjective ψ ∧ ψ.ker = (K.map κ).subgroupOf (H.map κ) := by
  have he : ∀ y : ↥(H.map κ), κ ((H.equivMapOfInjective κ hκ).symm y : G) = (y : A) := fun y =>
    congrArg Subtype.val ((H.equivMapOfInjective κ hκ).apply_symm_apply y)
  refine ⟨φ.comp (H.equivMapOfInjective κ hκ).symm.toMonoidHom,
    hφ.comp (H.equivMapOfInjective κ hκ).symm.surjective, ?_⟩
  ext y
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← he y,
    Subgroup.mem_map_iff_mem hκ]

theorem summand_of_card_eleven [Finite A] {M₀ R V : Subgroup A} (hV : Nat.card V = 2 ^ 11) :
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k →
      k ≤ 2 := by
  intro m k hm _ h
  obtain ⟨-, -, -, -, -, β, hβ, hker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  have hcard := Nat.card_eq_of_bijective β ⟨hinj, hβ⟩
  have hc : Nat.card (Multiplicative (Fin k → Fin m → ZMod 2)) = 2 ^ (k * m) := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card, ← pow_mul, mul_comm]
  rw [hc, hV] at hcard
  have h11 := Nat.pow_right_injective (le_refl 2) hcard
  rcases hm with rfl | rfl <;> omega

theorem isQuasisimple_M24 :
    CFSG.IsQuasisimple CFSG.Quasithin.A312M24.G24 := by
  have hs : IsSimpleGroup CFSG.Quasithin.A312M24.G24 :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hna : ∃ a b : CFSG.Quasithin.A312M24.G24, a * b ≠ b * a := by
    refine CFSG.QuasithinUnique.Vol2Native.A312L.Seven.nonabelian_of_card_not_prime ?_
    rw [show Nat.card CFSG.Quasithin.A312M24.G24 = 244823040 from
      CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1

structure HFacts (H E T : Subgroup A) : Prop where
  EH : E ≤ H
  NE : Subgroup.normalizer (E : Set A) = H
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  sq : ∀ a ∈ E, a * a = 1
  card : Nat.card E = 2 ^ 11
  unique : ∀ B : Subgroup A, B ≤ T → (∀ a ∈ B, a * a = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
    2 ^ 11 ≤ Nat.card B → B = E
  min : ∀ N : Subgroup A, N ≤ E → H ≤ Subgroup.normalizer (N : Set A) → N = ⊥ ∨ N = E
  max : ∀ N : Subgroup A, E ≤ N → N ≤ H → H ≤ Subgroup.normalizer (N : Set A) → N = E ∨ N = H
  CE : H ⊓ Subgroup.centralizer (E : Set A) ≤ E
  quot : ∃ ψ : ↥H →* CFSG.Quasithin.A312M24.G24, Function.Surjective ψ ∧ ψ.ker = E.subgroupOf H

namespace HFacts

variable {H E T : Subgroup A} (F : HFacts H E T)
include F

theorem elemAb : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (F.comm a a.2 b b.2)⟩⟩, fun a ha => by rw [pow_two]; exact F.sq a ha⟩

theorem pGroup : IsPGroup 2 ↥E := fun g => ⟨1, Subtype.ext (by
  rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
  exact F.sq g g.2)⟩

end HFacts

theorem max_Hj :
    ∀ K : Subgroup G₀, CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11 ≤ K →
      K ≤ CFSG.Sporadic.J4.Hj → CFSG.Sporadic.J4.Hj ≤ Subgroup.normalizer (K : Set G₀) →
      K = CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11 ∨ K = CFSG.Sporadic.J4.Hj := by
  have : IsSimpleGroup CFSG.Quasithin.A312M24.G24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  exact simple_of_surj CFSG.Quasithin.J4Fam.fHj CFSG.Quasithin.J4Fam.fHj_surjective
    CFSG.Quasithin.J4Fam.ker_fHj

theorem hFacts [Finite A]
    {κ : G₀ →* A} (hκ : Iso κ) :
    HFacts (CFSG.Sporadic.J4.Hj.map κ) ((CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11).map κ)
      (CFSG.Sporadic.J4.QT.P0.map κ) := by
  have LD := CFSG.EvenSporadicStandard.J4Std.localData_J4 κ hκ.inj
  have hNE : Subgroup.normalizer
      (((CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11).map κ : Subgroup A) : Set A) =
      CFSG.Sporadic.J4.Hj.map κ := by
    rw [← hκ.map_normalizer, CFSG.Sporadic.J4.QT.normalizer_Eg_eq_Hj CFSG.Sporadic.J4.j4Facts]
  refine ⟨Subgroup.map_mono CFSG.Sporadic.J4.QT.Eg_le_Hj, hNE, LD.U_comm, LD.U_sq, LD.card_U,
    LD.unique, ?_, simple_map κ hκ.inj max_Hj, ?_,
    exists_surj_map κ hκ.inj CFSG.Quasithin.J4Fam.fHj CFSG.Quasithin.J4Fam.fHj_surjective
      CFSG.Quasithin.J4Fam.ker_fHj⟩
  · intro N hNE' hHN
    refine LD.irred N hNE' fun g hg d hd => ?_
    have hgN : g ∈ Subgroup.normalizer
        (((CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11).map κ : Subgroup A) : Set A) :=
      Subgroup.mem_normalizer_iff.mpr (CFSG.EvenSporadicStandard.J4Std.mem_Hloc.mp hg).2
    rw [hNE] at hgN
    exact (Subgroup.mem_normalizer_iff.mp (hHN hgN) d).mp hd
  · rintro x ⟨-, hxC⟩
    exact LD.selfCentralizing x (MonoidHom.mem_range.mpr (hκ.surj x)) fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hxC u hu).symm

theorem exists_le_P0 [Finite A]
    {f : G₀ →* A} (hf : Iso f) {R : Subgroup A} (hR : IsPGroup 2 ↥R) :
    ∃ κ : G₀ →* A, Iso κ ∧ R ≤ CFSG.Sporadic.J4.QT.P0.map κ := by
  have LD := CFSG.EvenSporadicStandard.J4Std.localData_J4 f hf.inj
  have hsyl : IsSylowTwoOf (CFSG.Sporadic.J4.QT.P0.map f) ⊤ := by
    rw [← hf.range]
    exact ⟨LD.T0_le_L, LD.T0_pGroup, LD.T0_index_odd⟩
  obtain ⟨x, -, hx⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hsyl le_top hR
  refine ⟨(MulAut.conj x).toMonoidHom.comp f, hf.conj x, ?_⟩
  rw [← Subgroup.map_map]
  exact hx

theorem caseA [Finite A]
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f)
    (hB : ∃ B : Subgroup A, B ≤ R ∧ IsElemAbelian 2 B ∧ 2 ^ 11 ≤ Nat.card B) :
    Concl S M₀ R M V := by
  obtain ⟨κ, hκ, hRT⟩ := exists_le_P0 hf h.hR2
  have F := hFacts hκ
  generalize CFSG.Sporadic.J4.Hj.map κ = H at F
  generalize (CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11).map κ = E at F
  generalize CFSG.Sporadic.J4.QT.P0.map κ = T at F hRT
  have hsq : ∀ {B : Subgroup A}, IsElemAbelian 2 B → ∀ a ∈ B, a * a = 1 := fun hB a ha => by
    rw [← pow_two]
    exact hB.2 a ha
  have hcomm : ∀ {B : Subgroup A}, IsElemAbelian 2 B → ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
    fun hB a ha b hb => congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨B, hBR, hBe, hBc⟩ := hB
  have hER : E ≤ R := F.unique B (hBR.trans hRT) (hsq hBe) (hcomm hBe) hBc ▸ hBR
  have hEe : IsElemAbelian 2 E := F.elemAb
  have hEmax : CFSG.Quasithin.IsMaxElemAbelian R E := by
    refine ⟨hER, hEe, fun B' hB'R hB' => ?_⟩
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hB'E := F.unique B' (hB'R.trans hRT) (hsq hB') (hcomm hB') (F.card ▸ hlt'.le)
    rw [hB'E] at hlt'
    exact lt_irrefl _ hlt'
  have hJ : CFSG.Quasithin.thompsonJ R = E := thompsonJ_eq_of_unique hEmax fun B' hB' =>
    F.unique B' (hB'.1.trans hRT) (hsq hB'.2.1) (hcomm hB'.2.1)
      (by rw [← F.card]; exact hB'.2.2 E hER hEe)
  have hHM : H ≤ M := by
    have := h.hJ
    rwa [hJ, F.NE] at this
  have hNRH : Subgroup.normalizer (R : Set A) ≤ H := by
    intro x hx
    rw [← F.NE, Subgroup.mem_normalizer_iff_map_conj_eq]
    have hinj : Function.Injective (MulAut.conj x : A →* A) := (MulAut.conj x).injective
    have hEx : E.map (MulAut.conj x : A →* A) ≤ R := by
      have := Subgroup.map_mono (f := (MulAut.conj x : A →* A)) hER
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq.mp hx] at this
    refine F.unique _ (hEx.trans hRT) ?_ ?_
      ((Subgroup.card_map_of_injective hinj).trans F.card).ge
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, F.sq a ha, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, F.comm a ha b hb]
  have hM₀eq : M₀ = H := eq_of_perfect_normal F.EH F.NE.ge F.comm F.min F.max F.CE
    (h.hM₀R.trans hNRH) (hHM.trans h.hMN) h.hper h.hM₀ne
  have hE2 : IsPGroup 2 ↥E := F.pGroup
  have hH2 : ¬ IsPGroup 2 ↥H := fun h2 =>
    h.hM₀ne (eq_bot_of_perfect_of_isPGroup h.hper (by rw [hM₀eq]; exact h2))
  have hOE : pCoreOf 2 H = E := pCoreOf_eq_of_max F.EH F.NE.ge hE2 F.max hH2
  have hVE : V = E := by
    have hVO := h.hVO
    have hVn := h.hM₀V
    rw [hM₀eq, hOE] at hVO
    rw [hM₀eq] at hVn
    exact (F.min V hVO hVn).resolve_left h.hVne
  have hE1 : E ≠ ⊥ := by rw [← hVE]; exact h.hVne
  obtain ⟨ψ, hψ, hψk⟩ := F.quot
  have hpc : CFSG.pCore 2 ↥H = ψ.ker := by rw [hψk, ← Hex.pCoreOf_subgroupOf', hOE]
  have eQ : ModO2 H ≃* CFSG.Quasithin.A312M24.G24 :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hshort : IsShort2 H := isShort2_of_irred F.NE.ge F.comm F.sq hE1 F.min F.CE hOE
    (hM₀eq ▸ h.hper) (hM₀eq ▸ h.hM₀ne)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm isQuasisimple_M24)
  have hext : CFSG.Quasithin.C31Case6M24 M H := by
    show IsExt ↥(conjClosure H M) _ _
    rw [conjClosure_eq_self' (hM₀eq ▸ h.hMN)]
    refine ⟨ψ.ker, inferInstance, ?_, ⟨QuotientGroup.quotientKerEquivOfSurjective ψ hψ⟩⟩
    rw [hψk]
    exact CFSG.Quasithin.J4Fam.isE2_of_elementary E F.comm F.sq F.card |>.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe F.EH).symm
  subst hM₀eq hVE
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨h.hSs, Or.inl hext⟩))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.hSs, hshort, Or.inl ⟨⟨eQ⟩, hext⟩⟩))))),
    summand_of_card_eleven F.card⟩

end CFSG.Quasithin.KGC31.J4

end
