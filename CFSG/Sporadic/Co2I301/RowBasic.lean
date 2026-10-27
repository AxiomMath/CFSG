module

public import CFSG.Sporadic.Co2I301.Spec
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271 CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QP45)


private theorem B1_le_locC : B1 ≤ locC := by
  obtain ⟨hd, -, hb2, hb3, -, -⟩ := gens_mem_locC
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  exacts [hd, hb2, hb3]

theorem row_hR : IsExtraSpec2 (locQ.subgroupOf co2P) ∧
    Nat.card (locQ.subgroupOf co2P) = 2 ^ Row.co2.rexp := by
  have e : ↥(locQ.subgroupOf locC) ≃* ↥(locQ.subgroupOf co2P) :=
    (Subgroup.subgroupOfEquivOfLe locQ_le_C).trans
      (Subgroup.subgroupOfEquivOfLe (locQ_le_C.trans locC_le_P)).symm
  obtain ⟨h2, hc, hf, hz⟩ :=
    CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv e qc_extraspecial
  refine ⟨⟨h2, hc.trans hf.symm, hf, hz⟩, ?_⟩
  rw [← Nat.card_congr e.toEquiv, card_qc]
  rfl

theorem row_hB : IsElemAbelian Row.co2.prime (B1.subgroupOf co2P) ∧
    Nat.card (B1.subgroupOf co2P) = Row.co2.prime ^ (Row.co2.rank - 1) := by
  obtain ⟨-, hdb2, hdb3, -, -, hb23, -⟩ := commute_facts
  obtain ⟨hd3, -, hb2, hb3, -⟩ := pow_facts
  obtain ⟨⟨hcomm, hpow⟩, hcard⟩ :=
    isElemAbelian_closure_three hdb2 hdb3 hb23 hd3 hb2 hb3 indep_facts
  haveI : IsMulCommutative ↥B1 := hcomm
  have e : ↥(B1.subgroupOf co2P) ≃* ↥B1 :=
    Subgroup.subgroupOfEquivOfLe (B1_le_locC.trans locC_le_P)
  refine ⟨⟨isMulCommutative_iff.2 fun a b => e.injective ?_, fun g hg => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm' (e a) (e b)
  · show g ^ 3 = 1
    have h : (g : Equiv.Perm (Fin 2300)) ^ 3 = 1 := hpow _ hg
    exact Subtype.ext (by simpa using h)
  · exact (Nat.card_congr e.toEquiv).trans hcard

theorem row_hBN : B1.subgroupOf co2P ≤
    Subgroup.normalizer ((locQ.subgroupOf co2P : Subgroup ↥co2P) : Set ↥co2P) := by
  have hconj : ∀ c ∈ locC, ∀ q ∈ locQ, c * q * c⁻¹ ∈ locQ := fun c hc q hq =>
    Subgroup.mem_subgroupOf.1
      (locQ_normal.conj_mem ⟨q, locQ_le_C hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩)
  intro b hb
  have hbC : (b : Equiv.Perm (Fin 2300)) ∈ locC := B1_le_locC (Subgroup.mem_subgroupOf.1 hb)
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨fun hq => Subgroup.mem_subgroupOf.2
    (hconj _ hbC _ (Subgroup.mem_subgroupOf.1 hq)), fun hq => ?_⟩
  have h := hconj _ (inv_mem hbC) _ (Subgroup.mem_subgroupOf.1 hq)
  rw [Subgroup.mem_subgroupOf]
  simpa [mul_assoc] using h

theorem row_hd (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    x ∈ B1.subgroupOf co2P ∧ x ≠ 1 := by
  refine ⟨?_, fun h => pow_facts.2.1 ?_⟩
  · rw [Subgroup.mem_subgroupOf, hx]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [← hx, h]
    rfl

private theorem nonempty_Lsub_equiv :
    Nonempty (↥(Lsub.subgroupOf co2P) ≃* ↥QP45.originalSubgroup) := by
  obtain ⟨-, -, -, hcard, hLC, -, -, hrels⟩ := co2CaseB_spec
  obtain ⟨eL⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
  exact ⟨(Subgroup.subgroupOfEquivOfLe fun l hl => (hLC hl).2).trans eL⟩

private theorem glaPComponent_XB (hXB : co2XB ∈ co2P) :
    GLAPComponent 3 (Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P))
        (Lsub.subgroupOf co2P) ∧
      ∀ I, GLAPComponent 3 (Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P)) I →
        I = Lsub.subgroupOf co2P := by
  obtain ⟨-, -, -, -, hLC, hLn, hcent, -⟩ := co2CaseB_spec
  obtain ⟨e'⟩ := nonempty_Lsub_equiv
  have hLP : Lsub ≤ co2P := fun l hl => (hLC hl).2
  haveI hs : IsSimpleGroup ↥(Lsub.subgroupOf co2P) := isSimpleGroup_of_equiv_QP45 e'
  have hnab := nonabelian_of_equiv_QP45 e'
  have hp3 := three_dvd_card_of_equiv_QP45 e'
  have hmapC := map_centralizer_subtype' co2P (⟨co2XB, hXB⟩ : ↥co2P)
  have hLC' : Lsub.subgroupOf co2P ≤
      Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P) := by
    intro l hl
    have hl1 : (l : Equiv.Perm (Fin 2300)) ∈
        Subgroup.centralizer ({co2XB} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P := hLC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  have hgC : ∀ g ∈ Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P),
      (g : Equiv.Perm (Fin 2300)) ∈
        Subgroup.centralizer ({co2XB} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P := fun g hg => by
    have : (g : Equiv.Perm (Fin 2300)) ∈
        (Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P)).map co2P.subtype :=
      ⟨g, hg, rfl⟩
    rw [hmapC] at this
    exact this
  have hLn' : ∀ g ∈ Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P),
      ∀ l ∈ Lsub.subgroupOf co2P, g * l * g⁻¹ ∈ Lsub.subgroupOf co2P := by
    intro g hg l hl
    have h := hLn _ (hgC g hg) _ (Subgroup.mem_subgroupOf.1 hl)
    rw [Subgroup.mem_subgroupOf]
    simpa using h
  have hLq : CFSG.Open.IsQuasisimple ↥(Lsub.subgroupOf co2P) :=
    CFSG.HardMathSupport.Dickson.I271.isQuasisimple_of_simple_nonab hnab
  have hcentP : IsPGroup 3 ↥(Subgroup.centralizer ({(⟨co2XB, hXB⟩ : ↥co2P)} : Set ↥co2P) ⊓
      Subgroup.centralizer ((Lsub.subgroupOf co2P : Subgroup ↥co2P) : Set ↥co2P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcC := hgC c.1 (Subgroup.mem_inf.1 c.2).1
    have hcomm : ∀ l ∈ Lsub, l * ((c : ↥co2P) : Equiv.Perm (Fin 2300)) =
        ((c : ↥co2P) : Equiv.Perm (Fin 2300)) * l := by
      intro l hl
      have hlL : (⟨l, hLP hl⟩ : ↥co2P) ∈ Lsub.subgroupOf co2P := hl
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ hlL)
    have h0 := hcent _ hcC hcomm
    have h1 : (c : ↥co2P) ^ 3 = 1 := Subtype.ext (by simpa using h0)
    rw [pow_one]
    exact Subtype.ext h1
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three hLC' hLn' hLq hp3
    hcentP
  exact ⟨glaPComponent_of_normal_quasisimple hLC' hLn' hLq hcore, fun I hI =>
    eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three hLC' hLn' hLq hcore hcentP hI⟩

private theorem glaPLayer_map_of_unique {Q Q' : Type} [Group Q] [Group Q'] [Finite Q]
    [Finite Q'] {p : ℕ} (hp : p.Prime) (φ : Q ≃* Q') {X L : Subgroup Q}
    (hL : GLAPComponent p X L) (hu : ∀ J, GLAPComponent p X J → J = L) :
    GLAPLayer p (X.map φ.toMonoidHom) = L.map φ.toMonoidHom := by
  refine glaPLayer_eq_of_unique_glaPComponent (glaPComponent_map_equiv hp φ hL) fun J hJ => ?_
  have hX : (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X :=
    (Subgroup.map_symm_eq_iff_map_eq X (e := φ)).2 rfl
  have h1 := glaPComponent_map_equiv hp φ.symm hJ
  rw [hX] at h1
  exact ((Subgroup.map_symm_eq_iff_map_eq L (e := φ)).1 (hu _ h1)).symm

private theorem map_conj_Lsub :
    (Lsub.subgroupOf co2P).map (MulAut.conj (⟨hP, hP_mem⟩ : ↥co2P)).toMonoidHom =
      U0.subgroupOf co2P := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨l, hl, rfl⟩)
  · intro hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    have hly' : hP * l * hP⁻¹ = (y : Equiv.Perm (Fin 2300)) := hly
    have hlP : l ∈ co2P := by
      have hl' : l = hP⁻¹ * y * hP := by
        rw [← hly']
        group
      rw [hl']
      exact mul_mem (mul_mem (inv_mem hP_mem) y.2) hP_mem
    exact ⟨⟨l, hlP⟩, hl, Subtype.ext hly'⟩

theorem row_I (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    rowIOf Row.co2.prime x = U0.subgroupOf co2P := by
  obtain ⟨-, -, hXB, -⟩ := co2CaseB_spec
  have hφx : MulAut.conj (⟨hP, hP_mem⟩ : ↥co2P) ⟨co2XB, hXB⟩ = x :=
    Subtype.ext (by rw [hx, dP_eq]; rfl)
  obtain ⟨hcomp, huniq⟩ := glaPComponent_XB hXB
  have h := glaPLayer_map_of_unique Nat.prime_three (MulAut.conj (⟨hP, hP_mem⟩ : ↥co2P)) hcomp
    huniq
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton, hφx, map_conj_Lsub] at h
  exact h

private def pp2 : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

private theorem valid_twistedA_three : (TauCeti.LieTypeIndex.twistedA 3 pp2).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

private theorem catalogIs_isU4of_two {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (e : X ≃* StatedProj (StatedSU 4 (2 ^ 1) K)) :
    catalogIs X (isU4of 2) := by
  have hc2 : TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 2 :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 pp2
  have hf2 : TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 1 :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 pp2
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 pp2
    valid_twistedA_three
  have hq : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 pp2, valid_twistedA_three⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩ =
        2 ^ 1 := by
    rw [hc2, hf2]
  rw [← hq] at e
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
    ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
      (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) :=
    Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  refine ⟨.lie ⟨.twistedA 3 pp2, valid_twistedA_three⟩, ?_, ⟨?_⟩⟩
  · show pp2.card = 2
    rw [TauCeti.PrimePower.card_def]
    norm_num [pp2]
  · exact (e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 4 _)).trans eq.symm

private theorem catalogIs_isPSp43_of_equiv_QP45 {T : Type} [Group T]
    (e : T ≃* ↥QP45.originalSubgroup) : catalogIs T isPSp43 := by
  obtain ⟨i, hi, he⟩ := catalogIs_isU4of_two (K := CFSG.Blueprint.Fischer.K)
    (CFSG.Fischer.Classification.Unitary.card_K.trans (by norm_num))
    (e.trans (CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.symm.trans
      (CFSG.GH74.Exceptional.psp43EquivU2.trans CFSG.GH74.Exceptional.u2FourEquiv)))
  exact ⟨i, Or.inl hi, he⟩

private theorem nonempty_U0_equiv :
    Nonempty (↥(U0.subgroupOf co2P) ≃* ↥QP45.originalSubgroup) := by
  obtain ⟨e⟩ := nonempty_Lsub_equiv
  rw [← map_conj_Lsub]
  exact ⟨((MulAut.conj (⟨hP, hP_mem⟩ : ↥co2P)).subgroupMap _).symm.trans e⟩

theorem row_hI (x : ↥co2P) (hx : (x : Equiv.Perm (Fin 2300)) = dP) :
    RowI .co2 Row.co2.prime (rowIOf Row.co2.prime x) := by
  rw [row_I x hx]
  obtain ⟨e⟩ := nonempty_U0_equiv
  show IsTypeWithCenter 3 (U0.subgroupOf co2P) isPSp43 1
  exact isTypeWithCenter_of_isSimple Nat.prime_three (isSimpleGroup_of_equiv_QP45 e)
    (nonabelian_of_equiv_QP45 e) (three_dvd_card_of_equiv_QP45 e)
    (catalogIs_isPSp43_of_equiv_QP45 e)

end CFSG.Sporadic.Co2I301
