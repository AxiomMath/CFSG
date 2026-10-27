module

public import CFSG.Quasithin.MS93.S38G2Ker
public import CFSG.Quasithin.MS93.S33Base
public import CFSG.Quasithin.Background.SmithB42U33Gen
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1More13
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.MS93.S33Trans
public import CFSG.Quasithin.MS93.S38G2Model
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.MS93
open scoped commutatorElement

theorem IsOffG2.card_eq {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : IsOffG2 B) :
    Nat.card B = 8 ∧ Nat.card (fixV (B.map (g2QAct (ZMod 2)))) = 8 := by
  obtain ⟨hB1, hBc, hB2, hff⟩ := hB
  have hinj : Function.Injective (g2QAct (ZMod 2)) := g2QAct_injective
  have hle : B.map (g2QAct (ZMod 2)) ≤ (g2QAct (ZMod 2)).range := Subgroup.map_le_range _ _
  have hne : B.map (g2QAct (ZMod 2)) ≠ ⊥ := fun h =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)
  have hea : IsElemAbelian2 (B.map (g2QAct (ZMod 2))) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hB2 b hb, map_one]
  have hcard : Nat.card (B.map (g2QAct (ZMod 2))) = Nat.card B :=
    Subgroup.card_map_of_injective hinj
  obtain ⟨h1, h2⟩ := B42U33.offender_exact hle hne hea (by rw [hcard]; exact hff)
  rw [hcard] at h1
  exact ⟨h1, h2⟩

theorem IsOffG2.commV_eq {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : IsOffG2 B) :
    commV (B.map (g2QAct (ZMod 2))) = fixV (B.map (g2QAct (ZMod 2))) := by
  obtain ⟨hB1, hBc, hB2, hff⟩ := hB
  have hinj : Function.Injective (g2QAct (ZMod 2)) := g2QAct_injective
  refine offenderClaim_two_Q _ (Subgroup.map_le_range _ _) (fun h =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)) ⟨?_, ?_⟩ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hff

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem f_mul_inv_conv (hR : G2Rep h f φ) (v : IntMod (Uq M T L) h.isElemAbelian_Uq) (m : ↥M) :
    f (v * (convM h m v)⁻¹) = f v * (g2QAct (ZMod 2) (φ m) (f v))⁻¹ := by
  rw [map_mul, map_inv, hR.equiv]

theorem commutator_mem_zq_iff (hR : G2Rep h f φ) (v : IntMod (Uq M T L) h.isElemAbelian_Uq)
    (m : ↥M) : ⁅v.val, (m : G)⁆ ∈ Zq M L ↔ g2QAct (ZMod 2) (φ m) (f v) = f v := by
  have e : (v * (convM h m v)⁻¹).val = ⁅v.val, (m : G)⁆ := by
    rw [IntMod.val_mul, IntMod.val_inv, convM_apply_val, commutatorElement_def]
    group
  rw [← e, ← hR.ker, f_mul_inv_conv hR, mul_inv_eq_one, eq_comm]

abbrev imB (φ : ↥M →* ↥(quasithinG2 (ZMod 2))) (E : Subgroup G) :
    Subgroup ↥(quasithinG2 (ZMod 2)) := (E.subgroupOf M).map φ

theorem card_imB (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T) :
    Nat.card (imB φ E) = (pCoreOf 2 M).relIndex E := by
  have hEM : E ≤ M := hET.trans h.le
  set ψ : ↥(E.subgroupOf M) →* ↥(quasithinG2 (ZMod 2)) := φ.comp (E.subgroupOf M).subtype
  have hrange : ψ.range = imB φ E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ψ.ker = ((pCoreOf 2 M).subgroupOf M).subgroupOf (E.subgroupOf M) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hR.eq_one_iff_mem_pCoreOf (hET (Subgroup.mem_subgroupOf.mp x.2))
  rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.relIndex,
    Subgroup.relIndex_subgroupOf hEM]

abbrev cU (h : PUHyp M T L) (E : Subgroup G) : Subgroup (IntMod (Uq M T L) h.isElemAbelian_Uq) :=
  (Subgroup.centralizer (E : Set G)).comap (intModVal h.isElemAbelian_Uq)

theorem index_cU (h : PUHyp M T L) (E : Subgroup G) :
    (cU h E).index = (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := rfl

theorem cU_le_comap (hR : G2Rep h f φ) (E : Subgroup G) :
    cU h E ≤ (fixV ((imB φ E).map (g2QAct (ZMod 2)))).comap f := by
  intro v hv
  rw [Subgroup.mem_comap]
  rintro _ ⟨b, ⟨e, he, rfl⟩, rfl⟩
  rw [← hR.equiv]
  congr 1
  apply IntMod.val_injective
  rw [convM_apply_val]
  have hc : (e : G) * v.val = v.val * (e : G) :=
    Subgroup.mem_centralizer_iff.mp hv e (Subgroup.mem_subgroupOf.mp he)
  rw [hc, mul_inv_cancel_right]

theorem index_fixV_le (hR : G2Rep h f φ) (E : Subgroup G) :
    (fixV ((imB φ E).map (g2QAct (ZMod 2)))).index ≤
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  have h1 := Subgroup.index_comap_of_surjective (fixV ((imB φ E).map (g2QAct (ZMod 2)))) hR.surj
  rw [← h1, ← index_cU h E]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le (cU_le_comap hR E))

omit [Finite G] in
theorem imB_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    ∀ a ∈ imB φ E, ∀ b ∈ imB φ E, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  have hab : (a : G) * b = b * a := congrArg Subtype.val
    (hE.1.1.1 ⟨a, Subgroup.mem_subgroupOf.mp ha⟩ ⟨b, Subgroup.mem_subgroupOf.mp hb⟩)
  exact Subtype.ext hab

omit [Finite G] in
theorem imB_sq {E : Subgroup G} (hE : IsElemAbelian 2 E) : ∀ b ∈ imB φ E, b ^ 2 = 1 := by
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_pow]
  have : b ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hb))
  rw [this, map_one]

theorem relIndex_le (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 2 E) :
    (pCoreOf 2 M).relIndex E ≤ (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have h1 := card_mul_card_fixV_le (imB_comm (φ := φ) hE) (imB_sq (φ := φ) hE)
  rw [card_imB hR hET] at h1
  have h2 := Subgroup.index_mul_card (fixV ((imB φ E).map (g2QAct (ZMod 2))))
  have h3 := index_fixV_le hR E
  have hpos : 0 < Nat.card (fixV ((imB φ E).map (g2QAct (ZMod 2)))) := Nat.card_pos
  have h4 : (pCoreOf 2 M).relIndex E * Nat.card (fixV ((imB φ E).map (g2QAct (ZMod 2)))) ≤
      (fixV ((imB φ E).map (g2QAct (ZMod 2)))).index *
        Nat.card (fixV ((imB φ E).map (g2QAct (ZMod 2)))) := by
    rw [h2]
    exact h1
  exact (Nat.le_of_mul_le_mul_right h4 hpos).trans h3

theorem isOffG2_of_relIndex_eq (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T)
    (hE : IsElemAbelian 2 E) (hEQ : ¬ E ≤ pCoreOf 2 M)
    (heq : (pCoreOf 2 M).relIndex E = (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L)) :
    IsOffG2 (imB φ E) := by
  refine ⟨fun hbot => hEQ fun e he => ?_, imB_comm (φ := φ) hE, imB_sq (φ := φ) hE, ?_⟩
  · have hmem : φ ⟨e, hET.trans h.le he⟩ ∈ imB φ E :=
      ⟨⟨e, hET.trans h.le he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hR.eq_one_iff_mem_pCoreOf (m := ⟨e, hET.trans h.le he⟩) (hET he)).mp hmem
  · rw [card_imB hR hET, heq]
    have h2 := Subgroup.index_mul_card (fixV ((imB φ E).map (g2QAct (ZMod 2))))
    rw [← h2]
    exact Nat.mul_le_mul_right _ (index_fixV_le hR E)

omit [Finite G] in
theorem imB_le {E : Subgroup G} (hET : E ≤ T) : imB φ E ≤ (T.subgroupOf M).map φ := by
  rintro _ ⟨e, he, rfl⟩
  exact ⟨e, Subgroup.mem_subgroupOf.mpr (hET (Subgroup.mem_subgroupOf.mp he)), rfl⟩

theorem fixV_le_map (hR : G2Rep h f φ) {E : Subgroup G} (hoff : IsOffG2 (imB φ E)) :
    fixV ((imB φ E).map (g2QAct (ZMod 2))) ≤
      ((⁅Z0q M T, E⁆).comap (intModVal h.isElemAbelian_Uq)).map f := by
  rw [← hoff.commV_eq, commV, Subgroup.closure_le]
  rintro _ ⟨_, ⟨b, ⟨e, he, rfl⟩, rfl⟩, q, rfl⟩
  obtain ⟨v, rfl⟩ := hR.surj q
  refine ⟨convM h e v * v⁻¹, ?_, ?_⟩
  · have e1 : intModVal h.isElemAbelian_Uq (convM h e v * v⁻¹) = ⁅(e : G), v.val⁆ := by
      change (convM h e v * v⁻¹).val = _
      rw [IntMod.val_mul, IntMod.val_inv, convM_apply_val, commutatorElement_def]
    rw [SetLike.mem_coe, Subgroup.mem_comap, e1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp he)
      (Uq_le_Z0q h.L_le v.val_mem)
  · rw [map_mul, map_inv, hR.equiv]

theorem mem_sup_of_map_mem (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T) {y : G}
    (hy : y ∈ T) (hyB : φ ⟨y, h.le hy⟩ ∈ imB φ E) : y ∈ E ⊔ pCoreOf 2 M := by
  obtain ⟨e, he, hee⟩ := hyB
  have heT : (e : G) ∈ T := hET (Subgroup.mem_subgroupOf.mp he)
  have h1 : φ (e⁻¹ * ⟨y, h.le hy⟩) = 1 := by rw [map_mul, map_inv, hee, inv_mul_cancel]
  have h2 : ((e⁻¹ * ⟨y, h.le hy⟩ : ↥M) : G) ∈ pCoreOf 2 M :=
    (hR.eq_one_iff_mem_pCoreOf (m := e⁻¹ * ⟨y, h.le hy⟩) (T.mul_mem (T.inv_mem heT) hy)).mp h1
  have e2 : y = (e : G) * ((e⁻¹ * ⟨y, h.le hy⟩ : ↥M) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e2]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp he) h2

theorem mem_sup_of_commute (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T)
    (hoff : IsOffG2 (imB φ E)) {y : G} (hy : y ∈ T)
    (hyc : ∀ e ∈ E, ⁅y, e⁆ ∈ pCoreOf 2 M) : y ∈ E ⊔ pCoreOf 2 M := by
  refine mem_sup_of_map_mem hR hET hy (mem_of_commute_off (isPGroup_map_subgroupOf φ h.isPGroup)
    (imB_le hET) hoff ⟨⟨y, h.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩ ?_)
  rintro _ ⟨e, he, rfl⟩
  have h1 : φ ⁅(⟨y, h.le hy⟩ : ↥M), e⁆ = 1 :=
    hR.map_pCoreOf (m := ⁅(⟨y, h.le hy⟩ : ↥M), e⁆) (hyc e (Subgroup.mem_subgroupOf.mp he))
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem mem_sup_of_fix (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T)
    (hoff : IsOffG2 (imB φ E)) {y : G} (hy : y ∈ T)
    (hyf : ∀ r ∈ ⁅Z0q M T, E⁆, ⁅r, y⁆ ∈ Zq M L) : y ∈ E ⊔ pCoreOf 2 M := by
  refine mem_sup_of_map_mem hR hET hy (mem_of_fix_off (isPGroup_map_subgroupOf φ h.isPGroup)
    (imB_le hET) hoff ⟨⟨y, h.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩ fun q hq => ?_)
  obtain ⟨v, hv, rfl⟩ := fixV_le_map hR hoff hq
  exact (hR.commutator_mem_zq_iff v ⟨y, h.le hy⟩).mp (hyf _ hv)

theorem mem_commutator_of_fix (hR : G2Rep h f φ) {E : Subgroup G} (hoff : IsOffG2 (imB φ E))
    (hW : Uq M T L ⊓ Zq M L ≤ ⁅Z0q M T, E⁆) {u : G} (hu : u ∈ Uq M T L)
    (huf : ∀ e ∈ E, ⁅u, e⁆ ∈ Zq M L) : u ∈ ⁅Z0q M T, E⁆ := by
  set v : IntMod (Uq M T L) h.isElemAbelian_Uq := IntMod.mk _ ⟨u, hu⟩ with hv
  have hfv : f v ∈ fixV ((imB φ E).map (g2QAct (ZMod 2))) := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact (hR.commutator_mem_zq_iff v e).mp (huf e (Subgroup.mem_subgroupOf.mp he))
  obtain ⟨r, hr, hrv⟩ := fixV_le_map hR hoff hfv
  have h1 : f (r⁻¹ * v) = 1 := by rw [map_mul, map_inv, hrv, inv_mul_cancel]
  have h2 : (r⁻¹ * v).val ∈ Zq M L := (hR.ker _).mp h1
  have h3 : (r⁻¹ * v).val ∈ ⁅Z0q M T, E⁆ := hW ⟨(r⁻¹ * v).val_mem, h2⟩
  have e3 : u = r.val * (r⁻¹ * v).val := by
    rw [IntMod.val_mul, IntMod.val_inv, mul_inv_cancel_left]
    rfl
  rw [e3]
  exact Subgroup.mul_mem _ hr h3

theorem card_commutator (hR : G2Rep h f φ) {E : Subgroup G} (hoff : IsOffG2 (imB φ E)) :
    8 ≤ Nat.card ↥⁅Z0q M T, E⁆ := by
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  set R' := (⁅Z0q M T, E⁆).comap (intModVal h.isElemAbelian_Uq) with hR'
  have h1 : Nat.card (fixV ((imB φ E).map (g2QAct (ZMod 2)))) ≤ Nat.card (R'.map f) :=
    Subgroup.card_le_of_le (fixV_le_map hR hoff)
  have h2 : Nat.card (R'.map f) ≤ Nat.card R' := by
    refine Nat.card_le_card_of_surjective (fun r : ↥R' => (⟨f r, r, r.2, rfl⟩ : ↥(R'.map f)))
      ?_
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  have h3 : Nat.card R' ≤ Nat.card ↥⁅Z0q M T, E⁆ := by
    refine Nat.card_le_card_of_injective
      (fun r : ↥R' => (⟨intModVal h.isElemAbelian_Uq r, r.2⟩ : ↥⁅Z0q M T, E⁆)) ?_
    intro a b hab
    have hab' := congrArg (fun x : ↥⁅Z0q M T, E⁆ => (x : G)) hab
    exact Subtype.ext (IntMod.val_injective hab')
  rw [hoff.card_eq.2] at h1
  omega

theorem relIndex_eq_eight (hR : G2Rep h f φ) {E : Subgroup G} (hET : E ≤ T)
    (hoff : IsOffG2 (imB φ E)) : (pCoreOf 2 M).relIndex E = 8 := by
  rw [← card_imB hR hET]
  exact hoff.card_eq.1

theorem exists_two_gen
    (hR : G2Rep h f φ) {E : Subgroup G} (hoff : IsOffG2 (imB φ E)) :
    ∃ l₁ ∈ L, ∃ l₂ ∈ L, L ≤ E.map (MulAut.conj l₁).toMonoidHom ⊔
      E.map (MulAut.conj l₂).toMonoidHom ⊔ pCoreOf 2 M := by
  have h8 : Nat.card (imB φ E) = 8 := hoff.card_eq.1
  obtain ⟨hB1, hBc, hB2, -⟩ := hoff
  obtain ⟨r, m, hr, -, -, hmr, d, hd, hle⟩ := B42U33.shortGen hB1 hBc hB2
  have hr3 : r = 3 := by
    rw [h8] at hr
    have h8' : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8'] at hr
    exact (Nat.pow_right_injective (le_refl 2) hr).symm
  have hm2 : m ≤ 2 := by
    subst hr3
    omega
  choose l hlL hl using fun i => hR.L_onto (d i) (hd i)
  let g : ℕ → G := fun k => if hk : k < m then (l ⟨k, hk⟩ : G) else 1
  have hgL : ∀ k, g k ∈ L := by
    intro k
    by_cases hk : k < m
    · simp only [g, hk, ↓reduceDIte]
      exact hlL _
    · simp only [g, hk, ↓reduceDIte]
      exact L.one_mem
  have hgi : ∀ i : Fin m, g i.val = (l i : G) := fun i => by
    simp only [g, i.isLt, ↓reduceDIte]
  set P := E.map (MulAut.conj (g 0)).toMonoidHom ⊔ E.map (MulAut.conj (g 1)).toMonoidHom ⊔
    pCoreOf 2 M with hP
  refine ⟨g 0, hgL 0, g 1, hgL 1, hR.le_of_le_map le_sup_right (hle.trans ?_)⟩
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨b, ⟨e, he, rfl⟩, rfl⟩ := hi
  have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
  have hmem : (l i : G) * e * (l i : G)⁻¹ ∈ P := by
    have hconj : ∀ k, g k = (l i : G) →
        (l i : G) * e * (l i : G)⁻¹ ∈ E.map (MulAut.conj (g k)).toMonoidHom := by
      intro k hk
      rw [hk]
      exact ⟨e, heE, rfl⟩
    rcases Nat.lt_or_ge i.val 1 with h0 | h1
    · have : i.val = 0 := by omega
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hconj 0 (by rw [← this]; exact hgi i)))
    · have : i.val = 1 := by have := i.isLt; omega
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hconj 1 (by rw [← this]; exact hgi i)))
  refine ⟨l i * e * (l i)⁻¹, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
  simp only [map_mul, map_inv, hl i, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem exists_comm_D (hR : G2Rep h f φ) :
    ∃ K D : Subgroup G, K ≤ T ∧ pCoreOf 2 M ≤ K ∧ pCoreOf 2 M ≤ D ∧ D ≤ T ∧
      (pCoreOf 2 M).relIndex D ≤ 2 ∧
      (∀ E : Subgroup G, E ≤ T → IsOffG2 (imB φ E) → E ≤ K) ∧
      ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ D := by
  obtain ⟨X, z, hXoff, hXc⟩ := exists_comm_off (isPGroup_map_subgroupOf φ h.isPGroup)
  set K : Subgroup G := (X.comap φ).map M.subtype ⊓ T with hK
  have hmemK : ∀ m : ↥M, (m : G) ∈ T → φ m ∈ X → (m : G) ∈ K :=
    fun m hmT hmX => ⟨⟨m, hmX, rfl⟩, hmT⟩
  have hKφ : ∀ a ∈ K, ∃ m : ↥M, (m : G) = a ∧ (m : G) ∈ T ∧ φ m ∈ X := by
    rintro a ⟨⟨m, hm, rfl⟩, hmT⟩
    exact ⟨m, rfl, hmT, hm⟩
  have hQK : pCoreOf 2 M ≤ K := fun q hq =>
    hmemK ⟨q, pCoreOf_le' M hq⟩ (h.pCore_le hq)
      (by rw [hR.map_pCoreOf (m := ⟨q, pCoreOf_le' M hq⟩) hq]; exact X.one_mem)
  have hEK : ∀ E : Subgroup G, E ≤ T → IsOffG2 (imB φ E) → E ≤ K := by
    intro E hET hoff e he
    exact hmemK ⟨e, h.le (hET he)⟩ (hET he) (hXoff _ hoff (imB_le hET)
      ⟨⟨e, h.le (hET he)⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩)
  have hcT : ∀ m n : ↥M, (m : G) ∈ T → (n : G) ∈ T → ((⁅m, n⁆ : ↥M) : G) ∈ T := by
    intro m n hm hn
    change ⁅(m : G), (n : G)⁆ ∈ T
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hm hn) (T.inv_mem hm)) (T.inv_mem hn)
  by_cases hz : ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ = z ∧ z ≠ 1
  · obtain ⟨x, hx, y, hy, hxy, hz1⟩ := hz
    have hz2 : z ^ 2 = 1 := by
      rcases hXc y hy x hx with h1 | h1
      · exfalso
        apply hz1
        rw [← hxy, ← commutatorElement_inv, h1, inv_one]
      · rw [← commutatorElement_inv, hxy] at h1
        calc z ^ 2 = z * z := pow_two z
          _ = z * z⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel z
    set D : Subgroup G := ((Subgroup.zpowers z).comap φ).map M.subtype ⊓ T with hD
    have hQD : pCoreOf 2 M ≤ D := fun q hq => ⟨⟨⟨q, pCoreOf_le' M hq⟩, by
      rw [SetLike.mem_coe, Subgroup.mem_comap, hR.map_pCoreOf (m := ⟨q, pCoreOf_le' M hq⟩) hq]
      exact Subgroup.one_mem _, rfl⟩, h.pCore_le hq⟩
    have hDT : D ≤ T := inf_le_right
    refine ⟨K, D, inf_le_right, hQK, hQD, hDT, ?_, hEK, ?_⟩
    · rw [← card_imB hR hDT]
      have hle : imB φ D ≤ Subgroup.zpowers z := by
        rintro _ ⟨m, hm, rfl⟩
        obtain ⟨⟨m', hm', he⟩, -⟩ := Subgroup.mem_subgroupOf.mp hm
        have : m' = m := Subtype.ext he
        rw [← this]
        exact hm'
      refine (Subgroup.card_le_of_le hle).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hz2
    · intro a ha b hb
      obtain ⟨m, rfl, hmT, hmX⟩ := hKφ a ha
      obtain ⟨n, rfl, hnT, hnX⟩ := hKφ b hb
      refine ⟨⟨⁅m, n⁆, ?_, rfl⟩, hcT m n hmT hnT⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement]
      rcases hXc _ hmX _ hnX with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1]
        exact Subgroup.mem_zpowers z
  · push Not at hz
    refine ⟨K, pCoreOf 2 M, inf_le_right, hQK, le_rfl, h.pCore_le, ?_, hEK, ?_⟩
    · rw [Subgroup.relIndex_self]
      norm_num
    · intro a ha b hb
      obtain ⟨m, rfl, hmT, hmX⟩ := hKφ a ha
      obtain ⟨n, rfl, hnT, hnX⟩ := hKφ b hb
      have h1 : φ ⁅m, n⁆ = 1 := by
        rw [map_commutatorElement]
        rcases hXc _ hmX _ hnX with h1 | h1
        · exact h1
        · rw [h1]
          exact hz _ hmX _ hnX h1
      exact (hR.eq_one_iff_mem_pCoreOf (m := ⁅m, n⁆) (hcT m n hmT hnT)).mp h1

end G2Rep

end CFSG.Quasithin.MS93.S38G
