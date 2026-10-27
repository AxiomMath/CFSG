module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Center
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Constr
import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTrans
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

namespace Sylow155T51

private theorem card_mul_card_le_of_inf_eq_bot {X : Type*} [Group X] [Finite X]
    {H K M : Subgroup X} (hHK : H ⊓ K = ⊥) (hH : H ≤ M) (hK : K ≤ M) :
    Nat.card H * Nat.card K ≤ Nat.card M := by
  let f : ↥H × ↥K → ↥M := fun p => ⟨(p.1 : X) * (p.2 : X), M.mul_mem (hH p.1.2) (hK p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨h, k⟩ ⟨h', k'⟩ heq
    have heq' : (h : X) * (k : X) = (h' : X) * (k' : X) := congrArg Subtype.val heq
    have hmem : (h' : X)⁻¹ * (h : X) = (k' : X) * (k : X)⁻¹ := by
      calc (h' : X)⁻¹ * (h : X) = (h' : X)⁻¹ * ((h : X) * (k : X)) * (k : X)⁻¹ := by group
        _ = (h' : X)⁻¹ * ((h' : X) * (k' : X)) * (k : X)⁻¹ := by rw [heq']
        _ = (k' : X) * (k : X)⁻¹ := by group
    have hI : (h' : X)⁻¹ * (h : X) ∈ H ⊓ K := by
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem h'.2) h.2, ?_⟩
      rw [hmem]
      exact K.mul_mem k'.2 (K.inv_mem k.2)
    rw [hHK, Subgroup.mem_bot] at hI
    have hhh : (h : X) = (h' : X) := (inv_mul_eq_one.mp hI).symm
    have hkk : (k : X) = (k' : X) := by
      rw [hmem] at hI
      exact (mul_inv_eq_one.mp hI).symm
    exact Prod.ext (Subtype.ext hhh) (Subtype.ext hkk)
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at hle

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_centralizer {B : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (B : Set G)) :
    w ∈ Subgroup.normalizer ((Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  have hw' : w⁻¹ ∈ Subgroup.normalizer (B : Set G) := inv_mem hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx b hb
    have hb' : w⁻¹ * b * w ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp hw' b).mp hb
      rwa [inv_inv] at this
    have h := hx _ hb'
    calc b * (w * x * w⁻¹) = w * ((w⁻¹ * b * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * b * w)) * w⁻¹ := by rw [h]
      _ = w * x * w⁻¹ * b := by group
  · intro hx b hb
    have hb' : w * b * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hw b).mp hb
    have h := hx _ hb'
    calc b * x = w⁻¹ * ((w * b * w⁻¹) * (w * x * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * x * w⁻¹) * (w * b * w⁻¹)) * w := by rw [h]
      _ = x * b := by group

private theorem map_conj_map_conj (H : Subgroup G) (x y : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      H.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_centralizer_component_data (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hT : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoF G)
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) :
    ∃ Y : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
      CFSG.IsComponent Y ∧
      (∀ ψ : (↥(Subgroup.centralizer (B : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) ≃*
          (↥(Subgroup.centralizer (B : Set G)) ⧸
            CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
        Y.map ψ.toMonoidHom = Y) ∧
      (∃ a ∈ A.subgroupOf (Subgroup.centralizer (B : Set G)), a ≠ 1 ∧
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) a ∈ Y) ∧
      ¬ (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ≤ Y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFE := (hT.partTwoF_eq_partTwoE hS).1
  have hAE : A ∈ partTwoE G := hFE ▸ hA
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := hAE.2.1
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hCdef
  have hAC : A ≤ C := by
    intro a ha
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
  have hBC : B ≤ C := hBA.trans hAC
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hZ : Subgroup.center G = ⊥ := by
      rcases hT.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hT.nonabelian
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hBZ : B ≤ Subgroup.center G := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
    rw [hZ, le_bot_iff] at hBZ
    rw [hBZ, Subgroup.card_bot] at hB9
    norm_num at hB9
  have hC4 : SectionFourHyp C := hT.sectionFourHyp hCtop
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hA'ab : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf C) := hAab.subgroupOf C
  have hB'ab : CFSG.Assembly.IsElemAbelian 3 (B.subgroupOf C) := (hAab.mono hBA).subgroupOf C
  have hB'9 : Nat.card (B.subgroupOf C) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv).trans hB9
  have hBZ : B.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp y.2 (x : G) hx).symm)
  have hmaxC : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ U : Subgroup C, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set C)) →
      ∀ E' : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E := by
    rintro E hE hE27 ⟨U, hU1, hU2, hEU⟩ E' hE' hEE'
    have hmem : E.map C.subtype ∈ partTwoF G := by
      rw [hFE]
      refine ⟨hE.map _, ?_, U.map C.subtype, ?_, hU2.map _,
        (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)⟩
      · rw [Subgroup.card_map_of_injective C.subtype_injective, hE27]
      · exact fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U C.subtype_injective).mp h)
    exact Subgroup.map_injective C.subtype_injective
      (hmem.2.1 _ (hE'.map _) (Subgroup.map_mono hEE'))
  have hA'max : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → A.subgroupOf C ≤ E →
      E = A.subgroupOf C := by
    intro E hE hAE'
    have hAEm : A ≤ E.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAE' (show (⟨a, hAC ha⟩ : C) ∈ A.subgroupOf C from ha), rfl⟩
    have hEq : E.map C.subtype = A := hA.2.1 _ (hE.map _) hAEm
    rw [← hEq]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective E).symm
  obtain ⟨Y, hY⟩ := exists_isComponent_of_not_isPConstrained hcon
  have hYaut : ∀ ψ : (↥C ⧸ CFSG.pPrimeCore 3 ↥C) ≃* (↥C ⧸ CFSG.pPrimeCore 3 ↥C),
      Y.map ψ.toMonoidHom = Y := fun ψ =>
    eq_of_isComponent hB'ab hB'9 hBZ hmaxC (CFSG.LocalCores.isComponent_map_mulEquiv ψ hY) hY
  have hYn : ∀ q : ↥C ⧸ CFSG.pPrimeCore 3 ↥C,
      q ∈ Subgroup.normalizer (Y : Set (↥C ⧸ CFSG.pPrimeCore 3 ↥C)) := fun q =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hYaut (MulAut.conj q))
  obtain ⟨a, haA, ha1, haY⟩ := exists_mem_of_isComponent hA'ab hA'max hY (fun x _ => hYn x)
  have hBY : ¬ (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ≤ Y := by
    intro hle
    have hY4 : SectionFourHyp Y :=
      Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h1 hC4 hY
    refine false_of_elemAbelian_le_center h1 h2 h43 hin hY4 hY.1
      (B := ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).subgroupOf Y)
      ((hB'ab.map _).subgroupOf Y) ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        card_map_mk _ hN3 hB'ab.isPGroup, hB'9]
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C)
        (y : ↥C ⧸ CFSG.pPrimeCore 3 ↥C)
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hbx, ← hz, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp (hBZ hb) z]
  exact ⟨Y, hY, hYaut, ⟨a, haA, ha1, haY⟩, hBY⟩

theorem map_conj_inf_comap_eq {B : Subgroup G}
    {Y : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))}
    (hYaut : ∀ ψ : (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) ≃*
        (↥(Subgroup.centralizer (B : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
      Y.map ψ.toMonoidHom = Y)
    (X : Subgroup G) {w : G} (hwX : w ∈ Subgroup.normalizer (X : Set G))
    (hwB : w ∈ Subgroup.normalizer (B : Set G)) :
    ((X.subgroupOf (Subgroup.centralizer (B : Set G)) ⊓
        Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
        (Subgroup.centralizer (B : Set G)).subtype).map (MulAut.conj w).toMonoidHom =
      (X.subgroupOf (Subgroup.centralizer (B : Set G)) ⊓
        Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
        (Subgroup.centralizer (B : Set G)).subtype := by
  have hwC : w ∈ Subgroup.normalizer
      ((Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_centralizer hwB
  set φ := (Subgroup.centralizer (B : Set G)).normalizerMonoidHom ⟨w, hwC⟩
  have hNφ : (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))).map φ.toMonoidHom =
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)) :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance _
  have hψ := hYaut (QuotientGroup.congr (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))
    (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) φ hNφ)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.mp hx
    refine ⟨φ x, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (Subgroup.mem_normalizer_iff.mp hwX (x : G)).mp hxX
    · show QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) (φ x) ∈ Y
      rw [← hψ]
      exact ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) x, hxY,
        rfl⟩
  · exact (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge

theorem exists_invariant_of_not_isPConstrained (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hT : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoF G)
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) :
    ∃ F : Subgroup G, F ≤ A ∧ Nat.card F = 3 ∧
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (B : Set G) →
        F.map (MulAut.conj w).toMonoidHom = F := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hCdef
  obtain ⟨Y, -, hYaut, ⟨a, haA, ha1, haY⟩, hBY⟩ :=
    exists_centralizer_component_data h1 h2 h43 hin hT hS hA hBA hB9 hcon
  have hFE := (hT.partTwoF_eq_partTwoE hS).1
  have hAE : A ∈ partTwoE G := hFE ▸ hA
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := hAE.2.1
  have hAC : A ≤ C := by
    intro a ha
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
  have hBC : B ≤ C := hBA.trans hAC
  have hA'27 : Nat.card (A.subgroupOf C) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv).trans hA27
  have hB'9 : Nat.card (B.subgroupOf C) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv).trans hB9
  have hB'A' : B.subgroupOf C ≤ A.subgroupOf C := fun x hx => hBA hx
  by_cases hBYc : B.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) = ⊥
  ·
    refine ⟨(A.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype,
      ?_, ?_, fun w hwA hwB => map_conj_inf_comap_eq hYaut A hwA hwB⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.mp hx).1
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      have hD27 : Nat.card (A.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) : Subgroup C) ∣ 3 ^ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : A.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ≤ A.subgroupOf C)
        rw [hA'27] at this
        norm_num
        exact this
      have hD1 : Nat.card (A.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) : Subgroup C) ≠ 1 := by
        intro h
        have haD : a ∈ A.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) :=
          Subgroup.mem_inf.mpr ⟨haA, haY⟩
        rw [Subgroup.card_eq_one.mp h, Subgroup.mem_bot] at haD
        exact ha1 haD
      have hDB : (A.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))) ⊓
          B.subgroupOf C = ⊥ := by
        have h' : (A.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))) ⊓
            B.subgroupOf C ≤ B.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) :=
          le_inf inf_le_right (inf_le_left.trans inf_le_right)
        rw [hBYc] at h'
        exact le_bot_iff.mp h'
      have hle := card_mul_card_le_of_inf_eq_bot hDB inf_le_left hB'A'
      rw [hB'9, hA'27] at hle
      obtain ⟨k, hk, hkD⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hD27
      rw [hkD] at hD1 hle ⊢
      interval_cases k <;> revert hD1 hle <;> norm_num
  ·
    refine ⟨(B.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype,
      ?_, ?_, fun w _ hwB => map_conj_inf_comap_eq hYaut B hwB hwB⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hBA (Subgroup.mem_inf.mp hx).1
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      have hD9 : Nat.card (B.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) : Subgroup C) ∣ 3 ^ 2 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : B.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ≤ B.subgroupOf C)
        rw [hB'9] at this
        norm_num
        exact this
      have hD1 : Nat.card (B.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) : Subgroup C) ≠ 1 := fun h =>
        hBYc (Subgroup.card_eq_one.mp h)
      have hD9' : Nat.card (B.subgroupOf C ⊓
          Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) : Subgroup C) ≠ 9 := by
        intro h
        apply hBY
        have hDB : B.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) =
            B.subgroupOf C := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hB'9])
        rw [Subgroup.map_le_iff_le_comap, ← hDB]
        exact inf_le_right
      obtain ⟨k, hk, hkD⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hD9
      rw [hkD] at hD1 hD9' ⊢
      interval_cases k <;> revert hD1 hD9' <;> norm_num

theorem isPConstrained_of_case3 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46) (hT : TheoremFourHyp G)
    (hS : partTwoS G = ∅) {A L : Subgroup G} {c : G} (hA : A ∈ partTwoF G)
    (hc : Subgroup.zpowers c ∈ omegaA A)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hΩ : omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c))
    (h9 : (omegaA A).ncard = 9) (hAL : Nat.card (A ⊓ L : Subgroup G) = 9)
    {B : Subgroup G} (hB : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) :
    CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have hFE := (hT.partTwoF_eq_partTwoE hS).1
  have hAE : A ∈ partTwoE G := hFE ▸ hA
  have hA27 : Nat.card A = 27 := hAE.2.1
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [hA27] at h
    omega
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra h
    push Not at h
    have h27 := Subgroup.card_le_of_le (show A ≤ B from h)
    rw [hA27, hB9] at h27
    omega
  have hAa : A = Subgroup.zpowers a ⊔ B := by
    have hAB : A ⊓ B = B := inf_eq_right.mpr hB.1
    have h := TransProof.sup_eq_of_card (L := B) hA27 (by rw [hAB]; exact hB9) haA haB
    rw [hAB] at h
    exact h.symm
  have hsub : omegaA A ⊆ pointsOff A B := by
    rintro F ⟨hFA, hF3, x, rfl, hx⟩
    refine ⟨hFA, hF3, fun hFB => ?_⟩
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF3
      norm_num at hF3
    exact hfree x (hFB (Subgroup.mem_zpowers x)) hx1 ⟨hFA, hF3, x, rfl, hx⟩
  have hΩB : omegaA A = pointsOff A B :=
    Set.eq_of_subset_of_ncard_le hsub ((ncard_pointsOff hAab haA hAa haB hB9).trans h9.symm).le
  have hconjAL : ∀ x ∈ Subgroup.normalizer (A : Set G), ∀ y ∈ A ⊓ L, x * y * x⁻¹ ∈ A ⊓ L :=
    fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hWB hx) y).mp hy
  have hcA : c ∈ A := hc.1 (Subgroup.mem_zpowers c)
  have hcL : c ∉ L := by
    intro hcL
    have hcAL : c ∈ A ⊓ L := Subgroup.mem_inf.mpr ⟨hcA, hcL⟩
    have hΩL : ∀ F ∈ omegaA A, F ≤ A ⊓ L := by
      intro F hF
      rw [hΩ] at hF
      obtain ⟨x, hx, rfl⟩ := hF
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      simp only [MulEquiv.coe_toMonoidHom, map_zpow]
      exact (A ⊓ L).zpow_mem (by rw [MulAut.conj_apply]; exact hconjAL x hx c hcAL) k
    have hpt : ∀ b ∈ B, a * b ∈ L := by
      intro b hb
      have hmem : Subgroup.zpowers (a * b) ∈ pointsOff A B :=
        (mem_pointsOff_iff hAab haA hAa haB).mpr ⟨b, hb, rfl⟩
      rw [← hΩB] at hmem
      exact (Subgroup.mem_inf.mp (hΩL _ hmem (Subgroup.mem_zpowers _))).2
    have haL : a ∈ L := by simpa using hpt 1 (one_mem B)
    have hAL' : A ≤ L := by
      rw [hAa]
      refine sup_le (Subgroup.zpowers_le.mpr haL) fun b hb => ?_
      have := L.mul_mem (L.inv_mem haL) (hpt b hb)
      rwa [inv_mul_cancel_left] at this
    rw [inf_eq_left.mpr hAL', hA27] at hAL
    norm_num at hAL
  have hALB : A ⊓ L ≤ B := by
    intro y hy
    by_contra hyB
    have hy1 : y ≠ 1 := fun h => hyB (h ▸ one_mem B)
    have hy3 : Nat.card (Subgroup.zpowers y) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hAab.2 y (Subgroup.mem_inf.mp hy).1) hy1
    have hmem : Subgroup.zpowers y ∈ pointsOff A B :=
      ⟨Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hy).1, hy3,
        fun h => hyB (h (Subgroup.mem_zpowers y))⟩
    rw [← hΩB, hΩ] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    apply hcL
    have hc' : x * c * x⁻¹ ∈ Subgroup.zpowers y := by
      rw [hxy]
      exact ⟨c, Subgroup.mem_zpowers c, rfl⟩
    have hyAL : ∀ z ∈ Subgroup.zpowers y, z ∈ A ⊓ L := fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (A ⊓ L).zpow_mem hy k
    have h' := hconjAL x⁻¹ (inv_mem hx) _ (hyAL _ hc')
    have hcc : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
    rw [hcc] at h'
    exact (Subgroup.mem_inf.mp h').2
  have hBeq : A ⊓ L = B := Subgroup.eq_of_le_of_card_ge hALB (by rw [hB9, hAL])
  obtain ⟨F, hFA, hF3, hFinv⟩ :=
    exists_invariant_of_not_isPConstrained h1 h2 h43 hin hT hS hA hB.1 hB9 hcon
  have hFinv' : ∀ w ∈ Subgroup.normalizer (A : Set G), F.map (MulAut.conj w).toMonoidHom = F :=
    fun w hw => hFinv w hw (by rw [← hBeq]; exact hWB hw)
  by_cases hFB : F ≤ B
  ·
    have hFAL : F ≤ A ⊓ L := hBeq ▸ hFB
    have hF'3 : Nat.card (F.subgroupOf (A ⊓ L)) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFAL).toEquiv).trans hF3
    have hinvF : ∀ φ ∈ Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L),
        (F.subgroupOf (A ⊓ L)).map φ.toMonoidHom = F.subgroupOf (A ⊓ L) := by
      intro φ hφ
      obtain ⟨h, hN, hh, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
      have hFh := hFinv' h (Subgroup.mem_inf.mp hh).2
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        show h * (x : G) * h⁻¹ ∈ F
        rw [← hFh]
        exact ⟨(x : G), hx, rfl⟩
      · exact (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
    rcases hirr (F.subgroupOf (A ⊓ L)) hinvF with h0 | h0
    · rw [h0, Subgroup.card_bot] at hF'3
      norm_num at hF'3
    · rw [h0, Subgroup.card_top, hAL] at hF'3
      norm_num at hF'3
  ·
    have hFΩ : F ∈ omegaA A := by
      rw [hΩB]
      exact ⟨hFA, hF3, hFB⟩
    have hall : ∀ F' ∈ omegaA A, F' = F := by
      intro F' hF'
      rw [hΩ] at hF' hFΩ
      obtain ⟨y, hy, rfl⟩ := hF'
      obtain ⟨x, hx, hxF⟩ := hFΩ
      have hyx : y * x⁻¹ ∈ Subgroup.normalizer (A : Set G) := mul_mem hy (inv_mem hx)
      calc (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom
          = ((Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom).map
              (MulAut.conj (y * x⁻¹)).toMonoidHom := by
            rw [map_conj_map_conj, inv_mul_cancel_right]
        _ = F.map (MulAut.conj (y * x⁻¹)).toMonoidHom := by rw [← hxF]
        _ = F := hFinv' _ hyx
    have hle : (omegaA A).ncard ≤ 1 :=
      calc (omegaA A).ncard ≤ ({F} : Set (Subgroup G)).ncard :=
            Set.ncard_le_ncard (fun F' hF' => hall F' hF') (Set.toFinite _)
        _ = 1 := Set.ncard_singleton F
    omega

end Sylow155T51

end CFSG.RankThree.PartTwo.Sec15
