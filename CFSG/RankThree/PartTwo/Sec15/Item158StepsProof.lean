module

public import CFSG.RankThree.PartTwo.Sec15.Item1511Proof
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

section Data

variable {G : Type} [Group G] [Finite G]

structure Cartan158 (c : G) (L Y P E F : Subgroup G) : Prop where
  le_p : E ≤ P
  mem_c : c ∈ E
  elem : CFSG.Assembly.IsElemAbelian 3 E
  card : Nat.card E = 27
  le_normalizer : E ≤ Subgroup.normalizer (L : Set G)
  sectionCentralizer : Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
    (Subgroup.zpowers c : Set G)
  typeC : Sec4.IsTypeCOn E L
  isF : IsF138N L E F
  le_normalizer_Y : F ≤ Subgroup.normalizer (Y : Set G)

end Data

@[expose] noncomputable def Step158Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A = omegaOneThree P → ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)

@[expose] noncomputable def Step158Cartan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∃ E F : Subgroup G, Cartan158 c L Y P E F

@[expose] noncomputable def Step158R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∀ E F : Subgroup G, Cartan158 c L Y P E F →
      Sec8.IsZ3PGLThreePi (lBarA c L E) → ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
      CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
        Sec14.IsZ3PGLThreeAt ↥(lBarA c L (omegaOneThree P)) p e ∧
          (Nat.card ↥(omegaOneThree P ⊔ L)).factorization 3 = 4 ∧
          (Nat.card ↥((omegaOneThree P ⊔ L) ⊓ Subgroup.normalizer (Y : Set G))).factorization 3 =
            4 ∧
          CFSG.ABGLocalTools.IsSylowOf 3 F (Subgroup.zpowers c ⊔ L)

namespace Proof158Steps

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_isSylowOf {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (h' : CFSG.ABGLocalTools.IsSylowOf p P' K) :
    ∃ k ∈ K, P' = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨k, k.2, ?_⟩
  rw [← hk]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    refine ⟨K.subtype ((MulAut.conj k)⁻¹ • y), ⟨_, hy, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨MulAut.conj k s, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    · simp [MulAut.conj_apply]

omit [Finite G] in
theorem map_conj_inv_map_conj (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]

theorem omegaA_map_conj (g : G) (F : Subgroup G) :
    omegaA (F.map (MulAut.conj g).toMonoidHom) =
      (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) '' omegaA F := by
  ext X
  constructor
  · intro hX
    refine ⟨X.map (MulAut.conj g⁻¹).toMonoidHom, ?_, map_conj_inv_map_conj X g⟩
    rw [← mem_omegaA_map_conj_iff g, map_conj_inv_map_conj X g]
    exact hX
  · rintro ⟨X', hX', rfl⟩
    exact (mem_omegaA_map_conj_iff g).mpr hX'

omit [Finite G] in
theorem orbitIn_map_conj {X F : Subgroup G} {g : G}
    (hF : F.map (MulAut.conj g).toMonoidHom = F) :
    orbitIn (X.map (MulAut.conj g).toMonoidHom) F =
      (fun Y : Subgroup G => Y.map (MulAut.conj g).toMonoidHom) '' orbitIn X F := by
  ext Y
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
    refine ⟨F.map (MulAut.conj x').toMonoidHom, ⟨x', hx', rfl⟩, ?_⟩
    change (F.map (MulAut.conj x').toMonoidHom).map (MulAut.conj g).toMonoidHom =
      F.map (MulAut.conj (g * x' * g⁻¹)).toMonoidHom
    conv_rhs => rw [← hF]
    rw [Late.map_conj_map_conj, Late.map_conj_map_conj]
    congr 2
    group
  · rintro ⟨Y', ⟨x', hx', rfl⟩, rfl⟩
    refine ⟨g * x' * g⁻¹, ⟨x', hx', rfl⟩, ?_⟩
    change (F.map (MulAut.conj x').toMonoidHom).map (MulAut.conj g).toMonoidHom =
      F.map (MulAut.conj (g * x' * g⁻¹)).toMonoidHom
    conv_rhs => rw [← hF]
    rw [Late.map_conj_map_conj, Late.map_conj_map_conj]
    congr 2
    group

theorem omegaA_map_conj_of_commute {F : Subgroup G} {c g : G} (hgc : g * c = c * g)
    (hΩ : omegaA F = orbitIn (Subgroup.normalizer (F : Set G)) (Subgroup.zpowers c)) :
    omegaA (F.map (MulAut.conj g).toMonoidHom) =
        orbitIn (Subgroup.normalizer ((F.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
          (Subgroup.zpowers c) ∧
      (omegaA (F.map (MulAut.conj g).toMonoidHom)).ncard = (omegaA F).ncard := by
  have hc : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change g * c * g⁻¹ = c
    rw [hgc, mul_inv_cancel_right]
  refine ⟨?_, ?_⟩
  · rw [omegaA_map_conj, ← Subgroup.map_equiv_normalizer_eq F (MulAut.conj g),
      orbitIn_map_conj hc, hΩ]
  · rw [omegaA_map_conj]
    exact Set.ncard_image_of_injective _ (Subgroup.map_injective (MulAut.conj g).injective)

theorem mem_partTwoE_of_le_normalizer {A Y E : Subgroup G} (hY : Y ∈ scriptY2 A)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) : E ∈ partTwoE G :=
  ⟨hE, hE27, CFSG.Open.pCoreOf 2 Y, hY.2, CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y,
    hEY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)⟩

theorem mem_reachE_of_mem {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    {E : Subgroup G} (hE : E ∈ partTwoE G) (hcE : c ∈ E) : E ∈ reachE A :=
  ⟨hE, Relation.ReflTransGen.single
    ⟨hD.mem_partTwoE, hE, Subgroup.zpowers c, hD.zpowers_mem_omegaA,
      Subgroup.zpowers_le.mpr hcE⟩⟩

theorem hypT_of_mem_of_mem {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {E : Subgroup G}
    (hE : E ∈ partTwoE G) (hcE : c ∈ E) : HypT E :=
  hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR
    (mem_reachE_of_mem h.toSec13Data hE hcE)

omit [Finite G] in
theorem sup_le_centralizer {c : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({c} : Set G)) :
    Subgroup.zpowers c ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
  sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hL

omit [Finite G] in
theorem le_centralizer_of_mem {c : G} {E : Subgroup G} (hE : IsMulCommutative E) (hcE : c ∈ E) :
    E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))

end Proof158Steps

section Proof

open Proof158Steps


variable {G : Type} [Group G] [Finite G]

theorem nonempty_prod_of_not_isZ3PGLThreePi (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {p e : ℕ} [Fact p.Prime]
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, hprod, -⟩ |
      ⟨-, -, ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · exact hprod
  · exact (Proof1511.not_isoLThreePi_of_prod_M12 hD e12 hL3).elim
  · exact (Proof1511.not_isoLThreePi_of_prod_J2 hD eJ hL3).elim
  · exact (hnPGL hPGL).elim
  · exact (hcL hcL').elim

theorem rank3II_15_8_Y0_of (h131 : Item131) (h138 : Item138N) (hinner : Step158Inner)
    (hcartan : Step158Cartan) (hR : Step158R) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) : Item158Y0 A (lB A) c L := by
  intro p e _ he hL3 Y hY hmeet P hAP hP
  have hD := h.toSec13Data
  by_cases hΩ : A = omegaOneThree P
  · exact Or.inl ⟨nonempty_prod_of_not_isZ3PGLThreePi h131 h hL3
      (hinner G A c L h p e he hL3 Y hY hmeet P hAP hP hΩ), hΩ⟩
  · right
    have hFE : partTwoF G = partTwoE G :=
      (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
    obtain ⟨E, F, hC⟩ := hcartan G A c L h p e he hL3 Y hY hmeet P hAP hP hΩ
    have hL3pi : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨p, e, inferInstance, he, hL3⟩
    obtain ⟨⟨hFEL, hF3, hF27, hFfus, hFN⟩, hF9⟩ := hC.isF
    have hEE : E ∈ partTwoE G := mem_partTwoE_of_le_normalizer hY.2 hC.elem hC.card
      ((hC.le_p.trans hP.le).trans inf_le_right)
    have hFE' : F ∈ partTwoE G := mem_partTwoE_of_le_normalizer hY.2 hF3 hF27 hC.le_normalizer_Y
    obtain ⟨hPGL, hmod9, hFall⟩ := h138 G A c L hD hL3pi E hC.mem_c hC.elem hC.card
      hC.le_normalizer hC.sectionCentralizer (Or.inr (hypT_of_mem_of_mem h hEE hC.mem_c))
      hC.typeC
    obtain ⟨hSyl, hΩF⟩ := hFall F hFEL hF3 hF27 hF9 hFfus hFN
    have hEL : E ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (le_centralizer_of_mem hC.elem.1 hC.mem_c) hD.le_centralizer
    have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hD.mem_A
    have hcF : c ∈ F := mem_of_mem_partTwoF (hFE ▸ hFE') hc3 (hFEL.trans hEL)
    obtain ⟨hΩF', h9F⟩ := hΩF (Or.inr (hypT_of_mem_of_mem h hFE' hcF))
    obtain ⟨hRPGL, hR4, hRY4, hFsyl⟩ := hR G A c L h p e he hL3 Y hY hmeet P hAP hP hΩ E F hC
      hPGL (hmod9 p e he hL3) hSyl
    refine ⟨hRPGL, hR4, hRY4, fun F' hF' => ?_⟩
    obtain ⟨g, hg, rfl⟩ := exists_conj_of_isSylowOf hFsyl hF'
    have hgc : g * c = c * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (sup_le_centralizer hD.le_centralizer hg)
    obtain ⟨hΩg, hng⟩ := omegaA_map_conj_of_commute hgc hΩF'
    refine ⟨?_, hΩg, hng.trans h9F⟩
    rw [hFE]
    exact (map_mem_partTwoE_iff (MulAut.conj g)).mpr hFE'

end Proof

theorem item158Y0R_of
    (h131 : Item131) (h138 : Item138N) (hinner : Step158Inner)
    (hcartan : Step158Cartan) (hR : Step158R) : Item158Y0R :=
  fun _ _ _ _ _ _ h => rank3II_15_8_Y0_of h131 h138 hinner hcartan hR h

end CFSG.RankThree.PartTwo.Sec15
