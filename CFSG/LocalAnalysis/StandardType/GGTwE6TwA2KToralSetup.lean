module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComps
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Classes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import Certificates.Certificate41501

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups
open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_langDatum_of_toral_twisted_subgroup
    (t : TwistTag) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (f : ℕ) (hf : 1 ≤ f) (A : Subgroup (ModGL t.tag L))
    (hfix : ∀ u ∈ A, twistHom t L (iterateFrobenius L ℓ f) u = u)
    (hconj : ∃ g ∈ adjointGroup t.tag L, ∀ u ∈ A, g⁻¹ * u * g ∈ torusGroup t.tag L) :
    ∃ D : LangDatum t.tag L, D.Φ = twistHom t L (iterateFrobenius L ℓ f) ∧ D.q = ℓ ^ f ∧
      ∀ u ∈ A, u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
  obtain ⟨g, hg, hgA⟩ := hconj
  obtain ⟨w, g0, hg0, hF, hmem⟩ :=
    exists_lang_torus_of_conj_torus_twisted ℓ t f hf hfix hg hgA
  exact ⟨LangDatum.ofTwist t (iterateFrobenius L ℓ f) (ℓ ^ f)
    (iterateFrobenius_def ℓ f) w hg0 hF, rfl, rfl, hmem⟩

theorem exists_langSetup_of_big_elemAbelian
    {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (A : Subgroup ↥(twistedE6InndiagGL K σ))
    (hA : IsElemAbelian 3 A) (hbig : 3 ^ 5 ≤ Nat.card A) (h : ↥(twistedE6InndiagGL K σ))
    (hhA : h ∈ A) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ^ n ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (2 ^ n)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit Tag.E6 a ≠ 1 ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (twistedE6InndiagConj K σ h c) =
        rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      ∀ x ∈ A, S.D.g0⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 (AlgebraicClosure K)) * S.D.g0 ∈ S.D.torus := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L 2 n c = c ^ (2 ^ n) := fun c =>
    iterateFrobenius_def 2 n c
  set A' : Subgroup (ModGL TwistTag.E6.tag L) :=
    A.map ((baseChangeGL ι₁).comp (twistedE6InndiagGL K σ).subtype) with hA'def
  have hA'F : A' ≤ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 n) := by
    intro u hu
    rw [hA'def] at hu
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
      (iterateFrobenius L 2 n) hFr ⟨(a : ModGL TwistTag.E6.tag K), a.2, rfl⟩
  have hA'G : A' ≤ adjointGroup Tag.E6 L := fun u hu => (hA'F hu).1
  have hcommA : ∀ a b : ↥A, (a : ↥(twistedE6InndiagGL K σ)) * b = b * a := fun a b =>
    congrArg Subtype.val (hA.1.is_comm.comm a b)
  have hcomm' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    rw [hA'def] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hcommA ⟨a, ha⟩ ⟨b, hb⟩]
  have hpow' : ∀ x ∈ A', x ^ 3 = 1 := by
    intro x hx
    rw [hA'def] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := hA.2 a ha
    rw [ha3, map_one]
  have hinj' : Function.Injective
      ((baseChangeGL ι₁).comp (twistedE6InndiagGL K σ).subtype) :=
    (baseChangeGL_injective ι₁).comp (Subgroup.subtype_injective _)
  have hcard' : 3 ^ 5 ≤ Nat.card A' := by
    rw [hA'def, Subgroup.card_map_of_injective (K := A) hinj']
    exact hbig
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro hd
    have h1 : 3 ∣ 2 ^ n := Nat.prime_three.dvd_of_dvd_pow hd
    have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h1
    norm_num at h2
  obtain ⟨g, hg, hgA⟩ :=
    CFSG.StandardType.ExcFramesHalf.bigElemAbelianToralBar_E6_three K h3K A' hA'G hcomm'
      hpow' (by show 3 ^ 5 ≤ Nat.card A'; exact hcard')
  have hfix : ∀ u ∈ A', twistHom TwistTag.E6 L (iterateFrobenius L 2 n) u = u :=
    fun u hu => (hA'F hu).2
  obtain ⟨D, hΦ, hDq, hDmem⟩ :=
    exists_langDatum_of_toral_twisted_subgroup TwistTag.E6 n hn A' hfix ⟨g, hg, hgA⟩
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup Nat.prime_two hn hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 Nat.prime_two hn hK hσ hFr D hΦ
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K) with hu
  have hh3 : h ^ 3 = 1 := hA.2 h hhA
  have hu3 : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 :=
    congrArg (fun x : ↥(twistedE6InndiagGL K σ) => (x : ModGL TwistTag.E6.tag K)) hh3
  have hup : u ^ 3 = 1 := by
    rw [hu, ← map_pow (baseChangeGL ι₁) (h : ModGL TwistTag.E6.tag K) 3, hu3, map_one]
  have hu1 : u ≠ 1 := by
    intro h'
    rw [hu] at h'
    exact hh1 (Subtype.ext (baseChangeGL_injective ι₁ (by simpa using h')))
  have hβ' : ∀ c, ι₀ (twistedE6InndiagConj K σ h c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (twistedE6InndiagConj K σ h c : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K) *
        baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) *
        (baseChangeGL ι₁ (h : ModGL TwistTag.E6.tag K))⁻¹
    rw [twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
  have huA' : u ∈ A' := by
    rw [hu, hA'def]
    exact Subgroup.mem_map_of_mem _ hhA
  have hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := hDmem u huA'
  obtain ⟨S, a, -, hSD, hT, hap, h1, -, -, -, hg0⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.exists_langSetup_conj_of_toral_datum
      Nat.prime_two hn D hDq (by norm_num) (by norm_num) (Or.inl le_rfl) hfin ι₀ hι₀inj hΓ
      (twistedE6InndiagConj K σ h) hβ' hmem hup hu1
  subst hSD
  refine ⟨S, a, (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀, hDq, ⟨_, hFr, hΦ⟩, hT, hap, h1,
    (MulAut.conj S.D.g0⁻¹).injective.comp hι₀inj, ?_, fun c => ?_, ?_⟩
  · show _ = S.D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp _ _
  · change (MulAut.conj S.D.g0⁻¹) (ι₀ (twistedE6InndiagConj K σ h c)) =
      rootDiagUnit _ a * (MulAut.conj S.D.g0⁻¹) (ι₀ c) * (rootDiagUnit _ a)⁻¹
    simp only [MulAut.conj_apply, inv_inv]
    rw [hβ' c, ← hg0]
    group
  · intro x hx
    change S.D.g0⁻¹ * ((baseChangeGL ι₁).comp (twistedE6InndiagGL K σ).subtype) x *
      S.D.g0 ∈ S.D.torus
    have hx' : ((baseChangeGL ι₁).comp (twistedE6InndiagGL K σ).subtype) x ∈ A' :=
      Subgroup.mem_map_of_mem _ hx
    obtain ⟨t, ht, ht'⟩ := Subgroup.mem_map.mp (hDmem _ hx')
    rw [← ht']
    have hcalc : S.D.g0⁻¹ * ((MulAut.conj S.D.g0).toMonoidHom t) * S.D.g0 = t := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcalc]
    exact ht

end CFSG.StandardType.TwE6TwA2K

end
