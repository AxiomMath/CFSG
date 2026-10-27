module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBack
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import Certificates.Certificate43
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.ThinCatalog.FiveModels
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)
open CFSG.GorensteinWalter (PSL2)

theorem InnerConfig424.isPGroup {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X}
    {K : Subgroup X} (h : InnerConfig424 X D c d K) : IsPGroup 3 D :=
  fun x => ⟨1, Subtype.ext (by simpa using h.maximal.prop.2 x x.2)⟩

namespace Item424Proof

variable {X : Type} [Group X] [Finite X]

theorem census424_of_cyclic_sylow (hX : ∀ Q : Sylow 3 X, IsCyclic Q) : Census424 X := by
  intro D c d K h
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hDQ⟩ := h.isPGroup.exists_le_sylow
  have := hX Q
  have hDc : IsCyclic D := by
    have hc : IsCyclic (D.subgroupOf Q) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDQ).toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  have hg9 : orderOf g = 9 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, h.card_eq]
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using h.maximal.prop.2 g g.2)
  have h93 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg9] at h93
  exact absurd h93 (by norm_num)

theorem census424_of_not_three_dvd (hX : ¬ 3 ∣ Nat.card X) : Census424 X := by
  intro D c d K h
  have h9 : 9 ∣ Nat.card X := by
    rw [← h.card_eq]
    exact Subgroup.card_subgroup_dvd_card D
  exact (hX ((show 3 ∣ 9 by norm_num).trans h9)).elim

theorem isSolvable_of_center_ne_bot_psl2 {F : Type} [Field F]
    [Finite F] [Finite (PSL2 F)] {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f)
    (H : Subgroup (PSL2 F)) (hZ : Subgroup.center H ≠ ⊥) : Group.IsSolvable H := by
  have hZ' : ∀ (M : Type) [Group M], Nonempty (H ≃* M) → Subgroup.center M ≠ ⊥ := by
    rintro M _ ⟨e⟩ hM
    exact hZ (ABGLocalTools.center_eq_bot_of_mulEquiv e hM)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hab | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNab, -, hC, -, -, hNC⟩ | ⟨m, -, -, ⟨e⟩⟩ | ⟨m, -, -, ⟨e⟩⟩
  · exact inferInstance
  · exact inferInstance
  · have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hz
      exact Nat.card_pos.ne' hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact (hZ' _ ⟨e⟩ (alternatingGroup.center_eq_bot (by simp))).elim
  · exact (hZ' _ ⟨e⟩ ABGLocalTools.center_perm_fin_four_eq_bot).elim
  · exact (hZ' _ ⟨e⟩ (alternatingGroup.center_eq_bot (by simp))).elim
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy : y ∈ ((N ⊔ C : Subgroup H) : Set H) := by rw [hNC]; exact Subgroup.mem_top y
      rw [Subgroup.normal_mul, Set.mem_mul] at hy
      obtain ⟨n, hn, k, hk, rfl⟩ := hy
      refine ⟨⟨k, hk⟩, ?_⟩
      show (QuotientGroup.mk k : H ⧸ N) = QuotientGroup.mk (n * k)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have hQ : Group.IsSolvable (H ⧸ N) := Group.isSolvable_of_comm fun x y => by
      obtain ⟨x', rfl⟩ := hsurj x
      obtain ⟨y', rfl⟩ := hsurj y
      rw [← map_mul, ← map_mul, mul_comm' x' y']
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · exact (hZ' _ ⟨e⟩ (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p m))).elim
  · exact (hZ' _ ⟨e⟩ (CFSG.GorensteinWalter.pgl2_center_eq_bot (GaloisField p m))).elim

theorem census424_of_psl2 {F : Type} [Field F] [Finite F]
    (e : X ≃* PSL2 F) : Census424 X := by
  intro D c d K h
  exfalso
  have : Fintype F := Fintype.ofFinite F
  have : Finite (PSL2 F) := Finite.of_equiv X e.toEquiv
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  set C := Subgroup.centralizer ({c} : Set X) with hC
  have hCs : Group.IsSolvable C := by
    set H := C.map e.toMonoidHom with hH
    have eH : C ≃* H := C.equivMapOfInjective e.toMonoidHom e.injective
    have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hZ : Subgroup.center H ≠ ⊥ := by
      intro h0
      have hmem : eH ⟨c, hcC⟩ ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨y', rfl⟩ := eH.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y'.2)
      rw [h0, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
      exact h.c_ne_one (congrArg Subtype.val hmem)
    have := isSolvable_of_center_ne_bot_psl2 hF H hZ
    exact Group.isSolvable_of_surjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  have hKC : K ≤ C := (mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn).1
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKC)
      (Subgroup.inclusion_injective hKC)
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn h.mem_thetaComponentsIn
  have hKn : Nontrivial K := by
    obtain ⟨x, y, hxy⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial
      (isQuasisimple_of_mem_thetaComponentsIn h.mem_thetaComponentsIn)).exists_pair_ne
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x', y', fun hx => hxy (by rw [hx])⟩⟩
  exact Group.IsPerfect.not_isSolvable K hKs

end Item424Proof

open Item424Proof

theorem isCyclic_sylow_of_isSLThreeEpsAt {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hX : IsSLThreeEpsAt X (p ^ e)) (hπ : ¬ IsSLThreePiAt X (p ^ e))
    (Q : Sylow 3 X) : IsCyclic Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq3 : (p ^ e) % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hX
  ·
    have hq : p ^ e % 3 = 2 := by
      have : p ^ e % 3 ≠ 1 := fun h1 => hπ ⟨K, inferInstance, inferInstance,
        Or.inl ⟨hK, h1, ⟨φ⟩⟩⟩
      omega
    have hf : Function.Surjective φ.symm.toMonoidHom := φ.symm.surjective
    obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Q
    have := SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three (K := K)
      (H := CFSG.Assembly.LowTwoRank.StatedSL 3 K) (by rw [hK]; omega) (by rw [hK]; omega)
      S.isPGroup'
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  ·
    have hq : p ^ e % 3 = 1 := by
      have : p ^ e % 3 ≠ 2 := fun h1 => hπ ⟨K, inferInstance, inferInstance,
        Or.inr ⟨hK, h1, ⟨φ⟩⟩⟩
      omega
    have : Fintype K := Fintype.ofFinite K
    have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * e) (by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    have hf : Function.Surjective φ.symm.toMonoidHom := φ.symm.surjective
    obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Q
    have := ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hK
      (by norm_num) (Ne.symm hp3) (by omega) S
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem k424Inner46Two : K424Inner46Two := by
  rintro X _ _ ⟨p, e, hp, hp3, he, -, hX⟩ - - hSL
  have hp3' : p ≠ 3 := by omega
  have hq3 : (p ^ e) % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ p ^ e := Nat.dvd_of_mod_eq_zero h0
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  refine census424_of_cyclic_sylow ?_
  rcases hX with hX | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact isCyclic_sylow_of_isSLThreeEpsAt hp3' hX fun h => hSL (Or.inl ⟨_, h⟩)
  · have hq : p ^ e % 3 = 2 := by
      have : p ^ e % 3 ≠ 1 := fun h1 => hSL (Or.inr ⟨p, e, hp, he, Or.inl ⟨h1, ⟨φ⟩⟩⟩)
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inr ⟨hq, ⟨φ⟩⟩)
  · have hq : p ^ e % 3 = 1 := by
      have : p ^ e % 3 ≠ 2 := fun h1 => hSL (Or.inr ⟨p, e, hp, he, Or.inr ⟨h1, ⟨φ⟩⟩⟩)
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inl ⟨hq, ⟨φ⟩⟩)

theorem k424Inner46One : K424Inner46One := by
  rintro X _ _ ⟨p, e, hp, -, -, ⟨φ⟩⟩ - - -
  exact census424_of_psl2 (φ.trans (projSLEquivPSL _))

@[expose] def IsList46SixRest (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
  ∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
    Blueprint.ReeTitsModel X .twistedF4 2 f ∨ Blueprint.ReeTitsModel X .Tits 2 f

@[expose] def K424Inner46SixRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46SixRest X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

theorem k424Inner46Six_of
    (hR : K424Inner46SixRest) : K424Inner46Six := by
  intro X _ _ hX hq hZ hSL
  have h2 : ∀ n : ℕ, (2 ^ n) % 3 ≠ 0 := fun n h0 => by
    have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h0
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  rcases hX with
      ⟨⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨f, hf | hf | hf | hf | hf⟩⟩ |
      ⟨n, hn, hX⟩
  · exact census424_of_psl2 (φ.trans (projSLEquivPSL _))
  · refine census424_of_cyclic_sylow ?_
    have hq : 2 ^ n % 3 = 2 := by
      have : 2 ^ n % 3 ≠ 1 := fun h1 => hSL (Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn,
        Or.inl ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 n
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inr ⟨hq, ⟨φ⟩⟩)
  · refine census424_of_cyclic_sylow ?_
    have hq : 2 ^ n % 3 = 1 := by
      have : 2 ^ n % 3 ≠ 2 := fun h1 => hSL (Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn,
        Or.inr ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 n
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inl ⟨hq, ⟨φ⟩⟩)
  · exact hR X (Or.inl ⟨n, hn, Or.inl ⟨φ⟩⟩) hq hZ hSL
  · exact hR X (Or.inl ⟨n, hn, Or.inr ⟨φ⟩⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inl hf⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inl hf)⟩) hq hZ hSL
  · exact census424_of_not_three_dvd (ThinCatalog.not_three_dvd_card_of_suzukiModel hf)
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inr (Or.inl hf))⟩) hq hZ hSL
  · exact hR X (Or.inr ⟨f, Or.inr (Or.inr (Or.inr hf))⟩) hq hZ hSL
  · exact census424_of_cyclic_sylow (isCyclic_sylow_of_isSLThreeEpsAt (by norm_num) hX
      fun h => hSL (Or.inl ⟨_, h⟩))

end CFSG.RankThree.PartTwo.Sec4
