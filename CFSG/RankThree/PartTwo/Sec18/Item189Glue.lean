module

public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec20.OneTools
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

section Basic

variable {A M H : Subgroup G} {c : G}

theorem mem_of_sec18H189 (h : Sec18H G A M H c) : c ∈ A := by
  have hc : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
  rw [← h.centralizer_eq] at hc
  exact hc.1

theorem pow_three_of_sec18H189 (h : Sec18H G A M H c) : c ^ 3 = 1 :=
  (isE27_of_mem_partTwoE h.mem_partTwoE).1.2 c (mem_of_sec18H189 h)

theorem le_of_sec18H189 (h : Sec18H G A M H c) : A ≤ H :=
  le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp h.mem_scriptH).1

theorem mem_M_of_sec18H189 (h : Sec18H G A M H c) : c ∈ M :=
  sec18Std_le h.toSec18Std (mem_of_sec18H189 h)

theorem normalClosureIn_le_of_sec18H189 (h : Sec18H G A M H c) : normalClosureIn M c ≤ M :=
  Sec20.normalClosureIn_le (mem_M_of_sec18H189 h)

omit [Finite G] in
theorem s189_le_n189 (M H : Subgroup G) : s189 M H ≤ n189 H :=
  ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left).trans
    (le_normalizer_inSubgroup_perfectResidual H)

omit [Finite G] in
theorem s189_le (M H : Subgroup G) : s189 M H ≤ M :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

theorem isPGroup_s189 (M H : Subgroup G) : IsPGroup 2 (s189 M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem le_normalizer_s189 (h : Sec18H G A M H c) :
    A ≤ Subgroup.normalizer (s189 M H : Set G) :=
  (le_inf (le_of_sec18H189 h) (sec18Std_le h.toSec18Std)).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem s189_le_normalizer_k (M H : Subgroup G) (c : G) :
    s189 M H ≤ Subgroup.normalizer (normalClosureIn M c : Set G) :=
  (s189_le M H).trans (Sec20.le_normalizer_normalClosureIn M c)

omit [Finite G] in
theorem sk189_le_normalizer_k (M H : Subgroup G) (c : G) :
    sk189 M H c ≤ Subgroup.normalizer (normalClosureIn M c : Set G) :=
  sup_le (s189_le_normalizer_k M H c) Subgroup.le_normalizer

theorem le_normalizer_sk189 (h : Sec18H G A M H c) :
    A ≤ Subgroup.normalizer (sk189 M H c : Set G) := fun _ ha =>
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨le_normalizer_s189 h ha,
      Sec20.le_normalizer_normalClosureIn M c (sec18Std_le h.toSec18Std ha)⟩

theorem normalizer_sk189_le (M H : Subgroup G) (c : G) :
    Subgroup.normalizer (sk189 M H c : Set G) ≤
      Subgroup.normalizer (theta189 M H c : Set G) := by
  have : (aschbacherSolvableCore 3 ↥(sk189 M H c)).Characteristic :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.1
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem sk189_le_normalizer_theta189 (M H : Subgroup G) (c : G) :
    sk189 M H c ≤ Subgroup.normalizer (theta189 M H c : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_sk189_le M H c)

omit [Finite G] in
theorem theta189_le (M H : Subgroup G) (c : G) : theta189 M H c ≤ sk189 M H c :=
  Subgroup.map_subtype_le _

theorem not_three_dvd_card_theta189 (M H : Subgroup G) (c : G) :
    ¬ 3 ∣ Nat.card (theta189 M H c) := by
  rw [theta189, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem isSolvable_theta189 (M H : Subgroup G) (c : G) :
    Group.IsSolvable (theta189 M H c) := by
  have h := (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
    Nat.prime_three).1
  exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ _
    (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)

theorem theta189_le_n189 (h187 : Item187) (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    theta189 M H c ≤ n189 H := by
  refine h187 G A M H c h h7 _ ?_
  rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
  refine ⟨le_top, not_three_dvd_card_theta189 M H c, sup_le ?_ ?_⟩
  · exact (le_normalizer_sk189 h).trans (normalizer_sk189_le M H c)
  · exact (le_sup_left : s189 M H ≤ sk189 M H c).trans (sk189_le_normalizer_theta189 M H c)

theorem normalizer_s189_le (h186 : Item186H) (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    Subgroup.normalizer (s189 M H : Set G) ≤ n189 H :=
  (h186 G A M H c h h7).2.1.2

theorem s189_mem_maxInvariant (h186 : Item186H) (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) :=
  (h186 G A M H c h h7).2.1.1

theorem normalizer_zpowers_le189 (h7 : Hyp187 A M H c)
    (hne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H :=
  h7.2.2 hne

end Basic

theorem exists_isSylowOf_le_of_coprime189 {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {O B U : Subgroup G} (hBp : IsPGroup p B) (hBO : B ≤ Subgroup.normalizer (O : Set G))
    (hOp : ¬ p ∣ Nat.card O) (hUO : U ≤ O) (hUq : IsPGroup q U)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q T O ∧ U ≤ T ∧
      B ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let φ : ↥B →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hBO)
  let _ : MulDistribMulAction ↥B ↥O := MulDistribMulAction.compHom ↥O φ
  have hsmul : ∀ (b : ↥B) (x : ↥O), ((b • x : ↥O) : G) = (b : G) * x * (b : G)⁻¹ := by
    intro b x
    change (((O.normalizerMonoidHom) (Subgroup.inclusion hBO b)) x : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hUq' : IsPGroup q (U.subgroupOf O) := hUq.comap_subtype
  have hUinv : CFSG.DisconnectedInvolutionGraph.Helpers.InvariantSubgroup (A := ↥B)
      (U.subgroupOf O) := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hBU b.2) x).mp hx
  obtain ⟨Q, hUQ, hQinv⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_invariant_sylow_containment
      (G := ↥O) (A := ↥B) p q hBp hOp (U.subgroupOf O) hUq' hUinv
  refine ⟨(Q : Subgroup ↥O).map O.subtype, ⟨Q, rfl⟩, ?_, ?_⟩
  · intro u hu
    exact ⟨⟨u, hUO hu⟩, hUQ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  · intro b hb
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(⟨b, hb⟩ : ↥B) • x, hQinv ⟨b, hb⟩ x hx, ?_⟩
    rw [Subgroup.coe_subtype, hsmul]
    rfl

section Frattini

variable {A M H : Subgroup G} {c : G}

theorem not_three_dvd_card_s189_sup_theta189 (M H : Subgroup G) (c : G) :
    ¬ 3 ∣ Nat.card ↥(s189 M H ⊔ theta189 M H c) := by
  have hSN : s189 M H ≤ Subgroup.normalizer (theta189 M H c : Set G) :=
    (le_sup_left : s189 M H ≤ sk189 M H c).trans (sk189_le_normalizer_theta189 M H c)
  have h1 := Subgroup.relIndex_mul_card (theta189 M H c) (s189 M H ⊔ theta189 M H c)
  rw [inf_eq_left.mpr le_sup_right, Sec20.relIndex_sup_eq_of_le_normalizer hSN] at h1
  rw [← h1]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
  · have h2 := Subgroup.relIndex_dvd_card (theta189 M H c) (s189 M H)
    obtain ⟨k, hk⟩ := (isPGroup_s189 M H).exists_card_eq
    rw [hk] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow (h.trans h2))
    omega
  · exact not_three_dvd_card_theta189 M H c h

theorem isSylowOf_s189 (h186 : Item186H) (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    CFSG.ABGLocalTools.IsSylowOf 2 (s189 M H) (s189 M H ⊔ theta189 M H c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAO : A ≤ Subgroup.normalizer ((s189 M H ⊔ theta189 M H c : Subgroup G) : Set G) :=
    fun _ ha => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_s189 h ha, ((le_normalizer_sk189 h).trans (normalizer_sk189_le M H c)) ha⟩
  obtain ⟨T, hT, hST, hAT⟩ := exists_isSylowOf_le_of_coprime189 hA.isPGroup hAO
    (not_three_dvd_card_s189_sup_theta189 M H c) le_sup_left (isPGroup_s189 M H)
    (le_normalizer_s189 h)
  have hTmem : T ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT.isPGroup, hAT⟩
  have hTS : T = s189 M H :=
    (mem_maxInvariantPiSubgroups_iff.mp (s189_mem_maxInvariant h186 h h7)).2 T hTmem hST
  rwa [hTS] at hT

theorem mem_n189_of_mem_normalizer_sAlpha (h186 : Item186H) (h187 : Item187)
    (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) {x : ↥(sk189 M H c)}
    (hx : alpha189 M H c x ∈
      Subgroup.normalizer (sAlpha189 M H c : Set (SKAlpha189 M H c))) :
    (x : G) ∈ n189 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYSK : s189 M H ⊔ theta189 M H c ≤ sk189 M H c := sup_le le_sup_left (theta189_le M H c)
  have hpre : (sAlpha189 M H c).comap (alpha189 M H c) =
      (s189 M H ⊔ theta189 M H c).subgroupOf (sk189 M H c) := by
    rw [sAlpha189, Subgroup.comap_map_eq, alpha189, QuotientGroup.ker_mk',
      Subgroup.subgroupOf_sup le_sup_left (theta189_le M H c)]
    congr 1
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  have hxN : x ∈ Subgroup.normalizer
      (((s189 M H ⊔ theta189 M H c).subgroupOf (sk189 M H c) : Subgroup _) : Set _) := by
    rw [← hpre, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hx
  have hxG := Sec20.mem_normalizer_of_mem_normalizer_subgroupOf hYSK hxN
  obtain ⟨n, hn, m, hm, hnm⟩ := exists_mul_of_isSylowOf (isSylowOf_s189 h186 h h7)
    (Subgroup.zpowers_le.mpr hxG) (Subgroup.mem_zpowers _)
  rw [hnm]
  exact (n189 H).mul_mem ((sup_le (s189_le_n189 M H) (theta189_le_n189 h187 h h7)) hn)
    (normalizer_s189_le h186 h h7 hm)

omit [Finite G] in
theorem s189_le_theta189_of_sAlpha_eq_bot (hS : sAlpha189 M H c = ⊥) :
    s189 M H ≤ theta189 M H c := by
  intro s hs
  have hsk : s ∈ sk189 M H c := (le_sup_left : s189 M H ≤ sk189 M H c) hs
  have hs' : (⟨s, hsk⟩ : ↥(sk189 M H c)) ∈ (s189 M H).subgroupOf (sk189 M H c) := hs
  have h1 : alpha189 M H c ⟨s, hsk⟩ ∈ sAlpha189 M H c :=
    Subgroup.mem_map_of_mem _ hs'
  rw [hS, Subgroup.mem_bot, alpha189, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem mem_n189_of_mem_normalizer_cAlpha (h187 : Item187) (h : Sec18H G A M H c)
    (h7 : Hyp187 A M H c) (hcN : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H)
    {x : ↥(sk189 M H c)} (hx : alpha189 M H c x ∈ Subgroup.normalizer
      (imAlpha189 M H c (Subgroup.zpowers c) : Set (SKAlpha189 M H c))) :
    (x : G) ∈ n189 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcSK : Subgroup.zpowers c ≤ sk189 M H c := Subgroup.zpowers_le.mpr
    ((le_sup_right : normalClosureIn M c ≤ sk189 M H c) (Sec20.self_mem_normalClosureIn M c))
  have hYSK : Subgroup.zpowers c ⊔ theta189 M H c ≤ sk189 M H c :=
    sup_le hcSK (theta189_le M H c)
  have hpre : (imAlpha189 M H c (Subgroup.zpowers c)).comap (alpha189 M H c) =
      (Subgroup.zpowers c ⊔ theta189 M H c).subgroupOf (sk189 M H c) := by
    rw [imAlpha189, Subgroup.comap_map_eq, alpha189, QuotientGroup.ker_mk',
      Subgroup.subgroupOf_sup hcSK (theta189_le M H c)]
    congr 1
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  have hxN : x ∈ Subgroup.normalizer
      (((Subgroup.zpowers c ⊔ theta189 M H c).subgroupOf (sk189 M H c) : Subgroup _) :
        Set _) := by
    rw [← hpre, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hx
  have hxG := Sec20.mem_normalizer_of_mem_normalizer_subgroupOf hYSK hxN
  have hc3 := pow_three_of_sec18H189 h
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers c)
      (Subgroup.zpowers c ⊔ theta189 M H c) :=
    Sec20.isSylowOf_sup_of_coprime (Sec20.isPGroup_zpowers_of_pow_three hc3)
      (not_three_dvd_card_theta189 M H c)
      (hcSK.trans (sk189_le_normalizer_theta189 M H c))
  obtain ⟨n, hn, m, hm, hnm⟩ := exists_mul_of_isSylowOf hsyl
    (Subgroup.zpowers_le.mpr hxG) (Subgroup.mem_zpowers _)
  rw [hnm]
  have hcN' : Subgroup.zpowers c ≤ n189 H := Subgroup.zpowers_le.mpr
    (le_normalizer_inSubgroup_perfectResidual H (le_of_sec18H189 h (mem_of_sec18H189 h)))
  exact (n189 H).mul_mem ((sup_le hcN' (theta189_le_n189 h187 h h7)) hn) (hcN hm)

end Frattini

section Lifting

variable {M H : Subgroup G} {c : G}

omit [Finite G] in
theorem kAlpha_inf_normalizer_le189 {X : Subgroup (SKAlpha189 M H c)}
    (hlift : ∀ x : ↥(sk189 M H c), alpha189 M H c x ∈ Subgroup.normalizer
      (X : Set (SKAlpha189 M H c)) → (x : G) ∈ n189 H) :
    kAlpha189 M H c ⊓ Subgroup.normalizer (X : Set (SKAlpha189 M H c)) ≤
      ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c) := by
  rintro _ ⟨⟨y, hy, rfl⟩, hyN⟩
  exact ⟨y, ⟨hy, hlift y hyN⟩, rfl⟩

omit [Finite G] in
theorem le_n189_of_kAlpha_le189 (hθ : theta189 M H c ≤ n189 H)
    (hK : kAlpha189 M H c ≤
      ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c)) :
    normalClosureIn M c ≤ n189 H := by
  intro k hk
  have hkSK : k ∈ sk189 M H c := (le_sup_right : normalClosureIn M c ≤ sk189 M H c) hk
  obtain ⟨y, hy, hyk⟩ := hK ⟨⟨k, hkSK⟩, hk, rfl⟩
  have ht : (y : G)⁻¹ * k ∈ theta189 M H c := ⟨_, QuotientGroup.eq.mp hyk, rfl⟩
  have hk' : k = y * ((y : G)⁻¹ * k) := by group
  rw [hk']
  exact (n189 H).mul_mem hy.2 (hθ ht)

end Lifting

section Covering

variable {M H : Subgroup G} {c : G}

omit [Finite G] in
theorem le_n189_of_coveredMod {X : Subgroup G} (hcov : CoveredMod189 M H c X)
    (hX : Subgroup.normalizer (X : Set G) ≤ n189 H) (hθ : theta189 M H c ≤ n189 H) :
    normalClosureIn M c ≤ n189 H :=
  hcov.trans (sup_le (inf_le_right.trans hX) hθ)

omit [Finite G] in
theorem le_n189_of_coveredTwoMod {X : Subgroup G} (hcov : CoveredTwoMod189 M H c X)
    (hX : Subgroup.normalizer (X : Set G) ≤ n189 H)
    (hc : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H)
    (hθ : theta189 M H c ≤ n189 H) : normalClosureIn M c ≤ n189 H :=
  hcov.trans (sup_le (sup_le (inf_le_right.trans hX) (inf_le_right.trans hc)) hθ)

end Covering

section Transfer

variable {M H : Subgroup G} {c : G}

@[expose] noncomputable def kToKAlpha189 (M H : Subgroup G) (c : G) :
    ↥(normalClosureIn M c) →* ↥(kAlpha189 M H c) :=
  ((alpha189 M H c).comp (Subgroup.inclusion
    (le_sup_right : normalClosureIn M c ≤ sk189 M H c))).codRestrict (kAlpha189 M H c)
    fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2)

omit [Finite G] in
theorem coe_kToKAlpha189 (k : ↥(normalClosureIn M c)) :
    (kToKAlpha189 M H c k : SKAlpha189 M H c) =
      alpha189 M H c ⟨k, (le_sup_right : normalClosureIn M c ≤ sk189 M H c) k.2⟩ :=
  rfl

omit [Finite G] in
theorem kToKAlpha189_surjective : Function.Surjective (kToKAlpha189 M H c) := by
  rintro ⟨_, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

omit [Finite G] in
theorem mem_ker_kToKAlpha189 (k : ↥(normalClosureIn M c)) :
    k ∈ (kToKAlpha189 M H c).ker ↔ (k : G) ∈ theta189 M H c := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, coe_kToKAlpha189, Subgroup.coe_one, alpha189,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h1
    exact ⟨_, h1, rfl⟩
  · rintro ⟨t, ht, hteq⟩
    have : (⟨k, (le_sup_right : normalClosureIn M c ≤ sk189 M H c) k.2⟩ : ↥(sk189 M H c)) = t :=
      Subtype.ext hteq.symm
    rw [this]
    exact ht

omit [Finite G] in
theorem ker_kToKAlpha189 (hK : normalClosureIn M c ⊓ theta189 M H c =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    (kToKAlpha189 M H c).ker = CFSG.pCore 2 ↥(normalClosureIn M c) := by
  ext k
  rw [mem_ker_kToKAlpha189, mem_pCore_iff_mem_pCoreOf, ← hK]
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

@[expose] noncomputable def kQuotEquiv189 (hK : normalClosureIn M c ⊓ theta189 M H c =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    ↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c) ≃* ↥(kAlpha189 M H c) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_kToKAlpha189 hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ kToKAlpha189_surjective)

omit [Finite G] in
theorem map_kQuotEquiv189 (hK : normalClosureIn M c ⊓ theta189 M H c =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) (Y : Subgroup G) :
    (((normalClosureIn M c ⊓ Y).subgroupOf (normalClosureIn M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(normalClosureIn M c)))).map
        (kQuotEquiv189 hK).toMonoidHom =
      (((normalClosureIn M c ⊓ Y).subgroupOf (sk189 M H c)).map (alpha189 M H c)).subgroupOf
        (kAlpha189 M H c) := by
  ext z
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨k, (le_sup_right : normalClosureIn M c ≤ sk189 M H c) k.2⟩, hk, rfl⟩
  · intro hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    refine ⟨QuotientGroup.mk' _ ⟨y, hy.1⟩, ⟨⟨y, hy.1⟩, hy, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [← hyz]
    rfl

end Transfer

theorem isMaxParabolicRankTwo_of_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) {P : Subgroup X} (h : IsMaxParabolicRankTwo (P.map e.toMonoidHom)) :
    IsMaxParabolicRankTwo P := by
  obtain ⟨hco, T, hT⟩ := h
  refine ⟨((MulEquiv.mapSubgroup e).isCoatom_iff P).mp hco, ?_⟩
  have hinj : Function.Injective e.toMonoidHom := fun a b hab => e.injective hab
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨T.comapOfInjective e.toMonoidHom hinj ?_, ?_⟩
  · rw [MonoidHom.range_eq_top_of_surjective _ hsurj]
    exact le_top
  · change Subgroup.normalizer (((T : Subgroup Y).comap e.toMonoidHom : Subgroup X) : Set X) ≤ P
    rw [← Subgroup.comap_normalizer_eq_of_surjective _ hsurj]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hT hx
    rw [← e.injective hyx]
    exact hy

theorem isMaxParabolic_of_case189iv (h186 : Item186H) (h187 : Item187) {A M H : Subgroup G}
    {c : G} (h : Sec18H G A M H c) (h7 : Hyp187 A M H c)
    (hnot : ¬ normalClosureIn M c ≤ n189 H) (hiv : Case189iv M H c) :
    IsMaxParabolicRankTwo ((((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map
      (alpha189 M H c)).subgroupOf (kAlpha189 M H c)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K₁, hK₁, ⟨hco, T, hT⟩, hS⟩ := hiv
  set Y := ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c)
    with hYdef
  have hK₁Y : K₁ ≤ Y := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hK₁ hz
    have hzN : alpha189 M H c y ∈
        Subgroup.normalizer (sAlpha189 M H c : Set (SKAlpha189 M H c)) := by
      rw [hS]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁ hz
    exact ⟨y, ⟨hy, mem_n189_of_mem_normalizer_sAlpha h186 h187 h h7 hzN⟩, rfl⟩
  have hle : K₁.subgroupOf (kAlpha189 M H c) ≤ Y.subgroupOf (kAlpha189 M H c) :=
    fun _ hx => hK₁Y hx
  have hne : Y.subgroupOf (kAlpha189 M H c) ≠ ⊤ := by
    intro htop
    refine hnot (le_n189_of_kAlpha_le189 (theta189_le_n189 h187 h h7) fun z hz => ?_)
    have hmem : (⟨z, hz⟩ : ↥(kAlpha189 M H c)) ∈ Y.subgroupOf (kAlpha189 M H c) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  have heq : Y.subgroupOf (kAlpha189 M H c) = K₁.subgroupOf (kAlpha189 M H c) := by
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd (hco.2 _ hlt) hne
    · exact heq.symm
  rw [heq]
  exact ⟨hco, T, hT⟩

section Theta

theorem pCoreOf_le_theta189 (M H : Subgroup G) (c : G) :
    CFSG.Open.pCoreOf 2 (normalClosureIn M c) ≤ theta189 M H c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 (normalClosureIn M c) with hO
  have hOSK : O ≤ sk189 M H c := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_right
  have hSKO : sk189 M H c ≤ Subgroup.normalizer (O : Set G) :=
    (sk189_le_normalizer_k M H c).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hn : (O.subgroupOf (sk189 M H c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOSK).mpr hSKO
  have hO2 : IsPGroup 2 (O.subgroupOf (sk189 M H c)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
  have hOs : Group.IsSolvable (O.subgroupOf (sk189 M H c)) := by
    have := hO2.isNilpotent
    infer_instance
  have hO3 : ¬ 3 ∣ Nat.card (O.subgroupOf (sk189 M H c)) := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hle := (solvable_prime_complement_core_characterization (H := ↥(sk189 M H c))
    Nat.prime_three).2.2.2.1 _ hn hOs hO3
  intro x hx
  exact ⟨⟨x, hOSK hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem le_normalizer_inf_theta189 (M H : Subgroup G) (c : G) :
    normalClosureIn M c ≤
      Subgroup.normalizer ((normalClosureIn M c ⊓ theta189 M H c : Subgroup G) : Set G) :=
  fun _ hk => Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk)
    (sk189_le_normalizer_theta189 M H c
      ((le_sup_right : normalClosureIn M c ≤ sk189 M H c) hk))

theorem inf_theta189_eq_of_pPrimeCore_eq (M H : Subgroup G) (c : G)
    (h3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    normalClosureIn M c ⊓ theta189 M H c = CFSG.Open.pCoreOf 2 (normalClosureIn M c) := by
  refine le_antisymm ?_
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (pCoreOf_le_theta189 M H c))
  rw [← h3]
  refine Late.le_inSubgroup_pPrimeCore_of ?_ inf_le_left (le_normalizer_inf_theta189 M H c)
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  exact not_three_dvd_card_theta189 M H c (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem inf_theta189_eq_of_isSimpleGroup (M H : Subgroup G) (c : G)
    [Group.IsPerfect ↥(normalClosureIn M c)]
    [IsSimpleGroup (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c))] :
    normalClosureIn M c ⊓ theta189 M H c = CFSG.Open.pCoreOf 2 (normalClosureIn M c) := by
  refine le_antisymm ?_
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (pCoreOf_le_theta189 M H c))
  set K := normalClosureIn M c with hKdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set Z := (K ⊓ theta189 M H c).subgroupOf K with hZ
  have hZn : Z.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf_theta189 M H c)
  have hZs : Group.IsSolvable Z := by
    have := isSolvable_theta189 M H c
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion (inf_le_right : K ⊓ theta189 M H c ≤ theta189 M H c)).comp
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ theta189 M H c ≤ K)).toMonoidHom)
      ((Subgroup.inclusion_injective
        (inf_le_right : K ⊓ theta189 M H c ≤ theta189 M H c)).comp (MulEquiv.injective _))
  have := hZn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Z.map π) with hbot | htop
  · intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥K) ∈ Z := hx
    have h1 : π ⟨x, hx.1⟩ = 1 := by
      have := Subgroup.mem_map_of_mem π hxZ
      rwa [hbot, Subgroup.mem_bot] at this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    exact h1
  · exfalso
    have hsurj : Function.Surjective (π.comp Z.subtype) := by
      intro q
      have hq : q ∈ Z.map π := by rw [htop]; exact Subgroup.mem_top q
      obtain ⟨z, hz, rfl⟩ := hq
      exact ⟨⟨z, hz⟩, rfl⟩
    have hsol : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Group.isSolvable_of_surjective hsurj
    exact Group.IsPerfect.not_isSolvable _ hsol

end Theta

theorem isQuasisimple_of_isPerfect189 {Q : Type*} [Group Q] [Group.IsPerfect Q]
    [IsSimpleGroup Q] : CFSG.IsQuasisimple Q := by
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra hcomm
  push Not at hcomm
  exact Group.IsPerfect.not_isMulCommutative Q ⟨⟨hcomm⟩⟩

omit [Finite G] in
theorem isPerfect_of_mem_thetaComponentsIn189 {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) : Group.IsPerfect ↥K := by
  obtain ⟨hKM, hp, -, -⟩ := mem_thetaComponentsIn_iff.mp hK
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom)
    (MulEquiv.surjective _)

omit [Finite G] in
theorem mem_oTwoComponentsIn_of189 {M K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    [IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)] : K ∈ oTwoComponentsIn M := by
  obtain ⟨hKM, -, hsn, -⟩ := mem_thetaComponentsIn_iff.mp hK
  have := isPerfect_of_mem_thetaComponentsIn189 hK
  exact mem_oTwoComponentsIn_of_quasisimple hKM hsn (Subgroup.isPerfect_iff.mp this)
    isQuasisimple_of_isPerfect189

theorem not_nonempty_equiv_projSL_two_one189 {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] : ¬ Nonempty (Q ≃* projSL 2 (GaloisField 2 1)) := by
  rintro ⟨e⟩
  have hcard : Nat.card Q = 6 := by
    rw [Nat.card_congr e.toEquiv, Sec20.card_projSL_galois (by norm_num) (by norm_num)]
    simp only [show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [hcard]; norm_num)
  set P := Subgroup.zpowers x with hP
  have hP3 : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 2 := by
    have := P.card_mul_index
    rw [hP3, hcard] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hc : Nat.card (Q ⧸ P) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have := isCyclic_of_prime_card (p := 2) hc
  have hle : commutator Q ≤ P :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp inferInstance
  rw [Group.IsPerfect.commutator_eq_top] at hle
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_top, hcard, hP3] at h1
  omega

section OmegaOne

omit [Finite G] in
theorem omegaOneTwo189_le (S : Subgroup G) : omegaOneTwo189 S ≤ S :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem map_le_omegaOneTwo189 {S : Subgroup G} {E : Subgroup S} [IsElementaryAbelian 2 E] :
    E.map S.subtype ≤ omegaOneTwo189 S := by
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ⟨x.2, ?_⟩
  have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
  change (x : G) ^ 2 = 1
  rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]

variable {S T : Subgroup G} (hTS : T ≤ S)

omit [Finite G] in
include hTS in
theorem exists_eq_map_inclusion189
    (hET : ∀ E : Subgroup S, IsElementaryAbelian 2 E → E.map S.subtype ≤ T)
    (E : Subgroup S) (hE : IsElementaryAbelian 2 E) :
    ∃ E' : Subgroup T, IsElementaryAbelian 2 E' ∧ E'.map (Subgroup.inclusion hTS) = E := by
  have hinj : Function.Injective (Subgroup.inclusion hTS) := Subgroup.inclusion_injective hTS
  have hrange : E ≤ (Subgroup.inclusion hTS).range := by
    intro e he
    exact ⟨⟨e, hET E hE ⟨e, he, rfl⟩⟩, rfl⟩
  refine ⟨E.comap (Subgroup.inclusion hTS), ?_, Subgroup.map_comap_eq_self hrange⟩
  have hcomm : ∀ a b : ↥(E.comap (Subgroup.inclusion hTS)), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply hinj
    change (Subgroup.inclusion hTS) ((a : T) * b) = (Subgroup.inclusion hTS) ((b : T) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  have hexp : ∀ x : ↥(E.comap (Subgroup.inclusion hTS)), x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    apply hinj
    change (Subgroup.inclusion hTS) ((x : T) ^ 2) = (Subgroup.inclusion hTS) 1
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) _ x.2
  exact
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }

omit [Finite G] in
include hTS in
theorem pRank_eq_of_le189
    (hET : ∀ E : Subgroup S, IsElementaryAbelian 2 E → E.map S.subtype ≤ T) :
    CFSG.pRank 2 T = CFSG.pRank 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (Subgroup.inclusion hTS) := Subgroup.inclusion_injective hTS
  unfold CFSG.pRank
  congr 1
  ext r
  constructor
  · rintro ⟨E, hE, hcard⟩
    refine ⟨E.map (Subgroup.inclusion hTS), IsElementaryAbelian.map _, ?_⟩
    rw [Subgroup.card_map_of_injective hinj, hcard]
  · rintro ⟨E, hE, hcard⟩
    obtain ⟨E', hE', rfl⟩ := exists_eq_map_inclusion189 hTS hET E hE
    exact ⟨E', hE', by rw [← hcard, Subgroup.card_map_of_injective hinj]⟩

include hTS in
theorem higherElemThompson_eq_map189
    (hET : ∀ E : Subgroup S, IsElementaryAbelian 2 E → E.map S.subtype ≤ T) (j : ℕ) :
    CFSG.higherElemThompson S j =
      (CFSG.higherElemThompson T j).map (Subgroup.inclusion hTS) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (Subgroup.inclusion hTS) := Subgroup.inclusion_injective hTS
  have hrank := pRank_eq_of_le189 hTS hET
  have hfam : CFSG.higherElemThompsonFamily S j =
      (fun E => E.map (Subgroup.inclusion hTS)) '' CFSG.higherElemThompsonFamily T j := by
    ext E
    rw [CFSG.mem_higherElemThompsonFamily_iff]
    constructor
    · rintro ⟨hE, hcard⟩
      obtain ⟨E', hE', rfl⟩ := exists_eq_map_inclusion189 hTS hET E hE
      refine ⟨E', (CFSG.mem_higherElemThompsonFamily_iff j E').mpr ⟨hE', ?_⟩, rfl⟩
      rw [← Subgroup.card_map_of_injective hinj, hcard, hrank]
    · rintro ⟨E', hE', rfl⟩
      obtain ⟨hE'a, hcard⟩ := (CFSG.mem_higherElemThompsonFamily_iff j E').mp hE'
      refine ⟨IsElementaryAbelian.map _, ?_⟩
      rw [Subgroup.card_map_of_injective hinj, hcard, hrank]
  rw [CFSG.higherElemThompson, CFSG.higherElemThompson, hfam, sSup_image,
    ((Subgroup.gc_map_comap (Subgroup.inclusion hTS)).l_sSup)]

omit [Finite G] in
include hTS in
theorem omegaOneCenter_map_inclusion189 (J : Subgroup T) :
    CFSG.omegaOneCenter (J.map (Subgroup.inclusion hTS)) =
      (CFSG.omegaOneCenter J).map (Subgroup.inclusion hTS) := by
  have hinj : Function.Injective (Subgroup.inclusion hTS) := Subgroup.inclusion_injective hTS
  ext z
  rw [Sec20.mem_omegaOneCenter_iff']
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hc, h2⟩
    refine ⟨w, (Sec20.mem_omegaOneCenter_iff' J w).mpr ⟨hw, fun y hy => hinj ?_, hinj ?_⟩, rfl⟩
    · simpa using hc _ ⟨y, hy, rfl⟩
    · simpa using h2
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwJ, hc, h2⟩ := (Sec20.mem_omegaOneCenter_iff' J w).mp hw
    refine ⟨⟨w, hwJ, rfl⟩, ?_, by rw [← map_pow, h2, map_one]⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc y hy]

include hTS in
theorem fourChar_eq_of_le189
    (hET : ∀ E : Subgroup S, IsElementaryAbelian 2 E → E.map S.subtype ≤ T) (i : Fin 4)
    (hi : i ≠ 0) : fourChar S i = fourChar T i := by
  have hcomp : S.subtype.comp (Subgroup.inclusion hTS) = T.subtype := by
    ext; rfl
  fin_cases i
  · exact absurd rfl hi
  · change (CFSG.higherElemThompson S 0).map S.subtype =
      (CFSG.higherElemThompson T 0).map T.subtype
    rw [higherElemThompson_eq_map189 hTS hET, Subgroup.map_map, hcomp]
  · change (CFSG.higherElemThompsonOmega S 1).map S.subtype =
      (CFSG.higherElemThompsonOmega T 1).map T.subtype
    rw [CFSG.higherElemThompsonOmega, CFSG.higherElemThompsonOmega,
      higherElemThompson_eq_map189 hTS hET, omegaOneCenter_map_inclusion189 hTS,
      Subgroup.map_map, hcomp]
  · change (CFSG.higherElemThompsonOmega S 2).map S.subtype =
      (CFSG.higherElemThompsonOmega T 2).map T.subtype
    rw [CFSG.higherElemThompsonOmega, CFSG.higherElemThompsonOmega,
      higherElemThompson_eq_map189 hTS hET, omegaOneCenter_map_inclusion189 hTS,
      Subgroup.map_map, hcomp]

theorem normalizer_omegaOneTwo189_le (S : Subgroup G) (i : Fin 4) (hi : i ≠ 0) :
    Subgroup.normalizer (omegaOneTwo189 S : Set G) ≤
      Subgroup.normalizer (fourChar S i : Set G) := by
  rw [fourChar_eq_of_le189 (omegaOneTwo189_le S)
    (fun E hE => by exact map_le_omegaOneTwo189) i hi]
  exact Sec20.normalizer_le_normalizer_fourChar _ i

end OmegaOne

omit [Finite G] in
theorem isSimpleGroup_of_item189Three {K : Subgroup G}
    (h : (∃ n : ℕ, Odd n ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 2 (GaloisField 2 n)))) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  rcases h with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 n)
    exact e.isSimpleGroup
  · have := Sec21.isSimpleGroup_projSL_two hn
    exact e.isSimpleGroup

theorem item189_of_steps (h186 : Item186H) (h187 : Item187) (hK0 : Step189K0)
    (hTwo : Step189Two) (hType : Step189KType) (hO2 : Sec20.Step189O2)
    (hO2B : Step189O2Bound) (hList : Step189List) (hNL : Step189NotNL) (hThree : Step189Three)
    (hSNe : Step189SNe) (hOdd : Step189OddL2) (hInsp : Step189InspectI) (hIdx : Step189IndexI)
    (h1411 : Asc82Item1411And1412) (hL16 : Step189L16) (hL4 : Step189L4) (hO3 : Step189O3) :
    Item189 := by
  intro G _ _ A M H c h h7 K N
  obtain ⟨hKθ, hrank⟩ := hK0 G A M H c h h7
  have hnot := hNL G A M H c h h7 hKθ hrank
  have hset : Setting189 G A M H c :=
    { toSec18H := h
      hyp187 := h7
      mem_thetaComponentsIn := hKθ
      pRank_eq := hrank
      rankOne := hType G A M H c h h7 hKθ hrank
      not_le := hnot
      three := hThree G A M H c h h7
      sAlpha_ne := hSNe G A M H c h h7 hnot }
  have hθN := theta189_le_n189 h187 h h7
  have hperf := isPerfect_of_mem_thetaComponentsIn189 hKθ
  have h4case : Cases1411189 M H c → False := by
    intro hc
    rcases h1411 G A M H c hset hc with ⟨i, j, hij, hi, hj⟩ | ⟨h16, hcard⟩
    · rcases hThree G A M H c h h7 i j hij with hiN | hjN
      · exact hnot (le_n189_of_coveredMod hi hiN hθN)
      · exact hnot (le_n189_of_coveredMod hj hjN hθN)
    · have hcov := hL16 G A M H c hset hc h16 hcard
      have hO2ne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ := by
        intro hbot
        have := hO2B G A M H c h h7 hbot
        omega
      have hΩ : Subgroup.normalizer (omegaOneTwo189 (s189 M H) : Set G) ≤ n189 H := by
        rcases hThree G A M H c h h7 1 2 (by decide) with h1 | h1
        · exact (normalizer_omegaOneTwo189_le _ 1 (by decide)).trans h1
        · exact (normalizer_omegaOneTwo189_le _ 2 (by decide)).trans h1
      exact hnot (le_n189_of_coveredTwoMod hcov hΩ (normalizer_zpowers_le189 h7 hO2ne) hθN)
  have hmain : (∃ n : ℕ, Odd n ∧
        Nonempty (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c) ≃*
          projSL 3 (GaloisField 2 n)) ∧
        IsMaxParabolicRankTwo (((normalClosureIn M c ⊓ n189 H).subgroupOf
          (normalClosureIn M c)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(normalClosureIn M c))))) ∨
      (∃ n : ℕ, Even n ∧ 2 ≤ n ∧
        Nonempty (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c) ≃*
          projSL 2 (GaloisField 2 n)) ∧ ¬ 4 ∣ (M ⊓ n189 H).relIndex M) := by
    rcases hList G A M H c hset with hi | hii | hiii | hiv | hv | hvi
    ·
      by_cases hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
      · obtain ⟨m, hm0, ⟨e⟩⟩ := hO2 G A M H c h h7 hO
        have hm2 : 2 ≤ m := by
          by_contra hlt
          have hm1 : m = 1 := by omega
          subst hm1
          exact not_nonempty_equiv_projSL_two_one189 ⟨e⟩
        have := Sec21.isSimpleGroup_projSL_two hm2
        have : IsSimpleGroup (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c)) :=
          e.isSimpleGroup
        have hKθ' := inf_theta189_eq_of_isSimpleGroup M H c
        set ψ := kQuotEquiv189 hKθ' with hψ
        have hmeven : Even m := by
          by_contra hodd
          exact hOdd G A M H c hset m (Nat.not_even_iff_odd.mp hodd) ⟨ψ.symm.trans e⟩
        exact Or.inr ⟨m, hmeven, hm2, ⟨e⟩, hIdx G A M H c hset hi hO ⟨m, ⟨ψ.symm.trans e⟩⟩⟩
      · have hgen := hInsp G A M H c hset hi hO
        have hcN := normalizer_zpowers_le189 h7 hO
        refine (hnot (le_n189_of_kAlpha_le189 hθN (hgen.trans (sup_le ?_ ?_)))).elim
        · exact kAlpha_inf_normalizer_le189 fun x hx =>
            mem_n189_of_mem_normalizer_sAlpha h186 h187 h h7 hx
        · exact kAlpha_inf_normalizer_le189 fun x hx =>
            mem_n189_of_mem_normalizer_cAlpha h187 h h7 hcN hx
    ·
      exact (hset.sAlpha_ne hii.2).elim
    ·
      by_cases hL : Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2))
      · have hidx := hL4 G A M H c hset hiii hL
        have hO3' := hO3 G A M H c hset (Or.inl ⟨2, even_two, by norm_num, hL⟩)
        have hKθ' := inf_theta189_eq_of_pPrimeCore_eq M H c hO3'
        obtain ⟨e⟩ := hL
        exact Or.inr ⟨2, even_two, le_rfl, ⟨(kQuotEquiv189 hKθ').trans e⟩, hidx⟩
      · exact (h4case (Or.inl ⟨hiii, hL⟩)).elim
    ·
      have hO3' := hO3 G A M H c hset (Or.inr hiv)
      have hKθ' := inf_theta189_eq_of_pPrimeCore_eq M H c hO3'
      have hpar := isMaxParabolic_of_case189iv h186 h187 h h7 hnot hiv
      rw [← map_kQuotEquiv189 hKθ' (n189 H)] at hpar
      obtain ⟨n, hn, ⟨e⟩⟩ := hiv.1
      exact Or.inl ⟨n, hn, ⟨(kQuotEquiv189 hKθ').trans e⟩,
        isMaxParabolicRankTwo_of_map_mulEquiv (kQuotEquiv189 hKθ') hpar⟩
    · exact (h4case (Or.inr (Or.inl hv))).elim
    · exact (h4case (Or.inr (Or.inr hvi))).elim
  have hsimple : IsSimpleGroup (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c)) := by
    refine isSimpleGroup_of_item189Three ?_
    rcases hmain with ⟨n, hn, he, -⟩ | ⟨n, -, hn, he, -⟩
    · exact Or.inl ⟨n, hn, he⟩
    · exact Or.inr ⟨n, hn, he⟩
  refine ⟨⟨mem_oTwoComponentsIn_of189 hKθ, hnot⟩, hTwo G A M H c h hrank, ?_⟩
  rcases hmain with hm | ⟨n, hn, hn2, he, hidx⟩
  · exact Or.inl hm
  · exact Or.inr ⟨n, hn, by omega, he, hidx⟩

end CFSG.RankThree.PartTwo.Sec18
