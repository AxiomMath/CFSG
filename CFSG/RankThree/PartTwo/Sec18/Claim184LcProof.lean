module

public import CFSG.RankThree.PartTwo.Sec18.Item184a
public import CFSG.RankThree.PartTwo.Sec18.Rem187Bypass
public import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
public import CFSG.RankThree.PartTwo.KFacts.KS14SL34
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThreeEvenClassification.Helpers (centralizer_map_eq_of_pGroup_prime_complement_kernel)
open scoped Pointwise

namespace Claim184LcProof

variable {G : Type} [Group G] [Finite G]

theorem map_inSubgroup_perfectResidual {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (P : Subgroup X) :
    (inSubgroup perfectResidual P).map f = inSubgroup perfectResidual (P.map f) := by
  have h := map_perfectResidual_eq (f := f.subgroupMap P) (f.subgroupMap_surjective P)
  rw [inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem quotient_mulEquiv_map {H K : Subgroup G} (hKH : K ≤ H)
    (hO : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 H) :
    Nonempty (K ⧸ CFSG.pCore 2 K ≃*
      (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set φ : K →* H ⧸ CFSG.pCore 2 H := π.comp (Subgroup.inclusion hKH) with hφ
  have hmem : ∀ x : K, φ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 H := by
    intro x
    rw [hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf]
    rfl
  have hrange : φ.range = (K.subgroupOf H).map π := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hKH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 K := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      have himg : φ.ker.map K.subtype ≤ CFSG.Open.pCoreOf 2 H := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hmem x).mp hx
      exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le himg).of_equiv
        (φ.ker.equivMapOfInjective _ K.subtype_injective).symm
    · intro x hx
      rw [MonoidHom.mem_ker, hmem]
      exact hO ((mem_pCore_iff_mem_pCoreOf x).mp hx)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem quotient_mulEquiv_of_le_sup {L R N : Subgroup G} (hLN : L ≤ N) (hNLR : N ≤ L ⊔ R)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) :
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* N ⧸ CFSG.pCore 2 N) ∧
      CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : L →* N ⧸ CFSG.pCore 2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 N)).comp (Subgroup.inclusion hLN) with hφ
  have hker : ∀ l : L, φ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 N := by
    intro l
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨l, hl, hln⟩ := exists_mem_mul_of_le_sup hLN hNLR hLR hNR hR n.2
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_eq_mk']
    refine ⟨⟨l⁻¹ * n, N.mul_mem (N.inv_mem (hLN hl)) n.2⟩,
      (mem_pCore_iff_mem_pCoreOf _).mpr hln, ?_⟩
    apply Subtype.ext
    simp
  have hkerle : φ.ker ≤ CFSG.pCore 2 L := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have himg : (φ.ker).map L.subtype ≤ CFSG.Open.pCoreOf 2 N := by
      rintro _ ⟨l, hl, rfl⟩
      exact (hker l).mp hl
    have hp := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le himg
    exact hp.of_equiv ((φ.ker).equivMapOfInjective _ L.subtype_injective).symm
  have hle : CFSG.pCore 2 L ≤ φ.ker := by
    have hn : ((CFSG.pCore 2 L).map φ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := L)).map φ hsurj
    have hp : IsPGroup 2 ((CFSG.pCore 2 L).map φ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := L)).map φ
    have hbot : (CFSG.pCore 2 L).map φ ≤ CFSG.pCore 2 (N ⧸ CFSG.pCore 2 N) :=
      le_sSup ⟨hn, hp⟩
    rw [pCore_quotient_pCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hbot
    exact hbot
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hkerle hle).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  have hl' : l ∈ CFSG.pCore 2 L := by
    exact hl
  exact (hker l).mp (hle hl')

theorem mem_thetaComponentsIn_of_mem_oTwoComponentsIn {X K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn X) : K ∈ thetaComponentsIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKX, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  refine Sec6.mem_thetaComponentsIn_of hKX (isPerfect_of_mem_oTwoComponentsIn hK) hsn ?_
  refine Sec14.isQuasisimple_quotient_theta_of_surjective
    (isQuasisimple_of_mem_oTwoComponentsIn hK) (QuotientGroup.mk' (CFSG.pCore 2 K))
    (QuotientGroup.mk'_surjective _) ?_ ?_
  · rw [QuotientGroup.ker_mk']
    have : Group.IsNilpotent (CFSG.pCore 2 K) :=
      (CFSG.pCore_isPGroup (p := 2) (G := K)).isNilpotent
    infer_instance
  · rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega

theorem centralizer_ne_top {A M : Subgroup G} (h : Sec18Std G A M) {c : G} (hc : c ≠ 1) :
    Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := h.isSimpleGroup
  have hcZ : c ∈ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton c)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hc (Subgroup.mem_bot.mp (hb ▸ hcZ))
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    have hb : b ∈ Subgroup.center G := ht ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem not_inducesOuterTheta_of_forall_mem {L : Subgroup G} {x : G}
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    ¬ Sec4.InducesOuterTheta x L := by
  rintro ⟨hxN, hnot⟩
  apply hnot
  refine ⟨1, ?_⟩
  rw [map_one]
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
  rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
  symm
  rw [QuotientGroup.eq]
  have h1 := hx _ (L.inv_mem l.2)
  have h2 : ((Sec4.compAction L ⟨x, hxN⟩ l)⁻¹ * l : L) ∈ CFSG.pCore 2 L := by
    rw [mem_pCore_iff_mem_pCoreOf]
    have : (((Sec4.compAction L ⟨x, hxN⟩ l)⁻¹ * l : L) : G) =
        x * (l : G)⁻¹ * x⁻¹ * (l : G)⁻¹⁻¹ := by
      simp [Sec4.compAction, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
    rw [this]
    exact h1
  exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.2.2.2.2
    2 Nat.prime_two (by norm_num) h2

theorem sup_mem_scriptH_of_le {A M H K T : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) (hKH : K ≤ H) (hTH : T ≤ H) (hK : ⁅K, K⁆ = K)
    (hKq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hT2 : IsPGroup 2 T) (hTM : T ≤ M)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hYT : (K ⊔ A ⊔ T) ⊓ M ≤ Subgroup.normalizer (T : Set G))
    (hTO : ¬ T ≤ CFSG.Open.pCoreOf 2 (K ⊔ A ⊔ T)) :
    K ⊔ A ⊔ T ∈ scriptH A M ∧ inSubgroup perfectResidual (K ⊔ A ⊔ T) = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAH := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  set Y := K ⊔ A ⊔ T with hYdef
  have hKY : K ≤ Y := le_sup_left.trans le_sup_left
  have hAY : A ≤ Y := le_sup_right.trans le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYH : Y ≤ H := sup_le (sup_le hKH hAH) hTH
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hAK) hTK
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  have hATs := isSolvable_sup_of_le_normalizer hA.1.1 hT2 hAT
  have hsupY : K ⊔ (A ⊔ T) = Y := by rw [hYdef, sup_assoc]
  have hq : Group.IsSolvable (Y ⧸ K.subgroupOf Y) :=
    isSolvable_quotient_of_sup_eq hKY (sup_le hAY hTY) hYK hsupY hATs
  have hres : inSubgroup perfectResidual Y = K :=
    le_antisymm (inSubgroup_perfectResidual_le_of_isSolvable hKY hq)
      (le_inSubgroup_perfectResidual hK hKY)
  have hTO' : T ≤ CFSG.Open.pCoreOf 2 (Y ⊓ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hTY hTM) hYT hT2
  refine ⟨⟨fun htop => hH.1 (top_le_iff.mp (htop ▸ hYH)), ?_, ?_, ?_⟩, hres⟩
  · rw [hres]
    apply le_antisymm
    · exact sup_le_sup_left hTO' _
    · exact sup_le (sup_le hKY hAY)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  · rw [hres]
    exact mem_oTwoComponentsIn_of_quasisimple hKY hKn.isSubnormal hK hKq
  · intro heq
    exact hTO (heq ▸ hTO')

theorem le_map_inf_centralizer {H : Subgroup G} {c : G} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    {W : Subgroup (H ⧸ CFSG.pCore 2 H)}
    (hcW : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨c, hcH⟩ ∈ Subgroup.centralizer (W : Set _)) :
    W ≤ ((H ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pCore 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set y : H := ⟨c, hcH⟩ with hy
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa [hy] using hc3)
  have hact : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hcent := centralizer_map_eq_of_pGroup_prime_complement_kernel 3 Nat.prime_three π
    (QuotientGroup.mk'_surjective _) hker _ hact
  have hC : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup H) : Set H) =
      (H ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
  rw [← hC, hcent, MonoidHom.map_zpowers]
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
  exact hcW

theorem map_perfectResidual_inf_centralizer {H : Subgroup G} {c : G} (hcH : c ∈ H)
    (hc3 : c ^ 3 = 1)
    (hcL : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨c, hcH⟩ ∈ Subgroup.centralizer
      (((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) : Subgroup _) : Set _)) :
    ((inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G))).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) := by
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set P := (H ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf H with hP
  set W := (perfectResidual H).map π with hW
  have hsub : (inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G))).subgroupOf H =
      inSubgroup perfectResidual P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_left : H ⊓ _ ≤ H),
      inSubgroup_perfectResidual_map H.subtype H.subtype_injective]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [hsub]
  apply le_antisymm
  · refine Subgroup.map_mono ?_
    exact map_perfectResidual_le P.subtype
  · have hWP : W ≤ P.map π := le_map_inf_centralizer hcH hc3 hcL
    have hWp : ⁅W, W⁆ = W := by
      have hp : Group.IsPerfect (perfectResidual H) :=
        (CFSG.perfect_residual_characterization (G := H)).2.2.1
      rw [Subgroup.isPerfect_iff] at hp
      rw [hW, ← Subgroup.map_commutator, hp]
    rw [map_inSubgroup_perfectResidual]
    exact le_inSubgroup_perfectResidual hWp hWP

theorem pCoreOf_le_of_map_eq {H K : Subgroup G} (hKH : K ≤ H)
    {W : Subgroup (H ⧸ CFSG.pCore 2 H)} [hWn : W.Normal]
    (hKW : (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) = W) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  set N := (O.subgroupOf H).map π with hN
  have hN2 : IsPGroup 2 N :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_subtype (K := H)).map π
  have hNW : N ≤ W := by
    rw [← hKW]
    exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hOK (Subgroup.mem_subgroupOf.mp hx))
  have hWN : W ≤ Subgroup.normalizer (N : Set _) := by
    rw [← hKW]
    rintro _ ⟨k, hk, rfl⟩
    have hkN : (k : G) ∈ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (Subgroup.mem_subgroupOf.mp hk)
    have hkS : k ∈ Subgroup.normalizer ((O.subgroupOf H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hkN _
    exact Subgroup.le_normalizer_map π ⟨k, hkS, rfl⟩
  have hNO : N ≤ CFSG.Open.pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNW hWN hN2
  have hOW : CFSG.Open.pCoreOf 2 W ≤ CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) := by
    refine le_sSup ⟨?_, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W⟩
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normalizer_eq_top (H := W)).ge.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  rw [pCore_quotient_pCore_eq_bot] at hOW
  intro x hx
  have hxH : x ∈ H := hKH (hOK hx)
  have h1 : π ⟨x, hxH⟩ = 1 := by
    have : π ⟨x, hxH⟩ ∈ N := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    exact Subgroup.mem_bot.mp (hOW (hNO this))
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
  exact h1

theorem not_mem_pCoreOf_of_inducesOuterTheta {H K Y : Subgroup G} {s : G} (hsH : s ∈ H)
    (hKY : K ≤ Y) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hKimg : (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)))
    (hKO : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 H)
    (hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H)) :
    s ∉ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hsO
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  have hsY : s ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hsO
  have hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ R := by
    intro k hk
    have h1 : k * s⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (hKY hk)) _).mp
        (Subgroup.inv_mem _ hsO)
    have h2 : s * k * s⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
      have := Subgroup.mul_mem _ hsO h1
      simpa only [mul_assoc] using this
    have h3 : s * k * s⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYK hsY) k).mp hk) (K.inv_mem hk)
    have hle : CFSG.Open.pCoreOf 2 Y ⊓ K ≤ CFSG.Open.pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (hKY hx), Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left)
    exact hKO (hle ⟨h2, h3⟩)
  have hsc : ∀ w ∈ (perfectResidual H).map π, π ⟨s, hsH⟩ * w = w * π ⟨s, hsH⟩ := by
    intro w hw
    rw [← hKimg] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    have h1 := (hmemR (⟨s, hsH⟩ * k * ⟨s, hsH⟩⁻¹ * k⁻¹)).mpr
      (hsK k (Subgroup.mem_subgroupOf.mp hk))
    simp only [map_mul, map_inv] at h1
    calc π ⟨s, hsH⟩ * π k
        = π ⟨s, hsH⟩ * π k * (π ⟨s, hsH⟩)⁻¹ * (π k)⁻¹ * (π k * π ⟨s, hsH⟩) := by group
      _ = π k * π ⟨s, hsH⟩ := by rw [h1, one_mul]
  have hRL : R ⊓ L ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx), Subgroup.le_normalizer hx⟩)
      (hR2.to_le inf_le_left)
  refine not_inducesOuterTheta_of_forall_mem ?_ hout
  intro l hl
  obtain ⟨l', hl', rfl⟩ := hl
  have hc := hsc (π l') ⟨l', hl', rfl⟩
  have h2 : π (⟨s, hsH⟩ * l' * ⟨s, hsH⟩⁻¹ * l'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  refine hRL ⟨(hmemR _).mp h2, ?_⟩
  have hlL : (l' : G) ∈ L := ⟨l', hl', rfl⟩
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H hsH
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN _).mp hlL) (L.inv_mem hlL)

theorem inducesInnerMod_of_mem {H K K' : Subgroup G} {X : Subgroup (H ⧸ CFSG.pCore 2 H)}
    {U V : Subgroup X} (hsup : U ⊔ V = ⊤) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hK'H : K' ≤ H)
    (hK'img : (K'.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) = V.map X.subtype)
    (hKK' : K = K' ⊔ CFSG.Open.pCoreOf 2 K)
    (hK'O : CFSG.Open.pCoreOf 2 K' ≤ CFSG.Open.pCoreOf 2 K) {a : G} (haH : a ∈ H)
    (haX : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨a, haH⟩ ∈ X)
    (haK' : a ∈ Subgroup.normalizer (K' : Set G)) (haK : a ∈ Subgroup.normalizer (K : Set G)) :
    InducesInnerMod a K (CFSG.Open.pCoreOf 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set O := CFSG.Open.pCoreOf 2 K with hOdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  have hK'K : K' ≤ K := hKK' ▸ le_sup_left
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  refine ⟨haK, ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hsup hUV ⟨π ⟨a, haH⟩, haX⟩
  have hvK' : ((v : X) : H ⧸ CFSG.pCore 2 H) ∈ (K'.subgroupOf H).map π := by
    rw [hK'img]
    exact ⟨v, hv, rfl⟩
  obtain ⟨k', hk', hk'v⟩ := hvK'
  have hkK' : (k' : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk'
  refine ⟨k', hK'K hkK', ?_⟩
  have hRK' : R ⊓ K' ≤ CFSG.Open.pCoreOf 2 K' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hK'H hx), Subgroup.le_normalizer hx⟩)
      (hR2.to_le inf_le_left)
  have hkey : ∀ y ∈ K', a * y * a⁻¹ * ((k' : G) * y * (k' : G)⁻¹)⁻¹ ∈ O := by
    intro y hy
    have hyH : y ∈ H := hK'H hy
    have hy1 : a * y * a⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp haK' y).mp hy
    have hy2 : (k' : G) * y * (k' : G)⁻¹ ∈ K' :=
      K'.mul_mem (K'.mul_mem hkK' hy) (K'.inv_mem hkK')
    have hyV : π ⟨y, hyH⟩ ∈ V.map X.subtype := by
      rw [← hK'img]
      exact ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hyV
    have hX : (u * v) * w * (u * v)⁻¹ * (v * w * v⁻¹)⁻¹ = 1 := by
      have hc := hUV u hu (v * w * v⁻¹) (V.mul_mem (V.mul_mem hv hw) (V.inv_mem hv))
      calc (u * v) * w * (u * v)⁻¹ * (v * w * v⁻¹)⁻¹
          = (u * (v * w * v⁻¹)) * u⁻¹ * (v * w * v⁻¹)⁻¹ := by group
        _ = ((v * w * v⁻¹) * u) * u⁻¹ * (v * w * v⁻¹)⁻¹ := by rw [hc]
        _ = 1 := by group
    have hπa : π ⟨a, haH⟩ = X.subtype (u * v) := by
      rw [huv]
      rfl
    have h1 : π (⟨a, haH⟩ * ⟨y, hyH⟩ * ⟨a, haH⟩⁻¹ * (k' * ⟨y, hyH⟩ * k'⁻¹)⁻¹) = 1 := by
      calc π (⟨a, haH⟩ * ⟨y, hyH⟩ * ⟨a, haH⟩⁻¹ * (k' * ⟨y, hyH⟩ * k'⁻¹)⁻¹)
          = π ⟨a, haH⟩ * π ⟨y, hyH⟩ * (π ⟨a, haH⟩)⁻¹ * (π k' * π ⟨y, hyH⟩ * (π k')⁻¹)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = X.subtype (u * v) * X.subtype w * (X.subtype (u * v))⁻¹ *
              (X.subtype v * X.subtype w * (X.subtype v)⁻¹)⁻¹ := by
            rw [hπa, hk'v, ← hwy]
            rfl
        _ = X.subtype ((u * v) * w * (u * v)⁻¹ * (v * w * v⁻¹)⁻¹) := by
            simp only [map_mul, map_inv]
        _ = 1 := by rw [hX, map_one]
    have h2 := (hmemR _).mp h1
    have h3 : a * y * a⁻¹ * ((k' : G) * y * (k' : G)⁻¹)⁻¹ ∈ K' :=
      K'.mul_mem hy1 (K'.inv_mem hy2)
    exact hK'O (hRK' ⟨by simpa using h2, h3⟩)
  intro y hy
  have hy' : y ∈ ((K' : Set G) * (O : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K' O (hK'K.trans hKO), ← hKK']
    exact hy
  obtain ⟨l, hl, q, hq, rfl⟩ := hy'
  have haO : a ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K haK
  have hβ : a * q * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp haO q).mp hq
  have hγ : (k' : G) * q⁻¹ * (k' : G)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hKO (hK'K hkK')) q⁻¹).mp (O.inv_mem hq)
  have hα : a * l * a⁻¹ ∈ K := hK'K ((Subgroup.mem_normalizer_iff.mp haK' l).mp hl)
  have hαβγ : (a * l * a⁻¹) * ((a * q * a⁻¹) * ((k' : G) * q⁻¹ * (k' : G)⁻¹)) *
      (a * l * a⁻¹)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hKO hα) _).mp (O.mul_mem hβ hγ)
  have heq : a * (l * q) * a⁻¹ * ((k' : G) * (l * q) * (k' : G)⁻¹)⁻¹ =
      ((a * l * a⁻¹) * ((a * q * a⁻¹) * ((k' : G) * q⁻¹ * (k' : G)⁻¹)) * (a * l * a⁻¹)⁻¹) *
        (a * l * a⁻¹ * ((k' : G) * l * (k' : G)⁻¹)⁻¹) := by
    group
  rw [heq]
  exact O.mul_mem hαβγ (hkey l hl)

theorem exists_mem_centralizer {A H : Subgroup G} (hA : IsE27 A) (hAH : A ≤ H)
    {X : Subgroup (H ⧸ CFSG.pCore 2 H)} {U V : Subgroup X} (hsup : U ⊔ V = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (eV : V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    [hVn : (V.map X.subtype).Normal]
    (hAX : ∀ a (ha : a ∈ H), a ∈ A → QuotientGroup.mk' (CFSG.pCore 2 H) ⟨a, ha⟩ ∈ X) :
    ∃ c ∈ A, c ≠ 1 ∧ ∃ hcH : c ∈ H, QuotientGroup.mk' (CFSG.pCore 2 H) ⟨c, hcH⟩ ∈
      Subgroup.centralizer ((V.map X.subtype : Subgroup _) : Set (H ⧸ CFSG.pCore 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  set f : A.subgroupOf H →* H ⧸ CFSG.pCore 2 H := π.comp (A.subgroupOf H).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
    have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
    have : ((a : H) : G) ∈ A ⊓ R := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
  set Ab := f.range with hAb
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, ← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hAexp : ∀ a : A.subgroupOf H, a ^ 3 = 1 := fun a =>
    Subtype.ext (by simpa using (isE27_subgroupOf hA hAH).1.2 (a : H) a.2)
  have hAb3 : IsPGroup 3 Ab := by
    rintro ⟨_, a, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one]; simp [← map_pow, hAexp a])⟩
  have hAbX : Ab ≤ X := by
    rintro _ ⟨a, rfl⟩
    exact hAX _ (a : H).2 (Subgroup.mem_subgroupOf.mp a.2)
  set Vb : Subgroup (H ⧸ CFSG.pCore 2 H) := V.map X.subtype with hVb
  set φ : Vb ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    (V.equivMapOfInjective X.subtype X.subtype_injective).symm.trans eV with hφ
  set ψ : Vb ⧸ Subgroup.center Vb ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    QuotientGroup.congr (Subgroup.center Vb)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 (GaloisField 2 2)) φ
      ((Subgroup.map_center_eq φ).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
          (GaloisField 2 2)).symm) with hψ
  have hVbp : commutator Vb = ⊤ := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
    have : Group.IsPerfect Vb :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hXLC : ∀ x ∈ X, ∃ l ∈ Vb, ∃ z ∈ Subgroup.centralizer (Vb : Set (H ⧸ CFSG.pCore 2 H)),
      x = l * z := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hsup hUV ⟨x, hx⟩
    refine ⟨v, ⟨v, hv, rfl⟩, u, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (hUV u hu w hw).symm
    · have h1 : x = (u : H ⧸ CFSG.pCore 2 H) * (v : H ⧸ CFSG.pCore 2 H) :=
        (congrArg Subtype.val huv).symm
      rw [h1]
      exact congrArg Subtype.val (hUV u hu v hv)
  have hge := KFacts.KS18.three_le_card_inf_centralizer ψ hk hVbp hXLC hAbX hAb3 hAb27
  have hne : Ab ⊓ Subgroup.centralizer (Vb : Set (H ⧸ CFSG.pCore 2 H)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hge
    omega
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨a, ha⟩ := (Subgroup.mem_inf.mp y.2).1
  refine ⟨((a : H) : G), Subgroup.mem_subgroupOf.mp a.2, ?_, (a : H).2, ?_⟩
  · intro h1
    apply hy1
    apply Subtype.ext
    rw [← ha, Subgroup.coe_one]
    have : a = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, map_one]
  · have h2 : π ⟨((a : H) : G), (a : H).2⟩ = f a := rfl
    rw [h2, ha]
    exact (Subgroup.mem_inf.mp y.2).2

theorem exists_mem_thetaComponentsAt_of_used (h4443 : Sec4.Item4_44_3SLUsed) {A M H : Subgroup G}
    (h : Sec18Std G A M) (hH : H ∈ scriptH A M)
    {X : Subgroup (H ⧸ CFSG.pCore 2 H)} {U V : Subgroup X} (hsup : U ⊔ V = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (eV : V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hLbV : (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) = V.map X.subtype)
    (hAX : ∀ a (ha : a ∈ H), a ∈ A → QuotientGroup.mk' (CFSG.pCore 2 H) ⟨a, ha⟩ ∈ X)
    {s : G} (hsH : s ∈ H) (hsS : s ∈ CFSG.Open.pCoreOf 2 (H ⊓ M))
    (hsA : s ∈ Subgroup.centralizer (A : Set G))
    (hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H))
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hcH : c ∈ H)
    (hcV : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨c, hcH⟩ ∈
      Subgroup.centralizer ((V.map X.subtype : Subgroup _) : Set (H ⧸ CFSG.pCore 2 H))) :
    ∃ K ∈ thetaComponentsAt 3 c,
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
      (∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)) ∧
      inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) ≤ K ∧
      inSubgroup perfectResidual H ≤
        inSubgroup perfectResidual (H ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
          CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAM := sec18Std_le h
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb := (perfectResidual H).map π with hLbdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hsC : s ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsA c hcA).symm
  have hCtop : C ≠ ⊤ := centralizer_ne_top h hc1
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  obtain ⟨eL⟩ := quotient_mulEquiv_map hLH hLO
  set Lc := inSubgroup perfectResidual (H ⊓ C) with hLcdef
  have hLcHC : Lc ≤ H ⊓ C := Subgroup.map_subtype_le _
  have hLcH : Lc ≤ H := hLcHC.trans inf_le_left
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hLcN : H ⊓ C ≤ Subgroup.normalizer (Lc : Set G) :=
    le_normalizer_inSubgroup_perfectResidual _
  have hcL : π ⟨c, hcH⟩ ∈ Subgroup.centralizer (Lb : Set (H ⧸ CFSG.pCore 2 H)) := by
    rw [hLbV]
    exact hcV
  have hLcimg : (Lc.subgroupOf H).map π = Lb := map_perfectResidual_inf_centralizer hcH hc3 hcL
  have hLcO : CFSG.Open.pCoreOf 2 Lc ≤ CFSG.Open.pCoreOf 2 H := pCoreOf_le_of_map_eq hLcH hLcimg
  obtain ⟨eLc⟩ := quotient_mulEquiv_map hLcH hLcO
  have hLc_q : CFSG.IsQuasisimple (Lc ⧸ CFSG.pCore 2 Lc) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (eL.trans ((MulEquiv.subgroupCongr (hLimg.trans hLcimg.symm)).trans eLc.symm))
      (isQuasisimple_of_mem_oTwoComponentsIn hH₀.2.1)
  have eLcSL : Lc ⧸ CFSG.pCore 2 Lc ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    eLc.trans ((MulEquiv.subgroupCongr (hLcimg.trans hLbV)).trans
      ((V.equivMapOfInjective X.subtype X.subtype_injective).symm.trans eV))
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ C with hTdef
  have hTHM : T ≤ H ⊓ M := inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTC : T ≤ C := inf_le_right
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hsT : s ∈ T := ⟨hsS, hsC⟩
  have hNT : ∀ x, x ∈ H → x ∈ M → x ∈ C → x ∈ Subgroup.normalizer (T : Set G) :=
    fun x hxH hxM hxC => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hxH, hxM⟩,
        Subgroup.le_normalizer hxC⟩
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha => hNT a (hAH ha) (hAM ha) (hAC ha)
  have hALc : A ≤ Subgroup.normalizer (Lc : Set G) := fun a ha => hLcN ⟨hAH ha, hAC ha⟩
  have hTLc : T ≤ Subgroup.normalizer (Lc : Set G) := fun t ht => hLcN ⟨hTH ht, hTC ht⟩
  set Y := Lc ⊔ A ⊔ T with hYdef
  have hYHC : Y ≤ H ⊓ C :=
    sup_le (sup_le hLcHC (le_inf hAH hAC)) (le_inf hTH hTC)
  have hYC : Y ≤ C := hYHC.trans inf_le_right
  have hYT : Y ⊓ M ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    hNT x (hYHC hx.1).1 hx.2 (hYHC hx.1).2
  have hYLc : Y ≤ Subgroup.normalizer (Lc : Set G) := hYHC.trans hLcN
  have hTO : ¬ T ≤ CFSG.Open.pCoreOf 2 Y := fun hle =>
    not_mem_pCoreOf_of_inducesOuterTheta hsH (le_sup_left.trans le_sup_left) hYLc hLcimg hLcO
      hout (hle hsT)
  obtain ⟨hY, hYres⟩ :=
    sup_mem_scriptH_of_le h hH hLcH hTH hLcp hLc_q hT2 hTM hALc hTLc hAT hYT hTO
  obtain ⟨K, hK, hKL⟩ :=
    Rem187Bypass.exists_mem_oTwoComponentsIn_of_item4443SLUsed h4443 h hY hYC hCtop
      (by rw [hYres]; exact ⟨eLcSL⟩)
  rw [hYres] at hKL
  have hLcK : Lc ≤ K := hKL ▸ le_sup_left
  have hKO : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  obtain ⟨⟨eK⟩, hLcOK⟩ := quotient_mulEquiv_of_le_sup (R := CFSG.Open.pCoreOf 2 K) hLcK
    (hKL ▸ le_rfl) (hLcK.trans hKO) hKO (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hLLc : L ≤ Lc ⊔ CFSG.Open.pCoreOf 2 H := by
    rintro _ ⟨l, hl, rfl⟩
    have hlb : π l ∈ (Lc.subgroupOf H).map π := by
      rw [hLcimg]
      exact ⟨l, hl, rfl⟩
    obtain ⟨y, hy, hyl⟩ := hlb
    have h1 : π (y⁻¹ * l) = 1 := by rw [map_mul, map_inv, hyl, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    have heq : (l : G) = (y : G) * ((y⁻¹ * l : H) : G) := by simp
    change (l : G) ∈ Lc ⊔ CFSG.Open.pCoreOf 2 H
    rw [heq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) h1
  refine ⟨K, ?_, ⟨eK.symm.trans eLcSL⟩, fun a ha => ?_, hLcK, hLLc⟩
  · rw [thetaComponentsAt_eq_thetaComponentsIn]
    exact mem_thetaComponentsIn_of_mem_oTwoComponentsIn hK
  · exact inducesInnerMod_of_mem hsup hUV hLcH (hLcimg.trans hLbV) hKL hLcOK (hAH ha)
      (hAX a (hAH ha) ha) (hALc ha) (mem_normalizer_of_eq_sup hK hKL (hAC ha) (hALc ha))

end Claim184LcProof

theorem claim184LcLe_of_used
    (h1812 : Item181_2) (h4443 : Sec4.Item4_44_3SLUsed) : Claim184LcLe := by
  intro G _ _ A M h H hH hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨s, ⟨hsS, hsA, hgf, hsH, X, hXn, hX, hXt, -⟩, -, -⟩ := h1812 G A M h H hH
  have hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H) :=
    hgf.inducesOuterTheta _ (by decide)
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb : Subgroup (H ⧸ Q) := (perfectResidual H).map π with hLb
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ X) := by
    have h1 := ht2.map (QuotientGroup.mk' X)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' X) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self X), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ X) := by
    have := hq2.isNilpotent
    infer_instance
  have hLbeq : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆ → Lb = ⁅X, X⁆ := fun hp => by
    rw [hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
    exact perfectResidual_eq_commutator hqs hp
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective Q)
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  obtain ⟨eL⟩ := Claim184LcProof.quotient_mulEquiv_map hLH hLO
  have hLbcard : Nat.card Lb = 60480 := by
    rw [← hLimg, ← Nat.card_congr eL.toEquiv, Nat.card_congr hSL.some.toEquiv,
      KFacts.KS14.card_SL_three_four]
  have hAX : ∀ a (ha : a ∈ H), a ∈ A → π ⟨a, ha⟩ ∈ X := by
    intro a ha haA
    refine mem_of_isPGroup_quotient hq2 (k := 1) ?_
    rw [pow_one, ← map_pow]
    have : (⟨a, ha⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hA.1.2 a haA)
    rw [this, map_one]
  rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
  ·
    exfalso
    obtain ⟨e⟩ := he
    have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
    set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
    have hcomm := KFacts.KS18.commutator_eq_range e'
    have hle : Lb ≤ (KFacts.KS18.inrY e').range := by
      rw [← hcomm, hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
      exact KFacts.KS18.perfectResidual_le_commutator hXt
    have hcard := Subgroup.card_le_of_le hle
    rw [hLbcard, ← Nat.card_congr (MonoidHom.ofInjective
      (KFacts.KS18.inrY_injective e')).toEquiv, KFacts.L34.card_projectiveSL hk] at hcard
    norm_num at hcard
  ·
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
    have hXX : ⁅X, X⁆ = V.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, hcomm]
    have hVp : Group.IsPerfect V := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVmp : ⁅V.map X.subtype, V.map X.subtype⁆ = V.map X.subtype := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
        Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLbV : Lb = V.map X.subtype := by
      rw [hLbeq (by rw [hXX, hVmp]), hXX]
    have hVn : (V.map X.subtype).Normal := hLbV ▸ hLbn
    obtain ⟨c, hcA, hc1, hcH, hcV⟩ :=
      Claim184LcProof.exists_mem_centralizer hA hAH hsup hUV eV hAX
    exact ⟨c, hcA, hc1, Claim184LcProof.exists_mem_thetaComponentsAt_of_used h4443 h hH hsup hUV eV
      hLbV hAX hsH hsS hsA hout hcA hc1 hcH hcV⟩

theorem claim184LcLe_of
    (h1812 : Item181_2) (h4443 : Sec4.Item4_44_3SL) : Claim184LcLe :=
  claim184LcLe_of_used h1812 (Sec4.item4_44_3SLUsed_of_item4_44_3SL h4443)

end CFSG.RankThree.PartTwo.Sec18
