module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AConjComp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNON
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.HardMathSupport.Solomon.Coordinator.T112TTONLift
import CFSG.LargeExtraspecial.S8CorC
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Cover
public import CFSG.RankThree.PartTwo.Census.Sporadic.FourGroupCert
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148
open Equiv

@[expose] def a6V1 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6V2 : alternatingGroup (Fin 6) :=
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem exists_twoLocal_e9_of_tripleCover_A6 {X : Type} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    ∃ T E : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ E ≤ Subgroup.normalizer (T : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, ⟨φ⟩⟩ := hX
  set σ := Sec19.Item19Res4Proof.threeCycleSix with hσ
  set V : Subgroup (alternatingGroup (Fin 6)) := Subgroup.closure {a6V1, a6V2} with hV
  have h1sq : a6V1 ^ 2 = 1 := Subtype.ext (by decide)
  have h2sq : a6V2 ^ 2 = 1 := Subtype.ext (by decide)
  have h12 : a6V1 * a6V2 = a6V2 * a6V1 := Subtype.ext (by decide)
  have hV2 : IsPGroup 2 V := CFSG.RankThree.PartTwo.Census.FourGroup.isPGroup_closure_pair
    h1sq h2sq h12
  have hV1 : V ≠ ⊥ := by
    intro h
    have hmem : a6V1 ∈ V := Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    revert this
    decide
  have hσV : σ ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 6))) := by
    refine CFSG.RankThree.PartTwo.Census.FourGroup.mem_normalizer_closure_of_pow_three
      Sec19.Item19Res4Proof.threeCycleSix_pow_three ?_
    rintro x (rfl | hx)
    · have : σ * a6V1 * σ⁻¹ = a6V2 := Subtype.ext (by decide)
      rw [this]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [Set.mem_singleton_iff.mp hx]
      have : σ * a6V2 * σ⁻¹ = a6V1 * a6V2 := Subtype.ext (by decide)
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  set π : X →* alternatingGroup (Fin 6) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
  have hπs : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    simp only [hπ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨T, hT, hT2, hTN⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_two_group_lift π hπs
    hker hZ hV1 hV2 (Subgroup.zpowers_le.mpr hσV)
  set E : Subgroup X := (Subgroup.zpowers σ).comap π with hE
  have hcardX : Nat.card X = 1080 := Sec19.Item19Res4Proof.card_eq_of_isTripleA6 ⟨hZ, ⟨φ⟩⟩
  have hσ3 : Nat.card (Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime Sec19.Item19Res4Proof.threeCycleSix_pow_three
      Sec19.Item19Res4Proof.threeCycleSix_ne_one]
  have hE9 : Nat.card E = 9 := by
    have h1 := Subgroup.card_mul_index E
    have h2 := Subgroup.card_mul_index (Subgroup.zpowers σ)
    have h3 : E.index = (Subgroup.zpowers σ).index := Subgroup.index_comap_of_surjective _ hπs
    rw [h3, hcardX] at h1
    rw [hσ3, Sec19.Item19Res4Proof.card_alternatingGroup_six'] at h2
    have hidx : (Subgroup.zpowers σ).index = 120 := by omega
    rw [hidx] at h1
    omega
  have hE3 : ∀ g ∈ E, g ^ 3 = 1 := by
    intro g hg
    apply Sec19.Item19Res4Proof.pow_three_eq_one_of_isTripleA6 ⟨hZ, ⟨φ⟩⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hg)
    apply φ.injective
    rw [map_pow, map_one]
    change (π g) ^ 3 = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      Sec19.Item19Res4Proof.threeCycleSix_pow_three, one_zpow]
  have hEc : IsMulCommutative ↥E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num)
  exact ⟨T, E, hT, hT2, ⟨hEc, hE3⟩, hE9, hTN⟩

theorem quasisimple_commutator_of_isTripleCover_A6 {X : Type} [Group X] [Finite X]
    (h : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    IsQuasisimple ↥(commutator X) ∧ commutator X ⊔ Subgroup.center X = ⊤ ∧
      ∃ u ∈ commutator X, u ^ 3 = 1 ∧
        u ∉ Subgroup.centralizer ((commutator X : Subgroup X) : Set X) := by
  obtain ⟨hZ3, ⟨φ⟩⟩ := h
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hQs : IsSimpleGroup (X ⧸ Subgroup.center X) := MulEquiv.isSimpleGroup φ
  have hsup := CFSG.LargeExtraspecial.S8.commutator_sup_center_eq_top hQs
  have hperf :=
    CFSG.EvenSporadicStandard.Induction.Balance.isPerfect_commutator_of_sup_center_eq_top hsup
  set K := commutator X with hK
  set f : ↥K →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp K.subtype with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    have hx : x ∈ (K ⊔ Subgroup.center X : Subgroup X) := by rw [hsup]; exact Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
    obtain ⟨k, hk, z, hz, rfl⟩ := hx
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using Subgroup.inv_mem _ hz
  set S : Subgroup ↥K := (Subgroup.center X).subgroupOf K with hS
  have hker : f.ker = S := by
    ext k
    simp only [hf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hS, Subgroup.mem_subgroupOf]
  haveI : S.Normal := by rw [← hker]; infer_instance
  have hSZ : S ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hk) g)
  let e : ↥K ⧸ S ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)).trans φ
  have hSs : IsSimpleGroup (↥K ⧸ S) := MulEquiv.isSimpleGroup e
  have hnc : ∃ a b : ↥K ⧸ S, a * b ≠ b * a := by
    refine ⟨e.symm ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩,
      e.symm ⟨swap 1 2 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩, fun h0 => ?_⟩
    have h1 := congrArg (fun z => ((e z : alternatingGroup (Fin 6)) : Perm (Fin 6))) h0
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
    revert h1
    decide
  have hq : IsQuasisimple ↥K :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient S hSZ hperf hSs hnc
  refine ⟨hq, hsup, ?_⟩
  obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 ⟨hZ3, ⟨φ⟩⟩
  have hx : x ∈ (K ⊔ Subgroup.center X : Subgroup X) := by rw [hsup]; exact Subgroup.mem_top x
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
  obtain ⟨k, hk, z, hz, rfl⟩ := hx
  have hz3 : z ^ 3 = 1 := Sec19.Item19Res4Proof.pow_three_eq_one_of_mem_center ⟨hZ3, ⟨φ⟩⟩ hz
  have hkz : Commute k z := (Subgroup.mem_center_iff.mp hz) k
  refine ⟨k, hk, ?_, fun hkC => hxZ ?_⟩
  · have h1 : (k * z) ^ 3 = k ^ 3 * z ^ 3 := hkz.mul_pow 3
    rw [hx3, hz3, mul_one] at h1
    exact h1.symm
  · rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (K ⊔ Subgroup.center X : Subgroup X) := by rw [hsup]; exact Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨k', hk', z', hz', rfl⟩ := hg
    have h1 : k' * k = k * k' := Subgroup.mem_centralizer_iff.mp hkC k' hk'
    have hz'c : ∀ g : X, g * z' = z' * g := Subgroup.mem_center_iff.mp hz'
    have hzc : ∀ g : X, g * z = z * g := Subgroup.mem_center_iff.mp hz
    calc k' * z' * (k * z) = k' * (z' * k) * z := by group
      _ = k' * (k * z') * z := by rw [← hz'c k]
      _ = (k' * k) * (z' * z) := by group
      _ = (k * k') * (z * z') := by rw [h1, hzc z']
      _ = k * (k' * z) * z' := by group
      _ = k * (z * k') * z' := by rw [hzc k']
      _ = k * z * (k' * z') := by group

variable {G : Type} [Group G] [Finite G]

theorem center_eq_of_tripleCover_A6148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJ : IsComponent J) (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (x : ↥(Y ⊔ A) ⧸ ker148 A Y) (hne : J.map (MulAut.conj x).toMonoidHom ≠ J) :
    (J.map (MulAut.conj x).toMonoidHom) ⊓
        Subgroup.centralizer ((J.map (MulAut.conj x).toMonoidHom : Subgroup _) :
          Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := J.map (MulAut.conj x).toMonoidHom with hD
  have hDc : IsComponent D := Res2LBal.isComponent_conj hJ x
  have hDC : D ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun y hy =>
    Res2LBal.mem_centralizer_of_mem_of_ne hJ hDc (fun h' => hne h'.symm) hy
  have hJC : J ≤ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun y hy =>
    Res2LBal.mem_centralizer_of_mem_of_ne hDc hJ hne hy
  have hZJ : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
    rw [← hJA6.1, ← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hZDeq : D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      (J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))).map
        (MulAut.conj x).toMonoidHom := by
    rw [hD, Subgroup.map_inf _ _ _ hinj]
    congr 1
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, SetLike.mem_coe]
    constructor
    · intro hy
      refine ⟨x⁻¹ * y * x, fun j hj => ?_, by group⟩
      have := hy (x * j * x⁻¹) ⟨j, hj, rfl⟩
      calc j * (x⁻¹ * y * x) = x⁻¹ * ((x * j * x⁻¹) * y) * x := by group
        _ = x⁻¹ * (y * (x * j * x⁻¹)) * x := by rw [this]
        _ = x⁻¹ * y * x * j := by group
    · rintro ⟨w, hw, rfl⟩ z ⟨j, hj, rfl⟩
      calc x * j * x⁻¹ * (x * w * x⁻¹) = x * (j * w) * x⁻¹ := by group
        _ = x * (w * j) * x⁻¹ := by rw [hw j hj]
        _ = x * w * x⁻¹ * (x * j * x⁻¹) := by group
  have hZD : Nat.card ↥(D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
    rw [hZDeq, Subgroup.card_map_of_injective hinj, hZJ]
  by_contra hZne
  have hZint : (J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
      (D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = ⊥ := by
    have hdvd : Nat.card ↥((J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
        (D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))) ∣ 3 :=
      hZJ ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hZne
      have e1 := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        (J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
          (D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ≤
            J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) (by rw [hZJ, h3])
      have e2 := Subgroup.eq_of_le_of_card_ge (inf_le_right :
        (J ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
          (D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ≤
            D ⊓ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) (by rw [hZD, h3])
      rw [← e2, e1]
  have hJD : J ⊓ D = ⊥ := by
    rw [eq_bot_iff, ← hZint]
    exact fun y hy => ⟨⟨hy.1, hDC hy.2⟩, ⟨hy.2, hJC hy.1⟩⟩
  obtain ⟨T, E, hT, hT2, hE, hE9, hET⟩ := exists_twoLocal_e9_of_tripleCover_A6 hJA6
  have hinjJ : Function.Injective J.subtype := J.subtype_injective
  set E₁ := E.map J.subtype with hE₁
  have hE₁J : E₁ ≤ J := Subgroup.map_subtype_le E
  set E₂ := E₁.map (MulAut.conj x).toMonoidHom with hE₂
  have hE₂D : E₂ ≤ D := Subgroup.map_mono hE₁J
  have hint : E₁ ⊓ E₂ = ⊥ := le_bot_iff.mp ((inf_le_inf hE₁J hE₂D).trans hJD.le)
  exact false_of_commuting_twoLocal148 h ((Subgroup.map_eq_bot_iff_of_injective T hinjJ).not.mpr hT)
    (hT2.map _) (Subgroup.map_subtype_le T) hE₁J
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
    (CFSG.SectionRank.isElemAbelian_map hE _) (hE₂D.trans hDC)
    (CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE _) _) hint
    (by rw [hE₂, Subgroup.card_map_of_injective hinj, hE₁,
      Subgroup.card_map_of_injective hinjJ, hE9])

theorem false_of_two_commuting_A6148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J K₁ K₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (hK₁C : K₁ ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hK₂C : K₂ ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hK₁₂ : K₂ ≤ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {u₁ u₂ : ↥(Y ⊔ A) ⧸ ker148 A Y} (hu₁ : u₁ ∈ K₁) (hu₂ : u₂ ∈ K₂)
    (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1)
    (hu₁Z : u₁ ∉ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hu₂Z : u₂ ∉ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsymm : ∀ {U V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)},
      U ≤ Subgroup.centralizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      V ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun hUV v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hUV hu) v hv).symm
  have hJK₁ := hsymm hK₁C
  have hJK₂ := hsymm hK₂C
  have hK₁K₂ := hsymm hK₁₂
  have hu₁J := hK₁C hu₁
  have hu₂J := hK₂C hu₂
  have hu₂K₁ := hK₁₂ hu₂
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := Subgroup.mem_centralizer_iff.mp hu₂K₁ u₁ hu₁
  have hu₁1 : u₁ ≠ 1 := fun h1 => hu₁Z (h1 ▸ Subgroup.one_mem _)
  have hu₂u₁ : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hm
    apply hu₂Z
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.zpow_mem _ (hK₁K₂ hu₁) i
  set E₂ := Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ with hE₂
  have hUV : ∀ a ∈ Subgroup.zpowers u₁, ∀ b ∈ Subgroup.zpowers u₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute u₁ u₂ from hu₁₂).zpow_zpow k l).eq
  have hmem : ∀ x ∈ E₂, ∃ a ∈ Subgroup.zpowers u₁, ∃ b ∈ Subgroup.zpowers u₂, x = a * b := by
    intro x hx
    rw [hE₂, ← Ronan148J.commProdHom_range hUV] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨a, a.2, b, b.2, Ronan148J.commProdHom_apply hUV _⟩
  have hpow3 : ∀ {u : ↥(Y ⊔ A) ⧸ ker148 A Y}, u ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers u, a ^ 3 = 1 := by
    intro u hu a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  have hE₂el : CFSG.Open.IsElemAbelian 3 E₂ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, b, hb, hx⟩ := hmem x.1 x.2
      obtain ⟨a', ha', b', hb', hy⟩ := hmem y.1 y.2
      change (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * y = y * x
      rw [hx, hy]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
      obtain ⟨l', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
      have h12 : Commute u₁ u₂ := hu₁₂
      have c1 : Commute (u₁ ^ k * u₂ ^ l) (u₁ ^ k' * u₂ ^ l') :=
        ((Commute.zpow_zpow_self u₁ k k').mul_right (h12.zpow_zpow k l')).mul_left
          ((h12.symm.zpow_zpow l k').mul_right (Commute.zpow_zpow_self u₂ l l'))
      exact c1.eq
    · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
      rw [Commute.mul_pow (hUV a ha b hb) 3, hpow3 hu₁3 a ha, hpow3 hu₂3 b hb, one_mul]
  have hE₂9 : Nat.card E₂ = 9 :=
    Ronan148J.card_zpowers_sup_zpowers_eq_nine hu₁₂ hu₁3 hu₁1 hu₂3 hu₂u₁
  have hE₂C : E₂ ≤ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    sup_le (Subgroup.zpowers_le.mpr hu₁J) (Subgroup.zpowers_le.mpr hu₂J)
  obtain ⟨T, E, hT, hT2, hE, hE9, hET⟩ := exists_twoLocal_e9_of_tripleCover_A6 hJA6
  have hinjJ : Function.Injective J.subtype := J.subtype_injective
  set E₁ := E.map J.subtype with hE₁
  have hE₁J : E₁ ≤ J := Subgroup.map_subtype_le E
  have hint : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx₂
    have hxK₁ := hJK₁ (hE₁J hx₁)
    have hxK₂ := hJK₂ (hE₁J hx₁)
    have hbK₁ : b ∈ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      Subgroup.zpowers_le.mpr hu₂K₁ hb
    have haK₂ : a ∈ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      Subgroup.zpowers_le.mpr (hK₁K₂ hu₁) ha
    have haK₁ : a ∈ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      have := Subgroup.mul_mem _ hxK₁ (Subgroup.inv_mem _ hbK₁)
      rwa [mul_inv_cancel_right] at this
    have hbK₂ : b ∈ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haK₂) hxK₂
      rwa [inv_mul_cancel_left] at this
    have key : ∀ {u : ↥(Y ⊔ A) ⧸ ker148 A Y} {K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)},
        u ^ 3 = 1 → u ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ∀ w ∈ Subgroup.zpowers u, w ∈ Subgroup.centralizer (K : Set _) → w = 1 := by
      intro u K hu3 huZ w hw hwC
      by_contra hw1
      have hu1 : u ≠ 1 := fun h1 => huZ (h1 ▸ Subgroup.one_mem _)
      have hcard : Nat.card (Subgroup.zpowers u) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
      have heq := Ronan148J.zpowers_eq_of_card_three hcard hw hw1
      exact huZ ((Subgroup.zpowers_le.mpr hwC) (heq ▸ Subgroup.mem_zpowers u))
    rw [key hu₁3 hu₁Z a ha haK₁, key hu₂3 hu₂Z b hb hbK₂, one_mul]
    exact Subgroup.one_mem _
  exact false_of_commuting_twoLocal148 h ((Subgroup.map_eq_bot_iff_of_injective T hinjJ).not.mpr hT)
    (hT2.map _) (Subgroup.map_subtype_le T) hE₁J
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
    (CFSG.SectionRank.isElemAbelian_map hE _) hE₂C hE₂el hint
    (by rw [hE₁, Subgroup.card_map_of_injective hinjJ, hE9, hE₂9])

theorem false_of_three_components_A6148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J K₁ K₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJ : IsComponent J) (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (hK₁ : IsComponent K₁) (hK₂ : IsComponent K₂) (h₁ : K₁ ≠ J) (h₂ : K₂ ≠ J)
    (h₁₂ : K₁ ≠ K₂) {u₁ u₂ : ↥(Y ⊔ A) ⧸ ker148 A Y} (hu₁ : u₁ ∈ K₁) (hu₂ : u₂ ∈ K₂)
    (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1)
    (hu₁Z : u₁ ∉ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hu₂Z : u₂ ∉ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False :=
  false_of_two_commuting_A6148 h hJA6
    (fun _ hx => Res2LBal.mem_centralizer_of_mem_of_ne hJ hK₁ h₁.symm hx)
    (fun _ hx => Res2LBal.mem_centralizer_of_mem_of_ne hJ hK₂ h₂.symm hx)
    (fun _ hx => Res2LBal.mem_centralizer_of_mem_of_ne hK₁ hK₂ h₁₂ hx) hu₁ hu₂ hu₁3 hu₂3 hu₁Z hu₂Z

theorem map_conj_eq_or_of_tripleCover_A6148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hJ : IsComponent J) (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (x y : ↥(Y ⊔ A) ⧸ ker148 A Y) :
    J.map (MulAut.conj x).toMonoidHom = J ∨ J.map (MulAut.conj y).toMonoidHom = J ∨
      J.map (MulAut.conj x).toMonoidHom = J.map (MulAut.conj y).toMonoidHom := by
  by_contra hall
  push Not at hall
  obtain ⟨hx, hy, hxy⟩ := hall
  obtain ⟨u, hu3, huZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hJA6
  have hu3' : (u : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hu3
  have hnc : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w * (u : ↥(Y ⊔ A) ⧸ ker148 A Y) * w⁻¹ ∉ Subgroup.centralizer
        ((J.map (MulAut.conj w).toMonoidHom : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro w hw
    apply huZ
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hw (w * g * w⁻¹) ⟨g, g.2, rfl⟩
    simp only [Subgroup.coe_mul]
    have e1 : w * g * w⁻¹ * (w * u * w⁻¹) = w * (g * u) * w⁻¹ := by group
    have e2 : w * u * w⁻¹ * (w * g * w⁻¹) = w * (u * g) * w⁻¹ := by group
    rw [e1, e2] at this
    exact mul_left_cancel (mul_right_cancel this)
  exact false_of_three_components_A6148 h hJ hJA6 (Res2LBal.isComponent_conj hJ x)
    (Res2LBal.isComponent_conj hJ y) hx hy hxy (Res2LBal.conj_mem_map u.2 x)
    (Res2LBal.conj_mem_map u.2 y) (by rw [conj_pow, hu3', mul_one, mul_inv_cancel])
    (by rw [conj_pow, hu3', mul_one, mul_inv_cancel]) (hnc x) (hnc y)

theorem conj_not_mem_centralizer_map {Γ : Type*} [Group Γ] {K : Subgroup Γ} {u : Γ}
    (huZ : u ∉ Subgroup.centralizer (K : Set Γ)) (x : Γ) :
    x * u * x⁻¹ ∉ Subgroup.centralizer
      ((K.map (MulAut.conj x).toMonoidHom : Subgroup Γ) : Set Γ) := by
  intro hw
  apply huZ
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := Subgroup.mem_centralizer_iff.mp hw (x * g * x⁻¹) ⟨g, hg, rfl⟩
  have e1 : x * g * x⁻¹ * (x * u * x⁻¹) = x * (g * u) * x⁻¹ := by group
  have e2 : x * u * x⁻¹ * (x * g * x⁻¹) = x * (u * g) * x⁻¹ := by group
  rw [e1, e2] at this
  exact mul_left_cancel (mul_right_cancel this)

theorem map_conj_sup_eq_of_two_components_A6148 {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} [(ker148 A Y).Normal]
    {J Z : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hJ : IsComponent J)
    (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6))) (hZ : IsComponent Z) (hZJ : Z ≠ J)
    {u : ↥(Y ⊔ A) ⧸ ker148 A Y} (huZ : u ∈ Z) (hu3 : u ^ 3 = 1)
    (hunc : u ∉ Subgroup.centralizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (x : ↥(Y ⊔ A) ⧸ ker148 A Y) :
    (J ⊔ Z).map (MulAut.conj x).toMonoidHom = J ⊔ Z := by
  have hone : ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≠ J →
      ∀ w ∈ K, w ^ 3 = 1 → w ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        K = Z := by
    intro K hK hKJ w hw hw3 hwZ
    by_contra hKZ
    exact false_of_three_components_A6148 h hJ hJA6 hZ hK hZJ hKJ (Ne.symm hKZ) huZ hw hu3 hw3
      hunc hwZ
  obtain ⟨v, hv3, hvZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hJA6
  have hv3' : (v : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hv3
  have hvnc : (v : ↥(Y ⊔ A) ⧸ ker148 A Y) ∉
      Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro hc
    apply hvZ
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
  have hle : ∀ y : ↥(Y ⊔ A) ⧸ ker148 A Y,
      (J ⊔ Z).map (MulAut.conj y).toMonoidHom ≤ J ⊔ Z := by
    intro y
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · by_cases hJy : J.map (MulAut.conj y).toMonoidHom = J
      · rw [hJy]
        exact le_sup_left
      · rw [hone _ (Res2LBal.isComponent_conj hJ y) hJy _ (Res2LBal.conj_mem_map v.2 y)
          (by rw [conj_pow, hv3', mul_one, mul_inv_cancel]) (conj_not_mem_centralizer_map hvnc y)]
        exact le_sup_right
    · by_cases hZy : Z.map (MulAut.conj y).toMonoidHom = J
      · rw [hZy]
        exact le_sup_left
      · rw [hone _ (Res2LBal.isComponent_conj hZ y) hZy _ (Res2LBal.conj_mem_map huZ y)
          (by rw [conj_pow, hu3, mul_one, mul_inv_cancel]) (conj_not_mem_centralizer_map hunc y)]
        exact le_sup_right
  refine le_antisymm (hle x) ?_
  have h2 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) (hle x⁻¹)
  rwa [Res2LBal.map_conj_map_conj, mul_inv_cancel, Res2LBal.map_conj_one] at h2

theorem isComponent_of_le_centralizer_A6148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {J Z : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hJ : IsComponent J)
    (hJA6 : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6))) (hZq : IsQuasisimple ↥Z)
    (hZC : Z ≤ img148 A Y Y ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hCZ : img148 A Y Y ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
      Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    IsComponent Z := by
  set Y' := img148 A Y Y with hY'
  have hY'n : Y'.Normal := Item148Res5.img148_normal hAY
  set N := Y' ⊓ Subgroup.normalizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) with hN
  set C := Y' ⊓ Subgroup.centralizer (J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) with hC
  have hNn : (N.subgroupOf Y').Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g' : ↥(Y ⊔ A) ⧸ ker148 A Y, g' ∈ Y' → ∀ n ∈ N, g' * n * g'⁻¹ ∈ N := by
      intro g' hg' n hn
      refine Subgroup.mem_inf.mpr ⟨Y'.mul_mem (Y'.mul_mem hg' hn.1) (Y'.inv_mem hg'), ?_⟩
      have hnJ : J.map (MulAut.conj n).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
      have hnJ' : J.map (MulAut.conj n⁻¹).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hn.2)
      have hc : ∀ x y : ↥(Y ⊔ A) ⧸ ker148 A Y, J.map (MulAut.conj (x * y)).toMonoidHom =
          (J.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom :=
        fun x y => (Res2LBal.map_conj_map_conj J x y).symm
      have hc1 : J.map (MulAut.conj (g' * g'⁻¹)).toMonoidHom = J := by
        rw [mul_inv_cancel, Res2LBal.map_conj_one]
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      show J.map (MulAut.conj (g' * n * g'⁻¹)).toMonoidHom = J
      rw [mul_assoc, hc g' (n * g'⁻¹)]
      by_cases h1 : J.map (MulAut.conj g'⁻¹).toMonoidHom = J
      · rw [hc n g'⁻¹, h1, hnJ]
        have h4 := hc g' g'⁻¹
        rw [h1, hc1] at h4
        exact h4.symm
      · rcases map_conj_eq_or_of_tripleCover_A6148 h hJ hJA6 g'⁻¹ (n * g'⁻¹) with h2 | h2 | h2
        · exact absurd h2 h1
        · exfalso
          apply h1
          have h3 : J.map (MulAut.conj (n⁻¹ * (n * g'⁻¹))).toMonoidHom = J := by
            rw [hc n⁻¹ (n * g'⁻¹), h2, hnJ']
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at h3
        · rw [← h2, ← hc, hc1]
    intro y
    constructor
    · exact key g hg y
    · intro hy
      have := key g⁻¹ (Y'.inv_mem hg) _ hy
      have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [e] at this
      exact this
  have hCN : C ≤ N := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hCn : (C.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hgC := KFacts.KS14.normalizer_le_normalizer_centralizer J hg.2
    constructor
    · intro hy
      exact ⟨Y'.mul_mem (Y'.mul_mem hg.1 hy.1) (Y'.inv_mem hg.1),
        (Subgroup.mem_normalizer_iff.mp hgC y).mp hy.2⟩
    · intro hy
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hgC y).mpr hy.2⟩
      have := Y'.mul_mem (Y'.mul_mem (Y'.inv_mem hg.1) hy.1) hg.1
      simpa [mul_assoc] using this
  have hZn : (Z.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr hCZ
  have hY'sn : Y'.IsSubnormal := hY'n.isSubnormal
  have hNsn : N.IsSubnormal := Subgroup.IsSubnormal.trans inf_le_left hNn.isSubnormal hY'sn
  have hCsn : C.IsSubnormal := Subgroup.IsSubnormal.trans hCN hCn.isSubnormal hNsn
  exact ⟨hZq, Subgroup.IsSubnormal.trans hZC hZn.isSubnormal hCsn⟩

theorem mem_normalizer_zpowers_of_center148 {Γ : Type*} [Group Γ] {J : Subgroup Γ} {z x : Γ}
    (hz : J ⊓ Subgroup.centralizer (J : Set Γ) = Subgroup.zpowers z)
    (hx : J.map (MulAut.conj x).toMonoidHom = J ∨
      (J.map (MulAut.conj x).toMonoidHom) ⊓
          Subgroup.centralizer ((J.map (MulAut.conj x).toMonoidHom : Subgroup Γ) : Set Γ) =
        J ⊓ Subgroup.centralizer (J : Set Γ)) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set Γ) := by
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hZx : (J.map (MulAut.conj x).toMonoidHom) ⊓
      Subgroup.centralizer ((J.map (MulAut.conj x).toMonoidHom : Subgroup Γ) : Set Γ) =
        (J ⊓ Subgroup.centralizer (J : Set Γ)).map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ hinj]
    congr 1
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, SetLike.mem_coe]
    constructor
    · intro hy
      refine ⟨x⁻¹ * y * x, fun j hj => ?_, by group⟩
      have := hy (x * j * x⁻¹) ⟨j, hj, rfl⟩
      calc j * (x⁻¹ * y * x) = x⁻¹ * ((x * j * x⁻¹) * y) * x := by group
        _ = x⁻¹ * (y * (x * j * x⁻¹)) * x := by rw [this]
        _ = x⁻¹ * y * x * j := by group
    · rintro ⟨w, hw, rfl⟩ u ⟨j, hj, rfl⟩
      calc x * j * x⁻¹ * (x * w * x⁻¹) = x * (j * w) * x⁻¹ := by group
        _ = x * (w * j) * x⁻¹ := by rw [hw j hj]
        _ = x * w * x⁻¹ * (x * j * x⁻¹) := by group
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have key : (Subgroup.zpowers z).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers z := by
    rw [← hz, ← hZx]
    rcases hx with hJx | hZ
    · simp only [hJx]
    · exact hZ
  exact key

section Certificates


theorem center_eq_zpowers_of_mem148 {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {J : Subgroup G} (hJM : J ≤ Y ⊔ A) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hdJ : alpha148 A Y d hdA ∈ img148 A Y J)
    (hZ3 : Nat.card ↥(Subgroup.center ↥(img148 A Y J)) = 3) :
    img148 A Y J ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers (alpha148 A Y d hdA) := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hS.mem_partTwoF.1.2
  have hdC := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hdmem : alpha148 A Y d hdA ∈
      img148 A Y J ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine ⟨hdJ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hdC hy))
  have hcard : Nat.card ↥(img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
    rw [← hZ3, ← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (Ronan148J.zpowers_eq_of_card_three hcard hdmem
    (alpha148_ne_one hdA hd1 (hA3 d hdA))).symm

theorem img148_le_normalizer_zpowers_d_of_innerA6
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) {Yd : Subgroup G}
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hYdJ : Yd ≤ J) (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hη : letI := ker148_normal hY.2;
      Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)))
    (hJ6 : letI := ker148_normal hY.2;
      Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6))) (hdA : d ∈ A) :
    letI := ker148_normal hY.2
    img148 A Y Y ≤ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, -, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  obtain ⟨η⟩ := hη
  have hYd6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr η.symm hJ6
  obtain ⟨-, hdYB, -⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hYd6
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have hdJ : alpha148 A Y d hdA ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ (hYBYd hdYB), rfl⟩
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hYd6))).trans
      (Subgroup.card_dvd_of_le hYdJ)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  have hz := center_eq_zpowers_of_mem148 hS hJM hdA hd1 hdc hdJ hJ6.1
  intro y _
  refine mem_normalizer_zpowers_of_center148 hz ?_
  by_cases hne : (img148 A Y J).map (MulAut.conj y).toMonoidHom = img148 A Y J
  · exact Or.inl hne
  · exact Or.inr (center_eq_of_tripleCover_A6148 hS hJc hJ6 y hne)

theorem img148_le_normalizer_zpowers_d_of_innerON
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) {J Yd : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hYdJ : Yd ≤ J) (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (hJON : letI := ker148_normal hY.2;
      Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) (hdYd : d ∈ Yd) :
    letI := ker148_normal hY.2
    img148 A Y Y ≤ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  let := ker148_normal hY.2
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have hdJ : alpha148 A Y d hdA ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have h3J : 3 ∣ Nat.card J := by
    have h3 : 3 ∣ Nat.card ↥(img148 A Y J) := by
      have hord : orderOf (alpha148 A Y d hdA) = 3 :=
        orderOf_eq_prime (alpha148_pow_three hS.mem_partTwoF.1.2 hdA)
          (alpha148_ne_one hdA hd1 (hS.mem_partTwoF.1.2 d hdA))
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hdJ
    exact h3.trans (card_img148_dvd hJM)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  have hz := center_eq_zpowers_of_mem148 hS hJM hdA hd1 hdc hdJ hJON.1
  intro y _
  exact mem_normalizer_zpowers_of_center148 hz
    (Or.inl (map_conj_eq_of_tripleCover_ON148 hS hJc hJON y))

@[expose] def Step148HJNormalInnerONCent2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → d ∈ Yd →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        ((Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) Y))
              CFSG.Blueprint.NativeSporadic.ON ∨
            IsCentralProductA6Covers ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
            (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) ∨
          Case148Two A (lB A) Y)

theorem step148HJNormalInnerONCent_of_cent2
    (hR : Step148HJNormalInnerONCent2) : Ronan148J.Step148HJNormalInnerONCent := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ hdA
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, -, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hXY : img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y Y :=
    img148_mono (sSup_le fun _ hQ => hQ.2)
  refine ⟨hXY.trans (img148_le_normalizer_zpowers_d_of_innerON hS hY hdA hd1 hJ hYdJ hdc hJON
    hdYd), hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
