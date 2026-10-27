module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofGroup
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace KS11Lie4Proof

@[expose] noncomputable def g2LongSL2
    (K : Type) [Field K] :
    Subgroup (adjointGroup .G2 K) :=
  (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)).comap (adjointGroup .G2 K).subtype

@[expose] noncomputable def g2ShortSL2
    (K : Type) [Field K] :
    Subgroup (adjointGroup .G2 K) :=
  (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)).comap (adjointGroup .G2 K).subtype

@[expose] def G2ThreeConjSL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ z : adjointGroup .G2 K, z ^ 3 = 1 → z ≠ 1 →
      ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ g2ShortSL2 K ∨ g * z * g⁻¹ ∈ g2LongSL2 K

@[expose] def G2ThreeACent : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ z ∈ g2ShortSL2 K, z ^ 3 = 1 → z ≠ 1 →
      ∃ N : Subgroup (adjointGroup .G2 K),
        N ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ∧
        (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
          ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
            x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧
        ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1

@[expose] def G2ThreeBCent : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ z ∈ g2LongSL2 K, z ^ 3 = 1 → z ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
          x * y * x⁻¹ * y⁻¹ ∈ g2ShortSL2 K) ∧
      ∀ b ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        b ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) →
          b ^ (Nat.card K ^ 2 - 1) = 1

@[expose] def G2ShortNineCent :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ y ∈ g2ShortSL2 K, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
        ∀ w ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
          x * w * x⁻¹ * w⁻¹ ∈ g2LongSL2 K) ∧
      ∀ x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)),
        x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) → x ∈ g2LongSL2 K

@[expose] def G2ShortOut : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ β : MulAut (adjointGroup .G2 K), (∃ k : ℕ, β ^ 3 ^ k = 1) →
      (∀ x ∈ g2ShortSL2 K, β x = x) →
        β ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range

section Model

variable {K : Type} [Field K]

theorem isQuasisimple_sl2 [Finite K] (h4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (SL2 K) := by
  have hp := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have hs := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := K) h4
  refine ⟨hp, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL2 K ⧸ Subgroup.center (SL2 K)) := ⟨⟨h⟩⟩
  have : Group.IsPerfect (SL2 K ⧸ Subgroup.center (SL2 K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

theorem nonempty_mulEquiv_g2Q {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    Nonempty (SL2 K ≃* (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
      Subgroup (ModGL .G2 K))) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    obtain ⟨-, -, ⟨e, -⟩, -⟩ :=
      CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .G2 K hα
    exact ⟨e⟩
  · exact (odd_arbitrary_root_pair_SL2_p_components .G2 K h2 hα).2.1

@[expose] noncomputable def g2QEquiv (α : Fin Tag.G2.rank → ℤ) :
    ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)).comap (adjointGroup .G2 K).subtype :
      Subgroup (adjointGroup .G2 K)) ≃*
      (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :=
  Subgroup.subgroupOfEquivOfLe (sup_le (rootSubgroup_le_adjointGroup α)
    (rootSubgroup_le_adjointGroup (-α)))

theorem nonempty_mulEquiv_g2ShortSL2 : Nonempty (SL2 K ≃* g2ShortSL2 K) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2Q (K := K) isRoot_g2δ
  exact ⟨e.trans (g2QEquiv (K := K) g2δ).symm⟩

theorem nonempty_mulEquiv_g2LongSL2 : Nonempty (SL2 K ≃* g2LongSL2 K) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2Q (K := K) (isRoot_single .G2 g2l)
  exact ⟨e.trans (g2QEquiv (K := K) g2e0).symm⟩

theorem g2Short_commute_g2Long {s m : adjointGroup .G2 K} (hs : s ∈ g2ShortSL2 K)
    (hm : m ∈ g2LongSL2 K) : s * m = m * s := by
  have hs' : (s : ModGL .G2 K) ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := hs
  have hm' : (m : ModGL .G2 K) ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) := hm
  have h := (KS11Lie2Proof.g2_commute' hm' hs').eq
  exact Subtype.ext h.symm

theorem isQuasisimple_g2ShortSL2 [Finite K] (hK : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (g2ShortSL2 K) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (isQuasisimple_sl2 hK)

theorem isPerfect_g2LongSL2 [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect (g2LongSL2 K) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g2LongSL2 (K := K)
  have := (isQuasisimple_sl2 hK).1
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem card_g2LongSL2_eq : Nat.card (g2LongSL2 K) = Nat.card (g2ShortSL2 K) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_g2LongSL2 (K := K)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  exact (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr e₂.toEquiv)

end Model

section Transport

variable {Z C : Type} [Group Z] [Group C]

theorem mem_centralizer_map {e : Z ≃* C} {z x : Z} :
    e x ∈ Subgroup.centralizer ({e z} : Set C) ↔ x ∈ Subgroup.centralizer ({z} : Set Z) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul, e.injective.eq_iff]

end Transport

section Carrier

theorem exists_g2_model {Z : Type} [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 3 ∧ 4 ≤ Nat.card K ∧
      Nonempty (Z ≃* adjointGroup .G2 K) := by
  obtain ⟨X, _, ⟨q, hq, hp3, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  have hq3 : 3 ≤ q.card := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rwa [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
  have hq4 : 4 ≤ q.card := by
    rcases Nat.lt_or_ge q.card 4 with h | h
    · exfalso
      have h3 : q.card = 3 := by omega
      rw [TauCeti.PrimePower.card_def] at h3
      have h3' : q.p ∣ 3 := by
        rw [← h3]
        exact dvd_pow_self _ q.exponent_pos.ne'
      exact hp3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp h3')
    · exact h
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; exact hp3
  exact ⟨K, inferInstance, inferInstance, hK3, hK ▸ hq4,
    ⟨((e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans b.symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)⟩⟩

theorem g2_of_ss {Z : Type} [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) :
    ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) := by
  obtain ⟨X, _, ⟨q, hq, -, hf⟩, he⟩ := hZ
  exact ⟨X, inferInstance, ⟨q, hq, hf⟩, he⟩

theorem g2_order_three {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X))
    {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : z ^ 3 = 1 ∧ z ≠ 1 := by
  have hZ' := g2_of_ss hZ
  refine ⟨?_, KS11Lie3Proof.ne_one_of_isType424_g2 hZ' hJ hJT⟩
  have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (x := z ^ 3) (by rw [map_pow, hz3])
  rwa [KS11Lie3Proof.center_eq_bot_g2 Z hZ', Subgroup.mem_bot] at h1

end Carrier

section Data

variable {Z : Type} [Group Z] [Finite Z] {K : Type} [Field K] [Finite K]

theorem threeBAt_g2 (h2 : G2ThreeACent) (h3 : G2ThreeBCent) (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (e : Z ≃* adjointGroup .G2 K) {z : Z} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hmem : e z ∈ g2ShortSL2 K ∨ e z ∈ g2LongSL2 K) {J : Subgroup Z}
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    e z ∈ g2LongSL2 K ∧ ThreeBAt Z z ((g2ShortSL2 K).comap e.toMonoidHom) := by
  have hez3 : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (h.trans (map_one e).symm))
  rcases hmem with hzS | hzM
  ·
    exfalso
    obtain ⟨N, hNC, hcomm, hNq, x, hxN, hxc, hx1, hx3⟩ := h2 K hK3 hK4 (e z) hzS hez3 hez1
    have e' : (N.comap e.toMonoidHom : Subgroup Z) ≃* N :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
    refine false_of_threeA (N := N.comap e.toMonoidHom) (fun y hy => ?_) (fun a ha b hb => ?_)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hNq) ⟨e.symm x, ?_, ?_, ?_, ?_⟩ hJ hJT
    · exact mem_centralizer_map.mp (hNC hy)
    · have := hcomm _ (mem_centralizer_map.mpr ha) _ (mem_centralizer_map.mpr hb)
      change e (a * b * a⁻¹ * b⁻¹) ∈ N
      simpa [map_mul, map_inv] using this
    · change e (e.symm x) ∈ N
      rwa [MulEquiv.apply_symm_apply]
    · intro n hn
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hxc _ hn
    · intro h
      apply hx1
      rw [← MulEquiv.apply_symm_apply e x, h, map_one]
    · apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hx3, map_one]
  ·
    refine ⟨hzM, ?_, fun s hs => ?_, fun x hx y hy => ?_⟩
    · have e' : ((g2ShortSL2 K).comap e.toMonoidHom : Subgroup Z) ≃* g2ShortSL2 K :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm (isQuasisimple_g2ShortSL2 hK4)
    · rw [← mem_centralizer_map (e := e)]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (g2Short_commute_g2Long hs hzM)
    · have hx' := (mem_centralizer_map (e := e)).mpr hx
      have hy' := (mem_centralizer_map (e := e)).mpr hy
      have := (h3 K hK3 hK4 (e z) hzM hez3 hez1).1 _ hx' _ hy'
      change e (x * y * x⁻¹ * y⁻¹) ∈ g2ShortSL2 K
      simpa [map_mul, map_inv] using this

end Data

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace KS11Lie4Proof

section Provers

theorem exists_g2_threeB (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hB : G2ThreeBCent)
    {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X))
    {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 3 ∧ 4 ≤ Nat.card K ∧
      ∃ e : Z ≃* adjointGroup .G2 K, e z ∈ g2LongSL2 K ∧
        ThreeBAt Z z ((g2ShortSL2 K).comap e.toMonoidHom) := by
  obtain ⟨hz3', hz1⟩ := g2_order_three hZ hz3 hJ hJT
  obtain ⟨K, _, _, hK3, hK4, ⟨e⟩⟩ := exists_g2_model hZ
  have hez3 : e z ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := hC K hK3 hK4 (e z) hez3 hez1
  set e' : Z ≃* adjointGroup .G2 K := e.trans (MulAut.conj g) with he'
  have hmem : e' z ∈ g2ShortSL2 K ∨ e' z ∈ g2LongSL2 K := hg
  exact ⟨K, inferInstance, inferInstance, hK3, hK4, e',
    threeBAt_g2 hA hB hK3 hK4 e' hz3' hz1 hmem hJ hJT⟩

theorem thetaCentral119G2Ss_of (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hB : G2ThreeBCent) :
    ThetaCentral119G2Ss := by
  intro Z _ _ hZ z J hz3 hJ hJT
  obtain ⟨K, _, _, -, -, e, -, h⟩ := exists_g2_threeB hC hA hB hZ hz3 hJ hJT
  exact h.thetaCentral hJ

theorem centJ119G2Inn_of (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hB : G2ThreeBCent) :
    CentJ119G2Inn := by
  intro Z _ _ hZ z b J hz3 hb hbz hJ hJT hbJ
  obtain ⟨K, _, _, hK3, hK4, e, hez, h⟩ := exists_g2_threeB hC hA hB hZ hz3 hJ hJT
  have hcard : Nat.card ((g2ShortSL2 K).comap e.toMonoidHom) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))).toEquiv]
    obtain ⟨e₂⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
    rw [← Nat.card_congr e₂.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  refine h.inn (m := Nat.card K ^ 2 - 1) ⟨Nat.card K, by rw [hcard, mul_comm]⟩
    (fun x hx hxS => ?_) hJ hb hbz hbJ
  have hx' := (mem_centralizer_map (e := e)).mpr hx
  have hxS' : e x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨s', rfl⟩ := e.surjective s
    have := Subgroup.mem_centralizer_iff.mp hxS s' hs
    rw [← map_mul, ← map_mul, this]
  have := (hB K hK3 hK4 (e z) hez (by rw [← map_pow, (g2_order_three hZ hz3 hJ hJT).1, map_one])
    (fun h' => (g2_order_three hZ hz3 hJ hJT).2 (e.injective (h'.trans (map_one e).symm)))).2
    _ hx' hxS'
  exact e.injective (by rw [map_pow, this, map_one])

theorem centJ119G2Out_of (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hB : G2ThreeBCent)
    (hO : G2ShortOut) : CentJ119G2Out := by
  intro Z _ _ hZ z β J hz3 hβ hzβ hJ hJT hβJ
  obtain ⟨K, _, _, hK3, hK4, e, -, h⟩ := exists_g2_threeB hC hA hB hZ hz3 hJ hJT
  refine h.out (fun γ hγ hγS => ?_) hJ hβ hβJ
  obtain ⟨k, hk⟩ := hγ
  have hγ' : ∃ k : ℕ, MulAut.congr e γ ^ 3 ^ k = 1 := ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨g, hg⟩ := hO K hK3 hK4 (MulAut.congr e γ) hγ' fun x hx => by
    obtain ⟨x', rfl⟩ := e.surjective x
    change e (γ (e.symm (e x'))) = e x'
    rw [MulEquiv.symm_apply_apply, hγS x' hx]
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 := congrArg (fun φ : MulAut (adjointGroup .G2 K) => φ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem normCentJ1117G2Ss_of (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hB : G2ThreeBCent)
    (hN : G2ShortNineCent) : NormCentJ1117G2Ss := by
  intro Z _ _ hZ z J y g hz3 hJ hJT hyJ hyk hy3 _ hgy
  obtain ⟨K, _, _, hK3, hK4, e, -, h⟩ := exists_g2_threeB hC hA hB hZ hz3 hJ hJT
  have heM : ∀ x : Z, x ∈ (g2LongSL2 K).comap e.toMonoidHom ↔ e x ∈ g2LongSL2 K :=
    fun x => Iff.rfl
  refine h.normCent (M := (g2LongSL2 K).comap e.toMonoidHom) (fun s hs m hm => ?_) ?_ ?_ hJ hyJ
    hyk hy3 hgy
  · exact e.injective (by rw [map_mul, map_mul]; exact g2Short_commute_g2Long hs hm)
  · have e' : ((g2LongSL2 K).comap e.toMonoidHom : Subgroup Z) ≃* g2LongSL2 K :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
    have := isPerfect_g2LongSL2 (K := K) hK4
    exact Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  · intro y' hy' hy'k hy'3
    have hey'k : ∃ k : ℕ, e y' ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hy'k
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hey'3 : e y' ^ 3 ≠ 1 := fun h' => hy'3 (e.injective (by rw [map_pow, h', map_one]))
    obtain ⟨h1, h2⟩ := hN K hK3 hK4 (e y') hy' hey'k hey'3
    refine ⟨fun x hx w hw => ?_, fun x hx hxS => ?_⟩
    · have := h1 (e x) (mem_centralizer_map.mpr hx) (e w) (mem_centralizer_map.mpr hw)
      rw [heM]
      simpa [map_mul, map_inv] using this
    · rw [heM]
      refine h2 (e x) (mem_centralizer_map.mpr hx) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨s', rfl⟩ := e.surjective s
      have := Subgroup.mem_centralizer_iff.mp hxS s' hs
      rw [← map_mul, ← map_mul, this]

end Provers

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
