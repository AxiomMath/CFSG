module

public import CFSG.RankThree.LocalRank.PartTwoCollections
public import CFSG.RankThree.LocalRank.ThetaPlaneCentralLine
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.Open.RankThreeDefs
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G]

@[expose] def piOf (p : ℕ) : Set Nat.Primes := {q | (q : ℕ) = p}

@[expose] def piCompl (p : ℕ) : Set Nat.Primes := {q | (q : ℕ) ≠ p}

@[expose] def invariantPiSubgroups (H A : Subgroup G) (π : Set Nat.Primes) : Set (Subgroup G) :=
  {X | X ≤ H ∧ IsPiSubgroup π X ∧ A ≤ Subgroup.normalizer (X : Set G)}

@[expose] def maxInvariantPiSubgroups (H A : Subgroup G) (π : Set Nat.Primes) :
    Set (Subgroup G) :=
  {X | Maximal (· ∈ invariantPiSubgroups H A π) X}

theorem mem_invariantPiSubgroups_iff {H A X : Subgroup G} {π : Set Nat.Primes} :
    X ∈ invariantPiSubgroups H A π ↔
      X ≤ H ∧ IsPiSubgroup π X ∧ A ≤ Subgroup.normalizer (X : Set G) :=
  Iff.rfl

theorem isPiSubgroup_piOf_iff [Finite G] {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    IsPiSubgroup (piOf p) X ↔ IsPGroup p X := by
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_card]
  constructor
  · intro h
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdX =>
      h ⟨d, hd⟩ hdX⟩
  · rintro ⟨n, hn⟩ q hqX
    rw [hn] at hqX
    exact (Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow hqX)

theorem isPiSubgroup_piCompl_iff {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    IsPiSubgroup (piCompl p) X ↔ ¬ p ∣ Nat.card X := by
  constructor
  · intro h hdvd
    exact h ⟨p, hp⟩ hdvd rfl
  · intro h q hq hqp
    exact h (hqp ▸ hq)

theorem mem_invariantPiSubgroups_piOf_iff [Finite G] {p : ℕ} (hp : p.Prime)
    {H A X : Subgroup G} :
    X ∈ invariantPiSubgroups H A (piOf p) ↔
      X ≤ H ∧ IsPGroup p X ∧ A ≤ Subgroup.normalizer (X : Set G) := by
  rw [mem_invariantPiSubgroups_iff, isPiSubgroup_piOf_iff hp]

theorem mem_invariantPiSubgroups_piCompl_iff {p : ℕ} (hp : p.Prime) {H A X : Subgroup G} :
    X ∈ invariantPiSubgroups H A (piCompl p) ↔
      X ≤ H ∧ ¬ p ∣ Nat.card X ∧ A ≤ Subgroup.normalizer (X : Set G) := by
  rw [mem_invariantPiSubgroups_iff, isPiSubgroup_piCompl_iff hp]

theorem bot_mem_invariantPiSubgroups (H A : Subgroup G) (π : Set Nat.Primes) :
    (⊥ : Subgroup G) ∈ invariantPiSubgroups H A π := by
  refine ⟨bot_le, fun q hq => ?_, ?_⟩
  · rw [Subgroup.card_bot] at hq
    exact absurd hq q.2.not_dvd_one
  · rw [Subgroup.normalizer_eq_top ⊥]
    exact le_top

theorem invariantPiSubgroups_mono {H K A : Subgroup G} {π : Set Nat.Primes} (h : H ≤ K) :
    invariantPiSubgroups H A π ⊆ invariantPiSubgroups K A π :=
  fun _ hX => ⟨hX.1.trans h, hX.2.1, hX.2.2⟩

theorem invariantPiSubgroups_anti {H A B : Subgroup G} {π : Set Nat.Primes} (h : A ≤ B) :
    invariantPiSubgroups H B π ⊆ invariantPiSubgroups H A π :=
  fun _ hX => ⟨hX.1, hX.2.1, h.trans hX.2.2⟩

theorem mem_maxInvariantPiSubgroups_iff {H A X : Subgroup G} {π : Set Nat.Primes} :
    X ∈ maxInvariantPiSubgroups H A π ↔
      X ∈ invariantPiSubgroups H A π ∧
        ∀ Y ∈ invariantPiSubgroups H A π, X ≤ Y → Y = X :=
  ⟨fun h => ⟨h.prop, fun _ hY hXY => le_antisymm (h.2 hY hXY) hXY⟩,
    fun h => ⟨h.1, fun _ hY hXY => (h.2 _ hY hXY).le⟩⟩

theorem exists_le_mem_maxInvariantPiSubgroups [Finite G] {H A X : Subgroup G}
    {π : Set Nat.Primes} (hX : X ∈ invariantPiSubgroups H A π) :
    ∃ Y ∈ maxInvariantPiSubgroups H A π, X ≤ Y := by
  obtain ⟨Y, hXY, hY⟩ := Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups H A π)) hX
  exact ⟨Y, hY, hXY⟩

theorem maxInvariantPiSubgroups_nonempty [Finite G] (H A : Subgroup G) (π : Set Nat.Primes) :
    (maxInvariantPiSubgroups H A π).Nonempty :=
  let ⟨Y, hY, _⟩ := exists_le_mem_maxInvariantPiSubgroups (bot_mem_invariantPiSubgroups H A π)
  ⟨Y, hY⟩

theorem isPiSubgroup_map_mulEquiv {G' : Type*} [Group G'] (φ : G ≃* G') {π : Set Nat.Primes}
    {X : Subgroup G} (hX : IsPiSubgroup π X) : IsPiSubgroup π (X.map φ.toMonoidHom) := by
  intro q hq
  rw [Subgroup.card_map_of_injective φ.injective] at hq
  exact hX q hq

theorem map_mem_invariantPiSubgroups {G' : Type*} [Group G'] (φ : G ≃* G')
    {H A X : Subgroup G} {π : Set Nat.Primes} (hX : X ∈ invariantPiSubgroups H A π) :
    X.map φ.toMonoidHom ∈
      invariantPiSubgroups (H.map φ.toMonoidHom) (A.map φ.toMonoidHom) π := by
  refine ⟨Subgroup.map_mono hX.1, isPiSubgroup_map_mulEquiv φ hX.2.1, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hX.2.2

@[expose] def collectionIn (Δ : Set (Subgroup G)) (H : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Δ ∧ X ≤ H}

theorem mem_collectionIn_iff {Δ : Set (Subgroup G)} {H X : Subgroup G} :
    X ∈ collectionIn Δ H ↔ X ∈ Δ ∧ X ≤ H :=
  Iff.rfl

abbrev scriptM (X : Set G) : Set (Subgroup G) :=
  maximalTwoLocalsContaining X

theorem mem_scriptM_iff {X : Set G} {M : Subgroup G} :
    M ∈ scriptM X ↔ IsMaximalTwoLocal M ∧ X ⊆ M :=
  Iff.rfl

theorem exists_mem_scriptM_of_isTwoLocal [Finite G] {X : Set G} {H : Subgroup G}
    (hH : CFSG.Assembly.IsTwoLocal H) (hX : X ⊆ H) : ∃ M ∈ scriptM X, H ≤ M := by
  obtain ⟨M, hHM, hmax⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => IsPLocal 2 K) (a := H) hH
  refine ⟨M, ⟨⟨hmax.prop, fun K hMK hK => hMK.not_ge (hmax.2 hK hMK.le)⟩,
    fun x hx => hHM (hX hx)⟩, hHM⟩

theorem scriptM_nonempty_iff [Finite G] {X : Set G} :
    (scriptM X).Nonempty ↔ ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧ X ⊆ H := by
  constructor
  · rintro ⟨M, hM, hXM⟩
    exact ⟨M, hM.1, hXM⟩
  · rintro ⟨H, hH, hX⟩
    obtain ⟨M, hM, -⟩ := exists_mem_scriptM_of_isTwoLocal hH hX
    exact ⟨M, hM⟩

@[expose] def scriptN (X : Set G) : Set (Subgroup G) :=
  {N | IsCoatom N ∧ X ⊆ N}

theorem mem_scriptN_iff {X : Set G} {N : Subgroup G} : N ∈ scriptN X ↔ IsCoatom N ∧ X ⊆ N :=
  Iff.rfl

theorem mem_scriptN_empty_iff {N : Subgroup G} : N ∈ scriptN (∅ : Set G) ↔ IsCoatom N :=
  ⟨fun h => h.1, fun h => ⟨h, Set.empty_subset _⟩⟩

theorem scriptN_anti {X Y : Set G} (h : X ⊆ Y) : scriptN Y ⊆ scriptN X :=
  fun _ hN => ⟨hN.1, h.trans hN.2⟩

theorem scriptN_nonempty [Finite G] {X : Set G} (hX : Subgroup.closure X ≠ ⊤) :
    (scriptN X).Nonempty := by
  obtain ⟨N, hN, hXN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.closure X)).resolve_left
    hX
  exact ⟨N, hN, Subgroup.subset_closure.trans hXN⟩

theorem map_mem_scriptN {G' : Type*} [Group G'] (φ : G ≃* G') {X : Set G} {N : Subgroup G}
    (hN : N ∈ scriptN X) : N.map φ.toMonoidHom ∈ scriptN (φ '' X) := by
  refine ⟨((MulEquiv.mapSubgroup φ).isCoatom_iff N).mpr hN.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_map_of_mem φ.toMonoidHom (hN.2 hx)

section Gamma

variable [Finite G]

@[expose] noncomputable def gammaIn (k : ℕ) (A H : Subgroup G) : Subgroup G :=
  sSup {N | ∃ B : Subgroup G, B ≤ A ∧ k ≤ CFSG.Open.pRank 3 B ∧
    N = H ⊓ Subgroup.normalizer (B : Set G)}

noncomputable abbrev gamma (k : ℕ) (A : Subgroup G) : Subgroup G :=
  CFSG.Open.rankThreeGamma k 3 A

noncomputable abbrev gammaZero (P : Subgroup G) : Subgroup G :=
  aschCore 2 3 P

theorem inf_normalizer_le_gammaIn {k : ℕ} {A H B : Subgroup G} (hBA : B ≤ A)
    (hk : k ≤ CFSG.Open.pRank 3 B) : H ⊓ Subgroup.normalizer (B : Set G) ≤ gammaIn k A H :=
  le_sSup ⟨B, hBA, hk, rfl⟩

theorem gammaIn_le_iff {k : ℕ} {A H M : Subgroup G} :
    gammaIn k A H ≤ M ↔ ∀ B : Subgroup G, B ≤ A → k ≤ CFSG.Open.pRank 3 B →
      H ⊓ Subgroup.normalizer (B : Set G) ≤ M :=
  ⟨fun h _ hBA hk => (inf_normalizer_le_gammaIn hBA hk).trans h,
    fun h => sSup_le fun _ ⟨B, hBA, hk, hN⟩ => hN ▸ h B hBA hk⟩

theorem gammaIn_le (k : ℕ) (A H : Subgroup G) : gammaIn k A H ≤ H :=
  gammaIn_le_iff.mpr fun _ _ _ => inf_le_left

theorem gammaIn_top (k : ℕ) (A : Subgroup G) : gammaIn k A ⊤ = gamma k A := by
  simp only [gammaIn, gamma, CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore, top_inf_eq]

theorem normalizer_le_gamma {k : ℕ} {A B : Subgroup G} (hBA : B ≤ A)
    (hk : k ≤ CFSG.Open.pRank 3 B) : Subgroup.normalizer (B : Set G) ≤ gamma k A :=
  le_sSup ⟨B, hBA, hk, rfl⟩

theorem gamma_le_iff {k : ℕ} {A M : Subgroup G} :
    gamma k A ≤ M ↔ ∀ B : Subgroup G, B ≤ A → k ≤ CFSG.Open.pRank 3 B →
      Subgroup.normalizer (B : Set G) ≤ M :=
  ⟨fun h _ hBA hk => (normalizer_le_gamma hBA hk).trans h,
    fun h => sSup_le fun _ ⟨B, hBA, hk, hN⟩ => hN ▸ h B hBA hk⟩

theorem gammaZero_le_iff {P M : Subgroup G} :
    gammaZero P ≤ M ↔ ∀ X : Subgroup G, X ≤ P → 1 < CFSG.Open.pRank 3 X →
      2 < CFSG.Open.pRank 3 (X ⊔ (P ⊓ Subgroup.centralizer (X : Set G))) →
        Subgroup.normalizer (X : Set G) ≤ M := by
  constructor
  · intro h X hXP h1 h2
    exact le_trans (show Subgroup.normalizer (X : Set G) ≤ gammaZero P from
      le_sSup ⟨X, hXP, h1, h2, rfl⟩) h
  · intro h
    exact sSup_le fun _ ⟨X, hXP, h1, h2, hN⟩ => hN ▸ h X hXP h1 h2

theorem aschCore_eq_gamma_of_isMulCommutative (k : ℕ) {A : Subgroup G}
    (hA : IsMulCommutative A) (h3 : 3 ≤ CFSG.Open.pRank 3 A) : aschCore k 3 A = gamma k A := by
  unfold aschCore gamma CFSG.Open.rankThreeGamma CFSG.Open.GLBCore CFSG.Open.rankThreeAschCore
  congr 1
  ext N
  constructor
  · rintro ⟨X, hXA, hk, -, rfl⟩
    exact ⟨X, hXA, hk, rfl⟩
  · rintro ⟨X, hXA, hk, rfl⟩
    refine ⟨X, hXA, hk, ?_, rfl⟩
    have hAC : A ≤ Subgroup.centralizer (X : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hXA hx⟩ ⟨a, ha⟩)
    rw [inf_eq_left.mpr hAC, sup_eq_right.mpr hXA]
    exact h3

theorem pRank_eq_three_of_mem_partTwoE {E : Subgroup G} (hE : E ∈ partTwoE G) :
    CFSG.Open.pRank 3 E = 3 := by
  apply le_antisymm
  · have hle := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three E
    rwa [hE.2.1, show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.log_pow (by norm_num)] at hle
  · exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three E)
      ⟨E, le_rfl, hE.1, by rw [hE.2.1]; norm_num⟩

theorem aschCore_eq_gamma_of_mem_partTwoE {E : Subgroup G} (hE : E ∈ partTwoE G) :
    aschCore 2 3 E = gamma 2 E :=
  aschCore_eq_gamma_of_isMulCommutative 2 hE.1.1 (pRank_eq_three_of_mem_partTwoE hE).ge

theorem mem_partTwoT_iff {E : Subgroup G} :
    E ∈ partTwoT G ↔ E ∈ partTwoE G ∧ (scriptM (gamma 2 E : Set G)).Nonempty := by
  constructor
  · rintro ⟨hE, H, hH, hle⟩
    refine ⟨hE, scriptM_nonempty_iff.mpr ⟨H, hH, fun x hx => ?_⟩⟩
    rw [← aschCore_eq_gamma_of_mem_partTwoE hE] at hx
    exact hle hx
  · rintro ⟨hE, hM⟩
    obtain ⟨H, hH, hle⟩ := scriptM_nonempty_iff.mp hM
    refine ⟨hE, H, hH, fun x hx => ?_⟩
    rw [aschCore_eq_gamma_of_mem_partTwoE hE] at hx
    exact hle hx

theorem map_gamma_le {G' : Type*} [Group G'] [Finite G'] (φ : G ≃* G') (k : ℕ)
    (A : Subgroup G) : (gamma k A).map φ.toMonoidHom ≤ gamma k (A.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap, gamma_le_iff]
  intro B hBA hk
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  exact normalizer_le_gamma (Subgroup.map_mono hBA)
    (by rwa [CFSG.RankThreeEvenClassification.Helpers.pRank_map_equiv 3 Nat.prime_three])

theorem map_gamma {G' : Type*} [Group G'] [Finite G'] (φ : G ≃* G') (k : ℕ) (A : Subgroup G) :
    (gamma k A).map φ.toMonoidHom = gamma k (A.map φ.toMonoidHom) := by
  refine le_antisymm (map_gamma_le φ k A) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (map_gamma_le φ.symm k (A.map φ.toMonoidHom))
  rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm,
    Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' from
      MonoidHom.ext φ.apply_symm_apply, Subgroup.map_id] at h

end Gamma

@[expose] def StarConditionAt (A : Subgroup G) (a : G) : Prop :=
  thetaAlpha 3 ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (centralLine a))) ≤
    aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G) ⧸ centralLine a)

@[expose] def StarCondition (A : Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → StarConditionAt A a

@[expose] noncomputable def elemTwoFamily (i : ℕ) (H : Type*) [Group H] : Set (Subgroup H) :=
  {A | IsElementaryAbelian 2 A ∧ i ≤ CFSG.pRank 2 H ∧ Nat.card A = 2 ^ (CFSG.pRank 2 H - i)}

@[expose] noncomputable def elemTwoThompson (i : ℕ) (H : Type*) [Group H] : Subgroup H :=
  sSup (elemTwoFamily i H)

theorem mem_elemTwoFamily_iff {i : ℕ} {H : Type*} [Group H] {A : Subgroup H} :
    A ∈ elemTwoFamily i H ↔
      IsElementaryAbelian 2 A ∧ i ≤ CFSG.pRank 2 H ∧ Nat.card A = 2 ^ (CFSG.pRank 2 H - i) :=
  Iff.rfl

theorem elemTwoFamily_zero (H : Type*) [Group H] : elemTwoFamily 0 H = elemThompsonFamily H 2 := by
  ext A
  simp [elemTwoFamily, elemThompsonFamily]

theorem elemTwoThompson_zero (H : Type*) [Group H] : elemTwoThompson 0 H = elemThompson H 2 := by
  rw [elemTwoThompson, elemTwoFamily_zero, elemThompson]

theorem le_elemTwoThompson {i : ℕ} {H : Type*} [Group H] {A : Subgroup H}
    (hA : A ∈ elemTwoFamily i H) : A ≤ elemTwoThompson i H :=
  le_sSup hA

@[expose] def thetaComponentsIn (H : Subgroup G) : Set (Subgroup G) :=
  (fun L => L.map H.subtype) '' thetaComponents 3 H

@[expose] def oTwoComponents (H : Type*) [Group H] : Set (Subgroup H) :=
  {L | Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)}

@[expose] def oTwoComponentsIn (H : Subgroup G) : Set (Subgroup G) :=
  (fun L => L.map H.subtype) '' oTwoComponents H

theorem thetaComponentsAt_eq_thetaComponentsIn (a : G) :
    thetaComponentsAt 3 a = thetaComponentsIn (Subgroup.centralizer ({a} : Set G)) :=
  rfl

theorem mem_thetaComponentFamily_iff {A L : Subgroup G} :
    L ∈ thetaComponentFamily 3 A ↔ ∃ a ∈ A, a ≠ 1 ∧ L ∈ thetaComponentsAt 3 a := by
  simp only [thetaComponentFamily, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]

theorem mem_image_map_subtype_iff {H L : Subgroup G} {S : Set (Subgroup H)} :
    L ∈ (fun L' : Subgroup H => L'.map H.subtype) '' S ↔ L ≤ H ∧ L.subgroupOf H ∈ S := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    refine ⟨Subgroup.map_subtype_le L', ?_⟩
    rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  · rintro ⟨hLH, hL⟩
    exact ⟨_, hL, Subgroup.map_subgroupOf_eq_of_le hLH⟩

theorem mem_thetaComponentsIn_iff {H L : Subgroup G} :
    L ∈ thetaComponentsIn H ↔ L ≤ H ∧ L.subgroupOf H ∈ thetaComponents 3 H :=
  mem_image_map_subtype_iff

theorem mem_oTwoComponentsIn_iff {H L : Subgroup G} :
    L ∈ oTwoComponentsIn H ↔ L ≤ H ∧ L.subgroupOf H ∈ oTwoComponents H :=
  mem_image_map_subtype_iff

theorem le_of_mem_thetaComponentsIn {H L : Subgroup G} (hL : L ∈ thetaComponentsIn H) : L ≤ H :=
  (mem_thetaComponentsIn_iff.mp hL).1

theorem le_of_mem_oTwoComponentsIn {H L : Subgroup G} (hL : L ∈ oTwoComponentsIn H) : L ≤ H :=
  (mem_oTwoComponentsIn_iff.mp hL).1

theorem isPerfect_map_subtype {H : Subgroup G} {L : Subgroup H} (hL : Group.IsPerfect L) :
    Group.IsPerfect (L.map H.subtype) :=
  Group.IsPerfect.ofSurjective (f := (L.equivMapOfInjective H.subtype
    H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

theorem isPerfect_of_mem_thetaComponentsIn {H L : Subgroup G} (hL : L ∈ thetaComponentsIn H) :
    Group.IsPerfect L := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact isPerfect_map_subtype hL'.1

theorem isPerfect_of_mem_thetaComponentFamily {A L : Subgroup G}
    (hL : L ∈ thetaComponentFamily 3 A) : Group.IsPerfect L := by
  obtain ⟨a, -, -, haL⟩ := mem_thetaComponentFamily_iff.mp hL
  exact isPerfect_of_mem_thetaComponentsIn haL

theorem isPerfect_of_mem_oTwoComponentsIn {H L : Subgroup G} (hL : L ∈ oTwoComponentsIn H) :
    Group.IsPerfect L := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact isPerfect_map_subtype hL'.1

theorem map_mulEquiv_mem_oTwoComponents {H H' : Type*} [Group H] [Group H'] (σ : H ≃* H')
    {L : Subgroup H} (hL : L ∈ oTwoComponents H) : L.map σ.toMonoidHom ∈ oTwoComponents H' := by
  set e := L.equivMapOfInjective σ.toMonoidHom σ.injective
  refine ⟨?_, hL.2.1.map σ.surjective, ?_⟩
  · have := hL.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hL.2.2

@[expose] def llRel (L K : Subgroup G) : Prop :=
  L = inSubgroup perfectResidual (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) L

@[expose] def lStar (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentFamily 3 A ∧ ∀ K ∈ thetaComponentFamily 3 A, llRel L K → llRel K L}

@[expose] def lStarOf (A E : Subgroup G) : Set (Subgroup G) :=
  thetaComponentFamily 3 E ∩ lStar A

@[expose] def lStarAt (A : Subgroup G) (a : G) : Set (Subgroup G) :=
  lStar A ∩ thetaComponentsAt 3 a

theorem mem_lStar_iff {A L : Subgroup G} :
    L ∈ lStar A ↔
      L ∈ thetaComponentFamily 3 A ∧ ∀ K ∈ thetaComponentFamily 3 A, llRel L K → llRel K L :=
  Iff.rfl

theorem lStar_subset (A : Subgroup G) : lStar A ⊆ thetaComponentFamily 3 A :=
  fun _ hL => hL.1

theorem lStarOf_subset_lStar (A E : Subgroup G) : lStarOf A E ⊆ lStar A :=
  Set.inter_subset_right

theorem lStarOf_subset (A E : Subgroup G) : lStarOf A E ⊆ thetaComponentFamily 3 E :=
  Set.inter_subset_left

theorem lStarAt_subset_lStar (A : Subgroup G) (a : G) : lStarAt A a ⊆ lStar A :=
  Set.inter_subset_left

theorem lStarAt_subset (A : Subgroup G) (a : G) : lStarAt A a ⊆ thetaComponentsAt 3 a :=
  Set.inter_subset_right

theorem llRel_self_of_isPerfect [Finite G] {L : Subgroup G} (hL : Group.IsPerfect L) :
    llRel L L := by
  rw [llRel, inf_idem, inSubgroup_perfectResidual_of_isPerfect hL]
  exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm

theorem llRel_self_of_mem_thetaComponentFamily [Finite G] {A L : Subgroup G}
    (hL : L ∈ thetaComponentFamily 3 A) : llRel L L :=
  llRel_self_of_isPerfect (isPerfect_of_mem_thetaComponentFamily hL)

@[expose] def lZero (E : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentFamily 3 E ∧ ∃ U ∈ invariantPiSubgroups L E (piOf 2),
    ¬ ⁅U, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L}

@[expose] def lZeroUnion (A : Subgroup G) : Set (Subgroup G) :=
  ⋃ E ∈ collectionIn (partTwoE G) A, lZero E

@[expose] def lZeroAt (A : Subgroup G) (a : G) : Set (Subgroup G) :=
  lZeroUnion A ∩ thetaComponentsAt 3 a

@[expose] def lZeroStar (A : Subgroup G) : Set (Subgroup G) :=
  lZeroUnion A ∩ lStar A

@[expose] def lZeroStarAt (A : Subgroup G) (a : G) : Set (Subgroup G) :=
  thetaComponentsAt 3 a ∩ lZeroStar A

theorem mem_lZero_iff {E L : Subgroup G} :
    L ∈ lZero E ↔ L ∈ thetaComponentFamily 3 E ∧ ∃ U ∈ invariantPiSubgroups L E (piOf 2),
      ¬ ⁅U, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L :=
  Iff.rfl

theorem mem_lZeroUnion_iff {A L : Subgroup G} :
    L ∈ lZeroUnion A ↔ ∃ E ∈ partTwoE G, E ≤ A ∧ L ∈ lZero E := by
  simp only [lZeroUnion, Set.mem_iUnion, collectionIn, Set.mem_ofPred_eq, exists_prop, and_assoc]

theorem lZero_subset (E : Subgroup G) : lZero E ⊆ thetaComponentFamily 3 E :=
  fun _ hL => hL.1

theorem lZero_subset_lZeroUnion {A E : Subgroup G} (hE : E ∈ partTwoE G) (hEA : E ≤ A) :
    lZero E ⊆ lZeroUnion A :=
  fun _ hL => mem_lZeroUnion_iff.mpr ⟨E, hE, hEA, hL⟩

theorem lZeroUnion_eq_lZero [Finite G] {A : Subgroup G} (hA : A ∈ partTwoE G) :
    lZeroUnion A = lZero A := by
  ext L
  rw [mem_lZeroUnion_iff]
  constructor
  · rintro ⟨E, hE, hEA, hL⟩
    rwa [Subgroup.eq_of_le_of_card_ge hEA (by rw [hE.2.1, hA.2.1])] at hL
  · exact fun hL => ⟨A, hA, le_rfl, hL⟩

theorem lZeroAt_subset_lZeroUnion (A : Subgroup G) (a : G) : lZeroAt A a ⊆ lZeroUnion A :=
  Set.inter_subset_left

theorem lZeroAt_subset (A : Subgroup G) (a : G) : lZeroAt A a ⊆ thetaComponentsAt 3 a :=
  Set.inter_subset_right

theorem lZeroStar_subset_lZeroUnion (A : Subgroup G) : lZeroStar A ⊆ lZeroUnion A :=
  Set.inter_subset_left

theorem lZeroStar_subset_lStar (A : Subgroup G) : lZeroStar A ⊆ lStar A :=
  Set.inter_subset_right

theorem lZeroStarAt_subset (A : Subgroup G) (a : G) : lZeroStarAt A a ⊆ thetaComponentsAt 3 a :=
  Set.inter_subset_left

theorem lZeroStarAt_subset_lZeroStar (A : Subgroup G) (a : G) :
    lZeroStarAt A a ⊆ lZeroStar A :=
  Set.inter_subset_right

theorem lZeroStarAt_eq (A : Subgroup G) (a : G) :
    lZeroStarAt A a = lZeroAt A a ∩ lStarAt A a := by
  ext L
  simp only [lZeroStarAt, lZeroStar, lZeroAt, lStarAt, Set.mem_inter_iff]
  tauto

@[expose] def fourGroups (E : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ invariantPiSubgroups ⊤ E (piOf 2) ∧ CFSG.Assembly.IsElemAbelian 2 U ∧ Nat.card U = 4}

@[expose] def fourGroupsPlus (E : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ fourGroups E ∧ ⁅U, E⁆ = ⊥}

@[expose] def fourGroupsMinus (E : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ fourGroups E ∧ U = ⁅U, E⁆}

theorem mem_fourGroups_iff [Finite G] {E U : Subgroup G} :
    U ∈ fourGroups E ↔ E ≤ Subgroup.normalizer (U : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 U ∧ Nat.card U = 4 := by
  rw [fourGroups, Set.mem_ofPred_eq, mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
  constructor
  · rintro ⟨⟨-, -, hN⟩, hab, hcard⟩
    exact ⟨hN, hab, hcard⟩
  · rintro ⟨hN, hab, hcard⟩
    exact ⟨⟨le_top, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hN⟩, hab, hcard⟩

theorem fourGroupsPlus_subset (E : Subgroup G) : fourGroupsPlus E ⊆ fourGroups E :=
  fun _ hU => hU.1

theorem fourGroupsMinus_subset (E : Subgroup G) : fourGroupsMinus E ⊆ fourGroups E :=
  fun _ hU => hU.1

theorem mem_fourGroupsPlus_iff {E U : Subgroup G} :
    U ∈ fourGroupsPlus E ↔ U ∈ fourGroups E ∧ E ≤ Subgroup.centralizer (U : Set G) := by
  rw [fourGroupsPlus, Set.mem_ofPred_eq, Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.le_centralizer_iff]

theorem disjoint_fourGroupsPlus_fourGroupsMinus (E : Subgroup G) :
    Disjoint (fourGroupsPlus E) (fourGroupsMinus E) := by
  rw [Set.disjoint_left]
  rintro U ⟨hU, hcomm⟩ ⟨-, hU'⟩
  have hcard := hU.2.2
  rw [hU', hcomm, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

theorem map_mem_fourGroups {G' : Type*} [Group G'] (φ : G ≃* G') {E U : Subgroup G}
    (hU : U ∈ fourGroups E) : U.map φ.toMonoidHom ∈ fourGroups (E.map φ.toMonoidHom) := by
  refine ⟨?_, CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 φ.toMonoidHom U hU.2.1,
    by rw [Subgroup.card_map_of_injective φ.injective, hU.2.2]⟩
  have h := map_mem_invariantPiSubgroups φ hU.1
  rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h

theorem map_mem_fourGroupsPlus {G' : Type*} [Group G'] (φ : G ≃* G') {E U : Subgroup G}
    (hU : U ∈ fourGroupsPlus E) :
    U.map φ.toMonoidHom ∈ fourGroupsPlus (E.map φ.toMonoidHom) :=
  ⟨map_mem_fourGroups φ hU.1, by rw [← Subgroup.map_commutator, hU.2, Subgroup.map_bot]⟩

theorem map_mem_fourGroupsMinus {G' : Type*} [Group G'] (φ : G ≃* G') {E U : Subgroup G}
    (hU : U ∈ fourGroupsMinus E) :
    U.map φ.toMonoidHom ∈ fourGroupsMinus (E.map φ.toMonoidHom) :=
  ⟨map_mem_fourGroups φ hU.1, by rw [← Subgroup.map_commutator, ← hU.2]⟩

section Transport

variable {G' : Type*} [Group G']

theorem map_map_subtype_mulEquiv (φ : G ≃* G') (X : Subgroup G) (K : Subgroup X) :
    (K.map X.subtype).map φ.toMonoidHom =
      (K.map (X.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom).map
        (X.map φ.toMonoidHom).subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem perfectResidual_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (perfectResidual A).map e.toMonoidHom = perfectResidual B := by
  rw [perfectResidual, perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

theorem map_inSubgroup_perfectResidual (φ : G ≃* G') (X : Subgroup G) :
    (inSubgroup perfectResidual X).map φ.toMonoidHom =
      inSubgroup perfectResidual (X.map φ.toMonoidHom) := by
  rw [inSubgroup, map_map_subtype_mulEquiv, perfectResidual_map_mulEquiv, inSubgroup]

theorem map_inSubgroup_aschbacherSolvableCore [Finite G] (φ : G ≃* G') (X : Subgroup G) :
    (inSubgroup (aschbacherSolvableCore 3) X).map φ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (X.map φ.toMonoidHom) := by
  rw [inSubgroup, map_map_subtype_mulEquiv, aschbacherSolvableCore_map_mulEquiv Nat.prime_three,
    inSubgroup]

theorem map_centralizer_singleton (φ : G ≃* G') (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ a} : Set G') := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    change φ x * φ a = φ a * φ x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, Subgroup.mem_centralizer_singleton_iff.mpr (φ.injective ?_), by simp⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem map_mem_thetaComponentsIn [Finite G] (φ : G ≃* G') {H L : Subgroup G}
    (hL : L ∈ thetaComponentsIn H) :
    L.map φ.toMonoidHom ∈ thetaComponentsIn (H.map φ.toMonoidHom) := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact ⟨_, map_mulEquiv_mem_thetaComponents Nat.prime_three
    (H.equivMapOfInjective φ.toMonoidHom φ.injective) hL', (map_map_subtype_mulEquiv φ H L').symm⟩

theorem map_mem_oTwoComponentsIn (φ : G ≃* G') {H L : Subgroup G}
    (hL : L ∈ oTwoComponentsIn H) :
    L.map φ.toMonoidHom ∈ oTwoComponentsIn (H.map φ.toMonoidHom) := by
  obtain ⟨L', hL', rfl⟩ := hL
  exact ⟨_, map_mulEquiv_mem_oTwoComponents (H.equivMapOfInjective φ.toMonoidHom φ.injective) hL',
    (map_map_subtype_mulEquiv φ H L').symm⟩

theorem map_mem_thetaComponentsAt [Finite G] (φ : G ≃* G') {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 a) : L.map φ.toMonoidHom ∈ thetaComponentsAt 3 (φ a) := by
  rw [thetaComponentsAt_eq_thetaComponentsIn, ← map_centralizer_singleton]
  exact map_mem_thetaComponentsIn φ hL

theorem map_mem_thetaComponentFamily [Finite G] (φ : G ≃* G') {A L : Subgroup G}
    (hL : L ∈ thetaComponentFamily 3 A) :
    L.map φ.toMonoidHom ∈ thetaComponentFamily 3 (A.map φ.toMonoidHom) := by
  obtain ⟨a, haA, ha1, haL⟩ := mem_thetaComponentFamily_iff.mp hL
  exact mem_thetaComponentFamily_iff.mpr ⟨φ a, Subgroup.mem_map_of_mem φ.toMonoidHom haA,
    (map_ne_one_iff φ φ.injective).mpr ha1, map_mem_thetaComponentsAt φ haL⟩

theorem map_map_symm (φ : G ≃* G') (K : Subgroup G') :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' from
    MonoidHom.ext φ.apply_symm_apply, Subgroup.map_id]

theorem llRel_map [Finite G] (φ : G ≃* G') {L K : Subgroup G} (h : llRel L K) :
    llRel (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  unfold llRel at h ⊢
  rw [← Subgroup.map_inf _ _ _ φ.injective, ← map_inSubgroup_perfectResidual,
    ← map_inSubgroup_aschbacherSolvableCore, ← Subgroup.map_sup, ← h]

theorem llRel_map_iff [Finite G] [Finite G'] (φ : G ≃* G') {L K : Subgroup G} :
    llRel (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) ↔ llRel L K := by
  refine ⟨fun h => ?_, llRel_map φ⟩
  have h' := llRel_map φ.symm h
  rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm,
    CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm] at h'

theorem map_mem_lStar [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G}
    (hL : L ∈ lStar A) : L.map φ.toMonoidHom ∈ lStar (A.map φ.toMonoidHom) := by
  refine ⟨map_mem_thetaComponentFamily φ hL.1, fun K' hK' hLK' => ?_⟩
  have hK : K'.map φ.symm.toMonoidHom ∈ thetaComponentFamily 3 A := by
    have h := map_mem_thetaComponentFamily φ.symm hK'
    rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm] at h
  rw [← map_map_symm φ K'] at hLK' ⊢
  exact llRel_map φ (hL.2 _ hK ((llRel_map_iff φ).mp hLK'))

theorem map_mem_lStarOf [Finite G] [Finite G'] (φ : G ≃* G') {A E L : Subgroup G}
    (hL : L ∈ lStarOf A E) :
    L.map φ.toMonoidHom ∈ lStarOf (A.map φ.toMonoidHom) (E.map φ.toMonoidHom) :=
  ⟨map_mem_thetaComponentFamily φ hL.1, map_mem_lStar φ hL.2⟩

theorem map_mem_lStarAt [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G} {a : G}
    (hL : L ∈ lStarAt A a) : L.map φ.toMonoidHom ∈ lStarAt (A.map φ.toMonoidHom) (φ a) :=
  ⟨map_mem_lStar φ hL.1, map_mem_thetaComponentsAt φ hL.2⟩

theorem map_mem_partTwoE (φ : G ≃* G') {E : Subgroup G} (hE : E ∈ partTwoE G) :
    E.map φ.toMonoidHom ∈ partTwoE G' := by
  obtain ⟨hab, hcard, U, hU, hU2, hEU⟩ := hE
  refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ.toMonoidHom E hab,
    by rw [Subgroup.card_map_of_injective φ.injective, hcard], U.map φ.toMonoidHom,
    fun h => hU ((Subgroup.map_eq_bot_iff_of_injective U φ.injective).mp h),
    hU2.map φ.toMonoidHom, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hEU

theorem map_mem_partTwoF (φ : G ≃* G') {A : Subgroup G} (hA : A ∈ partTwoF G) :
    A.map φ.toMonoidHom ∈ partTwoF G' := by
  obtain ⟨hab, hmax, E, hE, hEA⟩ := hA
  refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ.toMonoidHom A hab,
    fun B hB hAB => ?_, E.map φ.toMonoidHom, map_mem_partTwoE φ hE, Subgroup.map_mono hEA⟩
  have hB' := hmax _ (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3
    φ.symm.toMonoidHom B hB) (by
      rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm φ A]
      exact Subgroup.map_mono hAB)
  rw [← hB', map_map_symm]

theorem map_mem_lZero [Finite G] (φ : G ≃* G') {E L : Subgroup G} (hL : L ∈ lZero E) :
    L.map φ.toMonoidHom ∈ lZero (E.map φ.toMonoidHom) := by
  obtain ⟨hLE, U, hU, hUE⟩ := hL
  refine ⟨map_mem_thetaComponentFamily φ hLE, U.map φ.toMonoidHom,
    map_mem_invariantPiSubgroups φ hU, ?_⟩
  rwa [← Subgroup.map_commutator, ← map_inSubgroup_aschbacherSolvableCore,
    Subgroup.map_le_map_iff_of_injective φ.injective]

theorem map_mem_lZeroUnion [Finite G] (φ : G ≃* G') {A L : Subgroup G}
    (hL : L ∈ lZeroUnion A) : L.map φ.toMonoidHom ∈ lZeroUnion (A.map φ.toMonoidHom) := by
  obtain ⟨E, hE, hEA, hLE⟩ := mem_lZeroUnion_iff.mp hL
  exact mem_lZeroUnion_iff.mpr ⟨E.map φ.toMonoidHom, map_mem_partTwoE φ hE,
    Subgroup.map_mono hEA, map_mem_lZero φ hLE⟩

theorem map_mem_lZeroAt [Finite G] (φ : G ≃* G') {A L : Subgroup G} {a : G}
    (hL : L ∈ lZeroAt A a) : L.map φ.toMonoidHom ∈ lZeroAt (A.map φ.toMonoidHom) (φ a) :=
  ⟨map_mem_lZeroUnion φ hL.1, map_mem_thetaComponentsAt φ hL.2⟩

theorem map_mem_lZeroStar [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G}
    (hL : L ∈ lZeroStar A) : L.map φ.toMonoidHom ∈ lZeroStar (A.map φ.toMonoidHom) :=
  ⟨map_mem_lZeroUnion φ hL.1, map_mem_lStar φ hL.2⟩

theorem map_mem_lZeroStarAt [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G} {a : G}
    (hL : L ∈ lZeroStarAt A a) :
    L.map φ.toMonoidHom ∈ lZeroStarAt (A.map φ.toMonoidHom) (φ a) :=
  ⟨map_mem_thetaComponentsAt φ hL.1, map_mem_lZeroStar φ hL.2⟩

end Transport

end CFSG.RankThree.PartTwo
