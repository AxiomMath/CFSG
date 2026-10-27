module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Milestones.ASVolI.I7
public import CFSG.Goldschmidt.Steps.Fusion
public import CFSG.Goldschmidt.StrongClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Strong

variable {G : Type} [Group G]

@[expose] def IsStronglyEmbeddedGLS (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card ↥M) ∧ ∃ T : Subgroup G, IsSylowTwoIn T M ∧
    ∀ Q : Subgroup G, Q ≤ T → Q ≠ ⊥ → Subgroup.normalizer (Q : Set G) ≤ M

@[expose] def involutionNormalClosure (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g : G, ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 ∧ x = g⁻¹ * i * g}

end Strong

@[expose] def IsBenderGroup (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, StatedClassicalModel X .PSL 2 2 n) ∨ (∃ f : ℕ, SuzukiModel X 2 f) ∨
    (∃ n : ℕ, StatedClassicalModel X .PSU 3 2 n)

@[expose] def IsSU3Group (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def IsBorelSubgroupTwo {X : Type} [Group X] (B : Subgroup X) : Prop :=
  ∃ S : Sylow 2 X, B = Subgroup.normalizer ((S : Subgroup X) : Set X)

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T : Subgroup G), M ≠ ⊤ → Even (Nat.card ↥M) →
    IsSylowTwoIn T M →
    (IsStronglyEmbeddedGLS M ↔ ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) ∧
    ((∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) ↔
      (Subgroup.normalizer (T : Set G) ≤ M ∧
        ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M)) ∧
    ((Subgroup.normalizer (T : Set G) ≤ M ∧
        ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M) ↔
      ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∃! x : G ⧸ M, t • x = x)

section BurnsideIc

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_exists_sylow_of_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowTwoIn T ⊤) : ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  exact ⟨hT.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

private theorem burnsideIc_map_conj_eq_iff {G : Type} [Group G] (U : Subgroup G) (g : G) :
    U.map (MulAut.conj g).toMonoidHom = U ↔ g ∈ Subgroup.normalizer (U : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_isTISubgroup_iff {G : Type} [Group G] (U : Subgroup G) :
    IsTISubgroup U ↔ fusionIsTI U := by
  have hinv : ∀ g : G, g⁻¹ ∈ Subgroup.normalizer (U : Set G) ↔
      g ∈ Subgroup.normalizer (U : Set G) := fun g =>
    (Subgroup.normalizer (U : Set G)).inv_mem_iff
  constructor
  · intro h g hg
    have hg' : g⁻¹ ∉ Subgroup.normalizer (U : Set G) := fun hn =>
      hg ((burnsideIc_map_conj_eq_iff U g).2 ((hinv g).1 hn))
    simpa [CFSG.conjugate, inv_inv] using h g⁻¹ hg'
  · intro h g hg
    have hg' : U.map (MulAut.conj g⁻¹).toMonoidHom ≠ U := fun hn =>
      hg ((hinv g).1 ((burnsideIc_map_conj_eq_iff U g⁻¹).1 hn))
    exact h g⁻¹ hg'


private theorem burnsideIc_mem_conjugate {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem burnsideIc_even_card_of_le {G : Type} [Group G] [Finite G] {Q X : Subgroup G}
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) (hle : Q ≤ X) : Even (Nat.card X) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq Q hn
  have h2 : 2 ∣ Nat.card X := by
    have := Subgroup.card_dvd_of_le hle
    rw [hn] at this
    exact (dvd_pow_self 2 hn0).trans this
  exact even_iff_two_dvd.2 h2

private theorem burnsideIc_exists_involution_of_even {G : Type} [Group G] [Finite G] {K :
    Subgroup G}
    (hK : Even (Nat.card K)) : ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 hK)
  have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one (x : G)
    rwa [hx'] at this
  · intro h1
    rw [h1, orderOf_one] at hx'
    omega

private theorem burnsideIc_exists_involution {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsPGroup 2 K) (hne : K ≠ ⊥) : ∃ i ∈ K, i ^ 2 = 1 ∧ i ≠ 1 :=
  burnsideIc_exists_involution_of_even (burnsideIc_even_card_of_le hK hne le_rfl)

private theorem burnsideIc_isPGroup_zpowers {G : Type} [Group G] {i : G} (hi2 : i ^ 2 = 1)
    (hi1 : i ≠ 1) : IsPGroup 2 (Subgroup.zpowers i) := by
  have ho : orderOf i = 2 := orderOf_eq_prime hi2 hi1
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])

private theorem burnsideIc_conj_involution {G : Type} [Group G] {i : G} (g : G) (hi2 : i ^ 2 = 1)
    (hi1 : i ≠ 1) : (g * i * g⁻¹) ^ 2 = 1 ∧ g * i * g⁻¹ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [conj_pow, hi2]
    group
  · intro h
    apply hi1
    have : i = g⁻¹ * (g * i * g⁻¹) * g := by group
    rw [this, h]
    group

private theorem burnsideIc_conj_mem_centralizer {G : Type} [Group G] {i c : G} (g : G)
    (hc : c ∈ Subgroup.centralizer ({i} : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer ({g * i * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have := hc i (Set.mem_singleton i)
  calc g * i * g⁻¹ * (g * c * g⁻¹) = g * (i * c) * g⁻¹ := by group
    _ = g * (c * i) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * (g * i * g⁻¹) := by group

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_exists_isSylowTwoIn_ge {G : Type} [Group G] [Finite G] {M R : Subgroup G}
    (hR : IsPGroup 2 R) (hRM : R ≤ M) : ∃ P : Subgroup G, IsSylowTwoIn P M ∧ R ≤ P := by
  have hR' : IsPGroup 2 (R.comap M.subtype) := hR.comap_subtype
  obtain ⟨P, hP⟩ := hR'.exists_le_sylow
  have hsub : ((P : Subgroup ↥M).map M.subtype).subgroupOf M = (P : Subgroup ↥M) :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨(P : Subgroup ↥M).map M.subtype,
    ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩, ?_⟩
  · rw [hsub]
    exact P.not_dvd_index
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hRM hx⟩, hP (Subgroup.mem_comap.mpr hx), rfl⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_isSylowTwoIn_conj {G : Type} [Group G] [Finite G] {M T T' : Subgroup G}
    (hT : IsSylowTwoIn T M) (hT' : IsSylowTwoIn T' M) :
    ∃ m ∈ M, ∀ x : G, x ∈ T' ↔ m⁻¹ * x * m ∈ T := by
  have hTp : IsPGroup 2 (T.subgroupOf M) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hTp' : IsPGroup 2 (T'.subgroupOf M) :=
    hT'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT'.1).symm
  let S : Sylow 2 M := hTp.toSylow hT.2.2
  let S' : Sylow 2 M := hTp'.toSylow hT'.2.2
  have hS : (S : Subgroup M) = T.subgroupOf M := rfl
  have hS' : (S' : Subgroup M) = T'.subgroupOf M := rfl
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S S'
  refine ⟨m, m.2, fun x => ?_⟩
  have key : ∀ y : M, y ∈ (S' : Subgroup M) ↔ (MulAut.conj m)⁻¹ • y ∈ (S : Subgroup M) := by
    intro y
    rw [← hm]
    show y ∈ ((m • S : Sylow 2 M) : Subgroup M) ↔ _
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    have hxM : x ∈ M := hT'.1 hx
    have h1 := (key ⟨x, hxM⟩).1 (by rw [hS']; simpa [Subgroup.mem_subgroupOf] using hx)
    rw [hS] at h1
    simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h1
  · intro hx
    have hxT : m⁻¹ * x * m ∈ T := hx
    have hxM : x ∈ M := by
      have : m⁻¹ * x * m ∈ M := hT.1 hxT
      have h2 := M.mul_mem (M.mul_mem m.2 this) (M.inv_mem m.2)
      simpa [mul_assoc] using h2
    have h1 : (MulAut.conj m)⁻¹ • (⟨x, hxM⟩ : M) ∈ (S : Subgroup M) := by
      rw [hS]
      simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using hx
    have h2 := (key ⟨x, hxM⟩).2 h1
    rw [hS'] at h2
    simpa [Subgroup.mem_subgroupOf] using h2

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_exists_conj_le {G : Type} [Group G] [Finite G] {M T R : Subgroup G}
    (hT : IsSylowTwoIn T M) (hRM : R ≤ M) (hR : IsPGroup 2 R) :
    ∃ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ ∈ T := by
  obtain ⟨P, hP, hRP⟩ := burnsideIc_exists_isSylowTwoIn_ge hR hRM
  obtain ⟨m, hm, hmP⟩ := burnsideIc_isSylowTwoIn_conj hT hP
  refine ⟨m⁻¹, M.inv_mem hm, fun r hr => ?_⟩
  have := (hmP r).1 (hRP hr)
  simpa using this

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_centralizer_le_of_mem {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoIn T M)
    (hC : ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M)
    {i : G} (hiM : i ∈ M) (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1) :
    Subgroup.centralizer ({i} : Set G) ≤ M := by
  obtain ⟨m, hm, hmT⟩ := burnsideIc_exists_conj_le hT (Subgroup.zpowers_le.2 hiM)
    (burnsideIc_isPGroup_zpowers hi2 hi1)
  have hj : m * i * m⁻¹ ∈ T := hmT i (Subgroup.mem_zpowers i)
  obtain ⟨hj2, hj1⟩ := burnsideIc_conj_involution m hi2 hi1
  intro c hc
  have h1 := hC _ hj hj2 hj1 (burnsideIc_conj_mem_centralizer m hc)
  have h3 := M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm
  simpa [mul_assoc] using h3

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_centralizer_le_inf_conjugate {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hT : IsSylowTwoIn T M)
    (hC : ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M)
    {g i : G} (hi : i ∈ M ⊓ CFSG.conjugate M g) (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1) :
    Subgroup.centralizer ({i} : Set G) ≤ M ⊓ CFSG.conjugate M g := by
  have h1 := burnsideIc_centralizer_le_of_mem hT hC hi.1 hi2 hi1
  have hgi : g * i * g⁻¹ ∈ M := burnsideIc_mem_conjugate.1 hi.2
  obtain ⟨hgi2, hgi1⟩ := burnsideIc_conj_involution g hi2 hi1
  have h2 := burnsideIc_centralizer_le_of_mem hT hC hgi hgi2 hgi1
  intro c hc
  exact ⟨h1 hc, burnsideIc_mem_conjugate.2 (h2 (burnsideIc_conj_mem_centralizer g hc))⟩

private theorem burnsideIc_exists_normalizing_gt {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 2 P) (hQP : Q < P) :
    ∃ Y : Subgroup G, Q < Y ∧ Y ≤ P ∧ Y ≤ Subgroup.normalizer (Q : Set G) ∧ IsPGroup 2 Y := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact not_le_of_gt hQP h
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt
  obtain ⟨x, hxN, hxQ⟩ := SetLike.exists_of_lt hgrow
  have hxN' : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    have := hxN
    rw [← Subgroup.subgroupOf_normalizer_eq hQP.le] at this
    exact this
  have hxQ' : (x : G) ∉ Q := hxQ
  refine ⟨Q ⊔ Subgroup.zpowers (x : G), ?_, sup_le hQP.le (Subgroup.zpowers_le.2 x.2), ?_, ?_⟩
  · refine lt_of_le_of_ne le_sup_left ?_
    intro h
    exact hxQ' (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxN')
  · exact hP.to_le (sup_le hQP.le (Subgroup.zpowers_le.2 x.2))

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_exists_larger {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQM : Q ≤ M) (hns : ¬ IsSylowTwoIn Q M) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ M ∧ Q < R ∧ R ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨P, hP, hQP⟩ := burnsideIc_exists_isSylowTwoIn_ge hQ hQM
  have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hns (by rw [h]; exact hP))
  obtain ⟨Y, hQY, hYP, hYN, hY2⟩ :=
    burnsideIc_exists_normalizing_gt hP.2.1 hlt
  exact ⟨Y, hY2, hYP.trans hP.1, hQY, hYN⟩

private theorem burnsideIc_exists_central_involution {G : Type} [Group G] [Finite G] {Q R :
    Subgroup G}
    (hR : IsPGroup 2 R) (hQR : Q ≤ R) (hN : R ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Q ≠ ⊥) :
    ∃ i ∈ Q, i ^ 2 = 1 ∧ i ≠ 1 ∧ R ≤ Subgroup.centralizer ({i} : Set G) := by
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  haveI hnorm : (Q.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hne : Q.subgroupOf R ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hQR hx⟩ : R) ∈ Q.subgroupOf R := hx
    rw [h] at hx'
    have := Subgroup.mem_bot.1 hx'
    simpa using congrArg Subtype.val this
  have hz := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hz
  have haQ : ((a : R) : G) ∈ Q := a.2.1
  have haC : ((a : R) : G) ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.1 a.2.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  have ha1 : ((a : R) : G) ≠ 1 := by
    intro h
    apply ha
    ext
    simpa using h
  have hK : Q ⊓ Subgroup.centralizer (R : Set G) ≠ ⊥ := by
    intro h
    have : ((a : R) : G) ∈ Q ⊓ Subgroup.centralizer (R : Set G) := ⟨haQ, haC⟩
    rw [h] at this
    exact ha1 (Subgroup.mem_bot.1 this)
  obtain ⟨i, hi, hi2, hi1⟩ := burnsideIc_exists_involution
    (hR.to_le (inf_le_left.trans hQR)) hK
  refine ⟨i, hi.1, hi2, hi1, fun r hr => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (Subgroup.mem_centralizer_iff.1 hi.2 r hr).symm

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_mem_of_sylow_le_conjugate {G : Type} [Group G] [Finite G] {M T :
    Subgroup G}
    (hT : IsSylowTwoIn T M) (hN : Subgroup.normalizer (T : Set G) ≤ M) {g : G}
    (hg : T ≤ CFSG.conjugate M g) : g ∈ M := by
  have hT₂M : T.map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    exact burnsideIc_mem_conjugate.1 (hg ht)
  have hT₂p : IsPGroup 2 (T.map (MulAut.conj g).toMonoidHom) := hT.2.1.map _
  obtain ⟨m, hm, hmT⟩ := burnsideIc_exists_conj_le hT hT₂M hT₂p
  have hle : T.map (MulAut.conj (m * g)).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    have := hmT _ ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hcard : Nat.card T ≤ Nat.card (T.map (MulAut.conj (m * g)).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj (m * g)).injective).ge
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hn : m * g ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  have h3 := M.mul_mem (M.inv_mem hm) (hN hn)
  simpa using h3

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_core {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoIn T M) (hN : Subgroup.normalizer (T : Set G) ≤ M)
    (hC : ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M) :
    ∀ (n : ℕ) (Q : Subgroup G), Nat.card G - Nat.card Q = n → IsPGroup 2 Q → Q ≠ ⊥ → Q ≤ M →
      ∀ g : G, Q ≤ CFSG.conjugate M g → g ∈ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hn hQ hQ1 hQM g hQg
    by_cases hsyl : IsSylowTwoIn Q M
    · obtain ⟨m, hm, hmQ⟩ := burnsideIc_isSylowTwoIn_conj hT hsyl
      have hTg : T ≤ CFSG.conjugate M (g * m) := by
        intro t ht
        rw [burnsideIc_mem_conjugate]
        have h1 : m * t * m⁻¹ ∈ Q := (hmQ _).2 (by simpa [mul_assoc] using ht)
        have h2 := burnsideIc_mem_conjugate.1 (hQg h1)
        simpa [mul_assoc] using h2
      have h3 := M.mul_mem (burnsideIc_mem_of_sylow_le_conjugate hT hN hTg) (M.inv_mem hm)
      simpa using h3
    · obtain ⟨R, hR, hRM, hQR, hRN⟩ := burnsideIc_exists_larger hQ hQM hsyl
      obtain ⟨i, hiQ, hi2, hi1, hRi⟩ := burnsideIc_exists_central_involution hR hQR.le hRN hQ1
      have hiI : i ∈ M ⊓ CFSG.conjugate M g := ⟨hQM hiQ, hQg hiQ⟩
      have hcent := burnsideIc_centralizer_le_inf_conjugate hT hC hiI hi2 hi1
      have hRg : R ≤ CFSG.conjugate M g := fun r hr => (hcent (hRi hr)).2
      have h1 : Nat.card Q < Nat.card R := Subgroup.card_lt_of_lt hQR
      have h2 : Nat.card R ≤ Nat.card G := Subgroup.card_le_card_group R
      exact ih (Nat.card G - Nat.card R) (by omega) R rfl hR
        ((bot_lt_iff_ne_bot).1 (lt_of_le_of_lt bot_le hQR)) hRM g hRg

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_odd_of_three {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoIn T M) (hN : Subgroup.normalizer (T : Set G) ≤ M)
    (hC : ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M) :
    ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g)) := by
  intro g hg
  by_contra hodd
  obtain ⟨t, ht, ht2, ht1⟩ := burnsideIc_exists_involution_of_even
    (Nat.not_odd_iff_even.1 hodd)
  exact hg (burnsideIc_core hT hN hC _ (Subgroup.zpowers t) rfl
    (burnsideIc_isPGroup_zpowers ht2 ht1)
    (fun h => ht1 (by simpa using (Subgroup.zpowers_eq_bot).1 h)) (Subgroup.zpowers_le.2 ht.1) g
    (Subgroup.zpowers_le.2 ht.2))

private theorem burnsideIc_mem_of_two_group_le_inter {G : Type} [Group G] [Finite G] {M Q :
    Subgroup G}
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g)))
    (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) {g : G} (hle : Q ≤ M ⊓ CFSG.conjugate M g) : g ∈ M := by
  by_contra hg
  exact (Nat.not_even_iff_odd.2 (h2 g hg)) (burnsideIc_even_card_of_le hQ hQ1 hle)

private theorem burnsideIc_mem_of_involution_mem_inter {G : Type} [Group G] [Finite G] {M :
    Subgroup G}
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g)))
    {g i : G} (hi : i ∈ M ⊓ CFSG.conjugate M g) (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1) : g ∈ M :=
  burnsideIc_mem_of_two_group_le_inter h2 (burnsideIc_isPGroup_zpowers hi2 hi1)
    (fun h => hi1 (by simpa using (Subgroup.zpowers_eq_bot).1 h)) (Subgroup.zpowers_le.2 hi)

private theorem burnsideIc_normalizer_le_of_odd {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g)))
    (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (hQM : Q ≤ M) : Subgroup.normalizer (Q : Set G) ≤ M := by
  intro n hn
  refine burnsideIc_mem_of_two_group_le_inter h2 hQ hQ1 (le_inf hQM fun q hq => ?_)
  rw [burnsideIc_mem_conjugate]
  exact hQM ((Subgroup.mem_normalizer_iff.1 hn q).1 hq)

private theorem burnsideIc_centralizer_le_normalizer_zpowers {G : Type} [Group G] (i : G) :
    Subgroup.centralizer ({i} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers i : Subgroup G) : Set G) := by
  intro c hc
  have : c ∈ Subgroup.centralizer ((Subgroup.zpowers i : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hc
  exact Subgroup.centralizer_le_normalizer _ this

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_ne_bot_of_even {G : Type} [Group G] {M T : Subgroup G}
    (hE : Even (Nat.card M)) (hT : IsSylowTwoIn T M) : T ≠ ⊥ := by
  rintro rfl
  apply hT.2.2
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact even_iff_two_dvd.1 hE

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_three_of_odd {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hE : Even (Nat.card M)) (hT : IsSylowTwoIn T M)
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) :
    Subgroup.normalizer (T : Set G) ≤ M ∧
      ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M := by
  refine ⟨burnsideIc_normalizer_le_of_odd h2 hT.2.1 (burnsideIc_ne_bot_of_even hE hT) hT.1,
    fun i hi hi2 hi1 => ?_⟩
  exact (burnsideIc_centralizer_le_normalizer_zpowers i).trans
    (burnsideIc_normalizer_le_of_odd h2 (burnsideIc_isPGroup_zpowers hi2 hi1)
      (fun h => hi1 (by simpa using (Subgroup.zpowers_eq_bot).1 h))
      ((Subgroup.zpowers_le.2 hi).trans hT.1))

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_stronglyEmbedded_of_odd {G : Type} [Group G] [Finite G] {M T :
    Subgroup G}
    (hM : M ≠ ⊤) (hE : Even (Nat.card M)) (hT : IsSylowTwoIn T M)
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g))) :
    IsStronglyEmbeddedGLS M :=
  ⟨hM, hE, T, hT, fun _ hQT hQ1 =>
    burnsideIc_normalizer_le_of_odd h2 (hT.2.1.to_le hQT) hQ1 (hQT.trans hT.1)⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_normalizer_le_of_stronglyEmbedded {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (h1 : IsStronglyEmbeddedGLS M) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) (hQM : Q ≤ M) : Subgroup.normalizer (Q : Set G) ≤ M := by
  obtain ⟨-, -, T', hT', hN'⟩ := h1
  obtain ⟨m, hm, hmT⟩ := burnsideIc_exists_conj_le hT' hQM hQ
  have hQ'T : Q.map (MulAut.conj m).toMonoidHom ≤ T' := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hmT q hq
  have hQ'1 : Q.map (MulAut.conj m).toMonoidHom ≠ ⊥ := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ1
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨m * x * m⁻¹, ⟨x, x.2, rfl⟩⟩, ?_⟩
    intro h
    apply hx
    ext
    exact conj_eq_one_iff.1 (congrArg Subtype.val h)
  have hN := hN' _ hQ'T hQ'1
  intro n hn
  have hconj : (Q.map (MulAut.conj m).toMonoidHom).map (MulAut.conj (m * n * m⁻¹)).toMonoidHom =
      Q.map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj (m * n * m⁻¹)).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
        (MulAut.conj m).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, (burnsideIc_map_conj_eq_iff Q n).2 hn]
  have h3 := hN ((burnsideIc_map_conj_eq_iff _ _).1 hconj)
  have h4 := M.mul_mem (M.mul_mem (M.inv_mem hm) h3) hm
  simpa [mul_assoc] using h4

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_three_of_stronglyEmbedded {G : Type} [Group G] [Finite G] {M T :
    Subgroup G}
    (hE : Even (Nat.card M)) (hT : IsSylowTwoIn T M) (h1 : IsStronglyEmbeddedGLS M) :
    Subgroup.normalizer (T : Set G) ≤ M ∧
      ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M := by
  refine ⟨burnsideIc_normalizer_le_of_stronglyEmbedded h1 hT.2.1 (burnsideIc_ne_bot_of_even hE hT)
    hT.1, fun i hi hi2 hi1 => ?_⟩
  exact (burnsideIc_centralizer_le_normalizer_zpowers i).trans
    (burnsideIc_normalizer_le_of_stronglyEmbedded h1 (burnsideIc_isPGroup_zpowers hi2 hi1)
      (fun h => hi1 (by simpa using (Subgroup.zpowers_eq_bot).1 h))
      ((Subgroup.zpowers_le.2 hi).trans hT.1))

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_isSylowTwoIn_top {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoIn T M) (hN : Subgroup.normalizer (T : Set G) ≤ M) : IsSylowTwoIn T ⊤ := by
  obtain ⟨P, hP, hTP⟩ := burnsideIc_exists_isSylowTwoIn_ge (M := ⊤) hT.2.1 le_top
  by_cases hEq : T = P
  · rw [hEq]
    exact hP
  · exfalso
    have hlt : T < P := lt_of_le_of_ne hTP hEq
    obtain ⟨Y, hTY, hYP, hYN, hY2⟩ := burnsideIc_exists_normalizing_gt hP.2.1 hlt
    obtain ⟨m, hm, hmT⟩ := burnsideIc_exists_conj_le hT (hYN.trans hN) hY2
    have hle : Y.map (MulAut.conj m).toMonoidHom ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hmT y hy
    have h1 : Nat.card Y ≤ Nat.card T := by
      have := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective (MulAut.conj m).injective] at this
    have h2 : Nat.card T < Nat.card Y := Subgroup.card_lt_of_lt hTY
    omega

private theorem burnsideIc_fixed_unique {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (h2 : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ CFSG.conjugate M g)))
    {t : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) {x y : G ⧸ M} (hx : t • x = x) (hy : t • y = y) :
    x = y := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have hxa : a⁻¹ * t * a ∈ M := by
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at hx
    simpa [hinv, mul_assoc] using hx
  have hyb : b⁻¹ * t * b ∈ M := by
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at hy
    simpa [hinv, mul_assoc] using hy
  obtain ⟨hi2, hi1⟩ := burnsideIc_conj_involution a⁻¹ ht2 ht1
  have hi2' : (a⁻¹ * t * a) ^ 2 = 1 := by simpa using hi2
  have hi1' : a⁻¹ * t * a ≠ 1 := by simpa using hi1
  have hconj : a⁻¹ * t * a ∈ CFSG.conjugate M (a⁻¹ * b)⁻¹ := by
    rw [burnsideIc_mem_conjugate]
    simpa [mul_assoc] using hyb
  have hmem : (a⁻¹ * b)⁻¹ ∈ M :=
    burnsideIc_mem_of_involution_mem_inter h2 ⟨hxa, hconj⟩ hi2' hi1'
  rw [QuotientGroup.eq]
  simpa using M.inv_mem hmem

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_four_of_three {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoIn T M) (hN : Subgroup.normalizer (T : Set G) ≤ M)
    (hC : ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M) :
    ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∃! x : G ⧸ M, t • x = x := by
  intro t ht2 ht1
  have h2 := burnsideIc_odd_of_three hT hN hC
  have hTtop := burnsideIc_isSylowTwoIn_top hT hN
  obtain ⟨h, -, hh⟩ := burnsideIc_exists_conj_le hTtop le_top
    (burnsideIc_isPGroup_zpowers ht2 ht1)
  have hhT : h * t * h⁻¹ ∈ T := hh t (Subgroup.mem_zpowers t)
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  refine ⟨((h⁻¹ : G) : G ⧸ M), ?_, fun y hy => ?_⟩
  · show t • ((h⁻¹ : G) : G ⧸ M) = ((h⁻¹ : G) : G ⧸ M)
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    have := hT.1 hhT
    simpa [hinv, mul_assoc] using this
  · refine burnsideIc_fixed_unique h2 ht2 ht1 hy ?_
    show t • ((h⁻¹ : G) : G ⧸ M) = ((h⁻¹ : G) : G ⧸ M)
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    have := hT.1 hhT
    simpa [hinv, mul_assoc] using this

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_three_of_four {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hE : Even (Nat.card M)) (hT : IsSylowTwoIn T M)
    (h4 : ∀ t : G, t ^ 2 = 1 → t ≠ 1 → ∃! x : G ⧸ M, t • x = x) :
    Subgroup.normalizer (T : Set G) ≤ M ∧
      ∀ i ∈ T, i ^ 2 = 1 → i ≠ 1 → Subgroup.centralizer ({i} : Set G) ≤ M := by
  obtain ⟨i₀, hi₀T, hi₀2, hi₀1⟩ :=
    burnsideIc_exists_involution hT.2.1 (burnsideIc_ne_bot_of_even hE hT)
  have key : ∀ i ∈ M, i ^ 2 = 1 → i ≠ 1 → ∀ c : G, i • (c : G ⧸ M) = (c : G ⧸ M) → c ∈ M := by
    intro i hiM hi2 hi1 c hc
    obtain ⟨x, -, hx⟩ := h4 i hi2 hi1
    have h1 : (c : G ⧸ M) = x := hx _ hc
    have h2 : ((1 : G) : G ⧸ M) = x := by
      refine hx _ ?_
      show i • ((1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M)
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
      simpa using M.inv_mem hiM
    have h3 := h1.trans h2.symm
    rw [QuotientGroup.eq] at h3
    simpa using M.inv_mem h3
  refine ⟨fun n hn => ?_, fun i hiT hi2 hi1 c hc => ?_⟩
  · refine key i₀ (hT.1 hi₀T) hi₀2 hi₀1 n ?_
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    have h1 := (Subgroup.mem_normalizer_iff''.1 hn _).1 (T.inv_mem hi₀T)
    have h2 := hT.1 h1
    simpa [mul_assoc] using h2
  · refine key i (hT.1 hiT) hi2 hi1 c ?_
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    have hci : i * c = c * i := Subgroup.mem_centralizer_iff.1 hc i (Set.mem_singleton i)
    have : (i • c)⁻¹ * c = i⁻¹ := by
      rw [smul_eq_mul, hci, mul_inv_rev]
      group
    rw [this]
    exact M.inv_mem (hT.1 hiT)

end BurnsideIc

theorem as_I_8_1 : I_8_1 := by
  intro G _ _ M T hM hE hT
  refine ⟨⟨fun h1 => burnsideIc_odd_of_three hT (burnsideIc_three_of_stronglyEmbedded hE hT h1).1
      (burnsideIc_three_of_stronglyEmbedded hE hT h1).2,
    burnsideIc_stronglyEmbedded_of_odd hM hE hT⟩,
    ⟨burnsideIc_three_of_odd hE hT, fun h3 => burnsideIc_odd_of_three hT h3.1 h3.2⟩,
    ⟨fun h3 => burnsideIc_four_of_three hT h3.1 h3.2, burnsideIc_three_of_four hE hT⟩⟩

@[expose] def I_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTightlyEmbedded K → ¬ K.Normal →
    (∀ g : G, CFSG.conjugate K g ≠ K →
      Odd (Nat.card ↥(CFSG.conjugate K g ⊓ Subgroup.normalizer (K : Set G)))) →
    (CFSG.pRank 2 ↥(involutionNormalClosure K) = 1 ∧
      ∃ z ∈ K, z ^ 2 = 1 ∧ z ≠ 1 ∧
        involutionNormalClosure K =
          (CFSG.oddCore ↥(involutionNormalClosure K)).map (involutionNormalClosure K).subtype ⊔
            Subgroup.zpowers z) ∨
    (IsBenderGroup (↥(involutionNormalClosure K) ⧸ CFSG.oddCore ↥(involutionNormalClosure K)) ∧
      (CFSG.oddCore ↥(involutionNormalClosure K)).map (involutionNormalClosure K).subtype ≤
        Subgroup.normalizer (K : Set G) ∧
      IsBorelSubgroupTwo
        (((Subgroup.normalizer (K : Set G)).subgroupOf (involutionNormalClosure K)).map
          (QuotientGroup.mk' (CFSG.oddCore ↥(involutionNormalClosure K)))))


@[expose] def I_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoIn T ⊤ →
    ∀ V : Subgroup G, IsElemAbelian 2 V → IsTISubgroup V →
      CFSG.IsStronglyClosedIn T (V : Set G) → 0 < CFSG.pRank 2 ↥V → ¬ V.Normal →
        (CFSG.pRank 2 ↥V = 1 ∧
          conjClosure V ⊤ =
            (CFSG.oddCore ↥(conjClosure V ⊤)).map (conjClosure V ⊤).subtype ⊔ V) ∨
        (1 < CFSG.pRank 2 ↥V ∧ CFSG.IsQuasisimple ↥(conjClosure V ⊤) ∧
          (StatedClassicalModel ↥(conjClosure V ⊤) .PSL 2 2 (CFSG.pRank 2 ↥V) ∨
            SuzukiModel ↥(conjClosure V ⊤) 2 (CFSG.pRank 2 ↥V) ∨
            StatedClassicalModel ↥(conjClosure V ⊤) .PSU 3 2 (CFSG.pRank 2 ↥V) ∨
            IsSU3Group (2 ^ CFSG.pRank 2 ↥V) ↥(conjClosure V ⊤)) ∧
          V = omegaOne (T ⊓ conjClosure V ⊤))


@[expose] def I_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoIn T ⊤ →
    ∀ V : Subgroup G, (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) → CFSG.IsStronglyClosedIn T (V : Set G) →
      ControlsFusionOfElements (Subgroup.normalizer (V : Set G)) V ∧
      (IsTISubgroup V ↔
        ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (V : Set G))

theorem as_I_8_4 : I_8_4 := by
  intro G _ _ T hT V hab hcl
  obtain ⟨S, rfl⟩ := burnsideIc_exists_sylow_of_top hT
  have hVS : (V : Set G) ⊆ (S : Subgroup G) := hcl.1
  have hVS' : V ≤ (S : Subgroup G) := hVS
  have hcl' : CFSG.Open.fusionStronglyClosed (V : Set G) (S : Subgroup G) := hcl.2
  haveI hcomm : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  refine ⟨?_, ?_⟩
  · intro x hx g hg
    have hxS : x ∈ (S : Subgroup G) := hVS' hx
    have hgS : g⁻¹ * x * g ∈ (S : Subgroup G) := hVS' hg
    obtain ⟨n, hn, hng⟩ := CFSG.Goldschmidt.N4b G S V (Subgroup.zpowers x) g hVS' hcomm hcl'
      (Subgroup.zpowers_le.2 hxS)
      (by
        rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        simpa [MulAut.conj_apply] using hgS)
    exact ⟨n, hn, hng x (Subgroup.mem_zpowers x)⟩
  · rw [burnsideIc_isTISubgroup_iff]
    exact CFSG.Goldschmidt.isTI_iff_centralizer_le_normalizer S hVS' hcl' hcomm

@[expose] def I_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), M ≠ ⊤ → V ≠ ⊥ → V ≤ M →
    IsNormalIn V M → IsElemAbelian 2 V →
    (∀ v ∈ V, v ≠ 1 → ∃! x : G ⧸ M, v • x = x) →
      ((Nat.card ↥V = 2 ∧
          conjClosure V ⊤ =
            (CFSG.oddCore ↥(conjClosure V ⊤)).map (conjClosure V ⊤).subtype ⊔ V) ∨
        (CFSG.IsQuasisimple ↥(conjClosure V ⊤) ∧
          IsBenderGroup (↥(conjClosure V ⊤) ⧸ Subgroup.center ↥(conjClosure V ⊤)) ∧
          (∃ TL : Subgroup G, IsSylowTwoIn TL (conjClosure V ⊤) ∧ V = omegaOne TL) ∧
          M ⊓ conjClosure V ⊤ = conjClosure V ⊤ ⊓ Subgroup.normalizer (V : Set G) ∧
          ∃ S : Subgroup G, IsSylowTwoIn S (conjClosure V ⊤) ∧
            M ⊓ conjClosure V ⊤ = conjClosure V ⊤ ⊓ Subgroup.normalizer (S : Set G))) ∧
      (∃ (_ : ((Subgroup.centralizer (V : Set G)).subgroupOf M).Normal),
        Group.IsSolvable (↥M ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf M))


end CFSG.ASVolI
