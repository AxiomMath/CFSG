module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsMaxSubgroupIn (H N : Subgroup G) : Prop :=
  N < H ∧ ∀ K : Subgroup G, N < K → K ≤ H → K = H

@[expose] def maxOver (H X : Subgroup G) : Set (Subgroup G) :=
  {N | IsMaxSubgroupIn H N ∧ X ≤ N}

@[expose] def uFam (H X : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ H ∧ X < U ∧ (maxOver U X).ncard = 1}

@[expose] def uFamHat (H X : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ uFam H X ∧ ¬ U ≤ Subgroup.normalizer (X : Set G)}

@[expose] def IsMinParabolicOf (H P : Subgroup G) : Prop :=
  ∃ T : Subgroup G, IsSylowTwoOf T H ∧ P ∈ uFamHat H T

@[expose] def IsUniqueMaxOver (H T M : Subgroup G) : Prop :=
  maxOver H T = {M}

structure MinParabolic (H T M : Subgroup G) : Prop where
  isSylow : IsSylowTwoOf T H
  not_normal : ¬ H ≤ Subgroup.normalizer (T : Set G)
  uniqueMax : IsUniqueMaxOver H T M

@[expose] def kerIn (A B : Subgroup G) : Subgroup G where
  carrier := {x | ∀ b ∈ B, b * x * b⁻¹ ∈ A}
  one_mem' := fun b _ => by simp
  mul_mem' := fun {x y} hx hy b hb => by
    have := A.mul_mem (hx b hb) (hy b hb)
    simpa [mul_assoc] using this
  inv_mem' := fun {x} hx b hb => by
    have := A.inv_mem (hx b hb)
    simpa [mul_assoc] using this

@[expose] def twoResidual (H : Subgroup G) : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G) ∧ ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ N), N

@[expose] def twoPrimeResidual (H : Subgroup G) : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G) ∧ ¬ 2 ∣ N.relIndex H), N

@[expose] def uHat (H X : Subgroup G) : Subgroup G := ⨆ U ∈ uFamHat H X, U

theorem mem_kerIn {A B : Subgroup G} {x : G} : x ∈ kerIn A B ↔ ∀ b ∈ B, b * x * b⁻¹ ∈ A :=
  Iff.rfl

namespace B6

@[expose] def conjSub (g : G) : Subgroup G ≃o Subgroup G := (MulAut.conj g).mapSubgroup

theorem mem_conjSub {g x : G} {X : Subgroup G} : x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  show x ∈ X.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conjSub_eq_self {g : G} {X : Subgroup G} (h : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g X = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp h

theorem conjSub_mul (a b : G) (X : Subgroup G) : conjSub (a * b) X = conjSub a (conjSub b X) := by
  ext x
  simp only [mem_conjSub, mul_inv_rev, mul_assoc]

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext x
  simp [mem_conjSub]

theorem mem_normalizer_of_conjSub_le {g : G} {S : Subgroup G} (h1 : conjSub g S ≤ S)
    (h2 : conjSub g⁻¹ S ≤ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 (mem_conjSub.mpr (by simpa [mul_assoc] using hx))
  · intro hx
    exact h2 (mem_conjSub.mpr (by simpa [mul_assoc] using hx))

theorem mem_normalizer_of_forall_mem {g : G} {S : Subgroup G} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem exists_relIndex_eq_two_pow_of_isPGroup [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (D : Subgroup G) : ∃ n : ℕ, D.relIndex T = 2 ^ n := by
  have : (D.subgroupOf T).FiniteIndex := Subgroup.finiteIndex_of_finite
  exact hT.index (D.subgroupOf T)

theorem le_of_isPGroup_of_odd_relIndex [Finite G] {H N T : Subgroup G} (hTH : T ≤ H)
    (hT : IsPGroup 2 T) (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hodd : ¬ 2 ∣ N.relIndex H) : T ≤ N := by
  have hnorm : T ≤ Subgroup.normalizer (N : Set G) := hTH.trans hHN
  have h1 : N.relIndex (T ⊔ N) = N.relIndex T := relIndex_sup_eq_of_le_normalizer hnorm
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow_of_isPGroup hT N
  have h2 : N.relIndex (T ⊔ N) ∣ N.relIndex H := by
    rw [← Subgroup.relIndex_mul_relIndex N (T ⊔ N) H le_sup_right (sup_le hTH hNH)]
    exact dvd_mul_right _ _
  rw [h1, hn] at h2
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans h2)
  rw [hn0, pow_zero] at hn
  exact (Subgroup.relIndex_eq_one.mp hn)

theorem relIndex_inf_eq_relIndex_sup [Finite G] {T N : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N : Set G)) : (T ⊓ N).relIndex N = T.relIndex (T ⊔ N) := by
  have h1 := relIndex_sup_eq_of_le_normalizer hT
  have e1 : N.relIndex (T ⊔ N) * Nat.card ↥(N ⊓ (T ⊔ N)) = Nat.card ↥(T ⊔ N) :=
    Subgroup.relIndex_mul_card N (T ⊔ N)
  have e2 : T.relIndex (T ⊔ N) * Nat.card ↥(T ⊓ (T ⊔ N)) = Nat.card ↥(T ⊔ N) :=
    Subgroup.relIndex_mul_card T (T ⊔ N)
  have e3 : (T ⊓ N).relIndex T * Nat.card ↥((T ⊓ N) ⊓ T) = Nat.card ↥T :=
    Subgroup.relIndex_mul_card (T ⊓ N) T
  have e4 : (T ⊓ N).relIndex N * Nat.card ↥((T ⊓ N) ⊓ N) = Nat.card ↥N :=
    Subgroup.relIndex_mul_card (T ⊓ N) N
  have i1 : N ⊓ (T ⊔ N) = N := inf_eq_left.mpr le_sup_right
  have i2 : T ⊓ (T ⊔ N) = T := inf_eq_left.mpr le_sup_left
  have i3 : (T ⊓ N) ⊓ T = T ⊓ N := inf_eq_left.mpr inf_le_left
  have i4 : (T ⊓ N) ⊓ N = T ⊓ N := inf_eq_left.mpr inf_le_right
  rw [i1] at e1
  rw [i2] at e2
  rw [i3] at e3
  rw [i4] at e4
  have h2 : (T ⊓ N).relIndex T = N.relIndex T := Subgroup.inf_relIndex_left T N
  rw [h1] at e1
  rw [h2] at e3
  have ha : 0 < N.relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have ht : 0 < Nat.card ↥(T ⊓ N) := Nat.card_pos
  have key : (N.relIndex T * Nat.card ↥(T ⊓ N)) * (T ⊓ N).relIndex N =
      (N.relIndex T * Nat.card ↥(T ⊓ N)) * T.relIndex (T ⊔ N) := by
    calc (N.relIndex T * Nat.card ↥(T ⊓ N)) * (T ⊓ N).relIndex N
        = N.relIndex T * ((T ⊓ N).relIndex N * Nat.card ↥(T ⊓ N)) := by ring
      _ = N.relIndex T * Nat.card ↥N := by rw [e4]
      _ = Nat.card ↥(T ⊔ N) := e1
      _ = T.relIndex (T ⊔ N) * Nat.card ↥T := e2.symm
      _ = T.relIndex (T ⊔ N) * (N.relIndex T * Nat.card ↥(T ⊓ N)) := by rw [e3]
      _ = (N.relIndex T * Nat.card ↥(T ⊓ N)) * T.relIndex (T ⊔ N) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha ht) key

theorem exists_relIndex_eq_two_pow [Finite G] {K D : Subgroup G}
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    ∃ n : ℕ, K.relIndex D = 2 ^ n := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hDK
  have hp : IsPGroup 2 (D ⧸ K.subgroupOf D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hD d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

theorem exists_uniform_two_pow [Finite G] (N : Subgroup G) (S : Set G)
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k ∈ N) : ∃ k : ℕ, ∀ s ∈ S, s ^ 2 ^ k ∈ N := by
  have hex : ∀ s : G, ∃ k : ℕ, s ∈ S → s ^ 2 ^ k ∈ N := by
    intro s
    by_cases h : s ∈ S
    · obtain ⟨k, hk⟩ := hS s h
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose f hf using hex
  obtain ⟨k, hk⟩ := (Set.finite_range f).bddAbove
  refine ⟨k, fun s hs => ?_⟩
  have hle : f s ≤ k := hk ⟨s, rfl⟩
  have : s ^ 2 ^ k = (s ^ 2 ^ (f s)) ^ 2 ^ (k - f s) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [this]
  exact N.pow_mem (hf s hs) _

theorem pow_mem_of_relIndex_eq_two_pow [Finite G] {K D : Subgroup G}
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : K.relIndex D = 2 ^ n) :
    ∀ d ∈ D, d ^ 2 ^ n ∈ K := by
  intro d hd
  have := Subgroup.normal_subgroupOf_of_le_normalizer hDK
  have hcard : Nat.card (D ⧸ K.subgroupOf D) = 2 ^ n := hn
  have h1 : (((⟨d, hd⟩ : D)) : D ⧸ K.subgroupOf D) ^ Nat.card (D ⧸ K.subgroupOf D) = 1 :=
    pow_card_eq_one'
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem isTwoQuotient_of_sup_eq [Finite G] {C D T : Subgroup G} (hT : IsPGroup 2 T)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hsup : T ⊔ C = D) :
    ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C := by
  have hTD : T ≤ Subgroup.normalizer (C : Set G) := (le_sup_left.trans hsup.le).trans hDC
  have h1 : C.relIndex (T ⊔ C) = C.relIndex T := relIndex_sup_eq_of_le_normalizer hTD
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow_of_isPGroup hT C
  rw [hsup] at h1
  exact fun d hd => ⟨n, pow_mem_of_relIndex_eq_two_pow hDC (h1.trans hn) d hd⟩

theorem sup_eq_of_isTwoQuotient [Finite G] {C D S : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C)
    (hS : IsSylowTwoOf S D) : C ⊔ S = D := by
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow hDC h2
  have h1 : (C ⊔ S).relIndex D ∣ C.relIndex D := Subgroup.relIndex_dvd_of_le_left D le_sup_left
  have h2' : (C ⊔ S).relIndex D ∣ S.relIndex D := Subgroup.relIndex_dvd_of_le_left D le_sup_right
  have hodd : ¬ 2 ∣ (C ⊔ S).relIndex D := fun hd => hS.2.2 (hd.trans h2')
  rw [hn] at h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hm0 : m = 0 := by
    by_contra hne
    exact hodd (hm ▸ dvd_pow_self 2 hne)
  rw [hm0, pow_zero] at hm
  exact le_antisymm (sup_le hCD hS.1) (Subgroup.relIndex_eq_one.mp hm)

open scoped Pointwise

noncomputable def toSylow2 {T H : Subgroup G} (hT : IsSylowTwoOf T H) : Sylow 2 ↥H :=
  (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2

theorem toSylow2_coe {T H : Subgroup G} (hT : IsSylowTwoOf T H) :
    ((toSylow2 hT : Sylow 2 ↥H) : Subgroup ↥H) = T.subgroupOf H := by
  simp [toSylow2]

theorem isSylowTwoOf_exists_conj [Finite G] {H S T : Subgroup G} (hS : IsSylowTwoOf S H)
    (hT : IsSylowTwoOf T H) : ∃ g ∈ H, T = conjSub g S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (toSylow2 hS) (toSylow2 hT)
  refine ⟨g, g.2, ?_⟩
  have key := congrArg (fun P : Sylow 2 ↥H => (P : Subgroup ↥H)) hg
  simp only [Sylow.coe_subgroup_smul, toSylow2_coe] at key
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have hxH : x ∈ H := hT.1 hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ T.subgroupOf H := hx
    rw [← key, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply] using hmem
  · intro hx
    have hxH : x ∈ H := by
      have : g * (g⁻¹ * x * g) * g⁻¹ ∈ H := H.mul_mem (H.mul_mem g.2 (hS.1 hx)) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ MulAut.conj g • S.subgroupOf H := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply] using hx
    rw [key] at hmem
    exact hmem

theorem isSylowTwoOf_conjSub {H T : Subgroup G} (hT : IsSylowTwoOf T H) (g : G) :
    IsSylowTwoOf (conjSub g T) (conjSub g H) := by
  refine ⟨(conjSub g).le_iff_le.mpr hT.1, ?_, ?_⟩
  · exact hT.2.1.of_equiv (Subgroup.equivMapOfInjective T (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  · have h : ((conjSub g T).subgroupOf (conjSub g H)).index = (T.subgroupOf H).index :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) T H
        (MulAut.conj g).injective
    rw [h]
    exact hT.2.2

theorem isSylowTwoOf_mono {H K T : Subgroup G} (hT : IsSylowTwoOf T H) (hTK : T ≤ K) (hKH : K ≤ H) :
    IsSylowTwoOf T K := by
  refine ⟨hTK, hT.2.1, fun hd => hT.2.2 ?_⟩
  have h : T.relIndex K * K.relIndex H = T.relIndex H :=
    Subgroup.relIndex_mul_relIndex T K H hTK hKH
  exact hd.trans ⟨K.relIndex H, h.symm⟩

theorem isSylowTwoOf_inf_normal [Finite G] {H N T : Subgroup G} (hT : IsSylowTwoOf T H)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (T ⊓ N) N := by
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
  have h1 : (T ⊓ N).relIndex N = T.relIndex (T ⊔ N) :=
    relIndex_inf_eq_relIndex_sup (hT.1.trans hHN)
  have h2 : T.relIndex (T ⊔ N) * (T ⊔ N).relIndex H = T.relIndex H :=
    Subgroup.relIndex_mul_relIndex T (T ⊔ N) H le_sup_left (sup_le hT.1 hNH)
  intro hd
  apply hT.2.2
  have hd' : 2 ∣ T.relIndex (T ⊔ N) := h1 ▸ hd
  show 2 ∣ T.relIndex H
  rw [← h2]
  exact hd'.mul_right _

theorem frattini_two [Finite G] {H N S : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hS : IsSylowTwoOf S N) :
    H ≤ N ⊔ (H ⊓ Subgroup.normalizer (S : Set G)) := by
  intro h hh
  have hcN : conjSub h N = N := conjSub_eq_self (hHN hh)
  have hS' : IsSylowTwoOf (conjSub h S) N := by
    have := isSylowTwoOf_conjSub hS h
    rwa [hcN] at this
  obtain ⟨n, hn, hnS⟩ := isSylowTwoOf_exists_conj hS hS'
  have hmem : n⁻¹ * h ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have : conjSub (n⁻¹ * h) S = S := by
      rw [conjSub_mul, hnS, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    exact this
  have hh' : h = n * (n⁻¹ * h) := by group
  rw [hh']
  exact Subgroup.mul_mem_sup hn ⟨H.mul_mem (H.inv_mem (hNH hn)) hh, hmem⟩

theorem pCoreOf_two_le_of_isSylowTwoOf [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  have : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hle : CFSG.Open.pCore 2 ↥H ≤ ((toSylow2 hT : Sylow 2 ↥H) : Subgroup ↥H) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal (toSylow2 hT)
  rw [toSylow2_coe] at hle
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (hle hy)

theorem exists_isSylowTwoOf_ge [Finite G] {J X : Subgroup G} (hX : IsPGroup 2 X) (hXJ : X ≤ J) :
    ∃ S, IsSylowTwoOf S J ∧ X ≤ S := by
  have hX' : IsPGroup 2 (X.subgroupOf J) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXJ).symm
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  refine ⟨P.map J.subtype, ⟨Subgroup.map_subtype_le _, P.isPGroup'.map J.subtype, ?_⟩, ?_⟩
  · have : (P.map J.subtype : Subgroup G).subgroupOf J = (P : Subgroup ↥J) :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    rw [this]
    exact Sylow.not_dvd_index P
  · intro x hx
    exact ⟨⟨x, hXJ hx⟩, hP (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩

end B6

open B6

theorem isMaxSubgroupIn_lt {H N : Subgroup G} (h : IsMaxSubgroupIn H N) : N < H := h.1

theorem IsMaxSubgroupIn.le {H N : Subgroup G} (h : IsMaxSubgroupIn H N) : N ≤ H := h.1.le

theorem IsMaxSubgroupIn.eq_of_lt_of_le {H N K : Subgroup G} (h : IsMaxSubgroupIn H N)
    (hNK : N < K) (hKH : K ≤ H) : K = H := h.2 K hNK hKH

theorem exists_isMaxSubgroupIn [Finite G] {H X : Subgroup G} (h : X < H) :
    ∃ N, IsMaxSubgroupIn H N ∧ X ≤ N := by
  obtain ⟨N, hXN, hN⟩ :=
    (Set.toFinite {K : Subgroup G | X ≤ K ∧ K < H}).exists_le_maximal ⟨le_rfl, h⟩
  refine ⟨N, ⟨hN.1.2, fun K hNK hKH => ?_⟩, hXN⟩
  by_contra hne
  have hKH' : K < H := lt_of_le_of_ne hKH hne
  exact absurd (hN.2 ⟨hXN.trans hNK.le, hKH'⟩ hNK.le) (not_le_of_gt hNK)

theorem isUniqueMaxOver_iff {H T M : Subgroup G} :
    IsUniqueMaxOver H T M ↔
      IsMaxSubgroupIn H M ∧ T ≤ M ∧ ∀ N, IsMaxSubgroupIn H N → T ≤ N → N = M := by
  unfold IsUniqueMaxOver
  constructor
  · intro h
    have hM : M ∈ maxOver H T := by rw [h]; exact rfl
    exact ⟨hM.1, hM.2, fun N hN hTN => by
      have : N ∈ maxOver H T := ⟨hN, hTN⟩
      rw [h] at this
      exact this⟩
  · rintro ⟨hM, hTM, hu⟩
    ext N
    constructor
    · intro hN
      exact hu N hN.1 hN.2
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨hM, hTM⟩

theorem maxOver_ncard_eq_one_iff {H X : Subgroup G} :
    (maxOver H X).ncard = 1 ↔ ∃ M, IsUniqueMaxOver H X M := Set.ncard_eq_one

theorem uFam_mono {K H X : Subgroup G} (hKH : K ≤ H) : uFam K X ⊆ uFam H X :=
  fun _ hU => ⟨hU.1.trans hKH, hU.2⟩

theorem mcBride [Finite G] : ∀ {H X : Subgroup G}, X < H → ⨆ U ∈ uFam H X, U = H := by
  intro H
  induction H using WellFoundedLT.induction with
  | _ H ih =>
    intro X hXH
    refine le_antisymm (iSup₂_le fun U hU => hU.1) ?_
    by_cases hone : (maxOver H X).ncard = 1
    · exact le_iSup₂_of_le H ⟨le_rfl, hXH, hone⟩ le_rfl
    · obtain ⟨N₀, hN₀, hXN₀⟩ := exists_isMaxSubgroupIn hXH
      have hne : ∃ M ∈ maxOver H X, M ≠ N₀ := by
        by_contra hcon
        apply hone
        rw [Set.ncard_eq_one]
        refine ⟨N₀, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hN₀, hXN₀⟩, fun N hN => ?_⟩⟩
        by_contra hN'
        exact hcon ⟨N, hN, hN'⟩
      obtain ⟨M, hM, hMN⟩ := hne
      have hN : N₀ ∈ maxOver H X := ⟨hN₀, hXN₀⟩
      have hNM : ¬ N₀ ≤ M := by
        intro hle
        have h1 : N₀ < M := lt_of_le_of_ne hle (Ne.symm hMN)
        have := hN₀.eq_of_lt_of_le h1 hM.1.le
        exact absurd this (ne_of_lt hM.1.1)
      have hMsup : M ⊔ N₀ = H :=
        hM.1.eq_of_lt_of_le (lt_of_le_of_ne le_sup_left (fun h => hNM (h ▸ le_sup_right)))
          (sup_le hM.1.le hN₀.le)
      have hXM : X < M := by
        refine lt_of_le_of_ne hM.2 fun h => ?_
        have h1 : M ≤ N₀ := h ▸ hXN₀
        have h2 : M < N₀ := lt_of_le_of_ne h1 hMN
        have := hM.1.eq_of_lt_of_le h2 hN₀.le
        exact absurd this (ne_of_lt hN₀.1)
      have hXN : X < N₀ := by
        refine lt_of_le_of_ne hXN₀ fun h => ?_
        have h1 : N₀ ≤ M := h ▸ hM.2
        exact hNM h1
      have h1 := ih M hM.1.1 hXM
      have h2 := ih N₀ hN₀.1 hXN
      have hM' : M ≤ ⨆ U ∈ uFam H X, U := h1 ▸ iSup₂_mono' fun U hU => ⟨U, uFam_mono hM.1.le hU, le_rfl⟩
      have hN' : N₀ ≤ ⨆ U ∈ uFam H X, U :=
        h2 ▸ iSup₂_mono' fun U hU => ⟨U, uFam_mono hN₀.le hU, le_rfl⟩
      calc H = M ⊔ N₀ := hMsup.symm
        _ ≤ _ := sup_le hM' hN'

theorem isMaxSubgroupIn_conjSub {g : G} {H N : Subgroup G} :
    IsMaxSubgroupIn (conjSub g H) (conjSub g N) ↔ IsMaxSubgroupIn H N := by
  unfold IsMaxSubgroupIn
  refine and_congr (conjSub g).lt_iff_lt ?_
  constructor
  · intro h K hNK hKH
    have := h (conjSub g K) ((conjSub g).lt_iff_lt.mpr hNK) ((conjSub g).le_iff_le.mpr hKH)
    exact (conjSub g).injective this
  · intro h K hNK hKH
    obtain ⟨K', rfl⟩ := (conjSub g).surjective K
    rw [h K' ((conjSub g).lt_iff_lt.mp hNK) ((conjSub g).le_iff_le.mp hKH)]

theorem maxOver_conjSub {g : G} {U X : Subgroup G} :
    maxOver (conjSub g U) (conjSub g X) = conjSub g '' maxOver U X := by
  ext N
  constructor
  · rintro ⟨hN, hXN⟩
    obtain ⟨N', rfl⟩ := (conjSub g).surjective N
    exact ⟨N', ⟨isMaxSubgroupIn_conjSub.mp hN, (conjSub g).le_iff_le.mp hXN⟩, rfl⟩
  · rintro ⟨N', ⟨hN, hXN⟩, rfl⟩
    exact ⟨isMaxSubgroupIn_conjSub.mpr hN, (conjSub g).le_iff_le.mpr hXN⟩

theorem ncard_maxOver_conjSub {g : G} {U X : Subgroup G} :
    (maxOver (conjSub g U) (conjSub g X)).ncard = (maxOver U X).ncard := by
  rw [maxOver_conjSub]
  exact Set.ncard_image_of_injective _ (conjSub g).injective

theorem conjSub_mem_uFamHat {n : G} {H X U : Subgroup G} (hn : n ∈ H)
    (hnX : n ∈ Subgroup.normalizer (X : Set G)) (hU : U ∈ uFamHat H X) :
    conjSub n U ∈ uFamHat H X := by
  have hH : conjSub n H = H := conjSub_eq_self (Subgroup.le_normalizer hn)
  have hX : conjSub n X = X := conjSub_eq_self hnX
  obtain ⟨⟨hUH, hXU, hcard⟩, hnorm⟩ := hU
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hH]; exact (conjSub n).le_iff_le.mpr hUH
  · rw [← hX]; exact (conjSub n).lt_iff_lt.mpr hXU
  · rw [← hX, ncard_maxOver_conjSub]; exact hcard
  · intro hle
    apply hnorm
    intro u hu
    have h1 : n * u * n⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      hle (mem_conjSub.mpr (by simpa [mul_assoc] using hu))
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnX) h1) hnX
    simpa [mul_assoc] using h2

theorem uHat_le (H X : Subgroup G) : uHat H X ≤ H :=
  iSup₂_le fun _ hU => hU.1.1

theorem uFam_eq_empty_of_eq {H : Subgroup G} : uFam H H = ∅ := by
  ext U
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hUH, hHU, -⟩
  exact absurd hUH (not_le_of_gt hHU)

theorem conjSub_uHat_le {H X : Subgroup G} {m : G} (hm : m ∈ H)
    (hmX : m ∈ Subgroup.normalizer (X : Set G)) : conjSub m (uHat H X) ≤ uHat H X := by
  unfold uHat
  simp only [OrderIso.map_iSup]
  exact iSup_le fun U => iSup_le fun hU =>
    le_iSup₂_of_le (conjSub m U) (conjSub_mem_uFamHat hm hmX hU) le_rfl

theorem mem_normalizer_uHat {H X : Subgroup G} {n : G} (hn : n ∈ H)
    (hnX : n ∈ Subgroup.normalizer (X : Set G)) :
    n ∈ Subgroup.normalizer (uHat H X : Set G) :=
  mem_normalizer_of_conjSub_le (conjSub_uHat_le hn hnX)
    (conjSub_uHat_le (inv_mem hn) (inv_mem hnX))

theorem le_uHat_sup_normalizer [Finite G] {H X : Subgroup G} (hXH : X ≤ H) :
    H ≤ uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) := by
  rcases eq_or_lt_of_le hXH with h | h
  · subst h
    exact le_sup_of_le_right (le_inf le_rfl (Subgroup.le_normalizer))
  · calc H = ⨆ U ∈ uFam H X, U := (mcBride h).symm
      _ ≤ _ := by
        refine iSup₂_le fun U hU => ?_
        by_cases hnorm : U ≤ Subgroup.normalizer (X : Set G)
        · exact le_sup_of_le_right (le_inf hU.1 hnorm)
        · exact le_sup_of_le_left (le_iSup₂_of_le U ⟨hU, hnorm⟩ le_rfl)

theorem uHat_normal_and_eq_sup [Finite G] {H X : Subgroup G} (hXH : X ≤ H) :
    uHat H X ≤ H ∧ H ≤ Subgroup.normalizer (uHat H X : Set G) ∧
      H = uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) := by
  have hle := le_uHat_sup_normalizer hXH
  have hge : uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) ≤ H :=
    sup_le (uHat_le H X) inf_le_left
  refine ⟨uHat_le H X, fun h hh => ?_, le_antisymm hle hge⟩
  have hmem : h ∈ uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) := hle hh
  have hN : uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.normalizer (uHat H X : Set G) :=
    sup_le Subgroup.le_normalizer fun n hn => mem_normalizer_uHat hn.1 hn.2
  exact hN hmem

theorem uHat_eq_of_conjClosure_eq [Finite G] {H X : Subgroup G} (hXH : X ≤ H)
    (hlt : X < conjClosure X H) (hcl : conjClosure X H = H) : uHat H X = H := by
  obtain ⟨hHle, hnormal, hHeq⟩ := uHat_normal_and_eq_sup hXH
  refine le_antisymm (uHat_le H X) ?_
  have hXHat : X ≤ uHat H X := by
    by_contra hXn
    have hbot : uHat H X = ⊥ := by
      refine le_antisymm (iSup₂_le fun U hU => ?_) bot_le
      exfalso
      apply hXn
      exact le_iSup₂_of_le U hU hU.1.2.1.le
    have hHN : H ≤ Subgroup.normalizer (X : Set G) := by
      intro h hh
      have : h ∈ uHat H X ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) := hHeq ▸ hh
      rw [hbot, bot_sup_eq] at this
      exact this.2
    have : conjClosure X H ≤ X := conjClosure_le fun h hh z hz =>
      ((Subgroup.mem_normalizer_iff.mp (hHN hh) z).mp hz)
    exact absurd hlt (not_lt_of_ge this)
  calc H = conjClosure X H := hcl.symm
    _ ≤ uHat H X := conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hnormal hh) z).mp (hXHat hz)

theorem conjClosure_eq_twoPrimeResidual [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    conjClosure T H = twoPrimeResidual H := by
  obtain ⟨hTH, hT2, hTodd⟩ := hT
  apply le_antisymm
  · refine le_iInf fun N => le_iInf fun hN => conjClosure_le fun h hh z hz => ?_
    obtain ⟨hNH, hHN, hNodd⟩ := hN
    have hTN : T ≤ N := le_of_isPGroup_of_odd_relIndex hTH hT2 hNH hHN hNodd
    exact (Subgroup.mem_normalizer_iff.mp (hHN hh) z).mp (hTN hz)
  · have hC : conjClosure T H ≤ H :=
      conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hTH hz)) (H.inv_mem hh)
    refine iInf₂_le (conjClosure T H) ⟨hC, le_normalizer_conjClosure T H, ?_⟩
    intro hdvd
    exact hTodd (hdvd.trans (Subgroup.relIndex_dvd_of_le_left H (le_conjClosure T H)))

theorem generated_by_uFamHat [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) (hTH : T < H)
    (hH : twoPrimeResidual H = H) : ⨆ P ∈ uFamHat H T, P = H := by
  have hcl : conjClosure T H = H := by rw [conjClosure_eq_twoPrimeResidual hT, hH]
  exact uHat_eq_of_conjClosure_eq hT.1 (by rw [hcl]; exact hTH) hcl

theorem kerIn_le {A B : Subgroup G} : kerIn A B ≤ A := fun x hx => by
  simpa using hx 1 B.one_mem

theorem le_normalizer_kerIn (A B : Subgroup G) :
    B ≤ Subgroup.normalizer (kerIn A B : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx c hc
    have := hx (c * b) (B.mul_mem hc hb)
    simpa [mul_assoc] using this
  · intro hx c hc
    have := hx (c * b⁻¹) (B.mul_mem hc (B.inv_mem hb))
    simpa [mul_assoc] using this

theorem le_kerIn_of_le_normalizer {N A B : Subgroup G} (hNA : N ≤ A)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) : N ≤ kerIn A B := fun x hx _ hb =>
  hNA ((Subgroup.mem_normalizer_iff.mp (hBN hb) x).mp hx)

theorem mem_twoResidual_iff {H : Subgroup G} {x : G} :
    x ∈ twoResidual H ↔ ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) →
      (∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → x ∈ N := by
  unfold twoResidual
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h N h1 h2 h3
    exact h N ⟨h1, h2, h3⟩
  · intro h N hN
    exact h N hN.1 hN.2.1 hN.2.2

theorem twoResidual_le (H : Subgroup G) : twoResidual H ≤ H :=
  iInf₂_le H ⟨le_rfl, Subgroup.le_normalizer, fun x hx => ⟨0, by simpa using hx⟩⟩

theorem twoResidual_le_of_isTwoQuotient {H N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (h2 : ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N) :
    twoResidual H ≤ N :=
  iInf₂_le N ⟨hNH, hN, h2⟩

theorem le_normalizer_twoResidual (H : Subgroup G) :
    H ≤ Subgroup.normalizer (twoResidual H : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_twoResidual_iff] at hx ⊢
    intro N h1 h2 h3
    exact (Subgroup.mem_normalizer_iff.mp (h2 hg) x).mp (hx N h1 h2 h3)
  · rw [mem_twoResidual_iff] at hx ⊢
    intro N h1 h2 h3
    have := (Subgroup.mem_normalizer_iff.mp (h2 (H.inv_mem hg)) x).mp (hx N h1 h2 h3)
    simpa using this

theorem twoResidual_isTwoQuotient [Finite G] (H : Subgroup G) :
    ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ twoResidual H := by
  intro x hx
  have hex : ∀ N : Subgroup G, ∃ k : ℕ,
      (N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G) ∧ ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N) →
        x ^ 2 ^ k ∈ N := by
    intro N
    by_cases h : N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G) ∧ ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N
    · obtain ⟨k, hk⟩ := h.2.2 x hx
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose f hf using hex
  obtain ⟨k, hk⟩ := (Set.finite_range f).bddAbove
  refine ⟨k, ?_⟩
  rw [mem_twoResidual_iff]
  intro N h1 h2 h3
  have hfN : x ^ 2 ^ (f N) ∈ N := hf N ⟨h1, h2, h3⟩
  have hle : f N ≤ k := hk ⟨N, rfl⟩
  have : x ^ 2 ^ k = (x ^ 2 ^ (f N)) ^ 2 ^ (k - f N) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [this]
  exact N.pow_mem hfN _

theorem sup_twoResidual_eq [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    T ⊔ twoResidual H = H := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow (le_normalizer_twoResidual H)
    (twoResidual_isTwoQuotient H)
  have h1 : (T ⊔ twoResidual H).relIndex H ∣ (twoResidual H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (T ⊔ twoResidual H).relIndex H ∣ T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have hodd : ¬ 2 ∣ (T ⊔ twoResidual H).relIndex H := fun hd => hT.2.2 (hd.trans h2)
  rw [hn] at h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hm0 : m = 0 := by
    by_contra hne
    exact hodd (hm ▸ dvd_pow_self 2 hne)
  rw [hm0, pow_zero] at hm
  exact le_antisymm (sup_le hT.1 hKH) (Subgroup.relIndex_eq_one.mp hm)

theorem twoResidual_twoResidual [Finite G] (H : Subgroup G) :
    twoResidual (twoResidual H) = twoResidual H := by
  apply le_antisymm (twoResidual_le _)
  set K := twoResidual H with hK
  have hKH : K ≤ H := twoResidual_le H
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  refine le_iInf fun N => le_iInf fun hN => ?_
  obtain ⟨hNK, hKN, hKN2⟩ := hN
  have hcore : twoResidual H ≤ kerIn N H := by
    refine twoResidual_le_of_isTwoQuotient ((kerIn_le).trans (hNK.trans hKH))
      (le_normalizer_kerIn N H) ?_
    intro x hx
    obtain ⟨a, ha⟩ := twoResidual_isTwoQuotient H x hx
    obtain ⟨b, hb⟩ := exists_uniform_two_pow N {s | ∃ h ∈ H, s = h * x ^ 2 ^ a * h⁻¹}
      (by
        rintro _ ⟨h, hh, rfl⟩
        have hmem : h * x ^ 2 ^ a * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hh) _).mp ha
        exact hKN2 _ hmem)
    refine ⟨a + b, fun h hh => ?_⟩
    have := hb _ ⟨h, hh, rfl⟩
    rw [← conj_pow] at this
    simpa [pow_add, pow_mul] using this
  exact hcore.trans kerIn_le

theorem MinParabolic.maximal {H T M : Subgroup G} (h : MinParabolic H T M) : IsMaxSubgroupIn H M :=
  (isUniqueMaxOver_iff.mp h.uniqueMax).1

theorem MinParabolic.le {H T M : Subgroup G} (h : MinParabolic H T M) : T ≤ M :=
  (isUniqueMaxOver_iff.mp h.uniqueMax).2.1

theorem MinParabolic.eq_of_maximal {H T M N : Subgroup G} (h : MinParabolic H T M)
    (hN : IsMaxSubgroupIn H N) (hTN : T ≤ N) : N = M :=
  (isUniqueMaxOver_iff.mp h.uniqueMax).2.2 N hN hTN

theorem MinParabolic.lt {H T M : Subgroup G} (h : MinParabolic H T M) : T < H :=
  lt_of_le_of_lt h.le h.maximal.1

theorem minParabolic_iff [Finite G] {H T M : Subgroup G} :
    MinParabolic H T M ↔
      IsMinParabolicOf H H ∧ IsSylowTwoOf T H ∧ IsUniqueMaxOver H T M := by
  constructor
  · intro h
    refine ⟨⟨T, h.isSylow, ⟨le_rfl, h.lt, ?_⟩, h.not_normal⟩, h.isSylow, h.uniqueMax⟩
    have : maxOver H T = {M} := h.uniqueMax
    rw [this]
    exact Set.ncard_singleton M
  · rintro ⟨⟨T₀, hT₀, ⟨-, -, -⟩, hnorm⟩, hT, hM⟩
    refine ⟨hT, ?_, hM⟩
    obtain ⟨g, hg, rfl⟩ := isSylowTwoOf_exists_conj hT₀ hT
    intro hle
    apply hnorm
    intro x hx
    have hy : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    have hy' := Subgroup.mem_normalizer_iff.mp (hle hy)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := hy' (g * z * g⁻¹)
    rw [mem_conjSub, mem_conjSub] at this
    constructor
    · intro hz
      have h2 := this.mp (by simpa [mul_assoc] using hz)
      simpa [mul_assoc] using h2
    · intro hz
      have h2 := this.mpr (by simpa [mul_assoc] using hz)
      simpa [mul_assoc] using h2

end CFSG.Quasithin
