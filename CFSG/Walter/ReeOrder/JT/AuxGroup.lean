module

public import CFSG.Walter.ReeOrder.JT.Section7C
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.InvolvedQuotient
import CFSG.Walter.ReeOrder.JT.Section7E
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.Walter.JT

theorem mem_map_subtype_iff {X : Type*} [Group X] {H : Subgroup X} {K : Subgroup H} {x : X} :
    x ∈ K.map H.subtype ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : H) ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨⟨x, hx⟩, hxK, rfl⟩

theorem exists_mul_mem_normalizer_of_sylow {X : Type*} [Group X] [Finite X] {s : ℕ}
    [Fact s.Prime] {H : Subgroup X} (P : Sylow s H) {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    ∃ y ∈ H, y * g ∈
      Subgroup.normalizer ((((P : Subgroup H).map H.subtype : Subgroup X)) : Set X) := by
  classical
  set P₁ : Subgroup X := (P : Subgroup H).map H.subtype with hP₁
  have hP₁H : P₁ ≤ H := Subgroup.map_subtype_le _
  have hQle : P₁.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hP₁H hx)
  set Q : Subgroup H := (P₁.map (MulAut.conj g).toMonoidHom).subgroupOf H
  have hQcard : Nat.card Q = Nat.card (P : Subgroup H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective H.subtype_injective]
  let Q' : Sylow s H := Sylow.ofCard Q (by rw [hQcard, P.card_eq_multiplicity])
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H Q' P
  have hmemQ : ∀ z : H, z ∈ (P : Subgroup H) ↔ g⁻¹ * ((y : X)⁻¹ * z * y) * g ∈ P₁ := by
    intro z
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj y)⁻¹ z ∈ Q ↔ _
    rw [Subgroup.mem_subgroupOf]
    simp only [MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨x, hx, hxe⟩
      have : x = g⁻¹ * ((y : X)⁻¹ * z * y) * g := by
        rw [← hxe]
        simp [MulAut.conj_apply]
        group
      rw [← this]
      exact hx
    · intro h
      refine ⟨_, h, ?_⟩
      simp [MulAut.conj_apply]
      group
  have hP₁mem : ∀ z : H, (z : X) ∈ P₁ ↔ z ∈ (P : Subgroup H) := by
    intro z
    rw [hP₁, mem_map_subtype_iff]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨z.2, h⟩⟩
  have hyg : (y : X) * g ∈ Subgroup.normalizer (H : Set X) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer y.2) hg
  refine ⟨y, y.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hzH : (y : X) * g * x * ((y : X) * g)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hyg x).mp (hP₁H hx)
    have := (hP₁mem ⟨_, hzH⟩).mpr ((hmemQ ⟨_, hzH⟩).mpr (by
      have : g⁻¹ * ((y : X)⁻¹ * ((y : X) * g * x * ((y : X) * g)⁻¹) * y) * g = x := by group
      rw [this]
      exact hx))
    exact this
  · intro hx
    have hxH : x ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp hyg x).mpr (hP₁H hx)
      exact this
    have h1 := (hmemQ ⟨_, hP₁H hx⟩).mp ((hP₁mem ⟨_, hP₁H hx⟩).mp hx)
    have : g⁻¹ * ((y : X)⁻¹ * ((y : X) * g * x * ((y : X) * g)⁻¹) * y) * g = x := by group
    rw [this] at h1
    exact h1

theorem isSolvable_of_not_four_dvd {X : Type*} [Group X] [Finite X]
    (h4 : ¬ 4 ∣ Nat.card X) : Group.IsSolvable X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Sy.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra hk1
    apply h4
    have := Subgroup.card_subgroup_dvd_card (Sy : Subgroup X)
    rw [hk] at this
    exact (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans this
  have hScyc : IsCyclic (Sy : Subgroup X) := by
    interval_cases k
    · have : Subsingleton (Sy : Subgroup X) := by
        rw [← Finite.card_le_one_iff_subsingleton, hk, pow_zero]
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := 2) (by rw [hk, pow_one])
  obtain ⟨-, -, -, ⟨hKn, hKodd, hKidx, -⟩, -⟩ :=
    cyclic_sylow_normal_odd_complement Sy hScyc
  exact isSolvable_of_normal_odd (pPrimeCore 2 X) hKodd (a := k) (b := 0) (by
    rw [← Subgroup.index, hKidx, hk, pow_zero, mul_one])

theorem exists_sylow_normalized_of_coprime {X : Type*} [Group X] [Finite X] {q : ℕ}
    [Fact q.Prime] {T K : Subgroup X} (hT : IsPGroup q T)
    (hTK : T ≤ Subgroup.normalizer (K : Set X)) (hK : ¬ q ∣ Nat.card K) (s : ℕ)
    [Fact s.Prime] :
    ∃ P : Sylow s K,
      T ≤ Subgroup.normalizer ((((P : Subgroup K).map K.subtype : Subgroup X)) : Set X) := by
  classical
  let := conjAct T K hTK
  have hcard := hT.card_modEq_card_fixedPoints (Sylow s K)
  obtain ⟨P₀⟩ : Nonempty (Sylow s K) := inferInstance
  have hnd : ¬ q ∣ Nat.card (Sylow s K) := fun hq =>
    hK (hq.trans ((Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _)))
  have hfix : (MulAction.fixedPoints T (Sylow s K)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hnd
    have : Nat.card (MulAction.fixedPoints T (Sylow s K)) = 0 := by
      rw [hemp]; simp
    rw [this] at hcard
    exact Nat.modEq_zero_iff_dvd.mp hcard
  obtain ⟨P, hP⟩ := hfix
  refine ⟨P, fun t ht => ?_⟩
  have htP : ∀ u : T, ∀ z : K, z ∈ (P : Subgroup K) ↔ u⁻¹ • z ∈ (P : Subgroup K) := by
    intro u z
    have := congrArg (fun Q : Sylow s K => z ∈ (Q : Subgroup K)) (hP u)
    simp only [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    exact (Iff.of_eq this).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (⟨t, ht⟩ : T)⁻¹⁻¹ • z ∈ (P : Subgroup K) := by
      rwa [← htP]
    refine ⟨_, hz', ?_⟩
    simp only [inv_inv]
    rfl
  · rintro ⟨z, hz, hzx⟩
    have hxK : x ∈ K := by
      have : x = t⁻¹ * (z : X) * t := by
        rw [Subgroup.coe_subtype] at hzx
        rw [hzx]
        group
      rw [this]
      exact (Subgroup.mem_normalizer_iff''.mp (hTK ht) z).mp z.2
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    change (⟨x, hxK⟩ : K) ∈ (P : Subgroup K)
    rw [htP ⟨t, ht⟩⁻¹]
    have heq : (⟨t, ht⟩ : T)⁻¹⁻¹ • (⟨x, hxK⟩ : K) = z := by
      apply Subtype.ext
      rw [Subgroup.coe_subtype] at hzx
      change ((⟨t, ht⟩ : T)⁻¹⁻¹ : T) * x * (((⟨t, ht⟩ : T)⁻¹⁻¹ : T) : X)⁻¹ = z
      simp only [inv_inv]
      exact hzx.symm
    rw [heq]
    exact hz

theorem isInvolved_of_mulEquiv {X Y G : Type*} [Group X] [Group Y] [Group G]
    (hX : IsInvolved X G) (e : X ≃* Y) : IsInvolved Y G := by
  obtain ⟨K, L, hL, ⟨f⟩⟩ := hX
  exact ⟨K, L, hL, ⟨f.trans e⟩⟩

theorem isInvolved_of_glauberman {X G : Type*} [Group X] [Group G]
    (h : Glauberman.Involved X G) : IsInvolved X G := by
  obtain ⟨K, N, hN, hq⟩ := h
  exact ⟨K, N, hN, hq⟩

theorem glauberman_of_isInvolved {X G : Type*} [Group X] [Group G]
    (h : IsInvolved X G) : Glauberman.Involved X G := by
  obtain ⟨K, N, hN, hq⟩ := h
  exact ⟨K, N, hN, hq⟩

theorem isInvolved_of_injective
    {X G : Type*} [Group X] [Group G] (f : X →* G)
    (hf : Function.Injective f) : IsInvolved X G :=
  isInvolved_of_mulEquiv (isInvolved_of_glauberman (Glauberman.involved_of_subgroup f.range))
    (MonoidHom.ofInjective hf).symm

theorem isInvolved_of_mulEquiv_right {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (h : IsInvolved X Y) (e : Y ≃* Z) : IsInvolved X Z := by
  obtain ⟨K, L, hL, ⟨f⟩⟩ := h
  let e' : K ≃* K.map e.toMonoidHom := K.equivMapOfInjective e.toMonoidHom e.injective
  have hL' : (L.map e'.toMonoidHom).Normal := hL.map _ e'.surjective
  exact ⟨K.map e.toMonoidHom, L.map e'.toMonoidHom, hL',
    ⟨(QuotientGroup.congr L (L.map e'.toMonoidHom) e' rfl).symm.trans f⟩⟩

theorem IsInvolved.trans
    {X Y G : Type*} [Group X] [Group Y] [Group G] (hXY : IsInvolved X Y)
    (hYG : IsInvolved Y G) : IsInvolved X G := by
  obtain ⟨K, L, hL, ⟨f⟩⟩ := hYG
  have h1 : IsInvolved X (K ⧸ L) := isInvolved_of_mulEquiv_right hXY f.symm
  have h2 : Glauberman.Involved X K :=
    Glauberman.involved_of_involved_quotient L (glauberman_of_isInvolved h1)
  exact isInvolved_of_glauberman (Glauberman.involved_of_involved_subgroup h2)

end CFSG.Walter.JT
