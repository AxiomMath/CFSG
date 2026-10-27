module

public import CFSG.Quasithin.EmptyFaithful.S152XA5
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.S152X

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

@[expose] noncomputable def piS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    ↥H →* Equiv.Perm (Fin 5) :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

theorem piS5_surj (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    Function.Surjective (piS5 H φ) :=
  φ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piS5_ker (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    (piS5 H φ).ker = CFSG.Open.pCore 2 ↥H := by
  ext x
  simp [piS5]

@[expose] noncomputable def k0S5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) : Subgroup ↥H :=
  (alternatingGroup (Fin 5)).comap (piS5 H φ)

@[expose] noncomputable def kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) : Subgroup G :=
  (k0S5 H φ).map H.subtype

theorem kS5_le (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) : kS5 H φ ≤ H :=
  Subgroup.map_subtype_le _

theorem kS5_subgroupOf (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    (kS5 H φ).subgroupOf H = k0S5 H φ :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem mem_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) {x : G} :
    x ∈ kS5 H φ ↔ ∃ hx : x ∈ H, piS5 H φ ⟨x, hx⟩ ∈ alternatingGroup (Fin 5) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem normal_k0S5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    (k0S5 H φ).Normal :=
  Subgroup.normal_comap _

theorem le_normalizer_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    H ≤ Subgroup.normalizer (kS5 H φ : Set G) := by
  have : ((kS5 H φ).subgroupOf H).Normal := by
    rw [kS5_subgroupOf]
    exact normal_k0S5 H φ
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (kS5_le H φ)).1 this

theorem pCoreOf_le_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    pCoreOf 2 H ≤ kS5 H φ := by
  rintro _ ⟨y, hy, rfl⟩
  refine (mem_kS5 H φ).2 ⟨y.2, ?_⟩
  have : piS5 H φ y = 1 := by
    rw [← MonoidHom.mem_ker, piS5_ker]
    exact hy
  simpa using this ▸ (alternatingGroup (Fin 5)).one_mem

theorem relIndex_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    (kS5 H φ).relIndex H = 2 := by
  rw [Subgroup.relIndex, kS5_subgroupOf, k0S5, Subgroup.index_comap_of_surjective _ (piS5_surj H φ)]
  exact alternatingGroup.index_eq_two


theorem eq_bot_of_normal_isPGroup {N : Subgroup A5G} [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup A5G := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at hN
    have hp : IsPGroup 2 A5G := hN.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [card_A5G] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

@[expose] noncomputable def psiS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    ↥(kS5 H φ) →* A5G :=
  ((piS5 H φ).comp (Subgroup.inclusion (kS5_le H φ))).codRestrict (alternatingGroup (Fin 5))
    (fun x => by
      obtain ⟨hx, h⟩ := (mem_kS5 H φ).1 x.2
      exact h)

theorem psiS5_coe (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) (x : ↥(kS5 H φ)) :
    ((psiS5 H φ x : A5G) : Equiv.Perm (Fin 5)) = piS5 H φ (Subgroup.inclusion (kS5_le H φ) x) :=
  rfl

theorem psiS5_surj (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    Function.Surjective (psiS5 H φ) := by
  intro a
  obtain ⟨y, hy⟩ := piS5_surj H φ a.1
  refine ⟨⟨y.1, (mem_kS5 H φ).2 ⟨y.2, by simp [hy]⟩⟩, Subtype.ext ?_⟩
  rw [psiS5_coe]
  exact hy

theorem mem_ker_psiS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) (x : ↥(kS5 H φ)) :
    x ∈ (psiS5 H φ).ker ↔ piS5 H φ (Subgroup.inclusion (kS5_le H φ) x) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (fun a : A5G => (a : Equiv.Perm (Fin 5))) h
    simpa [psiS5_coe] using this
  · intro h
    apply Subtype.ext
    rw [psiS5_coe, h]
    rfl


theorem psiS5_ker [Finite G] (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    (psiS5 H φ).ker = CFSG.Open.pCore 2 ↥(kS5 H φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    refine CFSG.LieType.BorelTits.le_pCore 2 (psiS5 H φ).normal_ker ?_
    intro x
    have hx : piS5 H φ (Subgroup.inclusion (kS5_le H φ) (x : ↥(kS5 H φ))) = 1 :=
      (mem_ker_psiS5 H φ _).1 x.2
    have hmem : Subgroup.inclusion (kS5_le H φ) (x : ↥(kS5 H φ)) ∈ CFSG.Open.pCore 2 ↥H := by
      rw [← piS5_ker]
      exact hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H)) ⟨_, hmem⟩
    refine ⟨k, ?_⟩
    have h1 : (Subgroup.inclusion (kS5_le H φ) ((x : ↥(kS5 H φ)))) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥H) => (y : ↥H)) hk
      simpa using this
    have h2 : ((x : ↥(kS5 H φ))) ^ 2 ^ k = 1 := by
      apply Subgroup.inclusion_injective (kS5_le H φ)
      rw [map_pow, map_one]
      exact h1
    exact Subtype.ext (by simpa using h2)
  · intro z hz
    have hn : (CFSG.Open.pCore 2 ↥(kS5 H φ)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hnorm : ((CFSG.Open.pCore 2 ↥(kS5 H φ)).map (psiS5 H φ)).Normal :=
      hn.map _ (psiS5_surj H φ)
    have hmap : (CFSG.Open.pCore 2 ↥(kS5 H φ)).map (psiS5 H φ) = ⊥ := by
      refine eq_bot_of_normal_isPGroup ?_
      exact (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
        IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥(kS5 H φ))).map _
    have hz' : psiS5 H φ z ∈ (CFSG.Open.pCore 2 ↥(kS5 H φ)).map (psiS5 H φ) := ⟨z, hz, rfl⟩
    rw [hmap] at hz'
    exact hz'


theorem mem_pCoreOf_iff_pi (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) {y : G}
    (hy : y ∈ H) : y ∈ pCoreOf 2 H ↔ piS5 H φ ⟨y, hy⟩ = 1 := by
  rw [← MonoidHom.mem_ker, piS5_ker]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = ⟨y, hy⟩ := Subtype.ext hzy
    rwa [this] at hz
  · intro h
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem inf_normalizer_subgroupOf' {X L : Subgroup G} (hXL : X ≤ L) :
    (L ⊓ Subgroup.normalizer (X : Set G)).subgroupOf L =
      Subgroup.normalizer ((X.subgroupOf L : Subgroup L) : Set L) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, hy⟩ z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hy z
  · intro hy
    refine ⟨y.2, Subgroup.mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · intro hz
      exact (hy ⟨z, hXL hz⟩).1 hz
    · intro hz
      have hzL : z ∈ L := by
        have h1 : y.1 * z * y.1⁻¹ ∈ L := hXL hz
        have h2 : y.1⁻¹ * (y.1 * z * y.1⁻¹) * y.1 ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem y.2) h1) y.2
        simpa [mul_assoc] using h2
      exact (hy ⟨z, hzL⟩).2 hz

section Sylow

variable [Finite G]

theorem nonempty_oTwoQuot_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    Nonempty (OTwoQuot (kS5 H φ) ≃* A5G) := by
  have e1 : (↥(kS5 H φ) ⧸ CFSG.Open.pCore 2 ↥(kS5 H φ)) ≃* (↥(kS5 H φ) ⧸ (psiS5 H φ).ker) :=
    QuotientGroup.quotientMulEquivOfEq (psiS5_ker H φ).symm
  exact ⟨e1.trans (QuotientGroup.quotientKerEquivOfSurjective _ (psiS5_surj H φ))⟩

theorem pCoreOf_kS5 (H : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) :
    pCoreOf 2 (kS5 H φ) = pCoreOf 2 H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (psiS5 H φ).ker := by rw [psiS5_ker]; exact hy
    exact (mem_pCoreOf_iff_pi H φ (kS5_le H φ y.2)).2 ((mem_ker_psiS5 H φ y).1 hy')
  · intro hx
    have hxH : x ∈ H := pCoreOf_le 2 H hx
    have hxK : x ∈ kS5 H φ := pCoreOf_le_kS5 H φ hx
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have h1 : (⟨x, hxK⟩ : ↥(kS5 H φ)) ∈ (psiS5 H φ).ker :=
      (mem_ker_psiS5 H φ _).2 ((mem_pCoreOf_iff_pi H φ hxH).1 hx)
    rw [psiS5_ker] at h1
    exact h1

theorem isSylowTwoOf_inf_kS5 {T : Subgroup G} {H : Subgroup G} (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5))
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (T ⊓ kS5 H φ) (kS5 H φ) :=
  A4.isSylowTwoOf_inf_normal hT (kS5_le H φ) (le_normalizer_kS5 H φ)

omit [Finite G] in
theorem not_le_kS5 {T : Subgroup G} {H : Subgroup G} (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5))
    (hT : IsSylowTwoOf T H) : ¬ T ≤ kS5 H φ := by
  intro hle
  have h1 : T.subgroupOf H ≤ k0S5 H φ := by
    rw [← kS5_subgroupOf]
    intro x hx
    exact hle hx
  have h2 := Subgroup.index_dvd_of_le h1
  have h3 : (k0S5 H φ).index = 2 := by
    have := relIndex_kS5 H φ
    rwa [Subgroup.relIndex, kS5_subgroupOf] at this
  rw [h3] at h2
  exact hT.2.2 h2

omit [Finite G] in
theorem sup_kS5_eq {T : Subgroup G} {H : Subgroup G} (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5))
    (hT : IsSylowTwoOf T H) : kS5 H φ ⊔ T = H := by
  apply le_antisymm (sup_le (kS5_le H φ) hT.1)
  have h3 : (k0S5 H φ).index = 2 := by
    have := relIndex_kS5 H φ
    rwa [Subgroup.relIndex, kS5_subgroupOf] at this
  set X : Subgroup ↥H := (kS5 H φ ⊔ T).subgroupOf H with hX
  have hle : k0S5 H φ ≤ X := by
    rw [← kS5_subgroupOf]
    intro x hx
    exact (le_sup_left : kS5 H φ ≤ kS5 H φ ⊔ T) hx
  have hmul := Subgroup.relIndex_mul_index hle
  rw [h3] at hmul
  have hdvd : X.index ∣ 2 := ⟨(k0S5 H φ).relIndex X, by rw [mul_comm]; exact hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · intro g hg
    have : X = ⊤ := Subgroup.index_eq_one.1 h1
    have hgX : (⟨g, hg⟩ : ↥H) ∈ X := by rw [this]; trivial
    exact hgX
  · exfalso
    rw [h2] at hmul
    have h1 : (k0S5 H φ).relIndex X = 1 := by omega
    have hXk : X ≤ k0S5 H φ := Subgroup.relIndex_eq_one.1 h1
    apply not_le_kS5 φ hT
    intro t ht
    have : (⟨t, hT.1 ht⟩ : ↥H) ∈ X := (le_sup_right : T ≤ kS5 H φ ⊔ T) ht
    have h4 := hXk this
    rw [← kS5_subgroupOf] at h4
    exact h4

theorem not_inf_le_pCoreOf {T : Subgroup G} {H : Subgroup G} (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5))
    (hT : IsSylowTwoOf T H) : ¬ T ⊓ kS5 H φ ≤ pCoreOf 2 H := by
  intro hle
  have hS := isSylowTwoOf_inf_kS5 φ hT
  have h1 : (T ⊓ kS5 H φ).subgroupOf (kS5 H φ) ≤ (psiS5 H φ).ker := by
    intro x hx
    rw [mem_ker_psiS5]
    exact (mem_pCoreOf_iff_pi H φ (kS5_le H φ x.2)).1 (hle hx)
  have h2 := Subgroup.index_dvd_of_le h1
  have h3 : (psiS5 H φ).ker.index = 60 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (psiS5_surj H φ), Subgroup.card_top, card_A5G]
  rw [h3] at h2
  exact hS.2.2 (dvd_trans (by norm_num) h2)

theorem relIndex_borel_kS5 {T : Subgroup G} {H : Subgroup G} (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5))
    (hT : IsSylowTwoOf T H) :
    (T ⊓ kS5 H φ).relIndex (kS5 H φ ⊓ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G)) = 3 := by
  have hS := isSylowTwoOf_inf_kS5 φ hT
  have hker : IsPGroup 2 (psiS5 H φ).ker := by
    rw [psiS5_ker]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h3 := relIndex_normalizer_of_surj (psiS5 H φ) (psiS5_surj H φ) hker
    (A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1) hS.2.2
  rw [← inf_normalizer_subgroupOf' hS.1] at h3
  rw [← h3]
  exact (Subgroup.relIndex_subgroupOf (inf_le_left :
    kS5 H φ ⊓ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G) ≤ kS5 H φ)).symm

end Sylow

end CFSG.Quasithin.S152X
