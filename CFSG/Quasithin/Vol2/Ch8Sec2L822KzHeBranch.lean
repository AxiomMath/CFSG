module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzHeCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G]

@[expose] noncomputable def kzF_kz2 {K X : Subgroup G} (hXK : X ≤ K) :
    ↥X →* (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hXK)

@[expose] noncomputable def kzImX_kz2 {K X : Subgroup G} (hXK : X ≤ K) : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (kzF_kz2 hXK).range

@[expose] noncomputable def kzImO_kz2 {K X : Subgroup G} (hXK : X ≤ K) : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  ((pCoreOf 2 X).subgroupOf X).map (kzF_kz2 hXK)

theorem kzImO_le_kzImX_kz2 {K X : Subgroup G} (hXK : X ≤ K) : kzImO_kz2 hXK ≤ kzImX_kz2 hXK :=
  Subgroup.map_le_range _ _

theorem preserve_kzImX_kz2 {K X : Subgroup G} (hXK : X ≤ K) {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (w : ↥K ⧸ CFSG.pCore 2 ↥K) (hw : w ∈ kzImX_kz2 hXK) :
    kzQmap_kz2 K t htK w ∈ kzImX_kz2 hXK := by
  obtain ⟨u, rfl⟩ := (MonoidHom.mem_range).mp hw
  have hX' : t * (u : G) * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htX (u : G)).mp u.2
  have key : kzQmap_kz2 K t htK ((kzF_kz2 hXK) u) = (kzF_kz2 hXK) ⟨t * (u : G) * t⁻¹, hX'⟩ := by
    rw [show (kzF_kz2 hXK) u = QuotientGroup.mk (Subgroup.inclusion hXK u) from rfl, kzQmap_mk_kz2]
    rfl
  exact MonoidHom.mem_range.mpr ⟨⟨t * (u : G) * t⁻¹, hX'⟩, key.symm⟩

theorem preserve_kzImO_kz2 {K X : Subgroup G} (hXK : X ≤ K) {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (htO : t ∈ Subgroup.normalizer (pCoreOf 2 X : Set G)) (w : ↥K ⧸ CFSG.pCore 2 ↥K)
    (hw : w ∈ kzImO_kz2 hXK) : kzQmap_kz2 K t htK w ∈ kzImO_kz2 hXK := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
  have hu' : (u : G) ∈ pCoreOf 2 X := Subgroup.mem_subgroupOf.mp hu
  have hX' : t * (u : G) * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htX (u : G)).mp u.2
  have hO' : t * (u : G) * t⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp htO (u : G)).mp hu'
  have key : kzQmap_kz2 K t htK ((kzF_kz2 hXK) u) = (kzF_kz2 hXK) ⟨t * (u : G) * t⁻¹, hX'⟩ := by
    rw [show (kzF_kz2 hXK) u = QuotientGroup.mk (Subgroup.inclusion hXK u) from rfl, kzQmap_mk_kz2]
    rfl
  refine Subgroup.mem_map.mpr ⟨⟨t * (u : G) * t⁻¹, hX'⟩, Subgroup.mem_subgroupOf.mpr hO', ?_⟩
  exact key.symm


theorem comm_le_pCoreOf_kz2 [Finite G] {X : Subgroup G} (hrel : (pCoreOf 2 X).relIndex X = 9) :
    ⁅X, X⁆ ≤ pCoreOf 2 X := by
  classical
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  set H₁ : Subgroup ↥X := (pCoreOf 2 X).subgroupOf X with hH₁
  haveI hH₁n : H₁.Normal := ⟨fun x hx g => by
    rw [hH₁, Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXN g.2) x).mp hx⟩
  have hcard : Nat.card (↥X ⧸ H₁) = 3 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcomm := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hcard
  have key : ∀ x y : ↥X, x⁻¹ * y⁻¹ * x * y ∈ H₁ := by
    intro x y
    have h := hcomm (QuotientGroup.mk y) (QuotientGroup.mk x)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
    have h2 := (QuotientGroup.eq).mp h
    have e : (y * x)⁻¹ * (x * y) = x⁻¹ * y⁻¹ * x * y := by group
    rw [e] at h2
    exact h2
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hk := key ⟨a⁻¹, X.inv_mem ha⟩ ⟨b⁻¹, X.inv_mem hb⟩
  rw [hH₁, Subgroup.mem_subgroupOf] at hk
  rw [commutatorElement_def]
  simpa [mul_assoc] using hk

theorem relIndex_kzIm_kz2 [Finite G] {K X : Subgroup G} (hXK : X ≤ K)
    (hrel : (pCoreOf 2 X).relIndex X = 9) :
    (kzImO_kz2 hXK).relIndex (kzImX_kz2 hXK) = 9 := by
  classical
  set H₁ : Subgroup ↥X := (pCoreOf 2 X).subgroupOf X with hH₁
  have hker : (kzF_kz2 hXK).ker ≤ H₁ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : Subgroup.inclusion hXK x ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp hx
    have hxK : (x : G) ∈ pCoreOf 2 K := (mem_pCore_iff_kz2 _).mp hxN
    have hRn : ((pCoreOf 2 K ⊓ X).subgroupOf X).Normal := ⟨fun r hr g => by
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      have hgK : (g : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hXK g.2)
      have hgN : (g : G) ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 K hgK
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgN (r : G)).mp hr.1,
        X.mul_mem (X.mul_mem g.2 hr.2) (X.inv_mem g.2)⟩⟩
    have hR : pCoreOf 2 K ⊓ X ≤ pCoreOf 2 X :=
      le_pCoreOf 2 inf_le_right hRn ((pCoreOf_isPGroup 2 K).to_le inf_le_left)
    exact Subgroup.mem_subgroupOf.mpr (hR ⟨hxK, x.2⟩)
  have h1 : (H₁.map (kzF_kz2 hXK)).index = (H₁ ⊔ (kzF_kz2 hXK).ker).index * (kzF_kz2 hXK).range.index :=
    Subgroup.index_map H₁ (kzF_kz2 hXK)
  rw [sup_eq_left.mpr hker] at h1
  have h2 := Subgroup.relIndex_mul_index (kzImO_le_kzImX_kz2 hXK)
  have hH : H₁.index = 9 := hrel
  have key : (kzImO_kz2 hXK).relIndex (kzImX_kz2 hXK) * (kzImX_kz2 hXK).index = 9 * (kzImX_kz2 hXK).index := by
    rw [h2]
    have h1' : (kzImO_kz2 hXK).index = H₁.index * (kzImX_kz2 hXK).index := h1
    rw [h1', hH]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) key


theorem irr_transport_kz2 [Finite G] {K X Tt : Subgroup G} (hXK : X ≤ K)
    (hTK : Tt ≤ Subgroup.normalizer (K : Set G)) (hTX : Tt ≤ Subgroup.normalizer (X : Set G))
    (hcomm : ⁅X, X⁆ ≤ pCoreOf 2 X)
    (hirr : ∀ Y : Subgroup G, ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Y → Y ≤ X → Tt ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⁅X, X⁆ ⊔ pCoreOf 2 X ∨ Y = X)
    (Stil : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hpres : ∀ W : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), Stil ≤ Subgroup.normalizer (W : Set _) →
      ∀ t ∈ Tt, ∀ htK : t ∈ Subgroup.normalizer (K : Set G), ∀ y ∈ W, kzQmap_kz2 K t htK y ∈ W) :
    ∀ W : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), kzImO_kz2 hXK ≤ W → W ≤ kzImX_kz2 hXK →
      Stil ≤ Subgroup.normalizer (W : Set _) → W = kzImO_kz2 hXK ∨ W = kzImX_kz2 hXK := by
  intro W hOW hWX hSW
  classical
  set Z : Subgroup ↥K := W.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hZ
  set Y : Subgroup G := (Z.map K.subtype) ⊓ X with hY
  have hYT : ∀ t ∈ Tt, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro t ht y hy
    obtain ⟨hyZ, hyX⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨z, hzZ, hzy⟩ := Subgroup.mem_map.mp hyZ
    have htK := hTK ht
    have hzW : (QuotientGroup.mk z : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ W := hzZ
    have hconj : (QuotientGroup.mk (kzConjK_kz2 K t htK z) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ W := by
      rw [← kzQmap_mk_kz2]
      exact hpres W hSW t ht htK _ hzW
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨kzConjK_kz2 K t htK z, hconj, ?_⟩, ?_⟩
    · show (kzConjK_kz2 K t htK z : G) = _
      rw [kzConjK_val_kz2, ← hzy]
      rfl
    · exact (Subgroup.mem_normalizer_iff.mp (hTX ht) y).mp hyX
  have hYN : Tt ≤ Subgroup.normalizer (Y : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hYT t ht y hy
    · intro hy
      have := hYT t⁻¹ (Tt.inv_mem ht) _ hy
      rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
  have hYX : Y ≤ X := inf_le_right
  have hOY : pCoreOf 2 X ≤ Y := by
    intro y hy
    have hyX : y ∈ X := pCoreOf_le 2 X hy
    have hyK : y ∈ K := hXK hyX
    have hu : (⟨y, hyX⟩ : ↥X) ∈ (pCoreOf 2 X).subgroupOf X := Subgroup.mem_subgroupOf.mpr hy
    have hw : kzF_kz2 hXK ⟨y, hyX⟩ ∈ W := hOW (Subgroup.mem_map.mpr ⟨_, hu, rfl⟩)
    have hZy : (⟨y, hyK⟩ : ↥K) ∈ Z := hw
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, hZy, rfl⟩, hyX⟩
  have hcompl : ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Y := sup_le (hcomm.trans hOY) hOY
  have hcases := hirr Y hcompl hYX hYN
  rw [sup_eq_right.mpr hcomm] at hcases
  rcases hcases with hYO | hYX'
  · left
    apply le_antisymm _ hOW
    intro w hw
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp (hWX hw)
    have hinZ : Subgroup.inclusion hXK u ∈ Z := hw
    have huY : (u : G) ∈ Y :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXK u, hinZ, rfl⟩, u.2⟩
    have huO : (u : G) ∈ pCoreOf 2 X := hYO ▸ huY
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr huO, rfl⟩
  · right
    apply le_antisymm hWX
    intro w hw
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hw
    have huY : (u : G) ∈ Y := by
      rw [hYX']
      exact u.2
    obtain ⟨hyZ, -⟩ := Subgroup.mem_inf.mp huY
    obtain ⟨z, hzZ, hzu⟩ := Subgroup.mem_map.mp hyZ
    have hzeq : Subgroup.inclusion hXK u = z := Subtype.ext hzu.symm
    show QuotientGroup.mk' (CFSG.pCore 2 ↥K) (Subgroup.inclusion hXK u) ∈ W
    rw [hzeq]
    exact hzZ


theorem mem_normalizer_of_conj_kz2 {Q : Type} [Group Q] {W : Subgroup Q} {q : Q}
    (h1 : ∀ y ∈ W, q * y * q⁻¹ ∈ W) (h2 : ∀ y ∈ W, q⁻¹ * y * q⁻¹⁻¹ ∈ W) :
    q ∈ Subgroup.normalizer (W : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => h1 y hy
  · intro hy
    have := h2 _ hy
    simpa [mul_assoc] using this

theorem inner_mem_stil_kz2 [Finite G] (hHeA : HeAutInner_kz2)
    {T K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTp : IsPGroup 2 ↥T)
    (hQe : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    (Bq : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hBq : Nat.card Bq = 69120) (hBqp : ⁅Bq, Bq⁆ = Bq)
    (hBqT : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ Bq, kzQmap_kz2 K t ht x ∈ Bq)
    (Stil : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hStilD : ∀ s ∈ Stil, ∃ x : ↥K, (x : G) ∈ T ∧ (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = s)
    (hStil2 : IsPGroup 2 Stil) (hStilc : Nat.card Stil = 2 ^ 10) (hStilS : IsSylowTwoOf Stil ⊤) :
    ∀ t : G, ∀ ht : t ∈ T, ∀ htK : t ∈ Subgroup.normalizer (K : Set G),
      ∃ k ∈ Stil, ∀ x : ↥K ⧸ CFSG.pCore 2 ↥K, kzQmap_kz2 K t htK x = k * x * k⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_bot_of_he_kz2 hQe
  have hStilN : Stil ≤ Subgroup.normalizer (Bq : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := hStilD s hs
    have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer x.2
    have hinvT : ((x⁻¹ : ↥K) : G) ∈ T := T.inv_mem hxT
    have hinvN : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer (x⁻¹ : ↥K).2
    apply mem_normalizer_of_conj_kz2
    · intro y hy
      rw [← kzQmap_eq_conj_kz2 x hxN y]
      exact hBqT _ hxT hxN y hy
    · intro y hy
      have e : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ * y *
          ((QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹)⁻¹ =
          kzQmap_kz2 K ((x⁻¹ : ↥K) : G) hinvN y := by
        rw [kzQmap_eq_conj_kz2 (x⁻¹) hinvN, QuotientGroup.mk_inv, inv_inv]
      rw [e]
      exact hBqT _ hinvT hinvN y hy
  have hex : ∀ t : ↥T, ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ∀ x : ↥K ⧸ CFSG.pCore 2 ↥K,
      kzQmap_kz2 K (t : G) (hTK t.2) x = k * x * k⁻¹ := by
    intro t
    have hbij := kzQmap_bijective_kz2 (hTK t.2)
    have hmap : Bq.map (kzQmap_kz2 K (t : G) (hTK t.2)) = Bq := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨y, hy, rfl⟩
        exact hBqT _ t.2 (hTK t.2) y hy
      · exact le_of_eq (Subgroup.card_map_of_injective hbij.1).symm
    exact hHeA (↥K ⧸ CFSG.pCore 2 ↥K) hQe Stil Bq hStil2 hStilc hStilN hBq hBqp _ hbij hmap
  choose kk hkk using hex
  have hmul : ∀ t s : ↥T, kk (t * s) = kk t * kk s := by
    intro t s
    apply eq_of_conj_eq_kz2 hZ
    intro x
    have h2 : kzQmap_kz2 K (t : G) (hTK t.2) (kzQmap_kz2 K (s : G) (hTK s.2) x) =
        kzQmap_kz2 K ((t * s : ↥T) : G) (hTK (t * s).2) x :=
      (kzQmap_mul_kz2 (hTK t.2) (hTK s.2) (hTK (t * s).2) x).symm
    rw [← hkk (t * s) x, ← h2, hkk t, hkk s]
    group
  let κ : ↥T →* (↥K ⧸ CFSG.pCore 2 ↥K) := MonoidHom.mk' kk hmul
  have hTtop : IsPGroup 2 ↥(⊤ : Subgroup ↥T) := hTp.of_equiv (Subgroup.topEquiv).symm
  have hκ2 : IsPGroup 2 κ.range := by
    rw [MonoidHom.range_eq_map]
    exact hTtop.map κ
  have hle : Stil ≤ κ.range := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := hStilD _ hs
    have hkt : kk ⟨(x : G), hxT⟩ = QuotientGroup.mk x := by
      apply eq_of_conj_eq_kz2 hZ
      intro y
      rw [← hkk ⟨(x : G), hxT⟩ y]
      exact kzQmap_eq_conj_kz2 x (hTK hxT) y
    exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxT⟩, hkt⟩
  have hκeq : κ.range = Stil := eq_of_sylow_le_kz2 hStilS hκ2 hle le_top
  intro t ht htK
  refine ⟨kk ⟨t, ht⟩, ?_, hkk ⟨t, ht⟩⟩
  rw [← hκeq]
  exact MonoidHom.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩


theorem false_of_he_K_kz2 [Finite G] (hHeA : HeAutInner_kz2) (hHe : HeSubO2_kz)
    {Gz T K X : Subgroup G} (hT : IsSylowTwoOf T Gz) (hKG : K ≤ Gz)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ K) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hrel : (pCoreOf 2 X).relIndex X = 9)
    (hirr : ∀ Y : Subgroup G, ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Y → Y ≤ X → T ≤ Subgroup.normalizer (Y : Set G) →
      Y = ⁅X, X⁆ ⊔ pCoreOf 2 X ∨ Y = X)
    (hQe : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He))
    (Bq : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hBq : Nat.card Bq = 69120) (hBqp : ⁅Bq, Bq⁆ = Bq)
    (hBqT : ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ Bq, kzQmap_kz2 K t ht x ∈ Bq) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 4030387200 := by
    rw [Nat.card_congr hQe.some.toEquiv]
    exact CFSG.Sporadic.He.card_He
  have hNS' : CFSG.pCore 2 ↥K ≤ (T ⊓ K).subgroupOf K := pCore_le_inf_kz2 hT hKG hTK
  have hrS := card_map_mul_kz2 K hNS'
  have hodd : ¬ 2 ∣ T.relIndex K := not_two_dvd_relIndex_kz2 hT hKG hTK
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥K)).exists_card_eq
  obtain ⟨a, ha⟩ := (hT.2.1.to_le (inf_le_left : T ⊓ K ≤ T)).exists_card_eq
  have hS'c : Nat.card ((T ⊓ K).subgroupOf K) = Nat.card (T ⊓ K : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
  have hKc : 4030387200 * Nat.card (CFSG.pCore 2 ↥K) = Nat.card K := by
    rw [← hQc]
    exact Subgroup.index_mul_card _
  have hcK : T.relIndex K * Nat.card (T ⊓ K : Subgroup G) = Nat.card K :=
    Subgroup.relIndex_mul_card T K
  have harith1 : T.relIndex K * 2 ^ a = 2 ^ 10 * 3935925 * 2 ^ b := by
    rw [← ha, ← hb, hcK, ← hKc]
    norm_num
  have harith2 : Nat.card (((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) * 2 ^ b = 2 ^ a := by
    rw [← ha, ← hb, ← hS'c, ← hrS]
  have hStilc : Nat.card (((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) = 2 ^ 10 :=
    two_part_eq_kz2 _ _ _ _ _ _ hodd (by norm_num) harith1 harith2
  set Stil : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hStil
  have hS'p : IsPGroup 2 ↥((T ⊓ K).subgroupOf K) :=
    (hT.2.1.to_le (inf_le_left : T ⊓ K ≤ T)).of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).symm
  have hStil2 : IsPGroup 2 ↥Stil := hS'p.map _
  have hStilS : IsSylowTwoOf Stil ⊤ := by
    refine ⟨le_top, hStil2, ?_⟩
    have hidx : Stil.index = 3935925 := by
      have h := Subgroup.index_mul_card Stil
      rw [hStilc, hQc] at h
      norm_num at h
      omega
    show ¬ 2 ∣ Stil.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hidx]
    norm_num
  have hStilD : ∀ s ∈ Stil, ∃ x : ↥K, (x : G) ∈ T ∧ (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = s := by
    intro s hs
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
    exact ⟨x, (Subgroup.mem_subgroupOf.mp hx).1, hxs⟩
  have hinner := inner_mem_stil_kz2 hHeA hTK hT.2.1 hQe Bq hBq hBqp hBqT Stil hStilD hStil2 hStilc hStilS
  have hpres : ∀ W : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), Stil ≤ Subgroup.normalizer (W : Set _) →
      ∀ t ∈ T, ∀ htK : t ∈ Subgroup.normalizer (K : Set G), ∀ y ∈ W, kzQmap_kz2 K t htK y ∈ W := by
    intro W hSW t ht htK y hy
    obtain ⟨k, hk, hkx⟩ := hinner t ht htK
    rw [hkx]
    exact (Subgroup.mem_normalizer_iff.mp (hSW hk) y).mp hy
  have hcomm := comm_le_pCoreOf_kz2 hrel
  have hirrT := irr_transport_kz2 hXK hTK hTX hcomm hirr Stil hpres
  have hrelI := relIndex_kzIm_kz2 hXK hrel
  have hSX : Stil ≤ Subgroup.normalizer ((kzImX_kz2 hXK : Subgroup _) : Set _) := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := hStilD s hs
    have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer x.2
    have hinvT : ((x⁻¹ : ↥K) : G) ∈ T := T.inv_mem hxT
    have hinvN : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer (x⁻¹ : ↥K).2
    have hxX : (x : G) ∈ Subgroup.normalizer (X : Set G) := hTX hxT
    have hinvX : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (X : Set G) := hTX hinvT
    apply mem_normalizer_of_conj_kz2
    · intro y hy
      rw [← kzQmap_eq_conj_kz2 x hxN y]
      exact preserve_kzImX_kz2 hXK hxN hxX y hy
    · intro y hy
      have e : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ * y *
          ((QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹)⁻¹ =
          kzQmap_kz2 K ((x⁻¹ : ↥K) : G) hinvN y := by
        rw [kzQmap_eq_conj_kz2 (x⁻¹) hinvN, QuotientGroup.mk_inv, inv_inv]
      rw [e]
      exact preserve_kzImX_kz2 hXK hinvN hinvX y hy
  have hSO : Stil ≤ Subgroup.normalizer ((kzImO_kz2 hXK : Subgroup _) : Set _) := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := hStilD s hs
    have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer x.2
    have hinvT : ((x⁻¹ : ↥K) : G) ∈ T := T.inv_mem hxT
    have hinvN : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer (x⁻¹ : ↥K).2
    have hxX : (x : G) ∈ Subgroup.normalizer (X : Set G) := hTX hxT
    have hinvX : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (X : Set G) := hTX hinvT
    have hxO : (x : G) ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 X hxX
    have hinvO : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 X hinvX
    apply mem_normalizer_of_conj_kz2
    · intro y hy
      rw [← kzQmap_eq_conj_kz2 x hxN y]
      exact preserve_kzImO_kz2 hXK hxN hxX hxO y hy
    · intro y hy
      have e : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ * y *
          ((QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹)⁻¹ =
          kzQmap_kz2 K ((x⁻¹ : ↥K) : G) hinvN y := by
        rw [kzQmap_eq_conj_kz2 (x⁻¹) hinvN, QuotientGroup.mk_inv, inv_inv]
      rw [e]
      exact preserve_kzImO_kz2 hXK hinvN hinvX hinvO y hy
  have hXO : kzImX_kz2 hXK ≤ Subgroup.normalizer ((kzImO_kz2 hXK : Subgroup _) : Set _) := by
    intro w hw
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hw
    show (QuotientGroup.mk (Subgroup.inclusion hXK u) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ _
    have hxK : ((Subgroup.inclusion hXK u : ↥K) : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer (Subgroup.inclusion hXK u).2
    have hxX : ((Subgroup.inclusion hXK u : ↥K) : G) ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.le_normalizer u.2
    have hinvK : (((Subgroup.inclusion hXK u)⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer ((Subgroup.inclusion hXK u)⁻¹ : ↥K).2
    have hinvX : (((Subgroup.inclusion hXK u)⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.le_normalizer (X.inv_mem u.2)
    have hxO : ((Subgroup.inclusion hXK u : ↥K) : G) ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 X hxX
    have hinvO : (((Subgroup.inclusion hXK u)⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 X hinvX
    apply mem_normalizer_of_conj_kz2
    · intro y hy
      rw [← kzQmap_eq_conj_kz2 _ hxK y]
      exact preserve_kzImO_kz2 hXK hxK hxX hxO y hy
    · intro y hy
      have e : (QuotientGroup.mk (Subgroup.inclusion hXK u) : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ * y *
          ((QuotientGroup.mk (Subgroup.inclusion hXK u) : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹)⁻¹ =
          kzQmap_kz2 K (((Subgroup.inclusion hXK u)⁻¹ : ↥K) : G) hinvK y := by
        rw [kzQmap_eq_conj_kz2 _ hinvK, QuotientGroup.mk_inv, inv_inv]
      rw [e]
      exact preserve_kzImO_kz2 hXK hinvK hinvX hinvO y hy
  have hOp : IsPGroup 2 (kzImO_kz2 hXK) :=
    (((pCoreOf_isPGroup 2 X).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 X)).symm)).map _
  exact false_of_heCore_gen_kz2 hHe hQe hQc hStil2 hStilc hSX hOp (kzImO_le_kzImX_kz2 hXK) hXO hSO hrelI hirrT

end CFSG.Quasithin.H13
