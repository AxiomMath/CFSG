module

public import CFSG.Quasithin.Vol2.Ch3Sec3Wreath
public import CFSG.Quasithin.EmptyFaithful.Der6DAux
public import CFSG.Quasithin.Vol2.Ch10SecB4Lift2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

noncomputable def oTwoQuotEquiv {G : Type} [Group G] {H : Subgroup G}
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) : OTwoQuot H ≃* S152N.W3 :=
  ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥H 2)).symm.trans e).trans
    Wreath.wreathEquiv.symm

@[expose] def FactAutL45Sylow : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (k : ℕ), (k = 4 ∨ k = 5) →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL k 2 1 →
    ∀ S : Subgroup (MulAut Q), IsSylowTwoOf S ⊤ → Subgroup.normalizer (S : Set (MulAut Q)) ≤ S

namespace Lem3313

open S152N

noncomputable local instance instFintypeW3' : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3' : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0'' : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

local instance instDecP0'' : DecidablePred (· ∈ W3.P0) := fun a =>
  inferInstanceAs (Decidable (∀ q, a.left q = 1 ∨ a.left q = W3.s01))

theorem P0_noncomm : ∃ a ∈ W3.P0, ∃ b ∈ W3.P0, ∃ n ∈ W3.N0,
    a * b * n * (a * b)⁻¹ ≠ b * a * n * (b * a)⁻¹ := by
  refine ⟨⟨fun q => if q = 1 then W3.s01 else 1, 1⟩, ?_, ⟨fun _ => 1, Multiplicative.ofAdd 1⟩, ?_,
    ⟨fun _ => Equiv.swap 0 1 * Equiv.swap 1 2, 1⟩, ?_, ?_⟩ <;> decide +kernel

variable {G : Type} [Group G] [Finite G] {T H : Subgroup G}

@[expose] noncomputable def piH (φ : OTwoQuot H ≃* W3) : ↥H →* W3 :=
  (φ : OTwoQuot H →* W3).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

omit [Finite G] in
theorem piH_eq_one_iff (φ : OTwoQuot H ≃* W3) (x : ↥H) :
    piH φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [← mk_eq_one_iff_mem_pCoreOf]
  exact φ.map_eq_one_iff

omit [Finite G] in
theorem map_piH (φ : OTwoQuot H ≃* W3) (X : Subgroup G) :
    ((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
      (φ : OTwoQuot H →* W3) = (X.subgroupOf H).map (piH φ) := by
  rw [Subgroup.map_map]
  rfl

omit [Finite G] in
theorem pow_four_mem_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) {s : G}
    (hs : s ∈ T) : s ^ 4 ∈ pCoreOf 2 H := by
  have hsH : s ∈ H := hT.1 hs
  obtain ⟨k, hk⟩ := hT.2.1 ⟨s, hs⟩
  have hk' : (⟨s, hsH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hw2 : piH φ ⟨s, hsH⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
  have hw72 : piH φ ⟨s, hsH⟩ ^ 72 = 1 := by
    have h : piH φ ⟨s, hsH⟩ ^ Nat.card W3 = 1 := pow_card_eq_one'
    rwa [W3.card_eq] at h
  have hdvd : orderOf (piH φ ⟨s, hsH⟩) ∣ 8 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hw2)
    have h72 : 2 ^ j ∣ 72 := by
      rw [← hj]
      exact orderOf_dvd_of_pow_eq_one hw72
    rw [hj]
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have h16 : 2 ^ 4 ∣ 72 := (Nat.pow_dvd_pow 2 (by omega)).trans h72
      norm_num at h16
    exact Nat.pow_dvd_pow 2 hj3
  have hw4 := Der6D.W3Facts.pow_four_of_pow_eight _ (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have e : (⟨s ^ 4, H.pow_mem hsH 4⟩ : ↥H) = ⟨s, hsH⟩ ^ 4 := Subtype.ext (by simp)
  refine (piH_eq_one_iff φ ⟨s ^ 4, H.pow_mem hsH 4⟩).mp ?_
  rw [e, map_pow, hw4]

theorem pow_four_comm_mem_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) {s : G}
    (hs : s ∈ T) {y : G} (hy : y ∈ oTwoUpper H) :
    s ^ 4 * y * (s ^ 4)⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)]
  have hs4 := pow_four_mem_of_iso hT φ hs
  have hs4H : s ^ 4 ∈ H := H.pow_mem (hT.1 hs) 4
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : s ^ 4 * y * (s ^ 4)⁻¹ ∈ oTwoUpper H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hs4H) y).mp hy
    exact (oTwoUpper H).mul_mem h1 ((oTwoUpper H).inv_mem hy)
  · have hN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
    have h1 : y * (s ^ 4)⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hN (hYH hy)) _).mp ((pCoreOf 2 H).inv_mem hs4)
    have e : s ^ 4 * y * (s ^ 4)⁻¹ * y⁻¹ = s ^ 4 * (y * (s ^ 4)⁻¹ * y⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hs4 h1

theorem exists_noncomm_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ oTwoUpper H,
      a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 (oTwoUpper H) := by
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hDsyl := isSylowTwoOf_image hT φ
  rw [map_piH] at hDsyl
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf W3.P0_isSylowTwoOf hDsyl
  obtain ⟨a, ha, b, hb, n, hn, hne⟩ := P0_noncomm
  have hconj : ∀ x ∈ W3.P0, g * x * g⁻¹ ∈ (T.subgroupOf H).map (piH φ) := fun x hx => by
    refine (hg _).mpr ?_
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hx
  obtain ⟨⟨a', ha'H⟩, ha'T, ha'⟩ := hconj a ha
  obtain ⟨⟨b', hb'H⟩, hb'T, hb'⟩ := hconj b hb
  have hn' : g * n * g⁻¹ ∈ (imageOTwoQuot H (oTwoUpper H)).map (φ : OTwoQuot H →* W3) := by
    rw [C1Pack12.map_imageOTwoQuot_oTwoUpper φ]
    exact W3.N0_normal.conj_mem n hn g
  obtain ⟨u, hu, hun⟩ := hn'
  obtain ⟨y, hyH, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  refine ⟨a', Subgroup.mem_subgroupOf.mp ha'T, b', Subgroup.mem_subgroupOf.mp hb'T, y, hyY,
    fun hmem => hne ?_⟩
  have hmemH : a' * b' * y * (a' * b')⁻¹ * (b' * a' * y * (b' * a')⁻¹)⁻¹ ∈ pCoreOf 2 H := by
    rw [S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  have h1 : piH φ (⟨a', ha'H⟩ * ⟨b', hb'H⟩ * ⟨y, hyH⟩ * (⟨a', ha'H⟩ * ⟨b', hb'H⟩)⁻¹ *
      (⟨b', hb'H⟩ * ⟨a', ha'H⟩ * ⟨y, hyH⟩ * (⟨b', hb'H⟩ * ⟨a', ha'H⟩)⁻¹)⁻¹) = 1 :=
    (piH_eq_one_iff φ _).mpr hmemH
  have hπy : piH φ ⟨y, hyH⟩ = g * n * g⁻¹ := hun
  simp only [map_mul, map_inv] at h1
  rw [ha', hb', hπy] at h1
  have h2 := mul_inv_eq_one.mp h1
  calc a * b * n * (a * b)⁻¹
      = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹) * (g * n * g⁻¹) *
          (g * a * g⁻¹ * (g * b * g⁻¹))⁻¹) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹) * (g * n * g⁻¹) *
          (g * b * g⁻¹ * (g * a * g⁻¹))⁻¹) * g := by rw [h2]
    _ = b * a * n * (b * a)⁻¹ := by group

theorem maxOver_eq_of_iso (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) :
    maxOver H T = {T} := by
  have hO : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  have hDsyl := isSylowTwoOf_image hT φ
  rw [map_piH] at hDsyl
  have hπs : Function.Surjective (piH φ) := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have key : ∀ K : Subgroup G, T ≤ K → K ≤ H → K = T ∨ K = H := by
    intro K hTK hKH
    have hDI : (T.subgroupOf H).map (piH φ) ≤ (K.subgroupOf H).map (piH φ) :=
      Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hTK (Subgroup.mem_subgroupOf.mp hx))
    rcases W3.sylow_maximal hDsyl hDI with h | h
    · left
      refine le_antisymm (fun k hk => ?_) hTK
      have hmem : piH φ ⟨k, hKH hk⟩ ∈ (K.subgroupOf H).map (piH φ) :=
        ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [h] at hmem
      obtain ⟨⟨t, htH⟩, htT, hte⟩ := hmem
      have h1 : piH φ ((⟨t, htH⟩ : ↥H)⁻¹ * ⟨k, hKH hk⟩) = 1 := by
        rw [map_mul, map_inv, hte, inv_mul_cancel]
      have h2 := (piH_eq_one_iff φ _).mp h1
      have h3 : k = t * (t⁻¹ * k) := by group
      rw [h3]
      exact T.mul_mem (Subgroup.mem_subgroupOf.mp htT) (hO h2)
    · right
      refine le_antisymm hKH fun x hx => ?_
      have hmem : piH φ ⟨x, hx⟩ ∈ (K.subgroupOf H).map (piH φ) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨⟨k, hkH⟩, hkK, hke⟩ := hmem
      have h1 : piH φ ((⟨k, hkH⟩ : ↥H)⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, hke, inv_mul_cancel]
      have h2 := (piH_eq_one_iff φ _).mp h1
      have h3 : x = k * (k⁻¹ * x) := by group
      rw [h3]
      exact K.mul_mem (Subgroup.mem_subgroupOf.mp hkK) (hTK (hO h2))
  have hTH : T < H := by
    refine lt_of_le_of_ne hT.1 fun heq => ?_
    have h9 := W3.index_eq_nine hDsyl
    have htop : (T.subgroupOf H).map (piH φ) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨x, rfl⟩ := hπs w
      refine ⟨x, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      rw [heq]
      exact x.2
    rw [htop, Subgroup.index_top] at h9
    omega
  ext N
  simp only [maxOver, IsMaxSubgroupIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hNH, -⟩, hTN⟩
    rcases key N hTN hNH.le with h | h
    · exact h
    · exact absurd h hNH.ne
  · rintro rfl
    refine ⟨⟨hTH, fun K hTK hKH => ?_⟩, le_rfl⟩
    rcases key K hTK.le hKH with h | h
    · exact absurd h hTK.ne'
    · exact h

omit [Finite G] in
theorem conj_mem_oTwoUpper_of_comm {K : Subgroup G} {d : G} (hOH : pCoreOf 2 K ≤ H)
    (hYK : oTwoUpper H ≤ K) (hd : ∀ y ∈ K, d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K) {y : G}
    (hy : y ∈ oTwoUpper H) : d * y * d⁻¹ ∈ oTwoUpper H := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    have hxY : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hx.1 hx.2
    have h1 : d * x * d⁻¹ * x⁻¹ ∈ H := hOH (hd x (hYK hxY))
    have h2 : d * x * d⁻¹ ∈ H := by
      have := H.mul_mem h1 hx.1
      simpa [mul_assoc] using this
    refine mem_oTwoUpper_of_odd h2 ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa [mul_assoc] using (oTwoUpper H).mul_mem ihx ihy
  | inv x _ ih =>
    simpa [mul_assoc] using (oTwoUpper H).inv_mem ih

omit [Finite G] in
theorem mem_normalizer_oTwoUpper_of_comm {K : Subgroup G} {d : G} (hOH : pCoreOf 2 K ≤ H)
    (hYK : oTwoUpper H ≤ K) (hd : ∀ y ∈ K, d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hd' : ∀ y ∈ K, d⁻¹ * y * d⁻¹⁻¹ * y⁻¹ ∈ pCoreOf 2 K) :
    d ∈ Subgroup.normalizer (oTwoUpper H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_oTwoUpper_of_comm hOH hYK hd hy, fun hy => ?_⟩
  have := conj_mem_oTwoUpper_of_comm hOH hYK hd' hy
  simpa [mul_assoc] using this

theorem comm_mem_pCoreOf_of_surjective (hF : FactAutL45Sylow) {K X : Subgroup G} {k : ℕ}
    (hk45 : k = 4 ∨ k = 5)
    (hk : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL k 2 1)
    (hEN : K ⊔ X ≤ Subgroup.normalizer (K : Set G)) (hTE : IsSylowTwoOf T (K ⊔ X))
    (hsurj : Function.Surjective (Vol2.Ch10.SecB.conjLBar K X hEN)) {d : G} (hdE : d ∈ K ⊔ X)
    (hdT : d ∈ Subgroup.normalizer (T : Set G)) (hodd : Odd (orderOf d)) {y : G}
    (hy : y ∈ K) : d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  set φ := Vol2.Ch10.SecB.conjLBar K X hEN with hφ
  set S : Subgroup (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := (T.subgroupOf (K ⊔ X)).map φ with hS
  have hSyl : IsSylowTwoOf S ⊤ := by
    have h := Vol2.Ch10.SecB.isSylowTwoOf_map_range hTE φ
    rwa [MonoidHom.range_eq_top.mpr hsurj] at h
  have key : ∀ (g : G) (hg : g ∈ K ⊔ X), g ∈ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ S, φ ⟨g, hg⟩ * s * (φ ⟨g, hg⟩)⁻¹ ∈ S := by
    rintro g hg hgT _ ⟨⟨t, htE⟩, htT, rfl⟩
    have htT' : t ∈ T := Subgroup.mem_subgroupOf.mp htT
    have h1 : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hgT t).mp htT'
    refine ⟨⟨g * t * g⁻¹, hTE.1 h1⟩, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    have e : (⟨g * t * g⁻¹, hTE.1 h1⟩ : ↥(K ⊔ X)) = ⟨g, hg⟩ * ⟨t, htE⟩ * (⟨g, hg⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hdi : d⁻¹ ∈ K ⊔ X := (K ⊔ X).inv_mem hdE
  have haN : φ ⟨d, hdE⟩ ∈ Subgroup.normalizer (S : Set (MulAut (↥K ⧸ CFSG.pCore 2 ↥K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨key d hdE hdT s, fun hs => ?_⟩
    have h1 := key d⁻¹ hdi (Subgroup.inv_mem _ hdT) _ hs
    have e : (⟨d⁻¹, hdi⟩ : ↥(K ⊔ X)) = (⟨d, hdE⟩)⁻¹ := rfl
    rw [e, map_inv] at h1
    simpa [mul_assoc] using h1
  have haS : φ ⟨d, hdE⟩ ∈ S := hF _ k hk45 hk S hSyl haN
  obtain ⟨j, hj⟩ := hSyl.2.1 ⟨_, haS⟩
  have hj' : φ ⟨d, hdE⟩ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd1 : φ ⟨d, hdE⟩ ^ orderOf d = 1 := by
    have h1 : (⟨d, hdE⟩ : ↥(K ⊔ X)) ^ orderOf d = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← map_pow, h1, map_one]
  have hcop : Nat.Coprime (2 ^ j) (orderOf d) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have ha1 : φ ⟨d, hdE⟩ = 1 := by
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hd1)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h1
    exact orderOf_eq_one_iff.mp h1
  have hdy : d * y * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hEN hdE) y).mp hy
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d * y * d⁻¹, hdy⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩ := by
    calc (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨d * y * d⁻¹, hdy⟩ : ↥K ⧸ CFSG.pCore 2 ↥K)
        = φ ⟨d, hdE⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩) :=
          (Vol2.Ch10.SecB.conjLBar_mk hEN ⟨d, hdE⟩ hy).symm
      _ = QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hy⟩ := by rw [ha1]; rfl
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨d * y * d⁻¹, hdy⟩ * (⟨y, hy⟩ : ↥K)⁻¹) :
      ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem le_normalizer_of_lk2 (hFc : Vol2.Ch10.SecB.FactL4L5) (hAut : FactAutL45Sylow)
    (hT : quasithinIsSylowTwo T) (hTsyl : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3)
    (hO : pCoreOf 2 H ≠ ⊥) {D K : Subgroup G} (hK : K ∈ cComp (H ⊔ D))
    (hTL : T ≤ Subgroup.normalizer (K : Set G)) (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hDodd : Odd (Nat.card D))
    (hYK : oTwoUpper H ≤ K) {k : ℕ} (hk45 : k = 4 ∨ k = 5)
    (hk : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL k 2 1) :
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hTsyl.1
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, hT.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le hT (hTH.trans le_sup_left)⟩
  have hXi := Der6D.xi_of_iso hTsyl hO φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := fun x hx => by
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, C1Pack12.pow_three_mem_pCoreOf φ hx⟩
  have hEN : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTL
  have hEN' : K ⊔ (T ⊔ D) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le hTL hDK)
  obtain ⟨eA⟩ := Vol2.Ch10.SecB.nonempty_aut_of hFc hT₀ hK hTL hk45 hk hYK hXi.1 hXi.2.1 hpow3
    hrel (exists_noncomm_of_iso hTsyl φ)
  have hker := Vol2.Ch10.SecB.ker_conjLBar hT₀ (le_of_mem_cComp hK) hTL
    (Vol2.Ch10.SecB.center_lbar_eq_bot hk) hEN
  have hsurj : Function.Surjective (Vol2.Ch10.SecB.conjLBar K T hEN) := by
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hk
    have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
    have eQ := MulAut.congr (eF.trans
      (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two k F hF2))
    refine MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ ?_)
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr eA.toEquiv, Nat.card_congr eQ.toEquiv]
  have hsurj' : Function.Surjective (Vol2.Ch10.SecB.conjLBar K (T ⊔ D) hEN') := by
    intro α
    obtain ⟨⟨x, hx⟩, rfl⟩ := hsurj α
    have hx' : x ∈ K ⊔ (T ⊔ D) := sup_le_sup_left le_sup_left K hx
    refine ⟨⟨x, hx'⟩, ?_⟩
    ext q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
    rw [Vol2.Ch10.SecB.conjLBar_mk, Vol2.Ch10.SecB.conjLBar_mk]
    rfl
  have hTE : IsSylowTwoOf T (K ⊔ (T ⊔ D)) := ⟨le_sup_left.trans le_sup_right, hT.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le hT (le_sup_left.trans le_sup_right)⟩
  have hcomm : ∀ d ∈ D, ∀ y ∈ K, d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
    intro d hd y hy
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hDodd h1
    exact comm_mem_pCoreOf_of_surjective hAut hk45 hk hEN' hTE hsurj'
      ((le_sup_right.trans le_sup_right : D ≤ K ⊔ (T ⊔ D)) hd) (hDT hd) hodd hy
  have hOK : pCoreOf 2 K ≤ H := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K (K ⊔ T)
        le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hEN)
    have hTKT : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hT.1,
      Vol2.Ch10.SecA.not_two_dvd_index_of_le hT le_sup_right⟩
    exact (h1.trans (pCoreOf_le_of_isSylowTwoOf hTKT)).trans hTH
  intro d hd
  exact mem_normalizer_oTwoUpper_of_comm hOK hYK (hcomm d hd) (hcomm d⁻¹ (D.inv_mem hd))

end Lem3313

end CFSG.Quasithin.H13
