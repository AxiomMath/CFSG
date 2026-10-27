module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F4
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

@[expose] noncomputable def quotCenterAut614 (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun σ := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem quotCenterAut614_mk (Y : Type*) [Group Y] (σ : MulAut Y) (y : Y) :
    quotCenterAut614 Y σ (y : Y ⧸ Subgroup.center Y) = ((σ y : Y) : Y ⧸ Subgroup.center Y) := rfl

theorem quotCenterAut614_conj (Y : Type*) [Group Y] (a : Y) :
    quotCenterAut614 Y (MulAut.conj a) = MulAut.conj (a : Y ⧸ Subgroup.center Y) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotCenterAut614_mk, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem eq_one_of_quotCenterAut614_eq_one {Y : Type*} [Group Y] (hY : commutator Y = ⊤)
    {σ : MulAut Y} (hσ : quotCenterAut614 Y σ = 1) : σ = 1 := by
  have hc : ∀ y : Y, y⁻¹ * σ y ∈ Subgroup.center Y := by
    intro y
    have h := congrArg (fun φ : MulAut (Y ⧸ Subgroup.center Y) =>
      φ (y : Y ⧸ Subgroup.center Y)) hσ
    simp only [quotCenterAut614_mk, MulAut.one_apply] at h
    rw [QuotientGroup.eq] at h
    have := Subgroup.inv_mem _ h
    simpa using this
  let f : Y →* ↥(Subgroup.center Y) := MonoidHom.mk' (fun y => ⟨y⁻¹ * σ y, hc y⟩) (by
    intro a b
    apply Subtype.ext
    show (a * b)⁻¹ * σ (a * b) = a⁻¹ * σ a * (b⁻¹ * σ b)
    have hcomm := Subgroup.mem_center_iff.mp (hc a) b⁻¹
    rw [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (σ a * σ b) = b⁻¹ * (a⁻¹ * σ a) * σ b := by group
      _ = a⁻¹ * σ a * b⁻¹ * σ b := by rw [hcomm]
      _ = a⁻¹ * σ a * (b⁻¹ * σ b) := by group)
  have hker : commutator Y ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hY] at hker
  ext y
  have h1 : f y = 1 := hker (Subgroup.mem_top y)
  have h2 : y⁻¹ * σ y = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  calc σ y = y * (y⁻¹ * σ y) := by group
    _ = y := by rw [h2, mul_one]

end

section

variable {Γ : Type} [Group Γ]

theorem mem_pCore_of_mem_pCoreOf614 [Finite Γ] {K : Subgroup Γ} {k : ↥K}
    (h : (k : Γ) ∈ pCoreOf 2 K) : k ∈ CFSG.pCore 2 ↥K := (CFSG.mem_openPCoreOf_iff k).mp h

theorem mem_pCoreOf_of_mem_pCore614 {K : Subgroup Γ} {k : ↥K} (h : k ∈ CFSG.pCore 2 ↥K) :
    (k : Γ) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff k).mpr h

theorem actModO2_614_of_mem (K : Subgroup Γ) {k : Γ} (hk : k ∈ K) :
    actModO2_614 K ⟨k, Subgroup.le_normalizer hk⟩ = MulAut.conj ((⟨k, hk⟩ : ↥K) : ModO2 K) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [actModO2_614_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem actModO2_614_eq_one [Finite Γ] (K : Subgroup Γ)
    {c : ↥(Subgroup.normalizer (K : Set Γ))}
    (hc : ∀ u ∈ K, (c : Γ) * u * (c : Γ)⁻¹ * u⁻¹ ∈ pCoreOf 2 K) : actModO2_614 K c = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [actModO2_614_mk, MulAut.one_apply, QuotientGroup.eq]
    apply mem_pCore_of_mem_pCoreOf614
    have := hc _ (K.inv_mem k.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert this using 1
    group

theorem commutator_le_pCoreOf_of_actModO2_614 {K X : Subgroup Γ}
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (h : ∀ x (hx : x ∈ X), actModO2_614 K ⟨x, hXK hx⟩ = 1) : ⁅X, K⁆ ≤ pCoreOf 2 K := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have h1 := congrArg (fun φ : MulAut (ModO2 K) =>
    φ ((⟨k⁻¹, K.inv_mem hk⟩ : ↥K) : ModO2 K)) (h x hx)
  simp only [actModO2_614_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have h2 := mem_pCoreOf_of_mem_pCore614 h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [commutatorElement_def]
  convert h2 using 1
  group

end

section

variable {Γ G : Type*} [Group Γ] [Group G]

theorem exists_zpowers_five614 [Finite Γ] [Finite G] {M X P T : Subgroup Γ} {N : Subgroup G}
    (σ : ↥M →* G) (hXM : X ≤ M) (hTM : T ≤ M) (hPX : P ≤ X) (hP2 : IsPGroup 2 P)
    (hPn : (P.subgroupOf X).Normal) (hX5 : P.relIndex X = 5) (hXO : X = oTwoUpper X)
    (hTX : T ≤ Subgroup.normalizer (X : Set Γ)) (hXN : ∀ x (hx : x ∈ X), σ ⟨x, hXM hx⟩ ∈ N)
    (hX1 : ∃ x, ∃ hx : x ∈ X, σ ⟨x, hXM hx⟩ ≠ 1)
    (hrank : ∀ V : Subgroup G, V ≤ N → IsElemAbelian 2 V → Nat.card V ≤ 4)
    (hcent : ∀ y u g : G, y ∈ N → u ∈ N → g ∈ N → orderOf y = 5 → orderOf u = 2 →
      Commute y u → Commute g u → g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    ∃ y : G, orderOf y = 5 ∧ y ∈ N ∧
      (∀ x (hx : x ∈ X), σ ⟨x, hXM hx⟩ ∈ Subgroup.zpowers y) ∧
      (∀ t (ht : t ∈ T), σ ⟨t, hTM ht⟩ ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) ∧
      (∀ x (hx : x ∈ X), σ ⟨x, hXM hx⟩ = 1 → x ∈ P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : ↥X →* G := σ.comp (Subgroup.inclusion hXM) with hτ
  have hτx : ∀ x (hx : x ∈ X), τ ⟨x, hx⟩ = σ ⟨x, hXM hx⟩ := fun _ _ => rfl
  set X' := τ.range with hX'
  set P' := (P.subgroupOf X).map τ with hP'
  have hX'N : X' ≤ N := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hXN x hx
  have hP'2 : IsPGroup 2 P' := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm).map τ
  have hP'X' : P' ≤ X' := Subgroup.map_le_range _ _
  have hX'O : X' = oTwoUpper X' := by
    have h1 : oTwoUpper (⊤ : Subgroup ↥X) = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hXO.symm
    rw [hX', MonoidHom.range_eq_map, oTwoUpper_map, h1]
  set ρ := τ.rangeRestrict with hρ
  have hsub : P'.subgroupOf X' = (P.subgroupOf X).map ρ := by
    ext ⟨φ, hφ⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, Subtype.ext he⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, congrArg Subtype.val he⟩
  have hXn' : (P'.subgroupOf X').Normal := by
    rw [hsub]
    exact hPn.map _ (MonoidHom.rangeRestrict_surjective τ)
  have hdvd : P'.relIndex X' ∣ 5 := by
    show (P'.subgroupOf X').index ∣ 5
    rw [hsub, ← hX5]
    exact Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective τ)
  have hX5' : P'.relIndex X' = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h
      obtain ⟨x, hx, hx1⟩ := hX1
      have hbot : X' = ⊥ := by
        rw [hX'O, eq_bot_iff, oTwoUpper, Subgroup.closure_le]
        rintro g ⟨hg, hgo⟩
        obtain ⟨k, hk⟩ := hP'2 ⟨g, h hg⟩
        have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        exact Subgroup.mem_bot.mpr (eq_one_of_pow_two_of_odd614 hk' (pow_orderOf_eq_one g) hgo)
      have hmem : τ ⟨x, hx⟩ ∈ X' := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx1 hmem
    · exact h
  have hinf : X' ⊓ P' = P' := inf_eq_right.mpr hP'X'
  obtain ⟨y, hy5, hXy⟩ := exists_eq_zpowers_of_relIndex_five614 hrank hcent hP'2 hX'N hX'O
    (by rw [hinf]; exact hX5') (by rw [hinf]; exact hXn')
  have hyX' : y ∈ X' := hXy ▸ Subgroup.mem_zpowers y
  have hσX : ∀ x (hx : x ∈ X), σ ⟨x, hXM hx⟩ ∈ Subgroup.zpowers y := fun x hx => by
    rw [← hXy]
    exact ⟨⟨x, hx⟩, rfl⟩
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  refine ⟨y, hy5, hX'N hyX', hσX, ?_, ?_⟩
  ·
    intro t ht
    obtain ⟨⟨x₀, hx₀⟩, hx₀y⟩ := hyX'
    have hconj : ∀ s (hs : s ∈ T),
        σ ⟨s, hTM hs⟩ * y * (σ ⟨s, hTM hs⟩)⁻¹ ∈ Subgroup.zpowers y := by
      intro s hs
      have hsx : s * x₀ * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hTX hs) x₀).mp hx₀
      have e : σ ⟨s, hTM hs⟩ * y * (σ ⟨s, hTM hs⟩)⁻¹ = σ ⟨s * x₀ * s⁻¹, hXM hsx⟩ := by
        rw [← hx₀y, hτx, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact hσX _ hsx
    refine mem_normalizer_zpowers_of_conj614 (hconj t ht) ?_
    have := hconj t⁻¹ (T.inv_mem ht)
    have e : σ ⟨t⁻¹, hTM (T.inv_mem ht)⟩ = (σ ⟨t, hTM ht⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e, inv_inv] at this
    exact this
  ·
    have hPker : P.subgroupOf X ≤ τ.ker := by
      intro p hp
      rw [MonoidHom.mem_ker]
      obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
      have hk' : (p : Γ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hk'' : τ p ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
        rw [this, map_one]
      have hmem : τ p ∈ X' := ⟨p, rfl⟩
      rw [hXy] at hmem
      exact eq_one_of_mem_zpowers_of_pow_two614 hy5' hmem hk''
    have hkerI : τ.ker.index = 5 := by
      rw [Subgroup.index_ker, ← hX', hXy, Nat.card_zpowers, hy5]
    have h1 := Subgroup.relIndex_mul_index hPker
    rw [hkerI, show (P.subgroupOf X).index = 5 from hX5] at h1
    have h2 : (P.subgroupOf X).relIndex τ.ker = 1 := by omega
    rw [Subgroup.relIndex_eq_one] at h2
    intro x hx h
    exact h2 (show (⟨x, hx⟩ : ↥X) ∈ τ.ker from h)

theorem le_of_mul_conj_mem614 {K X P : Subgroup Γ} (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hP2 : IsPGroup 2 P) (hXO : X = oTwoUpper X) {s : Γ} (hs : s ∈ K)
    (hw : ∀ x ∈ X, x * (s * x * s⁻¹) ∈ P) : X ≤ K := by
  classical
  set M := Subgroup.normalizer (K : Set Γ) with hM
  have hKn : (K.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  set φ := QuotientGroup.mk' (K.subgroupOf M) with hφ
  have hsM : s ∈ M := Subgroup.le_normalizer hs
  have hφs : φ ⟨s, hsM⟩ = 1 := by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hs
  rw [hXO, oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxX, hxo⟩
  have hxM : x ∈ M := hXK hxX
  obtain ⟨k, hk⟩ := hP2 ⟨_, hw x hxX⟩
  have hk' : (x * (s * x * s⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hwM : ((⟨x, hxM⟩ : ↥M) * ((⟨s, hsM⟩ : ↥M) * ⟨x, hxM⟩ * (⟨s, hsM⟩ : ↥M)⁻¹)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using hk')
  have h1 : φ ⟨x, hxM⟩ ^ 2 ^ (k + 1) = 1 := by
    have := congrArg φ hwM
    rw [map_pow, map_mul, map_mul, map_mul, map_inv, hφs, one_mul, inv_one, mul_one,
      map_one] at this
    rw [pow_succ', pow_mul, pow_two]
    exact this
  have h2 : φ ⟨x, hxM⟩ ^ orderOf x = 1 := by
    rw [← map_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have h3 := eq_one_of_pow_two_of_odd614 h1 h2 hxo
  rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

end

section

theorem odd_card_center_modO2_614 {Γ : Type} [Group Γ] [Finite Γ] (K : Subgroup Γ) :
    Odd (Nat.card (Subgroup.center (ModO2 K))) := by
  classical
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center (ModO2 K)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set N := CFSG.pCore 2 ↥K with hN
  have hz2 : orderOf (z : ModO2 K) = 2 := by rw [Subgroup.orderOf_coe, hz]
  set Z₂ : Subgroup (ModO2 K) := Subgroup.zpowers (z : ModO2 K) with hZ₂
  have hZc : Z₂ ≤ Subgroup.center (ModO2 K) := Subgroup.zpowers_le.mpr z.2
  have hZn : Z₂.Normal := Subgroup.normal_of_le_center hZc
  have hZ2 : IsPGroup 2 Z₂ := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; rfl)
  set L : Subgroup ↥K := Z₂.comap (QuotientGroup.mk' N) with hL
  have hLn : L.Normal := hZn.comap _
  have hL2 : IsPGroup 2 L := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := hZ2 ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hLN : L ≤ N := le_sSup ⟨hLn, hL2⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective N (z : ModO2 K)
  have hkL : k ∈ L := by
    show QuotientGroup.mk' N k ∈ Z₂
    rw [hk]
    exact Subgroup.mem_zpowers _
  have h1 : (z : ModO2 K) = 1 := by
    rw [← hk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hLN hkL
  rw [h1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem sqtkGroup_of_mulEquiv614 {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hS : SQTKGroup A) (e : A ≃* B) : SQTKGroup B := by
  refine ⟨fun p hp hp2 => ?_, hS.2.of_mulEquiv e.symm⟩
  show CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact hS.1 p hp hp2

end

end CFSG.Quasithin.H13
