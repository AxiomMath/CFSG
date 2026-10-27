module

public import CFSG.Quasithin.Vol2.E2SevenNS
public import CFSG.Quasithin.Vol2.E2SevenKG7Root
public import CFSG.Quasithin.Vol2.Ch3E213MP6CJ
public import CFSG.Quasithin.Vol2.E2SevenKG6
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent)

namespace E2

open Ch3E213M

variable {G : Type} [Group G] [Finite G]

theorem exists_isInIHTVC_of_bender_le (hKG2L2 : KGBenderSubL2) (hKG2Sz : KGBenderSubSz)
    {X T M V L : Subgroup G} (hLX : L ≤ X) {m : ℕ} (hm2 : 2 ≤ m)
    (hL : IsPSL 2 2 m ↥L ∨ IsSz m ↥L) (hSL : IsSylowTwoOf (T ⊓ L) L) (hVSL : V ≤ T ⊓ L)
    (hVZL : V ≤ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G))
    (hML : M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hV : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hmn : ∃ d : ℕ, E1.nParam X = ((m * d : ℕ) : ℕ∞)) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hV4
    omega
  have hsL : IsSimpleGroup ↥L := isSimpleGroup_of_psl_or_sz hL
  have hnabL := nonabelian_of_psl_or_sz (by omega) hL
  obtain ⟨g₀, hg₀L, hg₀N⟩ := exists_not_mem_normalizer_of_simple hsL hnabL hSL
    (fun hb => hV1 (le_bot_iff.mp (hb ▸ hVSL)))
  have hBen : IsBenderOf m ↥L := ⟨hm2, hL.imp id Or.inl⟩
  obtain ⟨g, hgL, -, hsyl, ⟨k, hk2, hkm, hYk⟩, hBor, ⟨h₀, hh₀, hI₀⟩⟩ :=
    exists_member_of_bender hBen hSL hVSL hV4 hg₀L hg₀N fun g' hg'L hg'N => by
      rcases hL with hL2 | hSz
      · exact hKG2L2 G L (T ⊓ L) V m g' hm2 hL2 hSL hVSL hVZL hV hV4 hg'L hg'N
      · exact hKG2Sz G L (T ⊓ L) V m g' hm2 hSz hSL hVSL hVZL hV hV4 hg'L hg'N
  set I₀ := V ⊔ conjSub g V with hI₀def
  have hVL : V ≤ L := hVSL.trans inf_le_right
  have hI₀L : I₀ ≤ L := sup_le hVL (by
    intro w hw
    rw [mem_conjSub] at hw
    have := L.mul_mem (L.mul_mem hgL (hVL hw)) (L.inv_mem hgL)
    simpa [mul_assoc] using this)
  have hTI : T ⊓ I₀ = (T ⊓ L) ⊓ I₀ := by rw [inf_assoc, inf_eq_right.mpr hI₀L]
  refine ⟨I₀, isInIHTVC_of_simple (hI₀L.trans hLX) hh₀ hI₀
    (le_inf (hVSL.trans inf_le_left) le_sup_left) hV1 (by rw [hTI]; exact hsyl) (by omega) hYk
    ?_ ?_⟩
  · rw [hTI, ← hBor, ← hML, inf_assoc, inf_eq_right.mpr hI₀L]
  · obtain ⟨d, hd⟩ := hmn
    obtain ⟨c, rfl⟩ := hkm
    exact ⟨c * d, by rw [hd]; push_cast; ring⟩

section Coord

variable {X T M V K : Subgroup G} {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite G] [Finite k] [CharP k 2] in
theorem mk'_kerIn_injective (hker : kerIn M X = ⊥) (hMX : M ≤ X) :
    Function.Injective (QuotientGroup.mk' (kerIn (M.subgroupOf X) ⊤)) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', kerIn_subgroupOf_top_eq hMX, hker,
    Subgroup.bot_subgroupOf]

omit [Finite G] in
theorem exists_coordEmb (D : Sp4Data X T M V K k) (hker : kerIn M X = ⊥) (hMX : M ≤ X)
    (hKX : K ≤ X) :
    ∃ φ : antiSp k →* G, Function.Injective φ ∧ φ.range = K ∧
      ∀ A : Subgroup G, A ≤ X → A.comap φ = coordIn D.θ A := by
  set q := QuotientGroup.mk' (kerIn (M.subgroupOf X) ⊤) with hq
  have hqi : Function.Injective q := mk'_kerIn_injective hker hMX
  let e₁ : ↥(K.subgroupOf X) ≃* ↥(barIn M X K) :=
    (K.subgroupOf X).equivMapOfInjective q hqi
  let e₂ : ↥(kZero X M) ≃* ↥(barIn M X K) := MulEquiv.subgroupCongr D.kZero_eq
  let φ : antiSp k →* G := X.subtype.comp ((K.subgroupOf X).subtype.comp
    (e₁.symm.toMonoidHom.comp (e₂.toMonoidHom.comp D.θ.symm.toMonoidHom)))
  have hφq : ∀ y : antiSp k, ∃ hx : φ y ∈ X,
      q ⟨φ y, hx⟩ = ((D.θ.symm y : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) := by
    intro y
    refine ⟨(e₁.symm (e₂ (D.θ.symm y)) : ↥X).2, ?_⟩
    have h1 := congrArg Subtype.val (e₁.apply_symm_apply (e₂ (D.θ.symm y)))
    exact h1
  refine ⟨φ, ?_, ?_, fun A hAX => ?_⟩
  · intro y z hyz
    apply D.θ.symm.injective
    apply e₂.injective
    apply e₁.symm.injective
    apply Subtype.ext
    exact X.subtype_injective hyz
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (e₁.symm (e₂ (D.θ.symm y))).2
    · intro hx
      obtain ⟨y, hy⟩ := D.θ.symm.surjective (e₂.symm (e₁ ⟨⟨x, hKX hx⟩,
        Subgroup.mem_subgroupOf.mpr hx⟩))
      refine ⟨y, ?_⟩
      change ((e₁.symm (e₂ (D.θ.symm y)) : ↥X) : G) = x
      rw [hy]
      simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · ext y
    rw [Subgroup.mem_comap, coordIn, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    obtain ⟨hx, hqx⟩ := hφq y
    change φ y ∈ A ↔ ((D.θ.symm y : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) ∈
      (A.subgroupOf X).map q
    rw [← hqx]
    constructor
    · intro h
      exact ⟨⟨φ y, hx⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · rintro ⟨x', hx', hxe⟩
      have := hqi hxe
      rw [this] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'

omit [Finite G] in
theorem comap_coordEmb_M (D : Sp4Data X T M V K k) {φ : antiSp k →* G}
    (hφ : Function.Injective φ) (hrange : φ.range = K)
    (hcomap : ∀ A : Subgroup G, A ≤ X → A.comap φ = coordIn D.θ A) (hTX : T ≤ X)
    (hMK : M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    T.comap φ = antiUnipotent k ∧
      M.comap φ = Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  have hT : T.comap φ = antiUnipotent k := (hcomap T hTX).trans D.sylow
  refine ⟨hT, ?_⟩
  have hTK : (antiUnipotent k).map φ = T ⊓ K := by
    rw [← hT, Subgroup.map_comap_eq, hrange, inf_comm]
  ext y
  have hyK : φ y ∈ K := hrange ▸ ⟨y, rfl⟩
  rw [Subgroup.mem_comap]
  constructor
  · intro hyM
    have h1 : φ y ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      hMK ▸ ⟨hyM, hyK⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h2 := Subgroup.mem_normalizer_iff.mp h1.2 (φ u)
    rw [← hTK] at h2
    constructor
    · intro hu
      obtain ⟨u', hu', hu'e⟩ := h2.mp ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul] at hu'e
      rwa [hφ hu'e] at hu'
    · intro hu
      have h3 : φ (y * u * y⁻¹) ∈ (antiUnipotent k).map φ := ⟨_, hu, rfl⟩
      rw [map_mul, map_mul, map_inv] at h3
      obtain ⟨u', hu', hu'e⟩ := h2.mpr h3
      rwa [hφ hu'e] at hu'
  · intro hyN
    have h1 : φ y ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hyK, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro w
      rw [← hTK]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN u).mp hu, by simp⟩
      · rintro ⟨u, hu, hue⟩
        have hw : w = φ (y⁻¹ * u * y) := by
          rw [map_mul, map_mul, map_inv, hue]
          group
        rw [hw]
        refine ⟨y⁻¹ * u * y, ?_, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) u).mp hu
        simpa using this
    exact (hMK ▸ h1 : φ y ∈ M ⊓ K).1

end Coord

section TypeThree

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiUnipotentCenter uElt antiSpEquiv antiUnipotentCenter_comm)
open CFSG.Quasithin.ASInputs (twoGen rootGroupOf IsSp4C)

omit [Finite G] in
theorem map_rootGroupOf_subtype_le {A : Type} [Group A] {Y : Subgroup A} (P : Subgroup ↥Y) :
    (rootGroupOf P).map Y.subtype ≤ rootGroupOf (P.map Y.subtype) := by
  have htw : (twoGen P).map Y.subtype = twoGen (P.map Y.subtype) := by
    rw [twoGen, twoGen, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hyP, m, hm⟩, rfl⟩
      exact ⟨⟨y, hyP, rfl⟩, m, by rw [← map_pow, hm, map_one]⟩
    · rintro ⟨⟨y, hyP, rfl⟩, m, hm⟩
      refine ⟨y, ⟨hyP, m, ?_⟩, rfl⟩
      apply Y.subtype_injective
      rw [map_pow, hm, map_one]
  rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
  refine ⟨htw ▸ ⟨z, hz1, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  rw [← htw] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  have := Subgroup.mem_centralizer_iff.mp hz2 x' hx'
  exact congrArg Subtype.val this

omit [Finite G] in
theorem inf_map_eq_map_comap_inf {A : Type} [Group A] {φ : A →* G} (hφ : Function.Injective φ)
    (B : Subgroup G) (Y : Subgroup A) : B ⊓ Y.map φ = (B.comap φ ⊓ Y).map φ := by
  rw [Subgroup.map_inf_eq _ _ _ hφ, Subgroup.map_comap_eq]
  apply le_antisymm
  · exact le_inf (le_inf (inf_le_right.trans (Subgroup.map_le_range φ Y)) inf_le_left)
      inf_le_right
  · exact inf_le_inf_right _ inf_le_right

variable {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite k] in
theorem inf_normalizer_antiUnipotent_eq {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c) :
    (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓
        Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ Subgroup.normalizer
        (((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓ antiUnipotent k : Subgroup _) :
          Set (antiSp k)) := by
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom
  apply le_antisymm
  · rintro y ⟨hyY, hyN⟩
    refine ⟨hyY, Subgroup.mem_normalizer_iff.mpr fun u => ?_⟩
    constructor
    · rintro ⟨huY, huU⟩
      exact ⟨Y.mul_mem (Y.mul_mem hyY huY) (Y.inv_mem hyY),
        (Subgroup.mem_normalizer_iff.mp hyN u).mp huU⟩
    · rintro ⟨huY, huU⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyN u).mpr huU⟩
      have := Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) huY) hyY
      simpa [mul_assoc] using this
  · rintro y ⟨hyY, hyN⟩
    exact ⟨hyY, mem_normalizer_of_isUpper (KG7.isUpper_of_mem_normalizer hc hyN)⟩

theorem isSp4C_subfieldSp {F₀ : Subfield k} (c : antiSp k) {m : ℕ} (hF₀ : Nat.card F₀ = 2 ^ m)
    (hm1 : 1 ≤ m) : IsSp4C m ↥((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) := by
  have : CharP ↥F₀ 2 := (F₀.subtype : ↥F₀ →+* k).charP Subtype.val_injective 2
  let eY : ↥((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ≃* StatedSp 2 ↥F₀ :=
    (((subfieldSp F₀).equivMapOfInjective _ (MulAut.conj c).injective).symm.trans
      (subfieldSpEquiv F₀).symm).trans (antiSpEquiv ↥F₀)
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by omega
    have := Fintype.ofFinite ↥F₀
    obtain ⟨f⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := ↥F₀) (by rw [← Nat.card_eq_fintype_card, hF₀, pow_one])
    exact Or.inr ⟨rfl, ⟨eY.trans f⟩⟩
  · refine Or.inl ⟨⟨Nat.prime_two, hm1, le_rfl, fun h => ?_⟩, ↥F₀, inferInstance, inferInstance,
      hF₀, ⟨eY.trans
        (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := ↥F₀) (n := 2) (by norm_num)).symm⟩⟩
    have h2 := congrArg Prod.snd h
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    simp only at h2
    omega

omit [Finite G] in
theorem map_inf_normalizer_map {A : Type} [Group A] {φ : A →* G} (hφ : Function.Injective φ)
    (Y S : Subgroup A) :
    Y.map φ ⊓ Subgroup.normalizer ((S.map φ : Subgroup G) : Set G) =
      (Y ⊓ Subgroup.normalizer (S : Set A)).map φ := by
  ext x
  constructor
  · rintro ⟨⟨y, hyY, rfl⟩, hyN⟩
    refine ⟨y, ⟨hyY, Subgroup.mem_normalizer_iff.mpr fun u => ?_⟩, rfl⟩
    have h := Subgroup.mem_normalizer_iff.mp hyN (φ u)
    constructor
    · intro hu
      obtain ⟨u', hu', hu'e⟩ := h.mp ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul] at hu'e
      rwa [hφ hu'e] at hu'
    · intro hu
      have h3 : φ (y * u * y⁻¹) ∈ S.map φ := ⟨_, hu, rfl⟩
      rw [map_mul, map_mul, map_inv] at h3
      obtain ⟨u', hu', hu'e⟩ := h.mpr h3
      rwa [hφ hu'e] at hu'
  · rintro ⟨y, ⟨hyY, hyN⟩, rfl⟩
    refine ⟨⟨y, hyY, rfl⟩, Subgroup.mem_normalizer_iff.mpr fun w => ?_⟩
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN u).mp hu, by simp⟩
    · rintro ⟨u, hu, hue⟩
      have hw : w = φ (y⁻¹ * u * y) := by
        rw [map_mul, map_mul, map_inv, hue]
        group
      rw [hw]
      refine ⟨y⁻¹ * u * y, ?_, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) u).mp hu
      simpa using this

theorem isInIHTVC_of_subfieldSp {X T M V : Subgroup G} {φ : antiSp k →* G}
    (hφ : Function.Injective φ) (hφX : φ.range ≤ X) (hT : T.comap φ = antiUnipotent k)
    (hM : M.comap φ = Subgroup.normalizer (antiUnipotent k : Set (antiSp k)))
    (hVr : V ≤ φ.range) {F₀ : Subfield k} {c g : antiSp k} (hc : IsUpper c)
    (hgY : g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom)
    (hY : V.comap φ ⊔ (V.comap φ).map (MulAut.conj g).toMonoidHom =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom)
    (hWZ : V.comap φ ≤ antiUnipotentCenter k) (hsp : SpansCenter (V.comap φ))
    (hSp : ∃ n : ℕ, IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot M X))))
    {m : ℕ} (hF₀ : Nat.card F₀ = 2 ^ m) (hm1 : 1 ≤ m)
    (hmn : ∃ d : ℕ, E1.nParam X = ((m * d : ℕ) : ℕ∞)) :
    ASInputs.IsInIHTVC X T M V (((subfieldSp F₀).map (MulAut.conj c).toMonoidHom).map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hYdef
  set W := V.comap φ with hWdef
  set I := Y.map φ with hIdef
  have hVW : W.map φ = V := Subgroup.map_comap_eq_self hVr
  have hWY : W ≤ Y := hY ▸ le_sup_left
  have hVI : V ≤ I := hVW ▸ Subgroup.map_mono hWY
  let eYI : ↥Y ≃* ↥I := Y.equivMapOfInjective φ hφ
  have heYI : ∀ y : ↥Y, ((eYI y : ↥I) : G) = φ y := fun _ => rfl
  have hTI : T ⊓ I = (Y ⊓ antiUnipotent k).map φ := by
    rw [inf_map_eq_map_comap_inf hφ, hT, inf_comm]
  have hMI : M ⊓ I = (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))).map φ := by
    rw [inf_map_eq_map_comap_inf hφ, hM, inf_comm]
  have hMI' : M ⊓ I = I ⊓ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
    rw [hMI, hTI, map_inf_normalizer_map hφ, inf_normalizer_antiUnipotent_eq hc]
  have hSY := isSylowOf_inf_antiUnipotent (F₀ := F₀) hc
  have hSI : IsSylowTwoOf (T ⊓ I) I := by
    rw [hTI, CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf]
    exact CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective φ hφ hSY
  have hker : kerIn (M ⊓ I) I = ⊥ := by
    rw [hMI]
    exact kerIn_map_eq_bot hφ (kerIn_inf_normalizer_eq_bot hc)
  have hgen : I = V ⊔ conjSub (φ g) V := by
    rw [hIdef, ← hY, Subgroup.map_sup, hVW, map_map_conj_eq, hVW]
    rfl
  have hVc : ∀ v ∈ V, ∀ t ∈ T ⊓ I, t * v = v * t := by
    intro v hv t ht
    rw [← hVW] at hv
    rw [hTI] at ht
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, hu, rfl⟩ := ht
    rw [← map_mul, ← map_mul, antiUnipotentCenter_comm (hWZ hw) hu.2]
  have hS2 : IsPGroup 2 ↥((T ⊓ I).subgroupOf I) :=
    hSI.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSI.1).symm
  set e := starQuotEquivOfBot hker with he
  set ε : StarQuot (M ⊓ I) I ≃* ↥Y := e.trans eYI.symm with hε
  have hεmk : ∀ x : ↥I, ε (QuotientGroup.mk' _ x) = eYI.symm x := fun x => by
    rw [hε, MulEquiv.trans_apply, starQuotEquivOfBot_mk]
  refine ⟨(Subgroup.map_le_range φ Y).trans hφX, ⟨φ g, ⟨g, hgY, rfl⟩, hgen⟩, hSI, ?_, m, hmn,
    Or.inr (Or.inr ⟨hSp, hm1, isSp4C_of_mulEquiv ε (isSp4C_subfieldSp c hF₀ hm1), ?_, ?_, ?_⟩)⟩
  ·
    rw [hker]
    have hb : pCoreOf 2 (⊥ : Subgroup G) = ⊥ :=
      le_bot_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)
    rw [hb]
    refine ⟨le_rfl, IsPGroup.of_bot, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  ·
    refine isBorelIn_of_map_equiv e ?_
    rw [map_star_starQuotEquivOfBot hker (M ⊓ I), hMI', Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq inf_le_right]
    refine ⟨(T ⊓ I).subgroupOf I, ⟨le_top, hS2, ?_⟩, by rw [top_inf_eq]⟩
    change ¬ 2 ∣ ((T ⊓ I).subgroupOf I).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hSI.2.2
  ·
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hVc v (Subgroup.mem_subgroupOf.mp hv) t
      (Subgroup.mem_subgroupOf.mp ht)))
  ·
    intro P hP hBP hVP
    set P₂ := (P.map ε.toMonoidHom).map Y.subtype with hP₂
    have hP₂max : IsMaxParabolic2 Y P₂ := by
      refine isMaxParabolic2_map_subtype le_rfl ?_
      rw [Subgroup.subgroupOf_self]
      exact isMaxParabolic2_map_equiv ε hP
    have hB₂ : Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) ≤ P₂ := by
      intro y hy
      have hφy : φ y ∈ M ⊓ I := hMI ▸ ⟨y, hy, rfl⟩
      have h1 : QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨φ y, hφy.2⟩ : ↥I) ∈ P :=
        hBP ⟨⟨φ y, hφy.2⟩, Subgroup.mem_subgroupOf.mpr hφy, rfl⟩
      refine ⟨⟨y, hy.1⟩, ⟨_, h1, ?_⟩, rfl⟩
      change ε (QuotientGroup.mk' _ ⟨φ y, hφy.2⟩) = ⟨y, hy.1⟩
      rw [hεmk]
      apply eYI.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hW₂ : W ≤ rootGroupOf P₂ := by
      intro w hw
      have hφw : φ w ∈ V := hw
      have h1 : QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨φ w, hVI hφw⟩ : ↥I) ∈
          rootGroupOf P := hVP ⟨⟨φ w, hVI hφw⟩, Subgroup.mem_subgroupOf.mpr hφw, rfl⟩
      have h2 : ε (QuotientGroup.mk' _ ⟨φ w, hVI hφw⟩) ∈ rootGroupOf (P.map ε.toMonoidHom) := by
        rw [← map_rootGroupOf_equiv]
        exact ⟨_, h1, rfl⟩
      rw [hεmk] at h2
      have h3 : eYI.symm ⟨φ w, hVI hφw⟩ = ⟨w, hWY hw⟩ := by
        apply eYI.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [h3] at h2
      exact map_rootGroupOf_subtype_le _ ⟨_, h2, rfl⟩
    exact KG7.not_le_rootGroupOf hc hWZ hsp hP₂max hB₂ hW₂

end TypeThree

end E2

end CFSG.Quasithin
