module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Members
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.LiftData
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoHall
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.LocalAnalysis.WeakClosure81.OddCentral
open scoped commutatorElement Pointwise

section Action
variable {G : Type} [Group G]

@[expose] def conjAut (I : Subgroup G) (k : G) (hk : k ∈ normalizer (I : Set G)) : MulAut ↥I where
  toFun a := ⟨k * a * k⁻¹, (mem_normalizer_iff.mp hk a).mp a.2⟩
  invFun a := ⟨k⁻¹ * a * k, by
    have := (mem_normalizer_iff.mp ((normalizer (I : Set G)).inv_mem hk) a).mp a.2
    simpa using this⟩
  left_inv a := by ext; simp only; group
  right_inv a := by ext; simp only; group
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

open Classical in
noncomputable def rho (I : Subgroup G) (k : G) : MulAut ↥I :=
  if hk : k ∈ normalizer (I : Set G) then conjAut I k hk else 1

theorem rho_apply {I : Subgroup G} {k : G} (hk : k ∈ normalizer (I : Set G)) (a : ↥I) :
    ((rho I k a : ↥I) : G) = k * a * k⁻¹ := by
  rw [rho, dif_pos hk]; rfl

theorem rho_mul {I : Subgroup G} {k₁ k₂ : G} (h₁ : k₁ ∈ normalizer (I : Set G))
    (h₂ : k₂ ∈ normalizer (I : Set G)) : rho I (k₁ * k₂) = rho I k₁ * rho I k₂ := by
  ext a
  rw [MulAut.mul_apply, rho_apply ((normalizer _).mul_mem h₁ h₂), rho_apply h₁, rho_apply h₂]
  group

theorem rho_one (I : Subgroup G) : rho I 1 = 1 := by
  ext a
  rw [rho_apply (normalizer _).one_mem]
  simp

theorem rho_inv {I : Subgroup G} {k : G} (hk : k ∈ normalizer (I : Set G)) :
    rho I k⁻¹ = (rho I k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rho_mul ((normalizer _).inv_mem hk) hk, inv_mul_cancel, rho_one]

theorem rho_conj {I : Subgroup G} {k g : G} (hk : k ∈ normalizer (I : Set G))
    (hg : g ∈ normalizer (I : Set G)) : rho I (k * g * k⁻¹) = rho I k * rho I g * (rho I k)⁻¹ := by
  rw [rho_mul ((normalizer _).mul_mem hk hg) ((normalizer _).inv_mem hk), rho_mul hk hg,
    rho_inv hk]

theorem rho_eq_one {I : Subgroup G} {k : G} (hk : k ∈ normalizer (I : Set G))
    (hc : ∀ a ∈ I, k * a = a * k) : rho I k = 1 := by
  ext a
  rw [rho_apply hk, hc a a.2]
  simp

theorem mem_centralizer_of_rho {I : Subgroup G} {k : G} (hk : k ∈ normalizer (I : Set G))
    (h : ∀ a : ↥I, rho I k a = a) : k ∈ centralizer (I : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  have := congrArg Subtype.val (h ⟨a, ha⟩)
  rw [rho_apply hk] at this
  calc a * k = k * a * k⁻¹ * k := by rw [this]
    _ = k * a := by group

@[reducible] def mulAutAdditive (M : Type*) [Monoid M] : DistribMulAction (MulAut M) (Additive M) where
  smul f a := Additive.ofMul (f a.toMul)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero f := by
    show Additive.ofMul (f 1) = Additive.ofMul 1
    rw [map_one]
  smul_add f a b := by
    show Additive.ofMul (f (a.toMul * b.toMul)) = Additive.ofMul (f a.toMul * f b.toMul)
    rw [map_mul]

@[reducible] def commGroupOf (I : Subgroup G) (h : IsMulCommutative I) : CommGroup ↥I :=
  { (inferInstance : Group ↥I) with
    mul_comm := fun a b => h.is_comm.comm a b }

end Action

theorem isPGroup_sup_zpowers {X : Type} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
  have hN : zpowers a ≤ normalizer (zpowers b : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    have hc : ∀ y ∈ zpowers b, a * y * a⁻¹ = y := fun y hy => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      rw [((Commute.zpow_right hab n)).eq]; group
    constructor
    · intro hy; rw [hc y hy]; exact hy
    · intro hy
      have := hc _ hy
      have e : y = a * y * a⁻¹ := by
        have h2 : a⁻¹ * (a * y * a⁻¹) * a = a⁻¹ * (a * y * a⁻¹) * a := rfl
        calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
          _ = a⁻¹ * (a * (a * y * a⁻¹) * a⁻¹) * a := by rw [this]
          _ = a * y * a⁻¹ := by group
      rw [e]; exact hy
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hx' : x ∈ ((zpowers a : Set X) * (zpowers b : Set X)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]; exact hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two, hb]
  have hc : Commute (a ^ m) (b ^ n) := (Commute.zpow_zpow hab m n)
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  show (a ^ m * b ^ n) ^ (2 ^ 1) = 1
  rw [pow_one, hc.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m,
    mul_comm n, zpow_mul, zpow_mul]
  simp [ha2, hb2]

section Main
variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G} {X : Type} [Group X]
  {φ : ↥(kSub V H E) →* X} {Y : Type} [Group Y] [Finite Y] {ι : Y →* X}

@[expose] def Over (φ : ↥(kSub V H E) →* X) (ι : Y →* X) (g : G) (y : Y) : Prop :=
  ∃ hg : g ∈ kSub V H E, φ ⟨g, hg⟩ = ι y

theorem over_mul {g g' : G} {y y' : Y} (h : Over φ ι g y) (h' : Over φ ι g' y') :
    Over φ ι (g * g') (y * y') := by
  obtain ⟨hg, hgy⟩ := h
  obtain ⟨hg', hgy'⟩ := h'
  refine ⟨(kSub V H E).mul_mem hg hg', ?_⟩
  rw [map_mul, ← hgy, ← hgy', ← map_mul]; rfl

theorem over_inv {g : G} {y : Y} (h : Over φ ι g y) : Over φ ι g⁻¹ y⁻¹ := by
  obtain ⟨hg, hgy⟩ := h
  refine ⟨(kSub V H E).inv_mem hg, ?_⟩
  rw [map_inv, ← hgy, ← map_inv]; rfl

theorem over_one : Over φ ι (1 : G) (1 : Y) := ⟨(kSub V H E).one_mem, by
  rw [map_one, show (⟨1, (kSub V H E).one_mem⟩ : ↥(kSub V H E)) = 1 from
    Subtype.ext (OneMemClass.coe_one _).symm, map_one]⟩

theorem over_conj {g k : G} {y e : Y} (h : Over φ ι g y) (hk : Over φ ι k e) :
    Over φ ι (k * g * k⁻¹) (e * y * e⁻¹) := over_mul (over_mul hk h) (over_inv hk)

theorem over_unique (hι : Function.Injective ι) {g : G} {y y' : Y} (h : Over φ ι g y)
    (h' : Over φ ι g y') : y = y' := by
  obtain ⟨hg, hgy⟩ := h
  obtain ⟨_, hgy'⟩ := h'
  exact hι (hgy.symm.trans hgy')

theorem over_one_iff (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {g : G} (hg : g ∈ kSub V H E) :
    Over φ ι g 1 ↔ g ∈ pCoreOf 2 (kSub V H E) := by
  constructor
  · rintro ⟨_, h⟩
    exact (hφ.ker_iff ⟨g, hg⟩).mp (by rw [h, map_one])
  · intro hJ
    exact ⟨hg, by rw [(hφ.ker_iff ⟨g, hg⟩).mpr hJ, map_one]⟩

theorem exists_over (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (y : Y) :
    ∃ g, Over φ ι g y := by
  obtain ⟨k, hk⟩ := hφ.surjective (ι y)
  exact ⟨k, k.2, hk⟩

@[expose] def preSub (φ : ↥(kSub V H E) →* X) (ι : Y →* X) (P : Subgroup Y) : Subgroup G where
  carrier := {g | ∃ y ∈ P, Over φ ι g y}
  one_mem' := ⟨1, P.one_mem, over_one⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y * y', P.mul_mem hy hy', over_mul h h'⟩
  inv_mem' := by
    rintro _ ⟨y, hy, h⟩
    exact ⟨y⁻¹, P.inv_mem hy, over_inv h⟩

theorem preSub_le_kSub (P : Subgroup Y) : preSub φ ι P ≤ kSub V H E := by
  rintro g ⟨y, -, hg, -⟩; exact hg

theorem le_preSub (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) (P : Subgroup Y) : pCoreOf 2 (kSub V H E) ≤ preSub φ ι P := by
  intro j hj
  have hjK := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E) hj
  exact ⟨1, P.one_mem, (over_one_iff hφ hι hjK).mpr hj⟩

noncomputable def preHom (hι : Function.Injective ι) (P : Subgroup Y) : ↥(preSub φ ι P) →* ↥P where
  toFun x := ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  map_one' := by
    apply Subtype.ext
    exact over_unique hι (Classical.choose_spec (preSub φ ι P).one_mem).2 over_one
  map_mul' x x' := by
    apply Subtype.ext
    exact over_unique hι (Classical.choose_spec (x * x').2).2
      (over_mul (Classical.choose_spec x.2).2 (Classical.choose_spec x'.2).2)

theorem preHom_spec (hι : Function.Injective ι) (P : Subgroup Y) (x : ↥(preSub φ ι P)) :
    Over φ ι (x : G) (preHom hι P x : Y) := (Classical.choose_spec x.2).2

theorem preHom_surjective (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) (P : Subgroup Y) : Function.Surjective (preHom (φ := φ) hι P) := by
  rintro ⟨p, hp⟩
  obtain ⟨g, hg⟩ := exists_over (ι := ι) hφ p
  refine ⟨⟨g, p, hp, hg⟩, Subtype.ext ?_⟩
  exact over_unique hι (preHom_spec hι P _) hg

theorem preHom_ker (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) (P : Subgroup Y) :
    (preHom (φ := φ) hι P).ker = (pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hxK := preSub_le_kSub P x.2
  constructor
  · intro h1
    have := preHom_spec hι P x
    rw [h1] at this
    exact (over_one_iff hφ hι hxK).mp this
  · intro hJ
    exact Subtype.ext (over_unique hι (preHom_spec hι P x) ((over_one_iff hφ hι hxK).mpr hJ))

theorem isNilpotent_of_comm_central {P : Subgroup Y}
    (hPnil : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ center Y) : Group.IsNilpotent ↥P := by
  apply Subgroup.isNilpotent_of_ker_le_center (Abelianization.of : ↥P →* Abelianization ↥P)
  rw [Abelianization.ker_of, commutator_eq_closure, closure_le]
  rintro _ ⟨a, b, rfl⟩
  rw [SetLike.mem_coe, mem_center_iff]
  intro g
  apply Subtype.ext
  have hc := mem_center_iff.mp (hPnil a a.2 b b.2) g
  simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
  exact hc

end Main

theorem mul_self_of_mem_card_two {X : Type} [Group X] {S : Subgroup X} (hS : Nat.card S = 2)
    {a : X} (ha : a ∈ S) : a * a = 1 := by
  have hdvd : orderOf a ∣ 2 := hS ▸ Subgroup.orderOf_dvd_natCard S ha
  rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd

theorem ne_one_of_isConj {Y : Type} [Group Y] {s e : Y} (hs1 : s ≠ 1) (h : IsConj s e) : e ≠ 1 := by
  rintro rfl
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact hs1 (by calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
    _ = 1 := by rw [hc]; group)

section Lift
variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G} {X : Type} [Group X]
  {φ : ↥(kSub V H E) →* X} {Y : Type} [Group Y] [Finite Y] {ι : Y →* X}

theorem kSub_le_H (h : Hyp711 V H E) : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le

theorem pCore_le_kSub : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
  CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E)

theorem iSub_le_H (h : Hyp711 V H E) : iSub V H E ≤ H :=
  h.iSub_le.trans (pCore_le_kSub.trans (kSub_le_H h))

theorem H_le_normalizer_iSub (h : Hyp711 V H E) : H ≤ normalizer (iSub V H E : Set G) :=
  CFSG.LocalAnalysis.WeakClosure81.le_normalizer_of_subgroupOf_normal (iSub_le_H h)
    (iSub_subgroupOf_normal h.le h.normal)

theorem H_le_normalizer_pCore (h : Hyp711 V H E) :
    H ≤ normalizer (pCoreOf 2 (kSub V H E) : Set G) :=
  CFSG.LocalAnalysis.WeakClosure81.le_normalizer_of_subgroupOf_normal
    (pCore_le_kSub.trans (kSub_le_H h)) h.jnormal

theorem normal_pCore_preSub (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    (P : Subgroup Y) : ((pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_preSub hφ hι P)).2
    ((preSub_le_kSub P).trans ((kSub_le_H h).trans (H_le_normalizer_pCore h)))

theorem mem_normalizer_preSub {P : Subgroup Y} [hP : P.Normal] {g : G} {e : Y}
    (hg : Over φ ι g e) : g ∈ normalizer (preSub φ ι P : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨e * y * e⁻¹, hP.conj_mem y hy e, over_conj hxy hg⟩
  · rintro ⟨y, hy, hxy⟩
    have := over_conj hxy (over_inv hg)
    refine ⟨e⁻¹ * y * e⁻¹⁻¹, hP.conj_mem y hy e⁻¹, ?_⟩
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem over_of_mem_member (h : Hyp711 V H E) (hι : Function.Injective ι)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    {u : G} {e : Y} (huU : u ∈ U) (hue : Over φ ι u e) (he1 : e ≠ 1) :
    barSub (kSub V H E) φ U = zpowers (ι e) ∧ ι e * ι e = 1 ∧
      ∀ x ∈ U, Over φ ι x 1 ∨ Over φ ι x e := by
  obtain ⟨huK, hu⟩ := hue
  have hcard := card_barSub_of_mem h hS hU
  have hmem : ι e ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨⟨u, huK⟩, huU, hu⟩
  have hne : ι e ≠ 1 := fun h1 => he1 (hι (h1.trans ι.map_one.symm))
  have hz := eq_zpowers_of_card_two hcard hmem hne
  have hsq := mul_self_of_mem_card_two hcard hmem
  refine ⟨hz, hsq, fun x hx => ?_⟩
  have hx' : φ ⟨x, le_kSub hU hx⟩ ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨_, hx, rfl⟩
  rw [hz] at hx'
  rcases eq_one_or_eq_of_mem_zpowers hsq hx' with h1 | h1
  · exact Or.inl ⟨_, h1.trans ι.map_one.symm⟩
  · exact Or.inr ⟨_, h1⟩

theorem hyp76_of (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y}
    [hJX : ((pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P)).Normal]
    (hPodd : Odd (Nat.card P)) (hPnil : Group.IsNilpotent P) {A : Subgroup G}
    (hAN : A ≤ normalizer (preSub φ ι P : Set G))
    (hAf : ∀ a ∈ A, (∀ x ∈ preSub φ ι P, ⁅a, x⁆ ∈ pCoreOf 2 (kSub V H E)) →
      a ∈ pCoreOf 2 (kSub V H E))
    (hAgen : A = ⨆ U ∈ omegaSet V H E, ⨆ (_ : U ≤ A), U) (hA2 : IsPGroup 2 A) :
    Hyp76 V H E (pCoreOf 2 (kSub V H E)) A (preSub φ ι P) := by
  have e : ↥(preSub φ ι P) ⧸ (pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P) ≃* ↥P :=
    (QuotientGroup.quotientMulEquivOfEq (preHom_ker hφ hι P).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (preHom_surjective hφ hι P))
  refine ⟨h.elemAbelian, h.ti, h.abelian, h.le, h.normal, h.omega_le, h.pcore_le, h.jnormal,
    h.iSub_le, le_preSub hφ hι P, (preSub_le_kSub P).trans (kSub_le_H h), hAN, ?_, ?_, hAf,
    hAgen, hA2⟩
  · rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
    exact hPodd
  · exact nilpotent_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem hyp76_bot (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y}
    [hJX : ((pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P)).Normal]
    (hPodd : Odd (Nat.card P)) (hPnil : Group.IsNilpotent P) :
    Hyp76 V H E (pCoreOf 2 (kSub V H E)) ⊥ (preSub φ ι P) :=
  hyp76_of h hφ hι hPodd hPnil bot_le
    (fun a ha _ => by rw [(Subgroup.mem_bot).mp ha]; exact one_mem _)
    (le_antisymm bot_le (iSup₂_le fun _ _ => iSup_le fun h => h)) IsPGroup.of_bot

theorem hyp76_member (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) (hS : Nat.card (barSub (kSub V H E) φ V) = 2)
    {P : Subgroup Y} [hP : P.Normal]
    [hJX : ((pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P)).Normal]
    (hPodd : Odd (Nat.card P)) (hPnil : Group.IsNilpotent P) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) {u : G} {e : Y} (huU : u ∈ U) (hue : Over φ ι u e) (he1 : e ≠ 1)
    (hmove : ∃ p ∈ P, e * p * e⁻¹ * p⁻¹ ≠ 1) :
    Hyp76 V H E (pCoreOf 2 (kSub V H E)) U (preSub φ ι P) := by
  obtain ⟨-, -, hov⟩ := over_of_mem_member h hι hS hU huU hue he1
  refine hyp76_of h hφ hι hPodd hPnil ?_ ?_ ?_
    (CFSG.Open.IsElemAbelian.isPGroup (isElemAbelian_of_mem_omegaSet h.elemAbelian hU))
  · intro x hx
    rcases hov x hx with h1 | h1
    · exact mem_normalizer_preSub h1
    · exact mem_normalizer_preSub h1
  · intro a ha hcomm
    rcases hov a ha with h1 | h1
    · exact (over_one_iff hφ hι h1.1).mp h1
    · exfalso
      obtain ⟨p, hp, hpne⟩ := hmove
      obtain ⟨x, hx⟩ := exists_over (ι := ι) hφ p
      have hc := hcomm x ⟨p, hp, hx⟩
      rw [commutatorElement_def] at hc
      have hov' : Over φ ι (a * x * a⁻¹ * x⁻¹) (e * p * e⁻¹ * p⁻¹) :=
        over_mul (over_conj hx h1) (over_inv hx)
      exact hpne (over_unique hι hov' ((over_one_iff hφ hι hov'.1).mpr hc))
  · exact le_antisymm (le_iSup₂_of_le U hU (le_iSup_of_le le_rfl le_rfl))
      (iSup₂_le fun _ _ => iSup_le fun h => h)

theorem exists_lift_hall (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    {P Ptil : Subgroup G} {Q : Subgroup Y} (hQ : P = preSub φ ι Q)
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) P Ptil) {y : Y} (hy : y ∈ Q) :
    ∃ q ∈ Ptil, Over φ ι q y := by
  subst hQ
  obtain ⟨g, hg⟩ := exists_over (ι := ι) hφ y
  have hgX : g ∈ Ptil ⊔ pCoreOf 2 (kSub V H E) := by rw [hY.sup_J]; exact ⟨y, hy, hg⟩
  have hPN : Ptil ≤ normalizer (pCoreOf 2 (kSub V H E) : Set G) :=
    hY.le_X.trans ((preSub_le_kSub Q).trans ((kSub_le_H h).trans (H_le_normalizer_pCore h)))
  have hgX' : g ∈ (Ptil : Set G) * (pCoreOf 2 (kSub V H E) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPN]; exact hgX
  obtain ⟨q, hq, j, hj, rfl⟩ := Set.mem_mul.mp hgX'
  have hj1 : Over φ ι j 1 := (over_one_iff hφ hι (pCore_le_kSub hj)).mpr hj
  have := over_mul hg (over_inv hj1)
  rw [inv_one, mul_one, mul_inv_cancel_right] at this
  exact ⟨q, hq, this⟩

noncomputable def theta (φ : ↥(kSub V H E) →* X) (ι : Y →* X) (Ptil : Subgroup G) (y : Y) :
    MulAut ↥(iSub V H E) :=
  open Classical in
  if hy : ∃ q ∈ Ptil, Over φ ι q y then rho (iSub V H E) (Classical.choose hy) else 1

@[expose] def LiftRel (φ : ↥(kSub V H E) →* X) (ι : Y →* X) (s : Y) (Ptil : Subgroup G)
    (w : MulAut ↥(iSub V H E)) (e : Y) : Prop :=
  ∃ U ∈ omegaSet V H E, ∃ u ∈ U, IsConj s e ∧ Over φ ι u e ∧
    u ∈ normalizer (Ptil : Set G) ∧ w = rho (iSub V H E) u

theorem rho_eq_of_over (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    {P Ptil : Subgroup G} (hPK : P ≤ kSub V H E)
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) P Ptil)
    {q q' : G} {y : Y} (hq : q ∈ Ptil) (hq' : q' ∈ Ptil) (hqy : Over φ ι q y)
    (hq'y : Over φ ι q' y) : rho (iSub V H E) q' = rho (iSub V H E) q := by
  have hIc : IsMulCommutative (iSub V H E) :=
    (seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le).1
  have hPN : Ptil ≤ normalizer (iSub V H E : Set G) :=
    hY.le_X.trans (hPK.trans ((kSub_le_H h).trans (H_le_normalizer_iSub h)))
  have hov : Over φ ι (q⁻¹ * q') 1 := by
    have := over_mul (over_inv hqy) hq'y
    rwa [inv_mul_cancel] at this
  have hi : q⁻¹ * q' ∈ iSub V H E := by
    rw [← hY.inf_J]
    exact ⟨Ptil.mul_mem (Ptil.inv_mem hq) hq', (over_one_iff hφ hι hov.1).mp hov⟩
  rw [show q' = q * (q⁻¹ * q') by group, rho_mul (hPN hq) (le_normalizer hi),
    rho_eq_one (le_normalizer hi) (fun a ha => Subgroup.mul_comm_of_mem_isMulCommutative _ hi ha),
    mul_one]

theorem theta_eq (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    {P Ptil : Subgroup G} (hPK : P ≤ kSub V H E)
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) P Ptil)
    {q : G} {y : Y} (hq : q ∈ Ptil) (hqy : Over φ ι q y) : theta φ ι Ptil y = rho (iSub V H E) q := by
  have hex : ∃ q ∈ Ptil, Over φ ι q y := ⟨q, hq, hqy⟩
  rw [theta, dif_pos hex]
  exact rho_eq_of_over h hφ hι hPK hY hq (Classical.choose_spec hex).1 hqy
    (Classical.choose_spec hex).2

theorem exists_liftRel (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : Y} (hsV : ι s ∈ barSub (kSub V H E) φ V)
    (hs1 : s ≠ 1) {P : Subgroup Y} [hP : P.Normal]
    [hJX : ((pCoreOf 2 (kSub V H E)).subgroupOf (preSub φ ι P)).Normal]
    (hPodd : Odd (Nat.card P)) (hPnil : Group.IsNilpotent P) {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil)
    (hmove : ∀ e, IsConj s e → ∃ p ∈ P, e * p * e⁻¹ * p⁻¹ ≠ 1) {e : Y} (hse : IsConj s e) :
    ∃ w, LiftRel φ ι s Ptil w e := by
  obtain ⟨v, hvV, hv⟩ := mem_barSub.mp hsV
  obtain ⟨c, rfl⟩ := isConj_iff.mp hse
  obtain ⟨k, hk⟩ := exists_over (ι := ι) hφ c
  have hvo : Over φ ι (v : G) s := ⟨v.2, hv⟩
  have hU : conjSubgroup V k⁻¹ ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem (H.inv_mem (kSub_le_H h hk.1))
  have huU : k * v * k⁻¹ ∈ conjSubgroup V k⁻¹ := by
    rw [CFSG.Quasithin.conjSubgroup]
    exact Subgroup.mem_map.mpr ⟨v, hvV, by simp [MulAut.conj_apply]⟩
  have hue := over_conj hvo hk
  have he1 := ne_one_of_isConj hs1 hse
  have h76 := hyp76_member h hφ hι hS hU huU hue he1 (hmove _ hse) (hPodd := hPodd)
    (hPnil := hPnil)
  have huJ : k * v * k⁻¹ ∉ pCoreOf 2 (kSub V H E) := fun hJ =>
    he1 (over_unique hι hue ((over_one_iff hφ hι hue.1).mpr hJ))
  obtain ⟨U', hU', -, d₁, hd₁U', -, hd₁N, hd₁J⟩ :=
    h76.exists_normalizing_rep hY ⟨_, hU, le_sup_left, huU, huJ⟩
  have hd₁ : Over φ ι d₁ (c * s * c⁻¹) := by
    have := over_mul hue ((over_one_iff hφ hι (pCore_le_kSub hd₁J)).mpr hd₁J)
    rwa [mul_one, mul_inv_cancel_left] at this
  exact ⟨_, U', hU', d₁, hd₁U', hse, hd₁, hd₁N, rfl⟩

theorem hall_le_normalizer_iSub (h : Hyp711 V H E) {P : Subgroup Y} {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil) :
    Ptil ≤ normalizer (iSub V H E : Set G) :=
  hY.le_X.trans ((preSub_le_kSub P).trans ((kSub_le_H h).trans (H_le_normalizer_iSub h)))

theorem theta_mul (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y} {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil) {x y : Y}
    (hx : x ∈ P) (hy : y ∈ P) : theta φ ι Ptil (x * y) = theta φ ι Ptil x * theta φ ι Ptil y := by
  obtain ⟨q, hq, hqx⟩ := exists_lift_hall h hφ hι rfl hY hx
  obtain ⟨q', hq', hq'y⟩ := exists_lift_hall h hφ hι rfl hY hy
  have hPN := hall_le_normalizer_iSub h hY
  rw [theta_eq h hφ hι (preSub_le_kSub P) hY (Ptil.mul_mem hq hq') (over_mul hqx hq'y),
    theta_eq h hφ hι (preSub_le_kSub P) hY hq hqx, theta_eq h hφ hι (preSub_le_kSub P) hY hq' hq'y,
    rho_mul (hPN hq) (hPN hq')]

theorem eq_one_of_theta (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y} {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil) {x : Y}
    (hx : x ∈ P) (hfix : ∀ a, theta φ ι Ptil x a = a) : x = 1 := by
  obtain ⟨q, hq, hqx⟩ := exists_lift_hall h hφ hι rfl hY hx
  rw [theta_eq h hφ hι (preSub_le_kSub P) hY hq hqx] at hfix
  have hqC := mem_centralizer_of_rho (hall_le_normalizer_iSub h hY hq) hfix
  have hqK : q ∈ kSub V H E := preSub_le_kSub P (hY.le_X hq)
  have hqJ := kSub_inf_centralizer_iSub_le_pCoreOf h ⟨hqK, hqC⟩
  exact over_unique hι hqx ((over_one_iff hφ hι hqK).mpr hqJ)

theorem theta_conj (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y} [hP : P.Normal] {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil) {s : Y}
    {w : MulAut ↥(iSub V H E)} {e : Y} (hw : LiftRel φ ι s Ptil w e) {p : Y} (hp : p ∈ P) :
    w * theta φ ι Ptil p * w⁻¹ = theta φ ι Ptil (e * p * e⁻¹) := by
  obtain ⟨U, hU, u, huU, -, hue, huN, rfl⟩ := hw
  obtain ⟨q, hq, hqp⟩ := exists_lift_hall h hφ hι rfl hY hp
  have huq : u * q * u⁻¹ ∈ Ptil := (mem_normalizer_iff.mp huN q).mp hq
  have huI : u ∈ normalizer (iSub V H E : Set G) := H_le_normalizer_iSub h (kSub_le_H h hue.1)
  rw [theta_eq h hφ hι (preSub_le_kSub P) hY hq hqp,
    theta_eq h hφ hι (preSub_le_kSub P) hY huq (over_conj hqp hue),
    rho_conj huI (hall_le_normalizer_iSub h hY hq)]

theorem liftRel_move (h : Hyp711 V H E) (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hι : Function.Injective ι) {P : Subgroup Y} {Ptil : Subgroup G}
    (hY : IsHallCompl V H E (pCoreOf 2 (kSub V H E)) (preSub φ ι P) Ptil) {s : Y}
    {w : MulAut ↥(iSub V H E)} {e : Y} (hw : LiftRel φ ι s Ptil w e) {p : Y} (hp : p ∈ P) :
    LiftRel φ ι s Ptil (theta φ ι Ptil p * w * (theta φ ι Ptil p)⁻¹) (p * e * p⁻¹) := by
  obtain ⟨U, hU, u, huU, hse, hue, huN, rfl⟩ := hw
  obtain ⟨q, hq, hqp⟩ := exists_lift_hall h hφ hι rfl hY hp
  have hqH : q ∈ H := kSub_le_H h (preSub_le_kSub P (hY.le_X hq))
  have huI : u ∈ normalizer (iSub V H E : Set G) := H_le_normalizer_iSub h (kSub_le_H h hue.1)
  refine ⟨conjSubgroup U q⁻¹, conjSubgroup_mem_omegaSet h.le h.normal hU (H.inv_mem hqH),
    q * u * q⁻¹, ?_, hse.trans (isConj_iff.mpr ⟨p, rfl⟩), over_conj hue hqp, ?_, ?_⟩
  · rw [CFSG.Quasithin.conjSubgroup]
    exact Subgroup.mem_map.mpr ⟨u, huU, by simp [MulAut.conj_apply]⟩
  · exact (normalizer _).mul_mem ((normalizer _).mul_mem (le_normalizer hq) huN)
      ((normalizer _).inv_mem (le_normalizer hq))
  · rw [theta_eq h hφ hι (preSub_le_kSub P) hY hq hqp,
      rho_conj (hall_le_normalizer_iSub h hY hq) huI]

theorem commute_of_liftRel (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : Y} (hs1 : s ≠ 1) {Ptil : Subgroup G}
    {w w' : MulAut ↥(iSub V H E)} {e e' : Y} (hw : LiftRel φ ι s Ptil w e)
    (hw' : LiftRel φ ι s Ptil w' e') (hee : e * e' = e' * e) : w * w' = w' * w := by
  obtain ⟨U, hU, u, huU, hse, hue, -, rfl⟩ := hw
  obtain ⟨U', hU', u', hu'U, hse', hu'e, -, rfl⟩ := hw'
  obtain ⟨hz, hsq, -⟩ := over_of_mem_member h hι hS hU huU hue (ne_one_of_isConj hs1 hse)
  obtain ⟨hz', hsq', -⟩ := over_of_mem_member h hι hS hU' hu'U hu'e (ne_one_of_isConj hs1 hse')
  have hc := commute_of_isPGroup h hφ hU hU'
    (by rw [hz, hz']; exact isPGroup_sup_zpowers hsq hsq' (by rw [← map_mul, hee, map_mul]))
    u huU u' hu'U
  have hN : ∀ {x : G}, x ∈ kSub V H E → x ∈ normalizer (iSub V H E : Set G) :=
    fun hx => H_le_normalizer_iSub h (kSub_le_H h hx)
  rw [← rho_mul (hN hue.1) (hN hu'e.1), hc, rho_mul (hN hu'e.1) (hN hue.1)]

theorem ti_of_liftRel (h : Hyp711 V H E) (hι : Function.Injective ι)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : Y} (hs1 : s ≠ 1) {Ptil : Subgroup G}
    {w w' : MulAut ↥(iSub V H E)} {e e' : Y} (hw : LiftRel φ ι s Ptil w e)
    (hw' : LiftRel φ ι s Ptil w' e') (hne : e ≠ e') (a b : ↥(iSub V H E))
    (hab : w a * a⁻¹ = w' b * b⁻¹) : w a * a⁻¹ = 1 := by
  obtain ⟨U, hU, u, huU, hse, hue, -, rfl⟩ := hw
  obtain ⟨U', hU', u', hu'U, hse', hu'e, -, rfl⟩ := hw'
  have hN : ∀ {x : G}, x ∈ kSub V H E → x ∈ normalizer (iSub V H E : Set G) :=
    fun hx => H_le_normalizer_iSub h (kSub_le_H h hx)
  have hab' := congrArg Subtype.val hab
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab'
  rw [rho_apply (hN hue.1), rho_apply (hN hu'e.1)] at hab'
  have h1 := commutator_mem_inf h hU huU a.2
  have h2 := commutator_mem_inf h hU' hu'U b.2
  have hUU : U ≠ U' := by
    rintro rfl
    obtain ⟨-, -, hov⟩ := over_of_mem_member h hι hS hU huU hue (ne_one_of_isConj hs1 hse)
    rcases hov u' hu'U with h' | h'
    · exact ne_one_of_isConj hs1 hse' (over_unique hι hu'e h')
    · exact hne (over_unique hι hu'e h').symm
  have hmem : u * a * u⁻¹ * (a : G)⁻¹ ∈ U ⊓ U' := ⟨h1.1, hab' ▸ h2.1⟩
  rw [inf_eq_bot_of_ne h hU hU' hUU] at hmem
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
  rw [rho_apply (hN hue.1)]
  exact (Subgroup.mem_bot).mp hmem

theorem false_of_frame_G (h : Hyp711 V H E)
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (hι : Function.Injective ι)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : Y} (hsV : ι s ∈ barSub (kSub V H E) φ V)
    (hs1 : s ≠ 1) {P Z₀ R : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal] [hRn : R.Normal]
    (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀) (hPodd : Odd (Nat.card P))
    {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdn : ∀ i j, i ≠ j → d i ≠ d j) {t : Y} (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀)
    (hRS : ∀ r ∈ R, ∀ x ∈ P, (d 0 * r * (d 0)⁻¹ * r⁻¹) * x * (d 0 * r * (d 0)⁻¹ * r⁻¹)⁻¹ *
      x⁻¹ ∈ Z₀)
    (hYR : ∀ y : Y, ∃ r ∈ R, ∃ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 ∧ y = r * g)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    (hmax : ∀ N : Subgroup Y, N.Normal → Z₀ ≤ N → N ≤ P → N = Z₀ ∨ N = P)
    (hnt : ∀ i, ∃ a ∈ InvSet P d i, a ≠ 1) (hds : ∀ i, IsConj s (d i))
    (hmove : ∀ e, IsConj s e → ∃ p ∈ P, e * p * e⁻¹ * p⁻¹ ≠ 1) : False := by
  classical
  have hPnil : Group.IsNilpotent P :=
    isNilpotent_of_comm_central (fun x hx y hy => hZc (hP' x hx y hy))
  haveI := normal_pCore_preSub h hφ hι P
  obtain ⟨Ptil, hY⟩ := (hyp76_bot h hφ hι hPodd hPnil (P := P)).exists_hallCompl
  have hIe := seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  letI iC : CommGroup ↥(iSub V H E) := commGroupOf _ hIe.1
  letI iA : DistribMulAction (MulAut ↥(iSub V H E)) (Additive ↥(iSub V H E)) :=
    mulAutAdditive _
  have hL : LiftData (Additive ↥(iSub V H E)) P (theta φ ι Ptil) (LiftRel φ ι s Ptil) :=
    { hom := fun x hx y hy => theta_mul h hφ hι hY hx hy
      faithful := fun x hx hfix => eq_one_of_theta h hφ hι hY hx
        (fun a => Additive.ofMul.injective (hfix (Additive.ofMul a)))
      conj := fun w e hw p hp => theta_conj h hφ hι hY hw hp
      move := fun w e hw p hp => liftRel_move h hφ hι hY hw hp
      ti := fun w e w' e' hw hw' hne a b hab => by
        have hab' := congrArg Additive.toMul hab
        change w a.toMul / a.toMul = w' b.toMul / b.toMul at hab'
        rw [div_eq_mul_inv, div_eq_mul_inv] at hab'
        have key := ti_of_liftRel h hι hS hs1 hw hw' hne a.toMul b.toMul hab'
        apply Additive.toMul.injective
        change w a.toMul / a.toMul = 1
        rw [div_eq_mul_inv]
        exact key }
  have h2 : ∀ a : Additive ↥(iSub V H E), a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← pow_two]
    exact hIe.2 _ a.toMul.2
  have hframe : ∀ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 →
      ∃ w : Fin 3 → MulAut ↥(iSub V H E), (∀ i, LiftRel φ ι s Ptil (w i) (g * d i * g⁻¹)) ∧
        ∀ i j, w i * w j = w j * w i := by
    intro g _
    have hex : ∀ i, ∃ w, LiftRel φ ι s Ptil w (g * d i * g⁻¹) := fun i =>
      exists_liftRel h hφ hι hS hsV hs1 hPodd hPnil hY hmove
        ((hds i).trans (isConj_iff.mpr ⟨g, rfl⟩))
    choose w hw using hex
    refine ⟨w, hw, fun i j => commute_of_liftRel h hφ hι hS hs1 (hw i) (hw j) ?_⟩
    rw [show g * d i * g⁻¹ * (g * d j * g⁻¹) = g * (d i * d j) * g⁻¹ by group, hdc i j]
    group
  exact hL.false_of_frame h2 hZc hZP hP' hPodd hd hdc hdn ht hc hLA hRS hYR hgen hmax hnt hframe

end Lift

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
