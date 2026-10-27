module

public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.H13.NQCat.LieThompson

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.Uniqueness.Bender (autFixed mem_autFixed_congr_iff)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def ThompsonModel (K : Type) [Group K] : Prop :=
  IsCyclic (Outer K) ∧
    ∀ P : Subgroup K, IsSylowTwoOf P ⊤ →
      (∃ E : Subgroup K, E ≤ P ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
        E ≤ Subgroup.centralizer (P : Set K)) →
      ∀ α : MulAut K, α * α = 1 → α ∉ OuterAutomorphisms.inner K → P.map α.toMonoidHom = P →
        ∃ E₀ : Subgroup K, E₀ ≤ P ∧ IsElemAbelian 2 E₀ ∧
          2 * Nat.card ↥(P ⊓ autFixed α) < Nat.card E₀

@[expose] def InnerOn {G : Type*} [Group G] (K : Subgroup G) (a : G) : Prop :=
  ∃ g ∈ K, ∀ x ∈ K, a * x * a⁻¹ = g * x * g⁻¹

section ElemAbelian

variable {G : Type*} [Group G]

theorem mul_self_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E) :
    x * x = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hE hx

theorem comm_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

theorem isElemAbelian_of_forall {E : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by rw [sq]; exact hs x hx⟩

theorem isElemAbelian_mono {E F : Subgroup G} (h : E ≤ F) (hF : IsElemAbelian 2 F) :
    IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hF h

theorem isElemAbelian_map {H : Type*} [Group H] (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_subgroupOf {E : Subgroup G} (K : Subgroup G) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {z : G}
    (hz : z ∈ H ⊔ K) : ∃ x ∈ H, ∃ y ∈ K, z = x * y := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hr : (MonoidHom.noncommCoprod H.subtype K.subtype comm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hr] at hz
  obtain ⟨⟨m, n⟩, rfl⟩ := hz
  exact ⟨m, m.2, n, n.2, rfl⟩

theorem card_sup_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hd : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have comm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype comm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hd
  have hr : (MonoidHom.noncommCoprod H.subtype K.subtype comm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isElemAbelian_sup {H K : Subgroup G} (hH : IsElemAbelian 2 H) (hK : IsElemAbelian 2 K)
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : IsElemAbelian 2 (H ⊔ K) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hH hK hc

theorem card_le_two_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C)
    (hH : ∀ x ∈ H, x * x = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_le_of_pow_eq_one (by norm_num) (Subtype.ext (by simpa [sq] using hH g g.2))

theorem mem_normalizer_inf {H K : Subgroup G} {a : G}
    (h1 : a ∈ Subgroup.normalizer (H : Set G)) (h2 : a ∈ Subgroup.normalizer (K : Set G)) :
    a ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_iff.2 fun x =>
    ⟨fun hx => ⟨(Subgroup.mem_normalizer_iff.1 h1 x).1 hx.1,
        (Subgroup.mem_normalizer_iff.1 h2 x).1 hx.2⟩,
      fun hx => ⟨(Subgroup.mem_normalizer_iff.1 h1 x).2 hx.1,
        (Subgroup.mem_normalizer_iff.1 h2 x).2 hx.2⟩⟩

theorem mem_centralizer_sup {K K' : Subgroup G} {w : G}
    (h1 : w ∈ Subgroup.centralizer (K : Set G)) (h2 : w ∈ Subgroup.centralizer (K' : Set G)) :
    w ∈ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) := by
  have hle : K ⊔ K' ≤ Subgroup.centralizer ({w} : Set G) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 h1 k hk))
      fun k hk => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 h2 k hk)
  exact Subgroup.mem_centralizer_iff.2 fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem exists_max_elemAbelian [Finite G] (P : Subgroup G) :
    ∃ M ≤ P, IsElemAbelian 2 M ∧ ∀ X ≤ P, IsElemAbelian 2 X → Nat.card X ≤ Nat.card M := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Nonempty {X : Subgroup G // X ≤ P ∧ IsElemAbelian 2 X} :=
    ⟨⟨⊥, bot_le, isElemAbelian_of_forall
      (fun _ hx _ hy => by rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy])
      fun _ hx => by rw [Subgroup.mem_bot.1 hx, one_mul]⟩⟩
  obtain ⟨⟨M, hMP, hM⟩, hmax⟩ :=
    Finite.exists_max (fun X : {X : Subgroup G // X ≤ P ∧ IsElemAbelian 2 X} => Nat.card X.1)
  exact ⟨M, hMP, hM, fun X hX hXe => hmax ⟨X, hX, hXe⟩⟩

end ElemAbelian

theorem ThompsonModel.of_mulEquiv {K L : Type} [Group K] [Group L] [Finite K] (e : K ≃* L)
    (h : ThompsonModel L) : ThompsonModel K := by
  have : Finite L := Finite.of_equiv K e.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun P hP hE α hα2 hα hαP => ?_⟩
  · have := h.1
    exact isCyclic_of_surjective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.toMonoidHom
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.surjective
  obtain ⟨E, hEP, hEe, hE16, hEC⟩ := hE
  set f : K →* L := e.toMonoidHom with hf
  set α' : MulAut L := MulAut.congr e α with hα'
  have hcomp : α'.toMonoidHom.comp f = f.comp α.toMonoidHom := by
    ext x
    simp [hα', hf, MulAut.congr_apply]
  have hP' : IsSylowTwoOf (P.map f) ⊤ := by
    have h1 := Setup.X6.isSylowOf_map_injective (p := 2) f e.injective
      (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hP)
    rw [Subgroup.map_top_of_surjective f e.surjective] at h1
    exact Setup.X6.isSylowTwoOf_iff_isSylowOf.2 h1
  have hEC' : E.map f ≤ Subgroup.centralizer ((P.map f : Subgroup L) : Set L) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hEC hx) y hy]
  have hα'2 : α' * α' = 1 := by rw [hα', ← map_mul, hα2, map_one]
  have hα'out : α' ∉ OuterAutomorphisms.inner L := by
    rintro ⟨y, hy⟩
    apply hα
    refine ⟨e.symm y, ?_⟩
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e.symm y, hy]
    ext x
    simp [hα', MulAut.congr_apply]
  have hα'P : (P.map f).map α'.toMonoidHom = P.map f := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hαP]
  obtain ⟨E₀, hE₀P, hE₀, hlt⟩ := h.2 (P.map f) hP'
    ⟨E.map f, Subgroup.map_mono hEP, isElemAbelian_map f hEe,
      by rw [Subgroup.card_map_of_injective e.injective]; exact hE16, hEC'⟩ α' hα'2 hα'out hα'P
  have hfix : (P ⊓ autFixed α).map f = P.map f ⊓ autFixed α' := by
    rw [Subgroup.map_inf_eq _ _ f e.injective]
    congr 1
    ext y
    rw [mem_autFixed_congr_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hf] using hx
    · intro hy
      exact ⟨e.symm y, hy, by simp [hf]⟩
  refine ⟨E₀.map e.symm.toMonoidHom, ?_, isElemAbelian_map _ hE₀, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hE₀P hy
    simpa [hf] using hz
  · have hc : Nat.card ↥(P ⊓ autFixed α) = Nat.card ↥(P.map f ⊓ autFixed α') := by
      rw [← hfix, Subgroup.card_map_of_injective e.injective]
    rw [hc, Subgroup.card_map_of_injective e.symm.injective]
    exact hlt

section Count

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_forall_comm {K E : Subgroup G} (hK : IsSimpleGroup ↥K) (hEK : E ≤ K)
    (hE : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) {z : G} (hz : z ∈ K)
    (hzc : ∀ x ∈ K, z * x = x * z) : z = 1 := by
  rcases hK.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
  · have hz' : (⟨z, hz⟩ : K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.2 fun x => Subtype.ext (hzc x x.2).symm
    rw [h, Subgroup.mem_bot] at hz'
    exact congrArg Subtype.val hz'
  · exfalso
    have hcomm : ∀ x y : K, x * y = y * x := fun x y => by
      have hx : x ∈ Subgroup.center ↥K := h ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.1 hx y).symm
    obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hE0 : E = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx)
      rw [hE0, Subgroup.card_bot] at hE16
      norm_num at hE16
    have hN : (Subgroup.zpowers (⟨e, hEK he⟩ : K)).Normal :=
      ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
    rcases hK.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (⟨e, hEK he⟩ : K)) with h1 | h1
    · apply he1
      have h2 : (⟨e, hEK he⟩ : K) ∈ Subgroup.zpowers (⟨e, hEK he⟩ : K) :=
        Subgroup.mem_zpowers _
      rw [h1, Subgroup.mem_bot] at h2
      exact congrArg Subtype.val h2
    · have h2 : Nat.card ↥(Subgroup.zpowers (⟨e, hEK he⟩ : K)) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num)
          (Subtype.ext (by simpa [sq] using mul_self_of_elemAbelian hE he))
      rw [h1, Subgroup.card_top] at h2
      have h3 : Nat.card E ≤ Nat.card K := Subgroup.card_le_of_le hEK
      omega

theorem mem_of_mem_normalizer {P K : Subgroup G} (hP : IsSylowTwoOf P K) {g : G} (hgK : g ∈ K)
    (hgN : g ∈ Subgroup.normalizer (P : Set G)) (hg : g * g = 1) : g ∈ P := by
  have hx : IsPGroup 2 (Subgroup.zpowers g) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hg, one_zpow]
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hgN
  have hpg := IsPGroup.to_sup_of_normal_left' hP.2.1 hx hle
  have heq := hP.eq_of_le le_sup_left
    (sup_le hP.1 (by rw [Subgroup.zpowers_le]; exact hgK)) hpg
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem exists_of_innerOn {K P : Subgroup G} (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1)
    (hP : IsSylowTwoOf P K) {a : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (ha2 : a * a = 1) (h : InnerOn K a) :
    ∃ g ∈ P, g * g = 1 ∧ g * a = a * g ∧ g⁻¹ * a ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨g, hgK, hg⟩ := h
  have hg2 : g * g = 1 := by
    refine hZ _ (mul_mem hgK hgK) fun x hx => ?_
    have hax : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 haK x).1 hx
    have e1 : a * (a * x * a⁻¹) * a⁻¹ = x := by
      calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [ha2]; group
    have e2 : a * (a * x * a⁻¹) * a⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
      rw [hg _ hax, hg x hx]
    calc g * g * x = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = x * (g * g) := by rw [← e2, e1]
  have hgN : g ∈ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hg x (hP.1 hx)]
      exact (Subgroup.mem_normalizer_iff.1 haP x).1 hx
    · have hxK : x ∈ K := by
        have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ K :=
          mul_mem (mul_mem (inv_mem hgK) (hP.1 hx)) hgK
        simpa [mul_assoc] using h1
      rw [← hg x hxK] at hx
      exact (Subgroup.mem_normalizer_iff.1 haP x).2 hx
  refine ⟨g, mem_of_mem_normalizer hP hgK hgN hg2, hg2, ?_, ?_⟩
  · have h1 := hg g hgK
    calc g * a = (g * g * g⁻¹) * a := by group
      _ = (a * g * a⁻¹) * a := by rw [h1]
      _ = a * g := by group
  · refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    calc x * (g⁻¹ * a) = g⁻¹ * (g * x * g⁻¹) * a := by group
      _ = g⁻¹ * (a * x * a⁻¹) * a := by rw [hg x hx]
      _ = g⁻¹ * a * x := by group

@[expose] noncomputable def conjOn {K A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) : ↥A →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hA)

omit [Finite G] in
theorem coe_conjOn_apply {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G)) (a : A)
    (x : K) : ((conjOn hA a x : K) : G) = (a : G) * x * (a : G)⁻¹ :=
  rfl

omit [Finite G] in
theorem conjOn_eq_one_iff {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G)) (a : A) :
    conjOn hA a = 1 ↔ (a : G) ∈ Subgroup.centralizer (K : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have h1 := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : G)) h
    simp only [coe_conjOn_apply, MulAut.one_apply] at h1
    calc x * a = (a : G) * x * (a : G)⁻¹ * a := by rw [h1]
      _ = a * x := by group
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_conjOn_apply, MulAut.one_apply, ← Subgroup.mem_centralizer_iff.1 h x x.2]
    group

omit [Finite G] in
theorem innerOn_iff {K A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G)) (a : A) :
    InnerOn K a ↔ conjOn hA a ∈ OuterAutomorphisms.inner K := by
  constructor
  · rintro ⟨g, hgK, hg⟩
    refine ⟨⟨g, hgK⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [coe_conjOn_apply, hg x x.2]
    rfl
  · rintro ⟨g, hg⟩
    refine ⟨g, g.2, fun x hx => ?_⟩
    have h1 := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : G)) hg
    simp only [coe_conjOn_apply] at h1
    exact h1.symm

theorem relIndex_centralizer_le {K P A M E : Subgroup G}
    (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1) (hT : ThompsonModel ↥K)
    (hP : IsSylowTwoOf P K) (hEP : E ≤ P) (hE : IsElemAbelian 2 E) (hE16 : Nat.card E = 16)
    (hEC : E ≤ Subgroup.centralizer (P : Set G))
    (hM : ∀ X ≤ P, IsElemAbelian 2 X → Nat.card X ≤ Nat.card M)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hA : IsElemAbelian 2 A) :
    (Subgroup.centralizer (K : Set G)).relIndex A ≤ Nat.card M ∧
      ((∃ a ∈ A, ¬ InnerOn K a) →
        (Subgroup.centralizer (K : Set G)).relIndex A < Nat.card M) := by
  have := hT.1
  set φ := conjOn hAK with hφ
  set D := φ.range with hD
  have hcard : (Subgroup.centralizer (K : Set G)).relIndex A = Nat.card D := by
    have hker : φ.ker = (Subgroup.centralizer (K : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact conjOn_eq_one_iff hAK a
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hsq : ∀ α ∈ D, α * α = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, show a * a = 1 from Subtype.ext (mul_self_of_elemAbelian hA a.2), map_one]
  have hcomm : ∀ α ∈ D, ∀ β ∈ D, α * β = β * α := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from
      Subtype.ext (comm_of_elemAbelian hA a.2 b.2)]
  set P' : Subgroup K := P.subgroupOf K with hP'
  have hnorm : ∀ α ∈ D, P'.map α.toMonoidHom = P' := by
    rintro _ ⟨a, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ P := hy
      change ((φ a y : K) : G) ∈ P
      exact (Subgroup.mem_normalizer_iff.1 (hAP a.2) y).1 hy'
    · intro hx
      rw [hP', Subgroup.mem_subgroupOf] at hx
      have hxK : (a : G)⁻¹ * x * a ∈ K := by
        simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem (hAK a.2)) x).1 x.2
      have hxP : (a : G)⁻¹ * x * a ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem (hAP a.2)) x).1 hx
      refine ⟨⟨_, hxK⟩, (Subgroup.mem_subgroupOf).2 hxP, Subtype.ext ?_⟩
      change (a : G) * ((a : G)⁻¹ * x * a) * (a : G)⁻¹ = x
      group
  have hinn : ∀ α ∈ D, α ∈ OuterAutomorphisms.inner K →
      ∃ g : K, (g : G) ∈ P ∧ α = MulAut.conj g := by
    rintro _ ⟨a, rfl⟩ hin
    obtain ⟨g, hgP, -, -, hc⟩ := exists_of_innerOn hZ hP (hAK a.2) (hAP a.2)
      (mul_self_of_elemAbelian hA a.2) ((innerOn_iff hAK a).2 hin)
    refine ⟨⟨g, hP.1 hgP⟩, hgP, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [coe_conjOn_apply]
    change (a : G) * x * (a : G)⁻¹ = g * x * g⁻¹
    have h1 := Subgroup.mem_centralizer_iff.1 hc x x.2
    calc (a : G) * x * (a : G)⁻¹ = g * (g⁻¹ * a * x) * (a : G)⁻¹ := by group
      _ = g * (x * (g⁻¹ * a)) * (a : G)⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ := by group
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine hZ g g.2 fun x hx => ?_
    have h1 := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : G)) hg
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * g := by group
      _ = x * g := by rw [h1]
  set X : Subgroup K := D.comap (MulAut.conj : K →* MulAut K) with hX
  have hXmap : X.map (MulAut.conj : K →* MulAut K) = D ⊓ OuterAutomorphisms.inner K := by
    ext α
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg, g, rfl⟩
    · rintro ⟨hαD, g, rfl⟩
      exact ⟨g, hαD, rfl⟩
  have hXcard : Nat.card X = Nat.card ↥(D ⊓ OuterAutomorphisms.inner K) := by
    rw [← hXmap, Subgroup.card_map_of_injective hinj]
  have hXP : ∀ g ∈ X, (g : G) ∈ P := by
    intro g hg
    obtain ⟨g', hg'P, hg'⟩ := hinn _ hg ⟨g, rfl⟩
    rw [hinj hg']
    exact hg'P
  have hXe : IsElemAbelian 2 X := by
    refine isElemAbelian_of_forall (fun x hx y hy => hinj ?_) fun x hx => hinj ?_
    · rw [map_mul, map_mul]
      exact hcomm _ hx _ hy
    · rw [map_mul, map_one]
      exact hsq _ hx
  have hXM : Nat.card X ≤ Nat.card M := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    refine hM _ ?_ (isElemAbelian_map _ hXe)
    rintro _ ⟨g, hg, rfl⟩
    exact hXP g hg
  have hout : ∀ α ∈ D, α ∉ OuterAutomorphisms.inner K → Nat.card D < Nat.card M := by
    intro α hαD hα
    have h2 : Nat.card D ≤ 2 * Nat.card ↥(D ⊓ OuterAutomorphisms.inner K) := by
      let ψ : D →* Outer K := (QuotientGroup.mk' (OuterAutomorphisms.inner K)).comp D.subtype
      have hker : ψ.ker = (D ⊓ OuterAutomorphisms.inner K).subgroupOf D := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        simp only [ψ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      have h1 := Subgroup.card_mul_index ψ.ker
      rw [Subgroup.index_ker, hker,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
      have hr : Nat.card ψ.range ≤ 2 := by
        refine card_le_two_of_isCyclic ψ.range ?_
        rintro _ ⟨x, rfl⟩
        rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x x.2), map_one]
      rw [← h1]
      nlinarith
    have hXfix : X ≤ P' ⊓ autFixed α := by
      intro g hg
      refine ⟨(Subgroup.mem_subgroupOf).2 (hXP g hg), ?_⟩
      apply hinj
      change MulAut.conj (α g) = MulAut.conj g
      have h1 : α * MulAut.conj g * α⁻¹ = MulAut.conj g := by
        rw [hcomm α hαD _ hg, mul_inv_cancel_right]
      rw [← h1]
      ext y
      simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
    obtain ⟨E₀, hE₀P, hE₀, hlt⟩ := hT.2 P' (Setup.X6.isSylowTwoOf_subgroupOf_top hP)
      ⟨E.subgroupOf K,
        fun x hx => (Subgroup.mem_subgroupOf).2 (hEP ((Subgroup.mem_subgroupOf).1 hx)),
        isElemAbelian_subgroupOf K hE,
        by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEP.trans hP.1)).toEquiv]; exact hE16,
        fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
          Subtype.ext (Subgroup.mem_centralizer_iff.1 (hEC hx) y hy)⟩
      α (hsq α hαD) hα (hnorm α hαD)
    have hE₀M : Nat.card E₀ ≤ Nat.card M := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective]
      refine hM _ ?_ (isElemAbelian_map _ hE₀)
      rintro _ ⟨g, hg, rfl⟩
      exact hE₀P hg
    calc Nat.card D ≤ 2 * Nat.card ↥(D ⊓ OuterAutomorphisms.inner K) := h2
      _ = 2 * Nat.card X := by rw [hXcard]
      _ ≤ 2 * Nat.card ↥(P' ⊓ autFixed α) := by
        gcongr
        exact Subgroup.card_le_of_le hXfix
      _ < Nat.card E₀ := hlt
      _ ≤ Nat.card M := hE₀M
  refine ⟨?_, fun ⟨a, ha, hna⟩ => ?_⟩
  · rw [hcard]
    by_cases hDI : D ≤ OuterAutomorphisms.inner K
    · rw [← inf_eq_left.2 hDI, ← hXcard]
      exact hXM
    · obtain ⟨α, hαD, hα⟩ := Set.not_subset.1 hDI
      exact (hout α hαD hα).le
  · rw [hcard]
    exact hout (φ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ fun hin => hna ((innerOn_iff hAK ⟨a, ha⟩).2 hin)

omit [Finite G] in
theorem mem_of_mem_sup_of_mem_centralizer {K K' : Subgroup G}
    (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1)
    (hK'C : K' ≤ Subgroup.centralizer (K : Set G)) {y : G} (hy : y ∈ K ⊔ K')
    (hyC : y ∈ Subgroup.centralizer (K : Set G)) : y ∈ K' := by
  obtain ⟨k, hk, k', hk', rfl⟩ := exists_mul_of_mem_sup
    (fun x hx z hz => Subgroup.mem_centralizer_iff.1 (hK'C hz) x hx) hy
  have hkC : k ∈ Subgroup.centralizer (K : Set G) := by
    have h1 := mul_mem hyC (inv_mem (hK'C hk'))
    rwa [mul_inv_cancel_right] at h1
  have hk1 : k = 1 := hZ k hk fun x hx => (Subgroup.mem_centralizer_iff.1 hkC x hx).symm
  rw [hk1, one_mul]
  exact hk'

omit [Finite G] in
theorem mem_normalizer_of_map_eq {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, rfl⟩
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [(MulAut.conj g).injective (hyx.trans (MulAut.conj_apply g x).symm)] at hy

omit [Finite G] in
theorem map_conj_mul (K : Subgroup G) (x y : G) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext z
  simp

theorem map_conj_eq_or_eq {K K' : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1)
    (hK'C : K' ≤ Subgroup.centralizer (K : Set G)) (hcard : Nat.card K' = Nat.card K) {a : G}
    (ha : a ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G)) :
    K.map (MulAut.conj a).toMonoidHom = K ∨ K.map (MulAut.conj a).toMonoidHom = K' := by
  have hLcard : Nat.card ↥(K.map (MulAut.conj a).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hKN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (hK'C.trans (Subgroup.centralizer_le_normalizer _))
  have hLN : ∀ y ∈ K ⊔ K', ∀ l ∈ K.map (MulAut.conj a).toMonoidHom,
      y * l * y⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom := by
    intro y hy l hl
    obtain ⟨k, hk, rfl⟩ := hl
    have hy' : a⁻¹ * y * a ∈ K ⊔ K' := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) y).1 hy
      rwa [inv_inv] at h1
    refine ⟨(a⁻¹ * y * a) * k * (a⁻¹ * y * a)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hKN hy') k).1 hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hLle : K.map (MulAut.conj a).toMonoidHom ≤ K ⊔ K' := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 ha k).1 (Subgroup.mem_sup_left hk)
  have hnormal : ((K.map (MulAut.conj a).toMonoidHom ⊓ K).subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨hLN g (Subgroup.mem_sup_left g.2) n hn.1,
        (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer g.2) n).1 hn.2⟩⟩
  rcases hK.eq_bot_or_eq_top_of_normal ((K.map (MulAut.conj a).toMonoidHom ⊓ K).subgroupOf K)
    with h | h
  · right
    have hLC : K.map (MulAut.conj a).toMonoidHom ≤ Subgroup.centralizer (K : Set G) := by
      intro l hl
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have h1 : l * k * l⁻¹ * k⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom ⊓ K := by
        refine ⟨?_, ?_⟩
        · have h3 := mul_mem hl (hLN k (Subgroup.mem_sup_left hk) l⁻¹ (inv_mem hl))
          simpa [mul_assoc] using h3
        · exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hKN (hLle hl)) k).1 hk) (K.inv_mem hk)
      have h2 : (⟨_, h1.2⟩ : K) ∈ (K.map (MulAut.conj a).toMonoidHom ⊓ K).subgroupOf K := h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : l * k * l⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h2
      calc k * l = (l * k * l⁻¹ * k⁻¹)⁻¹ * l * k := by group
        _ = l * k := by rw [h3, inv_one, one_mul]
    exact Subgroup.eq_of_le_of_card_ge
      (fun l hl => mem_of_mem_sup_of_mem_centralizer hZ hK'C (hLle hl) (hLC hl))
      (hcard.trans hLcard.symm).le
  · left
    have hKL : K ≤ K.map (MulAut.conj a).toMonoidHom := fun k hk => by
      have h1 : (⟨k, hk⟩ : K) ∈ (K.map (MulAut.conj a).toMonoidHom ⊓ K).subgroupOf K :=
        h ▸ Subgroup.mem_top _
      exact h1.1
    exact (Subgroup.eq_of_le_of_card_ge hKL hLcard.le).symm

omit [Finite G] in
theorem card_sup_sup {K K' M M' W : Subgroup G}
    (hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1)
    (hZ' : ∀ z ∈ K', (∀ x ∈ K', z * x = x * z) → z = 1)
    (hK'C : K' ≤ Subgroup.centralizer (K : Set G)) (hKK' : K ⊓ K' = ⊥) (hMK : M ≤ K)
    (hM'K' : M' ≤ K')
    (hWC : W ≤ Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (K' : Set G))
    (hMe : IsElemAbelian 2 M) (hM'e : IsElemAbelian 2 M') (hWe : IsElemAbelian 2 W) :
    IsElemAbelian 2 (M ⊔ M' ⊔ W) ∧
      Nat.card ↥(M ⊔ M' ⊔ W) = Nat.card M * Nat.card M' * Nat.card W := by
  have hc1 : ∀ x ∈ M, ∀ y ∈ M', x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hK'C (hM'K' hy)) x (hMK hx)
  have hd1 : M ⊓ M' = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : x ∈ K ⊓ K' := ⟨hMK hx.1, hM'K' hx.2⟩
    rwa [hKK'] at h1
  have hc2 : ∀ x ∈ M ⊔ M', ∀ w ∈ W, x * w = w * x := fun x hx w hw =>
    Subgroup.mem_centralizer_iff.1 (mem_centralizer_sup (hWC hw).1 (hWC hw).2) x
      (sup_le_sup hMK hM'K' hx)
  have hd2 : (M ⊔ M') ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 ?_
    refine hZ' x (mem_of_mem_sup_of_mem_centralizer hZ hK'C (sup_le_sup hMK hM'K' hx.1)
      (hWC hx.2).1) fun y hy => (Subgroup.mem_centralizer_iff.1 (hWC hx.2).2 y hy).symm
  exact ⟨isElemAbelian_sup (isElemAbelian_sup hMe hM'e hc1) hWe hc2,
    by rw [card_sup_of_commute hc2 hd2, card_sup_of_commute hc1 hd1]⟩

theorem le_of_thompsonModel {K K' Q : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hT : ThompsonModel ↥K) (hK' : K' = K ∨ ∃ r ∈ Q, K' = CFSG.conjugate K r ∧ ⁅K, K'⁆ = ⊥)
    (hQN : Q ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G))
    (hP : IsSylowTwoOf (Q ⊓ K) K)
    (hE : ∃ E : Subgroup G, E ≤ Q ⊓ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      E ≤ Subgroup.centralizer ((Q ⊓ K : Subgroup G) : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian Q A) :
    A ≤ ((Q ⊓ K) ⊔ (Q ⊓ K')) ⊔ (Q ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G)) := by
  obtain ⟨hAQ, hAe, hAmax⟩ := hA
  obtain ⟨E, hEP, hEe, hE16, hEC⟩ := hE
  have hZ : ∀ z ∈ K, (∀ x ∈ K, z * x = x * z) → z = 1 := fun z hz hzc =>
    eq_one_of_forall_comm hK (hEP.trans inf_le_right) hEe hE16 hz hzc
  obtain ⟨M, hMP, hMe, hMmax⟩ := exists_max_elemAbelian (Q ⊓ K)
  have hM16 : 16 ≤ Nat.card M := hE16 ▸ hMmax E hEP hEe
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => mul_self_of_elemAbelian hAe ha
  have hAQN : A ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    hAQ.trans Subgroup.le_normalizer
  rcases hK' with hK'K | ⟨r, hrQ, hK'eq, hcomm⟩
  ·
    rw [hK'K] at hQN ⊢
    simp only [sup_idem] at hQN ⊢
    have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAQ.trans hQN
    have hAP : A ≤ Subgroup.normalizer ((Q ⊓ K : Subgroup G) : Set G) :=
      fun a ha => mem_normalizer_inf (hAQN ha) (hAK ha)
    obtain ⟨-, hlt⟩ := relIndex_centralizer_le hZ hT hP hEP hEe hE16 hEC hMmax hAK hAP hAe
    have hinner : ∀ a ∈ A, InnerOn K a := by
      by_contra hcon
      push Not at hcon
      have h1 := hlt hcon
      have hcB : ∀ x ∈ M, ∀ y ∈ Subgroup.centralizer (K : Set G) ⊓ A, x * y = y * x :=
        fun x hx y hy => Subgroup.mem_centralizer_iff.1 hy.1 x (hMP hx).2
      have hdB : M ⊓ (Subgroup.centralizer (K : Set G) ⊓ A) = ⊥ := by
        refine eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 ?_
        exact hZ x (hMP hx.1).2 fun y hy => (Subgroup.mem_centralizer_iff.1 hx.2.1 y hy).symm
      have hB := hAmax (M ⊔ (Subgroup.centralizer (K : Set G) ⊓ A))
        (sup_le (hMP.trans inf_le_left) (inf_le_right.trans hAQ))
        (isElemAbelian_sup hMe (isElemAbelian_mono inf_le_right hAe) hcB)
      rw [card_sup_of_commute hcB hdB] at hB
      have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (K : Set G)) A
      have hWpos : 0 < Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ A) := Nat.card_pos
      have h3 : (Subgroup.centralizer (K : Set G)).relIndex A *
          Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ A) <
          Nat.card M * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓ A) :=
        Nat.mul_lt_mul_of_pos_right h1 hWpos
      omega
    intro a ha
    obtain ⟨g, hgP, -, -, hc⟩ :=
      exists_of_innerOn hZ hP (hAK ha) (hAP ha) (hAsq a ha) (hinner a ha)
    rw [show a = g * (g⁻¹ * a) by group]
    exact mul_mem (Subgroup.mem_sup_left hgP)
      (Subgroup.mem_sup_right ⟨Q.mul_mem (Q.inv_mem hgP.1) (hAQ ha), hc⟩)
  ·
    have hK'm : K' = K.map (MulAut.conj r⁻¹).toMonoidHom := hK'eq
    have hKC' : K ≤ Subgroup.centralizer (K' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hK'C : K' ≤ Subgroup.centralizer (K : Set G) := Subgroup.le_centralizer_iff.1 hKC'
    have hri : r⁻¹ ∈ Q := inv_mem hrQ
    have hcQ : Q.map (MulAut.conj r⁻¹).toMonoidHom = Q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mul_mem (mul_mem hri hy) (inv_mem hri)
      · intro hx
        refine ⟨r * x * r⁻¹, mul_mem (mul_mem hrQ hx) (inv_mem hrQ), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hP'eq : Q ⊓ K' = (Q ⊓ K).map (MulAut.conj r⁻¹).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj r⁻¹).injective, hcQ, hK'm]
    have hP' : IsSylowTwoOf (Q ⊓ K') K' := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h1 := Setup.X6.isSylowOf_map_injective (p := 2) (MulAut.conj r⁻¹).toMonoidHom
        (MulAut.conj r⁻¹).injective (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hP)
      rw [← hP'eq, ← hK'm] at h1
      exact Setup.X6.isSylowTwoOf_iff_isSylowOf.2 h1
    have hE'P : E.map (MulAut.conj r⁻¹).toMonoidHom ≤ Q ⊓ K' := by
      rw [hP'eq]
      exact Subgroup.map_mono hEP
    have hE'e : IsElemAbelian 2 (E.map (MulAut.conj r⁻¹).toMonoidHom) := isElemAbelian_map _ hEe
    have hE'16 : Nat.card ↥(E.map (MulAut.conj r⁻¹).toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj r⁻¹).injective]
      exact hE16
    have hE'C : E.map (MulAut.conj r⁻¹).toMonoidHom ≤
        Subgroup.centralizer ((Q ⊓ K' : Subgroup G) : Set G) := by
      rw [hP'eq]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hEC hx) y hy]
    have hK'card : Nat.card K' = Nat.card K := by
      rw [hK'm, Subgroup.card_map_of_injective (MulAut.conj r⁻¹).injective]
    let eK : ↥K ≃* ↥K' :=
      (K.equivMapOfInjective (MulAut.conj r⁻¹).toMonoidHom (MulAut.conj r⁻¹).injective).trans
        (MulEquiv.subgroupCongr hK'm.symm)
    have : IsSimpleGroup ↥K := hK
    have hK's : IsSimpleGroup ↥K' := MulEquiv.isSimpleGroup eK.symm
    have hT' : ThompsonModel ↥K' := ThompsonModel.of_mulEquiv eK.symm hT
    have hZ' : ∀ z ∈ K', (∀ x ∈ K', z * x = x * z) → z = 1 := fun z hz hzc =>
      eq_one_of_forall_comm hK's (hE'P.trans inf_le_right) hE'e hE'16 hz hzc
    have hKK' : K ⊓ K' = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2
      (hZ x hx.1 fun y hy => (Subgroup.mem_centralizer_iff.1 (hK'C hx.2) y hy).symm)
    obtain ⟨M', hM'P, hM'e, hM'max⟩ := exists_max_elemAbelian (Q ⊓ K')
    have hM'16 : 16 ≤ Nat.card M' := hE'16 ▸ hM'max _ hE'P hE'e
    obtain ⟨hB, hBcard⟩ := card_sup_sup hZ hZ' hK'C hKK' (hMP.trans inf_le_right)
      (hM'P.trans inf_le_right)
      (W := Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (K' : Set G) ⊓ A)
      inf_le_left hMe hM'e (isElemAbelian_mono inf_le_right hAe)
    have hBA := hAmax _ (sup_le (sup_le (hMP.trans inf_le_left) (hM'P.trans inf_le_left))
      (inf_le_right.trans hAQ)) hB
    rw [hBcard] at hBA
    have hWpos : 0 < Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
        Subgroup.centralizer (K' : Set G) ⊓ A) := Nat.card_pos
    have hconjK' : ∀ b ∈ Subgroup.normalizer (K : Set G),
        b ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) → ∀ y ∈ K', b * y * b⁻¹ ∈ K' := by
      intro b hbK hbKK y hy
      apply mem_of_mem_sup_of_mem_centralizer hZ hK'C
      · exact (Subgroup.mem_normalizer_iff.1 hbKK y).1 (Subgroup.mem_sup_right hy)
      · refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
        have hk' : b⁻¹ * k * b ∈ K := by
          simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hbK) k).1 hk
        have h1 := Subgroup.mem_centralizer_iff.1 (hK'C hy) _ hk'
        calc k * (b * y * b⁻¹) = b * ((b⁻¹ * k * b) * y) * b⁻¹ := by group
          _ = b * (y * (b⁻¹ * k * b)) * b⁻¹ := by rw [h1]
          _ = b * y * b⁻¹ * k := by group
    by_cases hAK : A ≤ Subgroup.normalizer (K : Set G)
    ·
      have hAK' : A ≤ Subgroup.normalizer (K' : Set G) := by
        intro a ha
        refine Subgroup.mem_normalizer_iff.2 fun x =>
          ⟨hconjK' a (hAK ha) (hQN (hAQ ha)) x, fun hx => ?_⟩
        have h1 := hconjK' a⁻¹ (inv_mem (hAK ha)) (inv_mem (hQN (hAQ ha))) _ hx
        have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
        rwa [h2] at h1
      have hAP : A ≤ Subgroup.normalizer ((Q ⊓ K : Subgroup G) : Set G) :=
        fun a ha => mem_normalizer_inf (hAQN ha) (hAK ha)
      have hAP' : A ≤ Subgroup.normalizer ((Q ⊓ K' : Subgroup G) : Set G) :=
        fun a ha => mem_normalizer_inf (hAQN ha) (hAK' ha)
      obtain ⟨h1, h1s⟩ := relIndex_centralizer_le hZ hT hP hEP hEe hE16 hEC hMmax hAK hAP hAe
      obtain ⟨h2, h2s⟩ :=
        relIndex_centralizer_le hZ' hT' hP' hE'P hE'e hE'16 hE'C hM'max hAK' hAP' hAe
      have hinner : ∀ a ∈ A, InnerOn K a ∧ InnerOn K' a := by
        by_contra hcon
        push Not at hcon
        obtain ⟨a, ha, hna⟩ := hcon
        have hlt : (Subgroup.centralizer (K : Set G)).relIndex A *
            (Subgroup.centralizer (K' : Set G)).relIndex A < Nat.card M * Nat.card M' := by
          by_cases hKa : InnerOn K a
          · have h4 := h2s ⟨a, ha, hna hKa⟩
            nlinarith
          · have h4 := h1s ⟨a, ha, hKa⟩
            nlinarith
        have h3 := Subgroup.relIndex_inf_le (H := Subgroup.centralizer (K : Set G))
          (K := Subgroup.centralizer (K' : Set G)) (L := A)
        have h5 := Subgroup.relIndex_mul_card
          (Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (K' : Set G)) A
        have h6 := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt h3 hlt) hWpos
        omega
      intro a ha
      obtain ⟨hKa, hK'a⟩ := hinner a ha
      obtain ⟨g, hgP, hg2, hga, hc₁⟩ :=
        exists_of_innerOn hZ hP (hAK ha) (hAP ha) (hAsq a ha) hKa
      have hgK' : g ∈ Subgroup.centralizer (K' : Set G) := hKC' hgP.2
      have hc₁Q : g⁻¹ * a ∈ Q := mul_mem (inv_mem hgP.1) (hAQ ha)
      have hc₁K' : g⁻¹ * a ∈ Subgroup.normalizer (K' : Set G) :=
        mul_mem (inv_mem (Subgroup.centralizer_le_normalizer _ hgK')) (hAK' ha)
      have hc₁P' : g⁻¹ * a ∈ Subgroup.normalizer ((Q ⊓ K' : Subgroup G) : Set G) :=
        mem_normalizer_inf (Subgroup.le_normalizer hc₁Q) hc₁K'
      have hag : a * g⁻¹ = g⁻¹ * a := by
        calc a * g⁻¹ = g⁻¹ * (g * a) * g⁻¹ := by group
          _ = g⁻¹ * (a * g) * g⁻¹ := by rw [hga]
          _ = g⁻¹ * a := by group
      have hc₁2 : g⁻¹ * a * (g⁻¹ * a) = 1 := by
        calc g⁻¹ * a * (g⁻¹ * a) = g⁻¹ * (a * g⁻¹) * a := by group
          _ = g⁻¹ * (g⁻¹ * a) * a := by rw [hag]
          _ = (g * g)⁻¹ * (a * a) := by group
          _ = 1 := by rw [hg2, hAsq a ha, inv_one, one_mul]
      have hc₁inn : InnerOn K' (g⁻¹ * a) := by
        obtain ⟨g', hg'K', hg'⟩ := hK'a
        refine ⟨g', hg'K', fun x hx => ?_⟩
        have hy : g' * x * g'⁻¹ ∈ K' := mul_mem (mul_mem hg'K' hx) (inv_mem hg'K')
        have h1 := Subgroup.mem_centralizer_iff.1 hgK' _ hy
        calc g⁻¹ * a * x * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * x * a⁻¹) * g := by group
          _ = g⁻¹ * (g' * x * g'⁻¹) * g := by rw [hg' x hx]
          _ = g⁻¹ * (g * (g' * x * g'⁻¹)) := by rw [mul_assoc, h1]
          _ = g' * x * g'⁻¹ := by group
      obtain ⟨g', hg'P, -, -, hc⟩ := exists_of_innerOn hZ' hP' hc₁K' hc₁P' hc₁2 hc₁inn
      have hcK : g'⁻¹ * (g⁻¹ * a) ∈ Subgroup.centralizer (K : Set G) :=
        mul_mem (inv_mem (hK'C hg'P.2)) hc₁
      rw [show a = g * (g' * (g'⁻¹ * (g⁻¹ * a))) by group]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hgP))
        (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hg'P))
          (Subgroup.mem_sup_right ⟨Q.mul_mem (Q.inv_mem hg'P.1) hc₁Q,
            mem_centralizer_sup hcK hc⟩))
    ·
      exfalso
      obtain ⟨s, hsA, hsK⟩ := IsConcreteLE.not_le_iff_exists.1 hAK
      have hAN : ∀ a ∈ A, a ∉ Subgroup.normalizer (K : Set G) →
          K.map (MulAut.conj a).toMonoidHom = K' := fun a ha haK =>
        (map_conj_eq_or_eq hK hZ hK'C hK'card (hQN (hAQ ha))).resolve_left
          fun h => haK (mem_normalizer_of_map_eq h)
      have hsK' := hAN s hsA hsK
      have hcover : ∀ a ∈ A, a ∉ Subgroup.normalizer (K : Set G) →
          s⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
        intro a ha haK
        apply mem_normalizer_of_map_eq
        rw [map_conj_mul, hAN a ha haK, ← hsK', ← map_conj_mul, inv_mul_cancel, map_conj_one]
      have hA₀ : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set G)) := by
        classical
        let F : A → ↥(A ⊓ Subgroup.normalizer (K : Set G)) × Bool := fun a =>
          if h : (a : G) ∈ Subgroup.normalizer (K : Set G) then (⟨a, a.2, h⟩, false)
          else (⟨s⁻¹ * a, A.mul_mem (A.inv_mem hsA) a.2, hcover a a.2 h⟩, true)
        have hF : Function.Injective F := by
          intro a b hab
          simp only [F] at hab
          split_ifs at hab with ha hb hb
          · simp only [Prod.mk.injEq, and_true] at hab
            have h1 := congrArg Subtype.val hab
            exact Subtype.ext h1
          · simp at hab
          · simp at hab
          · simp only [Prod.mk.injEq, and_true] at hab
            have h1 := congrArg Subtype.val hab
            exact Subtype.ext (mul_left_cancel h1)
        calc Nat.card A ≤ Nat.card (↥(A ⊓ Subgroup.normalizer (K : Set G)) × Bool) :=
              Nat.card_le_card_of_injective F hF
          _ = 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (K : Set G)) := by
            rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
              mul_comm]
      obtain ⟨h1, -⟩ := relIndex_centralizer_le hZ hT hP hEP hEe hE16 hEC hMmax
        (A := A ⊓ Subgroup.normalizer (K : Set G)) inf_le_right
        (fun a ha => mem_normalizer_inf (hAQN ha.1) ha.2) (isElemAbelian_mono inf_le_left hAe)
      have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (K : Set G))
        (A ⊓ Subgroup.normalizer (K : Set G))
      have h3 : Subgroup.centralizer (K : Set G) ⊓ (A ⊓ Subgroup.normalizer (K : Set G)) ≤
          Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (K' : Set G) ⊓ A := by
        rintro c ⟨hcK, hcA, -⟩
        refine ⟨⟨hcK, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, hcA⟩
        rw [← hsK'] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hcs : c * s = s * c := comm_of_elemAbelian hAe hcA hsA
        have hcx := Subgroup.mem_centralizer_iff.1 hcK x hx
        have hsc : s⁻¹ * c = c * s⁻¹ := by
          calc s⁻¹ * c = s⁻¹ * (c * s) * s⁻¹ := by group
            _ = s⁻¹ * (s * c) * s⁻¹ := by rw [hcs]
            _ = c * s⁻¹ := by group
        calc s * x * s⁻¹ * c = s * x * (s⁻¹ * c) := by group
          _ = s * x * (c * s⁻¹) := by rw [hsc]
          _ = s * (x * c) * s⁻¹ := by group
          _ = s * (c * x) * s⁻¹ := by rw [hcx]
          _ = s * c * x * s⁻¹ := by group
          _ = c * s * x * s⁻¹ := by rw [← hcs]
          _ = c * (s * x * s⁻¹) := by group
      have h4 := Subgroup.card_le_of_le h3
      have h5 := Nat.mul_le_mul h1 h4
      have h6 : 16 * (Nat.card M * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
          Subgroup.centralizer (K' : Set G) ⊓ A)) ≤
          Nat.card M * Nat.card M' * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
          Subgroup.centralizer (K' : Set G) ⊓ A) := by
        calc 16 * (Nat.card M * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
              Subgroup.centralizer (K' : Set G) ⊓ A)) =
            Nat.card M * 16 * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
              Subgroup.centralizer (K' : Set G) ⊓ A) := by ring
          _ ≤ _ := by gcongr
      have h7 : 0 < Nat.card M * Nat.card ↥(Subgroup.centralizer (K : Set G) ⊓
          Subgroup.centralizer (K' : Set G) ⊓ A) := Nat.mul_pos (by omega) hWpos
      linarith

end Count

end CFSG.Quasithin.H13.NQCat.LieThompson
