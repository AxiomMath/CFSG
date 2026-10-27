module

public import CFSG.RankThree.OddKernel.QuotientNoncyclicKernel
public import CFSG.RankThree.OddKernel.WeightModels
public import CFSG.RankThree.OddKernel.SectionRep
public import CFSG.RankThree.LocalRank.InvolutionCentralizerLocalRank
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

universe u

section FixedPlane

open Module

theorem eq_top_of_forall_sub_mem {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group Y] (α : Y →* (V ≃ₗ[K] V))
    (hnt : ∀ U U', IsIrreducibleFactor α U U' → ∃ y, ∃ w ∈ U', α y w - w ∉ U)
    (U₀ : Submodule K V) (hU₀ : ∀ y v, α y v - v ∈ U₀) : U₀ = ⊤ := by
  by_contra hne
  have hinv : ∀ y, ∀ w ∈ U₀, α y w ∈ U₀ := fun y w hw => by
    have h := U₀.add_mem (hU₀ y w) hw
    rwa [sub_add_cancel] at h
  let M : Set (Submodule K V) := {X | (∀ y, ∀ w ∈ X, α y w ∈ X) ∧ U₀ ≤ X ∧ X < ⊤}
  have hM : M.Nonempty := ⟨U₀, hinv, le_rfl, lt_top_iff_ne_top.2 hne⟩
  obtain ⟨X, ⟨hXinv, hU₀X, hXlt⟩, hXmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance M hM
  have hfac : IsIrreducibleFactor α X ⊤ := by
    refine ⟨hXinv, fun y w _ => Submodule.mem_top, hXlt, fun Z hZ hXZ _ => ?_⟩
    by_cases hZe : Z = ⊤
    · exact Or.inr hZe
    · exact Or.inl (eq_of_le_of_not_lt hXZ
        (hXmax Z ⟨hZ, hU₀X.trans hXZ, lt_top_iff_ne_top.2 hZe⟩)).symm
  obtain ⟨y, w, -, hw⟩ := hnt X ⊤ hfac
  exact hw (hU₀X (hU₀ y w))

variable {p : ℕ}

theorem le_ker_of_no_trivial_factor [Fact p.Prime] {Y E : Type*} [Group Y] [Finite Y] [Group E]
    (f : Y →* E) (D : Subgroup Y) [D.Normal] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (α : Y →* (V ≃ₗ[ZMod p] V)) (π : D →* Multiplicative V)
    (hπ : Function.Surjective π) (hπker : π.ker = frattini D)
    (hπα : ∀ (y : Y) (d : D), π (MulAut.conjNormal y d) =
      Multiplicative.ofAdd (α y (Multiplicative.toAdd (π d))))
    (hDZ : D.map f ≤ center E)
    (hnt : ∀ U U', IsIrreducibleFactor α U U' → ∃ y, ∃ w ∈ U', α y w - w ∉ U) :
    D ≤ f.ker := by
  let K₀ : Subgroup D := (⁅(⊤ : Subgroup Y), D⁆).subgroupOf D
  let U₀ : Submodule (ZMod p) V :=
    { carrier := {v | Multiplicative.ofAdd v ∈ K₀.map π}
      add_mem' := fun {a b} ha hb => by
        change Multiplicative.ofAdd (a + b) ∈ K₀.map π
        rw [ofAdd_add]
        exact mul_mem ha hb
      zero_mem' := by
        change Multiplicative.ofAdd (0 : V) ∈ K₀.map π
        rw [ofAdd_zero]
        exact one_mem _
      smul_mem' := fun c v hv => by
        change Multiplicative.ofAdd (c • v) ∈ K₀.map π
        have hc : c • v = c.val • v := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [hc, ofAdd_nsmul]
        exact pow_mem hv _ }
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_of_forall_sub_mem α hnt U₀ fun y v => ?_
    obtain ⟨d, hd⟩ := hπ (Multiplicative.ofAdd v)
    have hmem : MulAut.conjNormal y d * d⁻¹ ∈ K₀ := by
      change ((MulAut.conjNormal y d * d⁻¹ : D) : Y) ∈ ⁅(⊤ : Subgroup Y), D⁆
      have h := commutator_mem_commutator (mem_top y) d.2
      rw [commutatorElement_def] at h
      rwa [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
    refine ⟨_, hmem, ?_⟩
    rw [map_mul, map_inv, hπα, hd, toAdd_ofAdd, ← ofAdd_neg, ← ofAdd_add, sub_eq_add_neg]
  have hK₀ : K₀ ⊔ frattini D = ⊤ := by
    refine eq_top_iff.2 fun d _ => ?_
    have hv : Multiplicative.toAdd (π d) ∈ U₀ := hU₀ ▸ Submodule.mem_top
    obtain ⟨k, hk, hkd⟩ := hv
    have hker : k⁻¹ * d ∈ frattini D := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hkd]
      exact inv_mul_cancel _
    have := mul_mem_sup hk hker
    rwa [mul_inv_cancel_left] at this
  have hK₀top := frattini_nongenerating hK₀
  have hDK : D ≤ ⁅(⊤ : Subgroup Y), D⁆ := fun d hd => by
    have h : (⟨d, hd⟩ : D) ∈ K₀ := hK₀top ▸ mem_top _
    exact h
  refine hDK.trans ?_
  rw [commutator_le]
  intro y _ d hd
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 (hDZ (mem_map_of_mem f hd)) _)

theorem map_centralizer_eq_of_odd {Y E : Type*} [Group Y] [Finite Y] [Group E] (f : Y →* E)
    (hf : Function.Surjective f) (hodd : ¬ 2 ∣ Nat.card f.ker) {t : Y} (ht : orderOf t = 2) :
    (centralizer {t}).map f = centralizer {f t} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ fun e he => ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
    rw [mem_centralizer_singleton_iff, ← map_mul, hc, map_mul]
  obtain ⟨y, rfl⟩ := hf e
  rw [mem_centralizer_singleton_iff] at he
  have hA2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hcomm : Commute (f t) (f y) := he.symm
  have hinv : ∀ a : zpowers t, ∀ x : Y, y⁻¹ * x ∈ f.ker →
      y⁻¹ * (MulAut.conj.comp (zpowers t).subtype) a x ∈ f.ker := by
    rintro ⟨a, k, rfl⟩ x hx
    have hxy : f x = f y := by
      have h := MonoidHom.mem_ker.1 hx
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (f y)⁻¹ * f (t ^ k * x * (t ^ k)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, map_zpow, hxy, (hcomm.zpow_left k).eq, mul_inv_cancel_right,
      inv_mul_cancel]
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA2
    (MulAut.conj.comp (zpowers t).subtype) f.ker hodd y).2 hinv
  refine ⟨c, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h := hfix ⟨t, mem_zpowers t⟩
    change t * c * t⁻¹ = c at h
    calc c * t = t * c * t⁻¹ * t := by rw [h]
      _ = t * c := by group
  · have h := MonoidHom.mem_ker.1 hc
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm

theorem exists_centralizer_lift [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y]
    (D : Subgroup Y) [D.Normal] (hD : IsPGroup p D) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (α : Y →* (V ≃ₗ[ZMod p] V)) (π : D →* Multiplicative V)
    (hπ : Function.Surjective π) (hπker : π.ker = frattini D)
    (hπα : ∀ (y : Y) (d : D), π (MulAut.conjNormal y d) =
      Multiplicative.ofAdd (α y (Multiplicative.toAdd (π d))))
    {t : Y} (ht : orderOf t = 2) {v : V} (hv : α t v = v) :
    ∃ c : D, (c : Y) ∈ centralizer {t} ∧ π c = Multiplicative.ofAdd v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := hπ (Multiplicative.ofAdd v)
  have hA2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  let S : Subgroup Y :=
    { carrier := {g | α g v = v}
      mul_mem' := fun {a b} (ha : α a v = v) (hb : α b v = v) => by
        change α (a * b) v = v
        rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      one_mem' := by
        change α 1 v = v
        rw [map_one]
        rfl
      inv_mem' := fun {a} (ha : α a v = v) => by
        change α a⁻¹ v = v
        calc α a⁻¹ v = α a⁻¹ (α a v) := by rw [ha]
          _ = v := inv_apply_apply α a v }
  have hS : zpowers t ≤ S := zpowers_le.2 hv
  have hodd : ¬ 2 ∣ Nat.card (frattini D) := by
    obtain ⟨k, hk⟩ := (hD.to_subgroup (frattini D)).exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hinv : ∀ a : zpowers t, ∀ x : D, d⁻¹ * x ∈ frattini D →
      d⁻¹ * (MulAut.conjNormal.comp (zpowers t).subtype) a x ∈ frattini D := by
    intro a x hx
    rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hx ⊢
    change π d = π (MulAut.conjNormal (a : Y) x)
    rw [hπα, ← hx, hd, toAdd_ofAdd, (hS a.2 : α a v = v)]
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA2
    (MulAut.conjNormal.comp (zpowers t).subtype) (frattini D) hodd d).2 hinv
  refine ⟨c, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (hfix ⟨t, mem_zpowers t⟩)
    change ((MulAut.conjNormal t c : D) : Y) = c at h
    rw [MulAut.conjNormal_apply] at h
    calc (c : Y) * t = t * c * t⁻¹ * t := by rw [h]
      _ = t * c := by group
  · rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hc
    rw [← hc, hd]

theorem two_le_pRank_inf_centralizer [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*} [Group Y]
    [Finite Y] (D : Subgroup Y) [D.Normal] (hD : IsPGroup p D) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] (α : Y →* (V ≃ₗ[ZMod p] V))
    (π : D →* Multiplicative V) (hπ : Function.Surjective π) (hπker : π.ker = frattini D)
    (hπα : ∀ (y : Y) (d : D), π (MulAut.conjNormal y d) =
      Multiplicative.ofAdd (α y (Multiplicative.toAdd (π d))))
    {t : Y} (ht : orderOf t = 2) (hfix : finrank (ZMod p) (fixSpace (α t).toLinearMap) = 2) :
    2 ≤ CFSG.Open.pRank p (D ⊓ centralizer {t}) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (Multiplicative V) := inferInstanceAs (Finite V)
  let ρ : (D ⊓ centralizer {t} : Subgroup Y) →* Multiplicative V :=
    π.comp (Subgroup.inclusion inf_le_left)
  have hlift : ∀ v ∈ fixSpace (α t).toLinearMap, Multiplicative.ofAdd v ∈ ρ.range := by
    intro v hv
    have hv' : α t v = v := by
      have h := LinearMap.mem_ker.1 hv
      rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
      exact h
    obtain ⟨c, hc, hπc⟩ := exists_centralizer_lift hp2 D hD α π hπ hπker hπα ht hv'
    exact ⟨⟨c, c.2, hc⟩, hπc⟩
  have hcard : p ^ 2 ≤ Nat.card ρ.range := by
    have : Fintype (fixSpace (α t).toLinearMap) := Fintype.ofFinite _
    have h1 : Nat.card (fixSpace (α t).toLinearMap) = p ^ 2 := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), hfix, ZMod.card]
    rw [← h1]
    refine Nat.card_le_card_of_injective (fun v => ⟨Multiplicative.ofAdd v, hlift v v.2⟩)
      fun v w h => Subtype.ext ?_
    have h' := congrArg Subtype.val h
    exact Multiplicative.ofAdd.injective h'
  have hncyc : ¬ IsCyclic (D ⊓ centralizer {t} : Subgroup Y) := by
    intro hcyc
    have : IsCyclic ρ.range := isCyclic_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    have hle : Nat.card ρ.range ≤ p := by
      refine CFSG.RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic fun x => ?_
      apply Subtype.ext
      change (x : Multiplicative V) ^ p = 1
      rw [← ofAdd_toAdd (x : Multiplicative V), ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
        ZMod.natCast_self, zero_smul, ofAdd_zero]
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
    rw [pow_one] at this
    omega
  have hCp : IsPGroup p (D ⊓ centralizer {t} : Subgroup Y) := hD.to_le inf_le_left
  have : Fact (IsPGroup p (D ⊓ centralizer {t} : Subgroup Y)) := ⟨hCp⟩
  obtain ⟨B, -, hBcard, hBel⟩ := CFSG.lemma_4_5_a hp2 hncyc
  have hBel' : CFSG.Open.IsElemAbelian p (B.map (D ⊓ centralizer {t}).subtype) :=
    isElemAbelian_map ((isElementaryAbelian_iff_isElemAbelian p B).1 hBel) _
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt (map_subtype_le B) hBel'
    (by rw [card_map_of_injective (subtype_injective _), hBcard])

theorem pRank_le_two_of_surjective_of_two_le_ker (hp : p.Prime) (hp3 : 3 < p) {M L : Type*}
    [Group M] [Group L] [Finite M] [Finite L] (hM : IsPGroup p M) (hrank : pRank p M ≤ 2)
    (ψ : M →* L) (hψ : Function.Surjective ψ) (hker : 2 ≤ pRank p ψ.ker) : pRank p L ≤ 2 := by
  have e := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  rw [pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt e, ← pRank_eq_open_pRank_top]
  exact rank_two_large_prime_quotient_noncyclic_kernel hp hp3 hM hrank ψ.ker hker

theorem pRank_centralizer_le_localRank {Y : Type*} [Group Y] [Finite Y] (hp : 1 < p) {t : Y}
    (ht : orderOf t = 2) : pRank p (centralizer {t} : Subgroup Y) ≤ localRank p Y := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hA2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hAne : zpowers t ≠ ⊥ := fun h => ht1 (by
    have : t ∈ zpowers t := mem_zpowers t
    rwa [h, mem_bot] at this)
  have hCN : centralizer {t} ≤ normalizer (zpowers t : Set Y) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
  exact (pRank_mono hp hCN).trans
    (CFSG.RankThree.Classical.pRank_le_localRank hp ⟨_, hAne, hA2, rfl⟩)

theorem pRank_centralizer_le_two (hp : p.Prime) (hp3 : 3 < p) {Y E : Type*} [Group Y]
    [Finite Y] [Group E] [Finite E] (hloc : localRank p Y ≤ 2) (f : Y →* E)
    (hf : Function.Surjective f) (hA : IsPGroup p f.ker) (D : Subgroup Y) [D.Normal]
    (hD : IsPGroup p D) (hDA : D ≤ f.ker)
    (hCD : ∀ t : Y, orderOf t = 2 → 2 ≤ CFSG.Open.pRank p (D ⊓ centralizer {t}))
    {s : E} (hs : orderOf s = 2) : CFSG.Assembly.pRank p (centralizer {s}) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hoddA : Odd (Nat.card f.ker) := by
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨t, ht, rfl⟩ := exists_involution_lift f hf hoddA hs
  have hodd : ¬ 2 ∣ Nat.card f.ker := fun h =>
    (Nat.not_even_iff_odd.2 hoddA) (even_iff_two_dvd.2 h)
  have hmap := map_centralizer_eq_of_odd f hf hodd ht
  have hCloc := (pRank_centralizer_le_localRank hp.one_lt ht).trans hloc
  obtain ⟨Q₀⟩ : Nonempty (Sylow p (centralizer {t} : Subgroup Y)) := inferInstance
  have hQ₀rank : pRank p (Q₀ : Subgroup (centralizer {t} : Subgroup Y)) ≤ 2 :=
    (pRank_sylow Q₀).2 ▸ hCloc
  let ψ := (f.domRestrict (centralizer {t})).codRestrict (centralizer {f t})
    (fun x => hmap ▸ mem_map_of_mem f x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hmap] at hz
    obtain ⟨m, hm, rfl⟩ := mem_map.1 hz
    exact ⟨⟨m, hm⟩, rfl⟩
  let Q := Q₀.mapSurjective hψ
  let ψ₀ := (ψ.domRestrict (Q₀ : Subgroup (centralizer {t} : Subgroup Y))).codRestrict
    (Q : Subgroup (centralizer {f t} : Subgroup E)) (fun x => by
      rw [Sylow.coe_mapSurjective]
      exact mem_map_of_mem ψ x.2)
  have hψ₀ : Function.Surjective ψ₀ := by
    rintro ⟨z, hz⟩
    rw [Sylow.coe_mapSurjective] at hz
    obtain ⟨m, hm, rfl⟩ := mem_map.1 hz
    exact ⟨⟨m, hm⟩, rfl⟩
  have hC₀Q₀ : (D ⊓ centralizer {t}).subgroupOf (centralizer {t}) ≤
      (Q₀ : Subgroup (centralizer {t} : Subgroup Y)) := by
    have hn : ((D ⊓ centralizer {t}).subgroupOf (centralizer {t})).Normal := by
      rw [inf_subgroupOf_right]
      infer_instance
    have hCp : IsPGroup p ((D ⊓ centralizer {t}).subgroupOf (centralizer {t})) :=
      (hD.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    exact hCp.le_sylow_of_normal Q₀
  let ι : (D ⊓ centralizer {t} : Subgroup Y) →* ψ₀.ker :=
    (((Subgroup.inclusion (inf_le_right : D ⊓ centralizer {t} ≤ centralizer {t})).codRestrict
      (Q₀ : Subgroup (centralizer {t} : Subgroup Y)) fun x => hC₀Q₀ (by
        change ((x : Y) ∈ D ⊓ centralizer {t})
        exact x.2)).codRestrict ψ₀.ker fun x => by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      apply Subtype.ext
      change f (x : Y) = 1
      exact hDA x.2.1)
  have hι : Function.Injective ι := fun x y h => by
    have h' := congrArg (fun z : ψ₀.ker => (((z : Q₀) : centralizer {t}) : Y)) h
    exact Subtype.ext h'
  have hker : 2 ≤ pRank p ψ₀.ker := by
    refine (hCD t ht).trans ?_
    rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top, pRank_eq_open_pRank_top,
      pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt ι hι
  have h := pRank_le_two_of_surjective_of_two_le_ker hp hp3 Q₀.isPGroup' hQ₀rank ψ₀ hψ₀ hker
  change CFSG.Open.pRank p (centralizer {f t}) ≤ 2
  rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top, ← (pRank_sylow Q).2]
  exact h

theorem critical_fixed_plane_kernel_local_comparison [hp : Fact p.Prime] (hp3 : 3 < p)
    {Y E : Type u} [Group Y] [Finite Y] [Group E] [Finite E] (hloc : localRank p Y ≤ 2)
    (f : Y →* E) (hf : Function.Surjective f) (hA : IsPGroup p f.ker) (h2E : pRank 2 E ≤ 2)
    (D : Subgroup Y) [D.Normal] (hD : IsPGroup p D) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] (α : Y →* (V ≃ₗ[ZMod p] V))
    (π : D →* Multiplicative V) (hπ : Function.Surjective π) (hπker : π.ker = frattini D)
    (hπα : ∀ (y : Y) (d : D), π (MulAut.conjNormal y d) =
      Multiplicative.ofAdd (α y (Multiplicative.toAdd (π d))))
    (hDZ : D.map f ≤ center E)
    (hnt : ∀ U U', IsIrreducibleFactor α U U' → ∃ y, ∃ w ∈ U', α y w - w ∉ U)
    (hfix : ∀ t : Y, orderOf t = 2 → finrank (ZMod p) (fixSpace (α t).toLinearMap) = 2) :
    D ≤ f.ker ∧ localRank p E ≤ 2 := by
  have hp2 : p ≠ 2 := by omega
  have hDA := le_ker_of_no_trivial_factor f D α π hπ hπker hπα hDZ hnt
  refine ⟨hDA, ?_⟩
  have h2E' : CFSG.Assembly.twoRank E ≤ 2 := by
    change CFSG.Open.pRank 2 (⊤ : Subgroup E) ≤ 2
    rw [← pRank_eq_open_pRank_top]
    exact h2E
  rw [CFSG.RankThree.LocalRank.two_rank_two_involution_centralizer_local_rank hp.out hp3 h2E']
  refine csSup_le' ?_
  rintro _ ⟨s, hs, rfl⟩
  exact pRank_centralizer_le_two hp.out hp3 hloc f hf hA D hD hDA
    (fun t ht => two_le_pRank_inf_centralizer hp2 D hD α π hπ hπker hπα ht (hfix t ht)) hs

end FixedPlane

end CFSG.RankThree.OddKernel
