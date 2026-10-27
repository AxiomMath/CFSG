module

public import CFSG.Quasithin.MS93.S38EAQuot
public import CFSG.Quasithin.MS93.ASGroup

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

variable {U₀ : Type} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

section SMap

include hS in
theorem le_normalizer_v0 : G₀ ≤ Subgroup.normalizer ((⁅V, Lt⁆ : Subgroup U₀) : Set U₀) :=
  le_normalizer_comm_of hS.nV hS.nLt

theorem mk_mem_commV {x : U₀} (hx : x ∈ ⁅V, Lt⁆) :
    (QuotientGroup.mk (⟨x, hS.commV_le hx⟩ : ↥V) : hS.YM lam) ∈ commV (hS.kY lam hlam1) := by
  set H : Subgroup U₀ :=
    ((commV (hS.kY lam hlam1)).comap (QuotientGroup.mk' (zLam hS.cls2 lam))).map V.subtype
  have hle : ⁅V, Lt⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlv : l * v⁻¹ * l⁻¹ ∈ V := conj_mem_of_le_normalizer hS.nV (hS.lt_le hl) (V.inv_mem hv)
    refine ⟨⟨⁅v, l⁆, hS.commV_le (Subgroup.commutator_mem_commutator hv hl)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    have e : (⟨⁅v, l⁆, hS.commV_le (Subgroup.commutator_mem_commutator hv hl)⟩ : ↥V) =
        ⟨v, hv⟩ * ⟨l * v⁻¹ * l⁻¹, hlv⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group)
    have e2 : (QuotientGroup.mk (⟨l * v⁻¹ * l⁻¹, hlv⟩ : ↥V) : hS.YM lam) =
        hS.rho lam hlam1 ⟨l, hS.lt_le hl⟩ (QuotientGroup.mk ⟨v⁻¹, V.inv_mem hv⟩) := rfl
    rw [e, QuotientGroup.mk_mul, e2, mul_comm]
    have e3 : (QuotientGroup.mk (⟨v, hv⟩ : ↥V) : hS.YM lam) =
        (QuotientGroup.mk (⟨v⁻¹, V.inv_mem hv⟩ : ↥V))⁻¹ := by
      rw [← QuotientGroup.mk_inv]
      congr 1
      exact Subtype.ext (inv_inv v).symm
    rw [e3]
    exact Subgroup.subset_closure ⟨_, ⟨⟨l, hS.lt_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩,
      _, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hS.commV_le hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

@[expose] noncomputable def sMap : ↥⁅V, Lt⁆ →* hS.SM lam hlam1 :=
  (QuotientGroup.mk' _).comp
    (((QuotientGroup.mk' (zLam hS.cls2 lam)).comp (Subgroup.inclusion hS.commV_le)).codRestrict
      (commV (hS.kY lam hlam1)) fun x => mk_mem_commV hS lam hlam1 x.2)

theorem sMap_apply (x : ↥⁅V, Lt⁆) :
    sMap hS lam hlam1 x = QuotientGroup.mk (⟨QuotientGroup.mk (⟨x, hS.commV_le x.2⟩ : ↥V),
      mk_mem_commV hS lam hlam1 x.2⟩ : ↥(commV (hS.kY lam hlam1))) := rfl

theorem commV_le_map_v0 : commV (hS.kY lam hlam1) ≤
    (⁅V, Lt⁆.subgroupOf V).map (QuotientGroup.mk' (zLam hS.cls2 lam)) := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, y, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
  induction y using QuotientGroup.induction_on with
  | H v =>
    have hmem : ⁅(l : U₀), (v : U₀)⁆ ∈ ⁅V, Lt⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl v.2
    refine ⟨⟨⁅(l : U₀), (v : U₀)⁆, hS.commV_le hmem⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    rw [QuotientGroup.mk'_apply, hS.rho_mk lam hlam1, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem sMap_surjective : Function.Surjective (sMap hS lam hlam1) := by
  intro s
  induction s using QuotientGroup.induction_on with
  | H w =>
    obtain ⟨x, hx, hxw⟩ := commV_le_map_v0 hS lam hlam1 w.2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [sMap_apply]
    congr 1
    apply Subtype.ext
    rw [← hxw]
    rfl

theorem sMap_eq_one_iff (x : ↥⁅V, Lt⁆) :
    sMap hS lam hlam1 x = 1 ↔
      (QuotientGroup.mk (⟨x, hS.commV_le x.2⟩ : ↥V) : hS.YM lam) ∈ fixV (hS.kY lam hlam1) := by
  rw [sMap_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun h => h.2, fun h => ⟨mk_mem_commV hS lam hlam1 x.2, h⟩⟩

theorem sMap_conj (g : ↥G₀) (x : ↥⁅V, Lt⁆) :
    sMap hS lam hlam1 ⟨(g : U₀) * x * (g : U₀)⁻¹,
        conj_mem_of_le_normalizer (le_normalizer_v0 hS) g.2 x.2⟩ =
      hS.secRho lam hlam1 g (sMap hS lam hlam1 x) := by
  rw [sMap_apply, sMap_apply, secAct_mk]
  rfl

end SMap

section BSub

@[expose] def bSub (V Lt : Subgroup U₀) : Subgroup U₀ where
  carrier := {v | v ∈ V ∧ ∀ l ∈ Lt, ⁅v, l⁆ ∈ Subgroup.centralizer (V : Set U₀)}
  one_mem' := ⟨V.one_mem, fun l _ => by
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨V.mul_mem ha hb, fun l hl => ?_⟩
    have e : ⁅a * b, l⁆ = (a * ⁅b, l⁆ * a⁻¹) * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 : a * ⁅b, l⁆ * a⁻¹ = ⁅b, l⁆ := by
      rw [Subgroup.mem_centralizer_iff.mp (hb' l hl) a ha, mul_inv_cancel_right]
    rw [e, h1]
    exact Subgroup.mul_mem _ (hb' l hl) (ha' l hl)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨V.inv_mem ha, fun l hl => ?_⟩
    have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    have h1 : a⁻¹ * ⁅a, l⁆⁻¹ * a = ⁅a, l⁆⁻¹ := by
      have hc := Subgroup.inv_mem _ (ha' l hl)
      rw [mul_assoc, ← Subgroup.mem_centralizer_iff.mp hc a ha, inv_mul_cancel_left]
    rw [e, h1]
    exact Subgroup.inv_mem _ (ha' l hl)

theorem bSub_le : bSub V Lt ≤ V := fun _ h => h.1

include hS in
theorem le_normalizer_bSub : G₀ ≤ Subgroup.normalizer ((bSub V Lt : Subgroup U₀) : Set U₀) := by
  have key : ∀ g ∈ G₀, ∀ v ∈ bSub V Lt, g * v * g⁻¹ ∈ bSub V Lt := by
    rintro g hg v ⟨hv, hv'⟩
    refine ⟨conj_mem_of_le_normalizer hS.nV hg hv, fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ Lt := by
      have := (Subgroup.mem_normalizer_iff.mp (hS.nLt (G₀.inv_mem hg)) l).mp hl
      simpa using this
    have h1 := hv' _ hl'
    have e : ⁅g * v * g⁻¹, l⁆ = g * ⁅v, g⁻¹ * l * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ V := by
      have := conj_mem_of_le_normalizer hS.nV (G₀.inv_mem hg) hw
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp h1 _ hw'
    calc w * (g * ⁅v, g⁻¹ * l * g⁆ * g⁻¹)
        = g * ((g⁻¹ * w * g) * ⁅v, g⁻¹ * l * g⁆) * g⁻¹ := by group
      _ = g * (⁅v, g⁻¹ * l * g⁆ * (g⁻¹ * w * g)) * g⁻¹ := by rw [h2]
      _ = g * ⁅v, g⁻¹ * l * g⁆ * g⁻¹ * w := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key g hg v, fun hv => ?_⟩
  have := key g⁻¹ (G₀.inv_mem hg) _ hv
  simpa [mul_assoc] using this

include hS in
theorem commutator_v0_bSub : ⁅⁅V, Lt⁆, bSub V Lt⁆ = ⊥ := by
  have h1 : ⁅⁅Lt, bSub V Lt⁆, V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro l hl b hb
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hb.2 l hl)
  have h2 : ⁅⁅bSub V Lt, V⁆, Lt⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine (Subgroup.commutator_mono bSub_le le_rfl).trans ?_
    exact Subgroup.le_centralizer_iff.mp hS.ltC
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

include hS in
theorem commutator_v0_lt : ⁅⁅V, Lt⁆, Lt⁆ = ⁅V, Lt⁆ := by
  refine le_antisymm (Subgroup.commutator_mono hS.commV_le le_rfl) ?_
  set N := ⁅⁅V, Lt⁆, Lt⁆
  have hN : G₀ ≤ Subgroup.normalizer (N : Set U₀) :=
    le_normalizer_comm_of (le_normalizer_v0 hS) hS.nLt
  have h1 : ⁅⁅Lt, V⁆, Lt⁆ ≤ N := by rw [Subgroup.commutator_comm Lt V]
  have h2 : ⁅⁅V, Lt⁆, Lt⁆ ≤ N := le_rfl
  have h : ⁅⁅Lt, Lt⁆, V⁆ ≤ N :=
    three_subgroups_le (hS.lt_le.trans hN) (hS.lt_le.trans hN) (hS.v_le.trans hN) h1 h2
  rwa [hS.perf, Subgroup.commutator_comm] at h

include hS in
theorem mem_bSub_of_fix (he : 2 ≤ e ∧ e ≤ 4) (h4 : (fixV (hS.eS lam hlam1)).index = 4)
    (v : ↥V) (hv : (QuotientGroup.mk v : hS.YM lam) ∈ fixV (hS.kY lam hlam1)) :
    (v : U₀) ∈ bSub V Lt :=
  ⟨v.2, fun _ hl => commutator_mem_centralizer_of_fix hS lam hlam1 he h4 v hv hl⟩

end BSub

section Four

include hS in
theorem index_fixV_eS_eq_four
    (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
    (he4 : e = 4) : (fixV (hS.eS lam hlam1)).index = 4 := by
  have : Finite (hS.SM lam hlam1) := hS.finite_SM lam hlam1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (fixV (hS.eS lam hlam1)).index with hA
  have hA4 : A ≤ 4 := he4 ▸ hS.index_fixV_eS_le lam hlam1
  have hS2 : IsPGroup 2 (hS.SM lam hlam1) := fun s =>
    ⟨1, by rw [pow_one]; exact hS.sq_SM lam hlam1 s⟩
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hAd : A ∣ 2 ^ n := hn ▸ (fixV (hS.eS lam hlam1)).index_dvd_card
  obtain ⟨j, -, hAj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hAd
  have hcard4 : 4 ≤ Nat.card (hS.eS lam hlam1) := he4 ▸ hS.le_card_eS lam hlam1 hirr
  have hA1 : A ≠ 1 := by
    intro h1
    rw [hA, Subgroup.index_eq_one] at h1
    apply hS.eS_ne_bot lam hlam1 hirr (by omega)
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    ext s
    have hs : s ∈ fixV (hS.eS lam hlam1) := by rw [h1]; exact Subgroup.mem_top s
    exact hs x hx
  have hA2 : A ≠ 2 := by
    intro h2
    have hc0 := hS.card_commV_mul_card_fixV_SM lam hlam1 (P := hS.eS lam hlam1)
      (Subgroup.map_le_range _ _)
    have hc1 := (fixV (hS.eS lam hlam1)).index_mul_card
    have hpos : 0 < Nat.card (fixV (hS.eS lam hlam1)) := Nat.card_pos
    have hc : Nat.card (commV (hS.eS lam hlam1)) = 2 := by
      rw [← hc1, ← hA, h2] at hc0
      exact Nat.eq_of_mul_eq_mul_right hpos hc0
    have ha' : aI (hS.eS lam hlam1) ⊤ ⊥ = 2 := by rw [aI_top_bot]; exact h2
    have hc' : cI (hS.eS lam hlam1) ⊤ ⊥ = 2 := by rw [cI_top_bot]; exact hc
    have hk := relIndex_kerRel_le_two (hS.sq_SM lam hlam1) (stab_top _) (stab_bot _) ha' hc'
    have hker : kerRel (hS.eS lam hlam1) ⊤ ⊥ (stab_bot _) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨-, hx⟩
      rw [Subgroup.mem_bot]
      ext s
      have := hx s (Subgroup.mem_top s)
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
    rw [hker, Subgroup.relIndex_bot_left] at hk
    omega
  rw [hAj] at hA4 hA1 hA2 ⊢
  have hj2 : j ≤ 2 := by
    by_contra h3
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j
  · simp at hA1
  · simp at hA2
  · rfl

end Four

end CFSG.Quasithin.MS93.S38EA
