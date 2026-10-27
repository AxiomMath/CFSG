module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.H13.NQCat.F112G2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

section Action

@[expose] noncomputable def conjOn (H N : Subgroup G)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : ↥H →* MulAut ↥N where
  toFun h :=
    { toFun := fun y => ⟨(h : G) * y * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHN h.2) y).mp y.2⟩
      invFun := fun y => ⟨(h : G)⁻¹ * y * h, by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem h.2)) y).mp y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := by
    ext y
    simp
  map_mul' h k := by
    ext y
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, Subgroup.coe_mul, mul_inv_rev]
    group

end Action

section Chief

theorem simple_and_five {X : Type*} [Group X] (h : IsL2Quot 2 X) :
    IsSimpleGroup X ∧ ∃ x : X, orderOf x = 5 := by
  obtain ⟨e⟩ := h
  have hL4 : ∃ s : Finset (GaloisField 2 2), s.card = 4 := by
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    refine ⟨Finset.univ, ?_⟩
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hL4
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    e.trans (pslTwoGf2EquivSl 2)
  have hs : IsSimpleGroup X := e'.isSimpleGroup
  refine ⟨hs, ?_⟩
  have hc : Nat.card X = 60 := by
    rw [IsL2Quot.card (by norm_num) ⟨e⟩]
    norm_num
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card' 5 (by rw [hc]; norm_num)

theorem sixteen_le_relIndex {H L N : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥H))
    (hstep : IsChiefStep H (pCoreOf 2 H) L N) (hnc : ¬ IsCentralStep H L N) :
    16 ≤ L.relIndex N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  rw [not_le] at hlt
  apply hnc
  set U := pCoreOf 2 H with hU
  have hUH : U ≤ H := pCoreOf_le 2 H
  have hNU : N ≤ U := hstep.1.1
  have hLN : L ≤ N := hstep.2.2.1.le
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNUL : ⁅N, U⁆ ≤ L := F112W.commutator_le_of_isChiefStep (pCoreOf_isPGroup 2 H) hUH
    (le_normalizer_pCoreOf 2 H) hstep hNU
  have : (L.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2
    ((hNU.trans hUH).trans hHL)
  have hW : ∀ h : ↥H, (L.subgroupOf N).map ((conjOn H N hHN h : MulAut ↥N) : ↥N →* ↥N) =
      L.subgroupOf N := by
    intro h
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      show (h : G) * (w : G) * (h : G)⁻¹ ∈ L
      exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) w).mp hw
    · intro hy
      refine ⟨conjOn H N hHN h⁻¹ y, ?_, ?_⟩
      · show ((h⁻¹ : ↥H) : G) * (y : G) * ((h⁻¹ : ↥H) : G)⁻¹ ∈ L
        exact (Subgroup.mem_normalizer_iff.mp (hHL (h⁻¹).2) y).mp hy
      · show conjOn H N hHN h (conjOn H N hHN h⁻¹ y) = y
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  let ρ := SL2MinimalFaithful.quotientAction (conjOn H N hHN) (L.subgroupOf N) hW
  have hρ : ∀ (h : ↥H) (y : ↥N), ρ h (y : ↥N ⧸ L.subgroupOf N) =
      ((conjOn H N hHN h y : ↥N) : ↥N ⧸ L.subgroupOf N) := fun h y =>
    SL2MinimalFaithful.quotientAction_mk _ _ hW h y
  have hp : IsPGroup 2 (↥N ⧸ L.subgroupOf N) :=
    ((pCoreOf_isPGroup 2 H).to_le hNU).to_quotient _
  obtain ⟨d, hd⟩ := (IsPGroup.iff_card).1 hp
  have hd3 : d ≤ 3 := by
    have h1 : 2 ^ d < 2 ^ 4 := by
      have : Nat.card (↥N ⧸ L.subgroupOf N) = L.relIndex N := rfl
      rw [← hd, this]
      norm_num
      exact hlt
    exact Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h1)
  obtain ⟨hsimp, gq, hgq⟩ := simple_and_five hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  have h5 : 5 ∣ orderOf g := by
    rw [← hgq]
    exact orderOf_map_dvd (QuotientGroup.mk' _) g
  set x := g ^ (orderOf g / 5) with hx
  have hx5 : orderOf x = 5 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h5
  have hρx : ρ x = 1 := by
    by_contra hne
    obtain ⟨e, he, hdvd⟩ := SL2MinimalFaithful.exists_dvd_pow_sub_pow Nat.prime_two
      (by norm_num) ρ hx5 hne hd
    interval_cases d <;> interval_cases e <;> norm_num at hdvd
  have hρU : ∀ u : ↥H, u ∈ CFSG.Open.pCore 2 ↥H → ρ u = 1 := by
    intro u hu
    have hu' : (u : G) ∈ U := (F1.mem_pCore_iff_coe u).1 hu
    ext q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hρ, MulAut.one_apply, QuotientGroup.eq]
      show ((u : G) * (y : G) * (u : G)⁻¹)⁻¹ * (y : G) ∈ L
      have e : ((u : G) * (y : G) * (u : G)⁻¹)⁻¹ * (y : G) = ⁅(u : G), (y : G)⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hNUL (Subgroup.commutator_comm N U ▸
        Subgroup.commutator_mem_commutator hu' (N.inv_mem y.2))
  have hker : ρ.ker = ⊤ := by
    have hn : (ρ.ker.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).Normal :=
      (MonoidHom.normal_ker ρ).map _ (QuotientGroup.mk'_surjective _)
    rcases hn.eq_bot_or_eq_top with h0 | htop
    · exfalso
      have hxm : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) x ∈
          ρ.ker.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) := ⟨x, hρx, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxm
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)) ⟨x, hxm⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 : (5 : ℕ) ∣ 2 ^ k := hx5 ▸ orderOf_dvd_of_pow_eq_one hk'
      have h3 := (Nat.prime_five).dvd_of_dvd_pow h2
      norm_num at h3
    · rw [eq_top_iff]
      intro h _
      have hm : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) h ∈
          ρ.ker.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) := htop ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkh⟩ := hm
      have hkh' : k⁻¹ * h ∈ CFSG.Open.pCore 2 ↥H := (QuotientGroup.eq).1 hkh
      have e : h = k * (k⁻¹ * h) := by group
      rw [MonoidHom.mem_ker, e, map_mul, hk, hρU _ hkh', mul_one]
  intro g' hg' y hy
  have h1 : ρ ⟨g', hg'⟩ = 1 := by
    have : (⟨g', hg'⟩ : ↥H) ∈ ρ.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    exact this
  have h2 := congrArg (fun φ : MulAut (↥N ⧸ L.subgroupOf N) =>
    φ ((⟨y, hy⟩ : ↥N) : ↥N ⧸ L.subgroupOf N)) h1
  simp only [hρ, MulAut.one_apply] at h2
  have h3 : (((conjOn H N hHN ⟨g', hg'⟩ ⟨y, hy⟩ : ↥N))⁻¹ * ⟨y, hy⟩ : ↥N) ∈ L.subgroupOf N :=
    (QuotientGroup.eq).1 h2
  have h4 : (g' * y * g'⁻¹)⁻¹ * y ∈ L := h3
  have h5 : y * ((g' * y * g'⁻¹)⁻¹ * y)⁻¹ * y⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp ((hNU.trans hUH).trans hHL hy) _).mp (L.inv_mem h4)
  have e : y * ((g' * y * g'⁻¹)⁻¹ * y)⁻¹ * y⁻¹ = g' * y * g'⁻¹ * y⁻¹ := by group
  rwa [e] at h5

theorem sixteen_pow_le_card {H U : Subgroup G}
    (h16 : ∀ L N : Subgroup G, IsChiefStep H U L N → ¬ IsCentralStep H L N → 16 ≤ L.relIndex N)
    {N : Subgroup G} {n : ℕ} (h : IsChiefSeriesFrom H U N n) : 16 ^ n ≤ Nat.card N := by
  induction h with
  | bot => simp
  | @central N L n hstep hc hs ih =>
    exact ih.trans (Subgroup.card_le_of_le hstep.2.2.1.le)
  | @noncentral N L n hstep hnc hs ih =>
    have hLN : L ≤ N := hstep.2.2.1.le
    have h1 := Subgroup.relIndex_mul_card L N
    rw [inf_eq_left.2 hLN] at h1
    rw [pow_succ, ← h1, mul_comm]
    exact Nat.mul_le_mul (h16 L N hstep hnc) ih

end Chief

end CFSG.Quasithin.H13.NQCat.F112G2
