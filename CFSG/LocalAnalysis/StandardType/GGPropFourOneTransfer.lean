module

public import CFSG.RankThree.Transfer.FixedPoints
public import CFSG.RankThree.Transfer.PGroup
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.BigOperators.Intervals

public section

namespace CFSG.StandardType

open MulAction CFSG.RankThree.Transfer

variable {G : Type*} [Group G]

@[expose] def GGWeaklyClosed (W R : Subgroup G) : Prop :=
  ∀ g : G, (∀ w ∈ W, g⁻¹ * w * g ∈ R) → ∀ w ∈ W, g⁻¹ * w * g ∈ W

theorem mem_normalizer_of_forall_conj_mem [Finite G] {W : Subgroup G} {g : G}
    (hg : ∀ w ∈ W, g⁻¹ * w * g ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  let Q : Subgroup G := W.map (MulAut.conj g⁻¹).toMonoidHom
  have hQW : Q ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using hg w hw
  have hQeq : Q = W := Subgroup.eq_of_le_of_card_ge hQW
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hQeq] at hh
    obtain ⟨w, hw, rfl⟩ := hh
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro hh
    have := hQW ⟨g * h * g⁻¹, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem GGWeaklyClosed.mem_normalizer [Finite G] {W R : Subgroup G} (hW : GGWeaklyClosed W R)
    {g : G} (hg : ∀ w ∈ W, g⁻¹ * w * g ∈ R) : g ∈ Subgroup.normalizer (W : Set G) :=
  mem_normalizer_of_forall_conj_mem (hW g hg)

theorem GGWeaklyClosed.le_normalizer [Finite G] {W R : Subgroup G} (hW : GGWeaklyClosed W R)
    (hWR : W ≤ R) : R ≤ Subgroup.normalizer (W : Set G) := fun _ hr =>
  hW.mem_normalizer fun _ hw => R.mul_mem (R.mul_mem (R.inv_mem hr) (hWR hw)) hr

theorem eq_one_of_forall_smul_eq [Finite G] {p : ℕ} [Fact p.Prime] (R : Sylow p G)
    {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    {X : G ⧸ Subgroup.normalizer (W : Set G)} (hX : ∀ w ∈ W, w • X = X) :
    X = ((1 : G) : G ⧸ Subgroup.normalizer (W : Set G)) := by
  have hRN : (R : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer hWR
  obtain ⟨q, rfl⟩ : ∃ q : G, (q : G ⧸ Subgroup.normalizer (W : Set G)) = X :=
    ⟨Quotient.out X, QuotientGroup.out_eq' X⟩
  have hconj : ∀ w ∈ W, q⁻¹ * w * q ∈ Subgroup.normalizer (W : Set G) := fun w hw =>
    smul_coe_eq_iff.mp (hX w hw)
  let Q : Subgroup G := W.map (MulAut.conj q⁻¹).toMonoidHom
  have hQp : IsPGroup p Q := (R.isPGroup'.to_le hWR).map _
  have hQ'p : IsPGroup p (Q.subgroupOf (Subgroup.normalizer (W : Set G))) := hQp.comap_subtype
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (Subgroup.normalizer (W : Set G)) S (R.subtype hRN)
  have hmem : ∀ w ∈ W, (q * (n : G)⁻¹)⁻¹ * w * (q * (n : G)⁻¹) ∈ (R : Subgroup G) := by
    intro w hw
    have h1 : (⟨q⁻¹ * w * q, hconj w hw⟩ : Subgroup.normalizer (W : Set G)) ∈
        (S : Subgroup (Subgroup.normalizer (W : Set G))) :=
      hS (Subgroup.mem_subgroupOf.mpr ⟨w, hw, by simp⟩)
    have h2 : MulAut.conj n • (⟨q⁻¹ * w * q, hconj w hw⟩ : Subgroup.normalizer (W : Set G)) ∈
        ((R.subtype hRN : Sylow p (Subgroup.normalizer (W : Set G))) :
          Subgroup (Subgroup.normalizer (W : Set G))) := by
      rw [← hn, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h2
    convert h2 using 1
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hqN : q ∈ Subgroup.normalizer (W : Set G) := by
    have := (Subgroup.normalizer (W : Set G)).mul_mem (hW.mem_normalizer hmem) n.2
    simpa using this
  rw [QuotientGroup.eq]
  simpa using hqN

theorem exists_central_smul {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) {α : Type*} [MulAction R α] (W : Subgroup R) [hWn : W.Normal] (X₀ : α)
    (hX₀ : ∃ w ∈ W, w • X₀ ≠ X₀) :
    ∃ w ∈ W, (∀ c : R, ∀ Y ∈ orbit R X₀, c • w • Y = w • c • Y) ∧
      (∀ Y ∈ orbit R X₀, w ^ p • Y = Y) ∧ w • X₀ ≠ X₀ := by
  classical
  let K : Subgroup R :=
    { carrier := {c | ∀ Y ∈ orbit R X₀, c • Y = Y}
      mul_mem' := fun {a b} ha hb Y hY => by
        rw [mul_smul, hb Y hY, ha Y hY]
      one_mem' := fun Y _ => one_smul R Y
      inv_mem' := fun {a} ha Y hY => by
        rw [inv_smul_eq_iff]
        exact (ha Y hY).symm }
  have hKmem : ∀ c : R, c ∈ K ↔ ∀ Y ∈ orbit R X₀, c • Y = Y := fun _ => Iff.rfl
  have hKn : K.Normal := ⟨fun c hc d => by
    rw [hKmem] at hc ⊢
    intro Y hY
    have hY' : d⁻¹ • Y ∈ orbit R X₀ := by
      obtain ⟨e, rfl⟩ := hY
      exact ⟨d⁻¹ * e, mul_smul _ _ _⟩
    rw [mul_smul, mul_smul, hc _ hY', smul_inv_smul]⟩
  let π : R →* R ⧸ K := QuotientGroup.mk' K
  have hQp : IsPGroup p (R ⧸ K) := hR.to_quotient K
  have : Group.IsNilpotent (R ⧸ K) := hQp.isNilpotent
  have : (W.map π).Normal := hWn.map π (QuotientGroup.mk'_surjective K)
  have hne : W.map π ≠ ⊥ := by
    obtain ⟨w, hw, hwX⟩ := hX₀
    intro h
    have hw1 : π w ∈ W.map π := ⟨w, hw, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
    exact hwX (hw1 X₀ (mem_orbit_self X₀))
  have hH := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set H := W.map π ⊓ Subgroup.center (R ⧸ K) with hHdef
  have hHp : IsPGroup p H := hQp.to_subgroup H
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨m, hm, hcard⟩ := hHp.nontrivial_iff_card.mp this
  have hpd : p ∣ Nat.card H := by
    rw [hcard]
    exact dvd_pow_self p hm.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpd
  obtain ⟨w, hw, hwz⟩ := (Subgroup.mem_inf.mp z.2).1
  have hzc := (Subgroup.mem_inf.mp z.2).2
  have hcomm : ∀ c : R, ∀ Y ∈ orbit R X₀, c • w • Y = w • c • Y := by
    intro c Y hY
    have h1 : π (w * c) = π (c * w) := by
      rw [map_mul, map_mul, hwz]
      exact (Subgroup.mem_center_iff.mp hzc (π c)).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 := (hKmem _).mp h1 Y hY
    rw [mul_smul, inv_smul_eq_iff] at h2
    rw [← mul_smul, ← mul_smul]
    exact h2
  refine ⟨w, hw, hcomm, ?_, ?_⟩
  · intro Y hY
    have h1 : π (w ^ p) = 1 := by
      rw [map_pow, hwz, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1 Y hY
  · intro hwX
    have hwK : w ∈ K := by
      intro Y hY
      obtain ⟨c, rfl⟩ := hY
      rw [← hcomm c X₀ (mem_orbit_self X₀), hwX]
    have hz1 : z = 1 := by
      apply Subtype.ext
      rw [← hwz, Subgroup.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hwK
    rw [hz1, orderOf_one] at hz
    exact (Fact.out : p.Prime).one_lt.ne hz

theorem pow_inv_mul_mul_pow_eq {x w : G} (hc : Commute (x⁻¹ * w⁻¹ * x * w) w) (i : ℕ) :
    (w ^ i)⁻¹ * x * w ^ i = x * (x⁻¹ * w⁻¹ * x * w) ^ i := by
  set c := x⁻¹ * w⁻¹ * x * w with hc_def
  induction i with
  | zero => simp
  | succ i ih =>
    have hci : Commute (c ^ i) w := hc.pow_left i
    have hwx : w⁻¹ * x * w = x * c := by rw [hc_def]; group
    calc (w ^ (i + 1))⁻¹ * x * w ^ (i + 1) = w⁻¹ * ((w ^ i)⁻¹ * x * w ^ i) * w := by
          rw [pow_succ]; group
      _ = w⁻¹ * (x * c ^ i) * w := by rw [ih]
      _ = (w⁻¹ * x * w) * (w⁻¹ * c ^ i * w) := by group
      _ = (x * c) * c ^ i := by
          rw [hwx, mul_assoc w⁻¹, hci.eq, inv_mul_cancel_left]
      _ = x * c ^ (i + 1) := by rw [pow_succ', mul_assoc]

theorem prod_range_cosetValue_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {H : Subgroup G} (ψ : H →* Multiplicative (ZMod p)) {x w q : G}
    (hc : Commute (x⁻¹ * w⁻¹ * x * w) w)
    (hfix : ∀ i : ℕ, (w ^ i * q)⁻¹ * x * (w ^ i * q) ∈ H) :
    ∏ i ∈ Finset.range p, cosetValue ψ x ((w ^ i * q : G) : G ⧸ H) = 1 := by
  set c := x⁻¹ * w⁻¹ * x * w with hc_def
  have h0 : q⁻¹ * x * q ∈ H := by simpa using hfix 0
  have hcq : q⁻¹ * c * q ∈ H := by
    have h1 : (w * q)⁻¹ * x * (w * q) ∈ H := by simpa using hfix 1
    have e : q⁻¹ * c * q = (q⁻¹ * x * q)⁻¹ * ((w * q)⁻¹ * x * (w * q)) := by
      rw [hc_def]; group
    rw [e]
    exact H.mul_mem (H.inv_mem h0) h1
  have hval : ∀ i : ℕ, cosetValue ψ x ((w ^ i * q : G) : G ⧸ H) =
      ψ ⟨_, h0⟩ * ψ ⟨_, hcq⟩ ^ i := by
    intro i
    rw [cosetValue_coe ψ (hfix i), ← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    have e1 : (w ^ i * q)⁻¹ * x * (w ^ i * q) = q⁻¹ * ((w ^ i)⁻¹ * x * w ^ i) * q := by group
    have e2 : (q⁻¹ * c * q) ^ i = q⁻¹ * c ^ i * q := by
      simpa using conj_pow (i := i) (a := q⁻¹) (b := c)
    rw [e1, pow_inv_mul_mul_pow_eq hc i, ← hc_def, e2]
    group
  have hpow : ∀ a : Multiplicative (ZMod p), a ^ p = 1 := fun a => by
    have := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := a)
    rwa [card_multiplicative_zmod] at this
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hp.out.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hp2
    · exact ⟨k, hk⟩
  have hsum : ∑ i ∈ Finset.range p, i = p * k := by
    have h := Finset.sum_range_id_mul_two p
    have hp1 : p - 1 = 2 * k := by omega
    have h' : (∑ i ∈ Finset.range p, i) * 2 = (p * k) * 2 := by
      rw [h, hp1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  simp_rw [hval]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum,
    hsum, hpow, one_mul, pow_mul, hpow, one_pow]

theorem prod_eq_one_of_cyclic {H α M : Type*} [Group H] [MulAction H α] [CommMonoid M]
    {p : ℕ} [Fact p.Prime] (w : H) (S : Finset α) (f : α → M)
    (hS : ∀ Y ∈ S, w • Y ∈ S) (hper : ∀ Y ∈ S, w ^ p • Y = Y) (hne : ∀ Y ∈ S, w • Y ≠ Y)
    (hf : ∀ Y ∈ S, ∏ i ∈ Finset.range p, f (w ^ i • Y) = 1) :
    ∏ Y ∈ S, f Y = 1 := by
  classical
  let ρ : α → orbitRel.Quotient (Subgroup.zpowers w) α := Quotient.mk''
  have hρ : ∀ Y Z : α, ρ Y = ρ Z ↔ Y ∈ orbit (Subgroup.zpowers w) Z := fun _ _ =>
    Quotient.eq''.trans orbitRel_apply
  have hSpow : ∀ i : ℕ, ∀ Y ∈ S, w ^ i • Y ∈ S := by
    intro i
    induction i with
    | zero => intro Y hY; simpa using hY
    | succ i ih =>
      intro Y hY
      rw [pow_succ, mul_smul]
      exact ih _ (hS Y hY)
  rw [← Finset.prod_fiberwise_of_maps_to (t := S.image ρ) (g := ρ)
    (fun Y hY => Finset.mem_image_of_mem ρ hY) f]
  refine Finset.prod_eq_one fun b hb => ?_
  obtain ⟨Y₀, hY₀, rfl⟩ := Finset.mem_image.mp hb
  have hmin : Function.minimalPeriod (fun Y => w • Y) Y₀ = p := by
    refine Function.minimalPeriod_eq_prime ?_ ?_
    · change (fun Y => w • Y)^[p] Y₀ = Y₀
      rw [smul_iterate]
      exact hper Y₀ hY₀
    · exact hne Y₀ hY₀
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfib : S.filter (fun Y => ρ Y = ρ Y₀) =
      (Finset.range p).image (fun i => w ^ i • Y₀) := by
    ext Y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨-, hYρ⟩
      obtain ⟨⟨g, hg⟩, rfl⟩ := (hρ Y Y₀).mp hYρ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hlt := Int.emod_lt_of_pos n hp0
      have hnn := Int.emod_nonneg n hp0.ne'
      refine ⟨(n % p).toNat, by omega, ?_⟩
      change w ^ (n % (p : ℤ)).toNat • Y₀ = (w ^ n : H) • Y₀
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
      conv_lhs => rw [← hmin]
      exact zpow_smul_mod_minimalPeriod w Y₀ n
    · rintro ⟨i, -, rfl⟩
      exact ⟨hSpow i Y₀ hY₀, (hρ _ _).mpr ⟨⟨w ^ i, Subgroup.npow_mem_zpowers w i⟩, rfl⟩⟩
  rw [hfib, Finset.prod_image]
  · exact hf Y₀ hY₀
  · intro i hi j hj hij
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := fun Y => w • Y) (x := Y₀)
    rw [hmin] at hinj
    apply hinj (by simpa using hi) (by simpa using hj)
    simpa only [smul_iterate] using hij

theorem map_eq_one_of_orderOf_lt_of_pow_eq_one [Finite G] {p : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (ψ : H →* Multiplicative (ZMod p)) {x : G} (hxp : x ^ p = 1) (h : H)
    (hlt : orderOf (h : G) < orderOf x) : ψ h = 1 := by
  have hpos := orderOf_pos (h : G)
  have hox : orderOf x ≤ p := Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one hxp)
  have hndvd : ¬ p ∣ orderOf (h : G) := Nat.not_dvd_of_pos_of_lt hpos (by omega)
  have h1 : orderOf (ψ h) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    have := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := ψ h)
    rwa [card_multiplicative_zmod] at this
  have h2 : orderOf (ψ h) ∣ orderOf (h : G) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, Subgroup.orderOf_coe, pow_orderOf_eq_one, map_one]
  rcases (Nat.dvd_prime hp.out).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · exact absurd (h3 ▸ h2) hndvd

theorem transfer_eq_of_ggWeaklyClosed_of_orderOf [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p))
    {x : G} (hxR : x ∈ (R : Subgroup G))
    (hψord : ∀ h : Subgroup.normalizer (W : Set G), orderOf (h : G) < orderOf x → ψ h = 1)
    (hc : ∀ w ∈ W, Commute (x⁻¹ * w⁻¹ * x * w) w) :
    ψ.transfer x = ψ ⟨x, hW.le_normalizer hWR hxR⟩ := by
  classical
  have hRN : (R : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer hWR
  have : Fintype (G ⧸ Subgroup.normalizer (W : Set G)) := Fintype.ofFinite _
  set F : G ⧸ Subgroup.normalizer (W : Set G) → Multiplicative (ZMod p) :=
    fun X => if x • X = X then cosetValue ψ x X else 1 with hF
  have htot : ψ.transfer x = ∏ X, F X := transfer_eq_prod_fixed_of_orderOf_lt ψ x hψord
  rw [htot]
  set X₁ : G ⧸ Subgroup.normalizer (W : Set G) :=
    ((1 : G) : G ⧸ Subgroup.normalizer (W : Set G)) with hX₁
  let π : G ⧸ Subgroup.normalizer (W : Set G) →
      orbitRel.Quotient (R : Subgroup G) (G ⧸ Subgroup.normalizer (W : Set G)) := Quotient.mk''
  have : Fintype (orbitRel.Quotient (R : Subgroup G) (G ⧸ Subgroup.normalizer (W : Set G))) :=
    Fintype.ofFinite _
  have hπ : ∀ X Y, π X = π Y ↔ X ∈ orbit (R : Subgroup G) Y := fun _ _ =>
    Quotient.eq''.trans orbitRel_apply
  have hfib₁ : (Finset.univ.filter fun X => π X = π X₁) = {X₁} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hπ]
    constructor
    · rintro ⟨c, rfl⟩
      change c • X₁ = X₁
      rw [Subgroup.smul_def, hX₁, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq, mul_one]
      exact Subgroup.inv_mem _ (hRN c.2)
    · rintro rfl
      exact mem_orbit_self _
  have hFX₁ : F X₁ = ψ ⟨x, hRN hxR⟩ := by
    have hx1 : (1 : G)⁻¹ * x * 1 ∈ Subgroup.normalizer (W : Set G) := by simpa using hRN hxR
    have hfix : x • X₁ = X₁ := smul_coe_eq_iff.mpr hx1
    rw [hF]
    simp only [hfix, ite_true]
    rw [hX₁, cosetValue_coe ψ hx1]
    congr 1
    exact Subtype.ext (by simp)
  have horbit : ∀ X₀, π X₀ ≠ π X₁ →
      ∏ X ∈ Finset.univ.filter (fun X => π X = π X₀), F X = 1 := by
    intro X₀ hX₀
    have hmove : ∃ w ∈ W.subgroupOf (R : Subgroup G), w • X₀ ≠ X₀ := by
      by_contra hcon
      push Not at hcon
      exact hX₀ (by rw [eq_one_of_forall_smul_eq R hWR hW fun w hw => hcon ⟨w, hWR hw⟩ hw])
    have : (W.subgroupOf (R : Subgroup G)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hRN
    obtain ⟨w, hwW, hcen, hpow, hwX₀⟩ :=
      exists_central_smul (p := p) R.isPGroup' (W.subgroupOf (R : Subgroup G)) X₀ hmove
    set x' : (R : Subgroup G) := ⟨x, hxR⟩ with hx'
    have hmemS : ∀ X, X ∈ Finset.univ.filter (fun X => π X = π X₀) ↔
        X ∈ orbit (R : Subgroup G) X₀ := fun X => by simp [hπ]
    have hworb : ∀ Y ∈ orbit (R : Subgroup G) X₀, w • Y ∈ orbit (R : Subgroup G) X₀ := by
      rintro _ ⟨c, rfl⟩
      exact ⟨w * c, mul_smul _ _ _⟩
    have hxw : ∀ i : ℕ, ∀ Y ∈ orbit (R : Subgroup G) X₀, x' • w ^ i • Y = w ^ i • x' • Y := by
      intro i
      induction i with
      | zero => intro Y _; simp
      | succ i ih =>
        intro Y hY
        rw [pow_succ, mul_smul, mul_smul, ih _ (hworb Y hY), hcen x' Y hY]
    refine prod_eq_one_of_cyclic (p := p) w _ F ?_ ?_ ?_ ?_
    · intro Y hY
      rw [hmemS] at hY ⊢
      exact hworb Y hY
    · intro Y hY
      exact hpow Y ((hmemS Y).mp hY)
    · intro Y hY hwY
      obtain ⟨c, rfl⟩ := (hmemS _).mp hY
      rw [← hcen c X₀ (mem_orbit_self X₀)] at hwY
      exact hwX₀ (smul_left_cancel c hwY)
    · intro Y hY
      have hYo := (hmemS Y).mp hY
      by_cases hxY : x • Y = Y
      · obtain ⟨q, rfl⟩ : ∃ q : G, (q : G ⧸ Subgroup.normalizer (W : Set G)) = Y :=
          ⟨Quotient.out Y, QuotientGroup.out_eq' Y⟩
        have hwq : ∀ i : ℕ, w ^ i • ((q : G) : G ⧸ Subgroup.normalizer (W : Set G)) =
            ((((w : G) ^ i * q) : G) : G ⧸ Subgroup.normalizer (W : Set G)) := by
          intro i
          rw [Subgroup.smul_def, Subgroup.coe_pow, MulAction.Quotient.smul_mk, smul_eq_mul]
        have hfixi : ∀ i : ℕ, x • w ^ i • ((q : G) : G ⧸ Subgroup.normalizer (W : Set G)) =
            w ^ i • ((q : G) : G ⧸ Subgroup.normalizer (W : Set G)) := by
          intro i
          have h1 := hxw i _ hYo
          change x' • (w ^ i • ((q : G) : G ⧸ Subgroup.normalizer (W : Set G))) = _
          rw [h1]
          exact congrArg (w ^ i • ·) hxY
        have hfix : ∀ i : ℕ, ((w : G) ^ i * q)⁻¹ * x * ((w : G) ^ i * q) ∈
            Subgroup.normalizer (W : Set G) := by
          intro i
          rw [← smul_coe_eq_iff, ← hwq]
          exact hfixi i
        have hFi : ∀ i ∈ Finset.range p,
            F (w ^ i • ((q : G) : G ⧸ Subgroup.normalizer (W : Set G))) =
              cosetValue ψ x ((((w : G) ^ i * q) : G) : G ⧸ Subgroup.normalizer (W : Set G)) := by
          intro i _
          rw [hF]
          simp only [hfixi i, ↓reduceIte]
          rw [hwq i]
        rw [Finset.prod_congr rfl hFi]
        exact prod_range_cosetValue_eq_one hp2 ψ (hc _ hwW) hfix
      · refine Finset.prod_eq_one fun i _ => ?_
        rw [hF]
        dsimp only
        split_ifs with hfix
        · exfalso
          apply hxY
          change x' • w ^ i • Y = w ^ i • Y at hfix
          rw [hxw i Y hYo] at hfix
          exact smul_left_cancel _ hfix
        · rfl
  rw [← Finset.prod_fiberwise Finset.univ π F,
    Finset.prod_eq_single (π X₁) (fun o _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h),
    hfib₁, Finset.prod_singleton, hFX₁]
  obtain ⟨X₀, rfl⟩ := Quotient.exists_rep o
  exact horbit X₀ hne

theorem transfer_eq_of_ggWeaklyClosed [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p))
    {x : G} (hxR : x ∈ (R : Subgroup G)) (hxp : x ^ p = 1)
    (hc : ∀ w ∈ W, Commute (x⁻¹ * w⁻¹ * x * w) w) :
    ψ.transfer x = ψ ⟨x, hW.le_normalizer hWR hxR⟩ :=
  transfer_eq_of_ggWeaklyClosed_of_orderOf hp2 R hWR hW ψ hxR
    (map_eq_one_of_orderOf_lt_of_pow_eq_one ψ hxp) hc

theorem surjective_transfer_of_ggWeaklyClosed [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p))
    {x : G} (hxR : x ∈ (R : Subgroup G)) (hxp : x ^ p = 1)
    (hc : ∀ w ∈ W, Commute (x⁻¹ * w⁻¹ * x * w) w)
    (hψx : ψ ⟨x, hW.le_normalizer hWR hxR⟩ ≠ 1) :
    Function.Surjective ψ.transfer ∧ ψ.transfer x ≠ 1 := by
  have hV := transfer_eq_of_ggWeaklyClosed hp2 R hWR hW ψ hxR hxp hc
  refine ⟨?_, hV ▸ hψx⟩
  have : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
    ⟨by rw [card_multiplicative_zmod]; exact hp.out⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ψ.transfer.range with h | h
  · exfalso
    apply hψx
    rw [← hV]
    have hmem : ψ.transfer x ∈ ψ.transfer.range := ⟨x, rfl⟩
    rwa [h, Subgroup.mem_bot] at hmem
  · exact MonoidHom.range_eq_top.mp h

theorem not_isSimpleGroup_of_ggWeaklyClosed [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p))
    {x : G} (hxR : x ∈ (R : Subgroup G)) (hxp : x ^ p = 1)
    (hc : ∀ w ∈ W, Commute (x⁻¹ * w⁻¹ * x * w) w)
    (hψx : ψ ⟨x, hW.le_normalizer hWR hxR⟩ ≠ 1) (hnc : ∃ a b : G, a * b ≠ b * a) :
    ¬ IsSimpleGroup G := by
  intro hs
  have hVx := (surjective_transfer_of_ggWeaklyClosed hp2 R hWR hW ψ hxR hxp hc hψx).2
  rcases ψ.transfer.normal_ker.eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnc
    apply hab
    apply (MonoidHom.ker_eq_bot_iff _).mp h
    exact (ψ.transfer.map_mul a b).trans ((mul_comm _ _).trans (ψ.transfer.map_mul b a).symm)
  · apply hVx
    have hmem : x ∈ ψ.transfer.ker := h ▸ Subgroup.mem_top x
    exact hmem

theorem commute_of_isMulCommutative {W : Subgroup G} (hWab : IsMulCommutative W) {x : G}
    (hxN : x ∈ Subgroup.normalizer (W : Set G)) {w : G} (hw : w ∈ W) :
    Commute (x⁻¹ * w⁻¹ * x * w) w := by
  have hxw : x⁻¹ * w⁻¹ * x ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) w⁻¹).mp (W.inv_mem hw)
    simpa using this
  obtain ⟨c, hcW, hc⟩ : ∃ c ∈ W, c = x⁻¹ * w⁻¹ * x := ⟨_, hxw, rfl⟩
  have hcomm : c * w = w * c := congrArg Subtype.val (hWab.is_comm.comm ⟨c, hcW⟩ ⟨w, hw⟩)
  rw [← hc]
  show c * w * w = w * (c * w)
  rw [hcomm, mul_assoc, hcomm]

theorem exists_transfer_ne_one_of_isMulCommutative [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (hWab : IsMulCommutative W)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1) :
    ∃ x : G, ψ.transfer x ≠ 1 := by
  classical
  have hRN : (R : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := hW.le_normalizer hWR
  have hex : ∃ n, ∃ y : Subgroup.normalizer (W : Set G), ψ y ≠ 1 ∧ orderOf (y : G) = n := by
    obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (MonoidHom.ext h)
    exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy1, hyn⟩ := Nat.find_spec hex
  have hmin : ∀ h : Subgroup.normalizer (W : Set G), orderOf (h : G) < orderOf (y : G) →
      ψ h = 1 := by
    intro h hlt
    by_contra hne
    have := Nat.find_min' hex ⟨h, hne, rfl⟩
    omega
  have hψpow : ∀ a : Multiplicative (ZMod p), a ^ p = 1 := fun a => by
    have := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := a)
    rwa [card_multiplicative_zmod] at this
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (y : G)).ne' p hp.out.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hm1 : m = 1 := by
    by_contra hm1
    have hlt : orderOf ((y ^ m : Subgroup.normalizer (W : Set G)) : G) < orderOf (y : G) := by
      rw [Subgroup.coe_pow, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hord.symm), hord,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
      have hpa : 0 < p ^ a := pow_pos hp.out.pos a
      have h1m : 1 < m := by omega
      nlinarith
    apply hy1
    have h1 := hmin _ hlt
    rw [map_pow] at h1
    have h3 : orderOf (ψ y) ∣ Nat.gcd p m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hψpow (ψ y))) (orderOf_dvd_of_pow_eq_one h1)
    rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm), Nat.dvd_one,
      orderOf_eq_one_iff] at h3
  rw [hm1, mul_one] at hord
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hord]
  obtain ⟨S, hS⟩ := hyp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (Subgroup.normalizer (W : Set G)) S (R.subtype hRN)
  have hxmem : MulAut.conj n • y ∈
      ((R.subtype hRN : Sylow p (Subgroup.normalizer (W : Set G))) :
        Subgroup (Subgroup.normalizer (W : Set G))) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS (Subgroup.mem_zpowers y))
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hxmem
  have hψx : ψ (MulAut.conj n • y) = ψ y := by
    rw [MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]
  have hordx : orderOf ((MulAut.conj n • y : Subgroup.normalizer (W : Set G)) : G) =
      orderOf (y : G) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulAut.smul_def, MulEquiv.orderOf_eq]
  have hV := transfer_eq_of_ggWeaklyClosed_of_orderOf hp2 R hWR hW ψ hxmem
    (fun h hlt => hmin h (hordx ▸ hlt))
    (fun w hw => commute_of_isMulCommutative hWab (MulAut.conj n • y).2 hw)
  refine ⟨((MulAut.conj n • y : Subgroup.normalizer (W : Set G)) : G), ?_⟩
  rw [hV]
  change ψ (MulAut.conj n • y) ≠ 1
  rw [hψx]
  exact hy1

theorem surjective_transfer_of_isMulCommutative [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (hWab : IsMulCommutative W)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1) :
    Function.Surjective ψ.transfer := by
  obtain ⟨x, hx⟩ := exists_transfer_ne_one_of_isMulCommutative hp2 R hWR hW hWab ψ hψ
  have : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
    ⟨by rw [card_multiplicative_zmod]; exact hp.out⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ψ.transfer.range with h | h
  · exfalso
    have hmem : ψ.transfer x ∈ ψ.transfer.range := ⟨x, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hx hmem
  · exact MonoidHom.range_eq_top.mp h

theorem not_isSimpleGroup_of_isMulCommutative [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (R : Sylow p G) {W : Subgroup G} (hWR : W ≤ R) (hW : GGWeaklyClosed W R)
    (hWab : IsMulCommutative W)
    (ψ : Subgroup.normalizer (W : Set G) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1)
    (hnc : ∃ a b : G, a * b ≠ b * a) : ¬ IsSimpleGroup G := by
  intro hs
  obtain ⟨x, hx⟩ := exists_transfer_ne_one_of_isMulCommutative hp2 R hWR hW hWab ψ hψ
  rcases ψ.transfer.normal_ker.eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnc
    apply hab
    apply (MonoidHom.ker_eq_bot_iff _).mp h
    exact (ψ.transfer.map_mul a b).trans ((mul_comm _ _).trans (ψ.transfer.map_mul b a).symm)
  · apply hx
    have hmem : x ∈ ψ.transfer.ker := h ▸ Subgroup.mem_top x
    exact hmem

end CFSG.StandardType

end
