module

public import CFSG.Quasithin.EmptyFaithful.S152O4FBasic
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Z16

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.S1417

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem pow_mod_two_of_mul_self {U : Type*} [CommGroup U] {c : U} (h : c * c = 1) (k : ℕ) :
    c ^ (k % 2) = c ^ k := by
  have h2 : c ^ 2 = 1 := by rw [pow_two]; exact h
  conv_rhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, h2, one_pow, mul_one]

omit [Finite V] in
theorem pow_val_add_of_mul_self {U : Type*} [CommGroup U] {c : U} (h : c * c = 1) (z w : ZMod 2) :
    c ^ (z + w).val = c ^ z.val * c ^ w.val := by
  rw [ZMod.val_add, pow_mod_two_of_mul_self h, pow_add]

omit [Finite V] in
theorem exists_mulEquiv_F2sq {U : Type*} [CommGroup U] [Finite U] (hU : ∀ u : U, u * u = 1)
    (hcard : Nat.card U = 4) : Nonempty (U ≃* F2sq) := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hcard' : Fintype.card U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨a, ha⟩ : ∃ a : U, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card U ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => by rw [h x, h y]
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : U, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset U) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    have h2 : ({1, a} : Finset U).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at this
    omega
  have ha2 : a * a = 1 := hU a
  have hb2 : b * b = 1 := hU b
  let ψ : F2sq →* U :=
    { toFun := fun x => a ^ (Multiplicative.toAdd x 0).val * b ^ (Multiplicative.toAdd x 1).val
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [toAdd_mul, Pi.add_apply, pow_val_add_of_mul_self ha2,
          pow_val_add_of_mul_self hb2]
        rw [mul_mul_mul_comm] }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hv : ∀ z : ZMod 2, z.val = 0 ∨ z.val = 1 := by decide
    have hx' : a ^ (Multiplicative.toAdd x 0).val * b ^ (Multiplicative.toAdd x 1).val = 1 := hx
    rcases hv (Multiplicative.toAdd x 0) with hv0 | hv0 <;>
      rcases hv (Multiplicative.toAdd x 1) with hv1 | hv1
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · simpa using (ZMod.val_eq_zero _).mp hv0
      · simpa using (ZMod.val_eq_zero _).mp hv1
    · exfalso
      rw [hv0, hv1] at hx'
      simp at hx'
      exact hb1 hx'
    · exfalso
      rw [hv0, hv1] at hx'
      simp at hx'
      exact ha hx'
    · exfalso
      rw [hv0, hv1] at hx'
      simp at hx'
      apply hba
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right hx'
      rw [this]
      exact (inv_eq_of_mul_eq_one_right ha2)
  have hcardF : Nat.card F2sq = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hinj, by rw [hcard, hcardF]⟩
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

section S3

variable {L : Subgroup (MulAut V)} {U : Subgroup V}

omit [Finite V] in
theorem cube_of_not_invol (hN : ActsAsNaturalL2 L U) {m : MulAut V} (hm : m ∈ L)
    (h : ¬ (m ^ 2 = 1 ∧ m ≠ 1)) : m ^ 3 = 1 := by
  rcases S152O.eq_one_or_invol_or_cube hN hm with h1 | h1 | ⟨h1, -⟩
  · rw [h1]; simp
  · exact absurd h1 h
  · exact h1

end S3

section Omega

variable {O M₁ M₂ : Subgroup (MulAut V)} {s : MulAut V}

theorem sl2_inv_mul_aux : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ((a * b) ^ 2 = 1 ∧ a * b ≠ 1) ↔ ¬ ((a ^ 2 = 1 ∧ a ≠ 1) ↔ (b ^ 2 = 1 ∧ b ≠ 1)) := by
  decide +kernel

omit [Finite V] in
theorem inv_mul_iff {L : Subgroup (MulAut V)} {U : Subgroup V} (hN : ActsAsNaturalL2 L U)
    {a b : MulAut V} (ha : a ∈ L) (hb : b ∈ L) :
    ((a * b) ^ 2 = 1 ∧ a * b ≠ 1) ↔ ¬ ((a ^ 2 = 1 ∧ a ≠ 1) ↔ (b ^ 2 = 1 ∧ b ≠ 1)) := by
  obtain ⟨e, -, -⟩ := hN
  have key : ∀ (z : MulAut V) (hz : z ∈ L) (n : ℕ), z ^ n = 1 ↔ (e ⟨z, hz⟩) ^ n = 1 := by
    intro z hz n
    rw [← map_pow, ← map_one e, e.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have key1 : ∀ (z : MulAut V) (hz : z ∈ L), z = 1 ↔ e ⟨z, hz⟩ = 1 := by
    intro z hz
    rw [← map_one e, e.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hab : a * b ∈ L := L.mul_mem ha hb
  have e1 : e ⟨a * b, hab⟩ = e ⟨a, ha⟩ * e ⟨b, hb⟩ := map_mul e ⟨a, ha⟩ ⟨b, hb⟩
  have h1 : ((a * b) ^ 2 = 1 ∧ a * b ≠ 1) ↔
      ((e ⟨a, ha⟩ * e ⟨b, hb⟩) ^ 2 = 1 ∧ e ⟨a, ha⟩ * e ⟨b, hb⟩ ≠ 1) := by
    rw [← e1]
    exact and_congr (key (a * b) hab 2) (not_congr (key1 (a * b) hab))
  have h2 : (a ^ 2 = 1 ∧ a ≠ 1) ↔ ((e ⟨a, ha⟩) ^ 2 = 1 ∧ e ⟨a, ha⟩ ≠ 1) :=
    and_congr (key a ha 2) (not_congr (key1 a ha))
  have h3 : (b ^ 2 = 1 ∧ b ≠ 1) ↔ ((e ⟨b, hb⟩) ^ 2 = 1 ∧ e ⟨b, hb⟩ ≠ 1) :=
    and_congr (key b hb 2) (not_congr (key1 b hb))
  rw [h1, h2, h3]
  exact sl2_inv_mul_aux _ _

omit [Finite V] in
theorem cube_iff_not_inv {L : Subgroup (MulAut V)} {U : Subgroup V} (hN : ActsAsNaturalL2 L U)
    {m : MulAut V} (hm : m ∈ L) : m ^ 3 = 1 ↔ ¬ (m ^ 2 = 1 ∧ m ≠ 1) := by
  refine ⟨fun h3 => ?_, cube_of_not_invol hN hm⟩
  rintro ⟨h2, h1⟩
  apply h1
  calc m = m ^ 3 * (m ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

omit [Finite V] in
theorem conj_inv_iff (t m : MulAut V) :
    ((t * m * t⁻¹) ^ 2 = 1 ∧ t * m * t⁻¹ ≠ 1) ↔ (m ^ 2 = 1 ∧ m ≠ 1) := by
  have e : (t * m * t⁻¹) ^ 2 = t * m ^ 2 * t⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [e]
  have key : ∀ z : MulAut V, t * z * t⁻¹ = 1 ↔ z = 1 := fun z => by
    constructor
    · intro h
      have := congrArg (fun y => t⁻¹ * y * t) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      simp
  simp only [ne_eq, key]

omit [Finite V] in
theorem pow_eq_one_iff_of_mul (hS : OfourStruct O M₁ M₂ s) {m₁ m₂ : MulAut V} (hm₁ : m₁ ∈ M₁)
    (hm₂ : m₂ ∈ M₂) (n : ℕ) : (m₁ * m₂) ^ n = 1 ↔ m₁ ^ n = 1 ∧ m₂ ^ n = 1 := by
  have hcomm : Commute m₁ m₂ := hS.comm m₁ hm₁ m₂ hm₂
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcomm.mul_pow] at h
    have h1 : m₁ ^ n ∈ M₁ ⊓ M₂ := ⟨M₁.pow_mem hm₁ n, by
      have : m₁ ^ n = (m₂ ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact M₂.inv_mem (M₂.pow_mem hm₂ n)⟩
    rw [hS.Linf, Subgroup.mem_bot] at h1
    refine ⟨h1, ?_⟩
    rw [h1, one_mul] at h
    exact h
  · rw [hcomm.mul_pow, h.1, h.2, one_mul]

omit [Finite V] in
theorem conjAut_eq_of_swap (hS : OfourStruct O M₁ M₂ s) {g : MulAut V} (hg : g ∈ O)
    (hgN : g ∉ M₁ ⊔ M₂) : B1.conjAut g M₁ = M₂ ∧ B1.conjAut g M₂ = M₁ := by
  rcases hS.perm g hg with ⟨h1, -⟩ | h
  · exact absurd ((hS.mem_sup_iff hg).mpr fun u hu =>
      OfourStruct.commV_apply_mem g M₁ M₁ h1 hu) hgN
  · exact h

omit [Finite V] in
theorem apply_mem_of_swap (hS : OfourStruct O M₁ M₂ s) {g : MulAut V} (hg : g ∈ O)
    (hgN : g ∉ M₁ ⊔ M₂) :
    (∀ u ∈ commV M₁, g u ∈ commV M₂) ∧ (∀ u ∈ commV M₂, g u ∈ commV M₁) := by
  obtain ⟨h1, h2⟩ := conjAut_eq_of_swap hS hg hgN
  exact ⟨fun u hu => OfourStruct.commV_apply_mem g M₁ M₂ h1 hu,
    fun u hu => OfourStruct.commV_apply_mem g M₂ M₁ h2 hu⟩

omit [Finite V] in
theorem not_mem_sup_of_swap (hS : OfourStruct O M₁ M₂ s) {g : MulAut V} (hg : g ∈ O)
    (hg₁ : ∀ u ∈ commV M₁, g u ∈ commV M₂) : g ∉ M₁ ⊔ M₂ := by
  intro hgN
  have hst := (hS.mem_sup_iff hg).mp hgN
  have hbot : commV M₁ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h1 : g u ∈ commV M₁ ⊓ commV M₂ := ⟨hst u hu, hg₁ u hu⟩
    rw [hS.inf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact g.injective (by rw [h1, map_one])
  have h4 := hS.card_U₁
  rw [hbot, Subgroup.card_bot] at h4
  omega

omit [Finite V] in
theorem card_fixV_swap (hS : OfourStruct O M₁ M₂ s) {g x y : MulAut V}
    (hg₁ : ∀ u ∈ commV M₁, g u ∈ commV M₂) (hg₂ : ∀ u ∈ commV M₂, g u ∈ commV M₁)
    (hy : y ∈ M₂) (hgxy : g * g = x * y) :
    Nat.card (fixV (Subgroup.zpowers g)) = Nat.card ↥(commV M₁ ⊓ fixV (Subgroup.zpowers x)) := by
  set F : Subgroup V := commV M₁ ⊓ fixV (Subgroup.zpowers x) with hF
  let ψ : ↥F →* V := MonoidHom.mk' (fun f => (f : V) * g f) (fun a b => by
    simp only [Subgroup.coe_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h1 : (f : V) * g f = 1 := hf
    have h2 : (f : V) ∈ commV M₂ := by
      have : (f : V) = (g f)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact (commV M₂).inv_mem (hg₁ f f.2.1)
    have : (f : V) ∈ commV M₁ ⊓ commV M₂ := ⟨f.2.1, h2⟩
    rw [hS.inf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : ψ.range = fixV (Subgroup.zpowers g) := by
    ext w
    constructor
    · rintro ⟨f, rfl⟩
      obtain ⟨hf1, hf2⟩ := f.2
      have hfx : x f = f := mem_fixV_zpowers_iff.mp hf2
      have hyf : y f = f := hS.L₂_fix₁ hy hf1
      have hgg : g (g f) = f := by
        have := congrArg (fun φ : MulAut V => φ (f : V)) hgxy
        simpa [MulAut.mul_apply, hyf, hfx] using this
      rw [mem_fixV_zpowers_iff]
      show g ((f : V) * g f) = (f : V) * g f
      rw [map_mul, hgg, mul_comm]
    · intro hw
      rw [mem_fixV_zpowers_iff] at hw
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hS.exists_decomp_W w
      rw [map_mul] at hw
      have hc : g u₁ * g u₂ = g u₂ * g u₁ := mul_comm _ _
      obtain ⟨e1, e2⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot hS.inf hu₁ (hg₂ u₂ hu₂) hu₂ (hg₁ u₁ hu₁)
        (hw.symm.trans hc)
      have hyu : y u₁ = u₁ := hS.L₂_fix₁ hy hu₁
      have hxu : x u₁ = u₁ := by
        have h1 := congrArg (fun φ : MulAut V => φ u₁) hgxy
        simp only [MulAut.mul_apply, hyu] at h1
        rw [← h1, ← e2, ← e1]
      have hmem : u₁ ∈ F := ⟨hu₁, mem_fixV_zpowers_iff.mpr hxu⟩
      exact ⟨⟨u₁, hmem⟩, by
        show u₁ * g u₁ = u₁ * u₂
        rw [← e2]⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem even_rk_swap_iff (hS : OfourStruct O M₁ M₂ s) (hexp : ∀ w : V, w ^ 2 = 1) (hrk : rk V = 4)
    {g x y : MulAut V} (hg₁ : ∀ u ∈ commV M₁, g u ∈ commV M₂)
    (hg₂ : ∀ u ∈ commV M₂, g u ∈ commV M₁) (hx : x ∈ M₁) (hy : y ∈ M₂) (hgxy : g * g = x * y) :
    Even (rk (commV (Subgroup.zpowers g))) ↔ ¬ (x ^ 2 = 1 ∧ x ≠ 1) := by
  have hsum := rk_commV_add_rk_fixV g
  have hr : rk (fixV (Subgroup.zpowers g)) = rk ↥(commV M₁ ⊓ fixV (Subgroup.zpowers x)) := by
    unfold rk
    rw [card_fixV_swap hS hg₁ hg₂ hy hgxy]
  obtain ⟨h1, h1'⟩ := S152O.rk_fix_class hexp hS.nat₁ (fun l hl u hu => commV_stable M₁ hl hu) hx
  rw [hr, hrk] at hsum
  rw [Nat.even_iff, h1]
  omega

theorem even_rk_mul_swap_iff (hS : OfourStruct O M₁ M₂ s) (hexp : ∀ w : V, w ^ 2 = 1)
    (hrk : rk V = 4) {t : MulAut V} (htO : t ∈ O) (htN : t ∉ M₁ ⊔ M₂) (ht2 : t * t = 1)
    {m₁ m₂ : MulAut V} (hm₁ : m₁ ∈ M₁) (hm₂ : m₂ ∈ M₂) :
    Even (rk (commV (Subgroup.zpowers (m₁ * m₂ * t)))) ↔
      ((m₁ ^ 2 = 1 ∧ m₁ ≠ 1) ↔ (m₂ ^ 2 = 1 ∧ m₂ ≠ 1)) := by
  obtain ⟨hc₁, hc₂⟩ := conjAut_eq_of_swap hS htO htN
  have hm₁' : t * m₁ * t⁻¹ ∈ M₂ := by
    have : t * m₁ * t⁻¹ ∈ B1.conjAut t M₁ := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hm₁
    rwa [hc₁] at this
  have hm₂' : t * m₂ * t⁻¹ ∈ M₁ := by
    have : t * m₂ * t⁻¹ ∈ B1.conjAut t M₂ := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hm₂
    rwa [hc₂] at this
  have hmN : m₁ * m₂ ∈ M₁ ⊔ M₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hm₁) (Subgroup.mem_sup_right hm₂)
  have hgO : m₁ * m₂ * t ∈ O := O.mul_mem (O.mul_mem (hS.L₁_le hm₁) (hS.L₂_le hm₂)) htO
  have hgN : m₁ * m₂ * t ∉ M₁ ⊔ M₂ := by
    intro h
    apply htN
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) h
    rwa [inv_mul_cancel_left] at this
  have hcomm := hS.comm (t * m₂ * t⁻¹) hm₂' (m₂ * (t * m₁ * t⁻¹)) (M₂.mul_mem hm₂ hm₁')
  have e1 : (m₁ * m₂ * t) * (m₁ * m₂ * t) =
      m₁ * (m₂ * (t * m₁ * t⁻¹)) * (t * m₂ * t⁻¹) * (t * t) := by group
  have e2 : m₁ * (m₂ * (t * m₁ * t⁻¹)) * (t * m₂ * t⁻¹) =
      (m₁ * (t * m₂ * t⁻¹)) * (m₂ * (t * m₁ * t⁻¹)) := by
    calc m₁ * (m₂ * (t * m₁ * t⁻¹)) * (t * m₂ * t⁻¹)
        = m₁ * ((m₂ * (t * m₁ * t⁻¹)) * (t * m₂ * t⁻¹)) := mul_assoc _ _ _
      _ = m₁ * ((t * m₂ * t⁻¹) * (m₂ * (t * m₁ * t⁻¹))) := by rw [← hcomm]
      _ = (m₁ * (t * m₂ * t⁻¹)) * (m₂ * (t * m₁ * t⁻¹)) := (mul_assoc _ _ _).symm
  rw [ht2, mul_one] at e1
  have hswap := apply_mem_of_swap hS hgO hgN
  rw [even_rk_swap_iff hS hexp hrk hswap.1 hswap.2 (M₁.mul_mem hm₁ hm₂') (M₂.mul_mem hm₂ hm₁')
    (e1.trans e2), inv_mul_iff hS.nat₁ hm₁ hm₂', conj_inv_iff, not_not]

theorem tau_decomp (hS : OfourStruct O M₁ M₂ s) (hexp : ∀ w : V, w ^ 2 = 1) (hrk : rk V = 4)
    {τ : MulAut V} (hτN : τ ∈ M₁ ⊔ M₂) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hnt : rk (commV (Subgroup.zpowers τ)) ≠ 1) :
    ∃ n₁ ∈ M₁, ∃ n₂ ∈ M₂, τ = n₁ * n₂ ∧ (n₁ ^ 2 = 1 ∧ n₁ ≠ 1) ∧ (n₂ ^ 2 = 1 ∧ n₂ ≠ 1) := by
  obtain ⟨n₁, hn₁, n₂, hn₂, hτ⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hτN
  replace hτ := hτ.symm
  have hsq : n₁ ^ 2 = 1 ∧ n₂ ^ 2 = 1 := by
    rw [hτ] at hτ2
    exact (pow_eq_one_iff_of_mul hS hn₁ hn₂ 2).mp hτ2
  have hst₁ : ∀ l ∈ M₁, ∀ u ∈ commV M₁, l u ∈ commV M₁ := fun l hl u hu => commV_stable M₁ hl hu
  have hst₂ : ∀ l ∈ M₂, ∀ u ∈ commV M₂, l u ∈ commV M₂ := fun l hl u hu => commV_stable M₂ hl hu
  have hsum := rk_commV_add_rk_fixV (n₁ * n₂)
  rw [S152O.rk_fixV_mul hS hn₁ hn₂, hrk] at hsum
  obtain ⟨a1, a2, -⟩ := S152O.rk_fix_natural hexp hS.nat₁ hst₁ hn₁
  obtain ⟨b1, b2, -⟩ := S152O.rk_fix_natural hexp hS.nat₂ hst₂ hn₂
  refine ⟨n₁, hn₁, n₂, hn₂, hτ, ⟨hsq.1, fun h1 => ?_⟩, ⟨hsq.2, fun h2 => ?_⟩⟩
  · have hn₂1 : n₂ ≠ 1 := fun h2 => hτ1 (by rw [hτ, h1, h2, mul_one])
    have c1 := a1 h1
    have c2 := b2 hsq.2 hn₂1
    apply hnt
    rw [hτ]
    omega
  · have hn₁1 : n₁ ≠ 1 := fun h1 => hτ1 (by rw [hτ, h1, h2, mul_one])
    have c1 := a2 hsq.1 hn₁1
    have c2 := b1 h2
    apply hnt
    rw [hτ]
    omega

theorem omega_iff (hS : OfourStruct O M₁ M₂ s) (hexp : ∀ w : V, w ^ 2 = 1) (hrk : rk V = 4)
    {X P : Subgroup (MulAut V)} {t τ n₁ n₂ : MulAut V}
    (hXO : X ≤ O) (hP : ∀ x, x ∈ P ↔ x ∈ O ∧ x ^ 3 = 1) (hPX : P ≤ X)
    (htX : t ∈ X) (htN : t ∉ M₁ ⊔ M₂) (ht2 : t * t = 1)
    (hτX : τ ∈ X) (hτ : τ = n₁ * n₂) (hn₁ : n₁ ∈ M₁) (hn₂ : n₂ ∈ M₂)
    (hi₁ : n₁ ^ 2 = 1 ∧ n₁ ≠ 1) (hi₂ : n₂ ^ 2 = 1 ∧ n₂ ≠ 1)
    (hKN : ∀ g ∈ X, g ∈ M₁ ⊔ M₂ → g ∈ P ∨ g * τ⁻¹ ∈ P) :
    ∀ g, g ∈ X ↔ g ∈ O ∧ Even (rk (commV (Subgroup.zpowers g))) := by
  have htO : t ∈ O := hXO htX
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinv : ∀ n : MulAut V, (n ^ 2 = 1 ∧ n ≠ 1) → ((n⁻¹) ^ 2 = 1 ∧ n⁻¹ ≠ 1) := by
    rintro n ⟨h2, h1⟩
    exact ⟨by rw [inv_pow, h2, inv_one], fun h => h1 (inv_eq_one.mp h)⟩
  have hτinv : τ⁻¹ = n₁⁻¹ * n₂⁻¹ := by
    have hc : Commute n₁ n₂ := hS.comm n₁ hn₁ n₂ hn₂
    rw [hτ, mul_inv_rev]
    exact hc.inv_inv.eq.symm
  have hgτ : ∀ m₁ ∈ M₁, ∀ m₂ ∈ M₂, (m₁ * m₂) * τ⁻¹ = (m₁ * n₁⁻¹) * (m₂ * n₂⁻¹) := by
    intro m₁ hm₁ m₂ hm₂
    have hc := hS.comm n₁⁻¹ (M₁.inv_mem hn₁) m₂ hm₂
    rw [hτinv]
    calc m₁ * m₂ * (n₁⁻¹ * n₂⁻¹) = m₁ * (m₂ * n₁⁻¹) * n₂⁻¹ := by group
      _ = m₁ * (n₁⁻¹ * m₂) * n₂⁻¹ := by rw [hc]
      _ = m₁ * n₁⁻¹ * (m₂ * n₂⁻¹) := by group
  have hXN : ∀ m₁ ∈ M₁, ∀ m₂ ∈ M₂, m₁ * m₂ ∈ X →
      ((m₁ ^ 2 = 1 ∧ m₁ ≠ 1) ↔ (m₂ ^ 2 = 1 ∧ m₂ ≠ 1)) := by
    intro m₁ hm₁ m₂ hm₂ hX
    have hN : m₁ * m₂ ∈ M₁ ⊔ M₂ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hm₁) (Subgroup.mem_sup_right hm₂)
    rcases hKN _ hX hN with hP' | hP'
    · obtain ⟨c₁, c₂⟩ := (pow_eq_one_iff_of_mul hS hm₁ hm₂ 3).mp ((hP _).mp hP').2
      have d₁ := (cube_iff_not_inv hS.nat₁ hm₁).mp c₁
      have d₂ := (cube_iff_not_inv hS.nat₂ hm₂).mp c₂
      exact ⟨fun h => absurd h d₁, fun h => absurd h d₂⟩
    · rw [hgτ m₁ hm₁ m₂ hm₂] at hP'
      have hm₁' : m₁ * n₁⁻¹ ∈ M₁ := M₁.mul_mem hm₁ (M₁.inv_mem hn₁)
      have hm₂' : m₂ * n₂⁻¹ ∈ M₂ := M₂.mul_mem hm₂ (M₂.inv_mem hn₂)
      obtain ⟨c₁, c₂⟩ := (pow_eq_one_iff_of_mul hS hm₁' hm₂' 3).mp ((hP _).mp hP').2
      have d₁ := (cube_iff_not_inv hS.nat₁ hm₁').mp c₁
      have d₂ := (cube_iff_not_inv hS.nat₂ hm₂').mp c₂
      have iff₁ := inv_mul_iff hS.nat₁ hm₁ (M₁.inv_mem hn₁)
      have iff₂ := inv_mul_iff hS.nat₂ hm₂ (M₂.inv_mem hn₂)
      have e₁ : m₁ ^ 2 = 1 ∧ m₁ ≠ 1 := by
        by_contra hne
        exact d₁ (iff₁.mpr fun hh => hne (hh.mpr (hinv n₁ hi₁)))
      have e₂ : m₂ ^ 2 = 1 ∧ m₂ ≠ 1 := by
        by_contra hne
        exact d₂ (iff₂.mpr fun hh => hne (hh.mpr (hinv n₂ hi₂)))
      exact ⟨fun _ => e₂, fun _ => e₁⟩
  have hNX : ∀ m₁ ∈ M₁, ∀ m₂ ∈ M₂,
      ((m₁ ^ 2 = 1 ∧ m₁ ≠ 1) ↔ (m₂ ^ 2 = 1 ∧ m₂ ≠ 1)) → m₁ * m₂ ∈ X := by
    intro m₁ hm₁ m₂ hm₂ hty
    have hmO : m₁ * m₂ ∈ O := O.mul_mem (hS.L₁_le hm₁) (hS.L₂_le hm₂)
    by_cases h₁ : m₁ ^ 2 = 1 ∧ m₁ ≠ 1
    · have h₂ := hty.mp h₁
      have hm₁' : m₁ * n₁⁻¹ ∈ M₁ := M₁.mul_mem hm₁ (M₁.inv_mem hn₁)
      have hm₂' : m₂ * n₂⁻¹ ∈ M₂ := M₂.mul_mem hm₂ (M₂.inv_mem hn₂)
      have c₁ : (m₁ * n₁⁻¹) ^ 3 = 1 := cube_of_not_invol hS.nat₁ hm₁' fun hk =>
        ((inv_mul_iff hS.nat₁ hm₁ (M₁.inv_mem hn₁)).mp hk) ⟨fun _ => hinv n₁ hi₁, fun _ => h₁⟩
      have c₂ : (m₂ * n₂⁻¹) ^ 3 = 1 := cube_of_not_invol hS.nat₂ hm₂' fun hk =>
        ((inv_mul_iff hS.nat₂ hm₂ (M₂.inv_mem hn₂)).mp hk) ⟨fun _ => hinv n₂ hi₂, fun _ => h₂⟩
      have hcube : ((m₁ * m₂) * τ⁻¹) ^ 3 = 1 := by
        rw [hgτ m₁ hm₁ m₂ hm₂]
        exact (pow_eq_one_iff_of_mul hS hm₁' hm₂' 3).mpr ⟨c₁, c₂⟩
      have hmP : (m₁ * m₂) * τ⁻¹ ∈ P :=
        (hP _).mpr ⟨O.mul_mem hmO (O.inv_mem (hXO hτX)), hcube⟩
      have := X.mul_mem (hPX hmP) hτX
      simpa using this
    · have h₂ : ¬ (m₂ ^ 2 = 1 ∧ m₂ ≠ 1) := fun h => h₁ (hty.mpr h)
      have c₁ := (cube_iff_not_inv hS.nat₁ hm₁).mpr h₁
      have c₂ := (cube_iff_not_inv hS.nat₂ hm₂).mpr h₂
      exact hPX ((hP _).mpr ⟨hmO, (pow_eq_one_iff_of_mul hS hm₁ hm₂ 3).mpr ⟨c₁, c₂⟩⟩)
  have hdec : ∀ g ∈ O, g ∈ M₁ ⊔ M₂ ∨ ∃ m₁ ∈ M₁, ∃ m₂ ∈ M₂, g = m₁ * m₂ * t := by
    intro g hg
    rcases hS.coset hg htO htN with hN | hN
    · exact Or.inl hN
    · right
      obtain ⟨m₁, hm₁, m₂, hm₂, hmm⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hN
      refine ⟨m₁, hm₁, m₂, hm₂, ?_⟩
      rw [hmm]
      exact (inv_mul_cancel_right g t).symm
  intro g
  constructor
  · intro hg
    refine ⟨hXO hg, ?_⟩
    rcases hdec g (hXO hg) with hN | ⟨m₁, hm₁, m₂, hm₂, hgeq⟩
    · obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hN
      exact (S152O.even_rk_mul_iff hS hexp hrk hm₁ hm₂).mpr (hXN m₁ hm₁ m₂ hm₂ hg)
    · have hX' : m₁ * m₂ ∈ X := by
        have := X.mul_mem hg htX
        rwa [hgeq, mul_assoc, ht2, mul_one] at this
      rw [hgeq]
      exact (even_rk_mul_swap_iff hS hexp hrk htO htN ht2 hm₁ hm₂).mpr (hXN m₁ hm₁ m₂ hm₂ hX')
  · rintro ⟨hgO, hEven⟩
    rcases hdec g hgO with hN | ⟨m₁, hm₁, m₂, hm₂, hgeq⟩
    · obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hN
      exact hNX m₁ hm₁ m₂ hm₂ ((S152O.even_rk_mul_iff hS hexp hrk hm₁ hm₂).mp hEven)
    · rw [hgeq] at hEven ⊢
      exact X.mul_mem (hNX m₁ hm₁ m₂ hm₂
        ((even_rk_mul_swap_iff hS hexp hrk htO htN ht2 hm₁ hm₂).mp hEven)) htX

end Omega

section Concrete

variable {X : Subgroup (MulAut V)} {r : ℚ}

omit [Finite V] in
theorem commV_apply_of_conjBy {g : MulAut V} {Y Z : Subgroup (MulAut V)} (h : conjBy g Y = Z)
    {u : V} (hu : u ∈ commV Y) : g u ∈ commV Z := by
  have h1 : g u ∈ (commV Y).map g.toMonoidHom := ⟨u, hu, rfl⟩
  rwa [← commV_conjBy, h] at h1

theorem perm_pair {Pi : Fin 2 → Subgroup (MulAut V)} (hr : Set.range Pi = Pfam X)
    (hinj : Function.Injective Pi) {g : MulAut V} (hg : g ∈ X) :
    (conjBy g (Pi 0) = Pi 0 ∧ conjBy g (Pi 1) = Pi 1) ∨
      (conjBy g (Pi 0) = Pi 1 ∧ conjBy g (Pi 1) = Pi 0) := by
  have hPi : ∀ i, Pi i ∈ Pfam X := fun i => hr ▸ ⟨i, rfl⟩
  have hcase : ∀ i, ∃ j, conjBy g (Pi i) = Pi j := fun i => by
    have hmem : conjBy g (Pi i) ∈ Set.range Pi := hr ▸ Pfam_conj hg (hPi i)
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  obtain ⟨j₀, h₀⟩ := hcase 0
  obtain ⟨j₁, h₁⟩ := hcase 1
  fin_cases j₀ <;> fin_cases j₁
  · exact absurd (hinj (conjBy_injective g (h₀.trans h₁.symm))) (by decide)
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact absurd (hinj (conjBy_injective g (h₀.trans h₁.symm))) (by decide)

theorem isOmegaFourPlus_of_case7i (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) {Pi : Fin 2 → Subgroup (MulAut V)} (d : PDecomp X Pi)
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hXeq : X = pCoreOf 3 X ⊔ A)
    (hc : Case7i X A Pi) (hr : r = 3 / 2) (hW : fixV (pCoreOf 3 X) = ⊥) : IsOmegaFourPlus X := by
  classical
  obtain ⟨⟨t, u, hk, ht0, ht1, hu0, hu1⟩, -⟩ := hc
  have hrg : Set.range Pi = Pfam X := d.range_eq hV (hcomm_of_hall hV h hall)
  have hAX : A ≤ X := QhatStar_le hA
  have hinf : commV (Pi 0) ⊓ commV (Pi 1) = ⊥ :=
    disjoint_iff.mp (iSupIndep_fin_two_iff.mp d.vindep)
  have hsup : commV (Pi 0) ⊔ commV (Pi 1) = ⊤ := by
    have := iSup_commV_eq_top hV d hW
    rwa [iSup_fin_two_eq] at this
  have hcard : ∀ i, Nat.card ↥(commV (Pi i)) = 4 := fun i => by
    rw [card_eq_two_pow hV, d.rk_eq i]
    norm_num
  have hU : ∀ i, ∀ w : ↥(commV (Pi i)), w * w = 1 := fun i w => by
    have h1 := hV (w : V)
    rw [pow_two] at h1
    exact Subtype.ext h1
  obtain ⟨φ₁⟩ := exists_mulEquiv_F2sq (hU 0) (hcard 0)
  obtain ⟨φ₂⟩ := exists_mulEquiv_F2sq (hU 1) (hcard 1)
  obtain ⟨M₁, M₂, s, hS, hM₁, hM₂⟩ := S153.exists_ofourStruct hinf hsup φ₁ φ₂
  have hrk4 : rk V = 4 := by
    have h16 := S1417.card_eq_sixteen hinf hsup φ₁ φ₂
    have h2 := card_eq_two_pow_rk hV
    rw [h16] at h2
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ rk V = 2 ^ 4 by omega)
  have hXO : X ≤ orthogonalGroupOf (S1417.quadOf hinf hsup φ₁ φ₂) := by
    intro g hg v
    rcases perm_pair hrg d.injective hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact S1417.quadOf_apply_of_stab hinf hsup φ₁ φ₂ (fun w hw => commV_apply_of_conjBy h0 hw)
        (fun w hw => commV_apply_of_conjBy h1 hw) v
    · exact S1417.quadOf_apply_of_swap hinf hsup φ₁ φ₂ (fun w hw => commV_apply_of_conjBy h0 hw)
        (fun w hw => commV_apply_of_conjBy h1 hw) v
  have htX : t ∈ X := hAX hk.ha
  have huX : u ∈ X := hAX hk.hb
  have ht₁ : ∀ w ∈ commV M₁, t w ∈ commV M₂ := fun w hw => by
    rw [hM₂]
    rw [hM₁] at hw
    exact commV_apply_of_conjBy ht0 hw
  have ht₂ : ∀ w ∈ commV M₂, t w ∈ commV M₁ := fun w hw => by
    rw [hM₁]
    rw [hM₂] at hw
    exact commV_apply_of_conjBy ht1 hw
  have hu₁ : ∀ w ∈ commV M₁, u w ∈ commV M₂ := fun w hw => by
    rw [hM₂]
    rw [hM₁] at hw
    exact commV_apply_of_conjBy hu0 hw
  have htN : t ∉ M₁ ⊔ M₂ := not_mem_sup_of_swap hS (hXO htX) ht₁
  have huN : u ∉ M₁ ⊔ M₂ := not_mem_sup_of_swap hS (hXO huX) hu₁
  have ht2 : t * t = 1 := hk.mul_self_a
  have hτX : t * u ∈ X := X.mul_mem htX huX
  have hτst : ∀ w ∈ commV M₁, (t * u) w ∈ commV M₁ := fun w hw => ht₂ _ (hu₁ w hw)
  have hτN : t * u ∈ M₁ ⊔ M₂ := (hS.mem_sup_iff (hXO hτX)).mpr hτst
  have hτ2 : (t * u) ^ 2 = 1 := by
    have : t * u * (t * u) = 1 := by
      calc t * u * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [← hk.comm]
        _ = (t * t) * (u * u) := by group
        _ = 1 := by rw [hk.mul_self_a, hk.mul_self_b, mul_one]
    rw [pow_two]
    exact this
  have hτ1 : t * u ≠ 1 := by
    intro h1
    apply hk.hab
    calc t = t * (u * u) := by rw [hk.mul_self_b, mul_one]
      _ = (t * u) * u := by rw [mul_assoc]
      _ = u := by rw [h1, one_mul]
  have hτrk : rk (commV (Subgroup.zpowers (t * u))) ≠ 1 := fun hrk1 =>
    not_transvection hV h.qhat (by rw [hr]; norm_num) hτX hτ1 hτ2 hrk1
  obtain ⟨n₁, hn₁, n₂, hn₂, hτ, hi₁, hi₂⟩ := tau_decomp hS hV hrk4 hτN hτ2 hτ1 hτrk
  have hPN : ∀ p ∈ pCoreOf 3 X, p ∈ M₁ ⊔ M₂ := fun p hp =>
    hS.odd_mem_sup (hXO (pCoreOf_le 3 X hp))
      (S152O.odd_of_pow_three (pCoreOf_pow_three hV (hall A hA) p hp))
  have hP : ∀ x, x ∈ pCoreOf 3 X ↔
      x ∈ orthogonalGroupOf (S1417.quadOf hinf hsup φ₁ φ₂) ∧ x ^ 3 = 1 := by
    obtain ⟨P', hP'⟩ := S152O.exists_cubeSub hS
    have hle : pCoreOf 3 X ≤ P' := fun x hx =>
      (hP' x).mpr ⟨hXO (pCoreOf_le 3 X hx), pCoreOf_pow_three hV (hall A hA) x hx⟩
    have hodd := S152O.odd_card_cubeSub hP'
    have hdvd : Nat.card P' ∣ 72 := by
      have : Nat.card P' ∣ Nat.card (orthogonalGroupOf (S1417.quadOf hinf hsup φ₁ φ₂)) :=
        Subgroup.card_dvd_of_le fun x hx => ((hP' x).mp hx).1
      rwa [hS.card_X] at this
    have hle9 : Nat.card P' ≤ 9 := by
      have hc2 : Nat.Coprime (Nat.card P') 2 := Nat.coprime_two_right.mpr hodd
      have hc8 : Nat.Coprime (Nat.card P') 8 := by
        simpa using Nat.Coprime.pow_right 3 hc2
      have h9 : Nat.card P' ∣ 9 := hc8.dvd_of_dvd_mul_left (by simpa using hdvd)
      exact Nat.le_of_dvd (by norm_num) h9
    have heq : pCoreOf 3 X = P' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_P]; omega)
    intro x
    rw [heq]
    exact hP' x
  have hKN : ∀ g ∈ X, g ∈ M₁ ⊔ M₂ → g ∈ pCoreOf 3 X ∨ g * (t * u)⁻¹ ∈ pCoreOf 3 X := by
    intro g hg hgN
    have hgXA : g ∈ pCoreOf 3 X ⊔ A := by
      rw [← hXeq]
      exact hg
    have hn : A ≤ Subgroup.normalizer (pCoreOf 3 X : Set (MulAut V)) := fun a ha =>
      le_normalizer_pCoreOf 3 X (hAX ha)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hgXA
    obtain ⟨p, hp, a, ha, rfl⟩ := Set.mem_mul.mp hgXA
    rcases hk.mem a ha with h1 | h1 | h1 | h1
    · left
      rw [h1, mul_one]
      exact hp
    · exfalso
      apply htN
      rw [h1] at hgN
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPN p hp)) hgN
      simpa using this
    · exfalso
      apply huN
      rw [h1] at hgN
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPN p hp)) hgN
      simpa using this
    · right
      rw [h1, mul_inv_cancel_right]
      exact hp
  exact ⟨S1417.card_eq_sixteen hinf hsup φ₁ φ₂, S1417.quadOf hinf hsup φ₁ φ₂,
    S1417.quadOf_isQuadratic hinf hsup φ₁ φ₂, S1417.quadOf_nondeg hinf hsup φ₁ φ₂,
    S1417.quadOf_plus hinf hsup φ₁ φ₂,
    omega_iff hS hV hrk4 hXO hP (pCoreOf_le 3 X) htX htN ht2 hτX hτ hn₁ hn₂ hi₁ hi₂ hKN⟩

end Concrete

end CFSG.Quasithin
