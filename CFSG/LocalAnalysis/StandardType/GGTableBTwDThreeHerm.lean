module

public import CFSG.RankThree.PartOne.S11d.FormMaschke
public import Mathlib

public section

namespace CFSG.StandardType.TwDThree

open Module CFSG.RankThree.PartOne.LIT

universe u v

variable {K : Type u} [Field K]

theorem eq_one_of_finrank_eq_one {σ : K →+* K} {r : ℕ} (hr : Odd r)
    (hσ : ∀ c : K, c ^ r = 1 → σ c = c) {X : Type v} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (hX : finrank K X = 1) (B : X →ₗ[K] X →ₛₗ[σ] K)
    (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    {g : X ≃ₗ[K] X} (hg : g ^ r = 1) (hpres : ∀ u w, B (g u) (g w) = B u w) : g = 1 := by
  have hpos : 0 < finrank K X := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hall := (finrank_eq_one_iff_of_nonzero' v hv).mp hX
  obtain ⟨c, hc⟩ := hall (g v)
  have hk : ∀ k : ℕ, (g ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, ← hc, smul_smul, ← pow_succ]
  have hcr : c ^ r = 1 := by
    have h1 : v = c ^ r • v := by
      rw [← hk r, hg]
      rfl
    have h2 : (c ^ r - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  have hvv : B v v ≠ 0 := by
    intro h0
    apply hv
    apply hB
    intro w
    obtain ⟨d, rfl⟩ := hall w
    rw [LinearMap.map_smulₛₗ, h0, smul_zero]
  have hcc : c * c = 1 := by
    have h1 := hpres v v
    rw [← hc] at h1
    rw [LinearMap.map_smul B c v, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hσ c hcr, smul_smul,
      smul_eq_mul] at h1
    have h2 : (c * c - 1) * B v v = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvv
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hr
    rw [hm, pow_succ, pow_mul, sq, hcc, one_pow, one_mul] at hcr
    exact hcr
  apply LinearEquiv.ext
  intro w
  obtain ⟨d, rfl⟩ := hall w
  rw [LinearEquiv.map_smul, ← hc, hc1, one_smul]
  rfl

theorem card_le_pow_half_of_sesq {σ : K →+* K} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrK : (r : K) ≠ 0) (hσ : ∀ c : K, c ^ r = 1 → σ c = c) :
    ∀ (n : ℕ) (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (B : X →ₗ[K] X →ₛₗ[σ] K), (∀ v, (∀ w, B v w = 0) → v = 0) →
      ∀ (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ r = 1) →
      (∀ g ∈ E, ∀ u w, B (g u) (g w) = B u w) → Nat.card E ≤ r ^ (n / 2) := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn B hB E _ hcomm hexp hpres
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card E = r ^ k := by
    have : Fact r.Prime := ⟨hr⟩
    have hE : IsPGroup r E := fun a => ⟨1, by rw [pow_one]; exact hexpE a⟩
    exact IsPGroup.iff_card.mp hE
  have hr2' : 2 ≤ r := hr.two_le
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    have htriv : ∀ g ∈ E, g = 1 := by
      intro g hg
      interval_cases n
      · have : Subsingleton X := finrank_zero_iff.mp hn
        exact LinearEquiv.ext fun v => Subsingleton.elim _ _
      · exact eq_one_of_finrank_eq_one hodd hσ hn B hB (hexp g hg) (hpres g hg)
    have hsub : Subsingleton E :=
      ⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩
    have h1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [h1]
    exact Nat.one_le_pow _ _ hr.pos
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : Nat.card E ≤ r := by
        rw [hk]
        calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos (by omega)
          _ = r := pow_one r
      calc Nat.card E ≤ r := this
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)
    · have hbig : r ^ 2 ≤ Nat.card E := by
        rw [hk]; exact Nat.pow_le_pow_right hr.pos hk2
      obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hbig
      have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
      have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
      have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
        fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
      have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
        fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      have hUpos : 0 < finrank K (fixedSpace x) := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
      have hWpos : 0 < finrank K (commSpace x) := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        by_contra hcon
        have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
        apply hx1
        apply LinearEquiv.ext
        intro y
        have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
        have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
        simpa [sub_eq_zero] using h2
      have hUW : ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, B u w = 0 := fun u hu w hw =>
        (inf_fixedSpace_orthogonal B (hpres x hxE) hu hw).1
      have hWU : ∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, B w u = 0 := fun w hw u hu =>
        (inf_fixedSpace_orthogonal B (hpres x hxE) hu hw).2
      have hsplit : ∀ y : X, ∃ u ∈ fixedSpace x, ∃ w ∈ commSpace x, u + w = y := by
        intro y
        have : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; trivial
        exact Submodule.mem_sup.mp this
      let ρ : E →* (X ≃ₗ[K] X) := E.subtype
      let ρU := restrictAction ρ (fixedSpace x) hUinv
      let ρW := restrictAction ρ (commSpace x) hWinv
      let BU : fixedSpace x →ₗ[K] fixedSpace x →ₛₗ[σ] K :=
        B.domRestrict₁₂ (fixedSpace x) (fixedSpace x)
      let BW : commSpace x →ₗ[K] commSpace x →ₛₗ[σ] K :=
        B.domRestrict₁₂ (commSpace x) (commSpace x)
      have hBU : ∀ u : fixedSpace x, (∀ u' : fixedSpace x, BU u u' = 0) → u = 0 := by
        intro u hu
        apply Subtype.ext
        apply hB
        intro y
        obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
        rw [map_add, hUW u u.2 w₁ hw₁, add_zero]
        exact hu ⟨u₁, hu₁⟩
      have hBW : ∀ w : commSpace x, (∀ w' : commSpace x, BW w w' = 0) → w = 0 := by
        intro w hw
        apply Subtype.ext
        apply hB
        intro y
        obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
        rw [map_add, hWU w w.2 u₁ hu₁, zero_add]
        exact hw ⟨w₁, hw₁⟩
      let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
      let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
      have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
      have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
      have hcommU : ∀ g ∈ EU, ∀ h ∈ EU, g * h = h * g := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ρU (Subtype.ext (hcomm a a.2 b b.2))
      have hcommW : ∀ g ∈ EW, ∀ h ∈ EW, g * h = h * g := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ρW (Subtype.ext (hcomm a a.2 b b.2))
      have hexpU : ∀ g ∈ EU, g ^ r = 1 := by
        rintro _ ⟨a, rfl⟩
        rw [← map_pow, hexpE a, map_one]
      have hexpW : ∀ g ∈ EW, g ^ r = 1 := by
        rintro _ ⟨a, rfl⟩
        rw [← map_pow, hexpE a, map_one]
      have hpresU : ∀ g ∈ EU, ∀ u w, BU (g u) (g w) = BU u w := by
        rintro _ ⟨a, rfl⟩ u w
        exact hpres a a.2 u w
      have hpresW : ∀ g ∈ EW, ∀ u w, BW (g u) (g w) = BW u w := by
        rintro _ ⟨a, rfl⟩ u w
        exact hpres a a.2 u w
      have hIU := ih (finrank K (fixedSpace x)) (by omega) (fixedSpace x) rfl BU hBU EU
        hcommU hexpU hpresU
      have hIW := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl BW hBW EW
        hcommW hexpW hpresW
      have hinj : Function.Injective
          (fun g : E => ((⟨ρU g, g, rfl⟩ : EU), (⟨ρW g, g, rfl⟩ : EW))) := by
        intro g h hgh
        simp only [Prod.mk.injEq] at hgh
        obtain ⟨h1, h2⟩ := hgh
        have h1' : ρU g = ρU h := congrArg Subtype.val h1
        have h2' : ρW g = ρW h := congrArg Subtype.val h2
        apply Subtype.ext
        apply LinearEquiv.ext
        intro y
        have hfun : (g : X ≃ₗ[K] X).toLinearMap = (h : X ≃ₗ[K] X).toLinearMap := by
          apply ext_of_isCompl hc
          · intro u hu
            exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
              ((congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)).trans
                (restrictAction_apply ρ (fixedSpace x) hUinv h ⟨u, hu⟩))
          · intro w hw
            exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
              ((congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)).trans
                (restrictAction_apply ρ (commSpace x) hWinv h ⟨w, hw⟩))
        exact LinearMap.congr_fun hfun y
      have hle : Nat.card E ≤ Nat.card EU * Nat.card EW := by
        rw [← Nat.card_prod]
        exact Nat.card_le_card_of_injective _ hinj
      calc Nat.card E ≤ Nat.card EU * Nat.card EW := hle
        _ ≤ r ^ (finrank K (fixedSpace x) / 2) * r ^ (finrank K (commSpace x) / 2) :=
          Nat.mul_le_mul hIU hIW
        _ = r ^ (finrank K (fixedSpace x) / 2 + finrank K (commSpace x) / 2) :=
          (pow_add _ _ _).symm
        _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)

end CFSG.StandardType.TwDThree
