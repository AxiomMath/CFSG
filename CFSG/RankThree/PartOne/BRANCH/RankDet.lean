module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.RankThree.PartTwo.Census.LinearRank

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Module CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartTwo.Census

universe u v

variable {K : Type u} [Field K]

theorem card_le_pow_pred_of_det_eq_one {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ (E : Subgroup (V ≃ₗ[K] V)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ r = 1) →
      (∀ g ∈ E, LinearMap.det (g : V →ₗ[K] V) = 1) → Nat.card E ≤ r ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hV E _ hcomm hexp hdet
  classical
  have hr1 : 1 < r := hr.one_lt
  have hcrude := card_le_pow_finrank_sub hr hrK E hcomm hexp
  rw [hV] at hcrude
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simpa using hcrude
    · have hE1 : ∀ g ∈ E, g = 1 := fun g hg =>
        LinearEquiv.ext fun v => LinearMap.congr_fun
          (eq_id_of_det_eq_one_of_finrank_eq_one hV (g : V →ₗ[K] V) (hdet g hg)) v
      have : Nat.card E = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext ((hE1 a a.2).trans (hE1 b b.2).symm)⟩, ⟨1⟩⟩
      simp [this]
  let _ := commGroupOfCommSubgroup E hcomm
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hr hexpE
  by_cases hlarge : r ^ 2 ≤ Nat.card E
  swap
  · have hk2 : k < 2 := by
      rw [hk] at hlarge
      by_contra h
      push Not at h
      exact hlarge (Nat.pow_le_pow_right hr.pos h)
    have hk1 : k ≤ 1 := by omega
    calc Nat.card E = r ^ k := hk
      _ ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos hk1
      _ ≤ r ^ (n - 1) := Nat.pow_le_pow_right hr.pos (by omega)
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hlarge
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
  let ρ : E →* (V ≃ₗ[K] V) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  have hdet2 : ∀ g : E, LinearMap.det (ρU g : fixedSpace x →ₗ[K] fixedSpace x) *
      LinearMap.det (ρW g : commSpace x →ₗ[K] commSpace x) = 1 := by
    intro g
    have h := det_eq_mul_of_isCompl hc (g : V ≃ₗ[K] V).toLinearMap (hUinv g) (hWinv g)
    rw [hdet g g.2] at h
    exact h.symm
  have hext : ∀ g : E, ρU g = 1 → ρW g = 1 → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : V ≃ₗ[K] V).toLinearMap = LinearMap.id := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h2 ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  set a := finrank K (fixedSpace x) with ha
  set b := finrank K (commSpace x) with hb
  have han : a < n := by omega
  set N : Subgroup E := ρW.ker with hN
  have hinjN : Function.Injective (ρU.comp N.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgW : ρW (g : E) = 1 := g.2
    exact Subgroup.mem_bot.2 (Subtype.ext (hext g hg hgW))
  set EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := (ρU.comp N.subtype).range with hEU
  have : Finite EU := Finite.of_surjective _ (ρU.comp N.subtype).rangeRestrict_surjective
  have hEUcard : Nat.card EU = Nat.card N :=
    (Nat.card_congr (MonoidHom.ofInjective hinjN).toEquiv).symm
  have hEUcomm : ∀ g ∈ EU, ∀ h ∈ EU, g * h = h * g := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subtype.ext (hcomm g g.1.2 h h.1.2)))
  have hEUexp : ∀ g ∈ EU, g ^ r = 1 := by
    rintro _ ⟨g, rfl⟩
    rw [← map_pow]
    have : (g : N) ^ r = 1 := Subtype.ext (Subtype.ext (hexp g g.1.2))
    rw [this, map_one]
  have hEUdet : ∀ g ∈ EU, LinearMap.det (g : fixedSpace x →ₗ[K] fixedSpace x) = 1 := by
    rintro _ ⟨g, rfl⟩
    have hgW : ρW (g : E) = 1 := g.2
    have h := hdet2 g
    rw [hgW] at h
    simpa using h
  have hIH := ih a han (fixedSpace x) rfl EU hEUcomm hEUexp hEUdet
  set RW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range with hRW
  have : Finite RW := Finite.of_surjective _ ρW.rangeRestrict_surjective
  have hRWcomm : ∀ g ∈ RW, ∀ h ∈ RW, g * h = h * g := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hcomm g g.2 h h.2))
  have hRWexp : ∀ g ∈ RW, g ^ r = 1 := by
    rintro _ ⟨g, rfl⟩
    rw [← map_pow, hexpE g, map_one]
  have hRWcard : Nat.card RW ≤ r ^ b := card_le_pow_finrank_sub hr hrK RW hRWcomm hRWexp
  have hmul := Subgroup.card_ker_mul_card_range ρW
  calc Nat.card E = Nat.card ρW.ker * Nat.card ρW.range := hmul.symm
    _ ≤ r ^ (a - 1) * r ^ b := by
      refine Nat.mul_le_mul ?_ hRWcard
      rw [← hEUcard]
      exact hIH
    _ = r ^ (n - 1) := by
      rw [← pow_add]
      congr 1
      omega

theorem card_le_pow_pred_of_det_gl {ι : Type v} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (hr : r.Prime) (hrK : (r : K) ≠ 0) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1)
    (hdet : ∀ g ∈ E, (g : Matrix ι ι K).det = 1) : Nat.card E ≤ r ^ (Fintype.card ι - 1) := by
  have : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_pow_pred_of_det_eq_one hr hrK (Fintype.card ι) (ι → K)
    (Module.finrank_fintype_fun_eq_card K) (E.map (glAut ι K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp) (by
      rintro _ ⟨a, ha, rfl⟩
      rw [det_glAut]
      exact hdet a ha)
  rwa [card_map_glAut] at h

end CFSG.RankThree.PartOne.BRANCH
