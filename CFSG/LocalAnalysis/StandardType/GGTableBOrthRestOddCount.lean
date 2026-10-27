module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRank
public import CFSG.RankThree.PartTwo.Census.LinearRank
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open Module CFSG.RankThree.PartOne.LIT

universe u v

variable {K : Type u} [Field K]

structure IsoGroup {X : Type v} [AddCommGroup X] [Module K X] (B : X →ₗ[K] X →ₗ[K] K) (p : ℕ)
    (E : Subgroup (X ≃ₗ[K] X)) : Prop where
  sep : ∀ v, (∀ w, B v w = 0) → v = 0
  alt : ∀ v, B v v = 0
  comm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g
  pow : ∀ g ∈ E, g ^ p = 1
  pres : ∀ g ∈ E, ∀ u w, B (g u) (g w) = B u w

section Basic

variable {X : Type v} [AddCommGroup X] [Module K X] {B : X →ₗ[K] X →ₗ[K] K} {p : ℕ}
  {E : Subgroup (X ≃ₗ[K] X)}

theorem IsoGroup.even_finrank [FiniteDimensional K X] (hE : IsoGroup B p E) :
    Even (finrank K X) := by
  have hnd : LinearMap.BilinForm.Nondegenerate (B : LinearMap.BilinForm K X) :=
    ⟨hE.sep, fun y hy => hE.sep y fun w => by rw [alt_skew hE.alt, hy w, neg_zero]⟩
  exact LinearMap.BilinForm.IsAlt.even_finrank (B := (B : LinearMap.BilinForm K X)) hE.alt hnd

noncomputable abbrev resForm (B : X →ₗ[K] X →ₗ[K] K) (S : Submodule K X) :
    S →ₗ[K] S →ₗ[K] K :=
  B.compl₁₂ S.subtype S.subtype

noncomputable abbrev resHom (E : Subgroup (X ≃ₗ[K] X)) (S : Submodule K X)
    (hS : ∀ g ∈ E, ∀ s ∈ S, g s ∈ S) : E →* (S ≃ₗ[K] S) :=
  restrictAction E.subtype S fun g s hs => hS g g.2 s hs

theorem resHom_apply (S : Submodule K X) (hS : ∀ g ∈ E, ∀ s ∈ S, g s ∈ S) (g : E) (s : S) :
    ((resHom E S hS g s : S) : X) = (g : X ≃ₗ[K] X) s := rfl

instance resHom_range_finite [Finite E] (S : Submodule K X) (hS : ∀ g ∈ E, ∀ s ∈ S, g s ∈ S) :
    Finite (resHom E S hS).range :=
  Finite.of_surjective (resHom E S hS).rangeRestrict (resHom E S hS).rangeRestrict_surjective

theorem IsoGroup.res (hE : IsoGroup B p E) (S : Submodule K X)
    (hS : ∀ g ∈ E, ∀ s ∈ S, g s ∈ S) (hsep : ∀ s : S, (∀ s' : S, resForm B S s s' = 0) → s = 0) :
    IsoGroup (resForm B S) p (resHom E S hS).range where
  sep := hsep
  alt s := hE.alt s
  comm := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hE.comm a a.2 b b.2))
  pow := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (hE.pow a a.2), map_one]
  pres := by
    rintro _ ⟨a, rfl⟩ u w
    exact hE.pres a a.2 u w

theorem sep_res_of_isCompl (hsep : ∀ v, (∀ w, B v w = 0) → v = 0) {U W : Submodule K X}
    (hc : IsCompl U W) (horth : ∀ u ∈ U, ∀ w ∈ W, B u w = 0) :
    ∀ u : U, (∀ u' : U, resForm B U u u' = 0) → u = 0 := by
  intro u hu
  apply Subtype.ext
  apply hsep
  intro y
  have hy : y ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, horth u u.2 w₁ hw₁, add_zero]
  exact hu ⟨u₁, hu₁⟩

end Basic

section Split

variable {X : Type v} [AddCommGroup X] [Module K X] {B : X →ₗ[K] X →ₗ[K] K} {p : ℕ}
  {E : Subgroup (X ≃ₗ[K] X)}

theorem pair_injective {U W : Submodule K X} (hc : IsCompl U W)
    (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hW : ∀ g ∈ E, ∀ s ∈ W, g s ∈ W) :
    Function.Injective fun g : E =>
      ((⟨resHom E U hU g, g, rfl⟩ : (resHom E U hU).range),
        (⟨resHom E W hW g, g, rfl⟩ : (resHom E W hW).range)) := by
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have h1' : resHom E U hU g = resHom E U hU h := congrArg Subtype.val h1
  have h2' : resHom E W hW g = resHom E W hW h := congrArg Subtype.val h2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  have hfun : (g : X ≃ₗ[K] X).toLinearMap = (h : X ≃ₗ[K] X).toLinearMap := by
    apply ext_of_isCompl hc
    · intro u hu
      exact congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)
    · intro w hw
      exact congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)
  exact LinearMap.congr_fun hfun y

theorem card_le_mul_res [Finite E] {U W : Submodule K X} (hc : IsCompl U W)
    (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hW : ∀ g ∈ E, ∀ s ∈ W, g s ∈ W) :
    Nat.card E ≤ Nat.card (resHom E U hU).range * Nat.card (resHom E W hW).range := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (pair_injective hc hU hW)

theorem exists_lift [Finite E] {U W : Submodule K X} (hc : IsCompl U W)
    (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hW : ∀ g ∈ E, ∀ s ∈ W, g s ∈ W)
    (hcard : Nat.card (resHom E U hU).range * Nat.card (resHom E W hW).range ≤ Nat.card E)
    {a : U ≃ₗ[K] U} (ha : a ∈ (resHom E U hU).range) {b : W ≃ₗ[K] W}
    (hb : b ∈ (resHom E W hW).range) :
    ∃ g : E, resHom E U hU g = a ∧ resHom E W hW g = b := by
  have hbij := (pair_injective hc hU hW).bijective_of_nat_card_le
    (by rw [Nat.card_prod]; exact hcard)
  obtain ⟨g, hg⟩ := hbij.2 (⟨a, ha⟩, ⟨b, hb⟩)
  simp only [Prod.mk.injEq] at hg
  exact ⟨g, congrArg Subtype.val hg.1, congrArg Subtype.val hg.2⟩

theorem finrank_commSpace_of_res_eq_one {U W : Submodule K X} (hc : IsCompl U W)
    (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hW : ∀ g ∈ E, ∀ s ∈ W, g s ∈ W) {g : E}
    (h1 : resHom E U hU g = 1) :
    finrank K (commSpace (g : X ≃ₗ[K] X)) = finrank K (commSpace (resHom E W hW g)) := by
  have hfixU : ∀ u ∈ U, (g : X ≃ₗ[K] X) u = u := fun u hu =>
    congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩)
  have heq : commSpace (g : X ≃ₗ[K] X) = (commSpace (resHom E W hW g)).map W.subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := mem_commSpace.mp hy
      have hz : z ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      refine ⟨⟨(g : X ≃ₗ[K] X) w - w, Submodule.sub_mem _ (hW g g.2 w hw) hw⟩,
        mem_commSpace.mpr ⟨⟨w, hw⟩, Subtype.ext ?_⟩, ?_⟩
      · rw [Submodule.coe_sub, resHom_apply]
      · simp only [Submodule.subtype_apply]
        rw [map_add, hfixU u hu]
        abel
    · rintro ⟨w', hw', rfl⟩
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hw'
      refine mem_commSpace.mpr ⟨(w : X), ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, resHom_apply]
  rw [heq, Submodule.finrank_map_subtype_eq]

end Split

section Elt

variable {X : Type v} [AddCommGroup X] [Module K X]
  {B : X →ₗ[K] X →ₗ[K] K} {p : ℕ} {E : Subgroup (X ≃ₗ[K] X)}

theorem IsoGroup.fix_inv (hE : IsoGroup B p E) {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    ∀ g ∈ E, ∀ s ∈ fixedSpace x, g s ∈ fixedSpace x :=
  fun g hg _ hs => map_mem_fixedSpace (hE.comm g hg x hx) hs

theorem IsoGroup.comm_inv (hE : IsoGroup B p E) {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    ∀ g ∈ E, ∀ s ∈ commSpace x, g s ∈ commSpace x :=
  fun g hg _ hs => map_mem_commSpace (hE.comm g hg x hx) hs

theorem IsoGroup.isCompl [FiniteDimensional K X] (hE : IsoGroup B p E) (hpK : (p : K) ≠ 0)
    {x : X ≃ₗ[K] X} (hx : x ∈ E) : IsCompl (fixedSpace x) (commSpace x) :=
  isCompl_fixedSpace_commSpace hpK (hE.pow x hx)

theorem IsoGroup.orth (hE : IsoGroup B p E) {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, B u w = 0 := by
  intro u hu w hw
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
  have h1 := hE.pres x hx u y
  rw [mem_fixedSpace.mp hu] at h1
  rw [map_sub, h1, sub_self]

theorem IsoGroup.orth' (hE : IsoGroup B p E) {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    ∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, B w u = 0 := by
  intro w hw u hu
  rw [alt_skew hE.alt w u, hE.orth hx u hu w hw, neg_zero]

theorem IsoGroup.resFix [FiniteDimensional K X] (hE : IsoGroup B p E) (hpK : (p : K) ≠ 0)
    {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    IsoGroup (resForm B (fixedSpace x)) p (resHom E _ (hE.fix_inv hx)).range :=
  hE.res _ _ (sep_res_of_isCompl hE.sep (hE.isCompl hpK hx) (hE.orth hx))

theorem IsoGroup.resComm [FiniteDimensional K X] (hE : IsoGroup B p E) (hpK : (p : K) ≠ 0)
    {x : X ≃ₗ[K] X} (hx : x ∈ E) :
    IsoGroup (resForm B (commSpace x)) p (resHom E _ (hE.comm_inv hx)).range :=
  hE.res _ _ (sep_res_of_isCompl hE.sep (hE.isCompl hpK hx).symm (hE.orth' hx))

theorem commSpace_ne_bot {x : X ≃ₗ[K] X} (hx : x ≠ 1) : commSpace x ≠ ⊥ := by
  intro h
  apply hx
  apply LinearEquiv.ext
  intro y
  have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
  rw [h, Submodule.mem_bot, sub_eq_zero] at hy
  exact hy

theorem IsoGroup.card_le [FiniteDimensional K X] (hE : IsoGroup B p E) [Finite E] (hp : p.Prime)
    (hpK : (p : K) ≠ 0) :
    Nat.card E ≤ p ^ (finrank K X / 2) :=
  card_le_pow_half_of_alt hp hpK _ X rfl B hE.sep hE.alt E hE.comm hE.pow hE.pres

end Elt

section Dichotomy

variable {X : Type v} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  {B : X →ₗ[K] X →ₗ[K] K} {p : ℕ} {E : Subgroup (X ≃ₗ[K] X)}

theorem card_le_or_exists_fix (hE : IsoGroup B p E) [Finite E] (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {Y : Submodule K X} (hY : Y ≠ ⊥) (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) :
    Nat.card E ≤ p ∨ ∃ g ∈ E, g ≠ 1 ∧ ∃ Y' : Submodule K X, Y' ≠ ⊥ ∧ Y' ≤ Y ∧
      (∀ h ∈ E, ∀ y ∈ Y', h y ∈ Y') ∧ ∀ y ∈ Y', g y = y := by
  set EY := (resHom E Y hYinv).range with hEY
  have hEYc : ∀ a ∈ EY, ∀ b ∈ EY, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hE.comm a a.2 b b.2))
  have hEYp : ∀ a ∈ EY, a ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (hE.pow a a.2), map_one]
  by_cases hbig : p ^ 2 ≤ Nat.card EY
  · obtain ⟨xY, ⟨g, rfl⟩, hx1, y, hy0, hxy⟩ :=
      exists_fixed_of_sq_le_card hp hpK EY hEYc hEYp hbig
    have hg1 : (g : X ≃ₗ[K] X) ≠ 1 := by
      intro h
      apply hx1
      rw [show g = 1 from Subtype.ext h, map_one]
    refine Or.inr ⟨g, g.2, hg1, Y ⊓ fixedSpace (g : X ≃ₗ[K] X), ?_, inf_le_left, ?_, ?_⟩
    · intro h
      apply hy0
      have hmem : (y : X) ∈ Y ⊓ fixedSpace (g : X ≃ₗ[K] X) :=
        ⟨y.2, mem_fixedSpace.mpr (congrArg Subtype.val hxy)⟩
      rw [h, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro h hh z hz
      exact ⟨hYinv h hh z hz.1, hE.fix_inv g.2 h hh z hz.2⟩
    · intro z hz
      exact mem_fixedSpace.mp hz.2
  · push Not at hbig
    obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hp
      (fun a : EY => Subtype.ext (hEYp a a.2))
    have hk1 : k ≤ 1 := by
      by_contra h
      have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have hEYle : Nat.card EY ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
        _ = p := pow_one p
    by_cases hEp : Nat.card E ≤ p
    · exact Or.inl hEp
    · right
      push Not at hEp
      have hni : ¬ Function.Injective (resHom E Y hYinv).rangeRestrict := by
        intro hinj
        have : Nat.card E ≤ Nat.card EY := Nat.card_le_card_of_injective _ hinj
        omega
      rw [injective_iff_map_eq_one] at hni
      push Not at hni
      obtain ⟨g, hg, hg1⟩ := hni
      have hgY : resHom E Y hYinv g = 1 := congrArg Subtype.val hg
      exact ⟨g, g.2, fun h => hg1 (Subtype.ext h), Y, hY, le_rfl, hYinv, fun z hz =>
        congrArg Subtype.val (LinearEquiv.congr_fun hgY ⟨z, hz⟩)⟩

end Dichotomy

section Isotropic

theorem fix_of_finrank_eq_one {X : Type v} [AddCommGroup X] [Module K X]
    {E : Subgroup (X ≃ₗ[K] X)} {p : ℕ} (hpow : ∀ g ∈ E, g ^ p = 1)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {Y : Submodule K X} (hY1 : finrank K Y = 1)
    (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) {y : X} (hyY : y ∈ Y) (hy0 : y ≠ 0) :
    ∀ g ∈ E, g y = y := by
  intro g hg
  have hy0' : (⟨y, hyY⟩ : Y) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy0').mp hY1 ⟨g y, hYinv g hg y hyY⟩
  have hc' : g y = c • y := (congrArg Subtype.val hc).symm
  have hpowk : ∀ k : ℕ, (g ^ k) y = c ^ k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, hc', map_smul, ih, smul_smul, pow_succ']
  have h1 := hpowk p
  rw [hpow g hg] at h1
  change y = c ^ p • y at h1
  have h2 : (c ^ p - 1) • y = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  have h3 : c ^ p = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hy0)
  rw [hc', hK1 c h3, one_smul]

theorem card_le_of_isotropic {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) :
    ∀ (n : ℕ) (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (B : X →ₗ[K] X →ₗ[K] K) (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      IsoGroup B p E → ∀ Y : Submodule K X, Y ≠ ⊥ → (∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) →
      (∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0) → Nat.card E ≤ p ^ (n / 2 - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn B E _ hE Y hY hYinv hYiso
  obtain ⟨k, hk⟩ := hE.even_finrank
  rcases card_le_or_exists_fix hE hp hpK hY hYinv with hle | ⟨g, hgE, hg1, Y', hY'0, hY'Y,
    hY'inv, hgY'⟩
  · by_cases hn4 : 4 ≤ n
    · calc Nat.card E ≤ p := hle
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (n / 2 - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    ·
      have hYpos : 1 ≤ finrank K Y := Submodule.one_le_finrank_iff.mpr hY
      have hYle : finrank K Y ≤ n := hn ▸ Submodule.finrank_le Y
      have hY1 : finrank K Y = 1 := by
        by_contra hne
        have hYn : finrank K Y = n := by omega
        have htop : Y = ⊤ := Submodule.eq_top_of_finrank_eq (hYn.trans hn.symm)
        obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
        exact hy0 (hE.sep y fun w => hYiso y hyY w (htop ▸ Submodule.mem_top))
      obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
      have := OrthRestEnd.card_le_pow_half_sub_one hp hpK B hE.sep hE.alt E hE.comm hE.pow
        hE.pres hy0 (fix_of_finrank_eq_one hE.pow hK1 hY1 hYinv hyY hy0)
      rwa [hn] at this
  · have hc := hE.isCompl hpK hgE
    have hEU := hE.resFix hpK hgE
    have hEW := hE.resComm hpK hgE
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a, ha⟩ := hEU.even_finrank
    obtain ⟨b, hb⟩ := hEW.even_finrank
    have hW0 : finrank K (commSpace g) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hg1
    have hY'U : Y' ≤ fixedSpace g := fun y hy => mem_fixedSpace.mpr (hgY' y hy)
    set Y'' : Submodule K (fixedSpace g) := Y'.comap (fixedSpace g).subtype with hY''
    have hY''0 : Y'' ≠ ⊥ := by
      intro h
      obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
      have hmem : (⟨y, hY'U hyY⟩ : fixedSpace g) ∈ Y'' := hyY
      rw [h, Submodule.mem_bot] at hmem
      exact hy0 (congrArg Subtype.val hmem)
    have hU0 : finrank K (fixedSpace g) ≠ 0 := by
      intro h
      apply hY''0
      have : Subsingleton (fixedSpace g) := Module.finrank_zero_iff.mp h
      exact Subsingleton.elim _ _
    have hIU := ih (finrank K (fixedSpace g)) (by omega) (fixedSpace g) rfl _ _ hEU Y'' hY''0
      (by
        rintro _ ⟨h, rfl⟩ z hz
        exact hY'inv h h.2 z hz)
      (fun y hy y' hy' => hYiso y (hY'Y hy) y' (hY'Y hy'))
    have hIW := hEW.card_le hp hpK
    have h3 := card_le_mul_res hc (hE.fix_inv hgE) (hE.comm_inv hgE)
    calc Nat.card E ≤ _ := h3
      _ ≤ p ^ (finrank K (fixedSpace g) / 2 - 1) * p ^ (finrank K (commSpace g) / 2) :=
        Nat.mul_le_mul hIU hIW
      _ = p ^ (finrank K (fixedSpace g) / 2 - 1 + finrank K (commSpace g) / 2) :=
        (pow_add _ _ _).symm
      _ ≤ p ^ (n / 2 - 1) := Nat.pow_le_pow_right hp.pos (by omega)

end Isotropic

section Plane

theorem exists_commSpace_two_of_full {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∀ (n : ℕ) (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → 2 ≤ n → ∀ (B : X →ₗ[K] X →ₗ[K] K) (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      IsoGroup B p E → p ^ (n / 2) ≤ Nat.card E →
      ∃ t ∈ E, t ≠ 1 ∧ finrank K (commSpace t) = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn hn2 B E _ hE hcard
  obtain ⟨k, hk⟩ := hE.even_finrank
  by_cases hbig : p ^ 2 ≤ Nat.card E
  · obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hpK E hE.comm hE.pow hbig
    have hc := hE.isCompl hpK hxE
    have hEU := hE.resFix hpK hxE
    have hEW := hE.resComm hpK hxE
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a, ha⟩ := hEU.even_finrank
    obtain ⟨b, hb⟩ := hEW.even_finrank
    have hU0 : finrank K (fixedSpace x) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      have hv : v ∈ fixedSpace x := mem_fixedSpace.mpr hxv
      rw [h, Submodule.mem_bot] at hv
      exact hv0 hv
    have hW0 : finrank K (commSpace x) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hx1
    have h1 := hEU.card_le hp hpK
    have h2 := hEW.card_le hp hpK
    have h3 := card_le_mul_res hc (hE.fix_inv hxE) (hE.comm_inv hxE)
    have hpa : 0 < p ^ (finrank K (fixedSpace x) / 2) := pow_pos hp.pos _
    have hsplit : p ^ (n / 2) = p ^ (finrank K (fixedSpace x) / 2) *
        p ^ (finrank K (commSpace x) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hW : p ^ (finrank K (commSpace x) / 2) ≤
        Nat.card (resHom E _ (hE.comm_inv hxE)).range := by
      refine Nat.le_of_mul_le_mul_left ?_ hpa
      calc p ^ (finrank K (fixedSpace x) / 2) * p ^ (finrank K (commSpace x) / 2) =
          p ^ (n / 2) := hsplit.symm
        _ ≤ Nat.card E := hcard
        _ ≤ _ := h3
        _ ≤ _ := Nat.mul_le_mul_right _ h1
    have hmul : Nat.card (resHom E _ (hE.fix_inv hxE)).range *
        Nat.card (resHom E _ (hE.comm_inv hxE)).range ≤ Nat.card E := by
      calc _ ≤ p ^ (finrank K (fixedSpace x) / 2) * p ^ (finrank K (commSpace x) / 2) :=
            Nat.mul_le_mul h1 h2
        _ = p ^ (n / 2) := hsplit.symm
        _ ≤ Nat.card E := hcard
    obtain ⟨tW, htW, htW1, htW2⟩ := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl
      (by omega) _ _ hEW hW
    obtain ⟨g, hgU, hgW⟩ := exists_lift hc _ _ hmul (one_mem _) htW
    refine ⟨g, g.2, fun h => htW1 ?_, ?_⟩
    · rw [← hgW, show g = 1 from Subtype.ext h, map_one]
    · rw [finrank_commSpace_of_res_eq_one hc _ (hE.comm_inv hxE) hgU, hgW, htW2]
  · push Not at hbig
    have hn2' : n = 2 := by
      by_contra h
      have : p ^ 2 ≤ p ^ (n / 2) := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    subst hn2'
    have hE1 : 1 < Nat.card E := lt_of_lt_of_le (by simpa using hp.one_lt) hcard
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hE1
    obtain ⟨t, ht1⟩ := exists_ne (1 : E)
    have ht1' : (t : X ≃ₗ[K] X) ≠ 1 := fun h => ht1 (Subtype.ext h)
    refine ⟨t, t.2, ht1', ?_⟩
    have hEW := hE.resComm hpK t.2
    obtain ⟨b, hb⟩ := hEW.even_finrank
    have hW0 : finrank K (commSpace (t : X ≃ₗ[K] X)) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot ht1'
    have hle : finrank K (commSpace (t : X ≃ₗ[K] X)) ≤ 2 := hn ▸ Submodule.finrank_le _
    omega

theorem exists_commSpace_two_of_isotropic {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {X : Type v} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (hn : 6 ≤ finrank K X) {B : X →ₗ[K] X →ₗ[K] K}
    {E : Subgroup (X ≃ₗ[K] X)} [Finite E] (hE : IsoGroup B p E) {Y : Submodule K X}
    (hY : Y ≠ ⊥) (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0)
    (hcard : p ^ (finrank K X / 2 - 1) ≤ Nat.card E) :
    ∃ t ∈ E, t ≠ 1 ∧ finrank K (commSpace t) = 2 := by
  obtain ⟨k, hk⟩ := hE.even_finrank
  rcases card_le_or_exists_fix hE hp hpK hY hYinv with hle | ⟨g, hgE, hg1, Y', hY'0, hY'Y,
    hY'inv, hgY'⟩
  · exfalso
    have : p ^ 2 ≤ p ^ (finrank K X / 2 - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have := hp.one_lt
    have : p < p ^ 2 := by nlinarith
    omega
  · have hc := hE.isCompl hpK hgE
    have hEU := hE.resFix hpK hgE
    have hEW := hE.resComm hpK hgE
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a, ha⟩ := hEU.even_finrank
    obtain ⟨b, hb⟩ := hEW.even_finrank
    have hW0 : finrank K (commSpace g) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hg1
    have hY'U : Y' ≤ fixedSpace g := fun y hy => mem_fixedSpace.mpr (hgY' y hy)
    set Y'' : Submodule K (fixedSpace g) := Y'.comap (fixedSpace g).subtype with hY''
    have hY''0 : Y'' ≠ ⊥ := by
      intro h
      obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
      have hmem : (⟨y, hY'U hyY⟩ : fixedSpace g) ∈ Y'' := hyY
      rw [h, Submodule.mem_bot] at hmem
      exact hy0 (congrArg Subtype.val hmem)
    have hU0 : finrank K (fixedSpace g) ≠ 0 := by
      intro h
      apply hY''0
      have : Subsingleton (fixedSpace g) := Module.finrank_zero_iff.mp h
      exact Subsingleton.elim _ _
    have h1 := card_le_of_isotropic hp hpK hK1 (finrank K (fixedSpace g)) (fixedSpace g) rfl _ _
      hEU Y'' hY''0
      (by
        rintro _ ⟨h, rfl⟩ z hz
        exact hY'inv h h.2 z hz)
      (fun y hy y' hy' => hYiso y (hY'Y hy) y' (hY'Y hy'))
    have h2 := hEW.card_le hp hpK
    have h3 := card_le_mul_res hc (hE.fix_inv hgE) (hE.comm_inv hgE)
    have hpa : 0 < p ^ (finrank K (fixedSpace g) / 2 - 1) := pow_pos hp.pos _
    have hsplit : p ^ (finrank K X / 2 - 1) = p ^ (finrank K (fixedSpace g) / 2 - 1) *
        p ^ (finrank K (commSpace g) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hW : p ^ (finrank K (commSpace g) / 2) ≤
        Nat.card (resHom E _ (hE.comm_inv hgE)).range := by
      refine Nat.le_of_mul_le_mul_left ?_ hpa
      calc _ = p ^ (finrank K X / 2 - 1) := hsplit.symm
        _ ≤ Nat.card E := hcard
        _ ≤ _ := h3
        _ ≤ _ := Nat.mul_le_mul_right _ h1
    have hmul : Nat.card (resHom E _ (hE.fix_inv hgE)).range *
        Nat.card (resHom E _ (hE.comm_inv hgE)).range ≤ Nat.card E := by
      calc _ ≤ p ^ (finrank K (fixedSpace g) / 2 - 1) * p ^ (finrank K (commSpace g) / 2) :=
            Nat.mul_le_mul h1 h2
        _ = _ := hsplit.symm
        _ ≤ Nat.card E := hcard
    obtain ⟨tW, htW, htW1, htW2⟩ := exists_commSpace_two_of_full hp hpK
      (finrank K (commSpace g)) (commSpace g) rfl (by omega) _ _ hEW hW
    obtain ⟨t, htU, htW'⟩ := exists_lift hc _ _ hmul (one_mem _) htW
    refine ⟨t, t.2, fun h => htW1 ?_, ?_⟩
    · rw [← htW', show t = 1 from Subtype.ext h, map_one]
    · rw [finrank_commSpace_of_res_eq_one hc _ (hE.comm_inv hgE) htU, htW', htW2]

end Plane

end OrthRestOdd

end CFSG.StandardType
