module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartOne.LIT

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem exists_add_of_invariant [FiniteDimensional K V] {r : ℕ} (hrK : (r : K) ≠ 0)
    {x : V ≃ₗ[K] V} (hx : x ^ r = 1) {W : Submodule K V} (hW : ∀ w ∈ W, x w ∈ W) {w : V}
    (hw : w ∈ W) : ∃ f ∈ W ⊓ fixedSpace x, ∃ c ∈ W ⊓ commSpace x, w = f + c := by
  classical
  have hc := isCompl_fixedSpace_commSpace hrK hx
  obtain ⟨f₀, hf₀, c₀, hc₀, hfc⟩ : ∃ f₀ ∈ fixedSpace x, ∃ c₀ ∈ commSpace x, f₀ + c₀ = w := by
    have : w ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hxr : (x : V →ₗ[K] V) ^ r = 1 := by
    rw [← coe_pow_eq, hx]
    rfl
  have hpow : ∀ i : ℕ, ((x : V →ₗ[K] V) ^ i) f₀ = f₀ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Module.End.mul_apply]; simpa [mem_fixedSpace.mp hf₀] using ih
  have hNf : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) f₀ = (r : K) • f₀ := by
    rw [LinearMap.sum_apply]
    simp [hpow, Nat.cast_smul_eq_nsmul K]
  have hNc : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) c₀ = 0 := by
    obtain ⟨y, hy⟩ := mem_commSpace.mp hc₀
    have h := geom_sum_mul (x : V →ₗ[K] V) r
    rw [hxr, sub_self] at h
    have h2 := congrArg (fun f : V →ₗ[K] V => f y) h
    rw [← hy]
    simpa using h2
  have hNw : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) w = (r : K) • f₀ := by
    rw [← hfc, map_add, hNf, hNc, add_zero]
  have hxiW : ∀ i : ℕ, ((x : V →ₗ[K] V) ^ i) w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hw
    | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih
  have hNW : (∑ i ∈ Finset.range r, (x : V →ₗ[K] V) ^ i) w ∈ W := by
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => hxiW i
  have hf₀W : f₀ ∈ W := by
    rw [hNw] at hNW
    have := W.smul_mem ((r : K)⁻¹) hNW
    rwa [smul_smul, inv_mul_cancel₀ hrK, one_smul] at this
  have hc₀W : c₀ ∈ W := by
    have : c₀ = w - f₀ := by rw [← hfc]; abel
    rw [this]
    exact W.sub_mem hw hf₀W
  exact ⟨f₀, ⟨hf₀W, hf₀⟩, c₀, ⟨hc₀W, hc₀⟩, hfc.symm⟩

theorem finrank_inf_fixedSpace_add [FiniteDimensional K V] {r : ℕ} (hrK : (r : K) ≠ 0)
    {x : V ≃ₗ[K] V} (hx : x ^ r = 1) {W : Submodule K V} (hW : ∀ w ∈ W, x w ∈ W) :
    finrank K ↥(W ⊓ fixedSpace x) + finrank K ↥(W ⊓ commSpace x) = finrank K W := by
  have hc := isCompl_fixedSpace_commSpace hrK hx
  have hsup : (W ⊓ fixedSpace x) ⊔ (W ⊓ commSpace x) = W := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    obtain ⟨f, hf, c, hc', rfl⟩ := exists_add_of_invariant hrK hx hW hw
    exact Submodule.add_mem_sup hf hc'
  have hinf : (W ⊓ fixedSpace x) ⊓ (W ⊓ commSpace x) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ fixedSpace x := hv.1.2
    have h2 : v ∈ commSpace x := hv.2.2
    have := (Submodule.disjoint_def.mp hc.disjoint) v h1 h2
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ fixedSpace x) (W ⊓ commSpace x)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h.symm

theorem two_mul_le_finrank_of_good_split [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (Good : Submodule K V → Prop) (hTop : Good ⊤)
    (E : Subgroup (V ≃ₗ[K] V)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hcard : r ^ 2 ≤ Nat.card E)
    (hsplit : ∀ W : Submodule K V, Good W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ x ∈ E,
      Good (W ⊓ fixedSpace x) ∧ Good (W ⊓ commSpace x))
    {d : ℕ} (hd : ∀ W : Submodule K V, Good W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ g ∈ E,
      (∃ w ∈ W, g w ≠ w) → d ≤ finrank K W) :
    2 * d ≤ finrank K V ∧ (2 * d = finrank K V → ∃ x ∈ E, x ≠ 1 ∧ Good (fixedSpace x) ∧
      Good (commSpace x) ∧ finrank K (fixedSpace x) = d ∧ finrank K (commSpace x) = d ∧
      (∃ g ∈ E, ∃ w ∈ fixedSpace x, g w ≠ w) ∧ ∃ w ∈ commSpace x, x w ≠ w) := by
  classical
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hcard
  have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
  have hFinv : ∀ g ∈ E, ∀ w ∈ fixedSpace x, g w ∈ fixedSpace x := fun g hg w hw =>
    map_mem_fixedSpace (hcomm g hg x hxE) hw
  have hCinv : ∀ g ∈ E, ∀ w ∈ commSpace x, g w ∈ commSpace x := fun g hg w hw =>
    map_mem_commSpace (hcomm g hg x hxE) hw
  obtain ⟨hGF, hGC⟩ := hsplit ⊤ hTop (fun _ _ _ _ => Submodule.mem_top) x hxE
  rw [top_inf_eq] at hGF hGC
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  by_cases hA : ∃ g ∈ E, ∃ w ∈ fixedSpace x, g w ≠ w
  · obtain ⟨g, hgE, w, hwF, hgw⟩ := hA
    have hdF := hd _ hGF hFinv g hgE ⟨w, hwF, hgw⟩
    have hxC : ∃ c ∈ commSpace x, x c ≠ c := by
      by_contra hcon
      push Not at hcon
      have hCF : commSpace x ≤ fixedSpace x := fun c hc' => mem_fixedSpace.mpr (hcon c hc')
      have hCbot : commSpace x = ⊥ := by
        rw [eq_bot_iff]
        intro c hc'
        have := (Submodule.disjoint_def.mp hc.disjoint) c (hCF hc') hc'
        simp [this]
      have hFtop : fixedSpace x = ⊤ := by
        have := hc.sup_eq_top
        rwa [hCbot, sup_bot_eq] at this
      apply hx1
      apply LinearEquiv.ext
      intro y
      exact mem_fixedSpace.mp (by rw [hFtop]; exact Submodule.mem_top)
    obtain ⟨c, hcC, hxc⟩ := hxC
    have hdC := hd _ hGC hCinv x hxE ⟨c, hcC, hxc⟩
    exact ⟨by omega, fun heq => ⟨x, hxE, hx1, hGF, hGC, by omega, by omega,
      ⟨g, hgE, w, hwF, hgw⟩, ⟨c, hcC, hxc⟩⟩⟩
  · push Not at hA
    have hfaith : ∀ g ∈ E, (∀ c ∈ commSpace x, g c = c) → g = 1 := by
      intro g hg hgc
      apply LinearEquiv.ext
      intro y
      have hy : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨f, hf, c, hc', rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, hA g hg f hf, hgc c hc']
      rfl
    let ρ : E →* (V ≃ₗ[K] V) := E.subtype
    let ρC := restrictAction ρ (commSpace x) (fun g s hs => hCinv g g.2 s hs)
    have hinj : Function.Injective ρC := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      refine Subgroup.mem_bot.2 (Subtype.ext (hfaith g g.2 fun c hc' => ?_))
      have := congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨c, hc'⟩)
      exact this
    let E' : Subgroup (↥(commSpace x) ≃ₗ[K] ↥(commSpace x)) := ρC.range
    have hE'fin : Finite E' :=
      Finite.of_surjective (ρC.rangeRestrict) (MonoidHom.rangeRestrict_surjective ρC)
    have hE'comm : ∀ g ∈ E', ∀ h ∈ E', g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a a.2 b b.2)
    have hE'exp : ∀ g ∈ E', g ^ r = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ r = 1 := Subtype.ext (hexp a a.2)
      rw [this, map_one]
    have hE'card : r ^ 2 ≤ Nat.card E' := by
      have : Nat.card E' = Nat.card E :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [this]
      exact hcard
    obtain ⟨y', hy'E, hy'1, w, hw0, hyw⟩ :=
      exists_fixed_of_sq_le_card hr hrK E' hE'comm hE'exp hE'card
    obtain ⟨y, rfl⟩ := hy'E
    have hyE : (y : V ≃ₗ[K] V) ∈ E := y.2
    have hyr : (y : V ≃ₗ[K] V) ^ r = 1 := hexp _ hyE
    have hyc : ∃ c ∈ commSpace x, (y : V ≃ₗ[K] V) c ≠ c := by
      by_contra hcon
      push Not at hcon
      apply hy'1
      apply LinearEquiv.ext
      intro s
      exact Subtype.ext (hcon s s.2)
    have hwy : ((w : V)) ∈ fixedSpace (y : V ≃ₗ[K] V) :=
      mem_fixedSpace.mpr (congrArg Subtype.val hyw)
    have hyinvF : ∀ g ∈ E, ∀ w ∈ fixedSpace (y : V ≃ₗ[K] V), g w ∈ fixedSpace (y : V ≃ₗ[K] V) :=
      fun g hg w hw => map_mem_fixedSpace (hcomm g hg y hyE) hw
    have hyinvC : ∀ g ∈ E, ∀ w ∈ commSpace (y : V ≃ₗ[K] V), g w ∈ commSpace (y : V ≃ₗ[K] V) :=
      fun g hg w hw => map_mem_commSpace (hcomm g hg y hyE) hw
    obtain ⟨hGF', hGC''⟩ := hsplit (commSpace x) hGC hCinv y hyE
    have hF'inv : ∀ g ∈ E, ∀ w ∈ commSpace x ⊓ fixedSpace (y : V ≃ₗ[K] V),
        g w ∈ commSpace x ⊓ fixedSpace (y : V ≃ₗ[K] V) := fun g hg w hw =>
      ⟨hCinv g hg w hw.1, hyinvF g hg w hw.2⟩
    have hC'inv : ∀ g ∈ E, ∀ w ∈ commSpace x ⊓ commSpace (y : V ≃ₗ[K] V),
        g w ∈ commSpace x ⊓ commSpace (y : V ≃ₗ[K] V) := fun g hg w hw =>
      ⟨hCinv g hg w hw.1, hyinvC g hg w hw.2⟩
    have hxF' : ∃ w' ∈ commSpace x ⊓ fixedSpace (y : V ≃ₗ[K] V), x w' ≠ w' := by
      refine ⟨(w : V), ⟨w.2, hwy⟩, fun hxw => ?_⟩
      have := (Submodule.disjoint_def.mp hc.disjoint) (w : V) (mem_fixedSpace.mpr hxw) w.2
      exact hw0 (Subtype.ext this)
    have hdF' := hd _ hGF' hF'inv x hxE hxF'
    have hyC' : ∃ c ∈ commSpace x ⊓ commSpace (y : V ≃ₗ[K] V), (y : V ≃ₗ[K] V) c ≠ c := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hcC, hyc'⟩ := hyc
      obtain ⟨f', hf', c', hc'', rfl⟩ := exists_add_of_invariant hrK hyr
        (fun s hs => hCinv y hyE s hs) hcC
      apply hyc'
      rw [map_add, mem_fixedSpace.mp hf'.2, hcon c' hc'']
    have hdC' := hd _ hGC'' hC'inv y hyE hyC'
    have hdim := finrank_inf_fixedSpace_add (W := commSpace x) hrK hyr
      (fun s hs => hCinv y hyE s hs)
    have hle : finrank K (commSpace x) ≤ finrank K V := Submodule.finrank_le _
    refine ⟨by omega, fun heq => ?_⟩
    exfalso
    have hF1 : 1 ≤ finrank K (fixedSpace x) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have hbot : fixedSpace x = ⊥ := Submodule.finrank_eq_zero.mp h0
      exact hv0 (by simpa [hbot] using (mem_fixedSpace.mpr hxv : v ∈ fixedSpace x))
    omega

theorem two_mul_le_finrank_of_good [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (Good : Submodule K V → Prop) (hTop : Good ⊤)
    (E : Subgroup (V ≃ₗ[K] V)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hcard : r ^ 2 ≤ Nat.card E)
    (hsplit : ∀ W : Submodule K V, Good W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ x ∈ E,
      Good (W ⊓ fixedSpace x) ∧ Good (W ⊓ commSpace x))
    {d : ℕ} (hd : ∀ W : Submodule K V, Good W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ g ∈ E,
      (∃ w ∈ W, g w ≠ w) → d ≤ finrank K W) :
    2 * d ≤ finrank K V :=
  (two_mul_le_finrank_of_good_split hr hrK Good hTop E hcomm hexp hcard hsplit hd).1

section Sesq

variable {σ : K →+* K}

@[expose] def SesqNondegOn (B : V →ₗ[K] V →ₛₗ[σ] K) (W : Submodule K V) : Prop :=
  ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0

theorem inf_fixedSpace_orthogonal (B : V →ₗ[K] V →ₛₗ[σ] K) {x : V ≃ₗ[K] V}
    (hx : ∀ u v, B (x u) (x v) = B u v) {f c : V} (hf : f ∈ fixedSpace x)
    (hc : c ∈ commSpace x) : B f c = 0 ∧ B c f = 0 := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hc
  have hf' := mem_fixedSpace.mp hf
  have h1 : B f (x y) = B f y := by
    have := hx f y
    rwa [hf'] at this
  have h2 : B (x y) f = B y f := by
    have := hx y f
    rwa [hf'] at this
  refine ⟨?_, ?_⟩
  · rw [map_sub, h1, sub_self]
  · rw [map_sub, LinearMap.sub_apply, h2, sub_self]

theorem sesqNondegOn_inf_fixedSpace [FiniteDimensional K V] {r : ℕ} (hrK : (r : K) ≠ 0)
    (B : V →ₗ[K] V →ₛₗ[σ] K) {x : V ≃ₗ[K] V} (hx : x ^ r = 1)
    (hxiso : ∀ u v, B (x u) (x v) = B u v) {W : Submodule K V} (hW : SesqNondegOn B W)
    (hWinv : ∀ w ∈ W, x w ∈ W) :
    SesqNondegOn B (W ⊓ fixedSpace x) ∧ SesqNondegOn B (W ⊓ commSpace x) := by
  constructor
  · intro f hf hfo
    refine hW f hf.1 fun w hw => ?_
    obtain ⟨f', hf', c', hc', rfl⟩ := exists_add_of_invariant hrK hx hWinv hw
    rw [map_add, hfo f' hf', (inf_fixedSpace_orthogonal B hxiso hf.2 hc'.2).1, add_zero]
  · intro c hc hco
    refine hW c hc.1 fun w hw => ?_
    obtain ⟨f', hf', c', hc', rfl⟩ := exists_add_of_invariant hrK hx hWinv hw
    rw [map_add, (inf_fixedSpace_orthogonal B hxiso hf'.2 hc.2).2, hco c' hc', add_zero]

theorem two_mul_le_finrank_of_form [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (B : V →ₗ[K] V →ₛₗ[σ] K) (hB : SesqNondegOn B ⊤)
    (E : Subgroup (V ≃ₗ[K] V)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hcard : r ^ 2 ≤ Nat.card E)
    (hiso : ∀ g ∈ E, ∀ u v, B (g u) (g v) = B u v) {d : ℕ}
    (hd : ∀ W : Submodule K V, SesqNondegOn B W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ g ∈ E,
      (∃ w ∈ W, g w ≠ w) → d ≤ finrank K W) :
    2 * d ≤ finrank K V :=
  two_mul_le_finrank_of_good hr hrK (SesqNondegOn B) hB E hcomm hexp hcard
    (fun _ hW hWinv x hx =>
      sesqNondegOn_inf_fixedSpace hrK B (hexp x hx) (hiso x hx) hW (hWinv x hx)) hd

theorem exists_split_of_two_mul_eq_finrank_of_form [FiniteDimensional K V] {r : ℕ}
    (hr : r.Prime) (hrK : (r : K) ≠ 0) (B : V →ₗ[K] V →ₛₗ[σ] K) (hB : SesqNondegOn B ⊤)
    (E : Subgroup (V ≃ₗ[K] V)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hcard : r ^ 2 ≤ Nat.card E)
    (hiso : ∀ g ∈ E, ∀ u v, B (g u) (g v) = B u v) {d : ℕ}
    (hd : ∀ W : Submodule K V, SesqNondegOn B W → (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) → ∀ g ∈ E,
      (∃ w ∈ W, g w ≠ w) → d ≤ finrank K W) (h2 : 2 * d = finrank K V) :
    ∃ W₁ W₂ : Submodule K V, (∀ g ∈ E, ∀ w ∈ W₁, g w ∈ W₁) ∧ (∀ g ∈ E, ∀ w ∈ W₂, g w ∈ W₂) ∧
      SesqNondegOn B W₁ ∧ SesqNondegOn B W₂ ∧ IsCompl W₁ W₂ ∧
      (∀ u ∈ W₁, ∀ v ∈ W₂, B u v = 0) ∧ finrank K W₁ = d ∧ finrank K W₂ = d ∧
      (∃ g ∈ E, ∃ w ∈ W₁, g w ≠ w) ∧ ∃ g ∈ E, ∃ w ∈ W₂, g w ≠ w := by
  obtain ⟨-, hsplit⟩ := two_mul_le_finrank_of_good_split hr hrK (SesqNondegOn B) hB E hcomm hexp
    hcard (fun _ hW hWinv x hx =>
      sesqNondegOn_inf_fixedSpace hrK B (hexp x hx) (hiso x hx) hW (hWinv x hx)) hd
  obtain ⟨x, hxE, -, hGF, hGC, hF, hC, hA, w, hwC, hxw⟩ := hsplit h2
  refine ⟨fixedSpace x, commSpace x, fun g hg w hw => map_mem_fixedSpace (hcomm g hg x hxE) hw,
    fun g hg w hw => map_mem_commSpace (hcomm g hg x hxE) hw, hGF, hGC,
    isCompl_fixedSpace_commSpace hrK (hexp x hxE), fun u hu v hv =>
      (inf_fixedSpace_orthogonal B (hiso x hxE) hu hv).1, hF, hC, hA, ⟨x, hxE, w, hwC, hxw⟩⟩

end Sesq

end CFSG.RankThree.PartOne.LIT
