module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDict
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.H1Orth
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OTwoFixedSquare

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

private theorem wtO_two_or_four : ∀ y : orth.W, y ≠ 1 → wtO y = 2 ∨ wtO y = 4 := by
  decide +kernel

private theorem wtO_gen_four : ∀ y : orth.W, wtO y = 4 →
    ∃ y₁ y₂ : orth.W, wtO y₁ = 2 ∧ wtO y₂ = 2 ∧ y = y₁ * y₂ := by decide +kernel

private theorem wtO_gen_two : ∀ y : orth.W, wtO y = 2 →
    ∃ y₁ y₂ : orth.W, wtO y₁ = 4 ∧ wtO y₂ = 4 ∧ y = y₁ * y₂ := by decide +kernel

private theorem wtO_ne_one_of_two : ∀ y : orth.W, wtO y = 2 → y ≠ 1 := by decide +kernel

private theorem wtO_ne_one_of_four : ∀ y : orth.W, wtO y = 4 → y ≠ 1 := by decide +kernel

theorem orth_irred_alt5 (Y : Subgroup orth.W)
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, orth.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : ∀ u ∈ Y, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
  · right
    push Not at hbot
    obtain ⟨x, hxY, hx1⟩ := hbot
    have horb : ∀ y : orth.W, y ≠ 1 → wtO y = wtO x → y ∈ Y := fun y hy hw => by
      obtain ⟨σ, hσ, hσy⟩ := (orth_orbits x y hx1 hy).mpr hw.symm
      rw [← hσy]
      exact hY σ hσ x hxY
    rw [eq_top_iff]
    intro y _
    by_cases hy1 : y = 1
    · rw [hy1]; exact Y.one_mem
    rcases wtO_two_or_four x hx1 with hx | hx <;> rcases wtO_two_or_four y hy1 with hy | hy
    · exact horb y hy1 (hy.trans hx.symm)
    · obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := wtO_gen_four y hy
      exact Y.mul_mem (horb y₁ (wtO_ne_one_of_two y₁ h₁) (h₁.trans hx.symm))
        (horb y₂ (wtO_ne_one_of_two y₂ h₂) (h₂.trans hx.symm))
    · obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := wtO_gen_two y hy
      exact Y.mul_mem (horb y₁ (wtO_ne_one_of_four y₁ h₁) (h₁.trans hx.symm))
        (horb y₂ (wtO_ne_one_of_four y₂ h₂) (h₂.trans hx.symm))
    · exact horb y hy1 (hy.trans hx.symm)

variable {G : Type} [Group G]

theorem map_oTwoRes_le_alt {X : Subgroup G} (ψ : ↥X →* Perm (Fin 5)) :
    ((oTwoRes X).subgroupOf X).map ψ ≤ alternatingGroup (Fin 5) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : G) ∈ oTwoRes X := hx
  have hle : oTwoRes X ≤ ((alternatingGroup (Fin 5)).comap ψ).map X.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgX, m, hm, hgm⟩
    refine ⟨⟨g, hgX⟩, ?_, rfl⟩
    show ψ ⟨g, hgX⟩ ∈ alternatingGroup (Fin 5)
    rw [Equiv.Perm.mem_alternatingGroup]
    have h2 : Perm.sign (ψ ⟨g, hgX⟩) ^ m = 1 := by
      rw [← map_pow, ← map_pow]
      have : (⟨g, hgX⟩ : ↥X) ^ m = 1 := Subtype.ext (by simpa using hgm)
      rw [this]; simp
    rcases Int.units_eq_one_or (Perm.sign (ψ ⟨g, hgX⟩)) with h | h
    · exact h
    · rw [h, hm.neg_one_pow] at h2
      exact absurd h2 (by decide)
  obtain ⟨y, hy, hyx⟩ := hle hx'
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem alt_le_map_oTwoRes [Finite G] {X : Subgroup G} {ψ : ↥X →* Perm (Fin 5)}
    (hψ : Function.Surjective ψ) :
    alternatingGroup (Fin 5) ≤ ((oTwoRes X).subgroupOf X).map ψ := by
  have hthree : ∀ τ : Perm (Fin 5), τ.IsThreeCycle →
      ∃ o : G, o ∈ X ∧ (∃ m : ℕ, Odd m ∧ o ^ m = 1) ∧ ∃ ho : o ∈ X, ψ ⟨o, ho⟩ = τ := by
    intro τ hτ
    obtain ⟨g, rfl⟩ := hψ τ
    obtain ⟨j, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    have hτ3 : ψ g ^ 3 = 1 := by
      rw [← pow_orderOf_eq_one (ψ g), hτ.orderOf]
    refine ⟨(g : G) ^ (4 ^ j), X.pow_mem g.2 _, ⟨m', hm', ?_⟩, X.pow_mem g.2 _, ?_⟩
    · rw [← pow_mul]
      have : 4 ^ j * m' = 2 ^ j * m' * 2 ^ j := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
      rw [this, pow_mul, ← hm, pow_orderOf_eq_one, one_pow]
    · show ψ (g ^ 4 ^ j) = ψ g
      rw [map_pow]
      have h4 : ∀ t : ℕ, ψ g ^ (4 ^ t) = ψ g := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, pow_mul, ih]
          have : ψ g ^ 4 = ψ g := by
            rw [show 4 = 3 + 1 by norm_num, pow_add, hτ3, one_mul, pow_one]
          exact this
      exact h4 j
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro τ hτ
  obtain ⟨o, hoF, hodd, ho, hθo⟩ := hthree τ hτ
  exact ⟨⟨o, hoF⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨hoF, hodd⟩), hθo⟩

theorem map_oTwoRes_eq_alt [Finite G] {X : Subgroup G} {ψ : ↥X →* Perm (Fin 5)}
    (hψ : Function.Surjective ψ) :
    ((oTwoRes X).subgroupOf X).map ψ = alternatingGroup (Fin 5) :=
  le_antisymm (map_oTwoRes_le_alt ψ) (alt_le_map_oTwoRes hψ)

theorem conj_mem_of_normalizes {X Z : Subgroup G} (h : X ≤ Subgroup.normalizer (Z : Set G))
    {x z : G} (hx : x ∈ X) (hz : z ∈ Z) : x * z * x⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (h hx) z).mp hz

theorem exists_centralizer_quotient {X N Z : Subgroup G}
    (hZ : X ≤ Subgroup.normalizer (Z : Set G)) (hN : X ≤ Subgroup.normalizer (N : Set G)) :
    ∃ C : Subgroup G, (∀ g, g ∈ C ↔ g ∈ X ∧ ∀ n ∈ N, ⁅n, g⁆ ∈ Z) ∧ C ≤ X ∧
      X ≤ Subgroup.normalizer (C : Set G) := by
  let C : Subgroup G :=
    { carrier := {g | g ∈ X ∧ ∀ n ∈ N, ⁅n, g⁆ ∈ Z}
      one_mem' := ⟨X.one_mem, fun n _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨X.mul_mem ha hb, fun n hn => ?_⟩
        have e : ⁅n, a * b⁆ = ⁅n, a⁆ * (a * ⁅n, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Z.mul_mem (ha' n hn) (conj_mem_of_normalizes hZ ha (hb' n hn))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨X.inv_mem ha, fun n hn => ?_⟩
        have e : ⁅n, a⁻¹⁆ = a⁻¹ * ⁅n, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact conj_mem_of_normalizes hZ (X.inv_mem ha) (Z.inv_mem (ha' n hn)) }
  have key : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    refine ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx), fun n hn => ?_⟩
    have e : ⁅n, x * c * x⁻¹⁆ = x * ⁅x⁻¹ * n * x, c⁆ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hn' : x⁻¹ * n * x ∈ N := by
      have := conj_mem_of_normalizes hN (X.inv_mem hx) hn
      simpa using this
    exact conj_mem_of_normalizes hZ hx (hc.2 _ hn')
  refine ⟨C, fun g => Iff.rfl, fun g hg => hg.1, fun x hx => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x hx c, fun hc => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hc
  simpa [mul_assoc] using this

theorem oTwoRes_le_of_cover {X C Q : Subgroup G}
    (hn : X ≤ Subgroup.normalizer (C : Set G)) (hQ : IsPGroup 2 Q) (hQX : Q ≤ X)
    (hcov : ∀ x ∈ X, ∃ c ∈ C, ∃ q ∈ Q, x = c * q) : oTwoRes X ≤ C := by
  refine (Subgroup.closure_le C).mpr ?_
  rintro x ⟨hxX, m, hm, hxm⟩
  obtain ⟨c, hc, q, hq, rfl⟩ := hcov x hxX
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hq1 : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hpow : ∀ j : ℕ, ∃ c' ∈ C, (c * q) ^ j = c' * q ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨c', hc', he⟩ := ih
      have hconj : q ^ j * c * (q ^ j)⁻¹ ∈ C :=
        conj_mem_of_normalizes hn (X.pow_mem (hQX hq) j) hc
      refine ⟨c' * (q ^ j * c * (q ^ j)⁻¹), C.mul_mem hc' hconj, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨c', hc', he⟩ := hpow (2 ^ k)
  have hy : (c * q) ^ 2 ^ k ∈ C := by rw [he, hq1, mul_one]; exact hc'
  have hcop : (2 ^ k).Coprime (orderOf (c * q)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxm)
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm))
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← ha]
  exact C.pow_mem hy a

namespace Dict5

variable {X S Z : Subgroup G} (D : Dict5 X S Z)

include D in
theorem eq_bot_or_eq_of_invariant_oTwoRes [Finite G] {V : Subgroup G} (hVZ : V ≤ Z)
    (h : ∀ l ∈ oTwoRes X, ∀ v ∈ V, l * v * l⁻¹ ∈ V) : V = ⊥ ∨ V = Z := by
  have hinv := (D.invariant_iff (oTwoRes_le X) hVZ).mp h
  have hA : alternatingGroup (Fin 5) ≤ D.bar (oTwoRes X) := alt_le_map_oTwoRes D.surj
  rcases orth_irred_alt5 (V.comap D.φ) (fun σ hσ y hy => hinv σ (hA hσ) y hy) with h0 | h0
  · left
    rw [← D.map_comap_φ hVZ, h0]
    exact Subgroup.map_bot _
  · right
    rw [← D.map_comap_φ hVZ, h0]
    exact D.map_φ_top

include D in
theorem exists_principal [Finite G] (f : G → G) (hZ : ∀ l ∈ oTwoRes X, f l ∈ Z)
    (hcoc : ∀ l ∈ oTwoRes X, ∀ l' ∈ oTwoRes X, f (l * l') = f l * (l * f l' * l⁻¹))
    (hker : ∀ q ∈ oTwoRes X, q ∈ pCoreOf 2 X → f q = 1) :
    ∃ z ∈ Z, ∀ l ∈ oTwoRes X, f l = l * z * l⁻¹ * z⁻¹ := by
  classical
  have hA : alternatingGroup (Fin 5) ≤ D.bar (oTwoRes X) := alt_le_map_oTwoRes D.surj
  have hex : ∀ σ : alternatingGroup (Fin 5), ∃ x : ↥X, (x : G) ∈ oTwoRes X ∧ D.ψ x = σ.1 :=
    fun σ => (D.mem_bar_iff σ.1).mp (hA σ.2)
  choose x hxL hxψ using hex
  have hLX : ∀ l : ↥X, (l : G) ∈ oTwoRes X → D.ψ l ∈ alternatingGroup (Fin 5) := fun l hl =>
    map_oTwoRes_le_alt D.ψ ⟨l, hl, rfl⟩
  have hwd : ∀ l : ↥X, ∀ hl : (l : G) ∈ oTwoRes X,
      f l = f (x ⟨D.ψ l, hLX l hl⟩) := by
    intro l hl
    set x0 := x ⟨D.ψ l, hLX l hl⟩ with hx0
    have hx0ψ : D.ψ x0 = D.ψ l := hxψ _
    have hq : ((x0⁻¹ * l : ↥X) : G) ∈ pCoreOf 2 X :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hx0ψ, inv_mul_cancel])
    have hqL : ((x0⁻¹ * l : ↥X) : G) ∈ oTwoRes X := by
      have := (oTwoRes X).mul_mem ((oTwoRes X).inv_mem (hxL ⟨D.ψ l, hLX l hl⟩)) hl
      simpa using this
    have h1 := hcoc (x0 : G) (hxL _) ((x0⁻¹ * l : ↥X) : G) hqL
    rw [hker _ hqL hq] at h1
    have h2 : (x0 : G) * ((x0⁻¹ * l : ↥X) : G) = l := by simp
    rw [h2] at h1
    rw [h1]
    simp
  have hfx : ∀ σ : alternatingGroup (Fin 5), f (x σ) ∈ D.φ.range := fun σ =>
    D.range_eq.ge (hZ _ (hxL σ))
  choose F hF using fun σ => (hfx σ)
  have hcocF : ∀ g h : alternatingGroup (Fin 5),
      F (g * h) = F g * orth.act (g : Perm (Fin 5)) (F h) := by
    intro g h
    apply D.inj
    have h1 : D.φ (F (g * h)) = f (x (g * h)) := hF _
    have hl : ((x g * x h : ↥X) : G) ∈ oTwoRes X :=
      (oTwoRes X).mul_mem (hxL g) (hxL h)
    have hψl : D.ψ (x g * x h) = ((g * h : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
      rw [map_mul, hxψ, hxψ]; rfl
    have h2 : f ((x g * x h : ↥X) : G) = f (x (g * h)) := by
      rw [hwd _ hl]
      exact congrArg (fun σ : alternatingGroup (Fin 5) => f (x σ)) (Subtype.ext hψl)
    rw [map_mul, h1, ← h2, Subgroup.coe_mul, hcoc _ (hxL g) _ (hxL h), ← hF g, ← hF h]
    have h3 := D.act_eq (x g) (F h)
    rw [hxψ g] at h3
    rw [h3]
  obtain ⟨w, hw⟩ := h1_alt5_orth F hcocF
  refine ⟨D.φ w, D.φ_mem w, fun l hl => ?_⟩
  have hlX : l ∈ X := oTwoRes_le X hl
  set σ : alternatingGroup (Fin 5) := ⟨D.ψ ⟨l, hlX⟩, hLX ⟨l, hlX⟩ hl⟩ with hσ
  have h1 := hwd ⟨l, hlX⟩ hl
  have h2 : D.φ (F σ) = f (x σ) := hF σ
  have h3 := D.act_eq ⟨l, hlX⟩ w
  have h4 : f l = D.φ (F σ) := by rw [h2]; exact h1
  rw [h4, hw σ, map_mul, map_inv]
  have h5 : D.φ (orth.act (σ : Perm (Fin 5)) w) = l * D.φ w * l⁻¹ := h3
  rw [h5]

include D in
theorem eq_of_normalised_comm [Finite G] {N Qd Y K : Subgroup G}
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZc : ∀ q ∈ pCoreOf 2 X, ∀ z ∈ Z, q * z = z * q)
    (hZX : X ≤ Subgroup.normalizer (Z : Set G)) (hcard : Nat.card Z = 16)
    (hNX : X ≤ Subgroup.normalizer (N : Set G)) (hNle : N ≤ X) (hN2 : IsPGroup 2 N)
    (hZN : Z ≤ N) (hcen : N ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hKN : ∀ n ∈ N, ∀ k ∈ K, ⁅n, k⁆ ∈ Z)
    (hKodd : ∃ k ∈ K, ∃ hk : k ∈ X, D.ψ ⟨k, hk⟩ = swap 0 2)
    (hY : Nat.card Y = 4) (hQdY : ∀ n ∈ N, ∀ t ∈ pCoreOf 2 X ⊓ Qd, ⁅n, t⁆ ∈ Y)
    (hidx : Qd.relIndex (pCoreOf 2 X) = 2) : N = Z := by
  classical
  obtain ⟨C, hC, hCX, hCn⟩ := exists_centralizer_quotient hZX hNX
  have hQp : IsPGroup 2 (pCoreOf 2 X) := pCoreOf_isPGroup (r := 2) X
  have hQX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hτ : (swap 0 2 : Perm (Fin 5)) ∈ D.bar C := by
    obtain ⟨k, hk, hkX, hψ⟩ := hKodd
    exact (D.mem_bar_iff _).mpr ⟨⟨k, hkX⟩, (hC k).mpr ⟨hkX, fun n hn => hKN n hn k hk⟩, hψ⟩
  have hconj : ∀ i j : Fin 5, i ≠ j → ∃ g : Perm (Fin 5), g * swap 0 2 * g⁻¹ = swap i j := by
    decide +kernel
  have hswap : ∀ s : Perm (Fin 5), s.IsSwap → s ∈ D.bar C := by
    rintro s ⟨i, j, hij, rfl⟩
    obtain ⟨g, hg⟩ := hconj i j hij
    obtain ⟨y, rfl⟩ := D.surj g
    obtain ⟨c, hc, hcτ⟩ := (D.mem_bar_iff _).mp hτ
    refine (D.mem_bar_iff _).mpr ⟨y * c * y⁻¹, ?_, ?_⟩
    · have := conj_mem_of_normalizes hCn y.2 hc
      simpa using this
    · rw [map_mul, map_mul, map_inv, hcτ, hg]
  have hbarTop : D.bar C = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    exact fun s hs => hswap s hs
  have hcov : ∀ x ∈ X, ∃ c ∈ C, ∃ q ∈ pCoreOf 2 X, x = c * q := by
    intro x hx
    have hx' : D.ψ ⟨x, hx⟩ ∈ D.bar C := by rw [hbarTop]; trivial
    obtain ⟨c, hc, hcψ⟩ := (D.mem_bar_iff _).mp hx'
    refine ⟨c, hc, (c : G)⁻¹ * x, ?_, by group⟩
    have : ((c⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ pCoreOf 2 X :=
      (D.ker_iff _).mp (by rw [map_mul, map_inv, hcψ, inv_mul_cancel])
    simpa using this
  have hLC : oTwoRes X ≤ C := oTwoRes_le_of_cover hCn hQp hQX hcov
  set P : Subgroup G := oTwoRes X ⊓ pCoreOf 2 X with hP
  have hPC : ∀ t ∈ P, ∀ n ∈ N, ⁅n, t⁆ ∈ Z := fun t ht n hn => ((hC t).mp (hLC ht.1)).2 n hn
  have hPnorm : ∀ l ∈ oTwoRes X, ∀ t ∈ P, l * t * l⁻¹ ∈ P := fun l hl t ht =>
    ⟨(oTwoRes X).mul_mem ((oTwoRes X).mul_mem hl ht.1) ((oTwoRes X).inv_mem hl),
      conj_mem_of_normalizes (le_normalizer_pCoreOf 2 X) (oTwoRes_le X hl) ht.2⟩
  have hPtriv : ∀ n ∈ N, ∀ t ∈ P, ⁅n, t⁆ = 1 := by
    intro n hn
    let fn : ↥P →* G :=
      { toFun := fun t => ⁅n, (t : G)⁆
        map_one' := by simp
        map_mul' := fun t s => by
          have hs : ⁅n, (s : G)⁆ ∈ Z := hPC s s.2 n hn
          have hc : (t : G) * ⁅n, (s : G)⁆ = ⁅n, (s : G)⁆ * (t : G) := hZc t t.2.2 _ hs
          have h1 : (t : G) * ⁅n, (s : G)⁆ * (t : G)⁻¹ = ⁅n, (s : G)⁆ := by rw [hc]; group
          have e : ⁅n, (t : G) * s⁆ = ⁅n, (t : G)⁆ * ((t : G) * ⁅n, (s : G)⁆ * (t : G)⁻¹) := by
            simp only [commutatorElement_def]; group
          show ⁅n, ((t * s : ↥P) : G)⁆ = _
          rw [Subgroup.coe_mul, e, h1] }
    set B := fn.range with hB
    have hBZ : B ≤ Z := by
      rintro _ ⟨t, rfl⟩
      exact hPC t t.2 n hn
    have hBinv : ∀ l ∈ oTwoRes X, ∀ b ∈ B, l * b * l⁻¹ ∈ B := by
      rintro l hl _ ⟨t, rfl⟩
      have ht' := hPnorm l hl t t.2
      refine ⟨⟨l * t * l⁻¹, ht'⟩, ?_⟩
      show ⁅n, l * (t : G) * l⁻¹⁆ = l * ⁅n, (t : G)⁆ * l⁻¹
      have hlC := (hC l).mp (hLC hl)
      obtain ⟨u, hu⟩ : ∃ u, u = l * n * l⁻¹ * n⁻¹ := ⟨_, rfl⟩
      have huZ : u ∈ Z := by
        have h1 := Z.inv_mem (hlC.2 n hn)
        have e : ⁅n, l⁆⁻¹ = u := by rw [hu]; simp only [commutatorElement_def]; group
        rwa [e] at h1
      obtain ⟨t', ht'def⟩ : ∃ t', t' = l * (t : G) * l⁻¹ := ⟨_, rfl⟩
      rw [← ht'def]
      have ht'P : t' ∈ P := by rw [ht'def]; exact ht'
      have hw : ⁅n, t'⁆ ∈ Z := hPC t' ht'P n hn
      have hct : t' * u = u * t' := hZc t' ht'P.2 u huZ
      have e1 : l * ⁅n, (t : G)⁆ * l⁻¹ = ⁅u * n, t'⁆ := by
        have h1 : l * n * l⁻¹ = u * n := by rw [hu]; group
        calc l * ⁅n, (t : G)⁆ * l⁻¹ = ⁅l * n * l⁻¹, l * (t : G) * l⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅u * n, t'⁆ := by rw [h1, ht'def]
      have e2 : ⁅u * n, t'⁆ = u * ⁅n, t'⁆ * (t' * u⁻¹ * t'⁻¹) := by
        simp only [commutatorElement_def]; group
      have e3 : t' * u⁻¹ * t'⁻¹ = u⁻¹ := by
        have h : t' * u * t'⁻¹ = u := by rw [hct]; group
        calc t' * u⁻¹ * t'⁻¹ = (t' * u * t'⁻¹)⁻¹ := by group
          _ = u⁻¹ := by rw [h]
      have e4 : u * ⁅n, t'⁆ * u⁻¹ = ⁅n, t'⁆ := by rw [hZab u huZ _ hw]; group
      rw [e1, e2, e3, e4]
    rcases D.eq_bot_or_eq_of_invariant_oTwoRes hBZ hBinv with h0 | h0
    · intro t ht
      have : ⁅n, t⁆ ∈ B := ⟨⟨t, ht⟩, rfl⟩
      rw [h0] at this
      exact Subgroup.mem_bot.mp this
    · exfalso
      have hf' : Function.Surjective fn.rangeRestrict := MonoidHom.rangeRestrict_surjective fn
      set H0 : Subgroup ↥P := (Qd ⊓ P).subgroupOf P with hH0
      have hPQ : P ≤ pCoreOf 2 X := inf_le_right
      have hH0 : H0.index ≤ 2 := by
        have h1 : H0.index = Qd.relIndex P := by
          show (Qd ⊓ P).relIndex P = Qd.relIndex P
          exact Subgroup.inf_relIndex_right Qd P
        rw [h1, ← hidx]
        exact Subgroup.relIndex_le_of_le_right hPQ (by rw [hidx]; norm_num)
      set T : Subgroup ↥B := H0.map fn.rangeRestrict with hT
      have hTi : T.index ≤ 2 := by
        have hpos : 0 < H0.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H0))
        exact (Nat.le_of_dvd hpos (Subgroup.index_map_dvd H0 hf')).trans hH0
      have hTle : T.map B.subtype ≤ Y := by
        rintro _ ⟨b, ⟨s, hs, rfl⟩, rfl⟩
        have hs' : (s : G) ∈ Qd ⊓ P := hs
        exact hQdY n hn s ⟨hs'.2.2, hs'.1⟩
      have hTc : Nat.card T ≤ 4 := by
        rw [← hY, ← Subgroup.card_map_of_injective B.subtype_injective]
        exact Subgroup.card_le_of_le hTle
      have h16 : Nat.card B = 16 := by rw [h0]; exact hcard
      have hmul := Subgroup.card_mul_index T
      have : Nat.card T * T.index ≤ 4 * 2 := Nat.mul_le_mul hTc hTi
      omega
  refine le_antisymm (fun n hn => ?_) hZN
  have hfZ : ∀ l ∈ oTwoRes X, l * n * l⁻¹ * n⁻¹ ∈ Z := by
    intro l hl
    have h1 := Z.inv_mem (((hC l).mp (hLC hl)).2 n hn)
    have e : ⁅n, l⁆⁻¹ = l * n * l⁻¹ * n⁻¹ := by simp only [commutatorElement_def]; group
    rwa [e] at h1
  have hfcoc : ∀ l ∈ oTwoRes X, ∀ l' ∈ oTwoRes X,
      (l * l') * n * (l * l')⁻¹ * n⁻¹ = (l * n * l⁻¹ * n⁻¹) *
        (l * (l' * n * l'⁻¹ * n⁻¹) * l⁻¹) := by
    intro l hl l' hl'
    have h1 : l * (l' * n * l'⁻¹ * n⁻¹) * l⁻¹ ∈ Z :=
      conj_mem_of_normalizes hZX (oTwoRes_le X hl) (hfZ l' hl')
    rw [hZab _ (hfZ l hl) _ h1]
    group
  have hfker : ∀ q ∈ oTwoRes X, q ∈ pCoreOf 2 X → q * n * q⁻¹ * n⁻¹ = 1 := by
    intro q hq hqQ
    have h1 := hPtriv n hn q ⟨hq, hqQ⟩
    have e : q * n * q⁻¹ * n⁻¹ = ⁅n, q⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e, h1, inv_one]
  obtain ⟨z, hzZ, hz⟩ := D.exists_principal (fun g => g * n * g⁻¹ * n⁻¹) hfZ hfcoc hfker
  have hmC : z⁻¹ * n ∈ Subgroup.centralizer (oTwoRes X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : h * n * h⁻¹ * n⁻¹ = h * z * h⁻¹ * z⁻¹ := hz h hh
    have e : h * n * h⁻¹ = (h * z * h⁻¹ * z⁻¹) * n := by
      calc h * n * h⁻¹ = (h * n * h⁻¹ * n⁻¹) * n := by group
        _ = _ := by rw [h1]
    calc h * (z⁻¹ * n) = (h * z⁻¹ * h⁻¹) * (h * n * h⁻¹) * h := by group
      _ = (h * z⁻¹ * h⁻¹) * ((h * z * h⁻¹ * z⁻¹) * n) * h := by rw [e]
      _ = (z⁻¹ * n) * h := by group
  have hbot : N ⊓ Subgroup.centralizer (oTwoRes X : Set G) = ⊥ := by
    by_contra hne
    exact (inf_centralizer_ne_bot_of_oTwoRes hNle hN2 hNX hne) hcen
  have hm : z⁻¹ * n ∈ N ⊓ Subgroup.centralizer (oTwoRes X : Set G) :=
    ⟨N.mul_mem (N.inv_mem (hZN hzZ)) hn, hmC⟩
  rw [hbot, Subgroup.mem_bot] at hm
  rw [← inv_mul_eq_one.mp hm]
  exact hzZ

end Dict5

end CFSG.Quasithin.F53.Stellmacher.S43
