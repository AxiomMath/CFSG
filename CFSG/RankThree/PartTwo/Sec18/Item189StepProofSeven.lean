module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofTwoRank
public import CFSG.SignalizerFunctorTheorem.MinimalAction.Baer
public import CFSG.SignalizerFunctorTheorem.MinimalAction.AbelianCase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.SignalizerFunctorTheorem.MinimalAction

section Seven

variable {Y : Type*} [Group Y]

theorem commute_of_mem_zpowers189 {a g y : Y} (hg : a * g = g * a)
    (hy : y ∈ Subgroup.zpowers a) : y * g = g * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left hg k).eq

@[expose] def abelianizationEnd189 (P : Subgroup Y) :
    MulAut P →* AddMonoid.End (Additive (Abelianization P)) where
  toFun α := MonoidHom.toAdditive (Abelianization.map α.toMonoidHom)
  map_one' := by
    show MonoidHom.toAdditive (Abelianization.map (MonoidHom.id P)) =
      (1 : AddMonoid.End (Additive (Abelianization P)))
    rw [Abelianization.map_id]
    rfl
  map_mul' α β := by
    show MonoidHom.toAdditive (Abelianization.map (α.toMonoidHom.comp β.toMonoidHom)) = _
    rw [← Abelianization.map_comp]
    rfl

variable [Finite Y]

theorem mem_commutator_of_centralizes189 {p : ℕ} [Fact p.Prime] {P A : Subgroup Y}
    (hP : IsPGroup p P) (hA : Nat.Coprime p (Nat.card A))
    (hAP : A ≤ Subgroup.normalizer (P : Set Y)) (hPA : ⁅P, A⁆ = P) {r : Y} (hr : r ∈ P)
    (hcent : ∀ b ∈ A, b * r = r * b) : r ∈ ⁅P, P⁆ := by
  let ρ : A →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  let φ : A →* AddMonoid.End (Additive (Abelianization P)) := (abelianizationEnd189 P).comp ρ
  have hφ : ∀ (b : A) (g : P), φ b (Additive.ofMul (Abelianization.of g)) =
      Additive.ofMul (Abelianization.of (ρ b g)) := fun _ _ => rfl
  have hρ : ∀ (b : A) (g : P), ((ρ b g : P) : Y) = (b : Y) * g * (b : Y)⁻¹ := fun _ _ => rfl
  have hV : ∃ k : ℕ, Nat.card (Additive (Abelianization P)) = p ^ k := by
    have hab : IsPGroup p (Abelianization P) :=
      hP.of_surjective Abelianization.of fun y => QuotientGroup.induction_on y fun g => ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hab.exists_card_eq
    exact ⟨k, (Nat.card_congr Additive.toMul).trans hk⟩
  let W : AddSubgroup (Additive (Abelianization P)) :=
    AddSubgroup.closure {u | ∃ b ∈ (⊤ : Subgroup A), ∃ v, u = φ b v - v}
  have hgen : ∀ (b : A) (v : Additive (Abelianization P)), φ b v - v ∈ W := fun b v =>
    AddSubgroup.subset_closure ⟨b, Subgroup.mem_top b, v, rfl⟩
  let S₀ : Subgroup P := (AddSubgroup.toSubgroup' W).comap Abelianization.of
  have hS₀ : ∀ g : P, g ∈ S₀ ↔ Additive.ofMul (Abelianization.of g) ∈ W := fun g => Iff.rfl
  have hle : ⁅P, A⁆ ≤ S₀.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg b hb
    have hgb : ⁅g, b⁆ ∈ P := hPA.le (Subgroup.commutator_mem_commutator hg hb)
    refine ⟨⟨⁅g, b⁆, hgb⟩, (hS₀ _).mpr ?_, rfl⟩
    have hdecomp : (⟨⁅g, b⁆, hgb⟩ : P) = ⟨g, hg⟩ * (ρ ⟨b, hb⟩ ⟨g, hg⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ, commutatorElement_def]
      group
    rw [hdecomp, map_mul, map_inv, ofMul_mul, ofMul_inv, ← hφ]
    have h1 := neg_mem (hgen ⟨b, hb⟩ (Additive.ofMul (Abelianization.of ⟨g, hg⟩)))
    have h2 : Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P)) +
        -(φ ⟨b, hb⟩ (Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P)))) =
        -(φ ⟨b, hb⟩ (Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P))) -
          Additive.ofMul (Abelianization.of (⟨g, hg⟩ : P))) := by abel
    rw [h2]
    exact h1
  have hw : Additive.ofMul (Abelianization.of (⟨r, hr⟩ : P)) ∈ W := by
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp (hle (hPA.ge hr))
    have hy' : y = ⟨r, hr⟩ := Subtype.ext hyr
    rw [hy'] at hy
    exact (hS₀ _).mp hy
  have hρr : ∀ b : A, ρ b ⟨r, hr⟩ = ⟨r, hr⟩ := fun b => by
    apply Subtype.ext
    rw [hρ]
    exact mul_inv_eq_of_eq_mul (hcent b b.2)
  have hfix : ∀ b ∈ (⊤ : Subgroup A), φ b (Additive.ofMul (Abelianization.of (⟨r, hr⟩ : P))) =
      Additive.ofMul (Abelianization.of (⟨r, hr⟩ : P)) := fun b _ => by
    rw [hφ, hρr]
  have hQ : Nat.Coprime p (Nat.card (⊤ : Subgroup A)) := by rwa [Subgroup.card_top]
  have h0 := eq_zero_of_mem_commutator_of_fixed hV φ hQ hw hfix
  have h1 : Abelianization.of (⟨r, hr⟩ : P) = 1 := by simpa using h0
  have h2 : (⟨r, hr⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    exact h1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h2, rfl⟩

structure MinimalSeven189 (P : Subgroup Y) (x : Y) : Prop where
  pgroup : IsPGroup 2 P
  normalizes : x ∈ Subgroup.normalizer (P : Set Y)
  order : orderOf x = 7
  nontrivial : ∃ g ∈ P, x * g ≠ g * x
  minimal : ∀ R : Subgroup Y, R < P → x ∈ Subgroup.normalizer (R : Set Y) →
    ∀ g ∈ R, x * g = g * x

namespace MinimalSeven189

variable {P : Subgroup Y} {x : Y}

omit [Finite Y] in
theorem zpowers_le_normalizer (h : MinimalSeven189 P x) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set Y) :=
  Subgroup.zpowers_le.mpr h.normalizes

omit [Finite Y] in
theorem sevenGroup (h : MinimalSeven189 P x) : IsPGroup 7 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order, pow_one])

omit [Finite Y] in
theorem ne_bot (h : MinimalSeven189 P x) : P ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hg, hne⟩ := h.nontrivial
  rw [hbot, Subgroup.mem_bot] at hg
  exact hne (by rw [hg, mul_one, one_mul])

theorem coprime (h : MinimalSeven189 P x) :
    Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card P) := by
  obtain ⟨b, hb⟩ := h.pgroup.exists_card_eq
  rw [Nat.card_zpowers, h.order, hb]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem commutator_lt (h : MinimalSeven189 P x) : ⁅P, P⁆ < P :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups P P h.pgroup h.pgroup
    Subgroup.le_normalizer h.ne_bot

theorem commutator_eq_self (h : MinimalSeven189 P x) : ⁅P, Subgroup.zpowers x⁆ = P := by
  have hne : ⁅P, Subgroup.zpowers x⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨g, hg, hne⟩ := h.nontrivial
    exact hne (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hg) _ (Subgroup.mem_zpowers _))
  refine CFSG.GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime
    (Subgroup.zpowers x) P (Subgroup.zpowers x) h.zpowers_le_normalizer Subgroup.le_normalizer
    h.zpowers_le_normalizer h.coprime hne fun R hRP hxR hRne => ?_
  by_contra hPR
  refine hRne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun g hg => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact commute_of_mem_zpowers189
    (h.minimal R (lt_of_le_not_ge hRP hPR) (hxR (Subgroup.mem_zpowers x)) g hg) hy

omit [Finite Y] in
theorem mem_normalizer_commutator (h : MinimalSeven189 P x) :
    x ∈ Subgroup.normalizer ((⁅P, P⁆ : Subgroup Y) : Set Y) :=
  CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer (Subgroup.zpowers x) P P
    h.zpowers_le_normalizer h.zpowers_le_normalizer (Subgroup.mem_zpowers x)

theorem commute_of_mem_commutator (h : MinimalSeven189 P x) {g : Y} (hg : g ∈ ⁅P, P⁆) :
    x * g = g * x :=
  h.minimal ⁅P, P⁆ h.commutator_lt h.mem_normalizer_commutator g hg

theorem commutator_commutator_eq_bot (h : MinimalSeven189 P x) : ⁅⁅P, P⁆, P⁆ = ⊥ := by
  have hPP' : P ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup Y) : Set Y) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer P P P Subgroup.le_normalizer
      Subgroup.le_normalizer
  have hP'A : ⁅⁅P, P⁆, Subgroup.zpowers x⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun g hg =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        commute_of_mem_zpowers189 (h.commute_of_mem_commutator hg) hy
  have h1 : ⁅⁅P, ⁅P, P⁆⁆, Subgroup.zpowers x⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hP'A]
    exact Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_right.mp hPP')
      le_rfl
  have h2 : ⁅⁅⁅P, P⁆, Subgroup.zpowers x⁆, P⁆ = ⊥ := by
    rw [hP'A]
    exact Subgroup.commutator_bot_left P
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Subgroup.zpowers x)
    (H₂ := P) (H₃ := ⁅P, P⁆) h1 h2
  rwa [Subgroup.commutator_comm (Subgroup.zpowers x) P, h.commutator_eq_self,
    Subgroup.commutator_comm] at h3

theorem commutator_central (h : MinimalSeven189 P x) {z c : Y} (hz : z ∈ ⁅P, P⁆) (hc : c ∈ P) :
    z * c = c * z :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.commutator_commutator_eq_bot hz) c
      hc).symm

theorem mem_commutator_of_commute (h : MinimalSeven189 P x) {r : Y} (hr : r ∈ P)
    (hxr : x * r = r * x) : r ∈ ⁅P, P⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine mem_commutator_of_centralizes189 (p := 2) h.pgroup ?_ h.zpowers_le_normalizer
    h.commutator_eq_self hr fun b hb => commute_of_mem_zpowers189 hxr hb
  rw [Nat.card_zpowers, h.order]
  norm_num

theorem eq_commutator_or_eq (h : MinimalSeven189 P x) {R : Subgroup Y} (hR : ⁅P, P⁆ ≤ R)
    (hRP : R ≤ P) (hx : x ∈ Subgroup.normalizer (R : Set Y)) : R = ⁅P, P⁆ ∨ R = P := by
  by_cases hRP' : R = P
  · exact Or.inr hRP'
  refine Or.inl (le_antisymm (fun r hr => ?_) hR)
  exact h.mem_commutator_of_commute (hRP hr) (h.minimal R (lt_of_le_of_ne hRP hRP') hx r hr)

theorem sq_mem_commutator (h : MinimalSeven189 P x) {g : Y} (hg : g ∈ P) : g ^ 2 ∈ ⁅P, P⁆ := by
  have hP'norm : P ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup Y) : Set Y) :=
    Subgroup.normalizer_commutator_ge_left P P
  have hxP' := h.mem_normalizer_commutator
  let R : Subgroup Y :=
    { carrier := {y | y ∈ P ∧ y ^ 2 ∈ ⁅P, P⁆}
      one_mem' := ⟨one_mem P, by rw [one_pow]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hid : (a * b) ^ 2 = (a * ⁅b, a⁆ * a⁻¹) * a ^ 2 * b ^ 2 := by
          simp only [commutatorElement_def, sq]
          group
        rw [hid]
        refine mul_mem (mul_mem ?_ ha2) hb2
        exact (Subgroup.mem_normalizer_iff.mp (hP'norm ha) _).mp
          (Subgroup.commutator_mem_commutator hb ha)
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow]; exact inv_mem ha2⟩ }
  have hR : ∀ y, y ∈ R ↔ y ∈ P ∧ y ^ 2 ∈ ⁅P, P⁆ := fun _ => Iff.rfl
  have hxR : x ∈ Subgroup.normalizer (R : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    show y ∈ R ↔ x * y * x⁻¹ ∈ R
    rw [hR, hR, conj_pow]
    exact and_congr (Subgroup.mem_normalizer_iff.mp h.normalizes y)
      (Subgroup.mem_normalizer_iff.mp hxP' (y ^ 2))
  have hPR : ⁅P, P⁆ ≤ R := fun z hz =>
    (hR z).mpr ⟨Subgroup.commutator_le_of_le le_rfl le_rfl hz, pow_mem hz 2⟩
  rcases h.eq_commutator_or_eq hPR (fun y hy => ((hR y).mp hy).1) hxR with hRe | hRe
  · exfalso
    obtain ⟨g₀, hg₀, hg₀'⟩ := IsConcreteLE.exists_of_lt h.commutator_lt
    have key : ∀ y ∈ P, y ^ 2 ∈ ⁅P, P⁆ → y ∈ ⁅P, P⁆ := fun y hy hy2 => by
      have hyR : y ∈ R := (hR y).mpr ⟨hy, hy2⟩
      rwa [hRe] at hyR
    obtain ⟨m, hm⟩ := h.pgroup ⟨g₀, hg₀⟩
    have hm' : g₀ ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hdown : ∀ n : ℕ, g₀ ^ 2 ^ n ∈ ⁅P, P⁆ → g₀ ∈ ⁅P, P⁆ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        refine ih (key _ (pow_mem hg₀ _) ?_)
        rwa [← pow_mul, ← pow_succ]
    exact hg₀' (hdown m (by rw [hm']; exact one_mem _))
  · have hgR : g ∈ R := by rwa [hRe]
    exact ((hR g).mp hgR).2

end MinimalSeven189

end Seven

section Core

variable {H : Type*} [Group H]

theorem of_eq_one_iff189 (g : H) : Abelianization.of g = 1 ↔ g ∈ commutator H := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]

theorem of_surjective189 (v : Abelianization H) : ∃ g : H, Abelianization.of g = v :=
  QuotientGroup.induction_on v fun g => ⟨g, rfl⟩

@[expose] noncomputable def tau189 (σ : MulAut H) (k : ℕ) :
    Abelianization H →* Abelianization H :=
  Abelianization.map (σ ^ k).toMonoidHom

@[expose] noncomputable def pbar189 (σ : MulAut H) (v : Abelianization H) : Abelianization H :=
  tau189 σ 3 v * tau189 σ 1 v * v

variable (σ : MulAut H)

theorem tau189_of (k : ℕ) (g : H) :
    tau189 σ k (Abelianization.of g) = Abelianization.of ((σ ^ k) g) :=
  Abelianization.map_of _ g

theorem tau189_tau189 (k l : ℕ) (v : Abelianization H) :
    tau189 σ k (tau189 σ l v) = tau189 σ (k + l) v := by
  obtain ⟨g, rfl⟩ := of_surjective189 v
  rw [tau189_of, tau189_of, tau189_of, pow_add, MulAut.mul_apply]

theorem tau189_seven (hσ7 : σ ^ 7 = 1) (v : Abelianization H) : tau189 σ 7 v = v := by
  obtain ⟨g, rfl⟩ := of_surjective189 v
  rw [tau189_of, hσ7, MulAut.one_apply]

theorem pbar189_of (g : H) :
    pbar189 σ (Abelianization.of g) = Abelianization.of ((σ ^ 3) g * (σ ^ 1) g * g) := by
  rw [pbar189, tau189_of, tau189_of, map_mul, map_mul]

variable {σ}

theorem pow_apply_eq_of_mem_commutator189 (hσc : ∀ c ∈ commutator H, σ c = c) (k : ℕ)
    {c : H} (hc : c ∈ commutator H) : (σ ^ k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hσc c hc, ih]

theorem mem_center_of_mem_commutator189 (hcen : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H) {c : H}
    (hc : c ∈ commutator H) : c ∈ Subgroup.center H := by
  have hle : commutator H ≤ Subgroup.center H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hcen a b
  exact hle hc

theorem mul_self_eq_one189 (hsq : ∀ g : H, g ^ 2 ∈ commutator H) (v : Abelianization H) :
    v * v = 1 := by
  obtain ⟨g, rfl⟩ := of_surjective189 v
  rw [← map_mul, ← sq, of_eq_one_iff189]
  exact hsq g

theorem eq_one_of_tau189_eq [Finite H] (hH : IsPGroup 2 H) (hσ7 : σ ^ 7 = 1)
    (hσc : ∀ c ∈ commutator H, σ c = c) (hfix : ∀ g : H, σ g = g → g ∈ commutator H)
    {v : Abelianization H} (hv : tau189 σ 1 v = v) : v = 1 := by
  obtain ⟨g, rfl⟩ := of_surjective189 v
  rw [tau189_of, pow_one] at hv
  set c := g⁻¹ * σ g with hcdef
  have hc : c ∈ commutator H := by
    rw [← of_eq_one_iff189, hcdef, map_mul, map_inv, hv, inv_mul_cancel]
  have hσg : σ g = g * c := by rw [hcdef]; group
  have hk : ∀ k : ℕ, (σ ^ k) g = g * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hσg, map_pow, hσc c hc, mul_assoc, ← pow_succ']
  have h7 := hk 7
  rw [hσ7, MulAut.one_apply] at h7
  have hc7 : c ^ 7 = 1 := by
    have := congrArg (g⁻¹ * ·) h7
    simpa using this.symm
  obtain ⟨m, hm⟩ := hH c
  have hc1 : c = 1 := by
    have h := (pow_gcd_eq_one (a := c) (m := 7) (n := 2 ^ m)).mpr ⟨hc7, hm⟩
    rwa [show Nat.gcd 7 (2 ^ m) = 1 from Nat.Coprime.pow_right m (by norm_num), pow_one] at h
  have hσg' : σ g = g := by rw [hσg, hc1, mul_one]
  exact (of_eq_one_iff189 g).mpr (hfix g hσg')

theorem tau189_four_six189 (hV : ∀ v : Abelianization H, v * v = 1)
    {w : Abelianization H} (hw : pbar189 σ w = 1) :
    tau189 σ 4 w * tau189 σ 6 w * w = tau189 σ 1 w := by
  have hinv : ∀ v : Abelianization H, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_left (hV v)
  rw [pbar189] at hw
  have e3 : tau189 σ 3 w = tau189 σ 1 w * w := by
    rw [← hinv (tau189 σ 1 w * w)]
    exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hw)
  have hw3 := congrArg (tau189 σ 3) hw
  rw [map_mul, map_mul, tau189_tau189, tau189_tau189, map_one] at hw3
  have e6 : tau189 σ 6 w = tau189 σ 4 w * tau189 σ 3 w := by
    rw [← hinv (tau189 σ 4 w * tau189 σ 3 w)]
    exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hw3)
  rw [e6, e3]
  calc tau189 σ 4 w * (tau189 σ 4 w * (tau189 σ 1 w * w)) * w =
      (tau189 σ 4 w * tau189 σ 4 w) * tau189 σ 1 w * (w * w) := by ac_rfl
    _ = tau189 σ 1 w := by rw [hV, hV, one_mul, mul_one]

theorem pbar189_pbar189_inv (hσ7 : σ ^ 7 = 1) (hV : ∀ v : Abelianization H, v * v = 1)
    (v : Abelianization H) :
    pbar189 σ (tau189 σ 4 v * tau189 σ 6 v * v) =
      v * tau189 σ 1 v * tau189 σ 2 v * tau189 σ 3 v * tau189 σ 4 v * tau189 σ 5 v *
        tau189 σ 6 v := by
  have h7 : tau189 σ 7 v = v := tau189_seven σ hσ7 v
  have h9 : tau189 σ 9 v = tau189 σ 2 v := by
    rw [← tau189_tau189 σ 2 7, h7]
  rw [pbar189, map_mul, map_mul, map_mul, map_mul, tau189_tau189, tau189_tau189, tau189_tau189,
    tau189_tau189]
  norm_num only
  rw [h7, h9]
  calc v * tau189 σ 2 v * tau189 σ 3 v * (tau189 σ 5 v * v * tau189 σ 1 v) *
        (tau189 σ 4 v * tau189 σ 6 v * v) =
      (v * v) * (v * tau189 σ 1 v * tau189 σ 2 v * tau189 σ 3 v * tau189 σ 4 v *
        tau189 σ 5 v * tau189 σ 6 v) := by ac_rfl
    _ = _ := by rw [hV, one_mul]

theorem norm189_eq_one [Finite H] (hH : IsPGroup 2 H) (hσ7 : σ ^ 7 = 1)
    (hσc : ∀ c ∈ commutator H, σ c = c) (hfix : ∀ g : H, σ g = g → g ∈ commutator H)
    (v : Abelianization H) :
    v * tau189 σ 1 v * tau189 σ 2 v * tau189 σ 3 v * tau189 σ 4 v * tau189 σ 5 v *
      tau189 σ 6 v = 1 := by
  refine eq_one_of_tau189_eq hH hσ7 hσc hfix ?_
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, tau189_tau189, tau189_tau189,
    tau189_tau189, tau189_tau189, tau189_tau189, tau189_tau189]
  norm_num only
  rw [tau189_seven σ hσ7]
  ac_rfl

theorem commutator_eq_one_of_pbar189 (hσ7 : σ ^ 7 = 1)
    (hcen : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H) (hσc : ∀ c ∈ commutator H, σ c = c)
    (hsq : ∀ g : H, g ^ 2 ∈ commutator H) {u w : H}
    (hu : pbar189 σ (Abelianization.of u) = 1) (hw : pbar189 σ (Abelianization.of w) = 1) :
    ⁅u, σ w⁆ = 1 := by
  have hV := mul_self_eq_one189 hsq
  have hcm : ∀ a b : H, ⁅a, b⁆ ∈ commutator H := fun a b => by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hshift : ∀ k : ℕ, k ≤ 7 → ∀ a y : H, ⁅(σ ^ k) a, y⁆ = ⁅a, (σ ^ (7 - k)) y⁆ := by
    intro k hk a y
    have h1 : (σ ^ k) ⁅a, (σ ^ (7 - k)) y⁆ = ⁅(σ ^ k) a, y⁆ := by
      rw [map_commutatorElement, ← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hk, hσ7,
        MulAut.one_apply]
    rw [← h1, pow_apply_eq_of_mem_commutator189 hσc k (hcm _ _)]
  have he : (σ ^ 3) u * (σ ^ 1) u * u ∈ commutator H := by
    rw [← of_eq_one_iff189, ← pbar189_of]
    exact hu
  have hzy := Baer.commutator_eq_one_of_mem_center_left
    (mem_center_of_mem_commutator189 hcen he) w
  rw [Baer.commutator_mul_left hcen, Baer.commutator_mul_left hcen, hshift 3 (by norm_num),
    hshift 1 (by norm_num), ← Baer.commutator_mul_right hcen, ← Baer.commutator_mul_right hcen]
    at hzy
  norm_num only at hzy
  set y := (σ ^ 4) w * (σ ^ 6) w * w with hy
  have hwy : Abelianization.of y = Abelianization.of ((σ ^ 1) w) := by
    rw [hy, map_mul, map_mul, ← tau189_of, ← tau189_of, ← tau189_of]
    exact tau189_four_six189 hV hw
  set c := ((σ ^ 1) w)⁻¹ * y with hcdef
  have hc : c ∈ commutator H := by
    rw [← of_eq_one_iff189, hcdef, map_mul, map_inv, hwy, inv_mul_cancel]
  have hyc : y = (σ ^ 1) w * c := by rw [hcdef]; group
  rw [hyc, Baer.commutator_mul_right hcen,
    Baer.commutator_eq_one_of_mem_center_right (mem_center_of_mem_commutator189 hcen hc),
    mul_one, pow_one] at hzy
  exact hzy

@[expose] noncomputable def wSub189 (σ : MulAut H) : Subgroup H :=
  ((tau189 σ 3 * tau189 σ 1 * MonoidHom.id (Abelianization H)).ker).comap Abelianization.of

theorem mem_wSub189 {g : H} :
    g ∈ wSub189 σ ↔ pbar189 σ (Abelianization.of g) = 1 := by
  rw [wSub189, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mul_apply,
    MonoidHom.id_apply]
  rfl

theorem apply_mem_wSub189 {g : H} (hg : g ∈ wSub189 σ) : σ g ∈ wSub189 σ := by
  rw [mem_wSub189] at hg ⊢
  have e : Abelianization.of (σ g) = tau189 σ 1 (Abelianization.of g) := by
    rw [tau189_of, pow_one]
  have h1 : tau189 σ 1 (pbar189 σ (Abelianization.of g)) = 1 := by rw [hg, map_one]
  rw [pbar189, map_mul, map_mul, tau189_tau189, tau189_tau189] at h1
  rw [e, pbar189, tau189_tau189, tau189_tau189]
  exact h1

theorem ker_pbar_trivial_or189 [Finite H] (hσ7 : σ ^ 7 = 1)
    (hcen : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H) (hσc : ∀ c ∈ commutator H, σ c = c)
    (hsq : ∀ g : H, g ^ 2 ∈ commutator H) (hfix : ∀ g : H, σ g = g → g ∈ commutator H)
    (hmin : ∀ W : Subgroup H, (∀ g ∈ W, σ g ∈ W) → (∃ g ∈ W, σ g ≠ g) → W = ⊤) :
    (∀ v : Abelianization H, pbar189 σ v = 1 → v = 1) ∨ commutator H = ⊥ := by
  by_cases hW : ∃ g ∈ wSub189 σ, σ g ≠ g
  · right
    have hWtop := hmin _ (fun g hg => apply_mem_wSub189 hg) hW
    have hall : ∀ g : H, pbar189 σ (Abelianization.of g) = 1 := fun g =>
      mem_wSub189.mp (hWtop ▸ Subgroup.mem_top g)
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hb : σ ((σ ^ 6) b) = b := by
      rw [← MulAut.mul_apply, ← pow_succ', hσ7, MulAut.one_apply]
    rw [Subgroup.mem_bot, ← hb]
    exact commutator_eq_one_of_pbar189 hσ7 hcen hσc hsq (hall a) (hall _)
  · left
    push Not at hW
    intro v hv
    obtain ⟨g, rfl⟩ := of_surjective189 v
    exact (of_eq_one_iff189 g).mpr (hfix g (hW g (mem_wSub189.mpr hv)))

theorem pbar189_inv (hσ7 : σ ^ 7 = 1) (v : Abelianization H) :
    pbar189 σ⁻¹ v = tau189 σ 4 v * tau189 σ 6 v * v := by
  have e4 : σ⁻¹ ^ 3 = σ ^ 4 := by
    rw [inv_pow, inv_eq_of_mul_eq_one_left (by rw [← pow_add]; exact hσ7)]
  have e6 : σ⁻¹ ^ 1 = σ ^ 6 := by
    rw [pow_one, inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact hσ7)]
  rw [pbar189, tau189, tau189, e4, e6]
  rfl

theorem commutator_eq_bot_of_seven189 [Finite H] (hH : IsPGroup 2 H) (hσ7 : σ ^ 7 = 1)
    (hcen : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H) (hσc : ∀ c ∈ commutator H, σ c = c)
    (hsq : ∀ g : H, g ^ 2 ∈ commutator H) (hfix : ∀ g : H, σ g = g → g ∈ commutator H)
    (hmin : ∀ W : Subgroup H, (∀ g ∈ W, σ g ∈ W) → (∃ g ∈ W, σ g ≠ g) → W = ⊤)
    (hne : commutator H ≠ ⊤) : commutator H = ⊥ := by
  have hV := mul_self_eq_one189 hsq
  have hσinv : ∀ g : H, σ⁻¹ g = g → σ g = g := fun g hg => by
    have := congrArg σ hg
    rwa [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, eq_comm] at this
  have h76 : σ * σ ^ 6 = 1 := by rw [← pow_succ']; exact hσ7
  have hσ6 : (σ⁻¹) ^ 6 = σ := by
    rw [inv_pow, inv_eq_of_mul_eq_one_left h76]
  have hσ7' : (σ⁻¹) ^ 7 = 1 := by rw [inv_pow, hσ7, inv_one]
  have hσc' : ∀ c ∈ commutator H, σ⁻¹ c = c := fun c hc => by
    have := congrArg (fun y => (σ⁻¹ : MulAut H) y) (hσc c hc)
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, eq_comm] at this
  have hfix' : ∀ g : H, σ⁻¹ g = g → g ∈ commutator H := fun g hg => hfix g (hσinv g hg)
  have hmin' : ∀ W : Subgroup H, (∀ g ∈ W, σ⁻¹ g ∈ W) → (∃ g ∈ W, σ⁻¹ g ≠ g) → W = ⊤ := by
    intro W hW hne'
    have hpow : ∀ k : ℕ, ∀ g ∈ W, (σ⁻¹ ^ k) g ∈ W := by
      intro k
      induction k with
      | zero => intro g hg; exact hg
      | succ k ih => intro g hg; rw [pow_succ', MulAut.mul_apply]; exact hW _ (ih g hg)
    refine hmin W (fun g hg => hσ6 ▸ hpow 6 g hg) ?_
    obtain ⟨g, hg, hgne⟩ := hne'
    exact ⟨g, hg, fun h' => hgne (by
      have := congrArg (fun y => (σ⁻¹ : MulAut H) y) h'
      rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, eq_comm] at this)⟩
  rcases ker_pbar_trivial_or189 hσ7 hcen hσc hsq hfix hmin with h1 | h1
  · rcases ker_pbar_trivial_or189 hσ7' hcen hσc' hsq hfix' hmin' with h2 | h2
    · exfalso
      apply hne
      rw [eq_top_iff]
      intro g _
      rw [← of_eq_one_iff189]
      apply h2
      apply h1
      rw [pbar189_inv hσ7, pbar189_pbar189_inv hσ7 hV]
      exact norm189_eq_one hH hσ7 hσc hfix _
    · exact h2
  · exact h1

end Core

section Final

variable {Y : Type*} [Group Y] [Finite Y]

namespace MinimalSeven189

variable {Q : Subgroup Y} {x : Y}

omit [Finite Y] in
theorem mem_commutator_iff (g : Q) : g ∈ commutator Q ↔ (g : Y) ∈ ⁅Q, Q⁆ := by
  rw [← Subgroup.map_subtype_commutator]
  constructor
  · intro hg
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    rwa [← Subtype.ext hgg']

theorem commutator_eq_bot (h : MinimalSeven189 Q x) : ⁅Q, Q⁆ = ⊥ := by
  set σ : MulAut Q := Q.normalizerMonoidHom ⟨x, h.normalizes⟩ with hσdef
  have hσk : ∀ (k : ℕ) (g : Q), (((σ ^ k) g : Q) : Y) = x ^ k * g * (x ^ k)⁻¹ := by
    intro k g
    rw [hσdef, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hσ : ∀ g : Q, ((σ g : Q) : Y) = x * g * x⁻¹ := fun g => by
    simpa using hσk 1 g
  have hx7 : x ^ 7 = 1 := by rw [← h.order]; exact pow_orderOf_eq_one x
  have hσ7 : σ ^ 7 = 1 := by
    ext g
    rw [hσk, hx7, MulAut.one_apply]
    simp
  have hcen : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q := by
    intro a b
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hab : ((⁅a, b⁆ : Q) : Y) ∈ ⁅Q, Q⁆ := by
      rw [← mem_commutator_iff, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact (h.commutator_central hab g.2).symm
  have hσc : ∀ c ∈ commutator Q, σ c = c := by
    intro c hc
    apply Subtype.ext
    rw [hσ, h.commute_of_mem_commutator ((mem_commutator_iff c).mp hc), mul_inv_cancel_right]
  have hsq : ∀ g : Q, g ^ 2 ∈ commutator Q := fun g =>
    (mem_commutator_iff _).mpr (by simpa using h.sq_mem_commutator g.2)
  have hfix : ∀ g : Q, σ g = g → g ∈ commutator Q := by
    intro g hg
    refine (mem_commutator_iff g).mpr (h.mem_commutator_of_commute g.2 ?_)
    have := congrArg Subtype.val hg
    rw [hσ] at this
    calc x * g = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [this]
  have hmin : ∀ W : Subgroup Q, (∀ g ∈ W, σ g ∈ W) → (∃ g ∈ W, σ g ≠ g) → W = ⊤ := by
    intro W hW hne
    have hpow : ∀ k : ℕ, ∀ g ∈ W, (σ ^ k) g ∈ W := by
      intro k
      induction k with
      | zero => intro g hg; exact hg
      | succ k ih => intro g hg; rw [pow_succ', MulAut.mul_apply]; exact hW _ (ih g hg)
    have hx6 : x ^ 6 = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx7]
    have hxN : x ∈ Subgroup.normalizer ((W.map Q.subtype : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨σ g, hW g hg, hσ g⟩
      · rintro ⟨g, hg, hgy⟩
        refine ⟨(σ ^ 6) g, hpow 6 g hg, ?_⟩
        change (((σ ^ 6) g : Q) : Y) = y
        rw [hσk, hx6, inv_inv]
        change ((g : Q) : Y) = x * y * x⁻¹ at hgy
        rw [hgy]
        group
    by_contra hWtop
    have hlt : W.map Q.subtype < Q := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le W) fun heq => hWtop ?_
      apply Subgroup.map_injective Q.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    obtain ⟨g, hg, hgne⟩ := hne
    exact hgne (Subtype.ext (by
      rw [hσ, h.minimal _ hlt hxN g ⟨g, hg, rfl⟩, mul_inv_cancel_right]))
  have hne : commutator Q ≠ ⊤ := by
    intro htop
    have hlt := h.commutator_lt
    rw [← Subgroup.map_subtype_commutator, htop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hlt
    exact lt_irrefl _ hlt
  have hbot := commutator_eq_bot_of_seven189 h.pgroup hσ7 hcen hσc hsq hfix hmin hne
  rw [← Subgroup.map_subtype_commutator, hbot, Subgroup.map_bot]

end MinimalSeven189

end Final

theorem sevenRank189 : SevenRank189 := by
  intro Y _ _ P x hP hxN hx7 hnc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q, hQP, hQmin⟩ := Finite.exists_le_minimal
    (p := fun R : Subgroup Y => x ∈ Subgroup.normalizer (R : Set Y) ∧
      ¬ R ≤ Subgroup.centralizer ({x} : Set Y)) ⟨hxN, hnc⟩
  have h : MinimalSeven189 Q x := by
    refine ⟨hP.to_le hQP, hQmin.prop.1, hx7, ?_, ?_⟩
    · obtain ⟨g, hg, hgC⟩ := Set.not_subset.mp hQmin.prop.2
      refine ⟨g, hg, fun hxg => hgC ?_⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hxg.symm
    · intro R hR hxR g hg
      by_contra hxg
      have hRC : ¬ R ≤ Subgroup.centralizer ({x} : Set Y) := fun hle => hxg
        ((Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm)
      exact hR.not_ge (hQmin.le_of_le ⟨hxR, hRC⟩ hR.le)
  have hbot := h.commutator_eq_bot
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have hab : ⁅a, b⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact hab
  have hsq : ∀ g ∈ Q, g ^ 2 = 1 := fun g hg => by
    have := h.sq_mem_commutator hg
    rwa [hbot, Subgroup.mem_bot] at this
  have hfpf : ∀ g ∈ Q, x * g = g * x → g = 1 := fun g hg hxg => by
    have := h.mem_commutator_of_commute hg hxg
    rwa [hbot, Subgroup.mem_bot] at this
  let _ : MulAction ↥(Subgroup.zpowers x) ↥Q :=
    MulAction.compHom ↥Q (Q.normalizerMonoidHom.comp (Subgroup.inclusion h.zpowers_le_normalizer))
  have hsmul : ∀ (b : ↥(Subgroup.zpowers x)) (g : ↥Q), ((b • g : ↥Q) : Y) = b * g * (b : Y)⁻¹ :=
    fun b g => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hfp : MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥Q = {1} := by
    ext g
    rw [Set.mem_singleton_iff]
    constructor
    · intro hg
      have h1 := congrArg Subtype.val (hg ⟨x, Subgroup.mem_zpowers x⟩)
      rw [hsmul] at h1
      apply Subtype.ext
      refine hfpf g g.2 ?_
      calc x * g = x * g * x⁻¹ * x := by group
        _ = g * x := by rw [h1]
    · rintro rfl b
      apply Subtype.ext
      rw [hsmul]
      simp
  have hmod := h.sevenGroup.card_modEq_card_fixedPoints ↥Q
  have hcard1 : Nat.card ↑({1} : Set ↥Q) = 1 := Nat.card_unique
  rw [hfp, hcard1] at hmod
  obtain ⟨k, hk⟩ := h.pgroup.exists_card_eq
  rw [hk] at hmod
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact h.ne_bot (Subgroup.card_eq_one.mp hk)
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl <;> simp [Nat.ModEq] at hmod
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ 3 ∣ Nat.card ↥Q by rw [hk]; exact pow_dvd_pow 2 hk3)
  refine ⟨F.map Q.subtype, (Subgroup.map_subtype_le F).trans hQP, ?_, ?_⟩
  · have hc : ∀ a b : ↥(F.map Q.subtype), a * b = b * a := fun a b => by
      apply Subtype.ext
      obtain ⟨a', -, ha'⟩ := a.2
      obtain ⟨b', -, hb'⟩ := b.2
      change (a : Y) * b = b * a
      rw [← ha', ← hb']
      exact hcomm _ a'.2 _ b'.2
    have he : ∀ a : ↥(F.map Q.subtype), a ^ 2 = 1 := fun a => by
      apply Subtype.ext
      obtain ⟨a', -, ha'⟩ := a.2
      change (a : Y) ^ 2 = 1
      rw [← ha']
      exact hsq _ a'.2
    exact
      { toIsMulCommutative := ⟨⟨hc⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one he }
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hF]
    norm_num

theorem step189TwoRank_of_item184 (h184 : Item184_1) (h186 : Item186H) : Step189TwoRank :=
  step189TwoRank_of h184 h186 sevenRank189

end CFSG.RankThree.PartTwo.Sec18
