module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator
public import CFSG.SignalizerFunctorTheorem.MinimalAction.AbelianCase
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

section Aux

variable {G : Type*} [Group G]

private theorem commute_of_mem_zpowers {a g y : G} (hg : a * g = g * a)
    (hy : y ∈ Subgroup.zpowers a) : y * g = g * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left hg k).eq

private theorem commutator_le_self (P : Subgroup G) : ⁅P, P⁆ ≤ P :=
  Subgroup.commutator_le_of_le le_rfl le_rfl

private theorem zpowers_cube_le (x : G) : Subgroup.zpowers (x ^ 3) ≤ Subgroup.zpowers x :=
  Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers x) 3)

private theorem zpowers_le_normalizer_cube (x : G) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers (x ^ 3) : Set G) := by
  have hconj : ∀ b ∈ Subgroup.zpowers x, ∀ y ∈ Subgroup.zpowers (x ^ 3), b * y * b⁻¹ = y := by
    intro b hb y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (zpowers_cube_le x hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.zpow_zpow_self x k n).eq
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => by rwa [hconj b hb a ha], fun ha => ?_⟩
  have h1 := hconj b⁻¹ (inv_mem hb) _ ha
  have h2 : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
  have h3 : a = b * a * b⁻¹ := h2.symm.trans h1
  rwa [← h3] at ha

private def abelianizationEnd (P : Subgroup G) :
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

end Aux

variable {G : Type*} [Group G] [Finite G]

structure MinimalThree (P : Subgroup G) (x : G) : Prop where
  pgroup : IsPGroup 2 P
  normalizes : x ∈ Subgroup.normalizer (P : Set G)
  threeGroup : IsPGroup 3 (Subgroup.zpowers x)
  nontrivial : ∃ g ∈ P, x ^ 3 * g ≠ g * x ^ 3
  minimal : ∀ R : Subgroup G, R < P → x ∈ Subgroup.normalizer (R : Set G) →
    ∀ g ∈ R, x ^ 3 * g = g * x ^ 3

private theorem mem_commutator_of_centralizes {p : ℕ} [Fact p.Prime] {P A : Subgroup G}
    (hP : IsPGroup p P) (hA : Nat.Coprime p (Nat.card A))
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hPA : ⁅P, A⁆ = P) {r : G} (hr : r ∈ P)
    (hcent : ∀ b ∈ A, b * r = r * b) : r ∈ ⁅P, P⁆ := by
  let ρ : A →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  let φ : A →* AddMonoid.End (Additive (Abelianization P)) := (abelianizationEnd P).comp ρ
  have hφ : ∀ (b : A) (g : P), φ b (Additive.ofMul (Abelianization.of g)) =
      Additive.ofMul (Abelianization.of (ρ b g)) := fun _ _ => rfl
  have hρ : ∀ (b : A) (g : P), ((ρ b g : P) : G) = (b : G) * g * (b : G)⁻¹ := fun _ _ => rfl
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

namespace MinimalThree

variable {P : Subgroup G} {x : G}

omit [Finite G] in
private theorem zpowers_le_normalizer (h : MinimalThree P x) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
  Subgroup.zpowers_le.mpr h.normalizes

omit [Finite G] in
private theorem cube_le_normalizer (h : MinimalThree P x) :
    Subgroup.zpowers (x ^ 3) ≤ Subgroup.normalizer (P : Set G) :=
  (zpowers_cube_le x).trans h.zpowers_le_normalizer

omit [Finite G] in
private theorem threeGroup_cube (h : MinimalThree P x) : IsPGroup 3 (Subgroup.zpowers (x ^ 3)) :=
  h.threeGroup.to_le (zpowers_cube_le x)

omit [Finite G] in
private theorem ne_bot (h : MinimalThree P x) : P ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hg, hne⟩ := h.nontrivial
  rw [hbot, Subgroup.mem_bot] at hg
  exact hne (by rw [hg, mul_one, one_mul])

private theorem commutator_lt (h : MinimalThree P x) : ⁅P, P⁆ < P :=
  GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups P P h.pgroup h.pgroup
    Subgroup.le_normalizer h.ne_bot

theorem commutator_eq_self (h : MinimalThree P x) :
    ⁅P, Subgroup.zpowers (x ^ 3)⁆ = P := by
  have hne : ⁅P, Subgroup.zpowers (x ^ 3)⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨g, hg, hne⟩ := h.nontrivial
    exact hne (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hg) _ (Subgroup.mem_zpowers _))
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers (x ^ 3))) (Nat.card P) := by
    obtain ⟨a, ha⟩ := h.threeGroup_cube.exists_card_eq
    obtain ⟨b, hb⟩ := h.pgroup.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  refine GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime (Subgroup.zpowers x) P
    (Subgroup.zpowers (x ^ 3)) h.zpowers_le_normalizer (zpowers_le_normalizer_cube x)
    h.cube_le_normalizer hcop hne fun R hRP hxR hRne => ?_
  by_contra hPR
  refine hRne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun g hg => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact commute_of_mem_zpowers
    (h.minimal R (lt_of_le_not_ge hRP hPR) (hxR (Subgroup.mem_zpowers x)) g hg) hy

private theorem commutator_commutator_eq_bot (h : MinimalThree P x) : ⁅⁅P, P⁆, P⁆ = ⊥ := by
  have hPP' : P ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    GorensteinWalter.le_normalizer_commutator_of_le_normalizer P P P Subgroup.le_normalizer
      Subgroup.le_normalizer
  have hxP' : x ∈ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    GorensteinWalter.le_normalizer_commutator_of_le_normalizer (Subgroup.zpowers x) P P
      h.zpowers_le_normalizer h.zpowers_le_normalizer (Subgroup.mem_zpowers x)
  have hP'A : ⁅⁅P, P⁆, Subgroup.zpowers (x ^ 3)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun g hg =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        commute_of_mem_zpowers (h.minimal ⁅P, P⁆ h.commutator_lt hxP' g hg) hy
  have h1 : ⁅⁅P, ⁅P, P⁆⁆, Subgroup.zpowers (x ^ 3)⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hP'A]
    exact Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_right.mp hPP')
      le_rfl
  have h2 : ⁅⁅⁅P, P⁆, Subgroup.zpowers (x ^ 3)⁆, P⁆ = ⊥ := by
    rw [hP'A]
    exact Subgroup.commutator_bot_left P
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Subgroup.zpowers (x ^ 3))
    (H₂ := P) (H₃ := ⁅P, P⁆) h1 h2
  rwa [Subgroup.commutator_comm (Subgroup.zpowers (x ^ 3)) P, h.commutator_eq_self,
    Subgroup.commutator_comm] at h3

theorem commutator_central (h : MinimalThree P x) {z c : G} (hz : z ∈ ⁅P, P⁆) (hc : c ∈ P) :
    z * c = c * z :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.commutator_commutator_eq_bot hz) c hc).symm

theorem eq_commutator_or_eq (h : MinimalThree P x) {R : Subgroup G} (hR : ⁅P, P⁆ ≤ R)
    (hRP : R ≤ P) (hx : x ∈ Subgroup.normalizer (R : Set G)) : R = ⁅P, P⁆ ∨ R = P := by
  by_cases hRP' : R = P
  · exact Or.inr hRP'
  refine Or.inl (le_antisymm (fun r hr => ?_) hR)
  have hfix := h.minimal R (lt_of_le_of_ne hRP hRP') hx r hr
  refine mem_commutator_of_centralizes (p := 2) h.pgroup ?_ h.cube_le_normalizer
    h.commutator_eq_self (hRP hr) fun b hb => commute_of_mem_zpowers hfix hb
  obtain ⟨k, hk⟩ := h.threeGroup_cube.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem center_le_commutator (h : MinimalThree P x) (hP' : ⁅P, P⁆ ≠ ⊥) {z : G} (hz : z ∈ P)
    (hzc : ∀ c ∈ P, z * c = c * z) : z ∈ ⁅P, P⁆ := by
  let Zc : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G)
  have hP'Z : ⁅P, P⁆ ≤ Zc := fun z' hz' =>
    Subgroup.mem_inf.mpr ⟨commutator_le_self P hz',
      Subgroup.mem_centralizer_iff.mpr fun c hc => (h.commutator_central hz' hc).symm⟩
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ y ∈ Zc, g * y * g⁻¹ ∈ Zc := by
    intro g hg y hy
    obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' : g⁻¹ * c * g ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) c).mp hc
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hc'
    calc c * (g * y * g⁻¹) = g * ((g⁻¹ * c * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * c * g)) * g⁻¹ := by rw [hcomm]
      _ = g * y * g⁻¹ * c := by group
  have hxZ : x ∈ Subgroup.normalizer (Zc : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj x h.normalizes y hy, fun hy => ?_⟩
    have h1 := hconj x⁻¹ (inv_mem h.normalizes) _ hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h2] at h1
  rcases h.eq_commutator_or_eq hP'Z inf_le_left hxZ with hZ | hZ
  · have hzZ : z ∈ Zc := Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_iff.mpr fun c hc =>
      (hzc c hc).symm⟩
    rwa [hZ] at hzZ
  · refine absurd ?_ hP'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    have hgZ : g ∈ Zc := by rwa [hZ]
    exact (Subgroup.mem_inf.mp hgZ).2

theorem sq_mem_commutator (h : MinimalThree P x) {g : G} (hg : g ∈ P) : g ^ 2 ∈ ⁅P, P⁆ := by
  have hP'norm : P ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left P P
  have hxP' : x ∈ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    GorensteinWalter.le_normalizer_commutator_of_le_normalizer (Subgroup.zpowers x) P P
      h.zpowers_le_normalizer h.zpowers_le_normalizer (Subgroup.mem_zpowers x)
  let R : Subgroup G :=
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
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    show y ∈ R ↔ x * y * x⁻¹ ∈ R
    rw [hR, hR, conj_pow]
    exact and_congr (Subgroup.mem_normalizer_iff.mp h.normalizes y)
      (Subgroup.mem_normalizer_iff.mp hxP' (y ^ 2))
  have hPR : ⁅P, P⁆ ≤ R := fun z hz => (hR z).mpr ⟨commutator_le_self P hz, pow_mem hz 2⟩
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

theorem sq_eq_one_of_mem_commutator (h : MinimalThree P x) {z : G} (hz : z ∈ ⁅P, P⁆) :
    z ^ 2 = 1 := by
  let T : Subgroup G :=
    { carrier := {y | y ∈ ⁅P, P⁆ ∧ y ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hcomm : Commute a b := h.commutator_central ha (commutator_le_self P hb)
        rw [hcomm.mul_pow, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hT : ∀ y, y ∈ T ↔ y ∈ ⁅P, P⁆ ∧ y ^ 2 = 1 := fun _ => Iff.rfl
  have hle : ⁅P, P⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine (hT _).mpr ⟨Subgroup.commutator_mem_commutator ha hb, ?_⟩
    have h1 : ⁅a * a, b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm, ← sq]
      exact h.commutator_central (h.sq_mem_commutator ha) hb
    have h2 := commutatorElement_mul_left_eq_conj_mul a a b
    have h3 : a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (h.commutator_central (Subgroup.commutator_mem_commutator ha hb) ha).symm
    rw [h1, h3] at h2
    rw [sq]
    exact h2.symm
  exact ((hT z).mp (hle hz)).2

end MinimalThree

end CFSG.SignalizerFunctorTheorem.MinimalAction
