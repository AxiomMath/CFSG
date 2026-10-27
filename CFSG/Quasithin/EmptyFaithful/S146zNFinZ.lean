module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinY
public import CFSG.Quasithin.EmptyFaithful.S146zNFinS
public import CFSG.Quasithin.EmptyFaithful.S146zNFinT
public import CFSG.Quasithin.EmptyFaithful.S146zNFinW
public import CFSG.Quasithin.EmptyFaithful.S146zNFinX

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem Setup.isU_of_isT (h : Setup ρ) (α : MulAut A6)
    (hα : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ α x) {g : A6} (hg : IsT g) :
    IsU (α g) := by
  obtain ⟨h3, h1, hf⟩ := hg
  have hα3 : α g ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hα1 : α g ≠ 1 := fun e => h1 (α.injective (e.trans (map_one α).symm))
  refine ⟨hα3, hα1, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨i, hi⟩ := hno
  have := h.fc_fuse α hα g h3 h1
  apply this
  rw [fc_T (α g) ⟨hα3, hα1, ⟨i, hi⟩⟩, fc_T g ⟨h3, h1, hf⟩]

theorem Setup.isT_of_isU (h : Setup ρ) (α : MulAut A6)
    (hα : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ α x) {g : A6} (hg : IsU g) :
    IsT (α g) := by
  obtain ⟨h3, h1, hn⟩ := hg
  have hα3 : α g ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hα1 : α g ≠ 1 := fun e => h1 (α.injective (e.trans (map_one α).symm))
  refine ⟨hα3, hα1, ?_⟩
  by_contra hno
  push Not at hno
  have := h.fc_fuse α hα g h3 h1
  apply this
  rw [fc_U (α g) ⟨hα3, hα1, hno⟩, fc_U g ⟨h3, h1, hn⟩]

theorem Setup.hasU_of_hasT (h : Setup ρ) (α : MulAut A6)
    (hα : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ α x) {c d : A6} (hT : HasT c d) :
    HasU (α c) (α d) := by
  obtain ⟨g, hg, hN⟩ := hT
  exact ⟨α g, h.isU_of_isT α hα hg, NormA.map α hN⟩

theorem Setup.hasT_of_hasU (h : Setup ρ) (α : MulAut A6)
    (hα : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ α x) {c d : A6} (hU : HasU c d) :
    HasT (α c) (α d) := by
  obtain ⟨g, hg, hN⟩ := hU
  exact ⟨α g, h.isT_of_isU α hα hg, NormA.map α hN⟩


theorem bxA_facts : bxA * u2A = u1A ∧ bxA * u4A = u3A ∧ bxA * u2A = u2A * bxA ∧ bxA * u4A = u4A * bxA ∧
    bxA ≠ u2A ∧ bxA ≠ u4A ∧ bxA ≠ 1 ∧ u2A * u2A = 1 ∧ u4A * u4A = 1 ∧ bxA * bxA = 1 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, -, -, p10, p11⟩ := prod_facts
  refine ⟨Subtype.ext p1, Subtype.ext p2, Subtype.ext p3, Subtype.ext p4, fun e => p5 (congrArg Subtype.val e),
    fun e => p6 (congrArg Subtype.val e), fun e => p7 (congrArg Subtype.val e), Subtype.ext p10,
    Subtype.ext p11, Subtype.ext bx_sq⟩

theorem Setup.eqv_B (h : Setup ρ) {c d : A6} (hB : FamB c d) (heq : fixSub (ρ c) = fixSub (ρ d)) :
    fixSub (ρ bxA) = fixSub (ρ u1A) := by
  obtain ⟨r, e1, e2⟩ := hB
  have h1 := fixSub_eq_conj r heq
  rw [e1] at h1
  obtain ⟨f1, -, f3, -, f5, -, f7, f8, -, f10⟩ := bxA_facts
  rcases e2 with e2 | e2
  · rw [e2] at h1
    exact h1
  · rw [e2] at h1
    have := h.eqv_mul f5 f7 f10 f8 f3 h1
    rwa [f1] at this

theorem Setup.eqv_A (h : Setup ρ) {c d : A6} (hA : FamA c d) (heq : fixSub (ρ c) = fixSub (ρ d)) :
    fixSub (ρ bxA) = fixSub (ρ u3A) := by
  obtain ⟨r, e1, e2⟩ := hA
  have h1 := fixSub_eq_conj r heq
  rw [e1] at h1
  obtain ⟨-, f2, -, f4, -, f6, f7, -, f9, f10⟩ := bxA_facts
  rcases e2 with e2 | e2
  · rw [e2] at h1
    exact h1
  · rw [e2] at h1
    have := h.eqv_mul f6 f7 f10 f9 f4 h1
    rwa [f2] at this


theorem Setup.false_of_chain (h : Setup ρ)
    (key : fixSub (ρ x0A6) = fixSub (ρ (y0A6 * x0A6 * y0A6⁻¹))) : False := by
  set U := fixSub (ρ x0A6) with hU
  have hcard : Nat.card U = 4 := h.card_fixSub_invol x0A6_ne_one x0A6_sq
  let H : Subgroup A6 :=
    { carrier := {g | ∀ w : W, w ∈ U ↔ ρ g w ∈ U}
      mul_mem' := fun {a b} ha hb w => by
        show w ∈ U ↔ ρ (a * b) w ∈ U
        rw [map_mul, MulAut.mul_apply]
        exact (hb w).trans (ha (ρ b w))
      one_mem' := fun w => by
        show w ∈ U ↔ ρ 1 w ∈ U
        rw [map_one]
        exact Iff.rfl
      inv_mem' := fun {a} ha w => by
        show w ∈ U ↔ ρ a⁻¹ w ∈ U
        have := ha (ρ a⁻¹ w)
        rw [map_inv] at this ⊢
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hx : x0A6 ∈ H := by
    intro w
    show w ∈ U ↔ ρ x0A6 w ∈ U
    constructor
    · intro hw
      have : ρ x0A6 w = w := hw
      rw [this]; exact hw
    · intro hw
      have h1 : ρ x0A6 (ρ x0A6 w) = ρ x0A6 w := hw
      have h2 : ρ x0A6 w = w := (ρ x0A6).injective h1
      show ρ x0A6 w = w
      exact h2
  have hmap : U.map (ρ y0A6).toMonoidHom = U := (fixSub_map_conj x0A6 y0A6).trans key.symm
  have hy : y0A6 ∈ H := by
    intro w
    show w ∈ U ↔ ρ y0A6 w ∈ U
    constructor
    · intro hw
      have : ρ y0A6 w ∈ U.map (ρ y0A6).toMonoidHom := Subgroup.mem_map_of_mem _ hw
      rwa [hmap] at this
    · intro hw
      rw [← hmap] at hw
      obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
      have : v = w := (ρ y0A6).injective hvw
      rwa [this] at hv
  have hH : H = ⊤ := by
    rw [eq_top_iff, ← closure_x0y0A6]
    refine (Subgroup.closure_le H).mpr ?_
    intro g hg
    rcases hg with rfl | rfl
    · exact hx
    · exact hy
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact Subgroup.mem_bot.mpr (hcon w hw)
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hall : ∀ v : W, v ≠ 1 → v ∈ U := by
    intro v hv
    obtain ⟨g, hg⟩ := h.transitive hu1 hv
    have hgH : g ∈ H := by rw [hH]; exact Subgroup.mem_top g
    have := (hgH u).mp huU
    rwa [hg] at this
  have htop : U = ⊤ := by
    rw [eq_top_iff]
    intro w _
    by_cases hw : w = 1
    · rw [hw]; exact U.one_mem
    · exact hall w hw
  rw [htop, Subgroup.card_top, h.card] at hcard
  omega


theorem Setup.no_quad_pair (h : Setup ρ) (α : MulAut A6)
    (hα : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ α x) {a b : A6} (hab : a ≠ b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1) (hcomm : a * b = b * a) :
    ¬ (A6QuadPair (ρ a) (ρ b) ∧ A6QuadPair (ρ (α a)) (ρ (α b))) := by
  rintro ⟨hq1, hq2⟩
  have e1 := h.eqv_of_quad ha1 ha2 hb1 hb2 hq1
  have hαa1 : α a ≠ 1 := fun e => ha1 (α.injective (e.trans (map_one α).symm))
  have hαb1 : α b ≠ 1 := fun e => hb1 (α.injective (e.trans (map_one α).symm))
  have hαab : α a ≠ α b := fun e => hab (α.injective e)
  have hαa2 : α a * α a = 1 := by rw [← map_mul, ha2, map_one]
  have hαb2 : α b * α b = 1 := by rw [← map_mul, hb2, map_one]
  have hαcomm : α a * α b = α b * α a := by rw [← map_mul, ← map_mul, hcomm]
  have e2 := h.eqv_of_quad hαa1 hαa2 hαb1 hαb2 hq2
  have both : fixSub (ρ bxA) = fixSub (ρ u1A) ∧ fixSub (ρ bxA) = fixSub (ρ u3A) := by
    rcases fam_cases a b hab ha1 hb1 ha2 hb2 hcomm with hB | hA
    · have hU := hB.type.1
      have hAα : FamA (α a) (α b) := by
        rcases fam_cases (α a) (α b) hαab hαa1 hαb1 hαa2 hαb2 hαcomm with hB' | hA'
        · exact absurd (h.hasT_of_hasU α hα hU) hB'.type.2
        · exact hA'
      exact ⟨h.eqv_B hB e1, h.eqv_A hAα e2⟩
    · have hT := hA.type.1
      have hBα : FamB (α a) (α b) := by
        rcases fam_cases (α a) (α b) hαab hαa1 hαb1 hαa2 hαb2 hαcomm with hB' | hA'
        · exact hB'
        · exact absurd (h.hasU_of_hasT α hα hT) hA'.type.2
      exact ⟨h.eqv_B hBα e2, h.eqv_A hA e1⟩
  obtain ⟨r₁, hr₁s, hr₁1, hr₁2⟩ := conj_chain1
  obtain ⟨r₂, hr₂s, hr₂1, hr₂2⟩ := conj_chain2
  let R₁ : A6 := ⟨r₁, mem_alternatingGroup.mpr hr₁s⟩
  let R₂ : A6 := ⟨r₂, mem_alternatingGroup.mpr hr₂s⟩
  have c1 : fixSub (ρ x0A6) = fixSub (ρ u1A) := by
    have h1 := fixSub_eq_conj R₁ both.1
    have e1' : R₁ * bxA * R₁⁻¹ = x0A6 := Subtype.ext hr₁1
    have e2' : R₁ * u1A * R₁⁻¹ = u1A := Subtype.ext hr₁2
    rwa [e1', e2'] at h1
  have c2 : fixSub (ρ u1A) = fixSub (ρ (y0A6 * x0A6 * y0A6⁻¹)) := by
    have h1 := fixSub_eq_conj R₂ both.2
    have e1' : R₂ * bxA * R₂⁻¹ = u1A := Subtype.ext hr₂1
    have e2' : R₂ * u3A * R₂⁻¹ = y0A6 * x0A6 * y0A6⁻¹ := Subtype.ext hr₂2
    rwa [e1', e2'] at h1
  exact h.false_of_chain (c1.trans c2)

end CFSG.Quasithin.A6Fin
