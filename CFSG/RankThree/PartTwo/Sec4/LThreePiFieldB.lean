module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIc
public import CFSG.RankThree.PartTwo.Sec4.LThreePiField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section RingAut

variable {K : Type} [Field K]

theorem eq_or_eq_sq_of_pow {r : ℕ} {φ ψ : K ≃+* K} (hφ : ∀ c, φ c = c ^ r)
    (hψ : (∀ c, ψ c = c ^ r) ∨ ∀ c, ψ c = c ^ (r ^ 2)) : ψ = φ ∨ ψ = φ ^ 2 := by
  rcases hψ with h | h
  · exact Or.inl (RingEquiv.ext fun c => by rw [h, hφ])
  · refine Or.inr (RingEquiv.ext fun c => ?_)
    rw [h, ringAut_sq_apply, hφ, hφ, ← pow_mul, pow_two]

theorem ringAut_comp_of_ne {φ : K ≃+* K} (hφ3 : orderOf φ = 3) {ψ ψ' : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (hψ' : ψ' = φ ∨ ψ' = φ ^ 2) (hne : ψ' ≠ ψ) (c : K) :
    ψ' (ψ c) = c := by
  rcases hψ with rfl | rfl <;> rcases hψ' with rfl | rfl
  · exact absurd rfl hne
  · rw [ringAut_sq_apply, ringAut_apply_three hφ3]
  · rw [ringAut_sq_apply, ringAut_apply_three hφ3]
  · exact absurd rfl hne

theorem frobGL_comp_eq {ψ ψ' : K ≃+* K} (h : ∀ c, ψ' (ψ c) = c) (A : GL (Fin 3) K) :
    frobGL ψ' (frobGL ψ A) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL]
  ext i k
  simp only [Matrix.map_apply, h]

end RingAut

section Small

variable {G : Type*} [Group G]

theorem inf_zpowers_eq_bot {H : Subgroup G} {σ : G} (hσ3 : σ ^ 3 = 1) (hσH : σ ∉ H) :
    H ⊓ Subgroup.zpowers σ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ1 : σ ≠ 1 := fun h => hσH (h ▸ H.one_mem)
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  rw [eq_bot_iff]
  intro x ⟨hxH, hxσ⟩
  by_contra hx1
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxσ
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hσ3,
      _root_.one_zpow]
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hx1 (h ▸ Subgroup.mem_bot.mpr rfl))
  have heq : Subgroup.zpowers x = Subgroup.zpowers σ := by
    have : Finite (Subgroup.zpowers σ) :=
      (orderOf_pos_iff.mp (by rw [hσo]; norm_num)).finite_zpowers
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxσ)
    rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hσo]
  apply hσH
  have : σ ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers σ
  exact (Subgroup.zpowers_le.mpr hxH) this

end Small

section Fix

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem commute_of_slAct_eq {e : L ≃* slPi π 3 (p ^ f) K} {g : G} {s : slPi π 3 (p ^ f) K}
    (h : slAct e ⟨g, mem_normalizer_of_normal g⟩ s = s) :
    g * (e.symm s : G) = (e.symm s : G) * g := by
  rw [slAct_apply] at h
  have h5 := congrArg (fun s => (e.symm s : G)) h
  simp only [MulEquiv.symm_apply_apply] at h5
  change g * (e.symm s : G) * g⁻¹ = e.symm s at h5
  calc g * (e.symm s : G) = g * (e.symm s : G) * g⁻¹ * g := by group
    _ = (e.symm s : G) * g := by rw [h5]

omit hLn in
theorem mem_statedScalars_of_mem_inf (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {x : L} (hx : (x : G) ∈ Subgroup.centralizer (L : Set G)) :
    ((e x : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun y hy => ?_
  obtain ⟨m, hm⟩ := e.surjective ⟨y, hy⟩
  have h1 : x * m = m * x := Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx _ m.2).symm)
  have h2 := congrArg (fun s : L => ((e s : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
  simp only [map_mul, Subgroup.coe_mul, hm] at h2
  exact h2

end Fix

section FieldB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem fieldB_structure (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    [Group.IsPerfect L] (hθ : aschbacherSolvableCore 3 L = ⊥) {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* slPi π 3 (p ^ f) K)
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s) :
    (∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)),
        ∃ y, IsPGLAt e b y ∧ frobGL ψ y = y) ∧
      A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ ∧
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.zpowers σ = ⊥ ∧
      Nat.card A = Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) * 3 ∧
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (L : Set G) =
        Subgroup.zpowers c ∧
      Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) ≤ 27 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hΨ3 := frobGL_three' hφ3 hψ
  have hinnerpgl : ∀ b ∈ L ⊔ Subgroup.centralizer (L : Set G), ∃ y, IsPGLAt e b y := by
    intro b hb
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    exact ⟨_, isPGLAt_mul e (isPGLAt_of_mem e hπ hl) (isPGLAt_of_mem_centralizer e hu)⟩
  have hfix : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∃ y', IsPGLAt e a y' ∧ frobGL ψ y' = y' :=
    fun a ha y hy => exists_fixed_lift hK hq hf hφ hφ3 hψ hσψ (hAcomm a ha σ hσA) hy
  have hpglB : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) := by
    intro a ha y hy
    obtain ⟨y', hy', hy'ψ⟩ := hfix a ha y hy
    exact ⟨ha, mem_sup_centralizer_of_fixed hK hq hf hφ hφ3 hψ hy' hy'ψ⟩
  have hgen : ∀ a ∈ A, a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers σ := by
    intro a ha
    have ha3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.1.2 a ha)
    rcases slAct_pgl_or_field hK hq2 hθ e _ ha3 with ⟨y, hy, hys⟩ |
      ⟨-, f₀', hf', ψa, hψa, g, hg, hga⟩
    · exact Subgroup.mem_sup_left (hpglB a ha y ⟨hy, hys⟩)
    · have hf₀' : f₀' = f₀ := by omega
      subst hf₀'
      have hψa' : ψa = φ ∨ ψa = φ ^ 2 := eq_or_eq_sq_of_pow hφ hψa
      have hσσ : σ * σ ∈ Subgroup.zpowers σ := mul_mem (Subgroup.mem_zpowers σ)
        (Subgroup.mem_zpowers σ)
      by_cases hsame : ψa = ψ
      ·
        have hx : IsPGLAt e (a * σ * σ) g := by
          refine ⟨hg, fun s => ?_⟩
          rw [slAct_mul_apply, slAct_mul_apply, hga, hσψ, hσψ, hsame, hΨ3]
        have hxB := hpglB _ (mul_mem (mul_mem ha hσA) hσA) g hx
        have : a = a * σ * σ * (σ * σ)⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB) (Subgroup.mem_sup_right (inv_mem hσσ))
      ·
        have hx : IsPGLAt e (a * σ) g := by
          refine ⟨hg, fun s => ?_⟩
          rw [slAct_mul_apply, hga, hσψ,
            frobGL_comp_eq (ringAut_comp_of_ne hφ3 hψ hψa' hsame)]
        have hxB := hpglB _ (mul_mem ha hσA) g hx
        have : a = a * σ * σ⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB)
          (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers σ)))
  have hAeq : A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ :=
    le_antisymm (fun a ha => hgen a ha) (sup_le inf_le_left (Subgroup.zpowers_le.mpr hσA))
  have hBσ : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.zpowers σ = ⊥ :=
    inf_zpowers_eq_bot (hA.1.2 σ hσA) (fun h => hσB h.2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 :=
    orderOf_eq_prime (hA.1.2 σ hσA) (fun h => hσB (h ▸ Subgroup.one_mem _))
  have hcomm : ∀ x ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∀ y ∈ Subgroup.zpowers σ,
      x * y = y * x := fun x hx y hy =>
    hAcomm x hx.1 y ((Subgroup.zpowers_le.mpr hσA) hy)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [← hAeq, hBσ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hσo] at hcard
  have hBc : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers c := by
    apply le_antisymm
    · rw [← hAc]
      exact inf_le_inf_right _ inf_le_left
    · exact Subgroup.zpowers_le.mpr ⟨⟨hcAC.1, Subgroup.mem_sup_right hcAC.2⟩, hcAC.2⟩
  have hpglB' : ∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∃ y, IsPGLAt e b y :=
    fun b hb => hinnerpgl b hb.2
  have hcardB := card_eq_card_inf_mul_card_range (L := L) (e := e) (hK := hK) (hq := hq)
    (A' := A ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) (hA' := hpglB')
  rw [hBc, Nat.card_zpowers, hc3] at hcardB
  have hE := card_le_nine_of_comm h3 hτ hτ1 (pglHom hK hq _ hpglB').range
    (range_pglHom_comm fun a ha b hb => hAcomm a ha.1 b hb.1)
    (range_pglHom_pow fun b hb => hA.1.2 b hb.1)
  refine ⟨fun b hb => ?_, hAeq, hBσ, hcard, hBc, by omega⟩
  obtain ⟨y, hy⟩ := hinnerpgl b hb.2
  exact hfix b hb.1 y hy

end FieldB

section FieldThree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagTau_mul_diagE {τ : K} (hτ : τ ^ 3 = 1) (e : Kˣ) :
    diagTau hτ * diagE e = diagE e * diagTau hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagTau_eq_diagonal, coe_diagE, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

omit [Finite G] in
theorem type1_of_fixed (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAL : A ⊓ L ≤ Subgroup.zpowers c) {σ : G}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {b : G} (hbA : b ∈ A) (hbLC : b ∈ L ⊔ Subgroup.centralizer (L : Set G))
    (hbc : b ∉ Subgroup.zpowers c)
    (hgen : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers σ)
    {y : GL (Fin 3) K} (hy : IsPGLAt e b y) (hyψ : frobGL ψ y = y) :
    Type123 π (p ^ f) K y 1 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨S, hS, hScard⟩ := exists_fixedField hK hf hφ3
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hS₀ : PiField π p f₀ S := ⟨hK.prime, hf₀, hScard⟩
  have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hπ₀ : π = false → UnitaryFieldData p f₀ S := fun h => by subst h; exact hS₀.unitary
  have hq₀' : π = false → ModThree false (p ^ f₀) := fun h => by subst h; exact hq₀
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hS₀ hq₀
  have hSψ : ∀ c, c ∈ S ↔ ψ c = c := fun c => (hS c).trans (fixed_iff_of_sq hφ3 hψ c).symm
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hbC : b ∉ Subgroup.centralizer (L : Set G) := fun h => hbc (by rw [← hAc]; exact ⟨hbA, h⟩)
  have hyZ : y ∉ zPi π 3 (p ^ f) K := fun h =>
    hbC (mem_centralizer_of_isPGLAt_scalar hy (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h))
  have hy3 := pow_three_mem_zPi hK hq (hA.1.2 b hbA) hy
  have hyφ : frobGL φ y = y := by
    apply Units.ext
    have := congrArg Units.val hyψ
    rw [coe_frobGL] at this ⊢
    ext i k
    have h := congrFun (congrFun this i) k
    simp only [Matrix.map_apply] at h ⊢
    exact (fixed_iff_of_sq hφ3 hψ _).mp h
  obtain ⟨y₀, rfl⟩ := exists_subGL_eq hS hyφ
  have hy₀H : y₀ ∈ glPi π 3 (p ^ f₀) S := (subGL_mem_glPi_iff hK hf hφ hS hS₀ y₀).mp hy.1
  have hy₀Z : y₀ ∉ zPi π 3 (p ^ f₀) S := fun h => hyZ (subGL_mem_zPi hK hq hf hφ hS hS₀ hq₀ h)
  have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (p ^ f₀) S := by
    rw [zPi_eq hπ₀ hq₀' hτ₀ hτ₀1]
    refine Subgroup.mem_inf.mpr ⟨pow_mem hy₀H 3, mem_statedScalars_of_subGL S ?_⟩
    rw [map_pow]
    exact mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3
  rcases type123_exhaust hS₀ hq₀ hy₀H hy₀Z hy₀3 with h1 | h2 | h3
  · exact type123_one_subGL hK hq hf hφ hS hS₀ hq₀ h1
  ·
    exfalso
    obtain ⟨e₀, -, -, z₀, hz₀, g₀, hg₀, hD⟩ := h2
    set x₀ : GL (Fin 3) S := g₀ * diagTau hτ₀ * g₀⁻¹ with hx₀
    have hx₀L : x₀ ∈ slPi π 3 (p ^ f₀) S :=
      conj_mem_slPi hπ₀ hg₀ (diagTau_mem_slPi hπ₀ hq₀' hτ₀)
    have hx₀3 : x₀ ^ 3 = 1 := by
      rw [hx₀, conj_pow, diagTau_pow_three hτ₀, mul_one, mul_inv_cancel]
    have hz₀s := mem_statedScalars_of_mem_zPi hS₀ hq₀ hτ₀ hτ₀1 hz₀
    have hx₀y : x₀ * y₀ = y₀ * x₀ := by
      have hyz : y₀ * z₀ = g₀ * diagE e₀ * g₀⁻¹ := eq_conj_of_inv_conj hD
      have h1 : x₀ * (y₀ * z₀) = (y₀ * z₀) * x₀ := by
        rw [hyz, hx₀]
        calc g₀ * diagTau hτ₀ * g₀⁻¹ * (g₀ * diagE e₀ * g₀⁻¹) =
            g₀ * (diagTau hτ₀ * diagE e₀) * g₀⁻¹ := by group
          _ = g₀ * (diagE e₀ * diagTau hτ₀) * g₀⁻¹ := by rw [diagTau_mul_diagE]
          _ = _ := by group
      have hzc := commute_of_mem_statedScalars hz₀s
      calc x₀ * y₀ = x₀ * (y₀ * z₀) * z₀⁻¹ := by group
        _ = y₀ * z₀ * x₀ * z₀⁻¹ := by rw [h1]
        _ = y₀ * (z₀ * x₀) * z₀⁻¹ := by group
        _ = y₀ * (x₀ * z₀) * z₀⁻¹ := by rw [hzc x₀]
        _ = y₀ * x₀ := by group
    have hx₀s : x₀ ∉ StatedScalars (Fin 3) S := by
      rintro ⟨t₀, ht₀⟩
      have h1 : diagTau hτ₀ = GeneralLinearGroup.scalar (Fin 3) t₀ := by
        have := commute_of_mem_statedScalars ⟨t₀, ht₀⟩ g₀⁻¹
        calc diagTau hτ₀ = g₀⁻¹ * x₀ * g₀ := by rw [hx₀]; group
          _ = GeneralLinearGroup.scalar (Fin 3) t₀ := by
              rw [this, inv_mul_cancel_right]
              exact ht₀.symm
      have h00 := congrArg (fun M : GL (Fin 3) S => (M : Matrix (Fin 3) (Fin 3) S) 0 0) h1
      have h22 := congrArg (fun M : GL (Fin 3) S => (M : Matrix (Fin 3) (Fin 3) S) 2 2) h1
      simp only [coe_diagTau_eq_diagonal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h00 h22
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at h00 h22
      exact hτ₀1 (h00.trans h22.symm)
    have hxL : subGL S x₀ ∈ slPi π 3 (p ^ f) K :=
      (subGL_mem_slPi_iff hK hf hφ hS hS₀ x₀).mpr hx₀L
    obtain ⟨x, hx⟩ : ∃ x : L, x = e.symm ⟨subGL S x₀, hxL⟩ := ⟨_, rfl⟩
    have hxσ : σ * (x : G) = x * σ := by
      rw [hx]
      apply commute_of_slAct_eq
      apply Subtype.ext
      rw [hσψ]
      exact frobGL_subGL hSψ x₀
    have hxb : b * (x : G) = x * b := by
      rw [hx]
      apply commute_of_slAct_eq
      apply Subtype.ext
      rw [hy.2]
      change subGL S y₀ * subGL S x₀ * (subGL S y₀)⁻¹ = subGL S x₀
      rw [← map_mul, ← map_inv, ← map_mul, ← hx₀y, mul_inv_cancel_right]
    have hxc : c * (x : G) = x * c :=
      (Subgroup.mem_centralizer_iff.mp hcAC.2 x x.2).symm
    have hxA : ∀ a ∈ A, a * (x : G) = x * a := by
      intro a ha
      have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers σ ≤
          Subgroup.centralizer {(x : G)} := by
        refine sup_le (sup_le ?_ ?_) ?_ <;>
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact hxc
        · exact hxb
        · exact hxσ
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen ha))
    have hx3 : (x : G) ^ 3 = 1 := by
      rw [hx, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨subGL S x₀, hxL⟩ : slPi π 3 (p ^ f) K) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hx₀3, map_one, Subgroup.coe_one])
      rw [this, map_one, Subgroup.coe_one]
    have hxAm : (x : G) ∈ A := mem_of_maximal_of_commute hA hx3 hxA
    have hxc' : (x : G) ∈ Subgroup.zpowers c := hAL ⟨hxAm, x.2⟩
    have hxC : (x : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hLC] at hxc'
      exact hxc'.2
    have hs := mem_statedScalars_of_mem_inf hK hq (e := e) hxC
    rw [hx, MulEquiv.apply_symm_apply] at hs
    exact hx₀s (mem_statedScalars_of_subGL S hs)
  ·
    have htr : ((subGL S y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
      rw [trace_subGL, trace_eq_zero_of_type3 hS₀ hq₀ h3]
      rfl
    rcases type123_exhaust hK hq hy.1 hyZ hy3 with g1 | g2 | g3
    · exact g1
    · exact absurd htr (trace_ne_zero_of_type2 hK hq g2)
    · exact absurd hbLC (not_mem_sup_centralizer_of_type3 hK hq hy g3)

theorem alt411_field_three (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    [Group.IsPerfect L] (hθ : aschbacherSolvableCore 3 L = ⊥) {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* slPi π 3 (p ^ f) K)
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσkind : InducesStdKind L σ .field)
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    (hA27 : Nat.card A = 27) : Alt411 L A c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hfixB, hAeq, hBσ, hcard, hBc, -⟩ :=
    fieldB_structure hK hq hq2 hθ hf hφ hφ3 hψ e hA hc3 hAc hσA hσB hσψ
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  set B := A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) with hBdef
  have hB9 : Nat.card B = 9 := by omega
  have hALB : A ⊓ L ≤ B := fun x hx => ⟨hx.1, Subgroup.mem_sup_left hx.2⟩
  have hcAL : Subgroup.zpowers c ≤ A ⊓ L := Subgroup.zpowers_le.mpr ⟨hcAC.1, hcL⟩
  by_cases h9 : Nat.card (A ⊓ L : Subgroup G) = 9
  ·
    have hALeqB : A ⊓ L = B := Subgroup.eq_of_le_of_card_ge hALB (by rw [h9, hB9])
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hA27, σ, hσA, hσkind, ?_, ?_⟩)))
    · rw [hALeqB, sup_comm]
      exact hAeq
    · rw [eq_bot_iff]
      intro x hx
      have hxB : x ∈ B ⊓ Subgroup.zpowers σ :=
        ⟨hALB ⟨(Subgroup.zpowers_le.mpr hσA) hx.1, hx.2⟩, hx.1⟩
      rw [hBσ] at hxB
      exact hxB
  ·
    have hAL : A ⊓ L ≤ Subgroup.zpowers c := by
      have h1 : Nat.card (A ⊓ L : Subgroup G) ∣ 9 := hB9 ▸ Subgroup.card_dvd_of_le hALB
      have h2 : 3 ≤ Nat.card (A ⊓ L : Subgroup G) := by
        have := Subgroup.card_le_of_le hcAL
        rwa [Nat.card_zpowers, hc3] at this
      have h3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
          (show Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 2 from by
            rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h1)
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · rw [hk'] at h2
          norm_num at h2
        · rw [hk']
          norm_num
        · exact absurd (by rw [hk']; norm_num) h9
      have := Subgroup.eq_of_le_of_card_ge hcAL (by rw [h3, Nat.card_zpowers, hc3])
      rw [← this]
    obtain ⟨b, hbB, hbc⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers c := by
      by_contra hne
      push Not at hne
      have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers c from fun x hx => hne x hx)
      rw [Nat.card_zpowers, hc3] at this
      omega
    have hbA := hbB.1
    have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
    have hcb9 := card_zpowers_sup_zpowers hb3 hc3 hbc (hAcomm b hbA c hcAC.1)
    have hcbB : Subgroup.zpowers c ⊔ Subgroup.zpowers b ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hcAC.1, Subgroup.mem_sup_right hcAC.2⟩)
        (Subgroup.zpowers_le.mpr hbB)
    have hBeq : B = Subgroup.zpowers c ⊔ Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge hcbB (by rw [hB9, hcb9])).symm
    have hgen : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers σ := by
      rw [← hBeq]
      exact hAeq.le
    obtain ⟨y, hy, hyψ⟩ := hfixB b hbB
    have hy1 := type1_of_fixed hK hq hf hφ hφ3 hψ e hA hc3 hAc hAL hσψ hbA hbB.2 hbc hgen hy hyψ
    obtain ⟨v, hv3, hbv, hbvC, -⟩ := exists_inner_decomp hK hq hy hy1
    obtain ⟨u, hu⟩ : ∃ u, u = b * (v : G)⁻¹ := ⟨_, rfl⟩
    have huC : u ∈ Subgroup.centralizer (L : Set G) := hu ▸ hbvC
    have hbuv : b = u * v := by rw [hu]; group
    have huv : u * v = v * u := ((Subgroup.mem_centralizer_iff.mp huC) v v.2).symm
    have hbC : b ∉ Subgroup.centralizer (L : Set G) := fun h =>
      hbc (by rw [← hAc]; exact ⟨hbA, h⟩)
    have huL : u ∉ L := fun h => hbc (hAL ⟨hbA, by rw [hbuv]; exact mul_mem h v.2⟩)
    have hvC : (v : G) ∉ Subgroup.centralizer (L : Set G) := fun h =>
      hbC (by rw [hbuv]; exact mul_mem huC h)
    have hu3 : orderOf u = 3 := by
      refine orderOf_eq_prime ?_ fun h => huL (h ▸ Subgroup.one_mem _)
      have hc : Commute b (v : G)⁻¹ := (show Commute b (v : G) from hbv).inv_right
      rw [hu, hc.mul_pow, hb3, inv_pow, hv3, inv_one, one_mul]
    have hv3o : orderOf (v : G) = 3 :=
      orderOf_eq_prime hv3 fun h => hvC (h ▸ Subgroup.one_mem _)
    have hZ := commutator_mem_inf v.2 hu (hAcomm σ hσA b hbA) huC
    have hcomm : u * σ * u⁻¹ * σ⁻¹ ∈ Subgroup.zpowers c := hLC ▸ hZ
    have hne : u * σ * u⁻¹ * σ⁻¹ ≠ 1 := by
      intro h1
      have huσ : u * σ = σ * u := by
        calc u * σ = u * σ * u⁻¹ * σ⁻¹ * (σ * u) := by group
          _ = σ * u := by rw [h1, one_mul]
      have hvσ : (v : G) * σ = σ * v := by
        have hv : (v : G) = u⁻¹ * b := by rw [hbuv]; group
        have huσ' : u⁻¹ * σ = σ * u⁻¹ := by
          calc u⁻¹ * σ = u⁻¹ * (σ * u) * u⁻¹ := by group
            _ = u⁻¹ * (u * σ) * u⁻¹ := by rw [huσ]
            _ = σ * u⁻¹ := by group
        rw [hv]
        calc u⁻¹ * b * σ = u⁻¹ * (σ * b) := by rw [mul_assoc, hAcomm b hbA σ hσA]
          _ = (u⁻¹ * σ) * b := by group
          _ = σ * (u⁻¹ * b) := by rw [huσ']; group
      have hvA : ∀ a ∈ A, a * (v : G) = v * a := by
        intro a ha
        have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers σ ≤
            Subgroup.centralizer {(v : G)} := by
          refine sup_le (sup_le ?_ ?_) ?_ <;>
            rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          · exact (Subgroup.mem_centralizer_iff.mp hcAC.2 v v.2).symm
          · exact hbv
          · exact hvσ.symm
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen ha))
      have hvAm : (v : G) ∈ A := mem_of_maximal_of_commute hA hv3 hvA
      have hvc : (v : G) ∈ Subgroup.zpowers c := hAL ⟨hvAm, v.2⟩
      apply hvC
      rw [← hLC] at hvc
      exact hvc.2
    have hBcl : B = Subgroup.closure {c, u * v} := by
      rw [hBeq, ← hbuv, closure_pair_eq]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hA27, σ, hσA, hσkind, ?_⟩))))
    rcases eq_or_eq_inv_of_mem_zpowers hc3 hcomm hne with hpos | hneg
    · exact ⟨u, v, huC, huL, v.2, hvC, hu3, hv3o, hBcl, hpos⟩
    · have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp huC) c hcL
      refine ⟨u⁻¹, (v : G)⁻¹, inv_mem huC, fun h => huL (by simpa using inv_mem h),
        inv_mem v.2, fun h => hvC (by simpa using inv_mem h), by rw [orderOf_inv]; exact hu3,
        by rw [orderOf_inv]; exact hv3o, ?_, commutator_inv_eq hcu hneg⟩
      have : u⁻¹ * (v : G)⁻¹ = b⁻¹ := by rw [hbuv, huv, _root_.mul_inv_rev]
      rw [← hBdef, hBeq, this, closure_pair_eq, Subgroup.zpowers_inv]

end FieldThree

end CFSG.RankThree.PartTwo.Sec4
