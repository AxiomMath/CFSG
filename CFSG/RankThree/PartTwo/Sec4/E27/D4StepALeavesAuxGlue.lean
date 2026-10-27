module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxH
public import CFSG.RankThree.PartTwo.Sec4.E27.D4TwoLines
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase

public section

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Restrict

variable {K : Type*} [Group K]

@[expose] def restrictLayer (E : Subgroup (MulAut K)) (D : Subgroup K)
    (h : ∀ y ∈ E, ∀ d ∈ D, y d ∈ D) : E →* MulAut D where
  toFun y :=
    { toFun := fun d => ⟨(y : MulAut K) d, h y y.2 d d.2⟩
      invFun := fun d => ⟨(y : MulAut K)⁻¹ d, h (y : MulAut K)⁻¹ (E.inv_mem y.2) d d.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun d => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul (y : MulAut K) _ _) }
  map_one' := by
    ext d
    rfl
  map_mul' a b := by
    ext d
    rfl

end Restrict

section Glue

variable {K : Type*} [Group K] [Finite K]

theorem layer_closure_of_plane
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (τ : MulAut K) (x : K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hτx : τ x = x)
    {C D : Subgroup K} (hC : C = Subgroup.centralizer ({x} : Set K)) (hD : D = ⁅C, C⁆)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hxE : (MulAut.conj x : MulAut K) ∈ E)
    (hcard : Nat.card E = 27)
    (hshape : ∀ y ∈ E, ∃ (g : K) (j : ℕ), y = MulAut.conj g * τ ^ j)
    (hτD : ∀ d ∈ D, τ d = d)
    (hZab : ∀ a ∈ Subgroup.centralizer (D : Set K), ∀ b ∈ Subgroup.centralizer (D : Set K),
      a * b = b * a)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (D : Set K), (∃ k : ℕ, z ^ (3 ^ k) = 1) →
      z ∈ Subgroup.zpowers x)
    (hDZ : ∀ w ∈ D, (∀ d ∈ D, w * d = d * w) → w ∈ Subgroup.zpowers x)
    {S : Type*} [Group S] (P : MulAut S → Prop) (e : D ≃* S)
    (hP : ∀ g ∈ C, ∀ φ : MulAut S,
      (∀ d d' : D, (d' : K) = g * d * g⁻¹ → φ (e d) = e d') → P φ)
    (PT : ∀ E' : Subgroup (MulAut S), IsElemAbelian 3 E' → Nat.card E' = 9 → (∀ φ ∈ E', P φ) →
      (¬ FixCube E' → ¬ E' ≤ (MulAut.conj : S →* MulAut S).range) →
        Subgroup.closure (fixSet E') = ⊤) :
    D ≤ Subgroup.closure {l | l ∈ D ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut K) ∧ y l = l} := by
  classical
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => comm_of_isElemAbelian hE ha hb
  have hmemC : ∀ c : K, c ∈ C ↔ c * x = x * c := by
    intro c
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff
  have hDC : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ D := fun a ha b hb =>
    hD ▸ Subgroup.commutator_mem_commutator ha hb
  have hDle : ∀ {H : Subgroup K}, (∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ H) → D ≤ H := by
    intro H hH
    rw [hD, Subgroup.commutator_le]
    exact hH
  have hDC' : D ≤ C := by
    refine hDle fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
  have hτjD : ∀ (j : ℕ), ∀ d ∈ D, (τ ^ j) d = d := by
    intro j
    induction j with
    | zero => intro d _; simp
    | succ j ih => intro d hd; rw [pow_succ, MulAut.mul_apply, hτD d hd, ih d hd]
  have hτjx : ∀ j : ℕ, (τ ^ j) x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hτx, ih]
  have hxfix : ∀ y ∈ E, (y : MulAut K) x = x := by
    intro y hy
    apply hinj
    have h1 := aut_mul_conj_eq y x
    have h2 := hEc y hy _ hxE
    have h3 : MulAut.conj (y x) * y = MulAut.conj x * y := by rw [← h1, h2]
    exact mul_right_cancel h3
  have hCpres : ∀ y ∈ E, ∀ c ∈ C, (y : MulAut K) c ∈ C := by
    intro y hy c hc
    rw [hmemC] at hc ⊢
    have := congrArg (y : MulAut K) hc
    rw [map_mul, map_mul, hxfix y hy] at this
    exact this
  have hDpres : ∀ y ∈ E, ∀ d ∈ D, (y : MulAut K) d ∈ D := by
    intro y hy d hd
    have hle : D ≤ D.comap (y : MulAut K).toMonoidHom := by
      refine hDle fun a ha b hb => ?_
      rw [Subgroup.mem_comap]
      show (y : MulAut K) ⁅a, b⁆ ∈ D
      rw [map_commutatorElement]
      exact hDC _ (hCpres y hy a ha) _ (hCpres y hy b hb)
    exact hle hd
  obtain ⟨ρD, hρD⟩ : ∃ ρD : E →* MulAut D, ∀ (y : E) (d : D),
      ((ρD y d : D) : K) = (y : MulAut K) d :=
    ⟨restrictLayer E D (fun y hy d hd => hDpres y hy d hd), fun y d => rfl⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : E →* MulAut S, ∀ (y : E) (d : D), ρ' y (e d) = e (ρD y d) :=
    ⟨(MulAut.congr e).toMonoidHom.comp ρD, fun y d => by simp [MulAut.congr_apply]⟩
  set N : Subgroup (MulAut K) := Subgroup.zpowers (MulAut.conj x : MulAut K) with hN
  have hconj1 : (MulAut.conj x : MulAut K) ≠ 1 := fun h => hx1 (hinj (by rw [h, map_one]))
  have hconj3 : (MulAut.conj x : MulAut K) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hNle : N ≤ E := by rw [hN, Subgroup.zpowers_le]; exact hxE
  have hNcard : Nat.card N = 3 := by
    rw [hN, Nat.card_zpowers, orderOf_eq_prime hconj3 hconj1]
  by_cases hA : ∃ y ∈ E, y ∉ N ∧ ∀ d ∈ D, (y : MulAut K) d = d
  · obtain ⟨y, hy, hyN, hyd⟩ := hA
    intro l hl
    exact Subgroup.subset_closure ⟨hl, y, hy, hyN, hyd l hl⟩
  push_neg at hA
  have htriv : ∀ y : E, (y : MulAut K) ∈ N → ∀ d ∈ D, (y : MulAut K) d = d := by
    intro y hy d hd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk, ← map_zpow, MulAut.conj_apply]
    have hdC : d * x = x * d := (hmemC d).mp (hDC' hd)
    have hc : Commute (x ^ k) d := Commute.zpow_left (show Commute x d from hdC.symm) k
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.eq
  have hker : ∀ y : E, ρ' y = 1 ↔ (y : MulAut K) ∈ N := by
    intro y
    constructor
    · intro h1
      by_contra hyN
      obtain ⟨d, hd, hne⟩ := hA y y.2 hyN
      apply hne
      have h2 : ρ' y (e ⟨d, hd⟩) = e ⟨d, hd⟩ := by rw [h1]; rfl
      rw [hρ'] at h2
      have h3 := congrArg Subtype.val (e.injective h2)
      rw [hρD] at h3
      exact h3
    · intro hyN
      ext s
      obtain ⟨d, rfl⟩ := e.surjective s
      rw [hρ']
      have : ρD y d = d := Subtype.ext (by rw [hρD]; exact htriv y hyN d d.2)
      rw [this]
      rfl
  have hkerEq : ρ'.ker = N.subgroupOf E := by
    ext y
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hkcard : Nat.card ρ'.ker = 3 := by
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv, hNcard]
  have hE'card : Nat.card ρ'.range = 9 := by
    have := Subgroup.card_ker_mul_card_range ρ'
    rw [hkcard, hcard] at this
    omega
  have hE'ab : IsElemAbelian 3 ρ'.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨y₁, h₁⟩ := a.2
      obtain ⟨y₂, h₂⟩ := b.2
      apply Subtype.ext
      show (a : MulAut S) * (b : MulAut S) = (b : MulAut S) * (a : MulAut S)
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      exact congrArg ρ' (Subtype.ext (hEc _ y₁.2 _ y₂.2))
    · rintro φ ⟨y, rfl⟩
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (hE.2 _ y.2)
      rw [this, map_one]
  have hgC_of : ∀ (y : E) (g : K) (j : ℕ), (y : MulAut K) = MulAut.conj g * τ ^ j → g ∈ C := by
    intro y g j hg
    rw [hmemC]
    have hy := hxfix y y.2
    rw [hg, MulAut.mul_apply, hτjx j, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hy
    exact hy
  have hρDg : ∀ (y : E) (g : K) (j : ℕ), (y : MulAut K) = MulAut.conj g * τ ^ j →
      ∀ d : D, ((ρD y d : D) : K) = g * d * g⁻¹ := by
    intro y g j hg d
    rw [hρD, hg, MulAut.mul_apply, hτjD j d d.2, MulAut.conj_apply]
  have hP' : ∀ φ ∈ ρ'.range, P φ := by
    rintro φ ⟨y, rfl⟩
    obtain ⟨g, j, hg⟩ := hshape y y.2
    refine hP g (hgC_of y g j hg) (ρ' y) ?_
    intro d d' hd'
    rw [hρ']
    congr 1
    exact Subtype.ext ((hρDg y g j hg d).trans hd'.symm)
  have hz : ∀ (y : E) (g : K) (j : ℕ) (t : S), (y : MulAut K) = MulAut.conj g * τ ^ j →
      ρ' y = MulAut.conj t → ((e.symm t : D) : K)⁻¹ * g ∈ Subgroup.centralizer (D : Set K) := by
    intro y g j t hg hyt
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : ρ' y (e ⟨h, hh⟩) = (MulAut.conj t) (e ⟨h, hh⟩) := by rw [hyt]
    rw [hρ', MulAut.conj_apply] at h1
    have h2 : ρD y ⟨h, hh⟩ = e.symm t * ⟨h, hh⟩ * (e.symm t)⁻¹ := by
      apply e.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [hρDg y g j hg ⟨h, hh⟩] at h3
    set a : K := ((e.symm t : D) : K) with ha
    have h3' : g * h * g⁻¹ = a * h * a⁻¹ := h3
    have h4 : (a⁻¹ * g) * h * (a⁻¹ * g)⁻¹ = h := by
      calc (a⁻¹ * g) * h * (a⁻¹ * g)⁻¹ = a⁻¹ * (g * h * g⁻¹) * a := by group
        _ = a⁻¹ * (a * h * a⁻¹) * a := by rw [h3']
        _ = h := by group
    exact (mul_inv_eq_iff_eq_mul.1 h4).symm
  have houtc : ¬ FixCube ρ'.range → ¬ ρ'.range ≤ (MulAut.conj : S →* MulAut S).range := by
    intro hF hin
    apply hF
    intro e₁ he₁ s hs3 hsE
    obtain ⟨t₀, ht₀⟩ := hin he₁
    obtain ⟨y_e, hye⟩ := he₁
    obtain ⟨y_s, hys⟩ := hsE
    obtain ⟨g_e, j_e, hge⟩ := hshape y_e y_e.2
    obtain ⟨g_s, j_s, hgs⟩ := hshape y_s y_s.2
    have hze := hz y_e g_e j_e t₀ hge (hye.trans ht₀.symm)
    have hzs := hz y_s g_s j_s s hgs hys
    have hcomm : (MulAut.conj g_e * τ ^ j_e) * (MulAut.conj g_s * τ ^ j_s) =
        (MulAut.conj g_s * τ ^ j_s) * (MulAut.conj g_e * τ ^ j_e) := by
      rw [← hge, ← hgs]
      exact hEc _ y_e.2 _ y_s.2
    have hcom := commute_of_comm_autos hinj τ x D hx3 hτD hτx hZab hZ3 hDZ (e.symm t₀).2
      (e.symm s).2 hze hzs hcomm
    have hts : t₀ * s = s * t₀ := by
      have h1 : e.symm t₀ * e.symm s = e.symm s * e.symm t₀ := Subtype.ext hcom
      have h2 := congrArg e h1
      simpa using h2
    rw [← ht₀, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hts
  have htop := PT ρ'.range hE'ab hE'card hP' houtc
  intro d hd
  have hmem : e ⟨d, hd⟩ ∈ Subgroup.closure (fixSet ρ'.range) := by
    rw [htop]
    exact Subgroup.mem_top _
  have h2 : (⟨d, hd⟩ : D) ∈ Subgroup.closure (e.symm '' fixSet ρ'.range) := by
    have h := Subgroup.mem_map_of_mem e.symm.toMonoidHom hmem
    rw [MonoidHom.map_closure] at h
    simpa using h
  have hsub : e.symm '' fixSet ρ'.range ⊆
      {z : D | ∃ y ∈ E, y ∉ N ∧ (y : MulAut K) (z : K) = (z : K)} := by
    rintro _ ⟨s, ⟨e₁, ⟨y, rfl⟩, hne1, hfs⟩, rfl⟩
    refine ⟨y.1, y.2, ?_, ?_⟩
    · intro hyN
      exact hne1 ((hker y).2 hyN)
    · obtain ⟨z, rfl⟩ := e.surjective s
      rw [MulEquiv.symm_apply_apply]
      rw [hρ'] at hfs
      have h3 := congrArg Subtype.val (e.injective hfs)
      rw [hρD] at h3
      exact h3
  have h3 : D.subtype ⟨d, hd⟩ ∈ (Subgroup.closure {z : D | ∃ y ∈ E, y ∉ N ∧
      (y : MulAut K) (z : K) = (z : K)}).map D.subtype :=
    ⟨⟨d, hd⟩, Subgroup.closure_mono hsub h2, rfl⟩
  rw [MonoidHom.map_closure] at h3
  refine Subgroup.closure_mono ?_ h3
  rintro _ ⟨z, ⟨y, hy, hyN, hyz⟩, rfl⟩
  exact ⟨z.2, y, hy, hyN, hyz⟩

end Glue

end CFSG.RankThree.PartTwo.Sec4.E27
