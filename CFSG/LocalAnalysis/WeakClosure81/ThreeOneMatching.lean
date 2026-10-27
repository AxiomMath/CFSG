module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneFix
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderSwaps

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv Classical

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private lemma isSwap_conj {g s : Perm Ω} (hs : s.IsSwap) : (g * s * g⁻¹).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  exact ⟨g a, g b, fun h => hab (g.injective h), by rw [Equiv.swap_apply_apply]⟩

private lemma conj_mem_swaps {T : Subgroup (Perm Ω)} {σ g : Perm Ω}
    (hTσ : ∀ x y, x ≠ y → (swap x y ∈ T ↔ σ x = y)) (hg : ∀ x, g (σ x) = σ (g x))
    {s : Perm Ω} (hs : s ∈ T ∧ s.IsSwap) : (g * s * g⁻¹) ∈ T ∧ (g * s * g⁻¹).IsSwap := by
  obtain ⟨hsT, a, b, hab, rfl⟩ := hs
  have hσa : σ a = b := (hTσ a b hab).mp hsT
  have hgb : g b = σ (g a) := by rw [← hσa]; exact hg a
  have hne : g a ≠ σ (g a) := by
    rw [← hgb]
    exact fun h => hab (g.injective h)
  refine ⟨?_, ?_⟩
  · rw [← Equiv.swap_apply_apply, hgb]
    exact (hTσ (g a) (σ (g a)) hne).mpr rfl
  · rw [← Equiv.swap_apply_apply, hgb]
    exact ⟨g a, σ (g a), hne, rfl⟩

private noncomputable def partner (T : Subgroup (Perm Ω)) (x : Ω) : Ω :=
  if h : ∃ y, y ≠ x ∧ swap x y ∈ T then h.choose else x

private lemma partner_spec {T : Subgroup (Perm Ω)} {x : Ω}
    (h : ∃ y, y ≠ x ∧ swap x y ∈ T) :
    partner T x ≠ x ∧ swap x (partner T x) ∈ T := by
  have hx : partner T x = h.choose := by
    show (if h' : ∃ y, y ≠ x ∧ swap x y ∈ T then h'.choose else x) = h.choose
    rw [dif_pos h]
  rw [hx]
  exact h.choose_spec

private lemma partner_eq_self {T : Subgroup (Perm Ω)} {x : Ω}
    (h : ¬ ∃ y, y ≠ x ∧ swap x y ∈ T) : partner T x = x := by
  show (if h' : ∃ y, y ≠ x ∧ swap x y ∈ T then h'.choose else x) = x
  rw [dif_neg h]

private lemma eq_of_swap_mem {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) {x y y' : Ω}
    (hyx : y ≠ x) (hy : swap x y ∈ T) (hy'x : y' ≠ x) (hy' : swap x y' ∈ T) : y = y' := by
  by_contra hne
  have hne' : swap x y ≠ swap x y' := by
    intro h
    exact hne (by
      have := congrArg (fun f : Perm Ω => f x) h
      simpa [Equiv.swap_apply_left] using this)
  have hd := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.disjoint_swap_of_pGroup
    hT.2.1 hy hy' ⟨x, y, hyx.symm, rfl⟩ ⟨x, y', hy'x.symm, rfl⟩ hne'
  have hx := hd x
  simp [Equiv.swap_apply_left, hyx, hy'x] at hx

private lemma partner_eq_iff {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) {x y : Ω}
    (hxy : x ≠ y) : partner T x = y ↔ swap x y ∈ T := by
  constructor
  · intro h
    by_cases h' : ∃ z, z ≠ x ∧ swap x z ∈ T
    · have hspec := partner_spec h'
      rw [h] at hspec
      exact hspec.2
    · rw [partner_eq_self h'] at h
      exact absurd h hxy
  · intro h
    have h' : ∃ z, z ≠ x ∧ swap x z ∈ T := ⟨y, hxy.symm, h⟩
    exact (eq_of_swap_mem hT hxy.symm h (partner_spec h').1 (partner_spec h').2).symm

private lemma partner_involutive {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) :
    Function.Involutive (partner T) := by
  intro x
  by_cases h : ∃ y, y ≠ x ∧ swap x y ∈ T
  · have hspec := partner_spec h
    have hx : partner T x = h.choose := by
      show (if h' : ∃ y, y ≠ x ∧ swap x y ∈ T then h'.choose else x) = h.choose
      rw [dif_pos h]
    have hx' : partner T h.choose = x :=
      (partner_eq_iff hT h.choose_spec.1).mpr (by rw [swap_comm]; exact h.choose_spec.2)
    rw [hx]
    exact hx'
  · rw [partner_eq_self h]
    exact partner_eq_self h

private lemma not_exists_swap_partner_iff {T : Subgroup (Perm Ω)} {x : Ω} :
    (¬ ∃ z, z ≠ x ∧ swap x z ∈ T) ↔ ∀ t ∈ T, t.IsSwap → t x = x := by
  constructor
  · intro h t htT htSwap
    obtain ⟨a, b, hab, rfl⟩ := htSwap
    by_contra htx
    have hxab : x = a ∨ x = b := by
      by_contra h'
      push Not at h'
      exact htx (Equiv.swap_apply_of_ne_of_ne h'.1 h'.2)
    rcases hxab with hxa | hxb
    · have hbx : b ≠ x := by rw [hxa]; exact hab.symm
      exact h ⟨b, hbx, by rw [hxa]; exact htT⟩
    · have hax : a ≠ x := by rw [hxb]; exact hab
      exact h ⟨a, hax, by rw [hxb, swap_comm]; exact htT⟩
  · rintro h ⟨z, hzx, hzT⟩
    have := h (swap x z) hzT ⟨x, z, hzx.symm, rfl⟩
    rw [Equiv.swap_apply_left] at this
    exact hzx this

private lemma partner_eq_self_iff {T : Subgroup (Perm Ω)} {x : Ω} :
    partner T x = x ↔ ∀ t ∈ T, t.IsSwap → t x = x := by
  rw [← not_exists_swap_partner_iff]
  exact ⟨fun h ⟨z, hz, hzT⟩ => (partner_spec ⟨z, hz, hzT⟩).1 h, partner_eq_self⟩

theorem exists_matching {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) :
    ∃ σ : Perm Ω, (∀ x, σ (σ x) = x) ∧ (∀ x y, x ≠ y → (swap x y ∈ T ↔ σ x = y)) ∧
      ∀ x y, σ x = x → σ y = y → x = y := by
  have hinv : Function.Involutive (partner T) := partner_involutive hT
  refine ⟨hinv.toPerm (partner T), ?_, ?_, ?_⟩
  · intro x
    change partner T (partner T x) = x
    exact hinv x
  · intro x y hxy
    change swap x y ∈ T ↔ partner T x = y
    exact (partner_eq_iff hT hxy).symm
  · intro x y hx hy
    apply eq_of_forall_isSwap_apply_eq hT
    · exact (partner_eq_self_iff.mp hx)
    · exact (partner_eq_self_iff.mp hy)

theorem setNormalizer_eq_centralizer {T : Subgroup (Perm Ω)} {σ : Perm Ω}
    (hσ : ∀ x, σ (σ x) = x) (hTσ : ∀ x y, x ≠ y → (swap x y ∈ T ↔ σ x = y)) :
    Subgroup.setNormalizer {t : Perm Ω | t ∈ T ∧ t.IsSwap} = Subgroup.centralizer {σ} := by
  classical
  change Subgroup.normalizer {t : Perm Ω | t ∈ T ∧ t.IsSwap} = Subgroup.centralizer {σ}
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (∀ s : Perm Ω, s ∈ {t : Perm Ω | t ∈ T ∧ t.IsSwap} ↔
    g * s * g⁻¹ ∈ {t : Perm Ω | t ∈ T ∧ t.IsSwap}) ↔ g * σ = σ * g
  constructor
  · intro hnorm
    ext x
    simp only [Equiv.Perm.mul_apply]
    by_cases hx : σ x = x
    · rw [hx]
      by_contra hne
      have hD : swap (g x) (σ (g x)) ∈ T ∧ (swap (g x) (σ (g x))).IsSwap :=
        ⟨(hTσ (g x) (σ (g x)) hne).mpr rfl, ⟨g x, σ (g x), hne, rfl⟩⟩
      have h1 := (hnorm (g⁻¹ * swap (g x) (σ (g x)) * g)).symm
      have h2 : g * (g⁻¹ * swap (g x) (σ (g x)) * g) * g⁻¹ =
          swap (g x) (σ (g x)) := by group
      rw [h2] at h1
      have hconj := h1.mp hD
      set t : Ω := g⁻¹ (σ (g x)) with ht
      have heq : g⁻¹ * swap (g x) (σ (g x)) * g = swap x t := by
        rw [ht]
        simpa using (Equiv.swap_apply_apply g⁻¹ (g x) (σ (g x))).symm
      have hDT : swap x t ∈ T := by rw [← heq]; exact hconj.1
      have hxt : x ≠ t := by
        intro h
        apply hne
        calc g x = g t := by rw [h]
          _ = σ (g x) := by rw [ht]; simp
      have hσxt : σ x = t := (hTσ x t hxt).mp hDT
      rw [hx] at hσxt
      have hgx : σ (g x) = g x := by
        calc σ (g x) = g t := by rw [ht]; simp
          _ = g x := by rw [← hσxt]
      exact hne hgx.symm
    · have hD : swap x (σ x) ∈ T ∧ (swap x (σ x)).IsSwap :=
        ⟨(hTσ x (σ x) (Ne.symm hx)).mpr rfl, ⟨x, σ x, Ne.symm hx, rfl⟩⟩
      have hconj := (hnorm (swap x (σ x))).mp hD
      have heq : g * swap x (σ x) * g⁻¹ = swap (g x) (g (σ x)) :=
        (Equiv.swap_apply_apply g x (σ x)).symm
      have hDT : swap (g x) (g (σ x)) ∈ T := by rw [← heq]; exact hconj.1
      have hne : g x ≠ g (σ x) := fun h => hx (g.injective h).symm
      exact ((hTσ (g x) (g (σ x)) hne).mp hDT).symm
  · intro hgcomm
    have hg : ∀ x, g (σ x) = σ (g x) := by
      intro x
      have := congrArg (fun f : Perm Ω => f x) hgcomm
      simpa only [Equiv.Perm.mul_apply] using this
    have hginv : ∀ x, g⁻¹ (σ x) = σ (g⁻¹ x) := by
      intro x
      have h1 : g (σ (g⁻¹ x)) = σ x := by
        rw [hg (g⁻¹ x)]
        simp
      calc g⁻¹ (σ x) = g⁻¹ (g (σ (g⁻¹ x))) := by rw [h1]
        _ = σ (g⁻¹ x) := by simp
    intro s
    constructor
    · intro hs
      exact conj_mem_swaps hTσ hg hs
    · intro hs
      have hmem := conj_mem_swaps hTσ hginv hs
      have heq : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
      rwa [heq] at hmem

theorem le_centralizer_of_matching {T : Subgroup (Perm Ω)} {σ : Perm Ω}
    (hσ : ∀ x, σ (σ x) = x) (hTσ : ∀ x y, x ≠ y → (swap x y ∈ T ↔ σ x = y)) :
    T ≤ Subgroup.centralizer {σ} := by
  rw [← setNormalizer_eq_centralizer hσ hTσ]
  change T ≤ Subgroup.normalizer {t : Perm Ω | t ∈ T ∧ t.IsSwap}
  intro t ht
  rw [Subgroup.mem_set_normalizer_iff]
  intro s
  constructor
  · rintro ⟨hsT, hsSwap⟩
    exact ⟨T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht), isSwap_conj hsSwap⟩
  · rintro ⟨hsT, hsSwap⟩
    have hmem : t⁻¹ * (t * s * t⁻¹) * t ∈ T :=
      T.mul_mem (T.mul_mem (T.inv_mem ht) hsT) ht
    have hswap : (t⁻¹ * (t * s * t⁻¹) * t).IsSwap := isSwap_conj hsSwap
    have heq : t⁻¹ * (t * s * t⁻¹) * t = s := by group
    rw [heq] at hmem hswap
    exact ⟨hmem, hswap⟩

theorem even_card_of_forall_apply_ne {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x ≠ x) : Even (Fintype.card Ω) := by
  classical
  let f : Function.End Ω := ⇑σ
  have hf : f = ⇑σ := rfl
  have h2 : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    change f (f x) = x
    rw [hf]
    exact hσ x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) h2
  have hset : Function.fixedPoints f = ∅ := by
    ext x
    rw [Function.mem_fixedPoints_iff]
    exact ⟨fun h => absurd (by simpa [f] using h) (hfix x), fun h => h.elim⟩
  have hcard : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff, hset]
    infer_instance
  rw [hcard] at hmod
  exact Nat.even_iff.mpr (by simpa [Nat.ModEq] using hmod)

theorem odd_card_of_apply_eq {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x) {α : Ω} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) : Odd (Fintype.card Ω) := by
  classical
  let f : Function.End Ω := ⇑σ
  have hf : f = ⇑σ := rfl
  have h2 : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    change f (f x) = x
    rw [hf]
    exact hσ x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) h2
  have hset : Function.fixedPoints f = {α} := by
    ext x
    rw [Function.mem_fixedPoints_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => by by_contra hne; exact hfix x hne (by simpa [f] using hx),
      fun hx => by rw [hx]; simpa [f] using hα⟩
  have hcard : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨α, by rw [Function.mem_fixedPoints_iff]; simpa [f] using hα⟩, fun y => ?_⟩
    apply Subtype.ext
    by_contra hne
    exact hfix y.1 hne (by
      have := Function.mem_fixedPoints_iff.mp y.2
      simpa [f] using this)
  rw [hcard] at hmod
  exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using hmod)

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
