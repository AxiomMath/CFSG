module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreClassify
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSym1
public import Mathlib.GroupTheory.Perm.ClosureSwap

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k13_zmod3_ne_zero_iff (c : ZMod 3) : c ≠ 0 ↔ c = 1 ∨ c = -1 := by
  have h : ∀ c : ZMod 3, c ≠ 0 ↔ c = 1 ∨ c = -1 := by decide
  exact h c

private lemma ggQ2s08k13_prod_eq_neg_one {N : ℕ} (ε : Fin N → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) (h1 : ∏ i, ε i ≠ 1) : ∏ i, ε i = -1 := by
  have h0 : ∏ i, ε i ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact hε i
  rcases (ggQ2s08k13_zmod3_ne_zero_iff _).1 h0 with h | h
  · exact absurd h h1
  · exact h

private lemma ggQ2s08k13_mono_of_monoEven {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {N : ℕ} {f : Fin N → V} {g : V ≃ₗ[ZMod 3] V} (h : GGQ2S08MonoEven f g) :
    GGQ2S08Mono f g := by
  obtain ⟨σ, ε, hε, _, hg⟩ := h
  exact ⟨σ, ε, hε, hg⟩

private lemma ggQ2s08k13_mono_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    {f : Fin N → V} {g : V ≃ₗ[ZMod 3] V} :
    GGQ2S08Mono f g ↔ ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, g (f i) = c i • f (σ i) := by
  constructor
  · rintro ⟨σ, c, hc, h⟩
    exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).1 (hc i), h⟩
  · rintro ⟨σ, c, hc, h⟩
    exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).2 (hc i), h⟩

private lemma ggQ2s08k13_monoEven_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    {f : Fin N → V} {g : V ≃ₗ[ZMod 3] V} :
    GGQ2S08MonoEven f g ↔ ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, g (f i) = c i • f (σ i) := by
  constructor
  · rintro ⟨σ, c, hc, hp, h⟩
    exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).1 (hc i), hp, h⟩
  · rintro ⟨σ, c, hc, hp, h⟩
    exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).2 (hc i), hp, h⟩

private lemma ggQ2s08k13_monoEven_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {N : ℕ} (b : Module.Basis (Fin N) (ZMod 3) V)
    {a r : V ≃ₗ[ZMod 3] V} {σa σr : Equiv.Perm (Fin N)} {εa εr : Fin N → ZMod 3}
    (hεa : ∀ i, εa i ≠ 0) (hεr : ∀ i, εr i ≠ 0)
    (ha : ∀ i, a (b i) = εa i • b (σa i)) (hr : ∀ i, r (b i) = εr i • b (σr i))
    (hpa : ∏ i, εa i = -1) (hpr : ∏ i, εr i = -1) :
    GGQ2S08MonoEven b (a * r) := by
  refine ⟨σa * σr, fun i => εr i * εa (σr i), ?_, ?_, ?_⟩
  · intro i
    exact mul_ne_zero (hεr i) (hεa (σr i))
  · rw [Finset.prod_mul_distrib, hpr, Equiv.prod_comp σr εa, hpa]
    decide
  · intro i
    show (a * r) (b i) = (εr i * εa (σr i)) • b ((σa * σr) i)
    rw [LinearEquiv.mul_apply, hr i, map_smul, ha (σr i), smul_smul, Equiv.Perm.mul_apply]

private lemma ggQ2s08k13_closure_eq_of_eq {G : Type} [Group G] {W R : Subgroup G} {r : G}
    (h : W = R) (hr : r ∈ R) : Subgroup.closure ((W : Set G) ∪ {r}) = R := by
  subst h
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hr
  · intro x hx
    exact Subgroup.subset_closure (Or.inl hx)

private lemma ggQ2s08k13_closure_swap_path {ℓ : ℕ} (a : Fin (ℓ + 1) → Fin (ℓ + 1))
    (hinj : Function.Injective a) :
    Subgroup.closure (Set.range (fun i : Fin ℓ =>
      Equiv.swap (a i.castSucc) (a i.succ))) = ⊤ := by
  have hbij : Function.Bijective a := Finite.injective_iff_bijective.mp hinj
  let σa : Equiv.Perm (Fin (ℓ + 1)) := Equiv.ofBijective a hbij
  let c : Equiv.Perm (Fin (ℓ + 1)) →* Equiv.Perm (Fin (ℓ + 1)) := (MulAut.conj σa).toMonoidHom
  let g : Fin ℓ → Equiv.Perm (Fin (ℓ + 1)) := fun i => Equiv.swap i.castSucc i.succ
  have hσ : ∀ i, σa i = a i := fun i => Equiv.ofBijective_apply a hbij i
  have hτ : ∀ i : Fin ℓ, Equiv.swap (a i.castSucc) (a i.succ) = σa * g i * σa⁻¹ := by
    intro i
    simpa only [hσ] using Equiv.swap_apply_apply σa i.castSucc i.succ
  have hrange : Set.range (fun i : Fin ℓ => Equiv.swap (a i.castSucc) (a i.succ)) =
      c '' Set.range g := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨g i, ⟨i, rfl⟩, ?_⟩
      show MulAut.conj σa (g i) = Equiv.swap (a i.castSucc) (a i.succ)
      rw [MulAut.conj_apply, ← hτ i]
    · rintro ⟨y, ⟨i, rfl⟩, hy⟩
      refine ⟨i, ?_⟩
      show Equiv.swap (a i.castSucc) (a i.succ) = p
      rw [hτ i, ← MulAut.conj_apply]
      exact hy
  have hg_top : Subgroup.closure (Set.range g) = ⊤ := by
    have h : Submonoid.closure (Set.range g) = ⊤ := Equiv.Perm.mclosure_swap_castSucc_succ ℓ
    have hle : Submonoid.closure (Set.range g) ≤ (Subgroup.closure (Set.range g)).toSubmonoid :=
      Submonoid.closure_le.mpr Subgroup.subset_closure
    rw [eq_top_iff]
    intro x _
    exact hle (by rw [h]; exact Submonoid.mem_top x)
  rw [hrange]
  calc Subgroup.closure (c '' Set.range g)
      = (Subgroup.closure (Set.range g)).map c := (MonoidHom.map_closure c (Set.range g)).symm
    _ = ⊤ := by
        rw [hg_top]
        exact Subgroup.map_top_of_surjective c (by
          show Function.Surjective c
          exact (MulAut.conj σa).surjective)

theorem ggQ2s08core_full_rank (hKG : GGReflClassLargeThree) {H : Type} [AddCommGroup H]
    [Module (ZMod 3) H] {ℓ : ℕ} (hℓ : 9 ≤ ℓ) (hdim : Module.finrank (ZMod 3) H = ℓ)
    (Rb Wb : Subgroup (H ≃ₗ[ZMod 3] H)) (hirr : ZS.AbsIrred 3 Rb)
    (hgen : Rb = Subgroup.closure {a | a ∈ Rb ∧ GGLinRefl a})
    (hsmall : 8 * Nat.card Rb < 3 ^ (ℓ * (ℓ - 1) / 2)) (hWR : Wb ≤ Rb) (hWirr : ZS.AbsIrred 3 Wb)
    (s : Fin ℓ → (H ≃ₗ[ZMod 3] H)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsR : ∀ i, s i ∈ Rb) (hsrefl : ∀ i, GGLinRefl (s i))
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : Wb = Subgroup.closure (Set.range s))
    (r : H ≃ₗ[ZMod 3] H) (hrR : r ∈ Rb) (hr : GGLinRefl r) (hrW : r ∉ Wb) :
    Subgroup.closure ((Wb : Set (H ≃ₗ[ZMod 3] H)) ∪ {r}) = Rb := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h4 : 4 ≤ ℓ := by omega
  have hgenW : Wb = Subgroup.closure {a | a ∈ Wb ∧ GGLinRefl a} := by
    apply le_antisymm
    · rw [hWs]
      rw [Subgroup.closure_le]
      rintro a ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨i, rfl⟩, hsrefl i⟩
    · rw [Subgroup.closure_le]
      rintro a ⟨ha, _⟩
      exact ha
  rcases ggRC_classify_frame3 hKG hdim hℓ Rb hirr hgen hsmall with
    ⟨b, hR⟩ | ⟨e, he⟩ | ⟨e, he⟩
  ·
    have hmonW : ∀ a ∈ Wb, ∃ (σ : Equiv.Perm (Fin ℓ)) (c : Fin ℓ → ZMod 3),
        (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i) := by
      intro a ha
      have haR : a ∈ Rb := hWR ha
      rcases hR with hRmono | hReven
      · obtain ⟨σ, c, hc, h⟩ := (hRmono a).mp haR
        exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).1 (hc i), h⟩
      · obtain ⟨σ, c, hc, _, h⟩ := (hReven a).mp haR
        exact ⟨σ, c, fun i => (ggQ2s08k13_zmod3_ne_zero_iff (c i)).1 (hc i), h⟩
    have hWclass : (∀ a, a ∈ Wb ↔ GGQ2S08Mono b a) ∨
        (∀ a, a ∈ Wb ↔ GGQ2S08MonoEven b a) := by
      rcases ggRC_signed_class hp2 h4 b Wb hWirr hgenW hmonW with hB | hD
      · exact Or.inl fun a => (hB a).trans ggQ2s08k13_mono_iff.symm
      · exact Or.inr fun a => (hD a).trans ggQ2s08k13_monoEven_iff.symm
    rcases hWclass with hWmono | hWeven
    · rcases hR with hRmono | hReven
      ·
        exact ggQ2s08k13_closure_eq_of_eq
          (le_antisymm hWR fun a ha => (hWmono a).mpr ((hRmono a).mp ha)) hrR
      ·
        have hWeq : Wb = Rb := le_antisymm hWR fun a ha =>
          (hWmono a).mpr (ggQ2s08k13_mono_of_monoEven ((hReven a).mp ha))
        exact absurd (hWeq ▸ hrR) hrW
    · rcases hR with hRmono | hReven
      ·
        obtain ⟨σr, εr, hεr, hr_apply⟩ := (hRmono r).mp hrR
        have hpr : ∏ i, εr i = -1 :=
          ggQ2s08k13_prod_eq_neg_one εr hεr fun h1 =>
            hrW ((hWeven r).mpr ⟨σr, εr, hεr, h1, hr_apply⟩)
        have hKle : Subgroup.closure ((Wb : Set (H ≃ₗ[ZMod 3] H)) ∪ {r}) ≤ Rb := by
          rw [Subgroup.closure_le]
          rintro x (hx | hx)
          · exact hWR hx
          · rw [Set.mem_singleton_iff] at hx
            exact hx ▸ hrR
        apply le_antisymm hKle
        intro a ha
        obtain ⟨σa, εa, hεa, ha_apply⟩ := (hRmono a).mp ha
        by_cases hpa : ∏ i, εa i = 1
        · exact Subgroup.subset_closure
            (Or.inl ((hWeven a).mpr ⟨σa, εa, hεa, hpa, ha_apply⟩))
        · have hpa' : ∏ i, εa i = -1 := ggQ2s08k13_prod_eq_neg_one εa hεa hpa
          have har : a * r ∈ Wb := (hWeven (a * r)).mpr
            (ggQ2s08k13_monoEven_mul b hεa hεr ha_apply hr_apply hpa' hpr)
          have h1 : a * r ∈ Subgroup.closure ((Wb : Set (H ≃ₗ[ZMod 3] H)) ∪ {r}) :=
            Subgroup.subset_closure (Or.inl har)
          have h2 : r⁻¹ ∈ Subgroup.closure ((Wb : Set (H ≃ₗ[ZMod 3] H)) ∪ {r}) :=
            Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr (Set.mem_singleton r)))
          have h3 := Subgroup.mul_mem _ h1 h2
          simpa only [mul_assoc, mul_inv_cancel, mul_one] using h3
      ·
        exact ggQ2s08k13_closure_eq_of_eq
          (le_antisymm hWR fun a ha => (hWeven a).mpr ((hReven a).mp ha)) hrR
  ·
    let τ : Fin ℓ → Equiv.Perm (Fin (ℓ + 1)) := fun i => e ⟨s i, hsR i⟩
    have hsw : ∀ i, (τ i).IsSwap := by
      intro i
      obtain ⟨p, q, hpq, heq⟩ := he ⟨s i, hsR i⟩ (hsrefl i)
      exact ⟨p, q, hpq, heq⟩
    have hne : ∀ i j, i ≠ j → τ i ≠ τ j := by
      intro i j hij h
      exact hdist i j hij (congrArg Subtype.val (e.injective h))
    have hrel' : ∀ i j, i ≠ j → (τ i * τ j) ^ M i j = 1 := by
      intro i j hij
      have h1 : (⟨s i, hsR i⟩ * ⟨s j, hsR j⟩ : Rb) ^ M i j = 1 := by
        apply Subtype.ext
        simpa using hrel i j hij
      have hmul : τ i * τ j = e (⟨s i, hsR i⟩ * ⟨s j, hsR j⟩) := by
        rw [map_mul]
      rw [hmul, ← map_pow, h1, map_one]
    have hncomm' : ∀ i j, i ≠ j → M i j ≠ 2 → τ i * τ j ≠ τ j * τ i := by
      intro i j hij hMij h
      apply hncomm i j hij hMij
      have h' : (⟨s i, hsR i⟩ * ⟨s j, hsR j⟩ : Rb) = ⟨s j, hsR j⟩ * ⟨s i, hsR i⟩ := by
        apply e.injective
        simpa only [map_mul] using h
      exact congrArg Subtype.val h'
    obtain ⟨_, a, hinj, hτ⟩ :=
      ggQ2s08core_swap_coxeter hℓ τ hsw hne M hM hrel' hncomm'
    have hclosure : Subgroup.closure (Set.range τ) = ⊤ := by
      rw [show τ = (fun i : Fin ℓ => Equiv.swap (a i.castSucc) (a i.succ)) from funext hτ]
      exact ggQ2s08k13_closure_swap_path a hinj
    have hWbR : Subgroup.map e.toMonoidHom (Wb.subgroupOf Rb) = ⊤ := by
      rw [eq_top_iff, ← hclosure]
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      have hsi : s i ∈ Wb := by
        rw [hWs]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨s i, hsR i⟩, Subgroup.mem_subgroupOf.mpr hsi, rfl⟩
    have hWeq : Wb = Rb := by
      apply le_antisymm hWR
      intro a ha
      have hx : e ⟨a, ha⟩ ∈ Subgroup.map e.toMonoidHom (Wb.subgroupOf Rb) := by
        rw [hWbR]
        exact Subgroup.mem_top _
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hyx' : e y = e ⟨a, ha⟩ := hyx
      rw [e.injective hyx'] at hy
      exact Subgroup.mem_subgroupOf.mp hy
    exact ggQ2s08k13_closure_eq_of_eq hWeq hrR
  ·
    exact ggQ2s08core_sym1 hℓ Rb Wb hWR e he s M hM hsR hsrefl hrel hdist hncomm hWs
      r hrR hr hrW

end CFSG.StandardType

end
