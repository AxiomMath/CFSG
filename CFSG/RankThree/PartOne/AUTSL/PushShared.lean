module

public import CFSG.RankThree.PartOne.AUTSL.KF1514S0
public import CFSG.RankThree.PartOne.U5K.Hyp.Thompson
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace AUTSL

open Module

section Offender

variable {M : Type} [Group M] [Finite M]

theorem pushingUpS_eq_of_offender_free {T V : Subgroup M} {n : ℕ} (hVT : V ≤ T)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVs : ∀ x ∈ V, x ^ 2 = 1)
    (hVcard : Nat.card V = 2 ^ n) (hCT : ∀ t ∈ T, (∀ v ∈ V, v * t = t * v) → t ∈ V)
    (hoff : ∀ F : Subgroup M, F ≤ T → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      (∀ x ∈ F, x ^ 2 = 1) → ¬ F ≤ V →
        (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) < Nat.card V) :
    pushingUpS T = V := by
  have hcenter : (elemThompsonCenterTorsion ↥T 2).map T.subtype = V := by
    refine U5K.Hyp.elemCenter_eq_of_max hVT hVc hVs hVcard fun F hFT hc hs => ?_
    by_cases hFV : F ≤ V
    · refine ⟨hVcard ▸ Subgroup.card_le_of_le hFV, fun hcard => ?_⟩
      exact Subgroup.eq_of_le_of_card_ge hFV (by rw [hcard, hVcard])
    · have h1 := hoff F hFT hc hs hFV
      have h2 : Nat.card F = (F ⊓ V).relIndex F * Nat.card ↥(F ⊓ V) := by
        have := Subgroup.relIndex_mul_card (F ⊓ V) F
        rw [inf_eq_left.mpr (inf_le_left : F ⊓ V ≤ F)] at this
        exact this.symm
      have h3 : Nat.card ↥(F ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) := by
        refine Subgroup.card_le_of_le ?_
        intro x hx
        refine ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        exact (hc y hy x hx.1)
      have h4 : Nat.card F < Nat.card V := by
        calc Nat.card F = (F ⊓ V).relIndex F * Nat.card ↥(F ⊓ V) := h2
          _ ≤ (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) :=
            Nat.mul_le_mul_left _ h3
          _ < Nat.card V := h1
      rw [hVcard] at h4
      exact ⟨h4.le, fun h => absurd h (by omega)⟩
  have hP : pushingUpS T = T ⊓ Subgroup.centralizer (V : Set M) := by
    unfold pushingUpS
    rw [← hcenter]
    rfl
  rw [hP]
  apply le_antisymm
  · rintro t ⟨htT, htC⟩
    exact hCT t htT fun v hv => (Subgroup.mem_centralizer_iff.1 htC v hv)
  · intro v hv
    exact ⟨hVT hv, Subgroup.mem_centralizer_iff.2 fun w hw => (hVc w hw v hv)⟩

end Offender

section Artin

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def fixSubfield (σ : K ≃+* K) : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)

theorem mem_fixSubfield {σ : K ≃+* K} {x : K} : x ∈ fixSubfield σ ↔ σ x = x := Iff.rfl

theorem independent_of_fixed {k : ℕ} (σ : K ≃+* K) (ψ : V →+ V)
    (hψ : ∀ (c : K) (v : V), ψ (c • v) = σ c • ψ v) (w : Fin k → V) (hw : ∀ i, ψ (w i) = w i)
    (h0 : ∀ g : Fin k → K, (∀ i, σ (g i) = g i) → ∑ i, g i • w i = 0 → g = 0) :
    ∀ g : Fin k → K, ∑ i, g i • w i = 0 → g = 0 := by
  classical
  intro g
  induction' hn : (Finset.univ.filter fun i => g i ≠ 0).card using Nat.strong_induction_on with n ih
    generalizing g
  intro hsum
  by_contra hg
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, g i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  set g' : Fin k → K := fun i => (g i₀)⁻¹ * g i with hg'
  have hsum' : ∑ i, g' i • w i = 0 := by
    simp only [hg', mul_smul]
    rw [← Finset.smul_sum, hsum, smul_zero]
  have hψsum : ∑ i, σ (g' i) • w i = 0 := by
    have := congrArg ψ hsum'
    rw [map_sum, map_zero] at this
    simpa [hψ, hw] using this
  have hsumd : ∑ i, (σ (g' i) - g' i) • w i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hψsum, hsum', sub_zero]
  have hd : (fun i => σ (g' i) - g' i) = 0 := by
    refine ih (Finset.univ.filter fun i => σ (g' i) - g' i ≠ 0).card ?_ (fun i => σ (g' i) - g' i)
      rfl hsumd
    rw [← hn]
    refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i₀, ?_, ?_⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro hgi
      apply hi
      simp [hg', hgi]
    · simp [hi₀]
    · have h1 : g' i₀ = 1 := by simp [hg', inv_mul_cancel₀ hi₀]
      simp [h1]
  have hfix : ∀ i, σ (g' i) = g' i := fun i => sub_eq_zero.1 (congrFun hd i)
  have := h0 g' hfix hsum'
  have h1 := congrFun this i₀
  simp [hg', inv_mul_cancel₀ hi₀] at h1

variable [Finite K] [FiniteDimensional K V]

def fixSubmodule (σ : K ≃+* K) (ψ : V →+ V) (hψ : ∀ (c : K) (v : V), ψ (c • v) = σ c • ψ v) :
    Submodule (fixSubfield σ) V where
  carrier := {v | ψ v = v}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := fun c v hv => by
    have hc : σ (c : K) = (c : K) := c.2
    have h1 : ψ ((c : K) • v) = (c : K) • v := by
      rw [hψ, hc]
      exact congrArg _ hv
    simpa [Subfield.smul_def] using h1

theorem card_fix_le (σ : K ≃+* K) (ψ : V →+ V) (hψ : ∀ (c : K) (v : V), ψ (c • v) = σ c • ψ v) :
    Nat.card {v : V // ψ v = v} ≤ Nat.card (fixSubfield σ) ^ finrank K V := by
  classical
  have : Finite V := Module.finite_of_finite K
  set W := fixSubmodule σ ψ hψ with hW
  have hfinW : Module.Finite (fixSubfield σ) W := Module.Finite.of_finite
  set k := finrank (fixSubfield σ) W with hk
  let b : Basis (Fin k) (fixSubfield σ) W := Module.finBasis (fixSubfield σ) W
  let w : Fin k → V := fun i => (b i : V)
  have hw : ∀ i, ψ (w i) = w i := fun i => (b i).2
  have hind : ∀ g : Fin k → K, ∑ i, g i • w i = 0 → g = 0 := by
    refine independent_of_fixed σ ψ hψ w hw fun g hg hsum => ?_
    let g₀ : Fin k → fixSubfield σ := fun i => ⟨g i, hg i⟩
    have h1 : ∑ i, g₀ i • b i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      simpa [g₀, w, Subfield.smul_def] using hsum
    have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent g₀ h1
    funext i
    have := h2 i
    simpa [g₀] using congrArg Subtype.val this
  have hli : LinearIndependent K w :=
    Fintype.linearIndependent_iff.2 fun g hg i => congrFun (hind g hg) i
  have hkle : k ≤ finrank K V := by
    simpa using hli.fintype_card_le_finrank
  have hcard : Nat.card W = Nat.card (fixSubfield σ) ^ k := Module.natCard_eq_pow_finrank
  calc Nat.card {v : V // ψ v = v} = Nat.card W := rfl
    _ = Nat.card (fixSubfield σ) ^ k := hcard
    _ ≤ Nat.card (fixSubfield σ) ^ finrank K V :=
      Nat.pow_le_pow_right Nat.card_pos hkle

theorem card_fix_mul_le {n : ℕ} (hn : 2 ≤ n) (hV : finrank K V = n) (σ : K ≃+* K) (ψ : V →+ V)
    (hψ : ∀ (c : K) (v : V), ψ (c • v) = σ c • ψ v) (hne : ∃ v, ψ v ≠ v) :
    Nat.card {v : V // ψ v = v} * Nat.card K ≤ Nat.card V := by
  classical
  have : Finite V := Module.finite_of_finite K
  have hVcard : Nat.card V = Nat.card K ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := V), hV]
  by_cases hσ : ∀ c, σ c = c
  ·
    let W : Submodule K V :=
      { carrier := {v | ψ v = v}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
          rw [ha, hb]
        zero_mem' := by simp
        smul_mem' := fun c v hv => by
          have h1 : ψ (c • v) = c • v := by
            rw [hψ, hσ]
            exact congrArg _ hv
          simpa using h1 }
    have hWne : W ≠ ⊤ := by
      intro h
      obtain ⟨v, hv⟩ := hne
      exact hv (by
        have : v ∈ W := h ▸ Submodule.mem_top
        exact this)
    have hlt : finrank K W < finrank K V := Submodule.finrank_lt hWne
    have hWcard : Nat.card W = Nat.card K ^ finrank K W := Module.natCard_eq_pow_finrank
    have h1 : Nat.card {v : V // ψ v = v} = Nat.card K ^ finrank K W := hWcard
    rw [h1, hVcard, ← pow_succ]
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)
  · push Not at hσ
    obtain ⟨a, ha⟩ := hσ
    set K₀ := fixSubfield σ with hK₀
    have hfin : Module.Finite K₀ K := Module.Finite.of_finite
    have hK : Nat.card K = Nat.card K₀ ^ finrank K₀ K := Module.natCard_eq_pow_finrank
    have hge1 : 1 ≤ finrank K₀ K := Module.finrank_pos
    have hge2 : 2 ≤ finrank K₀ K := by
      by_contra hlt
      have h1 : finrank K₀ K = 1 := by omega
      rw [finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero] at h1
      obtain ⟨c, hc⟩ := h1 a
      apply ha
      have : (c : K) = a := by simpa [Subfield.smul_def] using hc
      rw [← this]
      exact c.2
    have hK0 : Nat.card K₀ ^ 2 ≤ Nat.card K := by
      rw [hK]
      exact Nat.pow_le_pow_right Nat.card_pos hge2
    have hfix := card_fix_le σ ψ hψ
    rw [hV] at hfix
    set F := Nat.card {v : V // ψ v = v}
    have hq : 0 < Nat.card K := Nat.card_pos
    have h2 : (F * Nat.card K) ^ 2 ≤ (Nat.card V) ^ 2 := by
      calc (F * Nat.card K) ^ 2 = F ^ 2 * Nat.card K ^ 2 := by ring
        _ ≤ (Nat.card K₀ ^ n) ^ 2 * Nat.card K ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hfix 2)
        _ = (Nat.card K₀ ^ 2) ^ n * Nat.card K ^ 2 := by ring
        _ ≤ Nat.card K ^ n * Nat.card K ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hK0 n)
        _ ≤ Nat.card K ^ n * Nat.card K ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq hn)
        _ = (Nat.card V) ^ 2 := by rw [hVcard]; ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2

end Artin

section Sylow

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem map_conj_self_of_mem {K : Subgroup M} {g : M} (hg : g ∈ K) :
    K.map (MulAut.conj g).toMonoidHom = K :=
  map_conj_eq_of_mem (K := K) (I := K) Subgroup.le_normalizer hg

theorem exists_isSylowOf_inf_eq {H N U : Subgroup M} (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set M)) (hU : IsSylowOf 2 U N) :
    ∃ T : Subgroup M, IsSylowOf 2 T H ∧ T ⊓ N = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 H
  have hT₁' : IsSylowOf 2 T₁ H := CFSG.ABGLocalTools.isSylowOf_iff.1 hT₁
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (T₁ ⊓ N) N := hT₁.inf_of_le_normalizer hNH hHN
  have h1' : IsSylowOf 2 (T₁ ⊓ N) N := CFSG.ABGLocalTools.isSylowOf_iff.1 h1
  obtain ⟨i, hi, hiU⟩ := exists_conj_isSylowOf h1' hU
  refine ⟨T₁.map (MulAut.conj i).toMonoidHom, ?_, ?_⟩
  · have := Sec9B.isSylowOf_map (f := (MulAut.conj i).toMonoidHom) (MulAut.conj i).injective hT₁'
    rwa [map_conj_self_of_mem (hNH hi)] at this
  · rw [hiU, Subgroup.map_inf _ _ _ (MulAut.conj i).injective, map_conj_eq_of_mem hHN (hNH hi)]

theorem exists_ne_one_mem_center_of_normal {T X : Subgroup M} (hT : IsPGroup 2 T)
    (hXT : X ≤ T) (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let X' : Subgroup ↥T := X.subgroupOf T
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : ↥T) : M) ∈ X
    have : ((t * x * t⁻¹ : ↥T) : M) = (t : M) * (x : M) * (t : M)⁻¹ := rfl
    rw [this]
    exact hXn t t.2 x hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X' := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzX : ((z : ↥T) : M) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : ↥T) : M), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (hzc ⟨t, ht⟩)

end Sylow

section Assembly

variable {L : Type} [Group L]

abbrev InnL (L : Type) [Group L] : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range

theorem InnL_normalizer (H : Subgroup (MulAut L)) :
    H ≤ Subgroup.normalizer (InnL L : Set (MulAut L)) := by
  have key : ∀ φ : MulAut L, ∀ i ∈ InnL L, φ * i * φ⁻¹ ∈ InnL L := by
    rintro φ _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  intro h _
  rw [Subgroup.mem_normalizer_iff]
  intro i
  refine ⟨fun hi => key h i hi, fun hi => ?_⟩
  have := key h⁻¹ _ hi
  simpa [mul_assoc] using this

theorem kf1514PAutGen_of_data [Finite L] {p : ℕ} (U V X : Subgroup (MulAut L))
    (hU : IsSylowOf 2 U (InnL L))
    (hS : ∀ T : Subgroup (MulAut L), IsPGroup 2 T → T ⊓ InnL L = U → pushingUpS T = V)
    (hX0 : X ≠ ⊥) (hXU : X ≤ U) (hXs : ∀ x ∈ X, x ^ 2 = 1)
    (hXn : ∀ T : Subgroup (MulAut L), IsPGroup 2 T → T ⊓ InnL L = U →
      ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hA : ∀ A₀ : Subgroup (MulAut L), A₀ ≤ InnL L → IsElementaryAbelian p ↥A₀ →
      Nat.card ↥A₀ = p ^ 3 →
      ∃ g ∈ InnL L,
        (∃ B : Subgroup (MulAut L), B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
          B.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (V : Set (MulAut L))) ∧
        (∃ B : Subgroup (MulAut L), B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
          ∀ x ∈ X, x ≠ 1 →
            B.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({x} : Set (MulAut L)))) :
    KF1514PAutGen L p := by
  intro H A₀ hInnH hA₀Inn hel hcard
  have hnorm := InnL_normalizer (L := L) H
  obtain ⟨T₂, hT₂, hT₂U⟩ := exists_isSylowOf_inf_eq hInnH hnorm hU
  have hT₂p : IsPGroup 2 T₂ := hT₂.2.1
  have hS₂ : pushingUpS T₂ = V := hS T₂ hT₂p hT₂U
  have hXT : X ≤ T₂ := fun x hx => by
    have : x ∈ T₂ ⊓ InnL L := hT₂U ▸ hXU hx
    exact this.1
  obtain ⟨x₀, hx₀X, hx₀1, hx₀c⟩ :=
    exists_ne_one_mem_center_of_normal hT₂p hXT (hXn T₂ hT₂p hT₂U) hX0
  obtain ⟨g, hgInn, ⟨B₁, hB₁A, hB₁c, hB₁n⟩, ⟨B₂, hB₂A, hB₂c, hB₂n⟩⟩ := hA A₀ hA₀Inn hel hcard
  set f : MulAut L →* MulAut L := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hcompinj : Function.Injective (f.comp T₂.subtype) := hfinj.comp T₂.subtype_injective
  have hgH : g ∈ H := hInnH hgInn
  have hHf : H.map f = H := map_conj_self_of_mem (Subgroup.inv_mem H hgH)
  refine ⟨T₂.map f, ?_, ⟨B₁, hB₁A, hB₁c, ?_⟩, ⟨f x₀, ?_, ?_, B₂, hB₂A, hB₂c, ?_⟩⟩
  · have := Sec9B.isSylowOf_map hfinj hT₂
    rwa [hHf] at this
  · rw [← U5K.map_pushingUpS f hcompinj, hS₂, ← Subgroup.map_normalizer_eq_of_bijective V
      (MulAut.conj g⁻¹).bijective]
    intro b hb
    refine ⟨g * b * g⁻¹, hB₁n ⟨b, hb, rfl⟩, ?_⟩
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rw [← Sec1514Five.map_omegaOneCenterIn f hcompinj]
    refine ⟨x₀, ?_, rfl⟩
    have hx₀T : x₀ ∈ T₂ := hXT hx₀X
    exact Subgroup.subset_closure ⟨⟨⟨x₀, hx₀T⟩, Subgroup.mem_center_iff.2 fun t =>
      Subtype.ext (hx₀c t t.2), rfl⟩, hXs x₀ hx₀X⟩
  · intro h
    apply hx₀1
    exact hfinj (h.trans (map_one f).symm)
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have h1 := Subgroup.mem_centralizer_iff.1 (hB₂n x₀ hx₀X hx₀1 ⟨b, hb, rfl⟩) x₀ rfl
    have h2 : x₀ * (g * b * g⁻¹) = g * b * g⁻¹ * x₀ := h1
    have hfx : f x₀ = g⁻¹ * x₀ * g := by simp [hf]
    rw [hfx]
    calc g⁻¹ * x₀ * g * b = g⁻¹ * (x₀ * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * x₀) * g := by rw [h2]
      _ = b * (g⁻¹ * x₀ * g) := by group

end Assembly

section Bounds

variable {M : Type} [Group M] [Finite M]

theorem offender_free_of_bounds {T Û V : Subgroup M} {m B₁ B₂ : ℕ} (hVÛ : V ≤ Û) (hm1 : 1 ≤ m)
    (ha : ∀ F : Subgroup M, F ≤ T → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
      (F ⊓ Û).relIndex F ≤ m)
    (hb : ∀ F : Subgroup M, F ≤ Û → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
      ¬ F ≤ V →
        (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) ≤ B₁)
    (hc : ∀ t ∈ T, t ∉ Û → Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set M)) ≤ B₂)
    (hB₁ : m * B₁ < Nat.card V) (hB₂ : m * B₂ < Nat.card V) :
    ∀ F : Subgroup M, F ≤ T → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
      ¬ F ≤ V →
        (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) < Nat.card V := by
  intro F hFT hFc hFs hFV
  by_cases hFÛ : F ≤ Û
  · have := hb F hFÛ hFc hFs hFV
    calc _ ≤ B₁ := this
      _ ≤ m * B₁ := Nat.le_mul_of_pos_left _ hm1
      _ < Nat.card V := hB₁
  ·
    have hF₀m := ha F hFT hFc hFs
    have hFVF₀ : F ⊓ V ≤ F ⊓ Û := inf_le_inf_left _ hVÛ
    have hchain : (F ⊓ V).relIndex (F ⊓ Û) * (F ⊓ Û).relIndex F = (F ⊓ V).relIndex F :=
      Subgroup.relIndex_mul_relIndex _ _ _ hFVF₀ inf_le_left
    have hF₀c : ∀ x ∈ F ⊓ Û, ∀ y ∈ F ⊓ Û, x * y = y * x := fun x hx y hy => hFc x hx.1 y hy.1
    have hF₀s : ∀ x ∈ F ⊓ Û, x ^ 2 = 1 := fun x hx => hFs x hx.1
    have hCle : ∀ F' : Subgroup M, F' ≤ F → Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (F' : Set M)) := fun F' hF' => by
      refine Subgroup.card_le_of_le (inf_le_inf_left _ ?_)
      exact Subgroup.centralizer_le hF'
    by_cases hF₀V : F ⊓ Û ≤ V
    ·
      obtain ⟨t, htF, htÛ⟩ : ∃ t ∈ F, t ∉ Û := by
        by_contra h
        push Not at h
        exact hFÛ h
      have h1 : (F ⊓ V).relIndex (F ⊓ Û) = 1 := by
        have : F ⊓ Û ≤ F ⊓ V := le_inf inf_le_left hF₀V
        have heq : F ⊓ V = F ⊓ Û := le_antisymm hFVF₀ this
        rw [heq]
        exact Subgroup.relIndex_self _
      have h2 : (F ⊓ V).relIndex F ≤ m := by
        rw [← hchain, h1, one_mul]
        exact hF₀m
      have h3 : Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) ≤ B₂ := by
        refine (Subgroup.card_le_of_le (inf_le_inf_left _ ?_)).trans (hc t (hFT htF) htÛ)
        refine Subgroup.centralizer_le ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact htF
      calc _ ≤ m * B₂ := Nat.mul_le_mul h2 h3
        _ < Nat.card V := hB₂
    · have hb' := hb (F ⊓ Û) inf_le_right hF₀c hF₀s hF₀V
      have hcomm : (F ⊓ Û ⊓ V) = F ⊓ V := by
        rw [inf_assoc, inf_eq_right.mpr hVÛ]
      rw [hcomm] at hb'
      have h3 := hCle (F ⊓ Û) inf_le_left
      calc (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M))
          = (F ⊓ V).relIndex (F ⊓ Û) * (F ⊓ Û).relIndex F *
              Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) := by rw [hchain]
        _ ≤ (F ⊓ Û).relIndex F * ((F ⊓ V).relIndex (F ⊓ Û) *
              Nat.card ↥(V ⊓ Subgroup.centralizer ((F ⊓ Û : Subgroup M) : Set M))) := by
            rw [mul_comm ((F ⊓ V).relIndex (F ⊓ Û)), mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ ≤ m * B₁ := by
            have h4 : (F ⊓ V).relIndex (F ⊓ Û) *
                Nat.card ↥(V ⊓ Subgroup.centralizer ((F ⊓ Û : Subgroup M) : Set M)) ≤ B₁ := by
              have := hb'
              have hh : (F ⊓ Û ⊓ V).relIndex (F ⊓ Û) = (F ⊓ V).relIndex (F ⊓ Û) := by rw [hcomm]
              simpa [hcomm] using this
            exact Nat.mul_le_mul hF₀m h4
        _ < Nat.card V := hB₁

theorem pushingUpS_eq_of_bounds {T Û V : Subgroup M} {n m B₁ B₂ : ℕ} (hVÛ : V ≤ Û) (hVT : V ≤ T)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVs : ∀ x ∈ V, x ^ 2 = 1)
    (hVcard : Nat.card V = 2 ^ n) (hCT : ∀ t ∈ T, (∀ v ∈ V, v * t = t * v) → t ∈ V)
    (hm1 : 1 ≤ m)
    (ha : ∀ F : Subgroup M, F ≤ T → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
      (F ⊓ Û).relIndex F ≤ m)
    (hb : ∀ F : Subgroup M, F ≤ Û → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
      ¬ F ≤ V →
        (F ⊓ V).relIndex F * Nat.card ↥(V ⊓ Subgroup.centralizer (F : Set M)) ≤ B₁)
    (hc : ∀ t ∈ T, t ∉ Û → Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set M)) ≤ B₂)
    (hB₁ : m * B₁ < Nat.card V) (hB₂ : m * B₂ < Nat.card V) :
    pushingUpS T = V :=
  pushingUpS_eq_of_offender_free hVT hVc hVs hVcard hCT
    (offender_free_of_bounds hVÛ hm1 ha hb hc hB₁ hB₂)

end Bounds

end AUTSL

end CFSG.RankThree.PartOne
