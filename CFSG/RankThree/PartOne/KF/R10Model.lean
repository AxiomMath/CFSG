module

public import CFSG.RankThree.PartOne.KF.SpQuad
public import CFSG.RankThree.PartOne.KF.Z2S4Mod

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] def IsSgn (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (x y : Fin 3 → (Qext K)ˣ) : Prop :=
  ∀ i, y i = if s (π.symm i) then (x (π.symm i))⁻¹ else x (π.symm i)

section Dictionary

omit [Finite K] in
theorem isSgn_swap12 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 0 1) ![false, false, false] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 1 2) d)) := by
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def]

omit [Finite K] in
theorem isSgn_swap13 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 0 2) ![false, false, false] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 1 3) d)) := by
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def]

omit [Finite K] in
theorem isSgn_swap23 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 1 2) ![false, false, false] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 2 3) d)) := by
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def]

omit [Finite K] in
theorem isSgn_swap01 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 1 2) ![false, true, true] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 0 1) d)) := by
  have h' : ((d : Fin 4 → (Qext K)ˣ) 0 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 1 : Qext K) *
      ((d : Fin 4 → (Qext K)ˣ) 2 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 3 : Qext K) = 1 := by
    simpa using congrArg Units.val (torusVec_prod_four d)
  have hne : ∀ j, (((d : Fin 4 → (Qext K)ˣ) j : (Qext K)ˣ) : Qext K) ≠ 0 := fun j =>
    ((d : Fin 4 → (Qext K)ˣ) j).ne_zero
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def] <;>
    first
    | done
    | (apply Units.ext
       simp only [Units.val_mul, Units.val_inv_eq_inv_val]
       have := hne 0
       have := hne 1
       have := hne 2
       have := hne 3
       field_simp
       try first | linear_combination h' | linear_combination -h')

omit [Finite K] in
theorem isSgn_swap02 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 0 2) ![true, false, true] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 0 2) d)) := by
  have h' : ((d : Fin 4 → (Qext K)ˣ) 0 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 1 : Qext K) *
      ((d : Fin 4 → (Qext K)ˣ) 2 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 3 : Qext K) = 1 := by
    simpa using congrArg Units.val (torusVec_prod_four d)
  have hne : ∀ j, (((d : Fin 4 → (Qext K)ˣ) j : (Qext K)ˣ) : Qext K) ≠ 0 := fun j =>
    ((d : Fin 4 → (Qext K)ˣ) j).ne_zero
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def] <;>
    first
    | done
    | (apply Units.ext
       simp only [Units.val_mul, Units.val_inv_eq_inv_val]
       have := hne 0
       have := hne 1
       have := hne 2
       have := hne 3
       field_simp
       try first | linear_combination h' | linear_combination -h')

omit [Finite K] in
theorem isSgn_swap03 (d : torusVec p 4 (Qext K)) :
    IsSgn (Equiv.swap 0 1) ![true, true, false] (sqCoords d)
      (sqCoords (symAct p (Qext K) (Equiv.swap 0 3) d)) := by
  have h' : ((d : Fin 4 → (Qext K)ˣ) 0 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 1 : Qext K) *
      ((d : Fin 4 → (Qext K)ˣ) 2 : Qext K) * ((d : Fin 4 → (Qext K)ˣ) 3 : Qext K) = 1 := by
    simpa using congrArg Units.val (torusVec_prod_four d)
  have hne : ∀ j, (((d : Fin 4 → (Qext K)ˣ) j : (Qext K)ˣ) : Qext K) ≠ 0 := fun j =>
    ((d : Fin 4 → (Qext K)ˣ) j).ne_zero
  intro i
  fin_cases i <;> simp [coe_symAct, sqCoords_apply, Equiv.swap_apply_def] <;>
    first
    | done
    | (apply Units.ext
       simp only [Units.val_mul, Units.val_inv_eq_inv_val]
       have := hne 0
       have := hne 1
       have := hne 2
       have := hne 3
       field_simp
       try first | linear_combination h' | linear_combination -h')

end Dictionary

section Realizers

@[expose] def Realizes10 (p : ℕ) (γ : W10) (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) : Prop :=
  ∀ d : torusVec p 4 (Qext K), g * emb10 d * g⁻¹ = emb10 (act10 γ d)

theorem realizes10_one : Realizes10 p (1 : W10) (1 : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) := by
  intro d
  simp

theorem realizes10_mul {γ₁ γ₂ : W10} {g₁ g₂ : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)}
    (h₁ : Realizes10 p γ₁ g₁) (h₂ : Realizes10 p γ₂ g₂) : Realizes10 p (γ₁ * γ₂) (g₁ * g₂) := by
  intro d
  have : g₁ * g₂ * emb10 d * (g₁ * g₂)⁻¹ = g₁ * (g₂ * emb10 d * g₂⁻¹) * g₁⁻¹ := by group
  rw [this, h₂ d, h₁, map_mul, MulAut.mul_apply]

theorem realizes10_of_isSgn (hpq : p ∣ Nat.card K + 1) (π : Equiv.Perm (Fin 3))
    (s : Fin 3 → Bool) (γ : W10)
    (hγ : ∀ d : torusVec p 4 (Qext K), IsSgn π s (sqCoords d) (sqCoords (act10 γ d))) :
    Realizes10 p γ (sgnPerm (K := K) π s) := fun d =>
  sgnPerm_conj hpq π s _ _ (sqCoords_pow d) (hγ d)

omit [Finite K] in
theorem isSgn_inv (d : torusVec p 4 (Qext K)) :
    IsSgn 1 (fun _ => true) (sqCoords d) (sqCoords (act10 (Multiplicative.ofAdd (1 : ZMod 2),
      (1 : Equiv.Perm (Fin 4))) d)) := by
  intro i
  rw [act10_inv, symAct_one, map_inv]
  simp
  rfl

theorem exists_realizer10_swap (hpq : p ∣ Nat.card K + 1) {a b : Fin 4} (hab : a ≠ b) :
    ∃ g ∈ M10 K, Realizes10 p ((1 : Multiplicative (ZMod 2)), Equiv.swap a b) g := by
  have key : ∀ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (a b : Fin 4),
      (∀ d : torusVec p 4 (Qext K), IsSgn π s (sqCoords d)
        (sqCoords (symAct p (Qext K) (Equiv.swap a b) d))) →
      ∃ g ∈ M10 K, Realizes10 p ((1 : Multiplicative (ZMod 2)), Equiv.swap a b) g := by
    intro π s a b h
    refine ⟨sgnPerm π s, sgnPerm_mem_M10 π s, realizes10_of_isSgn hpq π s _ fun d => ?_⟩
    rw [act10_one]
    exact h d
  have h01 := key _ _ 0 1 isSgn_swap01
  have h02 := key _ _ 0 2 isSgn_swap02
  have h03 := key _ _ 0 3 isSgn_swap03
  have h12 := key _ _ 1 2 isSgn_swap12
  have h13 := key _ _ 1 3 isSgn_swap13
  have h23 := key _ _ 2 3 isSgn_swap23
  fin_cases a <;> fin_cases b <;>
    first
    | exact absurd rfl hab
    | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23

theorem exists_realizer10 (hpq : p ∣ Nat.card K + 1) (γ : W10) :
    ∃ g ∈ M10 K, Realizes10 p γ g := by
  let R : Submonoid W10 :=
    { carrier := {γ | ∃ g ∈ M10 K, Realizes10 p γ g}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨g₁, hg₁, h₁⟩ := ha
        obtain ⟨g₂, hg₂, h₂⟩ := hb
        exact ⟨g₁ * g₂, (M10 K).mul_mem hg₁ hg₂, realizes10_mul h₁ h₂⟩
      one_mem' := ⟨1, (M10 K).one_mem, realizes10_one⟩ }
  have hinv : ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) ∈ R :=
    ⟨sgnPerm 1 (fun _ => true), sgnPerm_mem_M10 _ _,
      realizes10_of_isSgn hpq 1 (fun _ => true) _ isSgn_inv⟩
  obtain ⟨e, σ⟩ := γ
  have hσ : σ ∈ Submonoid.closure {σ : Equiv.Perm (Fin 4) | σ.IsSwap} := by
    rw [Equiv.Perm.mclosure_isSwap]
    trivial
  have h1 : ((1 : Multiplicative (ZMod 2)), σ) ∈ R := by
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      exact exists_realizer10_swap hpq hab
    | one => exact R.one_mem
    | mul x y _ _ hx hy =>
      have := R.mul_mem hx hy
      simpa using this
  rcases cases_zmod_two e with rfl | rfl
  · exact h1
  · have h2 : (Multiplicative.ofAdd (1 : ZMod 2), σ) ∈ R := by
      have := R.mul_mem hinv h1
      simpa using this
    exact h2

end Realizers

section Counting

@[expose] def SgnAut (p : ℕ) (ψ : MulAut (torusVec p 4 (Qext K))) : Prop :=
  ∃ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), ∀ (d : torusVec p 4 (Qext K)) (i : Fin 3),
    sqCoords (ψ d) (π i) = if s i then (sqCoords d i)⁻¹ else sqCoords d i

omit [Finite K] in
theorem sgnAut_unique (hp : p.Prime) (hp2 : p ≠ 2) {ψ ψ' : MulAut (torusVec p 4 (Qext K))}
    {π : Equiv.Perm (Fin 3)} {s : Fin 3 → Bool}
    (h : ∀ (d : torusVec p 4 (Qext K)) (i : Fin 3),
      sqCoords (ψ d) (π i) = if s i then (sqCoords d i)⁻¹ else sqCoords d i)
    (h' : ∀ (d : torusVec p 4 (Qext K)) (i : Fin 3),
      sqCoords (ψ' d) (π i) = if s i then (sqCoords d i)⁻¹ else sqCoords d i) : ψ = ψ' := by
  refine MulEquiv.ext fun d => sqCoords_injective hp hp2 (funext fun j => ?_)
  have h1 := h d (π.symm j)
  have h2 := h' d (π.symm j)
  rw [Equiv.apply_symm_apply] at h1 h2
  rw [h1, h2]

theorem sgnAut_of_induces (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (ψ : MulAut (torusVec p 4 (Qext K))) (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))
    (hψ : ∀ d, g * emb10 d * g⁻¹ = emb10 (ψ d)) : SgnAut p ψ := by
  have hp2 : p ≠ 2 := by omega
  have hg' : ∀ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) →
      ∃ y : Fin 3 → (Qext K)ˣ, g * torusEquiv x * g⁻¹ = torusEquiv y := by
    intro x hx
    obtain ⟨d, rfl⟩ := sqCoords_surjective hp hp2 x hx
    exact ⟨sqCoords (ψ d), hψ d⟩
  obtain ⟨π, ε, hπ⟩ := normalizer_torus_units hp hp2 hpq g hg'
  exact ⟨π, ε, fun d i => hπ (sqCoords d) (sqCoords (ψ d)) (sqCoords_pow d) (hψ d) i⟩

theorem card_W10 : Nat.card W10 = 48 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_sgn_index : Nat.card (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 48 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

omit [Finite K] in
theorem ncard_sgnAut_le (hp : p.Prime) (hp2 : p ≠ 2) :
    {ψ : MulAut (torusVec p 4 (Qext K)) | SgnAut p ψ}.ncard ≤ 48 := by
  classical
  let S : Set (MulAut (torusVec p 4 (Qext K))) := {ψ | SgnAut p ψ}
  have hS : ∀ ψ : S, ∃ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
      ∀ (d : torusVec p 4 (Qext K)) (i : Fin 3),
        sqCoords (ψ.1 d) (π i) = if s i then (sqCoords d i)⁻¹ else sqCoords d i := fun ψ => ψ.2
  choose π s hπs using hS
  let f : S → Equiv.Perm (Fin 3) × (Fin 3 → Bool) := fun ψ => (π ψ, s ψ)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : π a = π b := congrArg Prod.fst hab
    have h2 : s a = s b := congrArg Prod.snd hab
    have ha := hπs a
    have hb := hπs b
    rw [← h1, ← h2] at hb
    exact Subtype.ext (sgnAut_unique hp hp2 ha hb)
  have := Nat.card_le_card_of_injective f hf
  rw [card_sgn_index] at this
  rw [← Nat.card_coe_set_eq]
  exact this

theorem exists_act10_of_induces (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p)
    (ψ : MulAut (torusVec p 4 (Qext K))) (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))
    (hψ : ∀ d, g * emb10 d * g⁻¹ = emb10 (ψ d)) : ∃ γ : W10, act10 γ = ψ := by
  have hp2 : p ≠ 2 := by omega
  let S : Set (MulAut (torusVec p 4 (Qext K))) := {ψ | SgnAut p ψ}
  have hsub : Set.range (act10 : W10 →* MulAut (torusVec p 4 (Qext K))) ⊆ S := by
    rintro _ ⟨γ, rfl⟩
    obtain ⟨g', -, hr⟩ := exists_realizer10 hpq γ
    exact sgnAut_of_induces hp hp5 hpq _ g' hr
  have hfin : S.Finite := by
    have : Finite (MulAut (torusVec p 4 (Qext K))) := by
      have : Finite (torusVec p 4 (Qext K)) := by
        have : Finite (Qext K) := inferInstance
        exact Finite.of_injective (fun d : torusVec p 4 (Qext K) => (d : Fin 4 → (Qext K)ˣ))
          Subtype.val_injective
      infer_instance
    exact Set.toFinite S
  have hinj := act10_injective (K := Qext K) hp hp2 hζ
  have hr : (Set.range (act10 : W10 →* MulAut (torusVec p 4 (Qext K)))).ncard = 48 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, card_W10]
  have hcard : S.ncard ≤ (Set.range (act10 : W10 →* MulAut (torusVec p 4 (Qext K)))).ncard := by
    rw [hr]
    exact ncard_sgnAut_le hp hp2
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard hfin
  have hmem : ψ ∈ S := sgnAut_of_induces hp hp5 hpq ψ g hψ
  rw [← heq] at hmem
  exact hmem

end Counting

section Normalizer

theorem mem_normalizer_subgroupOf_iff10 {Γ : Type*} [Group Γ] {M T : Subgroup Γ} (hTM : T ≤ M)
    (m : ↥M) : m ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔
      (∀ x ∈ T, (m : Γ) * x * (m : Γ)⁻¹ ∈ T) ∧ (∀ x ∈ T, (m : Γ)⁻¹ * x * (m : Γ) ∈ T) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact (h ⟨x, hTM hx⟩).mp hx
    · have h1 : (⟨(m : Γ)⁻¹ * x * (m : Γ), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ : ↥M) ∈ T.subgroupOf M ↔ _ := h _
      have h2 : m * ⟨(m : Γ)⁻¹ * x * (m : Γ), M.mul_mem (M.mul_mem
          (M.inv_mem m.2) (hTM hx)) m.2⟩ * m⁻¹ = ⟨x, hTM hx⟩ := by
        apply Subtype.ext
        show (m : Γ) * ((m : Γ)⁻¹ * x * (m : Γ)) * (m : Γ)⁻¹ = x
        group
      rw [h2] at h1
      exact h1.mpr hx
  · rintro ⟨h1, h2⟩ y
    constructor
    · intro hy
      exact h1 _ hy
    · intro hy
      have h4 := h2 ((m * y * m⁻¹ : ↥M) : Γ) hy
      have h3 : (m : Γ)⁻¹ * ((m * y * m⁻¹ : ↥M) : Γ) * (m : Γ) = (y : Γ) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3] at h4
      exact h4

theorem realizes10_inv {γ : W10} {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)}
    (h : Realizes10 p γ g) (v : torusVec p 4 (Qext K)) :
    g⁻¹ * emb10 v * g = emb10 (act10 γ⁻¹ v) := by
  have h1 := h (act10 γ⁻¹ v)
  rw [← MulAut.mul_apply, ← map_mul] at h1
  have h0 : γ * γ⁻¹ = 1 := mul_inv_cancel γ
  rw [h0, map_one, MulAut.one_apply] at h1
  have h2 : g⁻¹ * (g * emb10 (act10 γ⁻¹ v) * g⁻¹) * g = emb10 (act10 γ⁻¹ v) := by group
  rw [h1] at h2
  exact h2

end Normalizer

section Ctx

theorem exists_w10ctx (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) :
    Nonempty (WCtx (act10 : W10 →* MulAut (torusVec p 4 (Qext K))) (⊤ : Subgroup ↥(M10 K))
      ((emb10 : torusVec p 4 (Qext K) →* (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf
        (M10 K))) := by
  classical
  have hp2 : p ≠ 2 := by omega
  set T : Subgroup (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) := emb10.range with hTdef
  have hTM : T ≤ M10 K := by
    rintro _ ⟨v, rfl⟩
    exact emb10_mem_M10 hpq v
  let torh : torusVec p 4 (Qext K) →* ↥(T.subgroupOf (M10 K)) :=
    { toFun := fun v => ⟨⟨emb10 v, emb10_mem_M10 hpq v⟩, ⟨v, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact map_one _
      map_mul' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        exact map_mul _ _ _ }
  have hinj : Function.Injective torh := by
    intro v w h
    exact emb10_injective hp hp2 (congrArg (fun x : ↥(T.subgroupOf (M10 K)) =>
      ((x : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))) h)
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨v, hv⟩ := hxT
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  let tor : torusVec p 4 (Qext K) ≃* ↥(T.subgroupOf (M10 K)) :=
    MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · intro γ
    obtain ⟨g, hgM, hr⟩ := exists_realizer10 hpq γ
    set gM : ↥(M10 K) := ⟨g, hgM⟩ with hgMdef
    have hg : gM ∈ Subgroup.normalizer
        ((T.subgroupOf (M10 K) : Subgroup ↥(M10 K)) : Set ↥(M10 K)) := by
      rw [mem_normalizer_subgroupOf_iff10 hTM]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨v, rfl⟩ := hx
        show g * emb10 v * g⁻¹ ∈ T
        rw [hr v]
        exact ⟨_, rfl⟩
      · obtain ⟨v, rfl⟩ := hx
        show g⁻¹ * emb10 v * g ∈ T
        rw [realizes10_inv hr v]
        exact ⟨_, rfl⟩
    refine ⟨gM, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    exact hr v
  · intro m hm _
    set φ := (T.subgroupOf (M10 K)).normalizerMonoidHom ⟨m, hm⟩ with hφ
    set ψ : MulAut (torusVec p 4 (Qext K)) := (MulAut.congr tor).symm φ with hψdef
    have hcongr : MulAut.congr tor ψ = φ := by
      rw [hψdef]
      exact MulEquiv.apply_symm_apply _ _
    have hψ : ∀ d, (m : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) * emb10 d *
        (m : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))⁻¹ = emb10 (ψ d) := by
      intro d
      have h1 := SymCtx.congr_apply_tor tor ψ d
      rw [hcongr] at h1
      exact congrArg (fun x : ↥(T.subgroupOf (M10 K)) =>
        ((x : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))) h1
    obtain ⟨γ, hγ⟩ := exists_act10_of_induces hp hp5 hpq hζ ψ _ hψ
    exact ⟨γ, hcongr.symm.trans (congrArg (MulAut.congr tor) hγ.symm)⟩

end Ctx

end CFSG.RankThree.PartOne.KFQ
