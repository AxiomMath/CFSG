module

public import Certificates.Certificate17006
public import Certificates.Certificate18950


public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

theorem exists_orbit_map {J X Y : Type*} [Group J] (σ : J →* Equiv.Perm X)
    (τ : J →* Equiv.Perm Y) (x₀ : X) (y₀ : Y) (hst : ∀ g, σ g x₀ = x₀ → τ g y₀ = y₀) :
    ∃ Φ : X → Y, ∀ g, Φ (σ g x₀) = τ g y₀ := by
  classical
  refine ⟨fun x => if h : ∃ g, σ g x₀ = x then τ h.choose y₀ else y₀, fun g => ?_⟩
  have h : ∃ g', σ g' x₀ = σ g x₀ := ⟨g, rfl⟩
  simp only [h, ↓reduceDIte]
  have hg := h.choose_spec
  have h1 : σ (g⁻¹ * h.choose) x₀ = x₀ := by
    rw [map_mul, Equiv.Perm.mul_apply, hg, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Equiv.Perm.one_apply]
  have h2 := hst _ h1
  rw [map_mul, Equiv.Perm.mul_apply] at h2
  calc τ h.choose y₀ = τ g (τ g⁻¹ (τ h.choose y₀)) := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    _ = τ g y₀ := by rw [h2]

@[expose] noncomputable def wordElem (w : List (Fin 5)) : U33G :=
  (w.map fun i : Fin 5 => u33GenPG (i : ℕ)).prod

theorem psiW_wordElem (w : List (Fin 5)) (c : ℕ) :
    psiW (wordElem w) (Multiplicative.ofAdd (vecOf c)) =
      Multiplicative.ofAdd (vecOf (wordApply w c)) := by
  induction w with
  | nil => simp [wordElem, wordApply]
  | cons i w ih =>
    rw [wordElem, List.map_cons, List.prod_cons, map_mul, MulAut.mul_apply]
    change psiW (u33GenPG i) (psiW (wordElem w) (Multiplicative.ofAdd (vecOf c))) = _
    rw [ih, psiW_gen_vecOf]
    rfl

theorem kWords_fix : ∀ b ∈ [1, 18], ∀ k ∈ kWords b, wordApply k 15 = 15 ∧ wordApply k b = b :=
  Certificates.certificate17006.1

theorem kWords_fixed_only : ∀ b ∈ [1, 18], ∀ c < 64, (kWords b).all (fun k => wordApply k c == c) →
    c = 0 ∨ c = 15 ∨ c = b ∨ c = 15 ^^^ b :=
  Certificates.certificate17006.2.1

theorem deriveSteps_ok : deriveCheck [1, 2, 4, 8, 16, 32] deriveSteps = true :=
  Certificates.certificate17006.2.2.1

theorem deriveSteps_cover : ∀ c < 64, c = 0 ∨ c ∈ [1, 2, 4, 8, 16, 32] ∨
    c ∈ deriveSteps.map Prod.fst :=
  Certificates.certificate17006.2.2.2

theorem wordApply_lt (w : List (Fin 5)) {c : ℕ} (hc : c < 64) : wordApply w c < 64 := by
  induction w with
  | nil => exact hc
  | cons i w _ => exact vapp_u6c_lt i _

theorem derive_agree {M : Type*} [AddCommGroup M] (h2M : ∀ m : M, m + m = 0) (f L : ℕ → M)
    (hL : ∀ x y, L (x ^^^ y) = L x + L y)
    (hf : ∀ (w : List (Fin 5)) (b : ℕ), b ∈ [1, 18] →
      f (wordApply w 15 ^^^ wordApply w b) = f (wordApply w 15) + f (wordApply w b)) :
    ∀ (steps : List (ℕ × List (Fin 5) × ℕ)) (D : List ℕ), deriveCheck D steps = true →
      (∀ c ∈ D, c < 64 ∧ f c = L c) → ∀ c ∈ D ++ steps.map Prod.fst, c < 64 ∧ f c = L c := by
  have hneg : ∀ m : M, -m = m := fun m => (neg_eq_of_add_eq_zero_right (h2M m))
  intro steps
  induction steps with
  | nil =>
    intro D _ hD c hc
    simp only [List.map_nil, List.append_nil] at hc
    exact hD c hc
  | cons st rest ih =>
    obtain ⟨x, w, b⟩ := st
    intro D hchk hD
    simp only [deriveCheck, Bool.and_eq_true] at hchk
    obtain ⟨hok, hrest⟩ := hchk
    simp only [stepOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.contains_iff_mem] at hok
    obtain ⟨hb, hcase⟩ := hok
    have hb' : b ∈ [1, 18] := by
      rcases hb with rfl | rfl <;> simp
    have hb64 : b < 64 := by rcases hb with rfl | rfl <;> norm_num
    set p := wordApply w 15 with hp
    set q := wordApply w b with hq
    have hp64 : p < 64 := wordApply_lt w (by norm_num)
    have hq64 : q < 64 := wordApply_lt w hb64
    have hpq64 : p ^^^ q < 64 := Nat.xor_lt_two_pow (n := 6) hp64 hq64
    have hrel := hf w b hb'
    have hx : x < 64 ∧ f x = L x := by
      rcases hcase with (⟨⟨rfl, hqD⟩, hpqD⟩ | ⟨⟨rfl, hpD⟩, hpqD⟩) | ⟨⟨rfl, hpD⟩, hqD⟩
      · refine ⟨hp64, ?_⟩
        have e1 := (hD _ hqD).2
        have e2 := (hD _ hpqD).2
        have hpq : p = (p ^^^ q) ^^^ q := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        calc f p = f (p ^^^ q) + f q := by rw [hrel, add_assoc, h2M, add_zero]
          _ = L (p ^^^ q) + L q := by rw [e1, e2]
          _ = L p := by rw [← hL, ← hpq]
      · refine ⟨hq64, ?_⟩
        have e1 := (hD _ hpD).2
        have e2 := (hD _ hpqD).2
        have hpq : q = p ^^^ (p ^^^ q) := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        calc f q = f p + f (p ^^^ q) := by rw [hrel, ← add_assoc, h2M, zero_add]
          _ = L p + L (p ^^^ q) := by rw [e1, e2]
          _ = L q := by rw [← hL, ← hpq]
      · refine ⟨hpq64, ?_⟩
        rw [hrel, (hD _ hpD).2, (hD _ hqD).2, hL]
    have hD' : ∀ c ∈ x :: D, c < 64 ∧ f c = L c := by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hx
      · exact hD c hc
    have h := ih (x :: D) hrest hD'
    intro c hc
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact hD c hc
    · exact hx
    · exact h c (List.mem_append_right _ hc)

section Unique

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem stab_ne_B
    (hV : Nat.card V = 64) (ψ : U33G →* MulAut V) {v₀ : V} (hv₀1 : v₀ ≠ 1)
    (hB : ∀ g, ψ g v₀ = v₀ ↔ g ∈ u33Data.B) (horb : ∀ w : V, w ≠ 1 → ∃ g, ψ g v₀ = w) : False := by
  classical
  let permV : U33G →* Equiv.Perm V := (MulAut.toPerm V).comp ψ
  have hne1 : ∀ (g : U33G) (v : V), v ≠ 1 → ψ g v ≠ 1 := fun g v hv h =>
    hv ((ψ g).injective (h.trans (map_one (ψ g)).symm))
  obtain ⟨Φ, hΦ⟩ := exists_orbit_map pi63 permV 0 v₀
    (fun g hg => (hB g).2 ((pi63_stab_zero g).1 hg))
  have hΦ' : ∀ g, Φ (pi63 g 0) = ψ g v₀ := hΦ
  have hΦinj : Function.Injective Φ := by
    intro k k' h
    obtain ⟨g, rfl⟩ := pi63_transitive k
    obtain ⟨g', rfl⟩ := pi63_transitive k'
    rw [hΦ', hΦ'] at h
    have h1 : ψ (g⁻¹ * g') v₀ = v₀ := by
      rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    have h2 := (pi63_stab_zero _).2 ((hB _).1 h1)
    rw [map_mul, Equiv.Perm.mul_apply] at h2
    calc pi63 g 0 = pi63 g (pi63 g⁻¹ (pi63 g' 0)) := by rw [h2]
      _ = pi63 g' 0 := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hΦeq : ∀ h k, Φ (pi63 h k) = ψ h (Φ k) := by
    intro h k
    obtain ⟨g, rfl⟩ := pi63_transitive k
    rw [← Equiv.Perm.mul_apply, ← map_mul, hΦ', hΦ', map_mul, MulAut.mul_apply]
  set y := u33GenPG 4 with hy
  have hset : {v : V | ψ y v = v} = insert 1 (Φ '' {k | pi63 y k = k}) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image]
    constructor
    · intro hv
      by_cases h1 : v = 1
      · exact Or.inl h1
      · right
        obtain ⟨g, rfl⟩ := horb v h1
        refine ⟨pi63 g 0, hΦinj ?_, hΦ' g⟩
        rw [hΦeq, hΦ', hv]
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact map_one _
      · rw [← hΦeq, hk]
  have h1notin : (1 : V) ∉ Φ '' {k | pi63 y k = k} := by
    rintro ⟨k, -, hk⟩
    obtain ⟨g, rfl⟩ := pi63_transitive k
    rw [hΦ'] at hk
    exact hne1 g v₀ hv₀1 hk
  have hcard : {v : V | ψ y v = v}.ncard = 10 := by
    rw [hset, Set.ncard_insert_of_notMem h1notin, Set.ncard_image_of_injective _ hΦinj,
      ← Nat.card_coe_set_eq]
    have h9 := card_fix_pi63_y
    rw [← hy] at h9
    exact congrArg (· + 1) h9
  let C : Subgroup V :=
    { carrier := {v | ψ y v = v}
      one_mem' := map_one _
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hC : Nat.card C = 10 := by
    rw [← hcard, ← Nat.card_coe_set_eq]
    rfl
  have hdvd := Subgroup.card_subgroup_dvd_card C
  rw [hV, hC] at hdvd
  norm_num at hdvd

theorem exists_fixed_T
    (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 64) (ψ : U33G →* MulAut V)
    (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1) :
    ∃ v₀ : V, v₀ ≠ 1 ∧ ∀ t ∈ u33Data.T, ψ t v₀ = v₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T₀ : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2
  have h2 := u33_sylow_fixed_card_two hV2 hV ψ hfix T₀
  obtain ⟨⟨v, hv⟩, hv1⟩ : ∃ x : {v : V // ∀ s ∈ T₀, ψ s v = v}, x ≠ ⟨1, fun s _ => map_one _⟩ := by
    by_contra h
    push Not at h
    have : Nat.card {v : V // ∀ s ∈ T₀, ψ s v = v} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  exact ⟨v, fun h => hv1 (Subtype.ext h), fun t ht => hv t ht⟩

theorem exists_equiv_u33_module
    (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 64)
    (ψ : U33G →* MulAut V) (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1) :
    ∃ F : Multiplicative W6 ≃* V, ∀ (g : U33G) (w : Multiplicative W6),
      F (psiW g w) = ψ g (F w) := by
  classical
  have hne1 : ∀ (g : U33G) (v : V), v ≠ 1 → ψ g v ≠ 1 := fun g v hv h =>
    hv ((ψ g).injective (h.trans (map_one (ψ g)).symm))
  have hne1W : ∀ (g : U33G) (w : Multiplicative W6), w ≠ 1 → psiW g w ≠ 1 := fun g w hw h =>
    hw ((psiW g).injective (h.trans (map_one (psiW g)).symm))
  obtain ⟨v₀, hv₀1, hv₀T⟩ := exists_fixed_T hV2 hV ψ hfix
  obtain ⟨hst, horb⟩ := u33_stab_orbit hV ψ hfix hv₀1 hv₀T
  have hA : ∀ g, ψ g v₀ = v₀ ↔ g ∈ u33Data.A := by
    rcases hst with h | h
    · exact h
    · exact (stab_ne_B hV ψ hv₀1 h horb).elim
  let permV : U33G →* Equiv.Perm V := (MulAut.toPerm V).comp ψ
  obtain ⟨Φ, hΦ⟩ := exists_orbit_map permW permV w0 v₀
    (fun g hg => (hA g).2 ((psiW_stab_w0.1 g).1 hg))
  have hΦ' : ∀ g, Φ (psiW g w0) = ψ g v₀ := hΦ
  let F₀ : Multiplicative W6 → V := fun w => if w = 1 then 1 else Φ w
  have hF₀1 : F₀ 1 = 1 := by simp [F₀]
  have hF₀ : ∀ g, F₀ (psiW g w0) = ψ g v₀ := by
    intro g
    simp only [F₀, hne1W g w0 w0_ne_one, ↓reduceIte]
    exact hΦ' g
  have hF₀eq : ∀ g w, F₀ (psiW g w) = ψ g (F₀ w) := by
    intro g w
    by_cases hw : w = 1
    · rw [hw, map_one, hF₀1, map_one]
    · obtain ⟨h, rfl⟩ := psiW_transitive w hw
      rw [← MulAut.mul_apply, ← map_mul, hF₀, hF₀, map_mul, MulAut.mul_apply]
  have hF₀ne : ∀ w, w ≠ 1 → F₀ w ≠ 1 := by
    intro w hw
    obtain ⟨g, rfl⟩ := psiW_transitive w hw
    rw [hF₀]
    exact hne1 g v₀ hv₀1
  have hF₀inj : Function.Injective F₀ := by
    intro w w' h
    by_cases hw : w = 1
    · by_contra hne
      have hw' : w' ≠ 1 := fun h' => hne (hw.trans h'.symm)
      exact hF₀ne w' hw' (by rw [← h, hw, hF₀1])
    · by_cases hw' : w' = 1
      · exact absurd (by rw [h, hw', hF₀1]) (hF₀ne w hw)
      · obtain ⟨g, rfl⟩ := psiW_transitive w hw
        obtain ⟨g', rfl⟩ := psiW_transitive w' hw'
        rw [hF₀, hF₀] at h
        have h1 : ψ (g⁻¹ * g') v₀ = v₀ := by
          rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, MulAut.one_apply]
        have h2 := (psiW_stab_w0.1 _).2 ((hA _).1 h1)
        rw [map_mul, MulAut.mul_apply] at h2
        calc psiW g w0 = psiW g (psiW g⁻¹ (psiW g' w0)) := by rw [h2]
          _ = psiW g' w0 := by
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hF₀surj : Function.Surjective F₀ := by
    intro v
    by_cases hv : v = 1
    · exact ⟨1, by rw [hF₀1, hv]⟩
    · obtain ⟨g, rfl⟩ := horb v hv
      exact ⟨psiW g w0, hF₀ g⟩
  have hbase : ∀ b ∈ [1, 18], F₀ (Multiplicative.ofAdd (vecOf (15 ^^^ b))) =
      F₀ w0 * F₀ (Multiplicative.ofAdd (vecOf b)) := by
    intro b hb
    have hb64 : b < 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> norm_num
    set eb := Multiplicative.ofAdd (vecOf b) with heb
    have hfixK : ∀ k ∈ kWords b, psiW (wordElem k) w0 = w0 ∧ psiW (wordElem k) eb = eb := by
      intro k hk
      obtain ⟨h1, h2⟩ := kWords_fix b hb k hk
      refine ⟨?_, ?_⟩
      · rw [w0, psiW_wordElem, h1]
      · rw [heb, psiW_wordElem, h2]
    obtain ⟨u, hu⟩ := hF₀surj (F₀ w0 * F₀ eb)
    have hufix : ∀ k ∈ kWords b, psiW (wordElem k) u = u := by
      intro k hk
      apply hF₀inj
      rw [hF₀eq, hu, map_mul, ← hF₀eq, ← hF₀eq, (hfixK k hk).1, (hfixK k hk).2]
    obtain ⟨c, hc, hcu⟩ := exists_vecOf (Multiplicative.toAdd u)
    have hu' : u = Multiplicative.ofAdd (vecOf c) := by rw [hcu]; rfl
    have hcfix : (kWords b).all (fun k => wordApply k c == c) = true := by
      rw [List.all_eq_true]
      intro k hk
      have h1 := hufix k hk
      rw [hu', psiW_wordElem] at h1
      have h2 : vecOf (wordApply k c) = vecOf c := congrArg Multiplicative.toAdd h1
      exact beq_iff_eq.2 (vecOf_injective (wordApply_lt k hc) hc h2)
    have heb1 : eb ≠ 1 := by
      intro h
      have h2 : vecOf b = vecOf 0 := by rw [vecOf_zero]; exact congrArg Multiplicative.toAdd h
      have := vecOf_injective hb64 (by norm_num) h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> norm_num at this
    have hw0eb : w0 ≠ eb := by
      intro h
      have h2 : vecOf 15 = vecOf b := congrArg Multiplicative.toAdd h
      have := vecOf_injective (by norm_num) hb64 h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> norm_num at this
    rcases kWords_fixed_only b hb c hc hcfix with h0 | h15 | hb' | hx
    ·
      exfalso
      rw [hu', h0, vecOf_zero] at hu
      change F₀ 1 = _ at hu
      rw [hF₀1] at hu
      have h2 : F₀ eb = F₀ w0 := by
        have h3 : F₀ w0 * (F₀ w0 * F₀ eb) = F₀ w0 := by rw [← hu, mul_one]
        rwa [← mul_assoc, hV2, one_mul] at h3
      exact hw0eb (hF₀inj h2.symm)
    · exfalso
      rw [hu', h15] at hu
      change F₀ w0 = F₀ w0 * F₀ eb at hu
      have : F₀ eb = 1 := by
        have h3 := congrArg (fun t => (F₀ w0)⁻¹ * t) hu
        simpa using h3.symm
      exact hF₀ne eb heb1 this
    · exfalso
      rw [hu', hb'] at hu
      change F₀ eb = F₀ w0 * F₀ eb at hu
      have : F₀ w0 = 1 := by
        have h3 := congrArg (fun t => t * (F₀ eb)⁻¹) hu
        simpa using h3.symm
      exact hF₀ne w0 w0_ne_one this
    · rw [← hx, ← hu', hu]
  have hrel : ∀ (w : List (Fin 5)) (b : ℕ), b ∈ [1, 18] →
      F₀ (Multiplicative.ofAdd (vecOf (wordApply w 15 ^^^ wordApply w b))) =
        F₀ (Multiplicative.ofAdd (vecOf (wordApply w 15))) *
          F₀ (Multiplicative.ofAdd (vecOf (wordApply w b))) := by
    intro w b hb
    have h1 := congrArg (ψ (wordElem w)) (hbase b hb)
    rw [map_mul, ← hF₀eq, ← hF₀eq, ← hF₀eq] at h1
    have e1 : psiW (wordElem w) (Multiplicative.ofAdd (vecOf (15 ^^^ b))) =
        Multiplicative.ofAdd (vecOf (wordApply w 15 ^^^ wordApply w b)) := by
      rw [vecOf_xor, ofAdd_add, map_mul, psiW_wordElem, psiW_wordElem, ← ofAdd_add,
        ← vecOf_xor]
    have e2 : psiW (wordElem w) w0 = Multiplicative.ofAdd (vecOf (wordApply w 15)) :=
      psiW_wordElem w 15
    rw [e1, e2, psiW_wordElem w b] at h1
    exact h1
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hV2 (Additive.toMul x))
  let basisV : Fin 6 → Additive V := fun i =>
    Additive.ofMul (F₀ (Multiplicative.ofAdd (Pi.single i 1)))
  let Lext : W6 →ₗ[ZMod 2] Additive V := Fintype.linearCombination (ZMod 2) basisV
  let fC : ℕ → Additive V := fun c => Additive.ofMul (F₀ (Multiplicative.ofAdd (vecOf c)))
  let LC : ℕ → Additive V := fun c => Lext (vecOf c)
  have h2M : ∀ m : Additive V, m + m = 0 := fun m =>
    congrArg Additive.ofMul (hV2 (Additive.toMul m))
  have hLC : ∀ x y, LC (x ^^^ y) = LC x + LC y := fun x y => by
    simp only [LC, vecOf_xor, map_add]
  have hfC : ∀ (w : List (Fin 5)) (b : ℕ), b ∈ [1, 18] →
      fC (wordApply w 15 ^^^ wordApply w b) = fC (wordApply w 15) + fC (wordApply w b) :=
    fun w b hb => congrArg Additive.ofMul (hrel w b hb)
  have hbasis : ∀ c ∈ [1, 2, 4, 8, 16, 32], c < 64 ∧ fC c = LC c := by
    intro c hc
    have hsingle : ∀ i : Fin 6, vecOf (2 ^ (i : ℕ)) = Pi.single i 1 :=
      Certificates.certificate18950
    have hLsingle : ∀ i : Fin 6, LC (2 ^ (i : ℕ)) = fC (2 ^ (i : ℕ)) := by
      intro i
      simp only [LC, fC, hsingle i, Lext, Fintype.linearCombination_apply_single, one_smul,
        basisV]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, (hLsingle 0).symm⟩
    · exact ⟨by norm_num, (hLsingle 1).symm⟩
    · exact ⟨by norm_num, (hLsingle 2).symm⟩
    · exact ⟨by norm_num, (hLsingle 3).symm⟩
    · exact ⟨by norm_num, (hLsingle 4).symm⟩
    · exact ⟨by norm_num, (hLsingle 5).symm⟩
  have hall := derive_agree h2M fC LC hLC hfC deriveSteps [1, 2, 4, 8, 16, 32] deriveSteps_ok
    hbasis
  have hagree : ∀ c < 64, fC c = LC c := by
    intro c hc
    rcases deriveSteps_cover c hc with rfl | hc' | hc'
    · simp only [fC, LC, vecOf_zero, map_zero]
      change Additive.ofMul (F₀ 1) = 0
      rw [hF₀1]
      rfl
    · exact (hall c (List.mem_append_left _ hc')).2
    · exact (hall c (List.mem_append_right _ hc')).2
  have hmul : ∀ u w, F₀ (u * w) = F₀ u * F₀ w := by
    intro u w
    obtain ⟨c, hc, hcu⟩ := exists_vecOf (Multiplicative.toAdd u)
    obtain ⟨d, hd, hdw⟩ := exists_vecOf (Multiplicative.toAdd w)
    have hu : u = Multiplicative.ofAdd (vecOf c) := by rw [hcu]; rfl
    have hw : w = Multiplicative.ofAdd (vecOf d) := by rw [hdw]; rfl
    have huw : u * w = Multiplicative.ofAdd (vecOf (c ^^^ d)) := by
      rw [hu, hw, vecOf_xor, ofAdd_add]
    have hcd : c ^^^ d < 64 := Nat.xor_lt_two_pow (n := 6) hc hd
    have e1 := hagree _ hcd
    have e2 := hagree _ hc
    have e3 := hagree _ hd
    rw [hLC] at e1
    have : Additive.ofMul (F₀ (u * w)) = Additive.ofMul (F₀ u * F₀ w) := by
      rw [ofMul_mul, huw, hu, hw]
      change fC (c ^^^ d) = fC c + fC d
      rw [e1, e2, e3]
    exact Additive.ofMul.injective this
  exact ⟨MulEquiv.ofBijective (MulHom.mk F₀ hmul) ⟨hF₀inj, hF₀surj⟩, fun g w => hF₀eq g w⟩

end Unique

end CFSG.Quasithin.H13.U3
