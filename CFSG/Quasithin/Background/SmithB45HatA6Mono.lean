module

public import CFSG.Quasithin.Background.SmithB45HatA6MonoData
public import CFSG.Quasithin.Background.SmithB42Alt6Conj
public import CFSG.Quasithin.Background.SmithB45HatA6Nine

public section

namespace CFSG.Quasithin.B45HatA6

open Equiv CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3E

@[expose] def Yk (k : Bool) : Subgroup (Perm (Fin 6)) := Subgroup.closure {g | g ∈ gensY k}

theorem exists_of_mem_EY (k : Bool) {c : List ℕ} (hc : c ∈ EY k) :
    ∃ x ∈ Yk k, codeN 6 x = c :=
  (mem_closure_iff_of_tblN (gensY_code k) (tblY_check k)).2 c hc

theorem codeN_mem_genC {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    codeN 6 σ ∈ genC := by
  classical
  have hnd : (eGenW.map evalG).Nodup := by
    have : ((eGenW.map evalG).map c6).Nodup := by
      rw [List.map_map, show c6 ∘ evalG = evalC from funext c6_evalG]
      exact genC_nodup
    exact List.Nodup.of_map _ this
  have hlen : (eGenW.map evalG).length = 360 := by
    rw [List.length_map]
    have := genC_length
    unfold genC at this
    rwa [List.length_map] at this
  have huniv : (eGenW.map evalG).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd, hlen, ← Nat.card_eq_fintype_card, card_S6]
  have hmem : (⟨σ, hσ⟩ : S6) ∈ eGenW.map evalG := by
    rw [← List.mem_toFinset, huniv]
    exact Finset.mem_univ _
  obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hmem
  have hc : codeN 6 σ = c6 ⟨σ, hσ⟩ := rfl
  rw [hc, ← hwe, c6_evalG]
  exact List.mem_map.2 ⟨w, hw, rfl⟩

theorem cover (k : Bool) {σ : Perm (Fin 6)} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ τ ∈ tauY k, ∃ y ∈ Yk k, σ = τ * y := by
  have h := coverY_check k
  rw [List.all_eq_true] at h
  have h1 := h _ (codeN_mem_genC hσ)
  rw [List.any_eq_true] at h1
  obtain ⟨t, ht, h2⟩ := h1
  rw [List.any_eq_true] at h2
  obtain ⟨e, he, h3⟩ := h2
  rw [beq_iff_eq] at h3
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 ht
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_EY k he
  refine ⟨τ, hτ, y, hy, codeN_injective ?_⟩
  rw [codeN_mul, h3]

@[expose] def fourY (k : Bool) : Subgroup (Perm (Fin 6)) := Subgroup.closure {aY, bY k}

theorem aY_mem_fourY (k : Bool) : aY ∈ fourY k := Subgroup.subset_closure (by simp)

theorem bY_mem_fourY (k : Bool) : bY k ∈ fourY k := Subgroup.subset_closure (by simp)

theorem card_fourY_ge (k : Bool) : 4 ≤ Nat.card (fourY k) := by
  have h := B42Alt6.length_le_card (fourY k) [1, aY, bY k, aY * bY k]
    (by cases k <;> decide) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact aY_mem_fourY k
      · exact bY_mem_fourY k
      · exact mul_mem (aY_mem_fourY k) (bY_mem_fourY k))
  simpa using h

theorem four_conj {P : Subgroup (Perm (Fin 6))} (hPA : P ≤ alternatingGroup (Fin 6))
    (hP4 : Nat.card P = 4) (hel : ∀ x ∈ P, x * x = 1) :
    ∃ c ∈ alternatingGroup (Fin 6), ∃ k : Bool,
      P = (fourY k).map (MulAut.conj c).toMonoidHom := by
  classical
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra h
    push Not at h
    have : P = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
    rw [this, Subgroup.card_bot] at hP4
    omega
  have hx0A : B42Alt6.x0 ∈ alternatingGroup (Fin 6) := by
    unfold B42Alt6.x0; rw [Perm.mem_alternatingGroup]; decide
  obtain ⟨ρ, hρA, hρx⟩ := S143.alt6_invol_conj x B42Alt6.x0 (hPA hxP) hx0A hx1
    (by unfold B42Alt6.x0; decide) (hel x hxP) (by unfold B42Alt6.x0; decide)
  set P₁ := P.map (MulAut.conj ρ).toMonoidHom with hP₁
  have hmem₁ : ∀ y, y ∈ P₁ ↔ ρ⁻¹ * y * ρ ∈ P := by
    intro y
    rw [hP₁, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hx0P : B42Alt6.x0 ∈ P₁ := by
    rw [hmem₁, ← hρx]
    simpa [mul_assoc] using hxP
  have hP₁4 : Nat.card P₁ = 4 := by
    rw [hP₁, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hP4]
  have hel₁ : ∀ y ∈ P₁, y * y = 1 := by
    intro y hy
    have h := hel _ ((hmem₁ y).1 hy)
    have : ρ⁻¹ * (y * y) * ρ = 1 := by
      calc ρ⁻¹ * (y * y) * ρ = (ρ⁻¹ * y * ρ) * (ρ⁻¹ * y * ρ) := by group
        _ = 1 := h
    have h2 : y * y = ρ * (ρ⁻¹ * (y * y) * ρ) * ρ⁻¹ := by group
    rw [h2, this]
    group
  have hcomm₁ : ∀ y ∈ P₁, ∀ z ∈ P₁, y * z = z * y := by
    intro y hy z hz
    have h1 := hel₁ _ (P₁.mul_mem hy hz)
    have h2 := hel₁ y hy
    have h3 := hel₁ z hz
    calc y * z = y * (y * z * (y * z)) * z := by rw [h1]; group
      _ = (y * y) * (z * y) * (z * z) := by group
      _ = z * y := by rw [h2, h3]; group
  have hPA₁ : P₁ ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem y (hPA hy) ρ
  obtain ⟨y, hyP, hy1, hyx⟩ : ∃ y ∈ P₁, y ≠ 1 ∧ y ≠ B42Alt6.x0 := by
    by_contra h
    push Not at h
    have hle : P₁ ≤ Subgroup.zpowers B42Alt6.x0 := by
      intro z hz
      by_cases h1 : z = 1
      · rw [h1]; exact one_mem _
      · rw [h z hz h1]; exact Subgroup.mem_zpowers _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcz : Nat.card (Subgroup.zpowers B42Alt6.x0) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by unfold B42Alt6.x0; decide) (by unfold B42Alt6.x0; decide)
    have := Subgroup.card_le_of_le hle
    omega
  have hyA := hPA₁ hyP
  rw [Perm.mem_alternatingGroup] at hyA
  have hfin : ∀ k : Bool, bY k ∈ P₁ →
      ∃ c ∈ alternatingGroup (Fin 6), ∃ k : Bool,
        P = (fourY k).map (MulAut.conj c).toMonoidHom := by
    intro k hb
    have hK : fourY k ≤ P₁ := by
      unfold fourY
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact hx0P
      · exact hb
    have heq : fourY k = P₁ :=
      Subgroup.eq_of_le_of_card_ge hK (by rw [hP₁4]; exact card_fourY_ge k)
    refine ⟨ρ⁻¹, (alternatingGroup (Fin 6)).inv_mem hρA, k, ?_⟩
    have hid : (MulAut.conj ρ⁻¹).toMonoidHom.comp (MulAut.conj ρ).toMonoidHom =
        MonoidHom.id (Perm (Fin 6)) := by
      ext z : 1
      simp [MulAut.conj_apply, mul_assoc]
    rw [heq, hP₁, Subgroup.map_map, hid, Subgroup.map_id]
  rcases B42Alt6.comm_x0 y hyA (hel₁ y hyP) hy1 hyx (hcomm₁ y hyP _ hx0P) with h | h | h | h
  · refine hfin true ?_
    have : bY true = B42Alt6.x0 * y := by rw [h]; unfold B42Alt6.x0 bY; decide
    rw [this]
    exact P₁.mul_mem hx0P hyP
  · refine hfin true ?_
    have : bY true = y := by rw [h]; rfl
    rw [this]
    exact hyP
  · refine hfin false ?_
    have : bY false = y := by rw [h]; rfl
    rw [this]
    exact hyP
  · refine hfin false ?_
    have : bY false = B42Alt6.x0 * y := by rw [h]; unfold B42Alt6.x0 bY; decide
    rw [this]
    exact P₁.mul_mem hx0P hyP

@[expose] def t2Y (k : Bool) : Perm (Fin 6) :=
  if k then c[0, 2, 3, 4, 5] else c[0, 3, 1] * c[2, 5, 4]

@[expose] def t3Y (k : Bool) : Perm (Fin 6) := if k then c[0, 1, 2] else c[1, 2, 3, 4, 5]

theorem tauY_eq (k : Bool) :
    tauY k = [1, t2Y k, t3Y k, aY * t3Y k, bY k * t3Y k, aY * bY k * t3Y k] := by
  cases k <;> rfl

theorem t2Y_t3Y_mem (k : Bool) :
    t2Y k ∈ alternatingGroup (Fin 6) ∧ t3Y k ∈ alternatingGroup (Fin 6) := by
  simp only [Perm.mem_alternatingGroup]
  cases k <;> decide

section Lines

variable {V : Type} [CommGroup V]

@[expose] def lineOf (z : MulAut V) (x : V) : Subgroup V := Subgroup.closure {x, z x}

theorem mem_lineOf_self (z : MulAut V) (x : V) : x ∈ lineOf z x :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem map_lineOf {z t : MulAut V} (htz : ∀ y, t (z y) = z (t y)) (x : V) :
    (lineOf z x).map t.toMonoidHom = lineOf z (t x) := by
  unfold lineOf
  rw [MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, htz]

theorem lineOf_z {z : MulAut V} (hzz : ∀ w, z (z w) = w * z w) (x : V) :
    lineOf z (z x) = lineOf z x := by
  unfold lineOf
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [hzz]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · have h : z (z y) * (z y)⁻¹ ∈ Subgroup.closure ({z y, z (z y)} : Set V) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
          (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)))
      have e : z (z y) * (z y)⁻¹ = y := by rw [hzz, mul_inv_cancel_right]
      rw [e] at h
      exact h
    · exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem lineOf_zpow {z : MulAut V} (hzz : ∀ w, z (z w) = w * z w) (n : ℕ) (x : V) :
    lineOf z ((z ^ n) x) = lineOf z x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, lineOf_z hzz, ih]

theorem zpow_eq_one_or_self {a : V} (ha : a * a = 1) (m : ℤ) : a ^ m = 1 ∨ a ^ m = a := by
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ha, one_zpow, one_mul]

theorem card_lineOf_le [Finite V] (hsq : ∀ v : V, v * v = 1) (z : MulAut V) (x : V) :
    Nat.card (lineOf z x) ≤ 4 := by
  classical
  have hsub : ((lineOf z x : Subgroup V) : Set V) ⊆ ↑({1, x, z x, x * z x} : Finset V) := by
    intro y hy
    rw [SetLike.mem_coe, lineOf, Subgroup.mem_closure_pair] at hy
    obtain ⟨m, n, rfl⟩ := hy
    rcases zpow_eq_one_or_self (hsq x) m with h1 | h1 <;>
      rcases zpow_eq_one_or_self (hsq (z x)) n with h2 | h2 <;> simp [h1, h2]
  calc Nat.card (lineOf z x) = Set.ncard ((lineOf z x : Subgroup V) : Set V) :=
        (Nat.card_coe_set_eq _)
    _ ≤ Set.ncard (↑({1, x, z x, x * z x} : Finset V) : Set V) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 4 := by rw [Set.ncard_coe_finset]; exact Finset.card_le_four

end Lines

section Main

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem mem_fixV_closure_pair {a b : MulAut V} {x : V} :
    x ∈ fixV (Subgroup.closure ({a, b} : Set (MulAut V))) ↔ a x = x ∧ b x = x := by
  constructor
  · intro h
    exact ⟨h a (Subgroup.subset_closure (Set.mem_insert _ _)),
      h b (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨ha, hb⟩ y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    | one => rfl
    | mul p q _ _ hp hq => rw [MulAut.mul_apply, hq, hp]
    | inv p _ hp =>
      calc p⁻¹ x = p⁻¹ (p x) := by rw [hp]
        _ = x := MulAut.inv_apply_self V p x

theorem false_of_lines (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 12)
    {z : MulAut V} (hzz : ∀ w, z (z w) = w * z w) {L : Subgroup (MulAut V)}
    (hLz : ∀ l ∈ L, ∀ x, l (z x) = z (l x))
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ x ∈ J, l x ∈ J) → J = ⊥ ∨ J = ⊤)
    {u v T2 T3 : MulAut V} (hu : u ∈ L) (hv : v ∈ L) (hT2 : T2 ∈ L) (hT3 : T3 ∈ L)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (huv : u * v = v * u) {w : V} (hw1 : w ≠ 1)
    (hcov : ∀ y ∈ L, ∃ n : ℕ, y w = (z ^ n) w ∨ y w = (z ^ n) (T2 w) ∨ y w = (z ^ n) (T3 w) ∨
      y w = (z ^ n) (u (T3 w)) ∨ y w = (z ^ n) (v (T3 w)) ∨ y w = (z ^ n) (u (v (T3 w))))
    (hidx : (fixV (Subgroup.closure ({u, v} : Set (MulAut V)))).index ≤ 16) : False := by
  classical
  have hsq : ∀ x : V, x * x = 1 := fun x => by rw [← pow_two]; exact hV x
  set H : Subgroup (MulAut V) := Subgroup.closure ({u, v} : Set (MulAut V)) with hH
  set M0 := lineOf z w with hM0
  set M1 := lineOf z (T2 w) with hM1
  set M2 := lineOf z (T3 w) with hM2
  set M3 := lineOf z (u (T3 w)) with hM3
  set M4 := lineOf z (v (T3 w)) with hM4
  set M5 := lineOf z (u (v (T3 w))) with hM5
  set Msup := M0 ⊔ M1 ⊔ M2 ⊔ M3 ⊔ M4 ⊔ M5 with hMsup
  have hline : ∀ y ∈ L, lineOf z (y w) ≤ Msup := by
    intro y hy
    obtain ⟨n, h | h | h | h | h | h⟩ := hcov y hy <;> rw [h, lineOf_zpow hzz]
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
        le_sup_left)))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
        le_sup_right)))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  have hmap : ∀ l ∈ L, ∀ a x : V, x ∈ lineOf z a → l x ∈ lineOf z (l a) := by
    intro l hl a x hx
    have h1 := Subgroup.mem_map_of_mem l.toMonoidHom hx
    rw [map_lineOf (hLz l hl)] at h1
    exact h1
  have hinv : ∀ l ∈ L, ∀ x ∈ Msup, l x ∈ Msup := by
    intro l hl
    have hc : ∀ t ∈ L, lineOf z (t w) ≤ Msup.comap l.toMonoidHom := by
      intro t ht y hy
      have h1 := hmap l hl _ y hy
      exact hline (l * t) (L.mul_mem hl ht) h1
    have h0 : M0 ≤ Msup.comap l.toMonoidHom := by
      have := hc 1 L.one_mem
      simpa using this
    have hle : Msup ≤ Msup.comap l.toMonoidHom :=
      sup_le (sup_le (sup_le (sup_le (sup_le h0 (hc T2 hT2)) (hc T3 hT3))
        (hc (u * T3) (L.mul_mem hu hT3))) (hc (v * T3) (L.mul_mem hv hT3)))
        (hc (u * (v * T3)) (L.mul_mem hu (L.mul_mem hv hT3)))
    intro x hx
    exact hle hx
  have hle0 : M0 ≤ Msup := le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left le_sup_left)))
  have hwM : w ∈ Msup := hle0 (mem_lineOf_self z w)
  have htop : Msup = ⊤ := (hirr Msup hinv).resolve_left fun h => by
    rw [h, Subgroup.mem_bot] at hwM
    exact hw1 hwM
  let F : ↥M0 × ↥M1 × ↥M2 × ↥M3 × ↥M4 × ↥M5 → V := fun p =>
    (p.1 : V) * (p.2.1 : V) * (p.2.2.1 : V) * (p.2.2.2.1 : V) * (p.2.2.2.2.1 : V) *
      (p.2.2.2.2.2 : V)
  have hFs : Function.Surjective F := by
    intro x
    have hx : x ∈ Msup := htop ▸ Subgroup.mem_top x
    obtain ⟨y4, hy4, x5, hx5, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨y3, hy3, x4, hx4, rfl⟩ := Subgroup.mem_sup.1 hy4
    obtain ⟨y2, hy2, x3, hx3, rfl⟩ := Subgroup.mem_sup.1 hy3
    obtain ⟨y1, hy1, x2, hx2, rfl⟩ := Subgroup.mem_sup.1 hy2
    obtain ⟨x0, hx0, x1, hx1, rfl⟩ := Subgroup.mem_sup.1 hy1
    exact ⟨(⟨x0, hx0⟩, ⟨x1, hx1⟩, ⟨x2, hx2⟩, ⟨x3, hx3⟩, ⟨x4, hx4⟩, ⟨x5, hx5⟩), rfl⟩
  have hc0 := card_lineOf_le hsq z w
  have hc1 := card_lineOf_le hsq z (T2 w)
  have hc2 := card_lineOf_le hsq z (T3 w)
  have hc3 := card_lineOf_le hsq z (u (T3 w))
  have hc4 := card_lineOf_le hsq z (v (T3 w))
  have hc5 := card_lineOf_le hsq z (u (v (T3 w)))
  have hdom : Nat.card (↥M0 × ↥M1 × ↥M2 × ↥M3 × ↥M4 × ↥M5) =
      Nat.card M0 * (Nat.card M1 * (Nat.card M2 * (Nat.card M3 *
        (Nat.card M4 * Nat.card M5)))) := by
    simp only [Nat.card_prod]
  have hFb : Function.Bijective F := by
    refine hFs.bijective_of_nat_card_le ?_
    rw [hdom, hcard]
    calc Nat.card M0 * (Nat.card M1 * (Nat.card M2 * (Nat.card M3 *
          (Nat.card M4 * Nat.card M5)))) ≤ 4 * (4 * (4 * (4 * (4 * 4)))) := by
          gcongr
      _ = 2 ^ 12 := by norm_num
  have hP3 : 64 ≤ Nat.card M3 * (Nat.card M4 * Nat.card M5) := by
    have h1 := Nat.card_le_card_of_surjective F hFs
    rw [hdom, hcard] at h1
    have h2 : Nat.card M0 * (Nat.card M1 * (Nat.card M2 *
        (Nat.card M3 * (Nat.card M4 * Nat.card M5)))) ≤
        4 * (4 * (4 * (Nat.card M3 * (Nat.card M4 * Nat.card M5)))) := by
      gcongr
    omega
  set N : Subgroup V := M3 ⊔ M4 ⊔ M5 with hN
  have hdisj : fixV H ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxN⟩
    obtain ⟨y34, hy34, x5, hx5, rfl⟩ := Subgroup.mem_sup.1 hxN
    obtain ⟨x3, hx3, x4, hx4, rfl⟩ := Subgroup.mem_sup.1 hy34
    have hux := (mem_fixV_closure_pair.1 hxC).1
    have hvx := (mem_fixV_closure_pair.1 hxC).2
    have huu : ∀ y, u (u y) = y := fun y => by
      rw [← MulAut.mul_apply, hu2, MulAut.one_apply]
    have hvv : ∀ y, v (v y) = y := fun y => by
      rw [← MulAut.mul_apply, hv2, MulAut.one_apply]
    have hvu : ∀ y, v (u y) = u (v y) := fun y => by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, huv]
    have hu3' : u x3 ∈ M2 := by
      have h1 := hmap u hu _ x3 hx3
      rw [huu] at h1
      exact h1
    have hu4' : u x4 ∈ M5 := hmap u hu _ x4 hx4
    have hu5' : u x5 ∈ M4 := by
      have h1 := hmap u hu _ x5 hx5
      rw [huu] at h1
      exact h1
    have hFu : F (1, 1, ⟨_, hu3'⟩, 1, ⟨_, hu5'⟩, ⟨_, hu4'⟩) =
        F (1, 1, 1, ⟨x3, hx3⟩, ⟨x4, hx4⟩, ⟨x5, hx5⟩) := by
      show (1 : V) * 1 * u x3 * 1 * u x5 * u x4 = 1 * 1 * 1 * x3 * x4 * x5
      simp only [one_mul, mul_one]
      rw [← hux, map_mul, map_mul, mul_right_comm]
    have h1 := hFb.1 hFu
    simp only [Prod.mk.injEq] at h1
    have hx3' : x3 = 1 := (congrArg Subtype.val h1.2.2.2.1).symm
    subst hx3'
    have hv4' : v x4 ∈ M2 := by
      have h2 := hmap v hv _ x4 hx4
      rw [hvv] at h2
      exact h2
    have hv5' : v x5 ∈ M3 := by
      have h2 := hmap v hv _ x5 hx5
      rw [hvu, hvv] at h2
      exact h2
    have hFv : F (1, 1, ⟨_, hv4'⟩, ⟨_, hv5'⟩, 1, 1) =
        F (1, 1, 1, 1, ⟨x4, hx4⟩, ⟨x5, hx5⟩) := by
      show (1 : V) * 1 * v x4 * v x5 * 1 * 1 = 1 * 1 * 1 * 1 * x4 * x5
      rw [one_mul] at hvx
      simp only [one_mul, mul_one]
      rw [← hvx, map_mul]
    have h2 := hFb.1 hFv
    simp only [Prod.mk.injEq] at h2
    have hx4' : x4 = 1 := (congrArg Subtype.val h2.2.2.2.2.1).symm
    have hx5' : x5 = 1 := (congrArg Subtype.val h2.2.2.2.2.2).symm
    rw [hx4', hx5']
    simp
  have hCN : Nat.card (fixV H) * Nat.card N ≤ 2 ^ 12 := by
    have h1 := Nat.card_le_card_of_injective _ (mul_injective_of_inf_eq_bot hdisj)
    rwa [Nat.card_prod, hcard] at h1
  have hN64 : 64 ≤ Nat.card N := by
    have hN3 : M3 ≤ N := le_sup_of_le_left le_sup_left
    have hN4 : M4 ≤ N := le_sup_of_le_left le_sup_right
    have hN5 : M5 ≤ N := le_sup_right
    let G3 : ↥M3 × ↥M4 × ↥M5 → ↥N := fun p =>
      ⟨(p.1 : V) * (p.2.1 : V) * (p.2.2 : V),
        N.mul_mem (N.mul_mem (hN3 p.1.2) (hN4 p.2.1.2)) (hN5 p.2.2.2)⟩
    have hG3 : Function.Injective G3 := by
      rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
      have h1 : F (1, 1, 1, a, b, c) = F (1, 1, 1, a', b', c') := by
        have := congrArg Subtype.val h
        show (1 : V) * 1 * 1 * a * b * c = 1 * 1 * 1 * a' * b' * c'
        simpa [G3] using this
      have h2 := hFb.1 h1
      simp only [Prod.mk.injEq] at h2
      rw [h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2]
    have h1 := Nat.card_le_card_of_injective G3 hG3
    rw [Nat.card_prod, Nat.card_prod] at h1
    omega
  have hC256 : 256 ≤ Nat.card (fixV H) := by
    have h1 := (fixV H).card_mul_index
    rw [hcard] at h1
    have h2 : Nat.card (fixV H) * 16 ≥ 2 ^ 12 := by
      calc Nat.card (fixV H) * 16 ≥ Nat.card (fixV H) * (fixV H).index :=
            Nat.mul_le_mul_left _ hidx
        _ = 2 ^ 12 := h1
    omega
  have : 256 * 64 ≤ Nat.card (fixV H) * Nat.card N := Nat.mul_le_mul hC256 hN64
  omega

theorem false_of_pair (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L)
    (hcard : Nat.card V = 2 ^ 12)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* ↥(alternatingGroup (Fin 6))) (k : Bool) {u v : ↥L}
    (hu : ((e (QuotientGroup.mk u) : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = aY)
    (hv : ((e (QuotientGroup.mk v) : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = bY k)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (huv : u * v = v * u)
    (hidx : (fixV (Subgroup.closure ({(u : MulAut V), (v : MulAut V)} :
      Set (MulAut V)))).index ≤ 16) : False := by
  classical
  obtain ⟨zL, hcen, h3, hz1, hfp⟩ := HatA6.exists_center_gen hHyp hP
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hV h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLzn : ∀ (l : ↥L) (n : ℕ) (x : V),
      (l : MulAut V) ((z ^ n) x) = (z ^ n) ((l : MulAut V) x) := by
    intro l n x
    have h1 := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hzc n) l
    have h2 := congrArg (fun y : ↥L => (y : MulAut V) x) h1
    simpa [MulAut.mul_apply] using h2
  let π : ↥L →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)))
  have hπ : ∀ l : ↥L, π l = ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 6))) :
      Perm (Fin 6)) := fun l => rfl
  have hπA : ∀ l : ↥L, π l ∈ alternatingGroup (Fin 6) := fun l => (e (QuotientGroup.mk l)).2
  have hπs : ∀ σ ∈ alternatingGroup (Fin 6), ∃ l : ↥L, π l = σ := by
    intro σ hσ
    obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨l, by rw [hπ, hy]⟩
  have hπker : ∀ l : ↥L, π l = 1 → l ∈ Subgroup.center ↥L := by
    intro l hl
    have h1 : e (QuotientGroup.mk l) = 1 := Subtype.ext hl
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hπu : π u = aY := hu
  have hπv : π v = bY k := hv
  obtain ⟨g, hg⟩ := hπs gY (aY_bY k).2.2.2.2.2.1
  set H : Subgroup (MulAut V) := Subgroup.closure {(u : MulAut V), (v : MulAut V)} with hH
  have hidx' : (fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom)).index ≤ 16 := by
    have e1 := (fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom)).card_mul_index
    have e2 := (fixV H).card_mul_index
    rw [HatA6.card_fixV_conj] at e1
    have hpos : 0 < Nat.card (fixV H) := Nat.card_pos
    have : (fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom)).index = (fixV H).index :=
      Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
    rw [this]
    exact hidx
  have hinf : (fixV H ⊓ fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom)).index ≤ 256 :=
    (Subgroup.index_inf_le).trans (by nlinarith [Nat.zero_le (fixV H).index])
  obtain ⟨w, hwC, hw1⟩ : ∃ w ∈ fixV H ⊓ fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom),
      w ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : fixV H ⊓ fixV (H.map (MulAut.conj (g : MulAut V)).toMonoidHom) = ⊥ :=
      eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx)
    rw [hbot, Subgroup.index_bot, hcard] at hinf
    norm_num at hinf
  have hwu : (u : MulAut V) w = w := (mem_fixV_closure_pair.1 hwC.1).1
  have hwv : (v : MulAut V) w = w := (mem_fixV_closure_pair.1 hwC.1).2
  have hwg : ∀ x ∈ H, ((g : MulAut V) * x * (g : MulAut V)⁻¹) w = w := by
    intro x hx
    exact hwC.2 _ ⟨x, hx, rfl⟩
  have hwgu : ((g * u * g⁻¹ : ↥L) : MulAut V) w = w :=
    hwg _ (Subgroup.subset_closure (Set.mem_insert _ _))
  have hwgv : ((g * v * g⁻¹ : ↥L) : MulAut V) w = w :=
    hwg _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  set X : Subgroup ↥L := Subgroup.closure {u, v, g * u * g⁻¹, g * v * g⁻¹} with hX
  have hXw : ∀ x ∈ X, (x : MulAut V) w = w := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl | rfl | rfl
      · exact hwu
      · exact hwv
      · exact hwgu
      · exact hwgv
    | one => rfl
    | mul p q _ _ hp hq => rw [Subgroup.coe_mul, MulAut.mul_apply, hq, hp]
    | inv p _ hp =>
      rw [Subgroup.coe_inv]
      calc (p : MulAut V)⁻¹ w = (p : MulAut V)⁻¹ ((p : MulAut V) w) := by rw [hp]
        _ = w := MulAut.inv_apply_self V _ w
  have hXmap : X.map π = Yk k := by
    rw [hX, MonoidHom.map_closure]
    unfold Yk
    congr 1
    rw [gensY_eq]
    ext σ
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv, hπu, hπv, hg,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false]
  have hY : ∀ y : ↥L, π y ∈ Yk k → ∃ n : ℕ, (y : MulAut V) w = (z ^ n) w := by
    intro y hy
    rw [← hXmap] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hc : x⁻¹ * y ∈ Subgroup.center ↥L := by
      apply hπker
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hcen] at hc
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hc
    have hn' : zL ^ n = x⁻¹ * y := hn
    refine ⟨n, ?_⟩
    have hy' : y = x * zL ^ n := by rw [hn']; group
    rw [hy', Subgroup.coe_mul, MulAut.mul_apply, Subgroup.coe_pow, ← hzdef]
    have := hLzn x n w
    rw [this, hXw x hx]
  obtain ⟨T2, hT2⟩ := hπs (t2Y k) (t2Y_t3Y_mem k).1
  obtain ⟨T3, hT3⟩ := hπs (t3Y k) (t2Y_t3Y_mem k).2
  have hcov : ∀ y : ↥L, ∃ n : ℕ, (y : MulAut V) w = (z ^ n) w ∨
      (y : MulAut V) w = (z ^ n) ((T2 : MulAut V) w) ∨
      (y : MulAut V) w = (z ^ n) ((T3 : MulAut V) w) ∨
      (y : MulAut V) w = (z ^ n) ((u : MulAut V) ((T3 : MulAut V) w)) ∨
      (y : MulAut V) w = (z ^ n) ((v : MulAut V) ((T3 : MulAut V) w)) ∨
      (y : MulAut V) w = (z ^ n) ((u : MulAut V) ((v : MulAut V) ((T3 : MulAut V) w))) := by
    intro y
    obtain ⟨σ, hσ, yb, hyb, hπy⟩ := cover k (hπA y)
    have key : ∀ t : ↥L, π t = σ → ∃ n : ℕ, (y : MulAut V) w = (z ^ n) ((t : MulAut V) w) := by
      intro t ht
      have hy' : π (t⁻¹ * y) ∈ Yk k := by
        rw [map_mul, map_inv, ht, hπy, inv_mul_cancel_left]
        exact hyb
      obtain ⟨n, hn⟩ := hY _ hy'
      refine ⟨n, ?_⟩
      have h1 : y = t * (t⁻¹ * y) := by group
      rw [h1, Subgroup.coe_mul, MulAut.mul_apply, hn, hLzn]
    rw [tauY_eq] at hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨n, hn⟩ := key 1 (map_one π)
      exact ⟨n, Or.inl (by simpa using hn)⟩
    · obtain ⟨n, hn⟩ := key T2 hT2
      exact ⟨n, Or.inr (Or.inl hn)⟩
    · obtain ⟨n, hn⟩ := key T3 hT3
      exact ⟨n, Or.inr (Or.inr (Or.inl hn))⟩
    · obtain ⟨n, hn⟩ := key (u * T3) (by rw [map_mul, hπu, hT3])
      exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inl hn)))⟩
    · obtain ⟨n, hn⟩ := key (v * T3) (by rw [map_mul, hπv, hT3])
      exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))⟩
    · obtain ⟨n, hn⟩ := key (u * (v * T3)) (by rw [map_mul, map_mul, hπu, hπv, hT3, mul_assoc])
      exact ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))⟩
  refine false_of_lines hV hcard hzz (L := L) (fun l hl x => ?_) (HatA6.irr_of_b4Hyp hHyp)
    u.2 v.2 T2.2 T3.2 (congrArg Subtype.val hu2) (congrArg Subtype.val hv2)
    (congrArg Subtype.val huv) hw1 (fun y hy => hcov ⟨y, hy⟩) hidx
  simpa using hLzn ⟨l, hl⟩ 1 x

theorem index_fixV_map_conj (B : Subgroup (MulAut V)) (l : MulAut V) :
    (fixV (B.map (MulAut.conj l).toMonoidHom)).index = (fixV B).index :=
  CFSG.Quasithin.ConjTransport.index_fixV_map_conj B l

theorem false_of_four (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L)
    (hcard : Nat.card V = 2 ^ 12) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hAe : IsElemAbelian2 A) (hA4 : Nat.card A = 4) (hidx : (fixV A).index ≤ 16) : False := by
  classical
  obtain ⟨hq, hZ3, ⟨e⟩⟩ := id hP
  let π : ↥L →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)))
  have hπ : ∀ l : ↥L, π l = ((e (QuotientGroup.mk l) : ↥(alternatingGroup (Fin 6))) :
      Perm (Fin 6)) := fun l => rfl
  have hπA : ∀ l : ↥L, π l ∈ alternatingGroup (Fin 6) := fun l => (e (QuotientGroup.mk l)).2
  have hπs : ∀ σ ∈ alternatingGroup (Fin 6), ∃ l : ↥L, π l = σ := by
    intro σ hσ
    obtain ⟨y, hy⟩ := e.surjective ⟨σ, hσ⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨l, by rw [hπ, hy]⟩
  have hπker : ∀ l : ↥L, π l = 1 → l ∈ Subgroup.center ↥L := by
    intro l hl
    have h1 : e (QuotientGroup.mk l) = 1 := Subtype.ext hl
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  set A' : Subgroup ↥L := A.subgroupOf L with hA'
  let ψ : ↥A' →* Perm (Fin 6) := π.comp A'.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc := hπker _ ha
    have ha2 : ((a : ↥L) : MulAut V) ^ 2 = 1 := hAe.2 _ a.2
    exact Subtype.ext (Subtype.ext (HatA6.eq_one_of_mem_center hZ3 (a : ↥L).2 hc ha2))
  set P : Subgroup (Perm (Fin 6)) := A'.map π with hPdef
  have hPψ : P = ψ.range := by rw [hPdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hP4 : Nat.card P = 4 := by
    rw [hPψ, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, ← hA4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hPA : P ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨a, -, rfl⟩
    exact hπA a
  have hPel : ∀ x ∈ P, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hAe.2 _ ha)
    rw [this, map_one]
  obtain ⟨cb, hcb, k, hPk⟩ := four_conj hPA hP4 hPel
  obtain ⟨c, hc⟩ := hπs cb hcb
  have hlift : ∀ x ∈ fourY k, ∃ a ∈ A', π a = cb * x * cb⁻¹ := by
    intro x hx
    have h1 : (MulAut.conj cb).toMonoidHom x ∈ P := by
      rw [hPk]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨a, ha, h2⟩ := h1
    exact ⟨a, ha, h2⟩
  obtain ⟨a0, ha0, hπa0⟩ := hlift aY (aY_mem_fourY k)
  obtain ⟨b0, hb0, hπb0⟩ := hlift (bY k) (bY_mem_fourY k)
  have ha0L : ((a0 : ↥L) : MulAut V) ∈ A := ha0
  have hb0L : ((b0 : ↥L) : MulAut V) ∈ A := hb0
  set u : ↥L := c⁻¹ * a0 * c with hu
  set v : ↥L := c⁻¹ * b0 * c with hv
  have hπu : π u = aY := by rw [hu, map_mul, map_mul, map_inv, hπa0, hc]; group
  have hπv : π v = bY k := by rw [hv, map_mul, map_mul, map_inv, hπb0, hc]; group
  have ha2 : a0 * a0 = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hAe.2 _ ha0L)
  have hb2 : b0 * b0 = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hAe.2 _ hb0L)
  have hab : a0 * b0 = b0 * a0 := Subtype.ext (hAe.1 _ ha0L _ hb0L)
  have hu2 : u * u = 1 := by
    rw [hu]
    calc c⁻¹ * a0 * c * (c⁻¹ * a0 * c) = c⁻¹ * (a0 * a0) * c := by group
      _ = 1 := by rw [ha2]; group
  have hv2 : v * v = 1 := by
    rw [hv]
    calc c⁻¹ * b0 * c * (c⁻¹ * b0 * c) = c⁻¹ * (b0 * b0) * c := by group
      _ = 1 := by rw [hb2]; group
  have huv : u * v = v * u := by
    rw [hu, hv]
    calc c⁻¹ * a0 * c * (c⁻¹ * b0 * c) = c⁻¹ * (a0 * b0) * c := by group
      _ = c⁻¹ * (b0 * a0) * c := by rw [hab]
      _ = c⁻¹ * b0 * c * (c⁻¹ * a0 * c) := by group
  have hcl : Subgroup.closure ({((u : ↥L) : MulAut V), ((v : ↥L) : MulAut V)} : Set (MulAut V)) =
      (Subgroup.closure ({((a0 : ↥L) : MulAut V), ((b0 : ↥L) : MulAut V)} :
        Set (MulAut V))).map (MulAut.conj ((c : MulAut V)⁻¹)).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    congr 2
  have hle : Subgroup.closure ({((a0 : ↥L) : MulAut V), ((b0 : ↥L) : MulAut V)} :
      Set (MulAut V)) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha0L
    · exact hb0L
  have hidx2 : (fixV (Subgroup.closure ({((u : ↥L) : MulAut V), ((v : ↥L) : MulAut V)} :
      Set (MulAut V)))).index ≤ 16 := by
    rw [hcl, index_fixV_map_conj]
    exact (Subgroup.index_antitone (B1.fixV_le_fixV hle)).trans hidx
  exact false_of_pair hV hHyp hP hcard e k hπu hπv hu2 hv2 huv hidx2

end Main

end CFSG.Quasithin.B45HatA6
