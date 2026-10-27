module

public import CFSG.RankThree.PartOne.KLAY10.Plane

public section

namespace CFSG.RankThree.PartOne.KLAY10

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] def torusSub (P : Subgroup (Fin 3 → (Qext K)ˣ)) : Subgroup ↥(M10 K) where
  carrier := {g | ∃ x ∈ P, (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x}
  mul_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x * y, P.mul_mem hx hy, ?_⟩
    rw [Subgroup.coe_mul, ha, hb, torusEquiv_mul]
  one_mem' := ⟨1, P.one_mem, by rw [Subgroup.coe_one, torusEquiv_one]⟩
  inv_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨x⁻¹, P.inv_mem hx, ?_⟩
    have hinv : torusEquiv x⁻¹ = (torusEquiv x)⁻¹ := map_inv torusHom x
    rw [Subgroup.coe_inv, ha, hinv]

theorem mem_torusSub {P : Subgroup (Fin 3 → (Qext K)ˣ)} {g : ↥(M10 K)} :
    g ∈ torusSub P ↔ ∃ x ∈ P, (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x := Iff.rfl

@[expose] def planeI (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Fin 3 → (Qext K)ˣ) where
  carrier := {x | (∀ i, x i ^ p = 1) ∧ x 0 = 1}
  mul_mem' := fun {a b} ha hb => ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i], by simp [ha.2, hb.2]⟩
  one_mem' := ⟨fun i => by simp, rfl⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i], by simp [ha.2]⟩

@[expose] def planeII (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Fin 3 → (Qext K)ˣ) where
  carrier := {x | (∀ i, x i ^ p = 1) ∧ x 0 = x 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i], by simp [ha.2, hb.2]⟩
  one_mem' := ⟨fun i => by simp, rfl⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i], by simp [ha.2]⟩

@[expose] def TI (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup ↥(M10 K) :=
  torusSub (planeI p K)

@[expose] def TII (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup ↥(M10 K) :=
  torusSub (planeII p K)

theorem card_torusSub_le (hp : 0 < p) {P : Subgroup (Fin 3 → (Qext K)ˣ)}
    (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1) (a b : Fin 3)
    (hdet : ∀ x ∈ P, ∀ y ∈ P, x a = y a → x b = y b → x = y) :
    Nat.card (torusSub P) ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  have hch : ∀ g : torusSub P, ∃ x ∈ P, ((g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) =
      torusEquiv x := fun g => g.2
  choose x hxP hx using hch
  let f : torusSub P → rootsOfUnity p (Qext K) × rootsOfUnity p (Qext K) := fun g =>
    (⟨x g a, (mem_rootsOfUnity p _).2 (hPe _ (hxP g) a)⟩,
      ⟨x g b, (mem_rootsOfUnity p _).2 (hPe _ (hxP g) b)⟩)
  have hf : Function.Injective f := by
    intro g g' h
    have h1 : x g a = x g' a := congrArg (fun z => ((z.1 : (Qext K)ˣ))) h
    have h2 : x g b = x g' b := congrArg (fun z => ((z.2 : (Qext K)ˣ))) h
    have h3 := hdet _ (hxP g) _ (hxP g') h1 h2
    apply Subtype.ext
    apply Subtype.ext
    rw [hx g, hx g', h3]
  have h4 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at h4
  have h5 := card_rootsOfUnity (Qext K) p
  calc Nat.card (torusSub P) ≤ _ := h4
    _ ≤ p * p := Nat.mul_le_mul h5 h5
    _ = p ^ 2 := (sq p).symm

theorem card_TI_le (hp : 0 < p) : Nat.card (TI p K) ≤ p ^ 2 :=
  card_torusSub_le hp (fun x hx => hx.1) 1 2 fun x hx y hy h1 h2 => by
    funext k
    fin_cases k
    · exact hx.2.trans hy.2.symm
    · exact h1
    · exact h2

theorem card_TII_le (hp : 0 < p) : Nat.card (TII p K) ≤ p ^ 2 :=
  card_torusSub_le hp (fun x hx => hx.1) 1 2 fun x hx y hy h1 h2 => by
    funext k
    fin_cases k
    · exact hx.2.trans (h1.trans hy.2.symm)
    · exact h1
    · exact h2

theorem exists_standard_plane (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (T₀ : Subgroup ↥(M10 K))
    (hT₀ : ∀ t ∈ T₀, ∃ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) ∧
      (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x)
    (hcard : Nat.card T₀ = p ^ 2)
    (S : Subgroup ↥(M10 K)) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hT₀S : ∀ t ∈ T₀, ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    ∃ g : ↥(M10 K), T₀.map (MulAut.conj g).toMonoidHom = TI p K ∨
      T₀.map (MulAut.conj g).toMonoidHom = TII p K := by
  classical
  let P : Subgroup (Fin 3 → (Qext K)ˣ) :=
    { carrier := {x | (∀ i, x i ^ p = 1) ∧ ∃ t ∈ T₀,
        (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x}
      mul_mem' := by
        rintro a b ⟨ha, t, ht, hta⟩ ⟨hb, t', ht', htb⟩
        refine ⟨fun i => by simp [mul_pow, ha i, hb i], t * t', T₀.mul_mem ht ht', ?_⟩
        rw [Subgroup.coe_mul, hta, htb, torusEquiv_mul]
      one_mem' := ⟨fun i => by simp, 1, T₀.one_mem, by rw [Subgroup.coe_one, torusEquiv_one]⟩
      inv_mem' := by
        rintro a ⟨ha, t, ht, hta⟩
        refine ⟨fun i => by simp [inv_pow, ha i], t⁻¹, T₀.inv_mem ht, ?_⟩
        have hinv : torusEquiv a⁻¹ = (torusEquiv a)⁻¹ := map_inv torusHom a
        rw [Subgroup.coe_inv, hta, hinv] }
  have hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1 := fun x hx => hx.1
  let S' : Subgroup (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) := S.map (M10 K).subtype
  have hS'M : S' ≤ M10 K := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hS'2 : IsPGroup 2 S' :=
    hS2.of_surjective ((M10 K).subtype.subgroupMap S) ((M10 K).subtype.subgroupMap_surjective S)
  have hS'ne : S' ≠ ⊥ := by
    intro h
    apply hSne
    rw [eq_bot_iff]
    intro s hs
    have : ((s : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ∈ S' := ⟨s, hs, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  have hPS : ∀ x ∈ P, ∀ s ∈ S', torusEquiv x * s * (torusEquiv x)⁻¹ ∈ S' := by
    rintro x ⟨-, t, ht, hta⟩ _ ⟨s, hs, rfl⟩
    refine ⟨t * s * t⁻¹, hT₀S t ht s hs, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hta]
  have hrel : (∃ i, ∀ x ∈ P, x i = 1) ∨ (∃ i j, i ≠ j ∧ ∀ x ∈ P, x i = x j) ∨
      (∃ i j, i ≠ j ∧ ∀ x ∈ P, x i = (x j)⁻¹) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2, hc3⟩ := hcon
    apply hS'ne
    refine eq_bot_of_separated P hp hp2 hpq hPe S' hS'M hS'2 hPS hc1 ?_ ?_
    · intro i j hij
      obtain ⟨x, hx, hne⟩ := hc2 i j hij
      exact ⟨x, hx, hne⟩
    · intro i j hij
      obtain ⟨x, hx, hne⟩ := hc3 i j hij
      exact ⟨x, hx, hne⟩
  have hperm : ∀ i j : Fin 3, i ≠ j → ∃ π : Equiv.Perm (Fin 3), π i = 0 ∧ π j = 1 := by decide
  have hconj : ∀ (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (Q : Subgroup (Fin 3 → (Qext K)ˣ)),
      (∀ y : Fin 3 → (Qext K)ˣ, (∃ x ∈ P, ∀ k, y k = if s (π.symm k) then (x (π.symm k))⁻¹
        else x (π.symm k)) → y ∈ Q) → ∀ t' ∈ T₀.map (MulAut.conj
          (⟨sgnPerm π s, sgnPerm_mem_M10 π s⟩ : ↥(M10 K))).toMonoidHom, t' ∈ torusSub Q := by
    intro π s Q hQ t' ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    obtain ⟨x, hxe, htx⟩ := hT₀ t ht
    have hxP : x ∈ P := ⟨hxe, t, ht, htx⟩
    set y : Fin 3 → (Qext K)ˣ := fun k => if s (π.symm k) then (x (π.symm k))⁻¹
      else x (π.symm k) with hy
    have hyc := sgnPerm_conj hpq π s x y hxe (fun k => rfl)
    refine ⟨y, hQ y ⟨x, hxP, fun k => rfl⟩, ?_⟩
    show (((⟨sgnPerm π s, sgnPerm_mem_M10 π s⟩ : ↥(M10 K)) * t *
      (⟨sgnPerm π s, sgnPerm_mem_M10 π s⟩ : ↥(M10 K))⁻¹ : ↥(M10 K)) :
        QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, htx]
    exact hyc
  have hfin : ∀ g : ↥(M10 K), Nat.card (T₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := fun g => by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  rcases hrel with ⟨i, hi⟩ | ⟨i, j, hij, hij'⟩ | ⟨i, j, hij, hij'⟩
  ·
    let π : Equiv.Perm (Fin 3) := Equiv.swap i 0
    have hπi : π i = 0 := Equiv.swap_apply_left i 0
    have hπs : π.symm 0 = i := by rw [Equiv.symm_apply_eq]; exact hπi.symm
    refine ⟨⟨sgnPerm π (fun _ => false), sgnPerm_mem_M10 π _⟩, Or.inl ?_⟩
    have hle : T₀.map (MulAut.conj (⟨sgnPerm π (fun _ => false),
        sgnPerm_mem_M10 π _⟩ : ↥(M10 K))).toMonoidHom ≤ TI p K := by
      intro t' ht'
      refine hconj π (fun _ => false) (planeI p K) ?_ t' ht'
      rintro y ⟨x, hxP, hyx⟩
      refine ⟨fun k => ?_, ?_⟩
      · rw [hyx k]
        simp only [Bool.false_eq_true, ite_false]
        exact hxP.1 _
      · rw [hyx 0, hπs]
        simpa using hi x hxP
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hfin]; exact card_TI_le hp.pos)
  ·
    obtain ⟨π, hπi, hπj⟩ := hperm i j hij
    have hπi' : π.symm 0 = i := by rw [Equiv.symm_apply_eq]; exact hπi.symm
    have hπj' : π.symm 1 = j := by rw [Equiv.symm_apply_eq]; exact hπj.symm
    refine ⟨⟨sgnPerm π (fun _ => false), sgnPerm_mem_M10 π _⟩, Or.inr ?_⟩
    have hle : T₀.map (MulAut.conj (⟨sgnPerm π (fun _ => false),
        sgnPerm_mem_M10 π _⟩ : ↥(M10 K))).toMonoidHom ≤ TII p K := by
      intro t' ht'
      refine hconj π (fun _ => false) (planeII p K) ?_ t' ht'
      rintro y ⟨x, hxP, hyx⟩
      refine ⟨fun k => ?_, ?_⟩
      · rw [hyx k]
        simp only [Bool.false_eq_true, ite_false]
        exact hxP.1 _
      · rw [hyx 0, hyx 1, hπi', hπj']
        simpa using hij' x hxP
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hfin]; exact card_TII_le hp.pos)
  ·
    obtain ⟨π, hπi, hπj⟩ := hperm i j hij
    have hπi' : π.symm 0 = i := by rw [Equiv.symm_apply_eq]; exact hπi.symm
    have hπj' : π.symm 1 = j := by rw [Equiv.symm_apply_eq]; exact hπj.symm
    refine ⟨⟨sgnPerm π (fun k => decide (k = j)), sgnPerm_mem_M10 π _⟩, Or.inr ?_⟩
    have hle : T₀.map (MulAut.conj (⟨sgnPerm π (fun k => decide (k = j)),
        sgnPerm_mem_M10 π _⟩ : ↥(M10 K))).toMonoidHom ≤ TII p K := by
      intro t' ht'
      refine hconj π (fun k => decide (k = j)) (planeII p K) ?_ t' ht'
      rintro y ⟨x, hxP, hyx⟩
      refine ⟨fun k => ?_, ?_⟩
      · rw [hyx k]
        by_cases h : decide (π.symm k = j) = true
        · simp only [h, ite_true]
          rw [inv_pow, hxP.1 _, inv_one]
        · simp only [h]
          exact hxP.1 _
      · rw [hyx 0, hyx 1, hπi', hπj']
        have hij0 : decide (i = j) = false := by simpa using hij
        simp only [hij0, Bool.false_eq_true, ite_false, decide_true, ite_true]
        exact hij' x hxP
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hfin]; exact card_TII_le hp.pos)

end CFSG.RankThree.PartOne.KLAY10
