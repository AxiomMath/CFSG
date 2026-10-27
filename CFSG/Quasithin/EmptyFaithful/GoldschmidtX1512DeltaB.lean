module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.X1512

@[expose] def fixΔ (n : ℕ) (B : Subgroup (Equiv.Perm (Fin n))) : Subgroup ↥(G6.coreMod n) where
  carrier := {u | ∀ σ ∈ B, G6.coreAct n σ u = u}
  one_mem' := fun σ _ => map_one _
  mul_mem' := fun {a b} ha hb σ hσ => by
    simp only [map_mul]
    rw [ha σ hσ, hb σ hσ]
  inv_mem' := fun {a} ha σ hσ => by
    simp only [map_inv]
    rw [ha σ hσ]

namespace Delta

private theorem coreAct_conj {n : ℕ} (g σ : Equiv.Perm (Fin n)) (u : G6.coreMod n) :
    G6.coreAct n (g * σ * g⁻¹) u = G6.coreAct n g (G6.coreAct n σ (G6.coreAct n g⁻¹ u)) := by
  simp [map_mul]

private theorem coreAct_inv_cancel {n : ℕ} (g : Equiv.Perm (Fin n)) (u : G6.coreMod n) :
    G6.coreAct n g⁻¹ (G6.coreAct n g u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem coreAct_cancel_inv {n : ℕ} (g : Equiv.Perm (Fin n)) (u : G6.coreMod n) :
    G6.coreAct n g (G6.coreAct n g⁻¹ u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem mem_fixΔ_conj {n : ℕ} (B : Subgroup (Equiv.Perm (Fin n)))
    (g : Equiv.Perm (Fin n)) (u : G6.coreMod n) :
    u ∈ fixΔ n (B.map (MulAut.conj g).toMonoidHom) ↔ G6.coreAct n g⁻¹ u ∈ fixΔ n B := by
  constructor
  · intro hu σ hσ
    have h := hu (g * σ * g⁻¹) ⟨σ, hσ, rfl⟩
    rw [coreAct_conj] at h
    have h2 := congrArg (G6.coreAct n g⁻¹) h
    rwa [coreAct_inv_cancel] at h2
  · rintro hu _ ⟨σ, hσ, rfl⟩
    show G6.coreAct n (g * σ * g⁻¹) u = u
    rw [coreAct_conj, hu σ hσ, coreAct_cancel_inv]

end Delta

theorem card_fixΔ_conj {n : ℕ} (B : Subgroup (Equiv.Perm (Fin n))) (g : Equiv.Perm (Fin n)) :
    Nat.card (fixΔ n (B.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixΔ n B) :=
  Nat.card_congr
    { toFun := fun u => ⟨G6.coreAct n g⁻¹ u.1, (Delta.mem_fixΔ_conj B g u.1).mp u.2⟩
      invFun := fun v => ⟨G6.coreAct n g v.1, (Delta.mem_fixΔ_conj B g _).mpr (by
        rw [Delta.coreAct_inv_cancel]; exact v.2)⟩
      left_inv := fun u => Subtype.ext (Delta.coreAct_cancel_inv g u.1)
      right_inv := fun v => Subtype.ext (Delta.coreAct_inv_cancel g v.1) }

namespace Delta

@[expose] def fixCount (n : ℕ) (S : Finset (Equiv.Perm (Fin n))) : ℕ :=
  (Finset.univ.filter (fun u : Dsub n => ∀ σ ∈ S, G6.permAct n σ u.1 = u.1)).card

@[expose] def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (subs l).map (a :: ·) ++ subs l

private theorem card_fixΔ_eq {n : ℕ} (B : Subgroup (Equiv.Perm (Fin n)))
    (S : Finset (Equiv.Perm (Fin n))) (hS : ∀ σ, σ ∈ S ↔ σ ∈ B) :
    Nat.card (fixΔ n B) = fixCount n S := by
  classical
  unfold fixCount
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  show (∀ σ ∈ B, G6.coreAct n σ u = u) ↔ ∀ σ ∈ S, G6.permAct n σ u.1 = u.1
  refine forall_congr' fun σ => ?_
  rw [← hS σ]
  exact imp_congr_right fun _ => Subtype.ext_iff

private theorem natCard_eq_card {n : ℕ} (B : Subgroup (Equiv.Perm (Fin n)))
    (S : Finset (Equiv.Perm (Fin n))) (hS : ∀ σ, σ ∈ S ↔ σ ∈ B) : Nat.card B = S.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (hS σ).symm)

private theorem filter_mem_subs {α : Type} (p : α → Bool) : ∀ L : List α, L.filter p ∈ subs L
  | [] => by simp [subs]
  | a :: L => by
    have ih := filter_mem_subs p L
    simp only [subs, List.mem_append, List.mem_map, List.filter_cons]
    by_cases h : p a = true
    · exact Or.inl ⟨_, ih, by simp [h]⟩
    · exact Or.inr (by simpa [h] using ih)

@[expose] def FinConcl (n : ℕ) (D B : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  Nat.card B * Nat.card (fixΔ n B) ≤ 2 ^ (n - 1) ∧
    (Nat.card B * Nat.card (fixΔ n B) = 2 ^ (n - 1) → B ≠ ⊥ →
      ∃ ξ : Equiv.Perm (Fin n), ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
        (∀ g ∈ B, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧ (∃ g ∈ B, g * ξ * g⁻¹ = ξ⁻¹) ∧
        Subgroup.closure ({ξ} ∪ (D : Set (Equiv.Perm (Fin n)))) = ⊤)

theorem fin_of_cert {n : ℕ} {Dstd : Subgroup (Equiv.Perm (Fin n))}
    {E cands : List (Equiv.Perm (Fin n))} {Gen : Equiv.Perm (Fin n) → Prop}
    (hE : ∀ x ∈ Dstd, x * x = 1 → x = 1 ∨ x ∈ E)
    (cert : ∀ l ∈ subs E, (∀ a ∈ l, ∀ b ∈ l, a * b = b * a) →
      (∀ a ∈ l, ∀ b ∈ l, a * b = 1 ∨ a * b ∈ l) →
      (1 :: l).toFinset.card * fixCount n (1 :: l).toFinset ≤ 2 ^ (n - 1) ∧
      ((1 :: l).toFinset.card * fixCount n (1 :: l).toFinset = 2 ^ (n - 1) → l ≠ [] →
        ∃ ξ ∈ cands, ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
          (∀ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧
          (∃ g ∈ 1 :: l, g * ξ * g⁻¹ = ξ⁻¹) ∧ Gen ξ))
    {B : Subgroup (Equiv.Perm (Fin n))} (hBD : B ≤ Dstd)
    (hBe : CFSG.Open.IsElemAbelian 2 B) :
    Nat.card B * Nat.card (fixΔ n B) ≤ 2 ^ (n - 1) ∧
    (Nat.card B * Nat.card (fixΔ n B) = 2 ^ (n - 1) → B ≠ ⊥ →
      ∃ ξ : Equiv.Perm (Fin n), ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
        (∀ g ∈ B, g * ξ * g⁻¹ = ξ ∨ g * ξ * g⁻¹ = ξ⁻¹) ∧ (∃ g ∈ B, g * ξ * g⁻¹ = ξ⁻¹) ∧
        Gen ξ) := by
  classical
  set l : List (Equiv.Perm (Fin n)) := E.filter (fun x => decide (x ∈ B)) with hl
  have hmem : ∀ x, x ∈ B ↔ x = 1 ∨ x ∈ l := fun x => by
    simp only [hl, List.mem_filter, decide_eq_true_eq]
    refine ⟨fun hx => ?_, ?_⟩
    · rcases hE x (hBD hx) (by rw [← pow_two]; exact hBe.2 x hx) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | ⟨-, hx⟩)
      · exact B.one_mem
      · exact hx
  have hS : ∀ σ, σ ∈ (1 :: l).toFinset ↔ σ ∈ B := fun σ => by
    rw [List.mem_toFinset, List.mem_cons]
    exact (hmem σ).symm
  have hcom : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a := fun a ha b hb => by
    have := isMulCommutative_iff.mp hBe.1 ⟨a, (hmem a).mpr (Or.inr ha)⟩
      ⟨b, (hmem b).mpr (Or.inr hb)⟩
    exact congrArg Subtype.val this
  have hcl : ∀ a ∈ l, ∀ b ∈ l, a * b = 1 ∨ a * b ∈ l := fun a ha b hb =>
    (hmem _).mp (B.mul_mem ((hmem a).mpr (Or.inr ha)) ((hmem b).mpr (Or.inr hb)))
  obtain ⟨hle, heq⟩ := cert l (filter_mem_subs _ E) hcom hcl
  rw [natCard_eq_card B _ hS, card_fixΔ_eq B _ hS]
  refine ⟨hle, fun h hB => ?_⟩
  have hne : l ≠ [] := fun h0 => hB (by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases (hmem x).mp hx with h1 | h1
    · exact h1
    · simp [h0] at h1)
  obtain ⟨ξ, -, h3, h1, hc, hi, hg⟩ := heq h hne
  exact ⟨ξ, h3, h1, fun g hg' => hc g (List.mem_cons.mpr ((hmem g).mp hg')),
    by obtain ⟨g, hg', hgi⟩ := hi; exact ⟨g, (hmem g).mpr (List.mem_cons.mp hg'), hgi⟩, hg⟩

private theorem finConcl_conj {n : ℕ} {D0 B0 : Subgroup (Equiv.Perm (Fin n))}
    (g : Equiv.Perm (Fin n)) (h0 : FinConcl n D0 B0) :
    FinConcl n (D0.map (MulAut.conj g).toMonoidHom) (B0.map (MulAut.conj g).toMonoidHom) := by
  have hcard : Nat.card (B0.map (MulAut.conj g).toMonoidHom) = Nat.card B0 :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  unfold FinConcl at h0 ⊢
  rw [hcard, card_fixΔ_conj B0 g]
  refine ⟨h0.1, fun heq hne => ?_⟩
  obtain ⟨ξ, h3, h1, hc, hi, hcl⟩ := h0.2 heq (fun h => hne (by rw [h, Subgroup.map_bot]))
  have e : ∀ b0 : Equiv.Perm (Fin n),
      (MulAut.conj g).toMonoidHom b0 * (g * ξ * g⁻¹) * ((MulAut.conj g).toMonoidHom b0)⁻¹ =
        g * (b0 * ξ * b0⁻¹) * g⁻¹ := fun b0 => by simp [MulAut.conj_apply]; group
  refine ⟨g * ξ * g⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, h3, mul_one, mul_inv_cancel]
  · intro h
    exact h1 (by simpa using h)
  · rintro b ⟨b0, hb0, rfl⟩
    rw [e]
    rcases hc b0 hb0 with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; group)
  · obtain ⟨b0, hb0, h⟩ := hi
    exact ⟨(MulAut.conj g).toMonoidHom b0, ⟨b0, hb0, rfl⟩, by rw [e, h]; group⟩
  · rw [eq_top_iff]
    intro x _
    have hle : Subgroup.closure ({ξ} ∪ (D0 : Set (Equiv.Perm (Fin n)))) ≤
        (Subgroup.closure ({g * ξ * g⁻¹} ∪
          ((D0.map (MulAut.conj g).toMonoidHom : Subgroup _) : Set (Equiv.Perm (Fin n))))).comap
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact Subgroup.subset_closure (Or.inl (by simp [MulAut.conj_apply]))
      · exact Subgroup.subset_closure (Or.inr ⟨y, hy, rfl⟩)
    have hy := hle (hcl ▸ Subgroup.mem_top (g⁻¹ * x * g))
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem finConcl_of_conj {n : ℕ} {D0 D B : Subgroup (Equiv.Perm (Fin n))}
    (hstd : ∀ {B0 : Subgroup (Equiv.Perm (Fin n))}, B0 ≤ D0 → CFSG.Open.IsElemAbelian 2 B0 →
      FinConcl n D0 B0)
    (g : Equiv.Perm (Fin n)) (hg : D = D0.map (MulAut.conj g).toMonoidHom) (hBD : B ≤ D)
    (hBe : CFSG.Open.IsElemAbelian 2 B) : FinConcl n D B := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hB : (B.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = B :=
    Subgroup.map_comap_eq_self_of_surjective (MulEquiv.surjective _) B
  have hle : B.comap (MulAut.conj g).toMonoidHom ≤ D0 := by
    intro x hx
    have : (MulAut.conj g).toMonoidHom x ∈ D0.map (MulAut.conj g).toMonoidHom := hg ▸ hBD hx
    obtain ⟨y, hy, hyx⟩ := this
    exact hinj hyx ▸ hy
  have hel : CFSG.Open.IsElemAbelian 2 (B.comap (MulAut.conj g).toMonoidHom) := by
    refine ⟨isMulCommutative_iff.mpr fun a b => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have h1 := congrArg Subtype.val (isMulCommutative_iff.mp hBe.1 ⟨_, a.2⟩ ⟨_, b.2⟩)
      exact (map_mul _ _ _).trans (h1.trans (map_mul _ _ _).symm)
    · apply hinj
      rw [map_pow, hBe.2 _ hx, map_one]
  have := finConcl_conj g (hstd hle hel)
  rwa [hB, ← hg] at this

end Delta

end CFSG.Quasithin.X1512
