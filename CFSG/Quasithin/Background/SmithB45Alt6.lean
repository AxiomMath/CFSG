module

public import CFSG.Quasithin.Background.SmithB45AltBase
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42Alt6Norm

public section

namespace CFSG.Quasithin

namespace B45Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E
  CFSG.Quasithin.S143 B42Alt6

variable {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}

theorem exists_n6Model_of_lt [Finite S] {G : Subgroup (MulAut S)} (hS : ∀ s : S, s * s = 1)
    (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (hcard : Nat.card S < 2 ^ 16) :
    Nonempty (N6Model L) := by
  classical
  obtain ⟨ι⟩ := C.iso
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul, pow_two]
      exact hS _
    exact toMul_eq_one.1 h3
  let θ : S ≃* Multiplicative (Additive S) := (MulEquiv.multiplicativeAdditive S).symm
  let σ : S6 →* (Additive S ≃ₗ[ZMod 2] Additive S) :=
    (Setup.Layer.binPsi θ).toMonoidHom.comp (L.subtype.comp ι.symm.toMonoidHom)
  have hσ : ∀ γ w, σ γ w = Additive.ofMul ((ι.symm γ : MulAut S) (Additive.toMul w)) :=
    fun γ w => rfl
  have hsimple : Setup.X3.IsLSimple σ ⊤ ⊤ := by
    refine ⟨fun _ _ _ _ => trivial, ?_, fun U hU _ => ?_⟩
    · intro h
      obtain ⟨s, -, hs⟩ := IsConcreteLE.exists_of_lt hirr.1
      have h1 : Additive.ofMul s ∈ (⊤ : Submodule (ZMod 2) (Additive S)) := trivial
      rw [h, Submodule.mem_bot] at h1
      exact hs (Subgroup.mem_bot.2 (by simpa using h1))
    · let J : Subgroup S :=
        { carrier := {s | Additive.ofMul s ∈ U}
          one_mem' := U.zero_mem
          mul_mem' := fun ha hb => U.add_mem ha hb
          inv_mem' := fun ha => U.neg_mem ha }
      have hinv : XMod.IsInv ↥L J := by
        intro a j hj
        have h1 := hU (ι a) trivial (Additive.ofMul j) hj
        have h2 : σ (ι a) (Additive.ofMul j) = Additive.ofMul ((a : MulAut S) j) := by
          rw [hσ, MulEquiv.symm_apply_apply]
          rfl
        rw [h2] at h1
        exact h1
      rcases hirr.2 J hinv bot_le le_top with h | h
      · left
        rw [eq_bot_iff]
        intro w hw
        have h1 : Additive.toMul w ∈ J := hw
        rw [h, Subgroup.mem_bot] at h1
        rw [Submodule.mem_bot]
        exact h1
      · right
        rw [eq_top_iff]
        intro w _
        have h1 : Additive.toMul w ∈ J := by rw [h]; trivial
        exact h1
  obtain ⟨i, hi, Ψ, hΨ⟩ := exists_block_iso σ hsimple
  have hcardS : Nat.card S = 2 ^ (eNs.getD (i + 1) 0 - eNs.getD i 0) := by
    have h1 : Nat.card (Vec (eNs.getD (i + 1) 0 - eNs.getD i 0)) = Nat.card (Additive S) :=
      Nat.card_congr Ψ.toEquiv
    have h2 : Nat.card (Additive S) = Nat.card S := rfl
    rw [← h2, ← h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin _),
      Fintype.card_fin]
  have hone : ∀ b, (ι.symm (gen b) : MulAut S) ≠ 1 := by
    intro b h
    have h1 : ι.symm (gen b) = 1 := Subtype.ext h
    have h2 : gen b = 1 := by
      have := congrArg ι h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    cases b <;> exact absurd h2 (by decide)
  have htriv : (∀ b (s : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0)),
      lin _ (blkOf i b) s = s) → False := by
    intro hlin
    apply hone false
    apply MulEquiv.ext
    intro v
    obtain ⟨s, hs⟩ := Ψ.surjective (Additive.ofMul v)
    have h1 := hΨ false s
    rw [hlin, hs, hσ] at h1
    exact (congrArg Additive.toMul h1).symm
  interval_cases i
  · exact model_of_block blockOK_0 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_2 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_5 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact model_of_block blockOK_6 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_8 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exact (htriv fun b s => by rw [blkOf_one (by omega) b]; exact lin_one s).elim
  · exact model_of_block blockOK_10 ι Ψ fun b s => (hΨ b s).trans (hσ _ _)
  · exfalso
    have h16 : eNs.getD (11 + 1) 0 - eNs.getD 11 0 = 16 := by decide
    rw [hcardS, h16] at hcard
    exact lt_irrefl _ hcard

@[expose] def k4List : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 2 3 * swap 4 5, swap 0 1 * swap 4 5]

theorem k4_mul : ∀ a ∈ k4List, ∀ b ∈ k4List, a * b ∈ k4List := by decide +kernel

theorem k4_comm : ∀ a ∈ k4List, ∀ b ∈ k4List, a * b = b * a := by decide +kernel

theorem k4_sq : ∀ a ∈ k4List, a * a = 1 := by decide +kernel

theorem k4_sign : ∀ a ∈ k4List, sign a = 1 := by decide +kernel

@[expose] def K4 : Subgroup (Perm (Fin 6)) where
  carrier := {x | x ∈ k4List}
  mul_mem' := fun {a b} ha hb => k4_mul a ha b hb
  one_mem' := by simp [k4List]
  inv_mem' := fun {a} ha => by
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (k4_sq a ha)
    show a⁻¹ ∈ k4List
    rw [this]
    exact ha

theorem card_K4 : Nat.card K4 = 4 := by
  have h : (K4 : Set (Perm (Fin 6))) = ↑k4List.toFinset := by
    ext x
    simp [K4]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

theorem card_fix_K4 :
    (Finset.univ.filter fun a : N6 => ∀ σ ∈ k4List, n6Act σ a = a).card = 4 := by
  decide +kernel

theorem card_fixV_K4 (M : N6Model L) : Nat.card (fixV (K4.map M.ρ)) = 4 := by
  rw [M.card_fixV_map, ← card_fix_K4]
  rw [show Nat.card {a : N6 // ∀ σ ∈ K4, n6Act σ a = a} =
      Nat.card {a : N6 // ∀ σ ∈ k4List, n6Act σ a = a} from
    Nat.card_congr (Equiv.subtypeEquivRight fun a => Iff.rfl)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end B45Alt6

open B42Alt6 B45Alt6 in
theorem asB45Alt6_holds : AsB45Alt6 := by
  intro V _ _ hV G L hB hT hq
  have C := ctx_of_b4Hyp hB hT
  have hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := hB.2.2.2
  have hS2 : ∀ s : V, s * s = 1 := fun s => by simpa [pow_two] using hV s
  obtain ⟨A, hA, -, hidx⟩ := B45Alt.exists_cubic_of_qhatOf_le_two hV hq
  obtain ⟨r, m, hr, -, -, hmr, hle⟩ := card_le_index_pow C hirr hA.1 hA.2.1 hA.2.2
  have hlt : Nat.card V < 2 ^ 16 := by
    calc Nat.card V ≤ (fixV A).index ^ m := hle
      _ ≤ (Nat.card A ^ 2) ^ m := Nat.pow_le_pow_left hidx m
      _ = 2 ^ (2 * (m * r)) := by rw [hr, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 16 := by norm_num
  obtain ⟨M⟩ := exists_n6Model_of_lt hS2 C hirr hlt
  refine B45Alt.qhatOf_le_one_of_four hV (A := K4.map M.ρ) ?_ ⟨?_, ?_⟩ ?_ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact C.le_G (M.ρ_mem_L (Equiv.Perm.mem_alternatingGroup.2 (k4_sign σ hσ)))
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, k4_comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_two, k4_sq a ha, map_one]
  · rw [Subgroup.card_map_of_injective M.ρ_inj, card_K4]
  · rw [M.card_eq, card_fixV_K4 M]

end CFSG.Quasithin
