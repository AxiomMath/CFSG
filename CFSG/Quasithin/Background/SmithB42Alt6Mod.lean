module

public import CFSG.Quasithin.Background.SmithB42Alt6Ctx
public import CFSG.Quasithin.Background.SmithB42Alt6Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EMod

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E
  CFSG.Quasithin.S143

variable {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}

structure N6Model (L : Subgroup (MulAut S)) where
  Θ : S ≃* N6
  ρ : Perm (Fin 6) →* MulAut S
  ρ_inj : Function.Injective ρ
  Θ_ρ : ∀ (σ : Perm (Fin 6)) (v : S), Θ (ρ σ v) = n6Act σ (Θ v)
  ρ_alt : (alternatingGroup (Fin 6)).map ρ = L

@[expose] noncomputable def rhoOf (Θ : S ≃* N6) : Perm (Fin 6) →* MulAut S :=
  (MulAut.congr Θ.symm).toMonoidHom.comp n6Act

theorem rhoOf_apply (Θ : S ≃* N6) (σ : Perm (Fin 6)) (v : S) :
    Θ (rhoOf Θ σ v) = n6Act σ (Θ v) := by
  show Θ (Θ.symm (n6Act σ (Θ v))) = _
  rw [MulEquiv.apply_symm_apply]

theorem rhoOf_injective (Θ : S ≃* N6) : Function.Injective (rhoOf Θ) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply n6_faithful_perm
  intro a
  have h := rhoOf_apply Θ σ (Θ.symm a)
  rw [hσ, MulAut.one_apply, MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem model_of_gens (ι : ↥L ≃* alternatingGroup (Fin 6)) (Θ : S ≃* N6)
    (g : Bool → Perm (Fin 6)) (hg : ∀ b, g b ∈ alternatingGroup (Fin 6))
    (hgen : alternatingGroup (Fin 6) ≤ Subgroup.closure ({g false, g true} : Set (Perm (Fin 6))))
    (hΘ : ∀ (b : Bool) (v : S), Θ ((ι.symm (gen b) : MulAut S) v) = n6Act (g b) (Θ v)) :
    Nonempty (N6Model L) := by
  have hρg : ∀ b, rhoOf Θ (g b) = (ι.symm (gen b) : MulAut S) := by
    intro b
    apply MulEquiv.ext
    intro v
    apply Θ.injective
    rw [rhoOf_apply, hΘ]
  have hcl : alternatingGroup (Fin 6) = Subgroup.closure ({g false, g true} : Set (Perm (Fin 6))) :=
    le_antisymm hgen (by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg false
      · exact hg true)
  refine ⟨⟨Θ, rhoOf Θ, rhoOf_injective Θ, rhoOf_apply Θ, ?_⟩⟩
  have h1 : (alternatingGroup (Fin 6)).map (rhoOf Θ) =
      Subgroup.closure {(ι.symm gx : MulAut S), (ι.symm gy : MulAut S)} := by
    conv_lhs => rw [hcl]
    rw [MonoidHom.map_closure, Set.image_pair, hρg, hρg]
    rfl
  have h2 : L = Subgroup.closure {(ι.symm gx : MulAut S), (ι.symm gy : MulAut S)} := by
    have hL : L = (⊤ : Subgroup (alternatingGroup (Fin 6))).map
        (L.subtype.comp ι.symm.toMonoidHom) := by
      rw [← MonoidHom.range_eq_map]
      ext x
      constructor
      · intro hx
        exact ⟨ι ⟨x, hx⟩, by simp⟩
      · rintro ⟨y, rfl⟩
        exact (ι.symm y).2
    conv_lhs => rw [hL, ← closure_xy, MonoidHom.map_closure, Set.image_pair]
    rfl
  exact h1.trans h2.symm

theorem model_of_block [Module (ZMod 2) (Additive S)] {i : ℕ} (h : BlockOK i)
    (ι : ↥L ≃* alternatingGroup (Fin 6)) (Ψ : Vec 4 ≃ₗ[ZMod 2] Additive S)
    (hΨ : ∀ (b : Bool) (s : Vec 4), Ψ (lin 4 (blkOf i b) s) =
      Additive.ofMul ((ι.symm (gen b) : MulAut S) (Additive.toMul (Ψ s)))) :
    Nonempty (N6Model L) := by
  let Θ : S ≃* N6 := ((MulEquiv.multiplicativeAdditive S).symm.trans
    (AddEquiv.toMultiplicative Ψ.symm.toAddEquiv)).trans (qEquiv h)
  have hΘ : ∀ v : S, Θ v = qEquiv h (Multiplicative.ofAdd (Ψ.symm (Additive.ofMul v))) :=
    fun v => rfl
  have hg : ∀ b, gImg i b ∈ alternatingGroup (Fin 6) := by
    intro b
    unfold gImg
    split_ifs
    · exact (show tw2 ∈ alternatingGroup (Fin 6) by
        rw [mem_alternatingGroup]; decide)
    · exact (show tw1 ∈ alternatingGroup (Fin 6) by
        rw [mem_alternatingGroup]; decide)
    · exact (gen b).2
  refine model_of_gens ι Θ (gImg i) hg (alt_le_closure_gImg i) fun b v => ?_
  rw [hΘ, hΘ]
  have h1 := hΨ b (Ψ.symm (Additive.ofMul v))
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 : Ψ.symm (Additive.ofMul ((ι.symm (gen b) : MulAut S) v)) =
      lin 4 (blkOf i b) (Ψ.symm (Additive.ofMul v)) := by
    rw [LinearEquiv.symm_apply_eq, h1]
    rfl
  rw [h2, qEquiv_lin]

theorem blkOf_one {i : ℕ} (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9) (b : Bool) :
    blkOf i b = [1] := by
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem lin_one (s : Vec 1) : lin 1 [1] s = s := by
  funext j
  rw [lin_apply]
  fin_cases j
  simp [toVec]

theorem exists_n6Model [Finite S] {G : Subgroup (MulAut S)} (hS : ∀ s : S, s * s = 1)
    (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (hcard : Nat.card S ≤ 2 ^ 6) :
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
    norm_num at hcard

end B42Alt6

end CFSG.Quasithin
