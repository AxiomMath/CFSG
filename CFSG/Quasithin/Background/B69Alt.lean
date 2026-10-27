module

public import CFSG.Quasithin.Background.B69AltNorm
public import CFSG.Quasithin.Background.B69Done

public section

namespace CFSG.Quasithin

open CFSG.Open G6
open scoped commutatorElement

namespace B69

section Core

variable {n : ℕ}

theorem natKer_inf_eq_bot (hn : Odd n) :
    (Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
  obtain ⟨⟨j, hj⟩, hcore⟩ := hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hcoord : ∀ i : Fin n, Multiplicative.toAdd (x : PermMod n) i = (j : ZMod 2) := by
    intro i
    rw [← hj, toAdd_zpow]
    simp [allOnes]
  rcases zmod_two_cases (j : ZMod 2) with h0 | h1
  · apply Multiplicative.toAdd.injective
    funext i
    rw [hcoord i, h0]
    rfl
  · exfalso
    have hs : vsupp (x : PermMod n) = Finset.univ := by
      ext i
      simp [vsupp, hcoord i, h1]
    have := (mem_coreMod_iff_even _).1 hcore
    rw [hs, Finset.card_univ, Fintype.card_fin] at this
    exact (Nat.not_even_iff_odd.2 hn) this

end Core

section Equiv

variable {V : Type*} [CommGroup V]

theorem exists_core_equiv {n : ℕ} (hn : Odd n) {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : Equiv.Perm (Fin n) →* ↥H} (h : (FFModel.symDn n).RealizesVia H W ⊥ π) :
    ∃ e : ↥W ≃* ↥(coreMod n), ∀ (σ : Equiv.Perm (Fin n)) (u : ↥W)
      (hu : ((π σ : ↥H) : MulAut V) (u : V) ∈ W), e ⟨_, hu⟩ = coreAct n σ (e u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hker : ((FFModel.symDn n).ker).subgroupOf (FFModel.symDn n).sec = ⊥ := natKer_inf_eq_bot hn
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(FFModel.symDn n).sec ⧸ ((FFModel.symDn n).ker).subgroupOf (FFModel.symDn n).sec ≃*
      ↥(FFModel.symDn n).sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  let e : ↥W ≃* ↥(FFModel.symDn n).sec := (MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q
  have hqmk : ∀ m : ↥(FFModel.symDn n).sec, q (QuotientGroup.mk m) = m := fun m => rfl
  refine ⟨e, fun σ u hu => ?_⟩
  have h1 : β u = QuotientGroup.mk (e u) := by
    apply q.injective
    rw [hqmk]
    rfl
  have hm : (FFModel.symDn n).act σ ((e u : ↥(FFModel.symDn n).sec) : (FFModel.symDn n).Amb) ∈
      (FFModel.symDn n).sec := permAct_mem_coreMod σ (e u).2
  have h2 := hβe σ u (e u) hu hm h1
  have h4 : e ⟨_, hu⟩ = q (β ⟨_, hu⟩) := rfl
  have h5 := (congrArg q h2).trans (hqmk _)
  exact h4.trans (h5.trans rfl)

end Equiv

section Main

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem altBlock_of_ctx (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) (hctx : ShapeCtx X T M)
    (hO2 : pCoreOf 2 X = ⊥)
    (hact : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X →
      ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L)
    {A L A' : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hL : CFSG.Open.IsComponentOf L X)
    (hLA : ⁅L, A⁆ = L) (hAlt : AltShape M A L (commV L)) (hA' : IsFFStarMin X A')
    (hLA' : ⁅L, A'⁆ = L) : A' ≤ L ⊔ A := by
  classical
  obtain ⟨k, hk, π, hπs, hreal, hLeq, hAeq, hM⟩ := hAlt
  have hn : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  have hn5 : 5 ≤ 2 * k + 1 := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    subst hk1
    refine Group.IsPerfect.not_isMulCommutative ↥L
      (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
    rw [hLeq] at ha hb
    obtain ⟨σ₁, hσ₁, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨σ₂, hσ₂, rfl⟩ := Subgroup.mem_map.1 hb
    have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := by decide
    have := congrArg (fun x : alternatingGroup (Fin (2 * 1 + 1)) =>
        ((L ⊔ A).subtype.comp π) (x : Equiv.Perm (Fin (2 * 1 + 1))))
      (hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩)
    simpa using this
  set W : Subgroup V := commV L with hWdef
  have hW : W ∈ IrrPlus L (⊤ : Subgroup V) := commV_mem_irrPlus hV hctx hA hL hLA
  obtain ⟨e, he⟩ := exists_core_equiv hn hreal
  have hAW := a_stab_irr hV hA hL.2.2 hLA hW
  have hA'W := a_stab_irr hV hA' hL.2.2 hLA' hW
  have hLinv := (mem_irrPlus_top_iff.1 hW).1
  have hLst : L ≤ stabSub W := B1.le_stabSub_of_invariant hLinv
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hLAst : L ⊔ A ≤ stabSub W := sup_le hLst hAst
  have hLAB : L ⊔ A ≤ blk X L := sup_le le_blk_self (le_blk_of hA hLA)
  have hA'B : A' ≤ blk X L := le_blk_of hA' hLA'
  have hA'n : A' ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA'
  have hAn' : ∀ b ∈ A', ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hA'n hb hl
  intro a' ha'
  have ha'st : a' ∈ stabSub W := B1.le_stabSub_of_invariant hA'W ha'
  let rg : ↥W ≃* ↥W := resAut W ⟨a', ha'st⟩
  have hrg : ∀ w : ↥W, ((rg w : ↥W) : V) = a' (w : V) := fun w => rfl
  let ψ : MulAut ↥(coreMod (2 * k + 1)) := (e.symm.trans rg).trans e
  have hψapp : ∀ w : ↥W, ψ (e w) = e (rg w) := fun w => by
    show e (rg (e.symm (e w))) = _
    rw [e.symm_apply_apply]
  have hπst : ∀ σ : Equiv.Perm (Fin (2 * k + 1)), ∀ w : ↥W,
      ((π σ : ↥(L ⊔ A)) : MulAut V) (w : V) ∈ W := fun σ w =>
    ((hLAst (π σ).2) (w : V)).2 w.2
  have hψ : ∀ σ ∈ alternatingGroup (Fin (2 * k + 1)), ∃ τ ∈ alternatingGroup (Fin (2 * k + 1)),
      ∀ y : ↥(coreMod (2 * k + 1)), coreAct (2 * k + 1) σ (ψ y) = ψ (coreAct (2 * k + 1) τ y) := by
    intro σ hσ
    have h1 : ((π σ : ↥(L ⊔ A)) : MulAut V) ∈
        (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) :=
      Subgroup.mem_map.2 ⟨σ, hσ, rfl⟩
    have h1' : ((π σ : ↥(L ⊔ A)) : MulAut V) ∈ L := hLeq.ge h1
    have h2 : a'⁻¹ * ((π σ : ↥(L ⊔ A)) : MulAut V) * a' ∈ L := by
      have := hAn' a'⁻¹ (A'.inv_mem ha') _ h1'
      simpa using this
    have h2' := hLeq.le h2
    obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.1 h2'
    have hτeq' : ((π τ : ↥(L ⊔ A)) : MulAut V) =
        a'⁻¹ * ((π σ : ↥(L ⊔ A)) : MulAut V) * a' := hτeq
    refine ⟨τ, hτ, fun y => ?_⟩
    obtain ⟨u, rfl⟩ := e.surjective y
    have hval : ((π σ : ↥(L ⊔ A)) : MulAut V) (a' (u : V)) =
        a' (((π τ : ↥(L ⊔ A)) : MulAut V) (u : V)) := by
      rw [hτeq']
      simp [MulAut.mul_apply]
    have hu1 := hπst σ (rg u)
    have hu2 := hπst τ u
    have e1 : coreAct (2 * k + 1) σ (ψ (e u)) = e ⟨_, hu1⟩ := by
      rw [hψapp]
      exact (he σ (rg u) hu1).symm
    have e2 : ψ (coreAct (2 * k + 1) τ (e u)) = e (rg ⟨_, hu2⟩) := by
      rw [← he τ u hu2, hψapp]
    rw [e1, e2]
    refine congrArg e (Subtype.ext ?_)
    exact hval
  obtain ⟨ρ, hρ⟩ := exists_perm_of_normalizes hn hn5 ψ hψ
  have hy : ∀ w : ↥W, ((π ρ : ↥(L ⊔ A)) : MulAut V) (w : V) = a' (w : V) := by
    intro w
    have h1 := he ρ w (hπst ρ w)
    have h2 : e ⟨_, hπst ρ w⟩ = e (rg w) := by
      rw [h1, ← hρ, hψapp]
    exact congrArg Subtype.val (e.injective h2)
  set y : MulAut V := ((π ρ : ↥(L ⊔ A)) : MulAut V) with hydef
  have hyLA : y ∈ L ⊔ A := (π ρ).2
  have hgB : a' * y⁻¹ ∈ blk X L := (blk X L).mul_mem (hA'B ha') ((blk X L).inv_mem (hLAB hyLA))
  have hgX : a' * y⁻¹ ∈ X := blk_le_X hL hgB
  have hgW : ∀ w ∈ W, (a' * y⁻¹) w = w := by
    intro w hw
    have hw1 : y⁻¹ w ∈ W := ((hLAst ((L ⊔ A).inv_mem hyLA)) w).2 hw
    have h1 : y (y⁻¹ w) = a' (y⁻¹ w) := hy ⟨y⁻¹ w, hw1⟩
    have h2 : y (y⁻¹ w) = w := by simp
    show a' (y⁻¹ w) = w
    rw [← h1, h2]
  have hgU : ∀ u ∈ vSigma X, (a' * y⁻¹) u = u := by
    have hle : vSigma X ≤ MonoidHom.eqLocus (a' * y⁻¹).toMonoidHom (MonoidHom.id V) := by
      refine iSup₂_le fun L'' hL'' w hw => ?_
      by_cases hLL : L'' = L
      · subst hLL
        exact hgW w hw
      · exact blk_le_centSub hV hP4 hctx hL hL'' (hact L'' hL'') (Ne.symm hLL) hgB w hw
    exact fun u hu => hle hu
  have hgQ : ∀ v : V, (a' * y⁻¹) v * v⁻¹ ∈ vSigma X := fun v =>
    centQuot_mono (commV_le_vSigma hL) (blk_le_centQuot hV hctx hL (hact L hL) hgB) v
  have hg1 : a' * y⁻¹ = 1 := eq_one_of_stab hV hO2 (vSigma_invariant X) hgX hgU hgQ
  have : a' = y := by
    have := congrArg (fun z => z * y) hg1
    simpa using this
  rw [this]
  exact hyLA

theorem asB69AltBlock_of_component (hP4 : AsB15Part4) (hComp : AsB69Component) : AsB69AltBlock := by
  intro V _ _ hV X T M A L hCH W hW hAlt A' hA' hLA'
  obtain ⟨hsq, h, hO2, hFF, hns, hA, hL, hLA⟩ := hCH
  have hctx : ShapeCtx X T M := shapeCtx_of_component hComp hV hsq h hO2 hFF hns
  have hact := exists_active hV hP4 h hO2 hFF hns
  have hcomm : commV L = W :=
    (commV_eq_of_shape hV hA hL.2.2 hLA hW (hctx A L hA hL hLA W hW)).1
  refine altBlock_of_ctx hV hP4 hctx hO2 hact hA hL hLA ?_ hA' hLA'
  rw [hcomm]
  exact hAlt

theorem b69Struct_main (hP4 : AsB15Part4) (hComp : AsB69Component) (hG2 : AsB69GenByMin) :
    B69Struct :=
  b69Struct_of_inputs hP4 hComp (asB69AltBlock_of_component hP4 hComp) hG2

end Main

end B69

end CFSG.Quasithin
