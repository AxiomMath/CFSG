module

public import CFSG.Quasithin.MS93.S4AEA
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.MS93.S38EB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {V : Type*} [CommGroup V] {K : Type} [Field K] {H : Subgroup (MulAut V)}
  {I : Subgroup V} {π : ↥(StatedSL 3 K) →* ↥H}

theorem exists_coord (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia H I ⊥ π) :
    ∃ θ : ↥I ≃* Multiplicative (Fin 3 → K), ∀ (γ : ↥(StatedSL 3 K)) (v : ↥I)
      (hv : ((π γ : ↥H) : MulAut V) (v : V) ∈ I),
      Multiplicative.toAdd (θ ⟨_, hv⟩) =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβc⟩ := hR
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  obtain ⟨q, hq⟩ : ∃ q : ↥(FFModel.nat (StatedSL 3 K)).sec ⧸
      (FFModel.nat (StatedSL 3 K)).ker.subgroupOf (FFModel.nat (StatedSL 3 K)).sec ≃*
        Multiplicative (Fin 3 → K), ∀ m, q (QuotientGroup.mk m) = m.1 :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot).trans Subgroup.topEquiv, fun _ => rfl⟩
  refine ⟨(MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q, fun γ v hv => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β v)
  have h1 : β ⟨_, hv⟩ =
      QuotientGroup.mk ⟨(FFModel.nat (StatedSL 3 K)).act γ m.1, trivial⟩ :=
    hβc γ v m hv trivial hm.symm
  show Multiplicative.toAdd (q (β ⟨_, hv⟩)) = _ *ᵥ Multiplicative.toAdd (q (β v))
  rw [h1, ← hm, hq, hq]
  rfl

theorem charP_two_of_realizesVia (hsq : ∀ v : V, v ^ 2 = 1)
    (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia H I ⊥ π) : CharP K 2 := by
  obtain ⟨θ, -⟩ := exists_coord hR
  set v : ↥I := θ.symm (Multiplicative.ofAdd fun _ => (1 : K)) with hv
  have h1 : v ^ 2 = 1 := Subtype.ext (by simpa using hsq (v : V))
  have h2 := congrArg (fun w => Multiplicative.toAdd (θ w) 0) h1
  simp only [map_pow, hv, MulEquiv.apply_symm_apply, toAdd_pow, map_one, toAdd_one] at h2
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  rw [← one_add_one_eq_two]
  simpa [two_smul] using h2

@[expose] noncomputable def slHom (π : ↥(StatedSL 3 K) →* ↥H) : SL3 K →* MulAut V :=
  H.subtype.comp (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)

theorem slHom_apply (g : SL3 K) :
    slHom π g = ((π (specialLinearGroupEquivStatedSL 3 K g) : ↥H) : MulAut V) :=
  rfl

theorem card_fixV_inf_eq (θ : ↥I ≃* Multiplicative (Fin 3 → K))
    (hI : ∀ (g : SL3 K), ∀ v ∈ I, slHom π g v ∈ I)
    (hθ : ∀ (g : SL3 K) (v : ↥I), Multiplicative.toAdd (θ ⟨slHom π g v, hI g v v.2⟩) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v))
    (A : Subgroup (SL3 K)) :
    Nat.card ↥(fixV (A.map (slHom π)) ⊓ I) = Nat.card (fixN A) := by
  have hiff : ∀ v : ↥I, (v : V) ∈ fixV (A.map (slHom π)) ↔
      Multiplicative.toAdd (θ v) ∈ fixN A := by
    intro v
    rw [mem_fixV, mem_fixN]
    constructor
    · intro hv g hg
      rw [← hθ g v]
      congr 2
      exact Subtype.ext (hv _ ⟨g, hg, rfl⟩)
    · rintro hv _ ⟨g, hg, rfl⟩
      have h1 := hθ g v
      rw [hv g hg] at h1
      have h2 := congrArg Subtype.val
        (θ.injective (Multiplicative.toAdd.injective h1) : (⟨slHom π g v, hI g v v.2⟩ : ↥I) = v)
      exact h2
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (θ ⟨v, v.2.2⟩), (hiff _).mp v.2.1⟩
      invFun := fun u => ⟨θ.symm (Multiplicative.ofAdd u), (hiff _).mpr (by
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact u.2), (θ.symm (Multiplicative.ofAdd u)).2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }

theorem mem_commV_of_mem_commN (θ : ↥I ≃* Multiplicative (Fin 3 → K))
    (hI : ∀ (g : SL3 K), ∀ v ∈ I, slHom π g v ∈ I)
    (hθ : ∀ (g : SL3 K) (v : ↥I), Multiplicative.toAdd (θ ⟨slHom π g v, hI g v v.2⟩) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v))
    (A : Subgroup (SL3 K)) {w : Fin 3 → K} (hw : w ∈ commN A) :
    ((θ.symm (Multiplicative.ofAdd w) : ↥I) : V) ∈ commV (A.map (slHom π)) := by
  have hw' : w ∈ (commN A).toAddSubgroup := hw
  rw [commN_eq_closure] at hw'
  clear hw
  induction hw' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨g, hg, x, rfl⟩ := hy
    set u : ↥I := θ.symm (Multiplicative.ofAdd x) with hu
    have h1 : θ ⟨slHom π g u, hI g u u.2⟩ =
        Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) := by
      have := hθ g u
      rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
      rw [← this, ofAdd_toAdd]
    have h2 : θ.symm (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x - x)) =
        ⟨slHom π g u, hI g u u.2⟩ * u⁻¹ := by
      rw [ofAdd_sub, map_div, ← h1, MulEquiv.symm_apply_apply, div_eq_mul_inv]
    rw [h2]
    exact Subgroup.subset_closure ⟨slHom π g, ⟨g, hg, rfl⟩, u, rfl⟩
  | zero =>
    rw [ofAdd_zero, map_one]
    exact Subgroup.one_mem _
  | add x y _ _ hx hy =>
    rw [ofAdd_add, map_mul, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ hx hy
  | neg x _ hx =>
    rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hx

theorem coe_symm_injective (θ : ↥I ≃* Multiplicative (Fin 3 → K)) :
    Function.Injective fun w : Fin 3 → K => ((θ.symm (Multiplicative.ofAdd w) : ↥I) : V) :=
  fun _ _ h => Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h))

theorem card_commN_le (θ : ↥I ≃* Multiplicative (Fin 3 → K))
    (hI : ∀ (g : SL3 K), ∀ v ∈ I, slHom π g v ∈ I)
    (hθ : ∀ (g : SL3 K) (v : ↥I), Multiplicative.toAdd (θ ⟨slHom π g v, hI g v v.2⟩) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v))
    [Finite V] (A : Subgroup (SL3 K)) :
    Nat.card (commN A) ≤ Nat.card (commV (A.map (slHom π))) := by
  refine Nat.card_le_card_of_injective (fun w : ↥(commN A) =>
    (⟨_, mem_commV_of_mem_commN θ hI hθ A w.2⟩ : ↥(commV (A.map (slHom π))))) ?_
  intro w w' hww'
  have h1 : ((θ.symm (Multiplicative.ofAdd (w : Fin 3 → K)) : ↥I) : V) =
      ((θ.symm (Multiplicative.ofAdd (w' : Fin 3 → K)) : ↥I) : V) :=
    congrArg (fun x : ↥(commV (A.map (slHom π))) => (x : V)) hww'
  exact Subtype.ext (coe_symm_injective θ h1)

section Count

variable [Finite K] [CharP K 2]

theorem card_pow_three_le [Finite V] (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia H I ⊥ π)
    {E : Subgroup (MulAut V)} (hEH : E ≤ H) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = Nat.card K ^ 2) :
    Nat.card K ^ 3 ≤ (fixV E).index * Nat.card (commV E) := by
  obtain ⟨θ, hθ⟩ := exists_coord hR
  have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hR
  have hHI : ∀ x : ↥H, ∀ v ∈ I, (x : MulAut V) v ∈ I := hR.2.2.2.1
  have hI : ∀ (g : SL3 K), ∀ v ∈ I, slHom π g v ∈ I := fun g v hv => hHI _ v hv
  have hθ' : ∀ (g : SL3 K) (v : ↥I), Multiplicative.toAdd (θ ⟨slHom π g v, hI g v v.2⟩) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v) := fun g v =>
    hθ (specialLinearGroupEquivStatedSL 3 K g) v _
  have hψi : Function.Injective (slHom π) :=
    Subtype.val_injective.comp (hπi.comp (specialLinearGroupEquivStatedSL 3 K).injective)
  have hψr : E ≤ (slHom π).range := by
    intro x hx
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 K), π γ = ⟨x, hEH hx⟩ := hR.1 ⟨x, hEH hx⟩
    refine ⟨(specialLinearGroupEquivStatedSL 3 K).symm γ, ?_⟩
    rw [slHom_apply, MulEquiv.apply_symm_apply, hγ]
  set A := E.comap (slHom π)
  have hAE : A.map (slHom π) = E := Subgroup.map_comap_eq_self hψr
  have hcardA : Nat.card A = Nat.card K ^ 2 := by
    rw [← hcard, ← hAE, Subgroup.card_map_of_injective hψi]
  have hA2 : ∀ g ∈ A, g * g = 1 := fun g hg => hψi (by rw [map_mul, map_one]; exact hs _ hg)
  have hAc : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g := fun g hg g' hg' =>
    hψi (by rw [map_mul, map_mul]; exact hc _ hg _ hg')
  set c := Module.finrank K (fixN A)
  set d := Module.finrank K (commN A)
  have hdc : d ≤ c := finrank_commN_le_finrank_fixN_of_elemAb hA2 hAc
  have hc3 : c ≤ 3 := (Submodule.finrank_le _).trans (by simp)
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hbound := card_le_pow_finrank A
  rw [hcardA] at hbound
  have h2 : 2 ≤ (3 - c) * d := (Nat.pow_le_pow_iff_right hq1).mp hbound
  have hcd : c = d := by interval_cases c <;> omega
  have hIcard : Nat.card I = Nat.card K ^ 3 := by
    rw [Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_fin]
  have hfix : Nat.card ↥(fixV E ⊓ I) = Nat.card K ^ c := by
    rw [← hAE, card_fixV_inf_eq θ hI hθ' A, card_fixN]
  have hrel : (fixV E).relIndex I = Nat.card K ^ (3 - c) := by
    have hmul := Subgroup.relIndex_mul_card (fixV E) I
    rw [hfix, hIcard] at hmul
    have h3 : Nat.card K ^ (3 - c) * Nat.card K ^ c = Nat.card K ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) c) (hmul.trans h3.symm)
  have hidx : (fixV E).relIndex I ≤ (fixV E).index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  have hcomm : Nat.card K ^ d ≤ Nat.card (commV E) := by
    calc Nat.card K ^ d = Nat.card (commN A) := Module.natCard_eq_pow_finrank.symm
      _ ≤ Nat.card (commV (A.map (slHom π))) := card_commN_le θ hI hθ' A
      _ = Nat.card (commV E) := by rw [hAE]
  calc Nat.card K ^ 3 = Nat.card K ^ (3 - c) * Nat.card K ^ d := by
        rw [← pow_add]
        congr 1
        omega
    _ ≤ (fixV E).index * Nat.card (commV E) :=
        Nat.mul_le_mul (hrel ▸ hidx) hcomm

end Count

theorem card_mul_card_le {W : Type*} [CommGroup W] {I₀ I₁ Q : Subgroup W} [Finite Q]
    (hI : I₀ ⊓ I₁ = ⊥) {X₀ X₁ : Type*} {f₀ : X₀ → W} {f₁ : X₁ → W}
    (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    (h₀ : ∀ x, f₀ x ∈ I₀ ∧ f₀ x ∈ Q) (h₁ : ∀ x, f₁ x ∈ I₁ ∧ f₁ x ∈ Q) :
    Nat.card X₀ * Nat.card X₁ ≤ Nat.card Q := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨f₀ p.1 * f₁ p.2, Q.mul_mem (h₀ p.1).2 (h₁ p.2).2⟩ : ↥Q)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have e : f₀ a * f₁ b = f₀ a' * f₁ b' := congrArg Subtype.val hab
  have hm : f₀ a / f₀ a' ∈ I₀ ⊓ I₁ := by
    refine ⟨I₀.div_mem (h₀ a).1 (h₀ a').1, ?_⟩
    rw [div_eq_div_iff_mul_eq_mul.mpr (e.trans (mul_comm _ _))]
    exact I₁.div_mem (h₁ b').1 (h₁ b).1
  rw [hI, Subgroup.mem_bot, div_eq_one] at hm
  have hb : f₁ b = f₁ b' := by rw [hm] at e; exact mul_left_cancel e
  rw [hf₀ hm, hf₁ hb]

theorem slHom_mem (g : SL3 K) : slHom π g ∈ H := (π _).2

section SelfDual

variable [Finite K]

theorem natSummand_qLn (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia H I ⊥ π) :
    Nat.card I = Nat.card K ^ 3 ∧
      Nat.card ↥(fixV ((qLn : Subgroup (SL3 K)).map (slHom π)) ⊓ I) = Nat.card K ^ 2 ∧
      ∃ f : ↥(commN (qLn : Subgroup (SL3 K))) → V, Function.Injective f ∧
        ∀ w, f w ∈ I ∧ f w ∈ commV ((qLn : Subgroup (SL3 K)).map (slHom π)) := by
  obtain ⟨θ, hθ⟩ := exists_coord hR
  have hHI : ∀ x : ↥H, ∀ v ∈ I, (x : MulAut V) v ∈ I := hR.2.2.2.1
  have hI : ∀ (g : SL3 K), ∀ v ∈ I, slHom π g v ∈ I := fun g v hv => hHI _ v hv
  have hθ' : ∀ (g : SL3 K) (v : ↥I), Multiplicative.toAdd (θ ⟨slHom π g v, hI g v v.2⟩) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v) := fun g v =>
    hθ (specialLinearGroupEquivStatedSL 3 K g) v _
  refine ⟨?_, ?_, fun w => ((θ.symm (Multiplicative.ofAdd (w : Fin 3 → K)) : ↥I) : V),
    fun w w' h => Subtype.ext (coe_symm_injective θ h),
    fun w => ⟨(θ.symm _).2, mem_commV_of_mem_commN θ hI hθ' _ w.2⟩⟩
  · rw [Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_fin]
  · rw [card_fixV_inf_eq θ hI hθ' _, fixN_qLn, card_ln01]

theorem card_commV_mul_card_fixV_ne {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)}
    (hcase : (FFModel.nat (StatedSL 3 K)).Realizes H ⊤ ⊥ ∨
      DirectSumOfCopies H ⊤ ⊥ (FFModel.nat (StatedSL 3 K)) 2) :
    ∃ E : Subgroup (MulAut V), E ≤ H ∧ Nat.card (commV E) * Nat.card (fixV E) ≠ Nat.card V := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hcN : Nat.card (commN (qLn : Subgroup (SL3 K))) = Nat.card K ^ 2 := by
    rw [commN_qLn, card_ln01]
  rcases hcase with ⟨π, hπ⟩ | ⟨I, π, -, hdisj, hsup, hR⟩
  · refine ⟨(qLn : Subgroup (SL3 K)).map (slHom π), ?_, ?_⟩
    · rintro _ ⟨g, -, rfl⟩
      exact slHom_mem g
    obtain ⟨hV, hfix, f, hf, hfm⟩ := natSummand_qLn hπ
    rw [inf_top_eq] at hfix
    rw [Subgroup.card_top] at hV
    have hcomm : Nat.card K ^ 2 ≤ Nat.card (commV ((qLn : Subgroup (SL3 K)).map (slHom π))) := by
      rw [← hcN]
      exact Nat.card_le_card_of_injective (fun w => (⟨f w, (hfm w).2⟩ : ↥(commV _)))
        fun w w' h => hf (congrArg Subtype.val h)
    rw [hfix, hV]
    refine (Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ hcomm)).ne'
    rw [← pow_add]
    exact Nat.pow_lt_pow_right hq1 (by norm_num)
  · refine ⟨(qLn : Subgroup (SL3 K)).map (slHom π), ?_, ?_⟩
    · rintro _ ⟨g, -, rfl⟩
      exact slHom_mem g
    set E := (qLn : Subgroup (SL3 K)).map (slHom π)
    have hI01 : I 0 ⊓ I 1 = ⊥ := by
      have h1 : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
        le_sup_of_le_right (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
      exact eq_bot_iff.mpr ((inf_le_inf_left _ h1).trans (hdisj 0).le)
    have hsup' : I 0 ⊔ I 1 = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← hsup, bot_sup_eq]
      refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    obtain ⟨hV₀, hfix₀, f₀, hf₀, hfm₀⟩ := natSummand_qLn (hR 0)
    obtain ⟨hV₁, hfix₁, f₁, hf₁, hfm₁⟩ := natSummand_qLn (hR 1)
    have hV : Nat.card V ≤ Nat.card K ^ 6 := by
      have hs : Function.Surjective fun p : ↥(I 0) × ↥(I 1) => (p.1 : V) * p.2 := by
        intro v
        have hv : v ∈ I 0 ⊔ I 1 := by rw [hsup']; exact Subgroup.mem_top v
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
        exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
      calc Nat.card V ≤ Nat.card (↥(I 0) × ↥(I 1)) := Nat.card_le_card_of_surjective _ hs
        _ = Nat.card K ^ 6 := by rw [Nat.card_prod, hV₀, hV₁, ← pow_add]
    have hfix : Nat.card K ^ 4 ≤ Nat.card (fixV E) := by
      have := card_mul_card_le (Q := fixV E) hI01
        (f₀ := fun x : ↥(fixV E ⊓ I 0) => (x : V)) (f₁ := fun x : ↥(fixV E ⊓ I 1) => (x : V))
        Subtype.val_injective Subtype.val_injective (fun x => ⟨x.2.2, x.2.1⟩)
        (fun x => ⟨x.2.2, x.2.1⟩)
      rwa [hfix₀, hfix₁, ← pow_add] at this
    have hcomm : Nat.card K ^ 4 ≤ Nat.card (commV E) := by
      have := card_mul_card_le (Q := commV E) hI01 hf₀ hf₁ hfm₀ hfm₁
      rwa [hcN, ← pow_add] at this
    refine (Nat.lt_of_le_of_lt hV ?_).ne'
    calc Nat.card K ^ 6 < Nat.card K ^ (4 + 4) := Nat.pow_lt_pow_right hq1 (by norm_num)
      _ = Nat.card K ^ 4 * Nat.card K ^ 4 := pow_add _ _ _
      _ ≤ Nat.card (commV E) * Nat.card (fixV E) := Nat.mul_le_mul hcomm hfix

end SelfDual

end CFSG.Quasithin.MS93.S38EB
