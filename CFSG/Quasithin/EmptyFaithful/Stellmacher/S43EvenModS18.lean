module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Fe
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Quasithin.F53Mod Equiv

namespace EvenMod

variable {n : ℕ}

theorem idx_one (W : Model n) : idx W 1 = 1 := by
  unfold idx
  rw [Subgroup.index_eq_one, eq_top_iff]
  intro w _
  rw [mem_fixW_zpowers, map_one]
  rfl

theorem card_sup_le_mul {A : Type*} [CommGroup A] [Finite A] (U V : Subgroup A) :
    Nat.card ↥(U ⊔ V) ≤ Nat.card U * Nat.card V := by
  have h1 := Subgroup.relIndex_mul_card U (U ⊔ V)
  rw [inf_eq_left.mpr le_sup_left, Subgroup.relIndex_sup_left] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _))

@[expose] def restrictCongr (W : Model n) {U V : Subgroup W.W} (h : U = V)
    (hU : IsInvSub W ⊤ U) (hV : IsInvSub W ⊤ V) : (W.restrict U hU).Iso (W.restrict V hV) where
  toMulEquiv := MulEquiv.subgroupCongr h
  map_act _ _ := rfl

@[expose] def restrictIncl (W : Model n) (U : Subgroup W.W) (hU : IsInvSub W ⊤ U) :
    (W.restrict U hU).W →* W.W := U.subtype

theorem restrictIncl_act (W : Model n) (U : Subgroup W.W) (hU : IsInvSub W ⊤ U)
    (σ : Perm (Fin n)) (u : (W.restrict U hU).W) :
    restrictIncl W U hU ((W.restrict U hU).act σ u) = W.act σ (restrictIncl W U hU u) := rfl

theorem restrictIncl_injective (W : Model n) (U : Subgroup W.W) (hU : IsInvSub W ⊤ U) :
    Function.Injective (restrictIncl W U hU) := Subtype.val_injective

theorem restrictIncl_mem (W : Model n) (U : Subgroup W.W) (hU : IsInvSub W ⊤ U)
    (u : (W.restrict U hU).W) : restrictIncl W U hU u ∈ U := u.2

end EvenMod

theorem isInvSub_commW_top (W : Model 5) : IsInvSub W ⊤ (commW W ⊤ ⊤) :=
  isInvSub_top_commW_of_normal W Subgroup.normal_top (isInvSub_top W)

theorem isInvSub_commW_alt (W : Model 5) :
    IsInvSub W ⊤ (commW W (alternatingGroup (Fin 5)) ⊤) :=
  isInvSub_top_commW_of_normal W alternatingGroup.normal (isInvSub_top W)

theorem isInvSub_fixW_top (W : Model 5) : IsInvSub W ⊤ (fixW W ⊤) :=
  isInvSub_fixW_of_normal W Subgroup.normal_top

namespace EvenMod

theorem card_commW_top_le (W : Model 5) {t : Perm (Fin 5)} (ht : t.IsSwap) :
    Nat.card (commW W ⊤ ⊤) ≤ idx W t ^ 4 := by
  set Γ : Set (Perm (Fin 5)) := {swap 0 1, swap 1 2, swap 2 3, swap 3 4} with hΓ
  have hcl : Subgroup.closure Γ = ⊤ :=
    eq_top_of_path_swaps (Subgroup.subset_closure (by simp [hΓ]))
      (Subgroup.subset_closure (by simp [hΓ])) (Subgroup.subset_closure (by simp [hΓ]))
      (Subgroup.subset_closure (by simp [hΓ]))
  have h5 := bf5 (M := W) Γ (U := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [hcl] at h5
  obtain ⟨a, b, hab, rfl⟩ := ht
  have hsw : ∀ c d : Fin 5, c ≠ d →
      Nat.card (commW W (Subgroup.zpowers (swap c d)) ⊤) = idx W (swap a b) := by
    intro c d hcd
    obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_swap hab hcd)
    rw [← bf1, ← hg]
    exact idx_conj W g _
  rw [h5]
  simp only [hΓ, iSup_insert, iSup_singleton]
  refine (card_sup_le_mul _ _).trans ?_
  refine (Nat.mul_le_mul_left _ ((card_sup_le_mul _ _).trans
    (Nat.mul_le_mul_left _ (card_sup_le_mul _ _)))).trans (le_of_eq ?_)
  rw [hsw 0 1 (by decide), hsw 1 2 (by decide), hsw 2 3 (by decide), hsw 3 4 (by decide)]
  ring

theorem sup_eq_top_of_iso_orth (W : Model 5) {C : Subgroup W.W} (hC : IsInvSub W ⊤ C)
    (e : (W.quot C hC).Iso orth) {U : Subgroup W.W} (hU : IsInvSub W ⊤ U) (hUC : ¬ U ≤ C) :
    U ⊔ C = ⊤ := by
  set π := W.projQuot C hC with hπ
  set Y : Subgroup orth.W := (U.map π).map e.toMulEquiv.toMonoidHom with hY
  have hYinv : ∀ σ : Perm (Fin 5), ∀ y ∈ Y, orth.act σ y ∈ Y := by
    rintro σ _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨π (W.act σ u), ⟨W.act σ u, hU σ (Subgroup.mem_top σ) u hu, rfl⟩, ?_⟩
    show e.toMulEquiv (π (W.act σ u)) = orth.act σ (e.toMulEquiv (π u))
    rw [← e.map_act, hπ, Model.projQuot_act]
  rcases irreducible_orth Y hYinv with h | h
  · refine absurd (fun u hu => ?_) hUC
    have h1 : e.toMulEquiv (π u) ∈ Y := ⟨π u, ⟨u, hu, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
    rw [← W.ker_projQuot C hC]
    exact h1
  · rw [eq_top_iff]
    intro w _
    have h1 : e.toMulEquiv (π w) ∈ Y := by rw [h]; trivial
    obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := h1
    have h2 : π u = π w := e.toMulEquiv.injective hue
    rw [hπ, Model.projQuot_eq_iff] at h2
    have e2 : w = u * (u⁻¹ * w) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hu h2

theorem not_commW_le_of_iso_orth (W : Model 5) {C : Subgroup W.W} (hC : IsInvSub W ⊤ C)
    (e : (W.quot C hC).Iso orth) {B : Subgroup (Perm (Fin 5))}
    (hB : alternatingGroup (Fin 5) ≤ B) : ¬ commW W B ⊤ ≤ C := by
  intro hle
  have hfix : fixW (W.quot C hC) B = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, rfl⟩ := W.projQuot_surjective C hC x
    rw [W.projQuot_mem_fixW_iff, mem_fixQ]
    intro b hb
    exact hle (Subgroup.subset_closure ⟨b, hb, w, Subgroup.mem_top w, rfl⟩)
  have h2 : fixW orth B = ⊤ := (e.fixW_eq_top_iff B).mpr hfix
  have h3 : fixW orth (alternatingGroup (Fin 5)) = ⊤ :=
    eq_top_iff.mpr (h2 ▸ fixW_antitone orth hB)
  rw [fixW_orth_alt5] at h3
  have h4 := card_orth
  rw [← Subgroup.card_top (G := orth.W), ← h3, Subgroup.card_bot] at h4
  omega

theorem index_eq_sixteen_of_iso (W : Model 5) {C : Subgroup W.W} (hC : IsInvSub W ⊤ C)
    (e : (W.quot C hC).Iso orth) : C.index = 16 := by
  rw [Subgroup.index, ← card_orth]
  exact Nat.card_congr e.toMulEquiv.toEquiv

theorem relIndex_eq_sixteen_of_iso (W : Model 5) {C : Subgroup W.W} (hC : IsInvSub W ⊤ C)
    (e : (W.quot C hC).Iso orth) {U : Subgroup W.W} (hU : IsInvSub W ⊤ U) (hUC : ¬ U ≤ C) :
    C.relIndex U = 16 := by
  have h := Subgroup.relIndex_sup_left U C
  rw [sup_comm, sup_eq_top_of_iso_orth W hC e hU hUC, Subgroup.relIndex_top_right,
    index_eq_sixteen_of_iso W hC e] at h
  exact h.symm

end EvenMod

theorem S18_model (W : Model 5) (hf : W.Faithful) {t : Perm (Fin 5)} (ht : idx W t = 2) :
    t.IsSwap ∧ fixW W ⊤ = fixW W (alternatingGroup (Fin 5)) ∧
      commW W ⊤ ⊤ = commW W (alternatingGroup (Fin 5)) ⊤ ∧
      IsCompl (fixW W ⊤) (commW W ⊤ ⊤) ∧ (fixW W ⊤).index = 16 ∧
      Nat.card (commW W ⊤ ⊤) = 16 ∧
      Nonempty ((W.restrict (commW W ⊤ ⊤) (isInvSub_commW_top W)).Iso orth) := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [EvenMod.idx_one] at ht
    omega
  obtain ⟨hsw, hCA, ⟨e⟩⟩ := hss_1_5 W hf ht1 ht
  set A := alternatingGroup (Fin 5) with hA
  set C := fixW W ⊤ with hCdef
  set F := commW W ⊤ ⊤ with hFdef
  have hCinv : IsInvSub W ⊤ C := isInvSub_fixW_top W
  have e' : (W.quot C hCinv).Iso orth := (W.quotCongr hCA _ _).trans e
  have hFinv : IsInvSub W ⊤ F := isInvSub_commW_top W
  have hFC : ¬ F ≤ C := EvenMod.not_commW_le_of_iso_orth W hCinv e' le_top
  have hsup : F ⊔ C = ⊤ := EvenMod.sup_eq_top_of_iso_orth W hCinv e' hFinv hFC
  have hle : Nat.card F ≤ 16 := (EvenMod.card_commW_top_le W hsw).trans (by rw [ht]; norm_num)
  have hmul := Subgroup.relIndex_mul_card C F
  rw [EvenMod.relIndex_eq_sixteen_of_iso W hCinv e' hFinv hFC] at hmul
  have hinf : C ⊓ F = ⊥ := Subgroup.eq_bot_of_card_le _ (by omega)
  have hcardF : Nat.card F = 16 := by rw [← hmul, hinf, Subgroup.card_bot, mul_one]
  have hFA : F = commW W A ⊤ := by
    have hle' : commW W A ⊤ ≤ F := commW_mono_left W le_top ⊤
    have hAC : ¬ commW W A ⊤ ≤ C := EvenMod.not_commW_le_of_iso_orth W hCinv e' le_rfl
    have hmulA := Subgroup.relIndex_mul_card C (commW W A ⊤)
    rw [EvenMod.relIndex_eq_sixteen_of_iso W hCinv e' (isInvSub_commW_alt W) hAC] at hmulA
    have hpos : 0 < Nat.card ↥(C ⊓ commW W A ⊤) := Nat.card_pos
    exact (Subgroup.eq_of_le_of_card_ge hle' (by omega)).symm
  have hiso : Nonempty ((W.restrict F hFinv).Iso orth) := by
    set ι := EvenMod.restrictIncl W F hFinv with hι
    let f : (W.restrict F hFinv).W →* orth.W :=
      e'.toMulEquiv.toMonoidHom.comp ((W.projQuot C hCinv).comp ι)
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have h1 : W.projQuot C hCinv (ι u) = 1 :=
        (MulEquiv.map_eq_one_iff e'.toMulEquiv).mp hu
      have h2 : ι u ∈ C ⊓ F := ⟨by rw [← W.ker_projQuot C hCinv]; exact h1,
        EvenMod.restrictIncl_mem W F hFinv u⟩
      rw [hinf, Subgroup.mem_bot] at h2
      exact EvenMod.restrictIncl_injective W F hFinv (h2.trans (map_one ι).symm)
    have hcardR : Nat.card (W.restrict F hFinv).W = 16 := hcardF
    have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by
      rw [card_orth, hcardR])
    refine ⟨⟨MulEquiv.ofBijective f hfbij, fun σ u => ?_⟩⟩
    show e'.toMulEquiv (W.projQuot C hCinv (ι ((W.restrict F hFinv).act σ u))) =
      orth.act σ (e'.toMulEquiv (W.projQuot C hCinv (ι u)))
    rw [hι, EvenMod.restrictIncl_act, ← e'.map_act, Model.projQuot_act]
  refine ⟨hsw, hCA, hFA, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr (by rw [sup_comm, hsup])⟩,
    EvenMod.index_eq_sixteen_of_iso W hCinv e', hcardF, hiso⟩

theorem EvenMod.faithful_of_fixW_alt_ne_top (W : Model 5)
    (h : fixW W (alternatingGroup (Fin 5)) ≠ ⊤) : W.Faithful := by
  rw [Model.Faithful, ← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  refine h (eq_top_iff.mpr fun w _ => mem_fixW.mpr fun b hb => ?_)
  have hb' : b ∈ W.act.ker := F53.normal_ge_alt5 W.act.ker hne hb
  rw [MonoidHom.mem_ker] at hb'
  rw [hb']
  rfl

theorem S11_model (W : Model 5) {t : Perm (Fin 5)} (ht1 : t ≠ 1) (ht : idx W t ≤ 2) :
    IsCompl (fixW W (alternatingGroup (Fin 5))) (commW W (alternatingGroup (Fin 5)) ⊤) ∧
      (commW W (alternatingGroup (Fin 5)) ⊤ = ⊥ ∨
        (W.Faithful ∧ t.IsSwap ∧ idx W t = 2 ∧ fixW W ⊤ = fixW W (alternatingGroup (Fin 5)) ∧
          commW W ⊤ ⊤ = commW W (alternatingGroup (Fin 5)) ⊤ ∧
          Nonempty ((W.restrict (commW W (alternatingGroup (Fin 5)) ⊤)
            (isInvSub_commW_alt W)).Iso orth))) := by
  set A := alternatingGroup (Fin 5) with hA
  by_cases htriv : fixW W A = ⊤
  · have hc : commW W A ⊤ = ⊥ := by
      unfold commW
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨b, hb, u, -, rfl⟩
      have hu : u ∈ fixW W A := htriv ▸ Subgroup.mem_top u
      rw [Set.mem_singleton_iff, (mem_fixW.mp hu) b hb, mul_inv_cancel]
    refine ⟨?_, Or.inl hc⟩
    rw [htriv, hc]
    exact isCompl_top_bot
  · have hf : W.Faithful := EvenMod.faithful_of_fixW_alt_ne_top W htriv
    have h2 : idx W t = 2 := by
      have hne1 : idx W t ≠ 1 := by
        intro h1
        unfold idx at h1
        rw [Subgroup.index_eq_one] at h1
        refine ht1 (hf ?_)
        rw [map_one]
        exact MulEquiv.ext fun w => (mem_fixW_zpowers W).mp (h1 ▸ Subgroup.mem_top w)
      have hpos : 0 < idx W t := Nat.pos_of_ne_zero (by
        unfold idx
        exact Subgroup.index_ne_zero_of_finite)
      omega
    obtain ⟨hsw, hCA, hFA, hcompl, -, -, ⟨eF⟩⟩ := S18_model W hf h2
    refine ⟨?_, Or.inr ⟨hf, hsw, h2, hCA, hFA,
      ⟨(EvenMod.restrictCongr W hFA.symm _ _).trans eF⟩⟩⟩
    rw [← hCA, ← hFA]
    exact hcompl

end CFSG.Quasithin.F53.Stellmacher.S43.Even
