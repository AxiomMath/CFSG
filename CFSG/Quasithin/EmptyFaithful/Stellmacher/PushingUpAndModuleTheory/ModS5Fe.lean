module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Min
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5CF

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

@[expose] def Model.isoRestrictTop (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (h : U = ⊤) : M.Iso (M.restrict U hU) where
  toMulEquiv :=
    { toFun := fun x => ⟨x, by rw [h]; trivial⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  map_act _ _ := rfl

theorem mul_self_eq_one_of_idx_two (M : Model n) {t : Perm (Fin n)}
    (hinj : Function.Injective M.act) (h : idx M t = 2) : t * t = 1 := by
  set ψ : MulAut M.W := M.act t with hψ
  have hcard : Nat.card (delHom ψ).range = 2 := by
    rw [← commW_top_zpowers_eq_range, ← bf1]
    exact h
  obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : (delHom ψ).range)).mp hcard
  have key : ∀ w, delHom ψ (delHom ψ w) = 1 := by
    intro w
    by_cases ha : delHom ψ w = 1
    · rw [ha, map_one]
    by_cases hb : delHom ψ (delHom ψ w) = 1
    · exact hb
    exfalso
    have ha' : (⟨delHom ψ w, w, rfl⟩ : (delHom ψ).range) = u :=
      huniq _ (fun h1 => ha (congrArg Subtype.val h1))
    have hb' : (⟨delHom ψ (delHom ψ w), delHom ψ w, rfl⟩ : (delHom ψ).range) = u :=
      huniq _ (fun h1 => hb (congrArg Subtype.val h1))
    have hab : delHom ψ (delHom ψ w) = delHom ψ w :=
      congrArg Subtype.val (hb'.trans ha'.symm)
    rw [delHom_apply, mul_inv_eq_iff_eq_mul] at hab
    have h1 : ψ (delHom ψ w) = 1 := by rw [hab, M.sq]
    have h2 : delHom ψ w = 1 := by
      have : ψ (delHom ψ w) = ψ 1 := by rw [h1, map_one]
      exact ψ.injective this
    exact ha h2
  have h2 : M.act (t * t) = M.act 1 := by
    ext w
    have := key w
    rw [delHom_delHom M.sq, delHom_apply, mul_inv_eq_one] at this
    rw [map_mul]
    simpa using this
  exact hinj h2

private theorem idx_quot_eq_one {M : Model 5} {N : Subgroup M.W} (hN : IsInvSub M ⊤ N)
    {t : Perm (Fin 5)} (hR : idx (M.restrict N hN) t = 2) (hM : idx M t ≤ 2) :
    idx (M.quot N hN) t = 1 := by
  have h := idx_restrict_mul_idx_quot_le M N hN t
  have hpos : 0 < idx (M.quot N hN) t := Nat.pos_of_ne_zero (by
    rw [idx_quot]; exact Subgroup.FiniteIndex.index_ne_zero)
  rw [hR] at h
  omega

theorem fixW_quot_alt5_eq_bot (M : Model 5)
    (hK : IsInvSub M ⊤ (fixW M (alternatingGroup (Fin 5)))) :
    fixW (M.quot _ hK) (alternatingGroup (Fin 5)) = ⊥ := by
  rw [fixW_quot, ml0_fixQ_fixW alt5_le_closure_odd, eq_bot_iff, Subgroup.map_le_iff_le_comap,
    MonoidHom.comap_bot, M.ker_projQuot]

theorem hss_1_5 (M : Model 5) (hf : M.Faithful) {t : Perm (Fin 5)} (ht1 : t ≠ 1)
    (h2 : idx M t = 2) :
    t.IsSwap ∧ fixW M ⊤ = fixW M (alternatingGroup (Fin 5)) ∧
      Nonempty ((M.quot (fixW M (alternatingGroup (Fin 5)))
        (isInvSub_fixW_of_normal M (alternatingGroup.normal (α := Fin 5)))).Iso orth) := by
  set A := alternatingGroup (Fin 5) with hAdef
  have hK : IsInvSub M ⊤ (fixW M A) := isInvSub_fixW_of_normal M alternatingGroup.normal
  have hA : fixW M A ≠ ⊤ := fixW_alt5_ne_top_of_faithful hf
  have htt : t * t = 1 := mul_self_eq_one_of_idx_two M hf h2
  have hsw : t.IsSwap := by
    rw [isSwap_iff]
    refine ⟨ht1, by rw [pow_two]; exact htt, fun hs => ?_⟩
    have htA : t ∈ A := Perm.mem_alternatingGroup.mpr hs
    have := cf M hA htA ht1
    unfold cfm at this
    split_ifs at this <;> omega
  have hsq2 : idx orth t = 2 := ((transvections t ht1).2).mpr hsw
  have hge4 : 4 ≤ idx nat t := (transvections t ht1).1
  set M₁ := M.quot _ hK with hM₁
  have hM₁A : fixW M₁ A = ⊥ := fixW_quot_alt5_eq_bot M hK
  have hnt₁ : ∃ w : M₁.W, w ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hA
    rw [eq_top_iff]
    intro x _
    have : M.projQuot _ hK x = 1 := hall _
    have h3 : x ∈ (M.projQuot _ hK).ker := this
    rwa [M.ker_projQuot] at h3
  obtain ⟨N, hN, hNbot, hirr⟩ := exists_minimal_inv M₁ hnt₁
  have hmoved : ∃ σ w, (M₁.restrict N hN).act σ w ≠ w := by
    by_contra hall
    push Not at hall
    apply hNbot
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hfix : u ∈ fixW M₁ A := by
      intro b _
      exact congrArg Subtype.val (hall b ⟨u, hu⟩)
    rw [hM₁A, Subgroup.mem_bot] at hfix
    exact hfix
  have hM1le : idx M₁ t ≤ 2 := h2 ▸ idx_quot_le M _ hK t
  rcases model5_irred_classification _ hirr hmoved with horth | hnat
  swap
  · exfalso
    obtain ⟨e⟩ := hnat
    have h1 := idx_restrict_le M₁ N hN t
    rw [← e.idx_eq] at h1
    omega
  ·
    obtain ⟨e⟩ := horth
    have hR : idx (M₁.restrict N hN) t = 2 := by rw [← e.idx_eq]; exact hsq2
    have hq1 := idx_quot_eq_one hN hR hM1le
    have hfix1 : fixW (M₁.quot N hN) (Subgroup.zpowers t) = ⊤ := by
      rw [← Subgroup.index_eq_one]; exact hq1
    have hfix2 := fixW_top_of_swap _ hsw hfix1
    have hcomm : commW M₁ A ⊤ ≤ N := by
      unfold commW
      rw [Subgroup.closure_le]
      rintro _ ⟨b, hb, u, -, rfl⟩
      have : M₁.projQuot N hN u ∈ fixW (M₁.quot N hN) ⊤ := by rw [hfix2]; trivial
      exact (M₁.projQuot_mem_fixW_iff N hN _ u).mp this b (Subgroup.mem_top b)
    have hNtop := c27b_eq_top M₁ hN e hcomm hM₁A
    have hiso : M₁.Iso orth := (M₁.isoRestrictTop N hN hNtop).trans e
    have hid : idx M₁ t = 2 := by rw [← hiso.idx_eq]; exact hsq2
    have hfq : fixW M (Subgroup.zpowers t) ≤ fixQ M (Subgroup.zpowers t) (fixW M A) :=
      fixW_le_fixQ _ _
    have hrel : (fixW M (Subgroup.zpowers t)).relIndex
        (fixQ M (Subgroup.zpowers t) (fixW M A)) = 1 := by
      have h3 := Subgroup.relIndex_mul_index hfq
      rw [← idx_quot M _ hK t] at h3
      have hid' : idx M₁ t = 2 := hid
      unfold idx at h2
      rw [h2, hid'] at h3
      omega
    have hKt : fixW M A ≤ fixW M (Subgroup.zpowers t) := by
      refine le_trans (le_fixQ (B := Subgroup.zpowers t)
        (fun b _ u hu => hK b (Subgroup.mem_top b) u hu)) ?_
      exact Subgroup.relIndex_eq_one.mp hrel
    have hKG : fixW M A ≤ fixW M ⊤ := by
      intro w hw σ _
      have hwt : M.act t w = w := (mem_fixW_zpowers M).mp (hKt hw)
      by_cases hs : Perm.sign σ = 1
      · exact hw σ (Perm.mem_alternatingGroup.mpr hs)
      · have hsg : Perm.sign t = -1 :=
          (Int.units_eq_one_or _).resolve_left ((isSwap_iff t).mp hsw).2.2
        have hsσ : Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left hs
        have hst : σ * t ∈ A := by
          rw [Perm.mem_alternatingGroup, map_mul, hsg, hsσ]
          decide
        have : σ = (σ * t) * t := by rw [mul_assoc, htt, mul_one]
        rw [this, act_mul_apply, hwt]
        exact hw _ hst
    exact ⟨hsw, le_antisymm (fixW_antitone M (le_top : A ≤ ⊤)) hKG, ⟨hiso⟩⟩

theorem hss_1_5_top (M : Model 5) (hf : M.Faithful) {t : Perm (Fin 5)} (ht1 : t ≠ 1)
    (h2 : idx M t = 2) :
    t.IsSwap ∧ Nonempty ((M.quot (fixW M ⊤)
      (isInvSub_fixW_of_normal M (Subgroup.normal_top : (⊤ : Subgroup (Perm (Fin 5))).Normal))).Iso
        orth) := by
  obtain ⟨hsw, heq, ⟨e⟩⟩ := hss_1_5 M hf ht1 h2
  exact ⟨hsw, ⟨(M.quotCongr heq _ _).trans e⟩⟩

end CFSG.Quasithin.F53Mod
