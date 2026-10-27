module

public import CFSG.Quasithin.Background.ShultG53CoverHx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

theorem add_self_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem ρ_apply_ne_zero {X : Type} [Group X] (W : Md X) (g : X) {v : W.carrier} (hv : v ≠ 0) :
    W.ρ g v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (W.ρ g⁻¹) h
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at this
  exact this

theorem five_le_card {M : Type} [Finite M] (a₀ a₁ a₂ a₃ a₄ : M) (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂)
    (h03 : a₀ ≠ a₃) (h04 : a₀ ≠ a₄) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄) : 5 ≤ Nat.card M := by
  classical
  haveI := Fintype.ofFinite M
  have hnd : [a₀, a₁, a₂, a₃, a₄].Nodup := by
    simp [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have := hnd.length_le_card
  rw [Nat.card_eq_fintype_card]
  simpa using this

theorem sum_zero_of_card_four {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (K : AddSubgroup M) (hK : Nat.card K = 4) (a b c : M) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a + b + c = 0 := by
  by_contra hne
  have hc' : c ≠ a + b := by
    intro h
    apply hne
    rw [h, add_self_zmod2]
  have hs0 : (0 : M) ≠ a + b := by
    intro h
    apply hab
    have h2 : a + b = 0 := h.symm
    have h3 : a + b + b = b := by rw [h2, zero_add]
    rwa [add_assoc, add_self_zmod2, add_zero] at h3
  have hsa : a ≠ a + b := by
    intro h
    apply hb0
    have : a + 0 = a + b := by rw [add_zero]; exact h
    exact (add_left_cancel this).symm
  have hsb : b ≠ a + b := by
    intro h
    apply ha0
    have : 0 + b = a + b := by rw [zero_add]; exact h
    exact (add_right_cancel this).symm
  have h5 := five_le_card (M := K) ⟨0, K.zero_mem⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨a + b, K.add_mem ha hb⟩
    (fun h => ha0 (congrArg Subtype.val h).symm) (fun h => hb0 (congrArg Subtype.val h).symm)
    (fun h => hc0 (congrArg Subtype.val h).symm) (fun h => hs0 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => hac (congrArg Subtype.val h))
    (fun h => hsa (congrArg Subtype.val h)) (fun h => hbc (congrArg Subtype.val h))
    (fun h => hsb (congrArg Subtype.val h)) (fun h => hc' (congrArg Subtype.val h))
  omega

theorem card_closure_le_two {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    {S : Set M} (a : M) (hS : ∀ x ∈ S, x = a) : Nat.card (AddSubgroup.closure S) ≤ 2 := by
  classical
  have key : ∀ x ∈ AddSubgroup.closure S, x = 0 ∨ x = a := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact Or.inr (hS x hx)
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl (add_zero _)
      · exact Or.inr (zero_add _)
      · exact Or.inr (add_zero _)
      · exact Or.inl (add_self_zmod2 _)
    | neg x _ hx =>
      rcases hx with rfl | rfl
      · exact Or.inl neg_zero
      · exact Or.inr (neg_eq_of_add_eq_zero_right (add_self_zmod2 _))
  let f : AddSubgroup.closure S → Fin 2 := fun x => if x.1 = 0 then 0 else 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : (if x.1 = 0 then (0 : Fin 2) else 1) = if y.1 = 0 then 0 else 1 := hxy
    by_cases hx : x.1 = 0 <;> by_cases hy : y.1 = 0
    · rw [hx, hy]
    · rw [if_pos hx, if_neg hy] at hxy'
      exact absurd hxy' (by decide)
    · rw [if_neg hx, if_pos hy] at hxy'
      exact absurd hxy' (by decide)
    · rcases key x.1 x.2 with h | h
      · exact absurd h hx
      · rcases key y.1 y.2 with h' | h'
        · exact absurd h' hy
        · rw [h, h']
  have := Nat.card_le_card_of_injective f hf
  simpa using this


theorem ρk_h0E_x0 (k : Fin 2) : ρk k (h0E k) (x0 k) = y2 k := by
  rw [ρk_apply]
  exact (h0_cycle k).1

theorem ρk_h0E_y2 (k : Fin 2) : ρk k (h0E k) (y2 k) = y3 k := by
  rw [ρk_apply]
  exact (h0_cycle k).2.1

theorem ρk_h0E_y3 (k : Fin 2) : ρk k (h0E k) (y3 k) = x0 k := by
  rw [ρk_apply]
  exact (h0_cycle k).2.2

theorem one_mem_Hl (k : Fin 2) : (1 : ↥(alternatingGroup (Fin 6))) ∈ Hl k := fun y hy => by
  rw [map_one, Module.End.one_apply]
  exact hy

theorem mul_mem_Hl {k : Fin 2} {g g' : ↥(alternatingGroup (Fin 6))} (hg : g ∈ Hl k)
    (hg' : g' ∈ Hl k) : g * g' ∈ Hl k := fun y hy => by
  rw [map_mul, Module.End.mul_apply]
  exact hg _ (hg' y hy)

theorem h0E_mem_Hl (k : Fin 2) : h0E k ∈ Hl k := fun y hy => by
  rw [ρk_apply]
  exact h0_line k y hy

theorem x0_ne_zero (k : Fin 2) : x0 k ≠ 0 := (points_aux k).1

theorem ρk_ne_zero (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) {v : V4} (hv : v ≠ 0) :
    ρk k g v ≠ 0 :=
  ρ_apply_ne_zero (Mk k) g hv

open Classical in
@[expose] noncomputable def wf (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier)
    (y : V4) : W.carrier :=
  if h : ∃ g : ↥(alternatingGroup (Fin 6)), ρk k g (x0 k) = y then W.ρ h.choose w else 0

section Frobenius

variable {k : Fin 2} {W : Md ↥(alternatingGroup (Fin 6))} {w : W.carrier}

theorem wf_ρ (hHx : ∀ h ∈ Hx k, W.ρ h w = w) (g : ↥(alternatingGroup (Fin 6))) :
    wf k W w (ρk k g (x0 k)) = W.ρ g w := by
  have h : ∃ g' : ↥(alternatingGroup (Fin 6)), ρk k g' (x0 k) = ρk k g (x0 k) := ⟨g, rfl⟩
  unfold wf
  rw [dif_pos h]
  have hc := h.choose_spec
  have hmem : g⁻¹ * h.choose ∈ Hx k := by
    show ρk k (g⁻¹ * h.choose) (x0 k) = x0 k
    rw [map_mul, Module.End.mul_apply, hc, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  calc W.ρ h.choose w = W.ρ g (W.ρ (g⁻¹ * h.choose) w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = W.ρ g w := by rw [hHx _ hmem]

theorem wf_equiv (hHx : ∀ h ∈ Hx k, W.ρ h w = w) (g : ↥(alternatingGroup (Fin 6))) (y : V4) :
    wf k W w (ρk k g y) = W.ρ g (wf k W w y) := by
  by_cases hy : ∃ g' : ↥(alternatingGroup (Fin 6)), ρk k g' (x0 k) = y
  · obtain ⟨g', rfl⟩ := hy
    have : ρk k g (ρk k g' (x0 k)) = ρk k (g * g') (x0 k) := by
      rw [map_mul, Module.End.mul_apply]
    rw [this, wf_ρ hHx, wf_ρ hHx, map_mul, Module.End.mul_apply]
  · have hy' : ¬ ∃ g'' : ↥(alternatingGroup (Fin 6)), ρk k g'' (x0 k) = ρk k g y := by
      rintro ⟨g'', hg''⟩
      apply hy
      refine ⟨g⁻¹ * g'', ?_⟩
      rw [map_mul, Module.End.mul_apply, hg'', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]
    unfold wf
    rw [dif_neg hy', dif_neg hy, map_zero]

@[expose] noncomputable def Psi (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier) :
    Fn →+ W.carrier where
  toFun u := ∑ y : V4, u y • wf k W w y
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]

theorem Psi_equiv (hHx : ∀ h ∈ Hx k, W.ρ h w = w) (g : ↥(alternatingGroup (Fin 6))) (u : Fn) :
    Psi k W w (permAct (Mk k) g u) = W.ρ g (Psi k W w u) := by
  show ∑ y : V4, u (ρk k g⁻¹ y) • wf k W w y = W.ρ g (∑ y : V4, u y • wf k W w y)
  rw [map_sum]
  simp only [map_smul]
  rw [← (eqv k g).sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  show u (ρk k g⁻¹ (ρk k g y)) • wf k W w (ρk k g y) = u y • W.ρ g (wf k W w y)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    wf_equiv hHx]

theorem Psi_delta (a : V4) : Psi k W w (delta a) = wf k W w a := by
  show ∑ y : V4, delta a y • wf k W w y = _
  simp [delta, ite_smul]

theorem wf_x0 (hHx : ∀ h ∈ Hx k, W.ρ h w = w) : wf k W w (x0 k) = w := by
  have := wf_ρ hHx 1
  rwa [map_one, Module.End.one_apply, map_one, Module.End.one_apply] at this

theorem wf_y2 (hHx : ∀ h ∈ Hx k, W.ρ h w = w) : wf k W w (y2 k) = W.ρ (h0E k) w := by
  rw [← ρk_h0E_x0 k, wf_ρ hHx]

theorem wf_y3 (hHx : ∀ h ∈ Hx k, W.ρ h w = w) :
    wf k W w (y3 k) = W.ρ (h0E k) (W.ρ (h0E k) w) := by
  rw [← ρk_h0E_y2 k, wf_equiv hHx, wf_y2 hHx]

theorem wf_cycle (hHx : ∀ h ∈ Hx k, W.ρ h w = w) :
    W.ρ (h0E k) (W.ρ (h0E k) (W.ρ (h0E k) w)) = w := by
  rw [← wf_y3 hHx, ← wf_equiv hHx, ρk_h0E_y3, wf_x0 hHx]

theorem Psi_lineSharp (hHx : ∀ h ∈ Hx k, W.ρ h w = w) :
    Psi k W w (lineSharp k) = w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) := by
  have h1 : lineSharp k = delta (x0 k) + delta (y2 k) + delta (y3 k) :=
    funext fun x => lineSharp_eq k x
  rw [h1, map_add, map_add, Psi_delta, Psi_delta, Psi_delta, wf_x0 hHx, wf_y2 hHx, wf_y3 hHx]

theorem hsum_eq_of (k : Fin 2) {r : ℕ} (σ : Fin r → Perm (Fin 6)) (hs : ∀ i, Perm.sign (σ i) = 1)
    (u v : Fn) (h : ∀ w : V4, ∑ i, u (Matrix.mulVec (Rm k (σ i)⁻¹) w) = v w) :
    ∑ i, permAct (Mk k) ⟨σ i, Perm.mem_alternatingGroup.mpr (hs i)⟩ u = v := by
  funext w
  rw [Finset.sum_apply]
  simp only [permAct_apply, ρk_apply]
  exact h w

theorem Psi_onesOm (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hrel : w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0) : Psi k W w onesOm = 0 := by
  have h1 : Psi k W w (lineSharp k) = 0 := by rw [Psi_lineSharp hHx]; exact hrel
  have h2 := hsum_eq_of k (RS2 k) (RS2_sign k) (lineSharp k) onesOm (spread_sum k)
  rw [← h2, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Psi_equiv hHx, h1, map_zero]

theorem Psi_U2gen (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hrel : w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0) : Psi k W w (U2gen k) = 0 := by
  have h1 : Psi k W w (lineSharp k) = 0 := by rw [Psi_lineSharp hHx]; exact hrel
  have h2 : U2gen k = lineSharp k + onesOm := funext fun x => U2gen_eq k x
  rw [h2, map_add, h1, Psi_onesOm hHx hrel, add_zero]

theorem Psi_U0gen (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hrel : w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0) : Psi k W w (U0gen k) = w := by
  have h2 : U0gen k = onesOm + delta (x0 k) := funext fun x => U0gen_eq k x
  rw [h2, map_add, Psi_onesOm hHx hrel, Psi_delta, wf_x0 hHx, zero_add]

end Frobenius

theorem N2_le_closure (k : Fin 2) : ∀ n ∈ Nk k 2, n ∈ AddSubgroup.closure
    (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h (U2gen k)) := by
  fin_cases k
  · exact le_closure_of_indep 0 (N2_inv 0) (U2gen_mem 0) (card_N2 0).le gP_2_0 hS_2_0 yP_2_0
      MP_2_0 hM_2_0
  · exact le_closure_of_indep 1 (N2_inv 1) (U2gen_mem 1) (card_N2 1).le gP_2_1 hS_2_1 yP_2_1
      MP_2_1 hM_2_1

theorem Psi_N2 {k : Fin 2} {W : Md ↥(alternatingGroup (Fin 6))} {w : W.carrier}
    (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hrel : w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0) {n : Fn} (hn : n ∈ Nk k 2) :
    Psi k W w n = 0 := by
  have hU := Psi_U2gen hHx hrel
  have hle : AddSubgroup.closure
      (Set.range fun h : ↥(alternatingGroup (Fin 6)) => permRep (Mk k) h (U2gen k)) ≤
      (Psi k W w).ker := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    show Psi k W w (permAct (Mk k) g (U2gen k)) = 0
    rw [Psi_equiv hHx, hU, map_zero]
  exact AddMonoidHom.mem_ker.mp (hle (N2_le_closure k n hn))

theorem cover_core (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier)
    (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hgen : AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤)
    (hrel : w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0) :
    ∃ π : ↥(Nk k 0) →+ W.carrier, Function.Surjective π ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
        π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = W.ρ g (π n)) ∧
      ∀ n : ↥(Nk k 0), (n : Fn) ∈ Nk k 2 → π n = 0 := by
  refine ⟨(Psi k W w).comp (Nk k 0).subtype, ?_, fun g n => Psi_equiv hHx g n, fun n hn =>
    Psi_N2 hHx hrel hn⟩
  have hrange : ((Psi k W w).comp (Nk k 0).subtype).range = ⊤ := by
    apply top_unique
    rw [← hgen, AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨⟨permAct (Mk k) g (U0gen k), N0_inv k g _ (U0gen_mem k)⟩, ?_⟩
    show Psi k W w (permAct (Mk k) g (U0gen k)) = W.ρ g w
    rw [Psi_equiv hHx, Psi_U0gen hHx hrel]
  exact AddMonoidHom.range_eq_top.mp hrange

theorem rel_of_card (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier)
    (hw0 : w ≠ 0) (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hline : Nat.card ↥(AddSubgroup.closure
      (Set.range fun g : ↥(Hl k) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)) = 4) :
    w + W.ρ (h0E k) w + W.ρ (h0E k) (W.ρ (h0E k) w) = 0 := by
  set K := AddSubgroup.closure
    (Set.range fun g : ↥(Hl k) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w) with hK
  have hgens : ∀ g : ↥(Hl k), W.ρ (g : ↥(alternatingGroup (Fin 6))) w = w ∨
      W.ρ (g : ↥(alternatingGroup (Fin 6))) w = W.ρ (h0E k) w ∨
      W.ρ (g : ↥(alternatingGroup (Fin 6))) w = W.ρ (h0E k) (W.ρ (h0E k) w) := by
    intro g
    have h1 : inLine k (ρk k g (x0 k)) := g.2 _ ((inLine_iff k _).mpr (Or.inr (Or.inl rfl)))
    have h2 : ρk k g (x0 k) ≠ 0 := ρk_ne_zero k g (x0_ne_zero k)
    rw [inLine_iff] at h1
    rw [← wf_ρ hHx]
    rcases h1 with h | h | h | h
    · exact absurd h h2
    · left; rw [h, wf_x0 hHx]
    · right; left; rw [h, wf_y2 hHx]
    · right; right; rw [h, wf_y3 hHx]
  have haK : w ∈ K := AddSubgroup.subset_closure
    ⟨⟨1, one_mem_Hl k⟩, by show W.ρ 1 w = w; rw [map_one, Module.End.one_apply]⟩
  have hbK : W.ρ (h0E k) w ∈ K := AddSubgroup.subset_closure ⟨⟨h0E k, h0E_mem_Hl k⟩, rfl⟩
  have hcK : W.ρ (h0E k) (W.ρ (h0E k) w) ∈ K := AddSubgroup.subset_closure
    ⟨⟨h0E k * h0E k, mul_mem_Hl (h0E_mem_Hl k) (h0E_mem_Hl k)⟩, by
      show W.ρ (h0E k * h0E k) w = _
      rw [map_mul, Module.End.mul_apply]⟩
  have hb0 : W.ρ (h0E k) w ≠ 0 := ρ_apply_ne_zero W _ hw0
  have hc0 : W.ρ (h0E k) (W.ρ (h0E k) w) ≠ 0 := ρ_apply_ne_zero W _ hb0
  have hcyc := wf_cycle hHx
  by_cases hdeg : w = W.ρ (h0E k) w ∨ W.ρ (h0E k) w = W.ρ (h0E k) (W.ρ (h0E k) w) ∨
      w = W.ρ (h0E k) (W.ρ (h0E k) w)
  · exfalso
    have hall : w = W.ρ (h0E k) w ∧ W.ρ (h0E k) w = W.ρ (h0E k) (W.ρ (h0E k) w) := by
      rcases hdeg with h | h | h
      · exact ⟨h, congrArg (W.ρ (h0E k)) h⟩
      · have hca : W.ρ (h0E k) (W.ρ (h0E k) w) = w := (congrArg (W.ρ (h0E k)) h).trans hcyc
        exact ⟨(h.trans hca).symm, h⟩
      · have hab : w = W.ρ (h0E k) w := ((congrArg (W.ρ (h0E k)) h).trans hcyc).symm
        exact ⟨hab, hab.symm.trans h⟩
    have hle : Nat.card K ≤ 2 := card_closure_le_two (M := W.carrier)
      (S := Set.range fun g : ↥(Hl k) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w) w (by
        rintro _ ⟨g, rfl⟩
        show W.ρ (g : ↥(alternatingGroup (Fin 6))) w = w
        rcases hgens g with h | h | h
        · exact h
        · rw [h, ← hall.1]
        · rw [h, ← hall.2, ← hall.1])
    omega
  · push Not at hdeg
    exact sum_zero_of_card_four K hline w _ _ haK hbK hcK hw0 hb0 hc0 hdeg.1 hdeg.2.2 hdeg.2.1

theorem cover_theorem (k : Fin 2) (W : Md ↥(alternatingGroup (Fin 6))) (w : W.carrier)
    (hw0 : w ≠ 0) (hHx : ∀ h ∈ Hx k, W.ρ h w = w)
    (hgen : AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => W.ρ g w) = ⊤)
    (hline : Nat.card ↥(AddSubgroup.closure
      (Set.range fun g : ↥(Hl k) => W.ρ (g : ↥(alternatingGroup (Fin 6))) w)) = 4) :
    ∃ π : ↥(Nk k 0) →+ W.carrier, Function.Surjective π ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥(Nk k 0)),
        π ⟨permAct (Mk k) g n, N0_inv k g n n.2⟩ = W.ρ g (π n)) ∧
      ∀ n : ↥(Nk k 0), (n : Fn) ∈ Nk k 2 → π n = 0 :=
  cover_core k W w hHx hgen (rel_of_card k W w hw0 hHx hline)

end CFSG.Quasithin.ShultG53
