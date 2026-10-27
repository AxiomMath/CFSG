module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationL32Tab
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveL32
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin.A10

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Quasithin.A10.L32Tab

namespace L32Proof

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

def pt : Fin 8 → Omega (ZMod 7) :=
  ![none, some 0, some 1, some 2, some 3, some 4, some 5, some 6]

def ix : Omega (ZMod 7) → Fin 8
  | none => 0
  | some x => ⟨x.val + 1, Nat.succ_lt_succ (ZMod.val_lt x)⟩

theorem pt_ix : ∀ p, pt (ix p) = p := by decide +kernel

theorem ix_pt : ∀ i, ix (pt i) = i := by decide +kernel

def code (σ : Equiv.Perm (Omega (ZMod 7))) : ℕ := codeV fun i => (ix (σ (pt i))).val

theorem dig_codeV (v : Fin 8 → ℕ) (hv : ∀ i, v i < 8) (j : Fin 8) :
    dig (codeV v) j.val = v j := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  have h8 : (7 : ℕ) = 2 ^ 3 - 1 := by norm_num
  have key : ∀ c m : ℕ, dig c m = c / 2 ^ (3 * m) % 2 ^ 3 := by
    intro c m
    simp only [dig, Nat.shiftRight_eq_div_pow, h8, Nat.and_two_pow_sub_one_eq_mod]
  fin_cases j
  · show dig (codeV v) 0 = v 0
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow, Nat.div_one]
    omega
  · show dig (codeV v) 1 = v 1
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 2 = v 2
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 3 = v 3
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 4 = v 4
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 5 = v 5
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 6 = v 6
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega
  · show dig (codeV v) 7 = v 7
    rw [key]
    simp only [codeV, Nat.reduceMul, Nat.reducePow]
    omega

theorem dig_lt (c i : ℕ) : dig c i < 8 := by
  unfold dig
  have := Nat.and_le_right (n := c >>> (3 * i)) (m := 7)
  omega

theorem dig_cmpN (a b : ℕ) (j : Fin 8) : dig (cmpN a b) j.val = dig a (dig b j.val) :=
  dig_codeV _ (fun _ => dig_lt _ _) j

theorem dig_code (σ : Equiv.Perm (Omega (ZMod 7))) (j : Fin 8) :
    dig (code σ) j.val = (ix (σ (pt j))).val :=
  dig_codeV _ (fun _ => Fin.is_lt _) j

theorem code_mul (σ τ : Equiv.Perm (Omega (ZMod 7))) : code (σ * τ) = cmpN (code σ) (code τ) := by
  have h : ∀ k : Fin 8, dig (code σ) (dig (code τ) k.val) = (ix ((σ * τ) (pt k))).val := by
    intro k
    rw [dig_code τ k, dig_code σ (ix (τ (pt k))), pt_ix]
    rfl
  exact congrArg codeV (funext fun k => (h k).symm)

theorem code_injective : Function.Injective code := by
  intro σ τ h
  have h1 : ∀ j : Fin 8, σ (pt j) = τ (pt j) := by
    intro j
    have h2 : (ix (σ (pt j))).val = (ix (τ (pt j))).val := by
      rw [← dig_code σ j, ← dig_code τ j, h]
    have h3 : ix (σ (pt j)) = ix (τ (pt j)) := Fin.ext h2
    calc σ (pt j) = pt (ix (σ (pt j))) := (pt_ix _).symm
      _ = pt (ix (τ (pt j))) := by rw [h3]
      _ = τ (pt j) := pt_ix _
  refine Equiv.ext fun p => ?_
  have := h1 (ix p)
  rwa [pt_ix] at this

theorem code_one : code 1 = idC := by decide +kernel

theorem commB_of_eq {a b : ℕ} (h : cmpN b a = cmpN a b) : commB a b = true := by
  simp only [commB, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro k hk
  have h1 : dig (cmpN b a) k = dig (cmpN a b) k := congrArg (fun c => dig c k) h
  have h2 := dig_cmpN b a ⟨k, hk⟩
  have h3 := dig_cmpN a b ⟨k, hk⟩
  rw [← h2, ← h3]
  exact h1

theorem commB_code {σ τ : Equiv.Perm (Omega (ZMod 7))} (h : σ * τ = τ * σ) :
    commB (code σ) (code τ) = true := by
  apply commB_of_eq
  rw [← code_mul, ← code_mul, h]

abbrev tau7 : Equiv.Perm (Omega (ZMod 7)) := translation (ZMod 7) 1

noncomputable abbrev iota7 : Equiv.Perm (Omega (ZMod 7)) := inversion (ZMod 7)

def mu3 : (ZMod 7)ˣ := ⟨3, 5, by decide, by decide⟩

abbrev mu7 : Equiv.Perm (Omega (ZMod 7)) := multiplier (ZMod 7) mu3

theorem code_tau : code tau7 = tauC := by decide +kernel

theorem code_tau_inv : code tau7⁻¹ = tauInvC := by decide +kernel

theorem code_mu : code mu7 = muC := by decide +kernel

theorem code_mu_inv : code mu7⁻¹ = muInvC := by decide +kernel

def iotaP : Fin 8 → Fin 8 := ![1, 0, 7, 4, 3, 6, 5, 2]

theorem inversion_pt (i : Fin 8) : inversion (ZMod 7) (pt i) = pt (iotaP i) := by
  fin_cases i
  · show inversion (ZMod 7) none = pt 1
    rw [inversion_none]
    rfl
  · show inversion (ZMod 7) (some 0) = pt 0
    rw [inversion_zero]
    rfl
  · show inversion (ZMod 7) (some 1) = pt 7
    rw [inversion_nonzero (ZMod 7) 1 (by decide)]
    decide +kernel
  · show inversion (ZMod 7) (some 2) = pt 4
    rw [inversion_nonzero (ZMod 7) 2 (by decide)]
    decide +kernel
  · show inversion (ZMod 7) (some 3) = pt 3
    rw [inversion_nonzero (ZMod 7) 3 (by decide)]
    decide +kernel
  · show inversion (ZMod 7) (some 4) = pt 6
    rw [inversion_nonzero (ZMod 7) 4 (by decide)]
    decide +kernel
  · show inversion (ZMod 7) (some 5) = pt 5
    rw [inversion_nonzero (ZMod 7) 5 (by decide)]
    decide +kernel
  · show inversion (ZMod 7) (some 6) = pt 2
    rw [inversion_nonzero (ZMod 7) 6 (by decide)]
    decide +kernel

theorem code_iota : code iota7 = iotaC := by
  have h : code iota7 = codeV fun i => (iotaP i).val := by
    unfold code
    congr 1
    funext i
    rw [inversion_pt, ix_pt]
  rw [h]
  decide +kernel

theorem iota7_mul_self : iota7 * iota7 = 1 := by
  apply code_injective
  rw [code_mul, code_iota, code_one]
  decide +kernel

theorem iota7_inv : iota7⁻¹ = iota7 := inv_eq_of_mul_eq_one_right iota7_mul_self

theorem code_mem_closure {s : Set (Equiv.Perm (Omega (ZMod 7)))} {S : List ℕ}
    (hone : code 1 ∈ S) (hmul : ∀ y ∈ s, ∀ t ∈ S, cmpN t (code y) ∈ S)
    (hinv : ∀ y ∈ s, ∀ t ∈ S, cmpN t (code y⁻¹) ∈ S) :
    ∀ x ∈ Subgroup.closure s, code x ∈ S := by
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact hone
  | mul_right x _ y hy ih =>
    rw [code_mul]
    exact hmul y hy _ ih
  | mul_inv_cancel x _ y hy ih =>
    rw [code_mul]
    exact hinv y hy _ ih

theorem translation_eq_pow : ∀ b : ZMod 7, translation (ZMod 7) b = tau7 ^ b.val := by
  decide +kernel

theorem multiplier_eq_pow :
    ∀ s : (ZMod 7)ˣ, ∃ n : Fin 6, multiplier (ZMod 7) s = mu7 ^ (n : ℕ) := by
  decide +kernel

theorem coordinateG_le : coordinateG (ZMod 7) ≤ Subgroup.closure {tau7, iota7} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (⟨b, rfl⟩ | rfl)
  · rw [translation_eq_pow]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem coordinateE_le : coordinateE (ZMod 7) ≤ Subgroup.closure {tau7, iota7, mu7} := by
  have hG : coordinateG (ZMod 7) ≤ Subgroup.closure {tau7, iota7, mu7} :=
    coordinateG_le.trans (Subgroup.closure_mono (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hD : coordinateD (ZMod 7) ≤ Subgroup.closure {tau7, iota7, mu7} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | ⟨s, rfl⟩)
    · exact hG hx
    · obtain ⟨n, hn⟩ := multiplier_eq_pow s
      rw [hn]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) _
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨σ, rfl⟩)
  · exact hD hx
  · have hσ : σ = 1 := Subsingleton.elim σ 1
    have h1 : fieldExtension (ZMod 7) σ = 1 := by
      rw [hσ]
      ext x
      cases x <;> rfl
    rw [h1]
    exact one_mem _

theorem coordinateG_code : ∀ x ∈ coordinateG (ZMod 7), code x ∈ Lc := by
  intro x hx
  refine code_mem_closure (s := {tau7, iota7}) (S := Lc) ?_ ?_ ?_ x (coordinateG_le hx)
  · rw [code_one]
    exact idC_mem_Lc
  · intro y hy t ht
    rcases hy with rfl | rfl
    · rw [code_tau]
      exact Lc_closed t ht tauC (by simp)
    · rw [code_iota]
      exact Lc_closed t ht iotaC (by simp)
  · intro y hy t ht
    rcases hy with rfl | rfl
    · rw [code_tau_inv]
      exact Lc_closed t ht tauInvC (by simp)
    · rw [iota7_inv, code_iota]
      exact Lc_closed t ht iotaC (by simp)

theorem coordinateE_code : ∀ x ∈ coordinateE (ZMod 7), code x ∈ Dc := by
  intro x hx
  refine code_mem_closure (s := {tau7, iota7, mu7}) (S := Dc) ?_ ?_ ?_ x (coordinateE_le hx)
  · rw [code_one]
    exact idC_mem_Dc
  · intro y hy t ht
    rcases hy with rfl | rfl | rfl
    · rw [code_tau]
      exact Dc_closed t ht tauC (by simp)
    · rw [code_iota]
      exact Dc_closed t ht iotaC (by simp)
    · rw [code_mu]
      exact Dc_closed t ht muC (by simp)
  · intro y hy t ht
    rcases hy with rfl | rfl | rfl
    · rw [code_tau_inv]
      exact Dc_closed t ht tauInvC (by simp)
    · rw [iota7_inv, code_iota]
      exact Dc_closed t ht iotaC (by simp)
    · rw [code_mu_inv]
      exact Dc_closed t ht muInvC (by simp)

theorem nonempty_equiv_coordinateG (X : Type) [Group X]
    (hX : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (X ≃* coordinateG (ZMod 7)) := by
  obtain ⟨eX⟩ := hX
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact ⟨eX.trans (e₂.trans (e₃.trans (e₄.trans (pslEquivCoordinateG (ZMod 7)))))⟩

end L32Proof

theorem l32AutFact : L32AutFact := by
  intro X _ hX S hS α hα
  obtain ⟨θ⟩ := L32Proof.nonempty_equiv_coordinateG X hX
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨e, he⟩ := coordinateConjugation_surjective (ZMod 7) (MulAut.congr θ α)
  have hconj : ∀ g : coordinateG (ZMod 7),
      (((MulAut.congr θ α) g : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) =
        (e : Equiv.Perm (Omega (ZMod 7))) * g * (e : Equiv.Perm (Omega (ZMod 7)))⁻¹ := by
    intro g
    rw [← he]
    exact coordinateConjugation_apply_coe (ZMod 7) e g
  have hcomm : ∀ s : S, (e : Equiv.Perm (Omega (ZMod 7))) *
      ((θ (s : X) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) =
        ((θ (s : X) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
          (e : Equiv.Perm (Omega (ZMod 7))) := by
    intro s
    have h1 : (MulAut.congr θ α) (θ (s : X)) = θ (s : X) := by
      show θ (α (θ.symm (θ (s : X)))) = θ (s : X)
      rw [MulEquiv.symm_apply_apply, hα (s : X) s.2]
    have h2 := hconj (θ (s : X))
    rw [h1] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2.symm
  have he1 : (e : Equiv.Perm (Omega (ZMod 7))) = 1 := by
    by_contra hne
    have hd : L32Proof.code (e : Equiv.Perm (Omega (ZMod 7))) ∈ L32Tab.Dc :=
      L32Proof.coordinateE_code _ e.2
    have hdne : L32Proof.code (e : Equiv.Perm (Omega (ZMod 7))) ≠ L32Tab.idC := fun h =>
      hne (L32Proof.code_injective (h.trans L32Proof.code_one.symm))
    have hlt := L32Tab.Dc_comm _ hd hdne
    let f : S → ℕ := fun s => L32Proof.code ((θ (s : X) : coordinateG (ZMod 7)) :
      Equiv.Perm (Omega (ZMod 7)))
    have hf_mem : ∀ s : S, f s ∈ L32Tab.Lc.filter
        (L32Tab.commB (L32Proof.code (e : Equiv.Perm (Omega (ZMod 7))))) := by
      intro s
      rw [List.mem_filter]
      refine ⟨L32Proof.coordinateG_code _ (θ (s : X)).2, ?_⟩
      exact L32Proof.commB_code (hcomm s)
    have hf_inj : Function.Injective f := by
      intro s s' h
      have h1 := L32Proof.code_injective h
      exact Subtype.ext (θ.injective (Subtype.ext h1))
    have h1 : Nat.card S ≤ Nat.card ((L32Tab.Lc.filter
        (L32Tab.commB (L32Proof.code (e : Equiv.Perm (Omega (ZMod 7)))))).toFinset) :=
      Nat.card_le_card_of_injective
        (fun s => ⟨f s, List.mem_toFinset.2 (hf_mem s)⟩)
        (fun s s' h => hf_inj (congrArg Subtype.val h))
    rw [Nat.card_eq_finsetCard] at h1
    have h2 := h1.trans (List.toFinset_card_le _)
    omega
  have hψ : MulAut.congr θ α = 1 := by
    refine MulEquiv.ext fun g => ?_
    refine Subtype.ext ?_
    rw [hconj g, he1]
    simp
  exact (MulAut.congr θ).injective (hψ.trans (map_one _).symm)

end CFSG.Quasithin.A10
