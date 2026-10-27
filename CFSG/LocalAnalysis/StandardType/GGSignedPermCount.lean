module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

namespace SignedPermCount

open SpCoord Multiplicative
open CFSG.Assembly

variable {p k : ℕ}

private def signVec (b : Fin k → Bool) : Fin k → ZMod p :=
  fun i => match b i with
    | true => -1
    | false => 1

private theorem signVec_eq_neg_one_of {b : Fin k → Bool} {i : Fin k} (h : b i = true) :
    (signVec b i : ZMod p) = -1 := by
  simp [signVec, h]

private theorem signVec_eq_one_of {b : Fin k → Bool} {i : Fin k} (h : b i = false) :
    (signVec b i : ZMod p) = 1 := by
  simp [signVec, h]

private theorem signVec_eq_one_or_neg_one (b : Fin k → Bool) (i : Fin k) :
    (signVec b i : ZMod p) = 1 ∨ (signVec b i : ZMod p) = -1 := by
  cases h : b i <;> simp [signVec, h]

private theorem signVec_ne_zero (hp : p.Prime) (b : Fin k → Bool) (i : Fin k) :
    (signVec b i : ZMod p) ≠ 0 :=
  coord_sign_ne_zero hp (signVec_eq_one_or_neg_one b i)

private theorem one_ne_neg_one (hp : p.Prime) (hp2 : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  intro h
  exact coord_two_ne_zero hp hp2 (by linear_combination h)

private theorem apply_mulSingle_diag (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p)
    (hε : ∀ i, ε i * ε i = 1) (i : Fin k) (c : ZMod p) :
    ((permAut π : MulAut (Fin k → Multiplicative (ZMod p))) * diagAut ε hε)
        (Pi.mulSingle i (ofAdd c)) =
      Pi.mulSingle (π i) (ofAdd (ε i * c)) := by
  rw [MulAut.mul_apply, diagAut_mulSingle, permAut_mulSingle]

private theorem isSignedPerm_mul_sgnAut {u : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : IsSignedPerm ⇑u) (i : Fin k) :
    IsSignedPerm ⇑(u * (sgnAut i : MulAut (Fin k → Multiplicative (ZMod p)))) := by
  obtain ⟨π, ε, hε, hup⟩ := hu
  refine ⟨π, Function.update ε i (-ε i), fun j => ?_, fun f j => ?_⟩
  · by_cases hj : j = i
    · rw [hj, Function.update_self]
      rcases hε i with h | h <;> rw [h] <;> simp
    · rw [Function.update_of_ne hj]
      exact hε j
  · rw [MulAut.mul_apply, hup (sgnAut i f) j, sgnAut_apply]
    by_cases hj : j = i
    · rw [hj, Function.update_self, Function.update_self, toAdd_inv]
      ring
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]

private def signedPermEquivFun (x : Equiv.Perm (Fin k) × (Fin k → Bool)) :
    {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} :=
  ⟨(permAut x.1 : MulAut (Fin k → Multiplicative (ZMod p))) *
      diagAut (signVec x.2)
        (fun i => coord_sign_mul_self (signVec_eq_one_or_neg_one x.2 i)),
    isSignedPerm_permAut_mul_diagAut x.1 (signVec x.2) (signVec_eq_one_or_neg_one x.2)⟩

theorem card_isSignedPerm (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} =
      2 ^ k * k.factorial := by
  have hinj : Function.Injective (signedPermEquivFun (p := p) (k := k)) := by
    rintro ⟨π, b⟩ ⟨π', b'⟩ h
    have hval : ∀ i,
        ((permAut π : MulAut (Fin k → Multiplicative (ZMod p))) *
            diagAut (signVec b : Fin k → ZMod p)
              (fun j => coord_sign_mul_self (signVec_eq_one_or_neg_one b j)))
          (Pi.mulSingle i (ofAdd 1)) =
        ((permAut π' : MulAut (Fin k → Multiplicative (ZMod p))) *
            diagAut (signVec b' : Fin k → ZMod p)
              (fun j => coord_sign_mul_self (signVec_eq_one_or_neg_one b' j)))
          (Pi.mulSingle i (ofAdd 1)) :=
      fun i => congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod p)) =>
        u (Pi.mulSingle i (ofAdd 1))) (Subtype.ext_iff.mp h)
    have h2 : ∀ i, (Pi.mulSingle (π i) (ofAdd ((signVec b i : ZMod p) * 1)) :
        Fin k → Multiplicative (ZMod p)) =
        (Pi.mulSingle (π' i) (ofAdd ((signVec b' i : ZMod p) * 1)) :
        Fin k → Multiplicative (ZMod p)) := by
      intro i
      have hi := hval i
      rwa [apply_mulSingle_diag, apply_mulSingle_diag] at hi
    have hπ : π = π' := Equiv.ext fun i =>
      (mulSingle_ofAdd_eq_iff (by simpa using signVec_ne_zero hp b i) (h2 i)).1
    have hε : ∀ i, signVec b i = signVec b' i := fun i => by
      have := (mulSingle_ofAdd_eq_iff (by simpa using signVec_ne_zero hp b i) (h2 i)).2
      simpa using this
    have hb : b = b' := by
      funext i
      have hi := hε i
      cases hbi : b i <;> cases hbi' : b' i
      · rfl
      · exfalso
        simp only [signVec, hbi, hbi'] at hi
        exact one_ne_neg_one hp hp2 hi
      · exfalso
        simp only [signVec, hbi, hbi'] at hi
        exact one_ne_neg_one hp hp2 hi.symm
      · rfl
    rw [hπ, hb]
  have hsurj : Function.Surjective (signedPermEquivFun (p := p) (k := k)) := by
    rintro ⟨u, hu⟩
    obtain ⟨π, ε, hε, hup⟩ := hu
    let b : Fin k → Bool := fun i => decide (ε i = -1)
    have hb : signVec b = ε := by
      funext i
      rcases hε i with h1 | h1
      · have hbi : b i = false := by
          simp only [b]
          exact decide_eq_false (by rw [h1]; exact one_ne_neg_one hp hp2)
        rw [signVec_eq_one_of hbi, h1]
      · have hbi : b i = true := by
          simp only [b]
          exact decide_eq_true h1
        rw [signVec_eq_neg_one_of hbi, h1]
    rw [← hb] at hup
    refine ⟨(π, b), ?_⟩
    have hEq : u = (permAut π : MulAut (Fin k → Multiplicative (ZMod p))) *
        diagAut (signVec b)
          (fun j => coord_sign_mul_self (signVec_eq_one_or_neg_one b j)) := by
      refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
      rw [hup f i, MulAut.mul_apply, permAut_apply, Function.comp_apply]
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
      rw [diagAut_apply, toAdd_ofAdd]
    refine Subtype.ext ?_
    show ((permAut π : MulAut (Fin k → Multiplicative (ZMod p))) * diagAut (signVec b)
      (fun j => coord_sign_mul_self (signVec_eq_one_or_neg_one b j))) = u
    exact hEq.symm
  have hcard : Nat.card (Equiv.Perm (Fin k) × (Fin k → Bool)) = k.factorial * 2 ^ k := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), hcard, mul_comm]

theorem card_eq_of_isSignedPerm (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))} (hH : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hs : ∀ i, sgnAut i ∈ H) (ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H) :
    Nat.card H = 2 ^ k * k.factorial := by
  rw [← card_isSignedPerm (p := p) (k := k) hp hp2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u =>
    ⟨hH u, fun hu => mem_of_isSignedPerm hs ht hu⟩)

private theorem finiteMulAutOfPrime (p k : ℕ) [Fact p.Prime] :
    Finite (MulAut (Fin k → Multiplicative (ZMod p))) :=
  Finite.of_injective (fun f : MulAut (Fin k → Multiplicative (ZMod p)) =>
    (f : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))))
    (fun _ _ h => MulEquiv.ext (congrFun h))

theorem card_eq_of_isSignedPerm_even (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))} (hH : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H)
    (hmiss : ∃ i : Fin k, sgnAut i ∉ H) :
    Nat.card H = 2 ^ (k - 1) * k.factorial := by
  classical
  by_cases hk : k = 0
  · subst hk
    obtain ⟨i, _⟩ := hmiss
    exact i.elim0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let i₀ : Fin k := ⟨0, hkpos⟩
    let s : MulAut (Fin k → Multiplicative (ZMod p)) := sgnAut i₀
    have hsgn : sgnAut i₀ ∉ H := by
      intro h0
      obtain ⟨i, hi⟩ := hmiss
      by_cases hii : i = i₀
      · exact hi (by rw [hii]; exact h0)
      · have h1 : sgnAut i * sgnAut i₀ ∈ H := hd i i₀ hii
        have h2 : (sgnAut i * sgnAut i₀) * sgnAut i₀ ∈ H := H.mul_mem h1 h0
        rw [mul_assoc, OrthExcEven.sgnAut_mul_self, mul_one] at h2
        exact hi h2
    have hnot : ∀ h : ↥H, h.1 * s ∉ H := by
      intro h hmem
      exact hsgn (by
        have h1 : h.1⁻¹ * (h.1 * s) ∈ H := H.mul_mem (H.inv_mem h.2) hmem
        rwa [inv_mul_cancel_left] at h1)
    let f : {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} → ↥H ⊕ ↥H :=
      fun x => if hx : x.1 ∈ H then Sum.inl ⟨x.1, hx⟩
        else Sum.inr ⟨x.1 * s,
          (OrthExcEven.mem_or_mul_mem_of_isSignedPerm hd ht i₀ x.2).resolve_left hx⟩
    let g : ↥H ⊕ ↥H → {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} :=
      fun y => match y with
        | Sum.inl h => ⟨h.1, hH h.1 h.2⟩
        | Sum.inr h => ⟨h.1 * s, isSignedPerm_mul_sgnAut (hH h.1 h.2) i₀⟩
    have hgf : Function.LeftInverse g f := by
      intro x
      by_cases hx : x.1 ∈ H
      · have hfx : f x = Sum.inl ⟨x.1, hx⟩ := dif_pos hx
        rw [hfx]
      · have hfx : f x = Sum.inr ⟨x.1 * s, _⟩ := dif_neg hx
        rw [hfx]
        refine Subtype.ext ?_
        show (x.1 * s) * s = x.1
        rw [mul_assoc, OrthExcEven.sgnAut_mul_self, mul_one]
    have hfg : Function.RightInverse g f := by
      intro y
      rcases y with h | h
      · show f (g (Sum.inl h)) = Sum.inl h
        change f ⟨h.1, hH h.1 h.2⟩ = Sum.inl h
        have hf : f ⟨h.1, hH h.1 h.2⟩ = Sum.inl ⟨h.1, h.2⟩ := dif_pos h.2
        rw [hf]
      · show f (g (Sum.inr h)) = Sum.inr h
        change f ⟨h.1 * s, isSignedPerm_mul_sgnAut (hH h.1 h.2) i₀⟩ = Sum.inr h
        have hf : f ⟨h.1 * s, isSignedPerm_mul_sgnAut (hH h.1 h.2) i₀⟩ =
            Sum.inr ⟨(h.1 * s) * s, _⟩ := dif_neg (hnot h)
        rw [hf]
        exact congrArg Sum.inr (Subtype.ext (by
          show (h.1 * s) * s = h.1
          rw [mul_assoc, OrthExcEven.sgnAut_mul_self, mul_one]))
    have heq : {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} ≃
        ↥H ⊕ ↥H := ⟨f, g, hgf, hfg⟩
    have hS : Nat.card {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} =
        2 ^ k * k.factorial := card_isSignedPerm hp hp2
    have hfinAut : Finite (MulAut (Fin k → Multiplicative (ZMod p))) :=
      @finiteMulAutOfPrime p k ⟨hp⟩
    have hfinS : Finite {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} :=
      @Finite.of_injective _ _ hfinAut (fun x => x.1) (fun x y h => Subtype.ext h)
    have hfinH : Finite ↥H :=
      @Finite.of_injective _ _ hfinS (fun h : ↥H =>
        (⟨h.1, hH h.1 h.2⟩ : {u : MulAut (Fin k → Multiplicative (ZMod p)) //
          IsSignedPerm ⇑u})) (fun h1 h2 h => Subtype.ext (congrArg (fun x : {u : MulAut (Fin k → Multiplicative (ZMod p)) // IsSignedPerm ⇑u} => x.1) h))
    have hsum : 2 ^ k * k.factorial = Nat.card ↥H + Nat.card ↥H := by
      rw [← hS, Nat.card_congr heq, @Nat.card_sum ↥H ↥H hfinH hfinH]
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      have hk1 : k = (k - 1) + 1 := by omega
      conv_lhs => rw [hk1]
      rw [pow_succ]
    have hmain : 2 * (2 ^ (k - 1) * k.factorial) = 2 * Nat.card ↥H := by
      have h2 : Nat.card ↥H + Nat.card ↥H = 2 * Nat.card ↥H := by ring
      rw [← h2, ← hsum, hpow]
      ring
    have hHcard : Nat.card ↥H = 2 ^ (k - 1) * k.factorial := by omega
    exact hHcard

theorem dvd_card_of_isSignedPerm_even (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))} (hH : ∀ u ∈ H, IsSignedPerm ⇑u)
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H) :
    2 ^ (k - 1) * k.factorial ∣ Nat.card H := by
  classical
  by_cases hk : k = 0
  · subst hk
    simp
  · by_cases hmiss : ∃ i : Fin k, sgnAut i ∉ H
    · rw [card_eq_of_isSignedPerm_even hp hp2 hH hd ht hmiss]
    · have hs : ∀ i : Fin k, sgnAut i ∈ H := by
        intro i
        by_contra hi
        exact hmiss ⟨i, hi⟩
      have hcard := card_eq_of_isSignedPerm hp hp2 hH hs ht
      rw [hcard]
      refine ⟨2, ?_⟩
      have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
        have hk1 : k = (k - 1) + 1 := by omega
        conv_lhs => rw [hk1]
        rw [pow_succ]
      rw [hpow]
      ring

theorem isSignedPerm_one (p k : ℕ) :
    SpCoord.IsSignedPerm (⇑(1 : MulAut (Fin k → Multiplicative (ZMod p)))) :=
  ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun f i => by simp⟩

theorem isSignedPerm_mul {p k : ℕ}
    {u v : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : SpCoord.IsSignedPerm ⇑u) (hv : SpCoord.IsSignedPerm ⇑v) :
    SpCoord.IsSignedPerm ⇑(u * v) := by
  obtain ⟨πu, εu, hεu, hu⟩ := hu
  obtain ⟨πv, εv, hεv, hv⟩ := hv
  refine ⟨πu * πv, fun i => εu (πv i) * εv i, fun i => ?_, fun f i => ?_⟩
  · dsimp only
    rcases hεu (πv i) with h | h <;> rcases hεv i with h' | h' <;>
      rw [h, h'] <;> simp [mul_neg]
  · show Multiplicative.toAdd (u (v f) (πu (πv i))) =
      (εu (πv i) * εv i) * Multiplicative.toAdd (f i)
    rw [hu (v f) (πv i), hv f i, mul_assoc]

theorem isSignedPerm_inv {p k : ℕ}
    {u : MulAut (Fin k → Multiplicative (ZMod p))} (hu : SpCoord.IsSignedPerm ⇑u) :
    SpCoord.IsSignedPerm ⇑(u⁻¹) := by
  obtain ⟨π, ε, hε, hu⟩ := hu
  refine ⟨π⁻¹, fun i => ε (π⁻¹ i), fun i => hε _, fun f i => ?_⟩
  show Multiplicative.toAdd (u⁻¹ f (π⁻¹ i)) = ε (π⁻¹ i) * Multiplicative.toAdd (f i)
  have h := hu (u⁻¹ f) (π.symm i)
  rw [MulAut.apply_inv_self, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun x => ε (π.symm i) * x) h
  simp only [← mul_assoc, SpCoord.coord_sign_mul_self (hε (π.symm i)), one_mul] at h2
  exact h2.symm

@[expose] def signedPermSubgroup (p k : ℕ) :
    Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) where
  carrier := {u | SpCoord.IsSignedPerm ⇑u}
  mul_mem' := fun ha hb => isSignedPerm_mul ha hb
  one_mem' := isSignedPerm_one p k
  inv_mem' := fun ha => isSignedPerm_inv ha

theorem card_signedPermSubgroup (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (signedPermSubgroup p k) = 2 ^ k * k.factorial := by
  rw [← card_isSignedPerm (p := p) (k := k) hp hp2]
  rfl

theorem card_dvd_signed_of_normalizer_model {L' : Type} [Group L'] {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ 2 ^ k * k.factorial := by
  classical
  let e : MulAut ↥A →* MulAut (Fin k → Multiplicative (ZMod p)) :=
    (MulAut.congr Θ).symm.toMonoidHom
  have he : Function.Injective e := (MulAut.congr Θ).symm.injective
  have hle : ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      (signedPermSubgroup p k).comap e := by
    intro φ hφ
    rw [Subgroup.mem_comap]
    change SpCoord.IsSignedPerm ⇑(e φ)
    obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    rw [MonoidHom.mem_range] at hgH
    obtain ⟨n, rfl⟩ := hgH
    have hEq : φ = ggConjAut A hgN := MulEquiv.ext fun b => Subtype.ext (hφg b)
    rw [hEq]
    exact hsp n hgN
  have hdvd : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣
      Nat.card (signedPermSubgroup p k) :=
    (Subgroup.card_dvd_of_le hle).trans
      (Subgroup.card_comap_dvd_of_injective (signedPermSubgroup p k) e he)
  rwa [card_signedPermSubgroup hp hp2] at hdvd

theorem ggAutomizer_card_eq_signed_of_model {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (hsgn : ∀ i : Fin k, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ)) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) =
      2 ^ k * k.factorial := by
  classical
  let W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  let H := W.comap (MulAut.congr Θ).toMonoidHom
  have hcardHW : Nat.card H = Nat.card W := by
    rw [show H = W.comap (MulAut.congr Θ).toMonoidHom from rfl,
      Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective (MulAut.congr Θ).symm.injective
  have hHmem : ∀ u ∈ H, SpCoord.IsSignedPerm ⇑u := by
    intro u hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hu
    have hv' : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    have h1 := hsp n hcN
    rwa [← hv', MulEquiv.symm_apply_apply] at h1
  have hsH : ∀ i : Fin k, sgnAut i ∈ H := by
    intro i
    obtain ⟨n, hn, hnα⟩ := hsgn i
    rw [Subgroup.mem_comap]
    change MulAut.congr Θ (sgnAut i) ∈ W
    rw [← hnα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    obtain ⟨n, hn, hnα⟩ := hperm (Equiv.swap a b)
    rw [Subgroup.mem_comap]
    change MulAut.congr Θ (permAut (Equiv.swap a b)) ∈ W
    rw [← hnα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hcardH : Nat.card H = 2 ^ k * k.factorial :=
    card_eq_of_isSignedPerm hp hp2 hHmem hsH htH
  rw [← hcardHW]
  exact hcardH
theorem card_inner_even_signed_bounds {L' : Type} [Group L'] [Finite L']
    {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (MulAut L')}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* A)
    (hD : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    2 ^ (k - 1) * k.factorial ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∧
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ 2 ^ k * k.factorial := by
  classical
  have hp : p.Prime := Fact.out
  let W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  let H := W.comap (MulAut.congr Θ).toMonoidHom
  have hmap : H.map (MulAut.congr Θ).toMonoidHom = W :=
    Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.congr Θ).toMonoidHom)
      (MulAut.congr Θ).surjective W
  have hcard : Nat.card H = Nat.card W := by
    rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.congr Θ).toMonoidHom)
      (MulAut.congr Θ).injective]
  have hsp : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    have huW : MulAut.congr Θ u ∈ W := hu
    obtain ⟨_, ⟨n, rfl⟩, hn, hnu⟩ := mem_ggAutomizer_iff.mp huW
    have heq : MulAut.congr Θ u = ggConjAut A hn :=
      MulEquiv.ext fun a => Subtype.ext ((hnu a).trans (ggConjAut_apply A hn a).symm)
    have hu' : u = (MulAut.congr Θ).symm (ggConjAut A hn) := by
      rw [← heq, MulEquiv.symm_apply_apply]
    rw [hu']
    exact hN n hn
  have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hnd⟩ := hD i j hij
    change MulAut.congr Θ (sgnAut i * sgnAut j) ∈ W
    rw [← hnd]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have htH : ∀ i j : Fin k, i ≠ j → permAut (Equiv.swap i j) ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hnp⟩ := hP (Equiv.swap i j)
    change MulAut.congr Θ (permAut (Equiv.swap i j)) ∈ W
    rw [← hnp]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hdvd := SignedPermCount.dvd_card_of_isSignedPerm_even hp hp2 hsp hdH htH
  rw [hcard] at hdvd
  exact ⟨hdvd, SignedPermCount.card_dvd_signed_of_normalizer_model hp hp2 Θ hN⟩

theorem not_factorial_eq_two_pow_mul_factorial {k d : ℕ} (hk : 2 ≤ k) :
    d.factorial ≠ 2 ^ k * k.factorial := by
  intro h
  have hkpos : 0 < k := by omega
  have hfacpos : 0 < k.factorial := Nat.factorial_pos k
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hd : d ≤ k
  · have hle : d.factorial ≤ k.factorial := Nat.factorial_le hd
    have hlt : k.factorial < 2 ^ k * k.factorial := by
      calc k.factorial = 1 * k.factorial := (one_mul _).symm
        _ < 2 ^ k * k.factorial :=
            Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2 ^ k) hfacpos
    have hlt' : d.factorial < 2 ^ k * k.factorial := hle.trans_lt hlt
    rw [h] at hlt'
    exact lt_irrefl _ hlt'
  · have hd1 : k + 1 ≤ d := by omega
    by_cases hd2 : d = k + 1
    · subst d
      rw [Nat.factorial_succ] at h
      have hk1 : k + 1 = 2 ^ k :=
        Nat.eq_of_mul_eq_mul_right hfacpos (by simpa [mul_comm] using h)
      have hsucc : ∀ n : ℕ, 2 ≤ n → n + 1 < 2 ^ n := by
        intro n hn
        induction n with
        | zero => omega
        | succ m ih =>
          by_cases hm0 : m = 0
          · subst m
            omega
          by_cases hm1 : m = 1
          · subst m
            norm_num
          have hm2 : 2 ≤ m := by omega
          have h := ih hm2
          rw [pow_succ]
          nlinarith
      have hklt : k + 1 < 2 ^ k := hsucc k hk
      omega
    · have hd3 : k + 2 ≤ d := by omega
      have hfac2 : (k + 2).factorial ∣ d.factorial :=
        Nat.factorial_dvd_factorial hd3
      rw [h] at hfac2
      have hfac2' : (k + 2).factorial = (k + 2) * (k + 1) * k.factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        ring
      rw [hfac2'] at hfac2
      have hdiv : (k + 2) * (k + 1) ∣ 2 ^ k :=
        (Nat.mul_dvd_mul_iff_right hfacpos).mp hfac2
      have h1 : k + 1 ∣ 2 ^ k := (dvd_mul_left (k + 1) (k + 2)).trans hdiv
      have h2 : k + 2 ∣ 2 ^ k := (dvd_mul_right (k + 2) (k + 1)).trans hdiv
      obtain ⟨a, _, hA⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      obtain ⟨b, _, hB⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      by_cases ha0 : a = 0
      · rw [ha0] at hA
        omega
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        have h2a : 2 ∣ k + 1 := by
          rw [hA]
          exact dvd_pow_self 2 (by omega)
        obtain ⟨x, hx⟩ := h2a
        by_cases hb0 : b = 0
        · rw [hb0] at hB
          omega
        · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
          have h2b : 2 ∣ k + 2 := by
            rw [hB]
            exact dvd_pow_self 2 (by omega)
          obtain ⟨y, hy⟩ := h2b
          omega

end SignedPermCount

end CFSG.StandardType
