module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsModel

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative NbrOrth

@[expose] def GGTorusEvenSignedPermEltSC (p : ℕ) (R : Type) [Group R] (kP : ℕ → Prop) : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧ kP k ∧
      (∀ i j : Fin k, i ≠ j → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)

@[expose] def GGTorusEvenSignedPermEltSCOf (p : ℕ) (R : Type) [Group R] (kP : ℕ → Prop)
    (εP : ∀ k : ℕ, (Fin k → ZMod p) → Prop) : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧ kP k ∧
      (∀ i j : Fin k, i ≠ j → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧ εP k ε ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)

theorem ggTorusEvenSignedPermEltSCOf_of_permEltSC {p : ℕ} {R : Type} [Group R] {kP : ℕ → Prop}
    (h : GGTorusEvenSignedPermEltSC p R kP) :
    GGTorusEvenSignedPermEltSCOf p R kP fun _ _ => True := by
  intro E hE h3 hsc
  obtain ⟨k, τ, hinj, hrange, hk, hd, hP, hN⟩ := h E hE h3 hsc
  refine ⟨k, τ, hinj, hrange, hk, hd, hP, fun g hg => ?_⟩
  obtain ⟨π, ε, hε, hr⟩ := hN g hg
  exact ⟨π, ε, hε, trivial, hr⟩

theorem ggTorusEvenSignedPermEltSC_of_signedEltSC {p : ℕ} {R : Type} [Group R]
    (h : GGTorusSignedEltSC p R) : GGTorusEvenSignedPermEltSC p R fun _ => True := by
  intro E hE h3 hsc
  obtain ⟨k, τ, hinj, hrange, hsgn, hperm, hnorm⟩ := h E hE h3 hsc
  refine ⟨k, τ, hinj, hrange, trivial, fun i j _ => ?_, hperm, hnorm⟩
  obtain ⟨wi, hwi⟩ := hsgn i
  obtain ⟨wj, hwj⟩ := hsgn j
  exact ⟨wi * wj, fun f => by
    rw [show wi * wj * τ f * (wi * wj)⁻¹ = wi * (wj * τ f * wj⁻¹) * wi⁻¹ by group, hwj, hwi]
    rfl⟩

namespace OrthExcEven

section Coord

variable {p k : ℕ}

theorem sgnAut_mul_sgnAut_apply (i j : Fin k) (f : Fin k → Multiplicative (ZMod p)) :
    (sgnAut i * sgnAut j : MulAut (Fin k → Multiplicative (ZMod p))) f = dinv i j f :=
  rfl

theorem sgnAut_mul_self (i : Fin k) :
    (sgnAut i : MulAut (Fin k → Multiplicative (ZMod p))) * sgnAut i = 1 := by
  rw [← sq, sgnAut_sq]

theorem permAut_swap_mul_self (a b : Fin k) :
    (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))) *
      permAut (Equiv.swap a b) = 1 := by
  rw [← sq, permAut_swap_sq]

theorem mem_or_mul_mem_of_diag {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H) (i₀ : Fin k) (S : Finset (Fin k)) :
    ∀ (u : MulAut (Fin k → Multiplicative (ZMod p))) (ε : Fin k → ZMod p),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ i, i ∉ S → ε i = 1) →
      (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ H ∨ u * sgnAut i₀ ∈ H := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro u ε _ hS hu
    have h1 : u = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [hu, hS i (Finset.notMem_empty i), one_mul]
      rfl
    rw [h1]
    exact Or.inl H.one_mem
  | insert a S ha ih =>
    intro u ε hε hS hu
    rcases hε a with hεa | hεa
    · refine ih u ε hε (fun i hi => ?_) hu
      by_cases hia : i = a
      · rw [hia, hεa]
      · exact hS i (by simp [hia, hi])
    · have h1 : u * sgnAut a ∈ H ∨ u * sgnAut a * sgnAut i₀ ∈ H := by
        refine ih _ (Function.update ε a 1) (fun i => ?_) (fun i hi => ?_) (fun f i => ?_)
        · by_cases hia : i = a
          · subst hia
            simp
          · rw [Function.update_of_ne hia]
            exact hε i
        · by_cases hia : i = a
          · subst hia
            simp
          · rw [Function.update_of_ne hia]
            exact hS i (by simp [hia, hi])
        · rw [MulAut.mul_apply, hu, sgnAut_apply]
          by_cases hia : i = a
          · subst hia
            simp [hεa]
          · rw [Function.update_of_ne hia, Function.update_of_ne hia]
      by_cases ha0 : a = i₀
      · subst ha0
        rcases h1 with h1 | h1
        · exact Or.inr h1
        · left
          rwa [mul_assoc, sgnAut_mul_self, mul_one] at h1
      · rcases h1 with h1 | h1
        · right
          have h2 := H.mul_mem h1 (hd a i₀ ha0)
          rwa [mul_assoc, ← mul_assoc (sgnAut a), sgnAut_mul_self, one_mul] at h2
        · left
          have h2 := H.mul_mem h1 (hd i₀ a (Ne.symm ha0))
          rwa [mul_assoc, ← mul_assoc (sgnAut i₀), sgnAut_mul_self, one_mul, mul_assoc,
            sgnAut_mul_self, mul_one] at h2

theorem mem_or_mul_mem_of_isSignedPerm {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (ht : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H) (i₀ : Fin k)
    {u : MulAut (Fin k → Multiplicative (ZMod p))} (hu : IsSignedPerm u) :
    u ∈ H ∨ u * sgnAut i₀ ∈ H := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := hu
  have key : ∀ (π : Equiv.Perm (Fin k)) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) → u ∈ H ∨ u * sgnAut i₀ ∈ H := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one =>
      intro u hu
      exact mem_or_mul_mem_of_diag hd i₀ Finset.univ u ε hε
        (fun i hi => absurd (Finset.mem_univ i) hi) fun f i => by simpa using hu f i
    | swap_mul π x y hxy ih =>
      intro u hu
      have h1 := ih ((permAut (Equiv.swap x y))⁻¹ * u) fun f i => by
        rw [MulAut.mul_apply, permAut_inv_apply, Function.comp_apply, ← Equiv.Perm.mul_apply]
        exact hu f i
      rcases h1 with h1 | h1
      · left
        have h2 := H.mul_mem (ht x y hxy) h1
        rwa [mul_inv_cancel_left] at h2
      · right
        have h2 := H.mul_mem (ht x y hxy) h1
        rwa [← mul_assoc, mul_inv_cancel_left] at h2
  exact key π u hu

theorem mem_of_diag_even {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H) (n : ℕ) :
    ∀ (S : Finset (Fin k)), S.card = 2 * n →
      ∀ (u : MulAut (Fin k → Multiplicative (ZMod p))) (ε : Fin k → ZMod p),
        (∀ i, i ∉ S → ε i = 1) → (∀ i, i ∈ S → ε i = -1) →
        (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ H := by
  classical
  induction n with
  | zero =>
    intro S hS u ε hε1 _ hu
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    have h1 : u = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [hu, hε1 i (by simp [hS0]), one_mul]
      rfl
    rw [h1]
    exact H.one_mem
  | succ n ih =>
    intro S hS u ε hε1 hεm hu
    obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb⟩ : (S.erase a).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem ha]
      omega)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb
    set S' := (S.erase a).erase b with hS'
    have hS'c : S'.card = 2 * n := by
      rw [hS', Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
      omega
    have h1 : u * (sgnAut a * sgnAut b) ∈ H := by
      refine ih S' hS'c _ (Function.update (Function.update ε a 1) b 1) (fun i hi => ?_)
        (fun i hi => ?_) (fun f i => ?_)
      · by_cases hib : i = b
        · subst hib
          simp
        · rw [Function.update_of_ne hib]
          by_cases hia : i = a
          · subst hia
            simp
          · rw [Function.update_of_ne hia]
            exact hε1 i (fun hiS => hi (by simp [hS', hia, hib, hiS]))
      · have hib : i ≠ b := fun h => by simp [hS', h] at hi
        have hia : i ≠ a := fun h => by simp [hS', h] at hi
        rw [Function.update_of_ne hib, Function.update_of_ne hia]
        exact hεm i (by simp [hS'] at hi; exact hi.2.2)
      · rw [MulAut.mul_apply, MulAut.mul_apply, hu, sgnAut_apply, sgnAut_apply]
        by_cases hib : i = b
        · rw [hib]
          simp [Function.update_of_ne hba, hεm b hbS]
        · by_cases hia : i = a
          · rw [hia]
            simp [Function.update_of_ne (Ne.symm hba), hεm a ha]
          · simp [Function.update_of_ne hib, Function.update_of_ne hia]
    have hX : (sgnAut a * sgnAut b : MulAut (Fin k → Multiplicative (ZMod p))) *
        (sgnAut a * sgnAut b) = 1 := by
      rw [show (sgnAut a * sgnAut b : MulAut (Fin k → Multiplicative (ZMod p))) *
          (sgnAut a * sgnAut b) = sgnAut a * (sgnAut b * sgnAut a) * sgnAut b by group,
        sgnAut_mul_comm b a, show (sgnAut a : MulAut (Fin k → Multiplicative (ZMod p))) *
          (sgnAut a * sgnAut b) * sgnAut b = sgnAut a * sgnAut a * (sgnAut b * sgnAut b) by group,
        sgnAut_mul_self, sgnAut_mul_self, one_mul]
    have h2 := H.mul_mem h1 (hd a b (Ne.symm hba))
    rwa [mul_assoc, hX, mul_one] at h2

theorem card_fix_conj {V : Type} [Group V] (s c : MulAut V) :
    Nat.card {f : V // (c * s * c⁻¹) f = f} = Nat.card {f : V // s f = f} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (c⁻¹ : MulAut V).toEquiv fun f => ?_)
  simp only [MulAut.mul_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  constructor
  · intro h
    have h1 := congrArg (c⁻¹ : MulAut V) h
    rwa [MulAut.inv_apply_self] at h1
  · intro h
    rw [h, MulAut.apply_inv_self]

theorem sgnTransp_eq {a b : Fin k} (hab : a ≠ b) :
    (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
        MulAut (Fin k → Multiplicative (ZMod p))) =
      sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ := by
  have hinv : ((sgnAut a)⁻¹ : MulAut (Fin k → Multiplicative (ZMod p))) = sgnAut a :=
    inv_eq_of_mul_eq_one_right (sgnAut_mul_self a)
  rw [hinv]
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp only [MulAut.mul_apply, sgnAut_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hja : j = a
  · rw [hja]
    simp [hab, Ne.symm hab]
  · by_cases hjb : j = b
    · rw [hjb]
      simp [hab, Ne.symm hab]
    · simp [Function.update_apply, hja, hjb, Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem sgnTransp_sq {a b : Fin k} (hab : a ≠ b) :
    (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
      MulAut (Fin k → Multiplicative (ZMod p))) ^ 2 = 1 := by
  rw [sgnTransp_eq hab, sq, show sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ *
      (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) =
      sgnAut a * (permAut (Equiv.swap a b) * permAut (Equiv.swap a b)) * (sgnAut a)⁻¹ by group,
    permAut_swap_mul_self, mul_one, mul_inv_cancel]

theorem card_fix_sgnTransp (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin k} (hab : a ≠ b) :
    Nat.card {f : Fin k → Multiplicative (ZMod p) //
        (sgnAut a * sgnAut b * permAut (Equiv.swap a b) :
          MulAut (Fin k → Multiplicative (ZMod p))) f = f} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
  rw [sgnTransp_eq hab, card_fix_conj]
  exact card_fix_permAut_swap hp hp2 hab

@[expose] def negAut : MulAut (Fin k → Multiplicative (ZMod p)) :=
  MulEquiv.inv (Fin k → Multiplicative (ZMod p))

theorem negAut_apply (f : Fin k → Multiplicative (ZMod p)) : negAut f = f⁻¹ :=
  rfl

theorem negAut_mul_comm (u : MulAut (Fin k → Multiplicative (ZMod p))) :
    negAut * u = u * negAut :=
  MulEquiv.ext fun f => by simp [negAut_apply, map_inv]

theorem negAut_mul_self : (negAut : MulAut (Fin k → Multiplicative (ZMod p))) * negAut = 1 :=
  MulEquiv.ext fun f => by simp [negAut_apply]

theorem isSignedPerm_mul_negAut {u : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : IsSignedPerm u) :
    IsSignedPerm ⇑(u * (negAut : MulAut (Fin k → Multiplicative (ZMod p)))) := by
  obtain ⟨π, ε, hε, hu⟩ := hu
  refine ⟨π, fun i => -ε i, fun i => ?_, fun f i => ?_⟩
  · rcases hε i with h | h
    · exact Or.inr (show -ε i = -1 by rw [h])
    · exact Or.inl (show -ε i = 1 by rw [h, neg_neg])
  rw [MulAut.mul_apply, negAut_apply, hu, toAdd_inv_apply]
  beta_reduce
  ring

theorem negAut_mul_sgnAut_mem {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p)))}
    (hd : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H) (hk : Odd k) (i₀ : Fin k) :
    negAut * sgnAut i₀ ∈ H := by
  classical
  obtain ⟨n, hn⟩ := hk
  refine mem_of_diag_even hd n (Finset.univ.erase i₀) (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega) _ (fun i => if i = i₀ then 1 else -1) (fun i hi => by simp_all)
    (fun i hi => by simp_all) fun f i => ?_
  rw [MulAut.mul_apply, negAut_apply, sgnAut_apply, toAdd_inv_apply]
  by_cases hi : i = i₀
  · subst hi
    simp
  · simp [hi]

end Coord

section Model

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_evenSignedPermModelSCOf {kP : ℕ → Prop} {εP : ∀ k : ℕ, (Fin k → ZMod p) → Prop}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSCOf p R kP εP) {L' : Type}
    [Group L'] [Finite L'] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 3 ≤ k ∧ kP k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i j : Fin k, i ≠ j → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAut σ)) ∧
      (∀ i j : Fin k, i ≠ j → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j * permAut (Equiv.swap i j))) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          εP k ε ∧ ∀ f i,
            toAdd ((MulAut.congr Θ).symm (ggConjAut A hn) f (π i)) = ε i * toAdd (f i) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  obtain ⟨k, τ, hτinj, hτE, hkP, hdinv, hperm, hnorm⟩ := h E hEab (hcardE ▸ h3) hscE
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : (Fin k → Multiplicative (ZMod p)) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  have hk : 3 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A :=
      Nat.card_congr Θ.toEquiv
    rw [hcV] at h1
    rw [← h1] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have hlift : ∀ (w : R) (α : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, w * τ f * w⁻¹ = τ (α f)) → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α := by
    intro w α hw
    obtain ⟨n, rfl⟩ := hψ w
    have hconjΘ : ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
        ((Θ (α f) : ↥A) : MulAut L') := by
      intro f
      rw [hΘval, hΘval, ← hΛn n, ← map_inv, ← map_mul, ← map_mul, hw f]
    have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have h1 := hconjΘ (α⁻¹ f)
      rw [MulAut.apply_inv_self, hf] at h1
      have h2 : a = MulAut.conj n * ((Θ (α⁻¹ f) : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ := h1.symm
      have e : (MulAut.conj n)⁻¹ * a * MulAut.conj n = ((Θ (α⁻¹ f) : ↥A) : MulAut L') := by
        rw [h2]
        group
      rw [e]
      exact (Θ _).2
    refine ⟨n, hn, MulEquiv.ext fun a => Subtype.ext ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [ggConjAut_apply, hconjΘ, MulAut.congr_apply]
    simp
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (hp.odd_of_ne_two hp2) τ
    fun i j => by
      obtain ⟨m, hmi, hmj⟩ := TableBSymp.exists_ne_ne_of_three_le hk i j
      obtain ⟨w, hw⟩ := hdinv i m (Ne.symm hmi)
      refine ⟨w, ?_, fun hji => ?_⟩
      · rw [TableBSymp.torusBasis, hw, dinv_mulSingle_self (Ne.symm hmi), map_inv]
      · rw [TableBSymp.torusBasis, hw, dinv_mulSingle_of_ne hji (Ne.symm hmj)]
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ n * τ f * (ψ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ n * τ f * (ψ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ n * τ f * (ψ n)⁻¹ ∈ τ.range := hτE ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨k, Θ, hk, hkP, fun n hn => ?_, fun i j hij => ?_, fun σ' => ?_, fun i j hij => ?_,
    fun n hn => ?_⟩
  ·
    have hform : ∀ f, ∃ g, ∃ z ∈ ψ.ker, z ^ p = 1 ∧
        n * (MulAut.conj (σ f) n)⁻¹ = σ g * z := by
      intro f
      obtain ⟨f', hf'⟩ := hNE n hn f
      set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
      have hzk : z ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hψσ, hψσ, hf',
          inv_mul_cancel]
      have hzc := Subgroup.mem_center_iff.mp (hker hzk)
      have hzp : z ^ p = 1 := by
        have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
          rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
        have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
        rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
          ReflInner.pow_eq_one_of_zmod, map_one, one_mul] at h1
        exact h1
      refine ⟨f' * f⁻¹, z, hzk, hzp, ?_⟩
      rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
      group
    intro a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have haσ : a = MulAut.conj (σ f) := by
      rw [← hΘσ, hf]
    obtain ⟨g, z, hzk, hzp, he⟩ := hform f
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    rw [haσ, he]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [(show Commute (σ g) z from hzc (σ g)).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul, hzp]
    · obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
      have ha'σ : a' = MulAut.conj (σ f'') := by
        rw [← hΘσ, hf'']
      rw [ha'σ, MulAut.conj_apply]
      calc σ f'' * (σ g * z) * (σ f'')⁻¹ = σ g * (σ f'' * z) * (σ f'')⁻¹ := by
            rw [← mul_assoc, hσc]; group
        _ = σ g * (z * σ f'') * (σ f'')⁻¹ := by rw [hzc]
        _ = σ g * z := by group
  · obtain ⟨w, hw⟩ := hdinv i j hij
    exact hlift w _ fun f => (hw f).trans rfl
  · obtain ⟨w, hw⟩ := hperm σ'
    exact hlift w _ hw
  · obtain ⟨w₁, hw₁⟩ := hdinv i j hij
    obtain ⟨w₂, hw₂⟩ := hperm (Equiv.swap i j)
    refine hlift (w₁ * w₂) _ fun f => ?_
    rw [show w₁ * w₂ * τ f * (w₁ * w₂)⁻¹ = w₁ * (w₂ * τ f * w₂⁻¹) * w₁⁻¹ by group, hw₂, hw₁]
    rfl
  ·
    have hNE' : ∀ e ∈ E, ψ n * e * (ψ n)⁻¹ ∈ E := by
      intro e he
      rw [← hτE] at he ⊢
      obtain ⟨f, rfl⟩ := he
      obtain ⟨f', hf'⟩ := hNE n hn f
      exact ⟨f', hf'.symm⟩
    obtain ⟨π, ε, hε, hεP, hrel⟩ := hnorm (ψ n) hNE'
    refine ⟨π, ε, hε, hεP, fun f i => hrel f _ ?_ i⟩
    apply hΛinj
    set u := (MulAut.congr Θ).symm (ggConjAut A hn) with hu
    have hu' : MulAut.congr Θ u = ggConjAut A hn := MulEquiv.apply_symm_apply _ _
    have h1 : ((ggConjAut A hn (Θ f) : ↥A) : MulAut L') = ((Θ (u f) : ↥A) : MulAut L') := by
      rw [← hu', MulAut.congr_apply]
      simp
    rw [← hΘval, ← h1, ggConjAut_apply, hΘval, map_mul, map_mul, map_inv, hΛn]

theorem exists_evenSignedPermModelSC {kP : ℕ → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R kP) {L' : Type} [Group L']
    [Finite L'] {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 3 ≤ k ∧ kP k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i j : Fin k, i ≠ j → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAut σ)) ∧
      (∀ i j : Fin k, i ≠ j → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j * permAut (Equiv.swap i j))) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)) := by
  obtain ⟨k, Θ, hk, hkP, hW, hd, hP, hsw, hN⟩ := exists_evenSignedPermModelSCOf hp hp2 hI hZ hcp
    (ggTorusEvenSignedPermEltSCOf_of_permEltSC h) hψ hker hperf hA hAI h3 hsc
  refine ⟨k, Θ, hk, hkP, hW, hd, hP, hsw, fun n hn => ?_⟩
  obtain ⟨π, ε, hε, -, hr⟩ := hN n hn
  exact ⟨π, ε, hε, hr⟩

end Model

end OrthExcEven

end CFSG.StandardType

end
