module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

@[simp] theorem tbjA_coe_tauOmega (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    (f : Fin r → Multiplicative (ZMod p)) :
    ((Δ.τΩ hA f : ↥(orthDerived Q)) : V ≃ₗ[K] V) = Δ.τ f :=
  rfl

theorem tbjA_tauOmega_injective (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q) :
    Function.Injective (Δ.τΩ hA) :=
  fun f g h => Δ.τ_inj (Subtype.ext_iff.mp h)

theorem tbjA_isSignedPerm_of_induced (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {J : Subgroup ↥(orthDerived Q)} {σ : MulAut (Fin r → Multiplicative (ZMod p))}
    (hσ : ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (σ f)) : IsSignedPerm (⇑σ) := by
  obtain ⟨n, -, hn⟩ := hσ
  have hcoe : ∀ f, (n : V ≃ₗ[K] V) * Δ.τ f * (n : V ≃ₗ[K] V)⁻¹ = Δ.τ (σ f) := fun f => by
    have h := congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[K] V)) (hn f)
    simpa using h
  have hAnorm : ∀ a ∈ A, (n : V ≃ₗ[K] V) * a * (n : V ≃ₗ[K] V)⁻¹ ∈ A := by
    intro a ha
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp (by rwa [← Δ.τ_range] at ha)
    exact (le_of_eq Δ.τ_range) (⟨σ f, (hcoe f).symm⟩ : (n : V ≃ₗ[K] V) * Δ.τ f *
      (n : V ≃ₗ[K] V)⁻¹ ∈ Δ.τ.range)
  obtain ⟨π, ε, hε, hπ⟩ := Δ.normalizer (n : V ≃ₗ[K] V) hAnorm
  exact ⟨π, ε, hε, fun f i => hπ f (σ f) (hcoe f) i⟩

@[simp] theorem tbjA_permAut_one :
    permAut (p := p) (1 : Equiv.Perm (Fin r)) = 1 := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp [permAut_apply]

@[simp] theorem tbjA_permAut_mul (σ τ : Equiv.Perm (Fin r)) :
    permAut (p := p) (σ * τ) = permAut σ * permAut τ := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp only [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.Perm.coe_mul,
    Equiv.Perm.mul_apply, mul_inv_rev]

theorem tbjA_eq_permAut_mul_diagAut {u : MulAut (Fin r → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin r)} {ε : Fin r → ZMod p} (hε : ∀ i, ε i * ε i = 1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) :
    u = permAut π * diagAut ε hε := by
  refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
  simp only [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.Perm.coe_inv,
    Equiv.symm_apply_apply, diagAut_apply, toAdd_ofAdd]
  exact hu f i

theorem tbjA_permAut_swap_mem (S : Finset (Fin r)) {a b : Fin r} (hab : a ≠ b) (ha : a ∈ S)
    (hb : b ∈ S) : permAut (p := p) (Equiv.swap a b) ∈ permSupportedAut r p S :=
  Subgroup.subset_closure ⟨a, ha, b, hb, hab, rfl⟩

theorem tbjA_permSupportedAut_le_signedSupportedAut (S : Finset (Fin r)) :
    permSupportedAut r p S ≤ signedSupportedAut r p S := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro u ⟨a, ha, b, hb, hab, rfl⟩
  exact Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩)

theorem tbjA_permSupportedAut_le_evenSignedSupportedAut (S : Finset (Fin r)) :
    permSupportedAut r p S ≤ evenSignedSupportedAut r p S := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro u ⟨a, ha, b, hb, hab, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨a, ha, b, hb, hab, rfl⟩)

theorem tbjA_permAut_mem_permSupportedAut_of_fixes (S : Finset (Fin r)) (π : Equiv.Perm (Fin r))
    (hπ : ∀ i ∉ S, π i = i) : permAut (p := p) π ∈ permSupportedAut r p S := by
  classical
  have hπsupp : ∀ x, π x ≠ x → x ∈ S := fun x hx => by
    by_contra h
    exact hx (hπ x h)
  have hπinv : ∀ x, π x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hxS
      by_contra h
      have h1 : π x = x := hπ x h
      exact h (by rwa [h1] at hxS)
    · intro hx
      by_contra h
      have h1 : π (π x) = π x := hπ (π x) h
      have h2 : π x = x := π.injective h1
      exact h (by rwa [← h2] at hx)
  have hπ' : π = Equiv.Perm.ofSubtype (π.subtypePerm hπinv) :=
    (Equiv.Perm.ofSubtype_subtypePerm hπinv hπsupp).symm
  rw [hπ']
  refine Equiv.Perm.swap_induction_on (π.subtypePerm hπinv) ?_ ?_
  · rw [map_one, tbjA_permAut_one]
    exact Subgroup.one_mem _
  · intro f x y hxy ih
    rw [map_mul, tbjA_permAut_mul]
    refine (permSupportedAut r p S).mul_mem ?_ ih
    rw [Equiv.Perm.ofSubtype_swap_eq]
    exact tbjA_permAut_swap_mem S (Subtype.coe_ne_coe.mpr hxy) x.2 y.2

theorem tbjA_signedSupportedAut_mono {S T : Finset (Fin r)} (hST : S ⊆ T) :
    signedSupportedAut r p S ≤ signedSupportedAut r p T := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro u (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨i, hST hi, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨a, hST ha, b, hST hb, hab, rfl⟩)

theorem tbjA_diagAut_mem_signedSupportedAut_of_support (S : Finset (Fin r))
    (ε : Fin r → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hεS : ∀ i ∉ S, ε i = 1) :
    diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈ signedSupportedAut r p S := by
  classical
  revert ε
  induction S using Finset.induction_on with
  | empty =>
    intro ε hε hεS
    have h1 : diagAut ε (fun i => coord_sign_mul_self (hε i)) = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
      rw [diagAut_apply, hεS j (Finset.notMem_empty j), one_mul, toAdd_ofAdd]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  | insert a S ha ih =>
    intro ε hε hεS
    by_cases hεa : ε a = 1
    · have hεS' : ∀ i ∉ S, ε i = 1 := fun i hi => by
        by_cases hia : i = a
        · subst hia; exact hεa
        · exact hεS i (by simp [hia, hi])
      exact tbjA_signedSupportedAut_mono (Finset.subset_insert a S) (ih ε hε hεS')
    · have hεa' : ε a = -1 := (hε a).resolve_left hεa
      have hε' : ∀ i, Function.update ε a 1 i = 1 ∨ Function.update ε a 1 i = -1 := by
        intro i
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact Or.inl rfl
        · rw [Function.update_of_ne hia]; exact hε i
      have hεS' : ∀ i ∉ S, Function.update ε a 1 i = 1 := by
        intro i hi
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]
        · rw [Function.update_of_ne hia]
          exact hεS i (by simp [hia, hi])
      have hdiag : diagAut ε (fun i => coord_sign_mul_self (hε i)) =
          sgnAut a * diagAut (Function.update ε a 1)
            (fun i => coord_sign_mul_self (hε' i)) := by
        refine MulEquiv.ext fun f => eq_of_toAdd_eq fun j => ?_
        rw [diagAut_apply, toAdd_ofAdd, MulAut.mul_apply, sgnAut_apply]
        by_cases hja : j = a
        · subst hja
          rw [Function.update_self, diagAut_apply, Function.update_self, toAdd_inv,
            toAdd_ofAdd, one_mul, hεa']
          ring
        · rw [Function.update_of_ne hja, diagAut_apply, Function.update_of_ne hja, toAdd_ofAdd]
      rw [hdiag]
      exact (signedSupportedAut r p (insert a S)).mul_mem
        (Subgroup.subset_closure (Or.inl ⟨a, Finset.mem_insert_self a S, rfl⟩))
        (tbjA_signedSupportedAut_mono (Finset.subset_insert a S)
          (ih (Function.update ε a 1) hε' hεS'))

theorem tbjA_mem_signedSupportedAut_of {u : MulAut (Fin r → Multiplicative (ZMod p))}
    (S : Finset (Fin r)) {π : Equiv.Perm (Fin r)} {ε : Fin r → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hπ : ∀ i ∉ S, π i = i) (hεS : ∀ i ∉ S, ε i = 1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) :
    u ∈ signedSupportedAut r p S := by
  have hperm : permAut π ∈ signedSupportedAut r p S :=
    tbjA_permSupportedAut_le_signedSupportedAut S
      (tbjA_permAut_mem_permSupportedAut_of_fixes S π hπ)
  have hdiag : diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈ signedSupportedAut r p S :=
    tbjA_diagAut_mem_signedSupportedAut_of_support S ε hε hεS
  rw [tbjA_eq_permAut_mul_diagAut (fun i => coord_sign_mul_self (hε i)) hu]
  exact (signedSupportedAut r p S).mul_mem hperm hdiag

theorem tbjA_diagAut_mul_self (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1) :
    diagAut s hs * diagAut s hs = 1 := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [MulAut.mul_apply, diagAut_apply, diagAut_apply, toAdd_ofAdd, toAdd_ofAdd,
    ← mul_assoc, hs i, one_mul]
  rfl

theorem tbjA_diagAut_inv (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1) :
    (diagAut s hs)⁻¹ = diagAut s hs :=
  inv_eq_of_mul_eq_one_right (tbjA_diagAut_mul_self s hs)

theorem tbjA_mem_of_diag_even_of_subset (S : Finset (Fin r)) (n : ℕ) :
    ∀ (T : Finset (Fin r)), T ⊆ S → T.card = 2 * n →
      ∀ (u : MulAut (Fin r → Multiplicative (ZMod p))) (ε : Fin r → ZMod p),
        (∀ i, i ∉ T → ε i = 1) → (∀ i, i ∈ T → ε i = -1) →
        (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ evenSignedSupportedAut r p S := by
  classical
  induction n with
  | zero =>
    intro T _ hT u ε hε1 _ hu
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    have h1 : u = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [hu, hε1 i (by simp [hT0]), one_mul]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro T hTS hT u ε hε1 hεm hu
    obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb⟩ : (T.erase a).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem ha]
      omega)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbT : b ∈ T := Finset.mem_of_mem_erase hb
    set T' := (T.erase a).erase b with hT'
    have hT'S : T' ⊆ S := by
      intro i hi
      exact hTS (by
        simp only [hT', Finset.mem_erase] at hi
        exact hi.2.2)
    have hT'c : T'.card = 2 * n := by
      rw [hT', Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
      omega
    have h1 : u * (sgnAut a * sgnAut b) ∈ evenSignedSupportedAut r p S := by
      refine ih T' hT'S hT'c _ (Function.update (Function.update ε a 1) b 1)
        (fun i hi => ?_) (fun i hi => ?_) (fun f i => ?_)
      · by_cases hib : i = b
        · subst hib
          rw [Function.update_self]
        · rw [Function.update_of_ne hib]
          by_cases hia : i = a
          · subst hia
            rw [Function.update_self]
          · rw [Function.update_of_ne hia]
            exact hε1 i (fun hiT => hi (by
              simp only [hT', Finset.mem_erase]
              exact ⟨hib, hia, hiT⟩))
      · have hib : i ≠ b := fun h => by simp [hT', h] at hi
        have hia : i ≠ a := fun h => by simp [hT', h] at hi
        rw [Function.update_of_ne hib, Function.update_of_ne hia]
        exact hεm i (by simp only [hT', Finset.mem_erase] at hi; exact hi.2.2)
      · rw [MulAut.mul_apply, MulAut.mul_apply, hu, sgnAut_apply, sgnAut_apply]
        by_cases hib : i = b
        · rw [hib]
          simp [Function.update_of_ne hba, hεm b hbT]
        · by_cases hia : i = a
          · rw [hia]
            simp [Function.update_of_ne (Ne.symm hba), hεm a ha]
          · simp [Function.update_of_ne hib, Function.update_of_ne hia]
    have hX : (sgnAut a * sgnAut b : MulAut (Fin r → Multiplicative (ZMod p))) *
        (sgnAut a * sgnAut b) = 1 := by
      rw [show (sgnAut a * sgnAut b : MulAut (Fin r → Multiplicative (ZMod p))) *
          (sgnAut a * sgnAut b) = sgnAut a * (sgnAut b * sgnAut a) * sgnAut b by group,
        sgnAut_mul_comm b a, show (sgnAut a : MulAut (Fin r → Multiplicative (ZMod p))) *
          (sgnAut a * sgnAut b) * sgnAut b = sgnAut a * sgnAut a * (sgnAut b * sgnAut b) by
          group,
        ← _root_.sq, ← _root_.sq, SpCoord.sgnAut_sq a, SpCoord.sgnAut_sq b, one_mul]
    have h2 := (evenSignedSupportedAut r p S).mul_mem h1
      (Subgroup.subset_closure (Or.inr ⟨a, hTS ha, b, hTS hbT, Ne.symm hba, rfl⟩))
    rwa [mul_assoc, hX, mul_one] at h2

theorem tbjA_mem_evenSignedSupportedAut_of [Fact p.Prime] (hp2 : p ≠ 2)
    {u : MulAut (Fin r → Multiplicative (ZMod p))} (S : Finset (Fin r))
    {π : Equiv.Perm (Fin r)} {ε : Fin r → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hπ : ∀ i ∉ S, π i = i) (hεS : ∀ i ∉ S, ε i = 1) (hprod : ∏ i, ε i = 1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) :
    u ∈ evenSignedSupportedAut r p S := by
  classical
  have hp : p.Prime := Fact.out
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 := coord_two_ne_zero hp hp2
    apply h2
    have h' := congrArg (fun x : ZMod p => x + 1) h
    simpa only [neg_add_cancel, ← two_mul, mul_one] using h'.symm
  have hperm : permAut π ∈ evenSignedSupportedAut r p S :=
    tbjA_permSupportedAut_le_evenSignedSupportedAut S
      (tbjA_permAut_mem_permSupportedAut_of_fixes S π hπ)
  have hdiag : diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈
      evenSignedSupportedAut r p S := by
    set T := Finset.univ.filter (fun i => ε i = -1) with hT
    have hTS : T ⊆ S := by
      intro i hi
      by_contra his
      have hi1 : ε i = -1 := (Finset.mem_filter.mp hi).2
      rw [hεS i his] at hi1
      exact (Ne.symm hneg) hi1
    have he : ∏ i, ε i = (-1 : ZMod p) ^ T.card := by
      have hc' : ε = fun i => if i ∈ T then (-1 : ZMod p) else 1 := by
        funext i
        by_cases hi : i ∈ T
        · rw [if_pos hi]
          exact (Finset.mem_filter.mp hi).2
        · rw [if_neg hi]
          exact (hε i).resolve_right (by simpa [hT] using hi)
      rw [hc', Finset.prod_ite_mem_eq, Finset.prod_const]
    obtain ⟨n, hn⟩ := (neg_one_pow_eq_one_iff_even hneg).mp (he.symm.trans hprod)
    exact tbjA_mem_of_diag_even_of_subset S n T hTS (show T.card = 2 * n by omega) _ ε
      (fun i hi => by_contra fun h1 => hi (by
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hε i).resolve_left h1))
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun f i => rfl)
  rw [tbjA_eq_permAut_mul_diagAut (fun i => coord_sign_mul_self (hε i)) hu]
  exact (evenSignedSupportedAut r p S).mul_mem hperm hdiag

theorem tbjA_mem_twistedPermAut_of [Fact p.Prime] {u : MulAut (Fin r → Multiplicative (ZMod p))}
    (S : Finset (Fin r)) (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1)
    {π : Equiv.Perm (Fin r)} {ε : Fin r → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hπ : ∀ i ∉ S, π i = i) (hεS : ∀ i ∉ S, ε i = 1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    {f₀ : Fin r → Multiplicative (ZMod p)} {c : ZMod p} (hc : c ≠ 0)
    (hf₀ : ∀ i ∈ S, toAdd (f₀ i) = c * s i)
    (hfix : ∀ i, toAdd (f₀ (π i)) = ε i * toAdd (f₀ i)) :
    u ∈ twistedPermAut r p S s hs := by
  classical
  have hπS : ∀ i ∈ S, π i ∈ S := by
    intro i hi
    by_contra h
    have h1 : π (π i) = π i := hπ (π i) h
    have h2 : π i = i := π.injective h1
    exact h (by rw [h2]; exact hi)
  have hεs : ∀ i ∈ S, ε i = s (π i) * s i := by
    intro i hi
    have h1 := hfix i
    rw [hf₀ (π i) (hπS i hi), hf₀ i hi] at h1
    have h2 : s (π i) = ε i * s i := by
      apply mul_left_cancel₀ hc
      calc c * s (π i) = ε i * (c * s i) := h1
        _ = c * (ε i * s i) := by ring
    calc ε i = ε i * (s i * s i) := by rw [hs i, mul_one]
      _ = (ε i * s i) * s i := by ring
      _ = s (π i) * s i := by rw [← h2]
  let g : MulAut (Fin r → Multiplicative (ZMod p)) := diagAut s hs
  have hg : g⁻¹ = g := tbjA_diagAut_inv s hs
  have hv : g * u * g⁻¹ = permAut π := by
    refine MulEquiv.ext fun f => eq_of_toAdd_perm_eq π fun i => ?_
    rw [permAut_apply, Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    have hmain : s (π i) * (ε i * (s i * toAdd (f i))) = toAdd (f i) := by
      by_cases hi : i ∈ S
      · calc s (π i) * (ε i * (s i * toAdd (f i)))
            = s (π i) * ((s (π i) * s i) * (s i * toAdd (f i))) := by rw [hεs i hi]
          _ = (s (π i) * s (π i)) * (s i * s i) * toAdd (f i) := by ring
          _ = toAdd (f i) := by rw [hs (π i), hs i, one_mul, one_mul]
      · calc s (π i) * (ε i * (s i * toAdd (f i)))
            = s i * (1 * (s i * toAdd (f i))) := by rw [hπ i hi, hεS i hi]
          _ = (s i * s i) * toAdd (f i) := by ring
          _ = toAdd (f i) := by rw [hs i, one_mul]
    calc toAdd ((g * u * g⁻¹) f (π i))
        = s (π i) * (ε i * (s i * toAdd (f i))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, hg, diagAut_apply, toAdd_ofAdd,
            hu (g f) i, diagAut_apply, toAdd_ofAdd]
      _ = toAdd (f i) := hmain
  have hperm : permAut π ∈ permSupportedAut r p S :=
    tbjA_permAut_mem_permSupportedAut_of_fixes S π hπ
  have hu_eq : u = g⁻¹ * permAut π * g := by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * permAut π * g := by rw [hv]
  refine (Subgroup.mem_map).mpr ⟨permAut π, hperm, ?_⟩
  change g * permAut π * g⁻¹ = u
  rw [hu_eq, hg]

theorem tbjA_exists_mem_of_card_centralizer_le {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (P : Fin r → Prop)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ i, P i := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  have hcount' : p ^ 2 * Nat.card {f // f ∈ C} ≤ p ^ r := hcount
  by_contra hPempty
  have hPfalse : ∀ i, ¬P i := fun i hi => hPempty ⟨i, hi⟩
  have huniv : ∀ f : Fin r → Multiplicative (ZMod p), f ∈ C := by
    intro f
    exact hcent f ⟨0, fun i hi => absurd hi (hPfalse i)⟩
  have hle1 : Nat.card (Fin r → Multiplicative (ZMod p)) ≤ Nat.card {f // f ∈ C} :=
    Nat.card_le_card_of_injective (fun f => ⟨f, huniv f⟩)
      (fun a b hab => Subtype.ext_iff.mp hab)
  have hle2 : Nat.card {f // f ∈ C} ≤ Nat.card (Fin r → Multiplicative (ZMod p)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcardC : Nat.card {f // f ∈ C} = p ^ r := by
    rw [← ggTBJSpC_card_coord p r]
    exact le_antisymm hle2 hle1
  rw [hcardC] at hcount'
  have hpm_pos : 0 < p ^ r := pow_pos hp.pos r
  have hle : p ^ 2 ≤ 1 := Nat.le_of_mul_le_mul_right (by
    calc p ^ 2 * p ^ r ≤ p ^ r := hcount'
      _ = 1 * p ^ r := by ring) hpm_pos
  have hp2' : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  omega

theorem tbjA_le_card_of_pow_le {p r n : ℕ} (hp : p.Prime) {I : Finset (Fin r)}
    (hI : I.card ≤ r) (h : p ^ (n + (r - I.card)) ≤ p ^ r) : n ≤ I.card := by
  have h' := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  omega

theorem tbjA_le_card_class_of_centralizer {p r k : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (P : Fin r → Prop)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ k * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    k ≤ Nat.card {i : Fin r // P i} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount_le : ∀ f : Fin r → Multiplicative (ZMod p),
      (∀ i, P i → f i = 1) → f ∈ C := by
    intro f hf
    exact hcent f ⟨0, fun i hi => by rw [hf i hi, zero_mul, toAdd_one]⟩
  let e : ({i // i ∉ I} → Multiplicative (ZMod p)) → {f // f ∈ C} :=
    fun g => ⟨fun i => if h : i ∈ I then 1 else g ⟨i, h⟩, hcount_le _ (by
      intro i hi
      have hmem : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      simp [hmem])⟩
  have he : Function.Injective e := by
    intro g g' hgg
    funext x
    simpa [e, x.2] using congrFun (congrArg Subtype.val hgg) x.1
  have hcard2 : Nat.card ({i // i ∉ I} → Multiplicative (ZMod p)) = p ^ (r - I.card) := by
    rw [Nat.card_fun, ggTBJSpC_card_subtype_notMem,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  have hcard1 : p ^ (r - I.card) ≤ Nat.card {f // f ∈ C} := by
    rw [← hcard2]
    exact Nat.card_le_card_of_injective e he
  have hle : p ^ (k + (r - I.card)) ≤ p ^ r := by
    rw [pow_add]
    exact (Nat.mul_le_mul_left _ hcard1).trans hcount
  rw [hcardI]
  exact tbjA_le_card_of_pow_le hp (by simpa using Finset.card_le_univ I) hle

theorem tbjA_two_le_card_class_of_centralizer {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (P : Fin r → Prop)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    2 ≤ Nat.card {i : Fin r // P i} :=
  tbjA_le_card_class_of_centralizer hp τ f₀ J P hcent hcount

theorem tbjA_exists_coord_ne_zero_of_ne_zero {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ i, P i ∧ toAdd (f₀ i) ≠ 0 := by
  obtain ⟨i₀, hi₀P⟩ := tbjA_exists_mem_of_card_centralizer_le hp τ f₀ J P hcent hcount
  refine ⟨i₀, hi₀P, ?_⟩
  rcases hP i₀ hi₀P with h | h
  · rwa [h]
  · rw [h]
    exact neg_ne_zero.mpr ha

theorem tbjA_three_le_card_class_of_ne_zero {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    3 ≤ Nat.card {i : Fin r // P i} := by
  classical
  haveI : Fact p.Prime := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨i₀, hi₀P, ht₀⟩ :=
    tbjA_exists_coord_ne_zero_of_ne_zero hp τ f₀ J a P ha hP hcent hcount
  have hi₀ : i₀ ∈ I := by simpa [I] using hi₀P
  let e : ZMod p × ({i // i ∉ I} → Multiplicative (ZMod p)) → {f // f ∈ C} :=
    fun cg => ⟨fun i => if h : i ∈ I then ofAdd (cg.1 * toAdd (f₀ i)) else cg.2 ⟨i, h⟩,
      hcent _ ⟨cg.1, fun i hi => by simp [show i ∈ I by simpa [I] using hi]⟩⟩
  have hcard2 : Nat.card (ZMod p × ({i // i ∉ I} → Multiplicative (ZMod p))) =
      p ^ (1 + (r - I.card)) := by
    rw [Nat.card_prod, Nat.card_fun, ggTBJSpC_card_subtype_notMem,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_zmod, pow_add, pow_one]
  have hcard1 : p ^ (1 + (r - I.card)) ≤ Nat.card {f // f ∈ C} := by
    rw [← hcard2]
    refine Nat.card_le_card_of_injective e ?_
    rintro ⟨m, g⟩ ⟨m', g'⟩ hgg
    have h1 := congrFun (congrArg Subtype.val hgg)
    have hm : m = m' := mul_right_cancel₀ ht₀ (by
      simpa [e, hi₀] using congrArg Multiplicative.toAdd (h1 i₀))
    have hg : g = g' := by
      funext x
      simpa [e, x.2] using h1 x.1
    rw [hm, hg]
  have hle : p ^ (3 + (r - I.card)) ≤ p ^ r := by
    rw [show 3 + (r - I.card) = 2 + (1 + (r - I.card)) by omega, pow_add]
    exact (Nat.mul_le_mul_left _ hcard1).trans hcount
  rw [hcardI]
  exact tbjA_le_card_of_pow_le hp (by simpa using Finset.card_le_univ I) hle

theorem tbjA_fixed_of_mem_signedSupportedAut [Fact p.Prime] (hp2 : p ≠ 2) {S : Finset (Fin r)}
    {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ σ ∈ signedSupportedAut r p S, σ f = f) :
    ∀ i ∈ S, f i = 1 := by
  intro i hi
  have h := hf (sgnAut i) (Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩))
  have h1 : toAdd (f i) = -toAdd (f i) := by
    have h2 : (f i)⁻¹ = f i := by
      have h3 := congrFun h i
      simpa [sgnAut_apply] using h3
    rw [← toAdd_inv, h2]
  have h0 : toAdd (f i) = 0 :=
    coord_eq_zero_of_eq_neg (Fact.out : p.Prime) hp2 h1
  rw [← ofAdd_toAdd (f i), h0, ofAdd_zero]

theorem tbjA_fixed_of_mem_evenSignedSupportedAut [Fact p.Prime] (hp2 : p ≠ 2) {S : Finset (Fin r)}
    (hS : 2 ≤ S.card) {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ σ ∈ evenSignedSupportedAut r p S, σ f = f) :
    ∀ i ∈ S, f i = 1 := by
  intro i hi
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hk : ∃ k ∈ S, k ≠ i := by
    rcases eq_or_ne x i with rfl | hxi
    · exact ⟨y, hy, Ne.symm hxy⟩
    · exact ⟨x, hx, hxi⟩
  obtain ⟨k, hkS, hki⟩ := hk
  have hmem : (sgnAut i * sgnAut k : MulAut (Fin r → Multiplicative (ZMod p))) ∈
      evenSignedSupportedAut r p S :=
    Subgroup.subset_closure (Or.inr ⟨i, hi, k, hkS, Ne.symm hki, rfl⟩)
  have h := hf _ hmem
  have h1 : toAdd (f i) = -toAdd (f i) := by
    have h2 : (f i)⁻¹ = f i := by
      have h3 := congrFun h i
      simpa [MulAut.mul_apply, sgnAut_apply, Function.update_of_ne (Ne.symm hki)] using h3
    rw [← toAdd_inv, h2]
  have h0 : toAdd (f i) = 0 :=
    coord_eq_zero_of_eq_neg (Fact.out : p.Prime) hp2 h1
  rw [← ofAdd_toAdd (f i), h0, ofAdd_zero]

theorem tbjA_conj_diag_permAut_swap_toAdd (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1)
    {i k : Fin r} (hik : i ≠ k) (f : Fin r → Multiplicative (ZMod p)) :
    toAdd ((MulAut.conj (diagAut s hs : MulAut (Fin r → Multiplicative (ZMod p))))
      (permAut (Equiv.swap i k)) f i) = s i * s k * toAdd (f k) := by
  simp only [MulAut.conj_apply, MulAut.mul_apply, tbjA_diagAut_inv, diagAut_apply,
    permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left, toAdd_ofAdd,
    mul_assoc]

theorem tbjA_fixed_of_mem_twistedPermAut {S : Finset (Fin r)} (s : Fin r → ZMod p)
    (hs : ∀ i, s i * s i = 1) {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ σ ∈ twistedPermAut r p S s hs, σ f = f) :
    ∃ m : ZMod p, ∀ i ∈ S, toAdd (f i) = m * s i := by
  classical
  by_cases hS : S = ∅
  · subst hS
    exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    refine ⟨toAdd (f i₀) * s i₀, fun i hi => ?_⟩
    by_cases hii : i = i₀
    · rw [hii, mul_assoc, hs i₀, mul_one]
    · have hperm : permAut (Equiv.swap i i₀) ∈ permSupportedAut r p S :=
        tbjA_permAut_swap_mem S hii hi hi₀
      have hmem : MulAut.conj (diagAut s hs : MulAut (Fin r → Multiplicative (ZMod p)))
          (permAut (Equiv.swap i i₀)) ∈ twistedPermAut r p S s hs :=
        Subgroup.mem_map.mpr ⟨permAut (Equiv.swap i i₀), hperm, rfl⟩
      have hfix := hf _ hmem
      have hcoord : s i * s i₀ * toAdd (f i₀) = toAdd (f i) := by
        have h1 := congrArg (fun x : Multiplicative (ZMod p) => toAdd x) (congrFun hfix i)
        rw [tbjA_conj_diag_permAut_swap_toAdd s hs hii] at h1
        exact h1
      rw [← hcoord]
      ring

end OrthTorus

end CFSG.StandardType

end
