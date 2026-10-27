module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H14
public import CFSG.Quasithin.Vol2.Ch10SecQ9H12
public import CFSG.Quasithin.Vol2.Ch10SecQ9H13
public import CFSG.Quasithin.Vol2.Ch10SecQ9H9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.QuasithinUnique

theorem fixSet_iff {A : Subgroup SL4} {x : SL4} (hx : x ∈ Subgroup.normalizer (A : Set SL4))
    (v : Fin 4 → ZMod 2) : v ∈ fixSet A ↔ x • v ∈ fixSet A := by
  refine ⟨smul_mem_fixSet hx, fun h => ?_⟩
  have := smul_mem_fixSet (Subgroup.inv_mem _ hx) h
  rwa [inv_smul_smul] at this

theorem exists_fixed_of_card_two {W : AddSubgroup (Fin 4 → ZMod 2)} (hW : Nat.card W = 2) :
    ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ ∀ g : SL4, (∀ w, w ∈ W ↔ g • w ∈ W) → g • v = v := by
  obtain ⟨⟨v, hv⟩, hv0⟩ : ∃ x : ↥W, x ≠ 0 := by
    by_contra hc
    have hsub : Subsingleton ↥W := ⟨fun a b => by
      by_contra hab
      apply hc
      by_cases ha : a = 0
      · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  refine ⟨v, hv0', fun g hg => ?_⟩
  have hgv : g • v ∈ W := (hg v).mp hv
  have hgv0 : g • v ≠ 0 := mulVec_ne_zero g hv0'
  by_contra hne
  have h3 : 3 ≤ Nat.card W := by
    have hinj : Function.Injective (fun i : Fin 3 => match i with
        | 0 => (0 : ↥W) | 1 => (⟨v, hv⟩ : ↥W) | 2 => (⟨g • v, hgv⟩ : ↥W)) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp only at hij ⊢ <;>
        first
        | rfl
        | (exfalso
           have h' := congrArg Subtype.val hij
           simp only [ZeroMemClass.coe_zero] at h'
           first
           | exact hv0' h'.symm
           | exact hv0' h'
           | exact hgv0 h'.symm
           | exact hgv0 h'
           | exact hne h'.symm
           | exact hne h')
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin] at this
  omega

theorem factL4Aut_holds : FactL4Aut := by
  intro X S hS hSX _ hq α hαX
  obtain ⟨e⟩ := hq
  have hS64 := card_eq_64_of_sylow hS
  have hcard := card_X_eq X e
  have hOmax := fun N (hNX : N ≤ X) (hN : X ≤ Subgroup.normalizer (N : Set SL4))
    (hp : IsPGroup 2 N) => le_o2Of X hNX hN hp
  obtain ⟨k, hkX, hk⟩ : ∃ k ∈ X, orderOf k = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 7
      (by rw [hcard]; exact Dvd.dvd.mul_left (by norm_num) _)
    exact ⟨k, k.2, by rw [← hk, Subgroup.orderOf_coe]⟩
  obtain ⟨A, hAp, hA1, hXA, hSA⟩ : ∃ A : Subgroup SL4, IsPGroup 2 A ∧ A ≠ ⊥ ∧
      X ≤ Subgroup.normalizer (A : Set SL4) ∧ S ≤ Subgroup.normalizer (A : Set SL4) := by
    by_cases hO : o2Of X = ⊥
    · have hP : CFSG.pCore 2 ↥X = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (x : SL4) ∈ o2Of X := ⟨x, hx, rfl⟩
        rw [hO, Subgroup.mem_bot] at this
        exact Subtype.ext this
      have e' : ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
        ((QuotientGroup.quotientMulEquivOfEq hP).trans (QuotientGroup.quotientBot)).symm.trans e
      refine ⟨S ⊓ Subgroup.centralizer (X : Set SL4), hS.2.1.to_le inf_le_left,
        inf_centralizer_ne_bot hS64 hSX e', fun x hx => ?_, fun s hs => ?_⟩
      · rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          have hxa : x * a = a * x := (Subgroup.mem_centralizer_iff.mp ha.2 x hx)
          rw [hxa, mul_inv_cancel_right]
          exact ha
        · intro ha
          have hxa : x * (x * a * x⁻¹) = (x * a * x⁻¹) * x :=
            Subgroup.mem_centralizer_iff.mp ha.2 x hx
          have h2 : x * (x * a * x⁻¹) = x * a := by rw [hxa]; group
          have h3 : x * a * x⁻¹ = a := mul_left_cancel h2
          rw [h3] at ha
          exact ha
      · rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · rintro ⟨haS, haC⟩
          refine ⟨S.mul_mem (S.mul_mem hs haS) (S.inv_mem hs), ?_⟩
          show s * a * s⁻¹ ∈ Subgroup.centralizer (X : Set SL4)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : s⁻¹ * y * s ∈ X := by
            have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSX hs)) y).mp hy
            rwa [inv_inv] at this
          have h1 := Subgroup.mem_centralizer_iff.mp haC _ hy'
          calc y * (s * a * s⁻¹) = s * ((s⁻¹ * y * s) * a) * s⁻¹ := by group
            _ = s * (a * (s⁻¹ * y * s)) * s⁻¹ := by rw [h1]
            _ = s * a * s⁻¹ * y := by group
        · rintro ⟨haS, haC⟩
          have hS' : a ∈ S := by
            have := S.mul_mem (S.mul_mem (S.inv_mem hs) haS) hs
            rwa [show s⁻¹ * (s * a * s⁻¹) * s = a by group] at this
          refine ⟨hS', ?_⟩
          show a ∈ Subgroup.centralizer (X : Set SL4)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : s * y * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hSX hs) y).mp hy
          have h1 := Subgroup.mem_centralizer_iff.mp haC _ hy'
          calc y * a = s⁻¹ * ((s * y * s⁻¹) * (s * a * s⁻¹)) * s := by group
            _ = s⁻¹ * ((s * a * s⁻¹) * (s * y * s⁻¹)) * s := by rw [h1]
            _ = a * y := by group
    · exact ⟨o2Of X, isPGroup_o2Of X, hO, le_normalizer_o2Of X, le_normalizer_o2Of_of hSX⟩
  have hinvX : ∀ x ∈ X, ∀ v, v ∈ fixSet A ↔ x • v ∈ fixSet A := fun x hx => fixSet_iff (hXA hx)
  have hinvS : ∀ s ∈ S, ∀ v, v ∈ fixSet A ↔ s • v ∈ fixSet A := fun s hs => fixSet_iff (hSA hs)
  rcases card_fixSet_cases hAp hA1 with h2 | h4 | h8
  ·
    obtain ⟨v, hv0, hfix⟩ := exists_fixed_of_card_two h2
    have hXv : X ≤ stabV v := fun x hx => MulAction.mem_stabilizer_iff.mpr (hfix x (hinvX x hx))
    have hSv : S ≤ stabV v := fun s hs => MulAction.mem_stabilizer_iff.mpr (hfix s (hinvS s hs))
    have hXeq := eq_stabV_of_le hv0 hXv hSv hS64 hSX hcard hOmax
    obtain ⟨g, hg, hgα⟩ := eq_conj_of_stabV hv0 α (fun x hx => by
      rw [← hXeq] at hx ⊢
      exact hαX x hx)
    exact ⟨g, hXeq ▸ hg, fun x _ => hgα x⟩
  · exact (false_of_card_four hk h4 (hinvX k hkX)).elim
  ·
    obtain ⟨u, hu0, hW⟩ := exists_hyperplane h8
    have hpres : ∀ g : SL4, (∀ w, w ∈ fixSet A ↔ g • w ∈ fixSet A) →
        u ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = u := fun g hg =>
      vecMul_eq_of_preserves fun x => by
        rw [← hW, ← hW]
        exact hg x
    obtain ⟨τ, hτ⟩ : ∃ τ : MulAut SL4, τ = tInv 4 := ⟨_, rfl⟩
    have hτu : ∀ g : SL4, u ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = u → τ g ∈ stabV u :=
      fun g hg => hτ ▸ tInv_mem_stabV hg
    set X' := X.map τ.toMonoidHom with hX'
    set S' := S.map τ.toMonoidHom with hS'
    set O' := (o2Of X).map τ.toMonoidHom with hO'
    have hmem : ∀ {H : Subgroup SL4} {y : SL4}, y ∈ H.map τ.toMonoidHom ↔ τ.symm y ∈ H :=
      fun {H y} => Subgroup.mem_map_equiv
    have hX'u : X' ≤ stabV u := by
      rintro _ ⟨x, hx, rfl⟩
      exact hτu x (hpres x (hinvX x hx))
    have hS'u : S' ≤ stabV u := by
      rintro _ ⟨s, hs, rfl⟩
      exact hτu s (hpres s (hinvS s hs))
    have hS'64 : Nat.card S' = 64 := by
      rw [hS', Subgroup.card_map_of_injective τ.injective, hS64]
    have hS'X' : S' ≤ Subgroup.normalizer (X' : Set SL4) := by
      intro s' hs'
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmem, hmem, map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp (hSX (hmem.mp hs')) _
    have hcard' : Nat.card X' = Nat.card O' * 168 := by
      rw [hX', hO', Subgroup.card_map_of_injective τ.injective,
        Subgroup.card_map_of_injective τ.injective, hcard]
    have hOmax' : ∀ N : Subgroup SL4, N ≤ X' → X' ≤ Subgroup.normalizer (N : Set SL4) →
        IsPGroup 2 N → N ≤ O' := by
      intro N hNX hN hp y hy
      rw [hmem]
      refine hOmax (N.map τ.symm.toMonoidHom) ?_ ?_ (hp.map _) ⟨y, hy, rfl⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact hmem.mp (hNX hz)
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have hx' : τ x ∈ X' := ⟨x, hx, rfl⟩
        have h1 := Subgroup.mem_normalizer_iff.mp (hN hx') (τ z)
        simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at h1 ⊢
        rw [← map_inv, ← map_mul, ← map_mul] at h1
        exact h1
    have hXeq := eq_stabV_of_le hu0 hX'u hS'u hS'64 hS'X' hcard' hOmax'
    obtain ⟨g', hg', hgα'⟩ := eq_conj_of_stabV hu0 (τ * α * τ⁻¹) (fun y hy => by
      rw [← hXeq] at hy ⊢
      show τ (α (τ.symm y)) ∈ X'
      exact ⟨α (τ.symm y), hαX _ (hmem.mp hy), rfl⟩)
    have hg'X : g' ∈ X' := by rw [hXeq]; exact hg'
    refine ⟨τ.symm g', hmem.mp hg'X, fun x _ => ?_⟩
    have h1 : τ (α x) = g' * τ x * g'⁻¹ := by
      have h2 := hgα' (τ x)
      rwa [show (τ * α * τ⁻¹) (τ x) = τ (α x) from congrArg τ (congrArg α
        (τ.symm_apply_apply x))] at h2
    calc α x = τ.symm (τ (α x)) := (τ.symm_apply_apply _).symm
      _ = τ.symm g' * x * (τ.symm g')⁻¹ := by
        rw [h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
