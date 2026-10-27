module

public import CFSG.Quasithin.H13.A5W1622l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup

private theorem c23ne_subgroup_eq_top_of_singles
    {S : Subgroup (Multiplicative (Fin 3 → ZMod 2))}
    (h : ∀ i : Fin 3, Multiplicative.ofAdd (Pi.single i 1) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective y
  have hx : (∑ i : Fin 3, Pi.single i (x i)) = x := by
    funext j
    simpa using Finset.sum_pi_single j x
  rw [← hx]
  change (∏ i : Fin 3, Multiplicative.ofAdd (Pi.single i (x i))) ∈ S
  refine Subgroup.prod_mem S (t := Finset.univ) (fun i _ => ?_)
  have hx01 : ∀ (i : Fin 3) (x : Fin 3 → ZMod 2), x i = 0 ∨ x i = 1 := by
    decide
  rcases hx01 i x with h0 | h1
  · rw [h0]
    simp only [Pi.single_zero, ofAdd_zero]
    exact S.one_mem
  · rw [h1]
    exact h i

private theorem c23ne_commSub_le_of_natQuot {A : Type} [CommGroup A]
    {H : Subgroup (MulAut A)} {P Z : Subgroup A} (D : NatQuot3 H P Z) :
    commSub P H ≤ P := by
  apply commSub_le_of_invariant
  intro k hk p hp
  obtain ⟨g, hg⟩ := D.surj ⟨k, hk⟩
  have hgk : ((D.ρ g : ↥H) : MulAut A) = k := congrArg Subtype.val hg
  rw [← hgk]
  exact D.inv g p hp

theorem c23ne_natQuot3_of_hom {A' A : Type} [CommGroup A'] [CommGroup A]
    {H' : Subgroup (MulAut A')} {H : Subgroup (MulAut A)} {U : Subgroup A} (f : A' →* A)
    (hf : Function.Surjective f) (ρ : ↥H' ≃* ↥H)
    (hρ : ∀ (a : ↥H') (y : A'),
      f ((a : MulAut A') y) = ((ρ a : ↥H) : MulAut A) (f y))
    (h : Nonempty (NatQuot3 H U ⊥)) :
    Nonempty (NatQuot3 H' (U.comap f) f.ker) := by
  obtain ⟨D⟩ := h
  let ρ' : SL3F2 →* ↥H' := ρ.symm.toMonoidHom.comp D.ρ
  let g : ↥(U.comap f) →* ↥U :=
    (f.comp (U.comap f).subtype).codRestrict U (fun x => x.2)
  let invF : ∀ (k : SL3F2) (u : A'), u ∈ U.comap f →
      ((ρ' k : ↥H') : MulAut A') u ∈ U.comap f := fun k u hu => by
    show f (((ρ.symm (D.ρ k) : ↥H') : MulAut A') u) ∈ U
    rw [hρ (ρ.symm (D.ρ k)) u, MulEquiv.apply_symm_apply]
    exact D.inv k (f u) hu
  refine ⟨{ ρ := ρ'
            surj := fun a => ?_
            inj := fun a b hab => ?_
            θ := D.θ.comp g
            θ_surj := fun x => ?_
            θ_ker := fun u => ?_
            inv := invF
            equiv := fun k u => ?_ }⟩
  · obtain ⟨k, hk⟩ := D.surj (ρ a)
    exact ⟨k, by
      show ρ.symm (D.ρ k) = a
      rw [hk, MulEquiv.symm_apply_apply]⟩
  · exact D.inj (ρ.symm.injective (by simpa [ρ'] using hab))
  · obtain ⟨u, hu⟩ := D.θ_surj x
    obtain ⟨a, ha⟩ := hf (u : A)
    have haU : a ∈ U.comap f := by
      show f a ∈ U
      rw [ha]
      exact u.2
    refine ⟨⟨a, haU⟩, ?_⟩
    have hgu : g ⟨a, haU⟩ = u := Subtype.ext ha
    show D.θ (g ⟨a, haU⟩) = x
    rw [hgu, hu]
  · have hval : ((g u : ↥U) : A) = f (u : A') := rfl
    change D.θ (g u) = 1 ↔ (u : A') ∈ f.ker
    rw [D.θ_ker, Subgroup.mem_bot, MonoidHom.mem_ker, hval]
  · have h1 : f (((ρ.symm (D.ρ k) : ↥H') : MulAut A') (u : A')) =
        ((D.ρ k : ↥H) : MulAut A) (f (u : A')) := by
      simpa using hρ (ρ.symm (D.ρ k)) (u : A')
    have hq : f (u : A') ∈ U := u.2
    have harg : g ⟨((ρ' k : ↥H') : MulAut A') (u : A'), invF k u u.2⟩ =
        ⟨((D.ρ k : ↥H) : MulAut A) (f (u : A')), D.inv k (f (u : A')) hq⟩ :=
      Subtype.ext h1
    have hgu : g u = ⟨f (u : A'), hq⟩ := Subtype.ext rfl
    show D.θ (g ⟨((ρ' k : ↥H') : MulAut A') (u : A'), invF k u u.2⟩) =
      Multiplicative.ofAdd (k • Multiplicative.toAdd (D.θ (g u)))
    rw [harg, hgu, D.equiv k ⟨f (u : A'), hq⟩]

theorem c23ne_fix_eq_bot_of_natQuot {A : Type} [CommGroup A] {H : Subgroup (MulAut A)}
    {W : Subgroup A} (h : Nonempty (NatQuot3 H W ⊥)) : W ⊓ fixV H = ⊥ := by
  obtain ⟨D⟩ := h
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwW, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hθ : D.θ ⟨w, hwW⟩ = 1 := by
    have hv : Multiplicative.toAdd (D.θ ⟨w, hwW⟩) = 0 := by
      apply CFSG.Quasithin.H13.A5.fixed_eq_zero_of_sl3
      intro g
      have hthis := D.equiv g ⟨w, hwW⟩
      have hfix := hwfix ((D.ρ g : ↥H) : MulAut A) (D.ρ g).2
      have heq : D.θ ⟨((D.ρ g : ↥H) : MulAut A) w, D.inv g w hwW⟩ =
          D.θ ⟨w, hwW⟩ := by
        congr 1
        exact Subtype.ext hfix
      rw [heq] at hthis
      apply Multiplicative.ofAdd.injective
      show Multiplicative.ofAdd (g • Multiplicative.toAdd (D.θ ⟨w, hwW⟩)) =
        D.θ ⟨w, hwW⟩
      exact hthis.symm
    change Multiplicative.ofAdd (Multiplicative.toAdd (D.θ ⟨w, hwW⟩)) = 1
    rw [hv, ofAdd_zero]
  exact Subgroup.mem_bot.1 ((D.θ_ker ⟨w, hwW⟩).1 hθ)

theorem c23ne_cross_centralizes {A : Type*} [CommGroup A] {K : Subgroup (MulAut A)}
    {P Z : Subgroup A} (hK : ⁅K, K⁆ = K)
    (hPZ : ∀ k ∈ K, ∀ p ∈ P, (k : MulAut A) p * p⁻¹ ∈ Z)
    (hZ : ∀ k ∈ K, ∀ z ∈ Z, (k : MulAut A) z = z) :
    ∀ k ∈ K, ∀ p ∈ P, (k : MulAut A) p = p := by
  intro k hk p hp
  let φ : ↥K →* A :=
    { toFun := fun k => (k : MulAut A) p * p⁻¹,
      map_one' := by simp,
      map_mul' := fun a b => by
        have hbZ : (b : MulAut A) p * p⁻¹ ∈ Z := hPZ b b.2 p hp
        have hafix : (a : MulAut A) ((b : MulAut A) p * p⁻¹) =
            (b : MulAut A) p * p⁻¹ := hZ a a.2 _ hbZ
        have h1 : (a : MulAut A) ((b : MulAut A) p) =
            ((b : MulAut A) p * p⁻¹) * ((a : MulAut A) p) := by
          rw [map_mul, map_inv] at hafix
          rw [← hafix]
          group
        show (a : MulAut A) ((b : MulAut A) p) * p⁻¹ =
          ((a : MulAut A) p * p⁻¹) * ((b : MulAut A) p * p⁻¹)
        rw [h1]
        ac_rfl }
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have htriv : φ ⟨k, hk⟩ = 1 := by
    haveI : IsMulCommutative φ.range := inferInstance
    haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨φ ⟨k, hk⟩, ⟨k, hk⟩, rfl⟩ : φ.range) 1)
  exact mul_inv_eq_one.1 htriv

theorem c23ne_commSub_sup_ker {A : Type} [CommGroup A] {H : Subgroup (MulAut A)}
    {P Z : Subgroup A} (h : Nonempty (NatQuot3 H P Z)) (hZP : Z ≤ P) :
    commSub P H ⊔ Z = P := by
  obtain ⟨D⟩ := h
  have hcommP : commSub P H ≤ P := c23ne_commSub_le_of_natQuot D
  refine le_antisymm (sup_le hcommP hZP) ?_
  let T : Subgroup (Multiplicative (Fin 3 → ZMod 2)) :=
    ((commSub P H).subgroupOf P).map D.θ
  have hT : T = ⊤ := by
    apply c23ne_subgroup_eq_top_of_singles
    intro i
    have hgen : ∀ a b : Fin 3, a ≠ b →
        Multiplicative.ofAdd (Pi.single a 1) ∈ T := by
      intro a b hab
      let t : SL3F2 := Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2)
      obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd (Pi.single b 1))
      let v : ↥P := ⟨((D.ρ t : ↥H) : MulAut A) (u : A), D.inv t (u : A) u.2⟩
      let cP : ↥P := v * u⁻¹
      have hcval : (cP : A) = ((D.ρ t : ↥H) : MulAut A) (u : A) * (u : A)⁻¹ := rfl
      have hc : (cP : A) ∈ commSub P H := by
        rw [hcval]
        exact Subgroup.subset_closure
          ⟨((D.ρ t : ↥H) : MulAut A), (D.ρ t).2, (u : A), u.2, rfl⟩
      refine Subgroup.mem_map.2 ⟨cP, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact hc
      · have hv : D.θ v = Multiplicative.ofAdd (t • Pi.single b 1) := by
          have h1 := D.equiv t u
          rw [hu] at h1
          simpa using h1
        have hu' : D.θ u⁻¹ = Multiplicative.ofAdd (- Pi.single b 1) := by
          rw [map_inv, hu, ← ofAdd_neg]
        have hcPθ : D.θ cP = D.θ v * D.θ u⁻¹ := by
          change D.θ (v * u⁻¹) = D.θ v * D.θ u⁻¹
          rw [map_mul]
        rw [hcPθ, hv, hu', ← ofAdd_add]
        congr 1
        rw [Matrix.SpecialLinearGroup.transvection_smul_single_snd hab (1 : ZMod 2), one_smul]
        abel
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    fin_cases i
    · exact hgen 0 1 h01
    · exact hgen 1 2 h12
    · exact hgen 2 0 h20
  intro p hp
  have hθp : D.θ ⟨p, hp⟩ ∈ T := by
    rw [hT]
    exact Subgroup.mem_top _
  obtain ⟨cP, hcPmem, hθcP⟩ := Subgroup.mem_map.1 hθp
  have hcPval : (cP : A) ∈ commSub P H := Subgroup.mem_subgroupOf.1 hcPmem
  let zP : ↥P := ⟨p, hp⟩ * cP⁻¹
  have hz : (zP : A) ∈ Z := by
    apply (D.θ_ker zP).1
    rw [map_mul, map_inv, hθcP]
    exact mul_inv_cancel _
  have hple : p = (zP : A) * (cP : A) := by
    show p = (p * (cP : A)⁻¹) * (cP : A)
    group
  rw [hple, sup_comm]
  exact Subgroup.mul_mem_sup hz hcPval

theorem c23ne_complement_of_proper {A : Type} [CommGroup A] [Finite A]
    {H : Subgroup (MulAut A)} {P Z : Subgroup A} (hnat : Nonempty (NatQuot3 H P Z))
    (hZP : Z ≤ P) (hZ : Nat.card Z = 2) (hne : commSub P H ≠ P) :
    commSub P H ≤ P ∧ commSub P H ⊓ Z = ⊥ ∧ commSub P H ⊔ Z = P ∧
      ∀ a ∈ H, ∀ c ∈ commSub P H, (a : MulAut A) c ∈ commSub P H := by
  obtain ⟨D⟩ := hnat
  have hle : commSub P H ≤ P := c23ne_commSub_le_of_natQuot D
  have hsup : commSub P H ⊔ Z = P := c23ne_commSub_sup_ker ⟨D⟩ hZP
  have hHP : ∀ k ∈ H, ∀ p ∈ P, (k : MulAut A) p ∈ P := by
    intro k hk p hp
    obtain ⟨g, hg⟩ := D.surj ⟨k, hk⟩
    have hgk : ((D.ρ g : ↥H) : MulAut A) = k := congrArg Subtype.val hg
    rw [← hgk]
    exact D.inv g p hp
  have hinf : commSub P H ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(commSub P H ⊓ Z) ∣ Nat.card ↥Z :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hZ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact (Subgroup.eq_bot_iff_card (commSub P H ⊓ Z)).2 h1
    · exfalso
      have heq : commSub P H ⊓ Z = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hZ])
      have hZle : Z ≤ commSub P H := by
        rw [← heq]
        exact inf_le_left
      exact hne ((sup_eq_left.2 hZle).symm.trans hsup)
  refine ⟨hle, hinf, hsup, ?_⟩
  intro a ha c hc
  have hgen : ∀ x ∈ {c : A | ∃ b ∈ H, ∃ p ∈ P, b p * p⁻¹ = c},
      (a : MulAut A) x ∈ commSub P H := by
    rintro x ⟨b, hb, p, hp, rfl⟩
    have hap : (a : MulAut A) p ∈ P := hHP a ha p hp
    have hab : a * b * a⁻¹ ∈ H := H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)
    have hconj : (a * b * a⁻¹ : MulAut A) ((a : MulAut A) p) =
        (a : MulAut A) ((b : MulAut A) p) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply]
      congr 1
      group
    have heq : (a : MulAut A) ((b : MulAut A) p * p⁻¹) =
        (a * b * a⁻¹ : MulAut A) ((a : MulAut A) p) * ((a : MulAut A) p)⁻¹ := by
      rw [hconj, map_mul, map_inv]
    rw [heq]
    exact Subgroup.subset_closure ⟨a * b * a⁻¹, hab, (a : MulAut A) p, hap, rfl⟩
  exact Subgroup.closure_induction (k := {c : A | ∃ b ∈ H, ∃ p ∈ P, b p * p⁻¹ = c})
    (p := fun y _ => (a : MulAut A) y ∈ commSub P H)
    (fun x hx => hgen x hx) (by simp)
    (fun x y _ _ hx hy => by
      rw [map_mul]
      exact (commSub P H).mul_mem hx hy)
    (fun x _ hx => by
      rw [map_inv]
      exact (commSub P H).inv_mem hx) hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
