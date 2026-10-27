module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3ProdAut
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.EvenSporadicStandard.M24Std

private theorem eq_one_of_pow_five_prod_self {S : Type} [Group S]
    (hs : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hc : ∀ a : S, (∀ c, a * c = c * a) → a = 1) (hnt : ∃ s : S, s ≠ 1)
    (h5 : ¬ 5 ∣ Nat.card (MulAut S)) {α : MulAut (S × S)} (hα : α ^ 5 = 1) : α = 1 := by
  have hprime : Nat.Prime 5 := Nat.prime_five
  have hord : ∀ f : MulAut S, f ^ 5 = 1 → f = 1 := by
    intro f hf
    have h1 : orderOf f ∣ 5 := orderOf_dvd_of_pow_eq_one hf
    rcases (Nat.dvd_prime hprime).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard f) h5
  rcases ProdAut.mulAut_prod_cases hs hc hnt α with ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_preserve α hp1 hp2
    have e₁ : f₁ ^ 5 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (S × S) => (γ (a, 1)).1) hα
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hf] using this
    have e₂ : f₂ ^ 5 = 1 := MulEquiv.ext fun b => by
      have := congrArg (fun γ : MulAut (S × S) => (γ (1, b)).2) hα
      simpa [CFSG.EvenSporadicStandard.Fin76b.pow_apply_pres hf] using this
    have r₁ : f₁ = 1 := hord f₁ e₁
    have r₂ : f₂ = 1 := hord f₂ e₂
    exact CFSG.EvenSporadicStandard.Fin76b.mulAut_prod_eq_one fun a b => by
      simp [hf, r₁, r₂]
  · exfalso
    obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_swap α hs1 hs2
    obtain ⟨s, hs'⟩ := hnt
    have h6 : α ^ (2 * 3) = α := by
      have h : (2 * 3 : ℕ) = 5 + 1 := by norm_num
      rw [h, pow_succ, hα, one_mul]
    have e := CFSG.EvenSporadicStandard.Fin76b.pow_two_mul_apply_swap hf 3 1 s
    rw [h6, hf] at e
    have e1 := congrArg Prod.fst e
    simp only [map_one] at e1
    exact hs' (f₁.injective (by rw [e1]; exact (map_one f₁).symm))

private theorem central_prod_eq_one {S : Type} [Group S]
    (hc : ∀ a : S, (∀ c, a * c = c * a) → a = 1)
    (x : S × S) (hx : ∀ y : S × S, y * x = x * y) : x = 1 := by
  obtain ⟨a, b⟩ := x
  have ha : a = 1 := hc a fun c => (congrArg Prod.fst (hx (c, 1))).symm
  have hb : b = 1 := hc b fun c => (congrArg Prod.snd (hx (1, c))).symm
  simp [ha, hb]

private theorem card_mulAut_zmod_seven :
    Nat.card (MulAut (Multiplicative (ZMod 7))) = 6 := by
  haveI : IsCyclic (Multiplicative (ZMod 7)) := inferInstance
  rw [IsCyclic.card_mulAut, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
    Nat.totient_prime Nat.prime_seven]

theorem s16c1614_not_five_dvd_card_mulAut_z7_prod {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (h5 : ¬ 5 ∣ Nat.card (MulAut S)) :
    ¬ 5 ∣ Nat.card (MulAut (Multiplicative (ZMod 7) × S × S)) := by
  classical
  have hcent : Subgroup.center S = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center S := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hcentral : ∀ a : S, (∀ c, a * c = c * a) → a = 1 := by
    intro a ha
    have : a ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun g => (ha g).symm
    rw [hcent] at this
    exact Subgroup.mem_bot.mp this
  have hnt : ∃ s : S, s ≠ 1 := exists_ne 1
  have hsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤ := fun N hN => by
    haveI := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  have hcommS : commutator S = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator S) with h | h
    · exfalso
      have htop : Subgroup.center S = ⊤ := by
        rw [← commutator_eq_bot_iff_center_eq_top]
        exact h
      rw [hcent] at htop
      obtain ⟨s, hs⟩ := hnt
      have : s ∈ (⊥ : Subgroup S) := by rw [htop]; trivial
      exact hs (Subgroup.mem_bot.mp this)
    · exact h
  have hcommS' : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := hcommS
  have hcommB : commutator (S × S) = ⊤ := by
    have h := Subgroup.commutator_prod_prod (G := S) (G' := S)
        (H₁ := ⊤) (H₂ := ⊤) (K₁ := ⊤) (K₂ := ⊤)
    simp only [Subgroup.top_prod_top] at h
    rw [hcommS'] at h
    rw [Subgroup.top_prod_top] at h
    exact h
  have hcommB' : ⁅(⊤ : Subgroup (S × S)), (⊤ : Subgroup (S × S))⁆ = ⊤ := hcommB
  have hZcomm : commutator (Multiplicative (ZMod 7)) = ⊥ := by
    rw [commutator_def]
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⊤) (H₂ := ⊤)).mpr ?_
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact mul_comm y x
  have hZcomm' : ⁅(⊤ : Subgroup (Multiplicative (ZMod 7))),
      (⊤ : Subgroup (Multiplicative (ZMod 7)))⁆ = ⊥ := hZcomm
  have hprod : commutator (Multiplicative (ZMod 7) × S × S) =
      (⊥ : Subgroup (Multiplicative (ZMod 7))).prod (⊤ : Subgroup (S × S)) := by
    have h := Subgroup.commutator_prod_prod (G := Multiplicative (ZMod 7)) (G' := S × S)
        (H₁ := ⊤) (H₂ := ⊤) (K₁ := ⊤) (K₂ := ⊤)
    simp only [Subgroup.top_prod_top] at h
    rw [hZcomm'] at h
    rw [hcommB'] at h
    exact h
  rintro h5div
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨α, hαord⟩ := exists_prime_orderOf_dvd_card'
      (G := MulAut (Multiplicative (ZMod 7) × S × S)) 5 h5div
  have hα5 : α ^ 5 = 1 := by rw [← hαord]; exact pow_orderOf_eq_one α
  let N : Subgroup (Multiplicative (ZMod 7) × S × S) :=
    (⊥ : Subgroup (Multiplicative (ZMod 7))).prod (⊤ : Subgroup (S × S))
  have hNdef : N = (⊥ : Subgroup (Multiplicative (ZMod 7))).prod
      (⊤ : Subgroup (S × S)) := rfl
  have hNchar : N.Characteristic := by
    have hNcomm : N = commutator (Multiplicative (ZMod 7) × S × S) := hprod.symm
    rw [hNcomm]
    infer_instance
  haveI : N.Characteristic := hNchar
  let eN : N ≃* (S × S) :=
    { toFun := fun n => n.1.2
      invFun := fun x => ⟨(1, x), by
        rw [hNdef]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top x⟩⟩
      left_inv := fun n => by
        apply Subtype.ext
        have h1 : n.1.1 = 1 := by
          have hmem : n.1 ∈ (⊥ : Subgroup (Multiplicative (ZMod 7))).prod
              (⊤ : Subgroup (S × S)) := by rw [← hNdef]; exact n.2
          exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1
        exact Prod.ext h1.symm rfl
      right_inv := fun x => rfl
      map_mul' := fun n m => rfl }
  let γ : MulAut N := MulAut.characteristic N α
  have hγ5 : γ ^ 5 = 1 := by
    show (MulAut.characteristic N α) ^ 5 = 1
    rw [← map_pow, hα5, map_one]
  let β : MulAut (S × S) := MulAut.congr eN γ
  have hβ5 : β ^ 5 = 1 := by
    show (MulAut.congr eN γ) ^ 5 = 1
    rw [← map_pow, hγ5, map_one]
  have hβ1 : β = 1 := eq_one_of_pow_five_prod_self hsimple hcentral hnt h5 hβ5
  have hγ1 : γ = 1 := by
    have h : (MulAut.congr eN) γ = 1 := hβ1
    apply (MulAut.congr eN).injective
    rw [h]
    exact (map_one (MulAut.congr eN)).symm
  have hfixN : ∀ x : S × S, α (1, x) = (1, x) := by
    intro x
    let nx : N := ⟨(1, x), by
      rw [hNdef]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top x⟩⟩
    have h := congrArg (fun (δ : MulAut N) =>
      (δ nx : Multiplicative (ZMod 7) × S × S)) hγ1
    simpa [nx, γ, MulAut.characteristic_apply_apply_coe, MulAut.one_apply] using h
  have hcenter_snd : ∀ c : Subgroup.center
      (Multiplicative (ZMod 7) × S × S), c.1.2 = 1 := by
    intro c
    refine central_prod_eq_one hcentral c.1.2 ?_
    intro y
    exact congrArg Prod.snd (Subgroup.mem_center_iff.mp c.2 (1, y))
  let eC : Subgroup.center (Multiplicative (ZMod 7) × S × S) ≃*
      Multiplicative (ZMod 7) :=
    { toFun := fun c => c.1.1
      invFun := fun z => ⟨(z, 1), Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨z', x'⟩ := y
        exact Prod.ext (mul_comm z' z) (by simp)⟩
      left_inv := fun c => Subtype.ext (Prod.ext rfl (hcenter_snd c).symm)
      right_inv := fun z => rfl
      map_mul' := fun c d => rfl }
  have hcardAutC : Nat.card (MulAut (Subgroup.center
      (Multiplicative (ZMod 7) × S × S))) = 6 := by
    rw [Nat.card_congr (MulAut.congr eC).toEquiv, card_mulAut_zmod_seven]
  let δ : MulAut (Multiplicative (ZMod 7)) :=
    MulAut.congr eC (MulAut.characteristic (Subgroup.center
      (Multiplicative (ZMod 7) × S × S)) α)
  have hchar5 : (MulAut.characteristic (Subgroup.center
      (Multiplicative (ZMod 7) × S × S)) α) ^ 5 = 1 := by
    rw [← map_pow, hα5, map_one]
  have hδ5 : δ ^ 5 = 1 := by
    show (MulAut.congr eC (MulAut.characteristic (Subgroup.center
      (Multiplicative (ZMod 7) × S × S)) α)) ^ 5 = 1
    rw [← map_pow, hchar5, map_one]
  have hδ1 : δ = 1 := by
    have h1 : orderOf δ ∣ 5 := orderOf_dvd_of_pow_eq_one hδ5
    have h2 : orderOf δ ∣ Nat.card (MulAut (Multiplicative (ZMod 7))) :=
      orderOf_dvd_natCard δ
    rw [card_mulAut_zmod_seven] at h2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by decide) h1 h2)
  have hγC1 : MulAut.characteristic (Subgroup.center
      (Multiplicative (ZMod 7) × S × S)) α = 1 := by
    have h : (MulAut.congr eC) (MulAut.characteristic (Subgroup.center
        (Multiplicative (ZMod 7) × S × S)) α) = 1 := hδ1
    apply (MulAut.congr eC).injective
    rw [h]
    exact (map_one (MulAut.congr eC)).symm
  have hfixC : ∀ c : Multiplicative (ZMod 7) × S × S, c ∈ Subgroup.center
      (Multiplicative (ZMod 7) × S × S) → α c = c := by
    intro c hc
    have h := congrArg (fun (ε : MulAut (Subgroup.center
        (Multiplicative (ZMod 7) × S × S))) =>
      (ε ⟨c, hc⟩ : Multiplicative (ZMod 7) × S × S)) hγC1
    simpa only [MulAut.characteristic_apply_apply_coe, MulAut.one_apply] using h
  have hα1 : α = 1 := by
    apply MulEquiv.ext
    intro a
    rw [MulAut.one_apply]
    have ha : a = (a.1, (1 : S × S)) * (1, a.2) :=
      Prod.ext (by simp) (by simp)
    have hcenta : (a.1, (1 : S × S)) ∈ Subgroup.center
        (Multiplicative (ZMod 7) × S × S) :=
      Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨z', x'⟩ := y
        exact Prod.ext (mul_comm z' a.1) (by simp)
    have h1 : α a = α ((a.1, (1 : S × S)) * (1, a.2)) := congrArg α ha
    rw [h1, map_mul, hfixC _ hcenta, hfixN a.2]
    exact ha.symm
  rw [hα1, orderOf_one] at hαord
  exact absurd hαord (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
