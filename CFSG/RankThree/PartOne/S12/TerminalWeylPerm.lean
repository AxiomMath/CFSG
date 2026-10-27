module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartOne

namespace TerminalPerm

open Equiv

theorem odd_involution_exists : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
    ∃ x y : Fin 5, x ≠ y ∧ σ = swap x y := by
  decide +kernel

theorem isSwap_of_odd_involution (σ : Perm (Fin 5)) (h1 : σ * σ = 1) (h2 : Perm.sign σ = -1) :
    σ.IsSwap := by
  obtain ⟨x, y, hxy, h⟩ := odd_involution_exists σ h1 h2
  exact ⟨x, y, hxy, h⟩

theorem swap_conj_swap (σ τ : Perm (Fin 5)) (hσ : σ.IsSwap) (hτ : τ.IsSwap) :
    ∃ h : Perm (Fin 5), h * σ * h⁻¹ = τ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  obtain ⟨h, hh⟩ := isConj_iff.mp (Perm.isConj_swap hab hcd)
  exact ⟨h, hh⟩

theorem exists_fixed_point_of_card_24 (H : Subgroup (Perm (Fin 5))) (hH : Nat.card H = 24) :
    ∃ k : Fin 5, ∀ x ∈ H, x k = k := by
  classical
  have hbound : ∀ S : Finset (Fin 5), (∀ h ∈ H, ∀ j, h j ∈ S ↔ j ∈ S) →
      24 ≤ S.card.factorial * (5 - S.card).factorial := by
    intro S hS
    have hS' : ∀ h ∈ H, ∀ j, h j ∈ Sᶜ ↔ j ∈ Sᶜ := fun h hh j => by
      simpa only [Finset.mem_compl, not_iff_not] using hS h hh j
    let f : H → Perm {x // x ∈ S} × Perm {x // x ∈ Sᶜ} := fun h =>
      ((h : Perm (Fin 5)).subtypePerm (hS h h.2), (h : Perm (Fin 5)).subtypePerm (hS' h h.2))
    have hf : Function.Injective f := by
      intro h h' hh
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      apply Subtype.ext
      refine Equiv.ext fun j => ?_
      by_cases hj : j ∈ S
      · have := congrArg (fun σ : Perm {x // x ∈ S} => (σ ⟨j, hj⟩ : Fin 5)) h1
        simpa [f] using this
      · have hj' : j ∈ Sᶜ := Finset.mem_compl.mpr hj
        have := congrArg (fun σ : Perm {x // x ∈ Sᶜ} => (σ ⟨j, hj'⟩ : Fin 5)) h2
        simpa [f] using this
    have h3 := Nat.card_le_card_of_injective f hf
    rw [hH, Nat.card_prod, Nat.card_perm, Nat.card_perm] at h3
    have e1 : Nat.card {x // x ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have e2 : Nat.card {x // x ∈ Sᶜ} = 5 - S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    rw [e1, e2] at h3
    exact h3
  let O : Finset (Fin 5) := Finset.univ.filter fun j => ∃ h : H, (h : Perm (Fin 5)) 0 = j
  have hO : ∀ j, j ∈ O ↔ ∃ h : H, (h : Perm (Fin 5)) 0 = j := fun j => by simp [O]
  have hinv : ∀ h ∈ H, ∀ j, h j ∈ O ↔ j ∈ O := by
    intro h hh j
    rw [hO, hO]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) g.2⟩, ?_⟩
      show (h⁻¹ * (g : Perm (Fin 5))) 0 = j
      rw [Perm.mul_apply, hg]
      simp
    · rintro ⟨g, hg⟩
      refine ⟨⟨h * g, H.mul_mem hh g.2⟩, ?_⟩
      show (h * (g : Perm (Fin 5))) 0 = h j
      rw [Perm.mul_apply, hg]
  have h0 : (0 : Fin 5) ∈ O := (hO 0).mpr ⟨1, rfl⟩
  have hcard1 : 1 ≤ O.card := Finset.card_pos.mpr ⟨0, h0⟩
  have hcard5 : O.card ≤ 5 := by simpa using Finset.card_le_univ O
  have hcases : O.card = 1 ∨ O.card = 2 ∨ O.card = 3 ∨ O.card = 4 ∨ O.card = 5 := by omega
  rcases hcases with h | h | h | h | h
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    refine ⟨0, fun x hx => ?_⟩
    have h1 : x 0 ∈ O := (hinv x hx 0).mpr h0
    rw [ha, Finset.mem_singleton] at h1
    have h2 : (0 : Fin 5) ∈ ({a} : Finset (Fin 5)) := ha ▸ h0
    rw [Finset.mem_singleton] at h2
    rw [h1, h2]
  · exfalso
    have := hbound O hinv
    rw [h] at this
    norm_num [Nat.factorial] at this
  · exfalso
    have := hbound O hinv
    rw [h] at this
    norm_num [Nat.factorial] at this
  · have hc : Oᶜ.card = 1 := by rw [Finset.card_compl, h]; simp
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
    refine ⟨k, fun x hx => ?_⟩
    have hkc : k ∈ Oᶜ := by rw [hk]; exact Finset.mem_singleton_self k
    have h1 : x k ∈ Oᶜ := by
      rw [Finset.mem_compl] at hkc ⊢
      rw [hinv x hx]
      exact hkc
    rw [hk, Finset.mem_singleton] at h1
    exact h1
  · exfalso
    have horb : MulAction.orbit H (0 : Fin 5) = (O : Set (Fin 5)) := by
      ext j
      rw [MulAction.mem_orbit_iff, Finset.mem_coe, hO]
      rfl
    have hidx := MulAction.index_stabilizer H (0 : Fin 5)
    rw [horb, Set.ncard_coe_finset, h] at hidx
    have := Subgroup.index_mul_card (MulAction.stabilizer H (0 : Fin 5))
    rw [hidx, hH] at this
    omega

theorem exists_pi_of_equiv {A : Type*} [Group A] {Γ Y : Subgroup A}
    (e : Y ≃* alternatingGroup (Fin 5)) (hYΓ : Y ≤ Γ)
    (hYn : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    ∃ π : Γ →* Perm (Fin 5),
      (∀ (y : A) (hy : y ∈ Y),
        π ⟨y, hYΓ hy⟩ = ((e ⟨y, hy⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5))) ∧
      ∀ g : Γ, π g = 1 → ∀ y ∈ Y, (g : A) * y = y * g := by
  classical
  have hN : (Y.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hYn g g.2 n hn⟩
  let eN : (Y.subgroupOf Γ) ≃* alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hYΓ).trans e
  have bij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  let c : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) := MulEquiv.ofBijective _ bij
  let π : Γ →* Perm (Fin 5) :=
    c.symm.toMonoidHom.comp
      ((MulAut.congr eN).toMonoidHom.comp (MulAut.conjNormal (H := Y.subgroupOf Γ)))
  have key : ∀ γ : Γ, c (π γ) =
      MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) := fun γ => by
    simp [π]
  refine ⟨π, ?_, ?_⟩
  · intro y hy
    set γ : Γ := ⟨y, hYΓ hy⟩ with hγ
    set n : Y.subgroupOf Γ := ⟨γ, hy⟩ with hn
    have h1 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) =
        c ((eN n : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
      refine MulEquiv.ext fun a => ?_
      have h3 : MulAut.conjNormal (H := Y.subgroupOf Γ) γ (eN.symm a) = n * eN.symm a * n⁻¹ :=
        Subtype.ext (MulAut.conjNormal_apply γ _)
      have h5 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) a =
          eN (n * eN.symm a * n⁻¹) := by
        show eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ (eN.symm a)) = _
        rw [h3]
      rw [h5, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      refine Subtype.ext ?_
      show _ = ((MulAut.conjNormal ((eN n : alternatingGroup (Fin 5)) : Perm (Fin 5))) a :
        alternatingGroup (Fin 5)).1
      rw [MulAut.conjNormal_apply]
      rfl
    have h2 : π γ = ((eN n : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
      apply c.injective
      rw [key, ← h1]
    rw [h2]
    rfl
  · intro γ hγ y hy
    have h1 : MulAut.congr eN (MulAut.conjNormal (H := Y.subgroupOf Γ) γ) = 1 := by
      rw [← key, hγ, map_one]
    have h2 : MulAut.conjNormal (H := Y.subgroupOf Γ) γ = 1 := by
      have := (MulAut.congr eN).injective (h1.trans (map_one (MulAut.congr eN)).symm)
      exact this
    have h3 := congrArg (fun φ : MulAut (Y.subgroupOf Γ) =>
      ((φ ⟨⟨y, hYΓ hy⟩, hy⟩ : Y.subgroupOf Γ) : Γ)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    exact mul_inv_eq_iff_eq_mul.mp h4

theorem reflection_class_bijective {A : Type*} [Group A] {Γ : Subgroup A}
    (π : Γ →* Perm (Fin 5)) (δ : Γ →* (ZMod 5)ˣ) {R : Set A} (hRΓ : R ⊆ Γ)
    (hRconj : ∀ g ∈ Γ, ∀ t ∈ R, g * t * g⁻¹ ∈ R) (hRne : R.Nonempty)
    (hswap : ∀ t (ht : t ∈ R), (π ⟨t, hRΓ ht⟩).IsSwap)
    (hδ : ∀ t (ht : t ∈ R), δ ⟨t, hRΓ ht⟩ = -1)
    (hAπ : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∃ y : Γ, π y = σ)
    (hK : ∀ g : Γ, π g = 1 → δ g = 1 → g = 1) :
    Function.Bijective
      (π.comp (Subgroup.inclusion ((Subgroup.closure_le Γ).mpr hRΓ) : Subgroup.closure R →* Γ)) ∧
    ∀ σ : Perm (Fin 5), σ.IsSwap → ∃ (t : A) (ht : t ∈ R), π ⟨t, hRΓ ht⟩ = σ := by
  obtain ⟨t₀, ht₀⟩ := hRne
  set s₀ : Perm (Fin 5) := π ⟨t₀, hRΓ ht₀⟩ with hs₀
  have hs₀sign : Perm.sign s₀ = -1 := (hswap t₀ ht₀).sign_eq
  have hsurj : ∀ σ : Perm (Fin 5), ∃ g : Γ, π g = σ := by
    intro σ
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact hAπ σ h
    · have h1 : Perm.sign (σ * s₀) = 1 := by rw [Perm.sign_mul, h, hs₀sign]; rfl
      obtain ⟨y, hy⟩ := hAπ _ h1
      refine ⟨y * ⟨t₀, hRΓ ht₀⟩⁻¹, ?_⟩
      rw [map_mul, map_inv, hy, ← hs₀]
      group
  have hswaps : ∀ σ : Perm (Fin 5), σ.IsSwap → ∃ (t : A) (ht : t ∈ R), π ⟨t, hRΓ ht⟩ = σ := by
    intro σ hσ
    obtain ⟨h, hh⟩ := swap_conj_swap s₀ σ (hswap t₀ ht₀) hσ
    obtain ⟨g, hg⟩ := hsurj h
    have hmem : (g : A) * t₀ * (g : A)⁻¹ ∈ R := hRconj g g.2 t₀ ht₀
    refine ⟨(g : A) * t₀ * (g : A)⁻¹, hmem, ?_⟩
    have e : (⟨(g : A) * t₀ * (g : A)⁻¹, hRΓ hmem⟩ : Γ) = g * ⟨t₀, hRΓ ht₀⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg, ← hs₀]
    exact hh
  let ε : Perm (Fin 5) →* (ZMod 5)ˣ :=
    (Units.map (Int.castRingHom (ZMod 5)).toMonoidHom).comp Perm.sign
  have hΓ : Subgroup.closure R ≤ Γ := (Subgroup.closure_le Γ).mpr hRΓ
  have hε : ∀ (x : A) (hx : x ∈ Subgroup.closure R),
      δ ⟨x, hΓ hx⟩ = ε (π ⟨x, hΓ hx⟩) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : (⟨x, hΓ (Subgroup.subset_closure hx)⟩ : Γ) = ⟨x, hRΓ hx⟩ := rfl
      rw [hx', hδ x hx]
      have h1 : Perm.sign (π ⟨x, hRΓ hx⟩) = -1 := (hswap x hx).sign_eq
      show _ = Units.map (Int.castRingHom (ZMod 5)).toMonoidHom (Perm.sign (π ⟨x, hRΓ hx⟩))
      rw [h1]
      ext
      simp
    | one =>
      have : (⟨1, hΓ (one_mem _)⟩ : Γ) = 1 := rfl
      rw [this, map_one, map_one, map_one]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hΓ (mul_mem hx hy)⟩ : Γ) = ⟨x, hΓ hx⟩ * ⟨y, hΓ hy⟩ := rfl
      rw [this, map_mul, map_mul, map_mul, ihx, ihy]
    | inv x hx ih =>
      have : (⟨x⁻¹, hΓ (inv_mem hx)⟩ : Γ) = (⟨x, hΓ hx⟩ : Γ)⁻¹ := rfl
      rw [this, map_inv, map_inv, map_inv, ih]
  have hρinj : Function.Injective
      (π.comp (Subgroup.inclusion hΓ : Subgroup.closure R →* Γ)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (Subgroup.inclusion hΓ x) = 1 := hx
    have h2 : δ (Subgroup.inclusion hΓ x) = 1 := by
      have h3 := hε x.1 x.2
      show δ ⟨x.1, hΓ x.2⟩ = 1
      rw [h3]
      show ε (π (Subgroup.inclusion hΓ x)) = 1
      rw [h1, map_one]
    have h3 := hK _ h1 h2
    have h4 := congrArg (fun g : Γ => (g : A)) h3
    exact Subtype.ext h4
  have hρsurj : Function.Surjective
      (π.comp (Subgroup.inclusion hΓ : Subgroup.closure R →* Γ)) := by
    have htop : Subgroup.closure {σ : Perm (Fin 5) | σ.IsSwap} = ⊤ := Perm.closure_isSwap
    have hle : Subgroup.closure {σ : Perm (Fin 5) | σ.IsSwap} ≤
        (π.comp (Subgroup.inclusion hΓ : Subgroup.closure R →* Γ)).range := by
      rw [Subgroup.closure_le]
      intro σ hσ
      obtain ⟨t, ht, hts⟩ := hswaps σ hσ
      exact ⟨⟨t, Subgroup.subset_closure ht⟩, hts⟩
    rw [htop] at hle
    intro σ
    exact hle (Subgroup.mem_top σ)
  exact ⟨⟨hρinj, hρsurj⟩, hswaps⟩

end TerminalPerm

end CFSG.RankThree.PartOne
