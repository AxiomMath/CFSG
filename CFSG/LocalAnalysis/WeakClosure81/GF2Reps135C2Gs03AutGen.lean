module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def AutGenBound (S : Type) [Group S] (k : ℕ) (P : MulAut S → Prop) : Prop :=
  ∀ a : MulAut S, orderOf a = 2 → P a →
    ∃ s : Fin k → S, inner S ≤
      Subgroup.closure (Set.range fun i => (MulAut.conj (s i))⁻¹ * a * MulAut.conj (s i))

theorem gs03_of_autGenBound {S : Type} [Group S] {k : ℕ} {P : MulAut S → Prop}
    (h : AutGenBound S k P) {G : Type} [Group G] [Finite G] (S' : Subgroup G) [S'.Normal]
    (hC : Subgroup.centralizer (S' : Set G) = ⊥) (e : ↥S' ≃* S) {x : G} (hx : orderOf x = 2)
    (hP : P (MulAut.congr e (MulAut.conjNormal x))) :
    ∃ T : Finset G, T.card ≤ k ∧ (∀ y ∈ T, ∃ s ∈ S', y = s * x * s⁻¹) ∧
      S' ≤ Subgroup.closure (T : Set G) := by
  classical
  have hphi_inj : Function.Injective (MulAut.conjNormal : G →* MulAut ↥S') := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hcomm : g ∈ Subgroup.centralizer (S' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have key : (MulAut.conjNormal g) ⟨w, hw⟩ = ⟨w, hw⟩ := by
        rw [hg]; rfl
      have key' : g * w * g⁻¹ = w := by
        have hval := congrArg Subtype.val key
        simpa [MulAut.conjNormal_apply] using hval
      calc w * g = (g * w * g⁻¹) * g := by rw [key']
        _ = g * w := by group
    rw [hC] at hcomm
    simpa using hcomm
  have hx2 : x ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one x
    rw [hx] at hpow
    exact hpow
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hcn2 : ((MulAut.conjNormal x : MulAut ↥S')) ^ 2 = 1 := by
    rw [← map_pow, hx2, map_one]
  have hcnne : (MulAut.conjNormal x : MulAut ↥S') ≠ 1 := by
    intro h1
    exact hxne (hphi_inj (by rw [h1, map_one]))
  have hcn : orderOf (MulAut.conjNormal x : MulAut ↥S') = 2 :=
    orderOf_eq_prime hcn2 hcnne
  have ha2 : orderOf (MulAut.congr e (MulAut.conjNormal x)) = 2 := by
    rw [MulEquiv.orderOf_eq, hcn]
  obtain ⟨s, hs⟩ := h (MulAut.congr e (MulAut.conjNormal x)) ha2 hP
  let u : Fin k → ↥S' := fun i => e.symm (s i)
  let y : Fin k → G := fun i => ((u i : ↥S') : G)⁻¹ * x * ((u i : ↥S') : G)
  let T : Finset G := Finset.univ.image y
  let J : Subgroup G := Subgroup.closure (T : Set G)
  let psi : G →* MulAut S :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut ↥S')
  have hpsi_inj : Function.Injective psi := by
    intro a b hab
    change MulAut.congr e (MulAut.conjNormal a) =
      MulAut.congr e (MulAut.conjNormal b) at hab
    exact hphi_inj ((MulAut.congr e).injective hab)
  have hcu : ∀ i, MulAut.congr e (MulAut.conjNormal ((u i : ↥S') : G)) =
      MulAut.conj (s i) := by
    intro i
    rw [MulAut.conjNormal_val, congr_conj e (u i)]
    rw [show e (u i) = s i from e.apply_symm_apply (s i)]
  have hpsi_y : ∀ i, psi (y i) = (MulAut.conj (s i))⁻¹ *
      (MulAut.congr e (MulAut.conjNormal x)) * MulAut.conj (s i) := by
    intro i
    have h1 : psi (y i) =
        (psi ((u i : ↥S') : G))⁻¹ * psi x * psi ((u i : ↥S') : G) := by
      change psi (((u i : ↥S') : G)⁻¹ * x * ((u i : ↥S') : G)) = _
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    have hu : psi ((u i : ↥S') : G) = MulAut.conj (s i) := by
      change MulAut.congr e (MulAut.conjNormal ((u i : ↥S') : G)) = MulAut.conj (s i)
      rw [MulAut.conjNormal_val, congr_conj e (u i)]
      rw [show e (u i) = s i from e.apply_symm_apply (s i)]
    rw [hu]
    rfl
  have hmap : J.map psi = Subgroup.closure
      (Set.range fun i => (MulAut.conj (s i))⁻¹ *
        (MulAut.congr e (MulAut.conjNormal x)) * MulAut.conj (s i)) := by
    change (Subgroup.closure (T : Set G)).map psi = _
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      change g ∈ (Finset.univ.image y : Finset G) at hg
      rw [Finset.mem_image] at hg
      obtain ⟨i, -, rfl⟩ := hg
      exact ⟨i, (hpsi_y i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨y i, ?_, hpsi_y i⟩
      change y i ∈ (Finset.univ.image y : Finset G)
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, rfl⟩
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ J.map psi := by
    rw [hmap]
    exact hs
  have hS'le : S' ≤ J := by
    intro g hg
    have hmem : psi (⟨g, hg⟩ : ↥S') ∈ J.map psi := by
      apply hinner
      refine ⟨e ⟨g, hg⟩, ?_⟩
      change MulAut.conj (e ⟨g, hg⟩) =
        MulAut.congr e (MulAut.conjNormal ((⟨g, hg⟩ : ↥S') : G))
      rw [MulAut.conjNormal_val, congr_conj e ⟨g, hg⟩]
    obtain ⟨j, hj, hju⟩ := Subgroup.mem_map.mp hmem
    have hjg : j = g := hpsi_inj hju
    simpa [hjg] using hj
  have hTcard : T.card ≤ k := by
    change (Finset.univ.image y).card ≤ k
    calc (Finset.univ.image y).card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_image_le
      _ = k := by simp
  have hTmem : ∀ z ∈ T, ∃ s ∈ S', z = s * x * s⁻¹ := by
    intro z hz
    change z ∈ (Finset.univ.image y : Finset G) at hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    refine ⟨((u i : ↥S') : G)⁻¹, S'.inv_mem (u i).2, ?_⟩
    change ((u i : ↥S') : G)⁻¹ * x * ((u i : ↥S') : G) =
      ((u i : ↥S') : G)⁻¹ * x * (((u i : ↥S') : G)⁻¹)⁻¹
    rw [inv_inv]
  exact ⟨T, hTcard, hTmem, hS'le⟩

end CFSG.LocalAnalysis.WeakClosure81
