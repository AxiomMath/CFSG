module

public import CFSG.Quasithin.Background.B69Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.Quasithin.Background.HSL3Pair

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace B69

theorem exists_aut_of_ker_eq {L G₀ : Type*} [Group L] [Group G₀] (π : L →* G₀)
    (hπ : Function.Surjective π) (ψ : MulAut L) (hψ : ∀ l, π (ψ l) = 1 ↔ π l = 1) :
    ∃ θ : MulAut G₀, ∀ l, θ (π l) = π (ψ l) := by
  let θ₀ : L →* G₀ := π.comp ψ.toMonoidHom
  have hk : π.ker ≤ θ₀.ker := fun l hl =>
    MonoidHom.mem_ker.mpr ((hψ l).mpr (MonoidHom.mem_ker.mp hl))
  let θ : G₀ →* G₀ := π.liftOfSurjective hπ ⟨θ₀, hk⟩
  have hθ : ∀ l, θ (π l) = π (ψ l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, rfl⟩ := hπ g
    rw [hθ] at hg
    exact (hψ l).mp hg
  have hsurj : Function.Surjective θ := by
    intro g
    obtain ⟨l, rfl⟩ := hπ g
    obtain ⟨l', rfl⟩ := ψ.surjective l
    exact ⟨π l', hθ l'⟩
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hsurj⟩, hθ⟩

theorem not_exists_dual_iso {K : Type} [Field K] [Finite K]
    (Φ : StdMod (Fin 3) K ≃* StdMod (Fin 3) K)
    (hΦ : ∀ g ∈ StatedSL 3 K, ∀ x : StdMod (Fin 3) K, Φ (matAut g x) = matAut (dualGL g) (Φ x)) :
    False := by
  refine not_isoMod (K := K) ?_
  let e : V₁ K ≃* V₂ K :=
    { toFun := fun w => ⟨((1 : StdMod (Fin 3) K), Φ (w : PairMod K).1), mem_V₂.mpr rfl⟩
      invFun := fun w => ⟨(Φ.symm (w : PairMod K).2, (1 : StdMod (Fin 3) K)), mem_V₁.mpr rfl⟩
      left_inv := fun w => by
        apply Subtype.ext
        have h2 : (w : PairMod K).2 = 1 := mem_V₁.mp w.2
        exact Prod.ext (by simp) h2.symm
      right_inv := fun w => by
        apply Subtype.ext
        have h1 : (w : PairMod K).1 = 1 := mem_V₂.mp w.2
        exact Prod.ext h1.symm (by simp)
      map_mul' := fun w w' => by
        apply Subtype.ext
        exact Prod.ext (by simp) (by simp [map_mul]) }
  refine ⟨e, ?_⟩
  rintro _ ⟨g, hg, rfl⟩ w h
  refine Prod.ext ?_ ?_
  · simp [e, pairHom_apply]
  · simp [e, pairHom_apply, hΦ g hg]

theorem even_card_projectiveSL_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h2 : 2 ∣ Nat.card K) : Even (Nat.card (projectiveSL 3 K)) := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (projectiveSL 3 K)))
  have h1 := card_center_sylow_projectiveSL (K := K) (n := 3) (by norm_num) T
  have h3 : Nat.card (Subgroup.center (T : Subgroup (projectiveSL 3 K))) ∣
      Nat.card (T : Subgroup (projectiveSL 3 K)) := Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card (T : Subgroup (projectiveSL 3 K)) ∣ Nat.card (projectiveSL 3 K) :=
    Subgroup.card_subgroup_dvd_card _
  rw [h1] at h3
  exact even_iff_two_dvd.mpr (h2.trans (h3.trans h4))

theorem nontrivial_projectiveSL_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h2 : 2 ∣ Nat.card K) : Nontrivial (projectiveSL 3 K) := by
  have h := even_card_projectiveSL_three (K := K) h2
  rw [← Finite.one_lt_card_iff_nontrivial]
  have hpos : 0 < Nat.card (projectiveSL 3 K) := Nat.card_pos
  obtain ⟨m, hm⟩ := h
  omega

theorem center_projectiveSL_three {K : Type} [Field K] [Finite K] :
    Subgroup.center (projectiveSL 3 K) = ⊥ :=
  CFSG.QuasithinUnique.Setup.X7Sec.center_projectiveSL_eq_bot (F := K)

theorem mem_fixV_of_conj {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} {t : MulAut V}
    (ht : ∀ x ∈ L, t⁻¹ * x * t ∈ L) {w : V} (hw : w ∈ fixV L) : t w ∈ fixV L := by
  intro x hx
  have h := hw _ (ht x hx)
  have h2 : t⁻¹ (x (t w)) = w := h
  calc x (t w) = t (t⁻¹ (x (t w))) := by simp
    _ = t w := by rw [h2]

end B69

end CFSG.Quasithin
