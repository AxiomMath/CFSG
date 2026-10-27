module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixCoords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private theorem s1611e3_sixZ_mul_self : sixZ * sixZ = (1 : SixE6) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  change (1 : ZMod 2) + 1 = 0
  decide

private theorem s1611e3_sixDiag_mul_self :
    ((sixZ, sixZ) : SixE6 × SixE6) * (sixZ, sixZ) = 1 := by
  apply Prod.ext <;> exact s1611e3_sixZ_mul_self

private theorem s1611e3_mem_zpowers_two {G : Type*} [Group G] {z w : G} (hz : z * z = 1) :
    w ∈ Subgroup.zpowers z ↔ w = 1 ∨ w = z := by
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hsq : z ^ (2 : ℤ) = 1 := (zpow_two z).trans hz
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul z 2 n, hsq, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul z 2 n, hsq, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem s1611e3_six_module
    (h : SixHyp M L L' κ e) :
    ∃ (K : Subgroup (SixE6 × SixE6)) (Φ : SixE6 × SixE6 →* W) (θ : ↥sixLhat ≃* ↥L),
      (K = ⊥ ∨ K = sixDiag) ∧ Function.Surjective Φ ∧ Φ.ker = K ∧
        ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
          Φ ((l : MulAut (SixE6 × SixE6)) u) = ((θ l : ↥L) : MulAut W) (Φ u) := by
  classical
  obtain ⟨W₁, W₂, θ₁, Ψ₁, Ψ₂, hθ₁bij, hsup, hinf, hker₁, hker₂, hact₁, hact₂⟩ :=
    s1611e3_six_coords h
  let Φ : SixE6 × SixE6 →* W :=
    (W₁.subtype.comp Ψ₁.toMonoidHom).coprod (W₂.subtype.comp Ψ₂.toMonoidHom)
  let e₀ : ↥(alternatingGroup (Fin 6)) ≃* ↥sixLhat :=
    Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) sixRho sixRho_injective
  let θ : ↥sixLhat ≃* ↥L := e₀.symm.trans (MulEquiv.ofBijective θ₁ hθ₁bij)
  have hΦ : ∀ u : SixE6 × SixE6,
      Φ u = ((Ψ₁ u.1 : ↥W₁) : W) * ((Ψ₂ u.2 : ↥W₂) : W) :=
    fun u => MonoidHom.coprod_apply (W₁.subtype.comp Ψ₁.toMonoidHom)
      (W₂.subtype.comp Ψ₂.toMonoidHom) u
  have hθ_apply : ∀ l : ↥sixLhat, (θ l : ↥L) = θ₁ (e₀.symm l) := fun _ => rfl
  have hθa : ∀ a : ↥(alternatingGroup (Fin 6)), (θ (e₀ a) : ↥L) = θ₁ a := by
    intro a
    rw [hθ_apply, e₀.symm_apply_apply]
  have hsurj : Function.Surjective Φ := by
    intro w
    have hw : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
    rw [Subgroup.mem_sup] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
    obtain ⟨x, hx⟩ := Ψ₁.surjective ⟨w₁, hw₁⟩
    obtain ⟨y, hy⟩ := Ψ₂.surjective ⟨w₂, hw₂⟩
    refine ⟨(x, y), ?_⟩
    rw [hΦ, hx, hy]
  have hequiv : ∀ (l : ↥sixLhat) (u : SixE6 × SixE6),
      Φ ((l : MulAut (SixE6 × SixE6)) u) = ((θ l : ↥L) : MulAut W) (Φ u) := by
    intro l u
    obtain ⟨x, y⟩ := u
    have hl : (l : MulAut (SixE6 × SixE6)) ∈
        (alternatingGroup (Fin 6)).map sixRho := l.2
    rw [Subgroup.mem_map] at hl
    obtain ⟨a, ha, haeq⟩ := hl
    have haeq' : (l : MulAut (SixE6 × SixE6)) = sixRho a := haeq.symm
    have he0a : e₀ ⟨a, ha⟩ = l := by
      apply Subtype.ext
      change (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) sixRho
        sixRho_injective ⟨a, ha⟩ : MulAut (SixE6 × SixE6)) = ↑l
      rw [Subgroup.coe_equivMapOfInjective_apply]
      exact haeq
    have htheta : ((θ l : ↥L) : MulAut W) = ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W) := by
      have hh : θ l = θ₁ ⟨a, ha⟩ := by
        rw [← he0a]
        exact hθa ⟨a, ha⟩
      rw [hh]
    have hsig : sixRho a (x, y) =
        (CFSG.Quasithin.H13.VolI.act6 ⟨a, ha⟩ x,
          CFSG.Quasithin.H13.VolI.act6 (sixAlphaA ⟨a, ha⟩) y) := rfl
    calc Φ ((l : MulAut (SixE6 × SixE6)) (x, y))
        = Φ (sixRho a (x, y)) := by rw [haeq']
      _ = Φ (CFSG.Quasithin.H13.VolI.act6 ⟨a, ha⟩ x,
            CFSG.Quasithin.H13.VolI.act6 (sixAlphaA ⟨a, ha⟩) y) := by rw [hsig]
      _ = ((Ψ₁ (CFSG.Quasithin.H13.VolI.act6 ⟨a, ha⟩ x) : ↥W₁) : W) *
            ((Ψ₂ (CFSG.Quasithin.H13.VolI.act6 (sixAlphaA ⟨a, ha⟩) y) : ↥W₂) : W) :=
              hΦ _
      _ = ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W) ((Ψ₁ x : ↥W₁) : W) *
            ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W) ((Ψ₂ y : ↥W₂) : W) := by
              rw [hact₁ ⟨a, ha⟩ x, hact₂ ⟨a, ha⟩ y]
      _ = ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W)
            (((Ψ₁ x : ↥W₁) : W) * ((Ψ₂ y : ↥W₂) : W)) :=
              (map_mul ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W) _ _).symm
      _ = ((θ₁ ⟨a, ha⟩ : ↥L) : MulAut W) (Φ (x, y)) := by rw [hΦ]
      _ = ((θ l : ↥L) : MulAut W) (Φ (x, y)) := by rw [htheta]
  have hker_le : ∀ u : SixE6 × SixE6, u ∈ Φ.ker → u = 1 ∨ u = (sixZ, sixZ) := by
    intro u hu
    obtain ⟨x, y⟩ := u
    have h1 : ((Ψ₁ x : ↥W₁) : W) * ((Ψ₂ y : ↥W₂) : W) = 1 := by
      have hh : Φ (x, y) = 1 := (MonoidHom.mem_ker).mp hu
      rwa [hΦ (x, y)] at hh
    have hxW : ((Ψ₁ x : ↥W₁) : W) ∈ κ.ker := by
      refine hinf ?_
      rw [Subgroup.mem_inf]
      exact ⟨(Ψ₁ x).2, by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact W₂.inv_mem (Ψ₂ y).2⟩
    have hyW : ((Ψ₂ y : ↥W₂) : W) ∈ κ.ker := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact κ.ker.inv_mem hxW
    have hx' : x = 1 ∨ x = sixZ :=
      (s1611e3_mem_zpowers_two s1611e3_sixZ_mul_self).mp ((hker₁ x).mp hxW)
    have hy' : y = 1 ∨ y = sixZ :=
      (s1611e3_mem_zpowers_two s1611e3_sixZ_mul_self).mp ((hker₂ y).mp hyW)
    rcases hx' with rfl | rfl
    · left
      have h2 : (Ψ₂ y : ↥W₂) = 1 := by
        have hh : ((Ψ₂ y : ↥W₂) : W) = 1 := by simpa using h1
        exact Subtype.ext hh
      have hy1 : y = 1 := Ψ₂.injective (by rw [h2, map_one])
      exact Prod.ext rfl hy1
    · rcases hy' with rfl | rfl
      · left
        have h2 : (Ψ₁ sixZ : ↥W₁) = 1 := by
          have hh : ((Ψ₁ sixZ : ↥W₁) : W) = 1 := by simpa using h1
          exact Subtype.ext hh
        have hz1 : sixZ = (1 : SixE6) := Ψ₁.injective (by rw [h2, map_one])
        exact Prod.ext hz1 rfl
      · right
        rfl
  have hK : Φ.ker = ⊥ ∨ Φ.ker = sixDiag := by
    by_cases hz : (sixZ, sixZ) ∈ Φ.ker
    · right
      apply le_antisymm
      · intro u hu
        rcases hker_le u hu with rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      · intro u hu
        rw [sixDiag] at hu
        rcases (s1611e3_mem_zpowers_two s1611e3_sixDiag_mul_self).mp hu with rfl | rfl
        · exact Subgroup.one_mem _
        · exact hz
    · left
      apply le_antisymm
      · intro u hu
        rcases hker_le u hu with rfl | h
        · exact Subgroup.one_mem _
        · exact absurd (h ▸ hu) hz
      · exact bot_le
  exact ⟨Φ.ker, Φ, θ, hK, hsurj, rfl, hequiv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
