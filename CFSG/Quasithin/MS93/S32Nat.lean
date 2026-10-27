module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.MS93.ASIrr

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped Matrix

section NatReal

variable {V : Type*} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {H : Subgroup (MulAut V)} {I Z : Subgroup V}
  {π : ↥Γ →* ↥H}

@[expose] def IsTransNZ (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) : Prop :=
  ∀ x y : ι → F, x ≠ 0 → y ≠ 0 →
    ∃ γ : ↥Γ, ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = y

theorem isTransNZ_statedSL3 : IsTransNZ (CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
  statedSL3_transitive

theorem natReal_coord (h : (FFModel.nat Γ).RealizesVia H I Z π) :
    ∃ β : ↥I →* Multiplicative (ι → F), Function.Surjective β ∧
      (∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥I) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ I),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
            (Multiplicative.toAdd (β u))) :=
  FFModel.RealizesVia.coord rfl rfl h

theorem natReal_fixed (htr : IsTransNZ Γ) (h2 : ∃ x y : ι → F, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y)
    (h : (FFModel.nat Γ).RealizesVia H I Z π) {v : V} (hv : v ∈ I)
    (hfix : ∀ g ∈ H, g v = v) : v ∈ Z := by
  obtain ⟨β, -, hβk, hβe⟩ := natReal_coord h
  rw [← hβk ⟨v, hv⟩]
  by_contra hne
  set x := Multiplicative.toAdd (β ⟨v, hv⟩) with hx
  have hx0 : x ≠ 0 := fun h0 => hne (by
    apply Multiplicative.toAdd.injective
    rw [← hx, h0]
    rfl)
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  have hy : ∃ y : ι → F, y ≠ 0 ∧ y ≠ x := by
    by_cases hax : a = x
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨y, hy0, hyx⟩ := hy
  obtain ⟨γ, hγ⟩ := htr x y hx0 hy0
  have hu : ((π γ : ↥H) : MulAut V) v ∈ I := by rw [hfix _ (π γ).2]; exact hv
  have h1 := hβe γ ⟨v, hv⟩ hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) v, hu⟩ : ↥I) = ⟨v, hv⟩ :=
    Subtype.ext (hfix _ (π γ).2)
  rw [h2] at h1
  apply hyx
  rw [← hγ]
  have h3 := congrArg Multiplicative.toAdd h1
  rw [toAdd_ofAdd] at h3
  rw [← hx] at h3
  exact h3.symm

theorem natReal_ne [Nonempty ι] (h : (FFModel.nat Γ).RealizesVia H I Z π) : I ≠ Z := by
  obtain ⟨β, hβs, hβk, -⟩ := natReal_coord h
  intro hIZ
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (fun _ => 1))
  have h1 : β u = 1 := (hβk u).mpr (hIZ ▸ u.2)
  rw [h1] at hu
  have := congrArg
    (fun m : Multiplicative (ι → F) => Multiplicative.toAdd m (Classical.arbitrary ι)) hu
  simp at this

theorem natReal_inv_eq (htr : IsTransNZ Γ) (h : (FFModel.nat Γ).RealizesVia H I Z π)
    {J : Subgroup V} (hJ : ∀ g ∈ H, ∀ w ∈ J, g w ∈ J) (hZJ : Z ≤ J) (hJI : J ≤ I) :
    J = Z ∨ J = I := by
  obtain ⟨β, hβs, hβk, hβe⟩ := natReal_coord h
  by_cases hJZ : J ≤ Z
  · exact Or.inl (le_antisymm hJZ hZJ)
  · right
    refine le_antisymm hJI fun u hu => ?_
    obtain ⟨w, hwJ, hwZ⟩ := Set.not_subset.mp hJZ
    have hx0 : Multiplicative.toAdd (β ⟨w, hJI hwJ⟩) ≠ 0 := fun h0 => hwZ ((hβk _).mp (by
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl))
    by_cases hu0 : Multiplicative.toAdd (β ⟨u, hu⟩) = 0
    · have : (u : V) ∈ Z := (hβk ⟨u, hu⟩).mp (by
        apply Multiplicative.toAdd.injective
        rw [hu0]
        rfl)
      exact hZJ this
    · obtain ⟨γ, hγ⟩ := htr _ _ hx0 hu0
      have hgw : ((π γ : ↥H) : MulAut V) w ∈ J := hJ _ (π γ).2 w hwJ
      have h1 := hβe γ ⟨w, hJI hwJ⟩ (hJI hgw)
      rw [hγ, ofAdd_toAdd] at h1
      have h2 : ((⟨((π γ : ↥H) : MulAut V) w, hJI hgw⟩ : ↥I)⁻¹ * ⟨u, hu⟩ : ↥I) ∈
          β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : ((((⟨((π γ : ↥H) : MulAut V) w, hJI hgw⟩ : ↥I)⁻¹ * ⟨u, hu⟩ : ↥I) : V)) ∈ Z :=
        (hβk _).mp h2
      have h4 : (u : V) = ((π γ : ↥H) : MulAut V) w *
          ((((⟨((π γ : ↥H) : MulAut V) w, hJI hgw⟩ : ↥I)⁻¹ * ⟨u, hu⟩ : ↥I) : V)) := by
        simp
      rw [h4]
      exact J.mul_mem hgw (hZJ h3)

end NatReal

end CFSG.Quasithin.MS93.S32
