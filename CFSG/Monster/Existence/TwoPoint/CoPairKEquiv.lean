module

public import CFSG.Monster.Existence.TwoPoint.CoPairEquiv
public import CFSG.Certificates.Kernel.CoPairEqSound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native CFSG.KC.CoPair

attribute [local instance] kvLeft

theorem exists_hom_of_eqOK
    {a b : List ℕ} {w n N : ℕ} {D : EqData} (h : eqOK a b w n D = true) (hN : 0 < N)
    (e : ℕ → Fin N) (τa τb : Equiv.Perm (Fin N))
    (hea : ∀ l < n, e (f16 D.SA l) = τa (e l)) (heb : ∀ l < n, e (f16 D.SB l) = τb (e l))
    (hes : ∀ j : Fin N, ∃ l < n, e l = j) :
    ∃ Φ : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) →* Equiv.Perm (Fin N),
      Φ ⟨(xyK a)⁻¹, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = τa ∧
      Φ ⟨(xyK b)⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = τb := by
  classical
  obtain ⟨-, -, hmono, hlab, hA, hB, hrep⟩ := eqOK_sound h
  have hinj : ∀ i < D.m, ∀ j < D.m, f24 D.Q i = f24 D.Q j → i = j := fun i hi j hj hij => by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd hij (Nat.ne_of_lt (hmono i j h' hj))
    · exact absurd hij (Nat.ne_of_gt (hmono j i h' hi))
  let lab : ℕ → ℕ := fun i => r16 (f64 D.L i) 2
  let Ω : Set L2 := {x | ∃ i < D.m, dec (f24 D.Q i) = x}
  have hΩ : Ω.Finite := by
    have : Ω = (fun i => dec (f24 D.Q i)) '' Set.Iio D.m := by
      ext x
      simp [Ω]
    rw [this]
    exact (Set.finite_Iio D.m).image _
  let p : L2 → Fin N := fun x =>
    if hx : ∃ i < D.m, dec (f24 D.Q i) = x then e (lab (Classical.choose hx)) else ⟨0, hN⟩
  have hp : ∀ i < D.m, p (dec (f24 D.Q i)) = e (lab i) := fun i hi => by
    have hx : ∃ i' < D.m, dec (f24 D.Q i') = dec (f24 D.Q i) := ⟨i, hi, rfl⟩
    simp only [p, dite_eq_left hx]
    obtain ⟨hi', hdec⟩ := Classical.choose_spec hx
    rw [hinj _ hi' i hi (dec_injective (f24_lt _ _) (f24_lt _ _) hdec)]
  obtain ⟨Φ, h1, h2⟩ := exists_equivariant_hom (G := Kstab v0) (X := L2) hΩ p
    (fun j => by
      obtain ⟨l, hl, rfl⟩ := hes j
      obtain ⟨i, hi, rfl⟩ := hrep l hl
      exact ⟨_, ⟨i, hi, rfl⟩, hp i hi⟩)
    (xyK a)⁻¹ (xyK b)⁻¹ τa τb
    (fun x ⟨i, hi, hx⟩ => by
      subst hx
      rw [kvLeft_inv_smul, kOp_xyK_dec]
      obtain ⟨j, hj, hQ, hL⟩ := hA i hi
      rw [← hQ]
      exact ⟨⟨j, hj, rfl⟩, by rw [hp j hj, hp i hi]; exact (congrArg e hL).trans (hea _ (hlab i hi))⟩)
    (fun x ⟨i, hi, hx⟩ => by
      subst hx
      rw [kvLeft_inv_smul, kOp_xyK_dec]
      obtain ⟨j, hj, hQ, hL⟩ := hB i hi
      rw [← hQ]
      exact ⟨⟨j, hj, rfl⟩, by rw [hp j hj, hp i hi]; exact (congrArg e hL).trans (heb _ (hlab i hi))⟩)
  exact ⟨Φ, h1, h2⟩

theorem kvStab_equiv_of_eqOK
    {a b : List ℕ} {w n N : ℕ} {D : EqData} (h : eqOK a b w n D = true) (hN : 0 < N)
    (e : ℕ → Fin N) (τa τb : Equiv.Perm (Fin N))
    (hea : ∀ l < n, e (f16 D.SA l) = τa (e l)) (heb : ∀ l < n, e (f16 D.SB l) = τb (e l))
    (hes : ∀ j : Fin N, ∃ l < n, e l = j)
    {H : Subgroup (Equiv.Perm (Fin N))} (hH : Subgroup.closure {τa, τb} = H)
    (hcard : Nat.card (kvStab (dec w)) = Nat.card H) :
    Nonempty (kvStab (dec w) ≃* H) := by
  obtain ⟨hwa, hwb, -⟩ := eqOK_sound h
  obtain ⟨Φ, h1, h2⟩ := exists_hom_of_eqOK h hN e τa τb hea heb hes
  have hA : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) ≤ kvStab (dec w) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (kvStab (dec w)).inv_mem (by rw [mem_kvStab, kOp_xyK_dec, hwa])
    · exact (kvStab (dec w)).inv_mem (by rw [mem_kvStab, kOp_xyK_dec, hwb])
  have hrange : Φ.range = H := (range_eq_closure Φ h1 h2).trans hH
  have hle : Nat.card H ≤
      Nat.card ↥(Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0))) := by
    rw [← hrange]
    exact Nat.card_le_card_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hAeq : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) = kvStab (dec w) :=
    Subgroup.eq_of_le_of_card_ge hA (by rw [hcard]; exact hle)
  have hcardA : Nat.card ↥(Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0))) =
      Nat.card H := by
    rw [hAeq, hcard]
  have hbij : Function.Bijective Φ.rangeRestrict := by
    refine Φ.rangeRestrict_surjective.bijective_of_nat_card_le ?_
    rw [hrange, hcardA]
  exact ⟨(MulEquiv.subgroupCongr hAeq.symm).trans
    ((MulEquiv.ofBijective Φ.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.Monster.Existence.CoPair
