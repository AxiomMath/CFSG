module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdGen
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr

public section

namespace CFSG.StandardType.LineU

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.StandardType.TypeA

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem inner_comm_of_heart_U (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A Y : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hV : ∀ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u → (∀ i, u i ^ p = 1) →
      MulAut.conj (φ D) ∈ A ⊓ Subgroup.centralizer (Y : Set (MulAut L')))
    {s : ↥(unitarySU 2 n K d)} (hs : MulAut.conj (φ s) ∈ Y) :
    ∀ a ∈ A, MulAut.conj (φ s) * a = a * MulAut.conj (φ s) := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hK hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζnorm : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hζ.pow_eq_one, one_pow]
  intro a ha
  have hsd : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
    refine isDiag_of_conj_comm_U hK (by omega) hφker hζnorm hζinv (fun k l _ D hD => ?_)
    exact Subgroup.mem_centralizer_iff.mp
      (hV D _ hD (fun i => pow_ggPairVec hζ.pow_eq_one i)).2 _ hs
  obtain ⟨t, hat⟩ := hdiag a ha
  exact (hat.mul_conj_comm hsd).symm

theorem comm_step_U {S : Type} [Group S] {g : S →* L'} (hgs : Function.Surjective g)
    {A Y : Subgroup (MulAut L')} {W : Set L'}
    (hWA : ∀ m ∈ W, ∀ a ∈ A, MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A)
    (hWY : ∀ m ∈ W, ∀ f ∈ Y, MulAut.conj m * f * (MulAut.conj m)⁻¹ ∈ Y)
    (hYA : ∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hinner : ∀ s : S, MulAut.conj (g s) ∈ Y → ∀ a ∈ A,
      MulAut.conj (g s) * a = a * MulAut.conj (g s)) :
    ∀ f ∈ Y, ∀ m ∈ W, ∀ a ∈ A, f * (MulAut.conj m * a * (MulAut.conj m)⁻¹) * f⁻¹ =
      MulAut.conj m * (f * a * f⁻¹) * (MulAut.conj m)⁻¹ := by
  intro f hf m hm a ha
  have hzY : MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹ ∈ Y :=
    Y.mul_mem (hWY m hm f hf) (Y.inv_mem hf)
  have hz : MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹ = MulAut.conj (m * (f m)⁻¹) := by
    have hfm : MulAut.conj (f m) = f * MulAut.conj m * f⁻¹ := by
      rw [TypeANbrDvd.mul_conj_eq_conj_apply_mul, mul_inv_cancel_right]
    rw [map_mul, map_inv, hfm]
    group
  obtain ⟨s, hs⟩ := hgs (m * (f m)⁻¹)
  have hzc : ∀ b ∈ A, (MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹) * b =
      b * (MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹) := by
    intro b hb
    rw [hz, ← hs]
    exact hinner s (by rw [hs, ← hz]; exact hzY) b hb
  have hx : f * (MulAut.conj m * a * (MulAut.conj m)⁻¹) * f⁻¹ ∈ A :=
    hYA f hf _ (hWA m hm a ha)
  calc f * (MulAut.conj m * a * (MulAut.conj m)⁻¹) * f⁻¹
      = (MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹) *
          (f * (MulAut.conj m * a * (MulAut.conj m)⁻¹) * f⁻¹) *
          (MulAut.conj m * f * (MulAut.conj m)⁻¹ * f⁻¹)⁻¹ := by
        rw [hzc _ hx, mul_inv_cancel_right]
    _ = MulAut.conj m * (f * a * f⁻¹) * (MulAut.conj m)⁻¹ := by group

theorem fix_of_heart_U (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 3 ≤ d) (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A Y : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hV : ∀ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u → (∀ i, u i ^ p = 1) →
      MulAut.conj (φ D) ∈ A ⊓ Subgroup.centralizer (Y : Set (MulAut L')))
    (hYA : ∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hstep : ∀ f ∈ Y, ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A,
      f * (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹) * f⁻¹ =
        MulAut.conj (φ (permSU hK σ)) * (f * a * f⁻¹) * (MulAut.conj (φ (permSU hK σ)))⁻¹)
    {f : MulAut L'} (hf : f ∈ Y) {a : MulAut L'} (ha : a ∈ A) (σ : Equiv.Perm (Fin d)) :
    MulAut.conj (φ (permSU hK σ)) * (f * a * f⁻¹ * a⁻¹) * (MulAut.conj (φ (permSU hK σ)))⁻¹ =
      f * a * f⁻¹ * a⁻¹ := by
  obtain ⟨t, hat⟩ := hdiag a ha
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have het : ActsDiagU φ
      (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹)
      (fun k => t (σ⁻¹ k) * (t k)⁻¹) := (hat.conj_perm hK σ).mul hat.inv
  have hprod : ∏ k, (t (σ⁻¹ k) * (t k)⁻¹) = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ⁻¹ t]
    exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
  have hnorm : ∀ k, (t (σ⁻¹ k) * (t k)⁻¹) ^ (2 ^ n + 1) = 1 := by
    intro k
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hat.ratio_pow hK hd hφker (hAp a ha) (σ⁻¹ k) k, one_pow]
  obtain ⟨De, hDe⟩ := exists_diagSU hK hnorm hprod
  have heq : MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹ =
      MulAut.conj (φ De) := ActsDiagU.unique hφs het (actsDiagU_conj hDe)
  have heA' : MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹ ∈
      A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) := by
    rw [heq]
    exact hV De _ hDe (fun k => hat.ratio_pow hK hd hφker (hAp a ha) (σ⁻¹ k) k)
  have hφe : f * (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹) *
      f⁻¹ = MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹ := by
    rw [Subgroup.mem_centralizer_iff.mp heA'.2 f hf, mul_inv_cancel_right]
  have h7 := hstep f hf σ a ha
  have hbA : f * a * f⁻¹ * a⁻¹ ∈ A := A.mul_mem (hYA f hf a ha) (A.inv_mem ha)
  have hcomm := IsElemAbelian.comm hA heA'.1 hbA
  calc MulAut.conj (φ (permSU hK σ)) * (f * a * f⁻¹ * a⁻¹) * (MulAut.conj (φ (permSU hK σ)))⁻¹
      = (MulAut.conj (φ (permSU hK σ)) * (f * a * f⁻¹) *
            (MulAut.conj (φ (permSU hK σ)))⁻¹) *
          (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹)⁻¹ := by group
    _ = (f * (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹) * f⁻¹) *
          (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹)⁻¹ := by
        rw [h7]
    _ = (f * (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹) *
            f⁻¹) *
          (f * a * f⁻¹ * a⁻¹) *
          (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹)⁻¹ := by
        group
    _ = (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹) *
          (f * a * f⁻¹ * a⁻¹) *
          (MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ * a⁻¹)⁻¹ := by
        rw [hφe]
    _ = f * a * f⁻¹ * a⁻¹ := by rw [hcomm, mul_inv_cancel_right]

theorem nbr_of_model_U (hK : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) [Finite L'] (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hA1 : Nat.card A ≠ 1)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    ∃ W : Set L',
      (∀ m ∈ W, ∀ a ∈ A, (m * (a m)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
      ∀ Y : Subgroup (MulAut L'),
        (∀ m ∈ W, ∀ a ∈ A, MulAut.conj m * a * (MulAut.conj m)⁻¹ ∈ A) →
        (∀ m ∈ W, ∀ f ∈ Y, MulAut.conj m * f * (MulAut.conj m)⁻¹ ∈ Y) →
        (∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A) →
        (∀ f ∈ Y, ∃ k : ℕ, ∀ a ∈ A, f ^ p ^ k * a = a * f ^ p ^ k) →
        ∀ f ∈ Y, ∀ a ∈ A, f * a = a * f := by
  classical
  have := Fact.mk hp
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  refine ⟨{x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hK σ)},
    weyl_W_prop hK (by omega) hφker hAp hdiag, ?_⟩
  intro Y hWA hWY hYA hYp
  set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
  have hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hK σ)) * a * (MulAut.conj (φ (permSU hK σ)))⁻¹ ∈ A' := by
    intro σ a ha
    have hn : φ (permSU hK σ) ∈ {x : L' | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hK σ)} :=
      ⟨σ, rfl⟩
    refine ⟨hWA _ hn a ha.1, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hχ := inv_conj_mem_of_conj_mem (hWY _ hn) hf
    have hcf := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ
    set c := MulAut.conj (φ (permSU hK σ))
    calc f * (c * a * c⁻¹) = c * ((c⁻¹ * f * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * f * c)) * c⁻¹ := by rw [hcf]
      _ = c * a * c⁻¹ * f := by group
  obtain ⟨a₀, ha₀, ha₀1, ha₀c⟩ :=
    exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
  have ha₀A' : a₀ ∈ A' := ⟨ha₀, Subgroup.mem_centralizer_iff.mpr fun f hf => ha₀c f hf⟩
  have hV : ∀ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u → (∀ i, u i ^ p = 1) →
      MulAut.conj (φ D) ∈ A' := fun D u hD hu =>
    conj_mem_of_invariant_U hK hp (by omega) hpq hφker hφs inf_le_left hsc hdiag hAp hA'inv
      ha₀A' ha₀1 hD hu
  have hinner : ∀ s : ↥(unitarySU 2 n K d), MulAut.conj (φ s) ∈ Y →
      ∀ a ∈ A, MulAut.conj (φ s) * a = a * MulAut.conj (φ s) := fun s hs =>
    inner_comm_of_heart_U hK hp hp2 hpq hd hφker hdiag hV hs
  have hstep := comm_step_U hφs hWA hWY hYA hinner
  intro f hf a ha
  have hbA : f * a * f⁻¹ * a⁻¹ ∈ A := A.mul_mem (hYA f hf a ha) (A.inv_mem ha)
  obtain ⟨tb, hbt⟩ := hdiag _ hbA
  have hfix := fun σ : Equiv.Perm (Fin d) =>
    fix_of_heart_U hK hp hpq (by omega) hφs hφker hA hdiag hV hYA
      (fun f hf σ a ha => hstep f hf _ ⟨σ, rfl⟩ a ha) hf ha σ
  have hb1 := hbt.eq_one_of_conj_perm hK (by omega) hφs hφker hfix
  calc f * a = f * a * f⁻¹ * a⁻¹ * a * f := by group
    _ = a * f := by rw [hb1, one_mul]

end CFSG.StandardType.LineU

end
