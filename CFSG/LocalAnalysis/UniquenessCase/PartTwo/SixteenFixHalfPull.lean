module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.F918Z8Ex2a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {X Y : Type} [CommGroup X] [CommGroup Y]

theorem s16fh_realizes_pull {A : Subgroup (MulAut X)} {B : Subgroup (MulAut Y)} (ρ : ↥A ≃* ↥B)
    (κ : X →* Y)
    (hκ : ∀ (a : ↥A) (x : X), κ ((a : MulAut X) x) = ((ρ a : ↥B) : MulAut Y) (κ x))
    {U : Subgroup X} (hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) {S : Subgroup Y} (hS : S ≤ U.map κ)
    {D : FFModel} (hR : D.Realizes B S ⊥) :
    D.Realizes A (U ⊓ S.comap κ) (U ⊓ κ.ker) := by
  have hSinv : ∀ h : ↥B, ∀ u ∈ S, (h : MulAut Y) u ∈ S := by
    obtain ⟨_, _, _, _, hSinv, _, _, _, _, _, _, _⟩ := hR
    exact hSinv
  let U' : Subgroup X := U ⊓ S.comap κ
  let s : ↥U' →* ↥S := (κ.comp U'.subtype).codRestrict S fun u => u.2.2
  have hs_coe : ∀ u : ↥U', ((s u : ↥S) : Y) = κ (u : X) := fun _ => rfl
  have hU'inv : ∀ a ∈ A, ∀ u ∈ U', a u ∈ U' := by
    intro a ha u hu
    obtain ⟨huU, huS⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr ⟨hU a ha u huU, ?_⟩
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_comap] at huS
    rw [hκ ⟨a, ha⟩ u]
    exact hSinv (ρ ⟨a, ha⟩) (κ u) huS
  have hs : Function.Surjective s := by
    intro y
    obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp (hS y.2)
    refine ⟨⟨u, Subgroup.mem_inf.mpr ⟨hu, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [Subgroup.mem_comap]
      rw [huy]
      exact y.2
    · rw [hs_coe]
      exact huy
  have hequiv : ∀ (b : ↥B) (u : ↥U'),
      ((s ⟨((ρ.symm.toMonoidHom b : ↥A) : MulAut X) (u : X),
          hU'inv _ (ρ.symm.toMonoidHom b).2 (u : X) u.2⟩ : ↥S) : Y) =
        (b : MulAut Y) ((s u : ↥S) : Y) := by
    intro b u
    rw [hs_coe, hs_coe]
    change κ (((ρ.symm b : ↥A) : MulAut X) (u : X)) = (b : MulAut Y) (κ (u : X))
    rw [hκ (ρ.symm b) (u : X), ρ.apply_symm_apply]
  have hker_eq : (s.ker).map U'.subtype = U ⊓ κ.ker := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := Subgroup.mem_map.mp hx
      have hku : κ (u : X) = 1 := by
        have h2 := Subtype.ext_iff.mp (MonoidHom.mem_ker.mp hu)
        rw [hs_coe u] at h2
        simpa using h2
      refine Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_ker.mpr ?_⟩
      · rw [← hxu]
        exact (Subgroup.mem_inf.mp u.2).1
      · rw [← hxu]
        exact hku
    · intro hx
      obtain ⟨hxU, hxker⟩ := Subgroup.mem_inf.mp hx
      have hxU' : x ∈ U' := Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_comap.mpr (by
        rw [MonoidHom.mem_ker.mp hxker]
        exact S.one_mem)⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxU'⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      exact Subtype.ext (by rw [hs_coe]; simpa using MonoidHom.mem_ker.mp hxker)
  have hres := s16c11_v1_realizes_comp (W := X) (W' := Y) (A := A) (B := B)
    ρ.symm.toMonoidHom ρ.symm.surjective hU'inv s hs hequiv hR
  rw [hker_eq] at hres
  exact hres

theorem s16fh_sumOfNat_pull {A : Subgroup (MulAut X)} {B : Subgroup (MulAut Y)} (κ : X →* Y)
    {U : Subgroup X}
    {P : Subgroup (MulAut Y) → Subgroup Y → Subgroup Y → Prop}
    {P' : Subgroup (MulAut X) → Subgroup X → Subgroup X → Prop}
    (hP : ∀ S : Subgroup Y, S ≤ U.map κ → P B S ⊥ → P' A (U ⊓ S.comap κ) (U ⊓ κ.ker))
    {k : ℕ} (hsum : SumOfNat P B (U.map κ) ⊥ k) : SumOfNat P' A U (U ⊓ κ.ker) k := by
  obtain ⟨S, _hZS, hind, hsup, hPS⟩ := hsum
  have hsup' : ⨆ i, S i = U.map κ := by
    simpa only [bot_sup_eq] using hsup
  have hSle : ∀ i, S i ≤ U.map κ := fun i => hsup' ▸ le_iSup S i
  let J : Fin k → Subgroup X := fun i => U ⊓ (S i).comap κ
  let K : Subgroup X := U ⊓ κ.ker
  have hKJ : ∀ i, K ≤ J i := by
    intro i x hx
    obtain ⟨hxU, hxker⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_comap.mpr (by
      rw [MonoidHom.mem_ker.mp hxker]
      exact (S i).one_mem)⟩
  have hJU : (⨆ i, J i) ≤ U := iSup_le fun _ => inf_le_left
  have hindJ : ∀ i, J i ⊓ (K ⊔ ⨆ (j : Fin k) (_ : j ≠ i), J j) ≤ K := by
    intro i x hx
    obtain ⟨hxJ, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxU, hxSi⟩ := Subgroup.mem_inf.mp hxJ
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx2
    have haκ : κ a = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp ha).2
    have hbκ : κ b ∈ ⨆ (j : Fin k) (_ : j ≠ i), S j := by
      refine Subgroup.iSup_induction (fun j => ⨆ (_ : j ≠ i), J j) hb
        (C := fun z => κ z ∈ ⨆ (j : Fin k) (_ : j ≠ i), S j) ?_ ?_ ?_
      · intro j z hz
        refine Subgroup.iSup_induction (fun _ : j ≠ i => J j) hz
          (C := fun z => κ z ∈ ⨆ (j' : Fin k) (_ : j' ≠ i), S j') ?_ ?_ ?_
        · intro hj z hz
          exact Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hj
            (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hz).2))
        · simpa using Subgroup.one_mem (⨆ (j' : Fin k) (_ : j' ≠ i), S j')
        · intro x y hx hy
          rw [map_mul]
          exact mul_mem hx hy
      · simpa using Subgroup.one_mem (⨆ (j : Fin k) (_ : j ≠ i), S j)
      · intro x y hx hy
        rw [map_mul]
        exact mul_mem hx hy
    have hxκ : κ x = κ b := by rw [← hab, map_mul, haκ, one_mul]
    have hxS : κ x ∈ S i := Subgroup.mem_comap.mp hxSi
    have hxbot : κ x ∈ (⊥ : Subgroup Y) := by
      have hhin := hind i
      rw [bot_sup_eq] at hhin
      exact hhin (Subgroup.mem_inf.mpr ⟨hxS, hxκ ▸ hbκ⟩)
    exact Subgroup.mem_inf.mpr ⟨hxU, MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hxbot)⟩
  have hsupJ : K ⊔ ⨆ i, J i = U := by
    refine le_antisymm (sup_le inf_le_left (iSup_le fun _ => inf_le_left)) ?_
    intro w hw
    have hwκ : κ w ∈ ⨆ i, S i := by
      rw [hsup']
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hyprod⟩ := d321i_exists_prod_of_mem_iSup S hwκ
    have hlift : ∀ i, ∃ u : X, u ∈ U ∧ κ u = y i := fun i =>
      Subgroup.mem_map.mp (hSle i (hy i))
    choose u hu using hlift
    have huU : ∀ i, u i ∈ U := fun i => (hu i).1
    have hκu : ∀ i, κ (u i) = y i := fun i => (hu i).2
    have huJ : ∀ i, u i ∈ J i := fun i =>
      Subgroup.mem_inf.mpr ⟨huU i, Subgroup.mem_comap.mpr (hκu i ▸ hy i)⟩
    have hPmem : (∏ i, u i) ∈ ⨆ i, J i :=
      Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (huJ i)
    have hkin : w * (∏ i, u i)⁻¹ ∈ K := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem hw (inv_mem (hJU hPmem)), MonoidHom.mem_ker.mpr ?_⟩
      have hmapP : κ (∏ i, u i) = ∏ i, y i := by
        rw [map_prod κ u Finset.univ]
        exact Finset.prod_congr rfl fun i _ => hκu i
      rw [map_mul, map_inv, hmapP, hyprod]
      exact mul_inv_cancel _
    have hw_eq : (w * (∏ i, u i)⁻¹) * (∏ i, u i) = w := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← hw_eq]
    exact Subgroup.mul_mem_sup hkin hPmem
  exact ⟨J, hKJ, hindJ, hsupJ, fun i => hP (S i) (hSle i) (hPS i)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
