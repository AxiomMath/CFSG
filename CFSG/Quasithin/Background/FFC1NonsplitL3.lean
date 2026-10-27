module

public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.L3

section Generic

variable {V : Type*} [CommGroup V]

theorem mem_stabSub_of_inv_aux {W : Subgroup V} {g : MulAut V} (h1 : ∀ w ∈ W, g w ∈ W)
    (h2 : ∀ w ∈ W, g⁻¹ w ∈ W) : g ∈ stabSub W := by
  intro u
  refine ⟨fun hu => ?_, h1 u⟩
  have := h2 _ hu
  simpa using this

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem le_of_l3Data {L M : Subgroup (MulAut V)} {U C : Subgroup V} (D : L3Data L U C)
    (hLM : L ≤ M) (hMU : ∀ g ∈ M, ∀ u ∈ U, g u ∈ U) (hMC : ∀ g ∈ M, ∀ c ∈ C, g c ∈ C)
    (hfaith : M ⊓ centSec U C = ⊥) : M ≤ L := by
  intro t ht
  have htU : ∀ u ∈ U, t u ∈ U := hMU t ht
  have htC : ∀ c ∈ C, t c ∈ C := hMC t ht
  have htiC : ∀ c ∈ C, t⁻¹ c ∈ C := hMC t⁻¹ (M.inv_mem ht)
  let tU : ↥U →* ↥U :=
    ((t : V ≃* V).toMonoidHom.comp U.subtype).codRestrict U (fun u => htU u u.2)
  let ψ : ↥U →* Multiplicative L3.Vec := D.β.comp tU
  have hψ : ∀ u : ↥U, ψ u = D.β ⟨t (u : V), htU _ u.2⟩ := fun u => rfl
  have hker : D.β.ker ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxC : (x : V) ∈ C := (D.ker_β x).1 hx
    rw [hψ]
    exact (D.ker_β _).2 (htC _ hxC)
  let φ : Multiplicative L3.Vec →* Multiplicative L3.Vec :=
    MonoidHom.liftOfSurjective D.β D.β_surj ⟨ψ, hker⟩
  have hφ : ∀ u : ↥U, φ (D.β u) = D.β ⟨t (u : V), htU _ u.2⟩ := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply D.β (Function.surjInv D.β_surj)
      (Function.rightInverse_surjInv D.β_surj) ⟨ψ, hker⟩ u
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨u, rfl⟩ := D.β_surj x
    rw [hφ] at hx
    have h1 : t (u : V) ∈ C := (D.ker_β _).1 hx
    have h2 : (u : V) ∈ C := by simpa using htiC _ h1
    exact (D.ker_β u).2 h2
  let f : L3.Vec →+ L3.Vec := AddMonoidHom.toMultiplicative.symm φ
  have hf : ∀ v, f v = Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := fun v => rfl
  have hfinj : Function.Injective f := by
    intro v w hvw
    rw [hf, hf] at hvw
    exact Multiplicative.ofAdd.injective (hφinj (Multiplicative.toAdd.injective hvw))
  let fl : L3.Vec →ₗ[ZMod 2] L3.Vec := f.toZModLinearMap 2
  let Mx : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' fl
  have hMx : ∀ v, Mx.mulVec v = f v := fun v => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hunit : IsUnit Mx := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    apply hfinj
    rw [← hMx, ← hMx]
    exact hvw
  have hdet : Mx.det = 1 := by
    have h1 := ((Matrix.isUnit_iff_isUnit_det Mx).1 hunit).ne_zero
    revert h1
    generalize Mx.det = y
    revert y
    decide
  let γ : L3.Γ := ⟨Mx, hdet⟩
  have hγ : ∀ v, act γ v = f v := fun v => hMx v
  have hβt : ∀ (u : ↥U) (hu : t (u : V) ∈ U),
      D.β ⟨t (u : V), hu⟩ = Multiplicative.ofAdd (act γ (Multiplicative.toAdd (D.β u))) := by
    intro u hu
    rw [← hφ u, hγ, hf]
    rfl
  have hsL : D.rho γ ∈ L := D.rho_mem γ
  have hsM : D.rho γ ∈ M := hLM hsL
  have ht'M : (D.rho γ)⁻¹ * t ∈ M := M.mul_mem (M.inv_mem hsM) ht
  have ht'stab : (D.rho γ)⁻¹ * t ∈ stabSub U :=
    mem_stabSub_of_inv_aux (hMU _ ht'M) (hMU _ (M.inv_mem ht'M))
  have hcent : (D.rho γ)⁻¹ * t ∈ centSec U C := by
    refine ⟨ht'stab, fun w hw => ?_⟩
    have hmem : D.rho γ⁻¹ (t w) ∈ U := D.inv_U _ (D.rho_mem _) _ (htU w hw)
    have h1 := D.β_rho γ⁻¹ (t w) (htU w hw) hmem
    rw [hβt ⟨w, hw⟩ (htU w hw), toAdd_ofAdd, act_inv_act] at h1
    have h2 : D.β ⟨D.rho γ⁻¹ (t w), hmem⟩ = D.β ⟨w, hw⟩ := by
      rw [h1]
      rfl
    have h3 : ((⟨D.rho γ⁻¹ (t w), hmem⟩ : ↥U) * (⟨w, hw⟩ : ↥U)⁻¹) ∈ D.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv D.β, h2, mul_inv_cancel]
    have h4 := (D.ker_β _).1 h3
    have h5 : (D.rho γ)⁻¹ * t = D.rho γ⁻¹ * t := by rw [map_inv]
    rw [h5]
    exact h4
  have hmem : (D.rho γ)⁻¹ * t ∈ M ⊓ centSec U C := ⟨ht'M, hcent⟩
  rw [hfaith, Subgroup.mem_bot] at hmem
  have : t = D.rho γ := by
    calc t = D.rho γ * ((D.rho γ)⁻¹ * t) := by group
      _ = D.rho γ := by rw [hmem, mul_one]
  rw [this]
  exact hsL

end Generic

theorem sylow_le_of_binaryNaturalSL_three {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hT : IsSylowTwoOf T G) (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1) : T ≤ L := by
  obtain ⟨-, -, hGU, hGC, -, hfM⟩ := B5.secConfig hV h hU hT (C := fixV L ⊓ commV L) rfl
  obtain ⟨D⟩ := hnat.toL3Coord
  have hLG : L ≤ G := B5.le_G h
  have hMG : L ⊔ T ≤ G := sup_le hLG hT.1
  exact le_trans le_sup_right (le_of_l3Data D le_sup_left
    (fun g hg u hu => ((mem_stabSub.1 (hGU (hMG hg))) u).2 hu)
    (fun g hg c hc => ((mem_stabSub.1 (hGC (hMG hg))) c).2 hc) hfM)

end FFC

end CFSG.Quasithin
