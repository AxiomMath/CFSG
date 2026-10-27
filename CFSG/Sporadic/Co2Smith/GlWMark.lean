module

public import CFSG.Sporadic.Co2Smith.GlWPres
public import CFSG.Sporadic.Co2Smith.GlC0Marking
public import CFSG.Sporadic.Co2Smith.GlWChartB

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.CosetTable

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Inj

variable
  {G : Type} [Group G]

theorem z0_mul_self_W : z0 * z0 = 1 := by
  have h := genLetters_mul_self 0
  rwa [genLetters_elt_zero] at h

theorem injective_of_D (ρ : C0c →* G) (hD : ∀ w : C0c, (w : K) ∈ Cz → ρ w = 1 → w = 1) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hzz : z0C0 * z0C0 = 1 := Subtype.ext z0_mul_self_W
  have hm : ρ (n * z0C0 * n⁻¹ * z0C0) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hn, one_mul, inv_one, mul_one, ← map_mul, hzz,
      map_one]
  obtain ⟨i, hi, hni⟩ := exists_conj_z0_eq_reflK n.2
  have hmv : ((n * z0C0 * n⁻¹ * z0C0 : C0c) : K) = reflK i * z0 := by
    show (n : K) * z0 * (n : K)⁻¹ * z0 = reflK i * z0
    rw [hni]
  have hm1 : n * z0C0 * n⁻¹ * z0C0 = 1 := by
    by_cases hi16 : i < 16
    · refine hD _ (mem_Cz_of_comm ?_) hm
      rw [hmv]
      calc reflK i * z0 * z0 = reflK i := by rw [mul_assoc, z0_mul_self_W, mul_one]
        _ = z0 * (reflK i * z0) := by
          rw [← mul_assoc, ← (reflK_comm_z0_iff hi).2 hi16, mul_assoc, z0_mul_self_W, mul_one]
    · obtain ⟨hlt, hcomm⟩ := glWInj_spec (i := i - 16) (by omega)
      rw [show i - 16 + 16 = i by omega] at hcomm
      have hg := reflK_conj hlt
      set l := Native.glWInj[i - 16]!
      set g : C0c := ⟨rconjK l, rconjK_mem_C0c hlt⟩
      have hc : g⁻¹ * (n * z0C0 * n⁻¹ * z0C0) * g = 1 := by
        refine hD _ (mem_Cz_of_comm ?_) (by rw [map_mul, map_mul, hm, mul_one, map_inv,
          inv_mul_cancel])
        show (rconjK l)⁻¹ * ((n * z0C0 * n⁻¹ * z0C0 : C0c) : K) * rconjK l * z0 =
          z0 * ((rconjK l)⁻¹ * ((n * z0C0 * n⁻¹ * z0C0 : C0c) : K) * rconjK l)
        rw [hmv]
        calc (rconjK l)⁻¹ * (reflK i * z0) * rconjK l * z0 =
            (rconjK l)⁻¹ * (reflK i * z0) * (rconjK l * z0 * (rconjK l)⁻¹) * rconjK l := by
              group
          _ = (rconjK l)⁻¹ * (reflK i * z0 * reflK l) * rconjK l := by rw [hg]; group
          _ = (rconjK l)⁻¹ * (reflK l * (reflK i * z0)) * rconjK l := by rw [← hcomm]
          _ = ((rconjK l)⁻¹ * reflK l * rconjK l) *
              ((rconjK l)⁻¹ * (reflK i * z0) * rconjK l) := by group
          _ = z0 * ((rconjK l)⁻¹ * (reflK i * z0) * rconjK l) := by rw [← hg]; group
      calc n * z0C0 * n⁻¹ * z0C0 = g * (g⁻¹ * (n * z0C0 * n⁻¹ * z0C0) * g) * g⁻¹ := by group
        _ = 1 := by rw [hc, mul_one, mul_inv_cancel]
  have e : (n : K) * z0 * (n : K)⁻¹ * z0 = 1 := congrArg Subtype.val hm1
  refine hD n (mem_Cz_of_comm ?_) hn
  calc (n : K) * z0 = (n : K) * z0 * (n : K)⁻¹ * (z0 * z0) * n := by
        rw [z0_mul_self_W]; group
    _ = ((n : K) * z0 * (n : K)⁻¹ * z0) * (z0 * n) := by group
    _ = z0 * n := by rw [e, one_mul]

end Inj

section Rho

variable
  {G : Type} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz}
  {ψ : normalizer (Jc : Set K) →* G}

@[expose] noncomputable def wHomG (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) : PGw →* G :=
  PresentedGroup.toGroup (lift_glWRels (gLet φ ψ) fun _ hw => gLet_rel hψ hz hw)

@[expose] noncomputable def rhoW (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) : C0c →* G :=
  (wHomG hψ hz).comp wEquivC.symm.toMonoidHom

theorem wHomG_of (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) (i : Fin 7) :
    wHomG hψ hz (PresentedGroup.of i) = gLet φ ψ i :=
  PresentedGroup.toGroup.of _

theorem rhoW_w7C (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) {k : ℕ} (hk : k < 7) :
    rhoW hψ hz (w7C k) = gLet φ ψ k := by
  show wHomG hψ hz (wEquivC.symm (w7C k)) = gLet φ ψ k
  rw [wEquivC_symm_w7C hk, wHomG_of]

theorem rhoW_D (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) (w : C0c) (hw : (w : K) ∈ Cz) :
    rhoW hψ hz w = phiH φ ⟨w, hw⟩ := by
  refine eq_phiH_of_gen φ _ (fun k hk h0 h1 => ?_) w hw
  have e0 : (⟨_, h0⟩ : C0c) = w7C k := Subtype.ext (w7Letters_elt_lt hk).symm
  rw [e0]
  exact (rhoW_w7C hψ hz (by omega)).trans (gLet_of_ne φ ψ (by omega))

theorem rhoW_comm (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) (w : C0c) :
    rhoW hψ hz w * phiH φ α3c = phiH φ α3c * rhoW hψ hz w := by
  have hext : (MulAut.conj (phiH φ α3c)).toMonoidHom.comp (wHomG hψ hz) = wHomG hψ hz := by
    apply PresentedGroup.ext
    intro i
    rw [MonoidHom.comp_apply, wHomG_of]
    show phiH φ α3c * gLet φ ψ i * (phiH φ α3c)⁻¹ = gLet φ ψ i
    rw [mul_inv_eq_iff_eq_mul]
    by_cases hi : (i : ℕ) = 6
    · rw [hi, gLet_six]
      have hδα := (mem_C0c.1 δ1hK_mem_C0c).1
      have hv : δ1hK * (α3c : K) * δ1hK⁻¹ ∈ Cz := by
        show δ1hK * α3K * δ1hK⁻¹ ∈ Cz
        rw [δ1hK_conj_of_comm hδα.symm]
        exact α3K_mem_Cz
      have h := dG_conj hψ α3c α3K_mem_N hv
      have e : (⟨δ1hK * (α3c : K) * δ1hK⁻¹, hv⟩ : Cz) = α3c :=
        Subtype.ext (δ1hK_conj_of_comm hδα.symm)
      rw [e, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    · rw [gLet_of_ne φ ψ hi]
      exact (phiH_comm_iff φ).2
        (Subtype.ext (mem_C0c.1 (mem_inf.1 (genLetters_mem_D i)).1).1)
  obtain ⟨p, rfl⟩ := wEquivC.surjective w
  have e : rhoW hψ hz (wEquivC p) = wHomG hψ hz p := by
    show wHomG hψ hz (wEquivC.symm (wEquivC p)) = _
    rw [MulEquiv.symm_apply_apply]
  have h' : phiH φ α3c * wHomG hψ hz p * (phiH φ α3c)⁻¹ = wHomG hψ hz p :=
    DFunLike.congr_fun hext p
  rw [mul_inv_eq_iff_eq_mul] at h'
  rw [e]
  exact h'.symm

theorem exists_smithC0Marking_of_chart (hψ : IsNJChart φ ψ) (hz : phiH φ z0C = z) :
    ∃ ρ : C0c →* G, SmithC0Marking φ α3c ρ := by
  refine ⟨rhoW hψ hz, injective_of_D _ fun w hw h1 => ?_, rhoW_comm hψ hz, rhoW_D hψ hz⟩
  rw [rhoW_D hψ hz w hw] at h1
  have h2 : (⟨w, hw⟩ : Cz) = 1 := (phiH_injective φ) (h1.trans (map_one _).symm)
  have h3 : (w : K) = 1 := congrArg Subtype.val h2
  exact Subtype.ext h3

end Rho

end CFSG.Sporadic.Co2Smith
