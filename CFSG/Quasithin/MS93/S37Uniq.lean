module

public import CFSG.Quasithin.MS93.S37Part

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

section Good

variable (θ : MulAut ↥(T1 M T L))
  (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
  (hQQ : ∀ x ∈ pCoreOf 2 M ⊓ Qt M θ, ∃ u ∈ C.Usub (perp (pt₀ F)), u⁻¹ * x ∈ Dq M L)
  (hDtQ : Dt M L θ ≤ pCoreOf 2 M)

theorem Usub_perp_le_Qt (hE : C.rhoIm (Ut M T L θ) = X₂ F) :
    C.Usub (perp (pt₀ F)) ≤ Qt M θ := by
  intro u hu
  obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
  rw [C.Qt_eq C.pCore_le_T1 T1_le_T]
  refine ⟨C.Uq_le_T1 huU, ?_⟩
  have hfix : C.N.co ⟨u, huU⟩ ∈ fixSp (C.rhoIm (Ut M T L θ)) := by
    rw [hE, fixSp_X₂]
    exact hco
  exact (C.co_mem_fixSp_iff ((tImage_le θ _).trans T1_le_sup) ⟨u, huU⟩).1 hfix

include hQUD hQQ hDtQ in
theorem sq_mem_Dq_of_Qt (hE : C.rhoIm (Ut M T L θ) = X₂ F) {y : G} (hy : y ∈ Qt M θ) :
    y ^ 2 ∈ Dq M L := by
  obtain ⟨x, hxT, hxQ, rfl⟩ := mem_tImage.1 hy
  obtain ⟨u, hu, hd⟩ := hQUD x hxQ
  have huT : u ∈ T1 M T L := C.Uq_le_T1 hu
  have hdT : u⁻¹ * x ∈ T1 M T L := (T1 M T L).mul_mem ((T1 M T L).inv_mem huT) hxT
  set u' : G := ((θ ⟨u, huT⟩ : ↥(T1 M T L)) : G)
  set d' : G := ((θ ⟨u⁻¹ * x, hdT⟩ : ↥(T1 M T L)) : G)
  have hu' : u' ∈ Ut M T L θ := mem_tImage.2 ⟨u, huT, hu, rfl⟩
  have hd'Dt : d' ∈ Dt M L θ := mem_tImage.2 ⟨_, hdT, hd, rfl⟩
  have hd'Q : d' ∈ pCoreOf 2 M := hDtQ hd'Dt
  have hd'Qt : d' ∈ Qt M θ := tImage_mono' θ (inf_le_left : Dq M L ≤ pCoreOf 2 M) hd'Dt
  have hxy : ((θ ⟨x, hxT⟩ : ↥(T1 M T L)) : G) = u' * d' := by
    have e : (⟨x, hxT⟩ : ↥(T1 M T L)) = ⟨u, huT⟩ * ⟨u⁻¹ * x, hdT⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul]
    rfl
  obtain ⟨u₀, hu₀, hd₀⟩ := hQQ d' ⟨hd'Q, hd'Qt⟩
  have hu₀U := C.Usub_le _ hu₀
  have hcomm : u' * u₀ = u₀ * u' := by
    have h1 := C.Usub_perp_le_Qt θ hE hu₀
    rw [C.Qt_eq C.pCore_le_T1 T1_le_T] at h1
    exact Subgroup.mem_centralizer_iff.1 h1.2 u' hu'
  set d₀ := u₀⁻¹ * d' with hd₀def
  have hd'e : d' = u₀ * d₀ := by rw [hd₀def]; group
  have hu'2 : u' ^ 2 = 1 := C.Ut_sq θ hu'
  have hconjD : u'⁻¹ * d₀ * u' ∈ Dq M L := by
    have hDn : u'⁻¹ ∈ Subgroup.normalizer (Dq M L : Set G) :=
      le_normalizer_Dq C.h.le_normalizer (C.Ut_le_M T1_le_T θ ((Ut M T L θ).inv_mem hu'))
    have := (Subgroup.mem_normalizer_iff.1 hDn d₀).1 hd₀
    simpa using this
  have hu₀c : u₀ * (u'⁻¹ * d₀ * u') = (u'⁻¹ * d₀ * u') * u₀ :=
    (comm_of_mem_Uq C.h hu₀U hconjD.1).symm
  have e2 : (u' * d') ^ 2 = (u'⁻¹ * d₀ * u') * d₀ := by
    have hu'i : u'⁻¹ = u' := by
      rw [← mul_left_cancel_iff (a := u'), mul_inv_cancel, ← sq, hu'2]
    rw [hd'e, sq]
    calc u' * (u₀ * d₀) * (u' * (u₀ * d₀))
        = u' * u₀ * d₀ * u' * u₀ * d₀ := by group
      _ = u₀ * u' * d₀ * u' * u₀ * d₀ := by rw [hcomm]
      _ = u₀ * (u'⁻¹ * d₀ * u') * u₀ * d₀ := by rw [hu'i]; group
      _ = (u'⁻¹ * d₀ * u') * u₀ * u₀ * d₀ := by rw [hu₀c]
      _ = (u'⁻¹ * d₀ * u') * (u₀ ^ 2) * d₀ := by rw [sq]; group
      _ = (u'⁻¹ * d₀ * u') * d₀ := by rw [Sp4L.uq_sq C.h hu₀U, mul_one]
  rw [hxy, e2]
  exact (Dq M L).mul_mem hconjD hd₀

include hQUD hQQ hDtQ in
theorem conj_mem_Qt (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {g : G} (hg : g ∈ L ⊔ pCoreOf 2 M) (hgP : C.rho ⟨g, hg⟩ ∈ P₂ F)
    {y : G} (hy : y ∈ Qt M θ) : g * y * g⁻¹ ∈ Qt M θ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  set K := L ⊔ pCoreOf 2 M with hK
  have hyK : y ∈ K := T1_le_sup (tImage_le θ _ hy)
  have hwK : g * y * g⁻¹ ∈ K := K.mul_mem (K.mul_mem hg hyK) (K.inv_mem hg)
  have hgM : g ∈ M := C.sup_le_M hg
  have hUperp := C.Usub_perp_le_Qt θ hE
  have hρw : C.rho ⟨_, hwK⟩ = C.rho ⟨g, hg⟩ * C.rho ⟨y, hyK⟩ * (C.rho ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hyX : C.rho ⟨y, hyK⟩ ∈ X₂ F := hN ▸ (C.mem_rhoIm).2 ⟨y, hyK, hy, rfl⟩
  have hwX : C.rho ⟨_, hwK⟩ ∈ X₂ F := by
    rw [hρw]
    exact (Subgroup.mem_normalizer_iff.1 (P₂_le_normalizer_X₂ hgP) _).1 hyX
  obtain ⟨z, hzK, hz, hzw⟩ := (C.mem_rhoIm).1 (hN.symm ▸ hwX : C.rho ⟨_, hwK⟩ ∈ C.rhoIm (Qt M θ))
  set f := z⁻¹ * (g * y * g⁻¹) with hf
  have hfK : f ∈ K := K.mul_mem (K.inv_mem hzK) hwK
  have hfQ : f ∈ pCoreOf 2 M := by
    rw [← C.rho_eq_one_iff ⟨f, hfK⟩]
    have e : (⟨f, hfK⟩ : ↥K) = (⟨z, hzK⟩ : ↥K)⁻¹ * ⟨_, hwK⟩ := rfl
    rw [e, map_mul, map_inv, hzw, inv_mul_cancel]
  have hwe : g * y * g⁻¹ = z * f := by rw [hf]; group
  obtain ⟨c, hc⟩ := mem_X₂_iff.1 hwX
  have hρg : C.rho ⟨g, hg⟩ ∈ MSP.stab (perp (pt₀ F)) := by rwa [stab_perp]
  by_cases hc0 : c = 0
  ·
    have hρy : C.rho ⟨y, hyK⟩ = 1 := by
      have h1 : C.rho ⟨_, hwK⟩ = 1 := by rw [← hc, hc0, transv_zero]
      rw [hρw] at h1
      have h2 : C.rho ⟨y, hyK⟩ = (C.rho ⟨g, hg⟩)⁻¹ * 1 * C.rho ⟨g, hg⟩ := by
        rw [← h1]; group
      rw [h2]; group
    have hyQ : y ∈ pCoreOf 2 M := (C.rho_eq_one_iff ⟨y, hyK⟩).1 hρy
    obtain ⟨u, hu, hd⟩ := hQQ y ⟨hyQ, hy⟩
    obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
    have hgu : g * u * g⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (C.hMU hgM) u).1 huU
    have hgd : g * (u⁻¹ * y) * g⁻¹ ∈ Dq M L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer hgM) _).1 hd
    have hco' : C.N.co ⟨g * u * g⁻¹, hgu⟩ ∈ perp (pt₀ F) := by
      rw [C.co_conj ⟨g, hg⟩ (u := ⟨u, huU⟩) rfl]
      exact mulVec_mem_of_mem_stab hρg hco
    have e : g * y * g⁻¹ = (g * u * g⁻¹) * (g * (u⁻¹ * y) * g⁻¹) := by group
    rw [e]
    exact (Qt M θ).mul_mem (hUperp ((C.mem_Usub).2 ⟨hgu, hco'⟩)) (hDQt hgd)
  ·
    rw [hwe]
    refine (Qt M θ).mul_mem hz ?_
    obtain ⟨u, hu, hd⟩ := hQUD f hfQ
    set e := u⁻¹ * f with he
    have hfe : f = u * e := by rw [he]; group
    have hzM : z ∈ M := C.sup_le_M hzK
    have hz2 : z ^ 2 ∈ Dq M L := C.sq_mem_Dq_of_Qt θ hQUD hQQ hDtQ hE hz
    have hw2 : (z * f) ^ 2 ∈ Dq M L := by
      rw [← hwe, show (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ by rw [sq, sq]; group]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer hgM) _).1
        (C.sq_mem_Dq_of_Qt θ hQUD hQQ hDtQ hE hy)
    have hzez : z⁻¹ * e * z ∈ Dq M L := by
      have := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_Dq C.h.le_normalizer (M.inv_mem hzM)) e).1 hd
      simpa using this
    have hzuz : z⁻¹ * u * z ∈ Uq M T L := by
      have := (Subgroup.mem_normalizer_iff.1 (C.hMU (M.inv_mem hzM)) u).1 hu
      simpa using this
    have hcomm : u * (z⁻¹ * e * z) = (z⁻¹ * e * z) * u :=
      (comm_of_mem_Uq C.h hu hzez.1).symm
    have hkey : (z⁻¹ * u * z) * u ∈ Dq M L := by
      have h1 : (z⁻¹ * u * z) * u =
          ((z ^ 2)⁻¹ * (z * f) ^ 2) * ((z⁻¹ * e * z) * e)⁻¹ := by
        rw [hfe, sq, sq]
        calc (z⁻¹ * u * z) * u
            = (z⁻¹ * u * z) * (u * (z⁻¹ * e * z)) * e * ((z⁻¹ * e * z) * e)⁻¹ := by group
          _ = (z⁻¹ * u * z) * ((z⁻¹ * e * z) * u) * e * ((z⁻¹ * e * z) * e)⁻¹ := by
              rw [hcomm]
          _ = ((z * z)⁻¹ * (z * (u * e) * (z * (u * e)))) * ((z⁻¹ * e * z) * e)⁻¹ := by
              group
      rw [h1]
      exact (Dq M L).mul_mem ((Dq M L).mul_mem ((Dq M L).inv_mem hz2) hw2)
        ((Dq M L).inv_mem ((Dq M L).mul_mem hzez hd))
    have hco0 : C.N.co ⟨(z⁻¹ * u * z) * u, (Uq M T L).mul_mem hzuz hu⟩ = 0 :=
      (C.N.co_eq_zero_iff _).2 ⟨(Uq M T L).mul_mem hzuz hu, hkey.2⟩
    have e1 : (⟨(z⁻¹ * u * z) * u, (Uq M T L).mul_mem hzuz hu⟩ : ↥(Uq M T L)) =
        ⟨z⁻¹ * u * z, hzuz⟩ * ⟨u, hu⟩ := rfl
    have hzi : (⟨z⁻¹, K.inv_mem hzK⟩ : ↥K) = (⟨z, hzK⟩ : ↥K)⁻¹ := rfl
    have e2 : C.N.co ⟨z⁻¹ * u * z, hzuz⟩ =
        mat (C.rho ⟨z⁻¹, K.inv_mem hzK⟩) *ᵥ C.N.co ⟨u, hu⟩ :=
      C.co_conj ⟨z⁻¹, K.inv_mem hzK⟩ (u := ⟨u, hu⟩) (by simp)
    rw [e1, C.N.co_mul, e2, hzi, map_inv, hzw, ← hc, transv_inv, transv_mulVec,
      form_e₁] at hco0
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : (-c * C.N.co ⟨u, hu⟩ (.inr 0)) • e₁ F = 0 := by
      have e3 : C.N.co ⟨u, hu⟩ + (-c * C.N.co ⟨u, hu⟩ (.inr 0)) • e₁ F + C.N.co ⟨u, hu⟩ =
          (-c * C.N.co ⟨u, hu⟩ (.inr 0)) • e₁ F + (2 : F) • C.N.co ⟨u, hu⟩ := by
        rw [two_smul]; abel
      rw [e3, h2, zero_smul, add_zero] at hco0
      exact hco0
    have h4 : -c * C.N.co ⟨u, hu⟩ (.inr 0) = 0 := by
      have := congrFun h3 (.inl 0)
      simpa [e₁] using this
    have h5 : C.N.co ⟨u, hu⟩ (.inr 0) = 0 :=
      (mul_eq_zero.1 h4).resolve_left (neg_ne_zero.2 hc0)
    rw [hfe]
    exact (Qt M θ).mul_mem (hUperp ((C.mem_Usub).2 ⟨hu, mem_perp_pt₀.2 h5⟩)) (hDQt hd)

end Good

end Cfg

end CFSG.Quasithin.MS93.S37
