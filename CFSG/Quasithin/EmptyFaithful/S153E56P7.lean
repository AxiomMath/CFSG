module

public import CFSG.Quasithin.EmptyFaithful.S153E56P6

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Transv

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem rhoX_pi_eq {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) {u : ↥(UH153 T M V₁ Mc)}
    (hu : (u : G) ∈ Egp153 T M V₁ Mc y) :
    rhoX S hx (pi S.cx u) = pi S.cx u * sm (comm153 x (u : G)) (aa S) := by
  have hc := comm_XE S hx hu
  have e1 : x * (u : G) * x⁻¹ = ⁅x, (u : G)⁆ * u := by
    simp only [commutatorElement_def]
    group
  rw [rhoX_pi]
  rcases (mem_Z'_iff S).1 hc with h1 | h1
  · have h0 : comm153 x (u : G) = 0 := comm153_eq_zero_iff.2 h1
    rw [h0, sm_zero, mul_one]
    congr 1
    apply Subtype.ext
    show x * (u : G) * x⁻¹ = u
    rw [e1, h1, one_mul]
  · have h0 : comm153 x (u : G) = 1 :=
      comm153_eq_one_iff.2 (by rw [h1]; exact zp_ne_one S)
    rw [h0, sm_one]
    have e2 : (⟨x * (u : G) * x⁻¹, U_conj_mem (X_le_Mc S hx) u.2⟩ : ↥(UH153 T M V₁ Mc)) =
        ⟨zp S, zp_mem_U S⟩ * u := by
      apply Subtype.ext
      show x * (u : G) * x⁻¹ = zp S * u
      rw [e1, h1]
    rw [e2, map_mul, Ut_comm S.cx, aa_eq]

theorem exists_X (f : G → ZMod 2)
    (hadd : ∀ e ∈ Egp153 T M V₁ Mc y, ∀ e' ∈ Egp153 T M V₁ Mc y, f (e * e') = f e + f e')
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, f z = 0)
    (hZ' : ∀ z ∈ conjSubgroup (quasithinOmegaOneCenter T) y, f z = 0) :
    ∃ x ∈ Xgp153 T M V₁ Mc y, ∀ e ∈ Egp153 T M V₁ Mc y, comm153 x e = f e := by
  obtain ⟨p, hpU', hp⟩ := (exPair_U' S).rep (E_le_U' S) hadd (fun a _ ha => hZ' a ha)
  refine ⟨p, ?_, hp⟩
  rw [S.hG.X_eq]
  refine ⟨hpU', Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  have h1 : comm153 p z = 0 := by rw [hp z (Z_le_E S hz)]; exact hZ z hz
  exact (commutatorElement_eq_one_iff_mul_comm.1 (comm153_eq_zero_iff.1 h1)).symm

open scoped Classical in
theorem exists_rhoX (φ : Ut T M V₁ Mc → ZMod 2)
    (hadd : ∀ e ∈ Et1 T M V₁ Mc y, ∀ e' ∈ Et1 T M V₁ Mc y, φ (e * e') = φ e + φ e')
    (hφa : φ (aa S) = 0) :
    ∃ (x : G) (hx : x ∈ Xgp153 T M V₁ Mc y), ∀ e ∈ Et1 T M V₁ Mc y,
      rhoX S hx e = e * sm (φ e) (aa S) := by
  let f : G → ZMod 2 := fun e => if h : e ∈ UH153 T M V₁ Mc then φ (pi S.cx ⟨e, h⟩) else 0
  have hf : ∀ u : ↥(UH153 T M V₁ Mc), f (u : G) = φ (pi S.cx u) := fun u => by
    simp [f]
  have hφ1 : φ 1 = 0 := by
    have := hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at this
    have h2 : φ 1 + φ 1 = φ 1 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have hE : ∀ (e : G) (he : e ∈ Egp153 T M V₁ Mc y),
      pi S.cx ⟨e, E_le_U S he⟩ ∈ Et1 T M V₁ Mc y := fun e he =>
    (mem_Et1 S).2 ⟨⟨e, E_le_U S he⟩, he, rfl⟩
  obtain ⟨x, hx, hcomm⟩ := exists_X S f
    (fun e he e' he' => by
      have h1 : f e = φ (pi S.cx ⟨e, E_le_U S he⟩) := hf ⟨e, E_le_U S he⟩
      have h2 : f e' = φ (pi S.cx ⟨e', E_le_U S he'⟩) := hf ⟨e', E_le_U S he'⟩
      have h3 : f (e * e') = φ (pi S.cx (⟨e, E_le_U S he⟩ * ⟨e', E_le_U S he'⟩)) :=
        hf (⟨e, E_le_U S he⟩ * ⟨e', E_le_U S he'⟩)
      rw [h1, h2, h3, map_mul]
      exact hadd _ (hE e he) _ (hE e' he'))
    (fun z hz => by
      have h1 := hf ⟨z, Z_le_U S hz⟩
      rw [h1, (pi_eq_one_iff S.cx _).2 hz]
      exact hφ1)
    (fun z hz => by
      rcases (mem_Z'_iff S).1 hz with rfl | rfl
      · have h1 := hf 1
        have : ((1 : ↥(UH153 T M V₁ Mc)) : G) = 1 := rfl
        rw [this] at h1
        rw [h1, map_one]
        exact hφ1
      · have h1 := hf ⟨zp S, zp_mem_U S⟩
        rw [h1, ← aa_eq S]
        exact hφa)
  refine ⟨x, hx, fun e he => ?_⟩
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 he
  rw [rhoX_pi_eq S hx hu, hcomm u hu, hf]

end Transv

end S153E56p

end CFSG.Quasithin
