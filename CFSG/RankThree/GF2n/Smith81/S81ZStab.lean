module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model


variable (K : Type) [Field K]

@[expose] def StabW0 : Subgroup ↥(EAut K) where
  carrier := {g | ∃ c : K, c ≠ 0 ∧ (g : V K ≃ₗ[K] V K) (w0 : V K) = c • (w0 : V K)}
  mul_mem' := by
    rintro g h ⟨c, hc, hg⟩ ⟨d, hd, hh⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    show (g : V K ≃ₗ[K] V K) ((h : V K ≃ₗ[K] V K) (w0 : V K)) = _
    rw [hh, map_smul, hg, smul_smul]
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    have h1 : (g : V K ≃ₗ[K] V K) ((c⁻¹ • (w0 : V K))) = (w0 : V K) := by
      rw [map_smul, hg, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 : ((g⁻¹ : ↥(EAut K)) : V K ≃ₗ[K] V K) ((g : V K ≃ₗ[K] V K) (c⁻¹ • (w0 : V K))) =
        c⁻¹ • (w0 : V K) := by
      show ((g : V K ≃ₗ[K] V K)⁻¹) ((g : V K ≃ₗ[K] V K) _) = _
      exact LinearEquiv.symm_apply_apply _ _
    rw [h1] at h2
    exact h2

abbrev node7' : Fin (Tag.rank .E7) := ⟨6, by decide⟩

@[expose] def d7Hom : Kˣ →* ↥(EAut K) where
  toFun c := ⟨vAut K ((e7Data_valid.hm K node7' c : ↥(EGrp K)) : (Module.End K (V K))ˣ),
    Subgroup.mem_map_of_mem (vAut K).toMonoidHom (e7Data_valid.hm K node7' c).2⟩
  map_one' := Subtype.ext (by simp [e7Data_valid.hm_one])
  map_mul' c c' := Subtype.ext (by simp [e7Data_valid.hm_mul])

variable {K}

abbrev a0 : Fin e7Data.d := ⟨0, by decide⟩

theorem hm_apply_single (i : Fin (Tag.rank .E7)) (c : Kˣ) (a : Fin e7Data.d) :
    (((e7Data_valid.hm K i c : ↥(EGrp K)) : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single a 1) = ((c ^ e7Data.wt a i : Kˣ) : K) • Finsupp.single a 1 := by
  change e7Data_valid.endo K (e7Data_valid.hm K i c) (Finsupp.single a 1) = _
  rw [e7Data_valid.endo_hm, e7Data.hDiag_single]

set_option maxRecDepth 20000 in
theorem d7Hom_apply_w0 (c : Kˣ) :
    ((d7Hom K c : ↥(EAut K)) : V K ≃ₗ[K] V K) (w0 : V K) = (c : K) • (w0 : V K) := by
  have hwt : e7Data.wt (a0 : ℕ) node7' = 1 := by decide +kernel
  have h := hm_apply_single (K := K) node7' c a0
  rw [hwt, zpow_one] at h
  have h2 : (vAut K ((e7Data_valid.hm K node7' c : ↥(EGrp K)) : (Module.End K (V K))ˣ))
      (Finsupp.single a0 1) = (c : K) • Finsupp.single a0 1 := h
  exact h2

variable (K)

theorem d7Hom_mem (c : Kˣ) : d7Hom K c ∈ StabW0 K :=
  ⟨(c : K), c.ne_zero, d7Hom_apply_w0 c⟩

@[expose] def d7 : Kˣ →* ↥(StabW0 K) := (d7Hom K).codRestrict (StabW0 K) (d7Hom_mem K)

variable {K}

theorem d7_apply_w0 (c : Kˣ) :
    (((d7 K c : ↥(StabW0 K)) : ↥(EAut K)) : V K ≃ₗ[K] V K) (w0 : V K) = (c : K) • (w0 : V K) :=
  d7Hom_apply_w0 c

variable (K)

@[expose] def E5StabChar : Prop :=
  ∀ χ : ↥(StabW0 K) →* Kˣ, (∀ c : Kˣ, χ (d7 K c) = c) →
    ∀ g : ↥(StabW0 K), (((g : ↥(EAut K)) : V K ≃ₗ[K] V K)) (w0 : V K) = ((χ g : Kˣ) : K) • (w0 : V K)

end CFSG.RankThree.GF2n.Smith81.S81Z
