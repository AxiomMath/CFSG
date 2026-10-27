module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.LieType.Steinberg.Minuscule.Datum

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable (K : Type) [Field K]

@[expose] def StabP0 : Subgroup ↥(EAut0 K) where
  carrier := {g | ∃ c : K, c ≠ 0 ∧ (g : W K ≃ₗ[K] W K) (p0 K) = c • p0 K}
  mul_mem' := by
    rintro g h ⟨c, hc, hg⟩ ⟨d, hd, hh⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    show (g : W K ≃ₗ[K] W K) ((h : W K ≃ₗ[K] W K) (p0 K)) = _
    rw [hh, map_smul, hg, smul_smul]
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    have h1 : (g : W K ≃ₗ[K] W K) ((c⁻¹ • p0 K)) = p0 K := by
      rw [map_smul, hg, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 : ((g⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ((g : W K ≃ₗ[K] W K) (c⁻¹ • p0 K)) =
        c⁻¹ • p0 K := by
      show ((g : W K ≃ₗ[K] W K)⁻¹) ((g : W K ≃ₗ[K] W K) _) = _
      exact LinearEquiv.symm_apply_apply _ _
    rw [h1] at h2
    exact h2

variable [CharP K 2]

abbrev nodeQ2 : Fin (Tag.rank .E7) := ⟨1, by decide⟩

theorem d0Lam_mem (c : Kˣ) :
    (e7Data_valid.hm K nodeQ2 c : (Module.End K (V K))ˣ) ∈ Lam K := by
  have hα : (Pi.single nodeQ2 (1 : ℤ) : Fin (Tag.rank .E7) → ℤ) ∈ Perp := by
    rw [perp_iff]
    refine ⟨IsRoot.basis (τ := .E7) nodeQ2, ?_⟩
    rw [Pi.single_eq_of_ne (show node1 ≠ nodeQ2 by decide)]
  have hle : CFSG.LieType.CurtisTits.rankOne (e7Data_valid.rootGroup K) nodeQ2 ≤
      (Lam K).comap (e7Data_valid.minGroup K).subtype := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hg
      exact xu_mem_Lam hα u
    · intro g hg
      obtain ⟨u, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hg
      exact xu_mem_Lam (neg_mem_Perp hα) u
  exact hle (e7Data_valid.torus_le_rankOne K nodeQ2 (e7Data_valid.hm_mem_torus K nodeQ2 c))

@[expose] def d0Lam : Kˣ →* ↥(Lam K) where
  toFun c := ⟨(e7Data_valid.hm K nodeQ2 c : (Module.End K (V K))ˣ), d0Lam_mem K c⟩
  map_one' := Subtype.ext (by simp [e7Data_valid.hm_one])
  map_mul' c c' := Subtype.ext (by simp [e7Data_valid.hm_mul])

@[expose] def d0Hom : Kˣ →* ↥(EAut0 K) :=
  (((vAut0 K).toMonoidHom.comp (resV0 K)).comp (d0Lam K)).codRestrict (EAut0 K) fun c =>
    ⟨resV0 K (d0Lam K c), mem_LamW_iff.2 ⟨d0Lam K c, rfl⟩, rfl⟩

variable {K}

private theorem hm_apply_single' (i : Fin (Tag.rank .E7)) (c : Kˣ) (a : Fin e7Data.d) :
    (((e7Data_valid.hm K i c : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) :
        Module.End K (V K)) (Finsupp.single a 1) =
      ((c ^ e7Data.wt a i : Kˣ) : K) • Finsupp.single a 1 := by
  change e7Data_valid.endo K (e7Data_valid.hm K i c) (Finsupp.single a 1) = _
  rw [e7Data_valid.endo_hm, e7Data.hDiag_single]

set_option maxRecDepth 20000 in
theorem d0Hom_apply_p0 (c : Kˣ) :
    ((d0Hom K c : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = (c : K) • p0 K := by
  have hwt0 : e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) nodeQ2 = 1 := by decide +kernel
  have hwt : e7Data.wt (a0 : Fin e7Data.d) nodeQ2 = 1 := hwt0
  have h := hm_apply_single' (K := K) nodeQ2 c (a0 : Fin e7Data.d)
  rw [hwt, zpow_one] at h
  apply emb_injective
  have hind := resV0_induces (K := K) (d0Lam K c) (p0 K)
  change emb K ((resV0 K (d0Lam K c) : Module.End K (W K)) (p0 K)) =
    (((d0Lam K c : ↥(Lam K)) : (Module.End K (V K))ˣ) : Module.End K (V K)) (emb K (p0 K)) at hind
  change emb K ((resV0 K (d0Lam K c) : Module.End K (W K)) (p0 K)) = emb K ((c : K) • p0 K)
  rw [hind, map_smul, p0, emb_single]
  exact h

variable (K)

theorem d0Hom_mem (c : Kˣ) : d0Hom K c ∈ StabP0 K :=
  ⟨(c : K), c.ne_zero, d0Hom_apply_p0 c⟩

@[expose] def d0 : Kˣ →* ↥(StabP0 K) := (d0Hom K).codRestrict (StabP0 K) (d0Hom_mem K)

variable {K}

theorem d0_apply_p0 (c : Kˣ) :
    (((d0 K c : ↥(StabP0 K)) : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = (c : K) • p0 K :=
  d0Hom_apply_p0 c

variable (K)

@[expose] def E4StabChar : Prop :=
  ∀ χ : ↥(StabP0 K) →* Kˣ, (∀ c : Kˣ, χ (d0 K c) = c) →
    ∀ g : ↥(StabP0 K), (((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K)) (p0 K) = ((χ g : Kˣ) : K) • p0 K

end CFSG.RankThree.GF2n.Smith81.D6Spin
