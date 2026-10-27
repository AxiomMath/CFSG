module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen


abbrev G7 (K : Type) [Field K] : Type := ↥(e7Data_valid.minGroup K)

variable {K : Type} [Field K]

@[expose] noncomputable def act7 (g : G7 K) : V K ≃ₗ[K] V K := vAut K (g : (Module.End K (V K))ˣ)

@[expose] def IsRt5 (r : V K ≃ₗ[K] V K) : Prop := IsRootElt ((vAut K).symm r)

theorem act7_mul (g h : G7 K) : act7 (g * h) = act7 g * act7 h := by
  simp only [act7, Subgroup.coe_mul, map_mul]

theorem act7_one : act7 (1 : G7 K) = 1 := by
  simp only [act7, Subgroup.coe_one, map_one]

theorem act7_inv (g : G7 K) : act7 g⁻¹ = (act7 g)⁻¹ := by
  simp only [act7, Subgroup.coe_inv, map_inv]

theorem act7_injective : Function.Injective (act7 : G7 K → V K ≃ₗ[K] V K) := by
  intro g h e
  exact Subtype.ext ((vAut K).injective e)

theorem act7_apply (g : G7 K) (v : V K) : act7 g v = (e7Data_valid.endo K g) v := by
  rfl

theorem mem_EAut_iff_act7 {r : V K ≃ₗ[K] V K} : r ∈ EAut K ↔ ∃ g : G7 K, act7 g = r := by
  unfold EAut
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(g : (Module.End K (V K))ˣ), g.2, rfl⟩

theorem act7_xm (γ : Fin (Tag.rank .E7) → ℤ) (c : K) (v : V K) :
    act7 (e7Data_valid.xm K γ c) v = v + c • e7Data.rootOp K γ v := by
  rw [act7_apply, e7Data_valid.endo_xm, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply]

theorem isRt5_iff {r : V K ≃ₗ[K] V K} : IsRt5 r ↔ ∃ g : G7 K, IsRootEltG g ∧ act7 g = r := by
  constructor
  · intro hr
    obtain ⟨h, hh, γ, c, hγ, hc, hg⟩ := hr
    have hmem : (vAut K).symm r ∈ e7Data_valid.minGroup K := by
      rw [hg]
      exact mul_mem (mul_mem hh (e7Data_valid.xu_mem K γ c)) (inv_mem hh)
    have hrel : IsRootEltG (⟨(vAut K).symm r, hmem⟩ : G7 K) := by
      unfold IsRootEltG
      exact ⟨⟨h, hh⟩, γ, c, hγ, hc, Subtype.ext hg⟩
    exact ⟨⟨(vAut K).symm r, hmem⟩, hrel, (vAut K).apply_symm_apply r⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h, γ, c, hγ, hc, hgeq⟩ := hg
    have e : (vAut K).symm (act7 g) = (g : (Module.End K (V K))ˣ) :=
      (vAut K).symm_apply_apply _
    unfold IsRt5
    rw [e]
    unfold IsRootElt
    refine ⟨(h : (Module.End K (V K))ˣ), h.2, γ, c, hγ, hc, ?_⟩
    subst hgeq
    rfl

theorem isRt5_mul_self [CharP K 2] {r : V K ≃ₗ[K] V K} (hr : IsRt5 r) : r * r = 1 := by
  obtain ⟨g, hg, rfl⟩ := (isRt5_iff).1 hr
  obtain ⟨h, γ, c, -, -, hgeq⟩ := hg
  have key : e7Data_valid.xm K γ c * e7Data_valid.xm K γ c = 1 := fe3_xm_mul_self_eq_one γ c
  have hgg : g * g = 1 := by
    rw [hgeq]
    calc h * e7Data_valid.xm K γ c * h⁻¹ * (h * e7Data_valid.xm K γ c * h⁻¹)
        = h * (e7Data_valid.xm K γ c * e7Data_valid.xm K γ c) * h⁻¹ := by group
      _ = 1 := by simp [key]
  rw [← act7_mul, hgg, act7_one]

end CFSG.RankThree.GF2n.Smith81.RootGenE5
