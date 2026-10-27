module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6L1

public section

namespace CFSG.Quasithin.H13
namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem mem_sup_of_commute_pCore (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hqP : ∀ k ∈ pCoreOf 2 L, k * q = q * k) :
    q ∈ V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  obtain ⟨D⟩ := c.nat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [c.card16]; norm_num
  have hcommGr := commV_autOn_eq_top c.f.normalizes c.f.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.f.sq w w.2)
  have hqT : q ∈ T := (c.Q ▸ hq : q ∈ T ⊓ Subgroup.centralizer (V : Set G)).1
  have hqV : q ∈ Subgroup.centralizer (V : Set G) :=
    (c.Q ▸ hq : q ∈ T ⊓ Subgroup.centralizer (V : Set G)).2
  have hconj : ∀ (l : G) (hl : l ∈ Subgroup.normalizer (V : Set G)) (u : ↥V),
      ((conjAct V ⟨l, hl⟩ u : ↥V) : G) = l * u * l⁻¹ := fun l hl u => conjAct_coe V ⟨l, hl⟩ u
  have hwd : ∀ l ∈ L, ∀ l' ∈ L, ∀ (hl : l ∈ Subgroup.normalizer (V : Set G))
      (hl' : l' ∈ Subgroup.normalizer (V : Set G)), conjAct V ⟨l, hl⟩ = conjAct V ⟨l', hl'⟩ →
      l * q * l⁻¹ * q⁻¹ = l' * q * l'⁻¹ * q⁻¹ := by
    intro l hlL l' hl'L hl hl' heq
    have hk : l'⁻¹ * l ∈ pCoreOf 2 L := by
      refine c.inf_centralizer_le_pCore ⟨L.mul_mem (L.inv_mem hl'L) hlL, ?_⟩
      have hN : l'⁻¹ * l ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hl') hl
      have h1 : conjAct V ⟨l'⁻¹ * l, hN⟩ = 1 := by
        have : (⟨l'⁻¹ * l, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            (⟨l', hl'⟩)⁻¹ * ⟨l, hl⟩ := rfl
        rw [this, map_mul, map_inv, heq, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.1 h1
    have hkq : (l'⁻¹ * l) * q = q * (l'⁻¹ * l) := hqP _ hk
    calc l * q * l⁻¹ * q⁻¹ = l' * ((l'⁻¹ * l) * q) * l⁻¹ * q⁻¹ := by group
      _ = l' * (q * (l'⁻¹ * l)) * l⁻¹ * q⁻¹ := by rw [hkq]
      _ = l' * q * l'⁻¹ * q⁻¹ := by group
  have hlift : ∀ γ : L3.Γ, ∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨l, hl⟩ = D.rho γ := fun γ => Ctx.exists_of_mem_autOn (D.rho_mem γ)
  choose lf hlfL hlfN hlf using hlift
  let f : L3.Γ → ↥V := fun γ => ⟨lf γ * q * (lf γ)⁻¹ * q⁻¹, comm_mem hcomm hq (hlfL γ)⟩
  have hf : ∀ γ η, f (γ * η) = f γ * D.rho γ (f η) := by
    intro γ η
    have hN : lf γ * lf η ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (hlfN γ) (hlfN η)
    have h1 : conjAct V ⟨lf γ * lf η, hN⟩ = conjAct V ⟨lf (γ * η), hlfN (γ * η)⟩ := by
      have : (⟨lf γ * lf η, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨lf γ, hlfN γ⟩ * ⟨lf η, hlfN η⟩ := rfl
      rw [this, map_mul, hlf, hlf, hlf, map_mul]
    have h2 := hwd _ (L.mul_mem (hlfL γ) (hlfL η)) _ (hlfL (γ * η)) hN (hlfN (γ * η)) h1
    rw [mul_comm (f γ)]
    apply Subtype.ext
    simp only [f, Subgroup.coe_mul]
    rw [← hlf γ, hconj]
    simp only
    rw [← h2]
    group
  obtain ⟨w, hw⟩ := cocycle_cob hW h16 c.nat hind D f hf
  have hlw : ∀ l ∈ L, l * q * l⁻¹ * q⁻¹ = l * (w : G) * l⁻¹ * (w : G)⁻¹ := by
    intro l hl
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := c.f.normalizes hl
    obtain ⟨γ, hγ⟩ := D.exists_rho (Subgroup.mem_map_of_mem (conjAct V)
      (Subgroup.mem_subgroupOf.2 hl : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈
        L.subgroupOf (Subgroup.normalizer (V : Set G))))
    have h1 := hwd l hl (lf γ) (hlfL γ) hlN (hlfN γ) (hγ.symm.trans (hlf γ).symm)
    have h2 := congrArg Subtype.val (hw γ)
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h1, h2, hγ, hconj]
  have hwT : (w : G) ∈ T := c.f.le_T w.2
  have hqw : q = (w : G) * ((w : G)⁻¹ * q) := by group
  rw [hqw]
  refine Subgroup.mul_mem_sup w.2 ⟨T.mul_mem (T.inv_mem hwT) hqT, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
  have h1 := hlw l hl
  have h2 : l * q * l⁻¹ = l * (w : G) * l⁻¹ * (w : G)⁻¹ * q := by
    calc l * q * l⁻¹ = (l * q * l⁻¹ * q⁻¹) * q := by group
      _ = _ := by rw [h1]
  calc l * ((w : G)⁻¹ * q) = (l * (w : G)⁻¹ * l⁻¹) * (l * q * l⁻¹) * l := by group
    _ = (l * (w : G)⁻¹ * l⁻¹) * (l * (w : G) * l⁻¹ * (w : G)⁻¹ * q) * l := by rw [h2]
    _ = (w : G)⁻¹ * q * l := by group

theorem inf_centralizer_L1_le_Q {x : G}
    (hx : x ∈ c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G)) : x ∈ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  have haCLE := c.L1_le haL1
  obtain ⟨γa, hγa, hγac, -⟩ := c.image_CLE D haCLE
  have hγa3 : γa * γa * γa = 1 := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγa, ← map_mul, ← map_mul, map_one]
    exact A4.conjAct_eq_one_iff.2 (by
      show a * a * a ∈ Subgroup.centralizer (V : Set G)
      rw [ha3]; exact Subgroup.one_mem _)
  have hγa1 : γa ≠ 1 := fun h => haV (A4.conjAct_eq_one_iff.1 (by rw [← hγa, h, map_one]))
  obtain ⟨γ, hγAS, hγx⟩ := c.mem_AS_of_R1 D hx.1
  have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.1 hx.2 a haL1
  have hcomm : γ * γa = γa * γ := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγx, hγa, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxa.symm
  have hγ1 := as_three_cent _ (c.cv_ne D) γa hγac hγa3 hγa1 γ hγAS hcomm
  have hxV : x ∈ Subgroup.centralizer (V : Set G) :=
    A4.conjAct_eq_one_iff.1 (by rw [← hγx, hγ1, map_one])
  have hxQ : x ∈ pCoreOf 2 (L ⊔ T) := by rw [c.Q]; exact ⟨hx.1.1, hxV⟩
  exact hxQ

end Ctx

end N1246

end CFSG.Quasithin.H13
