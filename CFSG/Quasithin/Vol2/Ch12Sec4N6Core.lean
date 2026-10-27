module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def BlockQ1246SL27Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
    ¬ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G) →
    ⁅pCoreOf 2 (L ⊔ T), L⁆ = V → pCoreOf 2 L ≠ V →
      ⁅pCoreOf 2 L, pCoreOf 2 (L ⊔ T)⁆ = ⊥

namespace N1246

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem Q_eq_of_comm (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    (hPQ : ⁅pCoreOf 2 L, pCoreOf 2 (L ⊔ T)⁆ = ⊥) :
    pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  obtain ⟨D⟩ := c.nat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [c.card16]; norm_num
  have hcommGr := commV_autOn_eq_top c.f.normalizes c.f.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.f.sq w w.2)
  refine le_antisymm ?_ (sup_le c.V_le_Q c.CTL_le_Q)
  intro q hq
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
    have hkq : (l'⁻¹ * l) * q = q * (l'⁻¹ * l) := by
      have h1 := Subgroup.commutator_mem_commutator hk hq
      rw [hPQ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
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


end Ctx

end N1246

theorem blockQ1246SL27_of_core (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hcore : BlockQ1246SL27Core) : BlockQ1246SL27 := by
  intro G _ _ T L V hcx h3 E hEV hE4 hTE hN hcomm hO2
  obtain ⟨z, v, _, c⟩ := N1246.exists_ctx h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 hcx h3 hEV
    hE4 hTE
  exact c.Q_eq_of_comm hcomm (hcore G T L V hcx h3 E hEV hE4 hTE hN hcomm hO2)

end CFSG.Quasithin.H13
