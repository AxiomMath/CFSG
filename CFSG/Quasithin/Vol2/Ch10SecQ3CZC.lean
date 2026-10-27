module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZB
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

theorem normalizer_le_fsuM (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {R : Subgroup G}
    (hRp : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≠ ⊥ := fun h => hR1 (le_bot_iff.mp
    (h ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hRp))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have h := (isUniqueM_L0T h331 hyp).2 M' ⟨hM'.1, hRN.trans hM'.2⟩
  rw [← h]
  exact hM'.2

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers {z : G} :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hx

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem eq_one_of_mem_centralizer {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hzL : z ∈ Subgroup.centralizer (fsuL0 T L : Set G))
    (hzH : z ∈ Subgroup.centralizer (H : Set G)) : z = 1 := by
  by_contra hz1
  have hzT := quasithinOmegaOneCenter_le_center T hz
  have hC : ∀ {X : Subgroup G}, z ∈ Subgroup.centralizer (X : Set G) →
      X ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun {X} hX x hx =>
    centralizer_le_normalizer_zpowers (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hX x hx))
  have hRp : IsPGroup 2 (Subgroup.zpowers z) :=
    c.hyp.fsu.sylow.1.to_le (Subgroup.zpowers_le.mpr hzT.1)
  have hR1 : Subgroup.zpowers z ≠ ⊥ := fun h =>
    hz1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers z))
  have hle := normalizer_le_fsuM c.h331 c.hyp hRp hR1 (sup_le (hC hzL) (hC hzT.2))
  exact c.hH.2.1 ((hC hzH).trans hle)

theorem eq_one_of_mem_centralizer_L0 {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hzL : z ∈ Subgroup.centralizer (fsuL0 T L : Set G)) : z = 1 := by
  have hbL : b ∈ fsuL0 T L := (oTwoUpper_le _ c.hbB0).1
  have hbz : b * z * b⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzL b hbL, mul_inv_cancel_right]
  exact c.eq_one_of_mem_centralizer hz hzL (c.mem_centralizer_of_fix hz hbz)

theorem fsuCVM_eq_bot : fsuCVM T L I = ⊥ := by
  by_contra hne
  have hCT : fsuCVM T L I ≤ T := inf_le_left.trans (SecA.fsuVM_le_T c.hyp)
  have hTN : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) :=
    fun _ hx => SecA.le_normalizer_fsuCVM T L I (SecA.le_fsuM T L hx)
  obtain ⟨v, hv, hv1, hvT⟩ :=
    SecA.exists_ne_one_mem_centralizer c.hyp.fsu.sylow.1 hCT hTN hne
  have hv2 : v ^ 2 = 1 := by
    have := (SecA.isElemAbelian_fsuVM c.hyp).2 v hv.1
    simpa using this
  have hvZ : v ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hCT hv, hvT⟩, hv2⟩
  exact hv1 (c.eq_one_of_mem_centralizer_L0 hvZ hv.2)

theorem not_thompsonJ_le :
    ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  intro hJ
  have hN : fsuL0 T L ≤ Subgroup.normalizer
      (Subgroup.centralizer (fsuVM T L I : Set G) : Set G) := fun x hx =>
    SecA.le_normalizer_centralizer le_rfl (SecA.fsuL0_le_normalizer_fsuVM T L I hx)
  have hL0 : fsuL0 T L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [c.hL0J, Subgroup.commutator_le]
    intro x hx j hj
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hN hx) j).mp (hJ hj))
      (Subgroup.inv_mem _ (hJ hj))
  apply SecA.commutator_fsuVM_ne_bot c.hyp.fsu
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  exact (SecA.le_fsuL0 T L).trans hL0

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
