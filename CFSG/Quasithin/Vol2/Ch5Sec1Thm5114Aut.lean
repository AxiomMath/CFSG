module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G]

theorem centralizer_subgroupOf_eq_pCore {K W : Subgroup G} (hs : IsSimpleGroup (O2Q K))
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    (Subgroup.centralizer (W : Set G)).subgroupOf K = CFSG.pCore 2 ↥K := by
  set N := (Subgroup.centralizer (W : Set G)).subgroupOf K with hN
  have hPN : CFSG.pCore 2 ↥K ≤ N := by
    intro x hx
    rw [hN, Subgroup.mem_subgroupOf]
    exact hO ⟨x, by exact hx, rfl⟩
  have hNn : N.Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    have hw' : (k : G)⁻¹ * w * k ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKW k.2)) w).mp hw
      simpa using this
    have h1 := hx _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * ((k : G) * x * (k : G)⁻¹) = k * (((k : G)⁻¹ * w * k) * x) * (k : G)⁻¹ := by group
      _ = k * (x * ((k : G)⁻¹ * w * k)) * (k : G)⁻¹ := by rw [h1]
      _ = (k : G) * x * (k : G)⁻¹ * w := by group
  have hNbar : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
  · refine le_antisymm ?_ hPN
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    exact hb
  · exfalso
    apply hne
    intro x hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩ ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hmem
    have h1 : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K), MonoidHom.mem_ker, map_mul, map_inv, hcx,
        inv_mul_cancel]
    have h2 : (⟨x, hx⟩ : ↥K) = c * (c⁻¹ * ⟨x, hx⟩) := by group
    have h3 : (⟨x, hx⟩ : ↥K) ∈ N := by
      rw [h2]
      exact N.mul_mem hc (hPN h1)
    rw [hN, Subgroup.mem_subgroupOf] at h3
    exact h3

theorem nonempty_autOn_equiv_O2Q {K W : Subgroup G} (hs : IsSimpleGroup (O2Q K))
    (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    Nonempty (↥(autOn K W) ≃* O2Q K) := by
  have hker : (InternalSec.autOnHom hKW).ker = CFSG.pCore 2 ↥K := by
    rw [← centralizer_subgroupOf_eq_pCore hs hKW hO hne]
    ext k
    rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _
    (InternalSec.autOnHom_surjective hKW)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem card_autOn_of_lieModel {K W : Subgroup G} (hK : LieModel (O2Q K) .PSL 3 2 2)
    (hs : IsSimpleGroup (O2Q K)) (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn K W) = 20160 := by
  obtain ⟨e⟩ := nonempty_autOn_equiv_O2Q hs hKW hO hne
  rw [Nat.card_congr e.toEquiv, CFSG.GH74.card_of_lieModel_PSL (by norm_num) hK]
  decide

theorem not_equiv_SL4_of_lieModel (hL34 : Vol2.Ch11.SecA.FactL34) {X : Type} [Group X]
    (hX : LieModel X .PSL 3 2 2) : ¬ Nonempty (X ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rintro ⟨e⟩
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hX
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  let f : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (e.toMonoidHom.comp e'.symm.toMonoidHom).comp
      ((QuotientGroup.mk' _).comp (specialLinearGroupEquivStatedSL 3 F).toMonoidHom)
  exact hL34 F hF4 f ((e.surjective.comp e'.symm.surjective).comp
    ((QuotientGroup.mk'_surjective _).comp (specialLinearGroupEquivStatedSL 3 F).surjective))

end CFSG.Quasithin.H13
