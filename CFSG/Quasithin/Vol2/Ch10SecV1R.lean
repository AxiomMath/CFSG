module

public import CFSG.Quasithin.Vol2.Ch10SecV1N
public import CFSG.Quasithin.Vol2.Ch10SecV1P
public import CFSG.Quasithin.Vol2.Ch10SecV1Q
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420B56Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple

namespace V1C

theorem center_eq_bot_of_simple {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X)
    (hs : IsSimpleGroup X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x

end V1C

open V1C

theorem c27NoL2pJ1_of_b56 (h56 : AsB56) : C27NoL2pJ1 := by
  intro G _ _ H R M K hC23 hKc hq hch hKM hRK Q _ ⟨e⟩ htype
  obtain ⟨hsQ, hord, h6Q⟩ := q_facts htype
  have : IsSimpleGroup (ModO2 K) := e.isSimpleGroup
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_eq_bot_of_simple hq this
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hR2 : IsPGroup 2 R := hC23.radical.isPGroup
  have hKRK : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hKRV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := C27.sup_le_normalizer K R
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hKRV
  have hV : IsElemAbelian 2 V := B2F.isElemAbelian_omegaOneCenterOf _
  have hCK := C27.inf_centralizer_le hC23 hKc hq hZ hch hKM hRK
  have hQV : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G) :=
    L15420.le_centralizer_omegaOneCenterOf _
  have hOK : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (C27.pCoreOf_le_pCoreOf_sup hRK).trans hQV
  obtain ⟨e'⟩ := L15420.nonempty_mulEquiv_autOn hKV hCK hOK
  have hq' : CFSG.IsQuasisimple ↥(autI hV K) := FFL.isQuasisimple_of_mulEquiv e' hq
  have hcard : Nat.card ↥(autI hV K) = Nat.card Q :=
    (Nat.card_congr e'.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hΓ : autI hV (K ⊔ R) ⊓ Subgroup.centralizer (autI hV K : Set (MulAut (IntMod V hV))) =
      ⊥ :=
    L15420.autOn_inf_centralizer_eq_bot hZ hR2 hRK hKRV hCK hQV
  have hQ : G64.IsQuotientOfSQTKCat ↥(autI hV (K ⊔ R)) :=
    L15420.isQuotientOfSQTKCat_autOn hC23.sqtk (sup_le (le_of_mem_cComp hKc) hC23.radical.1)
      hKRV
  have hLΓ : autI hV K ≤ autI hV (K ⊔ R) := autI_mono hV le_sup_left
  have hnormal : ((autI hV K).subgroupOf (autI hV (K ⊔ R))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLΓ]
    rintro _ _ ⟨k, hk, rfl⟩ ⟨x, hx, rfl⟩
    refine ⟨x * k * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKRK hx) k).mp hk
  have hoff := C27.exists_ffStarOffender hC23 hKc hq hZ hch hKM hRK hV
  have hV2 : ∀ v : IntMod V hV, v * v = 1 := fun v => by
    rw [← sq]
    exact IntMod.sq_eq_one v
  have h6 : 6 < Nat.card ↥(autI hV K) := hcard ▸ h6Q
  have hB := FFL.b51Part1_of_b56 h56 hV2 hQ hLΓ hnormal hΓ hq' h6 hoff
  exact hord (hcard ▸ ffOrd_of_b51 (FFL.center_eq_bot hLΓ hΓ) h6 hB)

end CFSG.Quasithin.Vol2.Ch10
