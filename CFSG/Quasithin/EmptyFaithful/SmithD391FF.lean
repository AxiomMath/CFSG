module

public import CFSG.Quasithin.EmptyFaithful.S153MAR
public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.F918N5
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.SmithD391Mult

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

theorem exists_pow_mem_of_le_normalizer {G : Type*} [Group G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T) :
    ∀ x ∈ L ⊔ T, ∃ e : ℕ, x ^ 2 ^ e ∈ L := by
  intro x hx
  set H := L ⊔ T with hH
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hKn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHN
  set φ := QuotientGroup.mk' (L.subgroupOf H) with hφ
  have hT' : IsPGroup 2 ↥(T.subgroupOf H) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have htop : (T.subgroupOf H).map φ = ⊤ := by
    have h1 : L.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have h2 := congrArg (Subgroup.map φ) h1
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _)] at h2
    exact h2
  have hp : IsPGroup 2 ↥((T.subgroupOf H).map φ) := hT'.map φ
  rw [htop] at hp
  obtain ⟨e, he⟩ := hp ⟨φ ⟨x, hx⟩, trivial⟩
  refine ⟨e, ?_⟩
  have h3 : φ (⟨x, hx⟩ ^ 2 ^ e) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val he
  have h4 : (⟨x, hx⟩ : ↥H) ^ 2 ^ e ∈ L.subgroupOf H := (QuotientGroup.eq_one_iff _).1 h3
  exact h4

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

omit [Finite X] in
theorem commSub_eq_of_isIrr {K : Subgroup (MulAut X)} {S : Subgroup X} (hS : XMod.IsIrr ↥K S)
    (hfix : fixV K = ⊥) : commSub S K = S := by
  rw [← commOf_eq_commSub]
  rcases hS.2.2 (XMod.commOf ↥K S) (XMod.isInv_commOf S) bot_le (XMod.commOf_le_of_isInv hS.1)
    with h | h
  · exfalso
    have h1 : S ≤ XMod.fixed ↥K ⊤ := XMod.commOf_eq_bot_iff.1 h
    rw [fixed_top_eq_fixV, hfix] at h1
    exact hS.2.1.ne' (le_bot_iff.1 h1)
  · exact h

theorem sumNatDual_of_isFFModule (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {t : MulAut X} (htT : t ∈ Tb)
    (hsum : Vb ⊔ Vb.map t.toMonoidHom = ⊤)
    (hnot : ¬ XMod.Iso ↥Lb (Vb.map t.toMonoidHom) Vb) (hFF : IsFFModule (Mb ⊔ Tb)) :
    ∃ n, SumNatDual Lb ⊤ n := by
  subst hML
  have hV : ∀ x : X, x ^ 2 = 1 := h.exp
  have hLX : Mb ≤ Mb ⊔ Tb := le_sup_left
  have hTn : Tb ≤ Subgroup.normalizer (Mb : Set (MulAut X)) := fun t ht => n6_Tb_le_normalizer h ht
  have hn : ∀ x ∈ Mb ⊔ Tb, ∀ l ∈ Mb, x * l * x⁻¹ ∈ Mb := fun x hx l hl =>
    (Subgroup.mem_normalizer_iff.1 ((sup_le Subgroup.le_normalizer hTn) hx) l).1 hl
  have h2 := exists_pow_mem_of_le_normalizer hTn h.sylow.2.1
  have hS : SQTKGroup ↥Mb := by
    obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := h.qsqtk
    have hS' : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
    exact B69.sqtk_subgroup hA21 hS' φ hφ hLX h.quasi
  obtain ⟨-, hB⟩ := S153M.le_ffJ_of_ffModule hV hLX hn h2 h.quasi hS h.o2 hFF
  have h3 := (hB51 X hV _ _ hB).2.2.1
  unfold B51Part3 at h3
  have hirr' : XMod.IsIrr ↥Mb (Vb.map t.toMonoidHom) := z35_conj_irr h htT
  have hcomm : commV Mb = ⊤ := by
    rw [eq_top_iff, ← hsum]
    refine sup_le ?_ ?_
    · rw [← commSub_eq_of_isIrr h.irr h.fix, commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    · rw [← commSub_eq_of_isIrr hirr' h.fix, commV_eq_commSub]
      exact commSub_mono le_top le_rfl
  rw [hcomm, h.fix, bot_inf_eq] at h3
  rcases h3 with hhom | ⟨n, hn⟩
  · exfalso
    have hsec : ∀ S : Subgroup X, XMod.IsIrr ↥Mb S →
        ⊥ ≤ S ∧ S ≤ ⊤ ∧ XMod.IsInv ↥Mb S ∧ XMod.IsIrrSec ↥Mb ⊥ S :=
      fun S hS => ⟨bot_le, le_top, hS.1, hS.2⟩
    have hiso := hhom.2 Vb (Vb.map t.toMonoidHom) (hsec Vb h.irr) (hsec _ hirr')
    obtain ⟨e, he⟩ := InternalSec.equiv_of_secIsoL hiso
    have hiso' : XMod.Iso ↥Mb Vb (Vb.map t.toMonoidHom) := by
      refine ⟨e, fun k l l' hl => ?_⟩
      have hkl : (k : MulAut X) (l : X) ∈ Vb := by
        rw [show (k : MulAut X) (l : X) = (l' : X) from hl]
        exact l'.2
      have hke : (k : MulAut X) ((e l : ↥(Vb.map t.toMonoidHom)) : X) ∈ Vb.map t.toMonoidHom :=
        hirr'.1 k _ (e l).2
      have h1 := he k l hkl hke
      have h2 : (⟨(k : MulAut X) (l : X), hkl⟩ : ↥Vb) = l' := Subtype.ext hl
      rw [h2] at h1
      rw [h1]
      rfl
    exact hnot (XMod.Iso.symm h.irr.1 hiso')
  · exact ⟨n, hn⟩

end CFSG.Quasithin.SmithD391
