module

public import CFSG.Quasithin.Recognition.WBN.U4
public import CFSG.Quasithin.Recognition.WBN.IndexTwo
import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieYam
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.WBN

open CFSG.Quasithin.H13.F431.Un.OL CFSG.LocalAnalysis CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.QuasithinUnique CFSG.Open

private theorem map_fa_eq_self {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {B : Subgroup (Xg h)} (hB : FStab h B) (φ : K ≃+* K) :
    B.map (fa h φ).toMonoidHom = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB φ y).2 hy
  · intro hx
    refine ⟨fa h φ⁻¹ x, (hB φ⁻¹ x).2 hx, ?_⟩
    have h1 : fa h φ * fa h φ⁻¹ = 1 := by rw [fa_mul, mul_inv_cancel, fa_one]
    simpa using congrArg (fun e : MulAut (Xg h) => e x) h1

private theorem mem_Pt_of_map_cj_eq {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    [CharP K 2] (s : Xg h) (hmap : (Pt h).map (cj h s).toMonoidHom = Ln h) :
    s ∈ Pt h := by
  haveI : Finite (Xg h) := finite_gramSU_miyamotoJ4 h
  let Q : Subgroup (Xg h) := (Psy h).map (MulAut.conj s⁻¹).toMonoidHom
  have hQle : Q ≤ Pt h := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyLn : y ∈ Ln h := Psy_le_Ln h hy
    rw [← hmap] at hyLn
    obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hyLn
    have hconj : (MulEquiv.toMonoidHom (MulAut.conj s⁻¹))
        ((MulEquiv.toMonoidHom (MulAut.conj s)) p) = p := by
      rw [show (MulEquiv.toMonoidHom (MulAut.conj s)) p = MulAut.conj s p from rfl,
        show (MulEquiv.toMonoidHom (MulAut.conj s⁻¹)) (MulAut.conj s p) =
          MulAut.conj s⁻¹ (MulAut.conj s p) from rfl,
        MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [← hpy, hconj]
    exact hp
  have hQisP : IsPGroup 2 Q :=
    (isSylowTwoOf_Psy h).isPGroup.map (MulAut.conj s⁻¹).toMonoidHom
  have hcardPsy : Nat.card (Psy h) = twoPart (Pt h) := by
    have htop : Nat.card (Psy h) = twoPart (⊤ : Subgroup (Xg h)) :=
      (isSylowTwoOf_Psy h).card_eq
    have hle : twoPart (Pt h) ≤ twoPart (⊤ : Subgroup (Xg h)) := twoPart_mono le_top
    have hdvd : Nat.card (Psy h) ∣ twoPart (Pt h) :=
      card_dvd_twoPart (Psy_le_Pt h) (isSylowTwoOf_Psy h).isPGroup
    exact le_antisymm (Nat.le_of_dvd (twoPart_pos (Pt h)) hdvd) (htop ▸ hle)
  have hQcard : Nat.card Q = twoPart (Pt h) := by
    rw [show Nat.card Q = Nat.card (Psy h) from
      Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective, hcardPsy]
  have hQsyl : IsSylowTwoOf Q (Pt h) := isSylowTwoOf_of_card_eq hQle hQisP hQcard
  have hPsyl : IsSylowTwoOf (Psy h) (Pt h) :=
    isSylowTwoOf_of_card_eq (Psy_le_Pt h) (isSylowTwoOf_Psy h).isPGroup hcardPsy
  obtain ⟨t, htPt, ht⟩ := hQsyl.exists_conj hPsyl
  have hmemN : t * s⁻¹ ∈ Subgroup.normalizer (Psy h : Set (Xg h)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : MulAut.conj (t * s⁻¹) = MulAut.conj t * MulAut.conj s⁻¹ :=
      map_mul MulAut.conj t s⁻¹
    rw [hcomp]
    change (Psy h).map ((MulAut.conj t).toMonoidHom.comp
      (MulAut.conj s⁻¹).toMonoidHom) = Psy h
    rw [← Subgroup.map_map]
    exact ht.symm
  have hnPt : t * s⁻¹ ∈ Pt h := normalizer_Psy_le_Pt h hmemN
  have hsinv : s⁻¹ ∈ Pt h := by
    have := (Pt h).mul_mem ((Pt h).inv_mem htPt) hnPt
    simpa [mul_assoc] using this
  have hsPt : s ∈ Pt h := by
    have := (Pt h).inv_mem hsinv
    rwa [inv_inv] at this
  exact hsPt

theorem map_Pt_ne_Ln {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]
    [IsSimpleGroup (Xg h)] (φ : Xg h ≃* Xg h) :
    (Pt h).map φ.toMonoidHom ≠ Ln h := by
  intro hEq
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h φ
  have hmapPt : (Pt h).map (fa h (miyamotoFieldFactor h φ)).toMonoidHom = Pt h :=
    map_fa_eq_self h (fStab_Pt h) _
  have hcomp : (cj h s).toMonoidHom.comp (fa h (miyamotoFieldFactor h φ)).toMonoidHom =
      (cj h s * fa h (miyamotoFieldFactor h φ)).toMonoidHom := by
    ext x
    rfl
  have hmap : (Pt h).map (cj h s).toMonoidHom = Ln h := by
    calc (Pt h).map (cj h s).toMonoidHom
        = ((Pt h).map (fa h (miyamotoFieldFactor h φ)).toMonoidHom).map
            (cj h s).toMonoidHom := by rw [hmapPt]
      _ = (Pt h).map ((cj h s).toMonoidHom.comp
            (fa h (miyamotoFieldFactor h φ)).toMonoidHom) := Subgroup.map_map _ _ _
      _ = (Pt h).map (cj h s * fa h (miyamotoFieldFactor h φ)).toMonoidHom := by rw [hcomp]
      _ = Ln h := by rw [← hs]; exact hEq
  have hfix := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (mem_Pt_of_map_cj_eq h s hmap))
  exact Pt_ne_Ln h (hfix.symm.trans hmap)

theorem invertsByWeyl_u4ExtTwo {f : ℕ} (hf : 2 ≤ f) {Y Ŷ : Type} [Group Y] [Group Ŷ]
    (hY : CFSG.Quasithin.IsLieOverTwo .PSU 4 f Y) (ι : Y →* Ŷ) (hι : Function.Injective ι)
    (hidx : ι.range.index = 2) {T M₁ M₂ : Subgroup Ŷ} (hpair : IsYAmalgamPair T M₁ M₂) :
    InvertsByWeyl M₁ M₂ (2 ^ f - 1) := by
  obtain ⟨K, hField, h, hChar, hsimple, ⟨e⟩, S⟩ :=
    CFSG.Quasithin.H13.F431.Un.OL.exists_model_yamStd hf hY
  letI : Field K := hField
  letI : CharP K 2 := hChar
  letI : IsSimpleGroup (Xg h) := hsimple
  haveI : Finite (Xg h) := CFSG.LocalAnalysis.EvenBN.U4.finite_gramSU_miyamotoJ4 h
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨by norm_num, by have := h.one_le; omega⟩) odd_one
  exact InvertsByWeyl.of_index_two S (map_Pt_ne_Ln h) hodd (invertsByWeyl_u4 h) e ι hι hidx hpair

end CFSG.Quasithin.WBN
