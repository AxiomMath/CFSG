module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement Pointwise

variable {X : Type} [Group X]

private theorem s16h_eq_of_mul_eq_mul_of_inf_eq_bot {A B : Subgroup X} (hbot : A ⊓ B = ⊥)
    {a a' b b' : X} (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hab : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmemA : a'⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
  have hmemB : b' * b⁻¹ ∈ B := B.mul_mem hb' (B.inv_mem hb)
  have hmem : a'⁻¹ * a ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨hmemA, hab ▸ hmemB⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hb_eq : b' * b⁻¹ = 1 := by rw [← hab]; exact hmem
  exact ⟨(inv_mul_eq_one.mp hmem).symm, (mul_inv_eq_one.mp hb_eq).symm⟩

theorem s16h_sl28_involution_of_index_two_normalizer
    [Finite X]
    {A B T TL TLx : Subgroup X}
    (hT2 : IsPGroup 2 T)
    (hP : (T ⊓ Subgroup.normalizer (A : Set X)).relIndex T = 2)
    (hshape : T ⊓ Subgroup.normalizer (A : Set X) = TL ⊔ TLx)
    (hTL : TL ≤ A) (hTLx : TLx ≤ B)
    (hTL_T : TL ≤ T) (hTLx_T : TLx ≤ T)
    (hTL_syl : CFSG.ABGLocalTools.IsSylowOf 2 TL A)
    (hTLx_syl : CFSG.ABGLocalTools.IsSylowOf 2 TLx B)
    (hcomm : ⁅A, B⁆ = ⊥) (hbot : A ⊓ B = ⊥)
    (hconj : ∀ t ∈ T, t ∉ Subgroup.normalizer (A : Set X) →
      A.map (MulAut.conj t).toMonoidHom = B) :
    ∃ τ : X,
      τ ∈ T ∧
      τ ∉ Subgroup.normalizer (A : Set X) ∧
      τ ^ 2 = 1 ∧
      A.map (MulAut.conj τ).toMonoidHom = B ∧
      TL.map (MulAut.conj τ).toMonoidHom = TLx ∧
      T = (T ⊓ Subgroup.normalizer (A : Set X)) ⊔ Subgroup.zpowers τ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let NA : Subgroup X := Subgroup.normalizer (A : Set X)
  let P : Subgroup X := T ⊓ NA
  have hPrel : P.relIndex T = 2 := hP
  have hnotle : ¬ T ≤ P := by
    intro hle
    have h1 : P.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨t, htT, htP⟩ := SetLike.not_le_iff_exists.mp hnotle
  have htNA : t ∉ NA := fun ht => htP (Subgroup.mem_inf.mpr ⟨htT, ht⟩)
  have ht2P : t ^ 2 ∈ P := by
    have h := Subgroup.sq_mem_of_index_two (H := P.subgroupOf T) hPrel (⟨t, htT⟩ : T)
    rwa [Subgroup.mem_subgroupOf] at h
  have hAt : A.map (MulAut.conj t).toMonoidHom = B := hconj t htT htNA
  have ht2NA : t ^ 2 ∈ NA := (Subgroup.mem_inf.mp ht2P).2
  have hA_t2 : A.map (MulAut.conj (t ^ 2)).toMonoidHom = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp ht2NA
  have hBt : B.map (MulAut.conj t).toMonoidHom = A := by
    rw [← hAt, Subgroup.map_map]
    have hhom : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t ^ 2)).toMonoidHom := by
      rw [pow_two, map_mul]
      ext x
      rfl
    rw [hhom, hA_t2]
  have hAcentB : A ≤ Subgroup.centralizer (B : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hBcentA : B ≤ Subgroup.centralizer (A : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact hcomm)
  have ht2sup : t ^ 2 ∈ TL ⊔ TLx := by rw [← hshape]; exact ht2P
  have hTLcent : TL ≤ Subgroup.centralizer (TLx : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hAcentB (hTL hg)) y (hTLx hy)
  have hLE : TL ≤ Subgroup.normalizer (TLx : Set X) :=
    hTLcent.trans (Subgroup.centralizer_le_normalizer (TLx : Set X))
  have ht2prod : t ^ 2 ∈ (TL : Set X) * (TLx : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right TL TLx hLE]
    exact ht2sup
  obtain ⟨a, haTL, b, hbTLx, hab⟩ := Set.mem_mul.mp ht2prod
  have haA : a ∈ A := hTL haTL
  have hbB : b ∈ B := hTLx hbTLx
  have hTB_eq : T ⊓ B = TLx :=
    hTLx_syl.eq_of_le (le_inf hTLx_T hTLx) inf_le_right hT2.to_inf_left
  have hcardAB : Nat.card A = Nat.card B := by
    have h := Subgroup.card_map_of_injective (K := A)
      (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
    rw [hAt] at h
    exact h.symm
  have hcardT : Nat.card TL = Nat.card TLx := by
    rw [hTL_syl.card_eq, hTLx_syl.card_eq, hcardAB]
  have ht2t : MulAut.conj t (t ^ 2) = t ^ 2 := by
    rw [MulAut.conj_apply]; group
  have hkey : MulAut.conj t a * MulAut.conj t b = a * b := by
    calc MulAut.conj t a * MulAut.conj t b = MulAut.conj t (a * b) := by rw [map_mul]
      _ = MulAut.conj t (t ^ 2) := by rw [hab]
      _ = t ^ 2 := ht2t
      _ = a * b := hab.symm
  have hatB : MulAut.conj t a ∈ B := by
    rw [← hAt]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom haA
  have hbtA : MulAut.conj t b ∈ A := by
    rw [← hBt]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hbB
  have hcomm_elems : Commute (MulAut.conj t b) (MulAut.conj t a) :=
    ((Subgroup.mem_centralizer_iff.mp (hAcentB hbtA)) (MulAut.conj t a) hatB).symm
  have hkey' : MulAut.conj t b * MulAut.conj t a = a * b := by
    rw [hcomm_elems.eq, hkey]
  have hta : MulAut.conj t a = b :=
    (s16h_eq_of_mul_eq_mul_of_inf_eq_bot hbot haA hbB hbtA hatB hkey'.symm).2.symm
  have hab_comm : Commute a b :=
    ((Subgroup.mem_centralizer_iff.mp (hAcentB haA)) b hbB).symm
  have hanormB : A ≤ Subgroup.normalizer (B : Set X) :=
    hAcentB.trans (Subgroup.centralizer_le_normalizer (B : Set X))
  have hBconj : B.map (MulAut.conj a⁻¹).toMonoidHom = B :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hanormB (A.inv_mem haA))
  let τ : X := a⁻¹ * t
  have hτT : τ ∈ T := T.mul_mem (T.inv_mem (hTL_T haTL)) htT
  have hτNA : τ ∉ NA := by
    intro hmem
    apply htNA
    have haNA : a ∈ NA := Subgroup.le_normalizer haA
    have h := NA.mul_mem haNA hmem
    rwa [show a * (a⁻¹ * t) = t by group] at h
  have hτ2 : τ ^ 2 = 1 := by
    have h1 : t * a⁻¹ * t⁻¹ = b⁻¹ := by
      rw [← MulAut.conj_apply, map_inv, hta]
    show (a⁻¹ * t) ^ 2 = 1
    rw [pow_two]
    calc a⁻¹ * t * (a⁻¹ * t) = a⁻¹ * (t * a⁻¹ * t) := by group
      _ = a⁻¹ * (b⁻¹ * t ^ 2) := by
            rw [show t * a⁻¹ * t = b⁻¹ * t ^ 2 by rw [← h1]; group]
      _ = a⁻¹ * (b⁻¹ * (a * b)) := by rw [← hab]
      _ = 1 := by rw [hab_comm.eq]; group
  have hAτ : A.map (MulAut.conj τ).toMonoidHom = B := by
    have hhom : MulAut.conj τ = MulAut.conj a⁻¹ * MulAut.conj t := by
      rw [show τ = a⁻¹ * t from rfl, map_mul]
    have hcomp : (MulAut.conj a⁻¹ * MulAut.conj t).toMonoidHom =
        (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
      ext x
      rfl
    rw [hhom, hcomp, ← Subgroup.map_map, hAt, hBconj]
  have hTLτ : TL.map (MulAut.conj τ).toMonoidHom = TLx := by
    have hTLτ_B : TL.map (MulAut.conj τ).toMonoidHom ≤ B := by
      rw [← hAτ]
      exact Subgroup.map_mono hTL
    have hTLτ_T : TL.map (MulAut.conj τ).toMonoidHom ≤ T := by
      calc TL.map (MulAut.conj τ).toMonoidHom ≤ T.map (MulAut.conj τ).toMonoidHom :=
            Subgroup.map_mono hTL_T
        _ = T := (Subgroup.mem_normalizer_iff_map_conj_eq).mp
              (Subgroup.le_normalizer hτT)
    have hle : TL.map (MulAut.conj τ).toMonoidHom ≤ TLx := by
      have h := le_inf hTLτ_T hTLτ_B
      rwa [hTB_eq] at h
    have hcard : Nat.card TLx ≤ Nat.card (TL.map (MulAut.conj τ).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective, hcardT]
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hsup : T = P ⊔ Subgroup.zpowers τ := by
    let K : Subgroup X := P ⊔ Subgroup.zpowers τ
    change T = K
    have hPK : P ≤ K := le_sup_left
    have hKT : K ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr hτT)
    have hmul : P.relIndex K * K.relIndex T = P.relIndex T :=
      Subgroup.relIndex_mul_relIndex P K T hPK hKT
    rw [hPrel] at hmul
    have hne1 : P.relIndex K ≠ 1 := by
      intro h1
      have hKP : K ≤ P := Subgroup.relIndex_eq_one.mp h1
      have hτP : τ ∈ P := hKP (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ))
      exact hτNA (Subgroup.mem_inf.mp hτP).2
    have hdvd : P.relIndex K ∣ 2 := ⟨K.relIndex T, hmul.symm⟩
    have h2 : P.relIndex K = 2 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (P.relIndex K) hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hKrel : K.relIndex T = 1 := by
      rw [h2] at hmul
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hKrel) hKT
  exact ⟨τ, hτT, hτNA, hτ2, hAτ, hTLτ, hsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
