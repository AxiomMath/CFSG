module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S146zRSL
public import CFSG.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SL2Sylow
open scoped MatrixGroups Pointwise

namespace L3316

namespace SL2Over

variable {F : Type} [Field F]

theorem le_borel_of_ne_top {A : Subgroup SL(2, F)} (hA : stdSylow F ≤ A) (hne : A ≠ ⊤) :
    A ≤ borel F := by
  intro g hg
  by_contra hc
  have hc' : g 1 0 ≠ 0 := fun h0 => hc (mem_borel.mpr h0)
  have hlo : ∀ s : F, lowerElt s ∈ A := by
    intro s
    have hconj : upperElt (-(g 0 0 / g 1 0)) * (g * upperElt (-(s / g 1 0 ^ 2)) * g⁻¹) *
        upperElt (g 0 0 / g 1 0) = lowerElt s := by
      rw [conj_upperElt_conj_eq_lowerElt g hc']
      congr 1
      field_simp
    rw [← hconj]
    exact mul_mem (mul_mem (hA (upperElt_mem_stdSylow _)) (mul_mem (mul_mem hg
      (hA (upperElt_mem_stdSylow _))) (inv_mem hg))) (hA (upperElt_mem_stdSylow _))
  exact hne (eq_top_of_unitriangular_mem (fun t => hA (upperElt_mem_stdSylow t)) hlo)

theorem le_normalizer_of_ne_top [Finite F] [CharP F 2] {U A : Subgroup SL(2, F)}
    (hU : IsPGroup 2 U) (hU' : ¬ 2 ∣ U.index) (hUA : U ≤ A) (hA : A ≠ ⊤) :
    A ≤ Subgroup.normalizer (U : Set SL(2, F)) := by
  obtain ⟨e', he'⟩ := exists_equiv_map_eq_stdSylow (MulEquiv.refl SL(2, F)) hU hU'
  have h1 : stdSylow F ≤ A.map e'.toMonoidHom := he' ▸ Subgroup.map_mono hUA
  have h2 : A.map e'.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hA
    rw [eq_top_iff]
    intro x _
    have hx : e' x ∈ A.map e'.toMonoidHom := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← e'.injective hyx]
  have h3 := le_borel_of_ne_top h1 h2
  rw [← normalizer_stdSylow, ← he', ← Subgroup.map_equiv_normalizer_eq] at h3
  exact (Subgroup.map_le_map_iff_of_injective e'.injective).1 h3

end SL2Over

variable {G : Type} [Group G] [Finite G]

theorem exists_isUniqueMaxOver {X T : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT : IsSylowTwoOf T (X ⊔ T)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : 4 ≤ Nat.card F) {f : ↥X →* SL(2, F)} (hf : Function.Surjective f)
    (hk : IsPGroup 2 ↥f.ker) : ∃ M, IsUniqueMaxOver (X ⊔ T) T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup SL(2, F) := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup hF4
  have hTXs : IsSylowTwoOf (T ⊓ X) X := by
    refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
    have h1 := B6.relIndex_inf_eq_relIndex_sup hTX
    have h2 := hT.2.2
    rw [show (T.subgroupOf (X ⊔ T)).index = T.relIndex (X ⊔ T) from rfl, sup_comm] at h2
    show ¬ 2 ∣ (T ⊓ X).relIndex X
    rwa [h1]
  set U : Subgroup SL(2, F) := ((T ⊓ X).subgroupOf X).map f with hUdef
  have hUp : IsPGroup 2 U :=
    (hTXs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map f
  have hUi : ¬ 2 ∣ U.index := fun h2 =>
    hTXs.2.2 (h2.trans (Subgroup.index_map_dvd _ hf))
  have hkT : ∀ x : ↥X, x ∈ f.ker → (x : G) ∈ T ⊓ X := by
    intro x hx
    have hle : f.ker.map X.subtype ≤ pCoreOf 2 X := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _)
        ?_ (hk.map X.subtype)
      intro y hy
      refine Subgroup.le_normalizer_map X.subtype ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [Subgroup.normalizer_eq_top_iff.mpr f.normal_ker]
      exact Subgroup.mem_top _
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTXs (hle ⟨x, hx, rfl⟩)
  set B : Subgroup G := X ⊓ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) with hBdef
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hTX ht) y
    constructor
    · rintro ⟨hyT, hyX⟩
      exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht), h1.mp hyX⟩
    · rintro ⟨hyT, hyX⟩
      refine ⟨?_, h1.mpr hyX⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
      simpa [mul_assoc] using this
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := by
    intro t ht
    have hA := hTX ht
    have hB : t ∈ Subgroup.normalizer
        ((Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (hTN t ht)
    rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
    intro y
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hA y).mp h1, (hB y).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨(hA y).mpr h1, (hB y).mpr h2⟩⟩
  have hconj : ∀ x : ↥X, f x ∈ Subgroup.normalizer (U : Set SL(2, F)) →
      ∀ y ∈ T ⊓ X, (x : G) * y * (x : G)⁻¹ ∈ T ⊓ X := by
    intro x hx y hy
    have hyX : y ∈ X := hy.2
    have hfy : f (x * ⟨y, hyX⟩ * x⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨⟨y, hyX⟩, hy, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hfy
    have hk' : w⁻¹ * (x * ⟨y, hyX⟩ * x⁻¹) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
    have h1 := hkT _ hk'
    have hwT : (w : G) ∈ T ⊓ X := hw
    have h2 := (T ⊓ X).mul_mem hwT h1
    simpa [mul_assoc] using h2
  have hpre : ∀ x : ↥X, f x ∈ Subgroup.normalizer (U : Set SL(2, F)) → (x : G) ∈ B := by
    intro x hx
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj x hx y, fun hy => ?_⟩
    have hx' : f x⁻¹ ∈ Subgroup.normalizer (U : Set SL(2, F)) := by
      rw [map_inv]; exact Subgroup.inv_mem _ hx
    have := hconj x⁻¹ hx' _ hy
    simpa [mul_assoc] using this
  have hXT : ((X ⊔ T : Subgroup G) : Set G) = (X : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X T hTX
  have key : ∀ H : Subgroup G, T ≤ H → H ≤ X ⊔ T → H ≠ X ⊔ T → H ≤ B ⊔ T := by
    intro H hTH hHXT hne
    set A : Subgroup SL(2, F) := (H.subgroupOf X).map f with hAdef
    have hUA : U ≤ A := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨w, (hTH (hw : (w : G) ∈ T ⊓ X).1 : (w : G) ∈ H), rfl⟩
    have hAne : A ≠ ⊤ := by
      intro hA
      apply hne
      apply le_antisymm hHXT
      refine sup_le (fun x hx => ?_) hTH
      have hx' : f ⟨x, hx⟩ ∈ A := hA ▸ Subgroup.mem_top _
      obtain ⟨h, hh, hhx⟩ := hx'
      have hk' : h⁻¹ * ⟨x, hx⟩ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]
      have h3 := H.mul_mem (hh : (h : G) ∈ H) (hTH (hkT _ hk').1)
      simpa using h3
    have hAN := SL2Over.le_normalizer_of_ne_top hUp hUi hUA hAne
    intro h hh
    have hmem : h ∈ ((X ⊔ T : Subgroup G) : Set G) := hHXT hh
    rw [hXT] at hmem
    obtain ⟨x, hx, t, ht, rfl⟩ := hmem
    have hxH : x ∈ H := by
      have := H.mul_mem hh (H.inv_mem (hTH ht))
      simpa using this
    have hxB : x ∈ B := hpre ⟨x, hx⟩ (hAN ⟨⟨x, hx⟩, hxH, rfl⟩)
    exact (B ⊔ T).mul_mem (Subgroup.mem_sup_left hxB) (Subgroup.mem_sup_right ht)
  have hlt : B ⊔ T < X ⊔ T := by
    refine lt_of_le_of_ne (sup_le_sup_right inf_le_left T) fun heq => ?_
    have hBT : ((B ⊔ T : Subgroup G) : Set G) = (B : Set G) * (T : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left B T hTB
    have hXN : X ≤ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) := by
      intro x hx
      have hmem : x ∈ ((B ⊔ T : Subgroup G) : Set G) := heq ▸ (le_sup_left : X ≤ X ⊔ T) hx
      rw [hBT] at hmem
      obtain ⟨b, hb, t, ht, rfl⟩ := hmem
      have htX : t ∈ X := by
        have := X.mul_mem (X.inv_mem hb.1) hx
        simpa using this
      exact Subgroup.mul_mem _ hb.2 (Subgroup.le_normalizer ⟨ht, htX⟩)
    have hUn : U.Normal := by
      refine ⟨fun u hu g => ?_⟩
      obtain ⟨x, rfl⟩ := hf g
      obtain ⟨w, hw, rfl⟩ := hu
      refine ⟨x * w * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have h5 := (Subgroup.mem_normalizer_iff.mp (hXN x.2) (w : G)).mp hw
      exact Subgroup.mem_subgroupOf.mpr (by push_cast; exact h5)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
    · apply hUi
      rw [h, Subgroup.index_bot]
      have h2 : orderOf (upperElt (1 : F)) = 2 := by
        apply orderOf_eq_prime
        · rw [sq, upperElt_mul_upperElt, CharTwo.add_self_eq_zero, upperElt_zero]
        · intro h1
          have := upperElt_injective (h1.trans upperElt_zero.symm)
          exact one_ne_zero this
      have h6 := orderOf_dvd_natCard (upperElt (1 : F))
      rwa [h2] at h6
    · rw [h] at hUp
      have hp : IsPGroup 2 SL(2, F) := hUp.of_equiv Subgroup.topEquiv
      have := hp.isNilpotent
      exact not_isSolvable_sl2 hF4 inferInstance
  refine ⟨B ⊔ T, isUniqueMaxOver_iff.mpr ⟨⟨hlt, fun K hK hKH => ?_⟩, le_sup_right,
    fun N hN hTN' => ?_⟩⟩
  · by_contra hne
    exact absurd (key K (le_sup_right.trans hK.le) hKH hne) (not_le_of_gt hK)
  · have hN1 := key N hTN' hN.1.le (ne_of_lt hN.1)
    by_contra hne
    exact absurd (hN.2 _ (lt_of_le_of_ne hN1 hne) (le_of_lt hlt)) (ne_of_lt hlt)


theorem pCoreOf_sup_ne_bot (h10 : Stmt3_3_10) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    {X : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hO : pCoreOf 2 (X ⊔ T) ≠ ⊥)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {f : ↥X →* SL(2, F)} (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker) :
    pCoreOf 2 (X ⊔ T ⊔ D) ≠ ⊥ := by
  have hT := h.sylow
  have hsyl : IsSylowTwoOf T (X ⊔ T) :=
    ⟨le_sup_right, hT.1, fun h2 => hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  exact (h10 G T M L D h).1 (X ⊔ T) ⟨le_sup_right, hO⟩ (exists_isUniqueMaxOver hTX hsyl hF4 hf hk)

end L3316

end CFSG.Quasithin.H13
