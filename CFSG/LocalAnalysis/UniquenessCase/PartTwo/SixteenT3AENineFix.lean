module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNorm
public import CFSG.LargeExtraspecial.S12InspFamSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16t_natSum3_exists_fixing_subgroup {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L Z : Subgroup (MulAut W)} {J : Subgroup W}
    (hL : IsPSL 3 2 1 ↥L) (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (hAL : ∀ a ∈ A, L.map (MulAut.conj a).toMonoidHom = L)
    (hAZ : ∀ a ∈ A, Z.map (MulAut.conj a).toMonoidHom = Z)
    (hAJ : ∀ a ∈ A, J.map a.toMonoidHom = J) :
    ∃ B : Subgroup (MulAut W), B ≤ A ∧ E3.mQuot A B ≤ 2 ∧ J ≤ fixV B := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  let f : ↥A →* MulAut W := A.subtype
  have hA2 : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA
  have hf2 : ∀ a : ↥A, (f a) ^ 2 = 1 := fun a => hA.2 (a : MulAut W) a.2
  have hfL : ∀ a : ↥A, L.map (MulAut.conj (f a)).toMonoidHom = L :=
    fun a => hAL (a : MulAut W) a.2
  have hfZ : ∀ a : ↥A, Z.map (MulAut.conj (f a)).toMonoidHom = Z :=
    fun a => hAZ (a : MulAut W) a.2
  have hfJ : ∀ a : ↥A, J.map (f a).toMonoidHom = J :=
    fun a => hAJ (a : MulAut W) a.2
  have hJkeep := hJ
  obtain ⟨I₀, _, _, hI₀, _, _, hc₀, _, _, _, _, hsum⟩ := hJ
  have hI₀J : I₀ ≤ J := by
    rw [← hsum]
    exact le_sup_left.trans le_sup_left
  have hnt : ∃ x ∈ L, ∃ v ∈ I₀, x v ≠ v := s16c167_norm_irr_nontrivial hI₀ hc₀
  have hI₀inv : ∀ x ∈ L, ∀ v ∈ I₀, x v ∈ I₀ := fun x hx v hv => hI₀.1 ⟨x, hx⟩ v hv
  have hfaith : ∀ l ∈ L, (∀ w ∈ J, l w = w) → l = 1 := by
    intro l hl hfix
    exact rank3_inj hL hI₀inv hnt l hl (fun v hv => hfix v (hI₀J hv))
  have hex : ∀ a : ↥A, ∃ l : L, ∀ w ∈ J, f a w = (l : MulAut W) w := by
    intro a
    have h2 : (f a) ^ (2 ^ 1) = 1 := by simpa using hf2 a
    obtain ⟨l, hl, hle⟩ := (s16c167_natSum3_normalizer_two hW hL hJkeep hZ hZL hZJ hZf h2
      (hfZ a) (hfL a) (hfJ a)).1
    exact ⟨⟨l, hl⟩, hle⟩
  let φfun : ↥A → L := fun a => Classical.choose (hex a)
  have hφspec : ∀ a w (hw : w ∈ J), f a w = (φfun a : MulAut W) w :=
    fun a w hw => Classical.choose_spec (hex a) w hw
  have hmul : ∀ a b : ↥A, φfun (a * b) = φfun a * φfun b := by
    intro a b
    apply Subtype.ext
    change (φfun (a * b) : MulAut W) = (φfun a : MulAut W) * (φfun b : MulAut W)
    rw [← inv_mul_eq_one]
    have hmem : ((φfun (a * b) : MulAut W))⁻¹ *
        ((φfun a : MulAut W) * (φfun b : MulAut W)) ∈ L :=
      L.mul_mem (L.inv_mem (φfun (a * b)).2) (L.mul_mem (φfun a).2 (φfun b).2)
    have hfix : ∀ w ∈ J, (((φfun (a * b) : MulAut W))⁻¹ *
        ((φfun a : MulAut W) * (φfun b : MulAut W))) w = w := by
      intro w hw
      have hbw : f b w ∈ J := by
        have hmem2 : f b w ∈ J.map (f b).toMonoidHom := Subgroup.mem_map_of_mem _ hw
        rwa [hfJ b] at hmem2
      have h1 : (φfun b : MulAut W) w = f b w := (hφspec b w hw).symm
      have h2 : (φfun a : MulAut W) (f b w) = f a (f b w) := (hφspec a (f b w) hbw).symm
      have h3 : (φfun (a * b) : MulAut W) w = f (a * b) w := (hφspec (a * b) w hw).symm
      calc (((φfun (a * b) : MulAut W))⁻¹ *
            ((φfun a : MulAut W) * (φfun b : MulAut W))) w
          = ((φfun (a * b) : MulAut W))⁻¹
              (((φfun a : MulAut W) * (φfun b : MulAut W)) w) := by rw [MulAut.mul_apply]
        _ = ((φfun (a * b) : MulAut W))⁻¹
              ((φfun a : MulAut W) ((φfun b : MulAut W) w)) := by rw [MulAut.mul_apply]
        _ = ((φfun (a * b) : MulAut W))⁻¹ (f a (f b w)) := by rw [h1, h2]
        _ = ((φfun (a * b) : MulAut W))⁻¹ (f (a * b) w) := by
              rw [show f (a * b) w = f a (f b w) by rw [map_mul, MulAut.mul_apply]]
        _ = ((φfun (a * b) : MulAut W))⁻¹ ((φfun (a * b) : MulAut W) w) := by rw [h3]
        _ = w := MulAut.inv_apply_self W (φfun (a * b) : MulAut W) w
    exact hfaith _ hmem hfix
  let φ : ↥A →* L := MonoidHom.mk' φfun hmul
  have hφspec' : ∀ a w (hw : w ∈ J), f a w = (φ a : MulAut W) w := hφspec
  have hAtop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup ↥A) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · exact Subtype.ext (Subtype.ext (hA.1 a.1.1 a.1.2 b.1.1 b.1.2))
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA.2 x.1 x.2
  have hE : CFSG.Open.IsElemAbelian 2 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hAtop φ
  have hcard : Nat.card φ.range ≤ 2 ^ 2 :=
    CFSG.LargeExtraspecial.S12Insp5.card_le_four_of_lieModel_PSL32
      (Or.inl ⟨by decide, hL⟩ : CFSG.Blueprint.LieModel ↥L .PSL 3 2 1) φ.range hE
  have hrel : ((MonoidHom.ker φ).map A.subtype).relIndex A = (MonoidHom.ker φ).index := by
    have htop : (⊤ : Subgroup ↥A).map A.subtype = A := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := Subgroup.relIndex_map_map_of_injective (MonoidHom.ker φ) (⊤ : Subgroup ↥A)
      (Subgroup.subtype_injective A)
    rw [htop, Subgroup.relIndex_top_right] at h
    exact h
  refine ⟨(MonoidHom.ker φ).map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hmq : E3.mQuot A ((MonoidHom.ker φ).map A.subtype) =
        padicValNat 2 ((MonoidHom.ker φ).index) := by
      rw [E3.mQuot, hrel]
    rw [hmq]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (hA2.to_quotient (MonoidHom.ker φ))
    have hk' : (MonoidHom.ker φ).index = 2 ^ k := by
      rw [Subgroup.index, hk]
    rw [hk', padicValNat.prime_pow]
    have h2k : 2 ^ k ≤ 2 ^ 2 := by
      rw [← hk', Subgroup.index_ker]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2k
  · intro w hw
    rw [mem_fixV]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    have ha1 : φ a = 1 := MonoidHom.mem_ker.1 ha
    rw [hφspec' a w hw, ha1]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
