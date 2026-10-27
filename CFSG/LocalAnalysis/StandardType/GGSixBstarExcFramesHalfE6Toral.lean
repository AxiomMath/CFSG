module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Conj
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.E6Pilot
  TableBExc.E6Three


theorem exists_conj_rootDiagUnit_of_card_ge_of_le_xHat
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL .E6 L)} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEX : E ≤ xHat .E6 L modelHomE6.range) (hcard : 3 ^ 5 ≤ Nat.card E) :
    ∃ y ∈ adjointGroup .E6 L, ∀ e ∈ E, ∃ c, y * e * y⁻¹ = rootDiagUnit .E6 c := by
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  rcases NoOffTwE6Three.torus_or_cyclic hζo hζ hE hEX hcard with hT | ⟨i, hi⟩
  · exact ⟨1, one_mem _, fun e he => by
      obtain ⟨v, hv⟩ := hT e he
      exact ⟨zetaVec ζ hζ v, by simpa using hv⟩⟩
  · exact SmallExc.exists_conj_diag_of_le_xHat hζo hE hi

theorem bigElemAbelianToralBar_E6_three : BigElemAbelianToralBar .E6 3 := by
  intro K _ _ _ _ A hA hcomm hpow hcard
  have hcard5 : 3 ^ 5 ≤ Nat.card A := hcard
  have hAfin : (A : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite := by
    have : Finite A := Nat.finite_of_card_ne_zero (lt_of_lt_of_le (by norm_num) hcard5).ne'
    exact Set.toFinite _
  obtain ⟨K₁, hK₁, -, hq, hdesc⟩ := exists_descent_subgroup (ℓ := 2) (r := 3) (by norm_num)
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hA hAfin ∅ (M := 1) le_rfl
  haveI : Finite K₁ := hK₁
  haveI : Finite (ModGL Tag.E6 K₁) := finite_modGL
  set ι := K₁.subtype
  have hA₁C : A.comap (baseChangeGL ι) ≤ adjointGroup Tag.E6 K₁ := comap_le_adjointGroup ι hdesc
  have hcomm₁ : ∀ x ∈ A.comap (baseChangeGL ι), ∀ y ∈ A.comap (baseChangeGL ι),
      x * y = y * x := fun x hx y hy => baseChangeGL_injective ι (by
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy))
  have hpow₁ : ∀ x ∈ A.comap (baseChangeGL ι), x ^ 3 = 1 := fun x hx =>
    baseChangeGL_injective ι (by rw [map_pow, map_one]; exact hpow _ (Subgroup.mem_comap.mp hx))
  have hcard₁ : Nat.card (A.comap (baseChangeGL ι)) = Nat.card A := by
    have hrange : A ≤ (baseChangeGL (τ := Tag.E6) ι).range := fun x hx => by
      obtain ⟨y, -, hy⟩ := hdesc x hx
      exact ⟨y, hy⟩
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    exact (Subgroup.card_map_of_injective (baseChangeGL_injective ι)).symm
  have h3 : 3 ∣ Nat.card K₁ - 1 := by
    have h1 : 1 ≤ Nat.card K₁ := Nat.card_pos
    simpa using (Nat.modEq_iff_dvd' h1).mp hq.symm
  obtain ⟨k, hk⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_E6 h3)
    ((isPGroup_comap ι hpow).of_equiv (Subgroup.subgroupOfEquivOfLe hA₁C).symm)
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup (ModGL Tag.E6 K₁),
      E = (A.comap (baseChangeGL ι)).map (MulAut.conj (k : ModGL Tag.E6 K₁)).toMonoidHom :=
    ⟨_, rfl⟩
  have hEX : E ≤ xHat Tag.E6 K₁ modelHomE6.range := by
    rw [hEdef]
    rintro _ ⟨x, hx, rfl⟩
    have hmem : (MulAut.conj k).toMonoidHom (⟨x, hA₁C hx⟩ : adjointGroup Tag.E6 K₁) ∈
        ((A.comap (baseChangeGL ι)).subgroupOf (adjointGroup Tag.E6 K₁)).map
          (MulAut.conj k).toMonoidHom :=
      ⟨⟨x, hA₁C hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    simpa using mem_weylX_iff_mem_xHat.mp (hk hmem)
  have hE : CFSG.Open.IsElemAbelian 3 E := by
    rw [hEdef]
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
        hcomm₁ x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hpow₁ x hx, map_one]
  have hc : 3 ^ 5 ≤ Nat.card E := by
    rw [hEdef, Subgroup.card_map_of_injective (f := (MulAut.conj (k : ModGL Tag.E6 K₁)).toMonoidHom)
      (MulAut.conj _).injective, hcard₁]
    exact hcard5
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := K₁ˣ) 3 (by rwa [Nat.card_units])
  obtain ⟨y, hyC, hy⟩ :=
    exists_conj_rootDiagUnit_of_card_ge_of_le_xHat hζo hE hEX hc
  obtain ⟨u, hu⟩ : ∃ u : ModGL Tag.E6 K₁, u = y * (k : ModGL Tag.E6 K₁) := ⟨_, rfl⟩
  have hg : baseChangeGL ι u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι (hu ▸ mul_mem hyC k.2)
  refine ⟨(baseChangeGL ι u)⁻¹, inv_mem hg, fun x hx => ?_⟩
  obtain ⟨x₁, -, rfl⟩ := hdesc x hx
  obtain ⟨c, hc⟩ := hy ((MulAut.conj (k : ModGL Tag.E6 K₁)).toMonoidHom x₁)
    (by rw [hEdef]; exact ⟨x₁, hx, rfl⟩)
  have heq : baseChangeGL ι u * baseChangeGL ι x₁ * (baseChangeGL ι u)⁻¹ =
      baseChangeGL ι (rootDiagUnit Tag.E6 c) := by
    rw [← hc, hu]
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmem := mul_mem (mul_mem hg (hA hx)) (inv_mem hg)
  rw [heq, baseChangeGL_rootDiagUnit] at hmem
  rw [inv_inv, heq, baseChangeGL_rootDiagUnit]
  exact rootDiagUnit_mem_torusGroup_of_mem_adjointGroup _ hmem

end CFSG.StandardType.ExcFramesHalf
