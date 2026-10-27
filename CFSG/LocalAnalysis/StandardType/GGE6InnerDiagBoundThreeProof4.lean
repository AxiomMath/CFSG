module

public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof3
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.E6IDB

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem card_le_mul_card_fix_range {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {E : Subgroup (ModGL τ K)} [Finite E] (hE : IsElemAbelian p E)
    (hEM : E ≤ monoHat τ K) :
    Nat.card E ≤ Nat.card ((psiHat τ K).comp (Subgroup.inclusion hEM)).range *
      Nat.card {x : Fin τ.rank → ZMod p //
        ∀ a ∈ ((psiHat τ K).comp (Subgroup.inclusion hEM)).range, adAct τ p a x = x} := by
  set ψE : E →* WeylGroup τ := (psiHat τ K).comp (Subgroup.inclusion hEM) with hψE
  have hker : ∀ e : E, ψE e = 1 → ∃ x, (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) := by
    intro e he
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (x := Subgroup.inclusion hEM e) he
    have hb' : (e : ModGL τ K) = rootDiagUnit τ b := hb
    have hbp : b ^ p = 1 := by
      have h1 : (e : ModGL τ K) ^ p = 1 := hE.2 _ e.2
      rw [hb', rootDiagUnit_pow] at h1
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hbp
    exact ⟨x, by rw [hb', hx]⟩
  have hfix : ∀ (e₀ : E) (e : E) (x : Fin τ.rank → ZMod p),
      (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) → adAct τ p (ψE e₀) x = x := by
    intro e₀ e x hx
    have hc := conj_rootDiagUnit_of_mem_monoHat (Subgroup.inclusion hEM e₀) (zetaVec ζ hζ x)
    have hcomm : (e₀ : ModGL τ K) * e * (e₀ : ModGL τ K)⁻¹ = e := by
      rw [TableB.IsElemAbelian.comm hE e₀.2 e.2, mul_inv_cancel_right]
    rw [weylTuple_zetaVec] at hc
    have h2 : rootDiagUnit τ (zetaVec ζ hζ (adAct τ p (ψE e₀) x)) =
        rootDiagUnit τ (zetaVec ζ hζ x) := by
      rw [← hx, ← hcomm, hx]
      exact hc.symm
    exact zetaVec_injective hζo hζ (rootDiagUnit_injective h2)
  have hcardE := TableB.card_range_mul_card_ker ψE
  choose xf hxf using fun e : ψE.ker => hker e e.2
  have hk : Nat.card ψE.ker ≤
      Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ ψE.range, adAct τ p a x = x} := by
    refine Nat.card_le_card_of_injective (fun e => ⟨xf e, ?_⟩) fun a b hab => ?_
    · rintro _ ⟨e₀, rfl⟩
      exact hfix e₀ e (xf e) (hxf e)
    · apply Subtype.ext
      apply Subtype.ext
      have h1 := congrArg Subtype.val hab
      simp only at h1
      rw [hxf a, hxf b, h1]
  calc Nat.card E = Nat.card ψE.range * Nat.card ψE.ker := hcardE.symm
    _ ≤ _ := Nat.mul_le_mul_left _ hk

theorem exists_rootGroup_normalized_monoHat [CharP K 2] (j : Fin τ.rank) :
    ∃ U : Subgroup (adjointGroup τ K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ x : monoHat τ K, psiHat τ K x • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1 →
        ∀ u ∈ U, ∃ v ∈ U, (v : ModGL τ K) = x * u * (x : ModGL τ K)⁻¹ := by
  let xh : Multiplicative K →* adjointGroup τ K :=
    { toFun := fun c => ⟨pinnedX τ K (Pi.single j 1) (Multiplicative.toAdd c),
        pinnedX_mem_adjointGroup _ _⟩
      map_one' := Subtype.ext (pinnedX_zero τ K _)
      map_mul' := fun c c' => Subtype.ext (pinnedX_add τ K _ _ _) }
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨xh.range, fun h => ?_, ?_, ?_⟩
  · have h1 : xh (.ofAdd 1) ∈ xh.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : pinnedX τ K (Pi.single j 1) 1 = pinnedX τ K (Pi.single j 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (pinnedX_injective τ K _ h2)
  · rintro ⟨_, ⟨c, rfl⟩⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    change (pinnedX τ K (Pi.single j 1) (Multiplicative.toAdd c)) ^ 2 = 1
    rw [pow_two, ← pinnedX_add, ← two_mul, htwo, zero_mul, pinnedX_zero]
  · rintro x hfix _ ⟨c, rfl⟩
    obtain ⟨n, hn, a, hxa⟩ := x.2
    have hψ : psiHat τ K x = weylQuotientHom τ K ⟨n, hn⟩ := by
      rw [← psiHat_mul_rootDiagUnit hn a (hxa ▸ x.2)]
      congr 1
      exact Subtype.ext hxa
    rw [hψ] at hfix
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (isRoot_single τ j)
    refine ⟨xh (.ofAdd (μ * ((rootChar a (Pi.single j 1) : K) * Multiplicative.toAdd c))),
      ⟨_, rfl⟩, ?_⟩
    change pinnedX τ K (Pi.single j 1)
        (μ * ((rootChar a (Pi.single j 1) : K) * Multiplicative.toAdd c)) =
      (x : ModGL τ K) * pinnedX τ K (Pi.single j 1) (Multiplicative.toAdd c) *
        (x : ModGL τ K)⁻¹
    rw [hxa]
    have e1 : n * rootDiagUnit τ a * pinnedX τ K (Pi.single j 1) (Multiplicative.toAdd c) *
        (n * rootDiagUnit τ a)⁻¹ = n * (rootDiagUnit τ a *
          pinnedX τ K (Pi.single j 1) (Multiplicative.toAdd c) * (rootDiagUnit τ a)⁻¹) * n⁻¹ := by
      group
    rw [e1, rootDiagUnit_conj_pinnedX a (isRoot_single τ j), hμ, hfix]

end Count

section Fix

variable {K : Type} [Field K]

theorem exists_fixed_single_of_le_xHat {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 K)} [Finite E] (hE : IsElemAbelian 3 E)
    (hEX : E ≤ xHat .E6 K modelHomE6.range) (h5 : 3 ^ 5 ≤ Nat.card E) :
    ∃ j : Fin Tag.E6.rank, ∀ x : monoHat .E6 K, (x : ModGL .E6 K) ∈ E →
      psiHat .E6 K x • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
  have hEM : E ≤ monoHat .E6 K := hEX.trans (xHat_le_monoHat _)
  set ψE : E →* WeylGroup .E6 := (psiHat .E6 K).comp (Subgroup.inclusion hEM) with hψE
  have hψ : ∀ (x : monoHat .E6 K) (hx : (x : ModGL .E6 K) ∈ E), psiHat .E6 K x ∈ ψE.range :=
    fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hAS : ψE.range ≤ modelHomE6.range := by
    rintro _ ⟨e, rfl⟩
    exact (mem_xHat.mp (hEX e.2)).2
  have hA : IsElemAbelian 3 ψE.range :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ψE
  have hcount := card_le_mul_card_fix_range hζo hζ hE hEM
  by_cases hA1 : ψE.range = ⊥
  · refine ⟨⟨0, by decide⟩, fun x hx => ?_⟩
    have h1 := hψ x hx
    rw [hA1, Subgroup.mem_bot] at h1
    rw [h1, one_smul]
  · rcases E6ThreeEnd.refined_E6 _ hAS hA hA1 with hlt | ⟨i, hi⟩
    · exact absurd (h5.trans hcount) (not_le.mpr hlt)
    · obtain ⟨j, hj⟩ : ∃ j : Fin Tag.E6.rank, testE6 (i + 1) = Pi.single j 1 := by
        fin_cases i
        · exact ⟨⟨4, by decide⟩, rfl⟩
        · exact ⟨⟨1, by decide⟩, rfl⟩
        · exact ⟨⟨0, by decide⟩, rfl⟩
      have hst : Subgroup.zpowers (gE6 i) ≤
          MulAction.stabilizer (WeylGroup .E6) (testE6 (i + 1)) :=
        Subgroup.zpowers_le.mpr (testE6_fix (i + 1) i (by fin_cases i <;> decide))
      refine ⟨j, fun x hx => ?_⟩
      have h0 := hψ x hx
      rw [hi] at h0
      have h1 := hst h0
      rwa [MulAction.mem_stabilizer_iff, hj] at h1

end Fix

section Main

variable {K : Type} [Field K]

theorem exists_normalized_two_of_le_hatGroup [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {W : Subgroup (hatGroup .E6 K)} (hW : IsElemAbelian 3 W) (h5 : 3 ^ 5 ≤ Nat.card W) :
    ∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ w ∈ W, ∀ u ∈ U, hatAut .E6 K w u ∈ U := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) (TableB.isPGroup_of_isElemAbelian hW)
  set W' := W.map (MulAut.conj c).toMonoidHom with hW'
  set E : Subgroup (ModGL .E6 K) := W'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map (TableB.isElemAbelian_map hW _) _
  have hcardE : Nat.card E = Nat.card W := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hW',
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have : Finite E := Finite.of_surjective (fun p : W' => (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : E))
    (by rintro ⟨_, ⟨p, hp, rfl⟩⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨j, hj⟩ := exists_fixed_single_of_le_xHat hζo hζ hE hEX (hcardE ▸ h5)
  obtain ⟨U₀, hU₀, hU₀2, hU₀n⟩ := exists_rootGroup_normalized_monoHat (τ := .E6) (K := K) j
  refine ⟨U₀.map (hatAut .E6 K c)⁻¹.toMonoidHom, fun h => hU₀ ?_, hU₀2.map _, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ (hatAut .E6 K c)⁻¹.injective] at h
  · rintro w hw _ ⟨u₀, hu₀, rfl⟩
    have hpE : ((c * w * c⁻¹ : hatGroup .E6 K) : ModGL .E6 K) ∈ E :=
      ⟨c * w * c⁻¹, ⟨w, hw, rfl⟩, rfl⟩
    have hpm := xHat_le_monoHat _ (hEX hpE)
    obtain ⟨v, hv, hveq⟩ := hU₀n ⟨_, hpm⟩ (hj ⟨_, hpm⟩ hpE) u₀ hu₀
    have e1 : hatAut .E6 K (c * w * c⁻¹) u₀ = v :=
      Subtype.ext (by rw [coe_hatAut_apply]; exact hveq.symm)
    refine ⟨v, hv, ?_⟩
    rw [← e1, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self]

end Main

end CFSG.StandardType.E6IDB

end
