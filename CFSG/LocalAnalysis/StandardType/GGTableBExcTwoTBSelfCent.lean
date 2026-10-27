module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull

public section

namespace CFSG.StandardType.TableBExcTwoTB

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE8F
  CFSG.RankThree.CentralCover CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TableBExc TableBExcTwo TableBExcTwoFusion

private theorem famKernel_univ_eq_empty
    {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) :
    famKernel (Set.univ : Set (Fin Tag.E7.rank → Lˣ)) = ∅ := by
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hα, hall⟩
  apply redMod_ne_zero_of_isRoot TableBExcTwo.frameE7.symm_one hα
  funext j
  have h1 : ω ^ α j = 1 := by
    rw [← ExcSplitL.rootChar_mulSingle]
    exact hall _ trivial
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hω] at h2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (α j) 3).2 (by exact_mod_cast h2)

theorem centralizer_tE_frameE7
    {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) :
    Subgroup.centralizer ((tE K frameE7).range : Set (adjointGroup .E7 K)) =
      (tE K frameE7).range := by
  classical
  refine le_antisymm ?_ fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  swap
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have h3 := three_dvd_natCard_ext_sub_one hK
  obtain ⟨ω, hω⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hV : Nat.card (torusPow .E7 L 3) = 3 ^ Tag.E7.rank :=
    card_torusPow_E7 (K := L) Nat.prime_three h3
  have hpow : ∀ a : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 a ^ 3 = 1 := fun a => by
    rw [ExcSplitL.rootDiagUnit_pow', show a ^ 3 = 1 from funext fun i => units_pow_three hK (a i),
      rootDiagUnit_one]
  set G := langElt TableBExcTwo.frameE7 hω with hG
  set ι := adjointMap .E7 (algebraMap K L) with hι
  set T := (tE K TableBExcTwo.frameE7).range with hT
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow .E7 L 3 :=
    langElt_conj_frame_eq_torusPow (Or.inl rfl) TableBExcTwo.frameE7 rfl hV hω
  intro c hc
  set x : adjointGroup .E7 L := G⁻¹ * ι c * G with hx
  have hcomm : ∀ a ∈ (Set.univ : Set (Fin Tag.E7.rank → Lˣ)),
      rootDiagUnit .E7 a * (x : ModGL .E7 L) * (rootDiagUnit .E7 a)⁻¹ = x := by
    intro a _
    have hda : rootDiagUnit .E7 a ∈ torusGroup .E7 L := full_of_E7_E8 (Or.inl rfl) a
    set d : adjointGroup .E7 L := ⟨rootDiagUnit .E7 a, torusGroup_le_adjointGroup hda⟩ with hd
    have hdV : d ∈ torusPow .E7 L 3 :=
      ⟨hda, Subtype.ext (by
        rw [Subgroup.coe_pow, hd]
        exact hpow a)⟩
    rw [← hTV] at hdV
    obtain ⟨_, ⟨t, ht, rfl⟩, hdt⟩ := hdV
    have hct : t * c = c * t := Subgroup.mem_centralizer_iff.1 hc t ht
    have hdt' : d = G⁻¹ * ι t * G := by
      rw [← hdt, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxd : d * x = x * d := by
      rw [hdt', hx]
      calc G⁻¹ * ι t * G * (G⁻¹ * ι c * G) = G⁻¹ * ι (t * c) * G := by rw [map_mul]; group
        _ = G⁻¹ * ι (c * t) * G := by rw [hct]
        _ = G⁻¹ * ι c * G * (G⁻¹ * ι t * G) := by rw [map_mul]; group
    have h1 : d * x * d⁻¹ = x := by rw [hxd]; group
    have h2 := congrArg Subtype.val h1
    simpa [hd] using h2
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hxeq⟩ := fam_factor Set.univ x.2 hcomm
  have hker0 := famKernel_univ_eq_empty hω
  have hbot : ∀ S : Set (Fin Tag.E7.rank → ℤ), rootSpan .E7 L (∅ ∩ S) = ⊥ := by
    intro S
    rw [Set.empty_inter]
    exact le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  rw [hker0, hbot, Subgroup.mem_bot] at hu hv
  subst hu hv
  have hw1 : w = 1 :=
    ExcSplitL.eq_one_of_mem_rootCharStabilizer (p := 3) (by norm_num) hω fun j => hw _ trivial
  subst hw1
  have hxh : (x : ModGL .E7 L) = h := by
    rw [hxeq, canonicalRep_one, mul_one, mul_one, mul_one]
  have hxV : x ∈ torusPow .E7 L 3 := by
    refine ⟨hxh ▸ hh, Subtype.ext ?_⟩
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    rw [Subgroup.coe_pow, hxh, hb]
    exact hpow b
  rw [← hTV] at hxV
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hxV
  have hιt : ι t = ι c := by
    have e : G⁻¹ * ι t * G = G⁻¹ * ι c * G := by
      rw [← hx, ← hxt, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    simpa using e
  rw [← adjointMap_injective _ hιt]
  exact ht

end CFSG.StandardType.TableBExcTwoTB
