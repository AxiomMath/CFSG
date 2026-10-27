module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusPackageP4
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45_exists_mul_ne {R : Type*} [Group R] [IsSimpleGroup R]
    (hperf : commutator R = ⊤) : ∃ a b : R, a * b ≠ b * a := by
  haveI : Group.IsPerfect R := Group.isPerfect_def.mpr hperf
  haveI : Nontrivial R := IsSimpleGroup.toNontrivial
  have hnc : ¬ IsMulCommutative R := Group.IsPerfect.not_isMulCommutative R
  rw [isMulCommutative_iff] at hnc
  push Not at hnc
  exact hnc

private theorem ggL45_conj_injective {R : Type*} [Group R] [IsSimpleGroup R]
    (hnc : ∃ a b : R, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  have hcenter : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a)
  rw [injective_iff_map_eq_one]
  intro r hr
  have hmem : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h := congrArg (fun f : MulAut R => f s) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc s * r = (r * s * r⁻¹) * r := by rw [h]
      _ = r * s := by group
  rwa [hcenter, Subgroup.mem_bot] at hmem

private lemma ggL45_conj_conj {R : Type*} [Group R] (α : MulAut R) (r : R) :
    α * MulAut.conj r * α⁻¹ = MulAut.conj (α r) := by
  ext s
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem ggL45_commutator_eq_top_of_centerQuot {K R : Type*} [Group K] [Group R]
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) : commutator R = ⊤ := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hK
  haveI hQ : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective (Subgroup.center K))
  exact (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective).commutator_eq_top

private theorem ggL45_isElemAbelian_comap {H G : Type*} [Group H] [Group G] {p : ℕ}
    {ψ : H →* G} (hψ : Function.Injective ψ) {B : Subgroup G}
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.comap ψ) := by
  obtain ⟨hcomm, hexp⟩ := hB
  refine ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hψ ?_)), fun x hx => ?_⟩
  · simpa [Subgroup.coe_mul, map_mul] using
      congrArg Subtype.val (isMulCommutative_iff.mp hcomm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
  · apply hψ
    rw [map_pow, map_one]
    exact hexp (ψ x) hx

private theorem ggL45_isSimpleGroup_recipe (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :=
  CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
    (K := K) (n := 4) (by norm_num)

private theorem ggL45_labelAll_isSimpleGroup {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) :
    LargeEvenLabelAll lab (fun R _ _ _ => IsSimpleGroup R) :=
  largeEvenLabelAll_omegaPlus ht (by omega) (fun K _ _ _ _ => by
    rw [h4]
    exact ggL45_isSimpleGroup_recipe K)

private theorem ggL45HFour_d4_three_H4 {R : Type} [Group R] {I F : Set (MulAut R)}
    (hfix : GGRawThreeFixCyclic R I F) (hsimple : IsSimpleGroup R)
    (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E)
    (h27 : 27 ≤ Nat.card E) (hEI : ∀ e ∈ E, GGL45InducesIn θ I e) :
    GGL45HFour 3 I θ E := by
  classical
  haveI : IsSimpleGroup R := hsimple
  have hperfR : commutator R = ⊤ := ggL45_commutator_eq_top_of_centerQuot hK θ
  have hnc : ∃ a b : R, a * b ≠ b * a := ggL45_exists_mul_ne hperfR
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) := ggL45_conj_injective hnc
  obtain ⟨hIeq, S, hInnS, hcyc, hSfix⟩ := hfix hsimple hnc
  refine ⟨S, ?_, ?_, ?_⟩
  · intro u hu
    exact hInnS (by
      rw [hIeq] at hu
      simpa [LargeEvenInnSet, MonoidHom.mem_range] using hu)
  · obtain ⟨g, hgS, hg⟩ := hcyc
    refine ⟨g, hgS, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hg x hx
    exact ⟨k, by rw [hIeq]; simpa [LargeEvenInnSet, MonoidHom.mem_range] using hk⟩
  · intro α hα hαE
    let U : Subgroup (MulAut R) := E.map (ggInducedAut θ)
    let E₀ : Subgroup R := U.comap (MulAut.conj : R →* MulAut R)
    have hUle : U ≤ (MulAut.conj : R →* MulAut R).range := by
      rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      have hmem : ggInducedAut θ e ∈ I := (ggL45_inducesIn_iff θ I e).mp (hEI e he)
      rw [hIeq] at hmem
      simpa [LargeEvenInnSet, MonoidHom.mem_range] using hmem
    have hUab : IsElemAbelian 3 U := ggIsElemAbelian_map hE (ggInducedAut θ)
    have hE₀ab : IsElemAbelian 3 E₀ := ggL45_isElemAbelian_comap hconj_inj hUab
    have hcardU : Nat.card U = Nat.card E :=
      Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)
    have hcardE₀ : Nat.card E₀ = Nat.card U := by
      have hmap : Subgroup.map (MulAut.conj : R →* MulAut R)
          (U.comap (MulAut.conj : R →* MulAut R)) = U := Subgroup.map_comap_eq_self hUle
      calc Nat.card E₀ = Nat.card (U.comap (MulAut.conj : R →* MulAut R)) := rfl
        _ = Nat.card (Subgroup.map (MulAut.conj : R →* MulAut R)
              (U.comap (MulAut.conj : R →* MulAut R))) :=
              (Subgroup.card_map_of_injective hconj_inj).symm
        _ = Nat.card U := by rw [hmap]
    have hE₀9 : 9 < Nat.card E₀ := by rw [hcardE₀, hcardU]; omega
    have hE₀fix : ∀ e ∈ E₀, α e = e := by
      intro r hr
      have hr' : MulAut.conj r ∈ U := hr
      rw [Subgroup.mem_map] at hr'
      obtain ⟨e, he, heq⟩ := hr'
      have hcomm : α * MulAut.conj r = MulAut.conj r * α := by
        rw [← heq]
        exact hαE e he
      have hconj : MulAut.conj (α r) = MulAut.conj r := by
        calc MulAut.conj (α r) = α * MulAut.conj r * α⁻¹ := (ggL45_conj_conj α r).symm
          _ = (MulAut.conj r * α) * α⁻¹ := by rw [hcomm]
          _ = MulAut.conj r := by group
      exact hconj_inj hconj
    exact hSfix α hα E₀ hE₀ab hE₀9 hE₀fix

private theorem ggL45HFour_d4_three_H4Mod {R : Type} [Group R] {I F : Set (MulAut R)}
    (hfix : GGRawThreeFixCyclic R I F) (hsimple : IsSimpleGroup R)
    (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E)
    (h27 : 27 ≤ Nat.card E) (hEI : ∀ e ∈ E, GGL45InducesIn θ I e)
    (f : MulAut R) (hf3 : f ^ 3 = 1) (hfI : f ∉ I)
    (hfE : ∀ e ∈ E, f * ggInducedAut θ e = ggInducedAut θ e * f) :
    GGL45HFourMod 3 I θ E f := by
  haveI : IsSimpleGroup R := hsimple
  have hperfR : commutator R = ⊤ := ggL45_commutator_eq_top_of_centerQuot hK θ
  have hnc : ∃ a b : R, a * b ≠ b * a := ggL45_exists_mul_ne hperfR
  obtain ⟨hIeq, S, hInnS, hcyc, hSfix⟩ := hfix hsimple hnc
  let I' : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range
  have hI'eq : (I' : Set (MulAut R)) = I := by
    rw [hIeq]
    rfl
  haveI : I'.Normal := ggInnNormal R
  have hfI' : f ∉ I' := fun hf => hfI (hI'eq ▸ hf)
  have hH4 : GGL45HFour 3 I θ E :=
    ggL45HFour_d4_three_H4 hfix hsimple K θ hK E hE h27 hEI
  have hH4' : GGL45HFour 3 (I' : Set (MulAut R)) θ E := by
    rw [hI'eq]
    exact hH4
  have hres := ggL45HFourMod_of_HFour (p := 3) Nat.prime_three I' hf3 hfI' hfE hH4'
  rwa [hI'eq] at hres

theorem ggL45HFourMod_d4_three {lab : LargeEvenLabel} (ht : lab.tag = .D) (h4 : lab.rank = 4) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
        ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → 27 ≤ Nat.card E →
          (∀ e ∈ E, GGL45InducesIn θ I e) → ∀ f : MulAut R, f ^ 3 = 1 → f ∉ I →
            (∀ e ∈ E, f * ggInducedAut θ e = ggInducedAut θ e * f) → GGL45HFourMod 3 I θ E f := by
  refine LargeEvenLabelAll.mono ?_
    (largeEvenLabelAll_and (largeEvenLabelAll_d4ThreeFixCyclic ht h4)
      (ggL45_labelAll_isSimpleGroup ht h4))
  rintro R _ I F ⟨hfix, hsimple⟩
  intro K _ _ θ hK E hE h27 hEI f hf3 hfI hfE
  exact ggL45HFour_d4_three_H4Mod hfix hsimple K θ hK E hE h27 hEI f hf3 hfI hfE

end CFSG.StandardType
