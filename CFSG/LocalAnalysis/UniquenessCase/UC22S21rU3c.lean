module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rX
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

section Abstract

variable {Q : Type*} [Group Q] [Finite Q]

theorem uc22s21ru3c_isSolvable_centralizer {E : Subgroup Q} (hE : CFSG.perfectResidual Q = E) :
    Group.IsSolvable ↥(Subgroup.centralizer (E : Set Q)) := by
  set S : Subgroup Q := Subgroup.centralizer (E : Set Q) with hS
  have hperf : ⁅CFSG.perfectResidual ↥S, CFSG.perfectResidual ↥S⁆ = CFSG.perfectResidual ↥S :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := ↥S))
  set R : Subgroup Q := (CFSG.perfectResidual ↥S).map S.subtype with hR
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hperf]
  have hRE : R ≤ E := hE ▸ uc22p21c_le_perfectResidual R hRperf
  have hRS : R ≤ S := Subgroup.map_subtype_le _
  have hRbot : R = ⊥ := by
    rw [← hRperf, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hRS hy) x (hRE hx))
  have hbot : CFSG.perfectResidual ↥S = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hRbot
  obtain ⟨n, hn⟩ := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries
    (G := ↥S)
  exact ⟨n, hn.symm.trans hbot⟩

theorem uc22s21ru3c_isSolvable_sup {N T : Subgroup Q} [hN : N.Normal] (hNs : Group.IsSolvable ↥N)
    (hTs : Group.IsSolvable ↥T) : Group.IsSolvable ↥(N ⊔ T) := by
  let L : Subgroup Q := N ⊔ T
  let M : Subgroup L := N.subgroupOf L
  have hM : M.Normal := Subgroup.normal_subgroupOf
  have hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : N ≤ L)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : T →* L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : T ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN.conj_mem' a ha b
  have : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient M

end Abstract

section Bar

variable {G : Type} [Group G] [Finite G]

theorem uc22s21ru3c_isSolvable_barPreimage {M : Subgroup G} {H : Subgroup (Bar2 M)}
    (hH : Group.IsSolvable ↥H) : Group.IsSolvable ↥(barPreimage M H) := by
  classical
  set Hc : Subgroup ↥M := H.comap (uc22p21cPi M) with hHc
  have hle : CFSG.pCore 2 ↥M ≤ Hc := fun x hx => by
    have h1 : uc22p21cPi M x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [hHc, Subgroup.mem_comap, h1]
    exact H.one_mem
  have hK : IsPGroup 2 ↥((CFSG.pCore 2 ↥M).subgroupOf Hc) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  haveI := hK.isNilpotent
  have hHcs : Group.IsSolvable ↥Hc := by
    refine Group.isSolvable_of_ker_le_range ((CFSG.pCore 2 ↥M).subgroupOf Hc).subtype
      ((uc22p21cPi M).subgroupComap H) ?_
    intro x hx
    rw [Subgroup.range_subtype, Subgroup.mem_subgroupOf]
    have h1 : uc22p21cPi M (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact (QuotientGroup.eq_one_iff _).1 h1
  unfold barPreimage
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective Hc M.subtype M.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective Hc M.subtype M.subtype_injective).surjective

theorem uc22s21ru3c_isSolvable_barImage {M T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 ↥T) :
    Group.IsSolvable ↥(barImage M T) := by
  have h1 : IsPGroup 2 ↥(T.subgroupOf M) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have h2 : IsPGroup 2 ↥(barImage M T) := h1.map _
  haveI := h2.isNilpotent
  infer_instance

theorem uc22s21ru3c_exists_Y (D : Data G) (hS : Group.IsSolvable ↥(centE D.M)) :
    ∃ Y : Subgroup G, D.T ≤ Y ∧ Y ≤ D.M ∧ Group.IsSolvable ↥Y ∧
      barPreimage D.M (centE D.M) ≤ Y := by
  have hLn : (CFSG.layer (Bar2 D.M)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hSn : (centE D.M).Normal := uc22p21c_normal_centralizer (CFSG.layer (Bar2 D.M))
  have hTs : Group.IsSolvable ↥(barImage D.M D.T) :=
    uc22s21ru3c_isSolvable_barImage D.sylowM.le D.sylowM.isPGroup
  refine ⟨barPreimage D.M (centE D.M ⊔ barImage D.M D.T), ?_, uc22p21c_barPreimage_le _ _,
    uc22s21ru3c_isSolvable_barPreimage (uc22s21ru3c_isSolvable_sup hS hTs), ?_⟩
  · intro t ht
    refine uc22p21c_mem_barPreimage.2 ⟨D.sylowM.le ht, Subgroup.mem_sup_right ?_⟩
    exact uc22p21c_mem_barImage.2 ⟨⟨t, D.sylowM.le ht⟩, ht, rfl⟩
  · intro x hx
    obtain ⟨hxM, hx'⟩ := uc22p21c_mem_barPreimage.1 hx
    exact uc22p21c_mem_barPreimage.2 ⟨hxM, Subgroup.mem_sup_left hx'⟩

theorem uc22s21ru3c_pRank_eq_zero {Z Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hZY : Z ≤ Y)
    (hnd : ¬ p ∣ Nat.card Y) : CFSG.Open.pRank p Z = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le hp.one_lt fun E hEZ hE => ?_)
  have hEp : IsPGroup p ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  rcases hEp.card_eq_or_dvd with h | h
  · simp [h]
  · exact absurd (h.trans ((Subgroup.card_dvd_of_le hEZ).trans (Subgroup.card_dvd_of_le hZY))) hnd

theorem s21_22U3_of_S22_8 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (hc : Nonempty (Ctx22b D Ch)) (h8 : S22_8 D Ch) (h2118 : S21_18 D Ch) (h211 : S21_1 D Ch) :
    S21_22U3 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ _ hfX hS1 p hp
  obtain ⟨c'⟩ := hc
  have hsp : IsStronglyPEmbedded p D.M := st.sigmaStd.sig1_sp p (h8 h1930 c' ▸ hp)
  have hR : CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M) :=
    (uc22p21c_Hinf_eq_iff D.M).1 (h2118 h1930 c hS1)
  have hSs : Group.IsSolvable ↥(centE D.M) := uc22s21ru3c_isSolvable_centralizer hR
  obtain ⟨Y, hTY, hYM, hYs, hZY⟩ := uc22s21ru3c_exists_Y D hSs
  have hnd : ¬ p ∣ Nat.card Y :=
    uc22s21ru3b_not_dvd_card D Ch st h211 h1930 c hH₁ hH₂
      (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) hp hsp hTY hYM hYs
  exact uc22s21ru3c_pRank_eq_zero (D.sig_prime p hp).1 hZY hnd

end Bar

end CFSG.LocalAnalysis.UniquenessCase.UC22
