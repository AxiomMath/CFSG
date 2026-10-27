module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPinTwoB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_pCoreOf_of_swap_19 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {A : Subgroup G} (hAT : A ≤ D.T)
    (hq : 2 ≤ E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)))
    (hAL : ¬ A ≤ normalizer (L : Set G)) :
    ∃ d ∈ A, d ∈ normalizer (L : Set G) ∧ d ∉ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  classical
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hmapmul : ∀ (a b : G) (H : Subgroup G), H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b H
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hswap : ∀ w ∈ A, w ∉ normalizer (L : Set G) →
      L.map (MulAut.conj w).toMonoidHom = K ∧ K.map (MulAut.conj w).toMonoidHom = L := by
    intro w hw hwL
    rcases permutesPair_of_ctx19_one h w (hAM hw) with ⟨h1, -⟩ | h2
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hwL
    · exact h2
  obtain ⟨s, hsA, hsL⟩ := SetLike.not_le_iff_exists.mp hAL
  by_contra hcon
  have hcon' : ∀ d ∈ A, d ∈ normalizer (L : Set G) → d ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
    fun d hd hdL => by_contra fun hdQ => hcon ⟨d, hd, hdL, hdQ⟩
  have hcov : ∀ w ∈ A, w ∈ A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T) ∨
      (s⁻¹)⁻¹ * w ∈ A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro w hw
    by_cases hwL : w ∈ normalizer (L : Set G)
    · exact Or.inl ⟨hw, hcon' w hw hwL⟩
    · right
      rw [inv_inv]
      have heq : L.map (MulAut.conj (s * w)).toMonoidHom = L := by
        rw [hmapmul, (hswap w hw hwL).1, (hswap s hsA hsL).2]
      exact ⟨A.mul_mem hsA hw, hcon' _ (A.mul_mem hsA hw)
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)⟩
  have hle := CFSG.GroupTheory.mQuot_le_one_of_coset_cover
    (D.sylowM.isPGroup.to_le hAT) inf_le_left hcov
  omega

theorem mem_pCoreOf_of_rhoL_eq_one_of_swap_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {s d : G} (hsT : s ∈ D.T)
    (hsL : s ∉ normalizer (L : Set G)) (hdT : d ∈ D.T) (hdNL : d ∈ normalizer (L : Set G))
    (hdNK : d ∈ normalizer (K : Set G)) (hsd : ⁅s, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T))
    (hd1 : UC6S846.rhoL L ⟨d, hdNL⟩ = 1 ∨ UC6S846.rhoL K ⟨d, hdNK⟩ = 1) :
    d ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  classical
  have hsM : s ∈ D.M := D.sylowM.le hsT
  have hmapmul : ∀ (a b : G) (H : Subgroup G), H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b H
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hsw : L.map (MulAut.conj s).toMonoidHom = K ∧ K.map (MulAut.conj s).toMonoidHom = L := by
    rcases permutesPair_of_ctx19_one h s hsM with ⟨h1, -⟩ | h2
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hsL
    · exact h2
  have hsX : s ∈ L ⊔ K ⊔ D.T := Subgroup.mem_sup_right hsT
  have hXQ : L ⊔ K ⊔ D.T ≤ normalizer (pCoreOf 2 (L ⊔ K ⊔ D.T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ K ⊔ D.T)
  have hqQ : s⁻¹ * d * s * d⁻¹ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    have h2 := (Subgroup.mem_normalizer_iff.mp (hXQ ((L ⊔ K ⊔ D.T).inv_mem hsX)) _).mp
      ((pCoreOf 2 (L ⊔ K ⊔ D.T)).inv_mem hsd)
    convert h2 using 1
    rw [commutatorElement_def]
    group
  have htrans : ∀ Y Y' : Subgroup G, Y ≤ L ⊔ K ⊔ D.T →
      Y.map (MulAut.conj s).toMonoidHom = Y' → ∀ (hY : d ∈ normalizer (Y : Set G))
      (hY' : d ∈ normalizer (Y' : Set G)), UC6S846.rhoL Y ⟨d, hY⟩ = 1 →
      UC6S846.rhoL Y' ⟨d, hY'⟩ = 1 := by
    intro Y Y' hYX hYY' hY hY' hρ
    have hdiY : Y.map (MulAut.conj d⁻¹).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hY)
    have hdY' : Y'.map (MulAut.conj d).toMonoidHom = Y' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hY'
    have hsY' : Y'.map (MulAut.conj s⁻¹).toMonoidHom = Y := by
      rw [← hYY', ← hmapmul, inv_mul_cancel]
      ext x
      simp
    have hqN : s⁻¹ * d * s * d⁻¹ ∈ normalizer (Y : Set G) := by
      have heq : Y.map (MulAut.conj (s⁻¹ * d * s * d⁻¹)).toMonoidHom = Y := by
        rw [hmapmul, hdiY, hmapmul, hYY', hmapmul, hdY', hsY']
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    apply MulEquiv.ext
    intro zbar
    obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y') zbar
    rw [MulAut.one_apply]
    refine (UC6S846.rhoL_fix_iff Y' ⟨d, hY'⟩ z').2 ?_
    show d * (z' : G) * d⁻¹ * (z' : G)⁻¹ ∈ pCoreOf 2 Y'
    have hz'Y : (z' : G) ∈ Y.map (MulAut.conj s).toMonoidHom := hYY'.symm ▸ z'.2
    obtain ⟨z, hzY, hzz⟩ := Subgroup.mem_map.mp hz'Y
    have hz' : (z' : G) = s * z * s⁻¹ := by rw [← hzz]; simp [MulAut.conj_apply]
    have ho : d * z * d⁻¹ * z⁻¹ ∈ pCoreOf 2 Y :=
      (UC6S846.rhoL_fix_iff Y ⟨d, hY⟩ ⟨z, hzY⟩).1 (by rw [hρ]; rfl)
    have hqz : (s⁻¹ * d * s * d⁻¹) * z * (s⁻¹ * d * s * d⁻¹)⁻¹ * z⁻¹ ∈ pCoreOf 2 Y :=
      (UC6S846.rhoL_fix_iff Y ⟨_, hqN⟩ ⟨z, hzY⟩).1
        (by rw [UC6S846.rhoL_eq_one_of_mem_pCoreOf hYX hqN hqQ]; rfl)
    have hqo : (s⁻¹ * d * s * d⁻¹) * (d * z * d⁻¹ * z⁻¹) * (s⁻¹ * d * s * d⁻¹)⁻¹ ∈
        pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hqN) _).mp ho
    have hw := (pCoreOf 2 Y).mul_mem hqo hqz
    have hw' : s * ((s⁻¹ * d * s * d⁻¹) * (d * z * d⁻¹ * z⁻¹) * (s⁻¹ * d * s * d⁻¹)⁻¹ *
        ((s⁻¹ * d * s * d⁻¹) * z * (s⁻¹ * d * s * d⁻¹)⁻¹ * z⁻¹)) * s⁻¹ ∈ pCoreOf 2 Y' := by
      rw [← hYY', CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj s) Y]
      exact ⟨_, hw, by simp [MulAut.conj_apply]⟩
    rw [hz']
    convert hw' using 1
    group
  have hρL : UC6S846.rhoL L ⟨d, hdNL⟩ = 1 := by
    rcases hd1 with h1 | h1
    · exact h1
    · exact htrans K L (le_sup_right.trans le_sup_left) hsw.2 hdNK hdNL h1
  have hρK : UC6S846.rhoL K ⟨d, hdNK⟩ = 1 := by
    rcases hd1 with h1 | h1
    · exact htrans L K (le_sup_left.trans le_sup_left) hsw.1 hdNL hdNK h1
    · exact h1
  exact mem_pCoreOf_LKT_of_rhoL_eq_one_19 h hdT hdNL hdNK hρL hρK

theorem pin_two_swap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) = 2)
    (hAL : ¬ A ≤ normalizer (L : Set G)) : False := by
  classical
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hLn : ¬ (L.subgroupOf D.M).Normal := fun hLN =>
    hAL (hAM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN))
  obtain ⟨s, hsA, hsL⟩ := SetLike.not_le_iff_exists.mp hAL
  obtain ⟨d, hdA, hdNL, hdQ⟩ :=
    exists_mem_normalizer_not_mem_pCoreOf_of_swap_19 h hAT (le_of_eq hq.symm) hAL
  have hdNK : d ∈ normalizer (K : Set G) := mem_normalizer_right_19 h (hAM hdA) hdNL h.hne.symm
  have hsd : ⁅s, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hAc s hsA d hdA)]
    exact Subgroup.one_mem _
  have hdL : UC6S846.rhoL L ⟨d, hdNL⟩ ≠ 1 := fun h1 =>
    hdQ (mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h (hAT hsA) hsL (hAT hdA) hdNL hdNK hsd
      (Or.inl h1))
  have hdK : UC6S846.rhoL K ⟨d, hdNK⟩ ≠ 1 := fun h1 =>
    hdQ (mem_pCoreOf_of_rhoL_eq_one_of_swap_19 h (hAT hsA) hsL (hAT hdA) hdNL hdNK hsd
      (Or.inr h1))
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  let X : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 X
  have hXle : X ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hQH : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hHQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hTsyl : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : Q ≤ D.T := CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right
    D.sylowM.isPGroup hTsyl.2.2
  have hAH : A ≤ X := fun a ha => Subgroup.mem_sup_right (hAT ha)
  have hC2 : E3.cClos V₀ 2 D.T ≤ X :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have hAQ : ¬ A ≤ Q := fun hle => hdQ (hle hdA)
  have hAMO : ¬ A ≤ pCoreOf 2 D.M := fun hle =>
    hdQ (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXle ⟨hAH hdA, hle hdA⟩)
  have hP5 : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q → 5 ∣ Nat.card N := by
    intro N hNX hXN hNQ
    have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
    exact h5L.trans (Subgroup.card_dvd_of_le
      (le_sup_left.trans (sup_le_of_normal_LKT_19 h hLn hNX hXN hNQ)))
  have hqle : E3.mQuot A (A ⊓ Q) ≤ 2 := le_of_eq hq
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hXle hQH hHQ hQT hAH hAgamma
      hAMO hAQ hqle hC2 hP5
  exact false_of_twoSided_mem_19 h hm hAgamma hLn hZ hdA hdNL hdNK hdL hdK

theorem pin_two_19 (D : Data G) (hSg : UC6S846.SigmaStd D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hm : 4 < mSub V₀) (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M)
    {A J : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M) (hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2)
    (hres : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
      ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  by_cases hns : J ≠ L ⊔ K ∨ A ≤ normalizer (L : Set G)
  · exact pin_two_of_not_swap_19 D hSg h hm hN2 hA hJ hJA hq hres hns
  · rw [not_or, not_not] at hns
    obtain ⟨rfl, hAL⟩ := hns
    exact (pin_two_swap_19 D hSg h hm hN2 hA hq hAL).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
