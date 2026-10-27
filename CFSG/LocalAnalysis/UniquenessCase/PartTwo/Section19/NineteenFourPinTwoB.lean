module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPinTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_rhoL_eq_one_of_isU3_19 {L : Subgroup G} (hU3 : IsU3 (Bar2 L) 2)
    {y : G} (hyL : y ∈ L) (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hρ : UC6S846.rhoL L ⟨y, hyN⟩ = 1) : y ∈ pCoreOf 2 L := by
  exact
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.inf_centralizerBar_le_pCore_of_center_bar2
      (P := L) (center_bar2_of_isU3_two hU3)
    ⟨CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.mem_centralizerBar_iff.mpr
      ⟨hyL, fun z hz =>
        (UC6S846.rhoL_fix_iff L ⟨y, hyN⟩ ⟨z, hz⟩).1 (by rw [hρ]; rfl)⟩, hyL⟩

private abbrev GoodFiveConj (e c : Equiv.Perm (Fin 5)) : Prop :=
  c ^ 5 = 1 ∧ c ≠ 1 ∧ c.sign = 1 ∧
    e * (c⁻¹ * e * c) * e⁻¹ ≠ c⁻¹ * e * c ∧
    e * (c * e * c⁻¹) * e⁻¹ ≠ c * e * c⁻¹

private abbrev HasGoodFiveConj (e : Equiv.Perm (Fin 5)) : Prop :=
  e ^ 2 = 1 → e ≠ 1 → ∃ c : Equiv.Perm (Fin 5), GoodFiveConj e c

private instance (e : Equiv.Perm (Fin 5)) : Decidable (HasGoodFiveConj e) := by
  unfold HasGoodFiveConj GoodFiveConj
  infer_instance

private lemma perm5_exists_five_conj_invol_19 : ∀ e : Equiv.Perm (Fin 5), HasGoodFiveConj e := by
  decide +kernel

theorem exists_good_conj_perm5_19 (E : Subgroup (Equiv.Perm (Fin 5)))
    (hE : IsElemAbelian 2 E) (hcard : Nat.card E ≤ 4) :
    ∃ c ∈ alternatingGroup (Fin 5),
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E c : Set (Equiv.Perm (Fin 5))) → e = 1) ∧
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E c⁻¹ : Set (Equiv.Perm (Fin 5))) → e = 1) := by
  classical
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hE)
  have hn2 : n ≤ 2 := by
    have h1 : 2 ^ n ≤ 4 := hn ▸ hcard
    by_contra h
    have h3 : 3 ≤ n := by omega
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases n
  · have hbot : E = ⊥ :=
      Subgroup.eq_bot_of_card_eq E (by rw [hn]; norm_num)
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · intro e he _
      rw [hbot] at he
      simpa using he
    · intro e he _
      rw [hbot] at he
      simpa using he
  · have hcard2 : Nat.card E = 2 := by
      rw [hn]
      norm_num
    have : Nontrivial ↥E :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard2]; norm_num)
    obtain ⟨e₀, he₀⟩ := exists_ne (1 : ↥E)
    set e : Equiv.Perm (Fin 5) := (e₀ : Equiv.Perm (Fin 5)) with he
    have heE : e ∈ E := e₀.2
    have he1 : e ≠ 1 := fun h => he₀ (Subtype.ext h)
    have he2 : e ^ 2 = 1 := hE.2 e heE
    have he2' : e * e = 1 := by simpa [pow_two] using he2
    have hEeq : E = Subgroup.zpowers e := by
      have h2 : Nat.card ↥(Subgroup.zpowers e) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime he2 he1]
      refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers e) (K := E)
        (Subgroup.zpowers_le.mpr heE) ?_).symm
      rw [hcard2, h2]
    obtain ⟨c, hc5, hc1, hcsign, hineq1, hineq2⟩ :=
      perm5_exists_five_conj_invol_19 e he2 he1
    have hcalt : c ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.mpr hcsign
    have key : ∀ c' : Equiv.Perm (Fin 5), c' ^ 5 = 1 → c' ≠ 1 →
        e * (c'⁻¹ * e * c') * e⁻¹ ≠ c'⁻¹ * e * c' →
        ∀ f ∈ E, f ∈ Subgroup.normalizer
          (conjSubgroup E c' : Set (Equiv.Perm (Fin 5))) → f = 1 := by
      intro c' hc'5 hc'1 hineq f hfE hfN
      by_cases hf1 : f = 1
      · exact hf1
      · have hfz : f ∈ Subgroup.zpowers e := by rw [← hEeq]; exact hfE
        have hpair : (Subgroup.zpowers e : Set (Equiv.Perm (Fin 5))) = {1, e} :=
          CFSG.GroupTheory.coe_zpowers_eq_pair he2' he1
        change f ∈ (Subgroup.zpowers e : Set (Equiv.Perm (Fin 5))) at hfz
        rw [hpair] at hfz
        rcases hfz with hfz | hfz
        · exact absurd hfz hf1
        · subst hfz
          have he₁2 : (c'⁻¹ * e * c') * (c'⁻¹ * e * c') = 1 := by
            have hconj : c'⁻¹ * e * c' = (MulAut.conj c'⁻¹) e := by
              rw [MulAut.conj_apply]
              simp
            rw [hconj, ← pow_two, ← map_pow, he2, map_one]
          have he₁1 : c'⁻¹ * e * c' ≠ 1 := by
            intro h
            apply he1
            calc e = c' * (c'⁻¹ * e * c') * c'⁻¹ := by group
              _ = 1 := by rw [h]; group
          have hconjE : conjSubgroup E c' = Subgroup.zpowers (c'⁻¹ * e * c') := by
            rw [hEeq, conjSubgroup]
            change (Subgroup.zpowers e).map (MulAut.conj c'⁻¹).toMonoidHom = _
            rw [MonoidHom.map_zpowers]
            congr 1
          have hmem : e * (c'⁻¹ * e * c') * e⁻¹ ∈ Subgroup.zpowers (c'⁻¹ * e * c') := by
            rw [← hconjE]
            exact (Subgroup.mem_normalizer_iff.mp hfN (c'⁻¹ * e * c')).mp
              (by rw [hconjE]; exact Subgroup.mem_zpowers _)
          have hpair₁ : (Subgroup.zpowers (c'⁻¹ * e * c') :
              Set (Equiv.Perm (Fin 5))) = {1, c'⁻¹ * e * c'} :=
            CFSG.GroupTheory.coe_zpowers_eq_pair he₁2 he₁1
          change e * (c'⁻¹ * e * c') * e⁻¹ ∈
            (Subgroup.zpowers (c'⁻¹ * e * c') : Set (Equiv.Perm (Fin 5))) at hmem
          rw [hpair₁] at hmem
          rcases hmem with hmem | hmem
          · exfalso
            apply he₁1
            calc c'⁻¹ * e * c' = e⁻¹ * (e * (c'⁻¹ * e * c') * e⁻¹) * e := by group
              _ = 1 := by rw [hmem]; group
          · exact absurd hmem hineq
    refine ⟨c, hcalt, key c hc5 hc1 hineq1, key c⁻¹ ?_ ?_ ?_⟩
    · rw [inv_pow, hc5, inv_one]
    · intro h
      exact hc1 (by simpa using congrArg Inv.inv h)
    · simpa using hineq2
  · exact perm5_klein_conj_normalizer E hE (by rw [hn]; norm_num)

theorem rhoL_eq_one_of_normalizes_conj_19 {F A : Subgroup G}
    (hAF : A ≤ Subgroup.normalizer (F : Set G))
    (E : Subgroup (MulAut (Bar2 F)))
    (hE : E = (A.subgroupOf (Subgroup.normalizer (F : Set G))).map (UC6S846.rhoL F))
    {x y : G} (hxN : x ∈ Subgroup.normalizer (F : Set G))
    (hyN : y ∈ Subgroup.normalizer (F : Set G))
    (hρxy : UC6S846.rhoL F ⟨x, hxN⟩ = UC6S846.rhoL F ⟨y, hyN⟩)
    (hgood : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (UC6S846.rhoL F ⟨x, hxN⟩) : Set (MulAut (Bar2 F))) → e = 1)
    {a : G} (haA : a ∈ A)
    (ha : a ∈ Subgroup.normalizer (conjSubgroup A y : Set G)) :
    UC6S846.rhoL F ⟨a, hAF haA⟩ = 1 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (F : Set G)
  let φN : ↥N →* MulAut (Bar2 F) := UC6S846.rhoL F
  have hxN' : x ∈ N := hxN
  have hyN' : y ∈ N := hyN
  have haN : a ∈ N := hAF haA
  have hAyN : conjSubgroup A y ≤ N := by
    intro z hz
    have hzA : y * z * y⁻¹ ∈ A := mem_conjSubgroup_iff.mp hz
    have hzN : y * z * y⁻¹ ∈ N := hAF hzA
    have hzeq : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [hzeq]
    exact N.mul_mem (N.mul_mem (N.inv_mem hyN') hzN) hyN'
  have haNorm : (⟨a, haN⟩ : ↥N) ∈ Subgroup.normalizer
      ((conjSubgroup A y).subgroupOf N : Set ↥N) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hAyN]
    exact Subgroup.mem_subgroupOf.mpr ha
  have hYeq : (conjSubgroup A y).subgroupOf N =
      conjSubgroup (A.subgroupOf N) (⟨y, hyN'⟩ : ↥N) :=
    subgroupOf_conjSubgroup_hom hyN' hAF
  rw [hYeq] at haNorm
  have hconj0 : conjSubgroup (conjSubgroup (A.subgroupOf N) ⟨y, hyN'⟩) ⟨a, haN⟩ =
      conjSubgroup (A.subgroupOf N) ⟨y, hyN'⟩ :=
    conjSubgroup_eq_iff_mem_normalizer.mpr haNorm
  have hmap0 : (conjSubgroup (A.subgroupOf N) ⟨y, hyN'⟩).map φN =
      conjSubgroup E (φN ⟨y, hyN'⟩) := by
    have h := Eq.symm <| map_conjSubgroup_hom φN (A.subgroupOf N) (⟨y, hyN'⟩ : ↥N)
    rwa [show (A.subgroupOf N).map φN = E from hE.symm] at h
  have hmap1 : (conjSubgroup (conjSubgroup (A.subgroupOf N) ⟨y, hyN'⟩)
      ⟨a, haN⟩).map φN =
      conjSubgroup (conjSubgroup E (φN ⟨y, hyN'⟩)) (φN ⟨a, haN⟩) := by
    have h := Eq.symm <| map_conjSubgroup_hom φN
      (conjSubgroup (A.subgroupOf N) ⟨y, hyN'⟩) ⟨a, haN⟩
    rwa [hmap0] at h
  have hconjE : conjSubgroup (conjSubgroup E (φN ⟨y, hyN'⟩)) (φN ⟨a, haN⟩) =
      conjSubgroup E (φN ⟨y, hyN'⟩) := by
    rw [← hmap1, ← hmap0, hconj0]
  have hmemE : φN ⟨a, haN⟩ ∈ E := by
    rw [hE]
    exact Subgroup.mem_map_of_mem φN (Subgroup.mem_subgroupOf.mpr haA)
  have hcoe : φN ⟨x, hxN'⟩ = φN ⟨y, hyN'⟩ := hρxy
  have hnormE : φN ⟨a, haN⟩ ∈ Subgroup.normalizer
      (conjSubgroup E (φN ⟨x, hxN'⟩) : Set (MulAut (Bar2 F))) := by
    rw [hcoe]
    exact conjSubgroup_eq_iff_mem_normalizer.mp hconjE
  exact hgood _ hmemE hnormE

theorem exists_rhoL_good_19 {F A : Subgroup G} (hFalt : IsAlt (Bar2 F) 5)
    (hAF : A ≤ Subgroup.normalizer (F : Set G)) (hAel : IsElemAbelian 2 A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ x : ↥F,
      (∀ (y : G) (hyN : y ∈ Subgroup.normalizer (F : Set G)),
        UC6S846.rhoL F ⟨y, hyN⟩ =
          UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩ →
        ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (conjSubgroup A y : Set G) →
          UC6S846.rhoL F ⟨(a : G), hAF a.2⟩ = 1) ∧
      (∀ (y : G) (hyN : y ∈ Subgroup.normalizer (F : Set G)),
        UC6S846.rhoL F ⟨y, hyN⟩ =
          (UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩)⁻¹ →
        ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (conjSubgroup A y : Set G) →
          UC6S846.rhoL F ⟨(a : G), hAF a.2⟩ = 1) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (F : Set G)
  let φN : ↥N →* MulAut (Bar2 F) := UC6S846.rhoL F
  let E : Subgroup (MulAut (Bar2 F)) := (A.subgroupOf N).map φN
  have hE : E = (A.subgroupOf N).map φN := rfl
  have hEel : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff.mpr (fun x y => ?_), ?_⟩
    · obtain ⟨a, haA, ha⟩ := x.2
      obtain ⟨b, hbA, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (Bar2 F)) * (y : MulAut (Bar2 F)) =
        (y : MulAut (Bar2 F)) * (x : MulAut (Bar2 F))
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg φN (Subtype.ext (hAc a.1 (Subgroup.mem_subgroupOf.mp haA)
        b.1 (Subgroup.mem_subgroupOf.mp hbA)))
    · rintro x ⟨a, haA, ha⟩
      rw [← ha, ← map_pow,
        show (a : ↥N) ^ 2 = 1 from Subtype.ext
          (hAel.2 a.1 (Subgroup.mem_subgroupOf.mp haA))]
      exact map_one φN
  obtain ⟨e5⟩ := hFalt
  let ee : MulAut (Bar2 F) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm
  let Ep : Subgroup (Equiv.Perm (Fin 5)) := E.map ee.toMonoidHom
  have hEpel : IsElemAbelian 2 Ep := CFSG.SectionRank.isElemAbelian_map hEel ee.toMonoidHom
  have hEple : Nat.card Ep ≤ 4 :=
    CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm hEpel
  have hEcard : Nat.card E ≤ 4 := by
    have h := Subgroup.card_map_of_injective (f := ee.toMonoidHom) (K := E) ee.injective
    rw [← h]
    exact hEple
  obtain ⟨c, hcalt, hcgood, hcgoodinv⟩ := exists_good_conj_perm5_19 Ep hEpel hEple
  obtain ⟨x, hx⟩ := exists_rhoL_eq_19 e5 ⟨c, hcalt⟩
  have hx' : ee (φN ⟨(x : G), Subgroup.le_normalizer x.2⟩) = c := hx
  have transfer : ∀ (y : ↥F) (d : Equiv.Perm (Fin 5)),
      ee (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩) = d →
      (∀ e ∈ Ep, e ∈ Subgroup.normalizer
        (conjSubgroup Ep d : Set (Equiv.Perm (Fin 5))) → e = 1) →
      ∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩) :
          Set (MulAut (Bar2 F))) → e = 1 := by
    intro y d hyd hdgood e heE heN
    have hmemEp : ee e ∈ Ep := Subgroup.mem_map_of_mem ee.toMonoidHom heE
    have hmap : (conjSubgroup E (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩)).map
        ee.toMonoidHom = conjSubgroup Ep d := by
      have h := Eq.symm <| map_conjSubgroup_hom ee.toMonoidHom E
        (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩)
      rw [show E.map ee.toMonoidHom = Ep from rfl] at h
      simpa [hyd] using h
    have h1 : ee e ∈ Subgroup.normalizer
        (conjSubgroup Ep d : Set (Equiv.Perm (Fin 5))) := by
      have h2 := Subgroup.mem_map_of_mem ee.toMonoidHom heN
      rwa [Subgroup.map_normalizer_eq_of_bijective
        (H := conjSubgroup E (φN ⟨(y : G), Subgroup.le_normalizer y.2⟩))
        (f := ee.toMonoidHom) ee.bijective, hmap] at h2
    exact ee.injective (by simpa using hdgood _ hmemEp h1)
  have hgoodx : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (φN ⟨(x : G), Subgroup.le_normalizer x.2⟩) :
        Set (MulAut (Bar2 F))) → e = 1 :=
    transfer x c hx' hcgood
  have hxinv : ee (φN ⟨(((x⁻¹ : ↥F) : G)), Subgroup.le_normalizer (x⁻¹).2⟩) = c⁻¹ := by
    have h1 : (⟨(((x⁻¹ : ↥F) : G)), Subgroup.le_normalizer (x⁻¹).2⟩ : ↥N) =
        (⟨(x : G), Subgroup.le_normalizer x.2⟩ : ↥N)⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv, map_inv, hx']
  have hgoodxinv := transfer x⁻¹ c⁻¹ hxinv hcgoodinv
  have hxinvρ : UC6S846.rhoL F
      ⟨(((x⁻¹ : ↥F) : G)), Subgroup.le_normalizer (x⁻¹).2⟩ =
      (UC6S846.rhoL F ⟨(x : G), Subgroup.le_normalizer x.2⟩)⁻¹ := by
    have h1 : (⟨(((x⁻¹ : ↥F) : G)), Subgroup.le_normalizer (x⁻¹).2⟩ : ↥N) =
        (⟨(x : G), Subgroup.le_normalizer x.2⟩ : ↥N)⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv]
  refine ⟨x, ?_, ?_⟩
  · intro y hyN hyρ a ha
    exact rhoL_eq_one_of_normalizes_conj_19 hAF E hE (Subgroup.le_normalizer x.2) hyN
      hyρ.symm hgoodx a.2 ha
  · intro y hyN hyρ a ha
    exact rhoL_eq_one_of_normalizes_conj_19 hAF E hE
      (Subgroup.le_normalizer (x⁻¹).2) hyN (hxinvρ.trans hyρ.symm) hgoodxinv a.2 ha

theorem pin_two_of_sup_of_normalizes_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A J : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M) (hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2)
    (hres : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
      ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G))
    (hJLK : J = L ⊔ K) (hAL : A ≤ normalizer (L : Set G)) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  subst hJLK
  have hLn : ¬ (L.subgroupOf D.M).Normal := by
    rcases hJ with ⟨h1, -⟩ | ⟨-, hLn⟩
    · rcases h1 with heq | heq
      · exact absurd heq (sup_ne_left_right_19 h).1
      · exact absurd heq (sup_ne_left_right_19 h).2
    · exact hLn
  have hLalt : IsAlt (Bar2 L) 5 := isAlt_bar2_left_19 h hLn
  have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
    calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm
  have hLK' : L ≤ Subgroup.normalizer (K : Set G) :=
    calC_le_normalizer_of_ne h.hK h.hyp.hL.1 h.hne
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    mem_normalizer_right_19 h (D.sylowM.le (hAT ha)) (hAL ha) h.hne.symm
  let H : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  have hqH : E3.mQuot A (A ⊓ Q) = 2 := hq
  have hXM : L ⊔ K ≤ D.M := by
    rw [← h.hLK]
    exact S17.Lp_le_M D 5
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA
    have hJN : L ⊔ K ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅L ⊔ K, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hJN
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hAQ : ¬ A ≤ Q := by
    intro hle
    have h0 : E3.mQuot A (A ⊓ Q) = 0 := by rw [inf_eq_left.mpr hle, E3.mQuot_self]
    omega
  have hHM : H ≤ D.M := sup_le hXM D.sylowM.le
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : Q ≤ D.T := CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right
    D.sylowM.isPGroup hTsyl.2.2
  have hAH : A ≤ H := hAT.trans le_sup_right
  have hC2 : E3.cClos V₀ 2 D.T ≤ H :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hP5 : ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q → 5 ∣ Nat.card N := by
    intro N hNH hHN hNQ
    have hLKle : L ⊔ K ≤ N := sup_le_of_normal_LKT_19 h hLn hNH hHN hNQ
    have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
    exact h5L.trans (Subgroup.card_dvd_of_le (le_sup_left.trans hLKle))
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hHM hQH hHQ hQT hAH hAgamma hAM
      hAQ (le_of_eq hqH) hC2 hP5
  obtain ⟨xL, hgoodL⟩ := exists_rhoL_good_19 hLalt hAL hAel hAc
  obtain ⟨xK, hgoodK⟩ := exists_rhoL_good_19 h.hKshape hAK hAel hAc
  set x : G := (xL : G) * (xK : G) with hxdef
  have hxLK : x ∈ L ⊔ K :=
    (L ⊔ K).mul_mem (Subgroup.mem_sup_left xL.2) (Subgroup.mem_sup_right xK.2)
  have hxH : x ∈ H := Subgroup.mem_sup_left hxLK
  have hxNL : x ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer xL.2) (hKL xK.2)
  have hxNK : x ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem (hLK' xL.2) (Subgroup.le_normalizer xK.2)
  have hρLx : UC6S846.rhoL L ⟨x, hxNL⟩ =
      UC6S846.rhoL L ⟨(xL : G), Subgroup.le_normalizer xL.2⟩ := by
    have hsplit : (⟨x, hxNL⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨(xL : G), Subgroup.le_normalizer xL.2⟩ : ↥(Subgroup.normalizer (L : Set G))) *
          (⟨(xK : G), hKL xK.2⟩ : ↥(Subgroup.normalizer (L : Set G))) :=
      Subtype.ext (by simp [hxdef])
    rw [hsplit, map_mul,
      UC22.R8107Out.rhoL_eq_one_of_mem h.hyp.hL.1 h.hK h.hne.symm xK.2 (hKL xK.2), mul_one]
  have hρKx : UC6S846.rhoL K ⟨x, hxNK⟩ =
      UC6S846.rhoL K ⟨(xK : G), Subgroup.le_normalizer xK.2⟩ := by
    have hsplit : (⟨x, hxNK⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(xL : G), hLK' xL.2⟩ : ↥(Subgroup.normalizer (K : Set G))) *
          (⟨(xK : G), Subgroup.le_normalizer xK.2⟩ : ↥(Subgroup.normalizer (K : Set G))) :=
      Subtype.ext (by simp [hxdef])
    rw [hsplit, map_mul,
      UC22.R8107Out.rhoL_eq_one_of_mem h.hK h.hyp.hL.1 h.hne xL.2 (hLK' xL.2), one_mul]
  have hxQ : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x : Set G) → a ∈ Q := by
    intro a haA haN
    have hρLa : UC6S846.rhoL L ⟨a, hAL haA⟩ = 1 :=
      hgoodL.1 x hxNL hρLx ⟨a, haA⟩ haN
    have hρKa : UC6S846.rhoL K ⟨a, hAK haA⟩ = 1 :=
      hgoodK.1 x hxNK hρKx ⟨a, haA⟩ haN
    exact mem_pCoreOf_LKT_of_rhoL_eq_one_19 h (hAT haA) (hAL haA) (hAK haA)
      hρLa hρKa
  have hxinvH : x⁻¹ ∈ H := H.inv_mem hxH
  have hxinvNL : x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).inv_mem hxNL
  have hxinvNK : x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).inv_mem hxNK
  have hρLxinv : UC6S846.rhoL L ⟨x⁻¹, hxinvNL⟩ =
      (UC6S846.rhoL L ⟨(xL : G), Subgroup.le_normalizer xL.2⟩)⁻¹ := by
    have h1 : (⟨x⁻¹, hxinvNL⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨x, hxNL⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv, hρLx]
  have hρKxinv : UC6S846.rhoL K ⟨x⁻¹, hxinvNK⟩ =
      (UC6S846.rhoL K ⟨(xK : G), Subgroup.le_normalizer xK.2⟩)⁻¹ := by
    have h1 : (⟨x⁻¹, hxinvNK⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨x, hxNK⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := Subtype.ext (by simp)
    rw [h1, map_inv, hρKx]
  have hxQinv : ∀ a ∈ A,
      a ∈ Subgroup.normalizer (conjSubgroup A x⁻¹ : Set G) → a ∈ Q := by
    intro a haA haN
    have hρLa : UC6S846.rhoL L ⟨a, hAL haA⟩ = 1 :=
      hgoodL.2 x⁻¹ hxinvNL hρLxinv ⟨a, haA⟩ haN
    have hρKa : UC6S846.rhoL K ⟨a, hAK haA⟩ = 1 :=
      hgoodK.2 x⁻¹ hxinvNK hρKxinv ⟨a, haA⟩ haN
    exact mem_pCoreOf_LKT_of_rhoL_eq_one_19 h (hAT haA) (hAL haA) (hAK haA)
      hρLa hρKa
  exact exists_inCalO_two_not_one_19 h.hyp.hyp125 hm hQH hHQ hAH hAgamma hqH hZ hxH hxQ hxQinv

theorem exists_good_conj_of_inner_U3_19 {L : Subgroup G} (hU3 : IsU3 (Bar2 L) 2)
    (E : Subgroup (MulAut (Bar2 L))) (hEel : IsElemAbelian 2 E) (hEcard : Nat.card E = 4)
    (hEinn : E ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range) :
    ∃ x : ↥L,
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (UC6S846.rhoL L ⟨(x : G), Subgroup.le_normalizer x.2⟩) :
          Set (MulAut (Bar2 L))) → e = 1) ∧
      (∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E ((UC6S846.rhoL L ⟨(x : G), Subgroup.le_normalizer x.2⟩))⁻¹ :
          Set (MulAut (Bar2 L))) → e = 1) := by
  classical
  let cj : Bar2 L →* MulAut (Bar2 L) := MulAut.conj
  have hcj_inj : Function.Injective cj :=
    CFSG.mulAutConj_injective_of_center_eq_bot (center_bar2_of_isU3_two hU3)
  let E' : Subgroup (Bar2 L) := E.comap cj
  have hE'map : E'.map cj = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hEinn]
  have hE'card : Nat.card E' = 4 := by
    have h := Subgroup.card_map_of_injective (f := cj) (K := E') hcj_inj
    rw [hE'map] at h
    rw [← h, hEcard]
  have hE'el : IsElemAbelian 2 E' := by
    refine ⟨isMulCommutative_iff.mpr (fun x y => ?_), fun x hx => ?_⟩
    · apply Subtype.ext
      apply hcj_inj
      have hxE : cj (x : Bar2 L) ∈ E := hE'map ▸ Subgroup.mem_map_of_mem cj x.2
      have hyE : cj (y : Bar2 L) ∈ E := hE'map ▸ Subgroup.mem_map_of_mem cj y.2
      change cj ((x : Bar2 L) * (y : Bar2 L)) = cj ((y : Bar2 L) * (x : Bar2 L))
      rw [map_mul, map_mul]
      have : IsMulCommutative E := hEel.1
      exact congrArg Subtype.val (mul_comm' (⟨cj (x : Bar2 L), hxE⟩ : E)
        ⟨cj (y : Bar2 L), hyE⟩)
    · apply hcj_inj
      rw [map_pow, map_one]
      exact hEel.2 (cj x) (hE'map ▸ Subgroup.mem_map_of_mem cj hx)
  obtain ⟨xbar, hxbar, hxbarinv⟩ :=
    k_U34KleinNormalizer_holds (X := Bar2 L) hU3 E' hE'el hE'card
  have hmapE : (conjSubgroup E' xbar).map cj = conjSubgroup E (cj xbar) := by
    have h := Eq.symm <| map_conjSubgroup_hom cj E' xbar
    rwa [hE'map] at h
  have key : ∀ z : Bar2 L, (∀ e ∈ E', e ∈ Subgroup.normalizer
        (conjSubgroup E' z : Set (Bar2 L)) → e = 1) →
      ∀ e ∈ E, e ∈ Subgroup.normalizer
        (conjSubgroup E (cj z) : Set (MulAut (Bar2 L))) → e = 1 := by
    intro z hzgood e heE heN
    have heE' : e ∈ E'.map cj := hE'map ▸ heE
    obtain ⟨e', he', rfl⟩ := heE'
    have hmapEz : (conjSubgroup E' z).map cj = conjSubgroup E (cj z) := by
      have h := Eq.symm <| map_conjSubgroup_hom cj E' z
      rwa [hE'map] at h
    have he'z : e' ∈ Subgroup.normalizer (conjSubgroup E' z : Set (Bar2 L)) := by
      rw [Subgroup.mem_normalizer_iff] at heN ⊢
      intro w
      constructor
      · intro hw
        have hwc : cj w ∈ conjSubgroup E (cj z) := by
          rw [← hmapEz]
          exact Subgroup.mem_map_of_mem cj hw
        have h1 := (heN (cj w)).mp hwc
        rw [← hmapEz] at h1
        obtain ⟨w', hw', hw''⟩ := h1
        have h2 : cj (e' * w * e'⁻¹) = cj w' := by
          rw [hw'']
          simp only [map_mul, map_inv]
        rw [hcj_inj h2]
        exact hw'
      · intro hw
        have hwc : cj (e' * w * e'⁻¹) ∈ conjSubgroup E (cj z) := by
          rw [← hmapEz]
          exact Subgroup.mem_map_of_mem cj hw
        have h1 : cj (e' * w * e'⁻¹) = cj e' * cj w * (cj e')⁻¹ := by
          simp only [map_mul, map_inv]
        rw [h1] at hwc
        have h2 := (heN (cj w)).mpr hwc
        rw [← hmapEz] at h2
        obtain ⟨w', hw', hw''⟩ := h2
        have h3 : cj w = cj w' := by
          rw [hw'']
        rw [hcj_inj h3]
        exact hw'
    have h1 := hzgood e' he' he'z
    rw [h1]
    exact map_one cj
  have hgoodx : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (cj xbar) : Set (MulAut (Bar2 L))) → e = 1 :=
    key xbar hxbar
  have hgoodxinv : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (cj xbar)⁻¹ : Set (MulAut (Bar2 L))) → e = 1 := by
    have h1 : (cj xbar)⁻¹ = cj xbar⁻¹ := by
      change (MulAut.conj xbar)⁻¹ = MulAut.conj xbar⁻¹
      rw [← map_inv]
    rw [h1]
    exact key xbar⁻¹ (by simpa using hxbarinv)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) xbar
  have hρx : UC6S846.rhoL L ⟨(x : G), Subgroup.le_normalizer x.2⟩ = cj xbar := by
    rw [UC6S846.rhoL_inner L (x : G) x.2, ← hx, QuotientGroup.coe_mk']
  refine ⟨x, ?_, ?_⟩
  · intro e heE heN
    exact hgoodx e heE (by rwa [hρx] at heN)
  · intro e heE heN
    exact hgoodxinv e heE (by rwa [hρx] at heN)

theorem pin_two_of_isU3_19 (D : Data G) (hSg : UC6S846.SigmaStd D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hm : 4 < mSub V₀) (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M)
    {A J : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M) (hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2)
    (hres : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
      ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G))
    (hJL : J = L) (hU3 : IsU3 (Bar2 L) 2) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  classical
  have hJA' : ¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M := by rwa [hJL] at hJA
  have hq' : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) = 2 := by rwa [hJL] at hq
  have hres' : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T) ∨
      ¬ E1.tauOf (L ⊔ D.T) D.T A ≤ normalizer (L : Set G) := by rwa [hJL] at hres
  have hJ' : JChoice19 D L K L := hJL ▸ hJ
  have hLN : (L.subgroupOf D.M).Normal := by
    rcases hJ' with ⟨-, hLN⟩ | ⟨hJeq, -⟩
    · exact hLN
    · exact absurd hJeq.symm (sup_ne_left_right_19 h).1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hTN : D.T ≤ Subgroup.normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
  have hin : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T) := by
    rcases hres' with hin | hswap
    · exact hin
    · exact absurd ((E1.tauOf_le (L ⊔ D.T) D.T A).trans hTN) hswap
  let H : Subgroup G := L ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  have hqH : E3.mQuot A (A ⊓ Q) = 2 := hq'
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := hA
  obtain ⟨hAT, gA, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (E3.isElemAbelian_conjSubgroup h.hyp.hyp125.pairFacts.elemAbelian₀ gA)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hAM : ¬ A ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA'
    have hLN' : L ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
      hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    have hcalc : ⁅L, pCoreOf 2 D.M⁆ ≤ pCoreOf 2 D.M := by
      rw [Subgroup.commutator_comm]
      exact CFSG.GroupTheory.FT63ChII.commutator_le_of_le_normalizer hLN'
    exact (Subgroup.commutator_mono le_rfl hle).trans hcalc
  have hAQ : ¬ A ≤ Q := by
    intro hle
    have h0 : E3.mQuot A (A ⊓ Q) = 0 := by rw [inf_eq_left.mpr hle, E3.mQuot_self]
    omega
  have hHM : H ≤ D.M := sup_le hLM D.sylowM.le
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : Q ≤ D.T := CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right
    D.sylowM.isPGroup hTsyl.2.2
  have hAH : A ≤ H := hAT.trans le_sup_right
  have hC2 : E3.cClos V₀ 2 D.T ≤ H :=
    fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hP5 : ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) →
      ¬ N ≤ Q → 5 ∣ Nat.card N := by
    intro N hNH hHN hNQ
    have hJs : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape (Or.inr hU3)
    have hLNle : L ≤ N := le_of_normal_of_isSimple_19 hJs h.hyp.hL.1.2.1
      D.sylowM.isPGroup hTN
      (fun y hy hyN hρ => mem_pCoreOf_of_rhoL_eq_one_of_isU3_19 hU3 hy hyN hρ)
      hNH hHN hNQ
    exact ((h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2).trans (Subgroup.card_dvd_of_le hLNle)
  have hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ :=
    inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hHM hQH hHQ hQT hAH hAgamma hAM
      hAQ (le_of_eq hqH) hC2 hP5
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let φN : ↥N →* MulAut (Bar2 L) := UC6S846.rhoL L
  let E : Subgroup (MulAut (Bar2 L)) := (A.subgroupOf N).map φN
  have hE : E = (A.subgroupOf N).map φN := rfl
  have hAN : A ≤ N := fun a ha => hTN (hAT ha)
  have hHN : H ≤ N := sup_le Subgroup.le_normalizer hTN
  have hEel : IsElemAbelian 2 E := by
    refine ⟨isMulCommutative_iff.mpr (fun x y => ?_), fun x hx => ?_⟩
    · obtain ⟨a, haA, ha⟩ := x.2
      obtain ⟨b, hbA, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (Bar2 L)) * (y : MulAut (Bar2 L)) =
        (y : MulAut (Bar2 L)) * (x : MulAut (Bar2 L))
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg φN (Subtype.ext (hAc a.1 (Subgroup.mem_subgroupOf.mp haA)
        b.1 (Subgroup.mem_subgroupOf.mp hbA)))
    · obtain ⟨a, haA, ha⟩ := hx
      rw [show x = φN a from ha.symm, ← map_pow,
        show a ^ 2 = 1 from Subtype.ext (hAel.2 a.1 (Subgroup.mem_subgroupOf.mp haA))]
      exact map_one φN
  have hkerQ : ∀ a : G, (haH : a ∈ H) → φN ⟨a, hHN haH⟩ = 1 → a ∈ Q := by
    intro a haH h1
    exact UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one (X := L) (T := D.T) D.sylowM.isPGroup hTN
      (fun y hy hyN hρ => mem_pCoreOf_of_rhoL_eq_one_of_isU3_19 hU3 hy hyN hρ)
      haH (hHN haH) (by simpa using h1)
  let f : ↥A →* MulAut (Bar2 L) := φN.comp (Subgroup.inclusion hAN)
  have hErange : E = f.range := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨(a : G), hAN a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hfker : f.ker = (A ⊓ Q).subgroupOf A := by
    ext a
    constructor
    · intro ha
      have h1 : f a = 1 := MonoidHom.mem_ker.mp ha
      change φN ⟨(a : G), hAN a.2⟩ = 1 at h1
      exact Subgroup.mem_subgroupOf.mpr ⟨a.2, hkerQ (a : G) (hAH a.2) h1⟩
    · intro ha
      have haQ : (a : G) ∈ Q := (Subgroup.mem_subgroupOf.mp ha).2
      have h1 : φN ⟨(a : G), hAN a.2⟩ = 1 :=
        UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := L ⊔ D.T) le_sup_left
          (hHN (hAH a.2)) haQ
      refine MonoidHom.mem_ker.mpr ?_
      change φN ⟨(a : G), hAN a.2⟩ = 1
      exact h1
  have hEcard : Nat.card E = 4 := by
    rw [hErange]
    have h1 : Nat.card f.range = f.ker.relIndex ⊤ := by
      rw [Subgroup.relIndex_ker (⊤ : Subgroup ↥A) f, Subgroup.map_top]
    rw [h1, hfker]
    have h2 : ((A ⊓ Q).subgroupOf A).relIndex (⊤ : Subgroup ↥A) = (A ⊓ Q).relIndex A := by
      rw [← Subgroup.relIndex_subgroupOf (H := A ⊓ Q) (K := A) (L := A) le_rfl,
        Subgroup.subgroupOf_self]
    rw [h2]
    have hA2 : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
    rw [E3.relIndex_eq_two_pow hA2 (A ⊓ Q), hqH]
    norm_num
  have hEinn : E ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    intro e he
    obtain ⟨a, haA, rfl⟩ := he
    have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
    have hQn : Q ≤ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨hxT, hxL⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQT hq)) x).mp hxT,
            (Subgroup.mem_normalizer_iff.mp (hTN (hQT hq)) x).mp hxL⟩
      · intro hx
        obtain ⟨hxT, hxL⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQT hq)) x).mpr hxT,
            (Subgroup.mem_normalizer_iff.mp (hTN (hQT hq)) x).mpr hxL⟩
    have hamul : (a : G) ∈ (D.T ⊓ L) ⊔ Q := hin haA'
    change (a : G) ∈ (((D.T ⊓ L) ⊔ Q : Subgroup G) : Set G) at hamul
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (D.T ⊓ L) Q hQn] at hamul
    obtain ⟨u, huTL, q, hqQ, huq⟩ := hamul
    have hqN : q ∈ N := hHN (hQH hqQ)
    have hsplit : a = (⟨u, Subgroup.le_normalizer huTL.2⟩ : ↥N) * ⟨q, hqN⟩ := by
      apply Subtype.ext
      exact huq.symm
    refine ⟨QuotientGroup.mk (⟨u, huTL.2⟩ : ↥L), ?_⟩
    rw [hsplit, map_mul, UC6S846.rhoL_inner L u huTL.2,
      UC6S846.rhoL_eq_one_of_mem_pCoreOf (X := L) (H := L ⊔ D.T) le_sup_left hqN hqQ,
      mul_one]
  obtain ⟨xL, hgoodx, hgoodxinv⟩ := exists_good_conj_of_inner_U3_19 hU3 E hEel hEcard hEinn
  set x : G := (xL : G) with hxdef
  have hxH : x ∈ H := Subgroup.mem_sup_left xL.2
  have hxN : x ∈ N := Subgroup.le_normalizer xL.2
  have hxQ : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x : Set G) → a ∈ Q := by
    intro a haA haN
    have hρa : φN ⟨a, hAN haA⟩ = 1 :=
      rhoL_eq_one_of_normalizes_conj_19 hAN E hE hxN hxN rfl hgoodx haA haN
    exact hkerQ a (hAH haA) (by simpa using hρa)
  have hxinvH : x⁻¹ ∈ H := H.inv_mem hxH
  have hxinvN : x⁻¹ ∈ N := N.inv_mem hxN
  have hgoodxinv' : ∀ e ∈ E, e ∈ Subgroup.normalizer
      (conjSubgroup E (φN ⟨x⁻¹, hxinvN⟩) : Set (MulAut (Bar2 L))) → e = 1 := by
    have h1 : φN ⟨x⁻¹, hxinvN⟩ = (φN ⟨(xL : G), Subgroup.le_normalizer xL.2⟩)⁻¹ := by
      have h2 : (⟨x⁻¹, hxinvN⟩ : ↥N) =
          (⟨(xL : G), Subgroup.le_normalizer xL.2⟩ : ↥N)⁻¹ := Subtype.ext (by simp [hxdef])
      rw [h2, map_inv]
    rw [h1]
    exact hgoodxinv
  have hxQinv : ∀ a ∈ A, a ∈ Subgroup.normalizer (conjSubgroup A x⁻¹ : Set G) → a ∈ Q := by
    intro a haA haN
    have hρa : φN ⟨a, hAN haA⟩ = 1 :=
      rhoL_eq_one_of_normalizes_conj_19 hAN E hE hxinvN hxinvN rfl hgoodxinv' haA haN
    exact hkerQ a (hAH haA) (by simpa using hρa)
  exact exists_inCalO_two_not_one_19 h.hyp.hyp125 hm hQH hHQ hAH hAgamma hqH hZ hxH hxQ hxQinv

theorem pin_two_of_not_swap_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A J : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJA : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M) (hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2)
    (hres : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
      ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G))
    (hns : J ≠ L ⊔ K ∨ A ≤ normalizer (L : Set G)) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  by_cases hJK : J = L ⊔ K
  · have hAL : A ≤ Subgroup.normalizer (L : Set G) := by
      rcases hns with hne | hAL
      · exact absurd hJK hne
      · exact hAL
    exact pin_two_of_sup_of_normalizes_19 D hSg h hm hN2 hA hJ hJA hq hres hJK hAL
  · have hJ' : (J = L ∨ J = K) ∧ (L.subgroupOf D.M).Normal := by
      rcases hJ with h1 | ⟨h2, -⟩
      · exact h1
      · exact absurd h2 hJK
    rcases hJ'.1 with hJL | hJK'
    · rcases h.shape with hL2 | hU3
      · exact pin_two_of_isAlt_19 D hSg h hm hN2 hA hJ'
          (hJL.symm ▸ S17.isAlt_five_of_isL2_two hL2) hJA hq
      · exact pin_two_of_isU3_19 D hSg h hm hN2 hA hJ hJA hq hres hJL hU3
    · exact pin_two_of_isAlt_19 D hSg h hm hN2 hA hJ'
        (hJK'.symm ▸ h.hKshape) hJA hq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
