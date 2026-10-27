module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBorel
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc820pq_eq_one_of_odd_of_two {O S : Subgroup Q} (hO : Odd (Nat.card O))
    {x : Q} (hxO : x ∈ O) (hS2 : IsPGroup 2 S) (hxS : x ∈ S) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS2 ⟨x, hxS⟩
  have hk2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk2)
  have hxodd : Odd (orderOf x) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hxO)
  rw [hj] at hxodd
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩)
        (Nat.not_even_iff_odd.mpr hxodd)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem Cfg813.A_le_iSup_astar (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (h : Cfg813 T A B R L₀) :
    A ≤ ⨆ (J : Subgroup Q) (_ : IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q)),
      Astar T J A := by
  classical
  intro a ha
  let idx := {J : Subgroup Q // IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q)}
  haveI : Fintype idx := Fintype.ofFinite idx
  have hdec : ∀ J : idx, ∃ ℓ ∈ Astar T J.1 A,
      ∃ c ∈ T ⊓ centralizer (J.1 : Set Q), a = ℓ * c :=
    fun J => (Cfg813.astar_facts hF0 hF1 hF2 h J.2.1 J.2.2).2.2.2 a ha
  let ell : idx → Q := fun J => Classical.choose (hdec J)
  have ell_mem : ∀ J : idx, ell J ∈ Astar T J.1 A :=
    fun J => (Classical.choose_spec (hdec J)).1
  have ell_spec : ∀ J : idx, ∃ c ∈ T ⊓ centralizer (J.1 : Set Q), a = ell J * c :=
    fun J => (Classical.choose_spec (hdec J)).2
  have hcomm : ((Finset.univ : Finset idx) : Set idx).Pairwise
      (fun A B => Commute (ell A) (ell B)) := by
    intro J _ J' _ hne
    have hsub_ne : J.1 ≠ J'.1 := fun heq => hne (Subtype.ext heq)
    have hle : J.1 ≤ Subgroup.centralizer (J'.1 : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne J.1 J'.1 J.2.1 J'.2.1
          hsub_ne)
    exact (Subgroup.mem_centralizer_iff.mp (hle ((mem_Astar.mp (ell_mem J)).1.2))
      (ell J') ((mem_Astar.mp (ell_mem J')).1.2)).symm
  let e : Q := (Finset.univ : Finset idx).noncommProd ell hcomm
  let F : Subgroup Q := genFittingFitting Q
  let E : Subgroup Q := genFittingLayer Q
  let Fstar : Subgroup Q := genFittingFStar Q
  have hFnormal : F.Normal := by
    change (CFSG.fittingSubgroup Q).Normal
    infer_instance
  haveI : Group.IsNilpotent ↥F := by
    change Group.IsNilpotent ↥(CFSG.fittingSubgroup Q)
    infer_instance
  have hFsub : CFSG.Open.IsSubnormal F ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (Subgroup.Normal.isSubnormal hFnormal)
  have heP : e ∈ ⨆ (J : Subgroup Q)
      (_ : IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q)), Astar T J A := by
    dsimp only [e]
    refine Subgroup.noncommProd_mem (⨆ (J : Subgroup Q)
      (_ : IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q)), Astar T J A) hcomm ?_
    intro J _
    exact Subgroup.mem_iSup_of_mem J.1 (Subgroup.mem_iSup_of_mem J.2 (ell_mem J))
  have heT : e ∈ T := by
    dsimp only [e]
    refine Subgroup.noncommProd_mem T hcomm ?_
    intro J _
    exact (mem_Astar.mp (ell_mem J)).1.1
  have heF : e ∈ Subgroup.centralizer (F : Set Q) := by
    dsimp only [e]
    refine Subgroup.noncommProd_mem (Subgroup.centralizer (F : Set Q)) hcomm ?_
    intro J _
    have hle : J.1 ≤ Subgroup.centralizer (F : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
          J.1 F J.2.1 hFsub)
    exact hle (mem_Astar.mp (ell_mem J)).1.2
  let x : Q := e⁻¹ * a
  have hx_cent : ∀ J : Subgroup Q, IsComponentOf J ⊤ →
      x ∈ Subgroup.centralizer (J : Set Q) := by
    intro J hJ
    by_cases hne : ¬ A ≤ centralizer (J : Set Q)
    · let J' : idx := ⟨J, hJ, hne⟩
      obtain ⟨c, hc, ha_eq⟩ := ell_spec J'
      have hcomm' : (((Finset.univ : Finset idx).erase J') : Set idx).Pairwise
          (fun A B => Commute (ell A) (ell B)) :=
        fun A hA B hB hAB =>
          hcomm (Finset.mem_of_mem_erase hA) (Finset.mem_of_mem_erase hB) hAB
      let e' : Q := ((Finset.univ : Finset idx).erase J').noncommProd ell hcomm'
      have he_eq : ell J' * e' = e := by
        dsimp only [e, e']
        exact Finset.mul_noncommProd_erase (Finset.univ : Finset idx) (Finset.mem_univ J')
          ell hcomm hcomm'
      have he'_cent : e' ∈ Subgroup.centralizer (J : Set Q) := by
        dsimp only [e']
        refine Subgroup.noncommProd_mem (Subgroup.centralizer (J : Set Q)) hcomm' ?_
        intro J'' hJ''
        have hsub_ne : J''.1 ≠ J := by
          intro heq
          exact Finset.ne_of_mem_erase hJ'' (Subtype.ext heq)
        have hle : J''.1 ≤ Subgroup.centralizer (J : Set Q) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (CFSG.ComponentClassification.LocalComponents.commute_of_ne J''.1 J
              J''.2.1 hJ hsub_ne)
        exact hle (mem_Astar.mp (ell_mem J'')).1.2
      have hc_cent : c ∈ Subgroup.centralizer (J : Set Q) := (Subgroup.mem_inf.mp hc).2
      have hx_eq : x = e'⁻¹ * c := by
        dsimp only [x]
        rw [← he_eq, ha_eq]
        group
      rw [hx_eq]
      exact (Subgroup.centralizer (J : Set Q)).mul_mem
        ((Subgroup.centralizer (J : Set Q)).inv_mem he'_cent) hc_cent
    · have hAcent : A ≤ centralizer (J : Set Q) := Classical.not_not.mp hne
      have he_cent : e ∈ Subgroup.centralizer (J : Set Q) := by
        dsimp only [e]
        refine Subgroup.noncommProd_mem (Subgroup.centralizer (J : Set Q)) hcomm ?_
        intro J'' _
        have hsub_ne : J''.1 ≠ J := by
          intro heq
          apply J''.2.2
          rwa [heq]
        have hle : J''.1 ≤ Subgroup.centralizer (J : Set Q) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (CFSG.ComponentClassification.LocalComponents.commute_of_ne J''.1 J
              J''.2.1 hJ hsub_ne)
        exact hle (mem_Astar.mp (ell_mem J'')).1.2
      dsimp only [x]
      exact (Subgroup.centralizer (J : Set Q)).mul_mem
        ((Subgroup.centralizer (J : Set Q)).inv_mem he_cent) (hAcent ha)
  have hxT : x ∈ T := by
    dsimp only [x]
    exact T.mul_mem (T.inv_mem heT) (h.A_le ha)
  have hxF : x ∈ Subgroup.centralizer (F : Set Q) := by
    dsimp only [x]
    refine (Subgroup.centralizer (F : Set Q)).mul_mem
      ((Subgroup.centralizer (F : Set Q)).inv_mem heF) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (h.fitting_commute a ha z hz).symm
  have hFx : F ≤ Subgroup.centralizer ({x} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxF y hy
  have hEx : E ≤ Subgroup.centralizer ({x} : Set Q) := by
    change genFittingLayer Q ≤ Subgroup.centralizer ({x} : Set Q)
    rw [genFittingLayer.eq_sSup]
    refine sSup_le fun J hJ => ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hx_cent J hJ) z hz
  have hxE : x ∈ Subgroup.centralizer (E : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEx hy)
  have hFstara : x ∈ Subgroup.centralizer (Fstar : Set Q) := by
    have hsup : F ⊔ E ≤ Subgroup.centralizer ({x} : Set Q) := sup_le hFx hEx
    have hmem : x ∈ Subgroup.centralizer ((F ⊔ E : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hy)
    exact hmem
  have hxFstar : x ∈ Fstar := by
    have hmem := CFSG.Open.Open.generalized_fitting_self_centralizing Q hFstara
    exact hmem
  let Z : Subgroup Q := (Subgroup.center ↥Fstar).map Fstar.subtype
  have hxZ : x ∈ Z := by
    refine Subgroup.mem_map.mpr ⟨⟨x, hxFstar⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    have hcomm := Subgroup.mem_centralizer_iff.mp hFstara (z : Q) z.2
    exact Subtype.ext hcomm
  have hFstarNormal : Fstar.Normal := by
    have hEnormal : E.Normal := by
      change (CFSG.ComponentClassification.Layer.subgroup Q).Normal
      exact CFSG.ComponentClassification.Layer.normal Q
    haveI : F.Normal := hFnormal
    haveI : E.Normal := hEnormal
    have hsup : (F ⊔ E).Normal := inferInstance
    exact hsup
  have hZnormal : Z.Normal := by
    dsimp [Z]
    haveI : Fstar.Normal := hFstarNormal
    haveI : (Subgroup.center ↥Fstar).Characteristic := Subgroup.centerCharacteristic
    infer_instance
  have hZnil : Group.IsNilpotent ↥Z := by
    dsimp [Z]
    let η := Subgroup.equivMapOfInjective (Subgroup.center ↥Fstar) Fstar.subtype
      Fstar.subtype_injective
    exact Group.nilpotent_of_mulEquiv η
  have hZleF : Z ≤ F := by
    change Z ≤ genFittingFitting Q
    rw [genFittingFitting.eq_sSup]
    exact le_sSup ⟨hZnormal, hZnil⟩
  have hxF_mem : x ∈ F := hZleF hxZ
  have hFodd : Odd (Nat.card F) := h.fitting_odd
  have hx1 : x = 1 := wc820pq_eq_one_of_odd_of_two hFodd hxF_mem h.sylow.isPGroup hxT
  have hae : a = e := by
    have h1 : e⁻¹ * a = 1 := by simpa only [x] using hx1
    calc a = e * (e⁻¹ * a) := by group
      _ = e * 1 := by rw [h1]
      _ = e := mul_one e
  rw [hae]
  exact heP

private theorem wc820pq_conjSubgroup_le_conjClosure {Q : Type} [Group Q] (Z : Subgroup Q)
    (g : Q) : conjSubgroup Z g ≤ conjClosure Z ⊤ := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h := mem_conjClosure (Z := Z) (H := ⊤) (h := g⁻¹) (Subgroup.mem_top g⁻¹) hx
  have hx' : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [inv_inv, hx'] at h

theorem Cfg813.astar_central_of_commute (h : Cfg813 T A B R L₀) {J₀ : Subgroup Q}
    (hJ₀ : IsComponentOf J₀ ⊤)
    (hcomm : ∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure J₀ ⊤, a * t * a⁻¹ * t⁻¹ ∈ (⊥ : Subgroup Q)) :
    ∀ J : Subgroup Q, IsComponentOf J ⊤ → ¬ A ≤ centralizer (J : Set Q) →
      ∀ ℓ ∈ Astar T J A, ∀ s ∈ T ⊓ J, ℓ * s = s * ℓ := by
  intro J hJ _hne ℓ hℓ s hs
  obtain ⟨_, c, hc, hℓcA⟩ := mem_Astar.mp hℓ
  obtain ⟨_, hcC⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hsT, hsJ⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨t, _htT, hJ₀eq⟩ := Cfg813.component_conj h hJ hJ₀
  have hJeq : J = conjSubgroup J₀ t⁻¹ := by
    rw [hJ₀eq, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hsConj : s ∈ conjClosure J₀ ⊤ := by
    rw [hJeq] at hsJ
    exact wc820pq_conjSubgroup_le_conjClosure J₀ t⁻¹ hsJ
  have has : (ℓ * c) * s = s * (ℓ * c) := by
    have h1 : (ℓ * c) * s * (ℓ * c)⁻¹ * s⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hcomm (ℓ * c) hℓcA s ⟨hsT, hsConj⟩)
    have h2 : ((ℓ * c) * s) * (s * (ℓ * c))⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa [mul_assoc] using h1
    exact mul_inv_eq_one.mp h2
  have hcs : c * s = s * c := (Subgroup.mem_centralizer_iff.mp hcC s hsJ).symm
  have h2 : (ℓ * s) * c = (s * ℓ) * c := by
    calc (ℓ * s) * c = ℓ * (s * c) := by group
      _ = ℓ * (c * s) := by rw [hcs]
      _ = (ℓ * c) * s := by group
      _ = s * (ℓ * c) := has
      _ = (s * ℓ) * c := by group
  exact mul_right_cancel h2

private theorem wc820pq_component_iso (h : Cfg813 T A B R L₀) {J J₀ : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hJ₀ : IsComponentOf J₀ ⊤) : Nonempty (↥J ≃* ↥J₀) := by
  obtain ⟨t, _htT, hJ₀eq⟩ := Cfg813.component_conj h hJ hJ₀
  have hmap : J.map (MulAut.conj t⁻¹).toMonoidHom = J₀ := hJ₀eq.symm
  exact ⟨(Subgroup.equivMapOfInjective J (MulAut.conj t⁻¹).toMonoidHom
    (MulAut.conj t⁻¹).injective).trans (MulEquiv.subgroupCongr hmap)⟩

theorem Cfg813.A_le_of_section (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (hF6 : BorelGL32Fact)
    (h : Cfg813 T A B R L₀) (N : Subgroup Q)
    (hsec : ∃ (E : Type) (_ : Group E) (W : Subgroup (MulAut E)) (X : Type) (_ : Group X)
      (ψ : ↥W →* X) (Φ : ↥B →* X), ElemAbOrderEight E ∧ Function.Surjective ψ ∧
        ∀ x : ↥B, Φ x = 1 → (x : Q) ∈ N)
    {J₀ : Subgroup Q} (hJ₀ : IsComponentOf J₀ ⊤)
    (hcase : IsU3 ↥J₀ 2 ∨ (RankTwoShape J₀ ∧
      ∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure J₀ ⊤, a * t * a⁻¹ * t⁻¹ ∈ (⊥ : Subgroup Q))) :
    A ≤ N := by
  classical
  refine le_trans (Cfg813.A_le_iSup_astar hF0 hF1 hF2 h) ?_
  refine iSup_le fun J => iSup_le fun hJcond => ?_
  obtain ⟨hJ, hne⟩ := hJcond
  obtain ⟨hle, -, hcard, -⟩ := h.astar_facts hF0 hF1 hF2 hJ hne
  have hSne : T ⊓ J ≠ ⊥ := by
    intro hbot
    have hlebot : Astar T J A ≤ ⊥ := by
      rw [hbot] at hle
      exact hle
    have h1 : Astar T J A = ⊥ := le_bot_iff.mp hlebot
    have : Nat.card (Astar T J A) = 1 := by rw [h1, Subgroup.card_bot]
    omega
  have hJ5 : OddShape5 J := h.oddShape5 hF0 hJ
  have hsyl : IsSylowIn 2 (T ⊓ J) J := h.isSylowIn_inf_component hJ
  have hBeq : B ⊓ J = J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) :=
    h.inf_component_eq hF0 hF3 hJ hSne
  obtain ⟨E, hEgrp, W, X, hXgrp, ψ, Φ, hE8, hψsurj, hΦkerN⟩ := hsec
  letI : Group E := hEgrp
  letI : Group X := hXgrp
  have hleB : J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ B := by
    rw [← hBeq]
    exact inf_le_left
  let ι : ↥(J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) →* ↥B :=
    Subgroup.inclusion hleB
  let φ : ↥(J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) →* X := Φ.comp ι
  have hF6' : (IsU3 ↥J 2 →
        (T ⊓ J).subgroupOf (J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) ≤ φ.ker) ∧
      (RankTwoShape J →
        ((T ⊓ J) ⊓ centralizer ((T ⊓ J : Subgroup Q) : Set Q)).subgroupOf
          (J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) ≤ φ.ker) :=
    hF6 Q J (T ⊓ J) hJ5 hsyl E hE8 W X ψ hψsurj φ
  have hmemN_of : ∀ s : ↥(J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)),
      s ∈ φ.ker → (s : Q) ∈ N := by
    intro s hs
    have hΦ : Φ (ι s) = 1 := by
      have := MonoidHom.mem_ker.mp hs
      simpa [φ] using this
    have hN := hΦkerN (ι s) hΦ
    simpa [ι] using hN
  have hmemJN : ∀ ℓ ∈ Astar T J A, ℓ ∈ J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) :=
    fun ℓ hℓ => Subgroup.mem_inf.mpr ⟨(hle hℓ).2, Subgroup.le_normalizer (hle hℓ)⟩
  rcases hcase with hU₀ | ⟨hrt₀, hcomm₀⟩
  · have hJ3 : IsU3 ↥J 2 := by
      obtain ⟨eJ⟩ := wc820pq_component_iso h hJ hJ₀
      exact CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm hU₀
    have hU := hF6'.1 hJ3
    intro ℓ hℓ
    let s : ↥(J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) := ⟨ℓ, hmemJN ℓ hℓ⟩
    have hs : s ∈ (T ⊓ J).subgroupOf (J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) :=
      Subgroup.mem_subgroupOf.mpr (hle hℓ)
    exact hmemN_of s (hU hs)
  · have hJrt : RankTwoShape J := by
      obtain ⟨eJ⟩ := wc820pq_component_iso h hJ hJ₀
      rcases hrt₀ with h | h | h
      · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm h)
      · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm h))
      · exact Or.inr (Or.inr ⟨(CFSG.Open.IsQuasisimple.congr eJ).mpr h.1,
          CFSG.Blueprint.LieModel.of_mulEquiv
            (QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥J) eJ.symm
              (Subgroup.map_center_eq eJ.symm)) h.2⟩)
    have hcent := Cfg813.astar_central_of_commute h hJ₀ hcomm₀ J hJ hne
    have hAstCent :
        Astar T J A ≤ (T ⊓ J) ⊓ centralizer ((T ⊓ J : Subgroup Q) : Set Q) := by
      refine le_inf hle ?_
      intro ℓ hℓ
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (hcent ℓ hℓ s hs).symm
    have hC := hF6'.2 hJrt
    intro ℓ hℓ
    let s : ↥(J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) := ⟨ℓ, hmemJN ℓ hℓ⟩
    have hs : s ∈ ((T ⊓ J) ⊓ centralizer ((T ⊓ J : Subgroup Q) : Set Q)).subgroupOf
        (J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q)) :=
      Subgroup.mem_subgroupOf.mpr (by simpa using hAstCent hℓ)
    exact hmemN_of s (hC hs)

end CFSG.LocalAnalysis.WeakClosure81

end
