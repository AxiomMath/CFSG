module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Cover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2SpBlock

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private lemma l02qq2spr_conj_injective_of_center_eq_bot {G : Type} [Group G]
    (h : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hh := congrArg (fun f : MulAut G => f y) hx
    rw [MulAut.conj_apply, MulAut.one_apply] at hh
    have hxy : x * y = y * x := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hh]
    exact hxy.symm
  rw [h, Subgroup.mem_bot] at hxcenter
  exact hxcenter

theorem q2RToral_sp {d p : ℕ} (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {A : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K d)))} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K d))
      (LargeEvenGSpSet K d))
    {u : MulAut (LargeEvenProj (LargeEvenSpGroup K d))} (hu : u ∈ A) (hou : orderOf u = p)
    {J : Subgroup (LargeEvenProj (LargeEvenSpGroup K d))}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K'))
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J,
      (j' : LargeEvenProj (LargeEvenSpGroup K d)) = a (j : LargeEvenProj (LargeEvenSpGroup K d)) →
        α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2LinearLift M := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let φ : ↥(LargeEvenSpGroup K d) →* MulAut (LargeEvenProj (LargeEvenSpGroup K d)) :=
    (MulAut.conj :
        LargeEvenProj (LargeEvenSpGroup K d) →* MulAut (LargeEvenProj (LargeEvenSpGroup K d))).comp
      (LargeEvenProjMk (LargeEvenSpGroup K d))
  have hinner : ∀ a ∈ A, ∃ s : ↥(LargeEvenSpGroup K d), a = φ s := by
    intro a ha
    obtain ⟨r, hr⟩ := TableBSymp.sp_I_subset_inn (K := K) (m := d) (hAI a ha)
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d ⊕ Fin d) K).subgroupOf (LargeEvenSpGroup K d)) r
    refine ⟨s, ?_⟩
    change a = MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K d) s)
    rw [hs]
    exact hr.symm
  have hπinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K d)) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := d) (K := K)).1
  have hcenterR : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K d)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot (K := K) (m := d)
  have hconjinj : Function.Injective
      (MulAut.conj :
        LargeEvenProj (LargeEvenSpGroup K d) →* MulAut (LargeEvenProj (LargeEvenSpGroup K d))) :=
    l02qq2spr_conj_injective_of_center_eq_bot hcenterR
  have hφinj : Function.Injective φ := hconjinj.comp hπinj
  obtain ⟨b, hb_eq⟩ := hinner u hu
  have hu_ne1 : u ≠ 1 := by
    intro h1
    have h1' : orderOf u = 1 := by rw [h1, orderOf_one]
    rw [hou] at h1'
    exact hp.ne_one h1'
  have hbne : b ≠ 1 := by
    intro h1
    apply hu_ne1
    rw [hb_eq, h1]
    simp
  have hbpow : b ^ p = 1 := by
    apply hφinj
    rw [map_pow, map_one, hb_eq.symm, ← hou]
    exact pow_orderOf_eq_one u
  have hbdvd : orderOf b ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hbpow
  have hborder : orderOf b = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf b) hbdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hbne
    · exact h1
  have hbodd : Odd (orderOf b) := hborder ▸ hp.odd_of_ne_two hp2
  have hJb : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K d) b))) := by
    change CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (φ b))
    rw [← hb_eq]
    exact hJ
  obtain ⟨m, D, iD, iFin, ψ, πblk, hsquare⟩ := q2Sp_block hd b hbodd J hJb θ
  let E : Subgroup ↥(LargeEvenSpGroup K d) := A.comap φ
  haveI hEcomm : IsMulCommutative E := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply hφinj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.is_comm.comm
      (⟨φ (x : ↥(LargeEvenSpGroup K d)), x.2⟩ : ↥A)
      (⟨φ (y : ↥(LargeEvenSpGroup K d)), y.2⟩ : ↥A))
  have hbE : b ∈ E := by
    change φ b ∈ A
    rw [hb_eq.symm]
    exact hu
  have hEle : E ≤ Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using hEcomm.is_comm.comm ⟨s, hs⟩ ⟨b, hbE⟩
  let f : ↥E →* GL (Fin m) D := πblk.comp (Subgroup.inclusion hEle)
  let G : Subgroup (GL (Fin m) D) := f.range
  have hGcomm : IsMulCommutative G := inferInstance
  refine ⟨m, D, iD, iFin, ψ, G, hGcomm, ?_⟩
  intro α hαM
  obtain ⟨a, haA, hrel⟩ := hM α hαM
  obtain ⟨s_a, hsa⟩ := hinner a haA
  have hs_a_E : s_a ∈ E := by
    change φ s_a ∈ A
    rw [← hsa]
    exact haA
  have hs_a_cent : s_a ∈ Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) :=
    hEle hs_a_E
  refine ⟨πblk ⟨s_a, hs_a_cent⟩, ?_, ?_⟩
  · exact MonoidHom.mem_range.mpr ⟨⟨s_a, hs_a_E⟩, rfl⟩
  · ext y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    induction x using QuotientGroup.induction_on with
    | H j =>
      have hcond : ((⟨a (j : LargeEvenProj (LargeEvenSpGroup K d)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSpGroup K d)) j.2⟩ : ↥J) :
          LargeEvenProj (LargeEvenSpGroup K d)) =
          LargeEvenProjMk (LargeEvenSpGroup K d) s_a *
            (j : LargeEvenProj (LargeEvenSpGroup K d)) *
            (LargeEvenProjMk (LargeEvenSpGroup K d) s_a)⁻¹ := by
        have h := congrArg (fun f : MulAut (LargeEvenProj (LargeEvenSpGroup K d)) =>
          f (j : LargeEvenProj (LargeEvenSpGroup K d))) hsa
        simpa [φ, MulAut.conj_apply] using h
      have hS := hsquare ⟨s_a, hs_a_cent⟩ j
        ⟨a (j : LargeEvenProj (LargeEvenSpGroup K d)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSpGroup K d)) j.2⟩ hcond
      have hrelj := hrel j
        ⟨a (j : LargeEvenProj (LargeEvenSpGroup K d)),
          hAJ a haA (j : LargeEvenProj (LargeEvenSpGroup K d)) j.2⟩ rfl
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hrelj]
      exact hS.symm

theorem q2RLevel_symplectic : Q2RLevel .symplectic := by
  intro p d Q lab hΛ hfits
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hp, hp2, hpd, hpQ, ht, hl, hQ⟩ := hfits
  have hl' : d = l := hl.symm
  subst hl'
  rcases ht with ht | ht <;> subst ht
  all_goals
    intro Qc hQc
    dsimp only [LargeEvenRawDatum] at hQc ⊢
    try simp only [↓reduceIte] at hQc ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQc
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro A hAab hAI u hu hou J hJ hAJ Kq iq iFq hKq hne M hM
    haveI : CharP K 2 := charP_two_of_card hK
    haveI : CharP Kq 2 := charP_two_of_card (hKq.trans hQ)
    simp only [LargeEvenInLambda2] at hΛ
    have hd : 3 ≤ d := by
      have h2 : 2 ≤ d := hΛ.2.1
      rcases Nat.lt_or_ge d 3 with hlt | hge
      · exfalso
        have hd2 : d = 2 := by omega
        have hpd2 : p ∣ 2 := by simpa [hd2] using hpd
        have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpd2
        have hp_ge : 2 ≤ p := hp.two_le
        exact hp2 (by omega)
      · exact hge
    obtain ⟨θ⟩ := hne
    exact q2RToral_sp hd hp hp2 hAab hAI hu hou hJ hAJ θ M hM

end CFSG.StandardType
