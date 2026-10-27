module

public import CFSG.RankThree.GF2n.Tim77.Sec44Inner
public import CFSG.RankThree.GF2n.Tim77.Sec43
public import CFSG.RankThree.GF2n.Tim77.AutDich
public import CFSG.RankThree.GF2n.Tim77.Sec31
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

section Abstract

theorem sec44w_not_commute_conj {R : Type} [Group R] {D : Set R}
    (hD : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp D) {a ρ : R} (ha : a ∈ D) (hρ : ρ ∈ D)
    (hnc : ¬ Commute a ρ) : ¬ Commute a (ρ * a * ρ⁻¹) := by
  intro hc
  have haa : a * a = 1 := hD.mul_self_eq_one ha
  have hρρ : ρ * ρ = 1 := hD.mul_self_eq_one hρ
  have hodd' : Odd (orderOf (a * ρ)) := hD.odd_of_not_commute ha hρ hnc
  have hρi : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
  rw [hρi] at hc
  have hvv : (ρ * a * ρ) * (ρ * a * ρ) = 1 := by
    calc (ρ * a * ρ) * (ρ * a * ρ) = ρ * a * (ρ * ρ) * a * ρ := by group
      _ = ρ * (a * a) * ρ := by rw [hρρ, mul_one]; group
      _ = 1 := by rw [haa, mul_one, hρρ]
  have h4 := (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one haa hvv).mp hc
  have h4' : (a * ρ) ^ 4 = 1 := by
    have e1 : a * (ρ * a * ρ) = (a * ρ) ^ 2 := by
      rw [sq]
      group
    rw [e1, ← pow_mul] at h4
    exact h4
  have hdvd : orderOf (a * ρ) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4')
  have h1 : orderOf (a * ρ) = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases i with _ | i
    · simpa using hi
    · rw [hi, pow_succ] at hodd'
      exact absurd hodd' (by simp [Nat.not_odd_iff_even])
  rw [orderOf_eq_one_iff] at h1
  exact hnc (hD.eq_of_mul_eq_one ha h1 ▸ Commute.refl a)

theorem sec44w_mul_inv_mem {W : Type} [Group W] {K : Subgroup W} [K.Normal] {u w : W}
    (h : (QuotientGroup.mk u : W ⧸ K) = QuotientGroup.mk w) : u * w⁻¹ ∈ K := by
  have h1 : u⁻¹ * w ∈ K := QuotientGroup.eq.mp h
  have h2 : u * (u⁻¹ * w)⁻¹ * u⁻¹ ∈ K := ‹K.Normal›.conj_mem _ (K.inv_mem h1) u
  have e : u * (u⁻¹ * w)⁻¹ * u⁻¹ = u * w⁻¹ := by group
  rwa [e] at h2

theorem sec44w_not_solvable_quot {W : Type} [Group W] {K : Subgroup W} [K.Normal]
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hW : ¬ Group.IsSolvable W) :
    ¬ Group.IsSolvable (W ⧸ K) := by
  intro hq
  apply hW
  haveI : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext (hK _ a.2 _ b.2)⟩⟩
  exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem sec44w_dich {R : Type} [Group R] [Finite R] {D : Set R}
    (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup R D)
    (hinj : ∀ d ∈ D, ∀ z ∈ Subgroup.center R, z ≠ 1 → d * z ∉ D)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (R ⧸ Subgroup.center R))
    (hlift : ∀ d ∈ D, ∀ e ∈ D,
      Commute (QuotientGroup.mk' (Subgroup.center R) d)
        (QuotientGroup.mk' (Subgroup.center R) e) → Commute d e)
    (hgen : ∀ ψ : MulAut R, (∀ d ∈ D, ψ d = d) → ψ = 1)
    (φ : MulAut R) (hφφ : φ * φ = 1) (hφD : ∀ d ∈ D, φ d ∈ D) {ā : R} (hā : ā ∈ D)
    (hφā : φ ā = ā) :
    (∃ t ∈ D, φ t = t ∧ ¬ Commute ā t) ∨ (∀ x, φ x = x) ∨
      (∃ c ∈ D, Commute ā c ∧ ∀ x, φ x = c * x * c⁻¹) := by
  have hmap : (Subgroup.center R).map (φ : R →* R) = Subgroup.center R :=
    Subgroup.map_center_eq φ
  let σ : MulAut (R ⧸ Subgroup.center R) :=
    QuotientGroup.congr (Subgroup.center R) (Subgroup.center R) φ hmap
  have hσ : ∀ x : R, σ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := fun x => rfl
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, hσ, hσ, MulAut.one_apply]
    have := congrArg (fun ψ : MulAut R => ψ y) hφφ
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [this]
  have huniq : ∀ d ∈ D, ∀ e ∈ D,
      (QuotientGroup.mk e : R ⧸ Subgroup.center R) = QuotientGroup.mk d → e = d := by
    intro d hd e he hde
    have hz : d⁻¹ * e ∈ Subgroup.center R := QuotientGroup.eq.mp hde.symm
    by_contra hne
    refine hinj d hd (d⁻¹ * e) hz (fun h1 => hne (inv_mul_eq_one.mp h1).symm) ?_
    rw [mul_inv_cancel_left]
    exact he
  have hlift_inv : ∀ τ : R ⧸ Subgroup.center R, τ * τ = 1 → τ ≠ 1 →
      ∃ d ∈ D, (QuotientGroup.mk d : R ⧸ Subgroup.center R) = τ := by
    intro τ hττ hτ1
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective τ
    have hu : u ∉ Subgroup.center R := fun hu => hτ1 ((QuotientGroup.eq_one_iff u).mpr hu)
    have hu2 : u * u ∈ Subgroup.center R := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact hττ
    obtain ⟨d, hd, hdu⟩ := hS.exists_inv_mul_mem_of_isBenderGroup (F := Subgroup.center R)
      le_rfl hB hu hu2
    exact ⟨d, hd, QuotientGroup.eq.mpr hdu⟩
  have hnot : ā ∉ Subgroup.center R :=
    hS.not_mem_of_isBenderGroup (F := Subgroup.center R) le_rfl hB hā
  have hā2 : orderOf (QuotientGroup.mk ā : R ⧸ Subgroup.center R) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hS.oddT.mul_self_eq_one hā, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hnot
  have hfix : σ (QuotientGroup.mk ā) = QuotientGroup.mk ā := by rw [hσ, hφā]
  rcases autDich hB σ hσσ hā2 hfix with ⟨τ, hττ, hτā, hστ⟩ | ⟨t, ht2, hσt, hnc⟩
  · by_cases hτ1 : τ = 1
    · right
      left
      have hall : ∀ d ∈ D, φ d = d := by
        intro d hd
        have h1 := hστ (QuotientGroup.mk d)
        rw [hσ, hτ1] at h1
        simp only [inv_one, one_mul, mul_one] at h1
        exact huniq d hd (φ d) (hφD d hd) h1
      have h1 : φ = 1 := hgen φ hall
      intro x
      rw [h1]
      rfl
    · right
      right
      obtain ⟨c, hc, hcτ⟩ := hlift_inv τ hττ hτ1
      refine ⟨c, hc, hlift ā hā c hc ?_, ?_⟩
      · show QuotientGroup.mk ā * QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk ā
        rw [hcτ]
        exact hτā.symm
      · have hψ : (MulAut.conj c⁻¹ * φ) = 1 := by
          refine hgen _ fun d hd => ?_
          have hmem : (MulAut.conj c⁻¹ * φ) d ∈ D := by
            rw [MulAut.mul_apply, MulAut.conj_apply]
            exact hS.conj_mem _ (hφD d hd)
          refine huniq d hd _ hmem ?_
          rw [MulAut.mul_apply, MulAut.conj_apply]
          have h1 := hστ (QuotientGroup.mk d)
          rw [hσ] at h1
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rw [h1, hcτ]
          group
        intro x
        have := congrArg (fun ψ : MulAut R => ψ x) hψ
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply, inv_inv] at this
        calc φ x = c * (c⁻¹ * φ x * c) * c⁻¹ := by group
          _ = c * x * c⁻¹ := by rw [this]
  · left
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht2, pow_two] at this
      exact this
    obtain ⟨d, hd, hdt⟩ := hlift_inv t htt ht1
    refine ⟨d, hd, ?_, ?_⟩
    · apply huniq d hd (φ d) (hφD d hd)
      rw [← hσ, hdt]
      exact hσt
    · intro hc
      apply hnc
      rw [← hdt]
      exact hc.map (QuotientGroup.mk' (Subgroup.center R))

end Abstract

section Main

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sec44w_conj_ne (h : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hne' : Section3.Abar0 A Abar ≠ conjSubgroup s (Section3.Abar0 A Abar)) :
    conjSubgroup s Abar ≠ Abar := by
  intro heq
  apply hne'
  have hsA : conjSubgroup s A = A := conjSubgroup_eq_self_iff.mpr (sec32a_s_facts h hs).1
  rw [h.abar0_eq, sec41_conj_inf_normalizer, heq, hsA]

theorem sec44w_nonsolv
    (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {b x₀ : G}
    (hsc : Sec3SChoiceAt A Abar S₀ B b s) (hx₀ : x₀ ∈ Section3.Abar0 A Abar) (hx₀1 : x₀ ≠ 1)
    (hsx : s ∈ Subgroup.closure {x₀, b}) (hs4 : orderOf s = 4)
    (hne : conjSubgroup s Abar ≠ Abar) (hsolv : ¬ Group.IsSolvable ↥(Section3.Y A Abar s)) :
    False := by
  have hs : Section3.IsSChoice A Abar S₀ B s := ⟨b, hsc⟩
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨-, hcomm2⟩ := sec32b_of tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨hcls, hRI, hne4, hcent⟩ := sec41_of tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  haveI hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr fun y hy => hYN y hy
  have hdat := sa_sec42Data h hs hcomm2 hRI hne4 hcls hcent
  have hns : ¬ Group.IsSolvable (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) :=
    sec44w_not_solvable_quot (fun x hx y hy => Subtype.ext (hNc _ (Subgroup.mem_subgroupOf.mp hx) _
      (Subgroup.mem_subgroupOf.mp hy))) hsolv
  obtain ⟨-, hB⟩ := qp_main hdat hns
  obtain ⟨φ, hφφ, hφ⟩ := sa_phi h hs
  obtain ⟨a, haA, haN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.setup.ne)
  have haY : a ∈ Section3.Y A Abar s := sa_A_le_Y haA
  have haD : a ∈ Section4.D A Abar s :=
    sec41_mem_D.mpr ⟨1, Subgroup.one_mem _, a, haA, haN, by simp⟩
  let a' : ↥(Section3.Y A Abar s) := ⟨a, haY⟩
  have habar : (QuotientGroup.mk a' : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈
      QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} := ⟨a', haD, rfl⟩
  have hφa : φ (QuotientGroup.mk a') = QuotientGroup.mk a' := by
    have hy : s * (a' : G) * s⁻¹ ∈ Section3.Y A Abar s := sa_conj_mem_Y h hs haY
    have e : (⟨s * (a' : G) * s⁻¹, hy⟩ : ↥(Section3.Y A Abar s)) = a' :=
      Subtype.ext (by show s * a * s⁻¹ = a; rw [sa_comm_A h hs haA]; group)
    rw [hφ a' hy, e]
  have hφD : ∀ d ∈ QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
      {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s},
      φ d ∈ QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
      {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} := by
    rintro _ ⟨t, ht, rfl⟩
    have hsy := sa_conj_mem_Y h hs t.2
    exact ⟨⟨s * t * s⁻¹, hsy⟩, sa_conj_D h hs ht, (hφ t hsy).symm⟩
  rcases sec44w_dich (qp_setup hdat) (fun d hd z hz hz1 => qp_inj hdat hd hz hz1) hB
      (fun d hd e he hc => qp_commute_lift_Z hdat hd he hc)
      (fun ψ hψ => qp_aut_eq_of_fix hdat ψ hψ) φ hφφ hφD habar hφa with
    ⟨t, htD, hφt, hnc⟩ | hφ1 | ⟨cbar, hcbarD, hcomm, hφc⟩
  ·
    obtain ⟨h₀, hmk, hsh⟩ := sa_lift_fixed h hs φ hφ hφt
    refine sa_field_contra h hs hne (h₀ := (h₀ : G)) h₀.2 hsh ?_
    intro hall
    apply sec44w_not_commute_conj (qp_setup hdat).oddT habar htD hnc
    have hc := hall a haA ((h₀ : G) * a * (h₀ : G)⁻¹) (sec41_mem_conj haA)
    have hc' : a' * (h₀ * a' * h₀⁻¹) = (h₀ * a' * h₀⁻¹) * a' :=
      Subtype.ext (by simpa using hc)
    have := congrArg (QuotientGroup.mk (s := (Section3.N A Abar s).subgroupOf
      (Section3.Y A Abar s))) hc'
    rw [← hmk]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    exact this
  ·
    refine sec44_trivial_contra h hs hne fun w hw => ?_
    have hsw := sa_conj_mem_Y h hs hw
    have h1 := hφ1 (QuotientGroup.mk ⟨w, hw⟩)
    have h2 : (QuotientGroup.mk (⟨s * w * s⁻¹, hsw⟩ : ↥(Section3.Y A Abar s)) :
        ↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk ⟨w, hw⟩ := (hφ ⟨w, hw⟩ hsw).symm.trans h1
    have h3 := Subgroup.mem_subgroupOf.mp (sec44w_mul_inv_mem h2)
    simpa using h3
  ·
    have hcomm' : ∃ c₀ : ↥(Section3.Y A Abar s), (c₀ : G) ∈ Section4.D A Abar s ∧
        QuotientGroup.mk c₀ = cbar ∧ Commute a' c₀ := by
      by_cases he : (QuotientGroup.mk a' : ↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = cbar
      · exact ⟨a', haD, he, Commute.refl a'⟩
      · obtain ⟨c₀, hc₀D, rfl⟩ := hcbarD
        exact ⟨c₀, hc₀D, rfl, qp_commute_lift hdat haD hc₀D he hcomm⟩
    obtain ⟨c₀, hc₀D, hc₀mk, hc₀comm⟩ := hcomm'
    subst hc₀mk
    obtain ⟨y, hy, a'', ha'', ha''0, hcy⟩ := sec41_mem_D.mp hc₀D
    have hcc : (c₀ : G) * c₀ = 1 := sec41_D_sq h.hyp.elemAbelian hc₀D
    have hc : (c₀ : G) ∈ conjSubgroup y A := by
      rw [hcy]
      exact sec41_mem_conj ha''
    have hc0 : (c₀ : G) ∉ conjSubgroup y (Section3.A0 A Abar) := by
      rw [hcy]
      exact sec41_not_mem_conj ha''0
    have hea : (c₀ : G) * a = a * c₀ := by
      have h1 : (a' : G) * c₀ = c₀ * a' := congrArg Subtype.val hc₀comm.eq
      exact h1.symm
    have ha1 : a ≠ 1 := fun h1 => haN (h1 ▸ Subgroup.one_mem _)
    have hCA := sec41_centralizer h hYN hNc hy haA ha1 hc hc0 hea
    refine sec44_inner_contra h hq hsc hx₀ hx₀1 hsx hs4 hne hy hc hc0 hCA fun w hw => ?_
    have hsw := sa_conj_mem_Y h hs hw
    have hcY : (c₀ : G) ∈ Section3.Y A Abar s := c₀.2
    have h2 : (QuotientGroup.mk (⟨s * w * s⁻¹, hsw⟩ : ↥(Section3.Y A Abar s)) :
        ↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk (c₀ * ⟨w, hw⟩ * c₀⁻¹) := by
      have e1 := hφ ⟨w, hw⟩ hsw
      have e2 := hφc (QuotientGroup.mk ⟨w, hw⟩)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact e1.symm.trans e2
    have h4 := Subgroup.mem_subgroupOf.mp (sec44w_mul_inv_mem h2)
    obtain ⟨n₁, hn₁⟩ : ∃ n₁ : G, n₁ = (s * w * s⁻¹) * ((c₀ : G) * w * (c₀ : G)⁻¹)⁻¹ := ⟨_, rfl⟩
    have hn₁N : n₁ ∈ Section3.N A Abar s := by
      rw [hn₁]
      simpa using h4
    have hcc' : (c₀ : G)⁻¹ * (c₀ : G)⁻¹ = 1 := by rw [← mul_inv_rev, hcc, inv_one]
    have e : ((c₀ : G) * s) * w * ((c₀ : G) * s)⁻¹ * w⁻¹ =
        ((c₀ : G) * n₁ * (c₀ : G)⁻¹) * ((c₀ : G) * c₀) * w * ((c₀ : G)⁻¹ * (c₀ : G)⁻¹) * w⁻¹ := by
      rw [hn₁]
      group
    rw [e, hcc, hcc']
    have hcn : (c₀ : G) * n₁ * (c₀ : G)⁻¹ ∈ Section3.N A Abar s :=
      (Subgroup.mem_normalizer_iff.mp (hYN _ hcY) n₁).mp hn₁N
    simpa using hcn

end Main

theorem sec44w_of
    (h43 : Tim77Sec43Statement) : Tim77Sec44Statement := by
  intro G _ _ A Abar S₀ B h hq b hb hb1
  by_contra hcon
  have hno : ∀ x ∈ Section3.Abar0 A Abar, x ≠ 1 → orderOf (x * b) ≠ 2 ∧ orderOf (x * b) ≠ 4 := by
    intro x hx hx1
    by_contra hx'
    apply hcon
    refine ⟨x, hx, hx1, ?_⟩
    by_contra hh
    exact hx' ⟨fun h2 => hh (Or.inl h2), fun h4 => hh (Or.inr h4)⟩
  obtain ⟨x₀, hx₀, hx₀1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot h.setup.Lb_ne_bot
  obtain ⟨s, hsx, hsS, hsC, hne', hcomm, hs4⟩ :=
    tim77Sec31_holds G A Abar S₀ B h x₀ hx₀ hx₀1 b hb hb1 (hno x₀ hx₀ hx₀1).1
      (hno x₀ hx₀ hx₀1).2
  have hsc : Sec3SChoiceAt A Abar S₀ B b s :=
    ⟨hb, hb1, Or.inr ⟨hno, x₀, hx₀, hx₀1, hsx, hsS, hsC, hne', hcomm, hs4⟩⟩
  have hs : Section3.IsSChoice A Abar S₀ B s := ⟨b, hsc⟩
  have hne := sec44w_conj_ne h hs hne'
  by_cases hsolv : Group.IsSolvable ↥(Section3.Y A Abar s)
  · have hY := h43 G A Abar S₀ B s h hs hq hsolv
    have hsb := tim77Sec34_holds G A Abar S₀ B b s h hsc hY
    have hbb : b ^ 2 = 1 := by
      rw [sq]
      exact sa_sq_of_mem_B h hb
    have hdvd := orderOf_dvd_of_pow_eq_one hbb
    rw [← hsb, hs4] at hdvd
    exact absurd hdvd (by norm_num)
  · exact sec44w_nonsolv h hq hsc hx₀ hx₀1 hsx hs4 hne hsolv

theorem sec44w_holds :
    Tim77Sec44Statement :=
  sec44w_of sec43_of

end CFSG.RankThree.GF2n.Tim77
