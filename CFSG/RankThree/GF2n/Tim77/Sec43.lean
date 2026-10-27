module

public import CFSG.RankThree.GF2n.Tim77.Sec43Basic
public import CFSG.RankThree.GF2n.Tim77.QuotPipe
public import CFSG.RankThree.GF2n.Tim77.Sec32b
public import CFSG.RankThree.GF2n.Tim77.Sec32d

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sa_sec42Data (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hcomm2 : ⁅(pCore 2 ↥(Section3.Y A Abar s)).map (Section3.Y A Abar s).subtype,
      Section3.Y A Abar s⁆ ≤ Section3.N A Abar s)
    (hRI : CFSG.Timmesfeld.IsRootInvolutionSet (Section4.D A Abar s))
    (hne4 : ∀ d ∈ Section4.D A Abar s, ∀ e ∈ Section4.D A Abar s, orderOf (d * e) ≠ 4)
    (hcls : ∃ d₀ ∈ Section4.D A Abar s, ∀ d ∈ Section4.D A Abar s,
      ∃ y ∈ Section3.Y A Abar s, d = y * d₀ * y⁻¹)
    (hcent : ∀ d ∈ Section4.D A Abar s,
      IsElemAbelian 2 (Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * d = d * e})) :
    Sec42Data (↥(Section3.Y A Abar s)) ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))
      {t | (t : G) ∈ Section4.D A Abar s} := by
  obtain ⟨hNY, hNnorm, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  have hDY : Section4.D A Abar s ⊆ Section3.Y A Abar s := sec32d_D_subset_Y
  obtain ⟨d₀, hd₀, hcl⟩ := hcls
  obtain ⟨hRI1, hRI2, -⟩ := hRI
  refine
    { sq := fun n hn =>
        Subtype.ext (by simpa using hNab.2 (n : G) (Subgroup.mem_subgroupOf.mp hn))
      disj := fun t ht htN =>
        sec32d_D_not_mem_N hC hNab hNnorm ht (Subgroup.mem_subgroupOf.mp htN)
      invol := ?_
      ord := ?_
      conjD := ?_
      gen := ?_
      cent := ?_
      single := ?_
      O2 := ?_ }
  · intro t ht
    apply Subtype.ext
    have h2 : (t : G) ^ 2 = 1 := by
      rw [← hRI1 (t : G) ht]
      exact pow_orderOf_eq_one _
    simpa using h2
  · intro t ht t' ht'
    have e : orderOf (t * t') = orderOf ((t : G) * (t' : G)) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    rw [e]
    rcases hRI2 (t : G) ht (t' : G) ht' with h2 | h4 | hodd
    · exact Or.inl (dvd_of_eq h2)
    · exact absurd h4 (hne4 _ ht _ ht')
    · exact Or.inr hodd
  · intro g t ht
    have := sec32d_D_conj g.2 ht
    simpa using this
  · intro y
    have hK := sec32d_gen hC hs hNnorm
    have hle : Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) ≤
        (Subgroup.closure ({t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} ∪
          (((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s) : Subgroup
            ↥(Section3.Y A Abar s)) : Set ↥(Section3.Y A Abar s)))).map
          (Section3.Y A Abar s).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (hg | hg)
      · exact Subgroup.mem_map.mpr ⟨⟨g, hDY hg⟩, Subgroup.subset_closure (Or.inl hg), rfl⟩
      · exact Subgroup.mem_map.mpr ⟨⟨g, hNY hg⟩,
          Subgroup.subset_closure (Or.inr (Subgroup.mem_subgroupOf.mpr hg)), rfl⟩
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp (hle (hK y y.2))
    have hwy' : w = y := Subtype.ext hwy
    rw [← hwy']
    exact hw
  · intro t ht x hx y hy hxt hyt
    have hxt' : (x : G) * (t : G) = (t : G) * (x : G) := congrArg Subtype.val hxt
    have hyt' : (y : G) * (t : G) = (t : G) * (y : G) := congrArg Subtype.val hyt
    have hxS : (x : G) ∈
        Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * (t : G) = (t : G) * e} :=
      Subgroup.subset_closure
        (show (x : G) ∈ Section4.D A Abar s ∧ (x : G) * (t : G) = (t : G) * (x : G) from
          ⟨hx, hxt'⟩)
    have hyS : (y : G) ∈
        Subgroup.closure {e | e ∈ Section4.D A Abar s ∧ e * (t : G) = (t : G) * e} :=
      Subgroup.subset_closure
        (show (y : G) ∈ Section4.D A Abar s ∧ (y : G) * (t : G) = (t : G) * (y : G) from
          ⟨hy, hyt'⟩)
    exact Subtype.ext (sec32d_comm_of_isElemAbelian (hcent (t : G) ht) hxS hyS)
  · refine ⟨⟨d₀, hDY hd₀⟩, hd₀, fun d hd => ?_⟩
    obtain ⟨y, hy, hdy⟩ := hcl d hd
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩
  · intro z hz g
    rw [Subgroup.mem_subgroupOf]
    have hz' : (z : G) ∈ (pCore 2 ↥(Section3.Y A Abar s)).map (Section3.Y A Abar s).subtype :=
      Subgroup.mem_map_of_mem _ hz
    have := hcomm2 (Subgroup.commutator_mem_commutator hz' g.2)
    simpa [commutatorElement_def] using this

end Data

theorem sec43_of :
    Tim77Sec43Statement := by
  intro G _ _ A Abar S₀ B s h hs hq hsolv
  by_cases hne : conjSubgroup s Abar = Abar
  · unfold Section3.Y Section3.X
    rw [hne]
    exact sup_eq_left.mpr le_sup_right
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨-, hcomm2⟩ := sec32b_of tim77Sec32a_holds G A Abar S₀ B s h hs
  obtain ⟨hcls, hRI, hne4, hcent⟩ := sec41_of tim77Sec32a_holds G A Abar S₀ B s h hs
  haveI hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr fun y hy => hYN y hy
  have hdat := sa_sec42Data h hs hcomm2 hRI hne4 hcls hcent
  haveI := hsolv
  have hS := qp_setup hdat
  have hE := qp_hE hdat
  have hO2 := qp_hO2 hdat
  have hinj : ∀ d ∈ QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
      {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s},
      ∀ z ∈ Subgroup.center (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)), z ≠ 1 →
      d * z ∉ QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} :=
    fun d hd z hz hz1 => qp_inj hdat hd hz hz1
  have hsolvR : Group.IsSolvable (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) :=
    solvable_of_surjective (QuotientGroup.mk'_surjective _)
  obtain ⟨φ, hφφ, hφ⟩ := sa_phi h hs
  obtain ⟨a, haA, haN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.setup.ne)
  obtain ⟨β, hβA, hβN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.Lb_le h.setup.Lb_ne)
  have haY : a ∈ Section3.Y A Abar s := sa_A_le_Y haA
  have hβY : β ∈ Section3.Y A Abar s := sa_Abar_le_Y hβA
  have hγY : s * β * s⁻¹ ∈ Section3.Y A Abar s := sa_conj_mem_Y h hs hβY
  have haD : a ∈ Section4.D A Abar s :=
    sec41_mem_D.mpr ⟨1, Subgroup.one_mem _, a, haA, haN, by simp⟩
  have hβD : β ∈ Section4.D A Abar s := by
    obtain ⟨k, hk, hAk, hAk0⟩ := sa_exists_k h
    have hkY : k ∈ Section3.Y A Abar s := by
      have : A ⊔ Abar ≤ Section3.Y A Abar s := by
        unfold Section3.Y
        exact le_sup_left
      exact this hk
    have hβk : β ∈ conjSubgroup k A := by
      rw [← hAk]
      exact hβA
    refine sec41_mem_D.mpr ⟨k, hkY, k⁻¹ * β * k, mem_conjSubgroup.mp hβk, ?_, by group⟩
    intro hmem
    apply hβN
    rw [hAk0]
    exact mem_conjSubgroup.mpr hmem
  have hγD := sa_conj_D h hs hβD
  let a' : ↥(Section3.Y A Abar s) := ⟨a, haY⟩
  let β' : ↥(Section3.Y A Abar s) := ⟨β, hβY⟩
  let γ' : ↥(Section3.Y A Abar s) := ⟨s * β * s⁻¹, hγY⟩
  have hφa : φ (QuotientGroup.mk a') = QuotientGroup.mk a' := by
    have hy : s * (a' : G) * s⁻¹ ∈ Section3.Y A Abar s := sa_conj_mem_Y h hs haY
    have e : (⟨s * (a' : G) * s⁻¹, hy⟩ : ↥(Section3.Y A Abar s)) = a' :=
      Subtype.ext (by show s * a * s⁻¹ = a; rw [sa_comm_A h hs haA]; group)
    rw [hφ a' hy, e]
  have hφβ : φ (QuotientGroup.mk β') = QuotientGroup.mk γ' := hφ β' hγY
  have habar : (QuotientGroup.mk a' : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈
      QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} := ⟨a', haD, rfl⟩
  have hβbar : (QuotientGroup.mk β' : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈
      QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} := ⟨β', hβD, rfl⟩
  have hγbar : (QuotientGroup.mk γ' : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈
      QuotientGroup.mk' ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ''
        {t : ↥(Section3.Y A Abar s) | (t : G) ∈ Section4.D A Abar s} := ⟨γ', hγD, rfl⟩
  have hgen : ∀ ψ : MulAut (↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)),
      ψ (QuotientGroup.mk a') = QuotientGroup.mk a' →
      ψ (QuotientGroup.mk β') = QuotientGroup.mk β' →
      ψ (φ (QuotientGroup.mk β')) = φ (QuotientGroup.mk β') → ψ = 1 := by
    intro ψ h1 h2 h3
    rw [hφβ] at h3
    exact sa_aut_eq_one h hs hq haA haN hβA hβN rfl ψ h1 h2 h3
  rcases sa_dichotomy hS hsolvR hE hO2 hinj φ hφφ habar hβbar (by rw [hφβ]; exact hγbar) hφa
      hgen with hinner | ⟨ρ, hρD, hρfix, hρnc⟩
  ·
    refine sa_Y_eq_X_of_comm h hs haA fun y hy => ?_
    have hsy : s * y * s⁻¹ ∈ Section3.Y A Abar s := sa_conj_mem_Y h hs hy
    have h1 := hinner (QuotientGroup.mk (⟨y, hy⟩ : ↥(Section3.Y A Abar s)))
    rw [hφ ⟨y, hy⟩ hsy] at h1
    have h2 : (QuotientGroup.mk (⟨s * y * s⁻¹, hsy⟩ : ↥(Section3.Y A Abar s)) :
        ↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk (a'⁻¹ * ⟨y, hy⟩ * a') := by
      rw [h1]
      simp
    have h3 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2)
    have hw : (s * y * s⁻¹)⁻¹ * (a⁻¹ * y * a) ∈ Section3.N A Abar s := by simpa using h3
    have e : (a * s) * y * (a * s)⁻¹ * y⁻¹ =
        y * (a * ((s * y * s⁻¹)⁻¹ * (a⁻¹ * y * a))⁻¹ * a⁻¹) * y⁻¹ := by group
    rw [e]
    have h4 := (Subgroup.mem_normalizer_iff.mp (hYN a haY) _).mp
      ((Section3.N A Abar s).inv_mem hw)
    exact (Subgroup.mem_normalizer_iff.mp (hYN y hy) _).mp h4
  ·
    exfalso
    obtain ⟨h₀, hmk, hsh⟩ := sa_lift_fixed h hs φ hφ hρfix
    refine sa_field_contra h hs hne (h₀ := (h₀ : G)) h₀.2 hsh ?_
    intro hall
    apply hρnc
    have hc := hall a haA ((h₀ : G) * a * (h₀ : G)⁻¹) (sec41_mem_conj haA)
    have hc' : a' * (h₀ * a' * h₀⁻¹) = (h₀ * a' * h₀⁻¹) * a' :=
      Subtype.ext (by simpa using hc)
    have := congrArg (QuotientGroup.mk (s := (Section3.N A Abar s).subgroupOf
      (Section3.Y A Abar s))) hc'
    rw [← hmk]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    exact this

end CFSG.RankThree.GF2n.Tim77
