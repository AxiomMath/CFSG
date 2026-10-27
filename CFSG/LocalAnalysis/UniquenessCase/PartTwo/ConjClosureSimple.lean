module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem image_eq_one_of_commute_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    {X : Subgroup G} (φ : ↥X →* S) (hφ : Function.Surjective φ) {𝒦 : Set (Subgroup G)}
    (hX : X = ⨆ K ∈ 𝒦, K) {L : Subgroup G} (hL : L ∈ 𝒦) (hLperf : ⁅L, L⁆ = L)
    (hcomm : ∀ K ∈ 𝒦, K ≠ L → ∀ a b : ↥X, (a : G) ∈ L → (b : G) ∈ K → φ a * φ b = φ b * φ a)
    (hL1 : ∃ a : ↥X, (a : G) ∈ L ∧ φ a ≠ 1) {K : Subgroup G} (hK : K ∈ 𝒦) (hKL : K ≠ L) :
    ∀ b : ↥X, (b : G) ∈ K → φ b = 1 := by
  have hle : ∀ K' ∈ 𝒦, K' ≤ X := fun K' hK' => hX ▸ le_iSup₂_of_le K' hK' le_rfl
  set A : Subgroup S := (L.subgroupOf X).map φ with hA
  have hnorm : ∀ x : ↥X, φ x ∈ normalizer (A : Set S) := by
    let P : Subgroup G := ((normalizer (A : Set S)).comap φ).map X.subtype
    have hKP : ∀ K' ∈ 𝒦, K' ≤ P := by
      intro K' hK' k hk
      refine ⟨⟨k, hle K' hK' hk⟩, ?_, rfl⟩
      show φ ⟨k, hle K' hK' hk⟩ ∈ normalizer (A : Set S)
      by_cases hK'L : K' = L
      · subst hK'L
        exact Subgroup.le_normalizer ⟨⟨k, hle K' hK' hk⟩, hk, rfl⟩
      · rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · rintro ⟨a, ha, rfl⟩
          rw [hcomm K' hK' hK'L a ⟨k, hle K' hK' hk⟩ ha hk |>.symm, mul_inv_cancel_right]
          exact ⟨a, ha, rfl⟩
        · rintro ⟨a, ha, hs⟩
          have h1 := hcomm K' hK' hK'L a ⟨k, hle K' hK' hk⟩ ha hk
          have : s = φ a := by
            have h2 : s = (φ ⟨k, hle K' hK' hk⟩)⁻¹ * φ a * φ ⟨k, hle K' hK' hk⟩ := by
              rw [hs]
              group
            rw [h2, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact ⟨a, ha, rfl⟩
    have hXP : X ≤ P := by
      have h := iSup₂_le hKP
      rwa [← hX] at h
    intro x
    obtain ⟨y, hy, hyx⟩ := hXP x.2
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hAn : A.Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 fun s _ => ?_)
    obtain ⟨x, rfl⟩ := hφ s
    exact hnorm x
  have hAtop : A = ⊤ := by
    refine (hAn.eq_bot_or_eq_top).resolve_left fun hbot => ?_
    obtain ⟨a, ha, ha1⟩ := hL1
    have : φ a ∈ A := ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hnc : ¬ ∀ s t : S, s * t = t * s := by
    intro hcomm'
    obtain ⟨a, ha, ha1⟩ := hL1
    let Q : Subgroup G := φ.ker.map X.subtype
    have hLQ : ⁅L, L⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⁅(⟨g₁, hle L hL hg₁⟩ : ↥X), ⟨g₂, hle L hL hg₂⟩⁆, ?_, rfl⟩
      show φ ⁅(⟨g₁, hle L hL hg₁⟩ : ↥X), ⟨g₂, hle L hL hg₂⟩⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm' _ _
    rw [hLperf] at hLQ
    obtain ⟨y, hy, hya⟩ := hLQ ha
    have hya' : y = a := Subtype.ext hya
    rw [hya'] at hy
    exact ha1 hy
  have hcenter : center S = ⊥ := by
    refine ((inferInstance : (center S).Normal).eq_bot_or_eq_top).resolve_right
      fun htop => hnc fun s t => ?_
    have hs : s ∈ center S := htop ▸ Subgroup.mem_top s
    exact (Subgroup.mem_center_iff.1 hs t).symm
  intro b hb
  have hbc : φ b ∈ center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hs : s ∈ A := hAtop ▸ Subgroup.mem_top s
    obtain ⟨a, ha, rfl⟩ := hs
    exact hcomm K hK hKL a b ha hb
  rw [hcenter, Subgroup.mem_bot] at hbc
  exact hbc

theorem self_mem_conjSetOf (M L : Subgroup G) : L ∈ conjSetOf M L := by
  refine ⟨1, M.one_mem, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem exists_mem_conjSetOf_ne_of_conjClosure_ne {M L : Subgroup G} (hne : conjClosure M L ≠ L) :
    ∃ K ∈ conjSetOf M L, K ≠ L := by
  by_contra h
  push Not at h
  refine hne (le_antisymm ?_ (TwelveTwentyThree.le_conjClosure M L))
  unfold conjClosure
  exact iSup₂_le fun K hK => by rw [h K hK]

theorem conjSetOf_subset_calC_conjClosure {M L : Subgroup G} (hL : L ∈ calC M) :
    conjClosure M L ≤ M ∧ M ≤ normalizer (conjClosure M L : Set G) ∧
      ∀ K ∈ conjSetOf M L, K ∈ calC (conjClosure M L) := by
  obtain ⟨hXM, hMX, -⟩ :=
    uc22p22u_conjClosure_isProd (M := M) (X := M) (K := L) le_rfl Subgroup.le_normalizer hL
  have hLX : L ≤ conjClosure M L := TwelveTwentyThree.le_conjClosure M L
  have hLc : L ∈ calC (conjClosure M L) := uc22p22u_calC_of_le hL hLX hXM
  refine ⟨hXM, hMX, ?_⟩
  rintro K ⟨g, hg, rfl⟩
  simpa [uniqueFourConj] using uc22p22u_calC_conj hMX hLc (M.inv_mem hg)

theorem conjClosure_eq_self_of_isSimpleGroup_bar2 {M L : Subgroup G} (hL : L ∈ calC M)
    (hs : IsSimpleGroup (Bar2 (conjClosure M L))) : conjClosure M L = L := by
  obtain ⟨-, -, hC⟩ := conjSetOf_subset_calC_conjClosure hL
  set X := conjClosure M L with hXdef
  by_contra hne
  obtain ⟨K, hK, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne
  have hLm := self_mem_conjSetOf M L
  have hcomm : ∀ K' ∈ conjSetOf M L, K' ≠ L → ∀ a b : ↥X, (a : G) ∈ L → (b : G) ∈ K' →
      uc22p21cPi X a * uc22p21cPi X b = uc22p21cPi X b * uc22p21cPi X a := by
    intro K' hK' hK'L a b ha hb
    exact uc22p22l_barImage_commute (hC L hLm) (hC K' hK') (Ne.symm hK'L) _
      (uc22p21c_mem_barImage.2 ⟨a, ha, rfl⟩) _ (uc22p21c_mem_barImage.2 ⟨b, hb, rfl⟩)
  have hne_bot : ∀ K' ∈ conjSetOf M L, barImage X K' ≠ ⊥ := by
    intro K' hK' hbot
    have hcomp := uc22p22l_barImage_isComponent (hC K' hK')
    obtain ⟨a, b, hab⟩ := hcomp.1.2.2
    haveI : Subsingleton ↥(barImage X K') := by
      rw [hbot]
      infer_instance
    exact hab (Subsingleton.elim _ _)
  have hL1 : ∃ a : ↥X, (a : G) ∈ L ∧ uc22p21cPi X a ≠ 1 := by
    by_contra h
    push Not at h
    refine hne_bot L hLm (eq_bot_iff.2 fun q hq => ?_)
    obtain ⟨a, ha, rfl⟩ := uc22p21c_mem_barImage.1 hq
    exact (Subgroup.mem_bot).2 (h a ha)
  have hK1 := image_eq_one_of_commute_of_isSimpleGroup (uc22p21cPi X) (uc22p21c_pi_surjective X) rfl
    hLm (hC L hLm).2.1 hcomm hL1 hK hKL
  refine hne_bot K hK (eq_bot_iff.2 fun q hq => ?_)
  obtain ⟨b, hb, rfl⟩ := uc22p21c_mem_barImage.1 hq
  exact (Subgroup.mem_bot).2 (hK1 b hb)

theorem conjClosure_eq_self_of_isSimpleGroup_barSub {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hs : IsSimpleGroup ↥(barSub V₀ V hV.isElemAbelian (conjClosure D.M L))) :
    conjClosure D.M L = L := by
  obtain ⟨hXM, hMX, hC⟩ := conjSetOf_subset_calC_conjClosure hL
  set X := conjClosure D.M L with hXdef
  set hE := hV.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hXS : X ≤ stabTil V₀ V := hXM.trans hMS
  have hXsub : CFSG.Open.IsSubnormal X D.M := CFSG.Quasithin.A3.subnormal_of_normal hXM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)
  have h2 : barSub V₀ V hE (pCoreOf 2 X) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hE hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  let φ : ↥X →* ↥(barSub V₀ V hE X) :=
    ((actTil V₀ V hE).comp (Subgroup.inclusion hXS)).codRestrict
      (barSub V₀ V hE X) (fun x => actTil_mem_barSub V₀ V hE x.2 (hXS x.2))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, haX, hay⟩ := (mem_barSub V₀ V hE X (y : MulAut (Vtil V₀ V hE))).1 y.2
    refine ⟨⟨a, haX⟩, Subtype.ext ?_⟩
    change actTil V₀ V hE ⟨(a : G), hXS haX⟩ = (y : MulAut (Vtil V₀ V hE))
    rw [← hay]
  have hφ1 : ∀ x : ↥X, φ x = 1 ↔ actTil V₀ V hE ⟨(x : G), hXS x.2⟩ = 1 := by
    intro x
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hconj : ∀ m : ↥D.M, ∀ x : ↥X, ∀ hy : (m : G) * x * (m : G)⁻¹ ∈ stabTil V₀ V,
      actTil V₀ V hE ⟨(m : G) * x * (m : G)⁻¹, hy⟩ =
        actTil V₀ V hE ⟨m, hMS m.2⟩ * actTil V₀ V hE ⟨(x : G), hXS x.2⟩ *
          (actTil V₀ V hE ⟨m, hMS m.2⟩)⁻¹ := by
    intro m x hy
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hLm := self_mem_conjSetOf D.M L
  have hL1 : ∃ a : ↥X, (a : G) ∈ L ∧ φ a ≠ 1 := by
    by_contra h
    push Not at h
    let Q : Subgroup G := ((actTil V₀ V hE).ker).map (stabTil V₀ V).subtype
    have hKQ : ∀ K ∈ conjSetOf D.M L, K ≤ Q := by
      rintro K ⟨g, hg, rfl⟩ k ⟨l, hl, rfl⟩
      have hlX : l ∈ X := TwelveTwentyThree.le_conjClosure D.M L hl
      have hkS : (MulAut.conj g).toMonoidHom l ∈ stabTil V₀ V := hMS (D.M.mul_mem
        (D.M.mul_mem hg (hXM hlX)) (D.M.inv_mem hg))
      refine ⟨⟨_, hkS⟩, ?_, rfl⟩
      have hl1 := (hφ1 ⟨l, hlX⟩).1 (h ⟨l, hlX⟩ hl)
      have := hconj ⟨g, hg⟩ ⟨l, hlX⟩ hkS
      simp only at this
      change actTil V₀ V hE ⟨g * l * g⁻¹, hkS⟩ = 1
      rw [this, hl1, mul_one, mul_inv_cancel]
    have hXQ : X ≤ Q := iSup₂_le hKQ
    have htriv : ∀ y : ↥(barSub V₀ V hE X), y = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := hφ y
      rw [hφ1]
      obtain ⟨z, hz, hzx⟩ := hXQ x.2
      have hzx' : z = ⟨(x : G), hXS x.2⟩ := Subtype.ext hzx
      rw [← hzx']
      exact hz
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(barSub V₀ V hE X))
    exact hy (htriv y)
  by_contra hne
  obtain ⟨K, hK, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne
  have hcomm : ∀ K' ∈ conjSetOf D.M L, K' ≠ L → ∀ a b : ↥X, (a : G) ∈ L → (b : G) ∈ K' →
      φ a * φ b = φ b * φ a := by
    intro K' hK' hK'L a b ha hb
    have hc := uc22p22l_barImage_commute (hC L hLm) (hC K' hK') (Ne.symm hK'L) _
      (uc22p21c_mem_barImage.2 ⟨a, ha, rfl⟩) _ (uc22p21c_mem_barImage.2 ⟨b, hb, rfl⟩)
    have hab : ((⁅a, b⁆ : ↥X) : G) ∈ pCoreOf 2 X :=
      uc22p22u_commutator_mem_pCoreOf a.2 b.2 hc
    have hact : actTil V₀ V hE ⟨((⁅a, b⁆ : ↥X) : G), hXS (⁅a, b⁆ : ↥X).2⟩ = 1 := by
      have hmem := actTil_mem_barSub V₀ V hE hab (hXS (⁅a, b⁆ : ↥X).2)
      rw [h2, Subgroup.mem_bot] at hmem
      exact hmem
    have hcomm1 : φ ⁅a, b⁆ = 1 := (hφ1 _).2 hact
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hcomm1
    exact hcomm1
  have hK1 := image_eq_one_of_commute_of_isSimpleGroup φ hφ rfl hLm hL.2.1 hcomm hL1 hK hKL
  obtain ⟨a, ha, ha1⟩ := hL1
  obtain ⟨g, hg, hKg⟩ := hK
  have hKX : K ≤ X := le_iSup₂_of_le K ⟨g, hg, hKg⟩ le_rfl
  have hbK : g * (a : G) * g⁻¹ ∈ K := by
    rw [hKg]
    exact ⟨(a : G), ha, rfl⟩
  have hbS : g * (a : G) * g⁻¹ ∈ stabTil V₀ V := hXS (hKX hbK)
  have hb1 := (hφ1 ⟨_, hKX hbK⟩).1 (hK1 ⟨_, hKX hbK⟩ hbK)
  have := hconj ⟨g, hg⟩ a hbS
  simp only at this
  rw [this] at hb1
  apply ha1
  rw [hφ1]
  have hb2 := congrArg (fun y => (actTil V₀ V hE ⟨g, hMS hg⟩)⁻¹ * y * actTil V₀ V hE ⟨g, hMS hg⟩)
    hb1
  simpa [mul_assoc] using hb2

theorem barSubBar2Equiv_conjClosure_of_isSimpleGroup {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hs : IsSimpleGroup (Bar2 (conjClosure D.M L)))
    (hX1 : barSub V₀ V hV.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    Nonempty (Bar2 (conjClosure D.M L) ≃* ↥(barSub V₀ V hV.isElemAbelian (conjClosure D.M L))) := by
  have hXL := conjClosure_eq_self_of_isSimpleGroup_bar2 hL hs
  rw [hXL] at hs hX1 ⊢
  exact barSubBar2Equiv_of_isSimpleGroup hV hL hX1 hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
