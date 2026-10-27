module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.Holt.Induced
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
  (xbar9 wbar9 toImg9 toImg9_surjective coprime_card_ker_toImg9 isCyclic_of_isPGroup_lbar9)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem r95_xbar_hasL32Quot {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃)
    (hX : LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1) : HasL32Quot (xbar9 Y H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXH : Opp 3 Y ≤ H :=
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.opp_le 3 Y).trans hyp.2.1.1
  have hle : img9 H (Opp 3 Y) ≤ img9 H (L9 Y H) :=
    Subgroup.map_mono fun y hy => opp_le_L9 Y H hy
  set ψ := toImg9 hXH
  have hψ : Function.Surjective ψ := toImg9_surjective hXH
  set π : ↥(Opp 3 Y) →* BarO3 (Opp 3 Y) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Opp 3 Y)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ψ.ker ≤ π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.le_pPrimeCore_of_normal_coprime (MonoidHom.normal_ker ψ)
      (coprime_card_ker_toImg9 hXH)
  let f : ↥(img9 H (Opp 3 Y)) →* BarO3 (Opp 3 Y) :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨π, hker⟩
  have hfψ : ∀ x : ↥(Opp 3 Y), f (ψ x) = π x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨π, hker⟩ x
  have hfs : Function.Surjective f := by
    intro b
    obtain ⟨x, rfl⟩ := hπs b
    exact ⟨ψ x, hfψ x⟩
  refine ⟨BarO3 (Opp 3 Y), inferInstance, f.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
    ?_, hX⟩
  exact hfs.comp (Subgroup.subgroupOfEquivOfLe hle).surjective

private theorem r95_lift_order_three {Y H : Subgroup G} (hXH : Opp 3 Y ≤ H)
    {Qb : Subgroup (Hbar9 H)} (hQ : Nat.card Qb = 3) (hQX : Qb ≤ img9 H (Opp 3 Y)) :
    ∃ A : Subgroup G, A ≤ Opp 3 Y ∧ Nat.card A = 3 ∧ img9 H A = Qb := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := toImg9 hXH
  set Qc : Subgroup ↥(img9 H (Opp 3 Y)) := Qb.subgroupOf (img9 H (Opp 3 Y))
  have eQ : ↥Qc ≃* ↥Qb := Subgroup.subgroupOfEquivOfLe hQX
  have hQp : IsPGroup 3 Qb := IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])
  obtain ⟨P, -, -, hP, hPQ⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := ⊤) (E := ⊥) ψ
    (hQp.of_equiv eQ.symm)
    (by rw [Subgroup.map_top_of_surjective ψ (toImg9_surjective hXH)]; exact le_top)
    IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  have hcop : (3 : ℕ).Coprime (Nat.card ψ.ker) := coprime_card_ker_toImg9 hXH
  obtain ⟨e⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image 3 Nat.prime_three ψ
      hcop P hP
  refine ⟨P.map (Opp 3 Y).subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Opp 3 Y).subtype_injective, Nat.card_congr e.toEquiv,
      hPQ, Nat.card_congr eQ.toEquiv, hQ]
  · ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
      have h1 : ψ x ∈ Qc := hPQ ▸ Subgroup.mem_map_of_mem ψ hx
      have hxy' : Subgroup.inclusion hXH x = y := Subtype.ext hxy
      have h2 : ((ψ x : ↥(img9 H (Opp 3 Y))) : Hbar9 H) =
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y := by
        rw [← hxy']
        rfl
      rw [← h2]
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hz
      have hz' : (⟨z, hQX hz⟩ : ↥(img9 H (Opp 3 Y))) ∈ P.map ψ := by
        rw [hPQ]
        exact Subgroup.mem_subgroupOf.2 hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz'
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), congrArg Subtype.val hxz⟩

theorem r95_normalizer_le_wbar {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    ∀ Dq : Subgroup (Lbar9 Y H), Dq ≤ xbar9 Y H → Nat.card Dq = 3 →
      normalizer (Dq : Set (Lbar9 Y H)) ≤ wbar9 D Y H := by
  intro Dq hDq h3 xb hxb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Lb := img9 H (L9 Y H)
  have hDb : Nat.card (Dq.map Lb.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, h3]
  have hDbX : Dq.map Lb.subtype ≤ img9 H (Opp 3 Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDq hd
  have hXY : Opp 3 Y ≤ Y :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.opp_le 3 Y
  obtain ⟨A, hAX, hAc, hAD⟩ := r95_lift_order_three (hXY.trans hyp.2.1.1) hDb hDbX
  have hAH : A ≤ H := hAX.trans (hXY.trans hyp.2.1.1)
  have hNA : normalizer (A : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
      (hyp.1.2.2 A (hAX.trans hXY) hAc)
  have hA3 : IsPGroup 3 (A.subgroupOf H) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc, pow_one])
  have hx : (xb : Hbar9 H) ∈ normalizer ((img9 H A : Subgroup (Hbar9 H)) : Set (Hbar9 H)) := by
    rw [hAD]
    exact Subgroup.le_normalizer_map Lb.subtype ⟨xb, hxb, rfl⟩
  obtain ⟨g, hg, hgx⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
    Nat.prime_three (CFSG.pPrimeCore 3 ↥H) CFSG.pPrimeCore_coprime_card hA3 hx
  have hgM : (g : G) ∈ D.M := by
    apply hNA
    have := Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH] at this
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 ⟨g.2, hgM⟩, hgx⟩

theorem r95_xbar_le_wbar {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    xbar9 Y H ≤ wbar9 D Y H := by
  have hXY : Opp 3 Y ≤ Y :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.opp_le 3 Y
  have hXH : Opp 3 Y ≤ H := hXY.trans hyp.2.1.1
  have hXM : Opp 3 Y ≤ D.M := hXY.trans hyp.1.1
  unfold xbar9 wbar9
  exact Subgroup.subgroupOf_mono _
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hXH hXM)))

theorem r95_wbar_ne_top {D : Data G} {Y H : Subgroup G}
    (hLM : ¬ img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) : wbar9 D Y H ≠ ⊤ := by
  intro htop
  apply hLM
  intro x hx
  have hmem : (⟨x, hx⟩ : Lbar9 Y H) ∈ wbar9 D Y H := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem r95_isSL2Cover_opp_wbar {D : Data G} {Y H : Subgroup G} {e : ℕ}
    (h : IsSL2Cover ↥(Opp 3 (wbar9 D Y H)) 7 e) :
    IsSL2Cover ↥(Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H))) 7 e := by
  have cover : ∀ {Q Q' : Type} [Group Q] [Group Q'] (φ : Q ≃* Q'),
      IsSL2Cover Q 7 e → IsSL2Cover Q' 7 e := by
    intro Q Q' _ _ φ hq
    obtain ⟨hQ, hc, hL⟩ := hq
    refine ⟨CFSG.IsQuasisimple.of_mulEquiv φ.symm hQ, ?_, ?_⟩
    · rw [← Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
      exact hc
    · exact CFSG.Blueprint.LieModel.of_mulEquiv
        (QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q') φ
          (Subgroup.map_center_eq φ)) hL
  have hmap : (wbar9 D Y H).map (img9 H (L9 Y H)).subtype
      = img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H) := by
    unfold wbar9
    exact Subgroup.subgroupOf_map_subtype _ _
  have hopp : Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H))
      = (Opp 3 (wbar9 D Y H)).map (img9 H (L9 Y H)).subtype := by
    rw [← hmap]
    exact (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_three
      (img9 H (L9 Y H)).subtype (wbar9 D Y H)).symm
  rw [hopp]
  exact cover ((Opp 3 (wbar9 D Y H)).equivMapOfInjective (img9 H (L9 Y H)).subtype
    (img9 H (L9 Y H)).subtype_injective) h

theorem r95_caseB {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (h92 : R92 D)
    (hX : LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1)
    (hLM : ¬ img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    ∃ e : ℕ, 1 ≤ e ∧ LieModel (Lbar9 Y H) .PSU 3 7 e ∧
      IsSL2Cover ↥(Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H))) 7 e ∧
      ¬ 2 ∣ (wbar9 D Y H).index := by
  have hshape : Shape92 (Lbar9 Y H) := (h92 Y H D₃ hyp hH).2
  have hcyc := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.isCyclic_of_isPGroup_lbar9 hyp
  have hE : HasL32Quot (xbar9 Y H) := r95_xbar_hasL32Quot hyp hX
  have hEW : xbar9 Y H ≤ wbar9 D Y H := r95_xbar_le_wbar hyp
  have hNW := r95_normalizer_le_wbar hyp
  have hW : wbar9 D Y H ≠ ⊤ := r95_wbar_ne_top hLM
  obtain ⟨e, he, hU3, hcov, hodd⟩ := r95_group_caseB hshape hcyc hE hEW hNW hW
  exact ⟨e, he, hU3, r95_isSL2Cover_opp_wbar hcov, hodd⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
