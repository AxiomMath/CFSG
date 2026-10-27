module

public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGenStatements
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofHull
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G]

namespace Item233ZGenProof

theorem eq_top_of_isPerfect_le {X : Type*} [Group X] (hX : Group.IsPerfect X)
    {T : Subgroup X} [T.Normal] (hT : Group.IsSolvable T) (hq : IsQuasisimple (X ⧸ T))
    {C : Subgroup X} [hC : C.Normal] {P : Subgroup X} (hP : Group.IsPerfect P) (hP1 : P ≠ ⊥)
    (hPC : P ≤ C) : C = ⊤ := by
  have : Group.IsPerfect X := hX
  have hM : (C.map (QuotientGroup.mk' T)).Normal := hC.map _ (QuotientGroup.mk'_surjective T)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hM with h | h
  · refine Sec4.Census.eq_top_of_isSolvable_quotient ?_
    have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp T.subtype) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H g =>
        have hg : QuotientGroup.mk' T g ∈ C.map (QuotientGroup.mk' T) := by
          rw [h]
          trivial
        obtain ⟨c, hc, hcg⟩ := hg
        have hk : c⁻¹ * g ∈ T := QuotientGroup.eq.mp hcg
        refine ⟨⟨c⁻¹ * g, hk⟩, ?_⟩
        change (QuotientGroup.mk (c⁻¹ * g) : X ⧸ C) = QuotientGroup.mk g
        rw [QuotientGroup.eq, show (c⁻¹ * g)⁻¹ * g = g⁻¹ * c * g by group]
        exact hC.conj_mem' c hc g
    exact Group.isSolvable_of_surjective hsurj
  · exfalso
    set f : P →* X ⧸ T := (QuotientGroup.mk' T).comp P.subtype with hf
    have hrange : Group.IsPerfect f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    have hcomm : ∀ a b : f.range, a * b = b * a := by
      rintro ⟨_, ⟨p, rfl⟩⟩ ⟨_, ⟨q, rfl⟩⟩
      apply Subtype.ext
      have hp : f p ∈ Subgroup.center (X ⧸ T) := h ⟨p, hPC p.2, rfl⟩
      exact (Subgroup.mem_center_iff.mp hp (f q)).symm
    have hsub := subsingleton_of_isPerfect_of_isSolvable hrange (Group.isSolvable_of_comm hcomm)
    have hPT : P ≤ T := by
      intro p hp
      have h1 : f ⟨p, hp⟩ = 1 := by
        have := Subsingleton.elim (⟨f ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩⟩ : f.range) 1
        exact congrArg Subtype.val this
      have h2 : QuotientGroup.mk' T p = 1 := h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hPs : Group.IsSolvable P :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPT)
        (Subgroup.inclusion_injective hPT)
    have := subsingleton_of_isPerfect_of_isSolvable hP hPs
    apply hP1
    rw [eq_bot_iff]
    intro p hp
    have h1 : (⟨p, hp⟩ : P) = 1 := Subsingleton.elim _ _
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)

theorem kOf_le_iSup {A Z : Subgroup G} {ψ : MulAut A} (hψ : ψ ∈ dStar A)
    (hψZ : ψ ∈ starOf A Z) :
    kOf A ψ ≤ ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ :=
  le_iSup_of_le ψ (le_iSup_of_le hψ (le_iSup_of_le hψZ le_rfl))

theorem wConj_mem_starOf {A Z : Subgroup G} (w : Subgroup.normalizer (A : Set G))
    (hw : (w : G) ∈ Z) : wConj A w ∈ starOf A Z :=
  ⟨w, Subgroup.mem_subgroupOf.mpr hw, rfl⟩

theorem normalizer_le_normalizer_iSup [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    (Z : Subgroup G) :
    Z ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (((⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z),
        kOf A ψ) : Subgroup G) : Set G) := by
  rintro w ⟨hwZ, hw⟩
  set w' : Subgroup.normalizer (A : Set G) := ⟨w, hw⟩
  set N := ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ with hN
  have hwZ' : wConj A w' ∈ starOf A Z := wConj_mem_starOf w' hwZ
  have hle : N.map (MulAut.conj w).toMonoidHom ≤ N := by
    rw [hN, Subgroup.map_iSup]
    refine iSup_le fun ψ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hψ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hψZ => ?_
    rw [← kOf_conj_of_unique hK w' hψ]
    exact kOf_le_iSup (conj_mem_dStar w' hψ)
      ((starOf A Z).mul_mem ((starOf A Z).mul_mem hwZ' hψZ) ((starOf A Z).inv_mem hwZ'))
  have heq : N.map (MulAut.conj w).toMonoidHom = N := Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj w).injective).symm)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simpa [MulAut.conj_apply] using hyx
    exact this ▸ hy

end Item233ZGenProof

open Item233ZGenProof

theorem item233ZGen_of (h222 : Item222) (hKW : KOfWellDefinedAll) (hInner : Item223OneInner)
    (hRefl : Item233ZReflDStar) (hRoot : Item233ZRootGen) : Item233ZGen := by
  intro G _ _ A E U c L hpair hconc φ hφ Z hZ hKZ _ h3
  have hK := hKW G A E U c L hpair
  have h4 : Nat.card A = 3 ^ 4 → Item223OneInnerConcl A φ Z :=
    fun hA => hInner G A E U c L hpair hA φ hφ Z hZ hKZ
  have hR := hRefl G A E U c L hpair hconc φ hφ Z hZ hKZ h4 h3
  have hgen := hRoot G A E U c L hpair hconc φ hφ Z hZ hKZ h4 h3 hR
  set N := ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ with hN
  have hZN : Z ≤ Subgroup.normalizer (N : Set G) :=
    hgen.trans (sup_le (normalizer_le_normalizer_iSup hK Z) Subgroup.le_normalizer)
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  have hφZ : φ ∈ starOf A Z := by
    rw [← hj]
    exact wConj_mem_starOf j (hKZ hjK)
  have hKN : kOf A φ ≤ N := kOf_le_iSup hφ hφZ
  obtain ⟨z, -, -, hZz⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hZp : Group.IsPerfect Z := Sec6.isPerfect_of_mem_thetaComponentsAt hZz
  have hZq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hZz
  obtain ⟨hTs, -⟩ := solvable_prime_complement_core_characterization (H := Z) Nat.prime_three
  obtain ⟨n, hn, ⟨eK⟩⟩ := Item233One.exists_two_le_mulEquiv_kOf h222 hpair hφ
  have hKp : Group.IsPerfect (kOf A φ) := isPerfect_of_mulEquiv_projSL hn eK
  have hPp : Group.IsPerfect ((kOf A φ).subgroupOf Z) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKZ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKZ).symm.surjective
  have hP1 : (kOf A φ).subgroupOf Z ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := exists_not_commute_of_mulEquiv_projSL eK
    have ha : (⟨a, hKZ a.2⟩ : Z) ∈ (kOf A φ).subgroupOf Z := Subgroup.mem_subgroupOf.mpr a.2
    have hb : (⟨b, hKZ b.2⟩ : Z) ∈ (kOf A φ).subgroupOf Z := Subgroup.mem_subgroupOf.mpr b.2
    rw [h, Subgroup.mem_bot] at ha hb
    have ha1 : a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
    have hb1 : b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
    exact hab (by rw [ha1, hb1])
  have hNZ : N ⊓ Z ≤ Z := inf_le_right
  have hnorm : ((N ⊓ Z).subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNZ).mpr fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hZN hx, Subgroup.le_normalizer hx⟩
  have hPC : (kOf A φ).subgroupOf Z ≤ (N ⊓ Z).subgroupOf Z := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨hKN (Subgroup.mem_subgroupOf.mp hx), x.2⟩
  have htop := eq_top_of_isPerfect_le hZp hTs hZq hPp hP1 hPC
  exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left

end CFSG.RankThree.PartTwo.Sec21
