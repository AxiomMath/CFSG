module

public import CFSG.RankThree.PartTwo.Sec11.Item113
public import CFSG.RankThree.PartTwo.Sec10.HWNormalizes
public import CFSG.RankThree.PartTwo.KFacts.K72List
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.EmbeddingFixedResidual
open scoped commutatorElement

theorem three_dvd_card_of_isList1016 {X : Type} [Group X] [Finite X] (hX : Sec9.IsList1016 X) :
    3 ∣ Nat.card X := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact KFacts.three_dvd_card_of_isoLThreeMinusPi hn hL
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.three_dvd_card_psl2 K

section Theta

variable {G : Type} [Group G] [Finite G]

theorem le_ker_of_normal_solvable {X : Type*} [Group X] [Finite X] {L : Subgroup G}
    (ψ : X →* L ⧸ aschbacherSolvableCore 3 L) (hψ : Function.Surjective ψ) (N : Subgroup X)
    [N.Normal] (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N) : N ≤ ψ.ker := by
  obtain ⟨hθs, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  have hbot := (solvable_prime_complement_core_quotient_centralizers (G := L) Nat.prime_three
    (aschbacherSolvableCore 3 L) hθs hθp).2.2.1
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L ⧸ aschbacherSolvableCore 3 L) Nat.prime_three
  have hMn : (N.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  have hMs : Group.IsSolvable (N.map ψ) :=
    Group.isSolvable_of_surjective (ψ.subgroupMap_surjective N)
  have hM3 : ¬ 3 ∣ Nat.card (N.map ψ) := fun h3 => hN3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hle := hmax (N.map ψ) hMn hMs hM3
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  exact hle

end Theta

theorem item111First_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : Item111First := by
  intro G _ _ A c L a R Y h g hgA hgne hcLg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := h.toTheoremFourHyp
  have := hG.isSimpleGroup
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := hexp c hcA
  have hc1 := h.ne_one
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hΩ : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A := fun x hx3 hx =>
    Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
  set x := g * c * g⁻¹ with hx
  have hxA : x ∈ A := hgA ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hx3 : x ^ 3 = 1 := hexp x hxA
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hc1
    calc c = g⁻¹ * x * g := by rw [hx]; group
      _ = 1 := by rw [hx1]; group
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxc : x ∉ Subgroup.zpowers c := by
    intro hxc
    apply hgne
    have hmap : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hmap]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hcord, hxord])
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLg
  have hLgx : Lg ∈ thetaComponentsAt 3 x :=
    map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
  obtain ⟨hcN, hcl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hcLg
  have htriv : ∀ w ∈ Lg, c * w * c⁻¹ * w⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Lg := by
    intro w hw
    have h1 := hcl w hw
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Lg hw) _).mp h1
    rwa [show w * (w⁻¹ * (c * w * c⁻¹)) * w⁻¹ = c * w * c⁻¹ * w⁻¹ by group] at h2
  have hxcc : x * c = c * x := hcomm x hxA c hcA
  obtain ⟨hsup, P', hP', hP'eq⟩ := fixed_residual_ambient Nat.prime_three hxcc
    ⟨1, by rw [hcord, pow_one]⟩ hLgx hcN htriv
  set K := Lg ⊓ Subgroup.centralizer ({c} : Set G) with hK
  set I := inSubgroup perfectResidual K with hI
  have hIK : I ≤ K := Subgroup.map_subtype_le _
  have hILg : I ≤ Lg := hIK.trans inf_le_left
  have hLgsup : Lg = I ⊔ inSubgroup (aschbacherSolvableCore 3) Lg := by
    rw [sup_comm]
    exact hsup.symm
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy c hcA)
  have hC4 : SectionFourHyp (Subgroup.centralizer ({c} : Set G)) :=
    hG.sectionFourHyp (centralizer_ne_top_of_simple hG.nonabelian hc1)
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
  have h27 : ∃ n : ℕ, 3 ≤ n ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) = 3 ^ n :=
    ⟨3, le_rfl, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, h.card_eq]
      norm_num⟩
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxcc
  obtain ⟨J', hJ', hPJ⟩ := h48 (Subgroup.centralizer ({c} : Set G)) hC4
    (A.subgroupOf (Subgroup.centralizer ({c} : Set G))) hA' h27 ⟨x, hxC⟩
    (Subgroup.mem_subgroupOf.mpr hxA) (fun h1 => hx1 (congrArg Subtype.val h1)) P' hP'
  set J := J'.map (Subgroup.centralizer ({c} : Set G)).subtype with hJ
  have hJc : J ∈ thetaComponentsAt 3 c := ⟨J', hJ', rfl⟩
  have hIJ : I ≤ J := hP'eq.symm.le.trans (Subgroup.map_mono hPJ)
  have hAN : A ≤ Subgroup.normalizer (Lg : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hxA hx1 Lg hLgx
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyC : y ∈ Subgroup.normalizer
        ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (hAC hy)
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAN hy) z).mp hz1,
        (Subgroup.mem_normalizer_iff.mp hyC z).mp hz2⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hAN hy) z).mpr hz1,
        (Subgroup.mem_normalizer_iff.mp hyC z).mpr hz2⟩
  have hAI : A ≤ Subgroup.normalizer (I : Set G) :=
    hAK.trans (GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual K)
  have hψs := surjective_inclusion_quotient hILg hLgsup
  have hLgList : Sec9.IsList1016 (Lg ⧸ aschbacherSolvableCore 3 Lg) :=
    isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm h.isList1016
  have h3I : 3 ∣ Nat.card I :=
    (three_dvd_card_of_isList1016 hLgList).trans (Subgroup.card_dvd_of_surjective hψs)
  obtain ⟨u, ⟨huI, huA'⟩, hu3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAI h3I
  have hu3' : u ^ 3 = 1 := by
    rw [← hu3]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  have huA : u ∈ A := hΩ u hu3' fun y hy => Subgroup.mem_centralizer_iff.mp huA' y hy
  have huLg : u ∈ Lg := hILg huI
  have hZg := center_eq_bot_of_isList1016 hLgList
  have hkey : u ∉ Subgroup.zpowers c := by
    intro huc
    have huC : u ∈ Sec4.thetaQuotCentralizer Lg := (Subgroup.zpowers_le.mpr hcLg) huc
    have h1 := mem_theta_of_mem_thetaQuotCentralizer hZg huLg huC
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (Subtype.ext (by simpa using hu3'))
    exact hu1 (congrArg Subtype.val h2)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L h.mem_thetaComponentsAt
  by_cases hJL : J = L
  ·
    have hIL : I ≤ L := hJL ▸ hIJ
    set φ : I →* L ⧸ aschbacherSolvableCore 3 L :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hIL) with hφ
    set ψ : I →* Lg ⧸ aschbacherSolvableCore 3 Lg :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Lg)).comp (Subgroup.inclusion hILg) with hψ
    have hker : φ.ker ≤ ψ.ker := by
      obtain ⟨hθs, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := L)
        Nat.prime_three
      have hrange : ∀ y : φ.ker,
          ((Subgroup.inclusion hIL).comp φ.ker.subtype) y ∈ aschbacherSolvableCore 3 L := by
        intro y
        have hy : φ (y : I) = 1 := MonoidHom.mem_ker.mp y.2
        change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hIL (y : I)) = 1
          at hy
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
        exact hy
      set f : φ.ker →* aschbacherSolvableCore 3 L :=
        ((Subgroup.inclusion hIL).comp φ.ker.subtype).codRestrict _ hrange with hf
      have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (by
        have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) hyz
        simpa [hf] using this))
      have hks : Group.IsSolvable φ.ker := Group.isSolvable_of_isSolvable_injective hfinj
      have hk3 : ¬ 3 ∣ Nat.card φ.ker := by
        intro h3
        apply hθp
        rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h3
        exact h3.trans (Subgroup.card_subgroup_dvd_card _)
      exact le_ker_of_normal_solvable ψ hψs φ.ker hks hk3
    have hcardL : Nat.card (Lg ⧸ aschbacherSolvableCore 3 Lg) =
        Nat.card (L ⧸ aschbacherSolvableCore 3 L) :=
      Nat.card_congr (Sec13.thetaQuotEquiv (MulAut.conj g) L).symm.toEquiv
    have hdvd : Nat.card ψ.range ∣ Nat.card φ.range := by
      rw [← Subgroup.index_ker, ← Subgroup.index_ker]
      exact Subgroup.index_dvd_of_le hker
    rw [MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top, hcardL] at hdvd
    have hφs : Function.Surjective φ := by
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
        (Nat.le_of_dvd Nat.card_pos hdvd))
    have hxI : ∀ i ∈ I, x * i = i * x := fun i hi =>
      (Subgroup.mem_centralizer_singleton_iff.mp
        (Sec6.le_centralizer_of_mem_thetaComponentsAt hLgx (hILg hi))).symm
    have hxθ : x ∈ Subgroup.normalizer
        (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
      Sec6.normalizer_le_normalizer_theta L (hAL hxA)
    have hxsec : x ∈ Late.sectionCentralizer A L
        ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨hxA, fun l hl => ?_⟩
      obtain ⟨i, hi⟩ := hφs ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hi
      set t := (i : G)⁻¹ * l with ht
      have htθ : t ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨_, hi, by simp [ht]⟩
      have hl' : l = (i : G) * t := by rw [ht]; group
      have h1 : x * t * x⁻¹ * t⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
        Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxθ t).mp htθ) (Subgroup.inv_mem _ htθ)
      have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L (hIL i.2)) _).mp h1
      have h3 : x * l * x⁻¹ * l⁻¹ = (i : G) * (x * t * x⁻¹ * t⁻¹) * (i : G)⁻¹ := by
        rw [hl']
        calc x * ((i : G) * t) * x⁻¹ * ((i : G) * t)⁻¹ =
            (x * (i : G)) * t * x⁻¹ * t⁻¹ * (i : G)⁻¹ := by group
          _ = ((i : G) * x) * t * x⁻¹ * t⁻¹ * (i : G)⁻¹ := by rw [hxI i i.2]
          _ = (i : G) * (x * t * x⁻¹ * t⁻¹) * (i : G)⁻¹ := by group
      rw [h3]
      exact h2
    rw [h.sectionCentralizer_eq] at hxsec
    exact hxc hxsec
  ·
    apply hkey
    have husec : u ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨huA, fun l hl => ?_⟩
      have h1 := Sec10.commutator_mem_theta_of_ne hJc h.mem_thetaComponentsAt hJL (hIJ huI) hl
      have h2 : u * l * u⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL huA) l).mp hl) (L.inv_mem hl)
      have h3 := Sec6.theta_eq_inf_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
      show u * l * u⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L
      rw [h3]
      exact ⟨h2, h1⟩
    rw [h.sectionCentralizer_eq] at husec
    exact husec

theorem item113_of (h97 : Sec9.Item97) (h112 : Item112) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) : Item113 :=
  item113_of_item111First h97 h112 h45 (item111First_of h45 h48)

end CFSG.RankThree.PartTwo.Sec11
