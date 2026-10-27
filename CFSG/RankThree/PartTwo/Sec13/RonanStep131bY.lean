module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan
public import CFSG.RankThree.PartTwo.Sec4.Item463Proof
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bYComp
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bYTransfer
import CFSG.RankThree.PartTwo.Sec4.Item422Proof

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem exists_Y
    (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) (h49 : Sec4.Item4_9) (h47 : Sec4.Item4_7W)
    (h423 : Sec4.Item4_23) (hAlt : Sec4.Step463Alt)
    {G : Type} [Group G] [Finite G] (hst : PartTwoStanding G)
    {E F R : Subgroup G} {a b c : G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hbE : b ∈ E)
    (hFF : F ∈ partTwoF G) (hF27 : Nat.card F = 27) (haF : a ∈ F) (hbF : b ∈ F) (hcF : c ∈ F)
    (hb1 : b ≠ 1)
    (hB9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (hbB : b ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRa : R ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hFR : F ≤ Subgroup.normalizer (R : Set G))
    (hRc : ∀ r ∈ R, c * r * c⁻¹ = r → r = 1)
    (hodd : Odd (Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))))) :
    ∃ Y : Subgroup G, Y ∈ lA F b ∧ E ≤ Subgroup.normalizer (Y : Set G) ∧ List463 Y := by
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hFF.1
  have hcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hb3o : orderOf b = 3 := orderOf_eq_prime (hFe.2 b hbF) hb1
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb3o]
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hFC : F ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbF)
  have hCtop : C ≠ ⊤ := Sec12.centralizer_ne_top_of_theoremFourHyp hst.toTheoremFourHyp hb1
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  have hmax := maximal_subgroupOf_of_le hFF.2.1 hFe hFC
  have h27' : Nat.card (F.subgroupOf C) = 27 := by
    rw [← hF27, ← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFC]
  set b' : C := ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hb'def
  set a' : C := ⟨a, hFC haF⟩ with ha'def
  set c' : C := ⟨c, hFC hcF⟩ with hc'def
  have hb'A : b' ∈ F.subgroupOf C := Subgroup.mem_subgroupOf.mpr hbF
  have ha'A : a' ∈ F.subgroupOf C := Subgroup.mem_subgroupOf.mpr haF
  have hc'A : c' ∈ F.subgroupOf C := Subgroup.mem_subgroupOf.mpr hcF
  have hb'Z : b' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers] at hB9
    have := orderOf_le_of_pow_eq_one (by norm_num) (hFe.2 c hcF)
    omega
  have ha'b' : a' ∉ Subgroup.zpowers b' := by
    intro ha'
    have ha : a ∈ Subgroup.zpowers b := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
      exact ⟨k, congrArg Subtype.val hk⟩
    have ha3 : orderOf a = 3 := orderOf_eq_prime (hFe.2 a haF) ha1
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hb3o])
    exact hbB (Subgroup.mem_sup_left (heq ▸ Subgroup.mem_zpowers b))
  have hodd' : Odd (Nat.card (aschbacherSolvableCore 3 C)) := by
    have h : Nat.card (inSubgroup (aschbacherSolvableCore 3) C) =
        Nat.card (aschbacherSolvableCore 3 C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rwa [h] at hodd
  have hev : 2 ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a'} : Set C)), F.subgroupOf C⁆ : Subgroup C) := by
    set R' := R.subgroupOf C with hR'def
    have hR'2 : IsPGroup 2 R' := hR2.comap_subtype
    obtain ⟨hθs, hθ3⟩ := Sec4.Item422Proof.inSubgroup_theta_solvable_coprime
      (Subgroup.centralizer ({a} : Set G))
    set S := (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))).subgroupOf C with hSdef
    set M := Subgroup.centralizer ({a'} : Set C) with hMdef
    have hSG : ∀ s : C, s ∈ S → (s : G) ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a} : Set G)) := fun s hs => Subgroup.mem_subgroupOf.mp hs
    have hMG : ∀ m : C, m ∈ M → (m : G) ∈ Subgroup.centralizer ({a} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hm))
    have hSM : S ≤ M := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp (Sec6.theta_le _ (hSG s hs))))
    have hSn : (S.subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSM]
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta _ (hMG m hm)) (x : G)
    let f : S →* inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) :=
      MonoidHom.codRestrict ((Subgroup.subtype C).comp S.subtype) _ fun s => hSG s s.2
    have hf : Function.Injective f := fun x y hxy => by
      have h1 : ((f x : _) : G) = ((f y : _) : G) := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    have hSsol : Group.IsSolvable S :=
      haveI := hθs
      Group.isSolvable_of_isSolvable_injective hf
    have hS3 : ¬ 3 ∣ Nat.card S := fun h =>
      hθ3 (h.trans (Subgroup.card_dvd_of_injective f hf))
    have hRS : R' ≤ S := fun r hr =>
      Subgroup.mem_subgroupOf.mpr (hRa (Subgroup.mem_subgroupOf.mp hr))
    have hR'H : R' ≤ inSubgroup (aschbacherSolvableCore 3) M :=
      hRS.trans (Sec4.Item422Proof.le_inSubgroup_theta_of_normal hSM hSn hSsol hS3)
    have hc'N : c' ∈ Subgroup.normalizer (R' : Set C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.mp (hFR hcF) (x : G)
    have hXR : (⁅R', Subgroup.zpowers c'⁆ : Subgroup C) ≤ R' :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hc'N)
    have hX2 : IsPGroup 2 (⁅R', Subgroup.zpowers c'⁆ : Subgroup C) := hR'2.to_le hXR
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
    have hr'R' : (⟨r, hRb r.2⟩ : C) ∈ R' := Subgroup.mem_subgroupOf.mpr r.2
    have hmem : ⁅(⟨r, hRb r.2⟩ : C), c'⁆ ∈ (⁅R', Subgroup.zpowers c'⁆ : Subgroup C) :=
      Subgroup.commutator_mem_commutator hr'R' (Subgroup.mem_zpowers c')
    have hne : ⁅(⟨r, hRb r.2⟩ : C), c'⁆ ≠ 1 := by
      intro h
      have h1 : (r : G) * c = c * r :=
        congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp h)
      have h2 : c * (r : G) * c⁻¹ = r := by rw [← h1]; group
      exact hr1 (Subtype.ext (hRc r r.2 h2))
    have hX1 : (⁅R', Subgroup.zpowers c'⁆ : Subgroup C) ≠ ⊥ := fun h =>
      hne (Subgroup.mem_bot.mp (h ▸ hmem))
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hX1 (Subgroup.eq_bot_of_card_eq _ hk)
    exact (hk ▸ dvd_pow_self 2 hk0 : 2 ∣ Nat.card (⁅R', Subgroup.zpowers c'⁆ : Subgroup C)).trans
      (Subgroup.card_dvd_of_le
        (Subgroup.commutator_mono hR'H (Subgroup.zpowers_le.mpr hc'A)))
  obtain ⟨L', hL', hA'N, h9, hα, hlist⟩ :=
    exists_component_list h45 h41 hKF h49 h47 h423 hAlt hS4 hmax h27' hb'A hb'Z hb'1 ha'A ha'b'
      hodd' hev
  have hlA : L'.map C.subtype ∈ lA F b :=
    mem_lA_map_subtype hbF hb3 hF27 C hCdef hFC hL' hA'N h9 hα
  refine ⟨L'.map C.subtype, hlA, ?_, list463_map_subtype C hlist⟩
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers b (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbE⟩)))
  exact Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hb3o hlA.1 hE3 hEH

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
