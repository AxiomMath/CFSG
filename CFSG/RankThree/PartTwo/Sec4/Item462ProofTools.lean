module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.LocalRank.ThetaPlaneExactQuotients
import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Milestones.LC_GL_local_rank_bounds

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item422Proof
open scoped commutatorElement

section Hyperplane

variable {G : Type*} [Group G]

theorem disjoint_zpowers_of_pow_three {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hxH : x ∉ H) : Disjoint H (Subgroup.zpowers x) := by
  rw [Subgroup.disjoint_def]
  intro y hyH hyx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  rw [zpow_eq_zpow_emod k hx3'] at hyH ⊢
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk] at hyH ⊢
  · exact zpow_zero x
  · exact absurd (by simpa using hyH) hxH
  · exfalso
    apply hxH
    have h1 : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hx3', mul_one, zpow_one]
    rw [h1]
    exact H.zpow_mem hyH 2

theorem card_sup_zpowers_of_not_mem {B : Subgroup G} {a : G} (haZ : a ∈ Subgroup.center G)
    (ha3 : orderOf a = 3) (haB : a ∉ B) :
    Nat.card (B ⊔ Subgroup.zpowers a : Subgroup G) = Nat.card B * 3 := by
  have hdisj : Disjoint B (Subgroup.zpowers a) :=
    disjoint_zpowers_of_pow_three (by rw [← ha3]; exact pow_orderOf_eq_one a) haB
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.zpowers_le.mpr haZ).trans ((Subgroup.center_le_centralizer _).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B _ hN hdisj,
    Nat.card_zpowers, ha3]

theorem centralizer_eq_of_not_mem [Finite G] {A B : Subgroup G} {a : G} (hBA : B ≤ A)
    (hAcard : Nat.card A = 27) (hBcard : Nat.card B = 9) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3) (haB : a ∉ B) :
    Subgroup.centralizer (B : Set G) = Subgroup.centralizer (A : Set G) := by
  have hBa : B ⊔ Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hBA (Subgroup.zpowers_le.mpr haA)) ?_
    rw [card_sup_zpowers_of_not_mem haZ ha3 haB, hAcard, hBcard]
  refine le_antisymm ?_ (Subgroup.centralizer_le hBA)
  rw [Subgroup.le_centralizer_iff, ← hBa]
  refine sup_le (Subgroup.le_centralizer_iff.mp le_rfl) ?_
  exact (Subgroup.zpowers_le.mpr haZ).trans (Subgroup.center_le_centralizer _)

theorem mem_of_le_centralizer_of_commutator_eq [Finite G] {A B U : Subgroup G} {a : G}
    (hBA : B ≤ A) (hAcard : Nat.card A = 27) (hBcard : Nat.card B = 9) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (hUB : U ≤ Subgroup.centralizer (B : Set G)) (hUA : ⁅U, A⁆ = U) (hU : U ≠ ⊥) : a ∈ B := by
  by_contra haB
  have hUA' : U ≤ Subgroup.centralizer (A : Set G) :=
    hUB.trans (centralizer_eq_of_not_mem hBA hAcard hBcard haA haZ ha3 haB).le
  apply hU
  rw [← hUA]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUA'

theorem exists_centralizer_eq [Finite G] {B : Subgroup G} {a : G} (hBcard : Nat.card B = 9)
    (hB3 : ∀ x ∈ B, x ^ 3 = 1) (haB : a ∈ B) (haZ : a ∈ Subgroup.center G)
    (ha3 : orderOf a = 3) :
    ∃ b ∈ B, b ∉ Subgroup.zpowers a ∧
      Subgroup.centralizer (B : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have hZB : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr haB
  obtain ⟨b, hbB, hba⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle : B ≤ Subgroup.zpowers a := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    rw [hBcard, Nat.card_zpowers, ha3] at this
    norm_num at this
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hB3 b hbB) hb1
  have hab : a ∉ Subgroup.zpowers b := by
    intro hab
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hab
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hb3])
    exact hba (heq ▸ Subgroup.mem_zpowers b)
  have hBeq : Subgroup.zpowers b ⊔ Subgroup.zpowers a = B := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hbB) hZB) ?_
    rw [card_sup_zpowers_of_not_mem haZ ha3 hab, Nat.card_zpowers, hb3, hBcard]
  refine ⟨b, hbB, hba, le_antisymm (Subgroup.centralizer_le (by simpa using hbB)) ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hBeq]
    refine sup_le ?_ ((Subgroup.zpowers_le.mpr haZ).trans (Subgroup.center_le_centralizer _))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_singleton_iff).mp hx).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hBx hy)

theorem inSubgroup_pCore_two_le_theta {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    inSubgroup (CFSG.pCore 2) H ≤ inSubgroup (aschbacherSolvableCore 3) H :=
  Subgroup.map_mono ((solvable_prime_complement_core_characterization (H := H)
    Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num))

end Hyperplane

section Core

theorem commutatorElement_mul_of_mem_center {H : Type*} [Group H] (g u w : H)
    (hw : w ∈ Subgroup.center H) : ⁅g, u * w⁆ = ⁅g, u⁆ := by
  have h1 := Subgroup.mem_center_iff.mp hw g⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  have h2 : g * (u * w) * g⁻¹ * (u * w)⁻¹ = g * u * (w * g⁻¹) * w⁻¹ * u⁻¹ := by group
  rw [h2, ← h1]
  group

theorem centralizer_mul_of_mem_center {H : Type*} [Group H] (b z : H)
    (hz : z ∈ Subgroup.center H) :
    Subgroup.centralizer ({b * z} : Set H) = Subgroup.centralizer ({b} : Set H) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hzx : x * z = z * x := Subgroup.mem_center_iff.mp hz x
  constructor
  · intro h
    have h' : x * b * z = b * x * z := by
      calc x * b * z = x * (b * z) := by group
        _ = b * z * x := h
        _ = b * (z * x) := by group
        _ = b * (x * z) := by rw [hzx]
        _ = b * x * z := by group
    exact mul_right_cancel h'
  · intro h
    calc x * (b * z) = x * b * z := by group
      _ = b * x * z := by rw [h]
      _ = b * (x * z) := by group
      _ = b * (z * x) := by rw [hzx]
      _ = b * z * x := by group

theorem mem_thetaQuotCentralizer_iff_mk {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (g : G) :
    g ∈ thetaQuotCentralizer L ↔ QuotientGroup.mk' (aschbacherSolvableCore 3 G) g ∈
      Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G)) := by
  obtain ⟨-, -, -, -, -, -, -, hC, -, -, -⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  rw [← hC g, Sec6.mem_thetaQuotCentralizer_iff]
  refine and_congr_right fun _ => forall₂_congr fun l _ => ?_
  rw [leftCoset_eq_iff]
  constructor
  · intro h
    have h2 : (g * l * g⁻¹)⁻¹ * l = (l⁻¹ * (g * l * g⁻¹))⁻¹ := by group
    rw [h2]
    exact inv_mem h
  · intro h
    have h2 : l⁻¹ * (g * l * g⁻¹) = ((g * l * g⁻¹)⁻¹ * l)⁻¹ := by group
    rw [h2]
    exact inv_mem h


theorem sectionFourHyp_component_of_largePrime (h1 : Item4_1LargePrime) {G : Type} [Group G]
    [Finite G] (hS4 : SectionFourHyp G) {K : Subgroup (G ⧸ aschbacherSolvableCore 3 G)}
    (hK : IsComponent K) : SectionFourHyp K := by
  set e := comapQuotientEquiv (aschbacherSolvableCore 3 G) K
  have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK.1
  exact Census.sectionFourHyp_of_mulEquiv e (Item41Narrow.sectionFourHyp_section h1 hS4 _ _
    (fun h => three_not_dvd_card_aschbacherSolvableCore
      (h.trans (Item41Narrow.card_subgroupOf_dvd _ _))) hq)

theorem exists_thetaComponent_of_le_commutator (h45 : Item4_5) (h41 : Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) {G : Type} [Group G] [Finite G]
    (hS4 : SectionFourHyp G) {A : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    {b : G} (hbA : b ∈ A) (hba : b ∉ Subgroup.zpowers a) {V : Subgroup G}
    (hV : V ≤ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)), A⁆)
    (hVθ : ¬ V ≤ aschbacherSolvableCore 3 G) :
    ∃ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) ∧
      V ≤ Subgroup.normalizer (L : Set G) ∧ ¬ V ≤ thetaQuotCentralizer L ∧
      Nat.card (autThetaQuot A L) = 9 ∧
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ ∧
      ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAE : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).mpr hAe
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hc3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  have hZA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hnorm : ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) := fun L hL =>
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [h27]; norm_num⟩) L hL
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  obtain ⟨hNs, -, hNp, -⟩ :=
    solvable_prime_complement_core_characterization (H := G) Nat.prime_three
  have hθX : aschbacherSolvableCore 3 (G ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers Nat.prime_three N hNs hNp).2.2.1
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hAp
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := G) Nat.prime_three
  have hAK : ∀ K : Subgroup (G ⧸ N), IsComponent K →
      A.map ρ ≤ Subgroup.normalizer (K : Set (G ⧸ N)) := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := hbij.surjOn hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hAiff⟩ :=
      theta_component_quotient_structure Nat.prime_three hL
    exact (hAiff A).mp (hnorm L hL)
  have hbp : IsPGroup 3 (Subgroup.zpowers b) := hAp.to_le (Subgroup.zpowers_le.mpr hbA)
  have hcz : ∀ {H : Type} [Group H] (x : H),
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup H) : Set H) =
        Subgroup.centralizer ({x} : Set H) := fun x => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hθmap : (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set G))).map ρ =
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({ρ b} : Set (G ⧸ N))) := by
    have h := (solvable_prime_complement_core_quotient_centralizers Nat.prime_three N hNs
      hNp).2.2.2 (Subgroup.zpowers b) hbp
    rw [hcz, MonoidHom.map_zpowers, hcz] at h
    exact h
  have hVX : V.map ρ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({ρ b} : Set (G ⧸ N))), A.map ρ⁆ := by
    rw [← hθmap, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hV
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hVΘ : V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) :=
    hV.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hAb.trans (Sec6.le_normalizer_theta _)))
  have hVΘX : V.map ρ ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({ρ b} : Set (G ⧸ N))) := hθmap ▸ Subgroup.map_mono hVΘ
  have hexists : ∃ K : Subgroup (G ⧸ N), IsComponent K ∧
      ¬ V.map ρ ≤ Subgroup.centralizer (K : Set (G ⧸ N)) := by
    by_contra hnone
    have hVE : V.map ρ ≤ Subgroup.centralizer (layer (G ⧸ N) : Set (G ⧸ N)) :=
      le_centralizer_layer_iff.mpr fun K hK => by_contra fun h => hnone ⟨K, hK, h⟩
    have hb3 : (ρ b) ^ 3 = 1 := by rw [← map_pow, hAe.2 b hbA, map_one]
    have hbot := eq_bot_of_le_thetaCore_of_le_centralizer_layer Nat.prime_three hθX hb3 hVΘX hVE
    apply hVθ
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  obtain ⟨K, hK, hVK⟩ := hexists
  obtain ⟨L, hL, hLK⟩ := hbij.surjOn hK
  have hLK : L.map ρ = K := hLK
  subst hLK
  obtain ⟨C', hC'⟩ := IsElementaryAbelian.exists_isCompl 3 A ((Subgroup.zpowers a).subgroupOf A)
  set B' := C'.map A.subtype with hB'
  have hB'A : B' ≤ A := Subgroup.map_subtype_le _
  have hBZ : Disjoint B' (Subgroup.zpowers a) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hxZ⟩
    have hyZ : y ∈ (Subgroup.zpowers a).subgroupOf A := Subgroup.mem_subgroupOf.mpr hxZ
    have hmem : y ∈ (Subgroup.zpowers a).subgroupOf A ⊓ C' := ⟨hyZ, hy⟩
    rw [hC'.inf_eq_bot, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
    exact Subgroup.one_mem _
  have hBZA : B' ⊔ Subgroup.zpowers a = A := by
    have h := congrArg (Subgroup.map A.subtype) hC'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZA,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [sup_comm]
    exact h
  have hB'el : CFSG.Assembly.IsElemAbelian 3 B' :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg (Subtype.val : A → G)
      (hAe.1.is_comm.comm (⟨x, hB'A x.2⟩ : A) ⟨y, hB'A y.2⟩))⟩⟩, fun x hx => hAe.2 x (hB'A hx)⟩
  have haB' : a ∉ B' := fun h => ha1 (by
    have hmem : a ∈ B' ⊓ Subgroup.zpowers a := ⟨h, Subgroup.mem_zpowers a⟩
    rwa [disjoint_iff.mp hBZ, Subgroup.mem_bot] at hmem)
  have hB'card : Nat.card B' = 3 ^ 2 := by
    have h := card_sup_zpowers_of_not_mem haZ hc3 haB'
    rw [hBZA, h27] at h
    omega
  have hbBZ : b ∈ B' ⊔ Subgroup.zpowers a := by rw [hBZA]; exact hbA
  obtain ⟨b', hb', z, hz, hbz⟩ := Subgroup.mem_sup_of_normal_right.mp hbBZ
  have hb'1 : b' ≠ 1 := by
    rintro rfl
    rw [one_mul] at hbz
    exact hba (hbz ▸ hz)
  have hρb'1 : ρ b' ≠ 1 := fun h => hb'1 (hinj (hB'A hb') A.one_mem (by rw [h, map_one]))
  have hρZ : ∀ w ∈ Subgroup.zpowers a, ρ w ∈ Subgroup.center (G ⧸ N) := fun w hw =>
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
      (Subgroup.mem_map_of_mem ρ ((Subgroup.zpowers_le.mpr haZ) hw))
  have hcent : Subgroup.centralizer ({ρ b} : Set (G ⧸ N)) =
      Subgroup.centralizer ({ρ b'} : Set (G ⧸ N)) := by
    rw [← hbz, map_mul, centralizer_mul_of_mem_center _ _ (hρZ z hz)]
  have hcommB : ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))), A.map ρ⁆ ≤
      ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))),
        B'.map ρ⁆ := by
    rw [Subgroup.commutator_le]
    rintro g hg _ ⟨y, hy, rfl⟩
    have hyBZ : y ∈ B' ⊔ Subgroup.zpowers a := by rw [hBZA]; exact hy
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hyBZ
    rw [map_mul, commutatorElement_mul_of_mem_center _ _ _ (hρZ w hw)]
    exact Subgroup.commutator_mem_commutator hg (Subgroup.mem_map_of_mem _ hu)
  have hVB : V.map ρ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))), B'.map ρ⁆ := by
    rw [hcent] at hVX
    exact hVX.trans hcommB
  have hJ : ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))), B'.map ρ⁆ ≤ thetaAlpha 3 (B'.map ρ) := by
    have h1 : ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))), B'.map ρ⁆ ≤ thetaJ 3 (B'.map ρ) := by
      rw [thetaJ]
      exact le_iSup₂_of_le (ρ b') (Subgroup.mem_map_of_mem _ hb') (le_iSup_of_le hρb'1 le_rfl)
    exact h1.trans le_sup_left
  have hQ : ¬ thetaAlpha 3 (B'.map ρ) ≤
      Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    fun h => hVK ((hVB.trans hJ).trans h)
  obtain ⟨hBbcard, -, -, -, -⟩ := theta_plane_alpha_exact_prime_kernel_quotients Nat.prime_three
    B' hB'el hB'card N (Or.inl ⟨hNs, hNp⟩)
  have hBb : CFSG.Assembly.IsElemAbelian 3 (B'.map ρ) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : G ⧸ N) * y = y * x
      rw [← hux, ← hvy, ← map_mul, ← map_mul]
      exact congrArg ρ (congrArg Subtype.val (hB'el.1.is_comm.comm (⟨u, hu⟩ : B') ⟨v, hv⟩))
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hB'el.2 u hu, map_one]
  have hBbE : IsElementaryAbelian 3 (B'.map ρ) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 (B'.map ρ)).mpr hBb
  have hBK : B'.map ρ ⊓ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      ⊥ := by
    by_contra hne
    apply hVK
    have hXL : ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({ρ b'} : Set (G ⧸ N))), B'.map ρ⁆ ≤
        Subgroup.normalizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      commutator_le_normalizer_of_components
        (fun K hK => (Subgroup.map_mono hB'A).trans (hAK K hK)) hK
    have h := (Coprime.nonfaithful_plane_local_core_product_centralizes_component
      Nat.prime_three hBbE hBbcard (Subgroup.mem_map_of_mem ρ hb') hρb'1 hK hXL hne).1
    exact hVB.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hZK : ∀ x : A, ρ x ∈ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ↔
      (x : G) ∈ Subgroup.zpowers a := by
    intro x
    constructor
    · intro hx
      have hxBZ : (x : G) ∈ B' ⊔ Subgroup.zpowers a := by rw [hBZA]; exact x.2
      obtain ⟨u, hu, w, hw, huw⟩ := Subgroup.mem_sup_of_normal_right.mp hxBZ
      have hρu : ρ u ∈ B'.map ρ ⊓
          Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        refine ⟨Subgroup.mem_map_of_mem ρ hu, ?_⟩
        have h := Subgroup.mul_mem _ hx (Subgroup.inv_mem _
          (Subgroup.center_le_centralizer _ (hρZ w hw)))
        rwa [← huw, map_mul, mul_inv_cancel_right] at h
      rw [hBK, Subgroup.mem_bot] at hρu
      have hu1 : u = 1 := hinj (hB'A hu) A.one_mem (by rw [hρu, map_one])
      rw [← huw, hu1, one_mul]
      exact hw
    · intro hx
      exact Subgroup.center_le_centralizer _ (hρZ _ hx)
  have hfaith : ∀ x ∈ A.map ρ,
      x ∈ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ↔
        x ∈ Subgroup.zpowers (ρ a) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hZK ⟨x, hx⟩]
    constructor
    · intro hxZ
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem _ hxZ
    · intro hxz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hck : a ^ k = x := hinj (A.zpow_mem haA k) hx (by rw [map_zpow, hk])
      subst hck
      exact Subgroup.zpow_mem_zpowers a k
  obtain ⟨η, act, -, hη, hact, -, -, hkerC, -, -⟩ :=
    theta_component_quotient_action Nat.prime_three hL A (hnorm L hL)
  have hker : ∀ x : A, act x = 1 ↔ (x : G) ∈ Subgroup.zpowers a := fun x => by
    rw [hkerC x]
    exact hZK x
  have haT : ∀ (x : A) (hxN : (x : G) ∈ Subgroup.normalizer (L : Set G)),
      act x = thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) := by
    intro x hxN
    ext y
    induction y using QuotientGroup.induction_on with
    | H l =>
      rw [hact x l (L.normalizerMonoidHom ⟨x, hxN⟩ l) (normalizerMonoidHom_apply_coe hxN l),
        thetaQuotMulAut_mk]
  have hAut : autThetaQuot A L = act.range := by
    ext σ
    rw [mem_autThetaQuot_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hA, rfl⟩
      exact ⟨⟨h, hA⟩, haT ⟨h, hA⟩ hN⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, hnorm L hL x.2, x.2, (haT x (hnorm L hL x.2)).symm⟩
  have hcard9 : Nat.card (autThetaQuot A L) = 9 := by
    have hkerZ : act.ker = (Subgroup.zpowers a).subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hcardA := Subgroup.card_eq_card_quotient_mul_card_subgroup act.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange act).toEquiv, hkerZ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv, h27, Nat.card_zpowers,
      hc3] at hcardA
    rw [hAut]
    omega
  have hKX : CFSG.IsKGroup (G ⧸ N) := theta_quotient_isKGroup hS4.kGroup
  have hcbZ : ρ a ∈ Subgroup.center (G ⧸ N) := hρZ a (Subgroup.mem_zpowers a)
  have hcb3 : orderOf (ρ a) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hAe.2 a haA, map_one]) fun h => ha1 ?_
    exact hinj haA A.one_mem (by rw [h, map_one])
  have hBcard9 : Nat.card (B'.map ρ) = 9 := by rw [hBbcard]; norm_num
  have hBZX : B'.map ρ ⊓ Subgroup.zpowers (ρ a) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hyz⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
    have hyc : a ^ k = y := hinj (A.zpow_mem haA k) (hB'A hy) (by rw [map_zpow, hk])
    have hyZ : y ∈ B' ⊓ Subgroup.zpowers a := ⟨hy, hyc ▸ Subgroup.zpow_mem_zpowers a k⟩
    rw [disjoint_iff.mp hBZ, Subgroup.mem_bot] at hyZ
    rw [hyZ, map_one]
    exact Subgroup.one_mem _
  have hABZX : A.map ρ = B'.map ρ ⊔ Subgroup.zpowers (ρ a) := by
    rw [← hBZA, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hrankX : CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ N) ≤ 3 :=
    (theta_quotient_core_and_ranks (G := G)).2.2.1.2.1.trans
      ((((CFSG.Milestones.lc_gl_local_rank_bounds G).1 3 Nat.prime_three (by norm_num)).2).trans
        hS4.evenRank_le)
  have hKFX : ∀ K₁ K₂ : Subgroup (G ⧸ N), IsComponent K₁ → IsComponent K₂ → K₁ ≠ K₂ →
      ∀ w ∈ Subgroup.center K₁, orderOf w = 3 → ∀ σ τ : MulAut K₁, σ w = w → τ w = w →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K₁ →* MulAut K₁).range := by
    intro K₁ K₂ hK₁ hK₂ hK₁₂
    have hKcL : K₁ ≤ Subgroup.centralizer (K₂ : Set (G ⧸ N)) := by
      rcases CFSG.LocalCores.distinct_components_commute hK₁ hK₂ with h | h
      · exact absurd h hK₁₂
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact hKF K₁ (sectionFourHyp_component_of_largePrime h41 hS4 hK₁) hK₁.1
      ((pRank_top_le_localRank_of_le_centralizer hK₂.1 hKcL).trans hrankX)
  have hX := thetaAlpha_autIn_ne_bot_of_fixComm hKFX KFacts.kpSz hθX hKX hcbZ hcb3 hBb
    hBcard9 hBZX hABZX (fun u hu huC => mem_map_of_maximal hmax _
      three_not_dvd_card_aschbacherSolvableCore hu huC) hAK hK hfaith hQ
  have hα : thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ := by
    rw [← thetaAlpha_subgroupOf_map_ne_bot_iff' (MulAut.congr η),
      map_autThetaQuot_eq_autIn hL η hη, map_autThetaQuot_eq_autIn hL η hη,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hAiff⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) :=
    (hAiff V).mpr (hVX.trans (commutator_le_normalizer_of_components hAK hK))
  have hVC : ¬ V ≤ thetaQuotCentralizer L := by
    intro hle
    apply hVK
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_thetaQuotCentralizer_iff_mk hL v).mp (hle hv)
  exact ⟨L, hL, hnorm L hL, hVN, hVC, hcard9, hα, fun y hy =>
    (mem_thetaQuotCentralizer_iff_mk hL y).trans (hZK ⟨y, hy⟩)⟩

end Core

end CFSG.RankThree.PartTwo.Sec4.Item462Proof
