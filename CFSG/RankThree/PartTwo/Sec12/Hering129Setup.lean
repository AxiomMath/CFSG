module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
public import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.ClassicalInvolution.SubnormalCommutator
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_inSubgroup_perfectResidual_of_isPerfect {X P : Subgroup G} (hPX : P ≤ X)
    (hP : Group.IsPerfect P) : P ≤ inSubgroup perfectResidual X := by
  have hP' : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have h := (perfect_residual_transport (MonoidHom.id X)).2.2 (P.subgroupOf X) hP'
  have h2 := Subgroup.map_mono (f := X.subtype) h
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPX] at h2

theorem isElemAbelian_of_le_three {A V : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hVA : V ≤ A) : CFSG.Assembly.IsElemAbelian 3 V := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  exact ⟨⟨⟨fun x y => Subtype.ext (hcomm _ (hVA x.2) _ (hVA y.2))⟩⟩, fun x hx => hA.2 x (hVA hx)⟩

theorem card_center_eq_three_of_list {L : Subgroup G} (hty : IsList122 L) :
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
  rcases hty with hSL | hA6 | hA7 | hM22
  · exact card_center_eq_three_of_isSLThreePi hSL
  · exact hA6.1
  · exact hA7.1
  · exact hM22.1

theorem inf_thetaQuotCentralizer_inf_eq {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : IsList122 L) :
    A ⊓ Sec4.thetaQuotCentralizer L ⊓ L = Subgroup.zpowers c := by
  have hZ := card_center_eq_three_of_list hty
  have hB3 : IsPGroup 3 (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
  have hle := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
  rw [hZ] at hle
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcmem : c ∈ A ⊓ Sec4.thetaQuotCentralizer L ⊓ L :=
    ⟨⟨h.mem_A, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩, h.mem_L⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcmem) ?_).symm
  rw [Nat.card_zpowers, hc3]
  exact hle

theorem card_inf_eq_nine_of_list {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : IsList122 L) : Nat.card (A ⊓ L : Subgroup G) = 9 :=
  card_inf_eq_nine_bar h.isE27 h.mem_A h.ne_one h.mem_L
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
    (card_center_eq_three_of_list hty) h.card_B h.sup_eq

theorem mem_normalizer_centralizer_of_commute {a g : G} (h : g * a = a * g) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  change n ∈ Subgroup.centralizer ({a} : Set G) at hn
  change g * n * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
  have h' : a * g⁻¹ = g⁻¹ * a := by
    have h2 : g⁻¹ * (g * a) * g⁻¹ = g⁻¹ * (a * g) * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  calc g * n * g⁻¹ * a = g * n * (g⁻¹ * a) := by group
    _ = g * n * (a * g⁻¹) := by rw [h']
    _ = g * (n * a) * g⁻¹ := by group
    _ = g * (a * n) * g⁻¹ := by rw [hn]
    _ = (g * a) * n * g⁻¹ := by group
    _ = (a * g) * n * g⁻¹ := by rw [h]
    _ = a * (g * n * g⁻¹) := by group

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have hH' : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp hH
  have hK' : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hK
  have h := Subgroup.map_commutator H K (MulAut.conj g).toMonoidHom
  rw [hH', hK'] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h

theorem commutator_closure_eq_zpowers {S B : Subgroup G} {b c : G}
    (hB : Subgroup.closure ({c, b} : Set G) = B) (hSb : S ≤ Subgroup.centralizer ({b} : Set G))
    (hSc : c ∈ Subgroup.normalizer (S : Set G)) : ⁅S, B⁆ = ⁅S, Subgroup.zpowers c⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro s hs x hx
    rw [← hB] at hx
    have hc : ∀ (j : ℤ) (t : G), t ∈ S → c ^ j * t * (c ^ j)⁻¹ ∈ S := fun j t ht =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hSc j) t).mp ht
    have key : ∃ j : ℤ, ∀ t ∈ S, x * t * x⁻¹ = c ^ j * t * (c ^ j)⁻¹ := by
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with rfl | rfl
        · exact ⟨1, fun t _ => by simp⟩
        · refine ⟨0, fun t ht => ?_⟩
          have := Subgroup.mem_centralizer_singleton_iff.mp (hSb ht)
          simp only [zpow_zero, one_mul, inv_one, mul_one]
          rw [← this]
          group
      | one => exact ⟨0, fun t _ => by simp⟩
      | mul y z _ _ ihy ihz =>
        obtain ⟨j, hj⟩ := ihy
        obtain ⟨k, hk⟩ := ihz
        refine ⟨j + k, fun t ht => ?_⟩
        have e1 : y * z * t * (y * z)⁻¹ = y * (z * t * z⁻¹) * y⁻¹ := by group
        rw [e1, hk t ht, hj _ (hc k t ht), zpow_add]
        group
      | inv y _ ihy =>
        obtain ⟨j, hj⟩ := ihy
        refine ⟨-j, fun t ht => ?_⟩
        have h1 := hj (c ^ (-j) * t * (c ^ (-j))⁻¹) (hc (-j) t ht)
        have h2 : c ^ j * (c ^ (-j) * t * (c ^ (-j))⁻¹) * (c ^ j)⁻¹ = t := by
          rw [zpow_neg]
          group
        rw [h2] at h1
        calc y⁻¹ * t * y⁻¹⁻¹ = y⁻¹ * (y * (c ^ (-j) * t * (c ^ (-j))⁻¹) * y⁻¹) * y := by
              rw [h1, inv_inv]
          _ = c ^ (-j) * t * (c ^ (-j))⁻¹ := by group
    obtain ⟨j, hj⟩ := key
    have hs' : s⁻¹ ∈ S := S.inv_mem hs
    have e : ⁅s, x⁆ = ⁅s, c ^ j⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have := hj s⁻¹ hs'
      calc s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
        _ = s * (c ^ j * s⁻¹ * (c ^ j)⁻¹) := by rw [this]
        _ = s * c ^ j * s⁻¹ * (c ^ j)⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
  · exact Subgroup.commutator_mono le_rfl
      (Subgroup.zpowers_le.mpr (hB ▸ Subgroup.subset_closure (Set.mem_insert c _)))

theorem centralizer_zpowers_eq (c : G) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    exact (hx c (Subgroup.mem_zpowers c)).symm
  · intro hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute c x from hx.symm) k)).eq

theorem centralizer_singleton_eq_of_zpowers_eq {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  rw [← centralizer_zpowers_eq a, ← centralizer_zpowers_eq b, h]

theorem not_mem_zpowers_of_lt {A L : Subgroup G} {c b : G} (h : Sec12StdBar G A c L)
    (hb1 : b ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 b)
    (hlt : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))) < K) :
    b ∉ Subgroup.zpowers c := by
  intro hbc
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  have hbA : b ∈ A := (Subgroup.zpowers_le.mpr h.mem_A) hbc
  have hb3 : orderOf b = 3 := orderOf_eq_prime (h.isE27.1.2 b hbA) hb1
  have hzz : Subgroup.zpowers c = Subgroup.zpowers b := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbc) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hb3, hc3]
  have hCeq : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({c} : Set G) :=
    (centralizer_singleton_eq_of_zpowers_eq hzz).symm
  have hthc : thetaComponentsAt 3 b = thetaComponentsAt 3 c := by
    unfold thetaComponentsAt
    rw [hCeq]
  rw [hthc] at hK
  have hL := h.mem_thetaComponentsAt
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hLinf : L ⊓ Subgroup.centralizer ({b} : Set G) = L := by
    rw [hCeq]
    exact inf_eq_left.mpr hLc
  have hLperf := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLle : L ≤ inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))) := by
    refine le_inSubgroup_perfectResidual_of_isPerfect ?_ hLperf
    rw [hLinf]
    exact le_sup_left
  have hLK : L ≤ K := hLle.trans hlt.le
  have hL1 : L ≠ ⊥ := fun h0 => h.ne_one (by simpa [h0] using h.mem_L)
  have heq := Sec6.eq_of_mem_thetaComponentsIn_of_le hL hK hLperf hL1 le_rfl hLK
  rw [← heq] at hlt
  exact absurd (lt_of_le_of_lt hLle hlt) (lt_irrefl L)

theorem exists_refine {A V : Subgroup G} {c : G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hc1 : c ≠ 1) (hVA : V ≤ A) (hV : CFSG.Assembly.IsElemAbelian 3 V)
    (hV9 : Nat.card V = 9) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hSN : A ≤ Subgroup.normalizer (S : Set G)) (hSc : ⁅S, Subgroup.zpowers c⁆ = S) :
    ∃ a ∈ V, a ∉ Subgroup.zpowers c ∧ ∃ S' : Subgroup G, S' ≠ ⊥ ∧ IsPGroup 2 S' ∧
      A ≤ Subgroup.normalizer (S' : Set G) ∧ S' ≤ S ∧ S' ≤ Subgroup.centralizer ({a} : Set G) ∧
      ⁅S', Subgroup.zpowers c⁆ = S' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hcop : ∀ {T : Subgroup G}, IsPGroup 2 T → Nat.Coprime 3 (Nat.card T) := fun {T} hT => by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity (p := 3)
    Nat.prime_three hV (by rw [hV9]; norm_num) (hVA.trans hSN) (hcop hS2)
  obtain ⟨a, haV, ha1, hne⟩ : ∃ a ∈ V, a ≠ 1 ∧
      ⁅S ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hSle : S ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      calc S = ⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1), S ⊓ Subgroup.centralizer ({a} : Set G) :=
            hgen.symm
        _ ≤ _ := iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 =>
            Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon a ha ha1)
    have h0 : ⁅S, Subgroup.zpowers c⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hSle
    exact hS1 (hSc ▸ h0)
  have haA : a ∈ A := hVA haV
  set S₀ : Subgroup G := S ⊓ Subgroup.centralizer ({a} : Set G) with hS₀
  have hS₀2 : IsPGroup 2 S₀ := hS2.to_le inf_le_left
  have hAS₀ : A ≤ Subgroup.normalizer (S₀ : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hSN hy) n).mp hn.1
    · exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer_of_commute (hcomm y hy a haA)) n).mp hn.2
  have hcS₀ : c ∈ Subgroup.normalizer (S₀ : Set G) := hAS₀ hcA
  have hzS₀ : Subgroup.zpowers c ≤ Subgroup.normalizer (S₀ : Set G) :=
    Subgroup.zpowers_le.mpr hcS₀
  set S₁ : Subgroup G := ⁅S₀, Subgroup.zpowers c⁆ with hS₁
  have hS₁S₀ : S₁ ≤ S₀ := by
    rw [hS₁, Subgroup.commutator_le]
    intro u hu g hg
    exact CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hu (hzS₀ hg)
  have hAS₁ : A ≤ Subgroup.normalizer (S₁ : Set G) := fun y hy =>
    mem_normalizer_commutator (hAS₀ hy) (mem_normalizer_zpowers_of_commute (hcomm y hy c hcA))
  have hzS₁ : Subgroup.zpowers c ≤ Subgroup.normalizer (S₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hAS₁ hcA)
  refine ⟨a, haV, ?_, S₁, hne, hS₀2.to_le hS₁S₀, hAS₁, hS₁S₀.trans inf_le_left,
    hS₁S₀.trans inf_le_right, ?_⟩
  · intro hac
    have hzz : Subgroup.zpowers a = Subgroup.zpowers c := by
      have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hac) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hc3]
    have hCeq := centralizer_singleton_eq_of_zpowers_eq hzz
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq, ← hCeq]
    exact inf_le_right
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu g hg
      exact CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hu (hzS₁ hg)
    · have hcop' : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card S₀) := by
        rw [Nat.card_zpowers, hc3]
        exact hcop hS₀2
      exact CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime S₀
        (Subgroup.zpowers c) hzS₀ hcop'

theorem exists_cfg (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : Sec6.BThreePropertyCentral) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G) (hAS : A ∈ partTwoS G)
    (hty : IsList122 L) :
    ∃ (b a : G) (K S : Subgroup G), Cfg129 G A c L b a K S := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.isE27.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcB : c ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨h.mem_A, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩
  have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ Sec4.thetaQuotCentralizer L) :=
    isElemAbelian_of_le_three hAe inf_le_left
  have hLfam : L ∈ thetaComponentFamily 3 A :=
    mem_thetaComponentFamily_iff.mpr ⟨c, h.mem_A, h.ne_one, h.mem_thetaComponentsAt⟩
  have hEcol : A ∈ collectionIn (partTwoE G) (A ⊔ L) := ⟨hAE, le_sup_left⟩
  obtain ⟨b, hbB, hb1, K, hK, hlt6, S, hS, hS1, hSB⟩ :=
    Sec6.rank3II_6_5_one_central h45 h48 h49 hB3 h.toPartTwoStanding hAS hLfam hBe h.card_B
      le_rfl hEcol inf_le_left
  obtain ⟨hSK, hSpi, hSN⟩ := mem_invariantPiSubgroups_iff.mp hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hSpi
  have hbc : b ∉ Subgroup.zpowers c := not_mem_zpowers_of_lt h hb1 hK hlt6
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have hIM : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G))) :=
    le_inSubgroup_perfectResidual_of_isPerfect
      (le_sup_of_le_left (Subgroup.map_subtype_le _))
      (Sec6.isPerfect_inSubgroup_perfectResidual _)
  have hlt : ¬ (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K = K) := by
    intro heq
    have hKM : K ≤ (L ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
      rw [← heq]
      refine sup_le (le_sup_of_le_left (Subgroup.map_subtype_le _)) (le_sup_of_le_right ?_)
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right
    have h2 := le_inSubgroup_perfectResidual_of_isPerfect hKM
      (Sec6.isPerfect_of_mem_thetaComponentsAt hK)
    exact absurd (lt_of_le_of_lt h2 hlt6) (lt_irrefl K)
  have hbc' : b ∉ Subgroup.zpowers c := hbc
  have hBeq : Subgroup.closure ({c, b} : Set G) = A ⊓ Sec4.thetaQuotCentralizer L :=
    closure_pair_eq_of_card_nine (fun x hx => hAe.2 x (Subgroup.mem_inf.mp hx).1) h.card_B hcB
      h.ne_one hbB hbc'
  have hSc : ⁅S, Subgroup.zpowers c⁆ = S :=
    (commutator_closure_eq_zpowers hBeq (hSK.trans hKb) (hSN h.mem_A)).symm.trans hSB
  obtain ⟨a, haV, ha_not, S', hS'1, hS'2, hS'N, hS'S, hS'a, hS'c⟩ :=
    exists_refine hAe h.mem_A h.ne_one (inf_le_left : A ⊓ L ≤ A)
      (isElemAbelian_of_le_three hAe inf_le_left) (card_inf_eq_nine_of_list h hty) hS2 hS1 hSN hSc
  refine ⟨b, a, K, S', ⟨h, hAE, hAS, hty, hbB, hbc, hK, hIM.trans hlt6.le, hlt, haV, ha_not,
    hS'S.trans hSK, hS'2, hS'1, hS'N, ?_, hS'c⟩⟩
  rw [D129, Subgroup.le_centralizer_iff]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS'a hs)
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKb (hSK (hS'S hs)))

theorem exists_stab_ne_one {A : Subgroup G} {c x : G} (hcA : c ∈ A) (hxA : x ∈ A)
    (hc3 : orderOf c = 3) (hT9 : Nat.card (transvectionGroup A ⟨c, hcA⟩) = 9) :
    ∃ σ ∈ transvectionGroup A ⟨c, hcA⟩, σ ≠ 1 ∧ σ ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
  set T := transvectionGroup A ⟨c, hcA⟩ with hT
  set x₀ : A := ⟨x, hxA⟩ with hx₀
  set c₀ : A := ⟨c, hcA⟩ with hc₀
  have hc₀3 : orderOf c₀ = 3 := by rw [hc₀, Subgroup.orderOf_mk]; exact hc3
  have hidx : (MulAction.stabilizer T x₀).index = Nat.card (MulAction.orbit T x₀) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have horb := Subgroup.index_mul_card (MulAction.stabilizer T x₀)
  rw [hidx, hT9] at horb
  have hle : Nat.card (MulAction.orbit T x₀) ≤ 3 := by
    have hmem : ∀ y : MulAction.orbit T x₀, y.1 * x₀⁻¹ ∈ Subgroup.zpowers c₀ := by
      rintro ⟨_, ⟨⟨σ, hσ⟩, rfl⟩⟩
      exact hσ.2 x₀
    let f : MulAction.orbit T x₀ → Subgroup.zpowers c₀ := fun y => ⟨y.1 * x₀⁻¹, hmem y⟩
    have hf : Function.Injective f := fun y z hyz => by
      apply Subtype.ext
      exact mul_right_cancel (congrArg Subtype.val hyz)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_zpowers, hc₀3] at this
  have h3 : 3 ≤ Nat.card (MulAction.stabilizer T x₀) := by
    set o := Nat.card (MulAction.orbit T x₀)
    set s := Nat.card (MulAction.stabilizer T x₀)
    by_contra hlt
    push Not at hlt
    have : o * s ≤ 3 * 2 := Nat.mul_le_mul hle (by omega)
    omega
  have hne : MulAction.stabilizer T x₀ ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨σ, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(σ : T), (σ : T).2, ?_, ?_⟩
  · intro h1
    apply hσ1
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  · exact σ.2

theorem exists_transvection_fixing (h45 : Sec4.Item4_5) (hK : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hty : IsList122 L) {x : G}
    (hxA : x ∈ A) :
    ∃ g : G, g ∈ Subgroup.normalizer (A : Set G) ∧ IsPGroup 3 (Subgroup.zpowers g) ∧
      g * x * g⁻¹ = x ∧ g * c * g⁻¹ = c ∧ (∃ y ∈ A, g * y * g⁻¹ ≠ y) ∧
      ∀ y ∈ A, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨P, hP, hPB⟩ := h.exists_sylow
  have hZ := card_center_eq_three_of_list hty
  obtain ⟨hPaut, hP9⟩ := autIn_eq_transvectionGroup_bar h45 h hZ
    (fun T hT hT9 hZT => hK _ (isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt) hty T hT
      hT9 hZT) hP hPB
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  have hT9' : Nat.card (transvectionGroup A ⟨c, h.mem_A⟩) = 9 := hPaut ▸ hP9
  obtain ⟨σ, hσT, hσ1, hσx⟩ := exists_stab_ne_one h.mem_A hxA hc3 hT9'
  have hσP : σ ∈ Sec4.autIn P A := hPaut ▸ hσT
  obtain ⟨g, hgN, hgP, hgσ⟩ := Sec4.mem_autIn_iff.mp hσP
  have hσcoe : ∀ y : A, ((σ y : A) : G) = g * (y : G) * g⁻¹ := fun y => by
    rw [← hgσ]
    exact Sec4.normalizerMonoidHom_apply_coe hgN y
  refine ⟨g, hgN, hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hgP), ?_, ?_, ?_, ?_⟩
  · have h1 := congrArg Subtype.val hσx
    rw [hσcoe] at h1
    exact h1
  · have h1 := congrArg Subtype.val hσT.1
    rw [hσcoe] at h1
    exact h1
  · by_contra hcon
    push Not at hcon
    apply hσ1
    ext y
    exact hσcoe y ▸ hcon y y.2
  · intro y hy
    have h1 := hσT.2 ⟨y, hy⟩
    have h2 := Subgroup.mem_map_of_mem A.subtype h1
    rw [MonoidHom.map_zpowers] at h2
    simpa [hσcoe] using h2

theorem mem_of_mem_zpowers_of_ne_one {c z : G} {R : Subgroup G} (hc3 : orderOf c = 3)
    (hz : z ∈ Subgroup.zpowers c) (hz1 : z ≠ 1) (hzR : z ∈ R) : c ∈ R := by
  have hz3 : z ^ 3 = 1 := by
    rw [← hc3]
    exact CFSG.RankThree.pow_orderOf_eq_one_of_mem_zpowers hz
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hzo]
  have : c ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr hzR) this

theorem core129_of (h45 : Sec4.Item4_5) (hK : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hty : IsList122 L) {x : G}
    (hxA : x ∈ A) (hx1 : x ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x)
    (hYc : ⁅Y, Subgroup.zpowers c⁆ = Y) : Core129 A c x Y := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.isE27.1
  have hA27 : Nat.card A = 27 := h.isE27.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hAe.2 x hxA) hx1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c h.mem_A) h.ne_one
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG hx3 hY hA3 fun y hy =>
      mem_normalizer_zpowers_of_commute (hcomm y hy x hxA)
  refine ⟨hY, hAN, ?_, hYc⟩
  set R := A ⊓ Sec4.thetaQuotCentralizer Y with hR
  have hxR : x ∈ R := ⟨hxA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hY⟩
  have hcR : c ∉ R := by
    intro hcR
    have hzY : Subgroup.zpowers c ≤ Sec4.thetaQuotCentralizer Y :=
      Subgroup.zpowers_le.mpr hcR.2
    have hle : ⁅Y, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
      refine Subgroup.commutator_le.mpr fun l hl g hg => ?_
      have := (Sec6.mem_thetaQuotCentralizer_iff.mp (hzY hg)).2 l⁻¹ (Y.inv_mem hl)
      simpa [commutatorElement_def, mul_assoc] using this
    rw [hYc] at hle
    exact Sec6.theta_ne_of_mem_thetaComponentsAt hY (le_antisymm (Sec6.theta_le Y) hle)
  obtain ⟨g, hgA, hg3, hgx, hgc, ⟨y₀, hy₀A, hy₀⟩, hgcomm⟩ :=
    exists_transvection_fixing h45 hK h hty hxA
  have hgxc : g * x = x * g := by
    have := congrArg (· * g) hgx
    simpa [mul_assoc] using this
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG hx3 hY hg3
      (Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_commute hgxc)) (Subgroup.mem_zpowers g)
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_inf_thetaQuotCentralizer hgA hgY
  have hfix : ∀ y ∈ R, g * y * g⁻¹ = y := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgR y).mp hy
    have h2 : g * y * g⁻¹ * y⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hy)
    by_contra hne
    have hne' : g * y * g⁻¹ * y⁻¹ ≠ 1 := fun h' => hne (mul_inv_eq_one.mp h')
    exact hcR (mem_of_mem_zpowers_of_ne_one hc3 (hgcomm y hy.1) hne' h2)
  set F : Subgroup G := A ⊓ Subgroup.centralizer ({g} : Set G) with hF
  have hmemF : ∀ y ∈ A, y ∈ F ↔ g * y * g⁻¹ = y := fun y hy => by
    constructor
    · intro hyF
      have := Subgroup.mem_centralizer_singleton_iff.mp hyF.2
      rw [← this]
      group
    · intro hgy
      refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg (· * g) hgy
      simpa [mul_assoc] using this.symm
  have hF9 : Nat.card F ≤ 9 := by
    have hdvd : Nat.card F ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · exfalso
      have hFA : F = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA27]; norm_num)
      exact hy₀ ((hmemF y₀ hy₀A).mp (hFA ▸ hy₀A))
  have hRF : R ≤ F := fun y hy => (hmemF y hy.1).mpr (hfix y hy)
  have hcF : c ∈ F := (hmemF c h.mem_A).mpr hgc
  have hRe : CFSG.Assembly.IsElemAbelian 3 R := isElemAbelian_of_le_three hAe inf_le_left
  have hcRc : c ∈ Subgroup.centralizer (R : Set G) := Subgroup.mem_centralizer_iff.mpr fun y hy =>
    hcomm y hy.1 c h.mem_A
  have hdisj : R ⊓ Subgroup.zpowers c = ⊥ := inf_zpowers_eq_bot_of_not_mem hc3 hcR
  obtain ⟨hRc, -, -⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint hcRc hRe.1 hRe.2 hc3 hdisj
  have hRcF : R ⊔ Subgroup.zpowers c ≤ F := sup_le hRF (Subgroup.zpowers_le.mpr hcF)
  have hR3 : Nat.card R ≤ 3 := by
    have := Subgroup.card_le_of_le hRcF
    rw [hRc] at this
    omega
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxR) ?_).symm
  rw [Nat.card_zpowers, hx3]
  exact hR3

theorem Cfg129.point_facts {A L K S : Subgroup G} {c b a : G} (cfg : Cfg129 G A c L b a K S) :
    b ∈ A ∧ a ∈ A ∧ a ∈ L ∧ b ≠ 1 ∧ a ≠ 1 ∧ a ∉ Sec4.thetaQuotCentralizer L ∧ b ∉ L ∧
      a ∉ Subgroup.zpowers b ∧ a ∈ D129 a b ∧ a * b ∈ D129 a b ∧ a * b ∉ Subgroup.zpowers b ∧
      a * b ∉ L ∧ a * b ∉ Sec4.thetaQuotCentralizer L ∧ a * b ∈ A ∧ a * b ≠ 1 := by
  have hbB : b ∈ A ⊓ Sec4.thetaQuotCentralizer L := cfg.hb
  have hbA : b ∈ A := hbB.1
  have haA : a ∈ A := cfg.ha.1
  have haL : a ∈ L := cfg.ha.2
  have hBL := inf_thetaQuotCentralizer_inf_eq cfg.std cfg.list
  have hb1 : b ≠ 1 := fun h1 => cfg.hb_not (h1 ▸ Subgroup.one_mem _)
  have haB : a ∉ Sec4.thetaQuotCentralizer L := fun hB' =>
    cfg.ha_not (hBL ▸ (⟨⟨haA, hB'⟩, haL⟩ : a ∈ A ⊓ Sec4.thetaQuotCentralizer L ⊓ L))
  have hbL : b ∉ L := fun hbL' =>
    cfg.hb_not (hBL ▸ (⟨hbB, hbL'⟩ : b ∈ A ⊓ Sec4.thetaQuotCentralizer L ⊓ L))
  have hab : a ∉ Subgroup.zpowers b := fun h' => haB ((Subgroup.zpowers_le.mpr hbB.2) h')
  have haD : a ∈ D129 a b := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbD : b ∈ D129 a b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hxb : a * b ∉ Subgroup.zpowers b := fun h' =>
    hab (by simpa using Subgroup.mul_mem _ h' (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)))
  have hxL : a * b ∉ L := fun h' => hbL (by simpa using L.mul_mem (L.inv_mem haL) h')
  have hxB : a * b ∉ Sec4.thetaQuotCentralizer L := fun h' => by
    have h2 := (Sec4.thetaQuotCentralizer L).mul_mem h'
      ((Sec4.thetaQuotCentralizer L).inv_mem hbB.2)
    exact haB (by simpa using h2)
  exact ⟨hbA, haA, haL, hb1, fun h1 => hab (h1 ▸ Subgroup.one_mem _), haB, hbL, hab, haD,
    Subgroup.mul_mem _ haD hbD, hxb, hxL, hxB, A.mul_mem haA hbA,
    fun h1 => hxb (h1 ▸ Subgroup.one_mem _)⟩

end CFSG.RankThree.PartTwo.Sec12
