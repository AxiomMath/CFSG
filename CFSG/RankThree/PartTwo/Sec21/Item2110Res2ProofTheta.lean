module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwo
public import CFSG.RankThree.PartTwo.Sec4.Statements426
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec9.Item95
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint

@[expose] def Item2110IData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      d ∈ iOf218 L d ∧
      iOf218 L d ∈ thetaComponentsIn
        (Subgroup.centralizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)) ∧
      inSubgroup (CFSG.pCore 3) (iOf218 L d ⊓ Subgroup.centralizer (iOf218 L d : Set G)) =
        Subgroup.zpowers d ∧
      (Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6)) ∨
        Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover (lBar (iOf218 L d)) NativeSporadic.M22 ∨
        Sec4.IsSLThreePi (lBar (iOf218 L d)))

@[expose] def Item2110JField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, iOf218 L d ≤ J →
      ∀ m : ℕ, 1 ≤ m → Sec4.IsSLThreePiAt (lBar (iOf218 L d)) (2 ^ m) →
        ¬ Sec4.IsSLThreePiAt (lBar J) (2 ^ (3 * m))

@[expose] def Item2110JON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, iOf218 L d ≤ J →
        Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6)) →
        ¬ Sec4.IsTripleCover (lBar J) NativeSporadic.ON

@[expose] def Item2110CentAJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J →
        Nat.card (A ⊓ Sec4.thetaQuotCentralizer J : Subgroup G) = 9 ∧
        (A ⊓ Sec4.thetaQuotCentralizer J) ⊔ (A ⊓ J) = A

namespace Item2110Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_of_mem_thetaComponentsIn₂₁₁₀ (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (hst : PartTwoStanding G) {A : Subgroup G}
    (hAe : IsElemAbelian 3 A) (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {b c : G}
    (hbA : b ∈ A) (hb1 : b ≠ 1) (hcA : c ∈ A) (hc1 : c ≠ 1) {I : Subgroup G}
    (hI : I ∈ thetaComponentsIn
      (Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G)))
    (hIZ : inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) = Subgroup.zpowers b)
    (htype : Sec4.IsTripleCover (lBar I) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (lBar I) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (lBar I) NativeSporadic.M22 ∨ Sec4.IsSLThreePi (lBar I)) :
    ∃ Y ∈ thetaComponentsAt 3 b, I ≤ Y ∧
      (Y = I ⊔ inSubgroup (aschbacherSolvableCore 3) Y ∨
        (∃ m : ℕ, 1 ≤ m ∧ Sec4.IsSLThreePiAt (lBar Y) (2 ^ (3 * m)) ∧
          Sec4.IsSLThreePiAt (lBar I) (2 ^ m)) ∨
        (Sec4.IsTripleCover (lBar Y) NativeSporadic.ON ∧
          Sec4.IsTripleCover (lBar I) (alternatingGroup (Fin 6)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcb : c * b = b * c := hcomm c hcA b hbA
  set D := Subgroup.centralizer ({b} : Set G) with hD
  have hS4 : SectionFourHyp ↥D :=
    hst.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hb1)
  set c' : ↥D := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hcb⟩ with hc'
  set Z₂ := Subgroup.centralizer ({c'} : Set ↥D) with hZ₂
  set CB := Subgroup.centralizer ((Subgroup.closure {c, b} : Subgroup G) : Set G) with hCB
  have hZ₂map : Z₂.map D.subtype = CB := by
    rw [hZ₂, SteinbergBY.map_subtype_centralizer_singleton D c', hCB,
      Subgroup.centralizer_closure]
    ext x
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    tauto
  obtain ⟨hICB, hI₁⟩ := mem_thetaComponentsIn_iff.mp hI
  let ψ : ↥CB ≃* ↥Z₂ := (MulEquiv.subgroupCongr hZ₂map.symm).trans
    (Z₂.equivMapOfInjective D.subtype D.subtype_injective).symm
  have hψ : (D.subtype.comp Z₂.subtype).comp ψ.toMonoidHom = CB.subtype := by
    ext x
    have h1 := (Z₂.equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hZ₂map.symm x)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  set T₂ := (I.subgroupOf CB).map ψ.toMonoidHom with hT₂
  have hT₂mem : T₂ ∈ thetaComponents 3 ↥Z₂ :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three ψ hI₁
  set K' := T₂.map Z₂.subtype with hK'
  have hK'at : K' ∈ thetaComponentsAt 3 c' := ⟨T₂, hT₂mem, rfl⟩
  have hK'map : K'.map D.subtype = I := by
    rw [hK', hT₂, Subgroup.map_map, Subgroup.map_map, hψ,
      Subgroup.map_subgroupOf_eq_of_le hICB]
  have hID : I ≤ D := hK'map ▸ Subgroup.map_subtype_le K'
  have hAD : A ≤ D := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
  have hA'el : IsElemAbelian 3 (A.subgroupOf D) :=
    Sec10.Sec10XProof.isElemAbelian_subgroupOf D hAe
  have hA'card : ∃ n : ℕ, 3 ≤ n ∧ Nat.card (A.subgroupOf D) = 3 ^ n := by
    obtain ⟨n, hn, hAcard⟩ := hAn
    exact ⟨n, hn, by rw [Sec10.Sec10XProof.card_subgroupOf_of_le hAD, hAcard]⟩
  have hc'1 : c' ≠ 1 := fun h1 => hc1 (congrArg Subtype.val h1)
  obtain ⟨X₀, hX₀, hK'X₀⟩ := h48 ↥D hS4 (A.subgroupOf D) hA'el hA'card c'
    (Subgroup.mem_subgroupOf.mpr hcA) hc'1 K' hK'at
  obtain ⟨hK'Z, hK'θ⟩ := PartOne.mem_thetaComponentsAt_iff.mp hK'at
  have hle : K' ≤ X₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D) := le_inf hK'X₀ hK'Z
  have hK'in : K' ∈ thetaComponentsIn (X₀ ⊓ Subgroup.centralizer ({c'} : Set ↥D)) :=
    ⟨K'.subgroupOf _, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle
      inf_le_right hK'θ, Subgroup.map_subgroupOf_eq_of_le hle⟩
  have hc'3 : orderOf c' = 3 :=
    (Subgroup.orderOf_mk c _).trans (orderOf_eq_prime (hAe.2 c hcA) hc1)
  let eK : ↥K' ≃* ↥I :=
    (K'.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hK'map)
  have htype' : Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K')
        (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') NativeSporadic.M22 ∨
      Sec4.IsSLThreePi (K' ⧸ aschbacherSolvableCore 3 K') := by
    rcases htype with h | h | h | h
    · exact Or.inl (Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK).symm h)
    · exact Or.inr (Or.inl (Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK).symm h))
    · exact Or.inr (Or.inr (Or.inl
        (Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK).symm h)))
    · exact Or.inr (Or.inr (Or.inr
        (Sec13.isSLThreePi_of_mulEquiv (Sec14.quotThetaEquiv eK).symm h)))
  have hK'eq : K' = I.subgroupOf D := by
    rw [← hK'map, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hYmap : (K' ⊓ Subgroup.centralizer (K' : Set ↥D)).map D.subtype =
      I ⊓ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.map_inf_eq _ _ D.subtype D.subtype_injective, hK'map, hK'eq,
      Sec10.Sec10XProof.centralizer_subgroupOf hID, Subgroup.subgroupOf_map_subtype,
      inf_comm (Subgroup.centralizer (I : Set G)) D, ← inf_assoc, inf_eq_left.mpr hID]
  have hpmap : (inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D))).map
      D.subtype = inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) := by
    rw [SteinbergBY.map_inSubgroup_pCore_of_injective 3 D.subtype D.subtype_injective, hYmap]
  have hZne' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≠ ⊥ := by
    intro hbot
    have h1 := hpmap
    rw [hbot, Subgroup.map_bot, hIZ] at h1
    apply hb1
    have h2 : b ∈ (⊥ : Subgroup G) := h1 ▸ Subgroup.mem_zpowers b
    exact Subgroup.mem_bot.mp h2
  have hZ' : inSubgroup (CFSG.pCore 3) (K' ⊓ Subgroup.centralizer (K' : Set ↥D)) ≤
      Subgroup.center ↥D := by
    intro w hw
    have hwG : (w : G) ∈ inSubgroup (CFSG.pCore 3) (I ⊓ Subgroup.centralizer (I : Set G)) :=
      hpmap ▸ ⟨w, hw, rfl⟩
    rw [hIZ] at hwG
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwG
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgb : (g : G) * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    simp only [Subgroup.coe_mul, ← hk]
    exact (Commute.zpow_right hgb k).eq
  set Y := X₀.map D.subtype with hY
  have hYmem : Y ∈ thetaComponentsAt 3 b := ⟨X₀, hX₀, rfl⟩
  have hIY : I ≤ Y := hK'map ▸ Subgroup.map_mono hK'X₀
  let eX : ↥X₀ ≃* ↥Y := X₀.equivMapOfInjective D.subtype D.subtype_injective
  refine ⟨Y, hYmem, hIY, ?_⟩
  rcases h426 ↥D hS4 X₀ hX₀ c' hc'3 K' hK'in htype' hZne' hZ' with h1 |
    ⟨m, hm, hX₀m, hK'm⟩ | ⟨hX₀ON, hK'A6⟩
  ·
    left
    have h2 := congrArg (Subgroup.map D.subtype) h1
    rw [Subgroup.map_sup, hK'map, ← inSubgroup_theta_map_subtype] at h2
    exact h2
  ·
    exact Or.inr (Or.inl ⟨m, hm, Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eX) hX₀m,
      Sec9.isSLThreePiAt_of_mulEquiv (Sec14.quotThetaEquiv eK) hK'm⟩)
  ·
    exact Or.inr (Or.inr ⟨Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eX) hX₀ON,
      Sec13.isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv eK) hK'A6⟩)

theorem mem_thetaQuotCentralizer_of_eq_sup {I J : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (J : Set G)) (hcI : ∀ x ∈ I, x * c = c * x)
    (hJI : J = I ⊔ inSubgroup (aschbacherSolvableCore 3) J) :
    c ∈ Sec4.thetaQuotCentralizer J := by
  rw [Sec6.mem_thetaQuotCentralizer_iff]
  refine ⟨hcN, ?_⟩
  set σ := J.normalizerMonoidHom ⟨c, hcN⟩ with hσ
  set θJ := aschbacherSolvableCore 3 J with hθJ
  set T : Subgroup J := MonoidHom.eqLocus ((QuotientGroup.mk' θJ).comp σ.toMonoidHom)
    (QuotientGroup.mk' θJ) with hT
  have hIJ : I ≤ J := by
    rw [hJI]
    exact le_sup_left
  have hIT : I.subgroupOf J ≤ T := by
    intro x hx
    have hσx : σ x = x := by
      apply Subtype.ext
      rw [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← hcI _ (Subgroup.mem_subgroupOf.mp hx), mul_inv_cancel_right]
    show QuotientGroup.mk' θJ (σ x) = QuotientGroup.mk' θJ x
    rw [hσx]
  have hθT : θJ ≤ T := by
    intro x hx
    show ((σ x : J) : J ⧸ θJ) = ((x : J) : J ⧸ θJ)
    have hσx : σ x ∈ θJ := by
      rw [hθJ, ← Sec4.map_aschbacherSolvableCore σ]
      exact ⟨x, hx, rfl⟩
    rw [(QuotientGroup.eq_one_iff (σ x)).mpr hσx, (QuotientGroup.eq_one_iff x).mpr hx]
  have hsup : I.subgroupOf J ⊔ θJ = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hIJ, ← Subgroup.subgroupOf_self,
      Subgroup.map_subgroupOf_eq_of_le le_rfl]
    exact hJI.symm
  have hTtop : T = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le hIT hθT)
  intro l hl
  have hlT : (⟨l, hl⟩ : J) ∈ T := hTtop ▸ Subgroup.mem_top _
  have hlT' : ((⟨l, hl⟩ : J) : J ⧸ θJ) = ((σ ⟨l, hl⟩ : J) : J ⧸ θJ) := hlT.symm
  have h : (⟨l, hl⟩ : J)⁻¹ * σ ⟨l, hl⟩ ∈ θJ := QuotientGroup.eq.mp hlT'
  refine ⟨_, h, ?_⟩
  simp [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem item2110Hyp121_of (h45 : Sec4.Item4_5) (hJ : Item2110JThetaI) (hC : Item2110CentAJ) :
    Item2110Hyp121 := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hdI, J, hJd, hJI⟩ := hJ G A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hB9, hsup⟩ := hC G A E U c L hpair hL d hdA hd1 hdcen J hJd hJI
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe := hpair.mem_S.1.1
  have hAN : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hdA hd1
      J hJd
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  have hIL : iOf218 L d ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  exact ⟨J, hJd, mem_of_jThetaI hdI hJI, mem_thetaQuotCentralizer_of_eq_sup (hAN hcA)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hLc (hIL hx))) hJI, hB9, hsup⟩

section JTheta


theorem item2110JThetaI_of (h211 : Item211) (h48 : Sec4.Item4_8) (h426 : Sec4.Item4_26Theta)
    (hI : Item2110IData) (hF : Item2110JField) (hON : Item2110JON) : Item2110JThetaI := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hdI, hIin, hIZ, htype⟩ := hI G A E U c L hpair hL d hdA hd1 hdcen
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 3 ^ 3 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  obtain ⟨J, hJ, hIJ, hJI | ⟨m, hm, hJm, hIm⟩ | ⟨hJON, hIA6⟩⟩ :=
    exists_mem_of_mem_thetaComponentsIn₂₁₁₀ h48 h426 hpair.standing hAe ⟨3, le_rfl, h27⟩ hdA hd1
      hcA hpairs.2.1 hIin hIZ htype
  · exact ⟨hdI, J, hJ, hJI⟩
  · exact absurd hJm (hF G A E U c L hpair hL d hdA hd1 hdcen J hJ hIJ m hm hIm)
  · exact absurd hJON (hON G A E U c L hpair hL d hdA hd1 hdcen J hJ hIJ hIA6)

theorem item2110Two_of_parts (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (hI : Item2110IData) (hF : Item2110JField)
    (hON : Item2110JON) (hC : Item2110CentAJ) : Item2110Two :=
  item2110Two_of h211 h129
    (item2110Hyp121_of h45 (item2110JThetaI_of h211 h48 h426 hI hF hON) hC)

theorem item2110Three_of_parts (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (hI : Item2110IData) (hF : Item2110JField)
    (hON : Item2110JON) (hC : Item2110CentAJ) (h23 : Item2110TwoThree) : Item2110Three :=
  item2110Three_of (item2110JThetaI_of h211 h48 h426 hI hF hON)
    (item2110ThreeUnique_of (item2110Two_of_parts h211 h45 h48 h426 h129 hI hF hON hC) h23)

theorem jTheta_of_parts (h211 : Item211) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h426 : Sec4.Item4_26Theta) (h129 : Item129Bar) (hI : Item2110IData) (hF : Item2110JField)
    (hON : Item2110JON) (hC : Item2110CentAJ) (h23 : Item2110TwoThree) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
        ∀ J ∈ thetaComponentsAt 3 d, d ∈ J →
          J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J :=
  jTheta_of (item2110JThetaI_of h211 h48 h426 hI hF hON)
    (item2110ThreeUnique_of (item2110Two_of_parts h211 h45 h48 h426 h129 hI hF hON hC) h23)

end JTheta

end Item2110Res2Proof

end CFSG.RankThree.PartTwo.Sec21
