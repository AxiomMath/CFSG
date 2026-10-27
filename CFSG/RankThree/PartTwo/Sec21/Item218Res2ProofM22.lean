module

public import CFSG.RankThree.PartTwo.Sec21.Item218ProofM22
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
import CFSG.RankThree.PartTwo.KFacts.KS12Moves

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item218Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem not_le_normalizer_of_isTripleCover
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hT : Sec4.IsTripleCover (lBar L) Blueprint.NativeSporadic.M22) {d : G} (hdA : d ∈ A)
    (hdc : d ∉ Subgroup.zpowers c) :
    ¬ (L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcE : c ∈ E := hpairs.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hcE
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAF : A ∈ partTwoF G := hpair.mem_S.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hexpA a a.2)⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c hcA) hc1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hG4 : TheoremFourHyp G := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
    exact SetLike.coe_injective hsc
  have hLperf : commutator (lBar L) = ⊤ := by
    have h1 := (Sec12.isQuasisimple_thetaQuot_of_mem hLc).1
    rwa [Group.isPerfect_def] at h1
  have hmax : ∀ z : G, z ^ 3 = 1 → (∀ a ∈ A, a * z = z * a) → z ∈ A := fun z hz3 hz => by
    have hab := Item211Proof.isElemAbelian_sup_zpowers hAe hz3 hz
    have heq := hAF.2.1 _ hab le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hAut3 : ∀ X : Subgroup G, IsPGroup 3 X → IsPGroup 3 (Sec4.autThetaQuot X L) := by
    intro X hX
    have h1 : IsPGroup 3 ((X ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
        (Subgroup.normalizer (L : Set G))) := (hX.to_le inf_le_left).comap_subtype
    exact (h1.map _).map _
  have hle9 : ∀ X : Subgroup G, IsPGroup 3 X → Nat.card (Sec4.autThetaQuot X L) ≤ 9 :=
    fun X hX => Item2117Proof.card_le_nine_of_isPGroup hLperf hT (hAut3 X hX)
  have hkA := Sec13.card_inf_mul_card_autThetaQuot hAL
  rw [hCA, Nat.card_zpowers, hc3] at hkA
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have h27le : 27 ≤ Nat.card A := hE27 ▸ Subgroup.card_le_of_le hpair.mem_E.2
  have hA9 := hle9 A hA3
  have hA27 : Nat.card A = 27 := by omega
  have hAut9 : Nat.card (Sec4.autThetaQuot A L) = 9 := by omega
  have hAutEq : ∀ X : Subgroup G, IsPGroup 3 X → A ≤ X →
      Sec4.autThetaQuot X L = Sec4.autThetaQuot A L := fun X hX hAX =>
    (Subgroup.eq_of_le_of_card_ge (Sec13.autThetaQuot_mono hAX L)
      (by rw [hAut9]; exact hle9 X hX)).symm
  set K : Subgroup G := L ⊔ A with hK
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hAL
  obtain ⟨Q₀, hQ₀⟩ := (hA3.comap_subtype (K := K)).exists_le_sylow
  set Q : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hQdef
  have hQ : IsSylowOf 3 Q K := ⟨Q₀, rfl⟩
  have hAQ : A ≤ Q := fun a ha =>
    ⟨⟨a, le_sup_right (a := L) ha⟩, hQ₀ (Subgroup.mem_comap.mpr ha), rfl⟩
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  set S : Subgroup G := Q ⊓ L with hSdef
  have hS : IsSylowOf 3 S L := hQ.inf_of_le_normalizer le_sup_left hKN
  have hS27 : Nat.card S = 27 := by
    rw [hS.card_eq, Item2117Proof.factorization_card_eq_three hT]
    norm_num
  have hS3 : IsPGroup 3 S := hS.isPGroup
  have hSL : S ≤ L := inf_le_right
  have hSQ : S ≤ Q := inf_le_left
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := hSL.trans Subgroup.le_normalizer
  have hAS : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs =>
    ⟨Q.mul_mem (Q.mul_mem (hAQ ha) hs.1) (Q.inv_mem (hAQ ha)),
      (Subgroup.mem_normalizer_iff.mp (hAL ha) s).mp hs.2⟩
  have hAutQ := hAutEq Q hQ3 hAQ
  have hAutSle : Sec4.autThetaQuot S L ≤ Sec4.autThetaQuot A L :=
    hAutQ ▸ Sec13.autThetaQuot_mono hSQ L
  have hkS := Sec13.card_inf_mul_card_autThetaQuot hSN
  rw [hS27] at hkS
  have hSC3le : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≤ 3 := by
    have h1 := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer
      (hS3.to_le inf_le_left) (inf_le_right : S ⊓ Sec4.thetaQuotCentralizer L ≤ _)
    rwa [inf_eq_left.mpr (inf_le_left.trans hSL), hT.1] at h1
  have hAutS9le : Nat.card (Sec4.autThetaQuot S L) ≤ 9 :=
    (Subgroup.card_le_of_le hAutSle).trans hAut9.le
  have hSC3 : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    have hpos : 0 < Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := Nat.card_pos
    interval_cases h : Nat.card (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) <;> omega
  have hAutS9 : Nat.card (Sec4.autThetaQuot S L) = 9 := by
    rw [hSC3] at hkS
    omega
  have hAutS : Sec4.autThetaQuot S L = Sec4.autThetaQuot A L :=
    Subgroup.eq_of_le_of_card_ge hAutSle (by rw [hAut9, hAutS9])
  have hSCeq : S ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    obtain ⟨z, hz⟩ : ∃ z : (S ⊓ Sec4.thetaQuotCentralizer L : Subgroup G), orderOf z = 3 :=
      exists_prime_orderOf_dvd_card' 3 (by rw [hSC3])
    have hz3 : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have hZeq : Subgroup.zpowers (z : G) = S ⊓ Sec4.thetaQuotCentralizer L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2)
        (by rw [hSC3, Nat.card_zpowers, hz3])
    have hzA : (z : G) ∈ A := hmax z (by rw [← hz3]; exact pow_orderOf_eq_one _) fun a ha => by
      have hconj : a * z * a⁻¹ ∈ Subgroup.zpowers (z : G) := by
        rw [hZeq]
        exact ⟨hAS a ha z z.2.1, Sec12.conj_mem_thetaQuotCentralizer (hAL ha) z.2.2⟩
      exact Sec12.commute_of_conj_mem_zpowers hz3 hconj (k := 1)
        (by rw [pow_one]; exact hexpA a ha)
    have hzc : Subgroup.zpowers (z : G) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hc3])
      rw [Subgroup.zpowers_le, ← hCA]
      exact ⟨hzA, z.2.2⟩
    rw [← hZeq, hzc]
  have hcSC : c ∈ S ⊓ Sec4.thetaQuotCentralizer L := by
    rw [hSCeq]
    exact Subgroup.mem_zpowers c
  have hcS : c ∈ S := hcSC.1
  have hcL : c ∈ L := hcS.2
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := hcSC.2
  have hφS : ∀ s (hs : s ∈ S), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨s, hSN hs⟩) ∈
      Sec4.autThetaQuot A L := fun s hs => by
    rw [← hAutS]
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨s, hSN hs, hs, rfl⟩
  have hcommS : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := fun s hs a ha => by
    rw [← hSCeq]
    refine ⟨?_, Item2117Proof.comm_mem_thetaQuotCentralizer hcommA hAL (hSN hs) (hφS s hs) ha⟩
    have h1 : a * s⁻¹ * a⁻¹ ∈ S := hAS a ha _ (S.inv_mem hs)
    have h2 : s * a * s⁻¹ * a⁻¹ = s * (a * s⁻¹ * a⁻¹) := by group
    rw [h2]
    exact S.mul_mem hs h1
  have hSA : S ≤ Subgroup.normalizer (A : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun a ha => by
      have h1 : s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
      rw [h1]
      exact A.mul_mem ((Subgroup.zpowers_le.mpr hcA) (hcommS s hs a ha)) ha
  have hSnc : ¬ IsMulCommutative S := by
    intro hcomm
    obtain ⟨S₀, hS₀⟩ := hS.exists_sylow_eq_subgroupOf
    have hLperf' : commutator L = ⊤ := by
      have h1 := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
      rwa [Group.isPerfect_def] at h1
    have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2))
    have hc3' : orderOf (⟨c, hcL⟩ : L) = 3 := by rw [Subgroup.orderOf_mk]; exact hc3
    apply KFacts.not_isMulCommutative_sylow_of_perfect hLperf' hcZ hc3' S₀
    rw [hS₀]
    refine ⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩
    have hx : ((x : L) : G) ∈ S := Subgroup.mem_subgroupOf.mp x.2
    have hy : ((y : L) : G) ∈ S := Subgroup.mem_subgroupOf.mp y.2
    have h := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simpa using h
  have hZS : Nat.card (Subgroup.center S) = 3 :=
    Item2117Proof.card_center_eq_three_of_card_eq hS27 hSnc
  have hcZS : (⟨c, hcS⟩ : S) ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun s =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC (hSL s.2)))
  have hZSeq : Subgroup.zpowers (⟨c, hcS⟩ : S) = Subgroup.center S := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZS) ?_
    rw [hZS, Nat.card_zpowers, Subgroup.orderOf_mk, hc3]
  have hnondeg : ∀ x ∈ A, (∀ s ∈ S, s * x = x * s) → x ∈ Subgroup.zpowers c := by
    intro x hx hxS
    have hxφ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hAL hx⟩) ∈
        Sec4.autThetaQuot S L := by
      rw [hAutS]
      exact Sec4.mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩
    obtain ⟨s₀, hs₀N, hs₀S, hs₀⟩ := Sec4.mem_autThetaQuot_iff.mp hxφ
    set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
    have hk : s₀⁻¹ * x ∈ Sec4.thetaQuotCentralizer L := by
      refine ⟨(⟨s₀, hs₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hAL hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      change φ ((⟨s₀, hs₀N⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hAL hx⟩) = 1
      rw [map_mul, map_inv]
      rw [show φ ⟨s₀, hs₀N⟩ = φ ⟨x, hAL hx⟩ from hs₀, inv_mul_cancel]
    have hkQ : s₀⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hSQ hs₀S)) (hAQ hx)
    have hkS : ∀ s ∈ S, Commute s (s₀⁻¹ * x) := by
      intro s hs
      have h1 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈
          inSubgroup (aschbacherSolvableCore 3) L :=
        (Sec6.mem_thetaQuotCentralizer_iff.mp hk).2 s (hSL hs)
      have h2 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈ Q :=
        Q.mul_mem (Q.inv_mem (hSQ hs)) (Q.mul_mem (Q.mul_mem hkQ (hSQ hs)) (Q.inv_mem hkQ))
      have h3 : s⁻¹ * ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) ∈ (⊥ : Subgroup G) := by
        rw [← Sec12.inf_inSubgroup_theta_eq_bot hQ3 (L := L)]
        exact ⟨h2, h1⟩
      rw [Subgroup.mem_bot] at h3
      have h4 : (s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹ = s := (inv_mul_eq_one.mp h3).symm
      change s * (s₀⁻¹ * x) = (s₀⁻¹ * x) * s
      calc s * (s₀⁻¹ * x) = ((s₀⁻¹ * x) * s * (s₀⁻¹ * x)⁻¹) * (s₀⁻¹ * x) := by rw [h4]
        _ = (s₀⁻¹ * x) * s := by group
    have hs₀Z : (⟨s₀, hs₀S⟩ : S) ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun s => by
      apply Subtype.ext
      change (s : G) * s₀ = s₀ * s
      have hc1' : Commute (s : G) x := hxS s s.2
      have hc2' : Commute (s : G) (s₀⁻¹ * x) := hkS s s.2
      have hc3' : Commute (s : G) (x * (s₀⁻¹ * x)⁻¹) := hc1'.mul_right hc2'.inv_right
      rw [show x * (s₀⁻¹ * x)⁻¹ = s₀ by group] at hc3'
      exact hc3'.eq
    rw [← hZSeq] at hs₀Z
    have hs₀c : s₀ ∈ Subgroup.zpowers c := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs₀Z
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hs₀C : s₀ ∈ Sec4.thetaQuotCentralizer L := (Subgroup.zpowers_le.mpr hcC) hs₀c
    have hxC : x ∈ Sec4.thetaQuotCentralizer L := by
      have h1 := (Sec4.thetaQuotCentralizer L).mul_mem hs₀C hk
      rwa [mul_inv_cancel_left] at h1
    rw [← hCA]
    exact ⟨hx, hxC⟩
  intro hLd
  obtain ⟨s, hsS, hsd⟩ : ∃ s ∈ S, s * d ≠ d * s := by
    by_contra hcon
    push Not at hcon
    exact hdc (hnondeg d hdA hcon)
  have hsN : s ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := hLd ⟨hSL hsS, hSA hsS⟩
  have h1 : s * d * s⁻¹ * d⁻¹ ∈ Subgroup.zpowers c := hcommS s hsS d hdA
  have h2 : s * d * s⁻¹ * d⁻¹ ∈ Subgroup.zpowers d :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hsN d).mp (Subgroup.mem_zpowers d))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
  have h3 : s * d * s⁻¹ * d⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← Sec13.zpowers_inf_eq_bot (hexpA d hdA) hdc]
    exact ⟨h2, h1⟩
  rw [Subgroup.mem_bot] at h3
  apply hsd
  calc s * d = (s * d * s⁻¹ * d⁻¹) * d * s := by group
    _ = d * s := by rw [h3, one_mul]

end CFSG.RankThree.PartTwo.Sec21.Item218Res2Proof
