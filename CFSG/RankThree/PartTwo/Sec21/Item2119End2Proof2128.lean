module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Item2119End2Proof

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_zpowers {Q : Subgroup G} (hQ : IsExtraspecialPGroup 3 Q) {d : G} (hdQ : d ∈ Q)
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d) :
    ∀ x ∈ Q, ∀ q ∈ Q, x⁻¹ * (q * x * q⁻¹) ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d' : Q := ⟨d, hdQ⟩
  have hd'c : d' ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have h := hdc q q.2
    show (q : G) * d = d * q
    calc (q : G) * d = (q : G) * d * (q : G)⁻¹ * q := (inv_mul_cancel_right _ _).symm
      _ = d * q := by rw [h]
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hZ : Subgroup.center Q = Subgroup.zpowers d' := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd'c) ?_).symm
    rw [hQ.2.2.2, Nat.card_zpowers, orderOf_eq_prime hd'3 hd'1]
  intro x hx q hq
  set x' : Q := ⟨x, hx⟩
  set q' : Q := ⟨q, hq⟩
  have hc : ⁅x'⁻¹, q'⁆ ∈ Subgroup.center Q := by
    rw [← hQ.2.1, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hZ] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_zpow, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv] at hk'
  rw [show x⁻¹ * (q * x * q⁻¹) = x⁻¹ * q * x * q⁻¹ by group, ← hk']
  exact Subgroup.zpow_mem_zpowers d k

theorem mem_of_isQOf2127 {A F Q : Subgroup G} {d : G} (hA27 : Nat.card A = 27)
    (hF27 : Nat.card F = 27) (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hAF : A ⊔ F ≤ Q)
    (hAF81 : Nat.card (A ⊔ F : Subgroup G) = 81)
    (hQC : Q ⊓ Subgroup.centralizer (A : Set G) = A) (hdA : d ∈ A)
    (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d) : d ∈ F := by
  by_contra hdF
  have hle : F ⊔ Subgroup.zpowers d ≤ A ⊔ F :=
    sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hdA))
  have hlt : F < F ⊔ Subgroup.zpowers d := by
    refine lt_of_le_of_ne le_sup_left fun h => hdF ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have h1 := Subgroup.card_dvd_of_le (le_sup_left : F ≤ F ⊔ Subgroup.zpowers d)
  have h2 := Subgroup.card_dvd_of_le hle
  have h3 := Subgroup.card_lt_of_lt hlt
  rw [hF27] at h1 h3
  rw [hAF81] at h2
  have h81 : Nat.card (F ⊔ Subgroup.zpowers d : Subgroup G) = 81 := by
    obtain ⟨k, hk⟩ := h1
    have hle81 := Nat.le_of_dvd (by norm_num) h2
    rw [hk] at h2 h3 hle81 ⊢
    have hk3 : k = 2 ∨ k = 3 := by omega
    rcases hk3 with rfl | rfl
    · norm_num at h2
    · rfl
  have heq : F ⊔ Subgroup.zpowers d = A ⊔ F :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h81, hAF81])
  have hcent : F ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer (F : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hFc y hy x hx) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h := hdc y ((le_sup_right.trans hAF) hy)
    calc y * d = y * d * y⁻¹ * y := by group
      _ = d * y := by rw [h]
  have hAC : A ≤ Subgroup.centralizer (F : Set G) :=
    (le_sup_left.trans heq.symm.le).trans hcent
  have hFC : F ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hAC hy) x hx).symm
  have hFA : F ≤ A := by
    rw [← hQC]
    exact le_inf (le_sup_right.trans hAF) hFC
  rw [sup_eq_left.mpr hFA, hA27] at hAF81
  norm_num at hAF81

end Item2119End2Proof

open Item2119End2Proof

@[expose] def Item2128Card : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          ∀ e ∈ A, e ∉ Subgroup.zpowers d →
            y2128Of (Lf e) (F e) (q2127Of A d F) ≤ Subgroup.normalizer (F e : Set G) →
            Sec4.autIn (y2128Of (Lf e) (F e) (q2127Of A d F)) (F e) ≤ trivOnQuot (F e) (Lf e) →
            d ∈ F e →
            Nat.card (Sec4.autIn (y2128Of (Lf e) (F e) (q2127Of A d F)) (F e)) = 216

theorem item2128_of (hC : Item2128Card) : Item2128 := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX e he hed
  have hQ' := hQ
  obtain ⟨hFe, hF27, hFle, hAN, -⟩ := hF e he hed
  obtain ⟨hLe, -, hLeU, -, hdLe, -⟩ := hLf e he hed
  obtain ⟨hQS, hQC, hQstar, -, hQ81⟩ := hQ
  set Q := q2127Of A d F with hQdef
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have heA : e ∈ A := he
  have hAFQ : A ⊔ F e ≤ Q := le_iSup₂_of_le e ⟨he, hed⟩ le_rfl
  have hFQ : F e ≤ Q := le_sup_right.trans hAFQ
  have hQN : Q ≤ Subgroup.normalizer (A : Set G) := by
    obtain ⟨S, hS⟩ := hQS
    rw [← hS]
    exact Subgroup.map_subtype_le _
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQstar] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hcommQ := comm_mem_zpowers hQX.1 ((le_sup_left.trans hAFQ) hdA) hd1 hd3 hdc
  have hdF : d ∈ F e :=
    mem_of_isQOf2127 hA27 hF27 hFc hAFQ (hQ81 e he hed).1 hQC hdA hdc
  have hdFz : Subgroup.zpowers d ≤ F e := Subgroup.zpowers_le.mpr hdF
  have hQNF : Q ≤ Subgroup.normalizer (F e : Set G) := by
    intro q hq
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h := hdFz (hcommQ x (hFQ hx) q hq)
    have e1 : q * x * q⁻¹ = x * (x⁻¹ * (q * x * q⁻¹)) := by group
    rw [e1]
    exact (F e).mul_mem hx h
  have ha : y2128Of (Lf e) (F e) Q ≤ Subgroup.normalizer (F e : Set G) :=
    sup_le inf_le_right hQNF
  have hALe : A ≤ Subgroup.normalizer (Lf e : Set G) := by
    intro g hg
    have hge : (MulAut.conj g) e = e := by
      rw [MulAut.conj_apply, hcomm g hg e heA, mul_inv_cancel_right]
    have hK := map_mem_thetaComponentsAt (MulAut.conj g) hLe
    rw [hge] at hK
    have hK3 : 3 ∣ Nat.card ((Lf e).map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact (hLf e he hed).2.1
    have hKeq := hLeU _ hK hK3
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← hKeq]
    exact ⟨y, hy, rfl⟩
  have hFNL : F e ≤ Subgroup.normalizer (Lf e : Set G) :=
    hFle.trans (sup_le hALe Subgroup.le_normalizer)
  set K : Subgroup G := ((trivOnQuot (F e) (Lf e)).comap (F e).normalizerMonoidHom).map
    (Subgroup.normalizer (F e : Set G)).subtype with hKdef
  have hLK : Lf e ⊓ Subgroup.normalizer (F e : Set G) ≤ K := by
    rintro g ⟨hgL, hgN⟩
    refine ⟨⟨g, hgN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_trivOnQuot_iff]
    intro x
    have hx := hFNL x.2
    have h1 : (x : G)⁻¹ * g * x ∈ Lf e := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) g).mp hgL
      simpa [mul_assoc] using this
    have e1 : ((x⁻¹ * (F e).normalizerMonoidHom ⟨g, hgN⟩ x : F e) : G) =
        ((x : G)⁻¹ * g * x) * g⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
      group
    rw [e1]
    exact (Lf e).mul_mem h1 ((Lf e).inv_mem hgL)
  have hQK : Q ≤ K := by
    intro q hq
    refine ⟨⟨q, hQNF hq⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_trivOnQuot_iff]
    intro x
    have e1 : ((x⁻¹ * (F e).normalizerMonoidHom ⟨q, hQNF hq⟩ x : F e) : G) =
        (x : G)⁻¹ * (q * x * q⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    rw [e1]
    exact (Subgroup.zpowers_le.mpr hdLe) (hcommQ x (hFQ x.2) q hq)
  have hYK : y2128Of (Lf e) (F e) Q ≤ K := sup_le hLK hQK
  have hb : Sec4.autIn (y2128Of (Lf e) (F e) Q) (F e) ≤ trivOnQuot (F e) (Lf e) := by
    rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
    obtain ⟨⟨y', hy'N⟩, hy', hyy'⟩ := hYK (Subgroup.mem_subgroupOf.mp hy).1
    have : (⟨y, hyN⟩ : Subgroup.normalizer (F e : Set G)) = ⟨y', hy'N⟩ :=
      Subtype.ext hyy'.symm
    rw [this]
    exact hy'
  refine ⟨ha, hb, ?_⟩
  exact hC G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ' hQX e he hed ha hb hdF

end CFSG.RankThree.PartTwo.Sec21
