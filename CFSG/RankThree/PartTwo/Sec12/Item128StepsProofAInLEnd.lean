module

public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofCaseA
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item128StepsProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open Item125BarTC

variable {G : Type} [Group G] [Finite G]

theorem mk_pow_three_eq_one_of_fixer {c : G} {L E : Subgroup G}
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hE : Late.IsE27 E) (hEN : E ≤ Subgroup.normalizer (L : Set G))
    {a : G} (haE : a ∈ E) (hcE : c ∈ E) (hcC : c ∈ Sec4.thetaQuotCentralizer L)
    {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (had : thetaBarAct L ⟨a, hEN haE⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩))
    (hfix : ∀ e ∈ E, e ∈ Item125Diag.fixer L
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) →
      e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    {e : G} (heE : e ∈ E) {l : G} (hl : l ∈ L) {z : G} (hz : z ∈ Sec4.thetaQuotCentralizer L)
    (hlz : e = l * z) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩ ^ 3 = 1 := by
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  set db := π ⟨d, hdL⟩ with hdb
  set xb := π ⟨l, hl⟩ with hxb
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb :=
    thetaBarAct_eq_conj hl hz hlz (hEN heE)
  have hx3Z : xb ^ 3 ∈ Subgroup.center (L ⧸ N) :=
    mk_pow_three_mem_center (hEN heE) (hE.1.2 e heE) hφe
  by_contra hx1
  have hcomm : thetaBarAct L ⟨a, hEN haE⟩ * thetaBarAct L ⟨e, hEN heE⟩ =
      thetaBarAct L ⟨e, hEN heE⟩ * thetaBarAct L ⟨a, hEN haE⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc a haE e heE)
  rw [had, hφe] at hcomm
  have hdx : db * xb * db⁻¹ * xb⁻¹ ∈ Subgroup.center (L ⧸ N) := by
    apply mem_center_of_conj_eq_one
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hdx' := conj_eq_of_mul_inv_mem_center hSL hx3Z hx1 hdx
  have heF : e ∈ Item125Diag.fixer L db := by
    rw [Item125Diag.mem_fixer_iff]
    refine ⟨hEN heE, ?_⟩
    rw [hφe, MulAut.conj_apply]
    have hdx2 : db * xb = xb * db := by
      calc db * xb = db * xb * db⁻¹ * db := by group
        _ = xb * db := by rw [hdx']
    rw [← hdx2, mul_inv_cancel_right]
  obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup (hEc a haE c hcE) (hfix e heE heF)
  have haN := hEN haE
  have hcN := hEN hcE
  have hσ : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj (db ^ i) := by
    have h1 : (⟨e, hEN heE⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ i * (⟨c, hcN⟩) ^ k :=
      Subtype.ext (by simp [hik])
    rw [h1, map_mul, map_zpow, map_zpow, had,
      (mem_thetaQuotCentralizer_iff_thetaBarAct hcN).mp hcC, one_zpow, mul_one, map_zpow]
  rw [hφe] at hσ
  have hw : xb * (db ^ i)⁻¹ ∈ Subgroup.center (L ⧸ N) := by
    apply mem_center_of_conj_eq_one
    rw [map_mul, map_inv, hσ, mul_inv_cancel]
  apply hx1
  have hw3 : (xb * (db ^ i)⁻¹) ^ 3 = 1 := by
    have h3 : (⟨_, hw⟩ : Subgroup.center (L ⧸ N)) ^ 3 = 1 := by
      have h0 := pow_card_eq_one' (x := (⟨_, hw⟩ : Subgroup.center (L ⧸ N)))
      rwa [hZ] at h0
    have h4 := congrArg Subtype.val h3
    simpa using h4
  have hdb3 : (db ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdb, ← map_pow]
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one, one_zpow]
  have hcw : Commute (xb * (db ^ i)⁻¹) (db ^ i) :=
    (Subgroup.mem_center_iff.mp hw (db ^ i)).symm
  calc xb ^ 3 = ((xb * (db ^ i)⁻¹) * db ^ i) ^ 3 := by group
    _ = 1 := by rw [hcw.mul_pow, hw3, hdb3, one_mul]

theorem false_of_transitive_of_not_mem (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hK9 : KFacts.KS12OrderNine) (hKT : KS125TypeCInvol)
    (hD : Item125Diag) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (haA : a ∈ A) (haC : a ∉ Sec4.thetaQuotCentralizer L) (haL : a ∉ L)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K)
    {F : Subgroup G} (hFK : F ≤ K) (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hcF : c ∈ F)
    (hT : ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v)
    (hR : ∀ f ∈ F, ∀ hfN : f ∈ Subgroup.normalizer (L : Set G),
      (¬ ∃ y : L ⧸ aschbacherSolvableCore 3 L, thetaBarAct L ⟨f, hfN⟩ = MulAut.conj y) →
      ∀ d : G, d ∈ A → ∀ hdL : d ∈ L, a * d⁻¹ ∈ Sec4.thetaQuotCentralizer L →
        thetaBarAct L ⟨f, hfN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) ≠
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ → a ∈ L) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hcL := h.mem_L
  have hc1 := h.ne_one
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.isE27.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c h.mem_A) hc1
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have haF : a ∉ F := fun h1 => haK (hFK h1)
  have hFa : ∀ y ∈ F, a * y = y * a := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKa (hFK hy))).symm
  obtain ⟨hEab, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine ha3 haF le_rfl hF9
    (fun s hs => hF.2 s hs) hFa
  set E := Subgroup.zpowers a ⊔ F with hEdef
  have hE : Late.IsE27 E := ⟨hEab, hE27⟩
  have haE : a ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hFE : F ≤ E := le_sup_right
  have hcE : c ∈ E := hFE hcF
  have hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3 hL hEp hEH
  have hmN : ∀ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) →
      m ∈ Subgroup.normalizer (E : Set G) := by
    intro m hmK hmF
    have hma : m * a = a * m := Subgroup.mem_centralizer_singleton_iff.mp (hKa hmK)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmF ⊢
    rw [hEdef, Subgroup.map_sup, hmF, MonoidHom.map_zpowers]
    congr 2
    change m * a * m⁻¹ = a
    rw [hma, mul_inv_cancel_right]
  obtain ⟨f₀, hf₀F, hf₀c⟩ : ∃ f₀ ∈ F, f₀ ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show F ≤ Subgroup.zpowers c from hcon)
    rw [hF9, Nat.card_zpowers, hc3] at this
    omega
  have hf₀1 : f₀ ≠ 1 := fun h1 => hf₀c (h1 ▸ Subgroup.one_mem _)
  obtain ⟨m₀, hm₀K, hm₀F, hm₀⟩ := hT c hcF hc1 f₀ hf₀F hf₀1
  have hU : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hle
    apply hf₀c
    rw [← hm₀]
    exact (Subgroup.mem_normalizer_iff.mp (hle (hmN m₀ hm₀K hm₀F)) c).mp
      (Subgroup.mem_zpowers c)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (A ⊓ Sec4.thetaQuotCentralizer L) (A ⊓ L) (fun x hx y hy => hAc x hx.1 y hy.1)
  have ha' : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L ⊔ A ⊓ L : Subgroup G) : Set G) := by
    rw [h.sup_eq]
    exact haA
  rw [hset] at ha'
  obtain ⟨b, hb, d, hd, hbd⟩ := ha'
  have hdA : d ∈ A := hd.1
  have hdL : d ∈ L := hd.2
  have hbC : b ∈ Sec4.thetaQuotCentralizer L := hb.2
  have hda : a = d * b := by rw [← hbd]; exact hAc b hb.1 d hdA
  have hadC : a * d⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
    rw [← hbd, mul_inv_cancel_right]
    exact hbC
  have hbH : b ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAc b hb.1 c h.mem_A))
  have halc : a ∈ lcBar c L := by
    rw [hda]
    exact KS128NotHJTC.mul_mem_lcBar hL hdL hbC hbH
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set db := π ⟨d, hdL⟩ with hdbdef
  have hφa : thetaBarAct L ⟨a, hEN haE⟩ = MulAut.conj db :=
    thetaBarAct_eq_conj hdL hbC hda (hEN haE)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hdb3 : db ^ 3 = 1 := by
    rw [hdbdef, ← map_pow]
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hdbZ : db ∉ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro hZd
    apply haC
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct (hEN haE), hφa]
    exact conj_eq_one_of_mem_center hZd
  have hZ := card_center_eq_three_of_isSLThreePi hSL
  have haF' : a ∈ Item125Diag.fixer L db := by
    rw [Item125Diag.mem_fixer_iff]
    refine ⟨hEN haE, ?_⟩
    rw [hφa, MulAut.conj_apply, mul_inv_cancel_right]
  have hBp : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := hEp.to_le inf_le_left
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨n, hn3, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
  have hcEL : c ∈ E ⊓ L := ⟨hcE, hcL⟩
  interval_cases n
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hn
    have hmem : c ∈ E ⊓ Sec4.thetaQuotCentralizer L := Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    rw [hn, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  ·
    rw [pow_one] at hn
    have hBc : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcE, hcC⟩))
        (by rw [hn, Nat.card_zpowers, hc3])).symm
    by_cases hfixF : F ≤ Item125Diag.fixer L db
    ·
      have hEfix : E ≤ Item125Diag.fixer L db :=
        sup_le (Subgroup.zpowers_le.mpr haF') hfixF
      have hfix : ∀ e (he : e ∈ E), thetaBarAct L ⟨e, hEN he⟩ db = db := by
        intro e he
        obtain ⟨hg, hgx⟩ := Item125Diag.mem_fixer_iff.mp (hEfix he)
        exact hgx
      obtain ⟨d', hd'π, hd'3, hd'E⟩ := Item125BarTC.exists_lift_pow_three hEp hEN db hdb3 hfix
      have hd'N : (d' : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer d'.2
      have hφd' : thetaBarAct L ⟨d', hd'N⟩ = MulAut.conj db := by
        rw [← hd'π]
        exact thetaBarAct_of_mem d'.2
      have hzN : a * (d' : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        mul_mem (hEN haE) (inv_mem hd'N)
      have hzC : a * (d' : G)⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
        rw [mem_thetaQuotCentralizer_iff_thetaBarAct hzN]
        have h1 : (⟨a * (d' : G)⁻¹, hzN⟩ : Subgroup.normalizer (L : Set G)) =
            ⟨a, hEN haE⟩ * (⟨d', hd'N⟩ : Subgroup.normalizer (L : Set G))⁻¹ := Subtype.ext rfl
        rw [h1, map_mul, map_inv, hφa, hφd', mul_inv_cancel]
      have hzc : a * (d' : G)⁻¹ ∉ Subgroup.zpowers c := by
        intro hmem
        apply haL
        have h2 : a * (d' : G)⁻¹ ∈ L := Subgroup.zpowers_le.mpr hcL hmem
        have h3 : a = a * (d' : G)⁻¹ * d' := by group
        rw [h3]
        exact L.mul_mem h2 d'.2
      have hd'E' : (d' : G) ∉ E := by
        intro hmem
        apply hzc
        rw [← hBc]
        exact ⟨E.mul_mem haE (E.inv_mem hmem), hzC⟩
      have hd'o : orderOf (d' : G) = 3 :=
        orderOf_eq_prime hd'3 fun h1 => hd'E' (h1 ▸ E.one_mem)
      have hd'c : (d' : G) ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        exact hd'E
      obtain ⟨hF81, hFc, hFe⟩ := card_sup_zpowers_of_disjoint hd'c hEab.1 hEab.2 hd'o
        (inf_zpowers_eq_bot_of_not_mem hd'o hd'E')
      exact Item125Diag.false_of_E81 hKT h.partTwoF_eq hL hZ hSL
        (F := E ⊔ Subgroup.zpowers (d' : G)) ⟨hFc, hFe⟩ (by rw [hF81, hE27])
        (sup_le hEN (Subgroup.zpowers_le.mpr hd'N)) (y := d')
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (by rw [hd'π]; exact hdbZ) hd'3
        (Subgroup.mem_sup_left hcE) hcC hc3 (z := a * (d' : G)⁻¹)
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left haE)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))) hzC hzc
    ·
      obtain ⟨f, hfF, hfnot⟩ : ∃ f ∈ F, f ∉ Item125Diag.fixer L db := by
        by_contra hcon
        push Not at hcon
        exact hfixF hcon
      have hfN : f ∈ Subgroup.normalizer (L : Set G) := hEN (hFE hfF)
      have hmv : thetaBarAct L ⟨f, hfN⟩ db ≠ db := fun h' =>
        hfnot (Item125Diag.mem_fixer_iff.mpr ⟨hfN, h'⟩)
      by_cases hin : ∃ y : L ⧸ aschbacherSolvableCore 3 L,
          thetaBarAct L ⟨f, hfN⟩ = MulAut.conj y
      ·
        obtain ⟨yb, hyb⟩ := hin
        obtain ⟨lf, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) yb
        have hlfN : (lf : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer lf.2
        have hzfN : (lf : G)⁻¹ * f ∈ Subgroup.normalizer (L : Set G) :=
          mul_mem (inv_mem hlfN) hfN
        have hzfC : (lf : G)⁻¹ * f ∈ Sec4.thetaQuotCentralizer L := by
          rw [mem_thetaQuotCentralizer_iff_thetaBarAct hzfN]
          have h1 : (⟨(lf : G)⁻¹ * f, hzfN⟩ : Subgroup.normalizer (L : Set G)) =
              (⟨lf, hlfN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨f, hfN⟩ := Subtype.ext rfl
          rw [h1, map_mul, map_inv, thetaBarAct_of_mem lf.2, hyb]
          exact inv_mul_cancel _
        have hzfH : (lf : G)⁻¹ * f ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
          mul_mem (inv_mem (Sec13.le_normalizer_zpowers_of_mem hL lf.2)) (hEH (hFE hfF))
        have hflc : f ∈ lcBar c L := by
          have := KS128NotHJTC.mul_mem_lcBar hL lf.2 hzfC hzfH
          simpa using this
        have hclc : c ∈ lcBar c L := by
          have := KS128NotHJTC.mul_mem_lcBar hL hcL (Subgroup.one_mem _) (Subgroup.one_mem _)
          simpa using this
        have hfc : f ∉ Subgroup.zpowers c := by
          intro hmem
          apply hmv
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
          have h1 : (⟨c ^ k, hfN⟩ : Subgroup.normalizer (L : Set G)) =
              (⟨c, hEN hcE⟩ : Subgroup.normalizer (L : Set G)) ^ k := Subtype.ext (by simp)
          rw [h1, map_zpow, (mem_thetaQuotCentralizer_iff_thetaBarAct (hEN hcE)).mp hcC, one_zpow,
            MulAut.one_apply]
        have hFcf : Subgroup.zpowers c ⊔ Subgroup.zpowers f = F := by
          refine Subgroup.eq_of_le_of_card_ge
            (sup_le (Subgroup.zpowers_le.mpr hcF) (Subgroup.zpowers_le.mpr hfF)) ?_
          rw [hF9, Sec4.card_zpowers_sup_zpowers (hF.2 f hfF) hc3 hfc
            (congrArg Subtype.val (hF.1.is_comm.comm ⟨f, hfF⟩ ⟨c, hcF⟩))]
        have hEL : E ≤ lcBar c L := by
          refine sup_le (Subgroup.zpowers_le.mpr halc) ?_
          rw [← hFcf]
          exact sup_le (Subgroup.zpowers_le.mpr hclc) (Subgroup.zpowers_le.mpr hflc)
        have hac : a ∉ Subgroup.zpowers c := fun hmem =>
          haC ((Subgroup.zpowers_le.mpr hcC) hmem)
        have hW9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
          rw [sup_comm]
          exact Sec4.card_zpowers_sup_zpowers ha3 hc3 hac (hEc a haE c hcE)
        have hWE : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ E :=
          sup_le (Subgroup.zpowers_le.mpr haE) (Subgroup.zpowers_le.mpr hcE)
        have hfix : ∀ e ∈ E, e ∈ Item125Diag.fixer L db →
            e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
          intro e heE heF
          by_contra heW
          have hcfix : c ∈ Item125Diag.fixer L db := by
            rw [Item125Diag.mem_fixer_iff]
            refine ⟨hEN hcE, ?_⟩
            rw [(mem_thetaQuotCentralizer_iff_thetaBarAct (hEN hcE)).mp hcC, MulAut.one_apply]
          have hS := eq_of_card_nine_lt hE27 (inf_le_left : E ⊓ Item125Diag.fixer L db ≤ E)
            (le_inf hWE (sup_le (Subgroup.zpowers_le.mpr haF') (Subgroup.zpowers_le.mpr hcfix)))
            hW9 (show e ∈ E ⊓ Item125Diag.fixer L db from ⟨heE, heF⟩) heW
          have hfE : f ∈ E ⊓ Item125Diag.fixer L db := by
            rw [hS]
            exact hFE hfF
          exact hfnot hfE.2
        have hx : ∀ e ∈ E, ∀ (l : G) (hl : l ∈ L), ∀ z ∈ Sec4.thetaQuotCentralizer L,
            e = l * z → QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩ ^ 3 = 1 :=
          fun e heE l hl z hz hlz =>
            mk_pow_three_eq_one_of_fixer hSL hZ hE hEN haE hcE hcC hdL hd3 hφa hfix heE hl hz hlz
        have hm3 : ∀ S : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsMulCommutative S →
            (∀ x ∈ S, x ^ 3 = 1) → Nat.card S ≤ 9 := fun S hS hS3 =>
          card_le_nine_of_isSLThreePi hSL S
            (fun x hx y hy => congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hS3
        have hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3 := by
          obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
          interval_cases j
          · rw [pow_zero, Subgroup.card_eq_one] at hj
            exact absurd (hj ▸ hcEL) (by simpa using hc1)
          · rw [hj, pow_one]
          · exact (false_of_card_inf_L_eq_nine_of hm3 hL hcL hc1 hZ hE hEL hcE hx hn
              (by rw [hj]; norm_num)).elim
          · exfalso
            have hEL' : E ⊓ L = E :=
              Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE27]; norm_num)
            exact false_of_isE27_le_of hm3 hE (hEL' ▸ inf_le_right)
        have hexp : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
            e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l := by
          intro e heE
          obtain ⟨l₀, hl₀, z₀, hz₀, hlz⟩ := exists_mul_of_mem_lcBar hL (hEL heE)
          exact exists_decomp_of_mk_pow hL (hEL heE) (hEab.2 e heE) hl₀ hz₀ hlz
            (hx e heE l₀ hl₀ z₀ hz₀ hlz)
        exact hU (hD G A c L h (Or.inl hSL) E hE hEL hcE hn hEL3 hexp)
      ·
        exact haL (hR f hfF hfN hin d hdA hdL hadC hmv)
  ·
    have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
      rw [hn]
      norm_num
    have hEsup : Subgroup.zpowers a ⊔ (E ⊓ Sec4.thetaQuotCentralizer L) = E :=
      eq_of_card_nine_lt hE27 (sup_le (Subgroup.zpowers_le.mpr haE) inf_le_left) le_sup_right hB9
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haC h1.2)
    have hEL : E ≤ lcBar c L := by
      rw [← hEsup]
      refine sup_le (Subgroup.zpowers_le.mpr halc) ?_
      intro x hx
      have := KS128NotHJTC.mul_mem_lcBar hL L.one_mem hx.2 (hEH hx.1)
      simpa using this
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd (E ⊓ L) inf_le_left)
    interval_cases j
    · rw [pow_zero, Subgroup.card_eq_one] at hj
      exact absurd (hj ▸ hcEL) (by simpa using hc1)
    · exact false_of_card_inf_L_eq_three hK9 h.partTwoF_eq hL hcL hc1 (Or.inl hSL) hE hEL hcE
        hB9 (by rw [hj, pow_one])
    ·
      have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by rw [hj]; norm_num
      obtain ⟨P, hP, hPB⟩ := hG1 G A c L h (Or.inl hSL) E hE hEL hcE hB9 hEL9 hU
      have hbar : Sec12StdBar G E c L :=
        { toPartTwoStanding := h.toPartTwoStanding
          partTwoF_eq := h.partTwoF_eq
          isE27 := hE
          mem_A := hcE
          ne_one := hc1
          mem_thetaComponentsAt := hL
          mem_L := hcL
          card_B := hB9
          sup_eq := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
          exists_sylow := ⟨P, hP, hPB⟩ }
      exact hU (normalizer_le_of_sec12StdBar_of_list h45 hK2 hbar (Or.inl hSL))
    ·
      exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE27]; norm_num)
      have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hBp inf_le_right (L := L)
      have h2 : E ⊓ Sec4.thetaQuotCentralizer L ⊓ L = E ⊓ Sec4.thetaQuotCentralizer L :=
        inf_eq_left.mpr (inf_le_left.trans (hEL' ▸ inf_le_right))
      rw [h2, hB9, hZ] at h1
      norm_num at h1
  ·
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hn, hE27]; norm_num)
    exact haC (hEC ▸ haE).2

end CFSG.RankThree.PartTwo.Sec12.Item128StepsProof
