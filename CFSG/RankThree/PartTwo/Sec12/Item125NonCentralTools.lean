module

import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap125NonCentralBar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_le {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 3 P) :
    ∃ Q : Subgroup G, IsSylowOf 3 Q K ∧ P ≤ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

noncomputable def thetaPreimage (L T : Subgroup G) : Subgroup G :=
  (((T.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).comap
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map L.subtype

omit [Finite G] in
theorem thetaPreimage_le (L T : Subgroup G) : thetaPreimage L T ≤ L :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_thetaPreimage_iff {L T : Subgroup G} {y : G} (hy : y ∈ L) :
    y ∈ thetaPreimage L T ↔ QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hy⟩ ∈
      (T.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact hy'
  · intro h
    exact ⟨⟨y, hy⟩, h, rfl⟩

omit [Finite G] in
theorem le_thetaPreimage {L T : Subgroup G} (hTL : T ≤ L) : T ≤ thetaPreimage L T :=
  fun t ht => ⟨⟨t, hTL ht⟩, ⟨⟨t, hTL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, rfl⟩

theorem card_thetaPreimage {L T : Subgroup G} (hTL : T ≤ L) (hT3 : IsPGroup 3 T) :
    Nat.card (thetaPreimage L T) = Nat.card (aschbacherSolvableCore 3 L) * Nat.card T := by
  set N := aschbacherSolvableCore 3 L with hN
  set T' : Subgroup L := T.subgroupOf L with hT'
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hT'3 : IsPGroup 3 T' := hT3.comap_subtype
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hT'3
  have hTb : Nat.card (T'.map (QuotientGroup.mk' N)) = Nat.card T' := by
    change Nat.card (↑(T'.map (QuotientGroup.mk' N)) : Set (L ⧸ N)) = Nat.card (T' : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  rw [thetaPreimage, Subgroup.card_map_of_injective L.subtype_injective, ← hT'card, ← hTb]
  exact QuotientGroup.card_preimage_mk N
    ((T'.map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) : Set (L ⧸ N))

theorem eq_of_isPGroup_le_thetaPreimage {L T S : Subgroup G} (hTL : T ≤ L) (hT3 : IsPGroup 3 T)
    (hS3 : IsPGroup 3 S) (hTS : T ≤ S) (hSY : S ≤ thetaPreimage L T) : S = T := by
  have hdvd := Subgroup.card_dvd_of_le hSY
  rw [card_thetaPreimage hTL hT3] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS3
  have hcop : Nat.Coprime (Nat.card S) (Nat.card (aschbacherSolvableCore 3 L)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      three_not_dvd_card_aschbacherSolvableCore)
  have h1 : Nat.card S ∣ Nat.card T := hcop.dvd_of_dvd_mul_left hdvd
  exact (Subgroup.eq_of_le_of_card_ge hTS (Nat.le_of_dvd Nat.card_pos h1)).symm

theorem isSylowOf_of_le_thetaPreimage {L T C : Subgroup G} (hTL : T ≤ L) (hT3 : IsPGroup 3 T)
    (hTC : T ≤ C) (hCY : C ≤ thetaPreimage L T) : IsSylowOf 3 T C := by
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylowOf_le hTC hT3
  rwa [eq_of_isPGroup_le_thetaPreimage hTL hT3 hQ.isPGroup hTQ (hQ.le.trans hCY)] at hQ

theorem conj_mem_thetaPreimage {L T : Subgroup G} {x : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer L) {y : G} (hy : y ∈ thetaPreimage L T) :
    x * y * x⁻¹ ∈ thetaPreimage L T := by
  obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  have hyL := thetaPreimage_le L T hy
  have hxy : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN y).mp hyL
  rw [mem_thetaPreimage_iff hyL] at hy
  rw [mem_thetaPreimage_iff hxy]
  obtain ⟨n, hn, hne⟩ := hxl y hyL
  have heq : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x * y * x⁻¹, hxy⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨y, hyL⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : (⟨x * y * x⁻¹, hxy⟩ : L)⁻¹ * ⟨y, hyL⟩ = n⁻¹ := by
      apply Subtype.ext
      have hne' : (n : G) = y⁻¹ * (x * y * x⁻¹) := hne
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hne']
      group
    rw [h1]
    exact inv_mem hn
  rw [heq]
  exact hy

theorem commute_of_mem_normalizer {L T : Subgroup G} (hT3 : IsPGroup 3 T) (hTL : T ≤ L)
    {x : G} (hx : x ∈ Sec4.thetaQuotCentralizer L) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    {t : G} (ht : t ∈ T) : x * t = t * x := by
  have h1 : t⁻¹ * (x * t * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp hx).2 t (hTL ht)
  have h2 : t⁻¹ * (x * t * x⁻¹) ∈ T :=
    T.mul_mem (T.inv_mem ht) ((Subgroup.mem_normalizer_iff.mp hxT t).mp ht)
  have h3 : t⁻¹ * (x * t * x⁻¹) ∈ (⊥ : Subgroup G) := by
    rw [← inf_inSubgroup_theta_eq_bot hT3 (L := L)]
    exact ⟨h2, h1⟩
  rw [Subgroup.mem_bot] at h3
  calc x * t = t * (t⁻¹ * (x * t * x⁻¹)) * x := by group
    _ = t * x := by rw [h3, mul_one]

theorem exists_conj_commute {L B T : Subgroup G} (hB3 : IsPGroup 3 B)
    (hBC : B ≤ Sec4.thetaQuotCentralizer L) (hTL : T ≤ L) (hT3 : IsPGroup 3 T) :
    ∃ w ∈ L, ∀ b ∈ B, ∀ t ∈ T, w * b * w⁻¹ * t = t * (w * b * w⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := thetaPreimage L T with hY
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    Subgroup.mem_normalizer_fintype fun y hy => conj_mem_thetaPreimage (hBC hb) hy
  set W := Y ⊔ B with hW
  have hWY : W ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hBY
  have hTW : T ≤ W := (le_thetaPreimage hTL).trans le_sup_left
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_le hTW hT3
  obtain ⟨R₁, hR₁, hBR₁⟩ := exists_isSylowOf_le (le_sup_right : B ≤ W) hB3
  obtain ⟨g, hgW, hg⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hR hR₁
  have hRY : R ⊓ Y = T :=
    eq_of_isPGroup_le_thetaPreimage hTL hT3 hR.isPGroup.to_inf_left
      (le_inf hTR (le_thetaPreimage hTL)) inf_le_right
  have hRT : R ≤ Subgroup.normalizer (T : Set G) := by
    intro r hr
    rw [← hRY]
    refine Subgroup.mem_normalizer_fintype fun u hu => ⟨R.mul_mem (R.mul_mem hr hu.1)
      (R.inv_mem hr), (Subgroup.mem_normalizer_iff.mp (hWY (hR.le hr)) u).mp hu.2⟩
  have hginv : g⁻¹ ∈ ((Y ⊔ B : Subgroup G) : Set G) := W.inv_mem hgW
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y B hBY] at hginv
  obtain ⟨y₀, hy₀, b₀, hb₀, hyb⟩ := hginv
  have hy₀L : y₀ ∈ L := thetaPreimage_le L T hy₀
  refine ⟨y₀, hy₀L, fun b hb t ht => ?_⟩
  have hbb : b₀⁻¹ * b * b₀ ∈ R₁ := hBR₁ (B.mul_mem (B.mul_mem (B.inv_mem hb₀) hb) hb₀)
  have hmem : y₀ * b * y₀⁻¹ ∈ R := by
    have h1 := (hg _).mp hbb
    have hyb' : y₀ * b₀ = g⁻¹ := hyb
    have hg' : g = (y₀ * b₀)⁻¹ := by rw [hyb', inv_inv]
    have e : g⁻¹ * (b₀⁻¹ * b * b₀) * g = y₀ * b * y₀⁻¹ := by rw [hg']; group
    rwa [e] at h1
  exact commute_of_mem_normalizer hT3 hTL
    (conj_mem_thetaQuotCentralizer (Subgroup.le_normalizer hy₀L) (hBC hb)) (hRT hmem) ht

theorem isE27_sup {B T : Subgroup G} {c : G} (hBe : CFSG.Assembly.IsElemAbelian 3 B)
    (hTe : CFSG.Assembly.IsElemAbelian 3 T) (hT9 : Nat.card T = 9) (hcB : c ∈ B) (hcT : c ∈ T)
    (hc1 : c ≠ 1) (hcomm : ∀ b ∈ B, ∀ t ∈ T, b * t = t * b) (hB9 : Nat.card B = 9)
    (hBT : B ⊓ T = Subgroup.zpowers c) : Late.IsE27 (B ⊔ T) := by
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hTe.2 c hcT) hc1
  obtain ⟨t₀, ht₀, ht₀c⟩ := exists_mem_not_mem_zpowers hT9 hc3
  have hTcl : Subgroup.closure ({c, t₀} : Set G) = T :=
    closure_pair_eq_of_card_nine hTe.2 hT9 hcT hc1 ht₀ ht₀c
  have ht₀B : t₀ ∉ B := fun h => ht₀c (hBT ▸ ⟨h, ht₀⟩)
  have ht₀3 : orderOf t₀ = 3 := orderOf_eq_prime (hTe.2 t₀ ht₀) fun h => ht₀c (h ▸ one_mem _)
  have hsup : B ⊔ T = B ⊔ Subgroup.zpowers t₀ := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [← hTcl, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_left hcB
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact sup_le le_sup_left (le_sup_of_le_right (Subgroup.zpowers_le.mpr ht₀))
  have hcent : t₀ ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb t₀ ht₀
  obtain ⟨hcard, hc, he⟩ := card_sup_zpowers_of_disjoint hcent hBe.1 hBe.2 ht₀3
    (inf_zpowers_eq_bot_of_not_mem ht₀3 ht₀B)
  rw [hsup]
  exact ⟨⟨hc, he⟩, by rw [hcard, hB9]⟩

theorem thetaImage_facts {c : G} {L T : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hTe : CFSG.Assembly.IsElemAbelian 3 T) (hT9 : Nat.card T = 9) (hTL : T ≤ L) (hcT : c ∈ T) :
    CFSG.Assembly.IsElemAbelian 3
        ((T.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) ∧
      Nat.card ((T.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) = 9 ∧
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≤
        (T.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  set N := aschbacherSolvableCore 3 L with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  set π := QuotientGroup.mk' N with hπ
  set T' : Subgroup L := T.subgroupOf L with hT'def
  have hT'9 : Nat.card T' = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv).trans hT9
  have hT'3 : IsPGroup 3 T' := IsPGroup.of_card (n := 2) (by rw [hT'9]; norm_num)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hT'3
  have hTb9 : Nat.card (T'.map π) = 9 := by
    rw [← hT'9]
    change Nat.card (↑(T'.map π) : Set (L ⧸ N)) = Nat.card (T' : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩, hTb9, ?_⟩
  · obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
    obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
    apply Subtype.ext
    change (u : L ⧸ N) * v = v * u
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    congr 1
    have h := hTe.1.is_comm.comm (⟨u', Subgroup.mem_subgroupOf.mp hu'⟩ : T)
      ⟨v', Subgroup.mem_subgroupOf.mp hv'⟩
    exact Subtype.ext (congrArg Subtype.val h : (u' : G) * v' = v' * u')
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hTe.2 _ (Subgroup.mem_subgroupOf.mp hu))
    rw [this, map_one]
  · set c' : L := ⟨c, hcL⟩ with hc'
    have hc'T : c' ∈ T' := Subgroup.mem_subgroupOf.mpr hcT
    have hc'Z : c' ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc g.2))
    have hπcZ : π c' ∈ Subgroup.center (L ⧸ N) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨c', hc'Z, rfl⟩
    have hc'3 : orderOf c' = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hTe.2 c hcT) hc1
    have hπc1 : π c' ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      apply hN3
      have h' := orderOf_dvd_natCard (⟨c', h1⟩ : N)
      rwa [Subgroup.orderOf_mk, hc'3] at h'
    have hπc3 : orderOf (π c') = 3 := by
      refine orderOf_eq_prime ?_ hπc1
      have hc'p := pow_orderOf_eq_one c'
      rw [hc'3] at hc'p
      rw [← map_pow, hc'p, map_one]
    have heq : Subgroup.zpowers (π c') = Subgroup.center (L ⧸ N) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hπcZ)
        (by rw [hZ, Nat.card_zpowers, hπc3])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr ⟨c', hc'T, rfl⟩

theorem exists_moving (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) :
    ∃ y : G, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ y ∈ Subgroup.normalizer (L : Set G) ∧
      y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      y ∈ Subgroup.normalizer ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) ∧
      ∃ b ∈ A ⊓ Sec4.thetaQuotCentralizer L, y * b * y⁻¹ ≠ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hPB⟩ := h.exists_sylow
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2)⟩
  have hPW : P ≤ Subgroup.normalizer (A : Set G) := hP.le.trans inf_le_left
  have hAWH : A ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx,
      mem_normalizer_zpowers_of_commute (hcommA x hx c h.mem_A)⟩
  have hPA : P ⊔ A = P := hP.eq_of_le le_sup_left (sup_le hP.le hAWH)
    (hP.isPGroup.to_sup_of_normal_right' hA3 hPW)
  have hAP : A ≤ P := hPA ▸ le_sup_right
  obtain ⟨b, hb₀, hbZ⟩ := Set.not_subset.mp hPB
  have hbP : b ∈ P := hAP hb₀.1
  have hbZ' : (⟨b, hbP⟩ : P) ∉ Subgroup.center P := fun hc => hbZ ⟨_, hc, rfl⟩
  rw [Subgroup.mem_center_iff] at hbZ'
  push Not at hbZ'
  obtain ⟨g₂, hg₂⟩ := hbZ'
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  have hPL : P ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3
      h.mem_thetaComponentsAt hP.isPGroup (hP.le.trans inf_le_right)
  refine ⟨g₂, ?_, hPL g₂.2, (hP.le g₂.2).2,
    mem_normalizer_inf_thetaQuotCentralizer (hPW g₂.2) (hPL g₂.2), b, hb₀, fun he => hg₂ ?_⟩
  · obtain ⟨k, hk⟩ := hP.isPGroup g₂
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g₂ : G) * b = ((g₂ : G) * b * (g₂ : G)⁻¹) * g₂ := by group
      _ = b * g₂ := by rw [he]

theorem exists_mul_mem_normalizer {c : G} {L B T : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hCT : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∀ Tb : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 Tb →
        Nat.card Tb = 9 → Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≤ Tb →
          ∃ x : L ⧸ aschbacherSolvableCore 3 L,
            Tb.map σ.toMonoidHom = Tb.map (MulAut.conj x).toMonoidHom)
    (hB3 : IsPGroup 3 B) (hBC : B ≤ Sec4.thetaQuotCentralizer L)
    (hBT : ∀ b ∈ B, ∀ t ∈ T, b * t = t * b)
    (hTe : CFSG.Assembly.IsElemAbelian 3 T) (hT9 : Nat.card T = 9) (hTL : T ≤ L) (hcT : c ∈ T)
    {y : G} (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    ∃ m ∈ L, (∀ b ∈ B, m * b = b * m) ∧ m * y ∈ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  obtain ⟨hTbe, hTb9, hZT⟩ := thetaImage_facts hL hcL hc1 hZ hTe hT9 hTL hcT
  set N := aschbacherSolvableCore 3 L with hNdef
  set π := QuotientGroup.mk' N with hπ
  set Tb := (T.subgroupOf L).map π with hTbdef
  set σ := thetaBarAct L ⟨y, hyN⟩ with hσdef
  have hσ : σ ^ 3 ^ k = 1 := by
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hy)
    rw [hσdef, ← map_pow, h1, map_one]
  obtain ⟨xb, hxb⟩ := hCT σ ⟨k, hσ⟩ Tb hTbe hTb9 hZT
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    hBC.trans (thetaQuotCentralizer_le_normalizer' L)
  obtain ⟨ℓ₀, rfl, hℓ₀B⟩ := exists_lift_fixed hB3 hBN xb fun d hd => by
    rw [(mem_thetaQuotCentralizer_iff_thetaBarAct (hBN hd)).mp (hBC hd), MulAut.one_apply]
  set z : G := (ℓ₀ : G)⁻¹ * y with hzdef
  have hzN : z ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer ℓ₀.2)) hyN
  have hφz : thetaBarAct L ⟨z, hzN⟩ = (MulAut.conj (π ℓ₀))⁻¹ * σ := by
    have h1 : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨ℓ₀, Subgroup.le_normalizer ℓ₀.2⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨y, hyN⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, thetaBarAct_of_mem ℓ₀.2]
  set Y := thetaPreimage L T with hY
  have hzY : ∀ u ∈ Y, z * u * z⁻¹ ∈ Y := by
    intro u hu
    have huL := thetaPreimage_le L T hu
    have hzu : z * u * z⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hzN u).mp huL
    rw [mem_thetaPreimage_iff hzu]
    rw [mem_thetaPreimage_iff huL] at hu
    have h1 : π ⟨z * u * z⁻¹, hzu⟩ = thetaBarAct L ⟨z, hzN⟩ (π ⟨u, huL⟩) := rfl
    rw [h1, hφz, MulAut.mul_apply]
    have h2 : σ (π ⟨u, huL⟩) ∈ Tb.map σ.toMonoidHom := ⟨_, hu, rfl⟩
    rw [hxb] at h2
    obtain ⟨tb, htb, htbe⟩ := h2
    rw [← htbe]
    have e : (MulAut.conj (π ℓ₀))⁻¹ ((MulAut.conj (π ℓ₀)).toMonoidHom tb) = tb := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [e]
    exact htb
  have hℓ₀c : ∀ b ∈ B, (ℓ₀ : G) * b = b * ℓ₀ := fun b hb => by
    have h1 := hℓ₀B b hb
    calc (ℓ₀ : G) * b = (b * ℓ₀ * b⁻¹) * b := by rw [h1]
      _ = b * ℓ₀ := by group
  have hzB : z ∈ Subgroup.normalizer (B : Set G) := by
    refine mul_mem (inv_mem (Subgroup.mem_normalizer_fintype fun b hb => ?_)) hyB
    rw [hℓ₀c b hb, mul_inv_cancel_right]
    exact hb
  set C := Y ⊓ Subgroup.centralizer (B : Set G) with hC
  have hTC : T ≤ C := le_inf (le_thetaPreimage hTL) fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hBT b hb t ht
  have hzC : ∀ u ∈ C, z * u * z⁻¹ ∈ C := by
    intro u hu
    refine ⟨hzY u hu.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hb' : z⁻¹ * b * z ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hzB) b).mp hb
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hu.2 _ hb'
    calc b * (z * u * z⁻¹) = z * ((z⁻¹ * b * z) * u) * z⁻¹ := by group
      _ = z * (u * (z⁻¹ * b * z)) * z⁻¹ := by rw [hc]
      _ = z * u * z⁻¹ * b := by group
  have hTS : IsSylowOf 3 T C := isSylowOf_of_le_thetaPreimage hTL hT3 hTC inf_le_left
  have hzTC : T.map (MulAut.conj z).toMonoidHom ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    exact hzC t (hTC ht)
  have hzTS : IsSylowOf 3 (T.map (MulAut.conj z).toMonoidHom) C :=
    CFSG.ABGLocalTools.isSylowOf_of_card hzTC (by
      rw [Subgroup.card_map_of_injective (MulAut.conj z).injective, hTS.card_eq])
  obtain ⟨g, hgC, hg⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hTS hzTS
  refine ⟨g⁻¹ * (ℓ₀ : G)⁻¹, L.mul_mem (L.inv_mem (thetaPreimage_le L T hgC.1))
    (L.inv_mem ℓ₀.2), fun b hb => ?_, ?_⟩
  · have h1 : Commute (ℓ₀ : G) b := hℓ₀c b hb
    have h2 : Commute g b := (Subgroup.mem_centralizer_iff.mp hgC.2 b hb).symm
    exact (h2.inv_left.mul_left h1.inv_left).eq
  · refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have h1 : z * t * z⁻¹ ∈ T.map (MulAut.conj z).toMonoidHom := ⟨t, ht, by simp⟩
    have h2 := (hg _).mp h1
    have e : g⁻¹ * (ℓ₀ : G)⁻¹ * y * t * (g⁻¹ * (ℓ₀ : G)⁻¹ * y)⁻¹ = g⁻¹ * (z * t * z⁻¹) * g := by
      rw [hzdef]
      group
    rw [e]
    exact h2

theorem sec12StdBar_sup {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hCT : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∀ Tb : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 Tb →
        Nat.card Tb = 9 → Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≤ Tb →
          ∃ x : L ⧸ aschbacherSolvableCore 3 L,
            Tb.map σ.toMonoidHom = Tb.map (MulAut.conj x).toMonoidHom)
    {B T : Subgroup G} (hBe : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hcB : c ∈ B) (hBC : B ≤ Sec4.thetaQuotCentralizer L)
    (hBT : ∀ b ∈ B, ∀ t ∈ T, b * t = t * b)
    (hTe : CFSG.Assembly.IsElemAbelian 3 T) (hT9 : Nat.card T = 9) (hTL : T ≤ L) (hcT : c ∈ T)
    {y : G} (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hyH : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {b : G} (hb : b ∈ B) (hyb : y * b * y⁻¹ ≠ b) :
    Sec12StdBar G (B ⊔ T) c L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBe.2 x x.2)⟩
  have hT3 : IsPGroup 3 T := fun x => ⟨1, Subtype.ext (by simpa using hTe.2 x x.2)⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hBe.2 c hcB) h.ne_one
  have hBTc : B ⊓ T = Subgroup.zpowers c := by
    have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 hBC (L := L)
    rw [hZ] at h1
    have h2 : Nat.card (B ⊓ T : Subgroup G) ≤ 3 :=
      (Subgroup.card_le_of_le (inf_le_inf_left B hTL)).trans h1
    exact (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcB, hcT⟩))
      (by rw [Nat.card_zpowers, hc3]; exact h2)).symm
  have hA' : Late.IsE27 (B ⊔ T) := isE27_sup hBe hTe hT9 hcB hcT h.ne_one hBT hB9 hBTc
  obtain ⟨t₀, ht₀, ht₀C⟩ : ∃ t ∈ T, t ∉ Sec4.thetaQuotCentralizer L := by
    by_contra hcon
    push Not at hcon
    have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hT3 hcon (L := L)
    rw [inf_eq_left.mpr hTL, hT9, hZ] at h1
    norm_num at h1
  have hBeq : (B ⊔ T) ⊓ Sec4.thetaQuotCentralizer L = B := by
    by_contra hne
    obtain ⟨x, hxS, hxB⟩ : ∃ x ∈ (B ⊔ T) ⊓ Sec4.thetaQuotCentralizer L, x ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon (le_inf le_sup_left hBC))
    have heq := eq_of_card_nine_lt hA'.2 inf_le_left (le_inf le_sup_left hBC) hB9 hxS hxB
    have h1 : t₀ ∈ (B ⊔ T) ⊓ Sec4.thetaQuotCentralizer L := by
      rw [heq]
      exact (le_sup_right : T ≤ B ⊔ T) ht₀
    exact ht₀C h1.2
  obtain ⟨k, hk⟩ := hy3
  obtain ⟨m, hmL, hmB, hmT⟩ := exists_mul_mem_normalizer hL h.mem_L h.ne_one hZ hCT hB3 hBC hBT
    hTe hT9 hTL hcT hyN hyB hk
  set x₁ := m * y with hx₁
  have hx₁B : x₁ ∈ Subgroup.normalizer (B : Set G) := by
    refine mul_mem (Subgroup.mem_normalizer_fintype fun b' hb' => ?_) hyB
    rw [hmB b' hb', mul_inv_cancel_right]
    exact hb'
  have hx₁A : x₁ ∈ Subgroup.normalizer ((B ⊔ T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx₁B hmT ⊢
    rw [Subgroup.map_sup, hx₁B, hmT]
  have hmH : m ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Sec13.le_normalizer_zpowers_of_mem hL hmL
  have hx₁H : x₁ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := mul_mem hmH hyH
  have hact : ∀ n : ℕ, ∀ b' ∈ B, x₁ ^ n * b' * (x₁ ^ n)⁻¹ = y ^ n * b' * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro b' _; simp
    | succ n ih =>
      intro b' hb'
      have hyb' : y ^ n * b' * (y ^ n)⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (pow_mem hyB n) b').mp hb'
      have hyb'' : y * (y ^ n * b' * (y ^ n)⁻¹) * y⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp hyB _).mp hyb'
      calc x₁ ^ (n + 1) * b' * (x₁ ^ (n + 1))⁻¹ = x₁ * (x₁ ^ n * b' * (x₁ ^ n)⁻¹) * x₁⁻¹ := by
            rw [pow_succ']
            group
        _ = x₁ * (y ^ n * b' * (y ^ n)⁻¹) * x₁⁻¹ := by rw [ih b' hb']
        _ = m * (y * (y ^ n * b' * (y ^ n)⁻¹) * y⁻¹) * m⁻¹ := by rw [hx₁]; group
        _ = y * (y ^ n * b' * (y ^ n)⁻¹) * y⁻¹ := by rw [hmB _ hyb'', mul_inv_cancel_right]
        _ = y ^ (n + 1) * b' * (y ^ (n + 1))⁻¹ := by rw [pow_succ']; group
  obtain ⟨k', n', hn', hx₂, -⟩ := exists_threePart x₁
  set x₂ := x₁ ^ n' with hx₂def
  have hx₂b : x₂ * b * x₂⁻¹ ≠ b := by
    rw [hx₂def, hact n' b hb]
    exact conj_pow_ne_of_conj_ne hk hyb hn'
  have hx₂WH : x₂ ∈ Subgroup.normalizer ((B ⊔ T : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Subgroup.mem_inf.mpr ⟨pow_mem hx₁A n', pow_mem hx₁H n'⟩
  have hx₂3 : IsPGroup 3 (Subgroup.zpowers x₂) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx₂)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P', hP', hxP'⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hx₂WH) hx₂3
  refine
    { toPartTwoStanding := h.toPartTwoStanding
      partTwoF_eq := h.partTwoF_eq
      isE27 := hA'
      mem_A := Subgroup.mem_sup_left hcB
      ne_one := h.ne_one
      mem_thetaComponentsAt := hL
      mem_L := h.mem_L
      card_B := by rw [hBeq, hB9]
      sup_eq := ?_
      exists_sylow := ⟨P', hP', ?_⟩ }
  · rw [hBeq]
    exact le_antisymm (sup_le le_sup_left inf_le_left)
      (sup_le_sup_left (le_inf le_sup_right hTL) B)
  · rw [hBeq]
    intro hle
    obtain ⟨zb, hzb, hzbe⟩ := hle hb
    have hx₂P : x₂ ∈ P' := hxP' (Subgroup.mem_zpowers x₂)
    have hc := Subgroup.mem_center_iff.mp hzb ⟨x₂, hx₂P⟩
    apply hx₂b
    have h1 : x₂ * b = b * x₂ := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [← hzbe]
      exact this
    rw [h1, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec12.Gap125NonCentralBar
