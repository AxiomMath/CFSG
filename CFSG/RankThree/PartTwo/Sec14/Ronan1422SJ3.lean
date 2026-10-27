module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SExcl
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SSyl
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SS6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_centralizer_of_zpowers {c w : G}
    (hw : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    w ∈ Subgroup.normalizer ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ v ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G), ∀ x ∈
      Subgroup.centralizer ({c} : Set G), v * x * v⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    intro v hv x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hvc : v⁻¹ * c * v⁻¹⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hv) c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvc
    rw [inv_inv] at hk
    have hxk : c ^ k * x = x * c ^ k := ((Commute.zpow_left hx.symm k)).eq
    calc v * x * v⁻¹ * c = v * x * (v⁻¹ * c * v) * v⁻¹ := by group
      _ = v * x * c ^ k * v⁻¹ := by rw [hk]
      _ = v * (c ^ k * x) * v⁻¹ := by rw [hxk]; group
      _ = v * (v⁻¹ * c * v) * x * v⁻¹ := by rw [hk]; group
      _ = c * (v * x * v⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key w hw x
  · intro hx
    have := key w⁻¹ (inv_mem hw) _ hx
    simpa [mul_assoc] using this

section KP4


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem card_A_inf_K (h : Cfg A c L R S J) :
    Nat.card (img148 A (Subgroup.normalizer (S : Set G)) A ⊓
      img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G)) :
        Subgroup _) = 9 := by
  set K' := img148 A (Subgroup.normalizer (S : Set G)) (L ⊓ Subgroup.normalizer (R : Set G))
    with hK'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  have hA : IsE27 A := h.pt.std.isE27
  obtain ⟨-, hB9, hBK⟩ := h.B_bar_facts
  have hBle : img148 A (Subgroup.normalizer (S : Set G)) (A ⊓ L) ≤ A' ⊓ K' :=
    le_inf (img148_mono inf_le_left) hBK
  have h9 : 9 ≤ Nat.card (A' ⊓ K' : Subgroup _) := hB9 ▸ Subgroup.card_le_of_le hBle
  have hA27 : Nat.card A' = 27 := (img148_isE27 (Y := Subgroup.normalizer (S : Set G)) hA).2
  have hdvd : Nat.card (A' ⊓ K' : Subgroup _) ∣ 27 := hA27 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (A' ⊓ K' : Subgroup _) ≠ 27 := by
    intro h27
    have heq : A' ⊓ K' = A' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA27])
    have hcK : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ K' := by
      have h1 : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ A' :=
        alpha148_mem_img148 h.pt.mem_A
      rw [← heq] at h1
      exact h1.2
    have hcB : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈ A' ⊓
        Subgroup.centralizer (K' : Set _) := ⟨alpha148_mem_img148 h.pt.mem_A,
      Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_singleton_iff.mp (h.K_le_centralizer.1 hk).2)⟩
    obtain ⟨φ⟩ := h.nonempty_K_equiv
    have hsimple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
      have : Nontrivial (alternatingGroup (Fin 6)) := hsimple6.toNontrivial
      obtain ⟨a, b, hab⟩ := Main148.exists_ne_comm_of_isPerfect isPerfect_alternatingGroup_six
      rcases (Subgroup.center (alternatingGroup (Fin 6))).normal_of_characteristic.eq_bot_or_eq_top
        with h0 | h0
      · exact h0
      · exfalso
        have ha : a ∈ Subgroup.center (alternatingGroup (Fin 6)) := h0 ▸ Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
    have hz : (⟨_, hcK⟩ : ↥K') ∈ Subgroup.center ↥K' := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcB.2 k k.2)
    have hφz : φ ⟨_, hcK⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := congrArg φ (hz (φ.symm g))
      simpa using this
    rw [hZ6, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφz
    have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
    exact Main148.alpha148_ne_one h.pt.mem_A h.c_ne_one (hA3 c h.pt.mem_A)
      (congrArg Subtype.val hφz)
  have : Nat.card (A' ⊓ K' : Subgroup _) ∈ Nat.divisors 27 := by
    rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
  have h27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [h27] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem false_of_J3 (hKF : KF1422J3) (hGL : KF1422GL42) (h : Cfg A c L R S J)
    (hJ : Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
      Blueprint.NativeSporadic.J3)) : False := by
  set J' := img148 A (Subgroup.normalizer (S : Set G)) J with hJ'
  set K := L ⊓ Subgroup.normalizer (R : Set G) with hK
  set K' := img148 A (Subgroup.normalizer (S : Set G)) K with hK'
  set A' := img148 A (Subgroup.normalizer (S : Set G)) A with hA'
  have hA : IsE27 A := h.pt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨hcard, hinn, hKF2⟩ := hKF ↥J' hJ
  have hne : Nat.card J' ≠ 360 := by rw [hcard]; norm_num
  have hcN : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ∈
      Subgroup.normalizer (J' : Set _) :=
    img148_le_normalizer h.A_le (alpha148_mem_img148 h.pt.mem_A)
  have hc3 : alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A ^ 3 = 1 := by
    rw [← alpha148_pow h.pt.mem_A 3]
    simp only [hA3 c h.pt.mem_A]
    rfl
  have hAJ := h.le_J_of_innerOn hne (innerOn148_of_inner hcN hc3 hinn)
  have hAJ' : A' ≤ J' := img148_mono hAJ
  have hKJ' : K' ≤ J' := img148_mono h.K_le
  have hE := isE27_subgroupOf1422 hAJ' (img148_isE27 hA)
  set c' : ↥J' := ⟨alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A,
    hAJ' (alpha148_mem_img148 h.pt.mem_A)⟩ with hc'
  have hc'E : c' ∈ A'.subgroupOf J' := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 h.pt.mem_A)
  have hc'1 : c' ≠ 1 := fun h1 => Main148.alpha148_ne_one h.pt.mem_A h.c_ne_one
    (hA3 c h.pt.mem_A) (congrArg Subtype.val h1)
  set KK := K'.subgroupOf J' with hKK
  have hKc : KK ≤ Subgroup.centralizer ({c'} : Set ↥J') := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (h.K_le_centralizer.1 (Subgroup.mem_subgroupOf.mp hx)).2
  have hCN : Subgroup.centralizer ({c'} : Set ↥J') ≤ Subgroup.normalizer (KK : Set ↥J') := by
    intro s hs
    have hsC : (s : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
        ker148 A (Subgroup.normalizer (S : Set G))) ∈ J' ⊓
          Subgroup.centralizer {alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A} :=
      ⟨s.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hs))⟩
    rw [Main148.img148_inf_centralizer_alpha148 h.A_le_NM (h.J_le_M.trans le_sup_left) h.A_le
      h.pt.mem_A (hA3 c h.pt.mem_A)] at hsC
    have hJCK : J ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
      fun x hx => h.pt.centralizer_inf_le_normalizer_K h.R_mem h.S_mem ⟨h.J_le_M hx.1, hx.2⟩
    have hsN := img148_le_normalizer hJCK hsC
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hKK, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp hsN x
  obtain ⟨φ⟩ := h.nonempty_K_equiv
  have hK6 : Nonempty (↥KK ≃* alternatingGroup (Fin 6)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKJ').trans φ⟩
  have hEK : Nat.card (A'.subgroupOf J' ⊓ KK : Subgroup ↥J') = 9 := by
    have hmap : (A'.subgroupOf J' ⊓ KK).map J'.subtype = A' ⊓ K' := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.mp hy1, Subgroup.mem_subgroupOf.mp hy2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hAJ' hx1⟩, ⟨hx1, hx2⟩, rfl⟩
    rw [← h.card_A_inf_K, ← hmap, Subgroup.card_map_of_injective J'.subtype_injective]
  obtain ⟨t, ht, htE, htc, hnot⟩ :=
    hKF2 (A'.subgroupOf J') hE.1 hE.2 c' hc'E hc'1 KK hKc hCN hK6 hEK
  have htA : (t : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G))) ∈ Subgroup.normalizer (A' : Set _) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have h1 := (Subgroup.mem_normalizer_iff.mp htE ⟨n, hAJ' hn⟩).mp
      (Subgroup.mem_subgroupOf.mpr hn)
    simpa [Subgroup.mem_subgroupOf] using h1
  have htc' : (t : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G))) ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A (Subgroup.normalizer (S : Set G)) c h.pt.mem_A) :
          Set _) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h1 := (Subgroup.mem_normalizer_iff.mp htc (c' ^ k)).mp
      (zpow_mem (Subgroup.mem_zpowers c') k)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have h2 := congrArg Subtype.val hj
    simpa [hc'] using h2
  obtain ⟨w, hw, hwA, hwt⟩ := exists_lift_normalizer148
    (fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩) h.A_le_NM htA
  have hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_alpha148 hA3 hw hwA h.pt.mem_A (by rw [hwt]; exact htc')
  have hwL := h.pt.normalizer_zpowers_le hwc
  have hwM : w ∈ Subgroup.normalizer (S : Set G) := h.sup_A_eq ▸ hw
  have hwR : w ∈ Subgroup.normalizer (R : Set G) := by
    have := mem_normalizer_inf hwM (mem_normalizer_centralizer_of_zpowers hwc)
    rwa [h.pt.inf_centralizer_eq h.R_mem h.S_mem] at this
  have hwK : w ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_inf hwL (mem_normalizer_normalizer hwR)
  obtain ⟨-, f, hf, hker⟩ := h.pt.K_kp4 h.R_mem
  obtain ⟨hRe, hR16, -, hRB⟩ := h.pt.R_kp4 h.R_mem
  obtain ⟨hRL, -, hAR, -⟩ := h.pt.R_facts h.R_mem
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.1.is_comm.comm (⟨x, hx⟩ : ↥R) ⟨y, hy⟩)
  have hCR : K ⊓ Subgroup.centralizer (R : Set G) ≤ R :=
    cent_le_of_quot (R_le_K hRL) f hf hker hRc h.R_ne_bot (B_le_K hAR) hRB
  have hKMA : K ≤ Subgroup.normalizer (S : Set G) ⊔ A := h.K_le_M.trans le_sup_left
  let π₀ : ↥K →* ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
      ker148 A (Subgroup.normalizer (S : Set G)) :=
    (QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))).comp
      (Subgroup.inclusion hKMA)
  have hπ₀K : ∀ k, π₀ k ∈ K' := fun k => mem_img148_iff.mpr ⟨k, hKMA k.2, k.2, rfl⟩
  let π : ↥K →* ↥KK := (π₀.codRestrict J' (fun k => hKJ' (hπ₀K k))).codRestrict KK
    (fun k => Subgroup.mem_subgroupOf.mpr (hπ₀K k))
  have hπ : Function.Surjective π := by
    rintro ⟨⟨x, hxJ⟩, hxK⟩
    obtain ⟨g, hg, hgK, rfl⟩ := mem_img148_iff.mp (Subgroup.mem_subgroupOf.mp hxK)
    exact ⟨⟨g, hgK⟩, rfl⟩
  have hπker : π.ker = R.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have h1 : QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))
          ⟨(k : G), hKMA k.2⟩ = 1 := by
        have h2 := congrArg (fun x : ↥KK => ((x : ↥J') : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸
          ker148 A (Subgroup.normalizer (S : Set G)))) hk
        exact h2
      rw [mk'_ker148_eq_one_iff] at h1
      have h2 : (k : G) ∈ K ⊓ pPrimeCoreOf 3 (Subgroup.normalizer (S : Set G)) := ⟨k.2, h1⟩
      rwa [h.inf_pPrimeCoreOf_eq] at h2
    · intro hk
      apply Subtype.ext
      apply Subtype.ext
      change QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))
        ⟨(k : G), hKMA k.2⟩ = 1
      rw [mk'_ker148_eq_one_iff]
      exact h.S_le_pPrimeCoreOf (h.R_le_S hk)
  have hα : ∀ k : ↥K, (KK.normalizerMonoidHom ⟨t, ht⟩) (π k) =
      π (K.normalizerMonoidHom ⟨w, hwK⟩ k) := by
    intro k
    set tt : ↥(Subgroup.normalizer (S : Set G) ⊔ A) ⧸ ker148 A (Subgroup.normalizer (S : Set G)) :=
      J'.subtype t with htt
    have hwt' : QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨w, hw⟩ = tt := hwt
    apply Subtype.ext
    apply Subtype.ext
    change tt * π₀ k * tt⁻¹ =
      QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G)))
        ⟨w * (k : G) * w⁻¹, hKMA (Subgroup.mem_normalizer_iff.mp hwK _ |>.mp k.2)⟩
    rw [← hwt']
    change QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨w, hw⟩ *
        QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨(k : G), hKMA k.2⟩ *
        (QuotientGroup.mk' (ker148 A (Subgroup.normalizer (S : Set G))) ⟨w, hw⟩)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  exact hnot (isS6Type_of_normalizes hGL inf_le_right f hf hker hRe hR16 hCR hwK hwR π hπ
    hπker _ hα)

end Cfg

end KP4

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
