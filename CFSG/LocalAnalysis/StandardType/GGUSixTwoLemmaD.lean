module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaDTransport
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open

variable {G : Type*} [Group G] {K : Type} [Field K]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

theorem normalizer_zpowers_eq_centralizer {t : G} (ht2 : orderOf t = 2) :
    Subgroup.normalizer (Subgroup.zpowers t : Set G) = Subgroup.centralizer ({t} : Set G) := by
  classical
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgt : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    have ht2pow : t ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ht2]
    have hfin : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ht2pow⟩
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, ht2] at hgt
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp hgt
    rw [Finset.mem_range] at hi
    have hne : g * t * g⁻¹ ≠ 1 := by
      intro h1
      have h2 : t = 1 := by
        have h3 := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using h3
      rw [h2] at ht2
      simp at ht2
    interval_cases i
    · simp only [pow_zero] at hit
      exact absurd hit.symm hne
    · have hconj : g * t * g⁻¹ = t := by simpa using hit.symm
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hconj]
  · rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact Subgroup.centralizer_le_normalizer _

theorem map_subtype_center (H : Subgroup G) :
    (Subgroup.center ↥H).map H.subtype = H ⊓ Subgroup.centralizer (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change H.subtype y ∈ Subgroup.centralizer (H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)
  · rintro ⟨hxH, hxCH⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxCH g.1 g.2)

theorem inf_pCoreOf_centralizer_eq_bot [Finite G] [Finite K] (hS : LocalSetting hω b L φ Bs)
    {t : G} (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    L ⊓ pCoreOf 2 (Subgroup.centralizer {t}) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set T : Subgroup G := pCoreOf 2 C with hT
  have hLC : L ≤ C := by
    intro l hl
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htL l hl
  have hTnorm : C ≤ Subgroup.normalizer (T : Set G) := by
    rw [hT]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hLT : L ≤ Subgroup.normalizer (T : Set G) := hLC.trans hTnorm
  have hInfNorm : ((L ⊓ T).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact (le_inf Subgroup.le_normalizer hLT).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := L) (K := T))
  haveI : IsSimpleGroup L := isSimpleGroup_L hS
  haveI := hInfNorm
  rcases Subgroup.Normal.eq_bot_or_eq_top ((L ⊓ T).subgroupOf L) with hbot | htop
  · have hdisj : Disjoint (L ⊓ T) L := Subgroup.subgroupOf_eq_bot.mp hbot
    have hbot2 : (L ⊓ T) ⊓ L = ⊥ := disjoint_iff.mp hdisj
    calc L ⊓ T = (L ⊓ T) ⊓ L := (inf_eq_left.mpr inf_le_left).symm
      _ = ⊥ := hbot2
  · exfalso
    have hLe : L ≤ T := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
    have hT2 : IsPGroup 2 T := by
      rw [hT]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
    have hL2 : IsPGroup 2 L := hT2.to_le hLe
    have h3U : 3 ∣ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      have h1 : 3 ∣ Nat.card (torU K) := by rw [card_torU hS.card_K]; norm_num
      simpa using h1.trans (Subgroup.card_dvd_of_le (H := torU K) (K := ⊤) le_top)
    have h3L : 3 ∣ Nat.card L := by
      rw [Nat.card_congr φ.toEquiv]
      exact h3U
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hL2
    rw [hk] at h3L
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3L) (by norm_num)

theorem pCoreOf_centralizer_inf_centralizer_eq [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (hnL : n * b * n⁻¹ ∈ L)
    (hnφ : φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    pCoreOf 2 (Subgroup.centralizer {t}) ⊓ Subgroup.centralizer {n * b * n⁻¹} =
      pCoreOf 2 (L.map (MulAut.conj n : G →* G) ⊓ Subgroup.centralizer {t}) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : G := n * b * n⁻¹ with he
  set M : Subgroup G := L.map (MulAut.conj n : G →* G) with hM
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set Ce : Subgroup G := Subgroup.centralizer ({e} : Set G) with hCe
  set T : Subgroup G := pCoreOf 2 C with hT
  set Q : Subgroup G := pCoreOf 2 (M ⊓ C) with hQ
  set P : Subgroup G := pCoreOf 2 (Ce ⊓ C) with hP
  have hS' : LocalSetting hω e M (conjEquiv φ n) Bs := hS.conj hn hnL hnφ
  have hMCe : M ≤ Ce := hS'.le_centralizer
  have hCeN : Ce ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMCe).mp hS'.normal
  have hXH : M ⊓ C ≤ Ce ⊓ C := le_inf (inf_le_left.trans hMCe) inf_le_right
  have hHX : Ce ⊓ C ≤ Subgroup.normalizer ((M ⊓ C : Subgroup G) : Set G) := by
    have h1 : Ce ⊓ C ≤ Subgroup.normalizer (M : Set G) := inf_le_left.trans hCeN
    have h2 : Ce ⊓ C ≤ Subgroup.normalizer (C : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := M) (K := C))
  have hQP : Q ≤ P := by
    rw [hQ, hP]
    exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hXH hHX
  have hPcard : Nat.card P ≤ 2 ^ 9 := by
    rw [hP]
    exact card_pCoreOf_centralizer_inf_le hG hS ht ht2 htb htL hn hnL hnφ htA
  have hQcard : Nat.card Q = 2 ^ 9 := by
    rw [hQ]
    exact card_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
  have hQP_eq : Q = P := by
    refine Subgroup.eq_of_le_of_card_ge hQP ?_
    rw [hQcard]
    exact hPcard
  have hTC : T ≤ C := by
    rw [hT]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hT2 : IsPGroup 2 T := by
    rw [hT]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hTnorm : C ≤ Subgroup.normalizer (T : Set G) := by
    rw [hT]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hTCe_le : T ⊓ Ce ≤ P := by
    rw [hP]
    have hXH2 : T ⊓ Ce ≤ Ce ⊓ C := le_inf inf_le_right (inf_le_left.trans hTC)
    have hHX2 : Ce ⊓ C ≤ Subgroup.normalizer ((T ⊓ Ce : Subgroup G) : Set G) := by
      have h1 : Ce ⊓ C ≤ Subgroup.normalizer (T : Set G) := inf_le_right.trans hTnorm
      have h2 : Ce ⊓ C ≤ Subgroup.normalizer (Ce : Set G) :=
        inf_le_left.trans Subgroup.le_normalizer
      exact (le_inf h1 h2).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := Ce))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXH2 hHX2 (hT2.to_le inf_le_left)
  have hLC : L ≤ C := by
    intro l hl
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htL l hl
  have hCtN : C ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [hC, ← CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact Subgroup.centralizer_le_normalizer _
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2, pow_one]
  have hzpT : Subgroup.zpowers t ≤ T := by
    rw [hT]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hCtN hzp2
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have htT : t ∈ T := hzpT (Subgroup.mem_zpowers t)
  have hte : t ∈ Ce := by
    rw [hCe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL e hnL).symm
  have hzple : Subgroup.zpowers t ≤ T ⊓ Ce := Subgroup.zpowers_le.mpr ⟨htT, hte⟩
  have hLnormT : L ≤ Subgroup.normalizer (T : Set G) := hLC.trans hTnorm
  have hLY : L ⊓ Ce ≤ Subgroup.normalizer ((T ⊓ Ce : Subgroup G) : Set G) := by
    have h1 : L ⊓ Ce ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hLnormT
    have h2 : L ⊓ Ce ≤ Subgroup.normalizer (Ce : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := Ce))
  have hYeq : T ⊓ Ce = Subgroup.zpowers t ∨ T ⊓ Ce = Q :=
    eq_or_eq_of_le_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
      hzple (hTCe_le.trans (le_of_eq hQP_eq.symm)) hLY
  rcases hYeq with hY | hY
  ·
    exfalso
    have hLX : L ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := hLC.trans hCtN
    have hYX : T ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := hTC.trans hCtN
    have hT3 : ¬ 3 ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
      rw [hk]
      exact fun hd => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
    have hfix : T ⊓ Ce ≤ Subgroup.zpowers t := by rw [hY]
    have hTle : T ≤ Subgroup.zpowers t :=
      le_of_centralizer_le_of_threeA (G := G) (K := K) hS.card_K hω (L := L)
        (X := Subgroup.zpowers t) (Y := T) φ hnL ⟨1, by simpa using hnφ⟩ hLX hLnormT hYX hT3 hfix
    have hTeq : T = Subgroup.zpowers t := le_antisymm hTle hzpT
    have hzpne : Subgroup.zpowers t ≠ ⊥ := by
      intro h1
      rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1] at ht2
      simp at ht2
    have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers t : Set G)) :=
      ⟨Subgroup.zpowers t, hzpne, hzp2, rfl⟩
    have hchar := hG (Subgroup.normalizer (Subgroup.zpowers t : Set G)) hloc
    have hN : Subgroup.normalizer (Subgroup.zpowers t : Set G) = C :=
      (normalizer_zpowers_eq_centralizer ht2).trans hC.symm
    have hpN : pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G)) = T := by
      rw [hN]
    have hCT : C ≤ Subgroup.centralizer
        (pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G)) : Set G) := by
      rw [hpN, hTeq, CFSG.centralizer_zpowers_eq_centralizer_singleton, hC]
    have hCN : C ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
      rw [hN]
    have hle : C ≤ T := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) ⊓
          Subgroup.centralizer
            (pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G)) : Set G) :=
        le_inf hCN hCT
      have h2 := h1.trans hchar
      rwa [hpN] at h2
    have hle' : C ≤ Subgroup.zpowers t := by
      rw [← hTeq]
      exact hle
    have hLT' : L ≤ Subgroup.zpowers t := hLC.trans hle'
    have h3U : 3 ∣ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      have h1 : 3 ∣ Nat.card (torU K) := by rw [card_torU hS.card_K]; norm_num
      simpa using h1.trans (Subgroup.card_dvd_of_le (H := torU K) (K := ⊤) le_top)
    have h3L : 3 ∣ Nat.card L := by
      rw [Nat.card_congr φ.toEquiv]
      exact h3U
    have hcle : Nat.card L ≤ Nat.card (Subgroup.zpowers t) := Subgroup.card_le_of_le hLT'
    rw [Nat.card_zpowers, ht2] at hcle
    obtain ⟨m, hm⟩ := h3L
    have hpos : 0 < Nat.card L := Nat.card_pos
    rw [hm] at hcle
    omega
  · exact hY

theorem isExtraspecialPGroup_pCoreOf_centralizer [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    (hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    IsExtraspecialPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer {t})) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hnL, hnφ, htA⟩ := hnA
  set e : G := n * b * n⁻¹ with he
  set M : Subgroup G := L.map (MulAut.conj n : G →* G) with hM
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set Ce : Subgroup G := Subgroup.centralizer ({e} : Set G) with hCe
  set T : Subgroup G := pCoreOf 2 C with hT
  set Q : Subgroup G := pCoreOf 2 (M ⊓ C) with hQ
  have hTQ : T ⊓ Ce = Q :=
    pCoreOf_centralizer_inf_centralizer_eq hG hS ht ht2 htb htL hn hnL hnφ htA
  have hTleC : T ≤ C := by
    rw [hT]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hT2 : IsPGroup 2 T := by
    rw [hT]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hTnorm : C ≤ Subgroup.normalizer (T : Set G) := by
    rw [hT]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hLC : L ≤ C := by
    intro l hl
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htL l hl
  have hCtN : C ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [hC, ← CFSG.centralizer_zpowers_eq_centralizer_singleton]
    exact Subgroup.centralizer_le_normalizer _
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2, pow_one]
  have hzpT : Subgroup.zpowers t ≤ T := by
    rw [hT]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ hCtN hzp2
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have htT : t ∈ T := hzpT (Subgroup.mem_zpowers t)
  have hte : t ∈ Ce := by
    rw [hCe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL e hnL).symm
  have hzpleCe : Subgroup.zpowers t ≤ Ce := Subgroup.zpowers_le.mpr hte
  have hQleT : Q ≤ T := by
    rw [← hTQ]
    exact inf_le_left
  have hQleC : Q ≤ C := hQleT.trans hTleC
  have hLnormT : L ≤ Subgroup.normalizer (T : Set G) := hLC.trans hTnorm
  have hQnonab : ¬ IsMulCommutative ↥Q := by
    obtain ⟨x, hxQ, y, hyQ, hxy⟩ :=
      exists_ne_of_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
    intro hcomm
    refine hxy ?_
    have h := hcomm.is_comm.comm ⟨x, hxQ⟩ ⟨y, hyQ⟩
    exact congrArg Subtype.val h
  have hTnonab : ¬ IsMulCommutative ↥T := by
    intro hcomm
    refine hQnonab (IsMulCommutative.of_comm ?_)
    intro a b
    apply Subgroup.inclusion_injective hQleT
    simpa using hcomm.is_comm.comm (Subgroup.inclusion hQleT a) (Subgroup.inclusion hQleT b)
  have hcommutator_ne_bot : _root_.commutator ↥T ≠ ⊥ := by
    intro hbot
    exact hTnonab ((_root_.commutator_eq_bot_iff (G := ↥T)).mp hbot)
  have hTderiv_ne_bot : ⁅T, T⁆ ≠ ⊥ := by
    rw [← Subgroup.map_subtype_commutator]
    intro hbot
    exact hcommutator_ne_bot
      (Subgroup.map_injective T.subtype_injective (by rw [hbot, Subgroup.map_bot]))
  have hS' : LocalSetting hω e M (conjEquiv φ n) Bs := hS.conj hn hnL hnφ
  have hMCe : M ≤ Ce := hS'.le_centralizer
  have hCeN : Ce ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMCe).mp hS'.normal
  have hP : ∀ {X Y : Subgroup G}, L ≤ Subgroup.normalizer (X : Set G) →
      L ≤ Subgroup.normalizer (Y : Set G) → Y ≤ Subgroup.normalizer (X : Set G) →
      ¬ 3 ∣ Nat.card Y → Y ⊓ Ce ≤ X → Y ≤ X := by
    intro X Y hLX hLY hYX hY hfix
    exact le_of_centralizer_le_of_threeA (G := G) (K := K) hS.card_K hω (L := L)
      (X := X) (Y := Y) φ hnL ⟨1, by simpa using hnφ⟩ hLX hLY hYX hY hfix
  have h3not : ∀ {Y : Subgroup G}, IsPGroup 2 Y → ¬ 3 ∣ Nat.card Y := by
    intro Y hY
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
    rw [hk]
    exact fun hd => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hClaim : ∀ N : Subgroup G, N ≤ T → Subgroup.zpowers t ≤ N →
      T ≤ Subgroup.normalizer (N : Set G) → L ≤ Subgroup.normalizer (N : Set G) →
      N = Subgroup.zpowers t ∨ N = T := by
    intro N hNT hzpN hTN hLN
    have hYleQ : N ⊓ Ce ≤ Q := by
      calc N ⊓ Ce ≤ T ⊓ Ce := inf_le_inf hNT le_rfl
        _ = Q := hTQ
    have hzpY : Subgroup.zpowers t ≤ N ⊓ Ce := le_inf hzpN hzpleCe
    have hLY : L ⊓ Ce ≤ Subgroup.normalizer ((N ⊓ Ce : Subgroup G) : Set G) := by
      have h1 : L ⊓ Ce ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hLN
      have h2 : L ⊓ Ce ≤ Subgroup.normalizer (Ce : Set G) :=
        inf_le_right.trans Subgroup.le_normalizer
      exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := Ce))
    have hYeq : N ⊓ Ce = Subgroup.zpowers t ∨ N ⊓ Ce = Q :=
      eq_or_eq_of_le_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
        hzpY hYleQ hLY
    rcases hYeq with hY | hY
    · left
      have hYle : N ⊓ Ce ≤ Subgroup.zpowers t := le_of_eq hY
      have hNle : N ≤ Subgroup.zpowers t :=
        hP (X := Subgroup.zpowers t) (Y := N) (hLC.trans hCtN) hLN
          (hNT.trans (hTleC.trans hCtN)) (h3not (hT2.to_le hNT)) hYle
      exact le_antisymm hNle hzpN
    · right
      have hQleN : Q ≤ N := by
        rw [← hY]
        exact inf_le_left
      have hfix : T ⊓ Ce ≤ N := by
        rw [hTQ]
        exact hQleN
      have hTleN : T ≤ N :=
        hP (X := N) (Y := T) hLN hLnormT hTN (h3not hT2) hfix
      exact le_antisymm hNT hTleN
  set Φ : Subgroup G := (frattini ↥T).map T.subtype with hΦ
  have hNTΦ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Φ : Set G) := by
    rw [hΦ]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := T)
      (frattini ↥T)
  have hTnormΦ : T ≤ Subgroup.normalizer (Φ : Set G) := Subgroup.le_normalizer.trans hNTΦ
  have hLnormΦ : L ≤ Subgroup.normalizer (Φ : Set G) := hLnormT.trans hNTΦ
  have hTNsup : T ≤ Subgroup.normalizer ((Φ ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
    (le_inf hTnormΦ (hTleC.trans hCtN)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Φ (Subgroup.zpowers t))
  have hLNsup : L ≤ Subgroup.normalizer ((Φ ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
    (le_inf hLnormΦ (hLC.trans hCtN)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Φ (Subgroup.zpowers t))
  have hKmapT : (Subgroup.zpowers (⟨t, htT⟩ : ↥T)).map T.subtype = Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    rfl
  have htopT : (⊤ : Subgroup ↥T).map T.subtype = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQcard : Nat.card Q = 2 ^ 9 := by
    rw [hQ]
    exact card_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
  have hΦle_zt : Φ ≤ Subgroup.zpowers t := by
    rcases hClaim (Φ ⊔ Subgroup.zpowers t)
      (sup_le (Subgroup.map_subtype_le _) hzpT) le_sup_right hTNsup hLNsup with h | h
    · calc Φ ≤ Φ ⊔ Subgroup.zpowers t := le_sup_left
        _ = Subgroup.zpowers t := h
    · exfalso
      have hsupmap : ((frattini ↥T) ⊔ Subgroup.zpowers (⟨t, htT⟩ : ↥T)).map T.subtype = T := by
        rw [Subgroup.map_sup, hKmapT, ← hΦ]
        exact h
      have hsup_top : (frattini ↥T) ⊔ Subgroup.zpowers (⟨t, htT⟩ : ↥T) = ⊤ :=
        Subgroup.map_injective T.subtype_injective (by rw [hsupmap, htopT])
      have hKtop : Subgroup.zpowers (⟨t, htT⟩ : ↥T) = ⊤ :=
        frattini_nongenerating (by rwa [sup_comm] at hsup_top)
      have hTeq : T = Subgroup.zpowers t := by
        calc T = (⊤ : Subgroup ↥T).map T.subtype := htopT.symm
          _ = (Subgroup.zpowers (⟨t, htT⟩ : ↥T)).map T.subtype := by rw [hKtop]
          _ = Subgroup.zpowers t := hKmapT
      have hQle_zt : Q ≤ Subgroup.zpowers t := hQleT.trans (le_of_eq hTeq)
      have hcard := Subgroup.card_le_of_le hQle_zt
      rw [hQcard, Nat.card_zpowers, ht2] at hcard
      norm_num at hcard
  haveI : Fact (IsPGroup 2 ↥T) := ⟨hT2⟩
  have hcomm_le_frattini : _root_.commutator ↥T ≤ frattini ↥T :=
    CFSG.commutator_le_frattini_of_isPGroup (R := ↥T) (p := 2)
  have hTderiv_le_Φ : ⁅T, T⁆ ≤ Φ := by
    rw [hΦ, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono hcomm_le_frattini
  have hTderiv_eq : ⁅T, T⁆ = Subgroup.zpowers t := by
    have hle : ⁅T, T⁆ ≤ Subgroup.zpowers t := hTderiv_le_Φ.trans hΦle_zt
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, ht2] at hcard
    have hgt : 1 < Nat.card ↥⁅T, T⁆ := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hTderiv_ne_bot
    have hcard2 : Nat.card ↥⁅T, T⁆ = 2 := by omega
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard2, Nat.card_zpowers, ht2]
  have hΦeq : Φ = Subgroup.zpowers t :=
    le_antisymm hΦle_zt ((le_of_eq hTderiv_eq.symm).trans hTderiv_le_Φ)
  have hzpQ : Subgroup.zpowers t ≤ Q := by
    rw [← hTQ]
    exact le_inf hzpT hzpleCe
  have hzpZQ : Subgroup.zpowers t ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    refine le_inf hzpQ ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro q hq
    have hqc : q ∈ C := hQleC hq
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hqc
    exact hqc
  have hNCeQ : L ⊓ Ce ≤ Subgroup.normalizer (Q : Set G) := by
    have h1 : L ⊓ Ce ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hLnormT
    have h2 : L ⊓ Ce ≤ Subgroup.normalizer (Ce : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    have h3 := (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := Ce))
    rwa [hTQ] at h3
  have hLYZQ : L ⊓ Ce ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) :
      Subgroup G) : Set G) := by
    have h3 := hNCeQ.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := Q)
        (Subgroup.center ↥Q))
    rw [map_subtype_center] at h3
    exact h3
  have hZQeq : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers t := by
    rcases eq_or_eq_of_le_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
      hzpZQ inf_le_left hLYZQ with h | h
    · exact h
    · exfalso
      have hQC : Q ≤ Subgroup.centralizer (Q : Set G) := by
        have h1 : Q ⊓ Subgroup.centralizer (Q : Set G) ≤
            Subgroup.centralizer (Q : Set G) := inf_le_right
        rwa [h] at h1
      have hcomm : IsMulCommutative ↥Q := by
        refine IsMulCommutative.of_comm ?_
        intro a b
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hQC a.2) b.1 b.2).symm
      exact hQnonab hcomm
  have hzpZ : Subgroup.zpowers t ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
    refine le_inf hzpT ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyc : y ∈ C := hTleC hy
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc
  have hfixZ : (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ Ce ≤ Subgroup.zpowers t := by
    have h1 : (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ Ce ≤ Q := by
      calc (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ Ce ≤ T ⊓ Ce :=
            inf_le_inf inf_le_left le_rfl
        _ = Q := hTQ
    have hCT : Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.centralizer_le (by intro x hx; exact hQleT hx)
    have h2 : (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ Ce ≤
        Subgroup.centralizer (Q : Set G) :=
      (inf_le_left.trans inf_le_right).trans hCT
    calc (T ⊓ Subgroup.centralizer (T : Set G)) ⊓ Ce
        ≤ Q ⊓ Subgroup.centralizer (Q : Set G) := le_inf h1 h2
      _ = Subgroup.zpowers t := hZQeq
  have hZeq : T ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers t := by
    have hLYZ : L ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set G) :
        Subgroup G) : Set G) := by
      have h3 := hLnormT.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := T)
          (Subgroup.center ↥T))
      rw [map_subtype_center] at h3
      exact h3
    have hYX : T ⊓ Subgroup.centralizer (T : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
      inf_le_left.trans (hTleC.trans hCtN)
    exact le_antisymm
      (hP (X := Subgroup.zpowers t) (Y := T ⊓ Subgroup.centralizer (T : Set G))
        (hLC.trans hCtN) hLYZ hYX (h3not (hT2.to_le inf_le_left)) hfixZ)
      hzpZ
  have hZmap : (Subgroup.center ↥T).map T.subtype =
      T ⊓ Subgroup.centralizer (T : Set G) := map_subtype_center T
  have hcommutator_map : (_root_.commutator ↥T).map T.subtype = ⁅T, T⁆ :=
    Subgroup.map_subtype_commutator T
  refine ⟨hT2, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective T.subtype_injective
    rw [hcommutator_map, hZmap, hTderiv_eq, hZeq]
  · apply Subgroup.map_injective T.subtype_injective
    rw [← hΦ, hZmap, hΦeq, hZeq]
  · calc Nat.card (Subgroup.center ↥T)
        = Nat.card ((Subgroup.center ↥T).map T.subtype) :=
          (Subgroup.card_map_of_injective T.subtype_injective).symm
      _ = Nat.card ↥(T ⊓ Subgroup.centralizer (T : Set G)) := by rw [hZmap]
      _ = Nat.card (Subgroup.zpowers t) := by rw [hZeq]
      _ = 2 := by rw [Nat.card_zpowers, ht2]

end LocalSetting

end CFSG.StandardType.USixTwo

end
