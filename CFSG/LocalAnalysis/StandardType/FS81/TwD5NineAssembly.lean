module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineO2
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineNorm
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineCore
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.GroupTheory.TwoReflections

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem t5NineO2_of_pieces (h92 : T5Nine92) (hmod : T5NineModel) (hK : T5TwoLocalK) :
    T5NineO2 := by
  intro G _ _ b₀ K E hstd hKproper hchar B hB hrec hfus hodd t ht ht0 ht1 ht2 Q hQ hQH hHQ
  have hD := odd_card_centralizer_inf_of_isCharTwoType hstd hchar hB hrec hfus
  have htN0 : t ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * b₀ * t⁻¹) = Subgroup.zpowers b₀
    have hta : t * b₀ * t⁻¹ = b₀⁻¹ := by simpa [hB.2.1] using ht0
    rw [hta, Subgroup.zpowers_inv]
  have htK : t ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_mem_normalizer_zpowers hstd hB hrec hodd hD htN0
  set N : Subgroup G := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) with hNdef
  set J : Subgroup G := nineJ K (B.b 2) with hJdef
  have hCN : Subgroup.centralizer ({B.b 2} : Set G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [hNdef]
    have hNC : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) ≤
        Subgroup.centralizer ({B.b 2} : Set G) :=
      Subgroup.map_subtype_le (pPrimeCore 3 _)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mp
      (gLAPPrimeCoreOf_normal 3 _)
  have hB2E : B.b 2 ∈ E := by
    rw [← hB.1]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef]
    exact odd_card_primeCore_centralizer_of_twoLocalK hK hstd hB hrec hD hB2E
  have hb₀b2 : b₀ * B.b 2 = B.b 2 * b₀ := by
    rw [← hB.2.1]
    exact (B.comm 0 2).eq
  have hb₀C : b₀ ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hb₀b2
  have hb2C : B.b 2 ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have htC : t ∈ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ht2 2 (by norm_num)
  have hJb : J ≤ Subgroup.centralizer ({B.b 2} : Set G) := by
    rw [hJdef]
    unfold nineJ
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hJK : J ≤ K := by
    rw [hJdef]
    unfold nineJ
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hJa : J ≤ Subgroup.centralizer ({b₀} : Set G) := hJK.trans hKC
  have haN : b₀ ∈ Subgroup.normalizer (N : Set G) := hCN hb₀C
  have hbN : B.b 2 ∈ Subgroup.normalizer (N : Set G) := hCN hb2C
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := hJb.trans hCN
  have htN : t ∈ Subgroup.normalizer (N : Set G) := hCN htC
  have htNC : t ∈ Subgroup.normalizer
      (Subgroup.centralizer ({B.b 2} : Set G) : Set G) := Subgroup.le_normalizer htC
  set H : Subgroup G := K ⊓ Subgroup.centralizer ({B.b 2} : Set G) with hHdef
  have htH : t ∈ Subgroup.normalizer (H : Set G) := by
    rw [hHdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := K)
      (K := Subgroup.centralizer ({B.b 2} : Set G))
      (Subgroup.mem_inf.mpr ⟨htK, htNC⟩)
  have htJ : t ∈ Subgroup.normalizer (J : Set G) := by
    rw [hJdef]
    unfold nineJ
    rw [hHdef] at htH
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htH ⊢
    rw [Subgroup.map_commutator, htH]
  obtain ⟨hJsimple, hMsimple, hM6, hJM⟩ :=
    hmod G b₀ K E hstd B hB hrec t ht htK ht1 ht2
  have hH := h92 G b₀ K E hstd hKproper hchar B hB hrec hfus hodd t ht ht0 ht1 ht2
  have hb₀3 : b₀ ^ 3 = 1 := by
    have hb₀ord : orderOf b₀ = 3 := hstd.2.1.1
    simpa [hb₀ord] using pow_orderOf_eq_one b₀
  exact le_zpowers_of_le_sup_simple (t := t) (a := b₀) (b := B.b 2)
    (N := N) (J := J) (Q := Q)
    (by simpa [ht] using pow_orderOf_eq_one t) hb₀3
    (by simpa [B.ord 2] using pow_orderOf_eq_one (B.b 2))
    hNodd haN hbN hJN htN hb₀b2 hJa hJb
    (by simpa [hB.2.1] using ht0) (ht2 2 (by norm_num))
    htJ hJsimple hMsimple hM6 hJM hQ hQH hHQ
    (by simpa [hNdef, hJdef] using hH)

theorem t5Nine_of_pieces (h92 : T5Nine92) (hmod : T5NineModel) (hK : T5TwoLocalK) : T5Nine :=
  t5Nine_of_o2 (t5NineO2_of_pieces h92 hmod hK)

end CFSG.StandardType.FrameRoute.FS81

end
