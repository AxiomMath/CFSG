module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42Gen
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open (pCoreOf)
open CFSG.Blueprint
open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem mem_of_mem_normalizer_m24
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .M24)) {B : Subgroup X}
    (hB : Nat.card B = 2 ^ 10 * 315) {k : X} (hk : k ∈ Subgroup.normalizer (B : Set X)) :
    k ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hX
  have hXc : Nat.card X = 2 ^ 10 * 239085 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_card
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥B) := inferInstance
  set T : Subgroup X := (T₀ : Subgroup ↥B).map B.subtype with hT
  have hTB : T ≤ B := Subgroup.map_subtype_le _
  have hTp : IsPGroup 2 T := T₀.isPGroup'.map B.subtype
  have hBi : B.index = 759 := by
    have h1 := Subgroup.card_mul_index B
    rw [hB, hXc] at h1
    omega
  have hTrel : T.relIndex B = (T₀ : Subgroup ↥B).index := by
    unfold Subgroup.relIndex
    rw [hT, show ((T₀ : Subgroup ↥B).map B.subtype).subgroupOf B = T₀ from
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _]
  have hTi : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_mul_index hTB, hTrel, hBi]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
    · exact T₀.not_dvd_index h1
    · omega
  have hTS : IsSylowTwoOf T ⊤ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨hTp, hTi⟩
  set N := Subgroup.normalizer (B : Set X) with hN
  have hBN : B ≤ N := Subgroup.le_normalizer
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups ⟨e⟩ hTS (hTB.trans hBN) with
    htop | ⟨m, hm, hNc, -, -⟩
  · exfalso
    have hS : IsSimpleGroup X :=
      @MulEquiv.isSimpleGroup X _ (NativeSporadic.Carrier .M24) _
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 e
    have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hBn.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot] at hB
      omega
    · rw [ht, Subgroup.card_top, hXc] at hB
      omega
  · have hle : ∀ m' ∈ CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems, m'.order ≤ 2 ^ 10 * 315 := by
      decide
    have hNB : N = B := (Subgroup.eq_of_le_of_card_ge hBN (by
      rw [hNc, hB]
      exact hle m hm)).symm
    rw [← hNB]
    exact hk

theorem exists_inner_m24_sub
    {Q : Type} [Group Q] [Finite Q] {K B : Subgroup Q}
    (hK : IsSporadic .M24 ↥K) (hBK : B ≤ K)
    (hB : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y)) {g : Q}
    (hgK : g ∈ Subgroup.normalizer (K : Set Q)) (hgB : g ∈ Subgroup.normalizer (B : Set Q)) :
    ∃ b ∈ B, ∀ x ∈ B, (g * x * g⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B := by
  obtain ⟨eK⟩ := hK
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.autInner_of_equiv_of_inner eK
    CFSG.QuasithinUnique.Ch1.m24_all_inner (L139A5.conjSub hgK)
  have hk : L139A5.conjSub hgK = MulAut.conj l⁻¹ := by
    ext x : 1
    rw [hl x, MulAut.conj_apply, inv_inv]
  obtain ⟨V, hVn, ⟨eV⟩, hY⟩ := hB
  have hcard : Nat.card ↥(B.subgroupOf K) = 2 ^ 10 * 315 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup V, Ch1Four.card_of_isPSL_four_two hY,
      Nat.card_congr eV.toEquiv]
    change 20160 * Nat.card (Fin 4 → ZMod 2) = _
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hmem := mem_of_mem_normalizer_m24 ⟨eK⟩ hcard (mem_normalizer_of_conj hgK hgB hk)
  refine exists_inner_of_conj hBK hgK hk ⟨l⁻¹, hmem, fun x _ => ?_⟩
  rw [inv_mul_cancel]
  exact one_mem _

end CFSG.Quasithin.L139L42
