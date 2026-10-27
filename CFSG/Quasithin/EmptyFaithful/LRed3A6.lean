module

public import CFSG.Quasithin.EmptyFaithful.LRed3A6Facts
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecA

section Alt

variable {V : Type} [CommGroup V] [Finite V]

theorem lred3_alt_of_symmetric (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB : B4Hyp G L) {n : ℕ} (hn5 : 5 ≤ n) (hS : SymmetricNatural (ffJ G) ⊤ ⊥ n) :
    AlternatingNatural L ⊤ ⊥ n ∧ Nonempty (↥L ≃* ↥(alternatingGroup (Fin n))) := by
  obtain ⟨-, hLF, hq, hirr⟩ := hB
  obtain ⟨π, hR⟩ := hS
  have hπinj : Function.Injective π :=
    hR.injective_of_faithful (InternalSec.symDn_faithful hn5)
  set e : Equiv.Perm (Fin n) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hπinj, hR.1⟩ with he
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hHG : (ffJ G) ≤ G := B6.ffJ_le G
  have hGH : G ≤ Subgroup.normalizer ((ffJ G) : Set (MulAut V)) := B6.le_normalizer_ffJ G
  have hqo := B1Red.isQuasisimple_to_open hq
  have hLH : L ≤ (ffJ G) := by
    by_contra hLH
    have hcomm := B1Red.commute_of_normal_not_le hqo
      (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hGL (hHG hx)) l).mp hl)
      (fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hGH (hLG hl)) x).mp hx) hLH
    have hHe : (ffJ G) ≤ XMod.eqvAut ↥L V := by
      intro x hx a p
      exact congrArg (fun f : MulAut V => f p) (hcomm x hx a a.2)
    have hodd := InternalSec.odd_card_eqvAut_of_irr hV hirr
      (InternalSec.exists_noncomm_of_isQuasisimple hq)
    have hdvd := Subgroup.card_dvd_of_le hHe
    have hcardH : Nat.card ↥(ffJ G) = n.factorial := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    have heven : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [hcardH] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (heven.trans hdvd))
  have hLHn : (L.subgroupOf (ffJ G)).Normal := by
    refine ⟨fun l hl h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hGL (hHG h.2)) l).mp hl
  set P : Subgroup (Equiv.Perm (Fin n)) := (L.subgroupOf (ffJ G)).comap e.toMonoidHom with hP
  have hPn : P.Normal := Subgroup.Normal.comap hLHn _
  have hPmap : P.map e.toMonoidHom = L.subgroupOf (ffJ G) :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  set ePL : ↥P ≃* ↥L := (e.subgroupMap P).trans
    ((MulEquiv.subgroupCongr hPmap).trans (Subgroup.subgroupOfEquivOfLe hLH)) with hePL
  have : Group.IsPerfect ↥L := ⟨hqo.1⟩
  have hPperf : Group.IsPerfect ↥P :=
    Group.IsPerfect.ofSurjective (f := ePL.symm.toMonoidHom) ePL.symm.surjective
  have hPA : P ≤ alternatingGroup (Fin n) := by
    intro σ hσ
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp P.subtype)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact MonoidHom.mem_ker.1 (h1 (Subgroup.mem_top ⟨σ, hσ⟩))
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn5)
  have hAP : alternatingGroup (Fin n) ≤ P := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (P.subgroupOf (alternatingGroup (Fin n))) with h | h
    · exfalso
      have hPb : P = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        have h2 : (⟨σ, hPA hσ⟩ : ↥(alternatingGroup (Fin n))) ∈
            P.subgroupOf (alternatingGroup (Fin n)) := hσ
        rw [h, Subgroup.mem_bot] at h2
        exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
      have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
      obtain ⟨l, hl1⟩ := exists_ne (1 : ↥L)
      apply hl1
      have h2 : ePL.symm l = 1 := by
        apply Subtype.ext
        have h3 : ((ePL.symm l : ↥P) : Equiv.Perm (Fin n)) ∈
            (⊥ : Subgroup (Equiv.Perm (Fin n))) := by
          rw [← hPb]
          exact (ePL.symm l).2
        exact Subgroup.mem_bot.1 h3
      rw [← ePL.apply_symm_apply l, h2, map_one]
    · intro σ hσ
      have h2 : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) ∈
          P.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]
        trivial
      exact h2
  set π' : ↥(alternatingGroup (Fin n)) →* ↥L :=
    ePL.toMonoidHom.comp (Subgroup.inclusion hAP) with hπ'
  have hπ'bij : Function.Bijective π' := by
    refine ⟨ePL.injective.comp (Subgroup.inclusion_injective hAP), fun l => ?_⟩
    obtain ⟨x, rfl⟩ := ePL.surjective l
    exact ⟨⟨x, hPA x.2⟩, congrArg ePL (Subtype.ext rfl)⟩
  obtain ⟨-, h1, h2, -, h4, h5', h6, β, hβs, hβk, hβe⟩ := id hR
  exact ⟨⟨π', hπ'bij.2, h1, h2, fun _ _ _ => trivial,
    fun l z hz => h4 ⟨l, hLH l.2⟩ z hz,
    fun (γ : ↥(alternatingGroup (Fin n))) m hm => h5' (γ : Equiv.Perm (Fin n)) m hm,
    fun (γ : ↥(alternatingGroup (Fin n))) m hm => h6 (γ : Equiv.Perm (Fin n)) m hm,
    β, hβs, hβk, fun (γ : ↥(alternatingGroup (Fin n))) u m hu hm hum =>
      hβe (γ : Equiv.Perm (Fin n)) u m hu hm hum⟩,
    ⟨(MulEquiv.ofBijective π' hπ'bij).symm⟩⟩

end Alt

section B42

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem lred3_b42_alt6 (hF : Facts10_1) (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L)
    (hA : IsFFStarOffender G A) (hc : B42Conclusion G L A) (hAlt : IsAlt 6 ↥L) :
    AlternatingNatural L ⊤ ⊥ 6 := by
  have hL := A6Target.of_isAlt hAlt
  have := hL.isSimple
  have := hL.nontrivial
  have hnc := hL.noncomm
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have one_le : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hc with ⟨-, ⟨n, hnat⟩, -, -⟩ | ⟨-, ⟨n, hnat⟩, -⟩ | ⟨⟨n, hsp, hJ⟩, -⟩ |
      ⟨⟨n, hg2, hrk, hJ⟩, -⟩ | h5 | c6 | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hcL : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hFc]
    exact (lred3_sl2_ne_360 (one_le hFc) (hcL.symm.trans hL.card)).elim
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hcL : Nat.card ↥L = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hFc]
    exact (lred3_sl3_ne_360 (one_le hFc) (hcL.symm.trans hL.card)).elim
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h1 : 1 ≤ n := by
        obtain ⟨K, _, _, hKc, -⟩ := hsp
        exact one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      exact (lred3_alt_of_symmetric hV hB (by norm_num)
        (B5FinSp.symmetricNatural_six_of_binaryNaturalSp4 hsp)).1
    · rw [hJ (by omega)] at hsp
      obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
      have hcL : Nat.card ↥L = 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
        rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hFc]
      exact (lred3_sp4_ne_360 (one_le hFc) (hcL.symm.trans hL.card)).elim
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
      have h1 := one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      have hLJ : L ≤ ffJ G := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL) h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := hF.g2Two K (by rw [hKc]; norm_num) _ π hR.1 _ hLn hq
      have hcL : Nat.card ↥L = 6048 := by rw [← Nat.card_congr eL.toEquiv, h6048]
      rw [hL.card] at hcL
      norm_num at hcL
    ·
      have hAL : A ≤ L := (hJ (by omega)) ▸ B19.le_ffJ hA
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥A := hA.2.2.1.isPGroup
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
      have hrk' : rk ↥A = k := by rw [rk, hk, padicValNat.prime_pow]
      have hk3 : k = 3 * n := hrk'.symm.trans hrk
      have hdvd : Nat.card ↥A ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hAL
      rw [hk, hk3, hL.card] at hdvd
      have := lred3_le_three_of_two_pow_dvd hdvd
      omega
  ·
    obtain ⟨m, hm, -, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    have h360 := hL.card
    rcases hm with rfl | rfl
    · rw [Nat.card_congr e.toEquiv, card_alt 5 (by norm_num)] at h360
      norm_num [Nat.factorial] at h360
    · rw [Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)] at h360
      norm_num [Nat.factorial] at h360
  ·
    exact c6.2.1
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π hR.1
    have h360 := hL.card
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)] at h360
    norm_num [Nat.factorial] at h360
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    have h360 := hL.card
    rcases hn with rfl | rfl
    · rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hF2] at h360
      norm_num at h360
    · rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hF2] at h360
      norm_num at h360
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 4) (by norm_num)) π hR.1
    have h360 := hL.card
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_two] at h360
    norm_num at h360
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 5) (by norm_num)) π hR.1
    have h360 := hL.card
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_two] at h360
    norm_num at h360

end B42

section Table

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem lred3_table_alt6 (hFA : FactsA6) (ht : AsB45Table G L)
    (hAlt : IsAlt 6 ↥L) : False := by
  have hL := A6Target.of_isAlt hAlt
  have := hL.isSimple
  have := hL.nontrivial
  have hnc := hL.noncomm
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, hsz, -⟩ | ⟨m, hm, ⟨K, _, _, _, hK, π, hR⟩, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨⟨eY, heY, hw, π, hR⟩, -⟩ | ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ |
      ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨h2324, -⟩
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π hR.1
    have h360 := hL.card
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)] at h360
    norm_num [Nat.factorial] at h360
  ·
    obtain ⟨K, _, _, _, hK, π, hR⟩ := horth
    have hinj := hR.injective_of_faithful (twistTensor_faithful (F := K) m)
    have hcG : Nat.card ↥(StatedSL 2 K) = 2 ^ (2 * m) * (4 ^ (2 * m) - 1) := by
      rw [card_statedSL, card_SL_two_pow hK]
    have hcL : Nat.card ↥L = 2 ^ (2 * m) * (4 ^ (2 * m) - 1) := by
      rw [← hcG]
      exact (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hR.1⟩).toEquiv).symm
    exact lred3_sl2_ne_360 (by omega) (hcL.symm.trans hL.card)
  · exact hFA.su3 K m hK _ hAlt π hR.1
  ·
    obtain ⟨a, K, _, _, ha, hf, hK, ⟨e⟩⟩ := hsz.exists_equiv
    subst hf
    have hcL : Nat.card ↥L = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
      rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    exact lred3_suzuki_ne_360 (hcL.symm.trans hL.card)
  · exact hFA.nineTensor K m hm hK _ hAlt π hR.1
  · exact hFA.g2Derived K (by rw [hK]; norm_num) _ hAlt π hR.1
  · exact hFA.m12 eY heY hw _ hAlt π hR.1
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  · exact hFA.m22 x y hxy _ hAlt π hR.1
  · exact hFA.m22 x y hxy _ hAlt π hR.1
  · rcases h2324 with ⟨x, π, hR⟩ | ⟨x, π, hR⟩ | ⟨π, hR⟩ | ⟨π, hR⟩
    · exact hFA.m23 x _ hAlt π hR.1
    · exact hFA.m23 x _ hAlt π hR.1
    all_goals exact hFA.m24 _ hAlt π hR.1

theorem lred3_part3_alt6 (hFA : FactsA6) (h3 : AsB45Part3 G L) (hAlt : IsAlt 6 ↥L) : False := by
  obtain ⟨-, -, ⟨a, ha, K, _, _, _, hK, π, hR⟩ | ⟨hJ2, -, -⟩⟩ := h3
  · exact hFA.sp4Twisted K a ha hK _ hAlt π hR.1
  · exact hFA.j2 _ hAlt hJ2

end Table

end CFSG.Quasithin
