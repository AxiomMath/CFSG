module

public import CFSG.Open.FusionDefs
public import CFSG.Open.SignalizerFunctorDefs
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.NearSolvable
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

theorem fusionStronglyEmbedded_inf_subgroupOf {Y : Type*} [Group Y] [Finite Y] {B H : Subgroup Y}
    (hB : fusionStronglyEmbedded B) (hHB : ¬ H ≤ B) (hev : ∃ u ∈ H ⊓ B, orderOf u = 2) :
    fusionStronglyEmbedded ((H ⊓ B).subgroupOf H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hHB (htop.trans inf_le_right)
  · obtain ⟨u, hu, hu2⟩ := hev
    have hmem : (⟨u, hu.1⟩ : H) ∈ (H ⊓ B).subgroupOf H := hu
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, hu2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · intro g hg
    have hgB : (g : Y) ∉ B := fun hgB => hg ⟨g.2, hgB⟩
    have hodd := hB.2.2 (g : Y) hgB
    have hle : ((((H ⊓ B).subgroupOf H) ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ≤
        B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨hy1.2, ?_⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy2
      refine Subgroup.mem_map.mpr ⟨(z : Y), hz.2, ?_⟩
      simp
    have hdvd : Nat.card ↥(((H ⊓ B).subgroupOf H ⊓
        ((H ⊓ B).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype) ∣
        Nat.card ↥(B ⊓ B.map (MulAut.conj (g : Y)⁻¹).toMonoidHom) :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact hodd.of_dvd_nat hdvd

private theorem exists_fusionBenderBorel_of_fusionIsBenderGroup {X : Type*} [Group X] [Finite X]
    (h : fusionIsBenderGroup X) : ∃ q k : ℕ, fusionBenderBorel X q k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩

theorem exists_noncommuting_of_fusionIsBenderGroup {X : Type*} [Group X] [Finite X]
    (h : fusionIsBenderGroup X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup h
  obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hcomm : IsMulCommutative X := ⟨⟨fun a b => hcon a b⟩⟩
  have hnorm : (Q : Subgroup X).Normal := ⟨fun n hn g => by
    rw [hcon g n]
    simpa using hn⟩
  exact (hB Q).1.1 (Subgroup.normalizer_eq_top_iff.mpr hnorm)

theorem nonempty_mulEquiv_psl2Even_of_dvd
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {H : Subgroup (PSU3 2 p)} (hH : H ≠ ⊤) {S : Type*} [Group S]
    (hS : signalizerNearSimpleModel p S) (hdvd : Nat.card S ∣ Nat.card H) :
    Nonempty (S ≃* PSL(2, GaloisField 2 p)) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcard := card_psu3_of_odd hodd
  have h5' := two_pow_mod_five hodd
  have h9 := two_pow_mod_nine (prime_mod_six hp hp2 hp3)
  have hdvdY : Nat.card S ∣ Nat.card (PSU3 2 p) := hdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rcases hS with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨e⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_psl2_three hp.ne_zero, hcard] at hdvdY
    exact not_twentyseven_dvd_psu3 h9
      ((twentyseven_dvd_three_pow (by omega)).trans
        ((three_pow_dvd_psl2_three p).trans hdvdY))
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_sz, ← hn, hcard] at hdvdY
    exact not_five_dvd_unitary h5'
      ((((five_dvd_sq_add_one h5').mul_left _).mul_right _).trans
        (hdvdY.trans (psu3_order_dvd (by omega))))
  · exfalso
    apply hH
    exact eq_top_of_card_dvd (by rw [← Nat.card_congr e.toEquiv]; exact hdvd)

theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {x : X} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem sq_eq_one_of_mem_sylow_psl2Even {p : ℕ} (hp : 2 ≤ p)
    (Q : Sylow 2 PSL(2, GaloisField 2 p)) {x : PSL(2, GaloisField 2 p)}
    (hx : x ∈ (Q : Subgroup PSL(2, GaloisField 2 p))) : x ^ 2 = 1 := by
  obtain ⟨-, -, hpow, hcenter, hcard⟩ := bender_psl2_borel_full p hp Q
  have htop : Subgroup.center ↥(Q : Subgroup PSL(2, GaloisField 2 p)) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hcenter, hcard, pow_one]
  have hz := hpow ⟨x, hx⟩ (by rw [htop]; trivial)
  exact congrArg Subtype.val hz

theorem sq_eq_one_of_isBenderSection
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) {H : Subgroup (PSU3 2 p)} (hH : H ≠ ⊤)
    {M N : Subgroup ↥H} [M.Normal] [N.Normal] [(M.subgroupOf N).Normal]
    (hMo : Odd (Nat.card M)) (hNo : Odd N.index)
    (hB : fusionIsBenderGroup (↥N ⧸ M.subgroupOf N)) {s : ↥H} {k : ℕ} (hs : s ^ 2 ^ k = 1) :
    s ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (↥N ⧸ M.subgroupOf N) := inferInstance
  have hsimple := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hnab := exists_noncommuting_of_fusionIsBenderGroup hB
  have hsecH : IsSectionOf (↥N ⧸ M.subgroupOf N) ↥H :=
    (IsSectionOf.of_surjective (QuotientGroup.mk' (M.subgroupOf N))
      (QuotientGroup.mk'_surjective _)).trans (IsSectionOf.of_subgroup N)
  have hsecY : IsSectionOf (↥N ⧸ M.subgroupOf N) (PSU3 2 p) :=
    hsecH.of_injective H.subtype H.subtype_injective
  have hmodel := nearSimpleModel_of_isSectionOf hnear hnab hsecY
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Even_of_dvd hp h5 hH hmodel (card_dvd_of_isSectionOf hsecH)
  have hsN : s ∈ N := by
    have hq : QuotientGroup.mk' N s = 1 := by
      have h1 : orderOf (QuotientGroup.mk' N s) ∣ 2 ^ k := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, hs, map_one]
      have h2 : orderOf (QuotientGroup.mk' N s) ∣ N.index := by
        have := orderOf_dvd_natCard (QuotientGroup.mk' N s)
        rwa [← Subgroup.index_eq_card] at this
      have hcop : Nat.Coprime (2 ^ k) N.index :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hNo)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    exact (QuotientGroup.eq_one_iff s).mp hq
  set y : ↥N := ⟨s, hsN⟩ with hy
  have hy2k : y ^ 2 ^ k = 1 := Subtype.ext hs
  let π : ↥N →* PSL(2, GaloisField 2 p) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (M.subgroupOf N))
  have hzp : IsPGroup 2 (Subgroup.zpowers (π y)) :=
    isPGroup_zpowers_of_pow_eq_one (k := k) (by rw [← map_pow, hy2k, map_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hπy : (π y) ^ 2 = 1 :=
    sq_eq_one_of_mem_sylow_psl2Even hp.two_le Q (hQ (Subgroup.mem_zpowers _))
  have hker : y ^ 2 ∈ M.subgroupOf N := by
    have h1 : π (y ^ 2) = 1 := by rw [map_pow, hπy]
    have h2 : (QuotientGroup.mk' (M.subgroupOf N)) (y ^ 2) = 1 := by
      have : e ((QuotientGroup.mk' (M.subgroupOf N)) (y ^ 2)) = 1 := h1
      exact (map_eq_one_iff e e.injective).mp this
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hs2M : s ^ 2 ∈ M := hker
  have hdvdM : orderOf (s ^ 2) ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hs2M
  have hdvd2 : orderOf (s ^ 2) ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_right_comm, hs, one_pow]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card M) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hMo)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdM)

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
