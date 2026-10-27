module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Defs

import CFSG.Adapters.StatedPSLTwo
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13h
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.FrattiniSylow
import CFSG.RankThree.PartTwo.Sec21.FF84S4PreD0
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_isStronglyPEmbedded {M X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : IsStronglyPEmbedded p M) (hXM : X ≤ M) (hX : IsPGroup p X) (hX1 : X ≠ ⊥) :
    normalizer (X : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsStronglyPEmbedded.normalizer_le hM hX1 hX hXM

private theorem exists_sylow_inf_of_isStronglyPEmbedded {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p T (D.M ⊓ N) ∧ D₀ ≤ T ∧
      normalizer (T : Set G) ≤ D.M := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hHN : H ≤ N := c.memN.2
  have hKN : F08.KOf8103 L B ≤ N := c.memH.2.2.1.trans hHN
  have hD0N : D₀ ≤ N := c.le_D₀.trans hKN
  have hD0M : D₀ ≤ D.M := c.le_D₀.trans (c.memH.2.2.1.trans c.memH.1)
  have hD0p : IsPGroup p D₀ := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [c.card_D₀, pow_one]⟩
  have hD0ne : D₀ ≠ ⊥ := by
    intro h
    have hcard : Nat.card D₀ = 1 := by rw [h, Subgroup.card_bot]
    rw [c.card_D₀] at hcard
    exact c.prime.ne_one hcard
  obtain ⟨T, hD0T, hTsyl⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hD0p (le_inf hD0M hD0N)
  have hTp : IsPGroup p T := hTsyl.isPGroup
  have hTM : T ≤ D.M := hTsyl.le.trans inf_le_left
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hD0T
    exact hD0ne (le_bot_iff.mp hD0T)
  exact ⟨T, hTsyl, hD0T, normalizer_le_of_isStronglyPEmbedded c.prime c.strong hTM hTp hTne⟩

theorem isCyclic_of_le {D : Data G} {L P B B' D₀ H N X : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hXN : X ≤ N) (hX : IsPGroup p X) : IsCyclic X := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  by_cases hXbot : X = ⊥
  · rw [hXbot]
    exact isCyclic_of_subsingleton
  by_contra hXnc
  obtain ⟨T, hTsyl, hD0T, hnormT⟩ := exists_sylow_inf_of_isStronglyPEmbedded c
  have hTp : IsPGroup p T := hTsyl.isPGroup
  have hTM : T ≤ D.M := hTsyl.le.trans inf_le_left
  have hTsylN : CFSG.ABGLocalTools.IsSylowOf p T N :=
    CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hTsyl (inf_le_left.trans hnormT)
  obtain ⟨S, hXS, hSsyl⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hX hXN
  obtain ⟨k, hkN, hk⟩ := hTsylN.exists_mem_conj hSsyl
  have hle : X.map (MulAut.conj k⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using (hk x).mp (hXS hx)
  have hXmap_nc : ¬ IsCyclic (X.map (MulAut.conj k⁻¹).toMonoidHom) := by
    intro hcyc
    have e : X ≃* X.map (MulAut.conj k⁻¹).toMonoidHom :=
      Subgroup.equivMapOfInjective X (MulAut.conj k⁻¹).toMonoidHom
        (MulAut.conj k⁻¹).injective
    exact hXnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hTnc : ¬ IsCyclic T := by
    intro hTcyc
    haveI : IsCyclic T := hTcyc
    exact hXmap_nc (Subgroup.isCyclic_of_le hle)
  have hpSig : p ∈ D.sig := c.hyp.2.2.2.1
  have huniq := c.r61 p hpSig T hTM hTp hTnc
  have hNcal : N ∈ calMOf T := ⟨c.memN.1, hTsylN.le⟩
  have hNmem : N ∈ ({D.M} : Set (Subgroup G)) := huniq ▸ hNcal
  exact c.neN (by simpa using hNmem)

private theorem le_relPPrimeCore_of_dvd_card {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hdiv : p ∣ Nat.card (relPPrimeCore 3 N)) : D₀ ≤ relPPrimeCore 3 N := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  let I := relPPrimeCore 3 N
  have hHN : H ≤ N := c.memN.2
  have hKN : F08.KOf8103 L B ≤ N := c.memH.2.2.1.trans hHN
  have hD0N : D₀ ≤ N := c.le_D₀.trans hKN
  have hD0p : IsPGroup p D₀ := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [c.card_D₀, pow_one]⟩
  have hIle : I ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hInorm : (I.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have hCn : ∀ k ∈ N, ∀ x ∈ I, k * x * k⁻¹ ∈ I := by
    intro k hk x hx
    have hmem := hInorm.conj_mem (⟨x, hIle hx⟩ : ↥N) (Subgroup.mem_subgroupOf.mpr hx)
      (⟨k, hk⟩ : ↥N)
    have hcoe := Subgroup.mem_subgroupOf.mp hmem
    simpa [mul_assoc] using hcoe
  obtain ⟨Q, hQN, hD0Q, hQp, hQdvd⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec13h.sylow_inf_normal_dvd N I D₀ hIle hCn
      hD0N hD0p
  have hQcyc : IsCyclic Q := isCyclic_of_le c hQN hQp
  have hpos : 0 < (Nat.card I).factorization p :=
    Nat.Prime.factorization_pos_of_dvd c.prime Nat.card_pos.ne' hdiv
  have hpPow : p ∣ p ^ (Nat.card I).factorization p := dvd_pow_self p hpos.ne'
  have hpInf : p ∣ Nat.card ↥(Q ⊓ I) := hpPow.trans hQdvd
  have hleSub : D₀.subgroupOf Q ≤ (Q ⊓ I).subgroupOf Q := by
    haveI : IsCyclic Q := hQcyc
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    have hcard0 : Nat.card (D₀.subgroupOf Q) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD0Q).toEquiv, c.card_D₀]
    have hcard1 : Nat.card ↥((Q ⊓ I).subgroupOf Q) = Nat.card ↥(Q ⊓ I) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hcard0, hcard1]
    exact hpInf
  have hD0Inf : D₀ ≤ Q ⊓ I := by
    have hmap := Subgroup.map_mono (f := Q.subtype) hleSub
    rwa [Subgroup.map_subgroupOf_eq_of_le hD0Q,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  exact hD0Inf.trans inf_le_right

private theorem eq_bot_of_normal_of_coprime_card {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {J : Subgroup X} (hJ : J.Normal) {q : ℕ} (hq : q.Prime)
    (hcop : Nat.Coprime q (Nat.card J)) (hdvd : q ∣ Nat.card X) : J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J with h | h
  · exact h
  · exfalso
    rw [h] at hcop
    have hXcop : Nat.Coprime q (Nat.card X) := by simpa using hcop
    exact hq.ne_one (hXcop.eq_one_of_dvd hdvd)

private theorem three_dvd_card_bar2 {K B' : Subgroup G} (hB'K : B' ≤ K)
    (hB'card : Nat.card B' = 3) : 3 ∣ Nat.card (Bar2 K) := by
  have h3K : 3 ∣ Nat.card ↥K := by
    have h : Nat.card B' ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hB'K
    rwa [hB'card] at h
  have hcardK := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have h3pc : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [hk]
    intro h
    exact absurd (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two h) (by norm_num)
  have h := Nat.prime_three.dvd_mul.mp (by rw [← hcardK]; exact h3K)
  exact h.resolve_right h3pc

private theorem inf_relPPrimeCore_KOf8103_le_pCoreOf_two {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    relPPrimeCore 3 N ⊓ F08.KOf8103 L B ≤ pCoreOf 2 (F08.KOf8103 L B) := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  let I := relPPrimeCore 3 N
  let K := F08.KOf8103 L B
  have hKN : K ≤ N := c.memH.2.2.1.trans c.memN.2
  have hIle : I ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hInorm : (I.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  have hJnorm : ((I ⊓ K).subgroupOf K).Normal := by
    haveI : (I.subgroupOf N).Normal := hInorm
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A := N) (A' := I) (B := K)
    rwa [inf_eq_right.mpr hKN] at h
  let J : Subgroup ↥K := (I ⊓ K).subgroupOf K
  let q : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hJmapNormal : (J.map q).Normal := hJnorm.map q (QuotientGroup.mk'_surjective _)
  have hIcop : Nat.Coprime 3 (Nat.card I) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three N
  have hIKcop : Nat.Coprime 3 (Nat.card ↥(I ⊓ K)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hIcop
  have hJcop : Nat.Coprime 3 (Nat.card J) := by
    have hcard : Nat.card J = Nat.card ↥(I ⊓ K) := by
      change Nat.card ↥((I ⊓ K).subgroupOf K) = Nat.card ↥(I ⊓ K)
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := I ⊓ K) (K := K) inf_le_right).toEquiv
    rw [hcard]
    exact hIKcop
  have hJmapCop : Nat.Coprime 3 (Nat.card (J.map q)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd J q) hJcop
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two c.notB.2.2
  have hJbot := eq_bot_of_normal_of_coprime_card hJmapNormal Nat.prime_three hJmapCop
    (three_dvd_card_bar2 c.le c.notB'.1)
  have hJle : J ≤ CFSG.pCore 2 ↥K := by
    have h := (Subgroup.map_eq_bot_iff J (f := q)).mp hJbot
    simpa [q] using h
  have hmap := Subgroup.map_mono (f := K.subtype) hJle
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at hmap
  simpa [K, CFSG.Open.pCoreOf] using hmap

private theorem le_pCoreOf_two_of_le_relPPrimeCore {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hD0I : D₀ ≤ relPPrimeCore 3 N) : D₀ ≤ pCoreOf 2 (F08.KOf8103 L B) :=
  (le_inf hD0I c.le_D₀).trans (inf_relPPrimeCore_KOf8103_le_pCoreOf_two c)

theorem not_dvd_card_relPPrimeCore {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : ¬ p ∣ Nat.card (relPPrimeCore 3 N) := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  intro hdiv
  have hpSig : p ∈ D.sig := c.hyp.2.2.2.1
  have hp2 : p ≠ 2 := (D.sig_prime p hpSig).2
  have hD0I : D₀ ≤ relPPrimeCore 3 N := le_relPPrimeCore_of_dvd_card c hdiv
  have hD0O2 : D₀ ≤ pCoreOf 2 (F08.KOf8103 L B) :=
    le_pCoreOf_two_of_le_relPPrimeCore c hD0I
  have hO2 : IsPGroup 2 (pCoreOf 2 (F08.KOf8103 L B)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (F08.KOf8103 L B)
  have hD02 : IsPGroup 2 D₀ := hO2.to_le hD0O2
  rcases hD02.card_eq_or_dvd with h | h
  · rw [c.card_D₀] at h
    exact c.prime.ne_one h
  · rw [c.card_D₀] at h
    exact (c.prime.odd_of_ne_two hp2).not_two_dvd_nat h


private theorem derInf8_map_conj (X : Subgroup G) (g : G) :
    F08.DerInf8 (X.map (MulAut.conj g).toMonoidHom) =
      (F08.DerInf8 X).map (MulAut.conj g).toMonoidHom := by
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
    (MulAut.conj g).toMonoidHom X
  simpa only [F08.DerInf8, CFSG.perfectResidual] using h.symm

private theorem KOf8103_map_conj {L Z : Subgroup G} {w : G}
    (hw : w ∈ normalizer (L : Set G)) :
    F08.KOf8103 L (Z.map (MulAut.conj w).toMonoidHom) =
      (F08.KOf8103 L Z).map (MulAut.conj w).toMonoidHom := by
  have hmc := CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv (MulAut.conj w) (Z : Set G)
  have himg : MulAut.conj w '' (Z : Set G) =
      (Z.map (MulAut.conj w).toMonoidHom : Set G) := by
    ext x
    simp [Subgroup.mem_map]
  have hL : L.map (MulAut.conj w).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hcent : Subgroup.centralizer (Z.map (MulAut.conj w).toMonoidHom : Set G) =
      (Subgroup.centralizer (Z : Set G)).map (MulAut.conj w).toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom, himg] using hmc.symm
  have hInf : L ⊓ Subgroup.centralizer (Z.map (MulAut.conj w).toMonoidHom : Set G) =
      (L ⊓ Subgroup.centralizer (Z : Set G)).map (MulAut.conj w).toMonoidHom := by
    rw [hcent]
    conv_lhs => rw [← hL]
    rw [← Subgroup.map_inf_eq L (Subgroup.centralizer (Z : Set G))
      (MulAut.conj w).toMonoidHom (MulAut.conj w).injective]
  unfold F08.KOf8103
  rw [hInf]
  exact derInf8_map_conj _ w

private theorem nonempty_bar2_map_conj {K : Subgroup G} {w : G} :
    Nonempty (Bar2 K ≃* Bar2 (K.map (MulAut.conj w).toMonoidHom)) := by
  let e : ↥K ≃* ↥(K.map (MulAut.conj w).toMonoidHom) :=
    Subgroup.equivMapOfInjective K (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  have hpker : IsPGroup 2 e.toMonoidHom.ker := by rw [hker]; exact IsPGroup.of_bot
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
    (p := 2) e.toMonoidHom e.surjective hpker

private theorem notationB_map_conj {L P : Subgroup G} {n : ℕ} {Z : Subgroup G} {w : G}
    (hZ : F08.NotationB8103 L P n Z) (hZP : Z.map (MulAut.conj w).toMonoidHom ≤ P)
    (hwL : w ∈ normalizer (L : Set G)) :
    F08.NotationB8103 L P n (Z.map (MulAut.conj w).toMonoidHom) := by
  refine ⟨?_, hZP, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hZ.1
  · obtain ⟨eBar⟩ := nonempty_bar2_map_conj (K := F08.KOf8103 L Z) (w := w)
    let eBar' : Bar2 (F08.KOf8103 L Z) ≃*
        Bar2 (F08.KOf8103 L (Z.map (MulAut.conj w).toMonoidHom)) :=
      (KOf8103_map_conj (L := L) (Z := Z) (w := w) hwL) ▸ eBar
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar' hZ.2.2

private theorem centralizer_inf_normalizer_normal (P N : Subgroup G) :
    ((Subgroup.centralizer (P : Set G) ⊓ N).subgroupOf
      (Subgroup.normalizer (P : Set G) ⊓ N)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hginv : (g : G)⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem g.2.1
    have hpa : (g : G)⁻¹ * p * g ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp hginv p).mp hp
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx.1) ((g : G)⁻¹ * p * g) hpa
    show p * ((g : G) * (x : G) * (g : G)⁻¹) =
      ((g : G) * (x : G) * (g : G)⁻¹) * p
    calc p * ((g : G) * (x : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * p * g) * (x : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((x : G) * ((g : G)⁻¹ * p * g)) * (g : G)⁻¹ := by rw [hcomm]
      _ = (g : G) * (x : G) * (g : G)⁻¹ * p := by group
  · exact N.mul_mem (N.mul_mem g.2.2 hx.2) (N.inv_mem g.2.2)

private theorem normalizer_le_normalizer_of_cyclic_of_card_prime {D₀ T : Subgroup G} {p : ℕ}
    (hT : IsCyclic T) (hD : D₀ ≤ T) (hDcard : Nat.card D₀ = p) :
    normalizer (T : Set G) ≤ normalizer (D₀ : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmapLe : D₀.map (MulAut.conj w).toMonoidHom ≤ T := by
    rintro _ ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hw d).mp (hD hd)
  have hleSub : D₀.subgroupOf T ≤ (D₀.map (MulAut.conj w).toMonoidHom).subgroupOf T := by
    haveI : IsCyclic T := hT
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    have h0 : Nat.card ↥(D₀.subgroupOf T) = Nat.card D₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
    have h1 : Nat.card ↥((D₀.map (MulAut.conj w).toMonoidHom).subgroupOf T) =
        Nat.card ↥(D₀.map (MulAut.conj w).toMonoidHom) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmapLe).toEquiv
    rw [h0, h1, Subgroup.card_map_of_injective (MulAut.conj w).injective]
  have hle : D₀ ≤ D₀.map (MulAut.conj w).toMonoidHom := by
    have hmap := Subgroup.map_mono (f := T.subtype) hleSub
    rwa [Subgroup.map_subgroupOf_eq_of_le hD,
      Subgroup.map_subgroupOf_eq_of_le hmapLe] at hmap
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])).symm

private theorem exists_sylow_cyclic {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) :
    ∃ T : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p T (Subgroup.centralizer (P : Set G) ⊓ N) ∧
        T ≤ N ∧ IsPGroup p T ∧ D₀ ≤ T ∧ IsCyclic T ∧
        normalizer (T : Set G) ≤ D.M := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hHN : H ≤ N := c.memN.2
  have hKN : F08.KOf8103 L B ≤ N := c.memH.2.2.1.trans hHN
  have hD0N : D₀ ≤ N := c.le_D₀.trans hKN
  have hD0M : D₀ ≤ D.M := c.le_D₀.trans (c.memH.2.2.1.trans c.memH.1)
  have hD0p : IsPGroup p D₀ := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [c.card_D₀, pow_one]⟩
  have hD0ne : D₀ ≠ ⊥ := by
    intro h
    have hcard : Nat.card D₀ = 1 := by rw [h, Subgroup.card_bot]
    rw [c.card_D₀] at hcard
    exact c.prime.ne_one hcard
  let CN : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ N
  have hD0CN : D₀ ≤ CN := le_inf c.cent_D₀ hD0N
  have hD0CNp : IsPGroup p (D₀.subgroupOf CN) := hD0p.comap_subtype (K := CN)
  obtain ⟨S, hD0S⟩ := hD0CNp.exists_le_sylow
  let T : Subgroup G := (S : Subgroup CN).map CN.subtype
  have hD0T : D₀ ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hD0CN]
    exact Subgroup.map_mono (f := CN.subtype) hD0S
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf p T CN := ⟨S, rfl⟩
  have hTp : IsPGroup p T := hTsyl.isPGroup
  have hTN : T ≤ N := hTsyl.le.trans inf_le_right
  have hTcyc : IsCyclic T := isCyclic_of_le c hTN hTp
  have hNormD0 : normalizer (D₀ : Set G) ≤ D.M :=
    normalizer_le_of_isStronglyPEmbedded c.prime c.strong hD0M hD0p hD0ne
  exact ⟨T, hTsyl, hTN, hTp, hD0T, hTcyc,
    (normalizer_le_normalizer_of_cyclic_of_card_prime hTcyc hD0T c.card_D₀).trans hNormD0⟩

private theorem exists_split_of_sylow {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {T : Subgroup G}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf p T (Subgroup.centralizer (P : Set G) ⊓ N)) :
    ∀ x ∈ Subgroup.normalizer (P : Set G) ⊓ N,
      ∃ y ∈ Subgroup.centralizer (P : Set G) ⊓ N,
        ∃ w ∈ Subgroup.normalizer (T : Set G) ⊓ (Subgroup.normalizer (P : Set G) ⊓ N),
          y * w = x := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  let CN : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ N
  let A : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ N
  have hCN_A : CN ≤ A :=
    inf_le_inf (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
  have hCNnorm : (CN.subgroupOf A).Normal := centralizer_inf_normalizer_normal P N
  have hA_normCN : A ≤ Subgroup.normalizer (CN : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN_A).mp hCNnorm
  obtain ⟨S, hST⟩ := hTsyl
  have hFr := eq_sup_normalizer_of_sylow hCN_A hCNnorm S
  rw [hST] at hFr
  have hle : Subgroup.normalizer (T : Set G) ⊓ A ≤ Subgroup.normalizer (CN : Set G) :=
    inf_le_right.trans hA_normCN
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left CN
    (Subgroup.normalizer (T : Set G) ⊓ A) hle
  intro x hx
  have hx' : x ∈ ((CN ⊔ (Subgroup.normalizer (T : Set G) ⊓ A) : Subgroup G) : Set G) :=
    hFr ▸ hx
  rw [hcoe] at hx'
  exact Set.mem_mul.mp hx'

private theorem exists_sylow_split {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) :
    ∃ T : Subgroup G, T ≤ N ∧ IsPGroup p T ∧ D₀ ≤ T ∧
      normalizer (T : Set G) ≤ D.M ∧
      ∀ x ∈ Subgroup.normalizer (P : Set G) ⊓ N,
        ∃ y ∈ Subgroup.centralizer (P : Set G) ⊓ N,
          ∃ w ∈ Subgroup.normalizer (T : Set G) ⊓ (Subgroup.normalizer (P : Set G) ⊓ N),
            y * w = x := by
  obtain ⟨T, hTsyl, hTN, hTp, hD0T, -, hNormT⟩ := exists_sylow_cyclic c
  exact ⟨T, hTN, hTp, hD0T, hNormT, exists_split_of_sylow c hTsyl⟩

private theorem exists_burnside_conj {D : Data G} {L P B B' D₀ H N Z : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hZ : Z = B ∨ Z = B') {y : G} (hy : y ∈ N)
    (hZy : Z.map (MulAut.conj y).toMonoidHom ≤ P) :
    ∃ n ∈ N, n ∈ Subgroup.normalizer (P : Set G) ∧
      Z.map (MulAut.conj y).toMonoidHom = Z.map (MulAut.conj n).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hPH : P ≤ H := by
    intro x hx
    have hxH : x ∈ (H : Set G) := by
      rw [c.memH.2.2.2]
      exact Set.mem_mul.mpr ⟨1, Set.mem_mul.mpr
        ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, x, hx, by simp⟩
    exact hxH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hPsylN : CFSG.ABGLocalTools.IsSylowOf 3 P N := c.sylow3.of_le hPN le_top
  have hZcard : Nat.card Z = 3 ∧ Z ≤ P := by
    rcases hZ with rfl | rfl
    · exact ⟨c.notB.1, c.notB.2.1⟩
    · exact ⟨c.notB'.1, c.notB'.2.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZcard.1])
  let a : G := (z : G)
  have haz : a ∈ Z := z.2
  have hzord' : orderOf a = 3 := by
    rw [show orderOf a = orderOf (z : ↥Z) from Subgroup.orderOf_coe z]
    exact hzord
  have hZgen : Z = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) ?_).symm
    rw [hZcard.1, Nat.card_zpowers, hzord']
  have haP : a ∈ P := hZcard.2 haz
  have hyP : y * a * y⁻¹ ∈ P := by
    have hmem := hZy (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom haz)
    simpa [MulAut.conj_apply] using hmem
  have hPsylN' : CFSG.RankThree.PartTwo.Sec21.FF79.IsSylowOf 3 P N := by
    refine ⟨hPsylN.le, hPsylN.isPGroup, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hPsylN).2.2
  obtain ⟨n, hnN, hnNor, hnconj⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF84.S4.burnside_sub hPsylN' c.abelian haP hyP hy rfl
  have hmapY : Z.map (MulAut.conj y).toMonoidHom =
      Subgroup.zpowers (y * a * y⁻¹) := by
    rw [hZgen, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hmapN : Z.map (MulAut.conj n).toMonoidHom =
      Subgroup.zpowers (n * a * n⁻¹) := by
    rw [hZgen, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hmapYN : Z.map (MulAut.conj y).toMonoidHom =
      Z.map (MulAut.conj n).toMonoidHom := by
    rw [hmapY, hmapN, hnconj]
  exact ⟨n, hnN, hnNor, hmapYN⟩

private theorem map_conj_eq_of_le_centralizer {P X : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (P : Set G)) (hX : X ≤ P) :
    X.map (MulAut.conj c).toMonoidHom = X := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change c * v * c⁻¹ ∈ X
    have hcomm : v * c = c * v := (Subgroup.mem_centralizer_iff.mp hc) v (hX hv)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hv
  · intro hu
    refine ⟨u, hu, ?_⟩
    change c * u * c⁻¹ = u
    have hcomm : u * c = c * u := (Subgroup.mem_centralizer_iff.mp hc) u (hX hu)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem exists_weak_conj {D : Data G} {L P B B' D₀ H N Z : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hZ : Z = B ∨ Z = B') {y : G} (hy : y ∈ N)
    (hZy : Z.map (MulAut.conj y).toMonoidHom ≤ P) :
    ∃ w ∈ N, w ∈ D.M ∧ Z.map (MulAut.conj y).toMonoidHom =
      Z.map (MulAut.conj w).toMonoidHom := by
  classical
  obtain ⟨T, -, -, -, hTnormDM, hsplit⟩ := exists_sylow_split c
  obtain ⟨n, hmnN, hnNor, hmapYN⟩ := exists_burnside_conj c hZ hy hZy
  obtain ⟨cc, hccCN, w, hwNA, hcw⟩ := hsplit n ⟨hnNor, hmnN⟩
  have hconjMul : (MulAut.conj (cc * w)).toMonoidHom =
      (MulAut.conj cc).toMonoidHom.comp (MulAut.conj w).toMonoidHom := by
    ext u
    simp [MulAut.conj_apply, mul_assoc]
  have hmapWN : Z.map (MulAut.conj n).toMonoidHom =
      (Z.map (MulAut.conj w).toMonoidHom).map (MulAut.conj cc).toMonoidHom := by
    rw [← hcw, hconjMul, Subgroup.map_map]
  have hWleP : Z.map (MulAut.conj w).toMonoidHom ≤ P := by
    have hle : (Z.map (MulAut.conj w).toMonoidHom).map (MulAut.conj cc).toMonoidHom ≤ P := by
      rw [← hmapWN, ← hmapYN]
      exact hZy
    have hPfix : P.map (MulAut.conj cc).toMonoidHom = P :=
      map_conj_eq_of_le_centralizer hccCN.1 le_rfl
    rw [← hPfix] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj cc).injective).mp hle
  refine ⟨w, hwNA.2.2, hTnormDM hwNA.1, ?_⟩
  calc Z.map (MulAut.conj y).toMonoidHom = Z.map (MulAut.conj n).toMonoidHom := hmapYN
    _ = (Z.map (MulAut.conj w).toMonoidHom).map (MulAut.conj cc).toMonoidHom := hmapWN
    _ = Z.map (MulAut.conj w).toMonoidHom :=
        map_conj_eq_of_le_centralizer hccCN.1 hWleP

private theorem false_of_two_le_pRank {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) {K K' : Subgroup G} (hKN : K ≤ N) (hK'N : K' ≤ N)
    (hrank : 2 ≤ Open.pRank p (K ⊔ K')) : False := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  obtain ⟨E, hE, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank c.prime.one_lt (K ⊔ K')
  have hEN : E ≤ N := hE.trans (sup_le hKN hK'N)
  have hEcyc : IsCyclic E := isCyclic_of_le c hEN hEelem.isPGroup
  have hge : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right c.prime.pos hrank
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hgpow : g ^ p = 1 := Subtype.ext (by simpa using hEelem.2 (g : G) g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgpow
  rw [hg] at hdvd
  have hle : Nat.card E ≤ p := Nat.le_of_dvd c.prime.pos hdvd
  have hlt : p < p ^ 2 := by nlinarith [c.prime.one_lt]
  omega


theorem weaklyClosed {D : Data G} {L P B B' D₀ H N Z : Subgroup G} {p n : ℕ} {y : G}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hZ : Z = B ∨ Z = B') (hy : y ∈ N)
    (hZy : Z.map (MulAut.conj y).toMonoidHom ≤ P) :
    Z.map (MulAut.conj y).toMonoidHom = Z := by
  classical
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hHN : H ≤ N := c.memN.2
  have hKN : F08.KOf8103 L B ≤ N := c.memH.2.2.1.trans hHN
  rcases hZ with hZB | hZB'
  · subst Z
    obtain ⟨w, hwN, hwM, hWy⟩ := exists_weak_conj c (Or.inl rfl) hy hZy
    have hwL : w ∈ normalizer (L : Set G) := c.normal hwM
    have hWyP : B.map (MulAut.conj w).toMonoidHom ≤ P := hWy ▸ hZy
    have hWnotB : F08.NotationB8103 L P n (B.map (MulAut.conj w).toMonoidHom) :=
      notationB_map_conj c.notB hWyP hwL
    rcases c.lines (B.map (MulAut.conj w).toMonoidHom) hWnotB with hWB | hWB
    · rw [hWy, hWB]
    · exfalso
      have hKmap := KOf8103_map_conj (L := L) (Z := B) (w := w) hwL
      rw [hWB] at hKmap
      have hK'N : F08.KOf8103 L B' ≤ N := by
        rw [hKmap]
        rintro x ⟨u, hu, rfl⟩
        exact N.mul_mem (N.mul_mem hwN (hKN hu)) (N.inv_mem hwN)
      exact false_of_two_le_pRank c hKN hK'N c.genRank
  · subst Z
    obtain ⟨w, hwN, hwM, hWy⟩ := exists_weak_conj c (Or.inr rfl) hy hZy
    have hwL : w ∈ normalizer (L : Set G) := c.normal hwM
    have hWyP : B'.map (MulAut.conj w).toMonoidHom ≤ P := hWy ▸ hZy
    have hWnotB : F08.NotationB8103 L P n (B'.map (MulAut.conj w).toMonoidHom) :=
      notationB_map_conj c.notB' hWyP hwL
    rcases c.lines (B'.map (MulAut.conj w).toMonoidHom) hWnotB with hWB | hWB
    · exfalso
      have hKmap := KOf8103_map_conj (L := L) (Z := B') (w := w) hwL
      rw [hWB] at hKmap
      have hmap := congrArg (Subgroup.map (MulAut.conj w⁻¹).toMonoidHom) hKmap
      have hcomp : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
      have hK'N : F08.KOf8103 L B' ≤ N := by
        rw [← hmap]
        rintro x ⟨u, hu, rfl⟩
        exact N.mul_mem (N.mul_mem (N.inv_mem hwN) (hKN hu)) (by simpa using hwN)
      exact false_of_two_le_pRank c hKN hK'N c.genRank
    · rw [hWy, hWB]


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
