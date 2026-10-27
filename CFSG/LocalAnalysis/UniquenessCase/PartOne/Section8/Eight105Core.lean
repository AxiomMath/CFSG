module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Commute

import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem exists_ne_one_of_card_prime {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hcard : Nat.card X = p) : ∃ d ∈ X, d ≠ 1 := by
  haveI : Nontrivial ↥X :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
  obtain ⟨d, hd⟩ := exists_ne (1 : ↥X)
  exact ⟨d, d.2, fun h => hd (Subtype.ext h)⟩

private theorem zpowers_eq_of_card_prime {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hcard : Nat.card X = p) {d : G} (hdX : d ∈ X) (hd : d ≠ 1) :
    Subgroup.zpowers d = X := by
  have hord : orderOf d = p := by
    have hdvd : orderOf d ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hdX
    rw [hcard] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hd
    · exact hp'
  have hcardz : Nat.card (Subgroup.zpowers d) = Nat.card X := by
    rw [Nat.card_zpowers, hord, hcard]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdX) (le_of_eq hcardz.symm)

private theorem coprime_three_card_relPPrimeCore (N : Subgroup G) :
    Nat.Coprime 3 (Nat.card (relPPrimeCore 3 N)) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
    Nat.prime_three N

private theorem ncl_le_of_le {N X : Subgroup G} (hX : X ≤ N) : ncl N X ≤ N := by
  rw [ncl]
  refine (Subgroup.closure_le N).mpr ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact N.mul_mem (N.mul_mem hg (hX hx)) (N.inv_mem hg)

private theorem le_normalizer_ncl_of_le {N X : Subgroup G} (hX : X ≤ N) :
    N ≤ Subgroup.normalizer (ncl N X : Set G) := by
  have hmap_le : ∀ {g : G}, g ∈ N →
      Subgroup.map (MulAut.conj g).toMonoidHom (ncl N X) ≤ ncl N X := by
    intro g hg
    rw [ncl, MonoidHom.map_closure]
    refine (Subgroup.closure_le (ncl N X)).mpr ?_
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨n, hn, x, hx, rfl⟩ := hz
    refine Subgroup.subset_closure ⟨g * n, N.mul_mem hg hn, x, hx, ?_⟩
    simp only [MulAut.conj_apply, MonoidHom.coe_mk, MulEquiv.coe_toMonoidHom]
    group
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hmap_le hg) ?_
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have h2 : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (ncl N X)) ≤
      Subgroup.map (MulAut.conj g).toMonoidHom (ncl N X) :=
    Subgroup.map_mono (hmap_le (N.inv_mem hg))
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h2

private theorem le_centralizer_inf_sup_of_trivial_action {p : ℕ} (hp : p.Prime)
    {I Q D : Subgroup G} (hDp : IsPGroup p D) (hDcard : Nat.card D = p)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQI : Q ≤ I)
    (hcop : Nat.Coprime p (Nat.card Q))
    (hact : ∀ d ∈ D, ∀ x ∈ I, x⁻¹ * (d * x * d⁻¹) ∈ Q) :
    I ≤ (Subgroup.centralizer (D : Set G) ⊓ I) ⊔ Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hdD, hdne⟩ := exists_ne_one_of_card_prime hp hDcard
  have hgen : Subgroup.zpowers d = D := zpowers_eq_of_card_prime hp hDcard hdD hdne
  have hord : orderOf d = p := by
    have hdvd : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hdD
    rw [hDcard] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hdne
    · exact hp'
  have hDQd : ∀ n ∈ Q, d * n * d⁻¹ ∈ Q := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (hDQ hdD) n).mp hn
  have hcop_d : Nat.Coprime (orderOf d) (Nat.card Q) := by
    rw [hord]
    exact hcop
  intro x hx
  obtain ⟨q, hqQ, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime Q (f := d) (g := x) hDQd
      (hact d hdD x hx) hcop_d
  have hcomm : (x * q) * d = d * (x * q) := by
    have h := congrArg (· * d) hfix
    simpa [mul_assoc] using h.symm
  have hcent_d : x * q ∈ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff).mpr hcomm
  have hcent : x * q ∈ Subgroup.centralizer (D : Set G) := by
    simpa [← hgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hcent_d
  have hxqI : x * q ∈ I := I.mul_mem hx (hQI hqQ)
  have hmem : (x * q) * q⁻¹ ∈ (Subgroup.centralizer (D : Set G) ⊓ I) ⊔ Q :=
    Subgroup.mul_mem_sup ⟨hcent, hxqI⟩ (Q.inv_mem hqQ)
  simpa [mul_assoc] using hmem

private theorem exists_mul_mem_normalizer_of_isSylow {p : ℕ} (hp : p.Prime)
    {N N₂ S : Subgroup G} (hN₂N : N₂ ≤ N) (hNnormal : N ≤ Subgroup.normalizer (N₂ : Set G))
    (hS_N₂ : S ≤ N₂) (hSyl : Nat.card S = p ^ (Nat.card N₂).factorization p)
    {n : G} (hn : n ∈ N) :
    ∃ ℓ ∈ N₂, ∃ m ∈ Subgroup.normalizer (S : Set G), ℓ * m = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn_norm : n ∈ Subgroup.normalizer (N₂ : Set G) := hNnormal hn
  let Q : Subgroup G := S.map (MulAut.conj n).toMonoidHom
  have hQ_N₂ : Q ≤ N₂ := by
    rintro y ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn_norm s).mp (hS_N₂ hs)
  have hQcard : Nat.card Q = p ^ (Nat.card N₂).factorization p := by
    rw [show Q = S.map (MulAut.conj n).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hSyl
  obtain ⟨ℓ, hℓN₂, hQeq⟩ :=
    CFSG.Walter.W67.Sec6.exists_conj_of_sylowIn (r := p) hS_N₂ hQ_N₂ hSyl hQcard
  have hQeq' : S.map (MulAut.conj n).toMonoidHom = S.map (MulAut.conj ℓ).toMonoidHom := by
    simpa [Q, CFSG.Walter.W67.Sec6.cj] using hQeq
  refine ⟨ℓ, hℓN₂, ℓ⁻¹ * n, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_mul : Subgroup.map ((MulAut.conj ℓ⁻¹ * MulAut.conj n)).toMonoidHom S =
      Subgroup.map (MulAut.conj ℓ⁻¹).toMonoidHom
        (Subgroup.map (MulAut.conj n).toMonoidHom S) := by
    change Subgroup.map ((MulAut.conj ℓ⁻¹).toMonoidHom.comp
      (MulAut.conj n).toMonoidHom) S = _
    exact (Subgroup.map_map S (MulAut.conj ℓ⁻¹).toMonoidHom (MulAut.conj n).toMonoidHom).symm
  calc
    Subgroup.map (MulAut.conj (ℓ⁻¹ * n)).toMonoidHom S
        = Subgroup.map ((MulAut.conj ℓ⁻¹ * MulAut.conj n)).toMonoidHom S := by rw [map_mul]
    _ = Subgroup.map (MulAut.conj ℓ⁻¹).toMonoidHom
          (Subgroup.map (MulAut.conj n).toMonoidHom S) := hmap_mul
    _ = Subgroup.map (MulAut.conj ℓ⁻¹).toMonoidHom
          (Subgroup.map (MulAut.conj ℓ).toMonoidHom S) := by rw [hQeq']
    _ = S := by
          rw [Subgroup.map_map]
          have hcomp : (MulAut.conj ℓ⁻¹).toMonoidHom.comp (MulAut.conj ℓ).toMonoidHom =
              MonoidHom.id G := by
            ext y
            simp [MulAut.conj_apply, mul_assoc]
          rw [hcomp, Subgroup.map_id]

private theorem exists_subgroupOf_conj_eq_of_commutator_mem {p : ℕ} (hp : p.Prime)
    {I D : Subgroup G} {x : G} (hDcard : Nat.card D = p)
    (hDI : D ≤ Subgroup.normalizer (I : Set G))
    (hxI : x ∈ Subgroup.normalizer (I : Set G))
    (hcopI : Nat.Coprime p (Nat.card I))
    (hcomm : ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ I) :
    ∃ n : ↥(I.subgroupOf (I ⊔ D)),
      (Subgroup.map (MulAut.conj x).toMonoidHom D).subgroupOf (I ⊔ D) =
        (D.subgroupOf (I ⊔ D)).map (MulAut.conj (n : ↥(I ⊔ D))).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  let L : Subgroup G := I ⊔ D
  let NN : Subgroup L := I.subgroupOf L
  let HH : Subgroup L := D.subgroupOf L
  let KK : Subgroup L := (Subgroup.map (MulAut.conj x).toMonoidHom D).subgroupOf L
  have hIL : I ≤ L := le_sup_left
  have hDL : D ≤ L := le_sup_right
  have hLnorm : L ≤ Subgroup.normalizer (I : Set G) := sup_le Subgroup.le_normalizer hDI
  have hKK_le : Subgroup.map (MulAut.conj x).toMonoidHom D ≤ L := by
    rintro y ⟨d, hd, rfl⟩
    change x * d * x⁻¹ ∈ L
    have hmem : x * d * x⁻¹ = (x * d * x⁻¹ * d⁻¹) * d := by group
    rw [hmem]
    exact Subgroup.mul_mem_sup (hcomm d hd) hd
  have hdisj : Disjoint I D := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hDcard]
    exact hcopI.symm
  have hcardNN : Nat.card NN = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIL).toEquiv
  have hcardHH : Nat.card HH = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hcardKK : Nat.card KK = Nat.card D := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKK_le).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hcardL : Nat.card L = Nat.card I * Nat.card D :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer I D hDI hdisj
  have hcompH : NN.IsComplement' HH := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hcardNN, hcardHH, hcardL]
    · rw [hcardNN, hcardHH, hDcard]
      exact hcopI.symm
  have hcompK : NN.IsComplement' KK := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hcardNN, hcardKK, hcardL]
    · rw [hcardNN, hcardKK, hDcard]
      exact hcopI.symm
  haveI : NN.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIL).mpr hLnorm
  have hcopIndex : Nat.Coprime (Nat.card NN) NN.index := by
    rw [hcompH.symm.index_eq_card, hcardNN, hcardHH, hDcard]
    exact hcopI.symm
  exact CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    NN HH KK inferInstance hcompH hcompK hcopIndex

private theorem exists_conj_eq_of_commutator_mem {p : ℕ} (hp : p.Prime)
    {I D : Subgroup G} {x : G} (hDcard : Nat.card D = p)
    (hDI : D ≤ Subgroup.normalizer (I : Set G))
    (hxI : x ∈ Subgroup.normalizer (I : Set G))
    (hcopI : Nat.Coprime p (Nat.card I))
    (hcomm : ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ I) :
    ∃ i ∈ I, Subgroup.map (MulAut.conj x).toMonoidHom D =
      Subgroup.map (MulAut.conj i).toMonoidHom D := by
  obtain ⟨n, hn⟩ :=
    exists_subgroupOf_conj_eq_of_commutator_mem hp hDcard hDI hxI hcopI hcomm
  let L : Subgroup G := I ⊔ D
  have hKK_le : Subgroup.map (MulAut.conj x).toMonoidHom D ≤ L := by
    rintro y ⟨d, hd, rfl⟩
    change x * d * x⁻¹ ∈ L
    have hmem : x * d * x⁻¹ = (x * d * x⁻¹ * d⁻¹) * d := by group
    rw [hmem]
    exact Subgroup.mul_mem_sup (hcomm d hd) hd
  have hiI : ((n : L) : G) ∈ I := Subgroup.mem_subgroupOf.mp n.2
  refine ⟨((n : L) : G), hiI, ?_⟩
  have hconv : ∀ d : L, L.subtype.comp (MulAut.conj d).toMonoidHom =
      (MulAut.conj (d : G)).toMonoidHom.comp L.subtype := by
    intro d
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hHHmap : Subgroup.map L.subtype (D.subgroupOf L) = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have hsimpl : Subgroup.map L.subtype
      (Subgroup.map (MulAut.conj (n : L)).toMonoidHom (D.subgroupOf L)) =
      Subgroup.map (MulAut.conj ((n : L) : G)).toMonoidHom D := by
    calc
      Subgroup.map L.subtype (Subgroup.map (MulAut.conj (n : L)).toMonoidHom (D.subgroupOf L))
          = Subgroup.map (L.subtype.comp (MulAut.conj (n : L)).toMonoidHom) (D.subgroupOf L) := by
            rw [Subgroup.map_map]
      _ = Subgroup.map ((MulAut.conj ((n : L) : G)).toMonoidHom.comp L.subtype)
            (D.subgroupOf L) := by rw [hconv]
      _ = Subgroup.map (MulAut.conj ((n : L) : G)).toMonoidHom
            (Subgroup.map L.subtype (D.subgroupOf L)) := by rw [Subgroup.map_map]
      _ = Subgroup.map (MulAut.conj ((n : L) : G)).toMonoidHom D := by rw [hHHmap]
  have hbase : Subgroup.map L.subtype
      ((Subgroup.map (MulAut.conj x).toMonoidHom D).subgroupOf L) =
      Subgroup.map (MulAut.conj x).toMonoidHom D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKK_le]
  have hmap := congrArg (Subgroup.map L.subtype) hn
  rwa [hbase, hsimpl] at hmap

theorem commutator_relPPrimeCore_le (hS : KSuzukiL2) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ⁅relPPrimeCore 3 N, F08.KOf8103 L B⁆ ≤ pCoreOf 2 N := by
  let I : Subgroup G := relPPrimeCore 3 N
  let K : Subgroup G := F08.KOf8103 L B
  haveI : IsSimpleGroup G := D.standing.simple
  have hI_le_N : I ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hN_ne_top : N ≠ ⊤ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocal_ne_top D.standing.nonab N c.memN.1.1
  have hI_ne_top : I ≠ ⊤ := fun h => hN_ne_top (top_le_iff.mp (h ▸ hI_le_N))
  have hKGrp : CFSG.Open.IsKGroup I := D.standing.kProper.isKGroup I hI_ne_top
  have hnot3 : ¬ 3 ∣ Nat.card I :=
    Nat.prime_three.coprime_iff_not_dvd.mp (coprime_three_card_relPPrimeCore N)
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r I ≤ 3 := by
    intro r hr hr2
    calc
      Open.pRank r I ≤ Open.pRank r N :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_mono r hr hI_le_N
      _ ≤ evenRank G :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 N c.memN.1.1
      _ = 3 := c.evenRank
  have hN_norm_I : N ≤ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_N).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N)
  have hK_le_N : K ≤ N := c.memH.2.2.1.trans c.memN.2
  have hKn : K ≤ Subgroup.normalizer (I : Set G) := hK_le_N.trans hN_norm_I
  have hKK : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (isPerfect_derInf8 (L ⊓ centralizer (B : Set G)))
  have h4 : 4 ≤ 2 * n := by
    calc 4 = 2 * 2 := by norm_num
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 c.two_le
  have hIsL2 : IsL2 (Bar2 K) (2 * n) := c.notB.2.2
  have h7 := hS (Y := G) I K hKGrp hnot3 hrank hKn hKK (2 * n) h4 hIsL2
  have hcore : pCoreOf 2 I ≤ pCoreOf 2 N :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hI_le_N hN_norm_I
  exact h7.trans hcore

theorem relPPrimeCore_le (hS : KSuzukiL2) {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) (hQ : pCoreOf 2 N ≤ D.M) :
    relPPrimeCore 3 N ≤ D.M := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hI_le_N : relPPrimeCore 3 N ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hQN : pCoreOf 2 N ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hQp : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hp2 : p ≠ 2 := (D.sig_prime p c.hyp.2.2.2.1).2
  have hcop_pQ : Nat.Coprime p (Nat.card (pCoreOf 2 N)) :=
    c.prime.coprime_iff_not_dvd.mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p) hQp c.prime hp2)
  have hcop3Q : Nat.Coprime 3 (Nat.card (pCoreOf 2 N)) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hQp Nat.prime_three
        (by norm_num))
  have hQ_normal : ((pCoreOf 2 N).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hQ_le_I : pCoreOf 2 N ≤ relPPrimeCore 3 N := by
    exact le_sSup ⟨hQN, hQ_normal, hcop3Q⟩
  have hD0_le_N : D₀ ≤ N := c.le_D₀.trans (c.memH.2.2.1.trans c.memN.2)
  have hD0_normQ : D₀ ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    hD0_le_N.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mp hQ_normal)
  have hD0p : IsPGroup p D₀ := IsPGroup.of_card (n := 1) (by rw [c.card_D₀, pow_one])
  have hcomm : ⁅relPPrimeCore 3 N, D₀⁆ ≤ pCoreOf 2 N :=
    (Subgroup.commutator_mono le_rfl c.le_D₀).trans (commutator_relPPrimeCore_le hS c)
  have hact : ∀ d ∈ D₀, ∀ x ∈ relPPrimeCore 3 N,
      x⁻¹ * (d * x * d⁻¹) ∈ pCoreOf 2 N := by
    intro d hd x hx
    have hmem : ⁅x⁻¹, d⁆ ∈ ⁅relPPrimeCore 3 N, D₀⁆ :=
      Subgroup.commutator_mem_commutator ((relPPrimeCore 3 N).inv_mem hx) hd
    simpa [commutatorElement_def, mul_assoc] using hcomm hmem
  have hI_le_cent :=
    le_centralizer_inf_sup_of_trivial_action c.prime hD0p c.card_D₀ hD0_normQ hQ_le_I hcop_pQ hact
  have hD0M : D₀ ≤ D.M := c.le_D₀.trans (c.memH.2.2.1.trans c.memH.1)
  have hD0ne : D₀ ≠ ⊥ := by
    intro hbot
    have hcard := c.card_D₀
    rw [hbot, Subgroup.card_bot] at hcard
    exact c.prime.ne_one hcard.symm
  have hcent_le_M : Subgroup.centralizer (D₀ : Set G) ⊓ relPPrimeCore 3 N ≤ D.M := by
    intro y hy
    exact (normalizer_le_of_isStronglyPEmbedded c.prime c.strong hD0M hD0p hD0ne)
      (Subgroup.centralizer_le_normalizer (D₀ : Set G) hy.1)
  exact hI_le_cent.trans (sup_le hcent_le_M hQ)

theorem not_ncl_le {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : ¬ ncl N B' ≤ D.M := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  intro hN2M
  have hB'_N : B' ≤ N := c.le.trans (c.memH.2.2.1.trans c.memN.2)
  have hN2_le_N : ncl N B' ≤ N := ncl_le_of_le hB'_N
  have hN2_normal : N ≤ Subgroup.normalizer (ncl N B' : Set G) := le_normalizer_ncl_of_le hB'_N
  have hD0_N2 : D₀ ≤ ncl N B' := c.le_D₀.trans (kOf8103_le_ncl c)
  have hD0p : IsPGroup p D₀ := IsPGroup.of_card (n := 1) (by rw [c.card_D₀, pow_one])
  have hD0sub_p : IsPGroup p (D₀.subgroupOf (ncl N B')) :=
    hD0p.of_equiv (Subgroup.subgroupOfEquivOfLe hD0_N2).symm
  obtain ⟨S', hD0S'⟩ := hD0sub_p.exists_le_sylow
  let S : Subgroup G := Subgroup.map (ncl N B').subtype (S' : Subgroup ↥(ncl N B'))
  have hS_N2 : S ≤ ncl N B' := Subgroup.map_subtype_le _
  have hS_N : S ≤ N := hS_N2.trans hN2_le_N
  have hSp : IsPGroup p S := S'.isPGroup'.map (ncl N B').subtype
  have hD0S : D₀ ≤ S := by
    intro d hd
    have hd' : (⟨d, hD0_N2 hd⟩ : ↥(ncl N B')) ∈ D₀.subgroupOf (ncl N B') :=
      Subgroup.mem_subgroupOf.mpr hd
    exact Subgroup.mem_map.mpr ⟨⟨d, hD0_N2 hd⟩, hD0S' hd', rfl⟩
  have hcardS : Nat.card S = p ^ (Nat.card (ncl N B')).factorization p := by
    rw [show S = Subgroup.map (ncl N B').subtype (S' : Subgroup ↥(ncl N B')) from rfl,
      Subgroup.card_map_of_injective (ncl N B').subtype_injective]
    exact Sylow.card_eq_multiplicity S'
  have hN_le_M : N ≤ D.M := by
    intro g hg
    obtain ⟨ℓ, hℓ, m, hm, rfl⟩ :=
      exists_mul_mem_normalizer_of_isSylow c.prime hN2_le_N hN2_normal hS_N2 hcardS hg
    have hℓM : ℓ ∈ D.M := hN2M hℓ
    have hSM : Subgroup.normalizer (S : Set G) ≤ D.M := by
      refine (CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic
        (isCyclic_of_le c hS_N hSp) hD0S).trans ?_
      exact normalizer_le_of_isStronglyPEmbedded c.prime c.strong
        (c.le_D₀.trans (c.memH.2.2.1.trans c.memH.1)) hD0p (by
          intro hbot
          have hcard := c.card_D₀
          rw [hbot, Subgroup.card_bot] at hcard
          exact c.prime.ne_one hcard.symm)
    exact D.M.mul_mem hℓM (hSM hm)
  exact c.neN (c.memN.1.2 D.M D.maxLocal.1 hN_le_M).symm

theorem mem_of_commutator_mem (hS : KSuzukiL2) {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} {x : G} (c : Ctx8105 D L P B B' D₀ H N p n) (hQ : pCoreOf 2 N ≤ D.M)
    (hx : x ∈ N) (hxD : ∀ d ∈ D₀, x * d * x⁻¹ * d⁻¹ ∈ relPPrimeCore 3 N) : x ∈ D.M := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hI_le_M : relPPrimeCore 3 N ≤ D.M := relPPrimeCore_le hS c hQ
  have hI_le_N : relPPrimeCore 3 N ≤ N :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hN_norm_I : N ≤ Subgroup.normalizer (relPPrimeCore 3 N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_N).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N)
  have hD0_le_N : D₀ ≤ N := c.le_D₀.trans (c.memH.2.2.1.trans c.memN.2)
  have hD0_normI : D₀ ≤ Subgroup.normalizer (relPPrimeCore 3 N : Set G) :=
    hD0_le_N.trans hN_norm_I
  have hx_normI : x ∈ Subgroup.normalizer (relPPrimeCore 3 N : Set G) := hN_norm_I hx
  have hcopI : Nat.Coprime p (Nat.card (relPPrimeCore 3 N)) :=
    c.prime.coprime_iff_not_dvd.mpr (not_dvd_card_relPPrimeCore c)
  obtain ⟨i, hiI, hiD⟩ := exists_conj_eq_of_commutator_mem c.prime c.card_D₀ hD0_normI
    hx_normI hcopI hxD
  have hiM : i ∈ D.M := hI_le_M hiI
  have hD0p : IsPGroup p D₀ := IsPGroup.of_card (n := 1) (by rw [c.card_D₀, pow_one])
  have hD0M : D₀ ≤ D.M := c.le_D₀.trans (c.memH.2.2.1.trans c.memH.1)
  have hD0ne : D₀ ≠ ⊥ := by
    intro hbot
    have hcard := c.card_D₀
    rw [hbot, Subgroup.card_bot] at hcard
    exact c.prime.ne_one hcard.symm
  have hnorm : i⁻¹ * x ∈ Subgroup.normalizer (D₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      Subgroup.map (MulAut.conj (i⁻¹ * x)).toMonoidHom D₀
          = Subgroup.map (MulAut.conj i⁻¹).toMonoidHom
              (Subgroup.map (MulAut.conj x).toMonoidHom D₀) := by
            rw [map_mul]
            change Subgroup.map ((MulAut.conj i⁻¹).toMonoidHom.comp
              (MulAut.conj x).toMonoidHom) D₀ = _
            exact (Subgroup.map_map D₀ (MulAut.conj i⁻¹).toMonoidHom
              (MulAut.conj x).toMonoidHom).symm
      _ = Subgroup.map (MulAut.conj i⁻¹).toMonoidHom
            (Subgroup.map (MulAut.conj i).toMonoidHom D₀) := by rw [hiD]
      _ = D₀ := by
            rw [Subgroup.map_map]
            have hcomp : (MulAut.conj i⁻¹).toMonoidHom.comp (MulAut.conj i).toMonoidHom =
                MonoidHom.id G := by
              ext y
              simp [MulAut.conj_apply, mul_assoc]
            rw [hcomp, Subgroup.map_id]
  have hnormM : i⁻¹ * x ∈ D.M :=
    (normalizer_le_of_isStronglyPEmbedded c.prime c.strong hD0M hD0p hD0ne) hnorm
  have hxeq : x = i * (i⁻¹ * x) := by group
  rw [hxeq]
  exact D.M.mul_mem hiM hnormM

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
