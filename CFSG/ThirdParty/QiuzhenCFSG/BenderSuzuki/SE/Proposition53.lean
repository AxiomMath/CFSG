module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary64
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 5.3 normalizer input

This file begins the source proof of Proposition 5.3.  It formalizes Lemma 5.1
in the form needed downstream: a maximal odd-prime subgroup fixing at least
three conjugate cosets has an involution in its normalizer.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

open PFAppendixIII PFchapter1section1

private theorem rightConjugate_stronglyEmbedded
    {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hM : IsStronglyEmbedded M) (g : G) :
    IsStronglyEmbedded (rightConjugate M g) := by
  have heq : M.comap (MulAut.conj g).toMonoidHom = rightConjugate M g := by
    ext x
    constructor
    · intro hx
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      simp [mul_assoc]
    · intro hx
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      change g * x * g⁻¹ ∈ M
      rw [← hyx]
      simpa [mul_assoc] using hy
  rw [← heq]
  apply hM.comap_of_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  · intro htop
    apply hM.ne_top
    apply top_unique
    intro x _hx
    let y : G := (MulAut.conj g).symm x
    have hyTop : y ∈ (⊤ : Subgroup G) := trivial
    rw [← htop] at hyTop
    change (MulAut.conj g) y ∈ M at hyTop
    have hgy : (MulAut.conj g) y = x := by
      exact (MulAut.conj g).apply_symm_apply x
    rwa [hgy] at hyTop
  · obtain ⟨z, hzM, hz⟩ := hM.exists_involution
    let z' : G := (MulAut.conj g).symm z
    refine ⟨z', ?_, ?_⟩
    · change (MulAut.conj g) z' ∈ M
      have hgz : (MulAut.conj g) z' = z := by
        exact (MulAut.conj g).apply_symm_apply z
      rwa [hgz]
    · exact IsInvolution.map_of_injective hz
        (MulAut.conj g).symm.toMonoidHom (MulAut.conj g).symm.injective

private theorem twoRankAtLeastTwo_of_contains_sylow
    {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (P : Sylow 2 G) (hPM : (P : Subgroup G) ≤ M)
    (hG : TwoRankAtLeastTwo G) : TwoRankAtLeastTwo M := by
  rcases hG with ⟨E, hEcard, hEsq⟩
  have hEp : IsPGroup 2 E := by
    apply IsPGroup.of_card (p := 2) (G := E) (n := 2)
    simp [hEcard]
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let fG : E →* G := (MulAut.conj g).toMonoidHom.comp E.subtype
  have hfG_inj : Function.Injective fG := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj g).injective
    simpa [fG] using hab
  have hfG_mem_P : ∀ e : E, fG e ∈ (P : Subgroup G) := by
    intro e
    rw [show (P : Subgroup G) = ((g • S : Sylow 2 G) : Subgroup G) from
      congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg.symm]
    rw [Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨e, hES e.property, rfl⟩
  let fM : E →* M := fG.codRestrict M (fun e => hPM (hfG_mem_P e))
  have hfM_inj : Function.Injective fM := by
    intro a b hab
    exact hfG_inj (by simpa [fM] using congrArg Subtype.val hab)
  let EM : Subgroup M := (⊤ : Subgroup E).map fM
  have hEMcard : Nat.card EM = 4 := by
    rw [Subgroup.card_map_of_injective hfM_inj]
    calc
      Nat.card (⊤ : Subgroup E) = Nat.card E :=
        Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv
      _ = 4 := hEcard
  refine ⟨EM, hEMcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨e, _he, rfl⟩
  apply Subtype.ext
  simpa using congrArg fM (hEsq e)

private theorem not_twoRankAtLeastTwo_of_normal_odd_not_le
    {G : Type*} [Group G] [Finite G]
    {M W : Subgroup G} (hM : IsStronglyEmbedded M)
    [W.Normal] (hWodd : Odd (Nat.card W)) (hWnotM : ¬ W ≤ M) :
    ¬ TwoRankAtLeastTwo G := by
  intro hGrank
  obtain ⟨P, hPM⟩ := hM.containsSylowTwo
  have hMrank : TwoRankAtLeastTwo M :=
    twoRankAtLeastTwo_of_contains_sylow P hPM hGrank
  obtain ⟨U, hUcard, hUsq⟩ := hMrank
  let UG : Subgroup G := U.map M.subtype
  have hUGM : UG ≤ M := by
    simpa [UG] using Subgroup.map_le_range M.subtype U
  have hUGcard : Nat.card UG = 4 := by
    rw [show Nat.card UG = Nat.card U from
      Subgroup.card_map_of_injective M.subtype_injective]
    exact hUcard
  have hUGsq : ∀ u : UG, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    rcases Subgroup.mem_map.mp u.property with ⟨v, hvU, hvu⟩
    let vU : U := ⟨v, hvU⟩
    have hv2 : (v : M) ^ 2 = 1 := by
      simpa [vU] using congrArg Subtype.val (hUsq vU)
    calc
      (u : G) ^ 2 = (M.subtype v) ^ 2 := by rw [hvu]
      _ = 1 := by simpa using congrArg M.subtype hv2
  apply hWnotM
  apply fourGroup_odd_subgroup_le_stronglyEmbedded hM hUGM hUGcard hUGsq
  · exact hUGM.trans Subgroup.le_normalizer_of_normal
  · exact hWodd

/-- If a normalizing involution fixes a coset not fixed by an odd `p`-subgroup,
then the subgroup normalizer has `2`-rank at most one. -/
public theorem normalizer_not_twoRank_of_not_fixed
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M)
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    (hPp : IsPGroup p P)
    {s : X} (hs : IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set X))
    {delta : conjugateCosetSpace M}
    (hsDelta : s • delta = delta)
    (hPnotDelta : ¬ P ≤ MulAction.stabilizer X delta) :
    ¬ TwoRankAtLeastTwo (Subgroup.normalizer (P : Set X)) := by
  classical
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  let H : Subgroup N :=
    (MulAction.stabilizer X delta).comap N.subtype
  let W : Subgroup N := P.subgroupOf N
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hWnormal : W.Normal := by
    simpa [W, N] using (Subgroup.normal_in_normalizer (H := P))
  letI : W.Normal := hWnormal
  have hWodd : Odd (Nat.card W) := by
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hWp : IsPGroup p W :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
    rw [hn]
    exact hpOdd.pow
  have hWnotH : ¬ W ≤ H := by
    intro hWH
    apply hPnotDelta
    intro x hxP
    let xN : N := ⟨x, hPN hxP⟩
    exact hWH (show xN ∈ W from hxP)
  have hHproper : H ≠ ⊤ := by
    intro htop
    apply hWnotH
    rw [htop]
    exact le_top
  rcases QuotientGroup.mk_surjective delta with ⟨g, rfl⟩
  have hstabilizer :
      MulAction.stabilizer X
          (QuotientGroup.mk g : conjugateCosetSpace M) =
        rightConjugate M g⁻¹ := by
    simpa using conjugateCoset_stabilizer M g
  have hconj : IsStronglyEmbedded (rightConjugate M g⁻¹) :=
    rightConjugate_stronglyEmbedded hM g⁻¹
  have hstab : IsStronglyEmbedded
      (MulAction.stabilizer X
        (QuotientGroup.mk g : conjugateCosetSpace M)) := by
    rwa [hstabilizer]
  have hsStab : s ∈ MulAction.stabilizer X
      (QuotientGroup.mk g : conjugateCosetSpace M) :=
    MulAction.mem_stabilizer_iff.mpr hsDelta
  let sN : N := ⟨s, hsNorm⟩
  have hsNH : sN ∈ H := hsStab
  have hsN : IsInvolution sN := IsInvolution.subtype hs hsNorm
  have hHN : IsStronglyEmbedded H :=
    hstab.comap_of_injective N.subtype Subtype.val_injective
      hHproper ⟨sN, hsNH, hsN⟩
  exact not_twoRankAtLeastTwo_of_normal_odd_not_le
    hHN hWodd hWnotH

private theorem involutions_conjugate_of_not_twoRank
    {G : Type*} [Group G] [Finite G]
    (hrank : ¬ TwoRankAtLeastTwo G)
    {x y : G} (hx : IsInvolution x) (hy : IsInvolution y) :
    ∃ g : G, rightConjugateElem x g = y := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
    simp [Nat.card_zpowers,
      orderOf_eq_prime hx.sq_eq_one hx.ne_one]
  have hyp : IsPGroup 2 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers y) (n := 1)
    simp [Nat.card_zpowers,
      orderOf_eq_prime hy.sq_eq_one hy.ne_one]
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  obtain ⟨Q, hyQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  let x' : G := rightConjugateElem x g⁻¹
  have hx'Q : x' ∈ (Q : Subgroup G) := by
    rw [← hg]
    change x' ∈ (P : Subgroup G).map (MulAut.conj g).toMonoidHom
    apply Subgroup.mem_map.mpr
    refine ⟨x, hxP (Subgroup.mem_zpowers x), ?_⟩
    simp [x', rightConjugateElem]
  have hx' : IsInvolution x' := isInvolution_rightConjugateElem hx
  let xQ : Q := ⟨x', hx'Q⟩
  let yQ : Q := ⟨y, hyQ (Subgroup.mem_zpowers y)⟩
  have hxQInv : IsInvolution xQ := IsInvolution.subtype hx' hx'Q
  have hyQInv : IsInvolution yQ :=
    IsInvolution.subtype hy (hyQ (Subgroup.mem_zpowers y))
  have hQrank : ¬ TwoRankAtLeastTwo Q := by
    intro hQr
    exact hrank (hQr.map_of_injective (Q : Subgroup G).subtype
      Subtype.val_injective)
  letI : Nontrivial Q :=
    ⟨⟨xQ, 1, hxQInv.ne_one⟩⟩
  obtain ⟨U, _hUcard, hUunique⟩ :=
    PFAppendixII.unique_order_two_subgroup_of_not_twoRank
      Q.isPGroup' hQrank
  have hxcard : Nat.card (Subgroup.zpowers xQ) = 2 := by
    simp [Nat.card_zpowers,
      orderOf_eq_prime hxQInv.sq_eq_one hxQInv.ne_one]
  have hycard : Nat.card (Subgroup.zpowers yQ) = 2 := by
    simp [Nat.card_zpowers,
      orderOf_eq_prime hyQInv.sq_eq_one hyQInv.ne_one]
  have hxyZ : Subgroup.zpowers xQ = Subgroup.zpowers yQ := by
    rw [hUunique (Subgroup.zpowers xQ) hxcard,
      hUunique (Subgroup.zpowers yQ) hycard]
  let xZ : Subgroup.zpowers xQ :=
    ⟨xQ, Subgroup.mem_zpowers xQ⟩
  let yZ : Subgroup.zpowers xQ :=
    ⟨yQ, by rw [hxyZ]; exact Subgroup.mem_zpowers yQ⟩
  obtain ⟨other, _hother, hotherUnique⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.zpowers xQ)).mp hxcard
  have hxZone : xZ ≠ 1 := by
    intro h
    exact hxQInv.ne_one (congrArg Subtype.val h)
  have hyZone : yZ ≠ 1 := by
    intro h
    exact hyQInv.ne_one (congrArg Subtype.val h)
  have hxyQ : xQ = yQ := by
    have hxOther : xZ = other := hotherUnique xZ hxZone
    have hyOther : yZ = other := hotherUnique yZ hyZone
    exact congrArg Subtype.val (hxOther.trans hyOther.symm)
  refine ⟨g⁻¹, ?_⟩
  exact congrArg Subtype.val hxyQ

public theorem rankOne_pair_involutions_card_eq_two_core
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] [Nonempty Omega]
    (hrank : ¬ TwoRankAtLeastTwo G)
    (hgen : involutionCore G = ⊤)
    (hOmegaEven : Even (Nat.card Omega))
    (hpair : ∀ alpha beta : Omega, alpha ≠ beta →
      ∃ s : G, IsInvolution s ∧ s • alpha = beta) :
    Nat.card Omega = 2 := by
  classical
  have hOmegaTwo : 2 ≤ Nat.card Omega := by
    have hpos : 0 < Nat.card Omega := Nat.card_pos
    rcases hOmegaEven with ⟨n, hn⟩
    omega
  letI : Nontrivial Omega :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let alpha : Omega := Classical.choice inferInstance
  obtain ⟨beta, hbeta⟩ := exists_ne alpha
  obtain ⟨s, hs, hsAlpha⟩ := hpair alpha beta hbeta.symm
  let O : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hOodd : Odd (Nat.card O) := by
    exact Nat.coprime_two_left.mp
      (by simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G))
  have hfactor : O ⊔ Subgroup.centralizer ({s} : Set G) = ⊤ := by
    simpa [O] using
      PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
        hrank hs
  have hqsCenter : q s ∈ Subgroup.center (G ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
    have hgSup : g ∈ O ⊔ Subgroup.centralizer ({s} : Set G) := by
      rw [hfactor]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
      ⟨o, ho, c, hc, hoc⟩
    have hqo : q o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    have hqc : q g = q c := by
      rw [← hoc, map_mul, hqo, one_mul]
    rw [hqc]
    exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hsp : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers s) (n := 1)
    simp [Nat.card_zpowers,
      orderOf_eq_prime hs.sq_eq_one hs.ne_one]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqinj : Function.Injective
      (q.comp (Subgroup.zpowers s).subtype) := by
    simpa [q, O] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (Subgroup.zpowers s) hsp
  let sz : Subgroup.zpowers s := ⟨s, Subgroup.mem_zpowers s⟩
  have hszOrder : orderOf sz = 2 := by
    calc
      orderOf sz = orderOf (sz : G) := (Subgroup.orderOf_coe sz).symm
      _ = 2 := orderOf_eq_prime hs.sq_eq_one hs.ne_one
  have hqsOrder : orderOf (q s) = 2 := by
    have horder := orderOf_injective
      (q.comp (Subgroup.zpowers s).subtype) hqinj sz
    simpa [sz] using horder.trans hszOrder
  have hq_involutions : ∀ t : G, IsInvolution t → q t = q s := by
    intro t ht
    obtain ⟨g, hg⟩ := involutions_conjugate_of_not_twoRank hrank ht hs
    have hqg := congrArg q hg
    have hcomm : q g * q s = q s * q g :=
      Subgroup.mem_center_iff.mp hqsCenter (q g)
    change (q g)⁻¹ * q t * q g = q s at hqg
    calc
      q t = q g * ((q g)⁻¹ * q t * q g) * (q g)⁻¹ := by group
      _ = q g * q s * (q g)⁻¹ := by rw [hqg]
      _ = q s := by rw [hcomm]; group
  have hquotient_zpowers : Subgroup.zpowers (q s) = ⊤ := by
    apply top_unique
    intro y _hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
    have hcore_le : involutionCore G ≤
        (Subgroup.zpowers (q s)).comap q := by
      rw [involutionCore_eq_closure, Subgroup.closure_le]
      intro t ht
      change q t ∈ Subgroup.zpowers (q s)
      rw [hq_involutions t ht]
      exact Subgroup.mem_zpowers (q s)
    apply hcore_le
    rw [hgen]
    trivial
  have hquotientCard : Nat.card (G ⧸ O) = 2 := by
    calc
      Nat.card (G ⧸ O) = Nat.card (⊤ : Subgroup (G ⧸ O)) := by simp
      _ = Nat.card (Subgroup.zpowers (q s)) := by rw [hquotient_zpowers]
      _ = 2 := by simp [Nat.card_zpowers, hqsOrder]
  have htrans : MulAction.IsPretransitive G Omega := by
    constructor
    intro a b
    by_cases hab : a = b
    · exact ⟨1, by simp [hab]⟩
    · obtain ⟨t, _ht, htab⟩ := hpair a b hab
      exact ⟨t, htab⟩
  letI : MulAction.IsPretransitive G Omega := htrans
  let H : Subgroup G := MulAction.stabilizer G alpha
  have hcardOmegaQuotient : Nat.card Omega = Nat.card (G ⧸ H) := by
    calc
      Nat.card Omega = Nat.card (MulAction.orbit G alpha) := by
        simp [MulAction.orbit_eq_univ]
      _ = Nat.card (G ⧸ H) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G alpha)
  have hcardG_O : Nat.card G = 2 * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O,
      hquotientCard]
  have hcardG_H : Nat.card G = Nat.card Omega * Nat.card H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H,
      ← hcardOmegaQuotient]
  have hHodd : Odd (Nat.card H) := by
    apply Nat.not_even_iff_odd.mp
    intro hHeven
    rcases hOmegaEven with ⟨a, ha⟩
    rcases hHeven with ⟨b, hb⟩
    have hfourG : 4 ∣ Nat.card G := by
      refine ⟨a * b, ?_⟩
      rw [hcardG_H, ha, hb]
      ring
    rcases hfourG with ⟨c, hc⟩
    apply hOodd.not_two_dvd_nat
    refine ⟨c, ?_⟩
    omega
  have hHleO : H ≤ O := by
    let I : Subgroup (G ⧸ O) := H.map q
    have hIodd : Odd (Nat.card I) :=
      Odd.of_dvd_nat hHodd (Subgroup.card_map_dvd H q)
    have hIdvd : Nat.card I ∣ 2 := by
      rw [← hquotientCard]
      exact Subgroup.card_subgroup_dvd_card I
    have hIcard : Nat.card I = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hIdvd with h | h
      · exact h
      · exfalso
        apply hIodd.not_two_dvd_nat
        rw [h]
    have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hIcard
    intro x hxH
    have hqxI : q x ∈ I := Subgroup.mem_map_of_mem q hxH
    rw [hIbot] at hqxI
    exact (QuotientGroup.eq_one_iff x).mp hqxI
  have hOleH : O ≤ H := by
    intro o hoO
    by_contra hoH
    have hbetaNe : o • alpha ≠ alpha := by
      exact fun h => hoH (MulAction.mem_stabilizer_iff.mpr h)
    obtain ⟨t, ht, htAlpha⟩ := hpair alpha (o • alpha) hbetaNe.symm
    have hotH : o⁻¹ * t ∈ H := by
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        (o⁻¹ * t) • alpha = o⁻¹ • (t • alpha) := by rw [mul_smul]
        _ = o⁻¹ • (o • alpha) := by rw [htAlpha]
        _ = alpha := inv_smul_smul o alpha
    have htO : t ∈ O := by
      have hotO : o⁻¹ * t ∈ O := hHleO hotH
      have hoInvO : o⁻¹ ∈ O := O.inv_mem hoO
      have : o * (o⁻¹ * t) ∈ O := O.mul_mem hoO hotO
      simpa [mul_assoc] using this
    let tO : O := ⟨t, htO⟩
    have htOorder : orderOf tO = 2 := by
      calc
        orderOf tO = orderOf (tO : G) := (Subgroup.orderOf_coe tO).symm
        _ = 2 := orderOf_eq_prime ht.sq_eq_one ht.ne_one
    have htwoO : 2 ∣ Nat.card O := by
      rw [← htOorder]
      exact orderOf_dvd_natCard tO
    exact hOodd.not_two_dvd_nat htwoO
  have hHO : H = O := le_antisymm hHleO hOleH
  rw [hcardOmegaQuotient, hHO, hquotientCard]

public theorem chapter1_rank_one_pair_involutions_card_eq_two
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] [Nonempty Omega]
    (hrank : ¬ TwoRankAtLeastTwo G)
    (hOmegaEven : Even (Nat.card Omega))
    (hpair : ∀ alpha beta : Omega, alpha ≠ beta →
      ∃ s : G, IsInvolution s ∧ s • alpha = beta) :
    Nat.card Omega = 2 := by
  classical
  let L : Subgroup G := involutionCore G
  letI : MulAction L Omega := MulAction.compHom Omega L.subtype
  have hrankL : ¬ TwoRankAtLeastTwo L := by
    intro hL
    exact hrank (hL.map_of_injective L.subtype Subtype.val_injective)
  apply rankOne_pair_involutions_card_eq_two_core
    hrankL (by simpa [L] using involutionCore_involutionCore_eq_top G)
    hOmegaEven
  intro alpha beta hab
  obtain ⟨s, hs, hsAlpha⟩ := hpair alpha beta hab
  have hsL : s ∈ L := by
    change s ∈ involutionCore G
    rw [involutionCore_eq_closure]
    exact Subgroup.mem_closure_of_mem hs
  let sL : L := ⟨s, hsL⟩
  refine ⟨sL, IsInvolution.subtype hs hsL, ?_⟩
  simpa [sL, MulAction.compHom_smul_def] using hsAlpha

private theorem conjugateCoset_exists_swap
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    {beta gamma : conjugateCosetSpace M} (hbetaGamma : beta ≠ gamma) :
    ∃ t : X, IsInvolution t ∧ t • beta = gamma ∧ t • gamma = beta := by
  obtain ⟨z, hzM, hz⟩ := hM.exists_involution
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  obtain ⟨g, hgbeta⟩ := MulAction.exists_smul_eq X beta alpha
  let gamma' : conjugateCosetSpace M := g • gamma
  have hgamma' : gamma' ≠ alpha := by
    intro h
    apply hbetaGamma
    apply MulAction.injective g
    exact hgbeta.trans h.symm
  obtain ⟨t0, ht0, _ht0M, ht0alpha, ht0gamma⟩ :=
    hM.corollary64_exists_swap hzM hz hgamma'
  let t : X := rightConjugateElem t0 g
  refine ⟨t, isInvolution_rightConjugateElem ht0, ?_, ?_⟩
  · calc
      t • beta = g⁻¹ • (t0 • (g • beta)) := by
        simp [t, rightConjugateElem, mul_smul]
      _ = g⁻¹ • (t0 • alpha) := by rw [hgbeta]
      _ = g⁻¹ • gamma' := by rw [ht0alpha]
      _ = gamma := by simp [gamma']
  · calc
      t • gamma = g⁻¹ • (t0 • (g • gamma)) := by
        simp [t, rightConjugateElem, mul_smul]
      _ = g⁻¹ • (t0 • gamma') := by rfl
      _ = g⁻¹ • alpha := by rw [ht0gamma]
      _ = beta := by rw [← hgbeta]; simp

public theorem twoPointStabilizer_card_odd
    {X Omega : Type*} [Group X] [Finite X] [MulAction X Omega]
    (hunique : ∀ {u : X}, IsInvolution u →
      ∀ {a b : Omega}, u • a = a → u • b = b → a = b)
    {beta gamma : Omega} (hbetaGamma : beta ≠ gamma) :
    Odd (Nat.card (MulAction.stabilizer X beta ⊓
      MulAction.stabilizer X gamma : Subgroup X)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let D : Subgroup X := MulAction.stabilizer X beta ⊓
    MulAction.stabilizer X gamma
  obtain ⟨u, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 heven.two_dvd
  have huData := (orderOf_eq_prime_iff).mp huOrder
  have huD : IsInvolution u := ⟨huData.2, huData.1⟩
  have hu : IsInvolution (u : X) :=
    IsInvolution.map_of_injective huD D.subtype Subtype.val_injective
  have huBeta : (u : X) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp u.property.1
  have huGamma : (u : X) • gamma = gamma :=
    MulAction.mem_stabilizer_iff.mp u.property.2
  exact hbetaGamma (hunique hu huBeta huGamma)

/-- A Sylow subgroup of a pointwise two-point stabilizer is normalized by an
involution interchanging those two points. -/
public theorem exists_involution_normalizing_of_sylow_twoPoint
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ} (hp : Nat.Prime p)
    {beta gamma : conjugateCosetSpace M} (hbetaGamma : beta ≠ gamma)
    (hPsyl : theorem4bIsSylowSubgroupOf p P
      (MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma)) :
    ∃ t : X, IsInvolution t ∧ t ∈ Subgroup.normalizer (P : Set X) ∧
      t • beta = gamma ∧ t • gamma = beta := by
  obtain ⟨t, ht, htBeta, htGamma⟩ :=
    conjugateCoset_exists_swap hM hbetaGamma
  let D : Subgroup X := MulAction.stabilizer X beta ⊓
    MulAction.stabilizer X gamma
  have hDodd : Odd (Nat.card D) := by
    apply twoPointStabilizer_card_odd
      (hunique := fun {u} hu {a b} ha hb =>
        (hM.involution_fixed_coset_unique hu).unique ha hb)
      hbetaGamma
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hforward : ∀ {y : X}, y ∈ D → t * y * t⁻¹ ∈ D := by
      intro y hy
      refine ⟨MulAction.mem_stabilizer_iff.mpr ?_,
        MulAction.mem_stabilizer_iff.mpr ?_⟩
      · calc
          (t * y * t⁻¹) • beta = t • (y • (t⁻¹ • beta)) := by
            simp [mul_smul, mul_assoc]
          _ = t • (y • gamma) := by rw [ht.inv_eq_self, htBeta]
          _ = t • gamma := by rw [MulAction.mem_stabilizer_iff.mp hy.2]
          _ = beta := htGamma
      · calc
          (t * y * t⁻¹) • gamma = t • (y • (t⁻¹ • gamma)) := by
            simp [mul_smul, mul_assoc]
          _ = t • (y • beta) := by rw [ht.inv_eq_self, htGamma]
          _ = t • beta := by rw [MulAction.mem_stabilizer_iff.mp hy.1]
          _ = gamma := htBeta
    constructor
    · exact hforward
    · intro hx
      have hback := hforward (y := t * x * t⁻¹) hx
      have htt : t * t = 1 := by
        simpa [pow_two] using ht.sq_eq_one
      have hcancel : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rwa [hcancel] at hback
  obtain ⟨x, hxNorm⟩ :=
    corollary64_exists_conjugate_involution_normalizing_sylow
      hDodd ht htNormD hp hPsyl
  let u : X := rightConjugateElem t (x : X)
  have hxBeta : (x : X) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp x.property.1
  have hxGamma : (x : X) • gamma = gamma :=
    MulAction.mem_stabilizer_iff.mp x.property.2
  have hxInvBeta : (x : X)⁻¹ • beta = beta := by
    calc
      (x : X)⁻¹ • beta = (x : X)⁻¹ • ((x : X) • beta) := by
        rw [hxBeta]
      _ = beta := inv_smul_smul (x : X) beta
  have hxInvGamma : (x : X)⁻¹ • gamma = gamma := by
    calc
      (x : X)⁻¹ • gamma = (x : X)⁻¹ • ((x : X) • gamma) := by
        rw [hxGamma]
      _ = gamma := inv_smul_smul (x : X) gamma
  refine ⟨u, isInvolution_rightConjugateElem ht, hxNorm, ?_, ?_⟩
  · calc
      u • beta = (x : X)⁻¹ • (t • ((x : X) • beta)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • beta) := by rw [hxBeta]
      _ = (x : X)⁻¹ • gamma := by rw [htBeta]
      _ = gamma := hxInvGamma
  · calc
      u • gamma = (x : X)⁻¹ • (t • ((x : X) • gamma)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • gamma) := by rw [hxGamma]
      _ = (x : X)⁻¹ • beta := by rw [htGamma]
      _ = beta := hxInvBeta

public theorem eq_of_isPGroup_of_le_of_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} (_hp : Nat.Prime p)
    {P Q D : Subgroup G}
    (hPsyl : theorem4bIsSylowSubgroupOf p P D)
    (hQp : IsPGroup p Q) (hPQ : P ≤ Q) (hQD : Q ≤ D) :
    Q = P := by
  classical
  letI : Fact (Nat.Prime p) := ⟨_hp⟩
  rcases hPsyl with ⟨S, hP⟩
  let QD : Subgroup D := Q.subgroupOf D
  have hQDp : IsPGroup p QD :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm
  have hSQD : (S : Subgroup D) ≤ QD := by
    intro x hxS
    change (x : G) ∈ Q
    apply hPQ
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hxS
  have hQD_eq : QD = (S : Subgroup D) :=
    S.is_maximal' hQDp hSQD
  apply le_antisymm
  · intro x hxQ
    let xD : D := ⟨x, hQD hxQ⟩
    have hxQD : xD ∈ QD := hxQ
    rw [hQD_eq] at hxQD
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hxQD
  · exact hPQ

public theorem odd_pSubgroup_le_pairStabilizer_of_normalizes
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega] {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    {R A : Subgroup G} (hAp : IsPGroup p A)
    (hAnorm : A ≤ Subgroup.normalizer (R : Set G))
    {beta gamma : Omega} (hbetaGamma : beta ≠ gamma)
    (hRbeta : beta ∈ fixedPointsOfSubgroup G Omega R)
    (hRgamma : gamma ∈ fixedPointsOfSubgroup G Omega R)
    (hRcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega R} = 2) :
    A ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let FixedR := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup G Omega R}
  let betaR : FixedR := ⟨beta, hRbeta⟩
  let gammaR : FixedR := ⟨gamma, hRgamma⟩
  obtain ⟨other, hother, hotherUnique⟩ :=
    (Nat.card_eq_two_iff' betaR).mp hRcard
  have hgammaOther : gammaR = other := by
    apply hotherUnique gammaR
    intro h
    apply hbetaGamma
    exact congrArg Subtype.val h.symm
  have hgammaNotOrbit : gamma ∉ MulAction.orbit A beta := by
    intro hgammaOrbit
    let f : MulAction.orbit A beta → FixedR := fun x =>
      ⟨x, by
        rcases x.property with ⟨a, ha⟩
        rw [← ha]
        exact fixedPoints_smul_of_mem_normalizer
          (hAnorm a.property) hRbeta⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : FixedR => (z : Omega)) hxy
    have horbitLe : Nat.card (MulAction.orbit A beta) ≤ 2 := by
      calc
        Nat.card (MulAction.orbit A beta) ≤ Nat.card FixedR :=
          Nat.card_le_card_of_injective f hf
        _ = 2 := hRcard
    let betaO : MulAction.orbit A beta := ⟨beta, ⟨1, by simp⟩⟩
    let gammaO : MulAction.orbit A beta := ⟨gamma, hgammaOrbit⟩
    have hbetaGammaO : betaO ≠ gammaO := by
      intro h
      exact hbetaGamma (congrArg Subtype.val h)
    letI : Nontrivial (MulAction.orbit A beta) :=
      ⟨⟨betaO, gammaO, hbetaGammaO⟩⟩
    have horbitTwo : Nat.card (MulAction.orbit A beta) = 2 := by
      have hone : 1 < Nat.card (MulAction.orbit A beta) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    obtain ⟨n, hn⟩ := hAp.card_orbit beta
    have hoddOrbit : Odd (Nat.card (MulAction.orbit A beta)) := by
      rw [hn]
      exact hpOdd.pow
    rw [horbitTwo] at hoddOrbit
    rcases hoddOrbit with ⟨k, hk⟩
    omega
  intro a haA
  have haNorm : a ∈ Subgroup.normalizer (R : Set G) := hAnorm haA
  have haBetaR : a • beta ∈ fixedPointsOfSubgroup G Omega R :=
    fixedPoints_smul_of_mem_normalizer haNorm hRbeta
  let aBetaR : FixedR := ⟨a • beta, haBetaR⟩
  have haBeta : a • beta = beta := by
    by_contra hne
    have haOther : aBetaR = other := by
      apply hotherUnique aBetaR
      intro h
      exact hne (congrArg Subtype.val h)
    apply hgammaNotOrbit
    refine ⟨⟨a, haA⟩, ?_⟩
    exact congrArg Subtype.val (haOther.trans hgammaOther.symm)
  have haGammaR : a • gamma ∈ fixedPointsOfSubgroup G Omega R :=
    fixedPoints_smul_of_mem_normalizer haNorm hRgamma
  let aGammaR : FixedR := ⟨a • gamma, haGammaR⟩
  have haGamma : a • gamma = gamma := by
    by_cases hbase : aGammaR = betaR
    · exfalso
      apply hbetaGamma
      apply MulAction.injective a
      calc
        a • beta = beta := haBeta
        _ = a • gamma := (congrArg Subtype.val hbase).symm
    · exact congrArg Subtype.val
        ((hotherUnique aGammaR hbase).trans hgammaOther.symm)
  exact ⟨MulAction.mem_stabilizer_iff.mpr haBeta,
    MulAction.mem_stabilizer_iff.mpr haGamma⟩

private theorem pair_involution_of_same_normalizer_orbit
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hmax : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q}) P)
    {beta gamma : conjugateCosetSpace M}
    (hbeta : beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P)
    (hgamma : gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P)
    (hbetaGamma : beta ≠ gamma)
    (g : Subgroup.normalizer (P : Set X))
    (hg : (g : X) • beta = gamma) :
    ∃ s : X, IsInvolution s ∧ s ∈ Subgroup.normalizer (P : Set X) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let Omega := conjugateCosetSpace M
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  let D : Subgroup X :=
    MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hbeta x hxP),
      MulAction.mem_stabilizer_iff.mpr (hgamma x hxP)⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let Q : Subgroup X := (S : Subgroup D).map D.subtype
  have hPQ : P ≤ Q := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  by_cases hPQeq : P = Q
  · obtain ⟨t, ht, htNorm, _htBeta, _htGamma⟩ :=
      exists_involution_normalizing_of_sylow_twoPoint
        hM hp hbetaGamma ⟨S, hPQeq⟩
    exact ⟨t, ht, htNorm⟩
  have hPQlt : P < Q := lt_of_le_of_ne hPQ hPQeq
  have hQp : IsPGroup p Q := S.isPGroup'.map D.subtype
  obtain ⟨R₀, hR₀p, hPR₀, hR₀Q, hR₀N⟩ :=
    exists_larger_normalizer_pSubgroup hp hQp hPQlt
  let K : Subgroup X := N ⊓ D
  have hR₀K : R₀ ≤ K := by
    intro x hxR₀
    exact ⟨hR₀N hxR₀,
      (show Q ≤ D by
        simpa [Q] using Subgroup.map_le_range D.subtype (S : Subgroup D))
        (hR₀Q hxR₀)⟩
  let R₀K : Subgroup K := R₀.subgroupOf K
  have hR₀Kp : IsPGroup p R₀K :=
    hR₀p.of_equiv (Subgroup.subgroupOfEquivOfLe hR₀K).symm
  obtain ⟨T, hR₀KT⟩ := hR₀Kp.exists_le_sylow
  let R : Subgroup X := (T : Subgroup K).map K.subtype
  have hR₀R : R₀ ≤ R := by
    intro x hxR₀
    let xK : K := ⟨x, hR₀K hxR₀⟩
    exact Subgroup.mem_map.mpr
      ⟨xK, hR₀KT (show xK ∈ R₀K from hxR₀), rfl⟩
  have hPR : P < R := hPR₀.trans_le hR₀R
  have hRp : IsPGroup p R := T.isPGroup'.map K.subtype
  have hRK : R ≤ K := by
    simpa [R] using Subgroup.map_le_range K.subtype (T : Subgroup K)
  have hRN : R ≤ N := hRK.trans inf_le_left
  have hRD : R ≤ D := hRK.trans inf_le_right
  have hRbeta : beta ∈ fixedPointsOfSubgroup X Omega R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).1
  have hRgamma : gamma ∈ fixedPointsOfSubgroup X Omega R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).2
  have hRcard : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega R} = 2 := by
    apply Nat.le_antisymm
    · by_contra hle
      have hthree : 2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega R} := by omega
      have hRleP := hmax.2 ⟨hRp, hthree⟩ hPR.le
      exact (not_le_of_gt hPR) hRleP
    · let f : Fin 2 → {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega R} :=
        fun i => if i = 0 then ⟨beta, hRbeta⟩ else ⟨gamma, hRgamma⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaGamma
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaGamma
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
  let RN : Subgroup N := R.subgroupOf N
  let B : Subgroup N := MulAction.stabilizer N beta
  have hRNB : RN ≤ B := by
    intro r hrRN
    apply MulAction.mem_stabilizer_iff.mpr
    change (r : X) • beta = beta
    exact hRbeta (r : X) hrRN
  have hRsylB : theorem4bIsSylowSubgroupOf p RN B := by
    let RNB : Subgroup B := RN.subgroupOf B
    have hRNBp : IsPGroup p RNB := by
      have hRNp : IsPGroup p RN :=
        hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
      exact hRNp.of_equiv (Subgroup.subgroupOfEquivOfLe hRNB).symm
    obtain ⟨U, hRNBU⟩ := hRNBp.exists_le_sylow
    let UN : Subgroup N := (U : Subgroup B).map B.subtype
    have hRNUN : RN ≤ UN := by
      intro r hrRN
      let rB : B := ⟨r, hRNB hrRN⟩
      exact Subgroup.mem_map.mpr
        ⟨rB, hRNBU (show rB ∈ RNB from hrRN), rfl⟩
    have hRNeqUN : RN = UN := by
      by_contra hne
      have hRNUNlt : RN < UN := lt_of_le_of_ne hRNUN hne
      let UX : Subgroup X := UN.map N.subtype
      have hRUX : R ≤ UX := by
        intro x hxR
        let xN : N := ⟨x, hRN hxR⟩
        exact Subgroup.mem_map.mpr
          ⟨xN, hRNUN (show xN ∈ RN from hxR), rfl⟩
      have hRUXne : R ≠ UX := by
        intro hEq
        apply hne
        apply le_antisymm hRNUN
        intro x hxUN
        have hxUX : (x : X) ∈ UX :=
          Subgroup.mem_map_of_mem N.subtype hxUN
        rw [← hEq] at hxUX
        exact hxUX
      have hRUXlt : R < UX := lt_of_le_of_ne hRUX hRUXne
      have hUXp : IsPGroup p UX := by
        exact (U.isPGroup'.map B.subtype).map N.subtype
      have hUXN : UX ≤ N := by
        simpa [UX] using Subgroup.map_le_range N.subtype UN
      have hUXbeta : UX ≤ MulAction.stabilizer X beta := by
        intro x hxUX
        rcases Subgroup.mem_map.mp hxUX with ⟨xN, hxUN, rfl⟩
        have hxB : xN ∈ B := by
          simpa [UN] using
            (Subgroup.map_le_range B.subtype (U : Subgroup B) hxUN)
        exact MulAction.mem_stabilizer_iff.mpr
          (MulAction.mem_stabilizer_iff.mp hxB)
      obtain ⟨A, hAp, hRA, hAUX, hAnormR⟩ :=
        exists_larger_normalizer_pSubgroup hp hUXp hRUXlt
      have hAD : A ≤ D :=
        odd_pSubgroup_le_pairStabilizer_of_normalizes
          hp hpOdd hAp hAnormR hbetaGamma hRbeta hRgamma hRcard
      have hAK : A ≤ K := by
        intro a haA
        exact ⟨hUXN (hAUX haA), hAD haA⟩
      have hRsylK : theorem4bIsSylowSubgroupOf p R K := ⟨T, rfl⟩
      have hAR : A = R :=
        eq_of_isPGroup_of_le_of_sylow hp hRsylK hAp hRA.le hAK
      exact hRA.ne hAR.symm
    exact ⟨U, hRNeqUN⟩
  rcases hRsylB with ⟨Sbeta, hRN_eq⟩
  have hgammaRN : gamma ∈ fixedPointsOfSubgroup N Omega RN := by
    intro r hrRN
    change (r : X) • gamma = gamma
    exact hRgamma (r : X) hrRN
  have hgammaS : gamma ∈ fixedPointsOfSubgroup N Omega
      ((Sbeta : Subgroup B).map B.subtype) := by
    rw [← hRN_eq]
    exact hgammaRN
  obtain ⟨n, hn⟩ :=
    witt_normalizer_fixedPoint_transporter hp beta gamma Sbeta
      hgammaS g hg
  have hnNormRN : (n : N) ∈ Subgroup.normalizer (RN : Set N) := by
    rw [hRN_eq]
    exact n.property
  have hRNmap : RN.map N.subtype = R := by
    rw [show RN = R.subgroupOf N by rfl,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRN]
  have hnNormR : ((n : N) : X) ∈ Subgroup.normalizer (R : Set X) := by
    have hnMap : ((n : N) : X) ∈
        (Subgroup.normalizer (RN : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hnNormRN
    have hmap := (Subgroup.le_normalizer_map (H := RN) N.subtype) hnMap
    rwa [hRNmap] at hmap
  let FixedR := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega R}
  let betaR : FixedR := ⟨beta, hRbeta⟩
  let gammaR : FixedR := ⟨gamma, hRgamma⟩
  obtain ⟨other, _hother, hotherUnique⟩ :=
    (Nat.card_eq_two_iff' betaR).mp hRcard
  have hgammaOther : gammaR = other := by
    apply hotherUnique gammaR
    intro h
    apply hbetaGamma
    exact congrArg Subtype.val h.symm
  have hnGammaR : ((n : N) : X) • gamma ∈
      fixedPointsOfSubgroup X Omega R :=
    fixedPoints_smul_of_mem_normalizer hnNormR hRgamma
  let nGammaR : FixedR := ⟨((n : N) : X) • gamma, hnGammaR⟩
  have hnGamma : ((n : N) : X) • gamma = beta := by
    by_cases hbase : nGammaR = betaR
    · exact congrArg Subtype.val hbase
    · have hngamma : ((n : N) : X) • gamma = gamma :=
        congrArg Subtype.val
          ((hotherUnique nGammaR hbase).trans hgammaOther.symm)
      exfalso
      apply hbetaGamma
      apply MulAction.injective ((n : N) : X)
      exact hn.trans hngamma.symm
  let C : Subgroup N := Subgroup.zpowers (n : N)
  have hCNormRN : C ≤ Subgroup.normalizer (RN : Set N) := by
    exact Subgroup.zpowers_le.mpr hnNormRN
  have hCNormR : ∀ c : C,
      (((c : N) : X) ∈ Subgroup.normalizer (R : Set X)) := by
    intro c
    have hcMapMem : (((c : N) : X)) ∈
        (Subgroup.normalizer (RN : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype (hCNormRN c.property)
    have hcMap := (Subgroup.le_normalizer_map (H := RN) N.subtype) hcMapMem
    rwa [hRNmap] at hcMap
  have hCOrbitLe : Nat.card (MulAction.orbit C beta) ≤ 2 := by
    let f : MulAction.orbit C beta → FixedR := fun x =>
      ⟨x, by
        rcases x.property with ⟨c, hc⟩
        rw [← hc]
        exact fixedPoints_smul_of_mem_normalizer (hCNormR c) hRbeta⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : FixedR => (z : Omega)) hxy
    calc
      Nat.card (MulAction.orbit C beta) ≤ Nat.card FixedR :=
        Nat.card_le_card_of_injective f hf
      _ = 2 := hRcard
  have hgammaCOrbit : gamma ∈ MulAction.orbit C beta := by
    refine ⟨⟨(n : N), Subgroup.mem_zpowers (n : N)⟩, ?_⟩
    exact hn
  let betaC : MulAction.orbit C beta := ⟨beta, ⟨1, by simp⟩⟩
  let gammaC : MulAction.orbit C beta := ⟨gamma, hgammaCOrbit⟩
  have hbetaGammaC : betaC ≠ gammaC := by
    intro h
    exact hbetaGamma (congrArg Subtype.val h)
  letI : Nontrivial (MulAction.orbit C beta) :=
    ⟨⟨betaC, gammaC, hbetaGammaC⟩⟩
  have hCOrbitCard : Nat.card (MulAction.orbit C beta) = 2 := by
    have hone : 1 < Nat.card (MulAction.orbit C beta) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite (MulAction.orbit C beta)
  letI := Fintype.ofFinite (MulAction.stabilizer C beta)
  have horbitStabilizer :
      Nat.card (MulAction.orbit C beta) *
          Nat.card (MulAction.stabilizer C beta) = Nat.card C := by
    simpa only [Nat.card_eq_fintype_card] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group C beta)
  have hCcardEven : Even (Nat.card C) := by
    refine ⟨Nat.card (MulAction.stabilizer C beta), ?_⟩
    rw [hCOrbitCard] at horbitStabilizer
    omega
  obtain ⟨s, hsOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 hCcardEven.two_dvd
  have hsData := (orderOf_eq_prime_iff).mp hsOrder
  have hsC : IsInvolution s := ⟨hsData.2, hsData.1⟩
  have hsN : IsInvolution (s : N) :=
    IsInvolution.map_of_injective hsC C.subtype Subtype.val_injective
  have hsX : IsInvolution ((s : N) : X) :=
    IsInvolution.map_of_injective hsN N.subtype Subtype.val_injective
  exact ⟨((s : N) : X), hsX, (s : N).property⟩

public theorem lemma_5_1_normalizer_involution
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X}
    (hM : IsStronglyEmbedded M) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hmax : Maximal (fun Q : Subgroup X =>
      IsPGroup p Q ∧
        2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q}) P) :
    ∃ s : X, IsInvolution s ∧ s ∈ Subgroup.normalizer (P : Set X) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let Omega := conjugateCosetSpace M
  let FixedP := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega P}
  have hFixedP : 2 < Nat.card FixedP := hmax.1.2
  letI : Nontrivial FixedP :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let betaP : FixedP := Classical.choice inferInstance
  obtain ⟨gammaP, hgammaP⟩ := exists_ne betaP
  let beta : Omega := betaP
  let gamma : Omega := gammaP
  have hbeta : beta ∈ fixedPointsOfSubgroup X Omega P := betaP.property
  have hgamma : gamma ∈ fixedPointsOfSubgroup X Omega P := gammaP.property
  have hbetaGamma : beta ≠ gamma := by
    intro h
    exact hgammaP (Subtype.ext h.symm)
  let D : Subgroup X :=
    MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hbeta x hxP),
      MulAction.mem_stabilizer_iff.mpr (hgamma x hxP)⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let Q : Subgroup X := (S : Subgroup D).map D.subtype
  have hPQ : P ≤ Q := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  by_cases hPQeq : P = Q
  · obtain ⟨t, ht, htNorm, _htBeta, _htGamma⟩ :=
      exists_involution_normalizing_of_sylow_twoPoint
        hM hp hbetaGamma ⟨S, hPQeq⟩
    exact ⟨t, ht, htNorm⟩
  have hPQlt : P < Q := lt_of_le_of_ne hPQ hPQeq
  have hQp : IsPGroup p Q := S.isPGroup'.map D.subtype
  obtain ⟨R₀, hR₀p, hPR₀, hR₀Q, hR₀N⟩ :=
    exists_larger_normalizer_pSubgroup hp hQp hPQlt
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  have hQD : Q ≤ D := by
    simpa [Q] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hR₀D : R₀ ≤ D := hR₀Q.trans hQD
  have hR₀beta : beta ∈ fixedPointsOfSubgroup X Omega R₀ := by
    intro x hxR₀
    exact MulAction.mem_stabilizer_iff.mp (hR₀D hxR₀).1
  have hR₀gamma : gamma ∈ fixedPointsOfSubgroup X Omega R₀ := by
    intro x hxR₀
    exact MulAction.mem_stabilizer_iff.mp (hR₀D hxR₀).2
  have hR₀card : Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega R₀} = 2 := by
    apply Nat.le_antisymm
    · by_contra hle
      have hthree : 2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega R₀} := by omega
      have hR₀leP := hmax.2 ⟨hR₀p, hthree⟩ hPR₀.le
      exact (not_le_of_gt hPR₀) hR₀leP
    · let f : Fin 2 → {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega R₀} :=
        fun i => if i = 0 then ⟨beta, hR₀beta⟩ else ⟨gamma, hR₀gamma⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaGamma
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaGamma
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
  let FixedR₀ := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega R₀}
  have hdeltaExists : ∃ delta : FixedP,
      ¬ (delta : Omega) ∈ fixedPointsOfSubgroup X Omega R₀ := by
    by_contra hno
    push Not at hno
    let f : FixedP → FixedR₀ := fun delta => ⟨delta, hno delta⟩
    have hf : Function.Injective f := by
      intro delta epsilon h
      exact Subtype.ext (congrArg (fun z : FixedR₀ => (z : Omega)) h)
    have hcardLe : Nat.card FixedP ≤ Nat.card FixedR₀ :=
      Nat.card_le_card_of_injective f hf
    rw [hR₀card] at hcardLe
    omega
  obtain ⟨deltaP, hdeltaNot⟩ := hdeltaExists
  let delta : Omega := deltaP
  have hdelta : delta ∈ fixedPointsOfSubgroup X Omega P := deltaP.property
  change ¬ ∀ x : X, x ∈ R₀ → x • delta = delta at hdeltaNot
  push Not at hdeltaNot
  obtain ⟨r, hrR₀, hrDelta⟩ := hdeltaNot
  let epsilon : Omega := r • delta
  have hepsilon : epsilon ∈ fixedPointsOfSubgroup X Omega P := by
    exact fixedPoints_smul_of_mem_normalizer (hR₀N hrR₀) hdelta
  have hdeltaEpsilon : delta ≠ epsilon := by
    exact Ne.symm hrDelta
  let rN : N := ⟨r, hR₀N hrR₀⟩
  apply pair_involution_of_same_normalizer_orbit
    hM hp hpOdd hmax hdelta hepsilon hdeltaEpsilon rN
  rfl
end CFSG.BenderSuzuki
