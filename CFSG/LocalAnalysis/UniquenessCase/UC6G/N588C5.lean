module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588C4
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S25
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S27
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S28
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C636a
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S15
public import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
public import CFSG.Holt.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calNOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

open N588

@[expose] def zClosure (N : Subgroup G) : Subgroup G :=
  (normalClosure ((m.Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype

theorem isSylowOf_R_top : IsSylowOf m.r m.R ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine ⟨m.toMc614.sylowTop.subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq, Mc614.coe_sylowTop]

theorem pRank_zClosure (hK : UCK.K332') (h69 : R6_9 Dat)
    (h623 : m.C623) (hr3 : m.r ≠ 3) {N : Subgroup G} (hNtop : N ≠ ⊤) (hZN : m.Z ≤ N) :
    CFSG.Open.pRank m.r (m.zClosure N) = 1 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h5 : 5 ≤ m.r := m.five_le_r hr3
  have hNk : CFSG.Open.IsKGroup ↥N := Dat.standing.kProper.isKGroup N hNtop
  set Z' : Subgroup ↥N := m.Z.subgroupOf N with hZ'
  have hZ'card : Nat.card Z' = m.r := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv]
    exact m.card_Z
  have hZ'p : IsPGroup m.r Z' :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZ'card)
  obtain ⟨S', hS'syl, hZS'⟩ := exists_isSylowOf_ge (p := m.r) (K := (⊤ : Subgroup ↥N))
    (Q := Z') (fun x _ => trivial) hZ'p
  have hS''p : IsPGroup m.r (S'.map N.subtype) := hS'syl.isPGroup.map _
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf m.isSylowOf_R_top le_top hS''p
  have hsix := m.hZ.sixteen h69
  have hS'comm : ∀ x ∈ S', x ^ m.r = 1 → ∀ y ∈ S', x * y = y * x := by
    intro x hx hxr y hy
    have hxR : k⁻¹ * (x : G) * k ∈ m.R := hk _ ⟨x, hx, rfl⟩
    have hxA : k⁻¹ * (x : G) * k ∈ m.Z ⊔ m.E := by
      refine hsix.2 _ hxR ?_
      have hx1 : (x : G) ^ m.r = 1 := by simpa using congrArg Subtype.val hxr
      have := conj_pow (a := k⁻¹) (b := (x : G)) (i := m.r)
      rw [inv_inv] at this
      rw [this, hx1]
      simp
    have hyR : k⁻¹ * (y : G) * k ∈ m.R := hk _ ⟨y, hy, rfl⟩
    have hc := hsix.1 _ hxA _ hyR
    apply Subtype.ext
    have h3 : k⁻¹ * ((x : G) * y) * k = k⁻¹ * ((y : G) * x) * k := by
      calc k⁻¹ * ((x : G) * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
        _ = (k⁻¹ * y * k) * (k⁻¹ * x * k) := hc
        _ = k⁻¹ * ((y : G) * x) * k := by group
    have h4 := congrArg (fun t => k * t * k⁻¹) h3
    simpa [mul_assoc] using h4
  have hS'rank : CFSG.Open.pRank m.r S' ≤ 3 := by
    have h1 : S'.map N.subtype ≤ uniqueFourConj k⁻¹ m.R := by
      intro x hx
      rw [mem_uniqueFourConj_iff]
      simpa using hk x hx
    have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono m.r m.hr h1
    rw [pRank_uniqueFourConj m.r m.hr, pRank_map_subtype_uc6 m.hr N] at h2
    exact h2.trans m.rank_le_three
  have hS'wc : IsWeaklyClosedIn Z' S' := by
    intro g hg
    have hZk : CFSG.conjugate m.Z k ≤ m.R := by
      intro y hy
      have hz : k * y * k⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hzS : (⟨k * y * k⁻¹, hZN hz⟩ : ↥N) ∈ S' := hZS' hz
      have := hk _ ⟨_, hzS, rfl⟩
      simpa [mul_assoc] using this
    have hZgk : CFSG.conjugate m.Z ((g : G) * k) ≤ m.R := by
      intro y hy
      have hz : (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hwN : k * y * k⁻¹ ∈ N := by
        have e : k * y * k⁻¹ = (g : G)⁻¹ * ((g : G) * k * y * ((g : G) * k)⁻¹) * g := by group
        rw [e]
        exact N.mul_mem (N.mul_mem (N.inv_mem g.2) (hZN hz)) g.2
      have hw' : (⟨k * y * k⁻¹, hwN⟩ : ↥N) ∈ CFSG.conjugate Z' g := by
        rw [mem_conjugate_iff_uc6]
        show (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ ∈ m.Z
        have e : (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ = (g : G) * k * y * ((g : G) * k)⁻¹ := by
          group
        rw [e]
        exact hz
      have := hk _ ⟨_, hg hw', rfl⟩
      simpa [mul_assoc] using this
    have hk1 := h623 k hZk
    have hk2 := h623 ((g : G) * k) hZgk
    have e1 : ∀ y : G, k * y * k⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk1]
    have e2 : ∀ y : G, (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk2]
    ext x
    rw [mem_conjugate_iff_uc6]
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ m.Z ↔ (x : G) ∈ m.Z
    have h1 := e2 (k⁻¹ * (x : G) * k)
    have h2 := e1 (k⁻¹ * (x : G) * k)
    have e3 : (g : G) * k * (k⁻¹ * (x : G) * k) * ((g : G) * k)⁻¹ =
        (g : G) * (x : G) * (g : G)⁻¹ := by
      group
    have e4 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = (x : G) := by group
    rw [e3] at h1
    rw [e4] at h2
    exact h1.trans h2.symm
  have h1 := hK ↥N hNk m.r m.hr h5 S' hS'syl hS'comm hS'rank Z' hZS' hZ'card hS'wc
  rw [zClosure, pRank_map_subtype_uc6 m.hr N]
  exact h1

theorem zClosure_le (N : Subgroup G) : m.zClosure N ≤ N := map_subtype_le _

theorem Z_le_zClosure {N : Subgroup G} (hZN : m.Z ≤ N) : m.Z ≤ m.zClosure N := by
  intro z hz
  exact ⟨⟨z, hZN hz⟩, Subgroup.subset_normalClosure (show (⟨z, hZN hz⟩ : ↥N) ∈ m.Z.subgroupOf N
    from hz), rfl⟩

theorem zClosure_normal (N : Subgroup G) : ((m.zClosure N).subgroupOf N).Normal := by
  rw [zClosure, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  infer_instance

theorem le_normalizer_zClosure (N : Subgroup G) :
    N ≤ normalizer ((m.zClosure N : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (m.zClosure_le N)).1 (m.zClosure_normal N)

theorem isCyclic_of_le_zClosure (hK : UCK.K332') (h69 : R6_9 Dat)
    (h623 : m.C623) (hr3 : m.r ≠ 3) {N : Subgroup G} (hNtop : N ≠ ⊤) (hZN : m.Z ≤ N)
    {D : Subgroup G} (hD : D ≤ m.zClosure N) (hDp : IsPGroup m.r D) : IsCyclic D := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  by_contra hnc
  obtain ⟨B, hBel, hBcard⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (m.hr.odd_of_ne_two m.d.odd) hDp hnc
  have hEel : IsElemAbelian m.r (B.map D.subtype) :=
    (isElemAbelian_iff_isElementaryAbelian.mpr hBel).map D.subtype
  have hEcard : Nat.card (B.map D.subtype) = m.r ^ 2 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hBcard
  have h2 := le_pRank_of_elemAbelian m.hr ((map_subtype_le _).trans hD) hEel hEcard
  have h1 := m.pRank_zClosure hK h69 h623 hr3 hNtop hZN
  omega

theorem commutator_zClosure_L_eq_bot (hK : UCK.K332') (hSch : UCK.KSch)
    (h69 : R6_9 Dat) (h619 : m.C619) (h620 : m.C620) (h623 : m.C623)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (hr3 : m.r ≠ 3) {N : Subgroup G} (hN : N ∈ calNOf (m.A ⊔ m.L)) :
    ⁅m.zClosure N, m.L⁆ = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hNle : m.A ⊔ m.L ≤ N := hN.2
  have hNtop : N ≠ ⊤ := hN.1.1
  have hZN : m.Z ≤ N := (m.Z_le_A.trans le_sup_left).trans hNle
  have hLN : m.L ≤ N := le_sup_right.trans hNle
  have hLperf := m.L_perfect_of_simple h620 hL1
  have hLO : m.L ≤ centralizer ((rCore m.r N : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (m.commutator_rCore_L_eq_bot hSch h619 h620 hL1 hL3 hr3 hN))
  have hIN : m.zClosure N ≤ N := m.zClosure_le N
  have hIn := m.zClosure_normal N
  have hLI : m.L ≤ normalizer ((m.zClosure N : Subgroup G) : Set G) :=
    hLN.trans (m.le_normalizer_zClosure N)
  have hcyc : ∀ D : Subgroup G, D ≤ m.zClosure N → IsPGroup m.r D → IsCyclic D :=
    fun D hD hDp => m.isCyclic_of_le_zClosure hK h69 h623 hr3 hNtop hZN hD hDp
  have hcore : ∀ Y : Subgroup G, Y ≤ N → N ≤ normalizer (Y : Set G) →
      Nat.Coprime m.r (Nat.card Y) → m.L ≤ centralizer (Y : Set G) := by
    intro Y hYN hNY hcop
    have hYO : Y ≤ rCore m.r N := by
      intro y hy
      have hle : Y.subgroupOf N ≤ CFSG.pPrimeCore m.r ↥N := le_sSup
        ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hYN).2 hNY, by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]; exact hcop⟩
      exact ⟨⟨y, hYN hy⟩, hle hy, rfl⟩
    exact hLO.trans (Subgroup.centralizer_le hYO)
  refine N588.commutator_eq_bot_of_fitting_of_components hLI hLperf ?_ ?_
  · rw [CFSG.fittingSubgroupOf, CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    rintro ⟨⟨q, hqmem⟩, -⟩
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    haveI : Fact q.Prime := ⟨hq⟩
    show m.L ≤ centralizer (((CFSG.pCore q ↥(m.zClosure N)).map (m.zClosure N).subtype :
      Subgroup G) : Set G)
    have hPp : IsPGroup q ((CFSG.pCore q ↥(m.zClosure N)).map (m.zClosure N).subtype) :=
      CFSG.pCore_isPGroup.map _
    have hNP : N ≤ normalizer (((CFSG.pCore q ↥(m.zClosure N)).map (m.zClosure N).subtype :
        Subgroup G) : Set G) := fun n hn =>
      mem_normalizer_map_of_characteristic (m.le_normalizer_zClosure N hn)
    have hPI : (CFSG.pCore q ↥(m.zClosure N)).map (m.zClosure N).subtype ≤ m.zClosure N :=
      map_subtype_le _
    by_cases hqr : q = m.r
    · have hPp' : IsPGroup m.r ((CFSG.pCore q ↥(m.zClosure N)).map (m.zClosure N).subtype) :=
        hqr ▸ hPp
      have hPc := hcyc _ hPI hPp'
      have hle : ⁅m.L, m.L⁆ ≤ centralizer (((CFSG.pCore q ↥(m.zClosure N)).map
          (m.zClosure N).subtype : Subgroup G) : Set G) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := UC6.commutator_centralizes_of_isCyclic_uc6 hPc (hNP (hLN ha)) (hNP (hLN hb))
          x hx
        rw [commutatorElement_def]
        exact h1.symm
      rw [hLperf] at hle
      exact hle
    · refine hcore _ (hPI.trans hIN) hNP ?_
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hPp
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes m.hr hq).2 (Ne.symm hqr))
  · intro K hK
    by_cases hdK : m.r ∣ Nat.card K
    · have hLK : m.L ≤ normalizer (K : Set G) := by
        intro ℓ hℓ
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hc := CFSG.Walter.isComponentOf_map_conj hK (hLI hℓ)
        have hd : m.r ∣ Nat.card (K.map (MulAut.conj ℓ).toMonoidHom) := by
          rwa [Subgroup.card_map_of_injective (MulAut.conj ℓ).injective]
        exact N588.eq_of_isComponentOf_of_dvd hc hK hd hdK hcyc
      have hKk : CFSG.Open.IsKGroup ↥K :=
        (Dat.standing.kProper.isKGroup N hNtop).of_le (hK.1.trans hIN)
      exact N588.le_centralizer_of_cyclic hSch hK.2.2 hKk hLK hLperf hL1 inf_le_right
        ((m.isElemAbelian_A).mono inf_le_left) (m.card_A_inf_L h620)
        fun D hD hDp => hcyc D (hD.trans hK.1) hDp
    · have hcop : Nat.Coprime m.r (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd m.hr).2 hdK
      have hKO : K ≤ rCore m.r N := N588.le_map_pPrimeCore_of_isSubnormal hK.1 hK.2.1 hIN hIn hcop
      exact hLO.trans (Subgroup.centralizer_le hKO)

theorem le_normalizer_L_of_mem_calNOf (hK : UCK.K332') (hSch : UCK.KSch)
    (h69 : R6_9 Dat) (h619 : m.C619) (h620 : m.C620) (h623 : m.C623)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (hr3 : m.r ≠ 3) {N : Subgroup G} (hN : N ∈ calNOf (m.A ⊔ m.L)) :
    N ≤ normalizer (m.L : Set G) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hNle : m.A ⊔ m.L ≤ N := hN.2
  have hZN : m.Z ≤ N := (m.Z_le_A.trans le_sup_left).trans hNle
  have hIN : m.zClosure N ≤ N := m.zClosure_le N
  have hZI := m.Z_le_zClosure hZN
  have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z)
  obtain ⟨D, hDsyl, hZD⟩ := exists_isSylowOf_ge hZI hZp
  have hDc : IsCyclic D :=
    m.isCyclic_of_le_zClosure hK h69 h623 hr3 hN.1.1 hZN hDsyl.le hDsyl.isPGroup
  have hfr := frattini_of_isSylowOf hIN (m.le_normalizer_zClosure N) hDsyl
  have hDZ : N ⊓ normalizer (D : Set G) ≤ normalizer (m.Z : Set G) := by
    rintro g ⟨-, hg⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : m.Z.map (MulAut.conj g).toMonoidHom ≤ D := by
      rintro _ ⟨z, hz, rfl⟩
      exact (mem_normalizer_iff.1 hg z).1 (hZD hz)
    have hcard : Nat.card ((m.Z.map (MulAut.conj g).toMonoidHom).subgroupOf D) =
        Nat.card (m.Z.subgroupOf D) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have h2 := (IsCyclic.subgroup_eq_iff_card_eq).2 hcard
    have h3 := congrArg (Subgroup.map D.subtype) h2
    rw [Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_subgroupOf_eq_of_le hZD] at h3
    exact h3
  have hIL : m.zClosure N ≤ normalizer (m.L : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (m.commutator_zClosure_L_eq_bot hK hSch h69 h619 h620 h623 hL1 hL3 hr3 hN)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [hfr]
  exact sup_le hIL ((inf_le_inf_left _ le_rfl).trans (hDZ.trans m.normalizer_Z_le_normalizer_L))

theorem calNOf_eq_normalizer_L (hK : UCK.K332') (hSch : UCK.KSch)
    (h69 : R6_9 Dat) (h619 : m.C619) (h620 : m.C620) (h623 : m.C623)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (hr3 : m.r ≠ 3) : calNOf (m.A ⊔ m.L) = {normalizer (m.L : Set G)} := by
  have hAL : m.A ⊔ m.L ≤ normalizer (m.L : Set G) :=
    sup_le ((m.A_le_R.trans (m.hZ.R_le_centralizer h69)).trans m.H_le_normalizer_L)
      Subgroup.le_normalizer
  have hne : normalizer (m.L : Set G) ≠ ⊤ := by
    intro h
    have hLn : m.L.Normal := Subgroup.normalizer_eq_top_iff.1 h
    haveI := Dat.standing.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal m.L with h1 | h1
    · have h2 := m.card_A_inf_L h620
      rw [h1, inf_bot_eq, Subgroup.card_bot] at h2
      have h3 : 1 < m.r ^ 2 := Nat.one_lt_pow two_ne_zero m.hr.one_lt
      omega
    · exact m.H_ne_top (top_le_iff.1 (h1 ▸ m.L_le_H))
  obtain ⟨N₀, hN₀, hLN₀⟩ := (eq_top_or_exists_le_coatom (normalizer (m.L : Set G))).resolve_left hne
  have hN₀mem : N₀ ∈ calNOf (m.A ⊔ m.L) := ⟨hN₀, hAL.trans hLN₀⟩
  have hN₀eq : N₀ = normalizer (m.L : Set G) :=
    le_antisymm (m.le_normalizer_L_of_mem_calNOf hK hSch h69 h619 h620 h623 hL1 hL3 hr3 hN₀mem)
      hLN₀
  ext N
  constructor
  · intro hN
    have h1 := m.le_normalizer_L_of_mem_calNOf hK hSch h69 h619 h620 h623 hL1 hL3 hr3 hN
    rcases eq_or_lt_of_le h1 with h | h
    · exact h
    · exact absurd (hN.1.2 _ h) hne
  · intro hN
    rw [Set.mem_singleton_iff] at hN
    rw [hN, ← hN₀eq]
    exact hN₀mem

end Mz614

section

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

theorem Mz614.c624_of_k332' (hK : UCK.K332') (hSch : UCK.KSch) (m : Mz614 Dat)
    (_h67 : R6_7 Dat) (h69 : R6_9 Dat)
    (h619 : m.C619) (h620 : m.C620) (h623 : m.C623) (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1) :
    m.C624 := fun hr3 => m.calNOf_eq_normalizer_L hK hSch h69 h619 h620 h623 hL1 hL3 hr3

end

end CFSG.LocalAnalysis.UniquenessCase.UC6G
