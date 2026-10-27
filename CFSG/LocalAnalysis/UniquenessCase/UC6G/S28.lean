module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S29
public import CFSG.LocalAnalysis.UniquenessCase.UC6S28

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

section Transport

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

theorem moduleData_uc6 (Dat : Data G) :
    CFSG.Open.IsKGroup ↥Dat.M ∧ IsPGroup 2 (CFSG.pCore 2 ↥Dat.M) ∧
      centralizer ((CFSG.pCore 2 ↥Dat.M : Subgroup ↥Dat.M) : Set ↥Dat.M) ≤ CFSG.pCore 2 ↥Dat.M := by
  haveI := Dat.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMtop : Dat.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top Dat.standing.nonab Dat.maxLocal.1
  refine ⟨Dat.standing.kProper.isKGroup Dat.M hMtop, CFSG.LieType.BorelTits.pCore_isPGroup 2, ?_⟩
  intro x hx
  have h1 := Dat.standing.charTwo Dat.M Dat.maxLocal.1
  have hxG : (x : G) ∈ Dat.M ⊓ centralizer (pCoreOf 2 Dat.M : Set G) := by
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ centralizer (pCoreOf 2 Dat.M : Set G)
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have := mem_centralizer_iff.1 hx q hq
    exact congrArg Subtype.val this
  obtain ⟨q, hq, hqx⟩ := h1 hxG
  have : q = x := Subtype.ext hqx
  exact this ▸ hq

theorem card_fix_le_uc6 (Dat : Data G) {X : Subgroup G} (hXM : X ≤ Dat.M)
    (hfix : Nat.card ↥(pCoreOf 2 Dat.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2) :
    Nat.card ↥((CFSG.pCore 2 ↥Dat.M) ⊓
      centralizer ((X.subgroupOf Dat.M : Subgroup ↥Dat.M) : Set ↥Dat.M)) ≤ 2 := by
  have hle : ((CFSG.pCore 2 ↥Dat.M) ⊓
      centralizer ((X.subgroupOf Dat.M : Subgroup ↥Dat.M) : Set ↥Dat.M)).map Dat.M.subtype ≤
      pCoreOf 2 Dat.M ⊓ centralizer (X : Set G) := by
    rintro _ ⟨x, ⟨hxQ, hxC⟩, rfl⟩
    refine ⟨⟨x, hxQ, rfl⟩, ?_⟩
    show Dat.M.subtype x ∈ centralizer (X : Set G)
    rw [mem_centralizer_iff]
    intro h hh
    have := mem_centralizer_iff.1 hxC ⟨h, hXM hh⟩ hh
    exact congrArg Subtype.val this
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective Dat.M.subtype_injective] at this
  exact this.trans hfix

end Transport

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] def C627 : Prop := m.Z ≤ ⁅m.M, m.M⁆

theorem U_le_M : m.U ≤ m.M := m.U_le_K.trans m.K_le_M

theorem M_le_normalizer_U : m.M ≤ normalizer (m.U : Set G) := fun _ hg =>
  mem_normalizer_of_forward_uc6 (m.conj_U_le hg)

theorem six28b (hK : UCK.K47) (h69 : R6_9 Dat) (h626 : m.C626)
    (h627 : m.C627) : m.C628b := by
  intro p hp hdvdU'
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hpr : p.Prime := (Dat.sig_prime _ hp).1
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp2 : p ≠ 2 := (Dat.sig_prime p hp).2
  have hpne : p ≠ m.r := fun h => m.hrσ (h ▸ hp)
  have hdvdU : p ∣ Nat.card m.U := by rw [m.card_U]; exact hdvdU'
  have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z)
  have hZU : m.Z ≤ normalizer (m.U : Set G) := fun z hz => m.K_le_normalizer_U (m.Z_le_K hz)
  have hcopU : ¬ m.r ∣ Nat.card m.U := fun h => m.hr.ne_one (m.coprime_card_U.eq_one_of_dvd h)
  obtain ⟨P, hPsyl, hZP⟩ := exists_invariant_sylow_uc6 (r := m.r) p hZU hZp hcopU
  have hPU : P ≤ m.U := hPsyl.le
  have hPM : P ≤ m.M := hPU.trans m.U_le_M
  have hPp : IsPGroup p P := hPsyl.isPGroup
  have hPbot : P ≠ ⊥ := by
    intro h
    have hc := hPsyl.card_eq
    rw [h, Subgroup.card_bot] at hc
    have hk : (Nat.card m.U).factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hpr (Nat.card_pos.ne') hdvdU).ne'
    rcases pow_eq_one_iff.1 hc.symm with h1 | h1
    · exact hpr.ne_one h1
    · exact hk h1
  have hCP : ∀ x ∈ P, (∀ z ∈ m.Z, z * x = x * z) → x = 1 := by
    intro x hxP hxc
    by_contra hx1
    have hxM : x ∈ m.M := hPM hxP
    have hxcen : x ∈ centralizer (m.Z : Set G) := mem_centralizer_iff.2 hxc
    have hxN : x ∈ m.M ⊓ normalizer (m.Z : Set G) :=
      ⟨hxM, Subgroup.centralizer_le_normalizer _ hxcen⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hPp ⟨x, hxP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hk]; rfl))
    have h1 : p ∣ orderOf x := by rw [hk]; exact dvd_pow_self p hk0
    have h2 : orderOf x ∣ Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : ↥(m.M ⊓ normalizer (m.Z : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    exact h626 p hp (h1.trans h2)
  set Q : Subgroup G := omegaCenter p P with hQ
  have hQP : Q ≤ P := omegaCenter_le p P
  have hQM : Q ≤ m.M := hQP.trans hPM
  have hQab : CFSG.Open.IsElemAbelian p Q := isElemAbelian_omegaCenter p P
  have hQne : Q ≠ ⊥ := omegaCenter_ne_bot hPp hPbot
  have hQZ : m.Z ≤ normalizer (Q : Set G) := fun z hz =>
    normalizer_le_normalizer_omegaCenter p P (hZP hz)
  have hQfix : ∀ q ∈ Q, (∀ z ∈ m.Z, z * q = q * z) → q = 1 := fun q hq hc => hCP q (hQP hq) hc
  obtain ⟨z₁, hz₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 m.Z_ne_bot
  have hZgen : m.Z = Subgroup.zpowers (z₁ : G) := by
    have hle : Subgroup.zpowers (z₁ : G) ≤ m.Z := (Subgroup.zpowers_le).2 z₁.2
    have hdvd : orderOf (z₁ : G) ∣ m.r := by
      rw [← m.card_Z]
      have h := orderOf_dvd_natCard z₁
      rwa [← Subgroup.orderOf_coe] at h
    have hne : orderOf (z₁ : G) ≠ 1 := fun h => hz₁ (Subtype.ext (orderOf_eq_one_iff.1 h))
    have hord : orderOf (z₁ : G) = m.r := ((Nat.dvd_prime m.hr).1 hdvd).resolve_left hne
    exact (Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, hord, m.card_Z])).symm
  have hcomm : ⁅m.Z, Q⁆ = Q :=
    commutator_eq_of_fixedPointFree_uc6 hZgen hQab.1 hQZ hQfix
  obtain ⟨hMg, hQ₀, hchar⟩ := moduleData_uc6 Dat
  haveI hQ₀n : (CFSG.pCore 2 ↥m.M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ' := isElemAbelian_subgroupOf_uc6 hQM hQab
  by_cases hQc : IsCyclic ↥Q
  ·
    haveI hU'n : (m.U.subgroupOf m.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer m.U_le_M).2 m.M_le_normalizer_U
    have htop : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
      rw [← MonoidHom.range_eq_map]
      exact Subgroup.range_subtype _
    have hFr : m.M = m.U ⊔ (m.M ⊓ normalizer (P : Set G)) :=
      frattini_of_isSylowOf m.U_le_M m.M_le_normalizer_U hPsyl
    have hNmap : (normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M)).map
        m.M.subtype = m.M ⊓ normalizer (P : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, (mem_normalizer_subgroupOf_iff_uc6 hPM).1 hy⟩
      · rintro ⟨hxM, hxN⟩
        exact ⟨⟨x, hxM⟩, (mem_normalizer_subgroupOf_iff_uc6 hPM).2 hxN, rfl⟩
    have hFr' : (⊤ : Subgroup ↥m.M) = m.U.subgroupOf m.M ⊔
        normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := by
      apply Subgroup.map_injective m.M.subtype_injective
      rw [htop, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le m.U_le_M, hNmap]
      exact hFr
    have hQN' : normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) ≤
        normalizer ((Q.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := by
      intro y hy
      exact (mem_normalizer_subgroupOf_iff_uc6 hQM).2
        (normalizer_le_normalizer_omegaCenter p P
          ((mem_normalizer_subgroupOf_iff_uc6 hPM).1 hy))
    have hQc' : IsCyclic ↥(Q.subgroupOf m.M) := by
      haveI := hQc
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQM).symm.toMonoidHom
        (MulEquiv.surjective _)
    have hZN' : m.Z.subgroupOf m.M ≤
        normalizer ((P.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := fun z hz =>
      (mem_normalizer_subgroupOf_iff_uc6 hPM).2 (hZP hz)
    have hZc' : m.Z.subgroupOf m.M ≤ ⁅(⊤ : Subgroup ↥m.M), ⊤⁆ := by
      intro z hz
      have hz' : (z : G) ∈ ⁅m.M, m.M⁆ := h627 hz
      have hmap : Subgroup.map m.M.subtype ⁅(⊤ : Subgroup ↥m.M), ⊤⁆ = ⁅m.M, m.M⁆ := by
        rw [Subgroup.map_commutator, htop]
      rw [← hmap] at hz'
      obtain ⟨w, hw, hwz⟩ := hz'
      have : w = z := Subtype.ext hwz
      exact this ▸ hw
    have hZr : ∀ z ∈ m.Z.subgroupOf m.M, z ^ m.r = 1 := by
      intro z hz
      have h1 : (⟨(z : G), hz⟩ : ↥m.Z) ^ Nat.card m.Z = 1 := pow_card_eq_one'
      rw [m.card_Z] at h1
      apply Subtype.ext
      simpa using congrArg Subtype.val h1
    have hcop' : Nat.Coprime m.r (Nat.card (m.U.subgroupOf m.M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.U_le_M).toEquiv]
      exact m.coprime_card_U
    have hcen := cyclic_case_uc6 (m.U.subgroupOf m.M) (P.subgroupOf m.M) (Q.subgroupOf m.M)
      (m.Z.subgroupOf m.M) hFr' hQN' hQc' hZN' hZc' m.hr.one_lt hZr hcop'
    apply hQne
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    refine hQfix q hq (fun z hz => ?_)
    have := hcen ⟨z, m.Z_le_M hz⟩ hz ⟨q, hQM hq⟩ hq
    exact congrArg Subtype.val this
  ·
    have hsub : Dat.sig ⊆ Dat.sig1 :=
      m.hσ1
    have hEM : m.E ≤ m.M := fun x hx => m.R_le_M (m.E_le_R hx)
    have hfixG : Nat.card ↥(pCoreOf 2 m.M ⊓ centralizer (m.Z : Set G) : Subgroup G) ≤ 2 :=
      (h69 hsub m.r m.hr m.d.odd m.E hEM m.d.E_el m.d.E_card m.d.E_gamma m.r m.Z m.hr
        m.Z_le_M m.card_Z (m.hZ.E_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
        m.hZ.not_normalizer_le m.Z m.Z_le_M hZp le_rfl).1.1
    have hfix' := card_fix_le_uc6 Dat m.Z_le_M hfixG
    have hZ'card : Nat.card (m.Z.subgroupOf m.M) = m.r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_M).toEquiv]
      exact m.card_Z
    have hQ'p : IsPGroup p (Q.subgroupOf m.M) := (hPp.to_le hQP).comap_subtype
    have hDQ' : m.Z.subgroupOf m.M ≤
        normalizer ((Q.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) := fun z hz =>
      (mem_normalizer_subgroupOf_iff_uc6 hQM).2 (hQZ hz)
    have hcomm' : ⁅m.Z.subgroupOf m.M, Q.subgroupOf m.M⁆ = Q.subgroupOf m.M := by
      apply Subgroup.map_injective m.M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le m.Z_le_M,
        Subgroup.map_subgroupOf_eq_of_le hQM]
      exact hcomm
    have hcyc := k47_transport_two_uc6 hK hMg (CFSG.pCore 2 ↥m.M) hQ₀ hchar hpr m.hr hp2
      m.d.odd hpne (m.Z.subgroupOf m.M) hZ'card hfix' (Q.subgroupOf m.M) hQ'p hQ'.1 hDQ' hcomm'
    exact hQc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQM).toMonoidHom
      (MulEquiv.surjective _))

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
