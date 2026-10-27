module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_card_barPreimage (M : Subgroup G) (D : Subgroup (Bar2 M)) :
    Nat.card ↥(barPreimage M D) = Nat.card ↥(pCoreOf 2 M) * Nat.card ↥D := by
  have h1 : Nat.card ↥(barPreimage M D) = Nat.card ↥(D.comap (uc22p21cPi M)) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : Nat.card ↥(pCoreOf 2 M) = Nat.card ↥(CFSG.pCore 2 ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have hidx : (D.comap (uc22p21cPi M)).index = D.index :=
    Subgroup.index_comap_of_surjective D (uc22p21c_pi_surjective M)
  have hM := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥M)
  have hD := Subgroup.card_mul_index D
  have hC := Subgroup.card_mul_index (D.comap (uc22p21cPi M))
  have hpos : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1, h2]
  rw [hidx] at hC
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card ↥(D.comap (uc22p21cPi M)) * D.index = Nat.card ↥M := hC
    _ = Nat.card (Bar2 M) * Nat.card ↥(CFSG.pCore 2 ↥M) := hM
    _ = (Nat.card ↥D * D.index) * Nat.card ↥(CFSG.pCore 2 ↥M) := by rw [hD]
    _ = Nat.card ↥(CFSG.pCore 2 ↥M) * Nat.card ↥D * D.index := by ring

theorem uc22p22u_exists_lift {M : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D : Subgroup (Bar2 M)} (hD : IsPGroup r ↥D) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r P (barPreimage M D) ∧ barImage M P = D ∧
      P ⊓ pCoreOf 2 M = ⊥ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow r ↥(barPreimage M D)))
  set Y : Subgroup G := barPreimage M D with hY
  set P : Subgroup G := (S : Subgroup ↥Y).map Y.subtype with hPdef
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf r P Y := ⟨S, rfl⟩
  have hYM : Y ≤ M := uc22p21c_barPreimage_le M D
  refine ⟨P, hPsyl, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
      obtain ⟨_, hmD⟩ := uc22p21c_mem_barPreimage.1 (hPsyl.le hm)
      exact hmD
    · let f : ↥Y →* ↥D := ((uc22p21cPi M).comp (Subgroup.inclusion hYM)).codRestrict D fun y => by
        obtain ⟨_, hyD⟩ := uc22p21c_mem_barPreimage.1 y.2
        exact hyD
      have hf : Function.Surjective f := by
        rintro ⟨d, hd⟩
        obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M d
        exact ⟨⟨(m : G), uc22p21c_mem_barPreimage.2 ⟨m.2, hd⟩⟩, rfl⟩
      have htop : ((S.mapSurjective hf : Sylow r ↥D) : Subgroup ↥D) = ⊤ := by
        symm
        exact (S.mapSurjective hf).is_maximal' (hD.of_equiv Subgroup.topEquiv.symm) le_top
      intro q hq
      have h1 : (⟨q, hq⟩ : ↥D) ∈ ((S.mapSurjective hf : Sylow r ↥D) : Subgroup ↥D) := by
        rw [htop]
        trivial
      rw [Sylow.coe_mapSurjective] at h1
      obtain ⟨s, hs, hsq⟩ := h1
      exact uc22p21c_mem_barImage.2 ⟨Subgroup.inclusion hYM s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsq⟩
  ·
    exact disjoint_iff.1 (IsPGroup.disjoint_of_ne r 2 hr2 P (pCoreOf 2 M) hPsyl.isPGroup
      (uc22p21c_isPGroup_pCoreOf M))

theorem uc22p22u_lift_props {M P : Subgroup G} {D : Subgroup (Bar2 M)} {r : ℕ} (hbar : barImage M P = D)
    (hP : P ⊓ pCoreOf 2 M = ⊥) (hPM : P ≤ M) :
    ((∀ x ∈ D, x ^ r = 1) → ∀ x ∈ P, x ^ r = 1) ∧ (⁅⁅D, D⁆, D⁆ = ⊥ → ⁅⁅P, P⁆, P⁆ = ⊥) ∧
      (¬ IsCyclic ↥D → ¬ IsCyclic ↥P) := by
  refine ⟨fun hexp x hx => ?_, fun hcl => ?_, fun hnc hc => hnc ?_⟩
  ·
    have hxM : x ∈ M := hPM hx
    have h1 : uc22p21cPi M ⟨x, hxM⟩ ∈ D := hbar ▸ uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩
    have h2 : uc22p21cPi M (⟨x, hxM⟩ ^ r) = 1 := by
      rw [map_pow]
      exact hexp _ h1
    have h3 : (⟨x, hxM⟩ ^ r : ↥M) ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h2
    have h5 : x ^ r ∈ P ⊓ pCoreOf 2 M := ⟨P.pow_mem hx r, ⟨_, h3, rfl⟩⟩
    rw [hP] at h5
    exact Subgroup.mem_bot.1 h5
  ·
    have hPmap : (P.subgroupOf M).map M.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPM]
    have hC1 : (⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆).map (uc22p21cPi M) = ⁅⁅D, D⁆, D⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
      exact congrArg (fun E : Subgroup (Bar2 M) => ⁅⁅E, E⁆, E⁆) hbar
    have hC2 : (⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆).map M.subtype = ⁅⁅P, P⁆, P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hPmap]
    have hCP : ⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆ ≤ P.subgroupOf M :=
      (Subgroup.commutator_mono (Subgroup.commutator_le_self _) le_rfl).trans
        (Subgroup.commutator_le_self _)
    have hCker : ⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆ ≤ CFSG.pCore 2 ↥M := by
      have h := (Subgroup.map_eq_bot_iff _).1 (hC1.trans hcl)
      rwa [QuotientGroup.ker_mk'] at h
    have hle1 : (⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆).map M.subtype ≤ P := by
      have h := Subgroup.map_mono (f := M.subtype) hCP
      rwa [hPmap] at h
    have hle2 : (⁅⁅P.subgroupOf M, P.subgroupOf M⁆, P.subgroupOf M⁆).map M.subtype ≤ pCoreOf 2 M :=
      Subgroup.map_mono hCker
    have h3 := le_inf hle1 hle2
    rw [hP] at h3
    rw [← hC2]
    exact le_bot_iff.1 h3
  ·
    let g : ↥P →* ↥D := ((uc22p21cPi M).comp (Subgroup.inclusion hPM)).codRestrict D fun a => by
      rw [← hbar]
      exact uc22p21c_mem_barImage.2 ⟨Subgroup.inclusion hPM a, a.2, rfl⟩
    have hg : Function.Surjective g := by
      rintro ⟨q, hq⟩
      rw [← hbar] at hq
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
      exact ⟨⟨(m : G), hm⟩, rfl⟩
    exact isCyclic_of_surjective g hg

theorem uc22p22u_pRank_le_normalizer_sylow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {M Y P : Subgroup G}
    (hYM : Y ≤ M) (hYn : M ≤ normalizer (Y : Set G)) (hP : CFSG.ABGLocalTools.IsSylowOf r P Y)
    (hpY : ¬ p ∣ Nat.card ↥Y) : CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M ⊓ normalizer (P : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hFr := uc22p22t_frattini_sup hYM hYn hP
  set N : Subgroup G := M ⊓ normalizer (P : Set G) with hN
  have hNM : N ≤ M := inf_le_left
  have hMeq : Y ⊔ N = M := le_antisymm (sup_le hYM hNM) hFr
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf p N
  have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' (hNM.trans hYn)
  rw [sup_comm, hMeq] at hprod
  have hY0 : (Nat.card ↥Y).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpY
  have hI0 : (Nat.card ↥(N ⊓ Y)).factorization p = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd fun hd => hpY (hd.trans ?_)
    exact Subgroup.card_dvd_of_le inf_le_right
  have hfac := congrArg (fun n => n.factorization p) hprod
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
  simp only [Finsupp.add_apply, hY0, hI0, add_zero] at hfac
  have hTM : CFSG.ABGLocalTools.IsSylowOf p T M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hT.le.trans hNM) ?_
    rw [hT.card_eq, hfac]
  exact (uc22p22q_pRank_le_sylow hTM).trans (CFSG.SectionRank.pRank_mono hp.one_lt hT.le)

end CFSG.LocalAnalysis.UniquenessCase.UC22
