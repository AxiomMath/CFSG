module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch11SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem map_oPrimeResidualOf_top (p : ℕ) (H : Subgroup G) :
    (oPrimeResidualOf p (⊤ : Subgroup ↥H)).map H.subtype = oPrimeResidualOf p H := by
  rw [oPrimeResidualOf, oPrimeResidualOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hk]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, k, by rw [← Subgroup.orderOf_coe]; exact hk⟩, rfl⟩

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_cComp_of_le (h : Hyp11 G T L I n) {H : Subgroup G} (hLT : L ⊔ T ≤ H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) : L ∈ cComp H := by
  obtain ⟨hne, hperf, -, hmin⟩ := cComp_of_isLocal h.fsu.maximal.1
  have hLH : L ≤ H := le_sup_left.trans hLT
  refine ⟨hne, hperf, ?_, fun K hKL hKne hKperf hKsub => ?_⟩
  · exact IsSubnormal.step hLH (Subgroup.normal_subgroupOf_of_le_normalizer hHL)
      (IsSubnormal.refl H)
  · exact hmin K hKL hKne hKperf
      (A3.subnormal_of_le_of_le hKsub (hKL.le.trans le_sup_left) hLT)

theorem pCoreOf_normalizer_L_ne_bot (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) :
    pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, hPM⟩ := (isMaxTwoLocal_M h331 h).1
  have hle : P ≤ pCoreOf 2 (Subgroup.normalizer (L : Set G)) := by
    rw [hPM]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
  intro hb
  rw [hb] at hle
  exact hP1 (le_bot_iff.mp hle)

theorem sqtkGroup_of_le_normalizer (h331 : Stmt3_3_1) (h : Hyp11 G T L I n) {H : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) : SQTKGroup ↥H := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  exact InternalSec.sqtkGroup_mono
    (InternalSec.sqtkGroup_of_localSQTK hloc (pCoreOf_normalizer_L_ne_bot h331 h)) hHL

omit [Finite G] in
theorem quotPCore_subgroupOf_equiv {H : Subgroup G} (hLH : L ≤ H) :
    Nonempty ((↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  have hmap : (CFSG.pCore 2 ↥(L.subgroupOf H)).map (e : ↥(L.subgroupOf H) →* ↥L) =
      CFSG.pCore 2 ↥L := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
    exact this
  exact ⟨QuotientGroup.congr _ _ e hmap⟩

theorem isQuasisimple_subgroupOf (h : Hyp11 G T L I n) {H : Subgroup G} (hLH : L ≤ H) :
    CFSG.IsQuasisimple (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) := by
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h.fsu.quasisimple

theorem pRank_subgroupOf_eq {H : Subgroup G} (hLH : L ≤ H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (L.subgroupOf H) =
      CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact p.Prime := ⟨hp⟩
  have e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt e
  have h2 := pRank_top_subtype (p := p) (L.subgroupOf H)
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    exact hp2 this
  have h3 := CFSG.SectionRank.pRank_quotient_eq (p := p) (CFSG.pCore 2 ↥L) hN
  rw [← h2, h1, h3]

end CFSG.Quasithin.Vol2.Ch11.SecA
