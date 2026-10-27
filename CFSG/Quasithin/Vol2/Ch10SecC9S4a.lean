module

public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch10SecC10
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.C2Nine

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isSylowTwoOf_top (hyp : Hyp10 G T L I) : IsSylowTwoOf T ⊤ :=
  ⟨le_top, hyp.fsu.sylow.1, fun h => hyp.fsu.sylow.2
    (h.trans (Subgroup.relIndex_dvd_index_of_le le_top))⟩

theorem pCoreOf_fsuM_ne_bot (hyp : Hyp10 G T L I) (hV : fsuVM T L I ≠ ⊥) :
    pCoreOf 2 (fsuM T L) ≠ ⊥ := fun h => hV (le_bot_iff.mp (h ▸
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (SecA.fsuVM_le_fsuM hyp.fsu)
    (SecA.fsuM_le_normalizer_fsuVM T L I) (SecA.isPGroup_fsuVM hyp)))

theorem charTwo_fsuM (hyp : Hyp10 G T L I) (hV : fsuVM T L I ≠ ⊥) : CharTwo (fsuM T L) := by
  have := hyp.fsu.simple
  have hev := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).2.1
  exact charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hev (isSylowTwoOf_top hyp) (SecA.le_fsuM T L)
    (pCoreOf_fsuM_ne_bot hyp hV)

theorem charTwo_centralizer {M : Subgroup G} (hM : CharTwo M) {x : G} (hxM : x ∈ M) (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) : CharTwo (M ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx1, pow_one])
  have hCz : Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine charTwo_of_centralizer_sup_le_of_le_normalizer hM (Subgroup.zpowers_le.mpr hxM) hP ?_ ?_
  · rw [hCz]
    refine sup_le (Subgroup.zpowers_le.mpr ⟨hxM, ?_⟩) le_rfl
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · refine inf_le_inf_left _ ?_
    rw [← hCz]
    exact Subgroup.centralizer_le_normalizer _

theorem oddCoreIn_eq_bot_of_le {X J : Subgroup G} (hX : CharTwo X) (hJX : oddCoreIn J ≤ X)
    (hXn : X ≤ Subgroup.normalizer (oddCoreIn J : Set G)) : oddCoreIn J = ⊥ := by
  have hQ : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hYC : oddCoreIn J ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hyX := hJX hy
    have hqX : q ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hq
    have h1 : q * y⁻¹ * q⁻¹ ∈ oddCoreIn J :=
      (Subgroup.mem_normalizer_iff.mp (hXn hqX) y⁻¹).mp ((oddCoreIn J).inv_mem hy)
    have h2 : y * q * y⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hyX) q).mp hq
    have h3 : y * q * y⁻¹ * q⁻¹ ∈ oddCoreIn J ⊓ pCoreOf 2 X := by
      refine ⟨?_, (pCoreOf 2 X).mul_mem h2 ((pCoreOf 2 X).inv_mem hq)⟩
      have := (oddCoreIn J).mul_mem hy h1
      simpa [mul_assoc] using this
    rw [oddCoreIn_inf_eq_bot hQ J] at h3
    have h4 : y * q * y⁻¹ * q⁻¹ = 1 := h3
    calc q * y = y * q * y⁻¹ * q⁻¹ * (q * y) := by rw [h4, one_mul]
      _ = y * q := by group
  have hYQ : oddCoreIn J ≤ pCoreOf 2 X := fun y hy => hX ⟨hJX hy, hYC hy⟩
  rw [eq_bot_iff, ← oddCoreIn_inf_eq_bot hQ J]
  exact le_inf le_rfl hYQ

theorem conj_mem_oddCoreIn {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    {y : G} (hy : y ∈ oddCoreIn J) : g * y * g⁻¹ ∈ oddCoreIn J := by
  set K := B6.conjSub g (oddCoreIn J) with hK
  have hKJ : K ≤ J := fun z hz => by
    rw [hK, B6.mem_conjSub] at hz
    have := (Subgroup.mem_normalizer_iff.mp hg _).mp (oddCoreIn_le_self J hz)
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at this
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := by
    intro j hj
    have hj' : g⁻¹ * j * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) j).mp hj
      rwa [inv_inv] at this
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hK, B6.mem_conjSub, B6.mem_conjSub]
    have h1 := Subgroup.mem_normalizer_iff.mp (C2Nine.le_normalizer_oddCoreIn J hj') (g⁻¹ * z * g)
    rw [show g⁻¹ * j * g * (g⁻¹ * z * g) * (g⁻¹ * j * g)⁻¹ = g⁻¹ * (j * z * j⁻¹) * g by group]
      at h1
    exact h1
  have hodd : Odd (Nat.card K) := by
    rw [hK, B6.card_conjSub]
    exact C2Nine.odd_card_oddCoreIn J
  have hnormal : (K.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK
  have hodd' : Odd (Nat.card (K.subgroupOf J)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv]
  have hle : K.subgroupOf J ≤ fusionOddCore J := le_sSup ⟨hnormal, hodd'⟩
  have hyK : g * y * g⁻¹ ∈ K := by
    rw [hK, B6.mem_conjSub, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  exact ⟨⟨_, hKJ hyK⟩, hle hyK, rfl⟩

theorem normalizer_le_normalizer_oddCoreIn' (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (oddCoreIn J : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_oddCoreIn hg, fun h => ?_⟩
  have := conj_mem_oddCoreIn ((Subgroup.normalizer _).inv_mem hg) h
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem oddCoreIn_eq_bot (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1026 : Stmt10_2_6) {t : G} (ht : t ∈ T) {w : G}
    (hwW : w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hwV1 : w ∉ fsuUL T L I) {J : Subgroup G}
    (hJ : J ∈ cComp (Subgroup.centralizer ({w} : Set G))) (hLJ : L ≤ J)
    (hJn : (J.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal) : oddCoreIn J = ⊥ := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hwV : w ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hwW
  have hw1 : w ≠ 1 := fun h => hwV1 (h ▸ Subgroup.one_mem _)
  have hw2 : w ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 w hwV
  have hH := pCoreOf_centralizer_ne_bot hw1 hw2
  have hSQ := InternalSec.sqtkGroup_of_localSQTK hK hH
  have hJH : J ≤ Subgroup.centralizer ({w} : Set G) := le_of_mem_cComp hJ
  have hVL : fsuVM T L I ≤ Subgroup.normalizer (L : Set G) :=
    (fsuVM_le_Q hyp).trans (Q_le_T1 h37 h38 hyp h1011) |>.trans inf_le_right
  have hV1L : fsuUL T L I ≤ L := by
    rw [fsuUL, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hVL
  have hV1el : IsElemAbelian 2 (fsuUL T L I) :=
    B2F.isElemAbelian_mono (commutator_le_left_of_le_normalizer hLN) (SecA.isElemAbelian_fsuVM hyp)
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p J) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := sqt_iff.mp hSQ.1 p hp hp2
    rw [pRank_top_subtype] at h1
    exact (CFSG.SectionRank.pRank_mono hp.one_lt
      ((CFSG.LieType.BorelTits.pCoreOf_le p J).trans hJH)).trans h1
  have hVc : fsuUL T L I ≤ Subgroup.centralizer (fusionOddCoreOf J : Set G) :=
    a126_one hLJ (opResidual_eq_of_perfect (commutator_self_of_local hyp.fsu.faithful.1))
      (hV1L.trans hLJ) (isPGroup_two_of_isElemAbelian hV1el) (commutator_fsuUL_eq hyp) hrank
      (frattiniIn_eq_bot_of_isElemAbelian hV1el)
  have hOM : oddCoreIn J ≤ fsuM T L := by
    intro y hy
    refine (h1026 G T L I hyp).2.1 L (Or.inl rfl) (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hVc hv)) y hy).symm
  have hVne : fsuVM T L I ≠ ⊥ := fun h => hw1 (by rw [h] at hwV; exact Subgroup.mem_bot.mp hwV)
  have hwM : w ∈ fsuM T L := SecA.fsuVM_le_fsuM hyp.fsu hwV
  have hC := charTwo_centralizer (charTwo_fsuM hyp hVne) hwM hw1 hw2
  refine oddCoreIn_eq_bot_of_le hC (le_inf hOM ((oddCoreIn_le_self J).trans hJH)) ?_
  intro x hx
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp hJn hx.2
  exact normalizer_le_normalizer_oddCoreIn' J hxJ

end CFSG.Quasithin.Vol2.Ch10.SecC
