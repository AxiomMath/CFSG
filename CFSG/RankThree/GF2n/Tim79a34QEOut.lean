module

public import CFSG.RankThree.GF2n.Tim79a34GammaSteps
public import CFSG.Holt.H78.Schur
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem xOf_commutator_eq_top {G : Type} [Group G] [Finite G]
    {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    {n : ℕ} (hn : 3 ≤ n) (e : ↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H) :
    ⁅xOf V H, xOf V H⁆ = xOf V H := by
  have hVH : V ≤ H := hH.setup.mc.toMinCex.V_le_H
  have hSpPerf : Group.IsPerfect ↥(StatedSp n (GaloisField 2 1)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n _
      (Or.inr (Or.inr ⟨by rw [GaloisField.card 2 1 one_ne_zero, pow_one], hn⟩))
  have hXbarZPerf : Group.IsPerfect (XbarZ V H) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hXbarPerf : Group.IsPerfect (Xbar V H) :=
    CFSG.Holt.H78.isPerfect_of_ker_le_commutator (projZ V H)
      (QuotientGroup.mk'_surjective _) (by
        simpa [CentreClause, projZ, QuotientGroup.ker_mk'] using hH.centre)
  have hWcomm : wOf V H ≤ ⁅xOf V H, xOf V H⁆ := by
    rw [← hH.setup.mc.toMinCex.commutator_wOf_xOf]
    exact Subgroup.commutator_mono (wOf_le_xOf V H) le_rfl
  have hker : (xToXbar hVH).ker ≤ commutator ↥(xOf V H) := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzW : (z : G) ∈ wOf V H := (cxw_xToXbar_eq_one hVH z).mp hz
    have hzmap : (z : G) ∈ (commutator ↥(xOf V H)).map (xOf V H).subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hWcomm hzW
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzmap
    rwa [show c = z from Subtype.ext hcz] at hc
  have hperfX : Group.IsPerfect ↥(xOf V H) :=
    CFSG.Holt.H78.isPerfect_of_ker_le_commutator (xToXbar hVH)
      (xToXbar_surjective hVH) hker
  rw [← Subgroup.map_subtype_commutator (xOf V H), hperfX.commutator_eq_top,
    Subgroup.map_top, Subgroup.range_subtype]

theorem xOf_le_pResidual {G : Type} [Group G] [Finite G]
    {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    {n : ℕ} (hn : 3 ≤ n) (e : ↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H) :
    xOf V H ≤ pResidual 2 G := by
  have hperf : ⁅xOf V H, xOf V H⁆ = xOf V H := xOf_commutator_eq_top hH hn e
  haveI : Group.IsPerfect ↥(xOf V H) := Subgroup.isPerfect_iff.mpr hperf
  set G₀ : Subgroup G := pResidual 2 G with hG₀
  haveI : G₀.Normal := CFSG.Quasithin.G6.pResidual_normal_aux 2
  have hquot2 : IsPGroup 2 (G ⧸ G₀) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := CFSG.Quasithin.G6.exists_pow_mem_pResidual 2 x
    exact ⟨k, by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  intro x hx
  let π : G →* G ⧸ G₀ := QuotientGroup.mk' G₀
  have hrange : (xOf V H).map π = (π.comp (xOf V H).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hperfImg : Group.IsPerfect ↥((xOf V H).map π) := by
    rw [hrange]
    exact Group.IsPerfect.range (f := π.comp (xOf V H).subtype)
  have hTop : IsPGroup 2 (⊤ : Subgroup (G ⧸ G₀)) := hquot2.of_equiv Subgroup.topEquiv.symm
  have h2Img : IsPGroup 2 ((xOf V H).map π) :=
    IsPGroup.to_le (G := G ⧸ G₀) (H := (xOf V H).map π) (K := ⊤) hTop le_top
  have hbot : (xOf V H).map π = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥((xOf V H).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect ↥((xOf V H).map π) := hperfImg
    exact (Group.IsPerfect.not_isNilpotent ↥((xOf V H).map π)) h2Img.isNilpotent
  have hxmem : π x ∈ (xOf V H).map π := Subgroup.mem_map_of_mem π hx
  rw [hbot, Subgroup.mem_bot] at hxmem
  exact (QuotientGroup.eq_one_iff x).mp hxmem

theorem P_le_pResidual {G : Type} [Group G] [Finite G]
    {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    P ≤ pResidual 2 G := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hn
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  obtain ⟨n', Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hZ
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hNat : NatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨-, -, hQX, -, -⟩ :=
    lemma12Statement_holds G M V Q P H hH hZ Φ ψ hNat a T ha hT hTV
  intro p hp
  have hpQX : p ∈ Q ⊓ xOf V H := by
    rw [hQX]
    exact hp
  exact xOf_le_pResidual hH hn3 e (Subgroup.mem_inf.mp hpQX).2

theorem inf_pResidual_eq_P {G : Type} [Group G] [Finite G]
    {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H))
    (hrel : P.relIndex Q = 2)
    (hOut : ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) :
    Q ⊓ pResidual 2 G = P := by
  have hPG : P ≤ pResidual 2 G := P_le_pResidual hH hZ hn
  have hQnot : ¬ Q ≤ pResidual 2 G := by
    intro hQle
    obtain ⟨N, hN, hq, hQN⟩ := hOut
    haveI := hN
    have hG0leN : pResidual 2 G ≤ N := by
      refine pResidual_le (fun x => ?_)
      obtain ⟨k, hk⟩ := hq (QuotientGroup.mk' N x)
      exact ⟨k, (QuotientGroup.eq_one_iff (x ^ 2 ^ k)).mp (by
        rw [QuotientGroup.mk_pow]
        exact hk)⟩
    exact hQN (hQle.trans hG0leN)
  have hPG' : P ≤ Q ⊓ pResidual 2 G := le_inf hH.setup.mc.toMinCex.P_le_Q hPG
  have hDne : Q ⊓ pResidual 2 G ≠ Q := by
    intro h
    exact hQnot (by rw [← h]; exact inf_le_right)
  have hrelD : (Q ⊓ pResidual 2 G).relIndex Q = 2 := by
    have hdvd : (Q ⊓ pResidual 2 G).relIndex Q ∣ P.relIndex Q :=
      Subgroup.relIndex_dvd_of_le_left (L := Q) hPG'
    rw [hrel] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h1)) hDne
    · exact h2
  have hPrelD : P.relIndex (Q ⊓ pResidual 2 G) = 1 := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := P) (K := Q ⊓ pResidual 2 G) (L := Q)
      hPG' (inf_le_left : Q ⊓ pResidual 2 G ≤ Q)
    rw [hrelD, hrel] at hmul
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hPrelD) hPG'

end CFSG.RankThree.GF2n.Tim79a
