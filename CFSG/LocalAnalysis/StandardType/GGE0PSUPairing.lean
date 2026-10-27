module

public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric
public import CFSG.LocalAnalysis.StandardType.GGE0PSUNotDvd
public import CFSG.LocalAnalysis.StandardType.GGE0PSURigid
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType.ClassicalPosition
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (conjTr antidiag)


private theorem sub_three_le_twoLocalRank_of_PSU {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .PSU n (f + 1)).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ)
    (hpq : p ∣ 2 ^ (f + 1) + 1) :
    n - 3 ≤ LargeEvenTwoLocalRank p G := by
  have hc : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (f + 1)
      (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hc, ← pow_mul, mul_comm]⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hc n
  exact SURep.sub_three_le_twoLocalRankU hUF hctx.prime hctx.ne_two hpq hn4
    (SURep.ggFrameKer_ggFrameU hc ψ P hP (by omega)
      (fun h' => by have h1 : n = 3 := congrArg Prod.fst h'; omega)
      hctx.2.2.2.2.1.2)

private theorem pow_le_card_map_conj_bstar_of_PSU {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .PSU n (f + 1)).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ)
    {g : G} (hp : p.Prime) :
    ∀ k ≤ LargeEvenTwoLocalRank p G,
      p ^ k ≤ Nat.card ↥(Bs.map (MulAut.conj g⁻¹).toMonoidHom) := by
  intro k hk
  have hcard : Nat.card ↥(Bs.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  rw [hcard]
  exact (Nat.pow_le_pow_right hp.pos hk).trans (hB.symm.le.trans hBBs)

theorem ggE0Pairing_PSU {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .PSU n (f + 1)).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b g : G} (hg : g ∈ ggM p B x L D J)
    (hEC : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer {b})
    {s : GL (Fin n) (GaloisField 2 (2 * (f + 1)))}
    (hsJ : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) * antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n)
    (hs : IsGLLift (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      n).subtype ψ s b) :
    ∀ e ∈ D.map (MulAut.conj g⁻¹).toMonoidHom, ∀ t : GL (Fin n) (GaloisField 2 (2 * (f + 1))),
      IsGLLift (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
        n).subtype ψ t e → Commute t s := by
  have hc : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  have hker : ψ.ker ≤ Subgroup.center _ := hctx.2.2.2.2.1.2
  have hp := hctx.prime
  have hp2 := hctx.ne_two
  have hE₀G1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSU hctx hg
    (hctx.d_le_bstar.trans (ggBs_le_ggG1 hctx))
  have hcomm : ∀ e ∈ D.map (MulAut.conj g⁻¹).toMonoidHom, Commute b e := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hEC he)).symm
  by_cases hpq : p ∣ 2 ^ (f + 1) + 1
  · have hB₁G1 := map_conj_le_ggG1 ggSteinbergCorrectionAt_PSU hctx hg (ggBs_le_ggG1 hctx)
    have hle := pow_le_card_map_conj_bstar_of_PSU (g := g) hctx hp
    have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hctx.range_eq]
      exact s1.1
    obtain ⟨x', y', hE, hrig⟩ := ggE0_rigid_generators hctx hg
    have hlift : ∀ c ∈ Subgroup.closure ({x', y'} : Set G),
        ∃ t, IsGLLift (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2
          (f + 1)) n).subtype ψ t c := by
      intro c hc'
      rw [← hE] at hc'
      obtain ⟨t, -, ht⟩ := exists_isGLLift_PSU hc n (by omega) ψ hker
        (hE₀G1 hc').1 (hE₀G1 hc').2
      exact ⟨t, ht⟩
    intro e he t ht
    rw [hE] at he hcomm
    refine isGLLift_commute_of_mem_closure (fun h h' => isGLLift_unique_PSU hc n ψ hker h h')
      hlift (fun z hz t' ht' => ?_) e he t ht
    obtain ⟨hzB, L', hL', hcard⟩ := hrig z hz
    rw [← hctx.range_eq] at hL'
    exact (isGLLift_commute_of_rigid_PSU hc n hn4 ψ hker hC hp hp2 hpq
      (fun b' hb' => (hB₁G1 hb').2)
      (CFSG.Open.IsElemAbelian.map hctx.bstar.2.1 _) (hle 4 hctx.beta.2.2.2)
      (hle (n - 3) (sub_three_le_twoLocalRank_of_PSU hctx hpq)) hzB hL' hcard
      (hcomm z (Subgroup.subset_closure hz)) hs ht').symm
  · intro e he t ht
    obtain ⟨t₀, ht₀J, ht₀⟩ := exists_isGLLift_PSU hc n (by omega) ψ hker
      (hE₀G1 he).1 (hE₀G1 he).2
    have h₀ : Commute s t₀ := isGLLift_commute_of_not_dvd_PSU hc n ψ hker hp hpq
      ((CFSG.Open.IsElemAbelian.map hctx.d_elem _).2 e he) (hcomm e he) hsJ ht₀J hs ht₀
    exact commute_of_inv_mul_eq_scalar h₀.symm (isGLLift_unique_PSU hc n ψ hker ht ht₀)

end CFSG.StandardType
