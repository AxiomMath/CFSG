module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.E22L2

open CFSG.GorensteinWalter

universe u

theorem e22ptr_pGammaL2PGLRange_eq_top (K : Type u) [CommRing K] [Subsingleton (K ≃+* K)] :
    pGammaL2PGLRange K = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  unfold pGammaL2PGLRange
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

theorem e22ptr_eq_psl_or_eq_pgl (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {A : Subgroup (PGammaL2 K)}
    (hPSL : pGammaL2PSLRange K ≤ A) (hPGL : A ≤ pGammaL2PGLRange K) :
    A = pGammaL2PSLRange K ∨ A = pGammaL2PGLRange K := by
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hPSL hPGL
  rw [pGammaL2_psl_range_relIndex_pgl_eq_two K hK] at hmul
  have hdvd : (pGammaL2PSLRange K).relIndex A ∣ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h) hPSL)
  · rw [h] at hmul
    exact Or.inr (le_antisymm hPGL (Subgroup.relIndex_eq_one.mp (by omega)))

theorem psl2_prime_transport {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hF : IsPSL 2 p 1 ↥(CFSG.generalizedFitting G)) :
    Nonempty (G ≃* CFSG.GorensteinWalter.PSL2 (ZMod p)) ∨
      Nonempty (G ≃* CFSG.GorensteinWalter.PGL2 (ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by simp⟩
  have hcard : 3 < Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  set L : Subgroup G := CFSG.generalizedFitting G
  have : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hF
  have hC : Subgroup.centralizer (L : Set G) = ⊥ := by
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
        (CFSG.GorensteinWalter.psl2_center_eq_bot (ZMod p))
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxL : x ∈ L := CFSG.centralizer_generalizedFitting_le G hx
    have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      exact fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [hZ, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  obtain ⟨ι, hι, hPSL, -⟩ :=
    CFSG.ABGDGroups.exists_embedding_of_normal_psl2 hodd hcard e hC
  have hPGL : ι.range ≤ pGammaL2PGLRange (ZMod p) :=
    le_top.trans_eq (e22ptr_pGammaL2PGLRange_eq_top (ZMod p)).symm
  have eι : G ≃* ι.range := MonoidHom.ofInjective hι
  rcases e22ptr_eq_psl_or_eq_pgl (ZMod p) hodd hPSL hPGL with h | h
  · exact Or.inl ⟨eι.trans ((MulEquiv.subgroupCongr h).trans (pGammaL2PSLRangeEquiv _).symm)⟩
  · exact Or.inr ⟨eι.trans ((MulEquiv.subgroupCongr h).trans (pGammaL2PGLRangeEquiv _).symm)⟩

end CFSG.Quasithin.E22L2
