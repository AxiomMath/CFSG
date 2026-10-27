module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

theorem outPNice_PSL2_field {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] (hKcard : Nat.card K = ℓ ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) : OutPNice p (PSL2 K) := by
  classical
  have hinj := pGammaL2ToMulAutPSL2_injective K hK hcard
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  let Ψe : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hcard) ⟨hinj, hsurj⟩
  have : Finite (PGammaL2 K) := Finite.of_equiv (MulAut (PSL2 K)) Ψe.symm.toEquiv
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let N : Subgroup (PGammaL2 K) := (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range
  have hcyc : IsCyclic (PGammaL2 K ⧸ N) := pGammaL2_quotient_pgl_isCyclic K hK
  let Θ : MulAut (PSL2 K) →* PGammaL2 K ⧸ N :=
    (QuotientGroup.mk' N).comp Ψe.symm.toMonoidHom
  have hΨinl : ∀ g : PGL2 K, Ψe (SemidirectProduct.inl g) = pgl2InnerAutPSL2 K hK hcard g :=
    fun g => pGammaL2ToMulAutPSL2_inl K hK hcard g
  have hker : ∀ δ ∈ Θ.ker, ∃ g : PGL2 K, δ = pgl2InnerAutPSL2 K hK hcard g := by
    intro δ hδ
    have h1 : Ψe.symm δ ∈ N := (QuotientGroup.eq_one_iff _).mp hδ
    obtain ⟨g, hg⟩ := h1
    refine ⟨g, ?_⟩
    rw [← hΨinl, hg, MulEquiv.apply_symm_apply]
  refine outPNice_of_hom Θ (fun x y => IsMulCommutative.is_comm.comm x y) ?_ ?_ (pChain_of_isCyclic hp)
  · rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    have : (MulAut.conj y : MulAut (PSL2 K)) =
        Ψe (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) := by
      rw [hΨinl, pgl2InnerAutPSL2_toPGL]
    change (QuotientGroup.mk' N) (Ψe.symm (MulAut.conj y)) = 1
    rw [this, MulEquiv.symm_apply_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  · intro δ hδ k hk
    obtain ⟨g, rfl⟩ := hker δ hδ
    obtain ⟨y, hy⟩ := hk
    have hHidx : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index ≤
        3 := by
      rw [pgl2_psl2Range_index_eq_two K hK]
      norm_num
    have hy' : pgl2InnerAutPSL2 K hK hcard (g ^ (p ^ k)) =
        pgl2InnerAutPSL2 K hK hcard (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      rw [pgl2InnerAutPSL2_toPGL, map_pow]
      exact hy.symm
    have hgp : g ^ (p ^ k) ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
      ⟨y, (pgl2InnerAutPSL2_injective K hK hcard hy').symm⟩
    have hgH := mem_of_pow_mem_of_index_le_three _ hHidx hp hp3 hgp
    obtain ⟨y', hy'⟩ := hgH
    exact ⟨y', by rw [← hy', pgl2InnerAutPSL2_toPGL]⟩

theorem outPNice_PSL_two_odd {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {X : Type} [Group X]
    {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2) (h : StatedClassicalModel X .PSL 2 ℓ f) : OutPNice p X := by
  obtain ⟨⟨hℓ, hf, -, hne2, hne3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hK' : IsOddPrimePower (Nat.card K) := ⟨ℓ, f, hℓ, hodd, hf, hK⟩
  have hcard : 3 < Nat.card K := by
    rw [hK]
    have h1 : 3 ≤ ℓ ^ f := by
      calc 3 ≤ ℓ := by
            have := hℓ.two_le
            omega
        _ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h2 : ℓ ^ f ≠ 3 := fun h3 => hne3 (by rw [h3])
    have h4 : ℓ ^ f ≠ 4 := fun h4 => by
      have := (hodd.pow (n := f))
      rw [h4] at this
      exact absurd this (by decide)
    omega
  have e' : X ≃* PSL2 K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact OutPNice.of_mulEquiv e' (outPNice_PSL2_field hp hp3 K hK hK' hcard)

end CFSG.RankThree.PartOne.OutStructure
