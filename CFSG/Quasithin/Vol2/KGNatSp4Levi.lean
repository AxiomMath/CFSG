module

public import CFSG.Quasithin.Vol2.KGNatSp4Flag
public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer mem_stabilizer flag isoFlag
  mem_isoFlag unipotent exists_sylow_unipotent)

variable {K : Type} [Field K]

theorem flag_one_eq : flag 2 K 1 = spLine K := by
  ext v
  rw [flag, ite_eq_left (by norm_num), mem_isoFlag, mem_spLine]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 1 (by simp), h1 0, h1 1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h2
      · exact h3
    · fin_cases j
      · simp at hj
      · exact h1

theorem flag_two_eq : flag 2 K 2 = spPlane K := by
  ext v
  rw [flag, ite_eq_left le_rfl, mem_isoFlag, mem_spPlane]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨h2, h3⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h2
      · exact h3
    · exact absurd j.2 (by omega)

theorem mem_stabilizer_iff' {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} {γ : StatedSp 2 K} :
    γ ∈ stabilizer 2 K W ↔ ∀ y, y ∈ W ↔ mat 2 K γ *ᵥ y ∈ W := by
  rw [mem_stabilizer]
  constructor
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have := congrArg (fun v => mat 2 K γ⁻¹ *ᵥ v) hzy
        simp only [Matrix.mulVecLin_apply] at this
        rwa [show (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
          mat 2 K γ from rfl, mat_inv_mulVec, mat_inv_mulVec] at this
      rwa [← this]
  · intro h
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (h y).mp hy
    · intro y hy
      refine ⟨mat 2 K γ⁻¹ *ᵥ y, (h _).mpr (by rwa [mat_mulVec_inv]), ?_⟩
      exact mat_mulVec_inv γ y

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

@[expose] noncomputable def psiSp (π : ↥(StatedSp 2 K) →* ↥H) (g : StatedSp 2 K) :
    StatedSp 2 K →* MulAut W :=
  H.subtype.comp (π.comp (MulAut.conj g).toMonoidHom)

theorem psiSp_apply (π : ↥(StatedSp 2 K) →* ↥H) (g γ : StatedSp 2 K) :
    psiSp π g γ = ((π (g * γ * g⁻¹) : ↥H) : MulAut W) := rfl

theorem psiSp_injective (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    Function.Injective (psiSp π g) :=
  H.subtype_injective.comp (hf.injective_nat.comp (MulAut.conj g).injective)

theorem map_stabilizer_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    (stabilizer 2 K S).map (psiSp π g) =
      H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g S).toAddSubgroup) := by
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [psiSp_apply]
    refine ⟨(π _).2, (hf.pi_mem_stabW_iff_sp (hf.le_pre _) _).mpr ?_⟩
    rw [hf.img_pre]
    intro y
    change y ∈ gmapSp g S ↔ _ ∈ gmapSp g S
    rw [mem_gmapSp, mem_gmapSp, conj_mulVec_sp]
    exact mem_stabilizer_iff'.mp hγ _
  · rintro ⟨hxH, hxS⟩
    obtain ⟨δ, hδ⟩ : ∃ δ : StatedSp 2 K, π δ = ⟨x, hxH⟩ := hf.onto ⟨x, hxH⟩
    have hδx : ((π δ : ↥H) : MulAut W) = x := congrArg Subtype.val hδ
    have hδS : ((π δ : ↥H) : MulAut W) ∈ Ch11.SecA.stabW (hf.pre (gmapSp g S).toAddSubgroup) := by
      rw [hδx]
      exact hxS
    refine ⟨g⁻¹ * δ * g, mem_stabilizer_iff'.mpr fun y => ?_, ?_⟩
    · have h1 := (hf.pi_mem_stabW_iff_sp (hf.le_pre _) δ).mp hδS (mat 2 K g *ᵥ y)
      rw [hf.img_pre] at h1
      change _ ∈ gmapSp g S ↔ _ ∈ gmapSp g S at h1
      rw [mem_gmapSp, mem_gmapSp, mat_inv_mulVec] at h1
      rw [h1, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    · rw [psiSp_apply, show g * (g⁻¹ * δ * g) * g⁻¹ = δ by group, hδx]

end Real

theorem factLeviSp4_holds : Ch11.SecA.FactLeviSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP i U hi hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple (K := K) hK4
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK] at hU
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, S = flag 2 K ((j : ℕ) + 1) := by
    rcases hi with rfl | rfl
    · exact ⟨0, by rw [(eq_std_of_stable_sp hS).1 (by rw [hc, pow_one])]; exact flag_one_eq.symm⟩
    · exact ⟨1, by rw [(eq_std_of_stable_sp hS).2.1 hc]; exact flag_two_eq.symm⟩
  subst hj
  have hA : perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g
      (flag 2 K ((j : ℕ) + 1))).toAddSubgroup)) =
      (perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q2 K j)).map (psiSp π g) :=
    (congrArg perfectCore (map_stabilizer_eq hf g _)).symm.trans
      (perfectCore_map _ (psiSp_injective hf g) _)
  let e := (MulEquiv.subgroupCongr hA).trans
    ((perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q2 K j)).equivMapOfInjective _
      (psiSp_injective hf g)).symm
  have hker : IsPGroup 2 (CFSG.QuasithinUnique.Vol2Native.A312L.blkN (K := K) j).ker := by
    obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := K) 2 2
    intro x
    have hxU := CFSG.QuasithinUnique.Vol2Native.A312L.blkN_ker (K := K) j
      (x : ↥(perfectCore (CFSG.QuasithinUnique.Setup.X7a.Q2 K j)))
      (MonoidHom.mem_ker.mp x.2)
    obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨_, hP₀ ▸ hxU⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).trans
    (CFSG.QuasithinUnique.Vol2Native.A312L.modO2EquivOfHom
      (CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4)
      (CFSG.QuasithinUnique.Vol2Native.A312L.blkN j)
      (CFSG.QuasithinUnique.Vol2Native.A312L.blkN_surjective hK4 j) hker)⟩

end CFSG.Quasithin.Vol2.KGNat
