module

public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.R1Levi
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.RankThree.CALinearPlane Matrix

theorem kf1212LayerRow1 : KF1212LayerRow 1 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r1frame hcore hmodel
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hu3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let e := specialLinearGroupEquivStatedSL 3 K
  let q := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
  have hq := isCentralPQuot_statedSL (K := K) hp h5
  have hq' : IsCentralPQuot p (q.comp e.toMonoidHom) := hq.comp_mulEquiv e
  set bM : SpecialLinearGroup (Fin 3) K := bSL ζ with hbM
  have hbMT : bM ∈ torusSL p K := bSL_mem_torusSL hζp
  have hbMp : bM ^ p = 1 := torusSL_pow_eq_one hbMT
  have hbMne : bM ≠ 1 := by
    intro h1
    have := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [hbM, coe_bSL, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at this
    exact hζ.ne_one (by omega) (Units.ext (by simpa [bVec] using this))
  have heT : e bM ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_comap.1 hbMT)
  obtain ⟨x, hx⟩ := hFT₁ (e bM) heT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = (q.comp e.toMonoidHom) bM := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : (q.comp e.toMonoidHom) bM = (q.comp e.toMonoidHom) 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq'.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torusSL p K).map (q.comp e.toMonoidHom) := by
    have hTmap : (torusSL p K).map e.toMonoidHom = (torusSU p 3 K).subgroupOf (StatedSL 3 K) := by
      ext t
      obtain ⟨g, rfl⟩ := e.surjective t
      constructor
      · rintro ⟨g', hg', hg'e⟩
        have : g' = g := e.injective hg'e
        subst this
        exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_comap.1 hg')
      · intro ht
        exact ⟨g, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.1 ht), rfl⟩
    rw [← Subgroup.map_map, hTmap, hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hKM := perfectResidual_centralizer_bSL (K := K) hK4 hu3
  have : CharP K 2 := hchar
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε
    (q.comp e.toMonoidHom) hε hq' hxA hxL hbMp hbb
    (T₀ := torusSL p K) (U := rootU K) (fun t ht => torusSL_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_bSL hK4 hu3)
    (by
      rw [hKM, card_center_blockJ]
      exact hp.not_dvd_one)
    (by
      rw [hKM]
      exact card_torusSL_inf_blockJ hp.pos ⟨ζ, hζ⟩)
    (by rw [hKM]; exact rootU_le_blockJ) isPGroup_rootU torusSL_le_normalizer_rootU
    ⟨trSL 1, trSL_mem_rootU 1, rhoSL ζ, rhoSL_mem_torusSL hζp, trSL_one_not_commute_rhoSL hζne⟩
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  refine ⟨le_rfl, by norm_num, f, hf1, hpq, ⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, K, hKf,
    hKfin, hK, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    let eJ : SpecialLinearGroup (Fin 2) K ≃* ↥(coordBlockSL K jTwo) :=
      (MonoidHom.ofInjective (blockSLOn_injective (k := K) jTwo)).trans
        (MulEquiv.subgroupCongr (range_blockSLOn jTwo))
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv eJ.symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)))⟩

end CFSG.RankThree.PartOne
