module

public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.R7Levi
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank Matrix

theorem layerRow7_of_core {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hEeq : E = (E ⊓ L) ⊔ Subgroup.zpowers c) (hEA' : E = A)
    (hcore : Table123Core p L (A ⊓ L) (E ⊓ L)) {f : ℕ} (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    ∃ (b : G) (K : Subgroup G), LayerCore p A L b K ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 f := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, hKf, hKfin, -, -, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame_of hcore hf1 hpq hmod
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hbMT : b7 ζ ∈ torus7 p K := b7_mem_torus7 hζp
  have hbMp : b7 ζ ^ p = 1 := torus7_pow_eq_one hbMT
  have hbMne : b7 ζ ≠ 1 := by
    intro h1
    have := congrArg (fun x : ↥(spRev K) => gm x 1 1) h1
    simp only [gm_one, Matrix.one_apply_eq] at this
    have h11 : gm (b7 ζ) 1 1 = (ζ : K) := by
      show ((diagU (dvec4 1 ζ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
      simp [diagU_val, dvec4]
    exact hζ1 (Units.ext (by rw [← h11]; exact this))
  obtain ⟨x, hx⟩ := hFT₁ (b7 ζ) hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = spQ K (b7 ζ) := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : spQ K (b7 ζ) = spQ K 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hKM := perfectResidual_centralizer_b7 (K := K) hK4 hζ1 hζ2
  have : CharP K 2 := hchar
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hEeq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem hLc hA ε
    (spQ K) hε hq hxA hxL hbMp hbb
    (T₀ := torus7 p K) (U := rootU7 K) (fun t ht => torus7_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_b7 hK4 hζ1 hζ2)
    (by
      rw [hKM, card_center_range_spBlock]
      exact hp.not_dvd_one)
    (by
      rw [hKM]
      exact card_torus7_inf_range hp.pos ⟨ζ, hζ⟩)
    (by rw [hKM]; exact rootU7_le_range) isPGroup_rootU7 torus7_le_normalizer_rootU7
    ⟨spBlock (tr2 1), spBlock_tr2_mem_rootU7 1, rho7 ζ, rho7_mem_torus7 hζp,
      spBlock_tr2_one_not_commute_rho7 hζ1⟩
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  refine ⟨⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, K, hKf, hKfin, hK, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv
      (MonoidHom.ofInjective (spBlock_injective (K := K))).symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)))⟩

theorem kf1212LayerRow7 : KF1212LayerRow 7 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨b, K, hd, hKmod⟩ := layerRow7_of_core ctx.hyp ctx.L_le_centralizer ctx.generic.E_eq hEA'
    ctx.table_core hf1 hpq hmod
  exact ⟨b, K, hd, by norm_num, by norm_num, f, hf1, hpq, hKmod⟩

end CFSG.RankThree.PartOne
