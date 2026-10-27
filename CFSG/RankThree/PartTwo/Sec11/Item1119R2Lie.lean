module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Mat

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11LieProof


open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

variable {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]

theorem exists_cube_of_cyclic {G : Type*} [Group G] [IsCyclic G] [Finite G]
    (h9 : 9 ∣ Nat.card G) (e : G) (he : e ^ 3 = 1) : ∃ c : G, c ^ 3 = e := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hx e)
  have hord : orderOf x = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hx
  obtain ⟨k, hk⟩ := h9
  have h3 : x ^ (j * 3) = 1 := by
    rw [_root_.zpow_mul, hj, zpow_ofNat]
    exact he
  have hdvd : (orderOf x : ℤ) ∣ j * 3 := orderOf_dvd_iff_zpow_eq_one.mpr h3
  rw [hord, hk] at hdvd
  push_cast at hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hj' : j = 3 * (k : ℤ) * t := by linarith
  refine ⟨x ^ ((k : ℤ) * t), ?_⟩
  rw [← zpow_natCast, ← _root_.zpow_mul, ← hj]
  congr 1
  push_cast
  linarith

theorem mem_projImage_slPi_of_cent (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (γ : projImage (glPi π 3 (p ^ f) Kf)) (hγ3 : γ ^ 3 = 1)
    (J : Subgroup (projImage (glPi π 3 (p ^ f) Kf))) (hJp : Group.IsPerfect J)
    (hJS : ∀ j ∈ J, (j : ProjGenLinGroup (Fin 3) Kf) ∈ projImage (slPi π 3 (p ^ f) Kf))
    (hJc : ∀ j ∈ J, γ * j = j * γ)
    (ξ : projImage (glPi π 3 (p ^ f) Kf)) (hξJ : ξ ∈ J) (hξ3 : ∃ k : ℕ, ξ ^ 3 ^ k = 1)
    (hξ9 : 9 ∣ orderOf ξ) :
    (γ : ProjGenLinGroup (Fin 3) Kf) ∈ projImage (slPi π 3 (p ^ f) Kf) := by
  have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hKf.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hKf hq
  obtain ⟨y₀, hy₀H, hy₀⟩ := γ.2
  have hmk1 : ∀ w ∈ StatedScalars (Fin 3) Kf, ProjGenLinGroup.mk w = 1 := fun w hw =>
    mk_eq_one_iff_mem_statedScalars.mpr hw
  have hγS : (γ : ProjGenLinGroup (Fin 3) Kf) ∈ projImage (slPi π 3 (p ^ f) Kf) ↔
      ∃ s ∈ slPi π 3 (p ^ f) Kf, ProjGenLinGroup.mk s = (γ : ProjGenLinGroup (Fin 3) Kf) := by
    constructor
    · rintro ⟨s, hs, hsγ⟩
      exact ⟨s, hs, hsγ⟩
    · rintro ⟨s, hs, hsγ⟩
      exact ⟨s, hs, hsγ⟩
  by_cases hy₀Z : y₀ ∈ StatedScalars (Fin 3) Kf
  ·
    have h1 : (γ : ProjGenLinGroup (Fin 3) Kf) = 1 := by rw [← hy₀]; exact hmk1 y₀ hy₀Z
    exact ⟨1, one_mem _, by rw [h1]; exact map_one _⟩
  have hy₀3s : y₀ ^ 3 ∈ StatedScalars (Fin 3) Kf := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hy₀]
    exact congrArg Subtype.val hγ3
  have hy₀Z' : y₀ ∉ zPi π 3 (p ^ f) Kf := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact fun h => hy₀Z h.2
  have hy₀3 : y₀ ^ 3 ∈ zPi π 3 (p ^ f) Kf := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hy₀H 3, hy₀3s⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcases⟩ := rank3II_4_10_one hKf hq hτ hτ1 hy₀H hy₀Z' hy₀3
  have hzs : z ∈ StatedScalars (Fin 3) Kf := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact hz.2
  have hmkz : ProjGenLinGroup.mk (y₀ * z) = ProjGenLinGroup.mk y₀ := by
    rw [map_mul, hmk1 z hzs, mul_one]
  haveI : Group.IsPerfect J := hJp
  have hξ1 : ξ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hξ9
    omega
  haveI : Nontrivial J := ⟨⟨⟨ξ, hξJ⟩, 1, fun h => hξ1 (congrArg Subtype.val h)⟩⟩
  have hJcm : ∀ j ∈ J, ∃ s ∈ centMod (slPi π 3 (p ^ f) Kf) (y₀ * z),
      ((j : projImage (glPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk s := by
    intro j hj
    obtain ⟨s, hs, hsj⟩ := hJS j hj
    have h1 : ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y₀)⁻¹ =
        ProjGenLinGroup.mk s := by
      have hcomm : ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk s =
          ProjGenLinGroup.mk s * ProjGenLinGroup.mk y₀ := by
        rw [hy₀, hsj]
        exact congrArg Subtype.val (hJc j hj)
      rw [hcomm, mul_inv_cancel_right]
    have h2 : y₀ * s * y₀⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      rw [← mk_eq_one_iff_mem_statedScalars]
      simp only [map_mul, map_inv]
      rw [h1, mul_inv_cancel]
    refine ⟨s, mem_centMod_iff_scalar.mpr ⟨hs, (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹, inv_mem h2, ?_⟩,
      hsj.symm⟩
    have hc1 := commute_of_mem_statedScalars hzs s⁻¹
    have hc2 := commute_of_mem_statedScalars (inv_mem h2) (y₀ * s)
    calc s * (y₀ * z) * s⁻¹ = s * y₀ * (z * s⁻¹) := by group
      _ = s * y₀ * (s⁻¹ * z) := by rw [hc1]
      _ = (y₀ * s * y₀⁻¹ * s⁻¹)⁻¹ * (y₀ * z) := by group
  have hsolv : Group.IsSolvable ↥(slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z}) →
      False := by
    intro hCs
    set C := centMod (slPi π 3 (p ^ f) Kf) (y₀ * z) with hC
    set C₀ := slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z} with hC₀
    have hC₀C : C₀ ≤ C := centralizer_le_centMod _ _
    have : Group.IsSolvable (C₀.subgroupOf C) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hC₀C).toMonoidHom) (MulEquiv.injective _)
    have : Group.IsSolvable (StatedScalars (Fin 3) Kf) := by
      refine Group.isSolvable_of_comm fun u v => Subtype.ext ?_
      exact commute_of_mem_statedScalars v.2 (u : GL (Fin 3) Kf)
    have hCs : Group.IsSolvable C := by
      refine Group.isSolvable_of_ker_le_range (C₀.subgroupOf C).subtype (commHom _ (y₀ * z)) ?_
      rw [ker_commHom, Subgroup.range_subtype]
    set S : Subgroup (ProjGenLinGroup (Fin 3) Kf) := C.map ProjGenLinGroup.mk with hS
    have hSs : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := ProjGenLinGroup.mk.subgroupMap C)
        (MonoidHom.subgroupMap_surjective _ _)
    have hJS' : ∀ j : J, (((j : projImage (glPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf)) ∈ S := by
      intro j
      obtain ⟨s, hsC, hms⟩ := hJcm j j.2
      rw [hms]
      exact Subgroup.mem_map_of_mem _ hsC
    set ι : J →* S := ((projImage (glPi π 3 (p ^ f) Kf)).subtype.comp J.subtype).codRestrict S
      hJS' with hι
    have hιinj : Function.Injective ι := by
      intro m m' h
      have h' : ((ι m : S) : ProjGenLinGroup (Fin 3) Kf) =
          ((ι m' : S) : ProjGenLinGroup (Fin 3) Kf) := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have hJs : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hιinj
    exact Group.IsPerfect.not_isSolvable J hJs
  rcases hcases with ⟨-, ⟨eT⟩, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, hcent⟩ | ⟨-, -, -, hcyc, -⟩
  · exfalso
    apply hsolv
    have : Group.IsSolvable (Multiplicative (ZMod (qSubPi π (p ^ f))) ×
        Multiplicative (ZMod (qSubPi π (p ^ f)))) := inferInstance
    exact Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
  swap
  · exfalso
    apply hsolv
    have : CommGroup ↥(slPi π 3 (p ^ f) Kf ⊓ Subgroup.centralizer {y₀ * z}) :=
      IsCyclic.commGroup
    infer_instance

  have hy : y₀ * z = g * diagE e * g⁻¹ := eq_conj_of_inv_conj hD
  have he3 : (e : Kf) ^ 3 = 1 := by
    rcases he with he | he <;> rw [he]
    · exact hτ
    · rw [← pow_mul, pow_mul', hτ, one_pow]
  have he1 : e ≠ 1 := by
    intro h1
    rw [h1, Units.val_one] at he
    rcases he with he | he
    · exact hτ1 he.symm
    · apply hτ1
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      calc τ = τ ^ 3 / τ ^ 2 := by field_simp
        _ = 1 := by rw [hτ, ← he, div_one]
  set Φ : GL (Fin 2) Kf →* ProjGenLinGroup (Fin 3) Kf :=
    (ProjGenLinGroup.mk : GL (Fin 3) Kf →* ProjGenLinGroup (Fin 3) Kf).comp
      ((MulAut.conj g).toMonoidHom.comp blockHom) with hΦ
  have hJΦ : ∀ j ∈ J, ((j : projImage (glPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf) ∈
      (glPi π 2 (p ^ f) Kf).map Φ := by
    intro j hj
    obtain ⟨s, hsC, hms⟩ := hJcm j hj
    rw [hcent, hy, ← map_conj_centralizer hπ hg, centralizer_diagE_eq hKf he1] at hsC
    obtain ⟨s', ⟨B, hB, rfl⟩, rfl⟩ := hsC
    exact ⟨B, hB, hms.symm⟩
  set JX : Subgroup (ProjGenLinGroup (Fin 3) Kf) :=
    J.map (projImage (glPi π 3 (p ^ f) Kf)).subtype with hJX
  have hJXp : Group.IsPerfect JX := Group.IsPerfect.map _
  have hJXle : JX ≤ (glPi π 2 (p ^ f) Kf).map Φ := by
    rintro _ ⟨j, hj, rfl⟩
    exact hJΦ j hj
  have hcomm : ⁅glPi π 2 (p ^ f) Kf, glPi π 2 (p ^ f) Kf⁆ ≤
      glPi π 2 (p ^ f) Kf ⊓ (GeneralLinearGroup.det : GL (Fin 2) Kf →* Kfˣ).ker := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    · rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
  have hJX2 : JX ≤ (glPi π 2 (p ^ f) Kf ⊓
      (GeneralLinearGroup.det : GL (Fin 2) Kf →* Kfˣ).ker).map Φ := by
    calc JX = ⁅JX, JX⁆ := (Subgroup.isPerfect_iff.mp hJXp).symm
      _ ≤ ⁅(glPi π 2 (p ^ f) Kf).map Φ, (glPi π 2 (p ^ f) Kf).map Φ⁆ :=
          Subgroup.commutator_mono hJXle hJXle
      _ = ⁅glPi π 2 (p ^ f) Kf, glPi π 2 (p ^ f) Kf⁆.map Φ := (Subgroup.map_commutator _ _ _).symm
      _ ≤ _ := Subgroup.map_mono hcomm
  obtain ⟨B, ⟨hB, hBdet⟩, hBξ⟩ := hJX2 ⟨ξ, hξJ, rfl⟩
  have hBsl : B ∈ slPi π 2 (p ^ f) Kf := by
    refine (mem_slPi_iff hπ).mpr ⟨hB, ?_⟩
    have := congrArg (fun u : Kfˣ => (u : Kf)) (MonoidHom.mem_ker.mp hBdet)
    simpa [GeneralLinearGroup.val_det_apply] using this
  have hordξB : orderOf ξ ∣ orderOf B := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    have h1 : ((ξ ^ orderOf B : projImage (glPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf) = (ξ : ProjGenLinGroup (Fin 3) Kf) ^ orderOf B := rfl
    have hB' : (ξ : ProjGenLinGroup (Fin 3) Kf) = Φ B := hBξ.symm
    rw [h1, hB', ← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  have hBcard : orderOf B ∣ Nat.card (slPi π 2 (p ^ f) Kf) := by
    have := Subgroup.orderOf_dvd_natCard (slPi π 2 (p ^ f) Kf) hBsl
    simpa using this
  have h9card : 9 ∣ Nat.card (slPi π 2 (p ^ f) Kf) :=
    (hξ9.trans hordξB).trans hBcard
  have hqne : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hKf hq
  have h9 : 9 ∣ qSubPi π (p ^ f) := by
    have := hKf.finite
    have hfac := Item1120V0Bar.factorization_card_slPi_two hKf hq
    have hpos : Nat.card (slPi π 2 (p ^ f) Kf) ≠ 0 := Nat.card_pos.ne'
    have h1 : 2 ≤ (Nat.card (slPi π 2 (p ^ f) Kf)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).mp
        (by simpa using h9card)
    rw [hfac] at h1
    simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hqne).mpr h1
  have hcube : ∃ c : Kfˣ, c ^ (qSubPi π (p ^ f)) = 1 ∧ c ^ 3 = e⁻¹ := by
    have := hKf.finite
    have : NeZero (qSubPi π (p ^ f)) := ⟨hqne⟩
    haveI : IsCyclic (rootsOfUnity (qSubPi π (p ^ f)) Kf) := rootsOfUnity.isCyclic _ _
    have hcardT := card_rootsOfUnity_qSubPi hKf hq
    have he3' : (e⁻¹) ^ 3 = 1 := by
      rw [inv_pow]
      have : e ^ 3 = 1 := Units.ext (by simpa using he3)
      rw [this, inv_one]
    have heN : e⁻¹ ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf := by
      rw [mem_rootsOfUnity]
      obtain ⟨m, hm⟩ := (dvd_trans (by norm_num : 3 ∣ 9) h9)
      rw [hm, pow_mul, he3', one_pow]
    obtain ⟨c, hc⟩ := exists_cube_of_cyclic (G := rootsOfUnity (qSubPi π (p ^ f)) Kf)
      (by rw [hcardT]; exact h9) ⟨e⁻¹, heN⟩ (Subtype.ext he3')
    refine ⟨(c : Kfˣ), ((mem_rootsOfUnity _ _).mp c.2), ?_⟩
    exact congrArg Subtype.val hc
  obtain ⟨c, hcN, hc3⟩ := hcube
  have hsc : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) Kf) ∈
      StatedScalars (Fin 3) Kf := ⟨c, rfl⟩
  have hlq : π = false → (e : Kf) ^ (p ^ f + 1) = 1 := by
    intro hπf
    subst hπf
    obtain ⟨m, hm⟩ := dvd_trans (by norm_num : 3 ∣ 9) (show 9 ∣ p ^ f + 1 from h9)
    rw [hm, pow_mul, he3, one_pow]
  have hscG : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) Kf) ∈
      glPi π 3 (p ^ f) Kf := (scalar_mem_glPi_iff hKf c).mpr ((mem_rootsOfUnity _ _).mpr hcN)
  have hyG : g * diagE e * g⁻¹ ∈ glPi π 3 (p ^ f) Kf :=
    mul_mem (mul_mem hg (diagE_mem_glPi hKf hlq)) (inv_mem hg)
  set s := Matrix.GeneralLinearGroup.scalar (Fin 3) c * (g * diagE e * g⁻¹) with hs
  have hsG : s ∈ glPi π 3 (p ^ f) Kf := mul_mem hscG hyG
  have hdetY : ((g * diagE e * g⁻¹ : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf).det =
      (e : Kf) := by
    rw [det_conj_gl, ← GeneralLinearGroup.val_det_apply, det_diagE]
  have hscdet : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) Kf) :
      Matrix (Fin 3) (Fin 3) Kf).det = (c : Kf) ^ 3 := by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Fin.prod_univ_three]
    ring
  have hsdet : (s : Matrix (Fin 3) (Fin 3) Kf).det = 1 := by
    rw [hs, Units.val_mul, det_mul, hscdet, hdetY]
    have h1 : (c : Kf) ^ 3 = ((e⁻¹ : Kfˣ) : Kf) := by
      rw [← Units.val_pow_eq_pow_val, hc3]
    rw [h1, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero e)]
  have hsS : s ∈ slPi π 3 (p ^ f) Kf := (mem_slPi_iff hπ).mpr ⟨hsG, hsdet⟩
  refine ⟨s, hsS, ?_⟩
  rw [hs, map_mul, hmk1 _ hsc, one_mul, ← hy, hmkz, hy₀]

end CFSG.RankThree.PartTwo.Sec11.KS11LieProof
