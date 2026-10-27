module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESU5
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.RankThree.PartTwo.Sec4.RonanK429E.SU5 (U KK eK card_U projEquiv f4c_eq_one_of_pow_five)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.GH74.Uniqueness.SU.SU5.F4c (z0 z1 w w2)
open Matrix

namespace U52

@[expose] noncomputable def Φ : Matrix (Fin 5) (Fin 5) KK ≃+* Matrix (Fin 5) (Fin 5) F4c :=
  eK.symm.mapMatrix

@[expose] noncomputable def matU : U →* Matrix (Fin 5) (Fin 5) KK :=
  (Units.coeHom (Matrix (Fin 5) (Fin 5) KK)).comp (CFSG.Open.StatedSU 5 (2 ^ 1) KK).subtype

theorem matU_injective : Function.Injective matU := by
  intro g h e
  exact Subtype.ext (Units.ext e)

@[expose] def u5Y : Matrix (Fin 5) (Fin 5) F4c :=
  !![z0, z0, z0, z0, z1; z1, z0, z0, z0, z0; z0, z1, z0, z0, z0; z0, z0, z1, z0, z0; z0, z0, z0, z1, z0]

@[expose] def u5Z : Matrix (Fin 5) (Fin 5) F4c :=
  !![w, z1, z1, z1, z1; z1, w, z1, z1, z1; z1, z1, w, z1, z1; z1, z1, z1, w, z1; z1, z1, z1, z1, w]

@[expose] def u5F : Matrix (Fin 5) (Fin 5) F4c :=
  !![z0, w, w, z1, z0; z0, w, z0, z1, w; z1, w, z1, w, z1; w, w, z0, z1, z0; w, z1, w, w, w]

@[expose] def u5Fi : Matrix (Fin 5) (Fin 5) F4c :=
  !![z0, z0, z1, w2, w2; w2, w2, w2, w2, z1; w2, z0, z1, z0, w2; z1, z1, w2, z1, w2; z0, w2, z1, z0, w2]

@[expose] def u5X : Matrix (Fin 5) (Fin 5) F4c :=
  !![w, z1, w, w, w; z0, w, w, z1, z0; z0, w, z0, z1, w; z1, w, z1, w, z1; w, w, z0, z1, z0]

@[expose] def u5M : Matrix (Fin 5) (Fin 5) F4c :=
  !![z1, z1, z0, z0, z0; z1, z1, z1, z0, z0; z1, z0, z1, z1, z0; z1, z0, z0, z1, z1; z1, z0, z0, z0, z1]

@[expose] def u5Mi : Matrix (Fin 5) (Fin 5) F4c :=
  !![z1, z1, z1, z1, z1; z0, z1, z1, z1, z1; z1, z1, z0, z0, z0; z0, z0, z0, z1, z1; z1, z1, z1, z1, z0]

@[expose] def u5Yi : Matrix (Fin 5) (Fin 5) F4c :=
  !![z0, z1, z0, z0, z0; z0, z0, z1, z0, z0; z0, z0, z0, z1, z0; z0, z0, z0, z0, z1; z1, z0, z0, z0, z0]

@[expose] def u5Zi : Matrix (Fin 5) (Fin 5) F4c :=
  !![w2, z1, z1, z1, z1; z1, w2, z1, z1, z1; z1, z1, w2, z1, z1; z1, z1, z1, w2, z1; z1, z1, z1, z1, w2]

theorem u5Y_mul : u5Y * u5Yi = 1 := by decide +kernel
theorem u5Y_mul' : u5Yi * u5Y = 1 := by decide +kernel
theorem u5Z_mul : u5Z * u5Zi = 1 := by decide +kernel
theorem u5Z_mul' : u5Zi * u5Z = 1 := by decide +kernel
theorem u5F_mul : u5F * u5Fi = 1 := by decide +kernel
theorem u5F_mul' : u5Fi * u5F = 1 := by decide +kernel
theorem u5M_mul' : u5Mi * u5M = 1 := by decide +kernel

theorem u5Y_unitary : (u5Y.map (· ^ (2 ^ 1)))ᵀ * u5Y = 1 := by decide +kernel
theorem u5Z_unitary : (u5Z.map (· ^ (2 ^ 1)))ᵀ * u5Z = 1 := by decide +kernel
theorem u5F_unitary : (u5F.map (· ^ (2 ^ 1)))ᵀ * u5F = 1 := by decide +kernel

theorem u5Y_pow : u5Y ^ 5 = 1 := by decide +kernel
theorem u5Y_ne : u5Y ≠ 1 := by decide +kernel
theorem u5Z_pow : u5Z ^ 3 = 1 := by decide +kernel
theorem u5F_pow : u5F ^ 5 = 1 := by decide +kernel
theorem u5YZ : u5Y * u5Z = u5Z * u5Y := by decide +kernel
theorem u5FZ : u5F * u5Z = u5Z * u5F := by decide +kernel
theorem u5YF : u5Y * u5F = u5X := by decide +kernel
theorem u5X_pow : u5X ^ 9 = 1 := by decide +kernel
theorem u5X_ne : u5X ^ 3 ≠ 1 := by decide +kernel

theorem u5Z_diag : u5Z = u5M * Matrix.diagonal ![w, w2, w2, w2, w2] * u5Mi := by decide +kernel

theorem det_u5Y : u5Y.det = 1 :=
  f4c_eq_one_of_pow_five _ (by rw [← Matrix.det_pow, u5Y_pow, Matrix.det_one])

theorem det_u5F : u5F.det = 1 :=
  f4c_eq_one_of_pow_five _ (by rw [← Matrix.det_pow, u5F_pow, Matrix.det_one])

theorem det_u5Z : u5Z.det = 1 := by
  have hMM : u5Mi.det * u5M.det = 1 := by rw [← Matrix.det_mul, u5M_mul', Matrix.det_one]
  have hD : (Matrix.diagonal ![w, w2, w2, w2, w2]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_five]
    decide
  rw [u5Z_diag, Matrix.det_mul, Matrix.det_mul, hD, mul_one, mul_comm, hMM]

@[expose] def pwY : Fin 5 → Matrix (Fin 5) (Fin 5) F4c := fun j => u5Y ^ (j : ℕ)

@[expose] def e0 : Fin 5 → F4c := ![z1, z0, z0, z0, z0]

theorem kr_eq' : (1 : Matrix (Fin 5) (Fin 5) F4c) = Matrix.of fun i j => (pwY j *ᵥ e0) i := by
  decide +kernel

theorem kr_eq : ∀ i j : Fin 5, (1 : Matrix (Fin 5) (Fin 5) F4c) i j = (pwY j *ᵥ e0) i := by
  intro i j
  rw [kr_eq']
  rfl

theorem commute_check : ∀ v : Fin 5 → F4c, (∑ j, v j • pwY j) ^ 3 = 1 →
    ((∑ j, v j • pwY j).map (· ^ (2 ^ 1)))ᵀ * (∑ j, v j • pwY j) = 1 →
    ∃ c : F4c, ∃ k : Fin 3, ∑ j, v j • pwY j = c • u5Z ^ (k : ℕ) := by
  decide +kernel

noncomputable def mkU (M Mi : Matrix (Fin 5) (Fin 5) F4c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hu : (M.map (· ^ (2 ^ 1)))ᵀ * M = 1) (hd : M.det = 1) : U :=
  ⟨CFSG.Adapters.RankTwoModelTransports.glCongr eK ⟨M, Mi, h1, h2⟩, by
    rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU eK 5 (2 ^ 1)]
    refine ⟨⟨M, Mi, h1, h2⟩, ?_, rfl⟩
    unfold CFSG.Open.StatedSU
    exact Subgroup.subset_closure ⟨hd, hu⟩⟩

theorem Φ_matU_mkU (M Mi : Matrix (Fin 5) (Fin 5) F4c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hu : (M.map (· ^ (2 ^ 1)))ᵀ * M = 1) (hd : M.det = 1) :
    Φ (matU (mkU M Mi h1 h2 hu hd)) = M := by
  show (M.map eK).map eK.symm = M
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id M]
  congr 1
  funext c
  exact eK.symm_apply_apply c

noncomputable def yU : U := mkU u5Y u5Yi u5Y_mul u5Y_mul' u5Y_unitary det_u5Y

noncomputable def zU : U := mkU u5Z u5Zi u5Z_mul u5Z_mul' u5Z_unitary det_u5Z

noncomputable def fU : U := mkU u5F u5Fi u5F_mul u5F_mul' u5F_unitary det_u5F

theorem Φy : Φ (matU yU) = u5Y := Φ_matU_mkU _ _ _ _ _ _
theorem Φz : Φ (matU zU) = u5Z := Φ_matU_mkU _ _ _ _ _ _
theorem Φf : Φ (matU fU) = u5F := Φ_matU_mkU _ _ _ _ _ _

theorem eq_of_Φ {a b : U} (h : Φ (matU a) = Φ (matU b)) : a = b :=
  matU_injective (Φ.injective h)

theorem orderOf_yU : orderOf yU = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (eq_of_Φ ?_) fun h => u5Y_ne ?_
  · rw [map_pow, map_pow, Φy, u5Y_pow, map_one, map_one]
  · rw [← Φy, h, map_one, map_one]

theorem zU_pow : zU ^ 3 = 1 := eq_of_Φ (by rw [map_pow, map_pow, Φz, u5Z_pow, map_one, map_one])

theorem yU_comm : yU * zU = zU * yU :=
  eq_of_Φ (by rw [map_mul, map_mul, map_mul, map_mul, Φy, Φz, u5YZ])

theorem fU_comm : fU * zU = zU * fU :=
  eq_of_Φ (by rw [map_mul, map_mul, map_mul, map_mul, Φf, Φz, u5FZ])

theorem fU_pow : fU ^ 5 = 1 := eq_of_Φ (by rw [map_pow, map_pow, Φf, u5F_pow, map_one, map_one])

theorem yU_pow : yU ^ 5 = 1 := eq_of_Φ (by rw [map_pow, map_pow, Φy, u5Y_pow, map_one, map_one])

theorem orderOf_yf : orderOf (yU * fU) = 9 := by
  have h9 : (yU * fU) ^ 9 = 1 :=
    eq_of_Φ (by rw [map_pow, map_pow, map_mul, map_mul, Φy, Φf, u5YF, u5X_pow, map_one, map_one])
  have h3 : (yU * fU) ^ 3 ≠ 1 := fun h => u5X_ne (by
    have := congrArg (fun a => Φ (matU a)) h
    simp only [map_pow, map_mul, map_one] at this
    rwa [Φy, Φf, u5YF] at this)
  have hd := orderOf_dvd_of_pow_eq_one h9
  have hd' : ¬ orderOf (yU * fU) ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.mp h)
  have h9' : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9'] at hd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hd
  interval_cases k
  · rw [hk', pow_zero] at hd'
    exact absurd (one_dvd 3) hd'
  · rw [hk', pow_one] at hd'
    exact absurd dvd_rfl hd'
  · rw [hk']
    norm_num

theorem unitary_Φ (s : U) : ((Φ (matU s)).map (· ^ (2 ^ 1)))ᵀ * Φ (matU s) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKK : Nat.card KK = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have hs : ((s : GL (Fin 5) KK)) ∈ CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution KK 2 1) 5 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hKK 5]
    exact s.2
  have h3 := congrArg Φ hs.2
  rw [map_mul, map_one] at h3
  refine Eq.trans ?_ h3
  congr 1
  ext i j
  simp only [Φ, matU, RingEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    CFSG.LieType.Universal.Unitary.conjTr, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply, Subgroup.coe_subtype, CFSG.LieType.BorelTits.unitaryInvolution_apply,
    map_pow]

theorem eq_of_commute_y (s : U) (hs : s * yU = yU * s) (h3 : s ^ 3 = 1) (h1 : s ≠ 1) :
    s = zU ∨ s = zU ^ 2 := by
  have hm : Φ (matU s) * u5Y = u5Y * Φ (matU s) := by
    rw [← Φy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hs]
  have heq := RonanK429E.eq_sum_of_commute (kr := 1) (kr' := 1) (v := e0) (M := pwY)
    (e := fun j => (j : ℕ)) (fun _ => rfl) kr_eq (mul_one 1) hm
  rw [Matrix.one_mulVec] at heq
  obtain ⟨c, k, hck⟩ := commute_check (Φ (matU s) *ᵥ e0)
    (by rw [← heq, ← map_pow, ← map_pow, h3, map_one, map_one])
    (by rw [← heq]; exact unitary_Φ s)
  rw [← heq] at hck
  have hdet : (Φ (matU s)).det = 1 := by
    have hd1 : (matU s).det = 1 := RonanK429E.det_eq_one_of_mem_statedSU s.2
    have hd2 := RingHom.map_det (eK.symm : KK →+* F4c) (matU s)
    rw [hd1, map_one] at hd2
    exact hd2.symm
  rw [hck, Matrix.det_smul, Matrix.det_pow, det_u5Z, one_pow, mul_one, Fintype.card_fin] at hdet
  have hc1 := f4c_eq_one_of_pow_five c hdet
  rw [hc1, one_smul] at hck
  have hs' : s = zU ^ (k : ℕ) := eq_of_Φ (by rw [hck, map_pow, map_pow, Φz])
  fin_cases k
  · exact absurd (by simpa using hs') h1
  · left
    simpa using hs'
  · right
    simpa using hs'

theorem good427_zU : Good427 (Subgroup.centralizer ({zU} : Set U)) := by
  refine good427_of_five (H := Subgroup.zpowers (yU * fU)) ?_ ?_ ?_
  · intro h
    have := h.trans (Subgroup.card_subgroup_dvd_card _)
    rw [card_U] at this
    norm_num at this
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨?_, yU_pow⟩)
      (Subgroup.subset_closure ⟨?_, fU_pow⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr yU_comm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr fU_comm
  · intro a
    rw [Nat.card_zpowers, orderOf_yf]
    exact not_dvd_sixty_of_nine_dvd dvd_rfl a

theorem good427_su52 (s : U) (hs : orderOf s = 3) :
    Good427 (Subgroup.centralizer ({s} : Set U)) := by
  have hs3 : s ^ 3 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    norm_num at hs
  by_cases h5 : 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set U))
  · obtain ⟨x, hx⟩ := RonanK429F.exists_conj_commute_of_dvd (by norm_num) orderOf_yU
      (by rw [card_U]; norm_num) h5
    have h3' : (x⁻¹ * s * x) ^ 3 = 1 := by
      rw [show x⁻¹ * s * x = MulAut.conj x⁻¹ s by simp [MulAut.conj_apply], ← map_pow, hs3,
        map_one]
    have h1' : x⁻¹ * s * x ≠ 1 := by
      intro h
      apply hs1
      calc s = x * (x⁻¹ * s * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    rcases eq_of_commute_y _ hx h3' h1' with h | h
    · refine Good427.of_isConj (isConj_iff.mpr ⟨x, ?_⟩) good427_zU
      rw [← h]
      group
    · have hz2 := RonanK429H.centralizer_pow_of_pow_three zU_pow (e := 2) (Or.inr rfl)
      refine Good427.of_isConj (a := zU ^ 2) (isConj_iff.mpr ⟨x, ?_⟩)
        (by rw [hz2]; exact good427_zU)
      rw [← h]
      group
  · exact good427_of_not_five_dvd h5

end U52

open U52

section Row

theorem rowOf427_su52
    : RowOf427 (projSU 5 2 1) :=
  rowOf427_of_noCfgS fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    have hout : ¬ 3 ∣ Nat.card (Outer (projSU 5 2 1)) := by
      rw [Item434SmallTwoIV.card_outer_projSU_five_two]
      norm_num
    refine ⟨noCfgS427_of_model (e.trans projEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
      (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) good427_su52, noONS427_of_card ?_⟩
    rw [Nat.card_congr (e.trans projEquiv).toEquiv, card_U]
    norm_num

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
