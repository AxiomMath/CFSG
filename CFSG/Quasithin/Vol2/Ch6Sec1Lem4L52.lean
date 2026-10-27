module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V3

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section L52

variable {K : Type} [Field K] [Finite K]

noncomputable def glEquivSL614 (hK : Nat.card K = 2) (m : ℕ) :
    GL (Fin m) K ≃* SpecialLinearGroup (Fin m) K :=
  (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →*
    GL (Fin m) K) ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      refine ⟨⟨(g : Matrix (Fin m) (Fin m) K), ?_⟩, Units.ext rfl⟩
      have h1 := units_eq_one_of_card_two hK (Matrix.GeneralLinearGroup.det g)
      have h2 := congrArg Units.val h1
      simpa using h2⟩).symm

theorem noFiveOver_gl4_614 (hK : Nat.card K = 2) :
    FiveNorm.NoFiveOver (GL (Fin 4) K) := by
  have h : StatedClassicalModel (GL (Fin 4) K) .PSL 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by decide⟩, K, inferInstance, inferInstance, by rw [hK]; norm_num,
      ⟨(glEquivSL614 hK 4).trans (slEquivStatedProj hK 4)⟩⟩
  exact noFiveOver_psl42_614 h

omit [Finite K] in
theorem mem_unitriangular_of_two_blocks614 {d : ℕ} (hd1 : 1 ≤ d) (hd5 : d < 5)
    {g : SpecialLinearGroup (Fin 5) K} (hg : g ∈ stabilizer (flagSpace 5 K d))
    (hA : blkAt 0 d (by omega) (g : Matrix (Fin 5) (Fin 5) K) = 1)
    (hD : blkAt d (5 - d) (by omega) (g : Matrix (Fin 5) (Fin 5) K) = 1) :
    g ∈ unitriangular 5 K := by
  refine mem_unitriangular_of_blocks (I := {d}) (mem_flagStabilizer.mpr fun i hi => ?_) ?_
  · rw [Set.mem_singleton_iff] at hi
    rw [hi]
    exact hg
  · intro a m h ha hb hc
    simp only [Set.mem_singleton_iff] at ha hb hc
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd ⟨by omega, by omega⟩ (hc d rfl)
    · subst ha
      obtain rfl : m = d := by omega
      exact hA
    · subst ha
      obtain rfl : m = 5 - a := by omega
      exact hD
    · obtain rfl : m = 0 := by omega
      ext i
      exact i.elim0

theorem not_five_dvd_card_stabilizer614 [CharP K 2] (hK : Nat.card K = 2) {d : ℕ}
    (hd : d = 2 ∨ d = 3) : ¬ 5 ∣ Nat.card (stabilizer (flagSpace 5 K d)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd5 : d < 5 := by omega
  set Q := stabilizer (flagSpace 5 K d) with hQ
  have hLA : BlockLeft Q 0 d := blockLeft_zero Q d
  have hRA : BlockRight Q 0 d := blockRight_of_stabilizer (a := 0) (m := d) fun g hg => by
    rw [zero_add]
    exact hg
  have hLD : BlockLeft Q d (5 - d) := blockLeft_of_stabilizer fun g hg => hg
  have hRD : BlockRight Q d (5 - d) := blockRight_top Q (by omega)
  set φ := (blkMon Q 0 d (by omega) hLA hRA).toHomUnits.prod
    (blkMon Q d (5 - d) (by omega) hLD hRD).toHomUnits with hφ
  have hker : IsPGroup 2 φ.ker := by
    refine isPGroup_ker_of_unitriangular (by norm_num) φ fun x hx => ?_
    have h1 := congrArg (fun u => (u.1 : Matrix (Fin d) (Fin d) K)) hx
    have h2 := congrArg (fun u => (u.2 : Matrix (Fin (5 - d)) (Fin (5 - d)) K)) hx
    exact mem_unitriangular_of_two_blocks614 hd1 hd5 x.2 h1 h2
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hdvd : Nat.card φ.range ∣ Nat.card (GL (Fin d) K) * Nat.card (GL (Fin (5 - d)) K) := by
    rw [← Nat.card_prod]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hGL : Nat.card (GL (Fin d) K) * Nat.card (GL (Fin (5 - d)) K) = 1008 := by
    rcases hd with rfl | rfl <;> rw [card_GL_eq, card_GL_eq, hK] <;> decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  intro h5
  rw [← hcard, hk] at h5
  have h5' : (5 : ℕ).Prime := by norm_num
  rcases h5'.dvd_mul.mp h5 with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow h5' h) (by norm_num)
  · exact absurd (h.trans (hGL ▸ hdvd)) (by norm_num)

theorem false_of_levi614 [CharP K 2] (hK : Nat.card K = 2)
    {Q : Subgroup (SpecialLinearGroup (Fin 5) K)} (ψ : ↥Q →* GL (Fin 4) K)
    {H : Subgroup (SpecialLinearGroup (Fin 5) K)} (hUH : unitriangular 5 K ≤ H) (hHQ : H ≤ Q)
    (hcard : Nat.card H = 5 * 2 ^ 10)
    (hkerU : ∀ x : ↥Q, ψ x = 1 → (x : SpecialLinearGroup (Fin 5) K) ∈ unitriangular 5 K)
    (hker4 : Nat.card ψ.ker ≤ 2 ^ 4) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' := (unitriangular 5 K).subgroupOf Q with hU'
  set H' := H.subgroupOf Q with hH'
  have hUQ : unitriangular 5 K ≤ Q := hUH.trans hHQ
  have hcU : Nat.card U' = 2 ^ 10 := by
    rw [hU', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv, card_unitriangular, hK]
  have hcH : Nat.card H' = 5 * 2 ^ 10 := by
    rw [hH', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv, hcard]
  have hkU : ψ.ker ≤ U' := fun x hx => hkerU x hx
  have hU'H' : U' ≤ H' := fun x hx => hUH hx
  set ψU := ψ.comp U'.subtype with hψU
  set ψH := ψ.comp H'.subtype with hψH
  have hkerψU : Nat.card ψU.ker = Nat.card ψ.ker := by
    have e : ψU.ker = ψ.ker.subgroupOf U' := by
      ext x
      simp [hψU, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkU).toEquiv]
  have hkerψH : Nat.card ψH.ker = Nat.card ψ.ker := by
    have e : ψH.ker = ψ.ker.subgroupOf H' := by
      ext x
      simp [hψH, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hkU.trans hU'H')).toEquiv]
  have h1 := Subgroup.card_ker_mul_card_range ψU
  have h2 := Subgroup.card_ker_mul_card_range ψH
  rw [hkerψU, hcU] at h1
  rw [hkerψH, hcH] at h2
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hrel : Nat.card ψH.range = 5 * Nat.card ψU.range := by
    have : Nat.card ψ.ker * Nat.card ψH.range = Nat.card ψ.ker * (5 * Nat.card ψU.range) := by
      rw [h2, mul_left_comm, h1]
    exact Nat.eq_of_mul_eq_mul_left hkpos this
  have hU2 : IsPGroup 2 U' :=
    (isPGroup_unitriangular_charTwo (K := K) (n := 5) (by norm_num)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hUQ).symm
  have hrU2 : IsPGroup 2 ψU.range := by
    rw [MonoidHom.range_eq_map]
    exact (hU2.of_equiv Subgroup.topEquiv.symm).map ψU
  obtain ⟨j, hj⟩ := hrU2.exists_card_eq
  have hGL : Nat.card (GL (Fin 4) K) = 2 ^ 6 * 315 := by
    rw [card_GL_eq, hK]
    decide
  have hj6 : j = 6 := by
    have hge : 2 ^ 6 ≤ 2 ^ j := by
      rw [← hj]
      have : 2 ^ 10 ≤ 2 ^ 4 * Nat.card ψU.range := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ hker4
      omega
    have hle : 2 ^ j ∣ 2 ^ 6 * 315 := by
      rw [← hj, ← hGL]
      exact Subgroup.card_subgroup_dvd_card _
    have hj1 : 6 ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
    by_contra hne
    have hj7 : 2 ^ 7 ∣ 2 ^ 6 * 315 := (Nat.pow_dvd_pow 2 (by omega)).trans hle
    norm_num at hj7
  have hSyl : IsSylowTwoOf ψU.range ⊤ := by
    refine ⟨le_top, hrU2, ?_⟩
    show ¬ 2 ∣ ψU.range.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have hi := Subgroup.card_mul_index ψU.range
    rw [hj, hj6, hGL] at hi
    have : ψU.range.index = 315 := by omega
    rw [this]
    decide
  have hle : ψU.range ≤ ψH.range := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact ⟨⟨u, hU'H' hu⟩, rfl⟩
  exact noFiveOver_gl4_614 hK _ _ hSyl hle hrel

theorem false_of_stab_one614 [CharP K 2] (hK : Nat.card K = 2)
    {H : Subgroup (SpecialLinearGroup (Fin 5) K)} (hUH : unitriangular 5 K ≤ H)
    (hHQ : H ≤ stabilizer (flagSpace 5 K 1)) (hcard : Nat.card H = 5 * 2 ^ 10) : False := by
  classical
  set Q := stabilizer (flagSpace 5 K 1) with hQ
  have hLD : BlockLeft Q 1 4 := blockLeft_of_stabilizer fun g hg => hg
  have hRD : BlockRight Q 1 4 := blockRight_top Q (by norm_num)
  set ψ : ↥Q →* GL (Fin 4) K := (blkMon Q 1 4 (by norm_num) hLD hRD).toHomUnits with hψ
  have hblk : ∀ x : ↥Q, ψ x = 1 →
      blkAt 1 4 (by norm_num) ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 :=
    fun x hx => congrArg Units.val hx
  have hkerU : ∀ x : ↥Q, ψ x = 1 → (x : SpecialLinearGroup (Fin 5) K) ∈ unitriangular 5 K := by
    intro x hx
    have h00 : ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0 = 1 := by
      rcases eq_zero_or_eq_one_of_card_two hK
          (((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0) with h | h
      · exfalso
        have hdet : ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 0 := by
          refine Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_
          by_cases hi : i = 0
          · rw [hi]
            exact h
          · exact stabilizer_entries x.2 (by simp) (by
              have : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
              omega)
        rw [(x : SpecialLinearGroup (Fin 5) K).2] at hdet
        exact one_ne_zero hdet
      · exact h
    have hA : blkAt 0 1 (by norm_num)
        ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [blkAt_apply] using h00
    exact mem_unitriangular_of_two_blocks614 (d := 1) le_rfl (by norm_num) x.2 hA (hblk x hx)
  have hker4 : Nat.card ψ.ker ≤ 2 ^ 4 := by
    have hinj : Function.Injective (fun x : ↥ψ.ker => fun j : Fin 4 =>
        (((x : ↥Q) : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 j.succ) := by
      intro x y hxy
      have hxU := hkerU x x.2
      have hyU := hkerU y y.2
      have hxD := hblk x x.2
      have hyD := hblk y y.2
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · rw [hxU.2 0, hyU.2 0]
      · exact congrFun hxy j
      · rw [hxU.1 _ _ (Fin.succ_pos i), hyU.1 _ _ (Fin.succ_pos i)]
      · have h1 := congrFun (congrFun hxD i) j
        have h2 := congrFun (congrFun hyD i) j
        simp only [blkAt_apply] at h1 h2
        have ei : (⟨1 + (i : ℕ), by omega⟩ : Fin 5) = i.succ := Fin.ext (by simp [add_comm])
        have ej : (⟨1 + (j : ℕ), by omega⟩ : Fin 5) = j.succ := Fin.ext (by simp [add_comm])
        rw [ei, ej] at h1 h2
        rw [h1, h2]
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fun, Nat.card_fin, hK] at h
  exact false_of_levi614 hK ψ hUH hHQ hcard hkerU hker4

theorem false_of_stab_four614 [CharP K 2] (hK : Nat.card K = 2)
    {H : Subgroup (SpecialLinearGroup (Fin 5) K)} (hUH : unitriangular 5 K ≤ H)
    (hHQ : H ≤ stabilizer (flagSpace 5 K 4)) (hcard : Nat.card H = 5 * 2 ^ 10) : False := by
  classical
  set Q := stabilizer (flagSpace 5 K 4) with hQ
  have hLA : BlockLeft Q 0 4 := blockLeft_zero Q 4
  have hRA : BlockRight Q 0 4 := blockRight_of_stabilizer (a := 0) (m := 4) fun g hg => by
    rw [zero_add]
    exact hg
  set ψ : ↥Q →* GL (Fin 4) K := (blkMon Q 0 4 (by norm_num) hLA hRA).toHomUnits with hψ
  have hblk : ∀ x : ↥Q, ψ x = 1 →
      blkAt 0 4 (by norm_num) ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 :=
    fun x hx => congrArg Units.val hx
  have hkerU : ∀ x : ↥Q, ψ x = 1 → (x : SpecialLinearGroup (Fin 5) K) ∈ unitriangular 5 K := by
    intro x hx
    have h44 : ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by
      rcases eq_zero_or_eq_one_of_card_two hK
          (((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4) with h | h
      · exfalso
        have hdet : ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 0 := by
          refine Matrix.det_eq_zero_of_row_eq_zero 4 fun j => ?_
          by_cases hj : j = 4
          · rw [hj]
            exact h
          · exact stabilizer_entries x.2 (by
              have : (j : ℕ) ≠ 4 := fun h4 => hj (Fin.ext h4)
              omega) (by simp)
        rw [(x : SpecialLinearGroup (Fin 5) K).2] at hdet
        exact one_ne_zero hdet
      · exact h
    have hD : blkAt 4 (5 - 4) (by norm_num)
        ((x : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [blkAt_apply] using h44
    exact mem_unitriangular_of_two_blocks614 (d := 4) (by norm_num) (by norm_num) x.2 (hblk x hx) hD
  have hker4 : Nat.card ψ.ker ≤ 2 ^ 4 := by
    have hinj : Function.Injective (fun x : ↥ψ.ker => fun i : Fin 4 =>
        (((x : ↥Q) : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i.castSucc 4) := by
      intro x y hxy
      have hxU := hkerU x x.2
      have hyU := hkerU y y.2
      have hxA := hblk x x.2
      have hyA := hblk y y.2
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      ext i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hxU.2 (Fin.last 4), hyU.2 (Fin.last 4)]
      · rw [hxU.1 _ _ (Fin.castSucc_lt_last j), hyU.1 _ _ (Fin.castSucc_lt_last j)]
      · exact congrFun hxy i
      · have h1 := congrFun (congrFun hxA i) j
        have h2 := congrFun (congrFun hyA i) j
        simp only [blkAt_apply] at h1 h2
        have ei : (⟨0 + (i : ℕ), by omega⟩ : Fin 5) = i.castSucc := Fin.ext (by simp)
        have ej : (⟨0 + (j : ℕ), by omega⟩ : Fin 5) = j.castSucc := Fin.ext (by simp)
        rw [ei, ej] at h1 h2
        rw [h1, h2]
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fun, Nat.card_fin, hK] at h
  exact false_of_levi614 hK ψ hUH hHQ hcard hkerU hker4

theorem false_of_five_over_unitriangular614 [CharP K 2]
    (hK : Nat.card K = 2) {H : Subgroup (SpecialLinearGroup (Fin 5) K)}
    (hUH : unitriangular 5 K ≤ H) (hcard : Nat.card H = 5 * 2 ^ 10) : False := by
  classical
  have hSL : Nat.card (SpecialLinearGroup (Fin 5) K) = 9999360 := by
    rw [card_SL_eq (by norm_num), hK]
    decide
  have hne : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hSL] at hcard
    norm_num at hcard
  have hinj : Function.Injective (proj 5 K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_bot_of_card_two hK]
  have hne' : H.map (proj 5 K) ≠ ⊤ := by
    intro h
    apply hne
    rw [← Subgroup.comap_map_eq_self_of_injective hinj H, h, Subgroup.comap_top]
  obtain ⟨M, hHM, hM⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hne')
  have hBM : projUpperTriangular 5 K ≤ M :=
    (Subgroup.map_mono ((upperTriangular_le_unitriangular hK).trans hUH)).trans hHM
  obtain ⟨d, hd1, hd5, rfl⟩ := eq_projStabilizer_of_isCoatom hM.isCoatom hBM
  have hHQ : H ≤ stabilizer (flagSpace 5 K d) := by
    rw [← comap_projStabilizer]
    exact (Subgroup.le_comap_map _ _).trans (Subgroup.comap_mono hHM)
  interval_cases d
  · exact false_of_stab_one614 hK hUH hHQ hcard
  · exact not_five_dvd_card_stabilizer614 hK (Or.inl rfl)
      ((dvd_mul_right 5 _).trans (hcard ▸ Subgroup.card_dvd_of_le hHQ))
  · exact not_five_dvd_card_stabilizer614 hK (Or.inr rfl)
      ((dvd_mul_right 5 _).trans (hcard ▸ Subgroup.card_dvd_of_le hHQ))
  · exact false_of_stab_four614 hK hUH hHQ hcard

theorem noFiveOver_sl5_614 [CharP K 2] (hK : Nat.card K = 2) :
    FiveNorm.NoFiveOver (SpecialLinearGroup (Fin 5) K) := by
  classical
  intro S H hS hSH hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 5) (by norm_num)
  obtain ⟨h1, h2⟩ := FiveNorm.isSylowTwoOf_top_index hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 5) K) (h1.toSylow h2) P
  have hSk : Nat.card S = 2 ^ 10 := by
    have e1 := Sylow.card_eq_multiplicity (h1.toSylow h2)
    have e2 := Sylow.card_eq_multiplicity P
    have e3 : Nat.card (P : Subgroup (SpecialLinearGroup (Fin 5) K)) = 2 ^ 10 := by
      rw [hP, card_unitriangular, hK]
    exact e1.trans (e2.symm.trans e3)
  have hUH : unitriangular 5 K ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : x ∈ ((g • h1.toSylow h2 : Sylow 2 (SpecialLinearGroup (Fin 5) K)) :
        Subgroup (SpecialLinearGroup (Fin 5) K)) := by
      rw [hg, hP]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hSH hy, rfl⟩
  refine false_of_five_over_unitriangular614 hK hUH ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hSk]

theorem noFiveOver_psl52_614 {W : Type} [Group W] [Finite W]
    (h : StatedClassicalModel W .PSL 5 2 1) : FiveNorm.NoFiveOver W := by
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  exact noFiveOver_of_mulEquiv614
    ((e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 5 K)).trans
      (slEquivProj hK2 5).symm) (noFiveOver_sl5_614 hK2)

end L52

theorem kg614FiveChar2_holds
    : KG614FiveChar2 :=
  kg614FiveChar2_of_L52 fun _ _ _ h => fiveOverNorm614_of_noFiveOver (noFiveOver_psl52_614 h)

theorem kg614Five_of_L3_J4
    (hlist : A23SQTKListFact) (hcat : CatalogStepFact) (h3 : KG614FiveL3)
    (hJ4 : FiveNorm.NoFiveOver (CFSG.Blueprint.NativeSporadic.Carrier .J4)) : KG614Five :=
  kg614Five_of_L2 hlist hcat h3 kg614FiveChar2_holds (kg614FiveSpor_of_J4 hJ4)

end CFSG.Quasithin.H13
