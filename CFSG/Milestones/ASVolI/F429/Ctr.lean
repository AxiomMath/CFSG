module

public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutLieMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSyl

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.H13.F431

@[expose] def burnsideF429_m_UnCenterProp (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D .PSU m 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T N : Subgroup ↥A.K) (z : ↥A.K), IsSylowTwoOf T ⊤ ∧ T ≤ A.Mb1 ∧ T ≤ A.Mb2 ∧
      ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w

theorem burnsideF429_m_unCenterProp_of_outLie {m f : ℕ} (h : F431UnOutLieProp m f) :
    burnsideF429_m_UnCenterProp m f := by
  intro D _ hD A hev
  obtain ⟨T, S, g, z, t, V, hO | hO⟩ := h D hD A hev
  · exact ⟨T, A.Mb1, z, hO.sylow, hO.T_le, hO.T_le', hO.center_T⟩
  · exact ⟨T, A.Mb2, z, hO.sylow, hO.T_le', hO.T_le, hO.center_T⟩

open CFSG.Quasithin.H13.F431.D4q.Struct

@[expose] def burnsideF429_m_UnCenterConcl {D : Type} [Group D] (A : LieAmalgamExt D) : Prop :=
  ∃ (T N : Subgroup ↥A.K) (z : ↥A.K), IsSylowTwoOf T ⊤ ∧ T ≤ A.Mb1 ∧ T ≤ A.Mb2 ∧
    ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w

theorem burnsideF429_m_unCenterConcl_of_kiso {D D' : Type} [Group D] [Group D']
    {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A') :
    burnsideF429_m_UnCenterConcl A' → burnsideF429_m_UnCenterConcl A := by
  rintro ⟨T', N', z', hT, h1, h2, hc⟩
  set θ : ↥A'.K ≃* ↥A.K := L.ψ.symm with hθ
  refine ⟨T'.map θ.toMonoidHom, N'.map θ.toMonoidHom, θ z', ?_, ?_, ?_, ?_⟩
  · have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv θ).2 hT
    rwa [Subgroup.map_top_of_surjective _ θ.surjective] at h
  · rw [← L.map_Mb1]
    exact Subgroup.map_mono h1
  · rw [← L.map_Mb2]
    exact Subgroup.map_mono h2
  · intro w hw hcw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨m, hm, e⟩ := hc w₀ hw₀ (fun y hy => by
      apply θ.injective
      simpa using hcw (θ y) (Subgroup.mem_map_of_mem _ hy)) (fun h => hw1 (by simp [h]))
    exact ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩

theorem burnsideF429_m_unCenterConcl_of_model {D : Type} [Group D] (A : LieAmalgamExt D)
    {T : Subgroup (MulAut D)} {z : MulAut D} (hT : IsSylowTwoOf T A.K)
    (h1 : T ≤ autStab A.P1) (h2 : T ≤ autStab A.P2) (hz : z ∈ A.K)
    (hc : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ A.K, m * z * m⁻¹ = w) :
    burnsideF429_m_UnCenterConcl A := by
  have hTK : T ≤ A.K := hT.1
  refine ⟨T.subgroupOf A.K, ⊤, ⟨z, hz⟩, ?_, ?_, ?_, ?_⟩
  · have := (sub_isSylowTwoOf_iff A.K hTK le_rfl).2 hT
    rwa [Subgroup.subgroupOf_self] at this
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨A.K_le_Mbar (hTK hx), h1 hx⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨A.K_le_Mbar (hTK hx), h2 hx⟩
  · intro w hw hcw hw1
    rw [Subgroup.mem_subgroupOf] at hw
    obtain ⟨m, hm, e⟩ := hc (w : MulAut D) hw (fun y hy => by
      have := hcw ⟨y, hTK hy⟩ (by rw [Subgroup.mem_subgroupOf]; exact hy)
      exact congrArg Subtype.val this) (fun h => hw1 (Subtype.ext h))
    exact ⟨⟨m, hm⟩, Subgroup.mem_top _, Subtype.ext e⟩

end CFSG.Quasithin.H13.F431.Un

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.Un

theorem burnsideF429_m_exists_model_yamStd {D : Type} [Group D] {f : ℕ} (hf1 : 1 ≤ f)
    (hD : CFSG.Blueprint.LieModel D .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (_ : CharP K 2),
      IsSimpleGroup (Xg h) ∧ Nonempty (D ≃* Xg h) ∧
      CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨hS, hY⟩ := yamStd_of_eps hF (brFD hF hf1) (brEps hF hf1) (brEps_map_Psy hF hf1)
  exact ⟨F, inferInstance, brFD hF hf1, inferInstance, hS,
    ⟨e.symm.trans (brEps hF hf1).symm⟩, hY⟩

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem burnsideF429_m_center_Ssd_le (F₂ : Subgroup (K ≃+* K)) (w : MulAut (Xg h))
    (hw : w ∈ Ssd h (Psy h) (fStab_Psy h) F₂)
    (hc : ∀ y ∈ Ssd h (Psy h) (fStab_Psy h) F₂, y * w = w * y) :
    w ∈ Ssd h (ZX h) (fStab_ZX h) ⊥ := by
  have hfix : ∀ u ∈ Psy h, w u = u :=
    fun u hu => fix_of_comm_cj h (fun u hu => (hc _ (cj_mem_Ssd h hu)).symm) hu
  obtain ⟨a, haA, rfl⟩ := (fixes_miyamotoZ2_iff h w).1 fun g hg =>
    hfix g (miyamotoA1_le_P h (miyamotoZ2_le_A1 h hg))
  have haP : (a : GL (Fin 4) K) ∈ miyamotoP h := miyamotoA1_le_P h haA
  have haZ : (a : GL (Fin 4) K) ∈ miyamotoZ h := by
    rw [← centerIn_miyamotoP]
    refine ⟨haP, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyX : y ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false false hy
    have e := hfix ⟨y, hyX⟩ hy
    have e2 : a * ⟨y, hyX⟩ = ⟨y, hyX⟩ * a := by
      rw [MulAut.conj_apply] at e
      have := congrArg (fun x => x * a) e
      simpa [mul_assoc] using this
    exact (congrArg Subtype.val e2).symm
  exact cj_mem_Ssd h haZ

theorem burnsideF429_m_ZX_eq_of_q2 (hf : f = 1) {a : Xg h} (ha : a ∈ ZX h) (ha1 : a ≠ 1) :
    a = z1X h := by
  obtain ⟨d, hd, e⟩ := (mem_Z h).1 (show (a : GL (Fin 4) K) ∈ miyamotoZ h from ha)
  have hd2 : d ^ 2 = d := by
    rw [UnitaryFieldData.bar_apply, hf, pow_one] at hd
    exact hd
  have h3 : d * (d - 1) = 0 := by linear_combination hd2
  rcases mul_eq_zero.1 h3 with h0 | h1
  · subst h0
    exact absurd (Subtype.ext (e.trans (miyamotoXGL_zero h))) ha1
  · have : d = 1 := sub_eq_zero.1 h1
    subst this
    exact Subtype.ext (e.trans (coe_z1X h).symm)

theorem burnsideF429_m_Ssd_le_autStab_Pt [IsSimpleGroup (Xg h)] (hPt : IsCoatom (Pt h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)} (hF : F₂ ≤ FK h K₀) :
    Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab (Pt h) := by
  intro x hx
  have hx' : x ∈ Ssd h (Pt h) (fStab_Pt h) (FK h K₀) := Ssd_mono h (Psy_le_Pt h) hF hx
  rw [← inf_autStab_Pt h hPt hinn] at hx'
  exact hx'.2

theorem burnsideF429_m_Ssd_le_autStab_Ln [IsSimpleGroup (Xg h)] (hLn : IsCoatom (Ln h))
    {K₀ : Subgroup (MulAut (Xg h))} (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)} (hF : F₂ ≤ FK h K₀) :
    Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab (Ln h) := by
  intro x hx
  have hx' : x ∈ Ssd h (Ln h) (fStab_Ln h) (FK h K₀) := Ssd_mono h (Psy_le_Ln h) hF hx
  rw [← inf_autStab_Ln h hLn hinn] at hx'
  exact hx'.2

end CFSG.Quasithin.H13.F431.Un.OL

namespace CFSG.Quasithin.H13.F431.Un

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Un.OL
  CFSG.Quasithin.H13.F431.D4q.Struct

theorem burnsideF429_m_unCenterProp_four_one : burnsideF429_m_UnCenterProp 4 1 := by
  intro D _ hD A _
  obtain ⟨K, _, h, _, _, ⟨e⟩, hY⟩ := burnsideF429_m_exists_model_yamStd le_rfl hD
  obtain ⟨A', hTD, hP, ⟨L⟩⟩ := exists_unNormalized h hY e A
  have hsup : A'.P1 ⊔ A'.P2 = ⊤ := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
    · rw [h1, h2, sup_comm]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
  have hinn := A'.range_conj_le_K hsup
  have := finite_aut h
  obtain ⟨F₂, hF₂⟩ := exists_isSylowTwoOf (FK h A'.K)
  have hsyl := isSylowTwoOf_Ssd_Psy h hinn hF₂
  have hPt := burnsideF429_m_Ssd_le_autStab_Pt h hY.coatom₀ hinn hF₂.1
  have hLn := burnsideF429_m_Ssd_le_autStab_Ln h hY.coatom₁ hinn hF₂.1
  have hT1 : Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab A'.P1 := by
    rcases hP with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    exacts [hPt, hLn]
  have hT2 : Ssd h (Psy h) (fStab_Psy h) F₂ ≤ autStab A'.P2 := by
    rcases hP with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    exacts [hLn, hPt]
  refine burnsideF429_m_unCenterConcl_of_kiso L
    (burnsideF429_m_unCenterConcl_of_model A' hsyl hT1 hT2 (hinn ⟨z1X h, rfl⟩) ?_)
  intro w hw hc hw1
  obtain ⟨a, ha, φ, hφ, rfl⟩ := burnsideF429_m_center_Ssd_le h F₂ w hw hc
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one] at hw1 ⊢
  have ha1 : a ≠ 1 := fun e => hw1 (by rw [e, cj_one])
  rw [burnsideF429_m_ZX_eq_of_q2 h rfl ha ha1]
  exact ⟨1, A'.K.one_mem, by rw [one_mul, inv_one, mul_one]⟩

theorem burnsideF429_m_unCenterProp_four_all (f : ℕ) : burnsideF429_m_UnCenterProp 4 f := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · interval_cases f
    · intro D _ hD
      exact absurd hD.admissible.2.1 (by norm_num)
    · exact burnsideF429_m_unCenterProp_four_one
  · exact burnsideF429_m_unCenterProp_of_outLie (f431UnOutLieProp_four f hf)

end CFSG.Quasithin.H13.F431.Un

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K]

theorem burnsideF429_m_twoCentralizerV (h : UnitaryFieldData 2 f K)
    (hZ : center (hypPSU h 2 1) = ⊥) (ρ : MulAut (hypPSU h 2 1))
    (hρk : ∃ k : ℕ, ρ ^ 2 ^ k = 1) (hρ : ∀ w ∈ Vh h, ρ * w = w * ρ) : ρ ∈ Sh h := by
  obtain ⟨k, hk⟩ := hρk
  obtain ⟨x, hxL, hx, hE, hF⟩ := lam_lift_of_central hZ hρ
  have hxk : x ^ 2 ^ k = 1 :=
    Phi_injOn_Lam (pow_mem hxL _) (one_mem _) (by rw [map_pow, hx, hk, map_one])
  have hzz : lmat x (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
    have h1 : (psiL h ⟨x, hxL⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxL⟩ : Lam h) ^ 2 ^ k = 1 := Subtype.ext hxk
      rw [this, map_one]
    exact eq_one_of_pow_two_pow_eq_one h h1
  obtain ⟨hxr, hxP, -⟩ := hxL
  have hP1 : blkP (lmat x) = 1 := by
    ext a b
    fin_cases a; fin_cases b
    exact hzz
  have hA : lmat x = blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1 := by
    have h1 := eq_blk3_of_para hxP
    have hEA : blkA (lmat x) = 1 := hE
    have hFD : blkD (lmat x) = 1 := hF
    rwa [hEA, hFD, hP1] at h1
  obtain ⟨ν, -, -, hgram⟩ := x.2
  have hg' : ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = ν • hypGram 2 1 K := hgram
  rw [hA] at hg'
  have hν : ν = 1 := by
    have e := congrFun (congrFun hg' (.inl 0)) (.inr (.inr 0))
    simp [Fintype.sum_sum_type, Matrix.mul_apply, hypGram] at e
    exact e.symm
  have hgram' : ((blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1).map h.bar)ᵀ *
      hypGram 2 1 K * blk3 1 (blkX (lmat x)) (blkY (lmat x)) 1 (blkQ (lmat x)) 1 =
        hypGram 2 1 K := by
    rw [hg', hν, one_smul]
  rw [blk3_gram_iff] at hgram'
  obtain ⟨-, -, hXQ, hYQ⟩ := hgram'
  set X := blkX (lmat x)
  set Y := blkY (lmat x)
  set Q := blkQ (lmat x)
  have hQ : Q = -(X.map h.bar)ᵀ := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
      Matrix.mul_one] at hXQ
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hXQ
  set v : Fin 2 → K := fun i => X i 0 with hv
  have hXv : X = replicateCol (Fin 1) v := by
    ext i l
    fin_cases l
    rfl
  have hQv : Q = replicateRow (Fin 1) fun j => -h.bar (v j) := by
    ext l j
    fin_cases l
    rw [hQ]
    simp [hv]
  have hcon : Y + (Y.map h.bar)ᵀ = -vecMulVec v fun j => h.bar (v j) := by
    have := h.charP
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.one_mul] at hYQ
    rw [hQv] at hYQ
    ext i j
    have e := congrFun (congrFun hYQ i) j
    simp [Matrix.mul_apply, vecMulVec, h.bar_bar] at e ⊢
    linear_combination e
  have hAN : lmat x = oddUni h v Y := by
    rw [hA, hXv, hQv]
    rfl
  obtain ⟨g, hg, hgm⟩ := exists_mem_Ssub hcon
  have hxg : x = inlG g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Units.ext
      change lmat x = mat g
      rw [hgm, hAN]
    · rw [hxr]
      rfl
  rw [← hx, hxg, Phi_inlG]
  exact ⟨g, hg, rfl⟩

end CFSG.LocalAnalysis.EvenBN.U5

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.F431.Un CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Blueprint CFSG.Open CFSG.Quasithin.H13.F431.D4q.Struct

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Center

include h in
theorem burnsideF429_m_center_T5 {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)}
    (hT2 : IsPGroup 2 ↥(Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂))
    {w : MulAut (hypPSU h 2 1)} (hw : w ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
    (hc : ∀ y ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂, y * w = w * y)
    (hw1 : w ≠ 1) :
    ∃ m ∈ K₀ ⊓ autStab (u5PtP h), m * cj5 h (z5Y h) * m⁻¹ = w := by
  have hZ := u5_center_eq_bot h
  have hinj := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ
  obtain ⟨k, hk⟩ := hT2 ⟨w, hw⟩
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hVT : ∀ v ∈ Vh h, v ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ := by
    intro v hv
    have : v ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ := by
      rw [Ssd5_bot_eq_Uh]
      exact Sh_le_Uh (Vh_le_Sh hv)
    exact Ssd5_mono h le_rfl bot_le this
  have hwS : w ∈ Sh h :=
    burnsideF429_m_twoCentralizerV h hZ w ⟨k, hk'⟩ (fun v hv => (hc v (hVT v hv)).symm)
  obtain ⟨g, hg, rfl⟩ := hwS
  set y : hypPSU h 2 1 := hypProj h 2 1 g with hy
  have hyU : y ∈ hypProjUnitriangular h 2 1 := ⟨g, Ssub_le_Usub hg, rfl⟩
  have hcomm : ∀ u ∈ hypProjUnitriangular h 2 1, u * y = y * u := by
    intro u hu
    have hcu : cj5 h u ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ :=
      cj5_mem_Ssd5 h hu
    have := hc _ hcu
    apply hinj
    rw [map_mul, map_mul]
    exact this
  have hy1 : y ≠ 1 := fun e => hw1 (by
    change MulAut.conj y = 1
    rw [e, map_one])
  obtain ⟨b, hb, e⟩ := center_Y hyU hcomm hy1
  refine ⟨cj5 h b, ⟨hinn ⟨b, rfl⟩, cj5_mem_autStab h hb.1⟩, ?_⟩
  rw [← cj5_inv, ← cj5_mul, ← cj5_mul, e]
  rfl

end Center

section Normalize

include h in
@[expose] def burnsideF429_m_F2 : Subgroup (K ≃+* K) where
  carrier := {φ | ∃ k : ℕ, φ ^ 2 ^ k = 1}
  mul_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨i + j, ?_⟩
    have ha : a ^ 2 ^ (i + j) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
    have hb : b ^ 2 ^ (i + j) = 1 := by rw [add_comm, pow_add, pow_mul, hj, one_pow]
    rw [Commute.mul_pow (fld5_comm h a b), ha, hb, one_mul]
  one_mem' := ⟨0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨i, hi⟩
    exact ⟨i, by rw [inv_pow, hi, inv_one]⟩

theorem burnsideF429_m_isPGroup_F2 : IsPGroup 2 (burnsideF429_m_F2 h) := by
  rintro ⟨φ, k, hk⟩
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

@[expose] def burnsideF429_m_Q5 : Subgroup (MulAut (hypPSU h 2 1)) :=
  Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) (burnsideF429_m_F2 h)

include h in
theorem burnsideF429_m_isPGroup_Q5 : IsPGroup 2 (burnsideF429_m_Q5 h) := by
  have := h.finite
  have := finite_hypPSU_five h
  have := fld5_finite h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 (u5_sylow h).2.1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 (burnsideF429_m_isPGroup_F2 h)
  rw [IsPGroup.iff_card]
  exact ⟨a + b, by rw [burnsideF429_m_Q5, card_Ssd5 h (u5_center_eq_bot h), ha, hb, pow_add]⟩

include h in
theorem burnsideF429_m_Q5_sylow :
    IsSylowTwoOf (burnsideF429_m_Q5 h) (autStab (hypProjUnitriangular h 2 1)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := hypProjUnitriangular h 2 1 with hU
  set G₁ := autStab U with hG₁
  have hQ2 := burnsideF429_m_isPGroup_Q5 h
  have hQle : burnsideF429_m_Q5 h ≤ G₁ := Ssd5_le_autStab h (fStab5_U h) le_rfl _
  refine ⟨hQle, hQ2, ?_⟩
  set Q₀ : Subgroup ↥G₁ := (burnsideF429_m_Q5 h).subgroupOf G₁ with hQ₀
  have hQ₀p : IsPGroup 2 Q₀ := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
  obtain ⟨P, hP⟩ := hQ₀p.exists_le_sylow
  have hker : ∀ y : MulAut (hypPSU h 2 1), y ∈ Dlin h ↔ QuotientGroup.mk' (Dlin h) y = 1 :=
    fun y => by rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have key : (P : Subgroup ↥G₁) ≤ Q₀ := by
    intro x hx
    have hxU : ∀ y, x.1 y ∈ U ↔ y ∈ U := fun y => (x.2 y).symm
    obtain ⟨e, he, σ', ⟨σ, hσ⟩, hxe⟩ := u5_normal_form h x.1 hxU
    subst hσ
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨x, hx⟩ : (P : Subgroup ↥G₁))
    have hxk : x.1 ^ 2 ^ k = 1 := by
      have h1 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow] at h2
    have hσD : fieldP h (σ ^ 2 ^ k) ∈ Dlin h := by
      have hq : QuotientGroup.mk' (Dlin h) (fieldP h σ) = QuotientGroup.mk' (Dlin h) x.1 := by
        rw [hxe, map_mul, (hker e).1 (Eext_le_Dlin h he), one_mul]
      rw [hker, map_pow, map_pow, hq, ← map_pow, hxk, map_one]
    have hσF : σ ∈ burnsideF429_m_F2 h := ⟨k, fa5_mem_Dlin h hσD⟩
    set s : ↥G₁ := ⟨fa5 h σ, fa5_mem_autStab h (fStab5_U h) σ⟩ with hs
    have hsQ : s ∈ Q₀ := fa5_mem_Ssd5 h (hB := fStab5_U h) hσF
    have hsP : s ∈ (P : Subgroup ↥G₁) := hP hsQ
    set e' : ↥G₁ := x * s⁻¹ with he'
    have he'P : e' ∈ (P : Subgroup ↥G₁) := P.mul_mem hx (P.inv_mem hsP)
    have he'val : (e' : MulAut (hypPSU h 2 1)) = e := by
      change x.1 * (fa5 h σ)⁻¹ = e
      rw [hxe]
      group
    obtain ⟨k', hk'⟩ := P.isPGroup' (⟨e', he'P⟩ : (P : Subgroup ↥G₁))
    have hek : e ^ 2 ^ k' = 1 := by
      have h1 : e' ^ 2 ^ k' = 1 := congrArg Subtype.val hk'
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, he'val] at h2
    obtain ⟨u, hu, hue⟩ := (borelAutDiag_u5 h).E_two e he k' hek
    have he'Q : e' ∈ Q₀ := by
      change (e' : MulAut (hypPSU h 2 1)) ∈ burnsideF429_m_Q5 h
      rw [he'val, hue]
      exact cj5_mem_Ssd5 h (hB := fStab5_U h) hu
    have : x = e' * s := by rw [he']; group
    rw [this]
    exact Q₀.mul_mem he'Q hsQ
  have hPQ : Q₀ = (P : Subgroup ↥G₁) := le_antisymm hP key
  have := P.not_dvd_index
  rwa [← hPQ] at this

include h in
theorem burnsideF429_m_exists_conj_into_Q5 {R : Subgroup (MulAut (hypPSU h 2 1))}
    (hR : IsPGroup 2 R) (hRU : R ≤ autStab (hypProjUnitriangular h 2 1)) :
    ∃ g ∈ autStab (hypProjUnitriangular h 2 1), ∀ y ∈ R, g⁻¹ * y * g ∈ burnsideF429_m_Q5 h := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  exact aut5_exists_conj (burnsideF429_m_isPGroup_Q5 h) (burnsideF429_m_Q5_sylow h).2.2 hRU hR

include h in
theorem burnsideF429_m_exists_normalized5 {K' : Subgroup (MulAut (hypPSU h 2 1))}
    (hinn : Pi h ≤ K') :
    ∃ g ∈ autStab (hypProjUnitriangular h 2 1), ∃ F₂ : Subgroup (K ≃+* K),
      IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
        (K'.map (MulAut.conj g).toMonoidHom) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have hZ := u5_center_eq_bot h
  set U := hypProjUnitriangular h 2 1 with hU
  have hUh_le : Uh h ≤ K' := Uh_le_Pi.trans hinn
  have hUhQ : Uh h ≤ burnsideF429_m_Q5 h := by
    rw [← Ssd5_bot_eq_Uh h]
    exact Ssd5_mono h le_rfl bot_le
  have hUh2 : IsPGroup 2 (Uh h) := (burnsideF429_m_isPGroup_Q5 h).to_le hUhQ
  obtain ⟨T, hUT, hT⟩ := exists_isSylowTwoOf_of_le hUh_le hUh2
  have hTPi : T ⊓ Pi h = Uh h :=
    (isSylowTwoOf_Uh h).eq_of_le (le_inf hUT Uh_le_Pi) inf_le_right
      (hT.isPGroup.to_le inf_le_left)
  have hTU : ∀ α ∈ T, ∀ x ∈ U, α x ∈ U := by
    intro α hα x hx
    have h1 : cj5 h x ∈ Uh h := by
      rw [Uh_eq_map]
      exact ⟨x, hx, rfl⟩
    have h2 : α * cj5 h x * α⁻¹ ∈ T := T.mul_mem (T.mul_mem hα (hUT h1)) (T.inv_mem hα)
    have h3 : α * cj5 h x * α⁻¹ ∈ Pi h :=
      (inferInstance : (Pi h).Normal).conj_mem _ (Uh_le_Pi h1) α
    rw [aut5_mul_cj5_mul_inv] at h2 h3
    have h4 : cj5 h (α x) ∈ Uh h := hTPi ▸ ⟨h2, h3⟩
    rw [Uh_eq_map] at h4
    obtain ⟨y, hy, hyx⟩ := h4
    have : y = α x := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ hyx
    exact this ▸ hy
  have hTstab : T ≤ autStab U := fun α hα x => by
    refine ⟨hTU α hα x, fun hx => ?_⟩
    have := hTU α⁻¹ (T.inv_mem hα) (α x) hx
    simpa using this
  obtain ⟨g₀, hg₀, hconj⟩ := burnsideF429_m_exists_conj_into_Q5 h hT.isPGroup hTstab
  have hg : g₀⁻¹ ∈ autStab U := (autStab U).inv_mem hg₀
  set g : MulAut (hypPSU h 2 1) := g₀⁻¹ with hgdef
  set T' : Subgroup (MulAut (hypPSU h 2 1)) := T.map (MulAut.conj g).toMonoidHom with hT'
  have hmemT' : ∀ y, y ∈ T' ↔ g⁻¹ * y * g ∈ T := fun y => by
    rw [hT', Subgroup.mem_map_equiv]
    rfl
  have hT'Q : ∀ y ∈ T', y ∈ Ssd5 h U (fStab5_U h) ⊤ := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have := hconj y₀ hy₀
    have h1 : (MulAut.conj g).toMonoidHom y₀ ∈ burnsideF429_m_Q5 h := by
      simpa [hgdef, MulAut.conj_apply] using this
    exact Ssd5_mono h le_rfl le_top h1
  have hUh_T' : Uh h ≤ T' := by
    intro α hα
    rw [Uh_eq_map] at hα
    obtain ⟨s, hs, rfl⟩ := hα
    rw [hmemT']
    have hs' : g⁻¹ s ∈ U := ((autStab U).inv_mem hg s).1 hs
    have e : g⁻¹ * cj5 h s * g = cj5 h (g⁻¹ s) := by
      have := aut5_mul_cj5_mul_inv h g⁻¹ s
      rwa [inv_inv] at this
    rw [e]
    exact hUT (by rw [Uh_eq_map]; exact ⟨_, hs', rfl⟩)
  set F₂ : Subgroup (K ≃+* K) := T'.comap (fieldP h) with hF₂
  have hT'eq : T' = Ssd5 h U (fStab5_U h) F₂ := by
    ext α
    constructor
    · intro hα
      have hαQ : α ∈ Ssd5 h U (fStab5_U h) ⊤ := hT'Q α hα
      obtain ⟨s, hs, φ, -, rfl⟩ := hαQ
      have hcs : cj5 h s ∈ T' := hUh_T' (by rw [Uh_eq_map]; exact ⟨s, hs, rfl⟩)
      have : fa5 h φ ∈ T' := by
        have := T'.mul_mem (T'.inv_mem hcs) hα
        simpa using this
      exact ⟨s, hs, φ, this, rfl⟩
    · rintro ⟨s, hs, φ, hφ, rfl⟩
      have hcs : cj5 h s ∈ T' := hUh_T' (by rw [Uh_eq_map]; exact ⟨s, hs, rfl⟩)
      exact T'.mul_mem hcs hφ
  refine ⟨g, hg, F₂, ?_⟩
  rw [← hT'eq]
  exact IsSylowTwoOf.map_equiv (MulAut.conj g) hT

include h in
theorem burnsideF429_m_lab5_perm {g : MulAut (hypPSU h 2 1)}
    (hg : g ∈ autStab (hypProjUnitriangular h 2 1)) :
    ((u5PtP h).map g.toMonoidHom = u5PtP h ∧ (u5LnP h).map g.toMonoidHom = u5LnP h) ∨
      ((u5PtP h).map g.toMonoidHom = u5LnP h ∧ (u5LnP h).map g.toMonoidHom = u5PtP h) := by
  have hY := u5_yamStd (h := h)
  have hne : (u5PtP h).map g.toMonoidHom ≠ (u5LnP h).map g.toMonoidHom := fun e =>
    hY.ne (Subgroup.map_injective g.injective e)
  rcases lab5_map_eq h hg hY.coatom₀ hY.le₀ with h1 | h1 <;>
    rcases lab5_map_eq h hg hY.coatom₁ hY.le₁ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

include h in
theorem burnsideF429_m_un5_exists_normalized2 {A' : LieAmalgamExt (hypPSU h 2 1)}
    (hTD : A'.TD = hypProjUnitriangular h 2 1)
    (hP : (A'.P1 = u5PtP h ∧ A'.P2 = u5LnP h) ∨ (A'.P1 = u5LnP h ∧ A'.P2 = u5PtP h))
    (hinn : (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)).range ≤ A'.K) :
    ∃ A'' : LieAmalgamExt (hypPSU h 2 1), A''.TD = hypProjUnitriangular h 2 1 ∧
      ((A''.P1 = u5PtP h ∧ A''.P2 = u5LnP h) ∨ (A''.P1 = u5LnP h ∧ A''.P2 = u5PtP h)) ∧
      Nonempty (KIso A' A'') ∧ ∃ F₂ : Subgroup (K ≃+* K),
        IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) A''.K := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨g, hg, F₂, hsyl⟩ := burnsideF429_m_exists_normalized5 h (K' := A'.K) hinn
  have hgU : (hypProjUnitriangular h 2 1).map g.toMonoidHom = hypProjUnitriangular h 2 1 :=
    (AG.mem_autStab_iff_map_eq g _).1 hg
  have hperm := burnsideF429_m_lab5_perm h hg
  let E : LieExt (hypPSU h 2 1) A'.N1 A'.N2 := A'.toLieExt
  refine ⟨(E.congr g).toLieAmalgamExt, ?_, ?_, ⟨(E.congrOfLocIso g _ rfl).toKIso⟩, F₂, ?_⟩
  · show A'.TD.map g.toMonoidHom = _
    rw [hTD, hgU]
  · show (A'.P1.map g.toMonoidHom = _ ∧ A'.P2.map g.toMonoidHom = _) ∨
      (A'.P1.map g.toMonoidHom = _ ∧ A'.P2.map g.toMonoidHom = _)
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hperm with ⟨hgP, hgL⟩ | ⟨hgP, hgL⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inr ⟨rfl, rfl⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inr ⟨rfl, rfl⟩
    · rw [h1, h2, hgP, hgL]
      exact Or.inl ⟨rfl, rfl⟩
  · have hK0 := LieExt.congrOf_K E g (E.Mbar.map (MulAut.congr g).toMonoidHom) rfl
    have hK : (E.congr g).toLieAmalgamExt.K = A'.K.map (MulAut.conj g).toMonoidHom := by
      refine hK0.trans ?_
      congr 1
    rw [hK]
    exact hsyl

end Normalize

end CFSG.Quasithin.H13.F431.Un.OL5

namespace CFSG.Quasithin.H13.F431.Un

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Blueprint CFSG.Open
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.Un.OL5

section Main

theorem burnsideF429_m_unCenterProp_five_all (f : ℕ) : burnsideF429_m_UnCenterProp 5 f := by
  intro D _ hD A _
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_model5 hD
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hY := u5_yamStd (h := h)
  have hsupc : ∀ A₀ : LieAmalgamExt (hypPSU h 2 1),
      ((A₀.P1 = u5PtP h ∧ A₀.P2 = u5LnP h) ∨ (A₀.P1 = u5LnP h ∧ A₀.P2 = u5PtP h)) →
      A₀.P1 ⊔ A₀.P2 = ⊤ := by
    rintro A₀ (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
    · rw [h1, h2, sup_comm]
      exact hY.coatom₀.sup_eq_top_of_ne hY.coatom₁ hY.ne
  obtain ⟨A', hTD, hP, ⟨L1⟩⟩ := un5_exists_normalized hY e A
  have hinn := A'.range_conj_le_K (hsupc A' hP)
  obtain ⟨A'', -, hP'', ⟨L2⟩, F₂, hsyl⟩ := burnsideF429_m_un5_exists_normalized2 h hTD hP hinn
  have hinn'' : Pi h ≤ A''.K := A''.range_conj_le_K (hsupc A'' hP'')
  have hT1 : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ≤ autStab A''.P1 := by
    rcases hP'' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    exacts [Ssd5_le_autStab_Pt h F₂, Ssd5_le_autStab_Ln h F₂]
  have hT2 : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ≤ autStab A''.P2 := by
    rcases hP'' with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    exacts [Ssd5_le_autStab_Ln h F₂, Ssd5_le_autStab_Pt h F₂]
  refine burnsideF429_m_unCenterConcl_of_kiso L1 (burnsideF429_m_unCenterConcl_of_kiso L2
    (burnsideF429_m_unCenterConcl_of_model A'' hsyl hT1 hT2 (hinn'' ⟨z5Y h, rfl⟩) ?_))
  intro w hw hc hw1
  obtain ⟨m, hm, hme⟩ := burnsideF429_m_center_T5 h hinn'' hsyl.2.1 hw hc hw1
  exact ⟨m, hm.1, hme⟩

end Main

end CFSG.Quasithin.H13.F431.Un

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

theorem burnsideF429_jb_exists_two_elt {E : Type} [Group E] {H B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics 2 H B P₁ P₂) : ∃ x ∈ H, x ≠ 1 ∧ ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨⟨S, ⟨hSH, hSp, -⟩, hB⟩, -, -, hmax⟩ := hP
  obtain ⟨hBP1, hP1H, hP1ne, -⟩ := (hmax P₁).mpr (Or.inl rfl)
  by_contra hcon
  push Not at hcon
  have hS : S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hSp ⟨x, hx⟩
    exact hcon x (hSH hx) hx1 k (by rw [← Subgroup.orderOf_mk x hx]; exact hk)
  have hBH : B = H := by
    rw [hB, hS, Subgroup.normalizer_eq_top, inf_top_eq]
  exact hP1ne (le_antisymm hP1H (by rw [← hBH]; exact hBP1))

theorem burnsideF429_jb_parabolics (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Generic

variable {K : Type*} [Group K]

theorem burnsideF429_m_inf_normal_ne_bot [Finite K] {T I : Subgroup K} (hT : IsSylowTwoOf T ⊤)
    (hI : I.Normal) {j : K} (hj : j ∈ I) (hj1 : j ≠ 1) {k : ℕ} (hk : orderOf j = 2 ^ k) :
    T ⊓ I ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨c, -, hc⟩ := F7.isSylowTwoOf_exists_conj_le hT le_top hp
  have hjT : c⁻¹ * j * c ∈ T := mem_conjSub.mp (hc (Subgroup.mem_zpowers j))
  have hjI : c⁻¹ * j * c ∈ I := by
    have := hI.conj_mem j hj c⁻¹
    simpa using this
  intro hbot
  have hmem : c⁻¹ * j * c ∈ T ⊓ I := ⟨hjT, hjI⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hj1
  calc j = c * (c⁻¹ * j * c) * c⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem burnsideF429_m_center_mem_of_center_T [Finite K] {T I N : Subgroup K} {z : K}
    (hT : IsSylowTwoOf T ⊤) (hI : I.Normal) (hTI : T ⊓ I ≠ ⊥)
    (hcen : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w)
    {w : K} (hw : w ∈ T) (hwc : ∀ y ∈ T, y * w = w * y) : w ∈ I := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact I.one_mem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
  haveI hHn : (I.subgroupOf T).Normal := Subgroup.normal_subgroupOf
  have hHne : I.subgroupOf T ≠ ⊥ := by
    intro h
    apply hTI
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxI⟩
    have hmem : (⟨x, hxT⟩ : ↥T) ∈ I.subgroupOf T := hxI
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hmem
  obtain ⟨w₁, hw₁1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  obtain ⟨hw₀I, hw₀Z⟩ := w₁.2
  set w₀ : ↥T := (w₁ : ↥T) with hw₀def
  have hw₀I' : ((w₀ : ↥T) : K) ∈ I := hw₀I
  have hw₀c : ∀ y ∈ T, y * (w₀ : K) = (w₀ : K) * y := by
    intro y hy
    have := Subgroup.mem_center_iff.mp hw₀Z ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hw₀ne : ((w₀ : ↥T) : K) ≠ 1 := by
    intro h
    exact hw₁1 (Subtype.ext (Subtype.ext h))
  obtain ⟨m₀, -, hm₀⟩ := hcen _ w₀.2 hw₀c hw₀ne
  obtain ⟨m, -, hm⟩ := hcen w hw hwc hw1
  have hconj : w = (m * m₀⁻¹) * (w₀ : K) * (m * m₀⁻¹)⁻¹ := by
    rw [← hm₀, ← hm]
    group
  rw [hconj]
  exact hI.conj_mem _ hw₀I' _

theorem burnsideF429_m_eq_of_sylow_le {G : Type*} [Group G] [Finite G] {S H P : Subgroup G}
    (hS : IsSylowTwoOf S H) (hP : IsPGroup 2 P) (hSP : S ≤ P) (hPH : P ≤ H) : P = S := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS hPH hP
  have h1 : Nat.card P ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hx
    have e : Nat.card ↥(conjSub x S) = Nat.card ↥S :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    rwa [e] at this
  exact (Subgroup.eq_of_le_of_card_ge hSP h1).symm

theorem burnsideF429_m_ctr_le_of_transport {E : Type} [Group E] [Finite E] (θ : E ≃* K)
    {Gp M₁ M₂ : Subgroup E} (hGp : Gp.Normal) {T : Subgroup K} (hT : IsSylowTwoOf T ⊤)
    (hTM : T.comap θ.toMonoidHom ≤ M₁ ⊓ M₂)
    (hZ : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ∈ Gp.map θ.toMonoidHom)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup E := T.comap θ.toMonoidHom with hT'
  have hT'map : T'.map θ.toMonoidHom = T := Subgroup.map_comap_eq_self_of_surjective θ.surjective T
  have hT'p : IsPGroup 2 T' := by
    have h := hT.2.1.comap_of_injective (θ.toMonoidHom) θ.injective
    exact h
  have hT'syl : IsSylowTwoOf T' ⊤ := by
    refine ⟨le_top, hT'p, ?_⟩
    have h1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
    have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    have h3 : T'.index = T.index := by
      rw [hT']
      exact Subgroup.index_comap_of_surjective T θ.surjective
    rw [h1, h3, ← h2]
    exact hT.2.2
  have hT'12 : IsSylowTwoOf T' (M₁ ⊓ M₂) := F7.isSylowTwoOf_mono_right hT'syl hTM le_top
  obtain ⟨c, hc, hle⟩ := F7.isSylowTwoOf_exists_conj_le hT'12 hTb.1 hTb.2.1
  have hcp : IsPGroup 2 (conjSub c T') := F7.isPGroup_conjSub hT'p
  have hcle : conjSub c T' ≤ M₁ ⊓ M₂ := by
    intro y hy
    rw [mem_conjSub] at hy
    have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hc (hTM hy)) ((M₁ ⊓ M₂).inv_mem hc)
    simpa [mul_assoc] using this
  have heq : conjSub c T' = Tb := burnsideF429_m_eq_of_sylow_le hTb hcp hle hcle
  have hxT : x ∈ conjSub c T' := heq ▸ hx.1
  have hx' : c⁻¹ * x * c ∈ T' := mem_conjSub.mp hxT
  have hx'c : ∀ y ∈ T', y * (c⁻¹ * x * c) = (c⁻¹ * x * c) * y := by
    intro y hy
    have hcy : c * y * c⁻¹ ∈ Tb := by
      rw [← heq, mem_conjSub]
      simpa [mul_assoc] using hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hx.2) _ hcy
    calc y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * x * c) * y := by group
  have himg : θ (c⁻¹ * x * c) ∈ Gp.map θ.toMonoidHom := by
    refine hZ _ hx' fun y hy => ?_
    obtain ⟨y', rfl⟩ := θ.surjective y
    have hy' : y' ∈ T' := hy
    rw [← map_mul, ← map_mul, hx'c y' hy']
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp himg
  have hgx : g = c⁻¹ * x * c := θ.injective hge
  have hgx' : x = c * g * c⁻¹ := by rw [hgx]; group
  rw [hgx']
  exact hGp.conj_mem g hg c

end Generic

section Bridge

set_option linter.unusedSectionVars false

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_m_mem_of_odd [Gp.Normal] [Finite E] (hodd : Odd Gp.index) {Tb H : Subgroup E}
    (hTb : IsSylowTwoOf Tb H) {x : E} (hx : x ∈ Tb) : x ∈ Gp := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hTb.2.1 ⟨x, hx⟩
  refine burnsideF4d_two_elt_mem hodd (k := k) ?_
  rw [Subgroup.orderOf_mk] at hk
  rw [← hk]
  exact pow_orderOf_eq_one x

theorem burnsideF429_m_not_odd [Finite E] (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) (hodd : ¬ Odd Gp.index) :
    ¬ Odd (Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K / Nat.card ↥Gp) := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : Nat.card ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = Nat.card E := by
    have : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
      burnsideF4d_K_eq hyp.toHypF_4_4g hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  rw [hK]
  have := Subgroup.card_mul_index Gp
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
    rw [← this, Nat.mul_div_cancel_left _ hpos]]
  exact hodd

theorem burnsideF429_m_ctr_le_of_lieExt [Finite E] (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    {T N : Subgroup ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K}
    {z : ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K}
    (hT : IsSylowTwoOf T ⊤) (hT1 : T ≤ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb1)
    (hT2 : T ≤ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb2)
    (hcen : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp.toHypF_4_4g hyam
  let θ : E ≃* ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hK.symm)
  have hθ : ∀ e : E, ((θ e : ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K) : MulAut ↥Gp) =
      burnsideF4d_rho Gp e := fun e => rfl
  have hN1 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N1 = M₁.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N1_eq hyp.toHypF_4_4g hyam
  have hN2 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N2 = M₂.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N2_eq hyp.toHypF_4_4g hyam
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K := Finite.of_equiv E θ.toEquiv
  have hTM : T.comap θ.toMonoidHom ≤ M₁ ⊓ M₂ := by
    intro e he
    have h1 : θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb1 := hT1 he
    have h2 : θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb2 := hT2 he
    rw [Subgroup.mem_subgroupOf, hθ, hN1] at h1
    rw [Subgroup.mem_subgroupOf, hθ, hN2] at h2
    obtain ⟨e1, he1, he1e⟩ := h1
    obtain ⟨e2, he2, he2e⟩ := h2
    exact ⟨hinj he1e ▸ he1, hinj he2e ▸ he2⟩
  have hInorm : (Gp.map θ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ θ.surjective
  obtain ⟨j, hjG, hj1, k, hk⟩ := burnsideF429_jb_exists_two_elt
    (burnsideF429_jb_parabolics ChF.nativeChartCompatibility hyp)
  have hTI : T ⊓ Gp.map θ.toMonoidHom ≠ ⊥ :=
    burnsideF429_m_inf_normal_ne_bot hT hInorm (Subgroup.mem_map_of_mem θ.toMonoidHom hjG)
      (fun h => hj1 (θ.injective (h.trans (map_one θ).symm)))
      ((orderOf_injective θ.toMonoidHom θ.injective j).trans hk)
  exact burnsideF429_m_ctr_le_of_transport θ inferInstance hT hTM
    (fun w hw hwc => burnsideF429_m_center_mem_of_center_T hT hInorm hTI hcen hw hwc) hTb hx

theorem burnsideF429_m_ctr_le_G2 (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF429_m_mem_of_odd hodd hTb hx.1
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI : CharP K 2 := burnsideF4f_charP_of_card (by omega) hcard
  have hK3 : 3 ≤ Nat.card K := by
    rw [hcard]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamG2 hK3 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_G2 hf hyp.model
  obtain ⟨T, S, g, z, I, hO | hO⟩ := G2.f431TwoOutLieProp_g2 f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF429_m_not_odd hyp hTD hodd)
  · exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

theorem burnsideF429_m_ctr_le_D4tw (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF429_m_mem_of_odd hodd hTb hx.1
  obtain ⟨K, fK, finK, sigma, hscope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamD4 sigma hscope marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_D4tw hyp.model
  have hf1 : 1 ≤ f := hyp.model.2.1
  obtain ⟨T, S, g, z, I, hO | hO⟩ := D4q.f431TwoOutLieProp_d4q f hf1 ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF429_m_not_odd hyp hTD hodd)
  · exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le hO.T_le' hO.center_T hTb hx
  · exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hO.sylow hO.T_le' hO.T_le hO.center_T hTb hx

end Bridge

end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Final

set_option linter.unusedSectionVars false

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_m_ctr_le_U4_all (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF429_m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU4 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U4 hyp.model
  obtain ⟨T, N, z, hT, hT1, hT2, hcen⟩ := Un.burnsideF429_m_unCenterProp_four_all f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF429_m_not_odd hyp hTD hodd)
  exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hT hT1 hT2 hcen hTb hx

theorem burnsideF429_m_ctr_le_U5_all (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF429_m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U5 hyp.model
  obtain ⟨T, N, z, hT, hT1, hT2, hcen⟩ := Un.burnsideF429_m_unCenterProp_five_all f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF429_m_not_odd hyp hTD hodd)
  exact burnsideF429_m_ctr_le_of_lieExt hyp hTD hT hT1 hT2 hcen hTb hx

end Final

end CFSG.ASVolI
