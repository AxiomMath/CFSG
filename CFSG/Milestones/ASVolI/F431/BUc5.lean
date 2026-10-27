module

public import CFSG.Milestones.ASVolI.F431.BUcDef
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSyl

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K]

theorem burnsideF4m_twoCentralizerV (h : UnitaryFieldData 2 f K)
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
theorem burnsideF4m_center_T5 {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
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
    burnsideF4m_twoCentralizerV h hZ w ⟨k, hk'⟩ (fun v hv => (hc v (hVT v hv)).symm)
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
@[expose] def burnsideF4m_F2 : Subgroup (K ≃+* K) where
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

theorem burnsideF4m_isPGroup_F2 : IsPGroup 2 (burnsideF4m_F2 h) := by
  rintro ⟨φ, k, hk⟩
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

@[expose] def burnsideF4m_Q5 : Subgroup (MulAut (hypPSU h 2 1)) :=
  Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) (burnsideF4m_F2 h)

include h in
theorem burnsideF4m_isPGroup_Q5 : IsPGroup 2 (burnsideF4m_Q5 h) := by
  have := h.finite
  have := finite_hypPSU_five h
  have := fld5_finite h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 (u5_sylow h).2.1
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 (burnsideF4m_isPGroup_F2 h)
  rw [IsPGroup.iff_card]
  exact ⟨a + b, by rw [burnsideF4m_Q5, card_Ssd5 h (u5_center_eq_bot h), ha, hb, pow_add]⟩

include h in
theorem burnsideF4m_Q5_sylow :
    IsSylowTwoOf (burnsideF4m_Q5 h) (autStab (hypProjUnitriangular h 2 1)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := hypProjUnitriangular h 2 1 with hU
  set G₁ := autStab U with hG₁
  have hQ2 := burnsideF4m_isPGroup_Q5 h
  have hQle : burnsideF4m_Q5 h ≤ G₁ := Ssd5_le_autStab h (fStab5_U h) le_rfl _
  refine ⟨hQle, hQ2, ?_⟩
  set Q₀ : Subgroup ↥G₁ := (burnsideF4m_Q5 h).subgroupOf G₁ with hQ₀
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
    have hσF : σ ∈ burnsideF4m_F2 h := ⟨k, fa5_mem_Dlin h hσD⟩
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
      change (e' : MulAut (hypPSU h 2 1)) ∈ burnsideF4m_Q5 h
      rw [he'val, hue]
      exact cj5_mem_Ssd5 h (hB := fStab5_U h) hu
    have : x = e' * s := by rw [he']; group
    rw [this]
    exact Q₀.mul_mem he'Q hsQ
  have hPQ : Q₀ = (P : Subgroup ↥G₁) := le_antisymm hP key
  have := P.not_dvd_index
  rwa [← hPQ] at this

include h in
theorem burnsideF4m_exists_conj_into_Q5 {R : Subgroup (MulAut (hypPSU h 2 1))}
    (hR : IsPGroup 2 R) (hRU : R ≤ autStab (hypProjUnitriangular h 2 1)) :
    ∃ g ∈ autStab (hypProjUnitriangular h 2 1), ∀ y ∈ R, g⁻¹ * y * g ∈ burnsideF4m_Q5 h := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  exact aut5_exists_conj (burnsideF4m_isPGroup_Q5 h) (burnsideF4m_Q5_sylow h).2.2 hRU hR

include h in
theorem burnsideF4m_exists_normalized5 {K' : Subgroup (MulAut (hypPSU h 2 1))}
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
  have hUhQ : Uh h ≤ burnsideF4m_Q5 h := by
    rw [← Ssd5_bot_eq_Uh h]
    exact Ssd5_mono h le_rfl bot_le
  have hUh2 : IsPGroup 2 (Uh h) := (burnsideF4m_isPGroup_Q5 h).to_le hUhQ
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
  obtain ⟨g₀, hg₀, hconj⟩ := burnsideF4m_exists_conj_into_Q5 h hT.isPGroup hTstab
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
    have h1 : (MulAut.conj g).toMonoidHom y₀ ∈ burnsideF4m_Q5 h := by
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
theorem burnsideF4m_lab5_perm {g : MulAut (hypPSU h 2 1)}
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
theorem burnsideF4m_un5_exists_normalized2 {A' : LieAmalgamExt (hypPSU h 2 1)}
    (hTD : A'.TD = hypProjUnitriangular h 2 1)
    (hP : (A'.P1 = u5PtP h ∧ A'.P2 = u5LnP h) ∨ (A'.P1 = u5LnP h ∧ A'.P2 = u5PtP h))
    (hinn : (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)).range ≤ A'.K) :
    ∃ A'' : LieAmalgamExt (hypPSU h 2 1), A''.TD = hypProjUnitriangular h 2 1 ∧
      ((A''.P1 = u5PtP h ∧ A''.P2 = u5LnP h) ∨ (A''.P1 = u5LnP h ∧ A''.P2 = u5PtP h)) ∧
      Nonempty (KIso A' A'') ∧ ∃ F₂ : Subgroup (K ≃+* K),
        IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) A''.K := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨g, hg, F₂, hsyl⟩ := burnsideF4m_exists_normalized5 h (K' := A'.K) hinn
  have hgU : (hypProjUnitriangular h 2 1).map g.toMonoidHom = hypProjUnitriangular h 2 1 :=
    (AG.mem_autStab_iff_map_eq g _).1 hg
  have hperm := burnsideF4m_lab5_perm h hg
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

theorem burnsideF4m_unCenterProp_five_all (f : ℕ) : burnsideF4m_UnCenterProp 5 f := by
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
  obtain ⟨A'', -, hP'', ⟨L2⟩, F₂, hsyl⟩ := burnsideF4m_un5_exists_normalized2 h hTD hP hinn
  have hinn'' : Pi h ≤ A''.K := A''.range_conj_le_K (hsupc A'' hP'')
  have hT1 : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ≤ autStab A''.P1 := by
    rcases hP'' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    exacts [Ssd5_le_autStab_Pt h F₂, Ssd5_le_autStab_Ln h F₂]
  have hT2 : Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ ≤ autStab A''.P2 := by
    rcases hP'' with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    exacts [Ssd5_le_autStab_Ln h F₂, Ssd5_le_autStab_Pt h F₂]
  refine burnsideF4m_unCenterConcl_of_kiso L1 (burnsideF4m_unCenterConcl_of_kiso L2
    (burnsideF4m_unCenterConcl_of_model A'' hsyl hT1 hT2 (hinn'' ⟨z5Y h, rfl⟩) ?_))
  intro w hw hc hw1
  obtain ⟨m, hm, hme⟩ := burnsideF4m_center_T5 h hinn'' hsyl.2.1 hw hc hw1
  exact ⟨m, hm.1, hme⟩

end Main

end CFSG.Quasithin.H13.F431.Un
