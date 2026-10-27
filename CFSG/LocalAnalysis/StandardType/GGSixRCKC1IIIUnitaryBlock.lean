module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUSurvivorCentral
public import CFSG.LocalAnalysis.StandardType.SUInvolutionRank
public import CFSG.ClassicalGroups.Unitary.PerpQuotient

public section
namespace CFSG.StandardType.RCKC1

open Matrix Module CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCKK1IIISU CFSG.StandardType.SUTransvection
  CFSG.StandardType.LieKnownR2.Short

theorem rckSU_rank_suR_sub_one {k : ℕ} (hk : 4 ≤ k) :
    (mat SUσ k (suR hk) - 1).rank = 2 := by
  have hmat : mat SUσ k (suR hk) - 1 = rckSUc_N hk := by
    rw [mat_apply, rckSUc_suR_eq, add_sub_cancel_left]
  rw [hmat, Matrix.rank_eq_finrank_range_toLin _
    (Pi.basisFun SUF (Fin k)) (Pi.basisFun SUF (Fin k)), Matrix.toLin_eq_toLin']
  change Module.finrank SUF (rckSU_A hk) = 2
  rw [← rckSU_U_eq_range]
  have hlin : LinearIndependent SUF
      ![rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h01 : sI0 hk ≠ sI1 hk := by
      simpa only [rckSUc_e, Matrix.cons_val_zero, Matrix.cons_val_one] using
        rckSUc_e_zero_ne_one hk
    have h0 := congrFun hc (sI0 hk)
    have h1 := congrFun hc (sI1 hk)
    rw [Fin.sum_univ_two] at h0 h1
    have hc0 : c 0 = 0 := by
      simpa [rckSU_std, Pi.single_apply, h01, h01.symm] using h0
    have hc1 : c 1 = 0 := by
      simpa [rckSU_std, Pi.single_apply, h01, h01.symm] using h1
    fin_cases i <;> assumption
  have h := finrank_span_eq_card hlin
  have hRange : Set.range
      ![rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)] =
      {rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  change Module.finrank SUF (Submodule.span SUF
    {rckSU_std (k := k) (sI0 hk), rckSU_std (k := k) (sI1 hk)}) = 2
  rw [← hRange]
  exact h.trans (Fintype.card_fin 2)

theorem rckSU_exists_conj_of_rank_eq
    {k : ℕ} {r s : SUG k} (hr : orderOf r = 2) (hs : orderOf s = 2)
    (hRank : (mat SUσ k r - 1).rank = (mat SUσ k s - 1).rank) :
    ∃ g : SUG k, r = g * s * g⁻¹ := by
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution SUσ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution_gf4
  obtain ⟨l, hl, hlk, a, ha⟩ := exists_conj_ggInvSU_of_orderOf_eq_two hσ hr
  obtain ⟨m, hm, hmk, b, hb⟩ := exists_conj_ggInvSU_of_orderOf_eq_two hσ hs
  have hlm : l = m := by
    rw [ha, hb, rank_mat_conj_sub_one, rank_mat_conj_sub_one,
      rank_mat_ggInvSU_sub_one hlk, rank_mat_ggInvSU_sub_one hmk] at hRank
    exact hRank
  subst m
  refine ⟨a * b⁻¹, ?_⟩
  rw [ha, hb]
  group

theorem rckSU_fixes_fixed_space_of_rank_two
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)} {r : SUG k}
    (hFour : FourAt (⊤ : Subgroup (SUG k)) V r)
    (hCore : CoreCommAt (⊤ : Subgroup (SUG k)) V r)
    (hRank : (mat SUσ k r - 1).rank = 2) :
    ∀ v ∈ V, ∀ z : Fin k → SUF,
      natRep (SU SUσ k) r z = z → natRep (SU SUσ k) v z = z := by
  have hr : orderOf r = 2 := orderOf_eq_prime (hFour.2.2.1.2 r hFour.1) hFour.2.2.2.2.1
  have hs : orderOf (suR hk) = 2 := orderOf_eq_prime (rckSU_suR_sq hk) (suR_ne_one hk)
  obtain ⟨g, hg⟩ := rckSU_exists_conj_of_rank_eq hr hs
    (hRank.trans (rckSU_rank_suR_sub_one hk).symm)
  let e : (⊤ : Subgroup (SUG k)) ≃* SUG k :=
    Subgroup.topEquiv.trans (MulAut.conj g⁻¹)
  let V' := (V.subgroupOf ⊤).map e.toMonoidHom
  have her : e ⟨r, Subgroup.mem_top _⟩ = suR hk := by
    change g⁻¹ * r * (g⁻¹)⁻¹ = suR hk
    rw [hg]
    group
  have hFour' : FourAt (⊤ : Subgroup (SUG k)) V' (suR hk) := by
    rw [← her]
    exact fourAt_map_mulEquiv e (Subgroup.mem_top _) hFour
  have hCore' : CoreCommAt (⊤ : Subgroup (SUG k)) V' (suR hk) := by
    rw [← her]
    exact coreCommAt_map_mulEquiv e (Subgroup.mem_top _) hCore
  intro v hv z hz
  have hv' : e ⟨v, Subgroup.mem_top _⟩ ∈ V' := Subgroup.mem_map_of_mem _ hv
  have hrconj : g⁻¹ * r * g = suR hk := by rw [hg]; group
  have hz' : natRep (SU SUσ k) (suR hk) (natRep (SU SUσ k) g⁻¹ z) =
      natRep (SU SUσ k) g⁻¹ z := by
    rw [← hrconj, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (natRep (SU SUσ k) g) (natRep (SU SUσ k) g⁻¹),
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, hz]
  have hfix := rckSU_fixes_fixed_space_of_coreComm hk hFour' hCore' _ hv' _ hz'
  have h := congrArg (natRep (SU SUσ k) g) hfix
  change natRep (SU SUσ k) g
    (natRep (SU SUσ k) (g⁻¹ * v * g) (natRep (SU SUσ k) g⁻¹ z)) =
    natRep (SU SUσ k) g (natRep (SU SUσ k) g⁻¹ z) at h
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    ← Module.End.mul_apply (natRep (SU SUσ k) g) (natRep (SU SUσ k) g⁻¹),
    ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  rw [← Module.End.mul_apply (natRep (SU SUσ k) g) (natRep (SU SUσ k) g⁻¹),
    ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

theorem rckSU_core_le_centralizer_of_fix_fixed_space
    {k : ℕ} (hk : 4 ≤ k) {V : Subgroup (SUG k)} {r : SUG k}
    (hr : orderOf r = 2) (hRank : (mat SUσ k r - 1).rank = 2)
    (hFix : ∀ v ∈ V, ∀ z : Fin k → SUF,
      natRep (SU SUσ k) r z = z → natRep (SU SUσ k) v z = z) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (SUG k))) ≤
      Subgroup.centralizer (V : Set (SUG k)) := by
  have hs : orderOf (suR hk) = 2 := orderOf_eq_prime (rckSU_suR_sq hk) (suR_ne_one hk)
  obtain ⟨g, hg⟩ := rckSU_exists_conj_of_rank_eq hr hs
    (hRank.trans (rckSU_rank_suR_sub_one hk).symm)
  let e : MulAut (SUG k) := MulAut.conj g⁻¹
  let V' := V.map e.toMonoidHom
  have her : e r = suR hk := by
    change g⁻¹ * r * (g⁻¹)⁻¹ = suR hk
    rw [hg]
    group
  have hV' : V' ≤ suZ0 hk := by
    intro v' hv'
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hv'
    apply mem_suZ0_of_fix_planePerp hk
    intro z hz
    have hz0 : natRep (SU SUσ k) (suR hk) z = z := rckSU_suR_fixes_perp hk hz
    have hgz : natRep (SU SUσ k) r (natRep (SU SUσ k) g z) =
        natRep (SU SUσ k) g z := by
      rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (natRep (SU SUσ k) g⁻¹) (natRep (SU SUσ k) g),
        ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hz0]
    have h := hFix v hv _ hgz
    change natRep (SU SUσ k) (g⁻¹ * v * g) z = z
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hC := rckSU_core_le_centralizer_of_le_suZ0 hk hV'
  intro y hy
  have hy' : e y ∈ CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({suR hk} : Set (SUG k))) := by
    have hCent : (Subgroup.centralizer ({r} : Set (SUG k))).map e.toMonoidHom =
        Subgroup.centralizer ({suR hk} : Set (SUG k)) := by
      rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
      change Subgroup.centralizer ({e r} : Set (SUG k)) = _
      rw [her]
    rw [← hCent, CFSG.GroupTheory.map_pCoreOf_mulEquiv]
    exact Subgroup.mem_map_of_mem _ hy
  have hyC := hC hy'
  rw [Subgroup.mem_centralizer_iff] at hyC ⊢
  intro v hv
  apply e.injective
  simpa only [map_mul] using hyC (e v) (Subgroup.mem_map_of_mem _ hv)

theorem rank_sub_one_of_unitary_linear_embedding
    {m n : ℕ} (ι : SUG m →* SUG n)
    (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF)) (hE : Function.Injective E)
    (W : Submodule SUF (Fin n → SUF))
    (hAct : ∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w) (r : SUG m) :
    (mat SUσ n (ι r) - 1).rank = (mat SUσ m r - 1).rank := by
  let N := natRep (SU SUσ m) r - 1
  let N' := natRep (SU SUσ n) (ι r) - 1
  have hRange : LinearMap.range N' = (LinearMap.range N).map E := by
    apply le_antisymm
    · rintro z ⟨y, rfl⟩
      obtain ⟨x, w, hw, rfl⟩ := hSplit y
      refine Submodule.mem_map.mpr ⟨N x, ⟨x, rfl⟩, ?_⟩
      change E (natRep (SU SUσ m) r x - x) =
        natRep (SU SUσ n) (ι r) (E x + w) - (E x + w)
      rw [map_add, hAct, hFix r w hw, map_sub]
      abel
    · rintro z hz
      obtain ⟨x, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_map.mp hz
      refine ⟨E y, ?_⟩
      change natRep (SU SUσ n) (ι r) (E y) - E y =
        E (natRep (SU SUσ m) r y - y)
      rw [hAct, map_sub]
  have hNatM : Matrix.toLin' (mat SUσ m r - 1) = N := by
    ext x
    simp [N, Matrix.toLin'_apply, Matrix.sub_mulVec, natRep_apply, mat_apply]
  have hNatN : Matrix.toLin' (mat SUσ n (ι r) - 1) = N' := by
    ext x
    simp [N', Matrix.toLin'_apply, Matrix.sub_mulVec, natRep_apply, mat_apply]
  rw [Matrix.rank_eq_finrank_range_toLin _
    (Pi.basisFun SUF (Fin n)) (Pi.basisFun SUF (Fin n)), Matrix.toLin_eq_toLin', hNatN,
    Matrix.rank_eq_finrank_range_toLin _
    (Pi.basisFun SUF (Fin m)) (Pi.basisFun SUF (Fin m)), Matrix.toLin_eq_toLin', hNatM,
    hRange]
  exact (Submodule.equivMapOfInjective E hE (LinearMap.range N)).finrank_eq.symm

theorem fixes_fixed_space_of_unitary_linear_embedding
    {m n : ℕ} (ι : SUG m →* SUG n)
    (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF)) (hE : Function.Injective E)
    (W : Submodule SUF (Fin n → SUF))
    (hAct : ∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w)
    {V : Subgroup (SUG m)} {r : SUG m}
    (hV : ∀ v ∈ V, ∀ z, natRep (SU SUσ m) r z = z → natRep (SU SUσ m) v z = z) :
    ∀ v ∈ V.map ι, ∀ z, natRep (SU SUσ n) (ι r) z = z →
      natRep (SU SUσ n) v z = z := by
  rintro v ⟨u, hu, rfl⟩ z hz
  obtain ⟨x, w, hw, rfl⟩ := hSplit z
  have hx : natRep (SU SUσ m) r x = x := by
    apply hE
    apply add_right_cancel (b := w)
    simpa only [map_add, hAct, hFix r w hw] using hz
  rw [map_add, hAct, hFix u w hw, hV u hu x hx]

theorem rank_sub_one_of_mem_suPair
    {n : ℕ} {v w v' w' : Fin n → SUF}
    (hFrame : SUFrame rckSU_suF_card n v w v' w')
    {r : SUG n} (hr : r ∈ suPair SUσ n v w) (hr1 : r ≠ 1) :
    (mat SUσ n r - 1).rank = 2 := by
  obtain ⟨c, hc⟩ := exists_mulVec_of_mem_suPair rckSU_suF_card
    hFrame.2.2.1.1 hFrame.2.2.1.2.1 hFrame.2.2.2.1 hr
  have hc0 : c ≠ 0 := by
    intro h0
    apply hr1
    apply natRep_injective (SU SUσ n)
    refine LinearMap.ext fun x => ?_
    rw [hc x, h0]
    simp
  have hσc : SUσ c ≠ 0 := (map_ne_zero SUσ).mpr hc0
  let N := natRep (SU SUσ n) r - 1
  have hN (x : Fin n → SUF) : N x =
      (c * (suH rckSU_suF_card n).β w x) • v +
        (SUσ c * (suH rckSU_suF_card n).β v x) • w := by
    change natRep (SU SUσ n) r x - x = _
    rw [hc x]
    abel
  have hRange : LinearMap.range N = Submodule.span SUF {v, w} := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      rw [hN]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · refine ⟨c⁻¹ • v', ?_⟩
        rw [hN, ReflForm.smul_right, ReflForm.smul_right,
          hFrame.2.1, hFrame.2.2.2.2.1]
        simp [hc0]
      · refine ⟨(SUσ c)⁻¹ • w', ?_⟩
        rw [hN, ReflForm.smul_right, ReflForm.smul_right,
          hFrame.1, hFrame.2.2.2.2.2.1]
        simp only [mul_one, mul_zero, zero_smul, zero_add, mul_inv_cancel₀ hσc, one_smul]
  have hNat : Matrix.toLin' (mat SUσ n r - 1) = N := by
    refine LinearMap.ext fun x => ?_
    simp [N, Matrix.toLin'_apply, Matrix.sub_mulVec, natRep_apply, mat_apply]
  rw [Matrix.rank_eq_finrank_range_toLin _
    (Pi.basisFun SUF (Fin n)) (Pi.basisFun SUF (Fin n)), Matrix.toLin_eq_toLin', hNat, hRange]
  have hlin : LinearIndependent SUF ![v, w] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 := congrArg (fun z => (suH rckSU_suF_card n).β z w') ha
    have h1 := congrArg (fun z => (suH rckSU_suF_card n).β z v') ha
    rw [Fin.sum_univ_two] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
      hFrame.1, hFrame.2.2.2.2.2.1, ReflForm.β_zero_left] at h0
    rw [ReflForm.add_left, ReflForm.smul_left, ReflForm.smul_left,
      hFrame.2.1, hFrame.2.2.2.2.1, ReflForm.β_zero_left] at h1
    have ha0 : a 0 = 0 := (map_eq_zero (suH rckSU_suF_card n).σ).mp
      (by simpa only [mul_one, mul_zero, add_zero] using h0)
    have ha1 : a 1 = 0 := (map_eq_zero (suH rckSU_suF_card n).σ).mp
      (by simpa only [mul_one, mul_zero, zero_add] using h1)
    fin_cases i <;> assumption
  have hR : Set.range ![v, w] = {v, w} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hR]
  exact (finrank_span_eq_card hlin).trans (Fintype.card_fin 2)

theorem k2At_of_unitary_linear_embedding
    {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) (ι : SUG m →* SUG n)
    (hι : Function.Injective ι)
    (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF)) (hE : Function.Injective E)
    (W : Submodule SUF (Fin n → SUF))
    (hAct : ∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w)
    {V : Subgroup (SUG m)} {r : SUG m}
    (hFour : FourAt (⊤ : Subgroup (SUG m)) V r)
    (hCore : CoreCommAt (⊤ : Subgroup (SUG m)) V r)
    (hRank : (mat SUσ m r - 1).rank = 2) :
    K2At (⊤ : Subgroup (SUG n)) (V.map ι) (ι r) := by
  have hr : orderOf r = 2 := orderOf_eq_prime (hFour.2.2.1.2 r hFour.1) hFour.2.2.2.2.1
  have hr' : orderOf (ι r) = 2 := by
    rw [orderOf_injective ι hι]
    exact hr
  have hRank' : (mat SUσ n (ι r) - 1).rank = 2 :=
    (rank_sub_one_of_unitary_linear_embedding ι E hE W hAct hFix hSplit r).trans hRank
  have hVfix := rckSU_fixes_fixed_space_of_rank_two hm hFour hCore hRank
  have hVfix' := fixes_fixed_space_of_unitary_linear_embedding ι E hE W hAct hFix hSplit hVfix
  have hC := rckSU_core_le_centralizer_of_fix_fixed_space hn hr' hRank' hVfix'
  simpa only [K2At, top_inf_eq] using
    hC.trans (Subgroup.centralizer_le_normalizer (V.map ι : Set (SUG n)))

theorem coreCommAt_subgroup_map_mulEquiv
    {X U : Type} [Group X] [Group U] {K J V : Subgroup X} {r : X}
    (η : K ≃* U) (hJK : J ≤ K) (hrK : r ∈ K) (h : CoreCommAt J V r) :
    CoreCommAt ((J.subgroupOf K).map η.toMonoidHom) ((V.subgroupOf K).map η.toMonoidHom)
      (η ⟨r, hrK⟩) := by
  intro v hv y hy
  obtain ⟨vK, hvK, rfl⟩ := Subgroup.mem_map.mp hv
  have hP : CFSG.Open.pCoreOf 2
      (((J ⊓ Subgroup.centralizer ({r} : Set X)).subgroupOf K).map η.toMonoidHom) =
      ((CFSG.Open.pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X))).subgroupOf K).map
        η.toMonoidHom := by
    rw [CFSG.GroupTheory.map_pCoreOf_mulEquiv,
      CFSG.GroupTheory.pCoreOf_subgroupOf 2 (inf_le_left.trans hJK)]
  have hCent : ((J ⊓ Subgroup.centralizer ({r} : Set X)).subgroupOf K).map η.toMonoidHom =
      ((J.subgroupOf K).map η.toMonoidHom) ⊓
        Subgroup.centralizer ({η ⟨r, hrK⟩} : Set U) := by
    have hinf : (J ⊓ Subgroup.centralizer ({r} : Set X)).subgroupOf K =
        (J.subgroupOf K) ⊓ ((Subgroup.centralizer ({r} : Set X)).subgroupOf K) := rfl
    rw [hinf, CFSG.GroupTheory.centralizer_subgroupOf_singleton hrK,
      Subgroup.map_inf _ _ η.toMonoidHom η.injective,
      CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
    rfl
  rw [← hCent, hP] at hy
  obtain ⟨yK, hyK, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (h vK hvK yK hyK)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨a, ?_⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_zpow]
  exact congrArg η (Subtype.ext ha)

end CFSG.StandardType.RCKC1
