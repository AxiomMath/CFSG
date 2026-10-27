module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpGspNil
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpField
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpAniso

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spEnd spEnd_apply)
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation

private lemma mul_one_add_mul_inv {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    {M N Minv : Matrix n n K} (hMN : M * N = N * M) (hMinv : M * Minv = 1) :
    M * (1 + N) * Minv = 1 + N := by
  calc M * (1 + N) * Minv = (M + M * N) * Minv := by rw [Matrix.mul_add, Matrix.mul_one]
    _ = M * Minv + (M * N) * Minv := by rw [Matrix.add_mul]
    _ = M * Minv + N * (M * Minv) := by rw [hMN, Matrix.mul_assoc]
    _ = 1 + N := by rw [hMinv, Matrix.mul_one]

private lemma maps_into_left_or_right {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {P M : Submodule K V} (Y : V →ₗ[K] V)
    (h : ∀ p ∈ P, Y p ∈ P ∨ Y p ∈ M) :
    (∀ p ∈ P, Y p ∈ P) ∨ (∀ p ∈ P, Y p ∈ M) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨p, hp⟩ := Classical.not_forall.mp hcon.1
  obtain ⟨hpP, hpN⟩ := Classical.not_imp.mp hp
  obtain ⟨q, hq⟩ := Classical.not_forall.mp hcon.2
  obtain ⟨hqP, hqM⟩ := Classical.not_imp.mp hq
  have hpM : Y p ∈ M := (h p hpP).resolve_left hpN
  have hqPt : Y q ∈ P := (h q hqP).resolve_right hqM
  have hsum := h (p + q) (P.add_mem hpP hqP)
  rcases hsum with hsum | hsum
  · have hYp : Y p = Y (p + q) - Y q := by rw [map_add]; abel
    exact hpN (hYp ▸ P.sub_mem hsum hqPt)
  · have hYq : Y q = Y (p + q) - Y p := by rw [map_add]; abel
    exact hqM (hYq ▸ M.sub_mem hsum hpM)

private lemma inf_eigenspace_eq_bot {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h2K : (2 : K) ≠ 0) {T : Module.End K V} :
    T.eigenspace 1 ⊓ T.eigenspace (-1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hv
  rw [one_smul, neg_one_smul] at hv
  have hneg : v = -v := by
    calc v = T v := hv.1.symm
      _ = -v := hv.2
  have h2v : (2 : K) • v = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (smul_eq_zero.mp h2v).resolve_left h2K

private lemma spEnd_ne_zero {K : Type} [Field K] {r : ℕ} (hr1 : 1 ≤ r) (g : StatedSp r K) :
    spEnd g ≠ 0 := by
  intro h0
  let v : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨0, hr1⟩) 1
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl ⟨0, hr1⟩)
    simp [v] at h1
  have h1 : spEnd g (spEnd g⁻¹ v) = 0 := by rw [h0]; rfl
  rw [spEnd_spEnd_inv] at h1
  exact hv h1

theorem planeGen_of_involutory_lift {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 2 ≤ r)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (a : StatedSp r F)
    (ha : MulAut.conj (proj r F a) ∈ E) (ha1 : MulAut.conj (proj r F a) ≠ 1)
    (haa : spEnd a * spEnd a = 1) (B : gsp r F) (hb : conjAut r F B ∈ E)
    (hb1 : conjAut r F B ≠ 1) (hab : MulAut.conj (proj r F a) ≠ conjAut r F B) :
    PlaneGen E := by
  classical
  have hr1 : 1 ≤ r := by omega
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set MA : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hMAdef
  set MB : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hMBdef
  let H : Subgroup (StatedSp r F) := (planeClosure E).comap (proj r F)
  have hAfix : ∀ v, spEnd a (spEnd a v) = v := fun v => by
    rw [← Module.End.mul_apply, haa, Module.End.one_apply]
  have hpure : ∀ v : Fin r ⊕ Fin r → F, spEnd a v = v ∨ spEnd a v = -v →
      TransCenter H v := by
    intro v hv t
    change proj r F (spTransvection v t) ∈ planeClosure E
    refine mem_planeClosure_of_fixed ha ha1 ?_
    rw [← conjAut_statedSp a, conjAut_proj]
    congr 1
    have hconj : conjSp r F ⟨a, statedSp_le_gsp a.2⟩ (spTransvection v t) =
        spTransvection v t := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_conjSp]
      have h := congrArg (fun g : StatedSp r F => ((g : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) (spTransvection_conj a v t)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
      simp only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv] at h
      rcases hv with hv | hv
      · simpa [hv] using h
      · have hneg : spTransvection (spEnd a v) t = spTransvection v t := by
          rw [hv, show (-v : Fin r ⊕ Fin r → F) = (-1 : F) • v by simp, spTransvection_smul]
          norm_num
        rw [hneg] at h
        simpa using h
    exact hconj
  have hB2aut : conjAut r F (B * B) = 1 := by
    rw [map_mul]
    rw [← pow_two]
    exact hE.2 (conjAut r F B) hb
  obtain ⟨-, c, hc⟩ :=
    (conjAut_mul_fieldAut_eq_one_iff hr1 (B * B) (1 : F ≃+* F)).mp
      (by rwa [map_one, mul_one])
  have hMB2 : MB * MB = (c : F) • 1 := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) hc
    rw [Subgroup.coe_mul, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar] at h
    rw [show (Matrix.scalar (Fin r ⊕ Fin r) (c : F)) = (c : F) • 1 by
      rw [Matrix.smul_one_eq_diagonal]; rfl] at h
    simpa [MB, hMBdef] using h
  have hBne : ∀ d : F, MB ≠ d • 1 := by
    intro d hd
    have hd0 : d ≠ 0 := by
      intro h0
      have hzero : MB = 0 := by rw [hd, h0, zero_smul]
      have hone : MB * ((((B : GL (Fin r ⊕ Fin r) F)⁻¹) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 := by
        simp [MB, hMBdef]
      rw [hzero, Matrix.zero_mul] at hone
      have hentry := congrFun (congrFun hone (Sum.inl ⟨0, hr1⟩)) (Sum.inl ⟨0, hr1⟩)
      simp at hentry
    apply hb1
    have hscalar : (B : GL (Fin r ⊕ Fin r) F) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 d hd0) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      exact hd.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
    have hbij :=
      (conjAut_mul_fieldAut_eq_one_iff hr1 B (1 : F ≃+* F)).mpr
        ⟨rfl, ⟨Units.mk0 d hd0, hscalar⟩⟩
    simpa [map_one, mul_one] using hbij
  obtain ⟨N, hN0, hNN, hBN, hNskew⟩ :=
    exists_sq_zero_commute_gsp hF hr (Units.ne_zero (multiplierUnit B))
      (by simpa [MB, hMBdef] using multiplierUnit_spec B) hMB2 hBne
  have hNin : (1 + N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) * (1 - N) = 1 := by
    calc (1 + N) * (1 - N) = 1 * (1 - N) + N * (1 - N) := by rw [Matrix.add_mul]
      _ = (1 - N) + (N - N * N) := by rw [Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hNN]
      _ = 1 := by rw [hNN]; abel
  have hdet : (1 + N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hNin
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  let Xg : GL (Fin r ⊕ Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + N) hdet
  have hXgcoe : ((Xg : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N := rfl
  have hXsp : Xg ∈ StatedSp r F := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hXgcoe]
    have hNskew' : Nᵀ * formJ r F = -(formJ r F * N) :=
      eq_neg_iff_add_eq_zero.mpr hNskew
    have hNsq : Nᵀ * formJ r F * N = 0 := by
      calc Nᵀ * formJ r F * N = (-(formJ r F * N)) * N := by rw [hNskew']
        _ = -((formJ r F * N) * N) := Matrix.neg_mul _ _
        _ = -(formJ r F * (N * N)) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hNN, Matrix.mul_zero, neg_zero]
    calc (1 + N)ᵀ * formJ r F * (1 + N)
        = (1 + Nᵀ) * formJ r F * (1 + N) := by rw [Matrix.transpose_add, Matrix.transpose_one]
      _ = (formJ r F + Nᵀ * formJ r F) * (1 + N) := by rw [Matrix.add_mul, Matrix.one_mul]
      _ = (formJ r F + Nᵀ * formJ r F) * 1 +
            (formJ r F + Nᵀ * formJ r F) * N := by rw [Matrix.mul_add, Matrix.mul_one]
      _ = (formJ r F + Nᵀ * formJ r F) + (formJ r F * N + Nᵀ * formJ r F * N) := by
            rw [Matrix.add_mul, Matrix.add_mul]
            simp only [Matrix.mul_one]
      _ = formJ r F := by
            rw [hNsq, add_zero]
            have hJN : formJ r F * N = -(Nᵀ * formJ r F) := by
              have := congrArg Neg.neg hNskew'
              simpa using this.symm
            rw [hJN]
            abel
  let X : StatedSp r F := ⟨Xg, hXsp⟩
  have hXcoe : ((X : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N := rfl
  have hX1 : X ≠ 1 := by
    intro h
    apply hN0
    have h' := congrArg (fun g : StatedSp r F => ((g : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h
    rw [hXcoe, Subgroup.coe_one, Units.val_one] at h'
    exact add_left_cancel (show 1 + N = 1 + 0 by simpa using h')
  have hX3 : (((X : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) - 1) ^ 3 = 0 := by
    rw [hXcoe]
    rw [show (1 + N - 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = N by abel]
    rw [pow_succ, pow_two, hNN, Matrix.zero_mul]
  have hBX : conjSp r F B X = X := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_conjSp]
    change MB * ((X : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((((B : GL (Fin r ⊕ Fin r) F)⁻¹) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N
    rw [hXcoe]
    exact mul_one_add_mul_inv hBN (by simp [MB, hMBdef])
  have hXH : X ∈ H := by
    change proj r F X ∈ planeClosure E
    refine mem_planeClosure_of_fixed hb hb1 ?_
    rw [conjAut_proj, hBX]
  by_cases hAN : MA * N = N * MA
  ·
    have hAX : conjSp r F ⟨a, statedSp_le_gsp a.2⟩ X = X := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_conjSp]
      change MA * ((X : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
          ((((a : GL (Fin r ⊕ Fin r) F)⁻¹) : GL (Fin r ⊕ Fin r) F) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N
      rw [hXcoe]
      exact mul_one_add_mul_inv hAN (by simp [MA, hMAdef])
    have hfixA : MulAut.conj (proj r F a) (proj r F X) = proj r F X := by
      rw [← conjAut_statedSp a, conjAut_proj, hAX]
    have hfixB : conjAut r F B (proj r F X) = proj r F X := by
      rw [conjAut_proj, hBX]
    have hfixE : ∀ e ∈ E, e (proj r F X) = proj r F X := by
      intro e he
      obtain h1 | h1 | h1 | h1 :=
        SpSeitz.mem_four hE h4 ha hb he ha1 hb1 hab
      · rw [h1]; rfl
      · rw [h1]; exact hfixA
      · rw [h1]; exact hfixB
      · rw [h1, MulAut.mul_apply, hfixB, hfixA]
    exact planeGen_of_fixed_unipotent_sp hF hE h4 X hX1 hX3 hfixE
  ·
    let P : Submodule F (Fin r ⊕ Fin r → F) := (spEnd a).eigenspace 1
    let M : Submodule F (Fin r ⊕ Fin r → F) := (spEnd a).eigenspace (-1)
    have hPmem : ∀ v, v ∈ P ↔ spEnd a v = v := fun v => by
      rw [Module.End.mem_eigenspace_iff]
      simp
    have hMmem : ∀ v, v ∈ M ↔ spEnd a v = -v := fun v => by
      rw [Module.End.mem_eigenspace_iff]
      simp
    have hspan : P ⊔ M = ⊤ := by
      have h := SpSeitz.eigB_iSup (K := F) (r := r) h2F haa
      rw [iSup_bool_eq] at h
      simpa [SpSeitz.eigB, P, M] using h
    have hPM : P ⊓ M = ⊥ := by
      simpa [P, M] using inf_eigenspace_eq_bot (K := F) (V := Fin r ⊕ Fin r → F) h2F
    have hPne : P ≠ ⊥ := by
      intro hbot
      have hMtop : M = ⊤ := by
        rw [eq_top_iff, ← hspan]
        refine sup_le ?_ le_rfl
        rw [hbot]
        exact bot_le
      have hAneg : spEnd a = -1 := by
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ M := by rw [hMtop]; exact Submodule.mem_top
        exact (hMmem v).mp hv
      have hproj : proj r F a = 1 := SpSeitz.proj_eq_one_of_spEnd_eq (Or.inr hAneg)
      exact ha1 (by rw [hproj]; exact map_one _)
    have hMne : M ≠ ⊥ := by
      intro hbot
      have hPtop : P = ⊤ := by
        rw [eq_top_iff, ← hspan]
        refine sup_le le_rfl ?_
        rw [hbot]
        exact bot_le
      have hAone : spEnd a = 1 := by
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ P := by rw [hPtop]; exact Submodule.mem_top
        exact (hPmem v).mp hv
      have hproj : proj r F a = 1 := SpSeitz.proj_eq_one_of_spEnd_eq (Or.inl hAone)
      exact ha1 (by rw [hproj]; exact map_one _)
    have decomp : ∀ v : Fin r ⊕ Fin r → F, ∃ p ∈ P, ∃ m ∈ M, p + m = v := by
      intro v
      have hv : v ∈ P ⊔ M := by rw [hspan]; exact Submodule.mem_top
      exact Submodule.mem_sup.mp hv
    have hex : ∃ p : Fin r ⊕ Fin r → F, (p ∈ P ∨ p ∈ M) ∧ p ≠ 0 ∧
        spEnd X p ∉ P ∧ spEnd X p ∉ M := by
      by_contra hcon
      have hpureP : ∀ p ∈ P, spEnd X p ∈ P ∨ spEnd X p ∈ M := by
        intro p hp
        by_cases hp0 : p = 0
        · subst hp0
          exact Or.inl (by rw [map_zero]; exact Submodule.zero_mem P)
        · by_contra hnot
          exact hcon ⟨p, Or.inl hp, hp0, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
      have hpureM : ∀ p ∈ M, spEnd X p ∈ P ∨ spEnd X p ∈ M := by
        intro p hp
        by_cases hp0 : p = 0
        · subst hp0
          exact Or.inl (by rw [map_zero]; exact Submodule.zero_mem P)
        · by_contra hnot
          exact hcon ⟨p, Or.inr hp, hp0, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
      have hYP := maps_into_left_or_right (P := P) (M := M) (spEnd X) hpureP
      have hYM : (∀ m ∈ M, spEnd X m ∈ M) ∨ (∀ m ∈ M, spEnd X m ∈ P) :=
        maps_into_left_or_right (P := M) (M := P) (spEnd X) fun m hm => (hpureM m hm).symm
      have hAlin : spEnd a = Matrix.toLin' MA := by
        refine LinearMap.ext fun v => ?_
        rw [spEnd_apply, Matrix.toLin'_apply, hMAdef]
      have hXlin : spEnd X = 1 + Matrix.toLin' N := by
        refine LinearMap.ext fun v => ?_
        rw [spEnd_apply, hXcoe]
        calc (1 + N) *ᵥ v = 1 *ᵥ v + N *ᵥ v := by rw [Matrix.add_mulVec]
          _ = v + (Matrix.toLin' N) v := by rw [Matrix.one_mulVec, Matrix.toLin'_apply]
          _ = (1 + Matrix.toLin' N) v := by rw [LinearMap.add_apply, Module.End.one_apply]
      have hNlin_sq : Matrix.toLin' N * Matrix.toLin' N = 0 := by
        refine LinearMap.ext fun v => ?_
        rw [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
          Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec, LinearMap.zero_apply]
      have hXsurj : Function.Surjective (spEnd X) := fun v =>
        ⟨spEnd X⁻¹ v, spEnd_spEnd_inv X v⟩
      rcases hYP with hPP | hPM'
      · rcases hYM with hMM | hMP
        ·
          have hYX : spEnd a * spEnd X = spEnd X * spEnd a := by
            refine LinearMap.ext fun v => ?_
            obtain ⟨p, hp, m, hm, hpm⟩ := decomp v
            have hpA : spEnd a p = p := (hPmem p).mp hp
            have hmA : spEnd a m = -m := (hMmem m).mp hm
            have hpX : spEnd a (spEnd X p) = spEnd X p := (hPmem _).mp (hPP p hp)
            have hmX : spEnd a (spEnd X m) = -(spEnd X m) := (hMmem _).mp (hMM m hm)
            have hAv : spEnd a v = p - m := by
              rw [← hpm, map_add, hpA, hmA]
              abel
            have hXv : spEnd X v = spEnd X p + spEnd X m := by
              rw [← hpm, map_add]
            calc (spEnd a * spEnd X) v = spEnd a (spEnd X v) := rfl
              _ = spEnd a (spEnd X p + spEnd X m) := by rw [hXv]
              _ = spEnd a (spEnd X p) + spEnd a (spEnd X m) := by rw [map_add]
              _ = spEnd X p + -(spEnd X m) := by rw [hpX, hmX]
              _ = spEnd X p - spEnd X m := by abel
              _ = spEnd X (p - m) := by rw [map_sub]
              _ = spEnd X (spEnd a v) := by rw [hAv]
              _ = (spEnd X * spEnd a) v := rfl
          have hlin : Matrix.toLin' MA * Matrix.toLin' N =
              Matrix.toLin' N * Matrix.toLin' MA := by
            have h := hYX
            rw [hAlin, hXlin] at h
            rw [mul_add, add_mul, mul_one, one_mul] at h
            exact add_left_cancel h
          have hMN : MA * N = N * MA := by
            apply Matrix.toLin'.injective
            rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
            simpa [Module.End.mul_eq_comp] using hlin
          exact hAN hMN
        ·
          have hPtop : P = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro v
            obtain ⟨w, rfl⟩ := hXsurj v
            obtain ⟨p, hp, m, hm, hpm⟩ := decomp w
            rw [← hpm, map_add]
            exact P.add_mem (hPP p hp) (hMP m hm)
          have hMbot : M = ⊥ := by
            rw [← hPM, hPtop, top_inf_eq]
          exact hMne hMbot
      · rcases hYM with hMM | hMP
        ·
          have hMtop : M = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro v
            obtain ⟨w, rfl⟩ := hXsurj v
            obtain ⟨p, hp, m, hm, hpm⟩ := decomp w
            rw [← hpm, map_add]
            exact M.add_mem (hPM' p hp) (hMM m hm)
          have hPbot : P = ⊥ := by
            rw [← hPM, hMtop, inf_top_eq]
          exact hPne hPbot
        ·
          have hanti : spEnd a * spEnd X = -(spEnd X * spEnd a) := by
            refine LinearMap.ext fun v => ?_
            obtain ⟨p, hp, m, hm, hpm⟩ := decomp v
            have hpA : spEnd a p = p := (hPmem p).mp hp
            have hmA : spEnd a m = -m := (hMmem m).mp hm
            have hpX : spEnd a (spEnd X p) = -(spEnd X p) := (hMmem _).mp (hPM' p hp)
            have hmX : spEnd a (spEnd X m) = spEnd X m := (hPmem _).mp (hMP m hm)
            have hAv : spEnd a v = p - m := by
              rw [← hpm, map_add, hpA, hmA]
              abel
            have hXv : spEnd X v = spEnd X p + spEnd X m := by
              rw [← hpm, map_add]
            calc (spEnd a * spEnd X) v = spEnd a (spEnd X v) := rfl
              _ = spEnd a (spEnd X p) + spEnd a (spEnd X m) := by rw [hXv, map_add]
              _ = -(spEnd X p) + spEnd X m := by rw [hpX, hmX]
              _ = -(spEnd X p - spEnd X m) := by abel
              _ = -(spEnd X (p - m)) := by rw [map_sub]
              _ = -(spEnd X (spEnd a v)) := by rw [hAv]
              _ = (-(spEnd X * spEnd a)) v := by rw [LinearMap.neg_apply]; rfl
          have hMNlin : Matrix.toLin' MA * Matrix.toLin' N =
              Matrix.toLin' N * Matrix.toLin' MA := by
            have heq : Matrix.toLin' MA * (1 + Matrix.toLin' N) =
                -((1 + Matrix.toLin' N) * Matrix.toLin' MA) := by
              simpa [hAlin, hXlin] using hanti
            have hXsq : (1 + Matrix.toLin' N) * (1 + Matrix.toLin' N) =
                1 + (2 : F) • Matrix.toLin' N := by
              calc (1 + Matrix.toLin' N) * (1 + Matrix.toLin' N)
                  = 1 * (1 + Matrix.toLin' N) +
                      Matrix.toLin' N * (1 + Matrix.toLin' N) := by rw [add_mul]
                _ = (1 + Matrix.toLin' N) +
                      (Matrix.toLin' N + Matrix.toLin' N * Matrix.toLin' N) := by
                      rw [one_mul, mul_add, mul_one]
                _ = 1 + Matrix.toLin' N + (Matrix.toLin' N + 0) := by rw [hNlin_sq]
                _ = 1 + (2 : F) • Matrix.toLin' N := by rw [two_smul]; abel
            have hsqcomm : Matrix.toLin' MA *
                  ((1 + Matrix.toLin' N) * (1 + Matrix.toLin' N)) =
                ((1 + Matrix.toLin' N) * (1 + Matrix.toLin' N)) * Matrix.toLin' MA := by
              calc Matrix.toLin' MA * ((1 + Matrix.toLin' N) * (1 + Matrix.toLin' N))
                  = (Matrix.toLin' MA * (1 + Matrix.toLin' N)) *
                      (1 + Matrix.toLin' N) := by rw [mul_assoc]
                _ = (-((1 + Matrix.toLin' N) * Matrix.toLin' MA)) *
                      (1 + Matrix.toLin' N) := by rw [heq]
                _ = -(((1 + Matrix.toLin' N) * Matrix.toLin' MA) *
                      (1 + Matrix.toLin' N)) := by
                      simp [Module.End.mul_eq_comp]
                _ = -((1 + Matrix.toLin' N) *
                      (Matrix.toLin' MA * (1 + Matrix.toLin' N))) := by rw [mul_assoc]
                _ = -((1 + Matrix.toLin' N) *
                      (-((1 + Matrix.toLin' N) * Matrix.toLin' MA))) := by rw [heq]
                _ = -(-((1 + Matrix.toLin' N) *
                      ((1 + Matrix.toLin' N) * Matrix.toLin' MA))) := by
                      congr 1
                      simp [Module.End.mul_eq_comp]
                _ = ((1 + Matrix.toLin' N) * (1 + Matrix.toLin' N)) * Matrix.toLin' MA := by
                      rw [neg_neg, ← mul_assoc]
            have h2 : (2 : F) • (Matrix.toLin' MA * Matrix.toLin' N) =
                (2 : F) • (Matrix.toLin' N * Matrix.toLin' MA) := by
              have h := hsqcomm
              rw [hXsq] at h
              rw [mul_add, add_mul, mul_one, one_mul, Algebra.mul_smul_comm,
                Algebra.smul_mul_assoc] at h
              exact add_left_cancel h
            have h2' : (2 : F) • (Matrix.toLin' MA * Matrix.toLin' N -
                Matrix.toLin' N * Matrix.toLin' MA) = 0 := by
              rw [smul_sub, h2, sub_self]
            have hzero : Matrix.toLin' MA * Matrix.toLin' N -
                Matrix.toLin' N * Matrix.toLin' MA = 0 :=
              (smul_eq_zero.mp h2').resolve_left h2F
            exact sub_eq_zero.mp hzero
          have hcommA : spEnd a * spEnd X = spEnd X * spEnd a := by
            rw [hAlin, hXlin, mul_add, mul_one, add_mul, one_mul, hMNlin]
          have hEq : spEnd a * spEnd X = -(spEnd a * spEnd X) := by
            have h := hanti
            rw [← hcommA] at h
            exact h
          have hspzero : spEnd a * spEnd X = 0 := by
            have h2 : (2 : F) • (spEnd a * spEnd X) = 0 := by
              rw [two_smul]
              exact eq_neg_iff_add_eq_zero.mp hEq
            exact (smul_eq_zero.mp h2).resolve_left h2F
          have hnotzero : spEnd (a * X) ≠ 0 := spEnd_ne_zero hr1 (a * X)
          rw [spEnd_mul] at hnotzero
          exact hnotzero hspzero
    obtain ⟨p, hp, hp0, hYpP, hYpM⟩ := hex
    have hpurep : spEnd a p = p ∨ spEnd a p = -p := by
      rcases hp with hp | hp
      · exact Or.inl ((hPmem p).mp hp)
      · exact Or.inr ((hMmem p).mp hp)
    have hTp : TransCenter H p := hpure p hpurep
    have hTy : TransCenter H (spEnd X p) := hTp.map hXH
    let y := spEnd X p
    let yp : Fin r ⊕ Fin r → F := (2 : F)⁻¹ • (y + spEnd a y)
    let ym : Fin r ⊕ Fin r → F := (2 : F)⁻¹ • (y - spEnd a y)
    have hysum : yp + ym = y := by
      rw [show yp + ym = (2 : F)⁻¹ • ((y + spEnd a y) + (y - spEnd a y)) by
        rw [smul_add]]
      rw [show (y + spEnd a y) + (y - spEnd a y) = (2 : F) • y by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ h2F, one_smul]
    have hyp : spEnd a yp = yp := by
      rw [show yp = (2 : F)⁻¹ • (y + spEnd a y) from rfl, map_smul, map_add, hAfix]
      rw [add_comm]
    have hym : spEnd a ym = -ym := by
      rw [show ym = (2 : F)⁻¹ • (y - spEnd a y) from rfl, map_smul, map_sub, hAfix]
      rw [show spEnd a y - y = -(y - spEnd a y) by abel, smul_neg]
    have hsum' : yp + ym = spEnd X p := hysum
    have hyp0 : yp ≠ 0 := by
      intro h0
      have h1 : spEnd X p = ym := by rw [← hsum', h0, zero_add]
      exact hYpM (h1 ▸ (hMmem ym).mpr hym)
    have hym0 : ym ≠ 0 := by
      intro h0
      have h1 : spEnd X p = yp := by rw [← hsum', h0, add_zero]
      exact hYpP (h1 ▸ (hPmem yp).mpr hyp)
    have hmix : TransCenter H (yp + ym) := by rw [hysum]; exact hTy
    have hall : ∀ v, TransCenter H v :=
      SpSeitz.transCenter_of_mix h2F haa hpure hyp hym hyp0 hym0 hmix
    have hHtop : H = ⊤ := eq_top_of_transCenter hall
    rw [PlaneGen]
    calc planeClosure E = Subgroup.map (proj r F) H := by
          rw [show H = (planeClosure E).comap (proj r F) from rfl]
          exact (Subgroup.map_comap_eq_self_of_surjective
            (proj_surjective (r := r) (K := F)) (planeClosure E)).symm
      _ = ⊤ := by rw [hHtop, Subgroup.map_top_of_surjective _ (proj_surjective (r := r) (K := F))]

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
