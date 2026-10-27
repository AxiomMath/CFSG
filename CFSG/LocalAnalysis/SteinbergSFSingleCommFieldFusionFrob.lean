module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommCanonical

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Aux

variable {G : Type} [Group G]

theorem sixFF_ff3a_conj_closure {g : G} {X : Set G} (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ closure X) :
    ∀ x ∈ closure X, g * x * g⁻¹ ∈ closure X := by
  have hle : closure X ≤ (closure X).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro x hx
    exact hX x hx
  intro x hx
  exact Subgroup.mem_comap.mp (hle hx)

end Aux

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff3a_frob_pow_mem (H : Subgroup (antiSp K)) (hH : ∀ g ∈ H, frobAut K g ∈ H)
    (k : ℕ) : ∀ g ∈ H, (frobAut K ^ k) g ∈ H := by
  intro g hg
  induction k with
  | zero => simpa using hg
  | succ k ih => rw [pow_succ', MulAut.mul_apply]; exact hH _ ih

theorem sixFF_ff3a_frob_antiUnipotent : ∀ g ∈ antiUnipotent K, frobAut K g ∈ antiUnipotent K := by
  rintro g ⟨a, b, c, d, rfl⟩
  rw [frobAut_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

theorem sixFF_ff3a_frob_diagTorus : ∀ g ∈ diagTorus K, frobAut K g ∈ diagTorus K := by
  rintro g ⟨r, s, hr, hs, hg⟩
  refine ⟨r ^ 2, s ^ 2, pow_ne_zero 2 hr, pow_ne_zero 2 hs, ?_⟩
  have h2 : (diagMat r s).map (fun x => x ^ 2) = diagMat (r ^ 2) (s ^ 2) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [diagMat, inv_pow]
  show glMat (frobAut K g : GL (Fin 4) K) = diagMat (r ^ 2) (s ^ 2)
  rw [← h2, ← hg]
  exact mat_frobAut g

theorem sixFF_ff3a_pow_antiUnipotent (k : ℕ) :
    ∀ g ∈ antiUnipotent K, (frobAut K ^ k) g ∈ antiUnipotent K :=
  sixFF_ff3a_frob_pow_mem _ sixFF_ff3a_frob_antiUnipotent k

theorem sixFF_ff3a_pow_diagTorus (k : ℕ) :
    ∀ g ∈ diagTorus K, (frobAut K ^ k) g ∈ diagTorus K :=
  sixFF_ff3a_frob_pow_mem _ sixFF_ff3a_frob_diagTorus k

theorem sixFF_ff3a_conj_symm (f : normalizer (L : Set G)) (a : antiSp K) :
    (f : G) * ((φ.symm a : L) : G) * (f : G)⁻¹ =
      ((φ.symm (FieldInvolution.transAct φ f a) : L) : G) :=
  (FieldInvolution.coe_symm_transAct φ f a).symm

theorem sixFF_ff3a_conj_pull (f : normalizer (L : Set G)) (k : ℕ)
    (hk : FieldInvolution.transAct φ f = frobAut K ^ k) (H : Subgroup (antiSp K))
    (hH : ∀ a ∈ H, (frobAut K ^ k) a ∈ H) :
    ∀ x ∈ pull φ H, (f : G) * x * (f : G)⁻¹ ∈ pull φ H := by
  intro x hx
  obtain ⟨h, hxH⟩ := mem_pull.mp hx
  have hx' : ((φ.symm (φ ⟨x, h⟩) : L) : G) = x := by simp
  rw [← hx', sixFF_ff3a_conj_symm, symm_mem_pull, hk]
  exact hH _ hxH

theorem sixFF_ff3a_conj_zpowers {f e : G} (hfC : f ∈ centralizer ({e} : Set G)) :
    ∀ x ∈ zpowers e, f * x * f⁻¹ ∈ zpowers e := by
  intro x hx
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  have hc : Commute f e := (mem_centralizer_iff.mp hfC e (Set.mem_singleton e)).symm
  rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
  exact zpow_mem_zpowers e m

theorem sixFF_ff3a_conj_map (f c : G) (hfc : f * c = c * f) (M : Subgroup G)
    (hM : ∀ x ∈ M, f * x * f⁻¹ ∈ M) :
    ∀ x ∈ M.map (MulAut.conj c).toMonoidHom,
      f * x * f⁻¹ ∈ M.map (MulAut.conj c).toMonoidHom := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨f * y * f⁻¹, hM y hy, ?_⟩
  show c * (f * y * f⁻¹) * c⁻¹ = f * (c * y * c⁻¹) * f⁻¹
  calc c * (f * y * f⁻¹) * c⁻¹ = (c * f) * y * (c * f)⁻¹ := by group
    _ = (f * c) * y * (f * c)⁻¹ := by rw [hfc]
    _ = f * (c * y * c⁻¹) * f⁻¹ := by group

theorem sixFF_ff3a_weyl_fixed (k : ℕ) (ax : Axis) :
    (frobAut K ^ k) (FullCenterWeyl.weylElt K ax) = FullCenterWeyl.weylElt K ax := by
  apply FieldInvolution.frobAut_pow_eq_self k
  intro a b
  cases ax <;> fin_cases a <;> fin_cases b <;>
    simp [mat, FullCenterWeyl.glMat_weylElt, FullCenterWeyl.weylMat]

theorem sixFF_ff3a_comm_w (f : normalizer (L : Set G)) (k : ℕ)
    (hk : FieldInvolution.transAct φ f = frobAut K ^ k) (ax : Axis) :
    (f : G) * w φ ax = w φ ax * (f : G) := by
  have h : (f : G) * w φ ax * (f : G)⁻¹ = w φ ax := by
    have h0 := sixFF_ff3a_conj_symm (φ := φ) f (FullCenterWeyl.weylElt K ax)
    rw [hk, sixFF_ff3a_weyl_fixed k ax] at h0
    exact h0
  calc (f : G) * w φ ax = ((f : G) * w φ ax * (f : G)⁻¹) * (f : G) := by group
    _ = w φ ax * (f : G) := by rw [h]

theorem sixFF_ff3a (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    FF3aConcl φ t i := by
  intro f hfC k hk
  have hP : ∀ x ∈ P φ, (f : G) * x * (f : G)⁻¹ ∈ P φ :=
    sixFF_ff3a_conj_pull (φ := φ) f k hk (antiUnipotent K) (sixFF_ff3a_pow_antiUnipotent k)
  have hZ : ∀ x ∈ zpowers t, (f : G) * x * (f : G)⁻¹ ∈ zpowers t :=
    sixFF_ff3a_conj_zpowers hfC
  have hQ : ∀ x ∈ Q φ t, (f : G) * x * (f : G)⁻¹ ∈ Q φ t :=
    fun x hx => RootAxisTwoCore.conj_mem_sup hP hZ hx
  have hfQ : (f : G) ∈ normalizer ((Q φ t : Subgroup G) : Set G) :=
    RootAxisTwoCore.mem_normalizer_of_conj_le hQ
  have hfD : (f : G) ∈ normalizer ((D φ t i : Subgroup G) : Set G) :=
    canon_N5_4 hS.fc i hS.ne_bot hS.eq_bot hfC hfQ
  have hfEn : (f : G) ∈ En φ t i.swap := canon_N5_7 hS.fc i hS.ne_bot hS.eq_bot hfQ
  have hfTp : (f : G) ∈ normalizer (Tplus φ t i : Set G) :=
    canon_N5_8 hS.fc i hS.ne_bot hS.eq_bot hfC hfQ
  have hP₁ : ∀ x ∈ P₁ φ t i, (f : G) * x * (f : G)⁻¹ ∈ P₁ φ t i :=
    fun x hx => FullCenter.conj_mem_pCore_map hfD hx
  have hP₂ : ∀ x ∈ P₂ φ t i.swap, (f : G) * x * (f : G)⁻¹ ∈ P₂ φ t i.swap :=
    fun x hx => FullCenter.conj_mem_pCore_map hfEn hx
  have hP₀ : ∀ x ∈ P₀ φ t i, (f : G) * x * (f : G)⁻¹ ∈ P₀ φ t i :=
    fun x hx => mem_inf.mpr ⟨hP₁ x (mem_inf.mp hx).1, hP₂ x (mem_inf.mp hx).2⟩
  have hJ : ∀ x ∈ J₀ φ, (f : G) * x * (f : G)⁻¹ ∈ J₀ φ :=
    sixFF_ff3a_conj_pull (φ := φ) f k hk (diagTorus K) (sixFF_ff3a_pow_diagTorus k)
  have hMc : ∀ x ∈ Mc φ t i, (f : G) * x * (f : G)⁻¹ ∈ Mc φ t i := by
    apply sixFF_ff3a_conj_closure
    rintro x ⟨p, hp, j, hj, rfl⟩
    exact subset_closure ⟨(f : G) * p * (f : G)⁻¹, hP₀ p hp,
      (f : G) * j * (f : G)⁻¹, hJ j hj, by group⟩
  have hMw : ∀ ax : Axis, ∀ x ∈ Mw φ t i ax, (f : G) * x * (f : G)⁻¹ ∈ Mw φ t i ax := by
    intro ax
    have hc : (f : G) * (w φ ax)⁻¹ = (w φ ax)⁻¹ * (f : G) :=
      (show Commute (f : G) (w φ ax) from sixFF_ff3a_comm_w f k hk ax).inv_right.eq
    exact sixFF_ff3a_conj_map (f : G) (w φ ax)⁻¹ hc (Mc φ t i) hMc
  have hMhat : ∀ ax : Axis, ∀ x ∈ Mhat φ t i ax, (f : G) * x * (f : G)⁻¹ ∈ Mhat φ t i ax :=
    fun ax x hx => RootAxisTwoCore.conj_mem_sup hMc (hMw ax) hx
  have hSt : ∀ x ∈ S φ t i, (f : G) * x * (f : G)⁻¹ ∈ S φ t i :=
    fun x hx => RootAxisTwoCore.conj_mem_sup (hMhat Axis.one) (hMhat Axis.two) hx
  exact ⟨RootAxisTwoCore.mem_normalizer_of_conj_le hSt, hfTp⟩

theorem sixFF_ff3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hK : SixKConclusion φ t i) (f0 : FF0Concl φ t i) (f1 : FF1Concl φ t i)
    (f2 : FF2Concl n φ t i) (f3a : FF3aConcl φ t i) : FF3Concl φ t i := by
  intro g hg
  have hST : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]
    exact le_sup_left
  have hPS : P φ ≤ S φ t i := by
    rw [← hK.centralizer_S]
    exact inf_le_left
  have hJS : ∀ x ∈ J₀ φ, x ∈ normalizer (S φ t i : Set G) := by
    intro x hx
    obtain ⟨-, -, hJ1⟩ := hH.normal_Mhat Axis.one
    obtain ⟨-, -, hJ2⟩ := hH.normal_Mhat Axis.two
    have h1 : x ∈ normalizer (Mhat φ t i Axis.one : Set G) := hJ1 hx
    have h2 : x ∈ normalizer (Mhat φ t i Axis.two : Set G) := hJ2 hx
    exact RootAxisTwoCore.mem_normalizer_of_conj_le fun y hy =>
      RootAxisTwoCore.conj_mem_sup (fun z hz => canon_conj_of_normalizer h1 hz)
        (fun z hz => canon_conj_of_normalizer h2 hz) hy
  obtain ⟨s, hs, hgs⟩ := f0 g hg
  have hsT : s ∈ normalizer (Tplus φ t i : Set G) :=
    (Subgroup.le_normalizer : Tplus φ t i ≤ normalizer (Tplus φ t i : Set G)) (hST hs)
  have hsS : s ∈ normalizer (S φ t i : Set G) :=
    (Subgroup.le_normalizer : S φ t i ≤ normalizer (S φ t i : Set G)) hs
  have hhN : g * s⁻¹ ∈ normalizer (Tplus φ t i : Set G) := mul_mem hg (inv_mem hsT)
  obtain ⟨hhP, hhUi, hhUj⟩ := f1 (g * s⁻¹) hhN hgs
  have hhL : g * s⁻¹ ∈ normalizer (L : Set G) := hS.fc.setup.cent_le hgs
  obtain ⟨p, hp, j, hj, k, -, hpj⟩ := f2 ⟨g * s⁻¹, hhL⟩ hgs hhP hhUi hhUj
  obtain ⟨A, hA⟩ : ∃ A : L, φ A = p * j := ⟨φ.symm (p * j), by simp⟩
  have hAC : (A : G) ∈ centralizer ({t} : Set G) := hS.fc.setup.L_le A.2
  have hAN : (A : G) ∈ normalizer (L : Set G) := hS.fc.setup.cent_le hAC
  have hA' : A = φ.symm p * φ.symm j := by
    apply φ.injective
    rw [hA, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hPn : ((φ.symm p : L) : G) ∈ normalizer (S φ t i : Set G) :=
    (Subgroup.le_normalizer : S φ t i ≤ normalizer (S φ t i : Set G))
      (hPS ((symm_mem_pull (φ := φ)).mpr hp))
  have hJn : ((φ.symm j : L) : G) ∈ normalizer (S φ t i : Set G) :=
    hJS _ ((symm_mem_pull (φ := φ)).mpr hj)
  have hAS : (A : G) ∈ normalizer (S φ t i : Set G) := by
    rw [hA', Subgroup.coe_mul]
    exact mul_mem hPn hJn
  have hTr : FieldInvolution.transAct φ (⟨(A : G), hAN⟩ : normalizer (L : Set G)) =
      MulAut.conj (p * j) := by
    rw [FieldInvolution.transAct_of_mem φ ⟨(A : G), hAN⟩ A.2]
    congr 1
  obtain ⟨F, hFdef⟩ : ∃ F : normalizer (L : Set G),
      F = (⟨(A : G), hAN⟩ : normalizer (L : Set G))⁻¹ * ⟨g * s⁻¹, hhL⟩ := ⟨_, rfl⟩
  have hFC : (F : G) ∈ centralizer ({t} : Set G) := by
    rw [hFdef, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem hAC) hgs
  have hFk : FieldInvolution.transAct φ F = frobAut K ^ k := by
    rw [hFdef, map_mul, map_inv, hTr, hpj, inv_mul_cancel_left]
  have hFG : (F : G) = (A : G)⁻¹ * (g * s⁻¹) := by
    subst hFdef
    rfl
  have hFS : (F : G) ∈ normalizer (S φ t i : Set G) := (f3a F hFC k hFk).1
  have hgeq : g = (A : G) * (F : G) * s := by
    rw [hFG]
    group
  rw [hgeq]
  exact mul_mem (mul_mem hAS hFS) hsS

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
