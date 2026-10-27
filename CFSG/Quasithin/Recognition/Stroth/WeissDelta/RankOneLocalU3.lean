module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic
public import CFSG.Quasithin.Recognition.Stroth.LemmaSDegree
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GorensteinWalter
open scoped LinearAlgebra.Projectivization MatrixGroups

instance instMulActionUnitaryIsotropicPoints {K : Type} [Field K] (J : HermitianForm 3 K) :
    MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
  CFSG.UnitaryThreeRecognition.Model.instMulActionIsoPoint (J := J)

@[simp] theorem coe_smul_unitaryIsotropicPoints {K : Type} [Field K] (J : HermitianForm 3 K)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) (x : unitaryIsotropicPoints J) :
    ((g • x : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) =
      (g : Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) := rfl

structure UnitaryPointStructure (G Ω : Type*) [Group G] [MulAction G Ω] (α β : Ω)
    (U T B : Subgroup G) : Prop where
  isMultiplyPretransitive : MulAction.IsMultiplyPretransitive G Ω 2
  ne : α ≠ β
  sup_eq_stabilizer : U ⊔ T = MulAction.stabilizer G α
  inf_eq_bot : U ⊓ T = ⊥
  eq_stabilizer : B = MulAction.stabilizer G α
  root_normal : (U.subgroupOf B).Normal
  stabilizer_inf_stabilizer : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β = T
  isCyclic_T : IsCyclic T
  odd_T : Odd (Nat.card T)
  regular : ∀ x y : Ω, x ≠ α → y ≠ α → ∃! u : U, (u : G) • x = y
  fix_T : ∀ x : Ω, (∀ t ∈ T, t • x = x) → x = α ∨ x = β
  exists_ne_ne : ∀ a b : Ω, ∃ c : Ω, c ≠ a ∧ c ≠ b

namespace UnitaryPointStructure

variable {G Ω : Type*} [Group G] [MulAction G Ω] {α β : Ω} {U T B : Subgroup G}

theorem map_conj_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (C : Subgroup A) (x : A) :
    (C.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (C.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext c
  simp [MulAut.conj_apply]

theorem regular_map_conj {G Ω : Type*} [Group G] [MulAction G Ω] {U : Subgroup G} {α : Ω}
    (h : ∀ x y : Ω, x ≠ α → y ≠ α → ∃! u : U, (u : G) • x = y) (g : G) :
    ∀ x y : Ω, x ≠ g • α → y ≠ g • α →
      ∃! u : U.map (MulAut.conj g).toMonoidHom, (u : G) • x = y := by
  intro x y hx hy
  have hx' : g⁻¹ • x ≠ α := fun h' => hx (by rw [← h', smul_inv_smul])
  have hy' : g⁻¹ • y ≠ α := fun h' => hy (by rw [← h', smul_inv_smul])
  obtain ⟨u, hu, huniq⟩ := h _ _ hx' hy'
  refine ⟨⟨g * (u : G) * g⁻¹, Subgroup.mem_map_of_mem _ u.2⟩, ?_, ?_⟩
  · show (g * (u : G) * g⁻¹) • x = y
    calc (g * (u : G) * g⁻¹) • x = g • ((u : G) • (g⁻¹ • x)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • y) := by rw [hu]
      _ = y := smul_inv_smul g y
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp v.2
    have hcongr : (w : G) • (g⁻¹ • x) = g⁻¹ • y := by
      have h := congrArg (fun z => g⁻¹ • z) hv
      rw [← hwv] at h
      simpa [mul_smul] using h
    have hEq : w = (u : G) := congrArg Subtype.val (huniq ⟨w, hw⟩ hcongr)
    apply Subtype.ext
    show (v : G) = g * (u : G) * g⁻¹
    rw [← hwv, hEq]
    simp [MulAut.conj_apply]

theorem exists_conj_torus (h : UnitaryPointStructure G Ω α β U T B) {a y : Ω} (hay : y ≠ a) :
    ∃ g : G, g • α = a ∧ g • β = y ∧
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G y =
        T.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hga, hgy⟩ :=
    MulAction.is_two_pretransitive_iff.mp h.isMultiplyPretransitive hay.symm h.ne
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply]
    group
  have ha : MulAction.stabilizer G a =
      (MulAction.stabilizer G α).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hga, MulAction.stabilizer_smul_eq_stabilizer_map_conj g a, Subgroup.map_map, hcomp,
      Subgroup.map_id]
  have hy : MulAction.stabilizer G y =
      (MulAction.stabilizer G β).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hgy, MulAction.stabilizer_smul_eq_stabilizer_map_conj g y, Subgroup.map_map, hcomp,
      Subgroup.map_id]
  refine ⟨g⁻¹, ?_, ?_, ?_⟩
  · rw [← hga, inv_smul_smul]
  · rw [← hgy, inv_smul_smul]
  · rw [ha, hy, ← Subgroup.map_inf (MulAction.stabilizer G α) (MulAction.stabilizer G β)
      _ (MulAut.conj g⁻¹).injective, h.stabilizer_inf_stabilizer]

theorem fix_stabilizer_inf' (h : UnitaryPointStructure G Ω α β U T B) {a y x : Ω} (hay : y ≠ a)
    (hx : ∀ t ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G y, t • x = x) :
    x = a ∨ x = y := by
  obtain ⟨g, hga, hgy⟩ :=
    MulAction.is_two_pretransitive_iff.mp h.isMultiplyPretransitive hay.symm h.ne
  have hfix : ∀ t ∈ T, t • (g • x) = g • x := by
    intro t ht
    have hmemT : t ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
      rw [h.stabilizer_inf_stabilizer]
      exact ht
    have hta : t • α = α :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hmemT).1
    have htb : t • β = β :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hmemT).2
    have hmem : g⁻¹ * t * g ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G y := by
      constructor
      · change (g⁻¹ * t * g) • a = a
        calc (g⁻¹ * t * g) • a = g⁻¹ • (t • (g • a)) := by rw [mul_smul, mul_smul]
          _ = g⁻¹ • (t • α) := by rw [hga]
          _ = g⁻¹ • α := by rw [hta]
          _ = a := by rw [← hga, inv_smul_smul]
      · change (g⁻¹ * t * g) • y = y
        calc (g⁻¹ * t * g) • y = g⁻¹ • (t • (g • y)) := by rw [mul_smul, mul_smul]
          _ = g⁻¹ • (t • β) := by rw [hgy]
          _ = g⁻¹ • β := by rw [htb]
          _ = y := by rw [← hgy, inv_smul_smul]
    have h1 : (g⁻¹ * t * g) • x = x := hx _ hmem
    calc t • (g • x) = (t * g) • x := (mul_smul t g x).symm
      _ = (g * (g⁻¹ * t * g)) • x := by
          rw [show g * (g⁻¹ * t * g) = t * g by group]
      _ = g • ((g⁻¹ * t * g) • x) := mul_smul g (g⁻¹ * t * g) x
      _ = g • x := by rw [h1]
  rcases h.fix_T _ hfix with h' | h'
  · left
    calc x = g⁻¹ • (g • x) := (inv_smul_smul g x).symm
      _ = g⁻¹ • α := by rw [h']
      _ = a := by rw [← hga, inv_smul_smul]
  · right
    calc x = g⁻¹ • (g • x) := (inv_smul_smul g x).symm
      _ = g⁻¹ • β := by rw [h']
      _ = y := by rw [← hgy, inv_smul_smul]

theorem pair_eq_stabilizer_inf {X Ω : Type*} [Group X] [MulAction X Ω] (N : Subgroup X)
    (ω ω' : Ω) :
    (N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') =
      (MulAction.stabilizer ↥N ω ⊓ MulAction.stabilizer ↥N ω').map N.subtype := by
  ext x
  constructor
  · rintro ⟨⟨hxN, hxω⟩, hxω'⟩
    exact ⟨⟨x, hxN⟩, ⟨by simpa using hxω, by simpa using hxω'⟩, rfl⟩
  · rintro ⟨n, ⟨hnω, hnω'⟩, rfl⟩
    refine ⟨⟨n.2, ?_⟩, ?_⟩
    · change (n : X) • ω = ω
      exact hnω
    · change (n : X) • ω' = ω'
      exact hnω'

end UnitaryPointStructure

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)

theorem fix_torusPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : ℕ) (hk : 2 ≤ k) (hcard : Nat.card K = (2 ^ k) ^ 2)
    (hconj : ∀ c : K, J.conj c = c ^ (2 ^ k)) (lam : Kˣ)
    (hlam : orderOf lam = Nat.card Kˣ) (x : unitaryIsotropicPoints J)
    (hx : (torusPSU J hJ lam) • x = x) :
    x = unitaryOuterIsotropicPoint J hJ 0 (by decide) ∨
      x = unitaryOuterIsotropicPoint J hJ 2 (by decide) := by
  classical
  obtain ⟨v, hv, hxv, hiso⟩ := x.2
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hbig : 2 * 2 ^ k ≤ (2 ^ k) ^ 2 - 1 := by
    have h2 : 2 * 2 ^ k + 1 ≤ (2 ^ k) ^ 2 := by
      rw [pow_two]
      calc 2 * 2 ^ k + 1 ≤ 4 * 2 ^ k := by omega
        _ = 2 ^ k * 4 := by ring
        _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_left (2 ^ k) hq4
    omega
  have hlamne : (lam : K) ≠ 0 := Units.ne_zero lam
  have hconjne : J.conj (lam : K) ≠ 0 := by
    intro h
    exact hlamne (J.conj.injective (by rw [h, map_zero]))
  have hord : orderOf (lam : K) = (2 ^ k) ^ 2 - 1 := by
    rw [orderOf_units, hlam, Nat.card_units, hcard]
  have hkey : ∀ m : ℕ, (lam : K) ^ m = 1 → m = 0 ∨ (2 ^ k) ^ 2 - 1 ≤ m := by
    intro m hm
    have hd : (2 ^ k) ^ 2 - 1 ∣ m := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (Nat.le_of_dvd hpos hd)
  have hcoe : ((torusPSU J hJ lam : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) =
      Projectivization.mk K
        (((torusGL J lam : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne (torusGL J lam)).2 hv) := by
    rw [torusPSU_val, hxv, Projectivization.PGL.mk_smul_mk]
    rfl
  have hx' : ((torusPSU J hJ lam : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) =
        (x : ℙ K (Fin 3 → K)) := by
    have h := congrArg Subtype.val hx
    rwa [coe_smul_unitaryIsotropicPoints] at h
  have hproj : Projectivization.mk K
        (((torusGL J lam : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne (torusGL J lam)).2 hv) = Projectivization.mk K v hv := by
    rw [← hxv, ← hx', hcoe]
  obtain ⟨mu, hmu⟩ := (Projectivization.mk_eq_mk_iff' K _ v _ hv).mp hproj
  have h0 : mu * v 0 = (lam : K) * v 0 := by
    have h := congrFun hmu 0
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have h1 : mu * v 1 = (J.conj (lam : K) / (lam : K)) * v 1 := by
    have h := congrFun hmu 1
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have h2 : mu * v 2 = (J.conj (lam : K))⁻¹ * v 2 := by
    have h := congrFun hmu 2
    simpa [torusGL_val, torusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, smul_eq_mul] using h
  have hv1 : v 1 = 0 := by
    by_contra hv1
    by_cases hv0 : v 0 = 0
    · by_cases hv2 : v 2 = 0
      · exfalso
        have hiso0 : J.conj (v 1) * v 1 = 0 := by
          have h := hiso
          rw [CFSG.UnitaryThreeRecognition.Model.selfPairing_std J hJ] at h
          simpa [hv0, hv2] using h
        rw [hconj] at hiso0
        have hq : (2 ^ k) ≠ 0 := by positivity
        rcases mul_eq_zero.mp hiso0 with h' | h'
        · exact hv1 ((pow_eq_zero_iff hq).mp h')
        · exact hv1 h'
      · have hmu1 : mu = J.conj (lam : K) / (lam : K) := mul_right_cancel₀ hv1 h1
        have hmu2 : mu = (J.conj (lam : K))⁻¹ := mul_right_cancel₀ hv2 h2
        have heq : J.conj (lam : K) / (lam : K) = (J.conj (lam : K))⁻¹ :=
          hmu1.symm.trans hmu2
        have hsq : (J.conj (lam : K)) ^ 2 = (lam : K) := by
          have h1' : J.conj (lam : K) = (J.conj (lam : K))⁻¹ * (lam : K) := by
            have h := congrArg (fun t => t * (lam : K)) heq
            rwa [div_mul_cancel₀ _ hlamne] at h
          calc (J.conj (lam : K)) ^ 2 = J.conj (lam : K) * J.conj (lam : K) := pow_two _
            _ = ((J.conj (lam : K))⁻¹ * (lam : K)) * J.conj (lam : K) :=
                congrArg (fun t => t * J.conj (lam : K)) h1'
            _ = (J.conj (lam : K))⁻¹ * ((lam : K) * J.conj (lam : K)) :=
                mul_assoc _ _ _
            _ = (J.conj (lam : K))⁻¹ * (J.conj (lam : K) * (lam : K)) := by
                rw [mul_comm (lam : K) (J.conj (lam : K))]
            _ = ((J.conj (lam : K))⁻¹ * J.conj (lam : K)) * (lam : K) :=
                (mul_assoc _ _ _).symm
            _ = (lam : K) := by rw [inv_mul_cancel₀ hconjne, one_mul]
        have h2q : (lam : K) ^ (2 * 2 ^ k) = (lam : K) := by
          rw [mul_comm 2 (2 ^ k), pow_mul, ← hconj, hsq]
        have hpow : (lam : K) ^ (2 * 2 ^ k - 1) = 1 := by
          have hmain : (lam : K) ^ (2 * 2 ^ k - 1) * (lam : K) = 1 * (lam : K) := by
            rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
            exact h2q
          exact mul_right_cancel₀ hlamne hmain
        rcases hkey _ hpow with h' | h'
        · omega
        · omega
    · have hmu1 : mu = J.conj (lam : K) / (lam : K) := mul_right_cancel₀ hv1 h1
      have hmu0 : mu = (lam : K) := mul_right_cancel₀ hv0 h0
      have heq : (lam : K) = J.conj (lam : K) / (lam : K) := hmu0.symm.trans hmu1
      have hsq : (lam : K) ^ 2 = J.conj (lam : K) := by
        have h := congrArg (fun t => t * (lam : K)) heq
        rw [div_mul_cancel₀ _ hlamne] at h
        rw [pow_two]
        exact h
      have h2q : (lam : K) ^ (2 ^ k) = (lam : K) ^ 2 := by
        rw [← hconj]
        exact hsq.symm
      have hpow : (lam : K) ^ (2 ^ k - 2) = 1 := by
        have hmain : (lam : K) ^ (2 ^ k - 2) * (lam : K) ^ 2 = 1 * (lam : K) ^ 2 := by
          rw [one_mul, ← pow_add, Nat.sub_add_cancel (by omega), h2q]
        exact mul_right_cancel₀ (pow_ne_zero 2 hlamne) hmain
      rcases hkey _ hpow with h' | h'
      · omega
      · omega
  by_cases hv0 : v 0 = 0
  · right
    have hv2 : v 2 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i <;> simp [hv0, hv1, h]
    apply Subtype.ext
    show (x : ℙ K (Fin 3 → K)) = Projectivization.mk K (Pi.single 2 1) _
    rw [hxv, Projectivization.mk_eq_mk_iff']
    refine ⟨v 2, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.single_apply, hv0, hv1]
  · left
    have hv2 : v 2 = 0 := by
      by_contra hv2
      have hmu0 : mu = (lam : K) := mul_right_cancel₀ hv0 h0
      have hmu2 : mu = (J.conj (lam : K))⁻¹ := mul_right_cancel₀ hv2 h2
      have heq : (lam : K) = (J.conj (lam : K))⁻¹ := hmu0.symm.trans hmu2
      have hq1 : (lam : K) ^ (2 ^ k + 1) = 1 := by
        have hmul : (lam : K) * J.conj (lam : K) = 1 := by
          have h := congrArg (fun t => t * J.conj (lam : K)) heq
          rw [inv_mul_cancel₀ hconjne] at h
          exact h
        rw [hconj, mul_comm] at hmul
        rwa [← pow_succ] at hmul
      rcases hkey _ hq1 with h' | h'
      · omega
      · omega
    apply Subtype.ext
    show (x : ℙ K (Fin 3 → K)) = Projectivization.mk K (Pi.single 0 1) _
    rw [hxv, Projectivization.mk_eq_mk_iff']
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [Pi.single_apply, hv1, hv2]

theorem unitaryPointStructure (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : ℕ) (hk : 2 ≤ k) (hcard : Nat.card K = (2 ^ k) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ k) :
    UnitaryPointStructure (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J)
      (unitaryOuterIsotropicPoint J hJ 0 (by decide))
      (unitaryOuterIsotropicPoint J hJ 2 (by decide))
      ((hermitianUnipotentPSU J hJ).range) ((torusPSU J hJ).range)
      (unitaryCoordinateStabilizer J 0) := by
  obtain ⟨hconj, -, -, -, -, rho, hrho, hnative, hcardΩ, h2, hstab, hstabβ, hnormal, hUT,
    hUTsup, hTeq, hTcyc, hTcard, ⟨S, hS⟩, hUcard, hreg, -⟩ :=
    unitary_three_point_structure J k hk hcard hfixed hJ
  have hrho_fix : ∀ (g : ProjectiveSpecialUnitaryMatrixGroup J)
      (p : unitaryIsotropicPoints J), rho g p = g • p := by
    intro g p
    exact Subtype.ext (by rw [coe_smul_unitaryIsotropicPoints]; exact hnative g p)
  have hstabB : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryOuterIsotropicPoint J hJ 0 (by decide)) = unitaryCoordinateStabilizer J 0 := by
    rw [← hstab]
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def, hrho_fix]
  have hstabBβ : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryOuterIsotropicPoint J hJ 2 (by decide)) = unitaryCoordinateStabilizer J 2 := by
    rw [← hstabβ]
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def, hrho_fix]
  have hodd : Odd (Nat.card ↥(torusPSU J hJ).range) := by
    rw [hTcard]
    have hsq : (2 ^ k) ^ 2 - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ k) 1
    have hdvd : Nat.gcd 3 (2 ^ k + 1) ∣ (2 ^ k) ^ 2 - 1 :=
      (Nat.gcd_dvd_right 3 (2 ^ k + 1)).trans ⟨2 ^ k - 1, hsq⟩
    have hEven : Even ((2 ^ k) ^ 2) := by
      rw [Nat.even_pow]
      exact ⟨Nat.even_pow.mpr ⟨⟨1, by norm_num⟩, by omega⟩, by norm_num⟩
    exact Odd.of_dvd_nat (Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) hEven
      odd_one) (Nat.div_dvd_of_dvd hdvd)
  refine
    { isMultiplyPretransitive := ?_
      ne := ?_
      sup_eq_stabilizer := by rw [hUTsup, hstabB]
      eq_stabilizer := hstabB.symm
      root_normal := hnormal
      inf_eq_bot := hUT
      stabilizer_inf_stabilizer := by rw [hstabB, hstabBβ, ← hTeq]
      isCyclic_T := hTcyc
      odd_T := hodd
      regular := ?_
      fix_T := ?_
      exists_ne_ne := ?_ }
  · rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := h2 a b c d hab hcd
    exact ⟨g, hrho_fix g a ▸ hg1, hrho_fix g b ▸ hg2⟩
  · intro h
    have h' : unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint (K := K) 2 := by
      have hval := congrArg Subtype.val h
      simpa [unitaryOuterIsotropicPoint] using hval
    exact unitaryCoordinatePoint_two_ne_zero h'.symm
  · intro a b ha hb
    obtain ⟨u, hu, huniq⟩ := hreg a b ha hb
    refine ⟨u, ?_, ?_⟩
    · exact (hrho_fix (u : ProjectiveSpecialUnitaryMatrixGroup J) a).symm.trans hu
    · intro v hv
      exact huniq v ((hrho_fix (v : ProjectiveSpecialUnitaryMatrixGroup J) a).trans hv)
  · intro x hxT
    obtain ⟨lam, hlam⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    exact fix_torusPSU J hJ k hk hcard hconj lam hlam x
      (hxT _ (MonoidHom.mem_range.mpr ⟨lam, rfl⟩))
  · intro a b
    by_contra hcon
    push Not at hcon
    have hle : Nat.card (unitaryIsotropicPoints J) ≤ 2 := by
      have hsub : (Set.univ : Set (unitaryIsotropicPoints J)) ⊆ ({a, b} : Set _) := by
        intro x _
        rcases eq_or_ne x a with rfl | hxa
        · simp
        · have hxb : x = b := hcon x hxa
          simp [hxb]
      calc Nat.card (unitaryIsotropicPoints J) = (Set.univ : Set _).ncard := by simp
        _ ≤ ({a, b} : Set (unitaryIsotropicPoints J)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
            rcases eq_or_ne a b with rfl | hab
            · simp
            · rw [Set.ncard_pair hab]
    rw [hcardΩ] at hle
    have hq4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith [hle, hq4]

end Model

end CFSG.Quasithin.Stroth.WeissDelta
