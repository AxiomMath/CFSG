module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFacts2
public import CFSG.RankThree.GF2n.Smith81.OrthE1Small

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Mult

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]

@[expose] def caseASylow_Mult (φg : E ≃ₗ[K] E) (β : E →ₗ[K] E) (c : K) : Prop :=
  ∀ e, φg (β e) = c • β (φg e)

theorem caseASylow_Mult_mul {φg φh : E ≃ₗ[K] E} {β : E →ₗ[K] E} {c d : K}
    (hg : caseASylow_Mult φg β c) (hh : caseASylow_Mult φh β d) :
    caseASylow_Mult (φg * φh) β (d * c) := by
  intro e
  simp only [LinearEquiv.mul_apply]
  rw [hh e, map_smul, hg (φh e), smul_smul]

theorem caseASylow_Mult_one (β : E →ₗ[K] E) :
    caseASylow_Mult (1 : E ≃ₗ[K] E) β 1 := by
  intro e
  simp

theorem caseASylow_Mult_pow {φg : E ≃ₗ[K] E} {β : E →ₗ[K] E} {c : K}
    (hg : caseASylow_Mult φg β c) (n : ℕ) : caseASylow_Mult (φg ^ n) β (c ^ n) := by
  induction n with
  | zero =>
    simpa using caseASylow_Mult_one β
  | succ n ih =>
    have h := caseASylow_Mult_mul ih hg
    rw [pow_succ, pow_succ, mul_comm]
    exact h

theorem caseASylow_Mult_unique {φg : E ≃ₗ[K] E} {β : E →ₗ[K] E} {c c' : K}
    (hβ : ∃ e0, β e0 ≠ 0) (hc : caseASylow_Mult φg β c) (hc' : caseASylow_Mult φg β c') :
    c = c' := by
  obtain ⟨e0, he0⟩ := hβ
  have h1 := hc (φg.symm e0)
  have h2 := hc' (φg.symm e0)
  simp only [LinearEquiv.apply_symm_apply] at h1 h2
  have h3 : c • β e0 = c' • β e0 := h1.symm.trans h2
  exact smul_left_injective K he0 h3

theorem caseASylow_mult_one_of_comm {φw φt : E ≃ₗ[K] E} {β : E →ₗ[K] E} {c : K} (hc : c ≠ 0)
    (ht : ∀ e, φt e = e + c • β e) (hcomm : φw * φt = φt * φw) :
    caseASylow_Mult φw β 1 := by
  intro e
  have h1 := congrArg (fun f : E ≃ₗ[K] E => f e) hcomm
  simp only [LinearEquiv.mul_apply, ht, map_add, map_smul] at h1
  have h2 : c • φw (β e) = c • β (φw e) := add_left_cancel h1
  have h3 : φw (β e) = β (φw e) := by
    have h4 := congrArg (fun v => c⁻¹ • v) h2
    simpa [smul_smul, inv_mul_cancel₀ hc] using h4
  rw [one_smul]
  exact h3

theorem caseASylow_comm_of_mult_one {φw φx : E ≃ₗ[K] E} {β : E →ₗ[K] E} {c : K}
    (hw : caseASylow_Mult φw β 1) (hx : ∀ e, φx e = e + c • β e) :
    φw * φx = φx * φw := by
  have hw' : ∀ e, φw (β e) = β (φw e) := fun e => by
    have h := hw e
    rwa [one_smul] at h
  apply LinearEquiv.ext
  intro e
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx e, hx (φw e), map_add, map_smul, hw' e]

end Mult

theorem caseASylow_eq_one_of_two_pow {K : Type} [Field K] [CharP K 2] {c : K} {k : ℕ}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp h1).1

section Line

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {t : G}

theorem caseASylow_Nt_isPGroup (M L : Subgroup G) (t : G) : IsPGroup 2 ↥(Nt M L t) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Rt M L t))).of_equiv
    (Subgroup.equivMapOfInjective _ (Rt M L t).subtype (Subgroup.subtype_injective _))

theorem caseASylow_comm_iff (AM : ActionModel M Q Z) {x y : G} (hx : x ∈ H0 M Z)
    (hy : y ∈ H0 M Z) :
    ⁅x, y⁆ ∈ Q ↔ AM.φ ⟨x, hx⟩ * AM.φ ⟨y, hy⟩ = AM.φ ⟨y, hy⟩ * AM.φ ⟨x, hx⟩ := by
  have hm : ⁅x, y⁆ ∈ H0 M Z := by
    rw [commutatorElement_def]
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).mul_mem hx hy) ((H0 M Z).inv_mem hx))
      ((H0 M Z).inv_mem hy)
  have he : AM.φ ⟨⁅x, y⁆, hm⟩ = ⁅AM.φ ⟨x, hx⟩, AM.φ ⟨y, hy⟩⁆ := by
    rw [← map_commutatorElement]
    congr 1
  rw [← commutatorElement_eq_one_iff_mul_comm, ← he]
  exact (AM.φ_ker ⟨⁅x, y⁆, hm⟩).symm

theorem caseASylow_coeff_ne (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (htN : t ∈ Nt M (LB M Q B) t) (htQ : t ∉ Q) (htH : t ∈ H0 M Z) :
    ∃ c : AM.K, c ≠ 0 ∧ ∀ e, AM.φ ⟨t, htH⟩ e = e + c • β e := by
  obtain ⟨c, hc⟩ := hL3 ⟨t, htH⟩ htN
  refine ⟨c, ?_, hc⟩
  rintro rfl
  apply htQ
  apply (AM.φ_ker ⟨t, htH⟩).mp
  apply LinearEquiv.ext
  intro e
  rw [hc e, zero_smul, add_zero]
  rfl

theorem caseASylow_beta_ne (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (htN : t ∈ Nt M (LB M Q B) t) (htQ : t ∉ Q) (htH : t ∈ H0 M Z) :
    ∃ e0, β e0 ≠ 0 := by
  obtain ⟨c, -, hc⟩ := caseASylow_coeff_ne AM hL3 htN htQ htH
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  apply htQ
  apply (AM.φ_ker ⟨t, htH⟩).mp
  apply LinearEquiv.ext
  intro e
  rw [hc e, h e, smul_zero, add_zero]
  rfl

theorem caseASylow_mult_exists (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hL4 : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    {g : G} (hg : g ∈ H0 M Z)
    (hgN : ∀ n ∈ Nt M (LB M Q B) t, g * n * g⁻¹ ∈ Nt M (LB M Q B) t) :
    ∃ c : AM.K, caseASylow_Mult (AM.φ ⟨g, hg⟩) β c := by
  obtain ⟨x₁, hx₁N, hx₁⟩ := hL4 1
  have hz : g * (x₁ : G) * g⁻¹ ∈ Nt M (LB M Q B) t := hgN _ hx₁N
  have hzH : g * (x₁ : G) * g⁻¹ ∈ H0 M Z :=
    (H0 M Z).mul_mem ((H0 M Z).mul_mem hg x₁.2) ((H0 M Z).inv_mem hg)
  obtain ⟨c, hc⟩ := hL3 ⟨_, hzH⟩ hz
  refine ⟨c, fun e => ?_⟩
  have hcomp : AM.φ ⟨_, hzH⟩ * AM.φ ⟨g, hg⟩ = AM.φ ⟨g, hg⟩ * AM.φ x₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  have h1 := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f e) hcomp
  simp only [LinearEquiv.mul_apply] at h1
  rw [hc, hx₁, map_add, map_smul, one_smul] at h1
  exact (add_left_cancel h1).symm

theorem caseASylow_mult_one_of_two_pow (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    {y : G} (hy : y ∈ H0 M Z) {k : ℕ} (hyk : y ^ 2 ^ k = 1) (hβ : ∃ e0, β e0 ≠ 0)
    {c : AM.K} (hc : caseASylow_Mult (AM.φ ⟨y, hy⟩) β c) : c = 1 := by
  have hpow : (AM.φ ⟨y, hy⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hy⟩ : ↥(H0 M Z)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [h1, map_one]
  have h1 := caseASylow_Mult_pow hc (2 ^ k)
  rw [hpow] at h1
  exact caseASylow_eq_one_of_two_pow (caseASylow_Mult_unique hβ h1 (caseASylow_Mult_one β))

theorem caseASylow_beta_comm (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (htN : t ∈ Nt M (LB M Q B) t) (htQ : t ∉ Q) (htH : t ∈ H0 M Z)
    {w : G} (hw : w ∈ H0 M Z) (hwt : ⁅w, t⁆ ∈ Q) :
    caseASylow_Mult (AM.φ ⟨w, hw⟩) β 1 := by
  obtain ⟨c, hc0, hc⟩ := caseASylow_coeff_ne AM hL3 htN htQ htH
  exact caseASylow_mult_one_of_comm hc0 hc ((caseASylow_comm_iff AM hw htH).mp hwt)

theorem caseASylow_comm_nt (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (htN : t ∈ Nt M (LB M Q B) t) (htQ : t ∉ Q) (htH : t ∈ H0 M Z)
    (hNH : Nt M (LB M Q B) t ≤ H0 M Z) {w : G} (hw : w ∈ H0 M Z) (hwt : ⁅w, t⁆ ∈ Q) :
    ∀ x ∈ Nt M (LB M Q B) t, ⁅x, w⁆ ∈ Q := by
  intro x hx
  obtain ⟨c, hc⟩ := hL3 ⟨x, hNH hx⟩ hx
  have hw1 := caseASylow_beta_comm AM hL3 htN htQ htH hw hwt
  exact (caseASylow_comm_iff AM (hNH hx) hw).mpr (caseASylow_comm_of_mult_one hw1 hc).symm

theorem caseASylow_comm_t_of_two (AM : ActionModel M Q Z) {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E}
    (hβ : ∃ e0, β e0 ≠ 0)
    (hL3 : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hL4 : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    (htN : t ∈ Nt M (LB M Q B) t) (htQ : t ∉ Q) (htH : t ∈ H0 M Z)
    {y : G} (hy : y ∈ H0 M Z) {k : ℕ} (hyk : y ^ 2 ^ k = 1)
    (hyN : ∀ n ∈ Nt M (LB M Q B) t, y * n * y⁻¹ ∈ Nt M (LB M Q B) t) :
    ⁅y, t⁆ ∈ Q := by
  obtain ⟨c, hc⟩ := caseASylow_mult_exists AM hL3 hL4 hy hyN
  have hc1 := caseASylow_mult_one_of_two_pow AM hy hyk hβ hc
  subst hc1
  obtain ⟨ct, -, hct⟩ := caseASylow_coeff_ne AM hL3 htN htQ htH
  exact (caseASylow_comm_iff AM hy htH).mpr (caseASylow_comm_of_mult_one hc hct)

end Line

section SylowAux

variable {X : Type} [Group X]

theorem caseASylow_mem_conj_of_mem {A : Subgroup X} {g a : X} (ha : a ∈ A) :
    g * a * g⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g A :=
  CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (by
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rw [e]
    exact ha)

theorem caseASylow_exists_max [Finite X] (C N : Subgroup X) (hN2 : IsPGroup 2 N) (hNC : N ≤ C) :
    ∃ S : Subgroup X, N ≤ S ∧ S ≤ C ∧ IsPGroup 2 S ∧
      ∀ U : Subgroup X, U ≤ C → IsPGroup 2 U → S ≤ U → U = S := by
  classical
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun U : Subgroup X => (U : Set X)) SetLike.coe_injective
  let P : Subgroup X → Prop := fun U => U ≤ C ∧ IsPGroup 2 U ∧ N ≤ U
  haveI : Nonempty {U : Subgroup X // P U} := ⟨⟨N, hNC, hN2, le_rfl⟩⟩
  obtain ⟨S₀, hS₀⟩ := Finite.exists_max (fun U : {U : Subgroup X // P U} => Nat.card U.1)
  refine ⟨S₀.1, S₀.2.2.2, S₀.2.1, S₀.2.2.1, fun U hUC hU2 hSU => ?_⟩
  have hUP : P U := ⟨hUC, hU2, S₀.2.2.2.trans hSU⟩
  exact (Subgroup.eq_of_le_of_card_ge hSU (hS₀ ⟨U, hUP⟩)).symm

theorem caseASylow_eq_of_normalizer [Finite X] {C S T : Subgroup X} (hT : IsPGroup 2 T)
    (hST : S ≤ T)
    (hmax : ∀ U : Subgroup X, U ≤ C → IsPGroup 2 U → S ≤ U → U = S)
    (hkey : ∀ y ∈ T, (∀ s ∈ S, y * s * y⁻¹ ∈ S) → y ∈ C) : T = S := by
  classical
  have ha : T ⊓ Subgroup.normalizer (S : Set X) = S := by
    refine hmax _ ?_ ?_ (le_inf hST Subgroup.le_normalizer)
    · intro y hy
      exact hkey y hy.1 (fun s hs => (Subgroup.mem_normalizer_iff.mp hy.2 s).mp hs)
    · exact hT.to_le inf_le_left
  by_contra hne
  haveI : Group.IsNilpotent T := hT.isNilpotent
  have hnc := normalizerCondition_of_isNilpotent (G := T)
  have hSlt : S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hST
  have hlt := hnc (S.subgroupOf T) hSlt
  obtain ⟨z, hzN, hzS⟩ : ∃ z ∈ Subgroup.normalizer ((S.subgroupOf T : Subgroup T) : Set T),
      z ∉ S.subgroupOf T := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hlt.2 (fun z hz => hcon z hz)
  have hyS : ∀ s ∈ S, (z : X) * s * (z : X)⁻¹ ∈ S := by
    intro s hs
    have h1 : (⟨s, hST hs⟩ : T) ∈ S.subgroupOf T := Subgroup.mem_subgroupOf.mpr hs
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hzN ⟨s, hST hs⟩).mp h1)
  have hyC : (z : X) ∈ C := hkey _ z.2 hyS
  have hyNorm : (z : X) ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hh : h ∈ T
    · have h1 := Subgroup.mem_normalizer_iff.mp hzN ⟨h, hh⟩
      constructor
      · intro hs
        exact Subgroup.mem_subgroupOf.mp (h1.mp (Subgroup.mem_subgroupOf.mpr hs))
      · intro hs
        exact Subgroup.mem_subgroupOf.mp (h1.mpr (Subgroup.mem_subgroupOf.mpr hs))
    · constructor
      · intro hs
        exact absurd (hST hs) hh
      · intro hs
        exfalso
        apply hh
        have h2 := hST hs
        have e : h = (z : X)⁻¹ * ((z : X) * h * (z : X)⁻¹) * (z : X) := by group
        rw [e]
        exact T.mul_mem (T.mul_mem (T.inv_mem z.2) h2) z.2
  have hmem : (z : X) ∈ T ⊓ Subgroup.normalizer (S : Set X) := ⟨z.2, hyNorm⟩
  rw [ha] at hmem
  exact hzS (Subgroup.mem_subgroupOf.mpr hmem)

theorem caseASylow_not_dvd_relIndex [Finite X] {D S : Subgroup X} (hSD : S ≤ D)
    (hS : IsPGroup 2 S) (hmax : ∀ U : Subgroup X, U ≤ D → IsPGroup 2 U → S ≤ U → U = S) :
    ¬ 2 ∣ S.relIndex D := by
  have h1 : IsPGroup 2 (S.subgroupOf D) := hS.comap_subtype
  obtain ⟨P, hPS⟩ := IsPGroup.exists_le_sylow h1
  have hU : P.toSubgroup.map D.subtype = S := by
    refine hmax _ (Subgroup.map_subtype_le _) (P.isPGroup'.map D.subtype) ?_
    intro s hs
    exact Subgroup.mem_map.mpr ⟨⟨s, hSD hs⟩, hPS (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  have hP : P.toSubgroup = S.subgroupOf D := by
    ext x
    constructor
    · intro hx
      have h2 := Subgroup.mem_map_of_mem D.subtype hx
      rw [hU] at h2
      exact Subgroup.mem_subgroupOf.mpr h2
    · intro hx
      exact hPS hx
  have hidx : P.toSubgroup.index = S.relIndex D := by
    rw [hP]
    rfl
  rw [← hidx]
  exact Sylow.not_dvd_index P

end SylowAux

section Main


theorem caseASylow_of (hA1 : CaseA1Statement) (hLine : NtLineStatement) :
    KFacts.CaseASylowStatement := by
  intro G _ _ M Q Z B t hH hE
  have hc : Ctx M Q Z B := hH.ctx
  obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
  obtain ⟨β, -, -, hL3, hL4⟩ := hLine G M Q Z B t hH AM
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have htQ : t ∉ Q := hH.notQ
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z :=
    (orthE1_Nt_le_Rt M (LB M Q B) t).trans (hc.Rt_le_H0 t)
  have htH : t ∈ H0 M Z := hNH htN
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hNL : Nt M (LB M Q B) t ≤ Lgen M (LB M Q B) :=
    (orthE1_Nt_le_Rt M (LB M Q B) t).trans (Rt_le_Lgen M (LB M Q B) t)
  have hβ : ∃ e0, β e0 ≠ 0 := caseASylow_beta_ne AM hL3 htN htQ htH
  have hNab := (ntElemAbelian_of hLine G M Q Z B t hH).1
  have hH0M : H0 M Z ≤ M := inf_le_left
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hND : Nt M (LB M Q B) t ≤ E1Dpre M Q B t := by
    refine le_iSup₂_of_le (1 : G) (Lgen M (LB M Q B)).one_mem ?_
    intro x hx
    exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (by simpa using hx)
  have hDL : E1Dpre M Q B t ≤ Lgen M (LB M Q B) := by
    refine iSup₂_le fun g hg => ?_
    intro x hx
    have h1 := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hx
    have h2 := (Lgen M (LB M Q B)).mul_mem ((Lgen M (LB M Q B)).mul_mem hg (hNL h1))
      ((Lgen M (LB M Q B)).inv_mem hg)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h2
    exact h2
  have hDH : E1Dpre M Q B t ≤ H0 M Z := hDL.trans hLH
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = CommQ hQM t ⊓ E1Dpre M Q B t := ⟨_, rfl⟩
  have hmemC : ∀ x : G, x ∈ C ↔ (x ∈ M ∧ ⁅x, t⁆ ∈ Q) ∧ x ∈ E1Dpre M Q B t := by
    intro x
    rw [hCdef, Subgroup.mem_inf, mem_CommQ]
  have hCM : ∀ x ∈ C, x ∈ H0 M Z := fun x hx => hDH ((hmemC x).mp hx).2
  have hCcomm : ∀ x ∈ C, ⁅x, t⁆ ∈ Q := fun x hx => ((hmemC x).mp hx).1.2
  have hCD : ∀ x ∈ C, x ∈ E1Dpre M Q B t := fun x hx => ((hmemC x).mp hx).2
  have hNC : Nt M (LB M Q B) t ≤ C := by
    intro x hx
    exact (hmemC x).mpr ⟨⟨hH0M (hNH hx), hNab x hx t htN⟩, hND hx⟩
  obtain ⟨S, hNS, hSC, hS2, hSmax⟩ :=
    caseASylow_exists_max C (Nt M (LB M Q B) t) (caseASylow_Nt_isPGroup M (LB M Q B) t) hNC
  have hkey : ∀ y : G, y ∈ E1Dpre M Q B t → (∃ k : ℕ, y ^ 2 ^ k = 1) →
      (∀ s ∈ S, y * s * y⁻¹ ∈ S) → y ∈ C := by
    intro y hyD hyk hyS
    obtain ⟨k, hk⟩ := hyk
    have hyH : y ∈ H0 M Z := hDH hyD
    have hyLg : y ∈ Lgen M (LB M Q B) := hDL hyD
    have hyw : CFSG.CGT.Timmesfeld75.conjSubgroup y (Nt M (LB M Q B) t) =
        Nt M (LB M Q B) t := by
      refine (hA1 G M Q Z B t hH hE y hyLg).mp ?_
      intro x hx w hw
      have hwS : w ∈ S := by
        have h1 := hyS _ (hNS (CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hw))
        have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
        rwa [e] at h1
      have hwC : w ∈ C := hSC hwS
      exact caseASylow_comm_nt AM hL3 htN htQ htH hNH (hCM w hwC) (hCcomm w hwC) x hx
    have hyN : ∀ n ∈ Nt M (LB M Q B) t, y * n * y⁻¹ ∈ Nt M (LB M Q B) t := by
      intro n hn
      rw [← hyw]
      exact caseASylow_mem_conj_of_mem hn
    have hyQ : ⁅y, t⁆ ∈ Q :=
      caseASylow_comm_t_of_two AM hβ hL3 hL4 htN htQ htH hyH hk hyN
    exact (hmemC y).mpr ⟨⟨hH0M hyH, hyQ⟩, hyD⟩
  have hmaxD : ∀ U : Subgroup G, U ≤ E1Dpre M Q B t → IsPGroup 2 U → S ≤ U → U = S := by
    intro U hUD hU2 hSU
    refine caseASylow_eq_of_normalizer hU2 hSU hSmax ?_
    intro y hyU hyS
    have hk : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hU2 ⟨y, hyU⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact hkey y (hUD hyU) hk hyS
  have hSD : S ≤ E1Dpre M Q B t := fun x hx => hCD x (hSC hx)
  have hodd : ¬ 2 ∣ S.relIndex (E1Dpre M Q B t) :=
    caseASylow_not_dvd_relIndex hSD hS2 hmaxD
  have hQS : Q ≤ S := (smith23E1_Q_le_Nt hc hH.mem).trans hNS
  have hSM : S ≤ M := fun x hx => ((hmemC x).mp (hSC hx)).1.1
  have hSN : S ≤ Subgroup.normalizer (Q : Set G) := fun x hx => hQM (hSM hx)
  haveI hnorm : (Q.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr hSN
  exact ⟨S, hQS, hSD, fun s hs => ((hmemC s).mp (hSC hs)).1.2,
    ⟨hnorm, hS2.to_quotient (Q.subgroupOf S)⟩, hodd⟩

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1
