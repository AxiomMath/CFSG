module

public import CFSG.Quasithin.Vol2.Ch11SecJEnd2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

namespace NatPair

variable {G : Type} [Group G] {U V V₁ W K : Subgroup G}
  {α : ↥K →* SL(2, F)} {βV : ↥V →* Multiplicative (Fin 2 → F)}
  {βU : ↥U →* Multiplicative (Fin 2 → F)} (P : NatPair U V V₁ W K α βV βU)

include P

theorem mat_eq_of {c : G} (hcU : c ∈ Subgroup.normalizer (U : Set G))
    {M : Matrix (Fin 2) (Fin 2) F}
    (hM : ∀ x y, P.T hcU (x, y) = (M 0 0 • x + M 0 1 • y, M 1 0 • x + M 1 1 • y)) :
    P.mat hcU = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, hM]

theorem T_eq_id_iff {c : G} (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G)) :
    (∀ p, P.T hcU p = p) ↔ ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ V₁ := by
  constructor
  · intro h u hu
    have h1 := h (P.X ⟨u, hu⟩)
    rw [P.T_X hcV₁, eq_comm, P.X_eq_iff] at h1
    have h2 := P.conj_mem le_rfl (P.hV₁V.trans P.hVU) hu h1
    simpa [cU, mul_assoc] using h2
  · intro h p
    obtain ⟨u, rfl⟩ := P.X_surjective p
    rw [P.T_X hcV₁, eq_comm, P.X_eq_iff]
    have h2 := P.conj_mem le_rfl (P.hV₁V.trans P.hVU) (U.inv_mem u.2) (h u u.2)
    simpa [cU, mul_assoc] using h2

variable (hα : Function.Surjective α) {C : Subgroup G}
  (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hCV₁ : C ≤ Subgroup.normalizer (V₁ : Set G))
  (hCK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ U)

@[expose] noncomputable def matHom : ↥C →* Matrix (Fin 2) (Fin 2) F where
  toFun c := P.mat (hCU c.2)
  map_one' := by
    refine P.mat_eq_of _ fun x y => ?_
    have h := (P.T_eq_id_iff (hCU C.one_mem) (hCV₁ C.one_mem)).2 (fun u _ => by simp) (x, y)
    rw [h]
    simp
  map_mul' a b := by
    refine P.mat_eq_of _ fun x y => ?_
    have hcomp : ∀ p, P.T (hCU (a * b).2) p = P.T (hCU a.2) (P.T (hCU b.2) p) := by
      intro p
      obtain ⟨u, rfl⟩ := P.X_surjective p
      rw [P.T_X (hCV₁ (a * b).2), P.T_X (hCV₁ b.2), P.T_X (hCV₁ a.2)]
      congr 1
      apply Subtype.ext
      show ((a * b : ↥C) : G) * u * ((a * b : ↥C) : G)⁻¹ = a * (b * u * (b : G)⁻¹) * (a : G)⁻¹
      rw [Subgroup.coe_mul]
      group
    rw [hcomp, P.T_eq hα (hCV₁ b.2) (hCK b b.2), P.T_eq hα (hCV₁ a.2) (hCK a a.2)]
    ext i <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end NatPair

theorem factNatPairEnd_holds : FactNatPairEnd := by
  intro G _ _ U V V₁ W K C F _ _ _ α βV βU hV₁V hVU hV₁W hWU hWV hWVU hcomm _ _ hKV _ hKW hα
    hβV hkerV hβU hkerU heqV heqU hCU hCV₁ hCK
  have P : NatPair U V V₁ W K α βV βU :=
    ⟨hV₁V, hVU, hV₁W, hWU, hWV, hWVU, hcomm, hKV, hKW, hβV, hkerV, hβU, hkerU, heqV, heqU⟩
  refine ⟨(P.matHom hα hCU hCV₁ hCK).toHomUnits, fun c => ?_, fun c r s hcV hr hs => ?_⟩
  ·
    have e : (P.matHom hα hCU hCV₁ hCK).toHomUnits c = 1 ↔ P.mat (hCU c.2) = 1 := by
      rw [Units.ext_iff]
      rfl
    rw [e, ← P.T_eq_id_iff (hCU c.2) (hCV₁ c.2)]
    constructor
    · intro h p
      rw [show p = (p.1, p.2) from rfl, P.T_eq hα (hCV₁ c.2) (hCK c c.2), h]
      simp
    · intro h
      exact P.mat_eq_of _ fun x y => by rw [h (x, y)]; simp
  ·
    have hmat : ((P.matHom hα hCU hCV₁ hCK).toHomUnits c : Matrix (Fin 2) (Fin 2) F) =
        P.mat (hCU c.2) := rfl
    rw [hmat]
    obtain ⟨v, hv⟩ := hβV (Multiplicative.ofAdd (Pi.single 0 1))
    have hXv : P.X ⟨v, hVU v.2⟩ = (Pi.single 0 1, 0) := by
      refine Prod.ext ?_ ?_
      · show P.kappa _ = _
        rw [P.kappa_of_mem_V v.2, hv, toAdd_ofAdd]
      · show Multiplicative.toAdd (βU _) = 0
        have h1 : βU ⟨v, hVU v.2⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hkerU, Subgroup.mem_subgroupOf]
          exact v.2
        rw [h1, toAdd_one]
    have hcv : (c : G) * v * (c : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcV v).mp v.2
    have hT1 : P.T (hCU c.2) (Pi.single 0 1, 0) = (r • Pi.single 0 1, 0) := by
      rw [← hXv, P.T_X (hCV₁ c.2)]
      refine Prod.ext ?_ ?_
      · show P.kappa ⟨_, hVU hcv⟩ = _
        rw [P.kappa_of_mem_V hcv, hr v ⟨_, hcv⟩ rfl, hv, toAdd_ofAdd]
      · show Multiplicative.toAdd (βU ⟨_, hVU hcv⟩) = 0
        have h1 : βU ⟨_, hVU hcv⟩ = 1 := by
          rw [← MonoidHom.mem_ker, hkerU, Subgroup.mem_subgroupOf]
          exact hcv
        rw [h1, toAdd_one]
    obtain ⟨w, hw⟩ := P.X_surjective (0, Pi.single 0 1)
    have hT2 : (P.T (hCU c.2) (0, Pi.single 0 1)).2 = s • Pi.single 0 1 := by
      rw [← hw, P.T_X (hCV₁ c.2)]
      have h2 : Multiplicative.toAdd (βU w) = Pi.single 0 1 := congrArg Prod.snd hw
      have h3 := hs w (NatPair.cU (hCU c.2) w) rfl
      rw [h2] at h3
      exact h3
    refine ⟨?_, ?_, ?_⟩
    · show (P.T (hCU c.2) (Pi.single 0 1, 0)).2 0 = 0
      rw [hT1]
      rfl
    · show (P.T (hCU c.2) (Pi.single 0 1, 0)).1 0 = r
      rw [hT1]
      simp
    · show (P.T (hCU c.2) (0, Pi.single 0 1)).2 0 = s
      rw [hT2]
      simp

end CFSG.Quasithin.Vol2.Ch11.SecJ
