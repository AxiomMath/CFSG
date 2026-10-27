module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUYModel
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUMarking

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section InnerDiag

open CFSG.LieType.Universal.Unitary CFSG.StandardType.InnerDiagSU

variable {n g r : ℕ}

theorem exists_conj_of_commuting_unitary {T : Matrix (Fin n) (Fin n) (PSUF g)}
    {P : Matrix (Fin n) (Fin r) (PSUF g)} {R : Matrix (Fin r) (Fin n) (PSUF g)}
    (hD : PSUYData g n r T P R) {t : GL (Fin n) (PSUF g)} (ht : t ∈ GUsub (PSUσ g) n)
    (htT : (t : Matrix (Fin n) (Fin n) (PSUF g)) * T =
      T * (t : Matrix (Fin n) (Fin n) (PSUF g))) :
    ∃ (A : GL (Fin r) (PSUF g)) (hA : IsJUnitary (PSUσ g) A),
      ∀ u : ↥(Unitary.SU (PSUσ g) r),
        t * ((tcYEmbSU hD u : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) * t⁻¹ =
          ((tcYEmbSU hD (conjSU A hA u) : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) := by
  set σ : PSUF g ≃+* PSUF g := PSUσ g with hσ
  set J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n with hJ
  set Jr : Matrix (Fin r) (Fin r) (PSUF g) := Unitary.antidiag r with hJr
  set tm : Matrix (Fin n) (Fin n) (PSUF g) := (t : Matrix (Fin n) (Fin n) (PSUF g)) with htm
  set ti : Matrix (Fin n) (Fin n) (PSUF g) := ((t⁻¹ : GL (Fin n) (PSUF g)) :
    Matrix (Fin n) (Fin n) (PSUF g)) with hti
  have htti : tm * ti = 1 := by rw [htm, hti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hitt : ti * tm = 1 := by rw [htm, hti, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfac : T = P * R := hD.fac
  have hRP : R * P = 1 := hD.rp
  have hTP : T * P = P := by rw [hfac, Matrix.mul_assoc, hRP, Matrix.mul_one]
  have hRT : R * T = R := by rw [hfac, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
  have hTti : ti * T = T * ti := by
    calc ti * T = ti * T * (tm * ti) := by rw [htti, Matrix.mul_one]
      _ = ti * (T * tm) * ti := by simp only [Matrix.mul_assoc]
      _ = ti * (tm * T) * ti := by rw [htT]
      _ = (ti * tm) * T * ti := by simp only [Matrix.mul_assoc]
      _ = T * ti := by rw [hitt, Matrix.one_mul]
  have hPA : tm * P = P * (R * tm * P) := by
    calc tm * P = tm * (T * P) := by rw [hTP]
      _ = (tm * T) * P := by rw [Matrix.mul_assoc]
      _ = (T * tm) * P := by rw [htT]
      _ = P * (R * tm * P) := by rw [hfac]; simp only [Matrix.mul_assoc]
  have hRA : R * ti = (R * ti * P) * R := by
    calc R * ti = (R * T) * ti := by rw [hRT]
      _ = R * (ti * T) := by rw [Matrix.mul_assoc, ← hTti]
      _ = (R * ti * P) * R := by rw [hfac]; simp only [Matrix.mul_assoc]
  have hAAi : (R * tm * P) * (R * ti * P) = 1 := by
    calc (R * tm * P) * (R * ti * P) = R * (tm * (P * R) * ti) * P := by
          simp only [Matrix.mul_assoc]
      _ = R * (tm * T * ti) * P := by rw [← hfac]
      _ = R * (T * tm * ti) * P := by rw [htT]
      _ = R * T * P := by rw [Matrix.mul_assoc T tm ti, htti, Matrix.mul_one]
      _ = 1 := by rw [hRT, hRP]
  have hAiA : (R * ti * P) * (R * tm * P) = 1 := by
    calc (R * ti * P) * (R * tm * P) = R * (ti * (P * R) * tm) * P := by
          simp only [Matrix.mul_assoc]
      _ = R * (ti * T * tm) * P := by rw [← hfac]
      _ = R * (T * ti * tm) * P := by rw [hTti]
      _ = R * T * P := by rw [Matrix.mul_assoc T ti tm, hitt, Matrix.mul_one]
      _ = 1 := by rw [hRT, hRP]
  let A : GL (Fin r) (PSUF g) := ⟨R * tm * P, R * ti * P, hAAi, hAiA⟩
  have hAval : (A : Matrix (Fin r) (Fin r) (PSUF g)) = R * tm * P := rfl
  have hAinv : ((A⁻¹ : GL (Fin r) (PSUF g)) : Matrix (Fin r) (Fin r) (PSUF g)) = R * ti * P := rfl
  have hA : IsJUnitary σ A := by
    unfold IsJUnitary
    have htu : tcConjTr σ tm * J * tm = J := ht
    have hRJR : tcConjTr σ R * Jr * R = J * T := by
      have h' : J * P = tcConjTr σ R * Jr := hD.adj'
      calc tcConjTr σ R * Jr * R = (J * P) * R := by rw [h']
        _ = J * (P * R) := by rw [Matrix.mul_assoc]
        _ = J * T := by rw [← hfac]
    rw [hAval]
    change tcConjTr σ (R * tm * P) * Jr * (R * tm * P) = Jr
    calc tcConjTr σ (R * tm * P) * Jr * (R * tm * P)
        = tcConjTr σ P * tcConjTr σ tm * (tcConjTr σ R * Jr * R) * tm * P := by
          rw [tcConjTr_mul, tcConjTr_mul]; simp only [Matrix.mul_assoc]
      _ = tcConjTr σ P * tcConjTr σ tm * (J * T) * tm * P := by rw [hRJR]
      _ = tcConjTr σ P * (tcConjTr σ tm * J * tm) * T * P := by
          have e : T * tm = tm * T := htT.symm
          calc tcConjTr σ P * tcConjTr σ tm * (J * T) * tm * P
              = tcConjTr σ P * tcConjTr σ tm * J * (T * tm) * P := by simp only [Matrix.mul_assoc]
            _ = tcConjTr σ P * tcConjTr σ tm * J * (tm * T) * P := by rw [e]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = tcConjTr σ P * J * (T * P) := by rw [htu]; simp only [Matrix.mul_assoc]
      _ = Jr := by rw [hTP]; exact hD.gram
  refine ⟨A, hA, fun u => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [show (((tcYEmbSU hD u : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) = tcYEmb P R ((u : GL (Fin r) (PSUF g)) :
        Matrix (Fin r) (Fin r) (PSUF g)) from rfl]
  rw [show (((tcYEmbSU hD (conjSU A hA u) : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) = tcYEmb P R (((conjSU A hA u : ↥(Unitary.SU (PSUσ g) r)) :
        GL (Fin r) (PSUF g)) : Matrix (Fin r) (Fin r) (PSUF g)) from rfl]
  rw [coe_conjSU, Units.val_mul, Units.val_mul, hAval, hAinv]
  unfold tcYEmb
  set um : Matrix (Fin r) (Fin r) (PSUF g) := ((u : GL (Fin r) (PSUF g)) :
    Matrix (Fin r) (Fin r) (PSUF g)) with hum
  calc tm * (1 + P * (um - 1) * R) * ti
      = tm * ti + (tm * P) * (um - 1) * (R * ti) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 + (P * (R * tm * P)) * (um - 1) * (R * ti) := by rw [htti, hPA]
    _ = 1 + (P * (R * tm * P)) * (um - 1) * ((R * ti * P) * R) := by
        exact congrArg (fun Y => 1 + (P * (R * tm * P)) * (um - 1) * Y) hRA
    _ = 1 + P * ((R * tm * P) * (um - 1) * (R * ti * P)) * R := by
        simp only [Matrix.mul_assoc]
    _ = 1 + P * ((R * tm * P) * um * (R * ti * P) - 1) * R := by
        congr 3
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAAi]

theorem tcInnerDiagOn_of_actions {X : Type} [Group X] {r : ℕ} (hr : 4 ≤ r)
    {ψ' : ↥(Unitary.SU (PSUσ g) r) →* X}
    (hker : ψ'.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) r)) (Bs : Subgroup X)
    (hact : ∀ b ∈ Bs, ∃ (A : GL (Fin r) (PSUF g)) (hA : IsJUnitary (PSUσ g) A),
      ∀ u, b⁻¹ * ψ' u * b = ψ' (conjSU A hA u)) :
    GGInnerDiagOn Bs ψ'.range := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hBN : Bs ≤ Subgroup.normalizer (ψ'.range : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨A, hA, hAc⟩ := hact b⁻¹ (Bs.inv_mem hb)
      refine ⟨conjSU A hA u, ?_⟩
      have := hAc u
      rw [inv_inv] at this
      exact this.symm
    · rintro ⟨u, hu⟩
      obtain ⟨A, hA, hAc⟩ := hact b hb
      refine ⟨conjSU A hA u, ?_⟩
      have := hAc u
      rw [← this, hu]
      group
  exact tcMarkingUnitary_of_conj (F := PSUF g) (f := g + 1) (card_PSUF g) (by omega) (by omega)
    ψ' hker Bs hBN hact

theorem tcMul_scalar_mul {F : Type} [Field F] {P : Matrix (Fin n) (Fin r) F}
    {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1) (c : F) :
    R * Matrix.scalar (Fin n) c * P = Matrix.scalar (Fin r) c := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]

theorem tcInv_commute {F : Type} [Field F] {t : GL (Fin n) F} {T : Matrix (Fin n) (Fin n) F}
    (h : (t : Matrix (Fin n) (Fin n) F) * T = T * (t : Matrix (Fin n) (Fin n) F)) :
    ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * T =
      T * ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have htti : (t : Matrix (Fin n) (Fin n) F) * ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hitt : ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (t : Matrix (Fin n) (Fin n) F)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * T
      = ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * T *
          ((t : Matrix (Fin n) (Fin n) F) * ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        rw [htti, Matrix.mul_one]
    _ = ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (T * (t : Matrix (Fin n) (Fin n) F)) *
          ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
    _ = ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((t : Matrix (Fin n) (Fin n) F) * T) *
          ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h]
    _ = T * ((t⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [← Matrix.mul_assoc, hitt, Matrix.one_mul]

theorem innerDiagOn_map_PSUYsd {X : Type} [Group X] {ψ : ↥(Unitary.SU (PSUσ g) n) →* X}
    (hker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) n))
    (hadm : StatedLieAdmissible .PSU n 2 (g + 1))
    {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) (hr : 4 ≤ Matrix.rank T)
    {x : X} {s : GL (Fin n) (PSUF g)} (hs : s ∈ GUsub (PSUσ g) n)
    (hsl : IsGLLift (PSUj n g) ψ s x)
    (hsT : (s : Matrix (Fin n) (Fin n) (PSUF g)) * T =
      T * (s : Matrix (Fin n) (Fin n) (PSUF g))) :
    GGInnerDiagOn (Subgroup.zpowers x) ((PSUYsd n g T).map ψ) := by
  classical
  obtain ⟨P, R, hD⟩ := exists_PSUYData hT hTa
  set ι := tcYEmbSU hD with hι
  set ψ' : ↥(Unitary.SU (PSUσ g) (Matrix.rank T)) →* X := ψ.comp ι with hψ'
  have hinj : Function.Injective (PSUj n g) := Subgroup.subtype_injective _
  let H : Subgroup X :=
    { carrier := {b | ∃ t : GL (Fin n) (PSUF g), t ∈ GUsub (PSUσ g) n ∧
        (t : Matrix (Fin n) (Fin n) (PSUF g)) * T = T * (t : Matrix (Fin n) (Fin n) (PSUF g)) ∧
        IsGLLift (PSUj n g) ψ t b}
      mul_mem' := by
        rintro b b' ⟨t, ht, htT, htl⟩ ⟨t', ht', htT', htl'⟩
        refine ⟨t' * t, (GUsub (PSUσ g) n).mul_mem ht' ht, ?_, htl.mul htl'⟩
        rw [Units.val_mul, Matrix.mul_assoc, htT, ← Matrix.mul_assoc, htT', Matrix.mul_assoc]
      one_mem' := ⟨1, (GUsub (PSUσ g) n).one_mem, by simp, isGLLift_one⟩
      inv_mem' := by
        rintro b ⟨t, ht, htT, htl⟩
        exact ⟨t⁻¹, (GUsub (PSUσ g) n).inv_mem ht, tcInv_commute htT,
          htl.inv_of_injective hinj⟩ }
  have hxH : x ∈ H := ⟨s, hs, hsT, hsl⟩
  have hzH : Subgroup.zpowers x ≤ H := (Subgroup.zpowers_le).mpr hxH
  have hact : ∀ b ∈ Subgroup.zpowers x,
      ∃ (A : GL (Fin (Matrix.rank T)) (PSUF g)) (hA : IsJUnitary (PSUσ g) A),
        ∀ u, b⁻¹ * ψ' u * b = ψ' (conjSU A hA u) := by
    intro b hb
    obtain ⟨t, ht, htT, htl⟩ := hzH hb
    obtain ⟨A, hA, hAc⟩ := exists_conj_of_commuting_unitary hD ht htT
    refine ⟨A, hA, fun u => ?_⟩
    obtain ⟨u', hj, hψ⟩ := htl (ι u)
    have hu' : u' = ι (conjSU A hA u) := by
      apply hinj
      rw [hj]
      exact hAc u
    show b⁻¹ * ψ (ι u) * b = ψ (ι (conjSU A hA u))
    rw [hψ, hu']
  have hker' : ψ'.ker ≤ Subgroup.center ↥(Unitary.SU (PSUσ g) (Matrix.rank T)) := by
    intro u hu
    have h1 : ι u ∈ ψ.ker := hu
    obtain ⟨c, hc⟩ := PSU_center_scalar hadm (hker h1)
    have hu_mat : ((u : GL (Fin (Matrix.rank T)) (PSUF g)) :
        Matrix (Fin (Matrix.rank T)) (Fin (Matrix.rank T)) (PSUF g)) =
        Matrix.scalar (Fin (Matrix.rank T)) c := by
      have e1 := tcYProj_tcYEmb hD.rp ((u : GL (Fin (Matrix.rank T)) (PSUF g)) :
        Matrix (Fin (Matrix.rank T)) (Fin (Matrix.rank T)) (PSUF g))
      have e2 : (((ι u : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) = tcYEmb P R ((u : GL (Fin (Matrix.rank T)) (PSUF g)) :
            Matrix (Fin (Matrix.rank T)) (Fin (Matrix.rank T)) (PSUF g)) := rfl
      rw [← e2, hc, tcMul_scalar_mul hD.rp] at e1
      exact e1.symm
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Units.ext
    change (((w : GL (Fin (Matrix.rank T)) (PSUF g)) * (u : GL (Fin (Matrix.rank T)) (PSUF g)) :
        GL (Fin (Matrix.rank T)) (PSUF g)) : Matrix (Fin (Matrix.rank T)) (Fin (Matrix.rank T))
          (PSUF g)) =
      (((u : GL (Fin (Matrix.rank T)) (PSUF g)) * (w : GL (Fin (Matrix.rank T)) (PSUF g)) :
        GL (Fin (Matrix.rank T)) (PSUF g)) : Matrix (Fin (Matrix.rank T)) (Fin (Matrix.rank T))
          (PSUF g))
    rw [Units.val_mul, Units.val_mul, hu_mat]
    exact (Matrix.scalar_commute c (fun r' => Commute.all c r') _).eq.symm
  have hmain := tcInnerDiagOn_of_actions hr hker' (Subgroup.zpowers x) hact
  have hrange : ψ'.range = (PSUYsd n g T).map ψ := by
    rw [hψ', MonoidHom.range_comp, hι, PSUYsd_range_tcYEmbSU hD]
  rw [hrange] at hmain
  exact hmain

end InnerDiag

end CFSG.StandardType.TableCRes
