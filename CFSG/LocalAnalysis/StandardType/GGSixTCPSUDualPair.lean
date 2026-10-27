module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPairEmb
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUSelfDual
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section DualPair

open CFSG.StandardType.ClassicalPosition.Geo

variable {g n k : ℕ}

section BlockGroup

variable {S : Set (GL (Fin n) (PSUF g))} {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
  {R W : Matrix (Fin k) (Fin n) (PSUF g)}

theorem mem_glBlockCentralizer_PSU_iff {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    {u : ↥(Unitary.SU (PSUσ g) n)} :
    u ∈ glBlockCentralizer (PSUj n g) S ε ↔
      (∀ s ∈ S, (s : Matrix (Fin n) (Fin n) (PSUF g)) *
          ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
        ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
          (s : Matrix (Fin n) (Fin n) (PSUF g))) ∧
        ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) = 1 - ε := by
  constructor
  · intro hu
    have hu' : PSUj n g u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) := hu
    refine ⟨fun s hs => ?_, hu'.2⟩
    have h := (Subgroup.mem_centralizer_iff.mp hu'.1) s hs
    have h' := congrArg (fun v : GL (Fin n) (PSUF g) => (v : Matrix (Fin n) (Fin n) (PSUF g))) h
    simpa [Units.val_mul] using h'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    change PSUj n g u ∈ Subgroup.centralizer S
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact h1 s hs

theorem mem_glBlockCentralizer_dualPair_iff (hD : PSUDualData g n k P Q R W)
    (hPR : P * R ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hQW : Q * W ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hsc : ∀ s ∈ S, ∃ c c' : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) * P = c • P ∧
      R * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c • R ∧
      (s : Matrix (Fin n) (Fin n) (PSUF g)) * Q = c' • Q ∧
      W * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c' • W)
    (u : ↥(Unitary.SU (PSUσ g) n)) :
    u ∈ glBlockCentralizer (PSUj n g) S (P * R + Q * W) ↔
      ∃ a : GL (Fin k) (PSUF g),
        PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det =
          (a : Matrix (Fin k) (Fin k) (PSUF g)).det ∧
        (u : GL (Fin n) (PSUF g)) = dualPairEmbGL hD a := by
  constructor
  · intro hu
    obtain ⟨hcomm, hfix⟩ := mem_glBlockCentralizer_PSU_iff.mp hu
    have huA : ∀ b ∈ Algebra.adjoin (PSUF g) (Units.val '' S),
        ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * b =
          b * ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) :=
      commute_adjoin_of_commute_gens (g := (u : GL (Fin n) (PSUF g)))
        (fun s hs => (hcomm s hs).symm)
    have hP := huA _ hPR
    have hQ := huA _ hQW
    have hdec := dpEmb_eq_of_commute hD.rp hD.wq hP hQ hfix
    have hUP := mul_P_eq_of_commute hD.rp hP
    have hUQ := mul_P_eq_of_commute hD.wq hQ
    have hU : tcConjTr (PSUσ g)
        ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
          ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
        Unitary.antidiag n := u.2.2
    have h01 := tcConjTr_mul_eq_one_of_unitary hD.wq hD.pj hU hUP hUQ
    have h10 : tcConjTr (PSUσ g) (W * ((u : GL (Fin n) (PSUF g)) :
        Matrix (Fin n) (Fin n) (PSUF g)) * Q) * (R * ((u : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) * P) = 1 := by
      have := congrArg (tcConjTr (PSUσ g)) h01
      rwa [tcConjTr_mul, tcConjTr_tcConjTr (PSUσ_involutive g), tcConjTr_one] at this
    have h01' : (R * ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * P) *
        tcConjTr (PSUσ g) (W * ((u : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) * Q) = 1 := mul_eq_one_comm.mp h10
    let a : GL (Fin k) (PSUF g) :=
      ⟨R * ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * P,
        tcConjTr (PSUσ g) (W * ((u : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) * Q), h01', h10⟩
    have hu_eq : (u : GL (Fin n) (PSUF g)) = dualPairEmbGL hD a := by
      apply Units.ext
      rw [coe_dualPairEmbGL]
      change _ = dpEmb P Q R W
        (R * ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * P)
        (tcConjTr (PSUσ g) (tcConjTr (PSUσ g) (W * ((u : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) * Q)))
      rw [tcConjTr_tcConjTr (PSUσ_involutive g)]
      exact hdec
    refine ⟨a, ?_, hu_eq⟩
    have hdet1 : ((u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)).det = 1 := u.2.1
    have h1 : (a : Matrix (Fin k) (Fin k) (PSUF g)).det *
        PSUσ g ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := by
      rw [← det_dualPairEmbGL hD, ← hu_eq]
      exact hdet1
    have h2 : ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det *
        (a : Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h3 : PSUσ g ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det *
        PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := by
      rw [← map_mul, h2, map_one]
    calc PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det
        = ((a : Matrix (Fin k) (Fin k) (PSUF g)).det *
            PSUσ g ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det) *
          PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det := by rw [h1, one_mul]
      _ = (a : Matrix (Fin k) (Fin k) (PSUF g)).det *
          (PSUσ g ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det *
            PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det) := mul_assoc _ _ _
      _ = (a : Matrix (Fin k) (Fin k) (PSUF g)).det := by rw [h3, mul_one]
  · rintro ⟨a, -, hua⟩
    refine mem_glBlockCentralizer_PSU_iff.mpr ⟨fun s hs => ?_, ?_⟩
    · obtain ⟨c, c', h1, h2, h3, h4⟩ := hsc s hs
      rw [hua, coe_dualPairEmbGL]
      exact dpEmb_commute_of_scalars h1 h2 h3 h4 _ _
    · rw [hua, coe_dualPairEmbGL]
      exact dpEmb_mul_N hD.rp hD.wq hD.rq hD.wp _ _

end BlockGroup

section Derived

open scoped commutatorElement

private theorem subsingleton_SL_of_le_one {F : Type} [Field F] {k : ℕ} (hk : k ≤ 1) :
    Subsingleton (Matrix.SpecialLinearGroup (Fin k) F) := by
  interval_cases k
  · exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  · refine ⟨fun a b => Subtype.ext (Matrix.ext fun i j => ?_)⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    have ha : (a : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have h := a.2
      rw [Matrix.det_unique] at h
      exact h
    have hb : (b : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have h := b.2
      rw [Matrix.det_unique] at h
      exact h
    rw [ha, hb]

theorem exists_finset_card_four_PSUF (g : ℕ) : ∃ s : Finset (PSUF g), s.card = 4 := by
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hcard : 4 ≤ Nat.card (PSUF g) := by
    rw [card_PSUF]
    have h2 : 2 ≤ 2 ^ (g + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ (g + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (PSUF g)))
    (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hcard)
  exact ⟨s, hs⟩

theorem commutator_top_SL_PSUF (g k : ℕ) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) (PSUF g))),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin k) (PSUF g)))⁆ = ⊤ := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have := subsingleton_SL_of_le_one (F := PSUF g) (k := k) (by omega)
    exact eq_top_iff.mpr fun x _ => by
      rw [Subsingleton.elim x 1]
      exact Subgroup.one_mem _
  · have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := PSUF g) (n := k) hk
      (Or.inr (exists_finset_card_four_PSUF g))
    exact Group.isPerfect_def.1 hperf

variable {S : Set (GL (Fin n) (PSUF g))} {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
  {R W : Matrix (Fin k) (Fin n) (PSUF g)}

theorem commutator_glBlockCentralizer_dualPair (hD : PSUDualData g n k P Q R W)
    (hPR : P * R ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hQW : Q * W ∈ Algebra.adjoin (PSUF g) (Units.val '' S))
    (hsc : ∀ s ∈ S, ∃ c c' : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) * P = c • P ∧
      R * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c • R ∧
      (s : Matrix (Fin n) (Fin n) (PSUF g)) * Q = c' • Q ∧
      W * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c' • W) :
    ⁅glBlockCentralizer (PSUj n g) S (P * R + Q * W),
      glBlockCentralizer (PSUj n g) S (P * R + Q * W)⁆ = (dualPairEmbSU hD).range := by
  have hG := mem_glBlockCentralizer_dualPair_iff hD hPR hQW hsc
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, -, hxa⟩ := (hG x).mp hx
    obtain ⟨b, -, hyb⟩ := (hG y).mp hy
    have hdet1 : Matrix.GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
    have hdetc : ((⁅a, b⁆ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet1, Units.val_one]
    let c : Matrix.SpecialLinearGroup (Fin k) (PSUF g) :=
      ⟨((⁅a, b⁆ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)), hdetc⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [coe_dualPairEmbSU]
    have hc : Matrix.SpecialLinearGroup.toGL c = ⁅a, b⁆ := Units.ext rfl
    have hxy : ((⁅x, y⁆ : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) =
        ⁅(x : GL (Fin n) (PSUF g)), (y : GL (Fin n) (PSUF g))⁆ := rfl
    rw [hc, map_commutatorElement, hxy, hxa, hyb]
  · have hrange : (dualPairEmbSU hD).range ≤
        glBlockCentralizer (PSUj n g) S (P * R + Q * W) := by
      rintro _ ⟨a', rfl⟩
      refine (hG _).mpr ⟨Matrix.SpecialLinearGroup.toGL a', ?_, rfl⟩
      have h1 : ((Matrix.SpecialLinearGroup.toGL a' : GL (Fin k) (PSUF g)) :
          Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := a'.2
      rw [h1, map_one]
    have h1 : (dualPairEmbSU hD).range = ⁅(dualPairEmbSU hD).range, (dualPairEmbSU hD).range⁆ := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_top_SL_PSUF]
    calc (dualPairEmbSU hD).range = ⁅(dualPairEmbSU hD).range, (dualPairEmbSU hD).range⁆ := h1
      _ ≤ _ := Subgroup.commutator_mono hrange hrange

theorem dualPairEmbSU_injective (hD : PSUDualData g n k P Q R W) :
    Function.Injective (dualPairEmbSU hD) := by
  intro a b hab
  have h1 := congrArg (fun w : ↥(Unitary.SU (PSUσ g) n) =>
    R * (((w : GL (Fin n) (PSUF g))) : Matrix (Fin n) (Fin n) (PSUF g)) * P) hab
  simp only [coe_dualPairEmbSU, coe_dualPairEmbGL, R_dpEmb_P hD.rp hD.rq] at h1
  exact Subtype.ext h1

theorem mem_center_of_dualPairEmbSU_mem_center (hD : PSUDualData g n k P Q R W)
    {a : Matrix.SpecialLinearGroup (Fin k) (PSUF g)}
    (h : dualPairEmbSU hD a ∈ Subgroup.center ↥(Unitary.SU (PSUσ g) n)) :
    a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin k) (PSUF g)) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro b
  apply dualPairEmbSU_injective hD
  rw [map_mul, map_mul]
  exact h (dualPairEmbSU hD b)

end Derived

section Existence

theorem tcBlockDegree_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (hne : e ≠ 0) :
    0 < blockDegree A e := by
  unfold blockDegree
  set W := (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) with hW
  have heW : e ∈ W := ⟨1, A.one_mem, by simp⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨e, heW⟩, fun h => hne (congrArg Subtype.val h)⟩

theorem dualPair_scalar_actions {S : Set (GL (Fin n) (PSUF g))}
    (hSU : ∀ s ∈ S, s ∈ GUsub (PSUσ g) n) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (he : IsPrimIdemIn (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e < 2) :
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ∈
        Algebra.adjoin (PSUF g) (Units.val '' S) ∧
      (∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S), ∃ c : PSUF g, a * e = c • e) ∧
      (∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S), ∃ c : PSUF g,
        a * formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e =
          c • formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) ∧
      (∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S), a * e = e * a) ∧
      (∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S),
        a * formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e =
          formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e * a) := by
  have hσσ : ∀ x, (PSUσ g).toRingHom ((PSUσ g).toRingHom x) = x := PSUσ_involutive g
  have hdet : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).det :=
    PSUantidiag_isUnit_det n g
  have hGh : Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)).map
      (PSUσ g).toRingHom) = Unitary.antidiag n := PSUantidiag_transpose_map n g
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) (PSUF g)).map
      (PSUσ g).toRingHom) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (PSUF g)) =
        Unitary.antidiag n := fun s hs => mem_GUsub_iff.mp (hSU s hs)
  have hbd : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e = 1 := by
    have := tcBlockDegree_pos (A := Algebra.adjoin (PSUF g) (Units.val '' S)) he.2.2.1
    omega
  have hscal : ∀ a ∈ Algebra.adjoin (PSUF g) (Units.val '' S), ∃ c : PSUF g, a * e = c • e :=
    fun a ha => tcScalar_of_blockDegree_eq_one he.1 he.2.2.1 hbd ha
  have heA : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ∈
      Algebra.adjoin (PSUF g) (Units.val '' S) :=
    formAdj_mem_adjoin (PSUσ g).toRingHom hdet hSU' he.1
  have hcomm := adjoin_commute hS
  refine ⟨heA, hscal, ?_, fun a ha => (hcomm a ha e he.1).eq, fun a ha => (hcomm a ha _ heA).eq⟩
  intro a ha
  obtain ⟨c, hc⟩ := hscal (formAdj (PSUσ g).toRingHom (Unitary.antidiag n) a)
    (formAdj_mem_adjoin (PSUσ g).toRingHom hdet hSU' ha)
  refine ⟨(PSUσ g).toRingHom c, ?_⟩
  have h1 := congrArg (formAdj (PSUσ g).toRingHom (Unitary.antidiag n)) hc
  rw [formAdj_mul (PSUσ g).toRingHom hdet, formAdj_smul,
    formAdj_formAdj (PSUσ g).toRingHom hσσ hdet hGh] at h1
  rw [(hcomm a ha _ heA).eq]
  exact h1

theorem exists_dualData {e : Matrix (Fin n) (Fin n) (PSUF g)} (heid : IsIdempotentElem e)
    (hee' : e * formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = 0)
    (he'e : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e * e = 0) :
    ∃ (P Q : Matrix (Fin n) (Fin (Matrix.rank e)) (PSUF g))
      (R W : Matrix (Fin (Matrix.rank e)) (Fin n) (PSUF g)),
      e = P * R ∧ formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = Q * W ∧
      R * P = 1 ∧ W * Q = 1 ∧ R * Q = 0 ∧ W * P = 0 ∧
      tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = W ∧
      tcConjTr (PSUσ g) Q * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = R := by
  obtain ⟨P, R, hfac, hRP⟩ := exists_rankFactorization_of_isIdempotentElem heid
  set σ : PSUF g ≃+* PSUF g := PSUσ g with hσdef
  set J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n with hJdef
  have hJJ : J * J = 1 := Unitary.antidiag_mul_self (F := PSUF g) n
  have hJh : tcConjTr σ J = J := PSUantidiag_transpose_map n g
  have hσσ : ∀ c, σ (σ c) = c := PSUσ_involutive g
  have hJinv : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
  set Q : Matrix (Fin n) (Fin (Matrix.rank e)) (PSUF g) := J * tcConjTr σ R with hQ
  set W : Matrix (Fin (Matrix.rank e)) (Fin n) (PSUF g) := tcConjTr σ P * J with hW
  have hte : tcConjTr σ e = tcConjTr σ R * tcConjTr σ P := by
    rw [← tcConjTr_mul, ← hfac]
  have he' : formAdj σ.toRingHom J e = Q * W := by
    unfold formAdj
    rw [hJinv]
    have : Matrix.transpose (e.map σ.toRingHom) = tcConjTr σ e := rfl
    rw [this, hte, hQ, hW]
    simp only [Matrix.mul_assoc]
  have hWQ : W * Q = 1 := by
    calc W * Q = tcConjTr σ P * (J * J) * tcConjTr σ R := by
          rw [hW, hQ]; simp only [Matrix.mul_assoc]
      _ = tcConjTr σ (R * P) := by rw [hJJ, Matrix.mul_one, tcConjTr_mul]
      _ = 1 := by rw [hRP, tcConjTr_one]
  have hRQ : R * Q = 0 := by
    have h1 : P * (R * Q) * W = 0 := by
      have e1 : e * (Q * W) = P * R * (Q * W) := by rw [← hfac]
      calc P * (R * Q) * W = P * R * (Q * W) := by simp only [Matrix.mul_assoc]
        _ = e * formAdj σ.toRingHom J e := by rw [he', e1]
        _ = 0 := hee'
    have h2 : R * (P * (R * Q) * W) * Q = R * Q := by
      calc R * (P * (R * Q) * W) * Q = (R * P) * (R * Q) * (W * Q) := by
            simp only [Matrix.mul_assoc]
        _ = R * Q := by rw [hRP, hWQ, Matrix.one_mul, Matrix.mul_one]
    rw [← h2, h1]
    simp
  have hWP : W * P = 0 := by
    have h1 : Q * (W * P) * R = 0 := by
      have e1 : Q * W * e = Q * W * (P * R) := by rw [← hfac]
      calc Q * (W * P) * R = Q * W * (P * R) := by simp only [Matrix.mul_assoc]
        _ = formAdj σ.toRingHom J e * e := by rw [he', e1]
        _ = 0 := he'e
    have h2 : W * (Q * (W * P) * R) * P = W * P := by
      calc W * (Q * (W * P) * R) * P = (W * Q) * (W * P) * (R * P) := by
            simp only [Matrix.mul_assoc]
        _ = W * P := by rw [hRP, hWQ, Matrix.one_mul, Matrix.mul_one]
    rw [← h2, h1]
    simp
  have hQJ : tcConjTr σ Q * J = R := by
    calc tcConjTr σ Q * J = tcConjTr σ (tcConjTr σ R) * (tcConjTr σ J * J) := by
          rw [hQ, tcConjTr_mul]; simp only [Matrix.mul_assoc]
      _ = R := by rw [hJh, hJJ, Matrix.mul_one, tcConjTr_tcConjTr hσσ]
  exact ⟨P, Q, R, W, hfac, he', hRP, hWQ, hRQ, hWP, rfl, hQJ⟩


end Existence

section Model

structure PSUDualPairModel (n g : ℕ) (S : Set (GL (Fin n) (PSUF g)))
    (e : Matrix (Fin n) (Fin n) (PSUF g)) {k : ℕ}
    (P Q : Matrix (Fin n) (Fin k) (PSUF g)) (R W : Matrix (Fin k) (Fin n) (PSUF g))
    (hD : PSUDualData g n k P Q R W) : Prop where
  e_eq : e = P * R
  adj_eq : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = Q * W
  blockGroup : ∀ u : ↥(Unitary.SU (PSUσ g) n),
    u ∈ glBlockCentralizer (PSUj n g) S
      (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e) ↔
      ∃ a : GL (Fin k) (PSUF g),
        PSUσ g (a : Matrix (Fin k) (Fin k) (PSUF g)).det =
          (a : Matrix (Fin k) (Fin k) (PSUF g)).det ∧
        (u : GL (Fin n) (PSUF g)) = dualPairEmbGL hD a
  derived : ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
      glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆ = (dualPairEmbSU hD).range
  inj : Function.Injective (dualPairEmbSU hD)
  center : ∀ a : Matrix.SpecialLinearGroup (Fin k) (PSUF g),
    dualPairEmbSU hD a ∈ Subgroup.center ↥(Unitary.SU (PSUσ g) n) →
      a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin k) (PSUF g))

theorem exists_dualPairModel_PSU
    (n g : ℕ) (S : Set (GL (Fin n) (PSUF g)))
    (hSU : ∀ s ∈ S, s ∈ GUsub (PSUσ g) n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (he : IsPrimIdemIn (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    (hpair : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e < 2) :
    ∃ (P Q : Matrix (Fin n) (Fin (Matrix.rank e)) (PSUF g))
      (R W : Matrix (Fin (Matrix.rank e)) (Fin n) (PSUF g))
      (hD : PSUDualData g n (Matrix.rank e) P Q R W), PSUDualPairModel n g S e P Q R W hD := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) (PSUF g)).map
      (PSUσ g).toRingHom) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (PSUF g)) =
        Unitary.antidiag n := fun s hs => mem_GUsub_iff.mp (hSU s hs)
  obtain ⟨hee', he'e⟩ := mul_formAdj_eq_zero_of_dualPair (PSUσ g).toRingHom (PSUσ_involutive g)
    (PSUantidiag_isUnit_det n g) (PSUantidiag_transpose_map n g) hSU' hS he hpair
  obtain ⟨P, Q, R, W, he_eq, hadj, hrp, hwq, hrq, hwp, hpj, hqj⟩ :=
    exists_dualData he.2.1 hee' he'e
  obtain ⟨heA, -, -, hcomm, -⟩ := dualPair_scalar_actions hSU hS he hdeg
  have hD : PSUDualData g n (Matrix.rank e) P Q R W := ⟨hrp, hwq, hrq, hwp, hpj, hqj⟩
  have hPR : P * R ∈ Algebra.adjoin (PSUF g) (Units.val '' S) := he_eq ▸ he.1
  have hQW : Q * W ∈ Algebra.adjoin (PSUF g) (Units.val '' S) := hadj ▸ heA
  have hsc : ∀ s ∈ S, ∃ c c' : PSUF g,
      (s : Matrix (Fin n) (Fin n) (PSUF g)) * P = c • P ∧
      R * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c • R ∧
      (s : Matrix (Fin n) (Fin n) (PSUF g)) * Q = c' • Q ∧
      W * (s : Matrix (Fin n) (Fin n) (PSUF g)) = c' • W := by
    intro s hs
    have hsA : (s : Matrix (Fin n) (Fin n) (PSUF g)) ∈
        Algebra.adjoin (PSUF g) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    obtain ⟨-, hscal, hscal', hcomm, hcomm'⟩ := dualPair_scalar_actions hSU hS he hdeg
    obtain ⟨c, hc⟩ := hscal _ hsA
    obtain ⟨c', hc'⟩ := hscal' _ hsA
    have h1 : (s : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) = c • (P * R) := he_eq ▸ hc
    have h2 : (s : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
        P * R * (s : Matrix (Fin n) (Fin n) (PSUF g)) := he_eq ▸ hcomm _ hsA
    have h3 : (s : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) = c' • (Q * W) := hadj ▸ hc'
    have h4 : (s : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
        Q * W * (s : Matrix (Fin n) (Fin n) (PSUF g)) := hadj ▸ hcomm' _ hsA
    exact ⟨c, c', mul_left_scalar_of_mul_eq_smul hrp h1,
      mul_right_scalar_of_mul_eq_smul hrp h2 h1, mul_left_scalar_of_mul_eq_smul hwq h3,
      mul_right_scalar_of_mul_eq_smul hwq h4 h3⟩
  have hε : e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e = P * R + Q * W := by
    rw [← he_eq, ← hadj]
  refine ⟨P, Q, R, W, hD, ⟨he_eq, hadj, fun u => ?_, ?_, dualPairEmbSU_injective hD,
    fun a => mem_center_of_dualPairEmbSU_mem_center hD⟩⟩
  · rw [hε]
    exact mem_glBlockCentralizer_dualPair_iff hD hPR hQW hsc u
  · rw [hε]
    exact commutator_glBlockCentralizer_dualPair hD hPR hQW hsc

end Model

section Component

theorem PSL_mem_classicalTags : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by
  simp [CFSG.Blueprint.classicalTags]

theorem blueprintLieModel_PSL_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {r f : ℕ} (h : CFSG.Blueprint.LieModel G .PSL r 2 f) :
    CFSG.Blueprint.LieModel G' .PSL r 2 f :=
  CFSG.Models.LieModel.toBlueprint PSL_mem_classicalTags
    (CFSG.Models.LieModel.of_mulEquiv e
      (CFSG.Models.LieModel.of_blueprint PSL_mem_classicalTags h))

theorem isQuasisimple_SL_PSUF (g k : ℕ) (hk : 2 ≤ k) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) (PSUF g)) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) (PSUF g)) :=
    CFSG.LinearGroups.special_linear_isPerfect hk (Or.inr (exists_finset_card_four_PSUF g))
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := PSUF g)
    (n := k) hk (Or.inr (exists_finset_card_four_PSUF g))
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  have : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin k) (PSUF g)) :=
    ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

theorem lieModel_SL_PSUF (g k : ℕ) (hk : 2 ≤ k) :
    CFSG.Blueprint.LieModel (Matrix.SpecialLinearGroup (Fin k) (PSUF g) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin k) (PSUF g))) .PSL k 2 (2 * (g + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hF : Nat.card (PSUF g) = 2 ^ (2 * (g + 1)) := by
    rw [card_PSUF, ← pow_mul, mul_comm]
  have h4 : 4 ≤ 2 ^ (2 * (g + 1)) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (g + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 (2 * (g + 1)) :=
    ⟨Nat.prime_two, by omega, hk, fun h => by
      have := (Prod.mk.inj h).2
      omega, fun h => by
      have := (Prod.mk.inj h).2
      omega⟩
  exact Or.inl ⟨PSL_mem_classicalTags,
    SpecialLinear.statedClassicalModel_center_quotient m (PSUF g) hadm hF⟩

theorem PSUDualPairModel.exists_model_of_component {S : Set (GL (Fin n) (PSUF g))}
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    {P Q : Matrix (Fin n) (Fin k) (PSUF g)} {R W : Matrix (Fin k) (Fin n) (PSUF g)}
    {hD : PSUDualData g n k P Q R W} (hM : PSUDualPairModel n g S e P Q R W hD)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
       glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆) :
    2 ≤ k ∧ (dualPairEmbSU hD).range = J' ∧
      CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL k 2 (2 * (g + 1)) := by
  rw [hM.derived] at hJe
  have hne : J' ≠ ⊥ := tcNe_bot_of_isQuasisimple hJe.2.2
  have hperf : ⁅J', J'⁆ = J' := tcCommutator_self_of_isQuasisimple hJe.2.2
  have hk : 2 ≤ k := by
    by_contra hk
    have := subsingleton_SL_of_le_one (F := PSUF g) (k := k) (by omega)
    apply hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := hJe.1 hx
    rw [Subsingleton.elim a 1, map_one]
    exact Subgroup.one_mem _
  have hRq : CFSG.Assembly.IsQuasisimple ↥(dualPairEmbSU hD).range :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hM.inj).symm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (isQuasisimple_SL_PSUF g k hk))
  have hRR : IsComponentOf (dualPairEmbSU hD).range (dualPairEmbSU hD).range :=
    ⟨le_rfl, IsSubnormal.refl _, hRq⟩
  have hJ'eq : J' = (dualPairEmbSU hD).range :=
    isComponentOf_eq_of_perfect_le hRR hJe hJe.1 le_rfl hperf hne
  refine ⟨hk, hJ'eq.symm, ?_⟩
  let e1 : ↥J' ≃* Matrix.SpecialLinearGroup (Fin k) (PSUF g) :=
    (MulEquiv.subgroupCongr hJ'eq).trans (MonoidHom.ofInjective hM.inj).symm
  exact blueprintLieModel_PSL_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin k) (PSUF g)))
      (Subgroup.center ↥J') e1.symm (Subgroup.map_center_eq e1.symm))
    (lieModel_SL_PSUF g k hk)

theorem exists_blockModel_dualPair_PSU_explicit
    (n g : ℕ) (S : Set (GL (Fin n) (PSUF g)))
    (hSU : ∀ s ∈ S, s ∈ GUsub (PSUσ g) n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (PSUF g)}
    (he : IsPrimIdemIn (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    (hpair : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e),
       glBlockCentralizer (PSUj n g) S
        (e + formAdj (PSUσ g).toRingHom (Unitary.antidiag n) e)⁆) :
    ∃ (P Q : Matrix (Fin n) (Fin (Matrix.rank e)) (PSUF g))
      (R W : Matrix (Fin (Matrix.rank e)) (Fin n) (PSUF g))
      (hD : PSUDualData g n (Matrix.rank e) P Q R W),
      PSUDualPairModel n g S e P Q R W hD ∧ 2 ≤ Matrix.rank e ∧
        (dualPairEmbSU hD).range = J' ∧
        CFSG.Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL (Matrix.rank e) 2
          (2 * (g + 1)) := by
  obtain ⟨P, Q, R, W, hD, hM⟩ := exists_dualPairModel_PSU n g S hSU hS he hpair hdeg
  obtain ⟨hk, hrange, hmodel⟩ := hM.exists_model_of_component hJe
  exact ⟨P, Q, R, W, hD, hM, hk, hrange, hmodel⟩

end Component

end DualPair

end CFSG.StandardType.TableCRes
