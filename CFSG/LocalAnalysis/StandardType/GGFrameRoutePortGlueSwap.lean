module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueSwapBasic
import CFSG.CGT.Stroth77.Arch76Lemma2Coord
import CFSG.Quasithin.Background.RonanF57Unitary

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.FrameRoute.GlueSwap
open CFSG.CGT.Stroth77.Arch76 (pow_val_add)
open CFSG.Quasithin.RonanF57 (unitaryFieldData_of_card)

private lemma swp_diag_entry_eq {F : Type} [Field F] {m : ℕ} (hm : 3 ≤ m)
    (U V s : GL (Fin m) F) (e : Fin m → Fˣ) (cc : F) (i j : Fin m) (hij : i ≠ j)
    (hs : s = TauCeti.permutationGL (k := F) (Equiv.swap i j)⁻¹)
    (hscalar : ((s⁻¹ * (U⁻¹ * V) * s : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.scalar (Fin m) cc *
        ((U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F)))
    (hE : (U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F) =
      TauCeti.diagGL e) :
    e i = e j := by
  have hW : ((s⁻¹ * (U⁻¹ * V) * s : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      TauCeti.diagGL (e ∘ Equiv.swap i j) := by
    rw [hs, show ((TauCeti.permutationGL (k := F) (Equiv.swap i j)⁻¹)⁻¹) =
        TauCeti.permutationGL (k := F) (Equiv.swap i j) from by rw [← map_inv]; rfl,
      map_inv]
    rw [show U⁻¹ * V = TauCeti.diagGL e from by
      apply Units.ext
      simpa [Units.val_mul, Units.val_inv_eq_inv_val] using hE]
    have h := TauCeti.permutationGL_mul_diagGL_mul_inv (Equiv.swap i j) e
    rw [show (fun i_1 => e ((Equiv.swap i j)⁻¹ i_1)) = (e ∘ Equiv.swap i j) from by
      funext x; simp [Equiv.swap_inv]] at h
    exact congrArg (fun x : GL (Fin m) F => ((x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) h
  have hentry : TauCeti.diagGL (e ∘ Equiv.swap i j) =
      Matrix.scalar (Fin m) cc * TauCeti.diagGL e := by
    rw [← hW, hscalar, hE]
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]; omega)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hkfix : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hk.1 hk.2
  have hkentry : e (Equiv.swap i j k) = cc * e k := by
    have h := congrFun (congrFun hentry k) k
    simpa [TauCeti.diagGL_coe, Matrix.scalar, Matrix.diagonal_mul, hkfix] using h
  have hc1 : cc = 1 := by
    rw [hkfix] at hkentry
    exact (mul_right_cancel₀ (Units.ne_zero (e k))) (by simpa using hkentry.symm)
  have hi : e (Equiv.swap i j i) = cc * e i := by
    have h := congrFun (congrFun hentry i) i
    simpa [TauCeti.diagGL_coe, Matrix.scalar, Matrix.diagonal_mul] using h
  rw [Equiv.swap_apply_left, hc1, one_mul] at hi
  exact Units.ext hi.symm

private lemma swp_entry_scalar {G : Type} [Group G] {Bs : Subgroup G}
    {L : Subgroup G} {F : Type} [Field F] {m : ℕ} (hF : Nat.card F = 4)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L}
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {b b' : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs) {P tb tb' s : ↥(unitarySU 2 1 F m)}
    (htb : (tb : GL (Fin m) F) = TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b))
    (htb' : (tb' : GL (Fin m) F) = TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b'))
    (hbb' : b' = ((φ P : ↥L) : G) * b * ((φ P : ↥L) : G)⁻¹)
    (U V : GL (Fin m) F) (hU : (tb' : GL (Fin m) F) = U)
    (hV : (P * tb * P⁻¹ : GL (Fin m) F) = V) :
    ∃ cc : F, (((U * (s : GL (Fin m) F) * U⁻¹)⁻¹ * (V * (s : GL (Fin m) F) * V⁻¹) :
      GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal (fun _ => cc) := by
  classical
  let η : ↥(unitarySU 2 1 F m) :=
    (tb' * s * tb'⁻¹)⁻¹ * (P * tb * P⁻¹ * s * (P * tb * P⁻¹)⁻¹)
  have h1 : ((φ (tb' * s * tb'⁻¹) : ↥L) : G) = b'⁻¹ * ((φ s : ↥L) : G) * b' := by
    rw [show tb' = correctedDiagSU hF hζ hdet b' hb' from Subtype.ext htb']
    exact conjSU_phi hF hζ hdet hw hb' s
  have h2 : ((φ (P * tb * P⁻¹ * s * (P * tb * P⁻¹)⁻¹) : ↥L) : G) =
      b'⁻¹ * ((φ s : ↥L) : G) * b' := by
    have ht'eq : P * tb * P⁻¹ * s * (P * tb * P⁻¹)⁻¹ =
        P * (tb * (P⁻¹ * s * P) * tb⁻¹) * P⁻¹ := by group
    rw [ht'eq]
    have hinner : ((φ (tb * (P⁻¹ * s * P) * tb⁻¹) : ↥L) : G) =
        b⁻¹ * ((φ (P⁻¹ * s * P) : ↥L) : G) * b := by
      rw [show tb * (P⁻¹ * s * P) * tb⁻¹ = conjSU hF hζ hdet hb (P⁻¹ * s * P) from by
        rw [show tb = correctedDiagSU hF hζ hdet b hb from Subtype.ext htb]
        rfl]
      exact conjSU_phi hF hζ hdet hw hb (P⁻¹ * s * P)
    calc ((φ (P * (tb * (P⁻¹ * s * P) * tb⁻¹) * P⁻¹) : ↥L) : G)
        = ((φ P : ↥L) : G) * ((φ (tb * (P⁻¹ * s * P) * tb⁻¹) : ↥L) : G) *
            ((φ P : ↥L) : G)⁻¹ := by
          simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = ((φ P : ↥L) : G) * (b⁻¹ * ((φ (P⁻¹ * s * P) : ↥L) : G) * b) *
            ((φ P : ↥L) : G)⁻¹ := by rw [hinner]
      _ = ((φ P : ↥L) : G) * (b⁻¹ * (((φ P : ↥L) : G)⁻¹ * ((φ s : ↥L) : G) *
            ((φ P : ↥L) : G)) * b) * ((φ P : ↥L) : G)⁻¹ := by
          congr 2; simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = b'⁻¹ * ((φ s : ↥L) : G) * b' := by
          have hbbg : b' = ((φ P : ↥L) : G) * b * ((φ P : ↥L) : G)⁻¹ := hbb'
          rw [hbbg]; group
  have hφη : φ η = 1 := by
    apply Subtype.ext; rw [show φ η = (φ (tb' * s * tb'⁻¹))⁻¹ *
      φ (P * tb * P⁻¹ * s * (P * tb * P⁻¹)⁻¹) by simp [η]]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, h1, h2]
    group
  obtain ⟨cc, hc⟩ := hφker η hφη; refine ⟨cc, ?_⟩
  let W : GL (Fin m) F := (U * (s : GL (Fin m) F) * U⁻¹)⁻¹ * (V * (s : GL (Fin m) F) * V⁻¹)
  have hP : ((P : GL (Fin m) F) * (tb : GL (Fin m) F) * (P : GL (Fin m) F)⁻¹) = V := by
    simpa [Subgroup.coe_inv] using hV
  have h : ((η : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((W : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
    apply congrArg (fun x : GL (Fin m) F => ((x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
    dsimp [η, W]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hU, hP]
  rw [← h]; exact hc

private lemma swp_entry_eq {G : Type} [Group G] {Bs : Subgroup G}
    {L : Subgroup G} {F : Type} [Field F] {m : ℕ} (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {φ : ↥(unitarySU 2 1 F m) →* ↥L}
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {a c : Fin m} {b b' : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs)
    (hbb' : b' = ((φ (CFSG.SeitzReduction.UnitaryPilot.permSU (unitaryFieldData_of_card hF)
      (Equiv.swap a c)) : ↥L) : G) * b *
      (((φ (CFSG.SeitzReduction.UnitaryPilot.permSU (unitaryFieldData_of_card hF)
      (Equiv.swap a c)) : ↥L) : G))⁻¹)
    {i j : Fin m} (hij : i ≠ j) :
    (correctedDiag hdet (ζ := ζ) b' i)⁻¹ * correctedDiag hdet (ζ := ζ) b (Equiv.swap a c i) =
      (correctedDiag hdet (ζ := ζ) b' j)⁻¹ * correctedDiag hdet (ζ := ζ) b (Equiv.swap a c j ) := by
  classical
  let hU := unitaryFieldData_of_card hF
  let P : ↥(unitarySU 2 1 F m) := CFSG.SeitzReduction.UnitaryPilot.permSU hU (Equiv.swap a c)
  let g : G := ((φ P : ↥L) : G)
  let tb : ↥(unitarySU 2 1 F m) := correctedDiagSU hF hζ hdet b hb
  let tb' : ↥(unitarySU 2 1 F m) := correctedDiagSU hF hζ hdet b' hb'
  let s : ↥(unitarySU 2 1 F m) := CFSG.SeitzReduction.UnitaryPilot.permSU hU (Equiv.swap i j)
  let U : GL (Fin m) F := TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b')
  let V : GL (Fin m) F := TauCeti.diagGL (fun t => correctedDiag hdet (ζ := ζ) b (Equiv.swap a c t))
  let e : Fin m → Fˣ := fun t => (correctedDiag hdet (ζ := ζ) b' t)⁻¹ *
    correctedDiag hdet (ζ := ζ) b (Equiv.swap a c t)
  have hV : (P * tb * P⁻¹ : GL (Fin m) F) = V := by
    dsimp only [P, tb, V]
    show (CFSG.SeitzReduction.UnitaryPilot.permSU hU (Equiv.swap a c) : GL (Fin m) F) *
      ((correctedDiagSU hF hζ hdet b hb : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) *
      (CFSG.SeitzReduction.UnitaryPilot.permSU hU (Equiv.swap a c) : GL (Fin m) F)⁻¹ = _
    rw [show ((correctedDiagSU hF hζ hdet b hb : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
        TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) from rfl,
      permSU_conj_diagGL hU (Equiv.swap a c) (correctedDiag hdet (ζ := ζ) b)]
    rfl
  obtain ⟨cc, hc⟩ := swp_entry_scalar hF hφker hζ hw hdet hb hb' rfl
    (rfl : (tb' : GL (Fin m) F) = U) (by simpa [g, P] using hbb') U V rfl hV
  have hscalar := conj_scalar_eq U V (s : GL (Fin m) F) cc
    (by simpa [Matrix.scalar_apply] using hc)
  have hE : (U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F) =
      TauCeti.diagGL e := by
    have hEgl : U⁻¹ * V = TauCeti.diagGL e := by
      dsimp [U, V, e]
      rw [show (TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b'))⁻¹ =
          TauCeti.diagGL (fun t => (correctedDiag hdet (ζ := ζ) b' t)⁻¹) from (map_inv _ _).symm,
        ← map_mul]
      exact congrArg TauCeti.diagGL (by funext t; simp [Pi.mul_apply])
    rw [← show ((U⁻¹ * V : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (U⁻¹ : Matrix (Fin m) (Fin m) F) * (V : Matrix (Fin m) (Fin m) F) from by
        simp [Units.val_mul, Units.val_inv_eq_inv_val], hEgl]
  exact swp_diag_entry_eq hm U V (s : GL (Fin m) F) e cc i j hij
    (by simpa [s] using permSU_coe hU (Equiv.swap i j)) hscalar hE

private lemma swp_dt_ratio {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    {u : G → Fin m → ZMod 3} {F : Type} [Field F] {ζ : Fˣ}
    (hζ : orderOf ζ = 3) (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {a c : Fin m} (b b' : G) (i : Fin m) :
    (correctedDiag hdet (ζ := ζ) b' i)⁻¹ * correctedDiag hdet (ζ := ζ) b (Equiv.swap a c i) =
      ζ ^ (((u b (Equiv.swap a c i) - coordinateSumRoot hdet b) -
        (u b' i - coordinateSumRoot hdet b')).val) := by
  have h3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hA : ∀ A : ZMod 3, (ζ ^ A.val)⁻¹ = ζ ^ ((-A).val) := by
    intro A
    have h : ζ ^ A.val * ζ ^ ((-A).val) = 1 := by
      rw [← pow_val_add h3, show A + -A = 0 by abel, ZMod.val_zero, pow_zero]
    exact (eq_inv_of_mul_eq_one_right h).symm
  simp only [correctedDiag]
  rw [hA, ← pow_val_add h3]
  exact congrArg (fun z : ZMod 3 => ζ ^ z.val) (by abel)

private lemma swp_conj_zpow {G : Type} [Group G] {g x : G} (h : Commute g x) (j : ℤ) :
    g * x ^ j * g⁻¹ = x ^ j := by
  rw [(Commute.zpow_right h j).eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma swp_mem_normalizer {G : Type} [Group G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hBs : GGBstar 3 B Bs) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] {m : ℕ} (hF : Nat.card F = 4)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} (hφs : Function.Surjective φ)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0) {a c : Fin m} :
    ((φ (CFSG.SeitzReduction.UnitaryPilot.permSU (unitaryFieldData_of_card hF)
      (Equiv.swap a c)) : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  let P : ↥(unitarySU 2 1 F m) := CFSG.SeitzReduction.UnitaryPilot.permSU
    (unitaryFieldData_of_card hF) (Equiv.swap a c)
  let g : G := ((φ P : ↥L) : G)
  have hcomm : Commute g x := by
    have h := Subgroup.mem_centralizer_iff.mp (hLx (φ P).2) x (by simp)
    show g * x = x * g
    exact h.symm
  have hg : g ^ 2 = 1 := by
    have hsq : P * P = 1 :=
      permSU_swap_mul_self (unitaryFieldData_of_card hF) (a := a) (c := c)
    calc g ^ 2 = (((φ P : ↥L) : G) * ((φ P : ↥L) : G)) := by rw [pow_two]
      _ = ((φ (P * P) : ↥L) : G) := by rw [← Subgroup.coe_mul, ← map_mul]
      _ = 1 := by rw [hsq, map_one]; rfl
  have hfwd : ∀ b ∈ Bs, g * b * g⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨j, hj⟩ := exists_zpow_mul_diag hBs hxBs hker hF hφs hζ hw hdet hb
    let t : ↥(unitarySU 2 1 F m) := correctedDiagSU hF hζ hdet b hb
    let u' : ↥(unitarySU 2 1 F m) := P * t * P⁻¹
    have hu' : ((u' : GL (Fin m) F) = TauCeti.diagGL
        (fun i => correctedDiag hdet (ζ := ζ) b (Equiv.swap a c i))) := by
      dsimp only [u', t]
      show (P : GL (Fin m) F) * ((correctedDiagSU hF hζ hdet b hb : ↥(unitarySU 2 1 F m)) :
        GL (Fin m) F) * (P : GL (Fin m) F)⁻¹ = _
      rw [show ((correctedDiagSU hF hζ hdet b hb : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
          TauCeti.diagGL (correctedDiag hdet (ζ := ζ) b) from rfl,
        permSU_conj_diagGL (unitaryFieldData_of_card hF) (Equiv.swap a c)
          (correctedDiag hdet (ζ := ζ) b)]
      rfl
    have hu'_mem : ((φ u' : ↥L) : G) ∈ Bs :=
      diag_phi_mem_Bs hBs hw (fun i => correctedDiag_pow_three hζ hdet b (Equiv.swap a c i)) hu'
    have hg_inv : g * ((φ t : ↥L) : G)⁻¹ * g⁻¹ = ((φ u' : ↥L) : G)⁻¹ := by
      dsimp only [g, u', t]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hfinal : g * b * g⁻¹ = x ^ j * ((φ u' : ↥L) : G)⁻¹ := by
      calc g * b * g⁻¹ = g * (x ^ j * ((φ t : ↥L) : G)⁻¹) * g⁻¹ := by rw [hj]
        _ = (g * x ^ j * g⁻¹) * (g * ((φ t : ↥L) : G)⁻¹ * g⁻¹) := by group
        _ = x ^ j * ((φ u' : ↥L) : G)⁻¹ := by rw [swp_conj_zpow hcomm j, hg_inv]
    rw [hfinal]
    exact Subgroup.mul_mem Bs (Subgroup.zpow_mem (K := Bs) hxBs j) (Subgroup.inv_mem Bs hu'_mem)
  have hginv : g⁻¹ * g⁻¹ = 1 := by
    rw [← mul_inv_rev, show g * g = 1 by simpa [pow_two] using hg, inv_one]
  refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨hfwd b, fun hb => ?_⟩
  have hb2 : g * (g * b * g⁻¹) * g⁻¹ ∈ Bs := hfwd (g * b * g⁻¹) hb
  have hconj : g * (g * b * g⁻¹) * g⁻¹ = b := by
    calc g * (g * b * g⁻¹) * g⁻¹ = (g * g) * b * (g⁻¹ * g⁻¹) := by group
      _ = b := by rw [show g * g = 1 by simpa [pow_two] using hg, hginv]; group
  rwa [hconj] at hb2

theorem exists_swap_of_unitaryModel {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hBs : GGBstar 3 B Bs) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {m : ℕ} (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {u : G → Fin m → ZMod 3}
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    (hdet : ¬ 3 ∣ m ∨ ∀ b ∈ Bs, ∑ i, u b i = 0)
    {a c : Fin m} (hac : a ≠ c) :
    ∃ g ∈ L, g ∈ Subgroup.normalizer (Bs : Set G) ∧ g ^ 2 = 1 ∧
      ∀ b ∈ Bs, ∃ k : ZMod 3, ∀ i, u (g * b * g⁻¹) i = u b (Equiv.swap a c i) + k := by
  classical
  let P : ↥(unitarySU 2 1 F m) := CFSG.SeitzReduction.UnitaryPilot.permSU
    (unitaryFieldData_of_card hF) (Equiv.swap a c)
  let g : G := ((φ P : ↥L) : G)
  have hg2 : g ^ 2 = 1 := by
    have hsq : P * P = 1 :=
      permSU_swap_mul_self (unitaryFieldData_of_card hF) (a := a) (c := c)
    calc g ^ 2 = (((φ P : ↥L) : G) * ((φ P : ↥L) : G)) := by rw [pow_two]
      _ = ((φ (P * P) : ↥L) : G) := by rw [← Subgroup.coe_mul, ← map_mul]
      _ = 1 := by rw [hsq, map_one]; rfl
  refine ⟨g, (φ P).2, ?_, hg2, ?_⟩
  · simpa [g, P] using
      swp_mem_normalizer (a := a) (c := c) hBs hxBs hLx hker hF hφs hζ hw hdet
  · intro b hb
    have hnorm :=
      swp_mem_normalizer (a := a) (c := c) hBs hxBs hLx hker hF hφs hζ hw hdet
    have hb' : g * b * g⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff (H := Bs) (g := g)).mp
        (by simpa [g, P] using hnorm) b).mp hb
    let e : Fin m → Fˣ := fun t => (correctedDiag hdet (ζ := ζ) (g * b * g⁻¹) t)⁻¹ *
      correctedDiag hdet (ζ := ζ) b (Equiv.swap a c t)
    have hentry : ∀ i j : Fin m, e i = e j := by
      intro i j
      by_cases hij : i = j
      · subst hij; rfl
      · exact swp_entry_eq hF hm hφker hζ hw hdet hb hb' (by dsimp [g, P]) hij
    let t0 : Fin m := ⟨0, by omega⟩
    refine ⟨u (g * b * g⁻¹) t0 - u b (Equiv.swap a c t0), fun i => ?_⟩
    have hpow : ζ ^ ((u b (Equiv.swap a c i) - coordinateSumRoot hdet b) -
        (u (g * b * g⁻¹) i - coordinateSumRoot hdet (g * b * g⁻¹))).val =
        ζ ^ ((u b (Equiv.swap a c t0) - coordinateSumRoot hdet b) -
        (u (g * b * g⁻¹) t0 - coordinateSumRoot hdet (g * b * g⁻¹))).val := by
      rw [← swp_dt_ratio hζ hdet b (g * b * g⁻¹) i,
        ← swp_dt_ratio hζ hdet b (g * b * g⁻¹) t0]
      exact hentry i t0
    have hR := (pow_val_eq_iff hζ _ _).mp hpow
    linear_combination -hR

end CFSG.StandardType.FrameRoute

end
