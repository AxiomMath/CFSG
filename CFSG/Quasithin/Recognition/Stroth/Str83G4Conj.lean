module

public import CFSG.Quasithin.Vol2.Ch10SecKGBender
public import CFSG.Quasithin.Background.F7E1
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str83G4_inf_conjugate_eq_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g : G}
    (hg : g ∈ L1 ⊔ S) (hgN : g ∉ Subgroup.normalizer (S : Set G)) :
    S ⊓ CFSG.conjugate S g = Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, hSz, -, -⟩ := hfr
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hgP : g⁻¹ ∈ P1 L1 L2 S := hHleP1 ((L1 ⊔ S).inv_mem hg)
  have hgB : g⁻¹ ∉ bigB L1 L2 S := fun hb =>
    hgN (by simpa using (Subgroup.normalizer (S : Set G)).inv_mem (hB hb))
  have h1 : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1) :=
    Or.inl ⟨a, ha, hSz⟩
  have h := f112_sylow_inf_conj_eq_pCoreOf_left hF hB h1 hgP hgB
  exact h

theorem str83G4_inf_conjugate_eq_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {h : G}
    (hh : h ∈ L2 ⊔ S) (hhN : h ∉ Subgroup.normalizer (S : Set G)) :
    S ⊓ CFSG.conjugate S h = Q2 L1 L2 S := by
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hHleP2 : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hhP : h⁻¹ ∈ P2 L1 L2 S := hHleP2 ((L2 ⊔ S).inv_mem hh)
  have hhB : h⁻¹ ∉ bigB L1 L2 S := fun hb =>
    hhN (by simpa using (Subgroup.normalizer (S : Set G)).inv_mem (hB hb))
  have h2 : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2) :=
    Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩)
  have h := f112_sylow_inf_conj_eq_pCoreOf_right hF hB h2 hhP hhB
  exact h

theorem str83G4_not_le_normalizer_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ¬ L1 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
  intro hle
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hL2le : L2 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hG0le : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    have hG0eq : L1 ⊔ L2 ⊔ S = (L1 ⊔ S) ⊔ L2 := by
      rw [sup_assoc, sup_comm L2 S, ← sup_assoc]
    rw [hG0eq]
    exact sup_le hle hL2le
  have hZ2leS : Z2 L1 L2 S ≤ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF))
  have hZ2leG0 : Z2 L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
    hZ2leS.trans (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S)
  have hpc : Z2 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZ2leG0 hG0le
      ((pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le
        ((omegaOneCenterOf_le (Q2 L1 L2 S))))
  rw [hF.1.o2] at hpc
  have hZ2bot : Z2 L1 L2 S = ⊥ := le_bot_iff.mp hpc
  exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hZ2bot)))

private theorem le_normalizer_q1_of_sup (L1 L2 S : Subgroup G) :
    L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
  (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S))

theorem str83G4_centralizer_conjugate_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g : G}
    (hg : g ∈ L1 ⊔ S) :
    Q1 L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G) =
      Q1 L1 L2 S ⊓ CFSG.conjugate (Q2 L1 L2 S) g := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, -, -, hSQ2C, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hQ1N : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_q1_of_sup L1 L2 S
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hQ1g : ∀ x ∈ Q1 L1 L2 S, g * x * g⁻¹ ∈ Q1 L1 L2 S := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hQ1N hg) x).mp hx
  ext x
  constructor
  · rintro ⟨hxQ1, hxC⟩
    refine ⟨hxQ1, ?_⟩
    change x ∈ CFSG.conjugate (Q2 L1 L2 S) g
    rw [CFSG.mem_conjugate_iff]
    have hgxQ1 : g * x * g⁻¹ ∈ Q1 L1 L2 S := hQ1g x hxQ1
    have hgxS : g * x * g⁻¹ ∈ S := hQ1S hgxQ1
    have hcent : g * x * g⁻¹ ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzmem : g⁻¹ * z * g ∈ CFSG.conjugate (Z2 L1 L2 S) g := by
        rw [CFSG.mem_conjugate_iff]
        simpa [mul_assoc] using hz
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC (g⁻¹ * z * g) hzmem
      have := congrArg (fun y => g * y * g⁻¹) hcomm
      simpa [mul_assoc] using this
    have hmem : g * x * g⁻¹ ∈ S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      Subgroup.mem_inf.mpr ⟨hgxS, hcent⟩
    rwa [hSQ2C] at hmem
  · rintro ⟨hxQ1, hxQ2g⟩
    refine ⟨hxQ1, ?_⟩
    change x ∈ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    change w ∈ CFSG.conjugate (Z2 L1 L2 S) g at hw
    rw [CFSG.mem_conjugate_iff] at hw
    have hxQ2 : g * x * g⁻¹ ∈ Q2 L1 L2 S :=
      (CFSG.mem_conjugate_iff (Q2 L1 L2 S) g x).mp hxQ2g
    have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hQ2C hxQ2) (g * w * g⁻¹) hw
    have := congrArg (fun y => g⁻¹ * y * g) hcomm
    simpa [mul_assoc] using this

theorem str83G4_relIndex_q1_conjugate_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {g : G}
    (hg : g ∈ L1 ⊔ S) :
    (Q1 L1 L2 S ⊓ CFSG.conjugate (Q2 L1 L2 S) g).relIndex (Q1 L1 L2 S) =
      2 ^ (2 * a + 1) := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  have hS : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_pCoreOf_sup_pCoreOf hF hB (Or.inl ⟨a, ha, hSz⟩) (by omega) hL2
  have hQ1N : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_q1_of_sup L1 L2 S
  have hQ1g : CFSG.conjugate (Q1 L1 L2 S) g = Q1 L1 L2 S :=
    CFSG.conjugate_eq_self_of_mem_normalizer (hQ1N hg)
  have hHconj : CFSG.conjugate (L1 ⊔ S) g = L1 ⊔ S :=
    CFSG.conjugate_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hQ2gH : CFSG.conjugate (Q2 L1 L2 S) g ≤ L1 ⊔ S :=
    (Subgroup.map_mono (hQ2S.trans (le_sup_right : S ≤ L1 ⊔ S))).trans (le_of_eq hHconj)
  have hQ2gN : CFSG.conjugate (Q2 L1 L2 S) g ≤
      Subgroup.normalizer (Q1 L1 L2 S : Set G) := hQ2gH.trans hQ1N
  have hSg : CFSG.conjugate S g = Q1 L1 L2 S ⊔ CFSG.conjugate (Q2 L1 L2 S) g := by
    conv_lhs => rw [← hS]
    change (Q1 L1 L2 S ⊔ Q2 L1 L2 S).map (MulAut.conj g⁻¹).toMonoidHom =
      Q1 L1 L2 S ⊔ (Q2 L1 L2 S).map (MulAut.conj g⁻¹).toMonoidHom
    rw [Subgroup.map_sup]
    exact congrArg (fun X => X ⊔ (Q2 L1 L2 S).map (MulAut.conj g⁻¹).toMonoidHom) hQ1g
  have hrel := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := CFSG.conjugate (Q2 L1 L2 S) g) (K := Q1 L1 L2 S) hQ2gN
  have hrelQ : (Q1 L1 L2 S ⊓ CFSG.conjugate (Q2 L1 L2 S) g).relIndex (Q1 L1 L2 S) =
      (CFSG.conjugate (Q2 L1 L2 S) g).relIndex (CFSG.conjugate S g) := by
    have h := hrel.1
    rw [sup_comm] at h
    rw [inf_comm (CFSG.conjugate (Q2 L1 L2 S) g) (Q1 L1 L2 S)] at h
    conv_rhs => rw [hSg]
    exact h.symm
  have hrelConj : (CFSG.conjugate (Q2 L1 L2 S) g).relIndex (CFSG.conjugate S g) =
      (Q2 L1 L2 S).relIndex S :=
    Subgroup.relIndex_pointwise_smul (MulAut.conj g⁻¹) (Q2 L1 L2 S) S
  rw [hrelQ, hrelConj, str86_relIndex_q2_s hF hB (by omega) hL2]

private theorem str83X_eq_conjClosure_L1 {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    str83X L1 L2 S = conjClosure (Z2 L1 L2 S) L1 := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hF.1
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  refine le_antisymm ?_ (conjClosure_mono le_rfl (le_sup_left : L1 ≤ P1 L1 L2 S))
  refine conjClosure_le ?_
  intro p hp z hz
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hp
  have hbz : b * z * b⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hBZ hb) z).mp hz
  simpa [mul_assoc] using mem_conjClosure (Z := Z2 L1 L2 S) (H := L1) hl hbz

private theorem iInf_conjugate_q2_le_centralizer_str83X {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) :
    (⨅ (g : G) (_ : g ∈ L1 ⊔ S), CFSG.conjugate (Q2 L1 L2 S) g) ≤
      Subgroup.centralizer (str83X L1 L2 S : Set G) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  let I : Subgroup G := ⨅ (g : G) (_ : g ∈ L1 ⊔ S), CFSG.conjugate (Q2 L1 L2 S) g
  change I ≤ Subgroup.centralizer (str83X L1 L2 S : Set G)
  have hXeq := str83X_eq_conjClosure_L1 hfr'
  have hbound : ∀ l ∈ L1, ∀ z ∈ Z2 L1 L2 S,
      l * z * l⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
    intro l hl z hz
    have hIle : I ≤ CFSG.conjugate (Q2 L1 L2 S) l⁻¹ := by
      change (⨅ (g : G) (_ : g ∈ L1 ⊔ S), CFSG.conjugate (Q2 L1 L2 S) g) ≤
        CFSG.conjugate (Q2 L1 L2 S) l⁻¹
      exact (iInf_le (fun g : G => ⨅ (_ : g ∈ L1 ⊔ S),
          CFSG.conjugate (Q2 L1 L2 S) g) l⁻¹).trans
        (iInf_le (fun _ : l⁻¹ ∈ L1 ⊔ S => CFSG.conjugate (Q2 L1 L2 S) l⁻¹)
          ((L1 ⊔ S).inv_mem ((le_sup_left : L1 ≤ L1 ⊔ S) hl)))
    have hcent : CFSG.conjugate (Q2 L1 L2 S) l⁻¹ ≤
        Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) l⁻¹ : Set G) := by
      intro q hq
      change q ∈ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) l⁻¹ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      change w ∈ CFSG.conjugate (Z2 L1 L2 S) l⁻¹ at hw
      rw [CFSG.mem_conjugate_iff] at hq hw
      rw [inv_inv] at hq hw
      have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
        SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
      have hcomm : (l⁻¹ * w * l) * (l⁻¹ * q * l) =
          (l⁻¹ * q * l) * (l⁻¹ * w * l) := by
        simpa [mul_assoc] using
          Subgroup.mem_centralizer_iff.mp (hQ2C hq) (l⁻¹ * w * l) hw
      calc w * q = l * ((l⁻¹ * w * l) * (l⁻¹ * q * l)) * l⁻¹ := by group
        _ = l * ((l⁻¹ * q * l) * (l⁻¹ * w * l)) * l⁻¹ := by rw [hcomm]
        _ = q * w := by group
    have hIleC : I ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) l⁻¹ : Set G) :=
      hIle.trans hcent
    have hwmem : l * z * l⁻¹ ∈ CFSG.conjugate (Z2 L1 L2 S) l⁻¹ := by
      rw [CFSG.mem_conjugate_iff]
      simpa [mul_assoc] using hz
    exact (Subgroup.le_centralizer_iff.mp hIleC) hwmem
  have hXle : str83X L1 L2 S ≤ Subgroup.centralizer (I : Set G) := by
    rw [hXeq]
    exact conjClosure_le hbound
  exact Subgroup.le_centralizer_iff.mp hXle

theorem str83G4_str83Y_eq_iInf
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    str83Y L1 L2 S = ⨅ (g : G) (_ : g ∈ L1 ⊔ S), CFSG.conjugate (Q2 L1 L2 S) g := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  let H : Subgroup G := L1 ⊔ S
  let I : Subgroup G := ⨅ (g : G) (_ : g ∈ H), CFSG.conjugate (Q2 L1 L2 S) g
  change str83Y L1 L2 S = I
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
        rw [show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)
  have hHP1 : H ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hIleQ2 : I ≤ Q2 L1 L2 S := by
    change (⨅ (g : G) (_ : g ∈ H), CFSG.conjugate (Q2 L1 L2 S) g) ≤ Q2 L1 L2 S
    have h := (iInf_le (fun g : G => ⨅ (_ : g ∈ H),
        CFSG.conjugate (Q2 L1 L2 S) g) 1).trans
      (iInf_le (fun _ : (1 : G) ∈ H => CFSG.conjugate (Q2 L1 L2 S) 1) H.one_mem)
    simpa using h
  have hI2 : IsPGroup 2 I :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hIleQ2
  have hIleH : I ≤ H := hIleQ2.trans (hQ2S.trans le_sup_right)
  have hconjI : ∀ h ∈ H, CFSG.conjugate I h = I := by
    intro h hh
    ext x
    constructor
    · intro hx
      rw [CFSG.mem_conjugate_iff] at hx
      rw [Subgroup.mem_iInf]
      intro g
      rw [Subgroup.mem_iInf]
      intro hg
      have hg' : g * h⁻¹ ∈ H := H.mul_mem hg (H.inv_mem hh)
      have hmem := (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (g * h⁻¹))) hg'
      rw [CFSG.mem_conjugate_iff] at hmem
      rw [CFSG.mem_conjugate_iff]
      simpa [mul_assoc] using hmem
    · intro hx
      rw [CFSG.mem_conjugate_iff]
      rw [Subgroup.mem_iInf]
      intro g
      rw [Subgroup.mem_iInf]
      intro hg
      have hg' : g * h ∈ H := H.mul_mem hg hh
      have hmem := (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (g * h))) hg'
      rw [CFSG.mem_conjugate_iff] at hmem
      rw [CFSG.mem_conjugate_iff]
      simpa [mul_assoc] using hmem
  have hInorm : H ≤ Subgroup.normalizer (I : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← CFSG.mem_conjugate_iff]
    rw [hconjI h hh]
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S := by
    change pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hIleQ1 : I ≤ Q1 L1 L2 S := by
    have h := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hIleH hInorm hI2
    rwa [hpCoreH] at h
  have hIleCX : I ≤ Subgroup.centralizer (str83X L1 L2 S : Set G) := by
    change (⨅ (g : G) (_ : g ∈ H), CFSG.conjugate (Q2 L1 L2 S) g) ≤
      Subgroup.centralizer (str83X L1 L2 S : Set G)
    simpa [H] using iInf_conjugate_q2_le_centralizer_str83X hfr'
  have hYleI : str83Y L1 L2 S ≤ I := by
    intro x hx
    obtain ⟨hxQ1, hxC⟩ := hx
    rw [Subgroup.mem_iInf]
    intro g
    rw [Subgroup.mem_iInf]
    intro hg
    have hB6 := str83G4_centralizer_conjugate_z2 hfr' (g := g) hg
    have hxCZ : x ∈ Subgroup.centralizer
        (CFSG.conjugate (Z2 L1 L2 S) g : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      change z ∈ CFSG.conjugate (Z2 L1 L2 S) g at hz
      rw [CFSG.mem_conjugate_iff] at hz
      have hmemX : z ∈ str83X L1 L2 S := by
        have hgen := mem_conjClosure (Z := Z2 L1 L2 S) (H := P1 L1 L2 S)
          (hHP1 (H.inv_mem hg)) hz
        simpa [str83X, mul_assoc] using hgen
      exact Subgroup.mem_centralizer_iff.mp hxC z hmemX
    have hxall : x ∈ Q1 L1 L2 S ⊓ CFSG.conjugate (Q2 L1 L2 S) g := by
      rw [← hB6]
      exact ⟨hxQ1, hxCZ⟩
    exact hxall.2
  refine le_antisymm hYleI ?_
  intro x hx
  exact ⟨hIleQ1 hx, hIleCX hx⟩

theorem str83G4_normalizer_z2_eq
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    (L1 ⊔ S) ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G) =
      (L1 ⊔ S) ⊓ Subgroup.normalizer (S : Set G) := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
          conv_lhs => rw [hS1]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [← sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
        rw [show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  rw [hsup1]
  let H : Subgroup G := L1 ⊔ Q1 L1 L2 S
  have hSH : S ≤ H := by
    rw [hS1]
    exact sup_le ((inf_le_right : S ⊓ L1 ≤ L1).trans
      (le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S)) le_sup_right
  have hQ1H : Q1 L1 L2 S ≤ H := le_sup_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxN⟩ := hx
    have hxP1 : x ∈ P1 L1 L2 S := by
      exact (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
        (by rwa [← hsup1] at hxH)
    set π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H) with hπ
    let Sbar : Subgroup (oTwoQuot ↥H) := (S.subgroupOf H).map π
    let NZ : Subgroup G := H ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G)
    let N : Subgroup ↥H := NZ.subgroupOf H
    let M : Subgroup (oTwoQuot ↥H) := N.map π
    have hpCoreH : pCore 2 ↥H = (Q1 L1 L2 S).subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_right : Q1 L1 L2 S ≤ H)]
      exact pCoreOf_sup_pCoreOf hF.1
    have hSylH : IsSylowTwoOf S H := isSylowTwoOf_sup_pCoreOf hF.1 hS1
    have hSylSbar : IsSylowTwoOf Sbar ⊤ :=
      CFSG.Quasithin.Vol2.Ch10.SecA.isSylowTwoOf_map_of_surjective hSylH π
        (QuotientGroup.mk'_surjective _)
    have hSNZ : S ≤ NZ := le_inf hSH (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hSM : Sbar ≤ M := Subgroup.map_mono (Subgroup.subgroupOf_mono H hSNZ)
    obtain ⟨e⟩ := hSz
    have hSuz : CFSG.Blueprint.SuzukiModel (oTwoQuot ↥H) 2 (2 * a + 1) :=
      CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha ((oTwoQuotSupEquiv hF.1).trans e)
    have hfact := CFSG.Quasithin.Vol2.Ch10.SecB.factBenderOver_holds
      (K := oTwoQuot ↥H) (Or.inr ⟨2 * a + 1, hSuz⟩) Sbar M hSylSbar hSM
    have hxNZ : x ∈ NZ := Subgroup.mem_inf.mpr ⟨hxH, hxN⟩
    have hπx : π ⟨x, hxH⟩ ∈ M :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxNZ)
    rcases hfact with hMle | hMtop
    ·
      have hπxN : π ⟨x, hxH⟩ ∈ Subgroup.normalizer (Sbar : Set (oTwoQuot ↥H)) := hMle hπx
      refine ⟨hxH, ?_⟩
      change x ∈ Subgroup.normalizer (S : Set G)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · rintro y ⟨s, hs, rfl⟩
        have hsH : s ∈ H := hSH hs
        have hπs : π ⟨s, hsH⟩ ∈ Sbar :=
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hs)
        have hconj : π ⟨x * s * x⁻¹,
            H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ ∈ Sbar := by
          have h := (Subgroup.mem_normalizer_iff.mp hπxN (π ⟨s, hsH⟩)).mp hπs
          have hsub : (⟨x * s * x⁻¹,
              H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ : ↥H) =
              ⟨x, hxH⟩ * ⟨s, hsH⟩ * (⟨x, hxH⟩)⁻¹ := by
            apply Subtype.ext
            simp [mul_assoc]
          rw [hsub, map_mul, map_mul, map_inv]
          exact h
        obtain ⟨t, htS, hπt⟩ := Subgroup.mem_map.mp hconj
        have htSG : (t : G) ∈ S := htS
        have hker : (⟨x * s * x⁻¹,
            H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ * t⁻¹) ∈ pCore 2 ↥H := by
          have h1 : π (⟨x * s * x⁻¹,
              H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ * t⁻¹) = 1 := by
            rw [map_mul, map_inv, hπt, mul_inv_cancel]
          rw [← QuotientGroup.ker_mk' (pCore 2 ↥H)]
          exact MonoidHom.mem_ker.mpr h1
        have hQ : ((⟨x * s * x⁻¹,
            H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ * t⁻¹ : ↥H) : G) ∈
            Q1 L1 L2 S := by
          rw [hpCoreH] at hker
          exact hker
        have hQleS : Q1 L1 L2 S ≤ S := hQ1S
        have heq : x * s * x⁻¹ = ((⟨x * s * x⁻¹,
            H.mul_mem (H.mul_mem hxH hsH) (H.inv_mem hxH)⟩ * t⁻¹ : ↥H) : G) * (t : G) := by
          simp [mul_assoc]
        change x * s * x⁻¹ ∈ S
        rw [heq]
        exact S.mul_mem (hQleS hQ) htSG
      · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    ·
      have hHleNZ : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
        intro h hh
        have hπh : π ⟨h, hh⟩ ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hπn⟩ := Subgroup.mem_map.mp hπh
        have hnNZ : (n : G) ∈ NZ := Subgroup.mem_subgroupOf.mp hn
        have hker : n⁻¹ * ⟨h, hh⟩ ∈ pCore 2 ↥H := by
          have h1 : π (n⁻¹ * ⟨h, hh⟩) = 1 := by
            rw [map_mul, map_inv, hπn, inv_mul_cancel]
          rw [← QuotientGroup.ker_mk' (pCore 2 ↥H)]
          exact MonoidHom.mem_ker.mpr h1
        have hqQ1 : ((n⁻¹ * ⟨h, hh⟩ : ↥H) : G) ∈ Q1 L1 L2 S := by
          rw [hpCoreH] at hker
          exact hker
        have hqNZ : ((n⁻¹ * ⟨h, hh⟩ : ↥H) : G) ∈
            Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
          le_normalizer_z2_of_sylow (hQ1S hqQ1)
        have hnNZ' : (n : G) ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hnNZ.2
        have heq : h = (n : G) * ((n⁻¹ * ⟨h, hh⟩ : ↥H) : G) := by simp [mul_assoc]
        rw [heq]
        exact (Subgroup.mem_inf.mpr
          ⟨H.mul_mem n.2 (n⁻¹ * ⟨h, hh⟩).2,
            (Subgroup.normalizer (Z2 L1 L2 S : Set G)).mul_mem hnNZ' hqNZ⟩).2
      exfalso
      exact (str83G4_not_le_normalizer_z2 hfr') (by
        rw [hsup1]
        exact hHleNZ)
  · intro x hx
    obtain ⟨hxH, hxN⟩ := hx
    have hxP1 : x ∈ P1 L1 L2 S := by
      exact (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
        (by rwa [← hsup1] at hxH)
    have hxBigB : x ∈ bigB L1 L2 S :=
      str86_p1_inf_normalizer_le_bigB hF hB (Subgroup.mem_inf.mpr ⟨hxP1, hxN⟩)
    exact ⟨hxH, hBZ hxBigB⟩


theorem str83G4_normalizer_conjugate_z2
    {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hgN : g ∉ Subgroup.normalizer (S : Set G)) :
    S ⊓ Subgroup.normalizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G) = Q1 L1 L2 S := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hB4 := str83G4_inf_conjugate_eq_q1 hfr' hg hgN
  have hB3 := str83G4_normalizer_z2_eq hfr'
  have hSleH : S ≤ L1 ⊔ S := le_sup_right
  have hHconj : CFSG.conjugate (L1 ⊔ S) g = L1 ⊔ S :=
    CFSG.conjugate_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hNconjZ2 : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
      (Subgroup.normalizer (Z2 L1 L2 S : Set G)) =
      Subgroup.normalizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G) := by
    simpa [CFSG.conjugate] using
      (Subgroup.map_equiv_normalizer_eq (Z2 L1 L2 S) (MulAut.conj g⁻¹))
  have hNconjS : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
      (Subgroup.normalizer (S : Set G)) =
      Subgroup.normalizer (CFSG.conjugate S g : Set G) := by
    simpa [CFSG.conjugate] using
      (Subgroup.map_equiv_normalizer_eq (S : Subgroup G) (MulAut.conj g⁻¹))
  have hHconjMap : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (L1 ⊔ S) = L1 ⊔ S := by
    simpa [CFSG.conjugate] using hHconj
  have hconjB3 : CFSG.conjugate ((L1 ⊔ S) ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G)) g =
      CFSG.conjugate ((L1 ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) g :=
    congrArg (fun X => CFSG.conjugate X g) hB3
  have hHinfZ2 : (L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G) =
      (L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate S g : Set G) := by
    rw [CFSG.conjugate, Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective] at hconjB3
    rw [CFSG.conjugate, Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective] at hconjB3
    rw [hNconjZ2, hNconjS, hHconjMap] at hconjB3
    exact hconjB3
  have hSylH : IsSylowTwoOf S (L1 ⊔ S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF) le_sup_right
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
  have hSylSg : IsSylowTwoOf (CFSG.conjugate S g) (L1 ⊔ S) := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hSylH g⁻¹
    rw [CFSG.Quasithin.F7.conjSub_eq_of_mem_normalizer
      (Subgroup.le_normalizer ((L1 ⊔ S).inv_mem hg))] at h
    simpa [CFSG.conjugate, CFSG.Quasithin.conjSub] using h
  have hSgH : CFSG.conjugate S g ≤ L1 ⊔ S := by
    calc CFSG.conjugate S g ≤ CFSG.conjugate (L1 ⊔ S) g :=
          Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSleH
      _ = L1 ⊔ S := hHconj
  have hSgN : CFSG.conjugate S g ≤ Subgroup.normalizer (CFSG.conjugate S g : Set G) :=
    Subgroup.le_normalizer
  have hSylN : IsSylowTwoOf (CFSG.conjugate S g)
      ((L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate S g : Set G)) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right hSylSg (le_inf hSgH hSgN) inf_le_left
  have hNnormal : ((CFSG.conjugate S g).subgroupOf
      ((L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate S g : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hSgH hSgN)).mpr inf_le_right
  have hK2 : IsPGroup 2 ↥(S ⊓ ((L1 ⊔ S) ⊓
      Subgroup.normalizer (CFSG.conjugate S g : Set G))) :=
    (f112_isSylowTwoOf_P1 hF).2.1.to_le
      (inf_le_left : S ⊓ ((L1 ⊔ S) ⊓
        Subgroup.normalizer (CFSG.conjugate S g : Set G)) ≤ S)
  have hSinfN : S ⊓ ((L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate S g : Set G)) =
      S ⊓ CFSG.conjugate S g := by
    apply le_antisymm
    · exact le_inf inf_le_left
        (CFSG.Quasithin.F7.le_of_normal_sylow hSylN hNnormal inf_le_right hK2)
    · exact le_inf inf_le_left
        (le_inf (inf_le_right.trans hSgH) (inf_le_right.trans hSgN))
  calc S ⊓ Subgroup.normalizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)
      = S ⊓ ((L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) := by
        rw [← inf_assoc, inf_eq_left.mpr hSleH]
    _ = S ⊓ ((L1 ⊔ S) ⊓ Subgroup.normalizer (CFSG.conjugate S g : Set G)) := by
        rw [hHinfZ2]
    _ = S ⊓ CFSG.conjugate S g := hSinfN
    _ = Q1 L1 L2 S := hB4


end CFSG.Quasithin.Stroth

end
