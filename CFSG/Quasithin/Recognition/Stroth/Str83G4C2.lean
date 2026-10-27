module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_relIndex_q1_s
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    (Q1 L1 L2 S).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
  have hQ1S := str83G4_q1_le_s hfr
  obtain ⟨hF, hB, ha, ⟨e⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨e⟩⟩)
  let Q : Subgroup G := Q1 L1 L2 S
  let P : Subgroup G := P1 L1 L2 S
  let S1 : Subgroup G := S ⊓ L1
  change Q.relIndex S = (2 ^ (2 * a + 1)) ^ 2
  have hS1P : S1 ≤ P := (inf_le_right : S ⊓ L1 ≤ L1).trans le_sup_left
  have hS1N : S1 ≤ Subgroup.normalizer (Q : Set G) :=
    hS1P.trans (le_normalizer_pCoreOf 2 P)
  have hsup : S1 ⊔ Q = S := hS1.symm
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    have h := CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
      (A := S1) (B := Q) hS1N
    rwa [hsup] at h
  rw [hrel]
  rw [← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L1 := by
    have h1 : Q ⊓ S1 = L1 ⊓ Q := by
      change Q ⊓ (S ⊓ L1) = L1 ⊓ Q
      rw [inf_comm Q (S ⊓ L1), inf_assoc,
        inf_eq_right.mpr (show L1 ⊓ Q ≤ S from inf_le_right.trans hQ1S)]
    rw [h1]
    exact str86_inf_p1_q1 (L1 := L1) (L2 := L2) (S := S) hF
  rw [hinf]
  exact relIndex_pCoreOf_sylow_sz ha e hF.1.h1.sylow

theorem str83G4_q1_inf_conjugate_q1_le_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    Q1 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w ≤ Q2 L1 L2 S := by
  intro x hx
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hS : S ⊓ CFSG.conjugate S d.w = Q2 L1 L2 S :=
    str83G4_inf_conjugate_eq_q2 hfr d.hwH2 d.hwNotN
  rw [← hS]
  refine ⟨hQ1S hx.1, ?_⟩
  have hxw : x ∈ CFSG.conjugate (Q1 L1 L2 S) d.w := hx.2
  rw [CFSG.mem_conjugate_iff] at hxw
  exact (CFSG.mem_conjugate_iff S d.w x).mpr (hQ1S hxw)

theorem relIndex_centralizer_le_of_le_centralizer [Finite G] {X Y : Subgroup G} {d : G}
    (hdX : d ∈ Subgroup.normalizer (X : Set G))
    (hY : ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ ∈ Y)
    (hYX : Y ≤ Subgroup.centralizer (X : Set G)) :
    (Subgroup.centralizer ({d} : Set G)).relIndex X ≤ Nat.card Y := by
  classical
  let f : ↥X → ↥Y := fun x => ⟨(x : G) * d * (x : G)⁻¹ * d⁻¹, hY x x.2⟩
  have hf_mul : ∀ x y : ↥X, f (x * y) = f y * f x := by
    intro x y
    apply Subtype.ext
    have e1 : ((x : G) * (y : G)) * d * ((x : G) * (y : G))⁻¹ * d⁻¹ =
        (x : G) * ((y : G) * d * (y : G)⁻¹ * d⁻¹) * (x : G)⁻¹ *
          ((x : G) * d * (x : G)⁻¹ * d⁻¹) := by group
    have hcomm : (x : G) * ((y : G) * d * (y : G)⁻¹ * d⁻¹) * (x : G)⁻¹ =
        (y : G) * d * (y : G)⁻¹ * d⁻¹ := by
      have hmem := Subgroup.mem_centralizer_iff.mp (hYX (hY y y.2)) (x : G) x.2
      rw [hmem, mul_assoc, mul_inv_cancel, mul_one]
    simp only [f, Subgroup.coe_mul]
    rw [e1, hcomm]
  let φ : ↥X →* ↥Y :=
    { toFun := fun x => f x⁻¹
      map_one' := by
        apply Subtype.ext
        simp [f]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (f ((x * y)⁻¹) : G) = (((f x⁻¹ : ↥Y) * (f y⁻¹ : ↥Y) : ↥Y) : G)
        rw [mul_inv_rev, hf_mul] }
  have hker : φ.ker = (Subgroup.centralizer ({d} : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ((φ x : ↥Y) : G) = 1 := by
        have := congrArg (fun y : ↥Y => (y : G)) h
        simpa using this
      have h1' : ((f x⁻¹ : ↥Y) : G) = 1 := h1
      simp only [f, Subgroup.coe_one] at h1'
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have h4 : (x : G)⁻¹ * d * (x : G) * d⁻¹ = 1 := by simpa using h1'
      have h2 : (x : G)⁻¹ * d * (x : G) = d := by
        calc (x : G)⁻¹ * d * (x : G)
            = ((x : G)⁻¹ * d * (x : G)) * d⁻¹ * d := by group
          _ = 1 * d := by rw [h4]
          _ = d := by group
      calc d * (x : G) = (x : G) * ((x : G)⁻¹ * d * (x : G)) := by group
        _ = (x : G) * d := by rw [h2]
    · intro hx
      have h2 : d * (x : G) = (x : G) * d :=
        Subgroup.mem_centralizer_iff.mp hx d (Set.mem_singleton d)
      have h3 : (x : G)⁻¹ * d * (x : G) = d := by
        calc (x : G)⁻¹ * d * (x : G) = (x : G)⁻¹ * (d * (x : G)) := by group
          _ = (x : G)⁻¹ * ((x : G) * d) := by rw [h2]
          _ = d := by group
      have hφx : φ x = f x⁻¹ := rfl
      rw [hφx]
      apply Subtype.ext
      simp only [f, Subgroup.coe_one, Subgroup.coe_inv, inv_inv]
      rw [h3, mul_inv_cancel]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  calc Nat.card φ.range ≤ Nat.card (⊤ : Subgroup ↥Y) :=
        Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
    _ = Nat.card ↥Y := by simp
    _ = Nat.card Y := rfl

theorem str83G4_relIndex_a0_inf_conjugate_q1_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    ((Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex
      (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
  classical
  set A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hA0
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set W : Subgroup G := CFSG.conjugate S d.w with hW
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hA0W : A0 ≤ W := by
    have h1 : A0 ≤ CFSG.conjugate (Q2 L1 L2 S) d.w := by
      rw [str83G4_conjugate_q2_eq d]
      exact inf_le_right
    exact h1.trans (Subgroup.map_mono hQ2S)
  have h1 : (A0 ⊓ V).relIndex A0 = V.relIndex A0 :=
    Subgroup.inf_relIndex_left (H := A0) (K := V)
  have h2 : V.relIndex A0 ≤ V.relIndex W :=
    Subgroup.relIndex_le_of_le_right hA0W (Subgroup.index_ne_zero_of_finite)
  have h3 : V.relIndex W = (Q1 L1 L2 S).relIndex S := by
    rw [hV, hW]
    exact Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹) (Q1 L1 L2 S) S
  rw [hA0]
  calc (A0 ⊓ V).relIndex A0 = V.relIndex A0 := h1
    _ ≤ V.relIndex W := h2
    _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [h3, str83G4_relIndex_q1_s hfr]

theorem str83G4_relIndex_q1_inf_conjugate_q1_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    (Q1 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex (Q1 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 3 := by
  classical
  set A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hA0
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hE : Q1 L1 L2 S ⊓ V = A0 ⊓ V := by
    ext x
    constructor
    · rintro ⟨hxQ1, hxV⟩
      exact ⟨⟨hxQ1, str83G4_q1_inf_conjugate_q1_le_q2 hfr d ⟨hxQ1, hxV⟩⟩, hxV⟩
    · rintro ⟨⟨hxQ1, -⟩, hxV⟩
      exact ⟨hxQ1, hxV⟩
  have hA0Q1 : A0 ≤ Q1 L1 L2 S := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (H := A0 ⊓ V) (K := A0)
    (L := Q1 L1 L2 S) inf_le_left hA0Q1
  have ha0 : A0.relIndex (Q1 L1 L2 S) = q := by
    have h := str83G4_relIndex_q1_conjugate_q2 hfr (g := 1) (L1 ⊔ S).one_mem
    simpa [hA0, hq] using h
  calc (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) = (A0 ⊓ V).relIndex (Q1 L1 L2 S) := by
        rw [hE]
    _ = (A0 ⊓ V).relIndex A0 * A0.relIndex (Q1 L1 L2 S) := hmul.symm
    _ ≤ q ^ 2 * q := Nat.mul_le_mul (str83G4_relIndex_a0_inf_conjugate_q1_le hfr d)
        (le_of_eq ha0)
    _ = q ^ 3 := by ring

private theorem str83G4_relIndex_centralizer_q1_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S) ≤ (2 ^ (2 * a + 1)) ^ 4 := by
  classical
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w with hW
  set E : Subgroup G := Q1 L1 L2 S ⊓ V with hE
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hWleS : W ≤ S := by
    rw [hW]
    exact str83G4_conjugate_x_le_s hfr d hX
  have htP1 : t ∈ P1 L1 L2 S :=
    (sup_left_le_p1 L1 L2 S) ((le_sup_right : S ≤ L1 ⊔ S) (hWleS ht))
  have htNQ1 : t ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S) htP1
  have hconjN : CFSG.conjugate (P1 L1 L2 S) d.w ≤
      Subgroup.normalizer (V : Set G) := by
    calc CFSG.conjugate (P1 L1 L2 S) d.w
        ≤ CFSG.conjugate (Subgroup.normalizer (Q1 L1 L2 S : Set G)) d.w :=
          Subgroup.map_mono (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
      _ = Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
          simpa [CFSG.conjugate] using
            (Subgroup.map_equiv_normalizer_eq (Q1 L1 L2 S) (MulAut.conj d.w⁻¹))
  have hXleP1 : str83X L1 L2 S ≤ P1 L1 L2 S :=
    hXQ1.trans (hQ1S.trans ((le_sup_right : S ≤ L1 ⊔ S).trans (sup_left_le_p1 L1 L2 S)))
  have htNV : t ∈ Subgroup.normalizer (V : Set G) :=
    hconjN (Subgroup.map_mono hXleP1 ht)
  have htNE : t ∈ Subgroup.normalizer (E : Set G) :=
    A4.mem_normalizer_inf htNQ1 htNV
  have hZ1wcomm : ⁅V, W⁆ ≤ CFSG.conjugate (Z1 L1 L2 S) d.w := by
    have hbase : ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ ≤ Z1 L1 L2 S := by
      rw [Subgroup.commutator_comm]
      exact str83G4_commutator_x_q1_le hfr
    calc ⁅V, W⁆ = CFSG.conjugate ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ d.w := by
          simp only [CFSG.conjugate, hV, hW]
          exact (Subgroup.map_commutator _ _ _).symm
      _ ≤ CFSG.conjugate (Z1 L1 L2 S) d.w := Subgroup.map_mono hbase
  have hcommE : ∀ x ∈ E, x * t * x⁻¹ * t⁻¹ ∈ CFSG.conjugate (Z1 L1 L2 S) d.w := by
    intro x hx
    have hmem := Subgroup.commutator_le.mp hZ1wcomm x hx.2 t ht
    simpa [commutatorElement_def] using hmem
  have hQ1Z1 : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hZ1Q1 : Z1 L1 L2 S ≤ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQ1Z1 hy) z hz).symm
  have hZ1V : CFSG.conjugate (Z1 L1 L2 S) d.w ≤
      Subgroup.centralizer (V : Set G) := by
    have h := CFSG.GorensteinWalter.centralizer_map_le_of_hom (MulAut.conj d.w⁻¹).toMonoidHom
      (Q1 L1 L2 S) (Z1 L1 L2 S) hZ1Q1
    simpa [hV, CFSG.conjugate] using h
  have hZE : CFSG.conjugate (Z1 L1 L2 S) d.w ≤ Subgroup.centralizer (E : Set G) :=
    hZ1V.trans (Subgroup.centralizer_le inf_le_right)
  have hEbound : (Subgroup.centralizer ({t} : Set G)).relIndex E ≤ q := by
    have h := relIndex_centralizer_le_of_le_centralizer (X := E)
      (Y := CFSG.conjugate (Z1 L1 L2 S) d.w) (d := t) htNE hcommE hZE
    have hcard : Nat.card ↥(CFSG.conjugate (Z1 L1 L2 S) d.w) = q := by
      rw [hq]
      have hcard_conj : Nat.card ↥(CFSG.conjugate (Z1 L1 L2 S) d.w) =
          Nat.card ↥(Z1 L1 L2 S) := by
        simpa [CFSG.conjugate] using
          Subgroup.card_map_of_injective (K := Z1 L1 L2 S)
            (f := (MulAut.conj d.w⁻¹).toMonoidHom) (MulAut.conj d.w⁻¹).injective
      rw [hcard_conj]
      exact str83G4Z1Card_holds G L1 L2 S a hfr
    exact h.trans (le_of_eq hcard)
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hErel : E.relIndex (Q1 L1 L2 S) ≤ q ^ 3 := by
    rw [hE]
    exact str83G4_relIndex_q1_inf_conjugate_q1_le hfr d
  have hmono : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S) ≤ (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Q1 L1 L2 S) := by
    rw [hcent]
    exact Subgroup.relIndex_le_of_le_left (L := Q1 L1 L2 S) inf_le_right
      (Subgroup.index_ne_zero_of_finite)
  have hmul := Subgroup.relIndex_mul_relIndex (H := E ⊓ Subgroup.centralizer ({t} : Set G))
    (K := E) (L := Q1 L1 L2 S) inf_le_left (by rw [hE]; exact inf_le_left)
  have hCE : (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E ≤ q := by
    have h1 : (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E =
        (Subgroup.centralizer ({t} : Set G)).relIndex E :=
      Subgroup.inf_relIndex_left (H := E) (K := Subgroup.centralizer ({t} : Set G))
    rw [h1]
    exact hEbound
  calc (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (Q1 L1 L2 S)
      ≤ (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Q1 L1 L2 S) := hmono
    _ = (E ⊓ Subgroup.centralizer ({t} : Set G)).relIndex E * E.relIndex (Q1 L1 L2 S) :=
          hmul.symm
    _ ≤ q * q ^ 3 := Nat.mul_le_mul hCE hErel
    _ = q ^ 4 := by ring

private theorem str83G4_sup_left_eq_sup_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, ⟨e⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨e⟩⟩)
  have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := congrArg (fun X => L1 ⊔ X) hS1
  rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]

private theorem str83G4_isNormalIn_q1_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (Q1 L1 L2 S) := by
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  refine ⟨le_rfl, fun g hg x hx => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hHleP1 hg)) x).mp hx

theorem str83G4_isNormalIn_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) := by
  have hYQ1 : str83Y L1 L2 S ≤ Q1 L1 L2 S := inf_le_left
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  refine ⟨hYQ1, fun g hg x hx => ?_⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (sup_left_le_p1 L1 L2 S hg)) x).mp hx.1, ?_⟩
  have hc := F7.normalizer_le_normalizer_centralizer (str83X L1 L2 S) (hHN hg)
  exact (Subgroup.mem_normalizer_iff.mp hc x).mp hx.2

private theorem str83G4_commutator_x_oTwo_le_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hY : twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83Y L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S)) :
    ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ Z1 L1 L2 S := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set Z1s : Subgroup G := Z1 L1 L2 S with hZ1def
  set Ys : Subgroup G := str83Y L1 L2 S with hYdef
  have hQH : Q ≤ H := by rw [hQ, hH]; exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hYsQ : Ys ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  have hYsX : Ys ≤ Subgroup.centralizer (X : Set G) := by
    rw [hYdef, hXdef]; exact inf_le_right
  have hQZ1 : Q ≤ Subgroup.centralizer (Z1s : Set G) := by
    rw [hQ, hZ1def]
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hZ1Q : Z1s ≤ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQZ1 hy) z hz).symm
  have hZ1CX : Z1s ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    have hz' : z ∈ Z1 L1 L2 S := by rwa [hZ1def] at hz
    have h := (str83G4_z1_le_center_x hfr hz').2
    show z ∈ Subgroup.centralizer (X : Set G)
    rwa [← hXdef] at h
  have hXCZ1 : X ≤ Subgroup.centralizer (Z1s : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZ1CX hz) v hv).symm
  have hHNX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hH, hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hHZ1 : H ≤ Subgroup.centralizer (Z1s : Set G) := by
    rw [hH, hZ1def, str83G4_sup_left_eq_sup_q1 hfr]
    exact hfr.2.2.2.2.2
  have hHNY : H ≤ Subgroup.normalizer (Ys : Set G) := by
    rw [hH, hYdef]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (str83G4_isNormalIn_y hfr).2 g hg y hy
    · intro hy
      have h1 := (str83G4_isNormalIn_y hfr).2 g⁻¹ (H.inv_mem hg) (g * y * g⁻¹) hy
      simpa [mul_assoc] using h1
  refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
  rw [← F6.twoResidual_eq_oTwoUpper] at hg
  have hgH : g ∈ H := twoResidual_le H hg
  have hgNX : g ∈ Subgroup.normalizer (X : Set G) := hHNX hgH
  have hgZ1 : g ∈ Subgroup.centralizer (Z1s : Set G) := hHZ1 hgH
  have hxgX : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgNX x).mp hx
  have huX : g * x * g⁻¹ * x⁻¹ ∈ X := X.mul_mem hxgX (X.inv_mem hx)
  have hu2 : (g * x * g⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) = 1 := by
    have h := (B6.isElemAbelian_iff.mp hX).2 _ huX
    simpa [pow_two] using h
  have huCent : ∀ y ∈ Q, y * (g * x * g⁻¹ * x⁻¹) = (g * x * g⁻¹ * x⁻¹) * y := by
    intro y hy
    have hxyZ : x * y * x⁻¹ * y⁻¹ ∈ Z1s :=
      str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hy)
    have hgfix : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp hgZ1 _ hxyZ
      rw [← h]
      group
    have hcY : g * y * g⁻¹ * y⁻¹ ∈ Ys := (hY hg).2.2 y hy
    have hcX : (g * x * g⁻¹) * (g * y * g⁻¹ * y⁻¹) =
        (g * y * g⁻¹ * y⁻¹) * (g * x * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hYsX hcY) (g * x * g⁻¹) hxgX
    have hcZ : (g * y * g⁻¹ * y⁻¹) * ⁅g * x * g⁻¹, y⁆ *
        (g * y * g⁻¹ * y⁻¹)⁻¹ = ⁅g * x * g⁻¹, y⁆ := by
      have hmem : ⁅g * x * g⁻¹, y⁆ ∈ Z1s :=
        str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hxgX hy)
      have h := Subgroup.mem_centralizer_iff.mp (hQZ1 (hYsQ hcY)) _ hmem
      rw [← h]
      group
    have h1 : (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ *
        (g * y * g⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      rw [← hgfix]
      group
    have h2 : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    have h3 : (g * x * g⁻¹) * ((g * y * g⁻¹ * y⁻¹) * y) * (g * x * g⁻¹)⁻¹ *
        ((g * y * g⁻¹ * y⁻¹) * y)⁻¹ =
        (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ := by
      change ⁅g * x * g⁻¹, (g * y * g⁻¹ * y⁻¹) * y⁆ = ⁅g * x * g⁻¹, y⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc1 : ⁅g * x * g⁻¹, g * y * g⁻¹ * y⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hcX
      rw [hc1, one_mul]
      exact hcZ
    have heq : (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
        x * y * x⁻¹ * y⁻¹ := by
      rw [← h3, ← h2]
      exact h1
    have hu : g * x * g⁻¹ * x⁻¹ = (g * x * g⁻¹) * x⁻¹ := by group
    have hux : (g * x * g⁻¹ * x⁻¹) * x = g * x * g⁻¹ := by group
    have hconj0 : (g * x * g⁻¹ * x⁻¹) * (x * y * x⁻¹ * y⁻¹) *
        (g * x * g⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp (hXCZ1 huX) _ hxyZ
      rw [← h]
      group
    have hconj : (g * x * g⁻¹ * x⁻¹) * ⁅x, y⁆ * (g * x * g⁻¹ * x⁻¹)⁻¹ = ⁅x, y⁆ := by
      simpa [commutatorElement_def] using hconj0
    have hmul := commutatorElement_mul_left_eq_conj_mul
      (a := g * x * g⁻¹ * x⁻¹) (b := x) (c := y)
    rw [hux, hconj] at hmul
    have heq' : ⁅g * x * g⁻¹, y⁆ = ⁅x, y⁆ := by
      simpa [commutatorElement_def] using heq
    rw [heq'] at hmul
    have huy : ⁅g * x * g⁻¹ * x⁻¹, y⁆ = 1 := by
      have h1 := congrArg (fun t => ⁅x, y⁆⁻¹ * t) hmul
      simpa [mul_assoc] using h1.symm
    exact ((commutatorElement_eq_one_iff_mul_comm).mp huy).symm
  have huMemZ : g * x * g⁻¹ * x⁻¹ ∈ Z1s := by
    have huCentQ : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact huCent
    have huCenter : g * x * g⁻¹ * x⁻¹ ∈ centerOf Q :=
      ⟨hXQ huX, huCentQ⟩
    exact Subgroup.subset_closure ⟨huCenter, by simpa [pow_two] using hu2⟩
  have hcomm : ⁅x, g⁆ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  exact Z1s.inv_mem huMemZ

private theorem exists_noncentral_step_of_isChiefSeriesBetween {H U W N : Subgroup G} {a : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W N a) (ha : a ≠ 0) :
    ∃ L N' : Subgroup G, IsChiefStep H U L N' ∧ W ≤ L ∧ ¬ IsCentralStep H L N' := by
  induction h with
  | refl => exact absurd rfl ha
  | @central N L n hstep hc hs ih => exact ih ha
  | @noncentral N L n hstep hnc hs ih =>
    by_cases hn : n = 0
    · exact ⟨L, N, hstep, hs.le, hnc⟩
    · exact ih hn

private theorem str83G4_exists_chiefStep_above_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ∃ L N : Subgroup G, IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) L N ∧
      str83Y L1 L2 S ≤ L ∧ ¬ IsCentralStep (L1 ⊔ S) L N := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set Ys : Subgroup G := str83Y L1 L2 S with hYdef
  have hQH : Q ≤ H := by
    rw [hQ, hH]
    exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hQcore : Q ≤ pCoreOf 2 H := by
    rw [hH, hQ, str83G4_pCoreOf_sup_left hfr]
  have hYnormal : IsNormalIn H Q Ys := by
    rw [hH, hQ, hYdef]
    exact str83G4_isNormalIn_y hfr
  have hQnormal : IsNormalIn H Q Q := by
    rw [hH, hQ]
    exact str83G4_isNormalIn_q1_q1 hfr
  have hYQ : Ys ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween hYnormal Q hQnormal hYQ
  by_cases hc0 : c = 0
  · have hcomm : ⁅Q, oTwoUpper H⁆ ≤ Ys :=
      (F112W.isChiefSeriesBetween_zero_iff hQH hQcore hYnormal hQnormal hYQ).mp
        (hc0 ▸ hser)
    have hYmem : twoResidual H ≤ centralizerMod Ys H Q := by
      intro g hg
      have hgO : g ∈ oTwoUpper H := by rwa [F6.twoResidual_eq_oTwoUpper] at hg
      refine ⟨twoResidual_le H hg,
        D14.le_normalizer_of_isNormalIn hYnormal (twoResidual_le H hg), fun u hu => ?_⟩
      have hmem : ⁅u, g⁆ ∈ Ys := Subgroup.commutator_le.mp hcomm u hu g hgO
      have e : g * u * g⁻¹ * u⁻¹ = ⁅u, g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Ys.inv_mem hmem
    have hXZ : ⁅str83X L1 L2 S, oTwoUpper H⁆ ≤ Z1 L1 L2 S :=
      str83G4_commutator_x_oTwo_le_z1 hfr d hX hYmem
    obtain ⟨L, N, hstep, hZ1L, hnc⟩ := str83G4_exists_chiefStep hfr
    exact absurd (show twoResidual H ≤ centralizerMod L H N from by
      intro g hg
      refine ⟨twoResidual_le H hg,
        D14.le_normalizer_of_isNormalIn hstep.2.1 (twoResidual_le H hg), fun n hn => ?_⟩
      have hmem : ⁅n, g⁆ ∈ ⁅str83X L1 L2 S, oTwoUpper H⁆ :=
        Subgroup.commutator_mem_commutator (hstep.1.1 hn)
          (by rwa [← F6.twoResidual_eq_oTwoUpper])
      have hmemZ : ⁅n, g⁆ ∈ Z1 L1 L2 S := hXZ hmem
      have e : g * n * g⁻¹ * n⁻¹ = ⁅n, g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hZ1L ((Z1 L1 L2 S).inv_mem hmemZ)) hnc
  · obtain ⟨L, N, hstep, hYL, hnc⟩ := exists_noncentral_step_of_isChiefSeriesBetween hser hc0
    exact ⟨L, N, hstep, hYL, hnc⟩

theorem str83G4_relIndex_centralizerMod_y_q1_ge
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (2 ^ (2 * a + 1)) ^ 2 ≤
      (centralizerMod (str83Y L1 L2 S) (Q1 L1 L2 S)
        (Subgroup.zpowers t)).relIndex (Q1 L1 L2 S) := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set Ys : Subgroup G := str83Y L1 L2 S with hYdef
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  obtain ⟨L, N, hstep, hYL, hnc⟩ := str83G4_exists_chiefStep_above_y hfr d hX
  have hQH : Q ≤ H := by
    rw [hQ, hH]
    exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hpCore : pCoreOf 2 H = Q := by
    rw [hH, hQ]
    exact str83G4_pCoreOf_sup_left hfr
  have hWleS : CFSG.conjugate (str83X L1 L2 S) d.w ≤ S :=
    str83G4_conjugate_x_le_s hfr d hX
  have hWabel : IsElemAbelian 2 (CFSG.conjugate (str83X L1 L2 S) d.w) :=
    str83G4_isElemAbelian_conjugate_x d hX
  have ht2 : t * t = 1 := by
    have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
    simpa [pow_two] using h
  have htH : t ∈ H := by
    rw [hH]
    exact (le_sup_right : S ≤ L1 ⊔ S) (hWleS ht)
  have hM7 := sq_le_relIndex_centralizerMod (H := H) (U := Q) (L := L) (N := N) (q := q)
    (str83G4_isSzU3Quot_sup_left hfr)
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hQH hstep hnc htH
    (by rw [hpCore, ht2]; exact Q.one_mem)
    (by rw [hpCore]; exact htQ)
  have hle : centralizerMod Ys Q (Subgroup.zpowers t) ≤
      centralizerMod L Q (Subgroup.zpowers t) := by
    intro x hx
    refine ⟨hx.1, D14.le_normalizer_of_isNormalIn hstep.2.1 (hQH hx.1), ?_⟩
    intro u hu
    exact hYL (hx.2.2 u hu)
  have hmono1 : (centralizerMod L Q (Subgroup.zpowers t)).relIndex Q ≤
      (centralizerMod Ys Q (Subgroup.zpowers t)).relIndex Q :=
    Subgroup.relIndex_le_of_le_left (L := Q) hle (Subgroup.index_ne_zero_of_finite)
  have hDN : centralizerMod L Q (Subgroup.zpowers t) ⊓ N =
      centralizerMod L N (Subgroup.zpowers t) := by
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      exact ⟨hxN, hx.2.1, hx.2.2⟩
    · intro hx
      exact ⟨⟨hstep.1.1 hx.1, hx.2.1, hx.2.2⟩, hx.1⟩
  have hmono2 : (centralizerMod L N (Subgroup.zpowers t)).relIndex N ≤
      (centralizerMod L Q (Subgroup.zpowers t)).relIndex Q := by
    rw [← hDN, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right hstep.1.1 (Subgroup.index_ne_zero_of_finite)
  exact hM7.trans (hmono2.trans hmono1)

theorem str83G4_relIndex_centralizer_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4 := by
  classical
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set C : Subgroup G :=
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) with hC
  set P : Subgroup G := centralizerMod (str83Y L1 L2 S) Q (Subgroup.zpowers t) with hP
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hQH : Q ≤ L1 ⊔ S := by
    rw [hQ]
    exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hHNX : L1 ⊔ S ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hHNY : L1 ⊔ S ≤ Subgroup.normalizer (str83Y L1 L2 S : Set G) :=
    D14.le_normalizer_of_isNormalIn (str83G4_isNormalIn_y hfr)
  have hXleY : X ≤ str83Y L1 L2 S := str83X_le_str83Y hfr hX
  refine le_antisymm ?_ ?_
  · have h := str83G4_relIndex_centralizer_q1_le hfr d hX ht htQ
    rwa [hq, hC, hQ]
  · set C₀ : Subgroup G := C ⊓ Q with hC₀def
    have hC₀Q : C₀ ≤ Q := inf_le_right
    have hC₀C : C₀ ≤ C := inf_le_left
    have hC₀NX : C₀ ≤ Subgroup.normalizer (X : Set G) := hC₀Q.trans (hQH.trans hHNX)
    have hP : q ^ 2 ≤ P.relIndex Q := by
      have h := str83G4_relIndex_centralizerMod_y_q1_ge hfr d hX ht htQ
      rwa [hq, hP, hQ]
    have hC₀P : C₀ ≤ P := by
      intro x hx
      obtain ⟨hxC, hxQ⟩ := hx
      refine ⟨hxQ, hHNY (hQH hxQ), fun u hu => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hmem : t ^ k ∈ Subgroup.zpowers t :=
        Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
      have hcomm : x * t ^ k = t ^ k * x :=
        (Subgroup.mem_centralizer_iff.mp hxC (t ^ k) hmem).symm
      have e : x * t ^ k * x⁻¹ * (t ^ k)⁻¹ = 1 := by rw [hcomm]; group
      rw [e]
      exact (str83Y L1 L2 S).one_mem
    have hXP : X ≤ P := by
      intro x hx
      have hxY : x ∈ str83Y L1 L2 S := hXleY hx
      refine ⟨hxY.1, Subgroup.le_normalizer hxY, fun u hu => ?_⟩
      have htH : t ∈ L1 ⊔ S :=
        (le_sup_right : S ≤ L1 ⊔ S) (str83G4_conjugate_x_le_s hfr d hX ht)
      have huH : u ∈ L1 ⊔ S := Subgroup.zpowers_le.mpr htH hu
      have h1 : u * x⁻¹ * u⁻¹ ∈ str83Y L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hHNY huH) x⁻¹).mp
          ((str83Y L1 L2 S).inv_mem hxY)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]
      exact (str83Y L1 L2 S).mul_mem hxY h1
    have hC₀XP : C₀ ⊔ X ≤ P := sup_le hC₀P hXP
    have hmonoP : P.relIndex Q ≤ (C₀ ⊔ X).relIndex Q :=
      Subgroup.relIndex_le_of_le_left (L := Q) hC₀XP (Subgroup.index_ne_zero_of_finite)
    have hCX : C₀.relIndex (C₀ ⊔ X) = q ^ 2 := by
      have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := C₀) (K := X) hC₀NX).1
      have hEq : C₀ ⊓ X = C ⊓ X := by
        rw [hC₀def]
        ext y
        constructor
        · rintro ⟨⟨hyC, -⟩, hyX⟩
          exact ⟨hyC, hyX⟩
        · rintro ⟨hyC, hyX⟩
          exact ⟨⟨hyC, hXQ hyX⟩, hyX⟩
      have hCP : (C ⊓ X).relIndex X = q ^ 2 := by
        rw [Subgroup.inf_relIndex_right]
        have hc := str83G4_relIndex_centralizer_x hfr d hX ht htQ
        simpa only [hq, hC, hXdef, hQ] using hc
      rw [h, hEq]
      exact hCP
    have hC₀Q₂ : C₀ ⊔ X ≤ Q := sup_le hC₀Q hXQ
    have hmul := Subgroup.relIndex_mul_relIndex (H := C₀) (K := C₀ ⊔ X) (L := Q)
      le_sup_left hC₀Q₂
    calc q ^ 4 = q ^ 2 * q ^ 2 := by ring
      _ = C₀.relIndex (C₀ ⊔ X) * q ^ 2 := by rw [← hCX]
      _ ≤ C₀.relIndex (C₀ ⊔ X) * P.relIndex Q := Nat.mul_le_mul_left _ hP
      _ ≤ C₀.relIndex (C₀ ⊔ X) * (C₀ ⊔ X).relIndex Q :=
          Nat.mul_le_mul_left _ hmonoP
      _ = C₀.relIndex Q := hmul
      _ = C.relIndex Q := by rw [hC₀def, Subgroup.inf_relIndex_right]

end CFSG.Quasithin.Stroth

end
