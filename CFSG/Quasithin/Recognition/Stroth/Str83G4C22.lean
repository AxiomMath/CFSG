module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4C2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4NM
public import CFSG.Timmesfeld.Bridge.OddLocalQd

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_relIndex_inf_centralizer_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    ((Q1 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ≤ 2 ^ (2 * a + 1) := by
  classical
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w with hW
  set E : Subgroup G := Q1 L1 L2 S ⊓ V with hE
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
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
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
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
  rw [hcent]
  have h1 : ((E ⊓ Subgroup.centralizer ({t} : Set G))).relIndex E =
      (Subgroup.centralizer ({t} : Set G)).relIndex E :=
    Subgroup.inf_relIndex_left (H := E) (K := Subgroup.centralizer ({t} : Set G))
  rw [h1]
  exact hEbound

private theorem str83G4_c2_index_eq
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (Q1 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex (Q1 L1 L2 S) =
        (2 ^ (2 * a + 1)) ^ 3 ∧
      ((Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex
        (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  classical
  obtain ⟨t, ht, htQ⟩ : ∃ t : G, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w ∧
      t ∉ Q1 L1 L2 S := by
    by_contra h
    apply hB
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  set A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hA0
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hEeq : Q1 L1 L2 S ⊓ V = A0 ⊓ V := by
    ext x
    constructor
    · rintro ⟨hxQ1, hxV⟩
      exact ⟨⟨hxQ1, str83G4_q1_inf_conjugate_q1_le_q2 hfr d ⟨hxQ1, hxV⟩⟩, hxV⟩
    · rintro ⟨⟨hxQ1, -⟩, hxV⟩
      exact ⟨hxQ1, hxV⟩
  have hqpos : 0 < q := by rw [hq]; positivity
  have hupperE : (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) ≤ q ^ 3 := by
    rw [hq]
    exact str83G4_relIndex_q1_inf_conjugate_q1_le hfr d
  have hCrel : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S) = q ^ 4 := by
    rw [hq]
    exact str83G4_relIndex_centralizer_q1 hfr d hX ht htQ
  have hCE : ((Q1 L1 L2 S ⊓ V) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (Q1 L1 L2 S ⊓ V) ≤ q := by
    rw [hq]
    exact str83G4_relIndex_inf_centralizer_le hfr d hX ht htQ
  have hmono : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Q1 L1 L2 S) ≤ ((Q1 L1 L2 S ⊓ V) ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
          (Q1 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_left (L := Q1 L1 L2 S) inf_le_right
      (Subgroup.index_ne_zero_of_finite)
  have hmul := Subgroup.relIndex_mul_relIndex (H := (Q1 L1 L2 S ⊓ V) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))
    (K := Q1 L1 L2 S ⊓ V) (L := Q1 L1 L2 S) inf_le_left inf_le_left
  have hEq3 : (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) = q ^ 3 := by
    have hle : q ^ 4 ≤ q * (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := by
      calc q ^ 4 = (Subgroup.centralizer
            ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex (Q1 L1 L2 S) := hCrel.symm
        _ ≤ ((Q1 L1 L2 S ⊓ V) ⊓ Subgroup.centralizer
              ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex (Q1 L1 L2 S) := hmono
        _ = ((Q1 L1 L2 S ⊓ V) ⊓ Subgroup.centralizer
              ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex (Q1 L1 L2 S ⊓ V) *
              (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := hmul.symm
        _ ≤ q * (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) :=
            Nat.mul_le_mul hCE le_rfl
    have h1 : q ^ 3 ≤ (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := by
      have h2 : q * q ^ 3 ≤ q * (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := by
        calc q * q ^ 3 = q ^ 4 := by ring
          _ ≤ q * (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := hle
      exact Nat.le_of_mul_le_mul_left h2 hqpos
    exact le_antisymm hupperE h1
  have hA0rel : A0.relIndex (Q1 L1 L2 S) = q := by
    have h := str83G4_relIndex_q1_conjugate_q2 hfr (g := 1) (L1 ⊔ S).one_mem
    simpa [hA0, hq] using h
  have hmul2 := Subgroup.relIndex_mul_relIndex (H := A0 ⊓ V) (K := A0)
    (L := Q1 L1 L2 S) inf_le_left (inf_le_left : A0 ≤ Q1 L1 L2 S)
  have hEq2 : (A0 ⊓ V).relIndex A0 = q ^ 2 := by
    have hm : (A0 ⊓ V).relIndex A0 * q = q ^ 3 := by
      calc (A0 ⊓ V).relIndex A0 * q
          = (A0 ⊓ V).relIndex A0 * A0.relIndex (Q1 L1 L2 S) := by rw [hA0rel]
        _ = (A0 ⊓ V).relIndex (Q1 L1 L2 S) := hmul2
        _ = (Q1 L1 L2 S ⊓ V).relIndex (Q1 L1 L2 S) := by rw [hEeq]
        _ = q ^ 3 := hEq3
    apply Nat.eq_of_mul_eq_mul_right hqpos
    rw [hm]
    ring
  exact ⟨hEq3, hEq2⟩

theorem str83G4_a0_sup_conjugate_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ CFSG.conjugate (Q1 L1 L2 S) d.w =
      CFSG.conjugate S d.w := by
  classical
  set A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hA0
  set V : Subgroup G := CFSG.conjugate (Q1 L1 L2 S) d.w with hV
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hA0S : A0 ≤ CFSG.conjugate S d.w := by
    have h1 : A0 ≤ CFSG.conjugate (Q2 L1 L2 S) d.w := by
      rw [str83G4_conjugate_q2_eq d]
      exact inf_le_right
    exact h1.trans (Subgroup.map_mono hQ2S)
  have hVle : V ≤ CFSG.conjugate S d.w := by
    rw [hV]
    exact Subgroup.map_mono hQ1S
  have hAVle : A0 ⊔ V ≤ CFSG.conjugate S d.w := sup_le hA0S hVle
  have hA0P1w : A0 ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
    have h1 : A0 ≤ CFSG.conjugate (Q2 L1 L2 S) d.w := by
      rw [str83G4_conjugate_q2_eq d]
      exact inf_le_right
    have h2 : Q2 L1 L2 S ≤ P1 L1 L2 S :=
      (hQ2S.trans (le_sup_right : S ≤ bigB L1 L2 S)).trans le_sup_right
    exact h1.trans (Subgroup.map_mono h2)
  have hA0NV : A0 ≤ Subgroup.normalizer (V : Set G) := by
    have hconjN : CFSG.conjugate (P1 L1 L2 S) d.w ≤
        Subgroup.normalizer (V : Set G) := by
      calc CFSG.conjugate (P1 L1 L2 S) d.w
          ≤ CFSG.conjugate (Subgroup.normalizer (Q1 L1 L2 S : Set G)) d.w :=
            Subgroup.map_mono (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
        _ = Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
            simpa [CFSG.conjugate] using
              (Subgroup.map_equiv_normalizer_eq (Q1 L1 L2 S) (MulAut.conj d.w⁻¹))
    exact hA0P1w.trans hconjN
  have hrel1 : V.relIndex (A0 ⊔ V) = q ^ 2 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := A0) (K := V) hA0NV).2
    rw [h]
    have h2 := (str83G4_c2_index_eq hfr d hX hB).2
    rw [hA0, hV, hq]
    exact h2
  have hrel2 : V.relIndex (CFSG.conjugate S d.w) = q ^ 2 := by
    rw [hV, hq]
    calc (CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex (CFSG.conjugate S d.w)
        = (Q1 L1 L2 S).relIndex S :=
          Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹) (Q1 L1 L2 S) S
      _ = (2 ^ (2 * a + 1)) ^ 2 := str83G4_relIndex_q1_s hfr
  have hmul := Subgroup.relIndex_mul_relIndex (H := V) (K := A0 ⊔ V)
    (L := CFSG.conjugate S d.w) le_sup_right hAVle
  have hone : (A0 ⊔ V).relIndex (CFSG.conjugate S d.w) = 1 := by
    rw [hrel1, hrel2] at hmul
    exact Nat.eq_of_mul_eq_mul_left (show 0 < q ^ 2 by positivity) (by rw [hmul, mul_one])
  exact le_antisymm hAVle (Subgroup.relIndex_eq_one.mp hone)

theorem str83G4_q2_eq_a0_sup_conjugate_a0
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    Q2 L1 L2 S = (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔
      CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w := by
  classical
  set A0 : Subgroup G := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hA0
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hA0Q2 : A0 ≤ Q2 L1 L2 S := by rw [hA0]; exact inf_le_right
  have hA0Q1 : A0 ≤ Q1 L1 L2 S := by rw [hA0]; exact inf_le_left
  have hAw : CFSG.conjugate A0 d.w =
      CFSG.conjugate (Q1 L1 L2 S) d.w ⊓ Q2 L1 L2 S := by
    rw [hA0, CFSG.conjugate,
      Subgroup.map_inf _ _ _ (MulAut.conj d.w⁻¹).injective]
    rw [show (Q2 L1 L2 S).map (MulAut.conj d.w⁻¹).toMonoidHom = Q2 L1 L2 S from
      str83G4_conjugate_q2_eq d]
    rfl
  have hQ2Sw : Q2 L1 L2 S ≤ CFSG.conjugate S d.w := by
    calc Q2 L1 L2 S = CFSG.conjugate (Q2 L1 L2 S) d.w :=
          (str83G4_conjugate_q2_eq d).symm
      _ ≤ CFSG.conjugate S d.w := Subgroup.map_mono hQ2S
  have hA0Sw : A0 ≤ CFSG.conjugate S d.w := hA0Q2.trans hQ2Sw
  have hSwN : CFSG.conjugate S d.w ≤
      Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
    have hSN : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      ((le_sup_right : S ≤ L1 ⊔ S).trans (sup_left_le_p1 L1 L2 S)).trans
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    calc CFSG.conjugate S d.w
        ≤ CFSG.conjugate (Subgroup.normalizer (Q1 L1 L2 S : Set G)) d.w :=
          Subgroup.map_mono hSN
      _ = Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
          simpa [CFSG.conjugate] using
            (Subgroup.map_equiv_normalizer_eq (Q1 L1 L2 S) (MulAut.conj d.w⁻¹))
  have hA0NQ1w : A0 ≤
      Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) :=
    hA0Sw.trans hSwN
  have hBQ2 : A0 ⊔ CFSG.conjugate A0 d.w ≤ Q2 L1 L2 S :=
    sup_le hA0Q2 (by rw [hAw]; exact inf_le_right)
  have hQ2le : Q2 L1 L2 S ≤ A0 ⊔ CFSG.conjugate A0 d.w := by
    intro x hx
    have hxSw : x ∈ CFSG.conjugate S d.w := hQ2Sw hx
    have hxsup : x ∈ CFSG.conjugate (Q1 L1 L2 S) d.w ⊔ A0 := by
      have hS := str83G4_a0_sup_conjugate_q1 hfr d hX hB
      rw [← hS] at hxSw
      rw [sup_comm]
      exact hxSw
    obtain ⟨u, huV, b, hbA, hxeq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hA0NQ1w).mp hxsup
    rw [hxeq] at hx
    have huQ2 : u ∈ Q2 L1 L2 S := by
      have h1 : u * b * b⁻¹ ∈ Q2 L1 L2 S :=
        (Q2 L1 L2 S).mul_mem hx ((Q2 L1 L2 S).inv_mem (hA0Q2 hbA))
      simpa using h1
    have huAw : u ∈ CFSG.conjugate A0 d.w := by
      rw [hAw]
      exact ⟨huV, huQ2⟩
    have hmem : u * b ∈ CFSG.conjugate A0 d.w ⊔ A0 := Subgroup.mul_mem_sup huAw hbA
    rw [hxeq, sup_comm]
    exact hmem
  exact le_antisymm hQ2le hBQ2

private theorem str83G4_c2_y_counts
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (centralizerMod (str83Y L1 L2 S) (Q1 L1 L2 S) (Subgroup.zpowers t)).relIndex
        (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 ∧
      centralizerMod (str83Y L1 L2 S) (Q1 L1 L2 S) (Subgroup.zpowers t) =
        (Q1 L1 L2 S ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ⊔
          str83Y L1 L2 S ∧
      str83Y L1 L2 S = (str83Y L1 L2 S ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ⊔
          str83X L1 L2 S := by
  classical
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set Y : Subgroup G := str83Y L1 L2 S with hYdef
  set C : Subgroup G :=
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) with hC
  set P : Subgroup G := centralizerMod Y Q (Subgroup.zpowers t) with hP
  set C₀ : Subgroup G := C ⊓ Q with hC₀def
  set CY : Subgroup G := C ⊓ Y with hCYdef
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hYQ : Y ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  have hXY : X ≤ Y := by rw [hXdef, hYdef]; exact str83X_le_str83Y hfr hX
  have hQH : Q ≤ L1 ⊔ S := by
    rw [hQ]
    exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hHNX : L1 ⊔ S ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hHNY : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYdef]
    exact D14.le_normalizer_of_isNormalIn (str83G4_isNormalIn_y hfr)
  have hCQ : C₀ ≤ Q := inf_le_right
  have hCYN : CY ≤ Y := inf_le_right
  have hCYX : CY ≤ C := inf_le_left
  have hC₀NX : C₀ ≤ Subgroup.normalizer (X : Set G) := hCQ.trans (hQH.trans hHNX)
  have hC₀NY : C₀ ≤ Subgroup.normalizer (Y : Set G) := hCQ.trans (hQH.trans hHNY)
  have hCYNX : CY ≤ Subgroup.normalizer (X : Set G) := hCYN.trans (hYQ.trans (hQH.trans hHNX))
  have hCrel : C.relIndex Q = q ^ 4 := by
    rw [hq, hC, hQ]
    exact str83G4_relIndex_centralizer_q1 hfr d hX ht htQ
  have hC₀rel : C₀.relIndex Q = q ^ 4 := by
    rw [hC₀def, Subgroup.inf_relIndex_right]
    exact hCrel
  have hCP : (C ⊓ X).relIndex X = q ^ 2 := by
    rw [Subgroup.inf_relIndex_right]
    have hc := str83G4_relIndex_centralizer_x hfr d hX ht htQ
    simpa only [hq, hC, hXdef] using hc
  have hCXrel : C₀.relIndex (C₀ ⊔ X) = q ^ 2 := by
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
    rw [h, hEq]
    exact hCP
  have hCYXrel : CY.relIndex (CY ⊔ X) = q ^ 2 := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := CY) (K := X) hCYNX).1
    have hEq : CY ⊓ X = C ⊓ X := by
      rw [hCYdef]
      ext y
      constructor
      · rintro ⟨⟨hyC, -⟩, hyX⟩
        exact ⟨hyC, hyX⟩
      · rintro ⟨hyC, hyX⟩
        exact ⟨⟨hyC, hXY hyX⟩, hyX⟩
    rw [h, hEq]
    exact hCP
  have hCYrel : C₀.relIndex (C₀ ⊔ Y) = CY.relIndex Y := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := C₀) (K := Y) hC₀NY).1
    have hEq : C₀ ⊓ Y = CY := by
      rw [hC₀def, hCYdef]
      ext y
      constructor
      · rintro ⟨⟨hyC, -⟩, hyY⟩
        exact ⟨hyC, hyY⟩
      · rintro ⟨hyC, hyY⟩
        exact ⟨⟨hyC, hYQ hyY⟩, hyY⟩
    rw [h, hEq]
  have hCYmul := Subgroup.relIndex_mul_relIndex (H := CY) (K := CY ⊔ X) (L := Y)
    le_sup_left (sup_le hCYN hXY)
  have hCYeq : CY.relIndex Y = q ^ 2 * (CY ⊔ X).relIndex Y := by
    rw [hCYXrel] at hCYmul
    rw [← hCYmul]
  have hPge : q ^ 2 ≤ P.relIndex Q := by
    rw [hq, hP, hQ]
    exact str83G4_relIndex_centralizerMod_y_q1_ge hfr d hX ht htQ
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
    exact Y.one_mem
  have hYP : Y ≤ P := by
    intro x hx
    have htH : t ∈ L1 ⊔ S :=
      (le_sup_right : S ≤ L1 ⊔ S) (str83G4_conjugate_x_le_s hfr d hX ht)
    refine ⟨hYQ hx, hHNY (hQH (hYQ hx)), fun u hu => ?_⟩
    have huH : u ∈ L1 ⊔ S := Subgroup.zpowers_le.mpr htH hu
    have h1 : u * x⁻¹ * u⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hHNY huH) x⁻¹).mp (Y.inv_mem hx)
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact Y.mul_mem hx h1
  have hC₀YP : C₀ ⊔ Y ≤ P := sup_le hC₀P hYP
  have hmul := Subgroup.relIndex_mul_relIndex (H := C₀) (K := C₀ ⊔ Y) (L := Q)
    le_sup_left (sup_le hCQ hYQ)
  have hPmono : P.relIndex Q ≤ (C₀ ⊔ Y).relIndex Q :=
    Subgroup.relIndex_le_of_le_left (L := Q) hC₀YP (Subgroup.index_ne_zero_of_finite)
  have hq4 : q ^ 4 = (q ^ 2 * (CY ⊔ X).relIndex Y) * (C₀ ⊔ Y).relIndex Q := by
    rw [← hC₀rel, ← hmul, hCYrel, hCYeq]
  have hRge : q ^ 2 ≤ (C₀ ⊔ Y).relIndex Q := hPge.trans hPmono
  have hW1 : (CY ⊔ X).relIndex Y = 1 := by
    have hle : q ^ 4 * (CY ⊔ X).relIndex Y ≤ q ^ 4 := by
      calc q ^ 4 * (CY ⊔ X).relIndex Y
          = (q ^ 2 * (CY ⊔ X).relIndex Y) * q ^ 2 := by ring
        _ ≤ (q ^ 2 * (CY ⊔ X).relIndex Y) * (C₀ ⊔ Y).relIndex Q :=
            Nat.mul_le_mul_left _ hRge
        _ = q ^ 4 := hq4.symm
    have hq4pos : 0 < q ^ 4 := by positivity
    have hle' : q ^ 4 * (CY ⊔ X).relIndex Y ≤ q ^ 4 * 1 := by simpa using hle
    refine le_antisymm (Nat.le_of_mul_le_mul_left hle' hq4pos) ?_
    refine Nat.one_le_iff_ne_zero.mpr ?_
    intro h0
    have hcard := Subgroup.relIndex_mul_card (H := CY ⊔ X) (K := Y)
    rw [h0, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  have hR : (C₀ ⊔ Y).relIndex Q = q ^ 2 := by
    rw [hW1, mul_one] at hq4
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q ^ 2) ?_
    rw [← hq4]
    ring
  have hPreq : P.relIndex Q = q ^ 2 := le_antisymm (hR ▸ hPmono) hPge
  have hPeq : P = C₀ ⊔ Y := by
    refine (CFSG.Quasithin.Ch3y.eq_of_le_of_relIndex_le
      (K₁ := C₀ ⊔ Y) (K₂ := P) (A := Q) hC₀YP
      (centralizerMod_le_left Y Q (Subgroup.zpowers t)) ?_).symm
    rw [hR, hPreq]
  have hYeq : Y = CY ⊔ X := by
    refine le_antisymm (Subgroup.relIndex_eq_one.mp hW1) (sup_le hCYN hXY)
  refine ⟨?_, ?_, ?_⟩
  · rw [hPreq, hq]
  · rw [hPeq, hC₀def, inf_comm C Q]
  · calc Y = CY ⊔ X := hYeq
      _ = (Y ⊓ C) ⊔ X := by rw [hCYdef, inf_comm]

theorem str83G4_y_eq_centralizer_sup_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    str83Y L1 L2 S =
      (str83Y L1 L2 S ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ⊔
        str83X L1 L2 S :=
  (str83G4_c2_y_counts hfr d hX ht htQ).2.2

theorem str83G4_commutator_y_conjugate_x_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ⁅str83Y L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆ ≤
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  classical
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set W : Subgroup G := CFSG.conjugate (str83X L1 L2 S) d.w with hWdef
  set Y : Subgroup G := str83Y L1 L2 S with hYdef
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  have hQ1S : Q ≤ S := by rw [hQ]; exact str83G4_q1_le_s hfr
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hXY : X ≤ Y := by rw [hXdef, hYdef]; exact str83X_le_str83Y hfr hX
  have hYQ : Y ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  have hQH : Q ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hHNX : L1 ⊔ S ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hYleNX : Y ≤ Subgroup.normalizer (X : Set G) := (hYQ.trans hQH).trans hHNX
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hYQ2 : Y ≤ Q2 L1 L2 S := by
    intro y hy
    have hCX := str83G4_centralizer_x_le hfr (str83G4_not_le_normalizer_z2 hfr)
    have hyH : y ∈ L1 ⊔ S := hQH (hYQ hy)
    exact (hCX ⟨hyH, hy.2⟩).2
  have hYSw : Y ≤ CFSG.conjugate S d.w := by
    calc Y ≤ Q2 L1 L2 S := hYQ2
      _ = CFSG.conjugate (Q2 L1 L2 S) d.w := (str83G4_conjugate_q2_eq d).symm
      _ ≤ CFSG.conjugate S d.w := Subgroup.map_mono hQ2S
  have hSNX : S ≤ Subgroup.normalizer (X : Set G) :=
    ((le_sup_right : S ≤ L1 ⊔ S).trans (sup_left_le_p1 L1 L2 S)).trans
      (hXdef ▸ le_normalizer_str83X L1 L2 S)
  have hSwNW : CFSG.conjugate S d.w ≤ Subgroup.normalizer (W : Set G) := by
    calc CFSG.conjugate S d.w
        ≤ CFSG.conjugate (Subgroup.normalizer (X : Set G)) d.w := Subgroup.map_mono hSNX
      _ = Subgroup.normalizer (CFSG.conjugate X d.w : Set G) := by
          simpa [CFSG.conjugate] using
            (Subgroup.map_equiv_normalizer_eq X (MulAut.conj d.w⁻¹))
  have hYNW : Y ≤ Subgroup.normalizer (W : Set G) := hYSw.trans hSwNW
  have hWleQ : W ≤ Q2 L1 L2 S := by
    rw [hWdef]
    calc CFSG.conjugate (str83X L1 L2 S) d.w
        ≤ CFSG.conjugate (Q2 L1 L2 S) d.w := Subgroup.map_mono (str83G4_x_le_q2 hfr hX)
      _ = Q2 L1 L2 S := str83G4_conjugate_q2_eq d
  have hWgen : Subgroup.closure ((W : Set G) \ (Q : Set G)) = W := by
    have hsub : Subgroup.closure ((W : Set G) \ (Q : Set G)) ≤ W :=
      (Subgroup.closure_le _).mpr (fun x hx => hx.1)
    have hunion : (W : Set G) ⊆
        (Subgroup.closure ((W : Set G) \ (Q : Set G)) : Set G) ∪ (W ⊓ Q : Subgroup G) := by
      intro w hw
      by_cases hwQ : w ∈ Q
      · exact Or.inr ⟨hw, hwQ⟩
      · exact Or.inl (Subgroup.subset_closure ⟨hw, hwQ⟩)
    rcases SubgroupClass.subset_union.mp hunion with h | h
    · exact le_antisymm hsub h
    · exact absurd (h.trans inf_le_right) hB
  have hYtX : ∀ t ∈ W, t ∉ Q → ∀ y ∈ Y, ⁅y, t⁆ ∈ X := by
    intro t htW htQ y hy
    have hYeq := str83G4_y_eq_centralizer_sup_x hfr d hX htW htQ
    have hCYleNX : (Y ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤ Subgroup.normalizer (X : Set G) :=
      (inf_le_left : (Y ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤ Y).trans hYleNX
    have hy' : y ∈ X ⊔ (Y ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G)) := by
      rw [sup_comm, ← hYeq]
      exact hy
    obtain ⟨x, hxX, c, hcCY, hyeq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hCYleNX).mp hy'
    rw [hyeq]
    have hct : ⁅c, t⁆ = 1 := by
      have hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := hcCY.2
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hc t (Subgroup.mem_zpowers t)).symm
    have hxt : ⁅x, t⁆ ∈ X :=
      (Subgroup.commutator_le.mp (str83G4_commutator_x_conjugate_le hfr d hX)
        x hxX t htW).1
    rw [commutatorElement_mul_left_eq_conj_mul, hct, mul_one]
    simpa using hxt
  have hpair : ∀ y ∈ (Y : Set G), ∀ t ∈ (W : Set G) \ (Q : Set G), ⁅y, t⁆ ∈ X :=
    fun y hy t ht => hYtX t ht.1 ht.2 y hy
  have hYWX : ⁅Y, W⁆ ≤ X := by
    have h := CFSG.Timmesfeld.Bridge.OddLocal.commutator_closure_le
      (S := (Y : Set G)) (T := ((W : Set G) \ (Q : Set G))) (N := X)
      ((Subgroup.closure_le _).mpr (fun y hy => hYleNX hy))
      ((Subgroup.closure_le _).mpr
        (fun t ht => hHNX ((le_sup_right : S ≤ L1 ⊔ S) (hQ2S (hWleQ ht.1)))))
      hpair
    rwa [hWgen, Subgroup.closure_eq] at h
  have hYWW : ⁅Y, W⁆ ≤ W := by
    refine Subgroup.commutator_le.mpr fun y hy w hw => ?_
    have h1 : y * w * y⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hYNW hy) w).mp hw
    change y * w * y⁻¹ * w⁻¹ ∈ W
    have e : y * w * y⁻¹ * w⁻¹ = (y * w * y⁻¹) * w⁻¹ := by group
    rw [e]
    exact W.mul_mem h1 (W.inv_mem hw)
  exact le_inf hYWX hYWW

theorem str83G4_isSzNaturalSection_chiefStep
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {L N : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) L N)
    (hZ1L : Z1 L1 L2 S ≤ L)
    (hnc : ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N) :
    IsSzNaturalSection (L1 ⊔ S) N L a := by
  refine str83G4_isSzNaturalSection_of_quadratic (C := CFSG.conjugate (str83X L1 L2 S) d.w)
    hfr ?_ ?_ hstep hZ1L hnc
  · exact str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB
  · exact str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX

end CFSG.Quasithin.Stroth

end
