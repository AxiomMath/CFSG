module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Vertex
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523Rank
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_isSzU3Quot_sup_left
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) := by
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hqU3 : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) :=
    Or.inl ⟨a, ha, rfl, ⟨eSz⟩⟩
  rw [hsup1]
  exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hqU3

theorem str83G4_conjugate_q2_eq {L1 L2 S : Subgroup G} (d : Str83G4Data L1 L2 S) :
    CFSG.conjugate (Q2 L1 L2 S) d.w = Q2 L1 L2 S := by
  apply CFSG.conjugate_eq_self_of_mem_normalizer
  have hwP2 : d.w ∈ P2 L1 L2 S :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
  exact (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) hwP2

private theorem conjugate_q1_twice
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    CFSG.conjugate (CFSG.conjugate (Q1 L1 L2 S) d.w) d.w = Q1 L1 L2 S := by
  rw [CFSG.conjugate_conjugate]
  apply CFSG.conjugate_eq_self_of_mem_normalizer
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hw2Q2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hw2P1 : d.w * d.w ∈ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right |> fun h => h (hQ2S hw2Q2)
  exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hw2P1

private theorem conjugate_inf_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    CFSG.conjugate
        (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w =
      CFSG.conjugate (str83X L1 L2 S) d.w ⊓ Q1 L1 L2 S := by
  rw [CFSG.conjugate, Subgroup.map_inf _ _ _ (MulAut.conj d.w⁻¹).injective]
  congr 1
  exact conjugate_q1_twice hfr d

theorem str83G4_x_le_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hX : IsElemAbelian 2 (str83X L1 L2 S)) : str83X L1 L2 S ≤ Q2 L1 L2 S := by
  classical
  have hXleY : str83X L1 L2 S ≤ str83Y L1 L2 S := str83X_le_str83Y hfr hX
  rw [str83G4_str83Y_eq_iInf hfr] at hXleY
  have h1 := (iInf_le (fun g : G => ⨅ (_ : g ∈ L1 ⊔ S),
    CFSG.conjugate (Q2 L1 L2 S) g) (1 : G)).trans
    (iInf_le (fun _ : (1 : G) ∈ L1 ⊔ S => CFSG.conjugate (Q2 L1 L2 S) 1)
      (L1 ⊔ S).one_mem)
  simpa using hXleY.trans h1

private theorem conjugate_str83X_le_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q2 L1 L2 S := by
  calc CFSG.conjugate (str83X L1 L2 S) d.w
      ≤ CFSG.conjugate (Q2 L1 L2 S) d.w := Subgroup.map_mono (str83G4_x_le_q2 hfr hX)
    _ = Q2 L1 L2 S := str83G4_conjugate_q2_eq d

theorem str83G4_conjugate_x_le_s
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    CFSG.conjugate (str83X L1 L2 S) d.w ≤ S :=
  (conjugate_str83X_le_q2 hfr d hX).trans
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1))

theorem str83G4_isElemAbelian_conjugate_x
    {L1 L2 S : Subgroup G} (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    IsElemAbelian 2 (CFSG.conjugate (str83X L1 L2 S) d.w) := by
  simpa [CFSG.conjugate] using
    CFSG.Open.IsElemAbelian.map hX (MulAut.conj d.w⁻¹).toMonoidHom

theorem relIndex_centralizerMod_le_relIndex_centralizer
    {H U U' V : Subgroup G} {t : G}
    (hUV : U ≤ V) (hU'U : U' < U)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hHU' : H ≤ Subgroup.normalizer (U' : Set G))
    [(U'.subgroupOf U).Normal] (htH : t ∈ H) :
    (centralizerMod U' U (Subgroup.zpowers t)).relIndex U ≤
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
  classical
  set C := centralizerMod U' U (Subgroup.zpowers t) with hC
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hUleN : U ≤ Subgroup.normalizer (U' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU'U.le).mp inferInstance
  have hU'C : U' ≤ C := by
    intro z hz
    refine mem_centralizerMod.mpr ⟨hU'U.le hz, hUleN (hU'U.le hz), ?_⟩
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (U' : Set G) :=
      hHU' (Subgroup.zpowers_le.mpr htH hv)
    have h1 : v * z⁻¹ * v⁻¹ ∈ U' :=
      (Subgroup.mem_normalizer_iff.mp hvN z⁻¹).mp (U'.inv_mem hz)
    have h2 : z * (v * z⁻¹ * v⁻¹) ∈ U' := U'.mul_mem hz h1
    simpa [mul_assoc] using h2
  have hCU : U ⊓ Subgroup.centralizer ({t} : Set G) ≤ C := by
    intro u hu
    refine mem_centralizerMod.mpr ⟨hu.1, hUleN hu.1, ?_⟩
    intro v hv
    have huC : u ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      simpa [hcent] using hu.2
    have huv : u * v = v * u :=
      (Subgroup.mem_centralizer_iff.mp huC v hv).symm
    have h1 : u * v * u⁻¹ * v⁻¹ = 1 := by rw [huv]; group
    rw [h1]
    exact U'.one_mem
  have hstep1 : C.relIndex U ≤ (U ⊓ Subgroup.centralizer ({t} : Set G)).relIndex U := by
    exact Subgroup.relIndex_le_of_le_left (L := U) hCU (Subgroup.index_ne_zero_of_finite)
  have hstep2 : (U ⊓ Subgroup.centralizer ({t} : Set G)).relIndex U ≤
      (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V := by
    have hCU' : U ⊓ Subgroup.centralizer ({t} : Set G) =
        U ⊓ (V ⊓ Subgroup.centralizer ({t} : Set G)) := by
      rw [← inf_assoc, inf_eq_left.mpr hUV]
    rw [hCU']
    have h1 : (U ⊓ (V ⊓ Subgroup.centralizer ({t} : Set G))).relIndex U =
        (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex U := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right _ _
    rw [h1]
    exact Subgroup.relIndex_le_of_le_right hUV (Subgroup.index_ne_zero_of_finite)
  exact hstep1.trans hstep2

theorem str83G4_cp_counts
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex
        (str83X L1 L2 S) = 2 ^ (2 * a + 1) ∧
      (str83X L1 L2 S ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 ∧
      (str83X L1 L2 S ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤
        CFSG.conjugate (Q1 L1 L2 S) d.w ∧
      ⁅str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w, Subgroup.zpowers t⁆ =
        CFSG.conjugate (Z1 L1 L2 S) d.w := by
  classical
  set X := str83X L1 L2 S with hXdef
  set W := CFSG.conjugate X d.w with hWdef
  set q : ℕ := 2 ^ (2 * a + 1) with hqdef
  have hXabel : IsElemAbelian 2 X := by rwa [hXdef]
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.1)
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  have hXQ2 : X ≤ Q2 L1 L2 S := by
    rw [hXdef]
    exact str83G4_x_le_q2 hfr hX
  have hXQ1 : X ≤ Q1 L1 L2 S := by
    rw [hXdef]
    exact str83X_le_q1 hfr
  have hWQ2 : W ≤ Q2 L1 L2 S := by
    rw [hWdef]
    exact conjugate_str83X_le_q2 hfr d hX
  have hWleS : W ≤ S := hWQ2.trans hQ2S
  have hWleH : W ≤ L1 ⊔ S := hWleS.trans le_sup_right
  have hWabel : IsElemAbelian 2 W := by
    rw [hWdef]
    exact str83G4_isElemAbelian_conjugate_x d hX
  have ht2 : t * t = 1 := by
    have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
    simpa [pow_two] using h
  have htH : t ∈ L1 ⊔ S := hWleH ht
  have htO : t ∉ pCoreOf 2 (L1 ⊔ S) := by simpa [hpCore1] using htQ
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hV0leX : X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w ≤ X := inf_le_left
  have hV0abel : ∀ x ∈ X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w,
      ∀ y ∈ X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w, x * y = y * x := by
    intro x hx y hy
    exact (B6.isElemAbelian_iff.mp hXabel).1 x (hV0leX hx) y (hV0leX hy)
  have htNX : t ∈ Subgroup.normalizer (X : Set G) := by
    have htP1 : t ∈ P1 L1 L2 S :=
      (le_sup_right : S ≤ bigB L1 L2 S) (hWleS ht) |> fun h =>
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) h
    exact le_normalizer_str83X L1 L2 S htP1
  have hWleP1w : W ≤ CFSG.conjugate (P1 L1 L2 S) d.w := by
    calc W ≤ Q2 L1 L2 S := hWQ2
      _ = CFSG.conjugate (Q2 L1 L2 S) d.w := (str83G4_conjugate_q2_eq d).symm
      _ ≤ CFSG.conjugate S d.w := Subgroup.map_mono hQ2S
      _ ≤ CFSG.conjugate (P1 L1 L2 S) d.w :=
          Subgroup.map_mono ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have htNQ1w : t ∈ Subgroup.normalizer
      (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
    have hconjN : CFSG.conjugate (P1 L1 L2 S) d.w ≤
        Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
      calc CFSG.conjugate (P1 L1 L2 S) d.w
          ≤ CFSG.conjugate (Subgroup.normalizer (Q1 L1 L2 S : Set G)) d.w :=
            Subgroup.map_mono (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
        _ = Subgroup.normalizer (CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) := by
            simpa [CFSG.conjugate] using
              (Subgroup.map_equiv_normalizer_eq (Q1 L1 L2 S) (MulAut.conj d.w⁻¹))
    exact hconjN (hWleP1w ht)
  have htNV0 : t ∈ Subgroup.normalizer
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w : Set G) :=
    A4.mem_normalizer_inf htNX htNQ1w
  have hcommQ1wW : ⁅CFSG.conjugate (Q1 L1 L2 S) d.w, W⁆ ≤
      CFSG.conjugate (Z1 L1 L2 S) d.w := by
    have hbase : ⁅Q1 L1 L2 S, X⁆ ≤ Z1 L1 L2 S := by
      rw [Subgroup.commutator_comm]
      exact str83G4_commutator_x_q1_le hfr
    calc ⁅CFSG.conjugate (Q1 L1 L2 S) d.w, W⁆
        = CFSG.conjugate ⁅Q1 L1 L2 S, X⁆ d.w := by
          simp only [CFSG.conjugate, hWdef]
          exact (Subgroup.map_commutator _ _ _).symm
      _ ≤ CFSG.conjugate (Z1 L1 L2 S) d.w := Subgroup.map_mono hbase
  have hY : ∀ x ∈ X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w,
      x * t * x⁻¹ * t⁻¹ ∈ CFSG.conjugate (Z1 L1 L2 S) d.w := by
    intro x hx
    have hmem := Subgroup.commutator_le.mp hcommQ1wW x hx.2 t ht
    simpa [commutatorElement_def] using hmem
  have hCbound0 : (Subgroup.centralizer ({t} : Set G)).relIndex
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ≤
        Nat.card ↥(CFSG.conjugate (Z1 L1 L2 S) d.w) :=
    S2A.relIndex_centralizer_le (X := X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w)
      (Y := CFSG.conjugate (Z1 L1 L2 S) d.w) (d := t) hV0abel htNV0 hY
  have hcardZ1w : Nat.card ↥(CFSG.conjugate (Z1 L1 L2 S) d.w) = q := by
    rw [hqdef]
    have hcard_conj : Nat.card ↥(CFSG.conjugate (Z1 L1 L2 S) d.w) =
        Nat.card ↥(Z1 L1 L2 S) := by
      simpa [CFSG.conjugate] using
        Subgroup.card_map_of_injective (K := Z1 L1 L2 S)
          (f := (MulAut.conj d.w⁻¹).toMonoidHom) (MulAut.conj d.w⁻¹).injective
    rw [hcard_conj]
    exact str83G4Z1Card_holds G L1 L2 S a hfr
  have hCbound : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ≤ q := by
    rw [hcent]
    exact hCbound0.trans (le_of_eq hcardZ1w)
  have hM5W : (W ⊓ Q1 L1 L2 S).relIndex W ≤ q := by
    have hbender1 := str83G4_isSzU3Quot_sup_left hfr
    have hsylow1 := str83G4_isSylowTwoOf_sup_left hfr
    have hsq : ∀ w ∈ W, w ^ 2 ∈ pCoreOf 2 (L1 ⊔ S) := by
      intro w hw
      have hw2 : w ^ 2 = 1 := (B6.isElemAbelian_iff.mp hWabel).2 w hw
      rw [hw2]
      exact (pCoreOf 2 (L1 ⊔ S)).one_mem
    have h := relIndex_inf_pCoreOf_le (L := L1 ⊔ S) (T := S) (A := W) (q := q)
      hbender1 hsylow1 hWleS hsq
    simpa [hpCore1] using h
  have hrelV0 : (CFSG.conjugate (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w).relIndex W =
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X := by
    rw [hWdef]
    exact Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹)
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) X
  have hmapV0 : CFSG.conjugate (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w =
      W ⊓ Q1 L1 L2 S := by
    rw [hWdef]
    exact conjugate_inf_q1 hfr d
  have hV0relUpper : (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X ≤ q := by
    rw [← hrelV0, hmapV0]
    exact hM5W
  have hXleH : X ≤ L1 ⊔ S := (hXQ1.trans hQ1S).trans le_sup_right
  have hCXlower : q ^ 2 ≤ (X ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X := by
    obtain ⟨L, N, hstep, hZ1L, hnotcent⟩ := str83G4_exists_chiefStep hfr
    have hnc : ¬ IsCentralStep (L1 ⊔ S) L N := by
      intro hc
      apply hnotcent
      intro y hy
      refine ⟨(twoResidual_le (L1 ⊔ S)) hy, ?_, ?_⟩
      · exact D14.le_normalizer_of_isNormalIn hstep.2.1 ((twoResidual_le (L1 ⊔ S)) hy)
      · intro u hu
        exact hc y ((twoResidual_le (L1 ⊔ S)) hy) u hu
    have hXp : IsPGroup 2 X := by
      rw [hXdef]
      exact CFSG.Open.IsElemAbelian.isPGroup hX
    have hM7 := sq_le_relIndex_centralizerMod (H := L1 ⊔ S) (U := X)
      (L := L) (N := N) (q := q) (str83G4_isSzU3Quot_sup_left hfr) hXp
      (by rw [hXdef]; exact hXleH)
      hstep hnc htH (by rw [hpCore1, ht2]; exact (Q1 L1 L2 S).one_mem) htO
    have hHNL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
      D14.le_normalizer_of_isNormalIn hstep.2.1
    haveI : (L.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr
        (hstep.1.1.trans (hXleH.trans hHNL))
    have hrel : (centralizerMod L N (Subgroup.zpowers t)).relIndex N ≤
        (X ⊓ Subgroup.centralizer ({t} : Set G)).relIndex X :=
      relIndex_centralizerMod_le_relIndex_centralizer (H := L1 ⊔ S) (U := N) (U' := L)
        (V := X) hstep.1.1 hstep.2.2.1 (D14.le_normalizer_of_isNormalIn hstep.1)
        (D14.le_normalizer_of_isNormalIn hstep.2.1) htH
    rw [hcent]
    exact hM7.trans hrel
  have hCbound' : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ≤ q := by
    rw [Subgroup.inf_relIndex_left]
    exact hCbound
  have hUpper : (X ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X ≤
        q ^ 2 := by
    have hle : (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ≤
        X ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h1 : (X ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X ≤
        ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X :=
      Subgroup.relIndex_le_of_le_left (L := X) hle (Subgroup.index_ne_zero_of_finite)
    have h2 : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
          (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X =
        ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X :=
      Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left
    calc (X ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X
        ≤ ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
            Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X := h1
      _ = ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
            Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
              (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X := h2.symm
      _ ≤ q * q := Nat.mul_le_mul hCbound' hV0relUpper
      _ = q ^ 2 := by rw [pow_two]
  have hCXrel : (X ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X = q ^ 2 :=
    le_antisymm hUpper hCXlower
  have hV0CrelX : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex X = q ^ 2 := by
    refine le_antisymm ?_ ?_
    · rw [← Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left]
      calc ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
            Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
              (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X
          ≤ q * q := Nat.mul_le_mul hCbound' hV0relUpper
        _ = q ^ 2 := by rw [pow_two]
    · rw [← hCXrel]
      exact Subgroup.relIndex_le_of_le_left (L := X)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (Subgroup.index_ne_zero_of_finite)
  have hV0rel : (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X = q := by
    have hmul : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
        (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X = q * q := by
      rw [Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left,
        hV0CrelX, pow_two]
    have hqpos : 0 < q := by rw [hqdef]; positivity
    rcases lt_or_eq_of_le hV0relUpper with hlt | heq
    · have hltprod : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
            Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
              (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
          (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X < q * q := by
        rw [mul_comm]
        exact Nat.mul_lt_mul_of_lt_of_le hlt hCbound' hqpos
      omega
    · exact heq
  have hCrel : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) = q := by
    have hmul : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
        (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X = q * q := by
      rw [Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left,
        hV0CrelX, pow_two]
    have hqpos : 0 < q := by rw [hqdef]; positivity
    have hmul' : ((X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
          Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
            (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) *
        (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X =
        q * (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex X := by
      rw [hmul, hV0rel]
    exact Nat.eq_of_mul_eq_mul_right (by rw [hV0rel]; exact hqpos) hmul'
  have hcommLe : ⁅X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w, Subgroup.zpowers t⁆ ≤
      CFSG.conjugate (Z1 L1 L2 S) d.w :=
    (Subgroup.commutator_mono inf_le_right (Subgroup.zpowers_le.mpr ht)).trans hcommQ1wW
  have hcommEq : ⁅X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w, Subgroup.zpowers t⁆ =
      CFSG.conjugate (Z1 L1 L2 S) d.w := by
    refine Subgroup.eq_of_le_of_card_ge hcommLe ?_
    rw [F53.Stellmacher.S43.card_commutator_zpowers (W := X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w)
      (x := t) hV0abel htNV0]
    rw [← hcent, hCrel, hcardZ1w]
  have hCXeq : X ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    symm
    exact CFSG.Quasithin.Ch3y.eq_of_le_of_relIndex_le
      (K₁ := (X ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) ⊓
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))
      (K₂ := X ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))
      (A := X) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) inf_le_left
      (by rw [hV0CrelX, hCXrel])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXdef, hqdef]
    exact hV0rel
  · rw [hXdef, hqdef]
    exact hCXrel
  · rw [hXdef, hCXeq]
    exact inf_le_left.trans inf_le_right
  · rw [hXdef]
    exact hcommEq

private theorem exists_conjugate_not_mem_q1
    {L1 L2 S : Subgroup G} {d : Str83G4Data L1 L2 S}
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∃ t : G, t ∈ CFSG.conjugate (str83X L1 L2 S) d.w ∧ t ∉ Q1 L1 L2 S := by
  by_contra h
  apply hB
  intro x hx
  by_contra hxQ
  exact h ⟨x, hx, hxQ⟩

theorem str83G4_relIndex_conjugate_x_inf_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (CFSG.conjugate (str83X L1 L2 S) d.w ⊓ Q1 L1 L2 S).relIndex
      (CFSG.conjugate (str83X L1 L2 S) d.w) = 2 ^ (2 * a + 1) := by
  obtain ⟨t, ht, htQ⟩ := exists_conjugate_not_mem_q1 hB
  have hV0rel := (str83G4_cp_counts hfr d hX ht htQ).1
  have hrelV0 : (CFSG.conjugate
      (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w).relIndex
        (CFSG.conjugate (str83X L1 L2 S) d.w) =
      (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w).relIndex
        (str83X L1 L2 S) :=
    Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹)
      (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) (str83X L1 L2 S)
  have hmapV0 : CFSG.conjugate
      (str83X L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S) d.w) d.w =
      CFSG.conjugate (str83X L1 L2 S) d.w ⊓ Q1 L1 L2 S :=
    conjugate_inf_q1 hfr d
  rw [← hmapV0, hrelV0, hV0rel]

theorem str83G4_mem_conjugate_x_sup_q1_iff
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) (s : G) :
    s ∈ CFSG.conjugate (str83X L1 L2 S) d.w ⊔ Q1 L1 L2 S ↔
      s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S := by
  classical
  set X := str83X L1 L2 S with hXdef
  set W := CFSG.conjugate X d.w with hWdef
  set q : ℕ := 2 ^ (2 * a + 1) with hqdef
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hWleS : W ≤ S := by
    rw [hWdef]
    exact str83G4_conjugate_x_le_s hfr d hX
  have hbender1 := str83G4_isSzU3Quot_sup_left hfr
  have hsylow1 := str83G4_isSylowTwoOf_sup_left hfr
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := str83G4_pCoreOf_sup_left hfr
  obtain ⟨X₀, hX₀mem, hQ1X₀, hQ1relX₀, -⟩ := exists_X0 hbender1 hsylow1
  have hQ1X₀' : Q1 L1 L2 S ≤ X₀ := by simpa [hpCore1] using hQ1X₀
  have hQ1relX₀' : (Q1 L1 L2 S).relIndex X₀ = q := by
    simpa [hpCore1, hqdef] using hQ1relX₀
  have hWabel : IsElemAbelian 2 W := by
    rw [hWdef]
    exact str83G4_isElemAbelian_conjugate_x d hX
  have hWleX₀ : W ≤ X₀ := by
    intro w hw
    rw [hX₀mem w]
    refine ⟨hWleS hw, ?_⟩
    have hw2 : w ^ 2 = 1 := (B6.isElemAbelian_iff.mp hWabel).2 w hw
    rw [hpCore1, hw2]
    exact (Q1 L1 L2 S).one_mem
  have hsup_le : W ⊔ Q1 L1 L2 S ≤ X₀ := sup_le hWleX₀ hQ1X₀'
  have hQ1relSup : (Q1 L1 L2 S).relIndex (W ⊔ Q1 L1 L2 S) = q := by
    have hWnorm : W ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
      intro w hw
      exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
        ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
          ((le_sup_right : S ≤ bigB L1 L2 S) (hWleS hw)))
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := W) (K := Q1 L1 L2 S) hWnorm).2
    rw [h, hWdef]
    exact str83G4_relIndex_conjugate_x_inf_q1 hfr d hX hB
  have hrelOne : (W ⊔ Q1 L1 L2 S).relIndex X₀ = 1 := by
    have hmul := Subgroup.relIndex_mul_relIndex (Q1 L1 L2 S)
      (W ⊔ Q1 L1 L2 S) X₀ le_sup_right hsup_le
    rw [hQ1relX₀', hQ1relSup] at hmul
    have hqpos : 0 < q := by rw [hqdef]; positivity
    have hmul' : q * (W ⊔ Q1 L1 L2 S).relIndex X₀ = q * 1 := by
      rw [mul_one]
      exact hmul
    exact Nat.eq_of_mul_eq_mul_left hqpos hmul'
  have hEq : W ⊔ Q1 L1 L2 S = X₀ :=
    le_antisymm hsup_le (Subgroup.relIndex_eq_one.mp hrelOne)
  constructor
  · intro hs
    rw [hEq] at hs
    rw [hX₀mem s] at hs
    exact ⟨hs.1, by simpa [hpCore1] using hs.2⟩
  · rintro ⟨hsS, hsQ⟩
    rw [hEq]
    rw [hX₀mem s]
    exact ⟨hsS, by simpa [hpCore1] using hsQ⟩

theorem str83G4_relIndex_centralizer_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    {t : G} (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w)
    (htQ : t ∉ Q1 L1 L2 S) :
    (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  have h := (str83G4_cp_counts hfr d hX ht htQ).2.1
  rwa [Subgroup.inf_relIndex_left] at h

theorem str83G4_chiefSeries_x_eq_one
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) {c : ℕ}
    (hser : IsChiefSeriesFrom (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) c) : c = 1 := by
  classical
  set X := str83X L1 L2 S with hXdef
  set H : Subgroup G := L1 ⊔ S with hHdef
  set q : ℕ := 2 ^ (2 * a + 1) with hqdef
  obtain ⟨t, ht, htQ⟩ := exists_conjugate_not_mem_q1 hB
  have hcounts := str83G4_cp_counts hfr d hX ht htQ
  have hCXrel' : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      X = q ^ 2 := by
    have h := hcounts.2.1
    rw [Subgroup.inf_relIndex_left] at h
    exact h
  have hXp : IsPGroup 2 X := by
    rw [hXdef]
    exact CFSG.Open.IsElemAbelian.isPGroup hX
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hXQ1 : X ≤ Q1 L1 L2 S := by
    rw [hXdef]
    exact str83X_le_q1 hfr
  have hXH : X ≤ H := by
    rw [hHdef]
    exact (hXQ1.trans hQ1S).trans le_sup_right
  have hpCore1 : pCoreOf 2 H = Q1 L1 L2 S := by
    rw [hHdef]
    exact str83G4_pCoreOf_sup_left hfr
  have hWleS : CFSG.conjugate X d.w ≤ S := by
    rw [hXdef]
    exact str83G4_conjugate_x_le_s hfr d hX
  have hWabel : IsElemAbelian 2 (CFSG.conjugate X d.w) := by
    rw [hXdef]
    exact str83G4_isElemAbelian_conjugate_x d hX
  have htH : t ∈ H := by
    rw [hHdef]
    exact (le_sup_right : S ≤ L1 ⊔ S) (hWleS ht)
  have ht2 : t * t = 1 := by
    have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
    simpa [pow_two] using h
  have htO : t ∉ pCoreOf 2 H := by simpa [hpCore1] using htQ
  have hle1 : c ≤ 1 := by
    have hM6 := pow_sq_le_relIndex_centralizer (H := H) (U := X) (q := q) (c := c)
      (str83G4_isSzU3Quot_sup_left hfr) hXp hXH hser htH
      (by rw [hpCore1, ht2]; exact (Q1 L1 L2 S).one_mem) htO
    rw [hCXrel'] at hM6
    have hq2 : 1 < q ^ 2 := by
      rw [hqdef, ← pow_mul]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    exact (Nat.pow_le_pow_iff_right hq2).mp (by simpa using hM6)
  have hXQ1H : X ≤ pCoreOf 2 H := by rwa [hpCore1]
  have hXN : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHdef, hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hnormal : IsNormalIn H X X :=
    ⟨le_rfl, fun g hg y hy =>
      (Subgroup.mem_normalizer_iff.mp (hXN hg) y).mp hy⟩
  have hge1 : 1 ≤ c := by
    by_contra hlt
    have hc0 : c = 0 := by omega
    have hcommZero : ⁅X, oTwoUpper H⁆ = ⊥ :=
      (F112W.isChiefSeriesFrom_zero_iff hXH hXQ1H hnormal).mp (hc0 ▸ hser)
    have hcommZero' : ⁅X, twoResidual H⁆ = ⊥ := by
      rw [F6.twoResidual_eq_oTwoUpper]
      exact hcommZero
    obtain ⟨L, N, hstep, hZ1L, hnotcent⟩ := str83G4_exists_chiefStep hfr
    apply hnotcent
    intro y hy
    refine ⟨(twoResidual_le H) hy, ?_, ?_⟩
    · exact D14.le_normalizer_of_isNormalIn hstep.2.1 ((twoResidual_le H) hy)
    · intro u hu
      have hmem : ⁅u, y⁆ ∈ ⁅X, twoResidual H⁆ :=
        Subgroup.commutator_mem_commutator (hstep.1.1 hu) hy
      rw [hcommZero'] at hmem
      have h1 : u * y * u⁻¹ * y⁻¹ = 1 := by
        simpa [commutatorElement_def] using Subgroup.mem_bot.mp hmem
      have h2 : y * u * y⁻¹ * u⁻¹ = 1 := by
        have := congrArg Inv.inv h1
        simpa [mul_assoc] using this
      rw [h2]
      exact L.one_mem
  omega

end CFSG.Quasithin.Stroth

end
