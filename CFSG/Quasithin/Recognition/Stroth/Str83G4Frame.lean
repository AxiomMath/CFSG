module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2Assembly
public import CFSG.Quasithin.Recognition.Stroth.Str83TorusFaithful

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] def str83X (L1 L2 S : Subgroup G) : Subgroup G :=
  conjClosure (Z2 L1 L2 S) (P1 L1 L2 S)

@[expose] def str83Y (L1 L2 S : Subgroup G) : Subgroup G :=
  Q1 L1 L2 S ⊓ Subgroup.centralizer (str83X L1 L2 S : Set G)

@[expose] def str83R (L1 L2 S : Subgroup G) : Subgroup G :=
  conjClosure (str83X L1 L2 S) (P2 L1 L2 S)

theorem le_normalizer_str83X (L1 L2 S : Subgroup G) :
    P1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
  le_normalizer_conjClosure _ _

theorem le_normalizer_str83R (L1 L2 S : Subgroup G) :
    P2 L1 L2 S ≤ Subgroup.normalizer (str83R L1 L2 S : Set G) :=
  le_normalizer_conjClosure _ _

theorem z2_le_str83X (L1 L2 S : Subgroup G) : Z2 L1 L2 S ≤ str83X L1 L2 S :=
  le_conjClosure _ _

@[expose] def Str83G4Frame (L1 L2 S : Subgroup G) (a : ℕ) : Prop :=
  F112HypW L1 L2 S ∧ bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) ∧ 1 ≤ a ∧
    Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∧ IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)

theorem str83G4Frame_of
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)) :
    Str83G4Frame L1 L2 S a := by
  have hB := str83_bigB_le_normalizer hF.1 ha hSz hL2
  refine ⟨hF, hB, ha, hSz, hL2, ?_⟩
  by_contra hII
  by_cases hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)
  · exact str83_caseII1_false hF hB ha hSz hL2 hII hZ2
  · exact str83_caseII2_false hF hB ha hSz (vBig_of_isL2Quot (by omega) hL2) ⟨_, hL2⟩ hII hZ2

theorem str83X_le_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    str83X L1 L2 S ≤ Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr
  have hZ := z2_le_q1_of_rq hF hB ha hSz hL2
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hh) z).mp (hZ hz)

theorem str83X_le_str83Y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hab : IsElemAbelian 2 (str83X L1 L2 S)) : str83X L1 L2 S ≤ str83Y L1 L2 S := by
  intro x hx
  refine ⟨str83X_le_q1 hfr hx, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have h := hab.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
  exact congrArg Subtype.val h

section NaturalBottom

open CFSG.QuasithinUnique.Setup
open scoped MatrixGroups

@[expose] def Str83G4VNat (L1 L2 S V : Subgroup G) (a : ℕ) : Prop :=
  ∃ (hstep : IsChiefStep (L2 ⊔ S) V ⊥ V) (hVH : V ≤ L2 ⊔ S) (hV : IsElemAbelian 2 V),
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hVH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ V) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ V)) := l2ChiefSectionModule hE
    ∃ (e : oTwoQuot ↥(L2 ⊔ S) ≃* SL(2, GaloisField 2 (2 * a + 1)))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 (2 * a + 1))
        (Additive (Ch3z.chiefMod ⊥ V)))
      (φ : Additive (Ch3z.chiefMod ⊥ V) ≃+ (Fin 2 → GaloisField 2 (2 * a + 1))),
      (∀ (h : ↥(L2 ⊔ S)) (x : Ch3z.chiefMod ⊥ V),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul x) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h x)) ∧
      (∀ g x, φ (ρ g x) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * a + 1))).mulVec (φ x))

@[expose] def Str83G4V (L1 L2 S V : Subgroup G) (a : ℕ) : Prop :=
  V ≤ Z2 L1 L2 S ∧ IsCentralStep (L2 ⊔ S) V (Z2 L1 L2 S) ∧ Str83G4VNat L1 L2 S V a

theorem str83G4_exists_natural_bottom
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ∃ V : Subgroup G, V ≤ Z2 L1 L2 S ∧ IsChiefStep (L2 ⊔ S) V ⊥ V ∧
      Str83G4VNat L1 L2 S V a := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨Y, hYZ, hstep⟩ := str83_exists_bottom_chiefStep hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hYH : Y ≤ L2 ⊔ S :=
    ((hYZ.trans (A4.omegaOneCenterOf_le (Q2 L1 L2 S))).trans hQ2S).trans le_sup_right
  have hV : IsElemAbelian 2 Y :=
    CFSG.Open.IsElemAbelian.mono (SmithC27.isElemAbelian_omegaOneCenterOf _) hYZ
  refine ⟨Y, hYZ, hstep, hstep, hYH, hV, ?_⟩
  by_cases hJ1 : thompsonJ S ≤ Q1 L1 L2 S
  · exact str83_natural_bottom_of_not_le_q2 hF hB ha hSz hL2 hZI
      (fun hJ2 => not_thompsonJ_le_q1_inf_q2 hF.1 (le_inf hJ1 hJ2)) hYZ hYH hV hstep
  · exact str83_natural_bottom_of_not_le_q1 hF hB ha hSz hL2 hZI hJ1 hYZ hYH hV hstep

@[expose] def Str83G4Z2Central : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ∀ V : Subgroup G, V ≤ Z2 L1 L2 S →
      IsChiefStep (L2 ⊔ S) V ⊥ V → IsCentralStep (L2 ⊔ S) V (Z2 L1 L2 S)

theorem str83G3Output_of_z2Central
    (h : Str83G4Z2Central) :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
      Str83G4Frame L1 L2 S a → ∃ V : Subgroup G, Str83G4V L1 L2 S V a := by
  intro G _ _ L1 L2 S a hfr
  obtain ⟨V, hVZ, hstep, hnat⟩ := str83G4_exists_natural_bottom hfr
  exact ⟨V, hVZ, h G L1 L2 S a hfr V hVZ hstep, hnat⟩

theorem str83G4_torusFaithful
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ∀ d ∈ borelOf L2 S, Odd (orderOf d) → (∀ z ∈ omegaOneCenterOf S, d * z = z * d) →
      d = 1 := by
  intro d hdB hodd hcent
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨Y, hYZ, hstep⟩ := str83_exists_bottom_chiefStep hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hYS : Y ≤ S := hYZ.trans ((A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S)
  have hYH : Y ≤ L2 ⊔ S := hYS.trans le_sup_right
  have hV : IsElemAbelian 2 Y :=
    CFSG.Open.IsElemAbelian.mono (SmithC27.isElemAbelian_omegaOneCenterOf _) hYZ
  have hsylow : IsSylowTwoOf S (L2 ⊔ S) := by
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
    exact h
  obtain ⟨e, ρ, φ, hcompat, hφnat⟩ :=
    if hJ1 : thompsonJ S ≤ Q1 L1 L2 S then
      str83_natural_bottom_of_not_le_q2 hF hB ha hSz hL2 hZI
        (fun hJ2 => not_thompsonJ_le_q1_inf_q2 hF.1 (le_inf hJ1 hJ2)) hYZ hYH hV hstep
    else
      str83_natural_bottom_of_not_le_q1 hF hB ha hSz hL2 hZI hJ1 hYZ hYH hV hstep
  have hdH : d ∈ L2 ⊔ S :=
    (le_sup_left : L2 ≤ L2 ⊔ S) ((CFSG.Quasithin.F1.borelOf_le L2 S) hdB)
  have hdBbig : d ∈ bigB L1 L2 S := by
    refine (show borelOf L2 S ≤ bigB L1 L2 S from ?_) hdB
    rw [bigB]
    exact le_sup_right.trans le_sup_left
  have hYinf : Y ⊓ Subgroup.centralizer (S : Set G) ≤ omegaOneCenterOf S :=
    inf_centralizer_le_omegaOneCenterOf_of_le hYS hV
  have hcentY : d ∈ Subgroup.centralizer
      ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcent x (hYinf hx)).symm
  exact l2_chiefStep_torus_faithful (n := 2 * a + 1) (H := L2 ⊔ S) (Y := Y) (S := S)
    (by omega) hsylow hYH hV hstep e ρ φ hcompat hφnat d hdH (hB hdBbig) hodd hcentY

end NaturalBottom

@[expose] def IsSzNaturalSection (H N M : Subgroup G) (a : ℕ) : Prop :=
  ∃ (e : oTwoQuot ↥H ≃* ↥(Sz a)) (c : ℕ)
    (φ : ↥N →* Multiplicative (Fin 4 → GaloisField 2 (2 * a + 1))),
    Function.Surjective φ ∧ φ.ker = M.subgroupOf N ∧
    ∀ (h : ↥H) (x y : ↥N), (y : G) = h * x * h⁻¹ →
      Multiplicative.toAdd (φ y) = Matrix.mulVec
        ((((e (QuotientGroup.mk h) : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c))
        (Multiplicative.toAdd (φ x))

theorem relIndex_eq_of_isSzNaturalSection {H N M : Subgroup G} {a : ℕ}
    (h : IsSzNaturalSection H N M a) : M.relIndex N = (2 ^ (2 * a + 1)) ^ 4 := by
  obtain ⟨-, -, φ, hsurj, hker, -⟩ := h
  have h1 : M.relIndex N = φ.ker.index := by rw [hker]; rfl
  rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd (α := Fin 4 → GaloisField 2 (2 * a + 1))), Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
    GaloisField.card 2 (2 * a + 1) (by omega)]

structure Str83G4Data (L1 L2 S : Subgroup G) : Type where
  D1 : Subgroup G
  D2 : Subgroup G
  hD1hall : RonanF13.HallTwoPrime D1 (borelOf L1 S)
  hD2hall : RonanF13.HallTwoPrime D2 (borelOf L2 S)
  hD1sup : borelOf L1 S = (S ⊓ L1) ⊔ D1
  hD2sup : borelOf L2 S = (S ⊓ L2) ⊔ D2
  hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x
  hBsplit : bigB L1 L2 S = S ⊔ D1 ⊔ D2
  hdelta : ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1,
    (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1
  w : G
  hwH2 : w ∈ L2 ⊔ S
  hwD2 : w ∈ Subgroup.normalizer (D2 : Set G)
  hwInv : ∀ d ∈ D2, w * d * w⁻¹ = d⁻¹
  hwNotN : w ∉ Subgroup.normalizer (S : Set G)
  hwTop : S ⊔ CFSG.conjugate S w = L2 ⊔ S

theorem str83G4Data_nonempty {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) : Nonempty (Str83G4Data L1 L2 S) := by
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr
  obtain ⟨D1, D2, hD1hall, hD2hall, hD1sup, hD2sup, hcomm, hBsplit, hdelta⟩ :=
    str83_exists_cartan_delta hF.1 ha hSz
  obtain ⟨w, hwH2, hwD2, hwInv, hwNotN, hwTop⟩ :=
    frameT1 hF hB ha hSz hL2 hD2hall.1 hD2hall.2.1 hD2sup.symm
  exact ⟨⟨D1, D2, hD1hall, hD2hall, hD1sup, hD2sup, hcomm, hBsplit, hdelta, w, hwH2, hwD2,
    hwInv, hwNotN, hwTop⟩⟩

end CFSG.Quasithin.Stroth

end
