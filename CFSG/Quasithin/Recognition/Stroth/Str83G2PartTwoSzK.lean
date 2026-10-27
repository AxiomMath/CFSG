module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzK2
public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzNat3
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E34Suz
public import CFSG.GroupTheory.SteinbergBKSolvableHallConjugacy
public import CFSG.Quasithin.Recognition.F112Crit.ConjAut
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Quasithin.Background.RonanF13Hall

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Sz CFSG.QuasithinUnique
open CFSG.Quasithin.F112R CFSG.LieType.Ree CFSG.Blueprint
open scoped Matrix MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_partTwo_le_normalizer_z1
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  rw [hsup1]
  refine sup_le ?_ ?_
  · exact ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
  · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
      (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))

theorem str83_partTwo_lemmaK_centralizes
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {d : G} (hdB : d ∈ bigB L1 L2 S)
    (hdZ2 : d ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hd : ∀ l ∈ L1, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    d ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  classical
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str83_partTwo_le_normalizer_z1 hF hB ha hSz
  have hQ1V : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    Q1_le_centralizer_Z1 L1 L2 S
  have hdP1 : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  have hdN : d ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))) hdP1
  have hcomm : ∀ l ∈ L1, d * l * d⁻¹ * l⁻¹ ∈ Q1 L1 L2 S :=
    fun l hl => hF.1.pCoreOf_le_pCoreOf_vertex (hd l hl)
  have hHZ1' : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [← hsup1]
    exact hHZ1
  have hstep1 : ∀ h ∈ L1 ⊔ Q1 L1 L2 S, ∀ z ∈ Z1 L1 L2 S,
      h * (d * z * d⁻¹) * h⁻¹ = d * (h * z * h⁻¹) * d⁻¹ :=
    conj_comm_of_commutator hdN hQ1V
      ((le_sup_left : L1 ≤ L1 ⊔ S).trans hHZ1) hcomm
  have hstep1' : ∀ h ∈ L1 ⊔ S, ∀ z ∈ Z1 L1 L2 S,
      h * (d * z * d⁻¹) * h⁻¹ = d * (h * z * h⁻¹) * d⁻¹ := by
    intro h hh
    exact hstep1 h (hsup1 ▸ hh)
  let Y : Subgroup G := Z1 L1 L2 S ⊓ Subgroup.centralizer ({d} : Set G)
  have hYZ : Y ≤ Z1 L1 L2 S := inf_le_left
  have hYforward : ∀ h ∈ L1 ⊔ S, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := by
    intro h hh y hy
    obtain ⟨hyZ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hhyZ : h * y * h⁻¹ ∈ Z1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hHZ1 hh) y).mp hyZ
    have hdy' : d * y = y * d := (Subgroup.mem_centralizer_iff.mp hyC) d (by simp)
    have hdy : d * y * d⁻¹ = y := by
      rw [hdy']
      group
    have hcommh : h * y * h⁻¹ = d * (h * y * h⁻¹) * d⁻¹ := by
      rw [← hstep1' h hh y hyZ, hdy]
    refine Subgroup.mem_inf.mpr ⟨hhyZ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxd : x = d := by simpa using hx
    subst x
    have hdcomm : d * (h * y * h⁻¹) = (h * y * h⁻¹) * d := by
      calc d * (h * y * h⁻¹) = (d * (h * y * h⁻¹) * d⁻¹) * d := by group
        _ = (h * y * h⁻¹) * d := by rw [← hcommh]
    exact hdcomm
  have hYN : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hYforward h hh y
    · intro hy
      have h' := hYforward h⁻¹ ((L1 ⊔ S).inv_mem hh) (h * y * h⁻¹) hy
      have h'' : y ∈ Y := by
        convert h' using 1
        group
      exact h''
  have hZle : omegaOneCenterOf S ≤ Z1 L1 L2 S ⊓ Z2 L1 L2 S :=
    omegaOneCenterOf_S_le_caseII hF.1 hS1 hS2
  have hZne : omegaOneCenterOf S ≠ ⊥ := omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hZ2Z1ne : Z1 L1 L2 S ⊓ Z2 L1 L2 S ≠ ⊥ := by
    intro hbot
    apply hZne
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Z1 L1 L2 S ⊓ Z2 L1 L2 S := hZle hx
    rwa [hbot] at hx'
  have hZ12Y : Z1 L1 L2 S ⊓ Z2 L1 L2 S ≤ Y := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hz1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxd : x = d := by simpa using hx
    subst x
    exact ((Subgroup.mem_centralizer_iff.mp hdZ2) z hz2).symm
  have hYne : Y ≠ ⊥ := by
    intro hbot
    exact hZ2Z1ne (le_bot_iff.mp (hbot ▸ hZ12Y))
  have hYeq := str83_partTwo_z1_irreducible hF hB ha hSz hL2 hII hZ2 hJ hYZ hYN
  rcases hYeq with hbot | htop
  · exact absurd hbot hYne
  · intro z hz
    have hzY : z ∈ Y := htop ▸ hz
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzY).2) d (by simp)).symm

theorem str83_partTwo_card_centralizer_le
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    {D1 : Subgroup G} (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    {d δ : G} (hdB : d ∈ bigB L1 L2 S) (hδ : δ ∈ D1) (hδ1 : δ ≠ 1)
    (hd : ∀ l ∈ L1, (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    Nat.card ↥(Z1 L1 L2 S ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 ^ (2 * a + 1) := by
  classical
  let K : Type := GaloisField 2 (2 * a + 1)
  haveI : Field K := inferInstance
  haveI : Finite K := inferInstance
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by
    change Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1)
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  haveI hcharK : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  haveI hperfectK : PerfectRing K 2 := inferInstance
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str83_partTwo_le_normalizer_z1 hF hB ha hSz
  have hQ1V : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    Q1_le_centralizer_Z1 L1 L2 S
  let V : Subgroup G := Z1 L1 L2 S
  obtain ⟨e, c, φ, hSmap, hφ⟩ :=
    str83_partTwo_z1_natural (K := K) hF hB ha hSz hL2 hII hZ2 hJ hK
  let M : ↥(suzukiGroup a K) → Matrix (Fin 4) (Fin 4) K := fun g =>
    (((g : Matrix.GeneralLinearGroup (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
  let Mt : ↥(suzukiGroup a K) → Matrix (Fin 4) (Fin 4) K :=
    fun g => (M g).map (· ^ 2 ^ c)
  let k : G := d * δ⁻¹
  have hδL : δ ∈ L1 ⊔ S :=
    (le_sup_left : L1 ≤ L1 ⊔ S) ((hD1.1.trans (F1.borelOf_le L1 S)) hδ)
  have hδN : δ ∈ Subgroup.normalizer (V : Set G) := hHZ1 hδL
  have hδB : δ ∈ bigB L1 L2 S :=
    ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤ bigB L1 L2 S)) (hD1.1 hδ)
  have hkB : k ∈ bigB L1 L2 S :=
    (bigB L1 L2 S).mul_mem hdB ((bigB L1 L2 S).inv_mem hδB)
  have hkP1 : k ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hkB
  have hkN : k ∈ Subgroup.normalizer (V : Set G) :=
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))) hkP1
  have hdP1 : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  have hdN : d ∈ Subgroup.normalizer (V : Set G) :=
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))) hdP1
  have hcomm : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S :=
    fun l hl => hF.1.pCoreOf_le_pCoreOf_vertex (hd l hl)
  have hstep1 : ∀ h ∈ L1 ⊔ S, ∀ z ∈ V,
      h * (k * z * k⁻¹) * h⁻¹ = k * (h * z * h⁻¹) * k⁻¹ := by
    have h' := conj_comm_of_commutator hkN hQ1V
      ((le_sup_left : L1 ≤ L1 ⊔ S).trans hHZ1) hcomm
    intro h hh z hz
    exact h' h (hsup1 ▸ hh) z hz
  have hnat : ∀ (h : ↥(L1 ⊔ S)) (w : Additive ↥V),
      F112Crit.ConjAut.conjAut V (h : G) (hHZ1 h.2) w =
        φ.symm (Mt (e (QuotientGroup.mk h)) *ᵥ φ w) := by
    intro h w
    apply φ.injective
    rw [AddEquiv.apply_symm_apply]
    have hmem : (h : G) * w.toMul * (h : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hHZ1 h.2) w.toMul).mp w.toMul.2
    have h1 : F112Crit.ConjAut.conjAut V (h : G) (hHZ1 h.2) w =
        Additive.ofMul (⟨(h : G) * w.toMul * (h : G)⁻¹, hmem⟩ : ↥V) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [F112Crit.ConjAut.val_conjAut]
      rfl
    rw [h1]
    simpa [Mt, M] using hφ h w.toMul ⟨(h : G) * w.toMul * (h : G)⁻¹, hmem⟩ rfl
  let y : Additive ↥(Z1 L1 L2 S) →+ Additive ↥(Z1 L1 L2 S) :=
    (F112Crit.ConjAut.conjAut V k hkN).toAddMonoidHom
  have hy : ∀ (g : ↥(suzukiGroup a K)) (w : Additive ↥V),
      y (φ.symm (Mt g *ᵥ φ w)) = φ.symm (Mt g *ᵥ φ (y w)) := by
    intro g w
    obtain ⟨x, hx⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    subst g
    have hN : (h : G) ∈ Subgroup.normalizer (V : Set G) := hHZ1 h.2
    have hconj : φ.symm (Mt (e (QuotientGroup.mk h)) *ᵥ φ w) =
        F112Crit.ConjAut.conjAut V (h : G) hN w := (hnat h w).symm
    calc y (φ.symm (Mt (e (QuotientGroup.mk h)) *ᵥ φ w))
        = y (F112Crit.ConjAut.conjAut V (h : G) hN w) := by rw [hconj]
      _ = F112Crit.ConjAut.conjAut V k hkN (F112Crit.ConjAut.conjAut V (h : G) hN w) := rfl
      _ = F112Crit.ConjAut.conjAut V (h : G) hN (F112Crit.ConjAut.conjAut V k hkN w) := by
            apply Additive.toMul.injective
            apply Subtype.ext
            exact (hstep1 h h.2 w.toMul w.toMul.2).symm
      _ = F112Crit.ConjAut.conjAut V (h : G) hN (y w) := rfl
      _ = φ.symm (Mt (e (QuotientGroup.mk h)) *ᵥ φ (y w)) := hnat h (y w)
  obtain ⟨μ, hμ⟩ := exists_smul_of_comm_twisted_sz (a := a) (K := K) (c := c) hK y (by
      intro g w
      simpa [Mt, V] using hy g w)
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    have h1 := hμ (φ.symm (Pi.single 0 (1 : K)))
    rw [hμ0, zero_smul] at h1
    have h2 : y (φ.symm (Pi.single 0 (1 : K))) = 0 := by
      apply φ.injective
      simpa using h1
    have h3' : φ.symm (Pi.single 0 (1 : K)) = 0 := by
      have hy : Function.Injective y := (F112Crit.ConjAut.conjAut V k hkN).injective
      apply hy
      rw [map_zero]
      exact h2
    have h4 : (Pi.single 0 (1 : K) : Fin 4 → K) = 0 := by
      rw [← AddEquiv.apply_symm_apply φ (Pi.single 0 (1 : K)), h3', map_zero]
    have h5 : (1 : K) = 0 := by simpa using congrFun h4 0
    exact one_ne_zero h5
  have hd_eq : d = k * δ := by
    show d = (d * δ⁻¹) * δ
    group
  have hklN : k * δ ∈ Subgroup.normalizer (V : Set G) := by rwa [← hd_eq]
  have hcd : ∀ z : Additive ↥V,
      F112Crit.ConjAut.conjAut V d hdN z =
        F112Crit.ConjAut.conjAut V k hkN (F112Crit.ConjAut.conjAut V δ hδN z) := by
    intro z
    calc F112Crit.ConjAut.conjAut V d hdN z
        = F112Crit.ConjAut.conjAut V (k * δ) hklN z := by
          apply Additive.toMul.injective
          apply Subtype.ext
          rw [F112Crit.ConjAut.val_conjAut, F112Crit.ConjAut.val_conjAut, hd_eq]
      _ = F112Crit.ConjAut.conjAut V k hkN (F112Crit.ConjAut.conjAut V δ hδN z) := by
          apply Additive.toMul.injective
          apply Subtype.ext
          simp only [F112Crit.ConjAut.val_conjAut]
          group
  let gδ : ↥(suzukiGroup a K) := e (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)))
  have hgδφ : ∀ z : Additive ↥V, φ (F112Crit.ConjAut.conjAut V δ hδN z) = Mt gδ *ᵥ φ z := by
    intro z
    have h := hnat (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) z
    have := congrArg φ h
    simpa [gδ, AddEquiv.apply_symm_apply] using this
  have hD1NS : D1 ≤ Subgroup.normalizer (S : Set G) := by
    rw [hS1]
    refine (le_inf ?_ ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (S ⊓ L1) (Q1 L1 L2 S))
    · exact hD1.1.trans inf_le_right
    · exact (hD1.1.trans (F1.borelOf_le L1 S)).trans
        ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)))
  have hgB : gδ ∈ suzukiB a K := by
    have hmkN : QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) ∈
        Subgroup.normalizer (szSbar L1 L2 S : Set (oTwoQuot ↥(L1 ⊔ S))) :=
      quotient_mk_mem_normalizer_map (le_sup_right) hδL (hD1NS hδ)
    have heN : e (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S))) ∈
        Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K)) := by
      have h1 := Subgroup.le_normalizer_map e.toMonoidHom
        (Subgroup.mem_map_of_mem _ hmkN)
      rwa [hSmap] at h1
    rw [CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK] at heN
    exact heN
  have hδQ1 : δ ∉ Q1 L1 L2 S := by
    intro hq
    have hbot : Q1 L1 L2 S ⊓ D1 = ⊥ :=
      CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S)) hD1.2.1
    have hmem : δ ∈ Q1 L1 L2 S ⊓ D1 := Subgroup.mem_inf.mpr ⟨hq, hδ⟩
    rw [hbot] at hmem
    exact hδ1 (Subgroup.mem_bot.mp hmem)
  have hg1 : gδ ≠ 1 := by
    intro hg
    apply hδQ1
    have h1 : (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) : oTwoQuot ↥(L1 ⊔ S)) = 1 := by
      apply e.injective
      simpa [gδ] using hg
    have h2 : (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) ∈ pCore 2 ↥(L1 ⊔ S) :=
      (QuotientGroup.eq_one_iff (N := pCore 2 ↥(L1 ⊔ S))
        (x := (⟨δ, hδL⟩ : ↥(L1 ⊔ S)))).mp h1
    have h3 : δ ∈ pCoreOf 2 (L1 ⊔ S) := (F1.mem_pCore_iff_coe _).mp h2
    rwa [hpCore1] at h3
  have hδodd : Odd (orderOf δ) := by
    have h1 : orderOf δ ∣ Nat.card ↥D1 := by
      have h := orderOf_dvd_natCard (⟨δ, hδ⟩ : ↥D1)
      rwa [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hD1.2.1 h1
  have hgodd : Odd (orderOf gδ) := by
    have hdvd1 : orderOf (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) : oTwoQuot ↥(L1 ⊔ S)) ∣
        orderOf δ := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) ⟨δ, hδL⟩
      simpa [Subgroup.orderOf_mk] using h
    have hdvd2 : orderOf gδ ∣
        orderOf (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)) : oTwoQuot ↥(L1 ⊔ S)) := by
      simpa [gδ] using orderOf_map_dvd e.toMonoidHom
        (QuotientGroup.mk (⟨δ, hδL⟩ : ↥(L1 ⊔ S)))
    exact Odd.of_dvd_nat hδodd (hdvd2.trans hdvd1)
  let π : Set Nat.Primes := {p | p.val ≠ 2}
  have hBsolv : Group.IsSolvable ↥(suzukiB a K) := (suzuki_borel_solvable hK).1
  let gB : ↥(suzukiB a K) := ⟨gδ, hgB⟩
  have hgπ : IsPiSubgroup π (Subgroup.zpowers gB) := by
    intro p hp
    change p.val ≠ 2
    intro hp2
    have hdvd : p.val ∣ Nat.card (Subgroup.zpowers gB) := hp
    rw [Nat.card_zpowers] at hdvd
    have hdvd' : p.val ∣ orderOf gδ := by
      rwa [Subgroup.orderOf_mk] at hdvd
    have h2dvd : 2 ∣ orderOf gδ := by simpa [hp2] using hdvd'
    exact (Odd.not_two_dvd_nat hgodd) h2dvd
  have hTHall : IsHallSubgroup π ((suzukiT a K).subgroupOf (suzukiB a K)) := by
    refine CFSG.isHallSubgroup_of π ((suzukiT a K).subgroupOf (suzukiB a K)) ?_ ?_
    · intro p hp
      change p.val ≠ 2
      have hcardT : Nat.card ↥((suzukiT a K).subgroupOf (suzukiB a K)) =
          Nat.card (suzukiT a K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiT_le_suzukiB a K))
      have hTodd : Odd (Nat.card (suzukiT a K)) := by
        have hcard : Nat.card (suzukiT a K) = Nat.card Kˣ := by
          rw [(suzuki_borel_structure hK).2.2.1, Nat.card_units, hK]
        rw [hcard]
        exact odd_card_units hK
      exact (Odd.of_dvd_nat hTodd (by rwa [hcardT] at hp)).ne_two_of_dvd_nat
        (dvd_refl p.val)
    · intro p hp hpdiv
      change p.val ≠ 2 at hp
      have hcardT : Nat.card ↥((suzukiT a K).subgroupOf (suzukiB a K)) =
          Nat.card (suzukiT a K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suzukiT_le_suzukiB a K))
      have hindex : ((suzukiT a K).subgroupOf (suzukiB a K)).index =
          (2 ^ (2 * a + 1)) ^ 2 := by
        have h1 := Subgroup.card_mul_index ((suzukiT a K).subgroupOf (suzukiB a K))
        have hcardB : Nat.card ↥(suzukiB a K) =
            (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
          (suzuki_borel_structure hK).2.2.2.2.2.2.2
        have hcardT' : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
          (suzuki_borel_structure hK).2.2.1
        rw [hcardT, hcardT', hcardB] at h1
        have hq1 : 0 < 2 ^ (2 * a + 1) - 1 := by
          have : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
          omega
        have h1' : (2 ^ (2 * a + 1) - 1) *
            ((suzukiT a K).subgroupOf (suzukiB a K)).index =
            (2 ^ (2 * a + 1) - 1) * (2 ^ (2 * a + 1)) ^ 2 := by
          rw [h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left hq1 h1'
      have hpow : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) := by
        ring_nf
      have hpdvd : p.val ∣ (2 : ℕ) ^ (2 * (2 * a + 1)) := by
        have h := hpdiv
        rw [hindex, hpow] at h
        exact h
      have hp2 : p.val ∣ 2 := Nat.Prime.dvd_of_dvd_pow p.2 hpdvd
      have hpeq : p.val = 2 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp hp2
      exact hp hpeq
  obtain ⟨H, hHHall, hgH⟩ := CFSG.SolvableHall.solvable_hall_containment hBsolv π
    (Subgroup.zpowers gB) hgπ
  obtain ⟨v, hv⟩ := CFSG.GroupTheory.SteinbergBK.solvable_hall_conjugacy hBsolv
    hTHall hHHall
  have hgHmem : gB ∈ H := hgH (Subgroup.mem_zpowers gB)
  have hgConj : gB ∈ CFSG.conjugate ((suzukiT a K).subgroupOf (suzukiB a K)) v := by
    simpa [hv] using hgHmem
  obtain ⟨t, htT, ht_eq⟩ := Subgroup.mem_map.mp hgConj
  have ht_eq' : (v : ↥(suzukiB a K))⁻¹ * t * (v : ↥(suzukiB a K)) =
      ⟨gδ, hgB⟩ := by
    simpa [CFSG.conjugate, MulAut.conj_apply] using ht_eq
  let t0 : ↥(suzukiGroup a K) := (t : ↥(suzukiB a K))
  let vv : ↥(suzukiGroup a K) := (v : ↥(suzukiB a K))
  have ht0T : t0 ∈ suzukiT a K := Subgroup.mem_subgroupOf.mp htT
  have ht0_eq : t0 = vv * gδ * vv⁻¹ := by
    have h : vv⁻¹ * t0 * vv = gδ := by
      simpa [t0, vv] using congrArg Subtype.val ht_eq'
    calc t0 = vv * (vv⁻¹ * t0 * vv) * vv⁻¹ := by group
      _ = vv * gδ * vv⁻¹ := by rw [h]
  have ht01 : t0 ≠ 1 := by
    intro h
    apply hg1
    have h1 : vv * gδ * vv⁻¹ = 1 := by rw [← ht0_eq, h]
    calc gδ = vv⁻¹ * (vv * gδ * vv⁻¹) * vv := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨l, hl⟩ := (mem_suzukiT_iff).1 ht0T
  have hl1 : l ≠ 1 := by
    intro h
    apply ht01
    rw [← hl, h, suzukiDElt_one]
  obtain ⟨x, hx⟩ := e.surjective vv
  obtain ⟨hv, rfl⟩ := QuotientGroup.mk_surjective x
  let cv : Additive ↥V ≃+ Additive ↥V := F112Crit.ConjAut.conjAut V (hv : G) (hHZ1 hv.2)
  have hcvφ : ∀ z : Additive ↥V, φ (cv z) = Mt vv *ᵥ φ z := by
    intro z
    have h := hnat hv z
    have := congrArg φ h
    simpa [cv, AddEquiv.apply_symm_apply, ← hx] using this
  have hMmul : ∀ x y : ↥(suzukiGroup a K), M (x * y) = M x * M y := by
    intro x y
    simp [M, Matrix.GeneralLinearGroup.coe_mul]
  have ht0vv : t0 * vv = vv * gδ := by
    rw [ht0_eq]
    group
  have hmat : Mt t0 * Mt vv = Mt vv * Mt gδ := by
    calc Mt t0 * Mt vv = (M (t0 * vv)).map (· ^ 2 ^ c) := by
          rw [hMmul]
          exact (matrix_map_pow_mul c (M t0) (M vv)).symm
      _ = (M (vv * gδ)).map (· ^ 2 ^ c) := by rw [ht0vv]
      _ = Mt vv * Mt gδ := matrix_map_pow_mul c (M vv) (M gδ)
  have hcvδ : ∀ z : Additive ↥V, φ (cv (F112Crit.ConjAut.conjAut V δ hδN z)) =
      Mt t0 *ᵥ φ (cv z) := by
    intro z
    calc φ (cv (F112Crit.ConjAut.conjAut V δ hδN z))
        = Mt vv *ᵥ φ (F112Crit.ConjAut.conjAut V δ hδN z) := hcvφ _
      _ = Mt vv *ᵥ (Mt gδ *ᵥ φ z) := by rw [hgδφ z]
      _ = (Mt vv * Mt gδ) *ᵥ φ z := Matrix.mulVec_mulVec (φ z) (Mt vv) (Mt gδ)
      _ = (Mt t0 * Mt vv) *ᵥ φ z := by rw [hmat]
      _ = Mt t0 *ᵥ (Mt vv *ᵥ φ z) := (Matrix.mulVec_mulVec (φ z) (Mt t0) (Mt vv)).symm
      _ = Mt t0 *ᵥ φ (cv z) := by rw [hcvφ z]
  have hcv_scalar : ∀ z : Additive ↥V, φ (cv (F112Crit.ConjAut.conjAut V k hkN z)) =
      μ • φ (cv z) := by
    intro z
    calc φ (cv (F112Crit.ConjAut.conjAut V k hkN z))
        = Mt vv *ᵥ φ (F112Crit.ConjAut.conjAut V k hkN z) := hcvφ _
      _ = Mt vv *ᵥ (μ • φ z) := by
            rw [show φ ((F112Crit.ConjAut.conjAut V k hkN) z) = μ • φ z from by
              simpa [y] using hμ z]
      _ = μ • (Mt vv *ᵥ φ z) := Matrix.mulVec_smul (Mt vv) μ (φ z)
      _ = μ • φ (cv z) := by rw [hcvφ z]
  have hcv_d : ∀ z : Additive ↥V,
      φ (cv (F112Crit.ConjAut.conjAut V d hdN z)) =
        μ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ φ (cv z)) := by
    intro z
    calc φ (cv (F112Crit.ConjAut.conjAut V d hdN z))
        = φ (cv (F112Crit.ConjAut.conjAut V k hkN (F112Crit.ConjAut.conjAut V δ hδN z))) := by
          rw [hcd z]
      _ = μ • φ (cv (F112Crit.ConjAut.conjAut V δ hδN z)) := hcv_scalar _
      _ = μ • (Mt t0 *ᵥ φ (cv z)) := by rw [hcvδ z]
      _ = μ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ φ (cv z)) := by
            rw [← hl]
            simp [Mt, M, coe_suzukiDElt]
  have hYcd : ∀ z : Additive ↥V, (z.toMul : G) ∈
      (V ⊓ Subgroup.centralizer ({d} : Set G)) ↔ F112Crit.ConjAut.conjAut V d hdN z = z := by
    intro z
    constructor
    · intro hz
      have hzC : (z.toMul : G) ∈ Subgroup.centralizer ({d} : Set G) :=
        (Subgroup.mem_inf.mp hz).2
      have h := (Subgroup.mem_centralizer_iff.mp hzC) d (by simp)
      apply Additive.toMul.injective
      apply Subtype.ext
      show d * (z.toMul : G) * d⁻¹ = (z.toMul : G)
      rw [h]
      group
    · intro hcd
      refine Subgroup.mem_inf.mpr ⟨z.toMul.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxd : x = d := by simpa using hx
      subst x
      have h : d * (z.toMul : G) * d⁻¹ = (z.toMul : G) := by
        rw [← F112Crit.ConjAut.val_conjAut V d hdN z, hcd]
      calc d * (z.toMul : G) = (d * (z.toMul : G) * d⁻¹) * d := by group
        _ = (z.toMul : G) * d := by rw [h]
  have hiff : ∀ z : Additive ↥V, (z.toMul : G) ∈
      (V ⊓ Subgroup.centralizer ({d} : Set G)) ↔
      (suzukiD a l).map (· ^ 2 ^ c) *ᵥ φ (cv z) = μ⁻¹ • φ (cv z) := by
    intro z
    rw [hYcd z]
    constructor
    · intro hcd
      have h1 : φ (cv (F112Crit.ConjAut.conjAut V d hdN z)) = φ (cv z) := by rw [hcd]
      rw [hcv_d z] at h1
      calc (suzukiD a l).map (· ^ 2 ^ c) *ᵥ φ (cv z) =
            μ⁻¹ • (μ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ φ (cv z))) := by
              rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • φ (cv z) := by rw [h1]
    · intro heig
      apply cv.injective
      apply φ.injective
      rw [hcv_d z, heig, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hbound : Nat.card {v : Fin 4 → K //
      (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = μ⁻¹ • v} ≤ Nat.card K :=
    card_eigenspace_suzukiD_map_pow_le hK hl1 c (μ⁻¹)
  let eY : {z : Additive ↥V // (z.toMul : G) ∈
      (V ⊓ Subgroup.centralizer ({d} : Set G))} ≃
      ↥(V ⊓ Subgroup.centralizer ({d} : Set G)) :=
  { toFun := fun z => (⟨(z.1.toMul : G), z.2⟩ : ↥(V ⊓ Subgroup.centralizer ({d} : Set G)))
    invFun := fun h => (⟨Additive.ofMul
      (⟨(h : G), (Subgroup.mem_inf.mp h.2).1⟩ : ↥V), h.2⟩ :
        {z : Additive ↥V // (z.toMul : G) ∈
          (V ⊓ Subgroup.centralizer ({d} : Set G))})
    left_inv := fun z => by
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl
    right_inv := fun h => by
      apply Subtype.ext
      rfl }
  have hcardY : Nat.card ↥(V ⊓ Subgroup.centralizer ({d} : Set G)) =
      Nat.card {z : Additive ↥V // (z.toMul : G) ∈
        (V ⊓ Subgroup.centralizer ({d} : Set G))} :=
    (Nat.card_congr eY).symm
  have hcardEq : Nat.card {z : Additive ↥V // (z.toMul : G) ∈
        (V ⊓ Subgroup.centralizer ({d} : Set G))} =
      Nat.card {v : Fin 4 → K //
        (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = μ⁻¹ • v} :=
    Nat.card_congr (Equiv.subtypeEquiv (cv.trans φ).toEquiv (fun z => hiff z))
  calc Nat.card ↥(V ⊓ Subgroup.centralizer ({d} : Set G))
      = Nat.card {z : Additive ↥V // (z.toMul : G) ∈
          (V ⊓ Subgroup.centralizer ({d} : Set G))} := hcardY
    _ = Nat.card {v : Fin 4 → K //
          (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = μ⁻¹ • v} := hcardEq
    _ ≤ Nat.card K := hbound
    _ = 2 ^ (2 * a + 1) := hK


end CFSG.Quasithin.Stroth

end
