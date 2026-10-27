module

public import CFSG.Quasithin.EmptyFaithful.S153DGen4
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4.G

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_mem_pCore {X : Subgroup G} {x : ↥X} (hx : x ∈ CFSG.pCore 2 ↥X) :
    (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).mpr hx

theorem pCoreOf_le_of_isMSPair {G₀ R : Subgroup G} (hMS : IsMSPair G₀ R) : pCoreOf 2 G₀ ≤ R := by
  rcases hMS.2.1 with ⟨H', hlt, hodd, hR⟩ | ⟨-, hle, -⟩
  · obtain ⟨S, hS⟩ := exists_isSylowTwoOf H'
    have hSG : IsSylowTwoOf S G₀ := by
      refine ⟨hS.le.trans hlt.le, hS.isPGroup, fun hdvd => ?_⟩
      have h1 := Subgroup.relIndex_mul_relIndex S H' G₀ hS.le hlt.le
      have h2 : 2 ∣ S.relIndex H' * H'.relIndex G₀ := by rw [h1]; exact hdvd
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
      · exact hS.2.2 h
      · exact hodd h
    calc pCoreOf 2 G₀ ≤ pCoreOf 2 H' :=
          F7.pCoreOf_le_pCoreOf_of_isSylowTwoOf hSG hS.le hlt.le
      _ = R := hR.symm
  · exact hle

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem pCoreOf_le_pCoreOf_sup (c : P4Ctx T Mc M H B₀ I X) :
    pCoreOf 2 X ≤ pCoreOf 2 (X ⊔ P4R M I) := by
  refine le_pCoreOf_of_le_normalizer 2 (pCoreOf_le 2 X |>.trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 X)
  refine sup_le (le_normalizer_pCoreOf 2 X) fun r hr => ?_
  exact normalizer_le_normalizer_pCoreOf 2 X (c.R_norm hr)

theorem pCoreOf_le_inf (c : P4Ctx T Mc M H B₀ I X) (hMS : IsMSPair (X ⊔ P4R M I) (P4R M I)) :
    pCoreOf 2 X ≤ M ⊓ I ⊓ X :=
  le_inf ((pCoreOf_le_pCoreOf_sup c).trans ((pCoreOf_le_of_isMSPair hMS).trans (pCoreOf_le 2 _)))
    (pCoreOf_le 2 X)

theorem pCoreOf_le_centralizer (c : P4Ctx T Mc M H B₀ I X) :
    pCoreOf 2 X ≤ Subgroup.centralizer (P4V M I X : Set G) :=
  (pCoreOf_le_pCoreOf_sup c).trans (c.c27.1.1.trans inf_le_right)

theorem exists_ne_one_statedSL (F : Type) [Field F] :
    ∃ y : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), y ≠ 1 := by
  refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)), ?_⟩
  intro h
  have h1 := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).injective
    (h.trans (map_one _).symm)
  have h2 := congr_arg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
    (A : Matrix (Fin 3) (Fin 3) F) 0 1) h1
  simp [Matrix.SpecialLinearGroup.transvection_coe] at h2

omit [Finite G] in
theorem le_normalizer_V (X : Subgroup G) (M I : Subgroup G) :
    X ≤ Subgroup.normalizer (P4V M I X : Set G) := SBc17.le_normalizer_V X (P4R M I)

omit [Finite G] in
theorem not_le_centralizer_V {F : Type} [Field F]
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    ¬ X ≤ Subgroup.centralizer (P4V M I X : Set G) := by
  intro hX
  obtain ⟨φ⟩ := e
  obtain ⟨y, hy⟩ := exists_ne_one_statedSL F
  apply hy
  have h1 : φ.symm y = 1 := by
    apply Subtype.ext
    obtain ⟨x, hx, hxX, hxa⟩ := mem_autOn_iff_exists.mp (φ.symm y).2
    rw [← hxa]
    exact A4.conjAct_eq_one_iff.mpr (hX hxX)
  simpa using congrArg φ h1

theorem inf_centralizer_eq_pCoreOf (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    X ⊓ Subgroup.centralizer (P4V M I X : Set G) = pCoreOf 2 X := by
  have hXN := le_normalizer_V X M I
  have hker := pCoreOf_le_centralizer c
  have hsq : SQTKGroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    S153D.sqtkGroup_quot_pCore (IsSQTKIn.mono c.hyp.sqtk c.X_le_I)
  have hH : IsL345Type ↥(autOn X (P4V M I X)) :=
    Or.inl ⟨n, F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF], e⟩
  obtain ⟨φ⟩ := S153D.nonempty_quot_mulEquiv_autOn hcover hXN c.quasi hsq hker
    (not_le_centralizer_V e) hH
  have hinj : Function.Injective (S153D.autOnQuot hXN hker) :=
    (Finite.injective_iff_surjective_of_equiv φ.toEquiv).mpr (S153D.autOnQuot_surjective hXN hker)
  refine le_antisymm (fun x hx => ?_) (le_inf (pCoreOf_le 2 X) hker)
  have h1 : S153D.autOnQuot hXN hker (QuotientGroup.mk (⟨x, hx.1⟩ : ↥X)) = 1 :=
    (S153D.autOnHom_eq_one_iff hXN ⟨x, hx.1⟩).mpr hx.2
  have h2 : (QuotientGroup.mk (⟨x, hx.1⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 := by
    apply hinj
    rw [h1, map_one]
  exact mem_pCoreOf_of_mem_pCore ((QuotientGroup.eq_one_iff _).mp h2)

end S15223P4.G

end CFSG.Quasithin
