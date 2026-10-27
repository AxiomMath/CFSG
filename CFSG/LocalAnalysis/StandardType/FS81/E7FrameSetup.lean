module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalModelE7
public import CFSG.LocalAnalysis.StandardType.FS81.WeakClosureFusion
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutE7
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.RootCoreE7
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvE7Off
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNative

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}

section Certs


theorem fus42_of_std (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G (Row.E7.n + 1)}
    (hB : Adapted B b₀ K E) : Fus42 B b₀ := by
  obtain ⟨B₁, hB₁, hloc⟩ := l1LocalAt_E7 G b₀ K E hstd
  have h := l1Fus42_holds G b₀ K E Row.E7 hstd B₁ hB₁ hloc
  unfold Fus42 at h ⊢
  rw [hB.1, ← hB₁.1]
  exact h

theorem card_realized_centralizer (hstd : StdAssumptions b₀ K E Row.E7)
    {B : Basis3 G (Row.E7.n + 1)} (hB : Adapted B b₀ K E) :
    Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040 := by
  obtain ⟨B₁, hB₁, hloc⟩ := l1LocalAt_E7 G b₀ K E hstd
  rw [Basis3.card_realized_eq_of_span_eq (hB.1.trans hB₁.1.symm)]
  exact hloc.1

theorem exists_R (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G (Row.E7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) ∧
      R ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨R, hRC, hRn, hR3, hdec⟩ := rowCentAt_E7 G b₀ K E hstd B hB hrec (fus42_of_std hstd hB)
  obtain ⟨-, ⟨⟨hb₀3, hKC, hKn, hKz, -, -, -, -⟩, -⟩, hrow'⟩ := hstd
  have hrow : IsRow Row.E7 K := hrow'.1
  have hKs : IsSimpleGroup ↥K := e7_isSimpleGroup hrow hKz
  have hK3 : 3 ∣ Nat.card K := by
    obtain ⟨-, -, -, -, hAcard, -⟩ := hrow'
    have h3 : 3 ∣ Nat.card ↥(E ⊓ K) := by
      rw [hAcard]
      exact dvd_pow_self 3 (by decide)
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
  exact ⟨R, hRC, hRn, hR3, hdec, le_centralizer_of_normal_threePrime hKs hK3 hKC hKn hRC hRn hR3⟩

theorem exists_model (hstd : StdAssumptions b₀ K E Row.E7) :
    Nonempty (↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) := by
  obtain ⟨-, ⟨⟨-, -, -, hKz, -, -, -, -⟩, -⟩, hrow, -⟩ := hstd
  obtain ⟨lab, hlabP, hlab⟩ := exists_glaLabel hrow
  obtain ⟨t, r, n⟩ := lab
  have hn1 : n = 1 := hlabP.1
  subst hn1
  have ht : t = .E7 := by
    obtain ⟨-, hcases⟩ := hlabP
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hKz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod,
      GaloisField.card 2 1 (by omega)]
    norm_num
  exact ⟨(φ.trans (CFSG.TauCetiBridge.adjointGroupCongr
    (FiniteField.ringEquivOfCardEq hcard))).symm⟩

end Certs

end CFSG.StandardType.FrameRoute.FS81.E7Frame
