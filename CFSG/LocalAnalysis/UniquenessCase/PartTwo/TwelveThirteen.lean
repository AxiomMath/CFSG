module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem twelve_thirteen (D : Data G) (h63 : UC6.R6_3 D) (h126 : R126 D) (h127 : R127 D)
    (h1211 : R1211_1 D) (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : Nat.card V₀ < 8 → MBarGT D.M V₀ V (D.k + 1))
    {X : Subgroup G} {n : ℕ} (hXsn : CFSG.Open.IsSubnormal X (X ⊔ D.T)) (hXM : X ⊔ D.T ≤ D.M)
    (hXA : Nonempty (Bar2 X ≃* alternatingGroup (Fin n)))
    (hP : ∀ P : Subgroup G, P ≤ X ⊔ D.T → IsPGroup 3 P → ¬ IsCyclic P →
      (∀ x ∈ P, x ^ 3 = 1) → ⁅⁅P, P⁆, P⁆ = ⊥ → Permutes P D.T → F11.InP11 D P) :
    (n = 8 → CFSG.Blueprint.LieModel (Bar2 (X ⊔ D.T)) .PSL 4 2 1 ∧ V₀ = ⊥ ∧
      MBarGT D.M V₀ V (D.k + 1) ∧ ¬ MBarGT D.M V₀ V (D.k + 2)) ∧ n ≤ 9 := by
  by_cases hn : n < 8
  · exact ⟨fun h8 => absurd h8 (by omega), by omega⟩
  have hn8 : 8 ≤ n := by omega
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T (X ⊔ D.T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.ABGLocalTools.isSylowOf_iff.2 (TwelveShort.isSylowIn_of_le D le_sup_right)
  obtain ⟨P, hPH, hPe, hP9, hPT, hPirr⟩ :=
    TwelveThirteen.exists_three_subgroup hn8 hXsn hTH hXA
  have hP3 : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hPe.2 x x.2)⟩
  have hPnc : ¬ IsCyclic P := by
    intro hcyc
    have h1 : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hPe.2 x x.2)
    rw [IsCyclic.exponent_eq_card] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hcl : ⁅⁅P, P⁆, P⁆ = ⊥ := by
    have hPP : ⁅P, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hPe.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hPP, Subgroup.commutator_bot_left]
  have hPin : F11.InP11 D P := hP P hPH hP3 hPnc (fun x hx => hPe.2 x hx) hcl hPT
  have hV8 : Nat.card V₀ < 8 := by
    by_contra h8
    exact ((twelve_nine D h127 h).2 (by omega)).2 P hPin
  have hmk := hm hV8
  have hstar := twelve_twelve D h63 h126 h1211 h111 h6161ii h hmk P
  have hV0 : V₀ = ⊥ := by
    by_contra hne
    exact hstar ((inPStar_iff_of_ne_bot hne P).2 hPin)
  have hnot : ¬ (9 < Nat.card P ∨ IrrOn (normalizer (P : Set G) ⊓ D.T) P) := by
    rintro (hbig | hirr)
    · exact hstar ⟨hPin, fun _ => ⟨3, Nat.prime_three, hP3, Or.inl (by omega)⟩⟩
    · refine hstar ⟨hPin, fun _ => ⟨3, Nat.prime_three, hP3, Or.inr (Or.inr ?_)⟩⟩
      intro W hW hN
      exact hirr W hW (le_trans (inf_le_inf_left _ le_normalizer) hN)
  have hcase : ¬ (10 ≤ n ∨ X ⊔ D.T ≠ X ⊔ pCoreOf 2 (X ⊔ D.T)) := fun hc => hnot (hPirr hc)
  refine ⟨fun h8 => ⟨?_, hV0, hmk, twelve_eleven_two D h63 h126 h111 h ⟨P, hPin⟩ hV0⟩, ?_⟩
  · have hH : X ⊔ D.T = X ⊔ pCoreOf 2 (X ⊔ D.T) := by
      by_contra hne
      exact hcase (Or.inr hne)
    obtain ⟨e₁⟩ := TwelveThirteen.nonempty_bar2_mulEquiv_of_eq hXsn hH
    obtain ⟨e₂⟩ := hXA
    subst h8
    exact (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2
      ⟨e₁.trans e₂⟩
  · by_contra h9
    exact hcase (Or.inl (by omega))

theorem twelve_thirteen_two (D : Data G) (h63 : UC6.R6_3 D) (h126 : R126 D) (h127 : R127 D)
    (h1211 : R1211_1 D) (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : Nat.card V₀ < 8 → MBarGT D.M V₀ V (D.k + 1))
    {X : Subgroup G} {n : ℕ} (hXsn : CFSG.Open.IsSubnormal X (X ⊔ D.T)) (hXM : X ⊔ D.T ≤ D.M)
    (hXA : Nonempty (Bar2 X ≃* alternatingGroup (Fin n)))
    (hP : ∀ P : Subgroup G, P ≤ X ⊔ D.T → IsPGroup 3 P → ¬ IsCyclic P →
      (∀ x ∈ P, x ^ 3 = 1) → ⁅⁅P, P⁆, P⁆ = ⊥ → Permutes P D.T → F11.InP11 D P) :
    n ≤ 9 :=
  (twelve_thirteen D h63 h126 h127 h1211 h111 h6161ii h hm hXsn hXM hXA hP).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
