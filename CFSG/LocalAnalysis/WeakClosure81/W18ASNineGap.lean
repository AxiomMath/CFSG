module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNine
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def NoSocle185Factor (Y : Type) [Group Y] : Prop :=
  ∀ (T : Type) [Group T], Socle185Shape T → ¬ E1.IsCompositionFactor Y T

namespace NoSocle185Factor

theorem of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : NoSocle185Factor Y) :
    NoSocle185Factor Y' :=
  fun T _ hT hcf => h T hT ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hcf)

theorem of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (h : NoSocle185Factor X) : NoSocle185Factor Y :=
  fun T _ hT hcf =>
    h T hT (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective f hf hcf)

theorem of_normal {Y : Type} [Group Y] (A : Subgroup Y) [A.Normal] (hA : NoSocle185Factor ↥A)
    (hQ : NoSocle185Factor (Y ⧸ A)) : NoSocle185Factor Y :=
  fun T _ hT hcf => (isCompositionFactor_of_normal A hcf).elim (hA T hT) (hQ T hT)

theorem of_commute {Y : Type} [Group Y] [Finite Y] (h : ∀ a b : Y, a * b = b * a) :
    NoSocle185Factor Y := by
  intro T _ hT hcf
  haveI := isCompositionFactor_finite hcf
  obtain ⟨a, b, hab⟩ := hT.exists_not_commute
  exact hab (isCompositionFactor_commute h hcf a b)

theorem of_commutator {Y : Type} [Group Y] [Finite Y] (h : NoSocle185Factor ↥(commutator Y)) :
    NoSocle185Factor Y :=
  of_normal (commutator Y) h (of_commute fun a b => mul_comm (G := Abelianization Y) a b)

theorem of_index_two {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) (hidx : A.index = 2)
    (hA : NoSocle185Factor ↥A) : NoSocle185Factor Y := by
  haveI : A.Normal := Subgroup.normal_of_index_eq_two hidx
  refine of_normal A hA (of_commute ?_)
  haveI : Fact (Nat.card (Y ⧸ A)).Prime :=
    ⟨by rw [← Subgroup.index_eq_card, hidx]; exact Nat.prime_two⟩
  haveI : IsCyclic (Y ⧸ A) := isCyclic_of_prime_card rfl
  exact fun a b => (IsCyclic.commGroup (α := Y ⧸ A)).mul_comm a b

theorem of_not_dvd {Y : Type} [Group Y] [Finite Y]
    (h : ∀ (T : Type) [Group T], Socle185Shape T → ¬ Nat.card T ∣ Nat.card Y) :
    NoSocle185Factor Y :=
  fun T _ hT hcf => h T hT (isCompositionFactor_natCard_dvd hcf)

theorem of_isSimpleGroup {Y : Type} [Group Y] [IsSimpleGroup Y]
    (h : ∀ (T : Type) [Group T], Socle185Shape T → IsEmpty (Y ≃* T)) : NoSocle185Factor Y :=
  fun T _ hT hcf => (h T hT).false (isCompositionFactor_mulEquiv_of_isSimpleGroup hcf).some

end NoSocle185Factor

private theorem odd_natCard_fusionOddCore' (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem tail189TwoNoSection_of_families
    (hEven : ∀ (T : Type) [Group T], Socle185Shape T → 2 ∣ Nat.card T)
    (hSp : ∀ (Y : Type) [Group Y] (m n : ℕ), IsSpGp Y m n → NoSocle185Factor Y)
    (hU : ∀ (Y : Type) [Group Y] (m n : ℕ), IsPSUGp Y m n → NoSocle185Factor Y)
    (hOrth : ∀ (Y : Type) [Group Y] (m n : ℕ), IsOrthGp Y m n → NoSocle185Factor Y)
    (hWr : ∀ (Y : Type) [Group Y] (n m : ℕ), IsL2WrSymGp Y n m → NoSocle185Factor Y)
    (hSym : ∀ (Y : Type) [Group Y] (m : ℕ), IsSymGp Y m → NoSocle185Factor Y)
    (hSix : ∀ (Y : Type) [Group Y], IsOrth6MinusMod Y → NoSocle185Factor Y) :
    Tail189TwoNoSection := by
  intro X _ _ S halt
  have hX : NoSocle185Factor X := by
    rcases halt with ⟨-, m, n, hc⟩ | ⟨-, n, hn⟩ | ⟨-, hX⟩
    · refine NoSocle185Factor.of_normal (Subgroup.center X)
        (NoSocle185Factor.of_commute fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1))
        ?_
      rcases hc with ⟨hY, -⟩ | ⟨hY, -⟩ | hY | hY
      · exact hSp _ m n hY
      · exact hU _ m n hY
      · exact hOrth _ m n hY
      · exact hWr _ n m hY
    · refine NoSocle185Factor.of_normal (fusionOddCore X) ?_ (hSym _ n hn)
      refine NoSocle185Factor.of_not_dvd fun T _ hT hdvd => ?_
      have h2 : 2 ∣ Nat.card (fusionOddCore X) := (hEven T hT).trans hdvd
      exact (Nat.not_even_iff_odd.mpr (odd_natCard_fusionOddCore' X)) (even_iff_two_dvd.mpr h2)
    · obtain ⟨Y, _, φ, hφ, -, hker, hY⟩ := hX
      refine NoSocle185Factor.of_normal φ.ker
        (NoSocle185Factor.of_commute fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) a.1)) ?_
      exact NoSocle185Factor.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm
        (hSix Y hY)
  exact fun T _ hT => hX T hT

end CFSG.LocalAnalysis.WeakClosure81

end
