module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Parity
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSE
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCover
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

private theorem ggR1Sp_labelIso {lab lab' : LargeEvenLabel} (ht : lab.tag = .E8)
    (h : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only at ht
  subst ht
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  all_goals simp_all

private theorem ggR1Sp_largeEvenSplit {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .E8)
    (hn : 2 ≤ lab.n) : LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hn
  have hn1 : n ≠ 1 := by omega
  subst ht
  simp [LargeEvenSplit, LargeEvenUntwisted, hn1]

theorem ggInnerDiagOnLabel_r1Par_of_rowR1E8 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E8 p lab) p Bs L) :
    GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E8 p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  have heq : labs = lab1 := ggR1Sp_labelIso hrow hiso
  have hrow' : GGTBRowR1E8 p labs := by rw [heq]; exact hrow
  have hq' : 2 ≤ labs.n := by rw [heq]; exact hQ4
  have hbad : GGLabQFour p labs ∧ GGTBRowR1E8 p labs ∧ p ∣ 2 ^ labs.n - 1 :=
    ⟨by unfold GGLabQFour; exact hq', hrow', (ggR1Sp_largeEvenSplit hrow' hq').mp hPs.1⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabs hhass
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

section Presentation

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenTag modelUniv_eq
  lieModel_unique_even)

private theorem ggR1Sp_of_lieModel
    {G : Type} [Group G] [Finite G] {p : ℕ} {K : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    (hp : p.Prime) (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hpf : p ∣ 2 ^ f - 1) [Finite (ggU t n f).K]
    (hsplit : 2 ≤ f → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU t n f).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : (ggU t n f).K →* E, ∀ g, π (s g) = g)
    (hK : commutator ↥K = ⊤) (hX : LieModel (↥K ⧸ Subgroup.center ↥K) t n 2 f) :
    ∃ ψ : (ggU t n f).K →* G, StatedLieAdmissible t n 2 f ∧
      ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = K ∧ p ∣ 2 ^ f - 1 := by
  have hadm := hX.admissible
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by have := hadm.2.1; omega
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpf))
  have hev : EvenTag t := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hiso : ∀ M : LieUniversal, M = ggU t n f →
      LieModel (M.K ⧸ Subgroup.center M.K) t n 2 f →
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := by
    rintro M rfl hY
    exact lieModel_unique_even hev hX hY
  obtain ⟨φ, hφ, hker⟩ := ggExists_universal_cover_of_marking hK
    (hiso _ (modelUniv_eq hev n 2 f Nat.prime_two)
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 f Nat.prime_two hev.isFundTag
        hadm).2)
    fun E _ _ π hπ hc => (hsplit hf E π hπ hc).imp fun s hs => MonoidHom.ext hs
  refine ⟨K.subtype.comp φ, hadm,
    fun x hx => hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hx))), ?_, hpf⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end Presentation

theorem ggR1E8_splitLie_tagged
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} (hp : p.Prime)
    (hL : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E8 p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∃ (n f : ℕ) (ψ : (ggU .E8 n f).K →* G), StatedLieAdmissible .E8 n 2 f ∧
      ψ.ker ≤ Subgroup.center (ggU .E8 n f).K ∧ ψ.range = L ∧ p ∣ 2 ^ f - 1 := by
  have h : StandardType.LargeEvenMarking ↥L (fun lab _ _ _ _ _ => ggRowP_SE8 p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2.1, hP.1.2.2⟩) hL
  obtain ⟨⟨tag, _, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ := largeEvenMarking_exists_markedModel h
  obtain ⟨rfl, hpn⟩ : tag = .E8 ∧ p ∣ 2 ^ n - 1 := hrow
  haveI : Finite (ggU .E8 0 n).K := by
    have : Finite (Module.End (GaloisField 2 n)
        (CFSG.Blueprint.Chevalley.RootModule .E8 (GaloisField 2 n))) :=
      Module.finite_of_finite (GaloisField 2 n)
    change Finite (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 n))
    infer_instance
  have hsec : 2 ≤ n → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU .E8 0 n).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : (ggU .E8 0 n).K →* E, ∀ g, π (s g) = g := by
    intro hf E _ _ π hπ hcen
    have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact CFSG.LieType.Steinberg.CentralExt.FieldFour.e8_four_exists_section hc E π hπ hcen
    · have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
      exact CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_exists_section_of_central
        (by omega) hπ hcen
  obtain ⟨ψ, hψ⟩ := ggR1Sp_of_lieModel (t := .E8) (n := 0) hp
    (.inr (.inr (.inr (.inr rfl)))) hpn hsec h.1 (MarkedModel.of_mulEquiv θ.symm hm)
  exact ⟨0, n, ψ, hψ⟩

end CFSG.StandardType

end
