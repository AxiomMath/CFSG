module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCover
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenTag modelUniv_eq
  lieModel_unique_even)

private theorem ggTBRowR1E7_labelIso {p : ℕ} {lab lab' : LargeEvenLabel}
    (ht : GGTBRowR1E7 p lab) (h : GGLabelIso lab lab') :
    lab'.n = lab.n ∧ GGTBRowR1E7 p lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGTBRowR1E7 at ht ⊢
  simp only at ht ⊢
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · injection h with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, ht⟩
  · obtain ⟨hb, -⟩ := h
    rcases hb with hb | hb <;> simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    injection h2 with h2a h2b h2c
    subst h2a
    simp_all

private theorem ggTBRowR1E7_largeEvenSplit {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGTBRowR1E7 p lab) (hn : 2 ≤ lab.n) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGTBRowR1E7 at ht
  simp only at ht hn
  have hn1 : n ≠ 1 := by omega
  subst ht
  simp [LargeEvenSplit, LargeEvenUntwisted, hn1]

theorem ggInnerDiagOnLabel_r1Par_of_rowR1E7 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E7 p lab) p Bs L) :
    GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E7 p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  obtain ⟨hn', hrow'⟩ := ggTBRowR1E7_labelIso hrow hiso
  have hbad : GGLabQFour p labs ∧ GGTBRowR1E7 p labs ∧ p ∣ 2 ^ labs.n - 1 := by
    have hq' : 2 ≤ labs.n := by rw [hn']; exact hQ4
    exact ⟨by unfold GGLabQFour; exact hq', hrow',
      (ggTBRowR1E7_largeEvenSplit hrow' hq').mp hPs.1⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabs hhass
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

theorem ggR1E7_splitLie_tagged
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} (hp : p.Prime)
    (h : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1E7 p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∃ (n f : ℕ) (ψ : (ggU .E7 n f).K →* G), StatedLieAdmissible .E7 n 2 f ∧
      ψ.ker ≤ Subgroup.center (ggU .E7 n f).K ∧ ψ.range = L ∧ p ∣ 2 ^ f - 1 := by
  have h' : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => ggRowP_SE7 p lab) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hP.1.2.1, hP.1.2.2⟩) h
  obtain ⟨⟨tag, _, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ :=
    largeEvenMarking_exists_markedModel h'
  obtain ⟨rfl, hpn⟩ : tag = .E7 ∧ p ∣ 2 ^ n - 1 := hrow
  haveI : Finite (ggU .E7 0 n).K :=
    FieldFour.finite_minGroup' (K := GaloisField 2 n) e7Data_valid
  have hX : LieModel (↥L ⧸ Subgroup.center ↥L) .E7 0 2 n :=
    MarkedModel.of_mulEquiv θ.symm hm
  have hadm := hX.admissible
  have hf : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by have := hadm.2.1; omega
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpn))
  have hev : EvenTag .E7 := by trivial
  have hsplit : 2 ≤ n → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU .E7 0 n).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : (ggU .E7 0 n).K →* E, ∀ g, π (s g) = g := by
    intro hf E _ _ π hπ hcen
    have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact FieldFour.e7_four_exists_section hc E π hπ hcen
    · have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
      exact MinusculeClosed.e7_exists_section_of_central (by omega) hπ hcen
  have hiso : ∀ M : LieUniversal, M = ggU .E7 0 n →
      LieModel (M.K ⧸ Subgroup.center M.K) .E7 0 2 n →
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (ggU .E7 0 n).K ⧸
          Subgroup.center (ggU .E7 0 n).K) := by
    rintro M rfl hY
    exact lieModel_unique_even hev hX hY
  obtain ⟨φ, hφ, hker⟩ := ggExists_universal_cover_of_marking h'.1
    (hiso _ (modelUniv_eq hev 0 2 n Nat.prime_two)
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .E7 0 2 n Nat.prime_two hev.isFundTag
        hadm).2)
    fun E _ _ π hπ hc => (hsplit hf E π hπ hc).imp fun s hs => MonoidHom.ext hs
  refine ⟨0, n, L.subtype.comp φ, hadm, ?_, ?_, hpn⟩
  · intro x hx
    exact hker (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hx)))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

end CFSG.StandardType

end
