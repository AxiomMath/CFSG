module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Parity
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSD
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCover
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGTBRowR1AD (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGTBRowR1A p lab ∧ ¬ p ∣ lab.rank + 1) ∨ GGTBRowR1D p lab

private theorem ggR1ADs_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 3 + 1 := by
  rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

private theorem ggR1ADs_labelIso {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab lab' : LargeEvenLabel}
    (ht : GGTBRowR1AD p lab) (h : GGLabelIso lab lab') : lab'.n = lab.n ∧ GGTBRowR1AD p lab' := by
  have h4 : ¬ p ∣ 3 + 1 := ggR1ADs_not_dvd_four hp hp2
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGTBRowR1AD GGTBRowR1A GGTBRowR1D at ht ⊢
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · injection h with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, ht⟩
  · obtain ⟨hb, -⟩ := h
    rcases hb with hb | hb <;> simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    injection h2 with h2a h2b h2c
    subst h1a; subst h2a; subst h2b; subst h2c
    exact ⟨rfl, Or.inl ⟨⟨rfl, le_rfl⟩, h4⟩⟩
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    injection h2 with h2a h2b h2c
    subst h1a; subst h2a; subst h2b; subst h2c
    exact ⟨rfl, Or.inr rfl⟩
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
    subst h1a; subst h1b
    simp_all

private theorem ggR1ADs_largeEvenSplit {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGTBRowR1AD p lab) (hn : 2 ≤ lab.n) : LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGTBRowR1AD GGTBRowR1A GGTBRowR1D at ht
  simp only at ht hn
  have hn1 : n ≠ 1 := by omega
  rcases ht with ⟨⟨ht, -⟩, -⟩ | ht <;> subst ht <;>
    simp [LargeEvenSplit, LargeEvenUntwisted, hn1]

theorem ggInnerDiagOnLabel_r1Par_of_rowR1AD (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR1AD p lab) p Bs L) :
    GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1AD p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L := by
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  obtain ⟨hn', hrow'⟩ := ggR1ADs_labelIso hp hp2 hrow hiso
  have hbad : GGLabQFour p labs ∧ GGTBRowR1AD p labs ∧ p ∣ 2 ^ labs.n - 1 := by
    have hq' : 2 ≤ labs.n := by rw [hn']; exact hQ4
    exact ⟨by unfold GGLabQFour; exact hq', hrow',
      (ggR1ADs_largeEvenSplit hrow' hq').mp hPs.1⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabs hhass
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

section Presentation

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenTag modelUniv_eq
  lieModel_unique_even)

private theorem ggR1ADs_of_lieModel
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

theorem ggR1AD_psl_of_lieModel
    {G : Type} [Group G] [Finite G] {p : ℕ} {L : Subgroup G} (hp : p.Prime) {m n : ℕ}
    (hm : 3 ≤ m) (hpn : p ∣ 2 ^ n - 1) (hL : commutator ↥L = ⊤)
    (hX : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL (m + 1) 2 n) :
    ∃ ψ : (ggU .PSL (m + 1) n).K →* G, StatedLieAdmissible .PSL (m + 1) 2 n ∧
      ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) n).K ∧ ψ.range = L ∧ p ∣ 2 ^ n - 1 := by
  have hfinPSL : Finite (ggU .PSL (m + 1) n).K := by
    change Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 n))
    infer_instance
  have hsec : 2 ≤ n → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU .PSL (m + 1) n).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : (ggU .PSL (m + 1) n).K →* E, ∀ g, π (s g) = g := by
    intro hf E _ _ π hπ hcen
    have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have h4 : 4 ≤ 2 ^ n := four_le_two_pow hf
    exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
      (by omega) (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card
        (by omega) (by omega) (by omega) (by omega)) hπ hcen
  exact ggR1ADs_of_lieModel (t := .PSL) (n := m + 1) (f := n) hp (.inl rfl) hpn hsec hL hX

theorem ggR1AD_splitLie_tagged
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1AD p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      ((t = .PSL ∧ ¬ p ∣ n) ∨ (t = .POmegaPlus ∧ 3 ≤ n)) ∧ StatedLieAdmissible t n 2 f ∧
      ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = L ∧ p ∣ 2 ^ f - 1 := by
  have h : StandardType.LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGTBRowR1AD p lab ∧ p ∣ 2 ^ lab.n - 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2.1, hP.1.2.2⟩) hL
  obtain ⟨⟨tag, l, n⟩, hlab2, _, _, _, _, θ, -, -, hrow, hm⟩ :=
    largeEvenMarking_exists_markedModel h
  obtain ⟨hAD, hpn⟩ : GGTBRowR1AD p ⟨tag, l, n⟩ ∧ p ∣ 2 ^ n - 1 := hrow
  have hPSL : ∀ m, 3 ≤ m → LieModel (↥L ⧸ Subgroup.center ↥L) .PSL (m + 1) 2 n →
      ∃ ψ : (ggU .PSL (m + 1) n).K →* G, StatedLieAdmissible .PSL (m + 1) 2 n ∧
        ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) n).K ∧ ψ.range = L ∧ p ∣ 2 ^ n - 1 :=
    fun m hm hX => ggR1AD_psl_of_lieModel hp hm hpn h.1 hX
  have hSp : ∀ m, 4 ≤ m → LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus m 2 n →
      ∃ ψ : (ggU .POmegaPlus m n).K →* G, StatedLieAdmissible .POmegaPlus m 2 n ∧
        ψ.ker ≤ Subgroup.center (ggU .POmegaPlus m n).K ∧ ψ.range = L ∧ p ∣ 2 ^ n - 1 := by
    intro m hm4 hX
    have hm3 : 3 ≤ m := by omega
    have hU : ggU .POmegaPlus m n =
        ⟨spinGroup (Spin.quadPlus m (GaloisField 2 n)),
          Spin.plusDatum m (GaloisField 2 n) hm3⟩ := by
      simp only [ggU, lieUniversal, hm3, ↓reduceDIte]
    have hfinSp : Finite (ggU .POmegaPlus m n).K := by
      have : NeZero m := ⟨by omega⟩
      rw [hU]
      exact CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
        Spin.coe_ker_spinMatrix_quadPlus
    have hsec : 2 ≤ n → ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU .POmegaPlus m n).K),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
          ∃ s : (ggU .POmegaPlus m n).K →* E, ∀ g, π (s g) = g := by
      intro hf E _ _
      have hc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      rw [hU]
      intro π hπ hcen
      exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
        hm3 (by rw [hc]; exact four_le_two_pow hf) hπ hcen
    exact ggR1ADs_of_lieModel (t := .POmegaPlus) (n := m) (f := n) hp
      (.inr (.inl rfl)) hpn hsec h.1 hX
  have hAorD : ((tag = .A ∧ 3 ≤ l) ∧ ¬ p ∣ l + 1) ∨ tag = .D := hAD
  rcases hAorD with ⟨⟨rfl, h3⟩, hpA⟩ | rfl
  · have hX : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL (l + 1) 2 n :=
      MarkedModel.of_mulEquiv θ.symm hm
    obtain ⟨ψ, hψ⟩ := hPSL l h3 hX
    exact ⟨.PSL, l + 1, n, ψ, Or.inl ⟨rfl, hpA⟩, hψ⟩
  · have hl3 : 3 ≤ l := hlab2.2
    by_cases hl : l = 3
    · subst hl
      have h4 := ggR1ADs_not_dvd_four hp hp2
      have hX : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL (3 + 1) 2 n :=
        MarkedModel.of_mulEquiv θ.symm hm
      obtain ⟨ψ, hψ⟩ := hPSL 3 le_rfl hX
      exact ⟨.PSL, 3 + 1, n, ψ, Or.inl ⟨rfl, h4⟩, hψ⟩
    · have hl4 : 4 ≤ l := by omega
      have hX : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus l 2 n := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg, hl] using
          MarkedModel.of_mulEquiv θ.symm hm
      obtain ⟨ψ, hψ⟩ := hSp l hl4 hX
      exact ⟨.POmegaPlus, l, n, ψ, Or.inr ⟨rfl, hl3⟩, hψ⟩

end CFSG.StandardType

end
