module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Parity
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1ADSplit
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Cond

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

private theorem ggR1ADvd_labelIso {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab lab' : LargeEvenLabel} (ht : GGTBRowR1A p lab ∧ p ∣ lab.rank + 1)
    (h : GGLabelIso lab lab') : lab'.n = lab.n ∧ GGTBRowR1A p lab' ∧ p ∣ lab'.rank + 1 := by
  have h4 : ¬ p ∣ 3 + 1 := by
    rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGTBRowR1A at ht ⊢
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · injection h with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, ht⟩
  · obtain ⟨hb, -⟩ := h
    rcases hb with hb | hb <;> simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1b
    exact absurd ht.2 h4
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨-, h2⟩ := h
    injection h2 with h2a h2b h2c
    subst h2b
    simp_all

theorem ggInnerDiagOnLabel_r1Par_of_rowR1ADvd (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ (GGTBRowR1A p lab ∧ p ∣ lab.rank + 1)) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ (GGTBRowR1A p lab ∧ p ∣ lab.rank + 1) ∧
      p ∣ 2 ^ lab.n - 1) p Bs L := by
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  exact ggInnerDiagOnLabel_r1Par_of_closed (P := fun p lab => GGTBRowR1A p lab ∧ p ∣ lab.rank + 1)
    hRig (fun h => Or.inl h.1) (fun h hi => ggR1ADvd_labelIso hp hp2 h hi) hHyp hL

theorem ggR1A_splitLie_tagged
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} (hp : p.Prime)
    (hL : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1A p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∃ (n f : ℕ) (ψ : (ggU .PSL n f).K →* G), StatedLieAdmissible .PSL n 2 f ∧
      ψ.ker ≤ Subgroup.center (ggU .PSL n f).K ∧ ψ.range = L ∧ p ∣ 2 ^ f - 1 := by
  have h : StandardType.LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGTBRowR1A p lab ∧ p ∣ 2 ^ lab.n - 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2.1, hP.1.2.2⟩) hL
  obtain ⟨⟨tag, l, n⟩, -, _, _, _, _, θ, -, -, hrow, hm⟩ :=
    largeEvenMarking_exists_markedModel h
  obtain ⟨⟨htag, h3⟩, hpn⟩ : (tag = .A ∧ 3 ≤ l) ∧ p ∣ 2 ^ n - 1 := hrow
  subst htag
  have hX : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL (l + 1) 2 n :=
    MarkedModel.of_mulEquiv θ.symm hm
  exact ⟨l + 1, n, ggR1AD_psl_of_lieModel hp h3 hpn h.1 hX⟩

theorem ggExcReflTBWeylDatumQFourOn_rowR1ADvd
    (hRig : GGLabelRigidInput)
    (hnc : GGTBJNoncommRowTarget (fun p lab => GGTBRowR1A p lab ∧ p ∣ lab.rank + 1)) :
    GGTBDatumRowTarget (fun p lab => GGTBRowR1A p lab ∧ p ∣ lab.rank + 1) := by
  refine ggTBDatumRowTarget_of_noncomm (fun {G} _ _ {p} {B Bs x L D J} hHyp hL => ?_) hnc
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  have hLA : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ GGTBRowR1A p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hP.1.2.1.1, hP.1.2.2⟩, hP.2⟩)
      (ggInnerDiagOnLabel_r1Par_of_rowR1ADvd hRig hHyp hL)
  obtain ⟨n, f, ψ, hadm, hker, hrange, hpf⟩ := ggR1A_splitLie_tagged hp hLA
  exact ⟨.PSL, n, f, ψ, Or.inl rfl, hadm, hker, hrange, hpf⟩

end CFSG.StandardType

end
