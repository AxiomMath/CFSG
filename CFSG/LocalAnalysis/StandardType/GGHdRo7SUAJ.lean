module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAJPerm
import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.Quasithin.Background.F918V3T3
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SUAJAux_three_dvd_card_of_row {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {J X : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J X) : p ∣ Nat.card J := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hp3, hJtag, hJn, hXtag, hXn, hXrank,
    hX6, h3X⟩ := hrow
  have hJrank : 4 ≤ labJ.rank := by omega
  subst hp3
  have hJlab' : LargeEvenRecipeUnitary (labJ.rank + 1) (2 ^ labJ.n)
      (fun R' _ _ _ => Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* R')) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, hJtag] using hJlab
  obtain ⟨K, hKfield, hKfin, hKcard, hKiso⟩ := hJlab'
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨e⟩ := hKiso
  have hcard_eq : Nat.card (↥J ⧸ Subgroup.center ↥J) =
      Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (labJ.rank + 1)) K (2 ^ labJ.n))) :=
    Nat.card_congr e.toEquiv
  have h3 : 3 ∣ Nat.card
      (LargeEvenProj (LargeEvenSUGroup (Fin (labJ.rank + 1)) K (2 ^ labJ.n))) := by
    exact CFSG.Quasithin.F918V3T3.three_dvd_card_PSU_of_three_le
      (n := labJ.rank + 1) (q := 2 ^ labJ.n) (K := K) (by omega) (by positivity)
  rw [← hcard_eq] at h3
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
  exact dvd_mul_of_dvd_left h3 _

private theorem hdRo7SUAJAux_labelIso_twA_twA {l1 l2 : LargeEvenLabel}
    (h : GGLabelIso l1 l2) (h1 : l1.tag = .twA) (h2 : l2.tag = .twA) : l1 = l2 := by
  obtain ⟨t1, r1, n1⟩ := l1
  obtain ⟨t2, r2, n2⟩ := l2
  simp only [GGLabelIso] at h
  simp only at h1 h2
  rw [h1, h2] at h ⊢
  simpa using h

private theorem hdRo7SUAJAux_labelIso_twA_left_ne {l1 l2 : LargeEvenLabel}
    (h : GGLabelIso l1 l2) (h1 : l1.tag = .twA)
    (h2 : l2.tag = .A ∨ l2.tag = .D ∨ l2.tag = .E8 ∨ l2.tag = .triD4 ∨
      l2.tag = .G2 ∨ l2.tag = .twE6) : False := by
  obtain ⟨t1, r1, n1⟩ := l1
  obtain ⟨t2, r2, n2⟩ := l2
  simp only [GGLabelIso] at h
  simp only at h1 h2
  rw [h1] at h
  rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 <;> rw [h2] at h <;> simp at h

private theorem hdRo7SUAJAux_not_nonLevi {G : Type} [Group G] [Finite G] {p : ℕ}
    {J X : Subgroup G} (hRig : GGLabelRigidInput)
    (hSU : GGResRowAt ggRowSUCorank2 p J X)
    (hNL : GGResRowAt ggRowNonLevi p J X) : False := by
  obtain ⟨lJ1, lX1, hJ1Λ, hX1Λ, hJ1lab, hX1lab, hp3, hJ1tag, hJ1n, hX1tag, hX1n, hXrank,
    hX6, h3X⟩ := hSU
  obtain ⟨lJ2, lX2, hJ2Λ, hX2Λ, hJ2lab, hX2lab, hNL'⟩ := hNL
  have hisoJ : GGLabelIso lJ1 lJ2 := hRig lJ1 lJ2 _ hJ1Λ hJ2Λ hJ1lab hJ2lab
  have hisoX : GGLabelIso lX1 lX2 := hRig lX1 lX2 _ hX1Λ hX2Λ hX1lab hX2lab
  have hJrank : 4 ≤ lJ1.rank := by omega
  rcases hNL' with h2 | hmax | htri | htri2 | h7 | htw2
  · rcases h2 with ⟨hJA, -, -, -⟩ | ⟨hJtwA, -, hdvdr, hXeq⟩ |
      ⟨hJD, -, -, -⟩ | ⟨hJD, -, -, -⟩
    · have hJAtag : lJ2.tag = .A := by rw [hJA]
      exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
    · have hJeq : lJ1 = lJ2 := hdRo7SUAJAux_labelIso_twA_twA hisoJ hJ1tag hJtwA
      have hX2tag : lX2.tag = .twA := by rw [hXeq]
      have hXeq' : lX1 = lX2 := hdRo7SUAJAux_labelIso_twA_twA hisoX hX1tag hX2tag
      have hdvd3 : 3 ∣ lJ2.rank + 3 := by simpa [hp3] using hdvdr
      have heq : lX1.rank + 1 = lJ2.rank + 3 := by rw [hXrank, hJeq]
      rw [← heq] at hdvd3
      exact h3X hdvd3
    · have hJDtag : lJ2.tag = .D := by rw [hJD]
      exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
    · have hJDtag : lJ2.tag = .D := by rw [hJD]
      exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
  · rcases hmax with ⟨hJA, -, -, -⟩ | ⟨hJeq2, -, -, hXeq2⟩
    · have hJAtag : lJ2.tag = .A := by rw [hJA]
      exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
    · have hJtwA : lJ2.tag = .twA := by rw [hJeq2]
      have hJeq : lJ1 = lJ2 := hdRo7SUAJAux_labelIso_twA_twA hisoJ hJ1tag hJtwA
      have hX2tag : lX2.tag = .E8 := by rw [hXeq2]
      exact hdRo7SUAJAux_labelIso_twA_left_ne hisoX hX1tag (by tauto)
  · rcases htri with ⟨hJtri, -, -⟩ | ⟨hJG2, -, -⟩
    · exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
    · exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
  · obtain ⟨hJtri, -, -, -⟩ := htri2
    exact hdRo7SUAJAux_labelIso_twA_left_ne hisoJ hJ1tag (by tauto)
  · obtain ⟨hp7, -⟩ := h7
    omega
  · obtain ⟨hJtwA, hJrank2, -, -, -⟩ := htw2
    have hJeq : lJ1 = lJ2 := hdRo7SUAJAux_labelIso_twA_twA hisoJ hJ1tag hJtwA
    rw [hJeq] at hJrank
    omega

private theorem hdRo7SUAJAux_nonabelian_of_data
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs J X : Subgroup G}
    {m : ℕ} (hm7 : 7 ≤ m)
    {Λ K : Type} [Fintype Λ] [Fintype K]
    {M : CoxeterMatrix Λ} {MJ : CoxeterMatrix K}
    (φ : Λ → MulAut ↥Bs) (e : K → Λ)
    (hWeylMJ : GGIsWeylMatrix MJ)
    (fJ : MJ.Group ≃* ↥(ggAutomizer J Bs))
    (hfJ : ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ (e j))
    (hΛcard : Nat.card Λ ≤ Nat.card K + 3)
    (hml : m ≤ Nat.card Λ + 1) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  classical
  by_contra h
  push Not at h
  have hnoedge : ∀ j j' : K, j ≠ j' → MJ.M j j' = 2 := by
    intro j j' hne
    have hcomm : fJ (MJ.simple j) * fJ (MJ.simple j') =
        fJ (MJ.simple j') * fJ (MJ.simple j) :=
      Subtype.ext (h (fJ (MJ.simple j)) (fJ (MJ.simple j)).2
        (fJ (MJ.simple j')) (fJ (MJ.simple j')).2)
    have hsimple_comm : MJ.simple j * MJ.simple j' = MJ.simple j' * MJ.simple j :=
      fJ.injective (by simpa [map_mul] using hcomm)
    have hsq : (MJ.simple j * MJ.simple j') ^ 2 = 1 := by
      have hc : Commute (MJ.simple j) (MJ.simple j') := hsimple_comm
      rw [hc.mul_pow]
      rw [show MJ.simple j ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j,
          show MJ.simple j' ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self MJ.toCoxeterSystem j']
      simp
    have horder : orderOf (MJ.simple j * MJ.simple j') = MJ.M j j' := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple MJ.toCoxeterSystem j j'
    have hdvd : MJ.M j j' ∣ 2 := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    have h1 : MJ.M j j' ≠ 1 := MJ.off_diagonal j j' hne
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact (h1 h').elim
    · exact h'
  have hsub : Subsingleton K := by
    refine ⟨fun j j' => ?_⟩
    by_contra hne
    have hpath := ggRC_weyl_connected hWeylMJ j j'
    have hEq : j = j' := by
      induction hpath with
      | refl => rfl
      | tail _ hstep _ =>
          exact (hstep.2 (hnoedge _ _ hstep.1)).elim
    exact hne hEq
  have hKpos : 0 < Nat.card K := by omega
  haveI : Nonempty K := by
    rw [← Fintype.card_pos_iff]
    simpa [Nat.card_eq_fintype_card] using hKpos
  have hKcard : Nat.card K = 1 := by
    have : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr
      ⟨Classical.arbitrary K, fun x => Subsingleton.elim x _⟩
    simpa [Nat.card_eq_fintype_card] using this
  omega

private theorem hdRo7SUAJAux_sideDatum_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hperm : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g)
    (hm7 : 7 ≤ m) (hD : GGResSideDatum p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, bnode, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, hfJ⟩, hgenJ, hconj⟩ := hD
  letI : Fintype Λ := instΛ
  letI : DecidableEq Λ := decΛ
  letI : AddCommGroup V' := instV
  letI : Module (ZMod p) V' := instMod
  have hml : m ≤ Nat.card Λ + 1 :=
    hdRo7SUAJPerm_model_card_le (M := M) b ι hperm φ f hf hgenX hrefl hm7
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ≠ bnode} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j = bnode} +
        Nat.card {j : Λ // j ≠ bnode} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j = bnode)), Nat.card_sum]
    have hsingle : Nat.card {j : Λ // j = bnode} = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have : (Finset.univ.filter (fun j : Λ => j = bnode)) = {bnode} := by
        ext j
        simp
      rw [this]
      simp
    omega
  exact hdRo7SUAJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (X := X) (m := m)
    (M := M) (MJ := MJ) hm7 φ Subtype.val hWeylMJ fJ hfJ hΛcard hml

private theorem hdRo7SUAJAux_le3_nonabelian
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (hperm : ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g)
    (hm7 : 7 ≤ m) (hD : GGResLeviSideDatumLE3 p Bs X J) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  obtain ⟨Λ, instΛ, decΛ, S, M, C, MJ, V', instV, instMod, ι', φ, hv, hα,
    hS2, hS3, hWeylM, hCartan, hWeylMJ, hMJsub, hformula, hrefl, hpair, ⟨f, hf⟩, hgenX,
    ⟨fJ, hfJ⟩, hgenJ, hconj⟩ := hD
  letI : Fintype Λ := instΛ
  letI : DecidableEq Λ := decΛ
  letI : AddCommGroup V' := instV
  letI : Module (ZMod p) V' := instMod
  have hml : m ≤ Nat.card Λ + 1 :=
    hdRo7SUAJPerm_model_card_le (M := M) b ι hperm φ f hf hgenX hrefl hm7
  have hΛcard : Nat.card Λ ≤ Nat.card {j : Λ // j ∉ S} + 3 := by
    have hEq : Nat.card Λ = Nat.card {j : Λ // j ∈ S} +
        Nat.card {j : Λ // j ∉ S} := by
      rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j ∈ S)), Nat.card_sum]
    have hSsub : Nat.card {j : Λ // j ∈ S} = S.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe S
    omega
  exact hdRo7SUAJAux_nonabelian_of_data (p := p) (Bs := Bs) (J := J) (X := X) (m := m)
    (M := M) (MJ := MJ) hm7 φ Subtype.val hWeylMJ fJ hfJ hΛcard hml

theorem su_aj_holds : SUAJLeaf := by
  intro hX hJ hRig hLB G _ _ p B Bs x L D J y K hH inst
  intro hmL hmK hrow
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hI : GGThmIHyp p B x L := hcfg.1
  have hStd : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJL : J ≤ L := by
    have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
      hStd.1.2.2.2.2.2.1
    exact hcomp.1.trans inf_le_left
  have hpJ : p ∣ Nat.card J := by
    rcases hrow with hrow | hrow
    · exact hdRo7SUAJAux_three_dvd_card_of_row hrow
    · exact hdRo7SUAJAux_three_dvd_card_of_row hrow
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStd hpJ hnbr
  have hle : ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs :=
    le_inf (ggAutomizer_mono Bs hJL) (ggAutomizer_mono Bs hJK)
  refine ⟨?_, hle⟩
  rcases hrow with hrowL | hrowK
  · obtain ⟨m, V, hVadd, hVmod, ι, b, hx, hp3, hm7, h3m, hxb, hperm⟩ := hmL hrowL
    letI : AddCommGroup V := hVadd
    letI : Module (ZMod p) V := hVmod
    have hXD : GGResXDatum p Bs L := by
      rcases (hX G p B Bs x L D J y K hH).1 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).1 hXD with hSD | hLE3 | hNL
    · exact hdRo7SUAJAux_sideDatum_nonabelian b ι hperm hm7 hSD
    · exact hdRo7SUAJAux_le3_nonabelian b ι hperm hm7 hLE3
    · exact (hdRo7SUAJAux_not_nonLevi hRig hrowL hNL).elim
  · obtain ⟨m, V, hVadd, hVmod, ι, b, hy, hp3, hm7, h3m, hyb, hperm⟩ := hmK hrowK
    letI : AddCommGroup V := hVadd
    letI : Module (ZMod p) V := hVmod
    have hXD : GGResXDatum p Bs K := by
      rcases (hX G p B Bs x L D J y K hH).2 with h | h7
      · exact h
      · exfalso
        obtain ⟨-, -, -, -, -, -, hp7, -⟩ := h7
        omega
    rcases (hJ G p B Bs x L D J y K hH).2 hXD with hSD | hLE3 | hNL
    · exact hdRo7SUAJAux_sideDatum_nonabelian b ι hperm hm7 hSD
    · exact hdRo7SUAJAux_le3_nonabelian b ι hperm hm7 hLE3
    · exact (hdRo7SUAJAux_not_nonLevi hRig hrowK hNL).elim

end CFSG.StandardType.HdRo7SU
