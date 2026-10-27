module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1On
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGE6DepXNotInL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem pow_succ_le_card_range_ggGamma_of_not_i1 {G : Type} [Group G] [Finite G] {p r : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hI1 : ¬ GGQTwoI1 Bs D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlift : GGTorusLift p r R) : p ^ (r + 1) ≤ Nat.card (ggGamma L hN).range := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hDdef : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hne : B ≠ Bs := by
    rintro rfl
    refine hI1 fun b hb hc => ?_
    rw [hDdef]
    exact ⟨hb, Subgroup.mem_centralizer_iff.mpr fun j hj => (hc j hj).symm⟩
  have hBsP : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2 b b.2)⟩
  obtain ⟨n, hn⟩ := hBsP.exists_card_eq
  have hlt : Nat.card B < Nat.card Bs :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hBBs) fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hBBs h.ge)
  rw [hS.1.2.1, hn] at hlt
  have hmn := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  have h1 := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ hlift
  have h2 : p ^ (r + 1) * p ≤ Nat.card (ggGamma L hN).range * p := by
    rw [card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN, hn, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  exact Nat.le_of_mul_le_mul_right h2 hp.pos

theorem exists_ggQ2LDatum_of_frameW {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} [Fact (Nat.Prime 3)] (hHyp : GGCorFiveTwentyHyp 3 B Bs x L D J)
    (hL : commutator L = ⊤) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : L ⧸ Subgroup.center L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I) (hcp : GGCenterPrime 3 R)
    {s : ℕ} (hs : 3 ^ s ≤ Nat.card (ggGamma L hBsN).range) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} (hF : GGTorusWeylFrameW 3 s R I M)
    (hA : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 s R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card Λ)
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hent : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2)
    (hT : SecFiveRootRefl.CartanTree C) (hdet : ((C.det : ℤ) : ZMod 3) ≠ 0)
    {lab : LargeEvenLabel} (hlab : GGQ2LabelWeyl lab M) :
    ∃ D : GGQ2LDatum 3 Bs L x, GGQ2LabelWeyl lab D.coxeter ∧ D.ShapeFull ∧
      Module.finrank (ZMod 3) D.V = Fintype.card D.Λ + 1 := by
  have hcfg : GGConfig 3 B Bs x L D J := hHyp.1
  have hNT : GGNoTransvection 3 Bs := hHyp.2.2.2.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hS.2.2.2.2
  have hcardmul : Nat.card (ggGamma L hBsN).range * 3 = Nat.card Bs :=
    card_range_ggGamma_mul_of (p := 3) hp hBs hxBs hx1 hLx hcyc hBsN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by
    have h4 := (pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2).trans
      (Subgroup.card_le_of_le hcfg.2.1.1)
    rw [← hcardmul, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  have hTB : GGTorusTBGroup 3 s R I L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hL θ hBsN hBsI hs h3
  have hW : GGWeylOfType 3 M (ggAutomizer L Bs) :=
    ggWeylOfType_of_frame hp (by norm_num) hBs hSC hNT hBsN
      (card_bstar_inf_center_le hcfg) (hF L (ggQuotHom θ) (ggGamma L hBsN).range hTB)
  have hA3 : Nat.card ↥(ggGamma L hBsN).range = 3 ^ Fintype.card Λ :=
    hA L (ggQuotHom θ) (ggGamma L hBsN).range hTB
  have hcard : Nat.card Bs = 3 ^ (Fintype.card Λ + 1) := by
    rw [← hcardmul, hA3, pow_succ]
  have hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) :=
    hcp ↥L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  have hxL : x ∉ L := ggE6Dep_x_not_mem_L hcfg hZ
  exact exists_ggQ2LDatum_shapeFull (by norm_num) hBs hxBs hx1 hLx hxL hNT hM hC hent hT hdet
    hW hcard hlab

theorem ggQ2TableBI1FailOn_of_frames {S : LargeEvenLabel → Prop}
    (hS : ∀ lab, S lab → GGQ2TBLabel lab)
    (h : ∀ lab, LargeEvenInLambda2 lab → GGLabQTwo 3 lab → S lab →
      ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ),
        GGQ2LabelWeyl lab M ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2) ∧ SecFiveRootRefl.CartanTree C ∧
        ((C.det : ℤ) : ZMod 3) ≠ 0 ∧
        LargeEvenLabelAll lab (fun R _ I _ => GGCenterPrime 3 R ∧
          ∃ r s, s ≤ r + 1 ∧ GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 s R I M ∧
            ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
              GGTorusTBGroup 3 s R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card Λ)) :
    GGQ2TableBI1FailOn S := by
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨hq, hSl⟩, hBsN, h3I⟩ := hP
  obtain ⟨Λ, _, _, M, C, hlabW, hMw, hC, hent, hT, hdet, hall⟩ := h lab hlab hq hSl
  obtain ⟨R₂, _, I₂, F₂, hQ₂⟩ := largeEvenRawDatum_exists (hall _ hraw)
  obtain ⟨hQold, hcp, r, s, hsr, hlift, hF, hA⟩ := hQ₂
  obtain ⟨-, -, θ₂, hP₂⟩ := hQold
  obtain ⟨-, hBsN₂, h3I₂⟩ := hP₂
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ₂ ⟨b, hBsN₂ hb⟩ ∈ I₂ :=
    fun b hb => ggLAut_mem_of_induces L θ₂ hBsN₂ h3I₂ hb
  have hsB : 3 ^ s ≤ Nat.card (ggGamma L hBsN₂).range :=
    (Nat.pow_le_pow_right (by norm_num) hsr).trans
      (pow_succ_le_card_range_ggGamma_of_not_i1 hset.1.1 hI1 hperf θ₂ hBsN₂ hlift)
  obtain ⟨D, hDW, hDfull, hDdim⟩ :=
    exists_ggQ2LDatum_of_frameW (G := G) hset.1 hperf θ₂ hBsN₂ hBsI hcp hsB hF hA hMw hC hent
      hT hdet hlabW
  exact ⟨lab, hq, hS lab hSl, ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩,
    D, hDW, Or.inl hDfull, fun hle => by omega⟩

end CFSG.StandardType

end
