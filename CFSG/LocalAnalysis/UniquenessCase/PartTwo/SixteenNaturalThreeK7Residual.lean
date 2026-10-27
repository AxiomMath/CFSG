module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.F918V2GDA
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Block
public import CFSG.Quasithin.EmptyFaithful.S152He4Core
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_hom_eq_one_of_isPGroup
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∈ D.sig ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {Q : Type} [Group Q] (hQ : IsPGroup p Q)
    (f : ↥(Mbar D.M V₀ V hV) →* Q) : f = 1 := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hMst : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hrange : (barHom V₀ V hV hMst).range = Mbar D.M V₀ V hV :=
    range_barHom V₀ V hV hMst
  let ψ : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
    (barHom V₀ V hV hMst).codRestrict (Mbar D.M V₀ V hV) (fun m => by
      rw [← hrange]
      exact ⟨m, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : MulAut (Vtil V₀ V hV)) ∈ (barHom V₀ V hV hMst).range := by
      rw [hrange]
      exact x.2
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, Subtype.ext hm⟩
  have htop : CFSG.GH74.GLS.oResidual p ↥D.M = ⊤ :=
    uc22p21c_oResidual_eq_top_of_opRes hp (c.std.h638 p hp hp2 hpM)
  have hle : CFSG.GH74.GLS.oResidual p ↥D.M ≤ (f.comp ψ).ker :=
    CFSG.RankThree.Transfer.oResidual_le_ker_of_isPGroup (f.comp ψ) hQ
  rw [htop] at hle
  have hker : (f.comp ψ).ker = ⊤ := top_le_iff.mp hle
  have hcomp : f.comp ψ = 1 := by
    ext m
    have hm : m ∈ (f.comp ψ).ker := by
      rw [hker]
      exact Subgroup.mem_top m
    exact MonoidHom.mem_ker.mp hm
  ext a
  obtain ⟨m, hm⟩ := hψ a
  rw [← hm]
  simpa using DFunLike.congr_fun hcomp m

theorem s168e3_exists_surj_kBar
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7) :
    ∃ π : ↥(Mbar D.M V₀ V hV) →*
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)),
      Function.Surjective π := by
  classical
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K := s1t3KBar A B
  obtain ⟨N, hNA, -, -, hNKcomm, hNKbot, hNKsup, -⟩ := hT.structure_of_seven h7
  have hKA : K ≤ A := inf_le_left
  let NA := N.subgroupOf A
  let KA := K.subgroupOf A
  have hsupA : NA ⊔ KA = ⊤ := by
    have h := Subgroup.subgroupOf_sup hNA hKA
    rw [hNKsup, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hbotA : NA ⊓ KA = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx
      have hxN : (x : MulAut (Vtil V₀ V hV)) ∈ N := Subgroup.mem_subgroupOf.mp hx.1
      have hxK : (x : MulAut (Vtil V₀ V hV)) ∈ K := Subgroup.mem_subgroupOf.mp hx.2
      have hxNK : (x : MulAut (Vtil V₀ V hV)) ∈ N ⊓ K := Subgroup.mem_inf.mpr ⟨hxN, hxK⟩
      rw [hNKbot, Subgroup.mem_bot] at hxNK
      rw [Subgroup.mem_bot]
      exact Subtype.ext hxNK
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hcommA : ∀ a ∈ NA, ∀ b ∈ KA, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext
      (hNKcomm (a : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp ha)
        (b : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp hb))
  obtain ⟨e⟩ := UC22.uc22p20p_prod_equiv hcommA hsupA hbotA
  let eK : ↥KA ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKA
  let π : ↥A →* ↥K := eK.toMonoidHom.comp ((MonoidHom.snd ↥NA ↥KA).comp e.toMonoidHom)
  refine ⟨π, ?_⟩
  intro k
  refine ⟨e.symm (1, eK.symm k), ?_⟩
  simp [π]

private theorem s168e3_false_of_kBar_card_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7)
    (hpM : 7 ∈ D.sig ∨ CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M) : False := by
  classical
  obtain ⟨π, hπsurj⟩ := s168e3_exists_surj_kBar hT h7
  let K := s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
  have hK' : Nat.card ↥K = 7 := hK
  have hQ : IsPGroup 7 ↥K := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hK')
  have hπ : π = 1 :=
    s168e3_hom_eq_one_of_isPGroup c Nat.prime_seven (by norm_num) hpM hQ π
  have hsub : Subsingleton ↥K := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hπsurj a
    obtain ⟨y, rfl⟩ := hπsurj b
    have hx : π x = 1 := by rw [hπ]; rfl
    have hy : π y = 1 := by rw [hπ]; rfl
    rw [hx, hy]
  have h1 : Nat.card ↥K = 1 := Nat.card_of_subsingleton (1 : ↥K)
  omega

theorem s168e3_seven_not_mem_sig_of_kBar_card_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) :
    7 ∉ D.sig := by
  intro h7sig
  exact s168e3_false_of_kBar_card_seven c hT h7 hK (Or.inl h7sig)

theorem s168e3_not_strongly_seven_of_kBar_card_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M := by
  intro hstr
  exact s168e3_false_of_kBar_card_seven c hT h7 hK (Or.inr hstr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
