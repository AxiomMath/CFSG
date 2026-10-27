module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LieType.SeitzGeneration.ExcPlaneF4Rest
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE7
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerCube
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice Polynomial
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open CFSG.Open (IsElemAbelian)

private theorem kgr_eq_one_of_pow_coprime {H : Type*} [Group H] {p : ℕ} (hp3 : Nat.Coprime p 3)
    {x : H} (h1 : x ^ p = 1) (h2 : x ^ 3 = 1) : x = 1 := by
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hp3, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

private theorem kgr_pow_mul_mem {G : Type*} [Group G] (R : Subgroup G) {c g : G}
    (hcn : c ∈ Subgroup.normalizer (R : Set G)) (hg : g ∈ R) (m : ℕ) :
    ∃ g' ∈ R, (c * g) ^ m = c ^ m * g' := by
  induction m with
  | zero => exact ⟨1, R.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨g', hg', h⟩ := ih
    have h1 : c⁻¹ * g' * c ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcn) g').1 hg'
      simpa using this
    refine ⟨c⁻¹ * g' * c * g, R.mul_mem h1 hg, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

section KGRankKnown

theorem kgr_pullback_adjoint (t : StatedLieTag) (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G) (p : ℕ) (E : Subgroup G) (hEr : E ≤ ψ.range)
    (hinj : Function.Injective ψ) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap ψ) ∧ Nat.card (E.comap ψ) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext; apply hinj
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
    simpa [map_mul] using h
  · apply hinj; rw [map_pow, map_one]; exact hE.2 _ hx
  · have h1 := Nat.card_congr (Subgroup.equivMapOfInjective (E.comap ψ) ψ hinj).toEquiv
    rw [Subgroup.map_comap_eq_self hEr] at h1
    exact h1

section ExcCertF4


theorem ggExcKGRank_F4 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .F4 n f).K →* G) (hset : GGKnownSetting .F4 n f ψ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : ¬ GGExcRegime p f)
    (E : Subgroup G) (hEn : E ≤ Subgroup.normalizer (ψ.range : Set G)) (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGPsiInnerDiag (ggU .F4 n f).D ψ b) : Nat.card E ≤ p ^ 3 := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  have hEr : E ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_F4 G n f ψ ψ.range
      ⟨⟨hadm, hrk⟩, ⟨rfl, hker⟩, hcomm, hlie⟩ b (hEn hb) (hdiag b hb)
    rw [hcent, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hE', hcard⟩ := kgr_pullback_adjoint .F4 n f G ψ p E hEr hinj hE
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hpK : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hq]; intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hnd : ¬ p ∣ Nat.card (GaloisField 2 f) ^ 2 - 1 := by
    rw [hq]
    have ha : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [ha, this]; ring
    rw [h1]; intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hreg (Or.inl h)
    · exact hreg (Or.inr h)
  have key := rankLE2_adjointGroup_F4 (GaloisField 2 f) hp hp2 hpK hnd
    (E.comap ψ : Subgroup ↥(adjointGroup .F4 (GaloisField 2 f))) hE'
  have key' : Nat.card (E.comap ψ) ≤ p ^ 2 := key
  rw [hcard] at key'
  exact key'.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

end ExcCertF4


private theorem kgr_regime_arith (f : ℕ) (hf : f ≠ 0) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : ¬ GGExcRegime p f) :
    ¬ p ∣ 2 ^ f ∧ 3 < p ∧ orderOf (((2 ^ f : ℕ) : ZMod p)) ≠ 1 ∧
      orderOf (((2 ^ f : ℕ) : ZMod p)) ≠ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ 2 ^ f := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have ha : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [ha, this]; ring
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    by_contra h
    have hp3 : p = 3 := by omega
    subst hp3
    apply hreg
    have hne : ((2 : ZMod 3) ^ f) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff (2 ^ f) 3).1 (by push_cast; exact h0)
      exact hpK this
    have h1 := ZMod.pow_card_sub_one_eq_one hne
    have h3 : (((2 ^ f) ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
      have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [Nat.cast_sub hq1]; push_cast
      have : ((2 : ZMod 3) ^ f) ^ 2 = 1 := by simpa using h1
      rw [this]; simp
    have h4 := (ZMod.natCast_eq_zero_iff _ 3).1 h3
    rw [hsq] at h4
    rcases (Nat.Prime.dvd_mul hp).1 h4 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcast : (((2 ^ f : ℕ) : ZMod p)) = (2 : ZMod p) ^ f := by push_cast; rfl
  refine ⟨hpK, hp3, ?_, ?_⟩
  · intro h
    apply hreg; left
    have h1 := orderOf_eq_one_iff.1 h
    have : (((2 ^ f - 1 : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_sub ha, h1]; simp
    exact (ZMod.natCast_eq_zero_iff _ p).1 this
  · intro h
    apply hreg; right
    generalize hx : (((2 ^ f : ℕ) : ZMod p)) = x at h
    have h2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [h])
    have hne1 : x ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at h; omega
    have h3 : x = -1 := by
      rcases mul_self_eq_one_iff.1 (show x * x = 1 by rw [← sq]; exact h2) with h | h
      · exact absurd h hne1
      · exact h
    have : (((2 ^ f + 1 : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, hx]
      exact eq_neg_iff_add_eq_zero.1 h3
    exact (ZMod.natCast_eq_zero_iff _ p).1 this

private theorem kgr_rankLE2_E8 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 ∧ orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 2 ∧
      orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 3 ∧ orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 4 ∧
      orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 6) :
    RankLE2 p (adjointGroup Tag.E8 K) := by
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he
  have he0 : e ≠ 0 := he' ▸ orderOf_natCast_ne_zero hp hpq
  by_cases hcnt : degCount Tag.E8 e ≤ 1
  · intro F hF
    have hc : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by rw [he']; exact hcnt
    exact (rankLE1_E8 K hp hpq hc F hF).trans (Nat.le_self_pow (by norm_num : 2 ≠ 0) p)
  · have hpos : 0 < degCount Tag.E8 e := by omega
    have h30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) hpos
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    intro F hF
    interval_cases e <;>
      first | exact absurd hcnt (by decide) | (exfalso; omega) | skip
    · exact (sylowTorus_E8_five K hp he').rank_le hp hF
    · exact (sylowTorus_E8_eight K hp he').rank_le hp hF
    · exact (sylowTorus_E8_ten K hp he').rank_le hp hF
    · exact (sylowTorus_E8_twelve K hp he').rank_le hp hF

section ExcCertE8


theorem ggExcKGRank_E8 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E8 n f).K →* G) (hset : GGKnownSetting .E8 n f ψ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : ¬ GGExcRegime p f)
    (hord : ¬ (orderOf ((2 : ZMod p) ^ f) ∈ ({3, 4, 6} : Set ℕ)))
    (E : Subgroup G) (hEn : E ≤ Subgroup.normalizer (ψ.range : Set G)) (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGPsiInnerDiag (ggU .E8 n f).D ψ b) : Nat.card E ≤ p ^ 3 := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le
  have hEr : E ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_E8 G n f ψ ψ.range
      ⟨⟨hadm, hrk⟩, ⟨rfl, hker⟩, hcomm, hlie⟩ b (hEn hb) (hdiag b hb)
    rw [hcent, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hE', hcard⟩ := kgr_pullback_adjoint .E8 n f G ψ p E hEr hinj hE
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  obtain ⟨hpK, hp3, hne1, hne2⟩ := kgr_regime_arith f hf p hp hp2 hreg
  rw [← hq] at hpK
  have hcast : ((2 ^ f : ℕ) : ZMod p) = (2 : ZMod p) ^ f := by push_cast; rfl
  have hne12 : orderOf (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≠ 1 ∧
      orderOf (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≠ 2 ∧
      orderOf (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≠ 3 ∧
      orderOf (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≠ 4 ∧
      orderOf (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≠ 6 := by
    rw [show (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = ((2 ^ f : ℕ) : ZMod p) by rw [hq]]
    refine ⟨hne1, hne2, ?_, ?_, ?_⟩ <;> intro h <;> exact hord (by rw [← hcast, h]; simp)
  have key := kgr_rankLE2_E8 (GaloisField 2 f) hp hp3 hpK hne12
    (E.comap ψ : Subgroup ↥(adjointGroup .E8 (GaloisField 2 f))) hE'
  have key' : Nat.card (E.comap ψ) ≤ p ^ 2 := key
  rw [hcard] at key'
  exact key'.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

end ExcCertE8


private theorem kgr_sylowTorus_of_blocks3 {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he3 : e = 3)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3])
    (hQ : ∀ d ∈ degreesE τ, e ∣ d → d / e ∈ [1, 2, 3, 4, 6])
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    SylowTorus (adjointGroup τ K) p (ds.count e) := by
  have he0 : e ≠ 0 := by omega
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hp3 : 3 < p := by omega
  have h5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp (by norm_num)
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    have hd123 := hso d hd.1 hde
    exact not_dvd_cyclotomic_eval_of_ne hp he hde (by
      intro hdvd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd123
      have := Nat.le_of_dvd (by omega) hdvd
      omega) hpa
  have hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      (p ^ (Nat.card K ^ e - 1).factorization p) ^ ds.count e := by
    rw [ordProj_card_adjointGroup_E (by rcases hτ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hp
      hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2 he (degreesE τ)
      (fun d hd hed => ⟨(hcard d hd).ne', not_dvd_small hp h5 (hQ d hd hed)⟩), hcount]
  exact sylowTorus_untwisted d hτ K hp hp3 hpq hM _ he0 hpow hn hchar' he hR hord

private theorem kgr_sylowTorus_E7_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    SylowTorus (adjointGroup Tag.E7 K) p 3 := by
  have h := kgr_sylowTorus_of_blocks3 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3]
    e7Three_charpoly e7Three_pow he rfl (by decide) (by decide) (by decide)
  simpa using h

private theorem kgr_sylowTorus_E7_six (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    SylowTorus (adjointGroup Tag.E7 K) p 3 := by
  have h := sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6]
    e7Six_charpoly e7Six_pow he (by norm_num) (by decide) (by decide) (by decide)
  simpa using h


private theorem kgr_map_elemAbelian {H H' : Type} [Group H] [Group H'] (φ : H →* H')
    (hφ : Function.Injective φ) (p : ℕ) (E : Subgroup H) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map φ) ∧ Nat.card (E.map φ) = Nat.card E := by
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, (Nat.card_congr (Subgroup.equivMapOfInjective E φ hφ).toEquiv).symm⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem kgr_rankLE3_E7 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 ∧ orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 2) :
    ∀ F : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p F → Nat.card F ≤ p ^ 3 := by
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he
  have he0 : e ≠ 0 := he' ▸ orderOf_natCast_ne_zero hp hpq
  intro F hF
  by_cases hcnt : degCount Tag.E7 e ≤ 1
  · have hc : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by rw [he']; exact hcnt
    exact (rankLE1_E7 K hp hpq hc F hF).trans (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
  · have hpos : 0 < degCount Tag.E7 e := by omega
    have h30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) hpos
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    interval_cases e <;>
      first | exact absurd hcnt (by decide) | (exfalso; omega) | skip
    · exact (kgr_sylowTorus_E7_three K hp he').rank_le hp hF
    · exact ((sylowTorus_E7_four K hp he').rank_le hp hF).trans
        (Nat.pow_le_pow_right hp.pos (by norm_num))
    · exact (kgr_sylowTorus_E7_six K hp he').rank_le hp hF

private theorem kgr_sylowTorus_E6_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    SylowTorus (adjointGroup Tag.E6 K) p 3 := by
  have h := kgr_sylowTorus_of_blocks3 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3]
    e6Three_charpoly e6Three_pow he rfl (by decide) (by decide) (by decide)
  simpa using h

theorem kgr_rankLE3_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 ∧ orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 2) :
    ∀ F : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian p F → Nat.card F ≤ p ^ 3 := by
  obtain ⟨e, he'⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he'] at he
  have he0 : e ≠ 0 := he' ▸ orderOf_natCast_ne_zero hp hpq
  intro F hF
  by_cases hcnt : degCount Tag.E6 e ≤ 1
  · have hc : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by rw [he']; exact hcnt
    exact (rankLE1_E6 K hp hpq hc F hF).trans (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
  · have hpos : 0 < degCount Tag.E6 e := by omega
    have h30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) hpos
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    interval_cases e <;>
      first | exact absurd hcnt (by decide) | (exfalso; omega) | skip
    · exact (kgr_sylowTorus_E6_three K hp he').rank_le hp hF
    · exact ((sylowTorus_E6_four K hp he').rank_le hp hF).trans
        (Nat.pow_le_pow_right hp.pos (by norm_num))
    · exact ((sylowTorus_E6_six K hp he').rank_le hp hF).trans
        (Nat.pow_le_pow_right hp.pos (by norm_num))

private theorem kgr_inn_E6 {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type*} [Group G]
    (ψ : ↥(e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k))
    (hcent : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    {c : G} (hcn : c ∈ Subgroup.normalizer (ψ.range : Set G)) {p : ℕ} (hp3 : Nat.Coprime p 3)
    (hcp : c ^ p = 1) (hc : GGPsiInnerDiag (e6Datum k) ψ c) : c ∈ ψ.range := by
  obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hc
  set y : G := c * g with hy
  have hpow : ∀ m : ℕ, ∀ (i : Fin (e6Datum k).rank) t,
      (y ^ m)⁻¹ * ψ (e6Data_valid.xm k (Pi.single i 1) t) * y ^ m =
        ψ (e6Data_valid.xm k (Pi.single i 1) (((a i : kˣ) : k) ^ m * t)) ∧
      (y ^ m)⁻¹ * ψ (e6Data_valid.xm k (-Pi.single i 1) t) * y ^ m =
        ψ (e6Data_valid.xm k (-Pi.single i 1) ((((a i)⁻¹ : kˣ) : k) ^ m * t)) := by
    intro m
    induction m with
    | zero => intro i t; simp
    | succ m ih =>
      intro i t
      obtain ⟨h1, h2⟩ := ih i t
      refine ⟨?_, ?_⟩
      · have e1 : (y ^ (m + 1))⁻¹ * ψ (e6Data_valid.xm k (Pi.single i 1) t) * y ^ (m + 1) =
            y⁻¹ * ((y ^ m)⁻¹ * ψ (e6Data_valid.xm k (Pi.single i 1) t) * y ^ m) * y := by
          rw [pow_succ]; group
        rw [e1, h1, (ha i _).1, ← mul_assoc, ← pow_succ']
      · have e1 : (y ^ (m + 1))⁻¹ * ψ (e6Data_valid.xm k (-Pi.single i 1) t) * y ^ (m + 1) =
            y⁻¹ * ((y ^ m)⁻¹ * ψ (e6Data_valid.xm k (-Pi.single i 1) t) * y ^ m) * y := by
          rw [pow_succ]; group
        rw [e1, h2, (ha i _).2, ← mul_assoc, ← pow_succ']
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  have hE := (e6Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E6 k
    posDef_cartan_E6 neighbour_E6 O).2
  have hsolv : ∀ a' : Fin (e6Datum k).rank → kˣ, ∃ s : Fin (e6Datum k).rank → kˣ,
      ∀ j, ∏ i, s i ^ (e6Datum k).cartan i j = a' j ^ 3 := fun a' =>
    PsiDiag.exists_prod_zpow_cartan_cube (A := (e6Datum k).cartan) _ (m := 3) TableB.cartanE6_adj a'
  have hpos : ∀ i : Fin (e6Datum k).rank, ∃ a' : kˣ, ∀ t,
      (y ^ 3)⁻¹ * ψ (e6Data_valid.xm k (Pi.single i 1) t) * y ^ 3 =
        ψ (e6Data_valid.xm k (Pi.single i 1) (((a' : kˣ) : k) ^ 3 * t)) :=
    fun i => ⟨a i, fun t => (hpow 3 i t).1⟩
  have hneg : ∀ i : Fin (e6Datum k).rank, ∃ φ : k → k, ∀ t,
      (y ^ 3)⁻¹ * ψ (e6Data_valid.xm k (-Pi.single i 1) t) * y ^ 3 =
        ψ (e6Data_valid.xm k (-Pi.single i 1) (φ t)) :=
    fun i => ⟨fun t => (((a i)⁻¹ : kˣ) : k) ^ 3 * t, fun t => (hpow 3 i t).2⟩
  obtain ⟨u, hu⟩ := PsiDiag.exists_mul_psi_mem_centralizer_cube hE rfl
    (e6Datum_isCTGroupDatum k).iSup_eq_top hsolv ψ hker (d := y ^ 3) hpos hneg
  rw [hcent, Subgroup.mem_bot] at hu
  have h3 : y ^ 3 ∈ ψ.range := by
    have : y ^ 3 = (ψ u)⁻¹ := eq_inv_of_mul_eq_one_left hu
    rw [this]
    exact ψ.range.inv_mem ⟨u, rfl⟩
  obtain ⟨g', hg', hgp⟩ := kgr_pow_mul_mem ψ.range hcn hg p
  have hp' : y ^ p ∈ ψ.range := by
    rw [hy, hgp, hcp, one_mul]
    exact hg'
  obtain ⟨u1, v1, h⟩ : IsCoprime (p : ℤ) ((3 : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 hp3
  have hy' : y = (y ^ p) ^ u1 * (y ^ 3) ^ v1 := by
    rw [← zpow_natCast, ← zpow_natCast y 3, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have h1 : ((p : ℤ) * u1 + ((3 : ℕ) : ℤ) * v1) = 1 := by linarith
    rw [mul_comm (p : ℤ) u1, mul_comm ((3 : ℕ) : ℤ) v1, h, zpow_one]
  have hym : y ∈ ψ.range := by
    rw [hy']
    exact ψ.range.mul_mem (ψ.range.zpow_mem hp' u1) (ψ.range.zpow_mem h3 v1)
  have hcy : c = y * g⁻¹ := by rw [hy]; group
  rw [hcy]
  exact ψ.range.mul_mem hym (ψ.range.inv_mem hg)

section ExcCertE6


theorem ggExcKGRank_E6 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E6 n f).K →* G) (hset : GGKnownSetting .E6 n f ψ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : ¬ GGExcRegime p f)
    (E : Subgroup G) (hEn : E ≤ Subgroup.normalizer (ψ.range : Set G)) (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGPsiInnerDiag (ggU .E6 n f).D ψ b) : Nat.card E ≤ p ^ 3 := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  obtain ⟨hpK, hp3, hne1, hne2⟩ := kgr_regime_arith f hf p hp hp2 hreg
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hEr : E ≤ ψ.range := fun b hb =>
    kgr_inn_E6 (k := GaloisField 2 f) ψ hker hcent (hEn hb) hcop (hE.2 b hb) (hdiag b hb)
  let iso : (ggU .E6 n f).K →* adjointGroup Tag.E6 (GaloisField 2 f) :=
    e6Isogeny (GaloisField 2 f)
  have hkerle : ψ.rangeRestrict.ker ≤ iso.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have : iso.ker = Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)) :=
      e6Isogeny_ker_eq_center
    rw [this]
    exact hker
  let θ : ψ.range →* adjointGroup Tag.E6 (GaloisField 2 f) :=
    MonoidHom.liftOfRightInverse ψ.rangeRestrict (Function.surjInv ψ.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨iso, hkerle⟩
  have hθ : ∀ z, θ (ψ.rangeRestrict z) = iso z := fun z =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let θE : E →* adjointGroup Tag.E6 (GaloisField 2 f) := θ.comp (Subgroup.inclusion hEr)
  have hcen3 : ∀ z ∈ Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)), z ^ 3 = 1 := by
    intro z hz
    obtain ⟨hcard, -⟩ := card_center_e6 (GaloisField 2 f)
    have hdvd : Nat.card (Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f))) ∣ 3 := by
      rw [hcard]; exact Nat.gcd_dvd_left _ _
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f))) ∣ 3 :=
      (orderOf_dvd_natCard _).trans hdvd
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  have hθinj : Function.Injective θE := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨z, hz⟩ := hEr x.2
    have h1 : iso z = 1 := by
      rw [← hθ]
      have : ψ.rangeRestrict z = Subgroup.inclusion hEr x := Subtype.ext hz
      rw [this]
      exact hx
    have hz' : z ∈ Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)) := by
      have : z ∈ iso.ker := h1
      rwa [show iso.ker = Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)) from
        e6Isogeny_ker_eq_center] at this
    have h3z : z ^ 3 = 1 := hcen3 z hz'
    have h3 : (x : G) ^ 3 = 1 := by rw [← hz, ← map_pow, h3z, map_one]
    have h4 : (x : G) = 1 := kgr_eq_one_of_pow_coprime hcop (hE.2 x x.2) h3
    exact Subtype.ext h4
  have hF : IsElemAbelian p θE.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg (fun w => (θE w : adjointGroup Tag.E6 (GaloisField 2 f)))
        (hE.1.is_comm.comm a b)
    · rintro _ ⟨a, rfl⟩
      have hap : a ^ p = 1 := Subtype.ext (by simpa using hE.2 a a.2)
      rw [← map_pow, hap, map_one]
  have hcardF : Nat.card θE.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm
  rw [← hq] at hpK
  have hcast : (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = ((2 ^ f : ℕ) : ZMod p) := by
    rw [hq]
  have key := kgr_rankLE3_E6 (GaloisField 2 f) hp hp3 hpK
    ⟨by rw [hcast]; exact hne1, by rw [hcast]; exact hne2⟩ _ hF
  exact hcardF ▸ key

end ExcCertE6

section ExcCertE7


theorem ggExcKGRank_E7 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .E7 n f).K →* G) (hset : GGKnownSetting .E7 n f ψ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : ¬ GGExcRegime p f)
    (E : Subgroup G) (hEn : E ≤ Subgroup.normalizer (ψ.range : Set G)) (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGPsiInnerDiag (ggU .E7 n f).D ψ b) : Nat.card E ≤ p ^ 3 := by
  obtain ⟨⟨hadm, hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := hset
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hcen : Subgroup.center (e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ := by
    obtain ⟨hcard, -⟩ :=
      card_center_e7 (GaloisField 2 f)
    rw [hq] at hcard
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hcard, hg])
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcen.le
  have hEr : E ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_E7 G n f ψ ψ.range
      ⟨⟨hadm, hrk⟩, ⟨rfl, hker⟩, hcomm, hlie⟩ b (hEn hb) (hdiag b hb)
    rw [hcent, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hE', hcard⟩ := kgr_pullback_adjoint .E7 n f G ψ p E hEr hinj hE
  have hiso : Function.Injective (e7Isogeny (GaloisField 2 f)) := by
    rw [← MonoidHom.ker_eq_bot_iff,
      e7Isogeny_ker_eq_center]
    exact hcen
  obtain ⟨hE'', hcard''⟩ := kgr_map_elemAbelian (e7Isogeny (GaloisField 2 f)) hiso p
    (E.comap ψ : Subgroup (e7Data_valid.minGroup (GaloisField 2 f))) hE'
  obtain ⟨hpK, hp3, hne1, hne2⟩ := kgr_regime_arith f hf p hp hp2 hreg
  rw [← hq] at hpK
  have hcast : (((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = ((2 ^ f : ℕ) : ZMod p) := by
    rw [hq]
  have key := kgr_rankLE3_E7 (GaloisField 2 f) hp hp3 hpK
    ⟨by rw [hcast]; exact hne1, by rw [hcast]; exact hne2⟩ _ hE''
  exact (le_of_eq (hcard.symm.trans hcard''.symm)).trans key

end ExcCertE7

section ExcCertTwE6


theorem ggExcKGRank_of_twE6 (h : GGExcKGRankTwE6) : GGExcKGRank := by
  intro t n f ht G _ _ ψ hset p hp hp2 hreg hexc E hEn hE hdiag
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggExcKGRank_F4 n f G ψ hset p hp hp2 hreg E hEn hE hdiag
  · exact ggExcKGRank_E6 n f G ψ hset p hp hp2 hreg E hEn hE hdiag
  · exact ggExcKGRank_E7 n f G ψ hset p hp hp2 hreg E hEn hE hdiag
  · exact ggExcKGRank_E8 n f G ψ hset p hp hp2 hreg (fun h' => hexc ⟨rfl, h'⟩) E hEn hE hdiag
  · exact h n f G ψ hset p hp hp2 hreg E hEn hE hdiag

end ExcCertTwE6

end KGRankKnown

end CFSG.StandardType
