module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aULift
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
import CFSG.Quasithin.Background.A3Structure312Quotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.Adapters.Certificate43Check
import CFSG.GroupTheory.PermutingProducts
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112u_l2_inv {L B T : Subgroup G} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : LieModel (BarInf L) .PSL 2 p f)
    (hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L) (hT : IsPGroup 2 ↥T)
    (hBN : B ≤ normalizer (L : Set G)) (hBT : Permutes B T) (hBab : IsMulCommutative ↥B)
    (hBo : Odd (Nat.card ↥B)) (hB3 : ¬ IsPGroup 3 ↥B)
    (hfaith : ∀ b (hb : b ∈ B), inducedBarInfAutHom L ⟨b, hBN hb⟩ = 1 → b = 1)
    (hinn : ∀ b (hb : b ∈ B),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    ∃ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ = b⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hLp (by decide))
  have hf1 : 1 ≤ f := hLp.admissible.2.1
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set φ := inducedBarInfAutHom L with hφdef
  set X : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hXdef
  have hZ : center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) = ⊥ :=
    CFSG.GorensteinWalter.psl2_center_eq_bot _
  have hinj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : ∀ w : BarInf L, w * z = z * w := by
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    have hc : e z ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f)) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hzc w']
    rw [hZ, mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  let eX : BarInf L ≃* ↥X := MonoidHom.ofInjective hinj
  haveI : Finite ↥X := Finite.of_equiv _ eX.toEquiv
  set Bφ : Subgroup (MulAut (BarInf L)) := (B.subgroupOf N).map φ with hBφdef
  set Sφ : Subgroup (MulAut (BarInf L)) := ((T ⊓ N).subgroupOf N).map φ with hSφdef
  have hBX : Bφ ≤ X := by
    rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
    have hbB : b ∈ B := hb
    exact hinn b hbB
  have hBTN := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBN inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hBT.symm hBN).symm
  have hperm : (Bφ : Set (MulAut (BarInf L))) * Sφ = Sφ * Bφ :=
    CFSG.GroupTheory.map_permutes_map φ hBTN
  have hpermX := CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBX inf_le_right
    (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hperm.symm hBX).symm
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf ((Sφ ⊓ X).subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hS2 : IsPGroup 2 ↥Sφ :=
        ((hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm).map φ
      exact (hS2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    · let fL : ↥L →* ↥X := (MulAut.conj : BarInf L →* MulAut (BarInf L)).rangeRestrict.comp
        (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      have hfL : Function.Surjective fL :=
        (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)
      have hle : ((T ⊓ L).subgroupOf L).map fL ≤ (Sφ ⊓ X).subgroupOf X := by
        rintro _ ⟨⟨t, htL⟩, ht, rfl⟩
        have htT : t ∈ T := (mem_inf.mp (show t ∈ T ⊓ L from ht)).1
        rw [mem_subgroupOf]
        refine ⟨⟨⟨t, le_normalizer htL⟩, ?_, uc22s2113_inducedBarInfAutHom_of_mem htL⟩,
          (fL ⟨t, htL⟩).2⟩
        show t ∈ T ⊓ N
        exact mem_inf.mpr ⟨htT, le_normalizer htL⟩
      have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index :=
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hTL).2.2
      change ¬ 2 ∣ ((Sφ ⊓ X).subgroupOf X).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact fun h2 => hidx
        (h2.trans ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hfL)))
  let ψ : ↥X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f) := eX.symm.trans e
  set S' := ((Sφ ⊓ X).subgroupOf X).map ψ.toMonoidHom with hS'def
  set B' := (Bφ.subgroupOf X).map ψ.toMonoidHom with hB'def
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map ψ.toMonoidHom ψ.surjective hS
  have hBinj : Function.Injective (φ.subgroupMap (B.subgroupOf N)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨b, hbN⟩, hb⟩ h1
    have hbB : b ∈ B := hb
    have h2 : φ ⟨b, hbN⟩ = 1 := congrArg Subtype.val h1
    exact Subtype.ext (Subtype.ext (hfaith b hbB h2))
  let eBB : ↥(B.subgroupOf N) ≃* ↥Bφ :=
    MulEquiv.ofBijective (φ.subgroupMap (B.subgroupOf N)) ⟨hBinj, φ.subgroupMap_surjective _⟩
  let eB : ↥B ≃* ↥B' :=
    ((subgroupOfEquivOfLe hBN).symm.trans eBB).trans ((subgroupOfEquivOfLe hBX).symm.trans
      ((Bφ.subgroupOf X).equivMapOfInjective ψ.toMonoidHom ψ.injective))
  have hB'odd : Odd (Nat.card ↥B') := by
    rw [← Nat.card_congr eB.toEquiv]
    exact hBo
  have hB'3 : ¬ IsPGroup 3 ↥B' := fun h => hB3 (h.of_equiv eB.symm)
  have hB'ab : IsMulCommutative ↥B' := by
    refine ⟨⟨fun a b => eB.symm.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact hBab.is_comm.comm _ _
  have hc : CFSG.ASVolI.burnsideA315x_Config _ S' B' :=
    ⟨hS', hB'odd, hB'3, Or.inl hB'ab, CFSG.GroupTheory.map_permutes_map ψ.toMonoidHom hpermX⟩
  obtain ⟨-, -, s', hs', hinv'⟩ := CFSG.ASVolI.burnsideA315x_l2_core hp2 hf1 hc
  obtain ⟨σ, hσ, rfl⟩ := mem_map.1 hs'
  have hσS : (σ : MulAut (BarInf L)) ∈ Sφ := (mem_inf.1 (mem_subgroupOf.1 hσ)).1
  obtain ⟨t₀, ht₀, ht₀σ⟩ := mem_map.1 hσS
  have hinvφ : ∀ b ∈ B.subgroupOf N, φ t₀ * φ b * (φ t₀)⁻¹ = (φ b)⁻¹ := by
    intro b hb
    have hbX : φ b ∈ X := hBX (mem_map_of_mem φ hb)
    have hβ : (⟨φ b, hbX⟩ : ↥X) ∈ Bφ.subgroupOf X := mem_subgroupOf.2 (mem_map_of_mem φ hb)
    have h1 := hinv' (ψ.toMonoidHom ⟨φ b, hbX⟩) (mem_map_of_mem _ hβ)
    have h2 : σ * ⟨φ b, hbX⟩ * σ⁻¹ = (⟨φ b, hbX⟩ : ↥X)⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h1
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [← ht₀σ] at h3
    exact h3
  have hS2N : IsPGroup 2 ↥((T ⊓ N).subgroupOf N) :=
    (hT.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  have hBoN : Odd (Nat.card ↥(B.subgroupOf N)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv]
    exact hBo
  have hfaithN : ∀ b ∈ B.subgroupOf N, φ b = 1 → b = 1 := fun b hb h1 =>
    Subtype.ext (hfaith b hb h1)
  obtain ⟨t, ht, htinv⟩ := uc22s2112u_lift_inv φ hS2N hBoN hBTN hfaithN ht₀ hinvφ
  refine ⟨t, (mem_inf.1 (mem_subgroupOf.1 ht)).1, fun b hb => ?_⟩
  have h := congrArg Subtype.val (htinv ⟨b, hBN hb⟩ hb)
  simpa using h

theorem uc22s2112u_l2_false {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀) (hH : H1930 D)
    (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) {L : Subgroup G} (hL : L ∈ calC D.M)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hLp : LieModel (BarInf L) .PSL 2 p f)
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    (hinn : ∀ b (hb : b ∈ c.B0) (hbN : b ∈ normalizer (L : Set G)),
      inducedBarInfAutHom L ⟨b, hbN⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    False := by
  let c₀ : Ctx21 D Ch :=
    { c with B := c.B0, hB := c.hB0, hle := le_rfl, hch := hCh c.L0 c.B0 c.hch }
  have hBN : c.B0 ≤ normalizer (L : Set G) := h5 hH c₀ L hL
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB0
  have hBo : Odd (Nat.card ↥c.B0) := ch214_odd_card c.hpi
  obtain ⟨r, hr, hrd, hr3⟩ := uc22p20o_prime_sub_one_ne_three hn3
  have hrB : r ∣ Nat.card ↥c.B0 := by
    have hpi : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, hrd⟩
    exact hpi.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : ¬ IsPGroup 3 ↥c.B0 := by
    intro h3
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    rw [hk] at hrB
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow hrB))
  have hne : c.B0 ≠ ⊥ := by
    intro h
    rw [h] at hB3
    exact hB3 IsPGroup.of_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, ht⟩ := uc22s2112u_l2_inv hp hp2 hLp (uc22p2214_isSylowOf_inf D.sylowM hL.1)
    D.sylowM.isPGroup hBN hBT hBab hBo hB3
    (fun b hb h1 => hfaith b hb
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN hb) h1))
    (fun b hb => hinn b hb (hBN hb))
  obtain ⟨hi, -⟩ := c.hch
  exact hi hne t htT (uc22s2112u_mem_normalizer_of_inv ht) ht

end CFSG.LocalAnalysis.UniquenessCase.UC22
