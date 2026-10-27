module

public import CFSG.RankThree.GF2n.Tim79aSec2O2
public import CFSG.RankThree.GF2n.Tim79aSec22Ti
public import CFSG.RankThree.GF2n.Tim77Prop24Roots
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.SplitBNPair
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem Prop24Setup.centralizer_mul_eq_one {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) {a b : G} (ha : a ∈ A) (haL : a ∉ L) (hb : b ∈ Ab)
    (hbL : b ∉ Lb) {m : G} (hm : m ∈ M) (hcomm : a * b * m = m * (a * b)) : m = 1 := by
  have ha2 := S.sq_A ha
  have hb2 := S.sq_Ab hb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have haN : ∀ x ∈ M, a * x * a⁻¹ ∈ M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (S.A_le_normalizer_M ha) x).mp hx
  have hbN : ∀ x ∈ M, b * x * b⁻¹ ∈ M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (S.Ab_le_normalizer_M hb) x).mp hx
  have hm2 : m * m = 1 := by rw [← sq]; exact S.isElemAbelian_M.2 m hm
  have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
  have hn' : a * m * a ∈ M := by simpa [hainv] using haN m hm
  have hbm : b * m * b = a * m * a := by
    have h1 : b * m * b⁻¹ = a⁻¹ * m * a := by
      calc b * m * b⁻¹ = a⁻¹ * ((a * b) * m * (a * b)⁻¹) * a := by group
        _ = a⁻¹ * (m * (a * b) * (a * b)⁻¹) * a := by rw [hcomm]
        _ = a⁻¹ * m * a := by group
    rw [hainv, hbinv] at h1
    exact h1
  set n' := a * m * a with hn'def
  have hs : m * n' ∈ M := M.mul_mem hm hn'
  have e0 : a * m * a⁻¹ = n' := by rw [hainv]
  have e1 : a * n' * a⁻¹ = m := by
    rw [hainv, hn'def]
    calc a * (a * m * a) * a = (a * a) * m * (a * a) := by group
      _ = m := by rw [ha2]; group
  have hsa : a * (m * n') = (m * n') * a := by
    have : a * (m * n') * a⁻¹ = m * n' := by
      calc a * (m * n') * a⁻¹ = (a * m * a⁻¹) * (a * n' * a⁻¹) := by group
        _ = n' * m := by rw [e0, e1]
        _ = m * n' := S.comm_M hn' hm
    exact mul_inv_eq_iff_eq_mul.mp this
  have f0 : b * m * b⁻¹ = n' := by rw [hbinv]; exact hbm
  have f1 : b * n' * b⁻¹ = m := by
    rw [hbinv, ← hbm]
    calc b * (b * m * b) * b = (b * b) * m * (b * b) := by group
      _ = m := by rw [hb2]; group
  have hsb : b * (m * n') = (m * n') * b := by
    have : b * (m * n') * b⁻¹ = m * n' := by
      calc b * (m * n') * b⁻¹ = (b * m * b⁻¹) * (b * n' * b⁻¹) := by group
        _ = n' * m := by rw [f0, f1]
        _ = m * n' := S.comm_M hn' hm
    exact mul_inv_eq_iff_eq_mul.mp this
  have hsL : m * n' ∈ L := S.mem_L_of_commute_M ha haL hs hsa
  have hsLb : m * n' ∈ Lb := S.symm.mem_L_of_commute_M hb hbL hs hsb
  have hs1 : m * n' = 1 := by
    have : m * n' ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le hsL, S.Lb_le hsLb⟩
    rw [S.inf_eq_bot, Subgroup.mem_bot] at this
    exact this
  have hn'm : n' = m := by
    have : n' = m⁻¹ := eq_inv_of_mul_eq_one_right hs1
    rw [this, hminv]
  have hmA : a * m = m * a := by
    have : a * m * a = m := hn'm
    calc a * m = a * m * a * a := by rw [mul_assoc, ha2, mul_one]
      _ = m * a := by rw [this]
  have hmB : b * m = m * b := by
    have : b * m * b = m := by rw [hbm]; exact hn'm
    calc b * m = b * m * b * b := by rw [mul_assoc, hb2, mul_one]
      _ = m * b := by rw [this]
  have hmL : m ∈ L := S.mem_L_of_commute_M ha haL hm hmA
  have hmLb : m ∈ Lb := S.symm.mem_L_of_commute_M hb hbL hm hmB
  have : m ∈ A ⊓ Ab := Subgroup.mem_inf.mpr ⟨S.L_le hmL, S.Lb_le hmLb⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at this
  exact this

end CFSG.RankThree.GF2n.Tim77

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_commutator_eq_of_fixed_eq_one [Finite G] {N : Subgroup G}
    (hN : IsMulCommutative N) {t : G} (ht : t ∈ Subgroup.normalizer (N : Set G))
    (hfix : ∀ n ∈ N, t * n * t⁻¹ = n → n = 1) : ∀ n ∈ N, ∃ m ∈ N, n = ⁅m, t⁆ := by
  have hconj : ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun n hn => (Subgroup.mem_normalizer_iff.mp ht n).mp hn
  have hcomm : ∀ x ∈ N, ∀ z ∈ N, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hN.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  let φ : N → N := fun m => ⟨⁅(m : G), t⁆, by
    have : ⁅(m : G), t⁆ = (m : G) * (t * (m : G) * t⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this]
    exact N.mul_mem m.2 (N.inv_mem (hconj m m.2))⟩
  have hφinj : Function.Injective φ := by
    intro m m' hmm
    have h1 : ⁅(m : G), t⁆ = ⁅(m' : G), t⁆ := congrArg Subtype.val hmm
    have e : ∀ x : G, ⁅x, t⁆ = x * (t * x * t⁻¹)⁻¹ := fun x => by
      rw [commutatorElement_def]; group
    rw [e, e] at h1
    set d : G := (m : G)⁻¹ * m' with hd
    have hdN : d ∈ N := N.mul_mem (N.inv_mem m.2) m'.2
    have hfixd : t * d * t⁻¹ = d := by
      have hm' : (m' : G) * (t * (m' : G) * t⁻¹)⁻¹ = (m : G) * (t * (m : G) * t⁻¹)⁻¹ := h1.symm
      have hA : t * (m : G) * t⁻¹ ∈ N := hconj m m.2
      have hB : t * (m' : G) * t⁻¹ ∈ N := hconj m' m'.2
      have : (m : G)⁻¹ * m' = (t * (m : G) * t⁻¹)⁻¹ * (t * (m' : G) * t⁻¹) := by
        have hh : (m' : G) = (m : G) * (t * (m : G) * t⁻¹)⁻¹ * (t * (m' : G) * t⁻¹) := by
          calc (m' : G) = ((m' : G) * (t * (m' : G) * t⁻¹)⁻¹) * (t * (m' : G) * t⁻¹) := by group
            _ = _ := by rw [hm']
        calc (m : G)⁻¹ * m' =
            (m : G)⁻¹ * ((m : G) * (t * (m : G) * t⁻¹)⁻¹ * (t * (m' : G) * t⁻¹)) := by
              rw [← hh]
          _ = _ := by group
      calc t * d * t⁻¹ = (t * (m : G)⁻¹ * t⁻¹) * (t * (m' : G) * t⁻¹) := by rw [hd]; group
        _ = (t * (m : G) * t⁻¹)⁻¹ * (t * (m' : G) * t⁻¹) := by group
        _ = d := by rw [← this]
    have hd1 : d = 1 := hfix d hdN hfixd
    apply Subtype.ext
    have : (m : G)⁻¹ * m' = 1 := hd1
    exact inv_mul_eq_one.mp this
  intro n hn
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hφinj ⟨n, hn⟩
  exact ⟨m, m.2, (congrArg Subtype.val hm).symm⟩

variable {M V Q P H : Subgroup G}

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem exists_noncommuting_conj :
    ∃ h ∈ H, ∃ u ∈ V, ∃ v ∈ conjSubgroup h V, u * v ≠ v * u := by
  by_contra hall
  push Not at hall
  have hcomm : ∀ g ∈ H, ∀ h ∈ H, ∀ u ∈ conjSubgroup g V, ∀ v ∈ conjSubgroup h V,
      u * v = v * u := by
    intro g hg h hh u hu v hv
    have hu' : g⁻¹ * u * g ∈ V := mem_conjSubgroup.mp hu
    have hv' : g⁻¹ * v * g ∈ conjSubgroup (g⁻¹ * h) V := by
      rw [mem_conjSubgroup]
      have := mem_conjSubgroup.mp hv
      rw [show (g⁻¹ * h)⁻¹ * (g⁻¹ * v * g) * (g⁻¹ * h) = h⁻¹ * v * h by group]
      exact this
    have := hall (g⁻¹ * h) (H.mul_mem (H.inv_mem hg) hh) _ hu' _ hv'
    calc u * v = g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = v * u := by group
  have hX : Assembly.IsElemAbelian 2 (xOf V H) := by
    unfold xOf
    rw [iSup_subtype']
    refine CFSG.CGT.Timmesfeld75.isElemAbelian_iSup_of_comm
      (fun U : ↥(omegaOf V H) => (U : Subgroup G)) ?_ ?_
    · rintro ⟨U, h, hh, rfl⟩ x hx
      exact (isElemAbelian_conjSubgroup hc.elemAb h).2 x hx
    · rintro ⟨U, g, hg, rfl⟩ ⟨U', h, hh, rfl⟩ a ha b hb
      exact hcomm g hg h hh a ha b hb
  have hle : xOf V H ≤ inSubgroup (pCore 2) H :=
    Tim78.le_inSubgroup_pCore (xOf_le_H hc.V_le_H) (H_le_normalizer_xOf V H)
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hX)
  exact hc.notLe ((le_xOf ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩).trans hle)

theorem inf_centralizer_xOf_eq_bot : V ⊓ Subgroup.centralizer (xOf V H : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨⟨c, hc'⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hcV, hcX⟩ := Subgroup.mem_inf.mp hc'
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  obtain ⟨h, hh, u, hu, v, hv, huv⟩ := hc.exists_noncommuting_conj
  apply huv
  have hle : conjSubgroup h V ≤ Subgroup.normalizer (V : Set G) := by
    intro w hw
    have hwX : w ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hh) hw
    have hcw : w * c = c * w := Subgroup.mem_centralizer_iff.mp hcX w hwX
    exact hc.normalizer_eq ▸ hc.mem_M_of_commute hcV hc1' hcw
  have habel := Tim77.tim77_2_3 hc.elemAb hc.ti hle
  exact congrArg Subtype.val (habel.1.is_comm.comm ⟨u, Subgroup.mem_sup_left hu⟩
    ⟨v, Subgroup.mem_sup_right hv⟩)

theorem wOf_inf_centralizer_xOf_eq_bot :
    wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) = ⊥ := by
  by_contra hne
  have hC2 : IsPGroup 2 (wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) : Subgroup G) :=
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian).to_le inf_le_left
  have hPC : P ≤ Subgroup.normalizer
      ((wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) : Subgroup G) : Set G) := fun p hp =>
    mem_normalizer_inf (H_le_normalizer_wOf V H (hc.PleH hp))
      (mem_normalizer_centralizer (H_le_normalizer_xOf V H (hc.PleH hp)))
  have := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
    hc.isPGroup_P hC2 hne hPC
  rw [hc.centralizer_P_eq] at this
  apply this
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ V ⊓ Subgroup.centralizer (xOf V H : Set G) :=
    ⟨hx.2, (Subgroup.mem_inf.mp hx.1).2⟩
  rw [hc.inf_centralizer_xOf_eq_bot] at hxV
  exact hxV

end MinCex

end CFSG.RankThree.GF2n.Tim79a
