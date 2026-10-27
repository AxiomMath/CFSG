module

public import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
public import CFSG.RankThree.PartTwo.Sec17.Item1729
import CFSG.RankThree.PartTwo.Sec13.Item137ProofTau
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.Asc83Table.GL23
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

@[expose] def Item137Invert : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e →
              e ∈ Subgroup.centralizer (P : Set G) → e ∉ Subgroup.zpowers c →
              (Sec8.IsZ3PGLThreePi (lBarA e K E) ∨
                Nonempty (lBarA e K E ≃*
                  Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
                Nonempty (lBarA e K E ≃*
                  Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) →
                ∃ s ∈ K ⊓ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, s * z * s⁻¹ = z⁻¹

section Parity

variable {G : Type} [Group G] [Finite G]

theorem false_of_ncard_omegaA_eq_nine {E : Subgroup G} {c u : G} (hc3 : c ^ 3 = 1)
    (huE : u ∈ Subgroup.normalizer (E : Set G))
    (hτ : ∀ v ∈ E, u * v * u⁻¹ ∈ Subgroup.zpowers v → v ∈ Subgroup.zpowers c)
    (hu4 : ∀ v ∈ E, u ^ 4 * v * (u ^ 4)⁻¹ = v) (hcΩ : Subgroup.zpowers c ∉ omegaA E)
    (h9 : (omegaA E).ncard = 9) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (omegaA E) := Fintype.ofFinite _
  let f : Function.End (omegaA E) := fun F =>
    ⟨F.1.map (MulAut.conj u).toMonoidHom, (map_conj_mem_omegaA_iff huE).mpr F.2⟩
  have hpow : ∀ (n : ℕ) (F : omegaA E),
      ((f ^ n) F).1 = F.1.map (MulAut.conj (u ^ n)).toMonoidHom := by
    intro n
    induction n with
    | zero =>
      intro F
      rw [pow_zero, pow_zero, map_one]
      exact (Subgroup.map_id _).symm
    | succ n ih =>
      intro F
      rw [pow_succ]
      change ((f ^ n) (f F)).1 = _
      rw [ih, pow_succ, map_mul, Subgroup.map_map]
      rfl
  have hf4 : f ^ 2 ^ 2 = 1 := by
    funext F
    apply Subtype.ext
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hpow]
    change F.1.map (MulAut.conj (u ^ 4)).toMonoidHom = F.1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyE : y ∈ E := F.2.1 hy
      change u ^ 4 * y * (u ^ 4)⁻¹ ∈ F.1
      rw [hu4 y hyE]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      change u ^ 4 * x * (u ^ 4)⁻¹ = x
      exact hu4 x (F.2.1 hx)
  have hfix : Function.fixedPoints f = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro F hF
    have hF' : F.1.map (MulAut.conj u).toMonoidHom = F.1 := congrArg Subtype.val hF
    obtain ⟨hFE, hF3, a, haF, -⟩ := F.2
    have haE : a ∈ E := hFE (haF ▸ Subgroup.mem_zpowers a)
    have hua : u * a * u⁻¹ ∈ Subgroup.zpowers a := by
      rw [← haF, ← hF']
      exact ⟨a, haF ▸ Subgroup.mem_zpowers a, rfl⟩
    have hac := hτ a haE hua
    apply hcΩ
    have hle : F.1 ≤ Subgroup.zpowers c := by
      rw [haF]
      exact Subgroup.zpowers_le.mpr hac
    have hcard : Nat.card (Subgroup.zpowers c) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
    rw [← Subgroup.eq_of_le_of_card_ge hle (by rw [hF3]; exact hcard)]
    exact F.2
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 2) hf4
  have hcard0 : Fintype.card (Function.fixedPoints f) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun x => (Set.eq_empty_iff_forall_notMem.mp hfix) x.1 x.2⟩
  rw [hcard0, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, h9] at hmod
  exact absurd hmod (by decide)

end Parity

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_tau_of_config (h131 : Item131) (hspor : SporadicModels131) {A L P E F : Subgroup G}
    {c t : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hcfg : Config137 A c L P E F t) :
    ∃ u ∈ L, u ∈ Subgroup.normalizer (E : Set G) ∧
      (∀ v ∈ E, u * v * u⁻¹ ∈ Subgroup.zpowers v → v ∈ Subgroup.zpowers c) ∧
      ∀ v ∈ E, u ^ 4 * v * (u ^ 4)⁻¹ = v := by
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨-, hE3, hE27, ⟨eGL⟩⟩ := hcfg.facts (Or.inl rfl)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hEdec, -⟩ := hcfg
  have hB3 : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) := isElemAbelian_inf_right hE3 L
  have h9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hLc y hy.2).symm k).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hEdec, hE27, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot hc3 hcL).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one] at hcard
    omega
  exact exists_tau_of_autIn_gl hc3 hcL hLc hEdec hB3 h9 eGL

theorem item137Core_of (h131 : Item131) (h133 : Item133) (h13S : Sec17.Item13Setup)
    (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local) (hinv : Item137Invert) :
    Item137Core := by
  intro G _ _ A c L h hM P E F t hcfg hST hU
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨-, hE3, hE27, ⟨eGL⟩⟩ := hcfg.facts (Or.inl rfl)
  have hcfg' := hcfg
  obtain ⟨hP, hAP, -, -, -, -, -, -, -, -, -, -, -, -, -, hEdec, -⟩ := hcfg'
  have hB3 : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) := isElemAbelian_inf_right hE3 L
  have h9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hLc y hy.2).symm k).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hEdec, hE27, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot hc3 hcL).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one] at hcard
    omega
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  obtain ⟨e₀, K₀, he₀, hK₀⟩ := h13S G h.toPartTwoStanding h.partTwoS_eq E hXF hXE.2
  have hne : Subgroup.zpowers e₀ ≠ Subgroup.zpowers c := by
    intro heq
    have hcΩ : Subgroup.zpowers c ∈ omegaA E := heq ▸ he₀
    have hKc : K₀ ∈ lA E c := by
      rw [← lA_congr heq]
      exact hK₀
    have hD' : Sec13Data G E c K₀ :=
      { h.toPartTwoStanding with
        partTwoS_eq := h.partTwoS_eq
        mem_partTwoF := hXF
        not_mem_partTwoT := hXE.2
        zpowers_mem_omegaA := hcΩ
        mem_lA := hKc }
    have h3K := three_dvd_card_of_sec13Data h131 hspor hD'
    have hspor' := hspor
    obtain ⟨-, ⟨-, hM12z⟩, -⟩ := hspor'
    obtain ⟨φ⟩ := hM
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      center_eq_bot_of_mulEquiv φ hM12z
    have hXcL : E ≤ Subgroup.zpowers c ⊔ L := hEdec ▸ sup_le_sup_left inf_le_right _
    have hKL := eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZ
      hXcL hE3 (fun F' hF' hXF' => (hXF.2.1 F' hF' hXF') ▸ le_rfl)
      hD'.mem_thetaComponentsAt h3K
    rw [hKL] at hD'
    exact false_of_autIn_gl h131 hspor hD' hcL eGL
  obtain ⟨d, hdL, hd1, hd3, hPP, -, hdZ, -, -⟩ :=
    exists_commutator_eq_zpowers_of_isSylowOf h131 hspor h414 h hM hP hAP
  have hEP : E ≤ P := by
    obtain ⟨-, -, -, -, hΔ, -⟩ := hcfg
    have hmem : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
        Nat.card B = 27} := by
      rw [hΔ]
      exact Or.inr (Or.inr (Or.inl rfl))
    exact hmem.1
  have hdE : d ∈ E := Sec15.mem_of_mem_partTwoF hXF hd3 fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hdZ x (hEP hx)).symm
  have hdB : d ∈ E ⊓ L := ⟨hdE, hdL⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hLc y hy.2).symm k).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have he₀E : e₀ ∈ E := he₀.1 (Subgroup.mem_zpowers e₀)
  have he₀' : e₀ ∈ ((Subgroup.zpowers c ⊔ (E ⊓ L) : Subgroup G) : Set G) := hEdec ▸ he₀E
  rw [hset] at he₀'
  obtain ⟨a, ha, y₀, hy₀, hay⟩ := he₀'
  simp only at hay
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  subst hay
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    apply hne
    rw [mul_one]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers c i))
      ?_
    have h3 := he₀.2.1
    rw [mul_one] at h3
    rw [h3, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
  obtain ⟨w, hwL, hwN, hwy⟩ :=
    exists_conj_eq_of_ne_one hc3 hcL hLc hEdec hB3 h9 eGL hy₀ hdB hy₀1 hd1
  have hwc : ∀ j : ℤ, w * c ^ j * w⁻¹ = c ^ j := fun j => by
    rw [(Commute.zpow_right (show Commute w c from hLc w hwL) j).eq, mul_inv_cancel_right]
  set e := c ^ i * d with he
  have hwe : w * (c ^ i * y₀) * w⁻¹ = e := by
    rw [show w * (c ^ i * y₀) * w⁻¹ = (w * c ^ i * w⁻¹) * (w * y₀ * w⁻¹) by group, hwc, hwy]
  have heΩ : Subgroup.zpowers e ∈ omegaA E := by
    rw [← hwe, ← show (Subgroup.zpowers (c ^ i * y₀)).map (MulAut.conj w).toMonoidHom =
        Subgroup.zpowers (w * (c ^ i * y₀) * w⁻¹) by rw [MonoidHom.map_zpowers]; rfl]
    exact (map_conj_mem_omegaA_iff hwN).mpr he₀
  set K := K₀.map (MulAut.conj w).toMonoidHom with hKdef
  have hK : K ∈ lA E e := by
    rw [← hwe]
    exact (map_conj_mem_lA_iff hwN).mpr hK₀
  have hcZ : ∀ x ∈ P, c * x = x * c := by
    intro x hx
    have hle : A ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le h.A_le_centralizer h.le_centralizer
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hP.le hx))).symm
  have heZ : e ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : c ^ i * x = x * c ^ i := by
      have : Commute c x := hcZ x hx
      exact (this.zpow_left i).eq
    calc x * (c ^ i * d) = c ^ i * x * d := by rw [← mul_assoc, h1]
      _ = c ^ i * (d * x) := by rw [mul_assoc, (hdZ x hx).symm]
      _ = c ^ i * d * x := (mul_assoc _ _ _).symm
  have hdc : d ∉ Subgroup.zpowers c := fun hdc => by
    have : d ∈ Subgroup.zpowers c ⊓ L := ⟨hdc, hdL⟩
    rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at this
    exact hd1 this
  have hec : e ∉ Subgroup.zpowers c := by
    intro hmem
    apply hdc
    have := (Subgroup.zpowers c).mul_mem
      (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c i)) hmem
    rwa [he, inv_mul_cancel_left] at this
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  obtain ⟨u, -, huE, hτ, hu4⟩ := exists_tau_of_autIn_gl hc3 hcL hLc hEdec hB3 h9 eGL
  rcases h133 G E e K hD hST with h1 | ⟨h2, -⟩ | h3 | h4 | h5 | h6
  ·
    exfalso
    have hue := h1 huE
    have : u * e * u⁻¹ ∈ Subgroup.zpowers e :=
      (Subgroup.mem_normalizer_iff.mp hue e).mp (Subgroup.mem_zpowers e)
    exact hec (hτ e (hD.mem_A) this)
  ·
    exfalso
    obtain ⟨φ, hφ⟩ : ∃ φ : wStar E →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4),
        Function.Injective φ := by
      rcases h2 with h2 | h2
      · obtain ⟨ψ⟩ := h2
        exact ⟨(MonoidHom.inr _ _).comp ψ.toMonoidHom,
          (Prod.mk_right_injective 1).comp ψ.injective⟩
      · obtain ⟨ψ⟩ := h2
        exact ⟨ψ.toMonoidHom, ψ.injective⟩
    let g : QuaternionGroup 2 →* wStar E :=
      (Subgroup.inclusion (autIn_mono (le_top : L ≤ ⊤))).comp
        (eGL.symm.toMonoidHom.comp CFSG.RankThree.Asc83Table.quatHom)
    have hg : Function.Injective g :=
      (Subgroup.inclusion_injective (autIn_mono (le_top : L ≤ ⊤))).comp (eGL.symm.injective.comp
        CFSG.RankThree.Asc83Table.quatHom_injective)
    have hsq := sq_eq_one_of_q8_rel hφ (x := g (QuaternionGroup.a 1))
      (y := g (QuaternionGroup.xa 0))
      (by rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide,
        map_one])
      (by rw [← map_pow, ← map_pow,
        show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.xa 0 ^ 2 by decide])
      (by rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
        show QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
          ((QuaternionGroup.a 1)⁻¹ : QuaternionGroup 2) by decide])
    rw [← map_pow] at hsq
    have := hg (hsq.trans (map_one g).symm)
    exact absurd this (by decide)
  ·
    exfalso
    obtain ⟨-, -, -, -, -, hΩeq, hΩ9, -⟩ := h3
    have hcΩ : Subgroup.zpowers c ∉ omegaA E := by
      rw [hΩeq]
      rintro ⟨g, hg, hgc⟩
      apply hec
      have hgH := hU hg
      have h1 : (Subgroup.zpowers c).map (MulAut.conj g⁻¹).toMonoidHom = Subgroup.zpowers c :=
        map_conj_eq_iff_mem_normalizer.mpr (inv_mem hgH)
      have h2 : Subgroup.zpowers e =
          (Subgroup.zpowers c).map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [hgc, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        congr 1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [← h1, ← h2]
      exact Subgroup.mem_zpowers e
    exact false_of_ncard_omegaA_eq_nine hc3 huE hτ hu4 hcΩ hΩ9
  all_goals
    obtain ⟨s, hsKP, hsinv⟩ := hinv G A c L h hM P E F t hcfg hST hU e K heΩ hK heZ hec
      (by tauto)
    refine ⟨s, hsKP.2, fun hsH => ?_⟩
    have hse : s * e * s⁻¹ = e := by
      have hKC : K ≤ Subgroup.centralizer ({e} : Set G) :=
        Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hKC hsKP.1), mul_inv_cancel_right]
    have hsd : s * d * s⁻¹ = d⁻¹ := hsinv d (hPP ▸ Subgroup.mem_zpowers d)
    have hsc : s * c * s⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hsH c).mp (Subgroup.mem_zpowers c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsc
    have hsci : s * c ^ i * s⁻¹ = c ^ (k * i) := by
      rw [← conj_zpow, ← hk, ← zpow_mul]
    have h1 : c ^ (k * i) * d⁻¹ = c ^ i * d := by
      rw [← hsci, ← hsd]
      calc s * c ^ i * s⁻¹ * (s * d * s⁻¹) = s * (c ^ i * d) * s⁻¹ := by group
        _ = c ^ i * d := hse
    have hdd : d * d ∈ Subgroup.zpowers c ⊓ L := by
      refine ⟨?_, L.mul_mem hdL hdL⟩
      have : d * d = (c ^ i)⁻¹ * c ^ (k * i) := by
        calc d * d = (c ^ i)⁻¹ * (c ^ i * d) * d := by group
          _ = (c ^ i)⁻¹ * (c ^ (k * i) * d⁻¹) * d := by rw [h1]
          _ = (c ^ i)⁻¹ * c ^ (k * i) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c i))
        (Subgroup.zpow_mem_zpowers c _)
    rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at hdd
    apply hd1
    calc d = d ^ 3 * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3, hdd, inv_one, one_mul]

end Core

end CFSG.RankThree.PartTwo.Sec13
