module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.LocalAnalysis.EvenBN.G2.G2LieModelFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Inn
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Offender

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.K148
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}
variable {H : Subgroup G} {Y Z : Submodule (ZMod 2) V}

section G2


theorem g2_innerOnSec [Finite G] [Finite V] {L B : Subgroup G} {n : ℕ} (hodd : Odd n)
    (hn : 1 < n) (hG2 : IsG2 ↥L n) (hBe : CFSG.IsElementaryAbelian 2 ↥B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hZY : Z ≤ Y)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y) :
    (∀ b ∈ B, ∃ l ∈ L, ∀ y ∈ Y, ρ b y - ρ l y ∈ Z) ∧
      ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y := by
  classical
  haveI : IsSimpleGroup ↥L := CFSG.LocalAnalysis.EvenBN.G2.isSimpleGroup_of_lieModel_G2 hG2
  have hZL : Subgroup.center ↥L = ⊥ := by
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel ↥L .G2 2 n :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
    obtain ⟨-, K, hfield, hfin, hchar, hKcard, ⟨e⟩⟩ :=
      CFSG.Quasithin.B42G2Id.exists_quasithinG2_of_chevalleyExceptionalModel hCE
    letI := hfield
    letI := hfin
    letI := hchar
    haveI : Fintype K := Fintype.ofFinite K
    refine CFSG.LocalAnalysis.RankThreeUC.S15.g2_center_eq_bot (F := K) (n := n)
      (by omega) ?_ e
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hcen : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
    intro x hx hxc
    have hmem : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((hxc y y.2).symm)
    rw [hZL, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨hBc, hB2⟩ := elemAb_facts hBe
  have hLH : L ≤ L ⊔ B := le_sup_left
  have hBH : B ≤ L ⊔ B := le_sup_right
  have hinner : ∀ b ∈ B, ∃ l ∈ L, ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹ := by
    intro b hb
    let bn : ↥(Subgroup.normalizer (L : Set G)) := ⟨b, hBN hb⟩
    have hbn2 : bn ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hB2 b hb
    have hα2 : (AutAux.condHom L bn) ^ 2 = 1 := by
      rw [← map_pow, hbn2, map_one]
    obtain ⟨g, hg⟩ :=
      (g2_twoAut_inner hodd hn hG2 (AutAux.condHom L bn) ⟨1, by simpa using hα2⟩ :
        AutAux.condHom L bn ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
    refine ⟨(g : G), g.2, fun x hx => ?_⟩
    have h1 : (AutAux.condHom L bn) ⟨x, hx⟩ = g * ⟨x, hx⟩ * g⁻¹ := by
      rw [← hg]
      exact MulAut.conj_apply g ⟨x, hx⟩
    have h2 := congrArg Subtype.val h1
    rw [AutAux.condHom_apply] at h2
    simpa using h2
  have hsec : ∀ b ∈ B, ∃ l ∈ L, ∀ y ∈ Y, ρ b y - ρ l y ∈ Z := by
    intro b hb
    obtain ⟨l, hl, hbl⟩ := hinner b hb
    exact ⟨l, hl, sub_mem_of_inducesInner hcen hBN hBc hB2 hZY hY hZ hirr hb hl hbl⟩
  refine ⟨hsec, ?_⟩
  intro W hWL hZW hWY
  refine hirr W ?_ hZW hWY
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.K148.isInvariant_sup hWL ?_
  intro b hb w hw
  obtain ⟨l, hl, hbl⟩ := hsec b hb
  have h1 : ρ l w ∈ W := hWL l hl w hw
  have h2 : ρ b w - ρ l w ∈ Z := hbl w (hWY hw)
  have h3 : ρ b w = ρ l w + (ρ b w - ρ l w) := by abel
  rw [h3]
  exact W.add_mem h1 (hZW h2)

theorem g2_secNatural [Finite G] [Finite V] {L B : Subgroup G} {K : Type} [Field K] [Fintype K]
    [CharP K 2] {n : ℕ} (hodd : Odd n) (hn : 1 < n) (hG2 : IsG2 ↥L n)
    (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* ↥(cayleyGroup K))
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm1 : 1 ≤ m)
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) (hcost : secCost ρ B Y Z ≤ m) :
    m ≤ 3 * n ∧ 2 * n ≤ secCost ρ B Y Z ∧
      ∃ φ : SecQ Y Z ≃+ (Ix3 → K), ∀ (l : ↥L) (q : SecQ Y Z),
        φ (secHom hY hZ (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ B) l) q) =
          g2Act (e l) (φ q) := by
  classical
  haveI : IsSimpleGroup ↥L := CFSG.LocalAnalysis.EvenBN.G2.isSimpleGroup_of_lieModel_G2 hG2
  haveI : IsSimpleGroup ↥(cayleyGroup K) := by
    have hG2' : IsG2 ↥(cayleyGroup K) n := CFSG.Blueprint.LieModel.of_mulEquiv e hG2
    exact CFSG.LocalAnalysis.EvenBN.G2.isSimpleGroup_of_lieModel_G2 hG2'
  haveI : Finite (SecQ Y Z) := Module.finite_of_finite (ZMod 2)
  haveI : Module.Finite (ZMod 2) (SecQ Y Z) := Module.Finite.of_finite
  have hLH : L ≤ L ⊔ B := le_sup_left
  have hBH : B ≤ L ⊔ B := le_sup_right
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hn2 : 2 ≤ n := by omega
  let π : ↥(cayleyGroup K) →* (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) :=
    (secHom hY hZ).comp ((Subgroup.inclusion hLH).comp e.symm.toMonoidHom)
  have hπx : ∀ x, π x = secHom hY hZ (Subgroup.inclusion hLH (e.symm x)) := fun x => rfl
  have hπ : ∀ l : ↥L, π (e l) = secHom hY hZ (Subgroup.inclusion hLH l) := fun l => by
    rw [hπx, MulEquiv.symm_apply_apply]
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, y, hy, hly⟩ := hnt
      have h1 : π (e ⟨l, hl⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      rw [hπ, secHom_eq_one_iff] at h1
      exact hly (h1 y hy)
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  have hntM : Nontrivial (SecQ Y Z) := by
    obtain ⟨l, hl, y, hy, hly⟩ := hnt
    have hyZ : y ∉ Z := fun hyZ => hly (Z.sub_mem (hZ l (hLH hl) y hyZ) hyZ)
    exact secQ_nontrivial hy hyZ
  obtain ⟨hinnerSec, hirrL⟩ := g2_innerOnSec hodd hn hG2 hBe hBN hZY hY hZ hirr
  have hirrM : ∀ U : Submodule (ZMod 2) (SecQ Y Z),
      (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine secHom_irr (hY := hY) (hZ := hZ) hLH hZY hirrL U fun l u hu => ?_
    rw [← hπ]
    exact hU _ u hu
  set A : Subgroup (SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z) := secImg hY hZ B with hAdef
  have hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y := by
    intro a ha x
    rw [hAdef] at ha
    obtain ⟨y, hy⟩ := secImg_normalizes hLH hBN ha (e.symm x)
    refine ⟨e y, ?_⟩
    rw [hπx, hπ y]
    exact hy
  have hk := inf_secKer_eq hBN (fun l hl => hY l (hLH hl)) hZ hCB hnt le_rfl inf_le_left
  have hd : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ secKer ρ Y Z) := by
    rw [hk]
    exact hm
  have hcardA : Nat.card ↥A = 2 ^ m := by
    rw [hAdef]
    have h1 := card_secImg_mul (hY := hY) (hZ := hZ) hBH
    rw [hd] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardA
    have hp := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm1
    omega
  have hAe : CFSG.IsElementaryAbelian 2 ↥A := by
    rw [hAdef]
    exact secImg_isElementaryAbelian hBe
  have hM : Nat.card (SecQ Y Z) = 2 ^ (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) :=
    card_secQ hZY
  have hfix : Nat.card {q : SecQ Y Z // ∀ a ∈ A, a q = q} =
      2 ^ (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) - finrank (ZMod 2) ↥Z) := by
    rw [hAdef]
    exact card_fix_secImg (hY := hY) (hZ := hZ) hZY hBH
  have hZP : Z ≤ Y ⊓ P22x.modFix ρ Z B :=
    le_inf hZY (le_modFix fun a ha => hZ a (hBH ha))
  have hoff : Nat.card (SecQ Y Z) ≤
      Nat.card ↥A * Nat.card {q : SecQ Y Z // ∀ a ∈ A, a q = q} := by
    rw [hM, hcardA, hfix, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold secCost at hcost
    have h1 := Submodule.finrank_mono hZP
    have h2 := Submodule.finrank_mono (inf_le_left : Y ⊓ P22x.modFix ρ Z B ≤ Y)
    omega
  obtain ⟨φ, hφ⟩ :=
    CFSG.Quasithin.B42G2F.exists_natural_of_offender (K := K) (M := SecQ Y Z) (f := n)
      hKf hn2 π hπinj hntM hirrM A hnorm hAe hA1 hoff
  have hAle : A ≤ π.range := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨h, hh, rfl⟩ := ha
    obtain ⟨l, hl, hbl⟩ := hinnerSec (h : G) (Subgroup.mem_subgroupOf.1 hh)
    refine ⟨e ⟨l, hl⟩, ?_⟩
    rw [hπ]
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [secHom_mk, secHom_mk]
    exact (Submodule.Quotient.eq _).2 (by
      have hneg := Z.neg_mem (hbl y y.2)
      simpa using hneg)
  have hcardÊ : Nat.card ↥(A.comap π) = Nat.card ↥A := by
    rw [← Subgroup.card_map_of_injective (K := A.comap π) hπinj, Subgroup.map_comap_eq,
      inf_eq_right.mpr hAle]
  have hΓ1 : ∀ γ ∈ A.comap π, γ * γ = 1 := by
    intro γ hγ
    have hγA : π γ ∈ A := Subgroup.mem_comap.1 hγ
    have h2 : π γ * π γ = 1 := (elemAb_facts hAe).2 (π γ) hγA
    exact hπinj (by rw [map_mul, map_one, h2])
  have hΓc : ∀ γ ∈ A.comap π, ∀ δ ∈ A.comap π, γ * δ = δ * γ := by
    intro γ hγ δ hδ
    have hγA : π γ ∈ A := Subgroup.mem_comap.1 hγ
    have hδA : π δ ∈ A := Subgroup.mem_comap.1 hδ
    refine hπinj ?_
    rw [map_mul, map_mul]
    exact (elemAb_facts hAe).1 (π γ) hγA (π δ) hδA
  have hm3 : m ≤ 3 * n := by
    have hcube := CFSG.Quasithin.B42G2.card_le_cube (F := K) hK (by omega) hΓ1 hΓc
    have h1 : 2 ^ m ≤ 2 ^ (3 * n) := by
      calc 2 ^ m = Nat.card ↥A := hcardA.symm
        _ = Nat.card ↥(A.comap π) := hcardÊ.symm
        _ ≤ Nat.card K ^ 3 := hcube
        _ = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  let a' : SecQ Y Z ≃ₗ[ZMod 2] SecQ Y Z := a
  have haA' : a' ∈ A := a.2
  have ha2 : a' * a' = 1 := by
    simpa [a'] using (elemAb_facts hAe).2 a' haA'
  have ha1' : a' ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hdisp := two_mul_le_dispRank_of_natural
    (K := K) (M := SecQ Y Z) (f := n) hK hn2 π hπinj hirrM φ hφ a' ha2 ha1' (hnorm a' haA')
  obtain ⟨h, hh, haeq⟩ := by
    rw [hAdef] at haA'
    exact haA'
  have hhB : (h : G) ∈ B := Subgroup.mem_subgroupOf.1 hh
  let S : Submodule (ZMod 2) (SecQ Y Z) :=
    LinearMap.ker ((secHom hY hZ h).toLinearMap - 1)
  have hcardS : Nat.card ↥S = Nat.card {q : SecQ Y Z // secHom hY hZ h q = q} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp
  have hfixh := card_fix_secHom (hY := hY) (hZ := hZ) hZY h
  have hfinS : finrank (ZMod 2) ↥S =
      finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers (h : G))) -
        finrank (ZMod 2) ↥Z := by
    have h1 : Nat.card ↥S = 2 ^ finrank (ZMod 2) ↥S := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h2 : 2 ^ finrank (ZMod 2) ↥S =
        2 ^ (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers (h : G))) -
          finrank (ZMod 2) ↥Z) := by
      rw [← h1, hcardS, hfixh]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  have hdisp_eq : CFSG.QuasithinUnique.Setup.X7b.dispRank (secHom hY hZ h) =
      finrank (ZMod 2) (SecQ Y Z) - finrank (ZMod 2) ↥S := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ((secHom hY hZ h).toLinearMap - 1)
    change Module.finrank (ZMod 2) (LinearMap.range ((secHom hY hZ h).toLinearMap - 1)) =
      Module.finrank (ZMod 2) (SecQ Y Z) - Module.finrank (ZMod 2) ↥S
    rw [show S = LinearMap.ker ((secHom hY hZ h).toLinearMap - 1) from rfl]
    omega
  have hdisp_le : CFSG.QuasithinUnique.Setup.X7b.dispRank (secHom hY hZ h) ≤
      secCost ρ B Y Z := by
    rw [hdisp_eq, hfinS, finrank_secQ hZY]
    have hzp : Subgroup.zpowers (h : G) ≤ B := Subgroup.zpowers_le.2 hhB
    have hmono : secCost ρ (Subgroup.zpowers (h : G)) Y Z ≤ secCost ρ B Y Z :=
      secCost_mono hzp Y Z
    unfold secCost at hmono ⊢
    have h1 : Z ≤ Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers (h : G)) :=
      le_inf hZY (le_modFix fun a ha => hZ a (hBH (hzp ha)))
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_mono
      (inf_le_left : Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers (h : G)) ≤ Y)
    omega
  rw [← haeq] at hdisp
  exact ⟨hm3, hdisp.trans hdisp_le, φ, fun l q => by rw [← hπ l]; exact hφ (e l) q⟩

theorem g2_factorBound [Finite G] [Finite V] {L : Subgroup G} {n : ℕ} (hodd : Odd n) (hn : 1 < n)
    (hG2 : IsG2 ↥L n) : FactorBound ρ L := by
  intro B hBe hBN m hm1 hm Y Z hZY hY hZ hCB hirr hnt hcost
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel ↥L .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  obtain ⟨-, K, hfield, hfin, hchar, hKcard, ⟨e⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hCE
  letI := hfield
  letI := hfin
  letI := hchar
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨h3n, h2n, -⟩ :=
    g2_secNatural (K := K) hodd hn hG2 hKcard e hBe hBN hm1 hm hZY hY hZ hCB hirr hnt hcost
  omega

end G2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
