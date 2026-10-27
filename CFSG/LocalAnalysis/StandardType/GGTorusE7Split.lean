module

public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Split
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.RootSystem


namespace E7SplitTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def coordHom : (Fin Tag.E7.rank → Kˣ) →* adjointGroup .E7 K :=
  (rootDiagUnitHom .E7 K).codRestrict (adjointGroup .E7 K)
    fun a => CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
      (TableBExc.full_of_E7_E8 (Or.inl rfl) a)

@[simp] theorem coe_coordHom (a : Fin Tag.E7.rank → Kˣ) :
    (coordHom a : ModGL .E7 K) = rootDiagUnit .E7 a := rfl

theorem coordHom_injective : Function.Injective (coordHom (K := K)) := by
  intro a b h
  exact CFSG.LieType.Chevalley.rootDiagUnit_injective (congrArg Subtype.val h)

theorem mem_range_coordHom_iff (g : adjointGroup .E7 K) :
    g ∈ (coordHom (K := K)).range ↔ (g : ModGL .E7 K) ∈ torusGroup .E7 K := by
  constructor
  · rintro ⟨a, rfl⟩
    exact TableBExc.full_of_E7_E8 (Or.inl rfl) a
  · intro hg
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    exact ⟨a, Subtype.ext ha.symm⟩

theorem mem_torusPow_iff {p : ℕ} (g : adjointGroup .E7 K) :
    g ∈ TableBExc.torusPow .E7 K p ↔ g ^ p = 1 ∧ g ∈ (coordHom (K := K)).range := by
  rw [TableBExc.mem_torusPow, mem_range_coordHom_iff]
  exact and_comm

@[expose] def simpleRep (k : Fin Tag.E7.rank) : adjointGroup .E7 K :=
  ⟨canonicalRep (coxeterSystem .E7) K (simple .E7 k),
    canonicalRep_mem_adjointGroup (coxeterSystem .E7) K (simple .E7 k)⟩

theorem simple_conj_coordHom (k : Fin Tag.E7.rank) (a : Fin Tag.E7.rank → Kˣ) :
    simpleRep k * coordHom a * (simpleRep k)⁻¹ =
      coordHom a * (coordHom (corTuple Tag.E7.cartan k (a k)))⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_coordHom, simpleRep]
  rw [canonicalRep_simple]
  have h := weylElt_conj_rootDiagUnit (τ := .E7) a k
  rw [h]
  rw [rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, corTuple, zpow_neg]


theorem centralizer_le_range {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) :
    Subgroup.centralizer ((TableBExc.torusPow .E7 K p) : Set (adjointGroup .E7 K)) ≤
      (coordHom (K := K)).range := by
  intro g hg
  apply (mem_range_coordHom_iff g).mpr
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  have hCG := TableBExc.adjointGroup_inf_centralizer_torusPow_of_ne_two
    (τ := .E7) hp hp2 hpk
    (fun a _ => TableBExc.full_of_E7_E8 (Or.inl rfl) a)
  rw [← hCG]
  refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hxC : x ∈ adjointGroup .E7 K :=
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hx.1
  have hxV : (⟨x, hxC⟩ : adjointGroup .E7 K) ∈ TableBExc.torusPow .E7 K p :=
    ExcFrames.mem_torusPow_iff_coe.mpr hx
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg) ⟨x, hxC⟩ hxV)

theorem exists_frame {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (_hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K),
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = TableBExc.torusPow .E7 K p ∧
      (∀ k s, simpleRep k * ι (Multiplicative.ofAdd s) * (simpleRep k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E7 K p) : Set (adjointGroup .E7 K)),
        ∃ w : WeylGroup .E7, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
          ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p w s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hfull : ∀ a : Fin Tag.E7.rank → Kˣ, rootDiagUnit .E7 a ∈ torusGroup .E7 K :=
    fun a => TableBExc.full_of_E7_E8 (Or.inl rfl) a
  let ι := ExcFrames.frameHom hfull ζ hζ (1 : adjointGroup .E7 K)
  have hιcoe : ∀ s : Fin Tag.E7.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .E7 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp only [ι, ExcFrames.coe_frameHom, Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hdet : IsUnit ((Tag.E7.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inl rfl)) hp2
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .E7 K p := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      apply ExcFrames.mem_torusPow_iff_coe.mpr
      rw [← ofAdd_toAdd s, hιcoe]
      exact ExcFrames.frameDiag_mem hfull ζ hζ _
    · intro hg
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
        (ExcFrames.mem_torusPow_iff_coe.mp hg)
      exact ⟨Multiplicative.ofAdd s, Subtype.ext ((hιcoe s).trans hs)⟩
  have hsimple : ∀ k s, simpleRep k * ι (Multiplicative.ofAdd s) * (simpleRep k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, simpleRep]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .E7 k) s
  refine ⟨ζ, hζ, ι, hζo, hι, hrange, hsimple, ?_⟩
  intro g hg
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes (Subgroup.mem_normalizer_iff.mp hg)
  refine ⟨w, fun s => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
  rw [hw _ (ExcFrames.frameDiag_mem hfull ζ hζ s)]
  exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s

theorem exists_conj_torusPow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .E7 K))
    (hE : IsElemAbelian p E) (hcard : p ^ 7 ≤ Nat.card E) :
    ∃ g : adjointGroup .E7 K,
      E.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow .E7 K p := by
  have hT : GGExcToralRankInput .E7 K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact ggE7ThreeToralRankInput_holds K hq
    · exact ggExcToralRankInput_E7_of_ne_three hp hp2 hp3 hq
  exact hT E hE (by simpa only [Tag.rank] using hcard)

end E7SplitTorus

end CFSG.StandardType

end
