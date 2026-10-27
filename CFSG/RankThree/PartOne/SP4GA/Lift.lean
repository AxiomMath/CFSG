module

public import CFSG.RankThree.PartOne.K1214.CycCtx

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.K1214

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem mod_B_of_mem_xPreimage (ctx : Fus12Ctx G p A c L E) {k : G} (hk : k ∈ xPreimage p E)
    {e : G} (he : e ∈ E) : k * e * k⁻¹ * e⁻¹ ∈ E ⊓ L := by
  obtain ⟨hkN, w, hw, hwk⟩ := mem_xPreimage_iff.1 hk
  have hD := data_of_ctx ctx
  have h1 := hD.mul_inv_mem hw ⟨e, he⟩
  have h2 := Subgroup.mem_subgroupOf.1 h1
  have h3 := Equivariance.coe_conjAut hkN ⟨e, he⟩
  have h4 : (((w : ↥(torusWeyl E)) : MulAut E) ⟨e, he⟩ : E) =
      ((conjAut E k hkN ⟨e, he⟩ : E)) := by rw [hwk]
  have h5 : ((((w : ↥(torusWeyl E)) : MulAut E) ⟨e, he⟩ * (⟨e, he⟩ : ↥E)⁻¹ : ↥E) : G) =
      k * e * k⁻¹ * e⁻¹ := by
    rw [Subgroup.coe_mul, h4, h3, Subgroup.coe_inv]
  rw [← h5]
  exact h2

theorem exists_frattini (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    ∃ k ∈ xPreimage p E, k⁻¹ * n ∈ Subgroup.normalizer (P : Set G) := by
  classical
  have hp : p.Prime := ctx.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p ↥P := hC.P_sylow.1.2.1
  have hPW : P ≤ xPreimage p E := by
    intro y hy
    obtain ⟨m, hm⟩ := hPp ⟨y, hy⟩
    obtain ⟨w, hw, hwy⟩ := exists_conjAut_mem_pCore ctx hnH (hPE hy)
      ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact mem_xPreimage_iff.2 ⟨hPE hy, w, hw, hwy⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p P (xPreimage p E) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hPW, hPp, ?_⟩
    have h1 : P.relIndex (xPreimage p E) ∣ X.relIndex (xPreimage p E) :=
      Subgroup.relIndex_dvd_of_le_left _ hC.P_sylow.2
    exact fun hd => hC.X_sylow.1.2.2 (hd.trans h1)
  have hnW : n ∈ Subgroup.normalizer (xPreimage p E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_xPreimage hn hy, fun hy => ?_⟩
    have := conj_mem_xPreimage (Subgroup.inv_mem _ hn) hy
    simpa [mul_assoc] using this
  exact Sec15Frattini.exists_mem_normalizer_of_isSylowOf hsyl hnW

theorem exists_lift (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), n ∈ Subgroup.normalizer (E : Set G) ∧
      (∀ e ∈ E, n * e * n⁻¹ * (w * e * w⁻¹)⁻¹ ∈ E ⊓ L) ∧
      (∀ z ∈ E ⊓ L, w * z * w⁻¹ ∈ E ⊓ L → n * z * n⁻¹ = w * z * w⁻¹) := by
  obtain ⟨k, hk, hkn⟩ := exists_frattini ctx hnH hC hPE hw
  have hk' : k⁻¹ ∈ xPreimage p E := (xPreimage p E).inv_mem hk
  have hkN : k⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
    obtain ⟨hkN, -⟩ := mem_xPreimage_iff.1 hk'
    exact hkN
  refine ⟨k⁻¹ * w, hkn, Subgroup.mul_mem _ hkN hw, ?_, ?_⟩
  · intro e he
    have he' : w * e * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hw e).1 he
    have := mod_B_of_mem_xPreimage ctx hk' he'
    have e1 : k⁻¹ * w * e * (k⁻¹ * w)⁻¹ * (w * e * w⁻¹)⁻¹ =
        k⁻¹ * (w * e * w⁻¹) * (k⁻¹)⁻¹ * (w * e * w⁻¹)⁻¹ := by group
    rw [e1]
    exact this
  · intro z hz hwz
    have := fix_of_mem_xPreimage ctx hk' hwz
    have e1 : k⁻¹ * w * z * (k⁻¹ * w)⁻¹ = k⁻¹ * (w * z * w⁻¹) * (k⁻¹)⁻¹ := by group
    rw [e1]
    exact this

end CFSG.RankThree.PartOne.SP4GA
