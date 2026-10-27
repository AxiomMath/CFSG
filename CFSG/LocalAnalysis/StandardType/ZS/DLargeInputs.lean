module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtDeg
public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFive
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneSix
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneSixTen
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNine
import CFSG.LocalAnalysis.StandardType.ZS.PropOneEight
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem splitOfIrred_of_tfNegOrGen (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) {l : ℕ}
    (htab : l < Module.finrank (ZMod p) U → TFNegOrGen p l) : SplitOfIrred p G l := by
  intro F hFG hFgen hirr hl hd
  exact splitSupport_of_irredOnSection hp htab ⟨hFgen, fun g hg => hG g (hFG hg)⟩ hirr hl hd

private theorem dli_one_le_finrank [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    1 ≤ Module.finrank (ZMod p) U := by
  obtain ⟨x, -, -, -, hxr, -, -⟩ := hd
  have hle := Submodule.finrank_le (LinearMap.range ((x : U →ₗ[ZMod p] U) - LinearMap.id))
  rw [hxr.2] at hle
  exact hle

private theorem dli_seven_degenerate_false (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hs : SplitSupport H l)
    (hmax' : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K →
      SplitSupport K l → K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hFfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hdeg : IsDegenerate F H) (hVtop : HardMathSupport.Kantor79.commutatorSpace F = ⊤) : False := by
  have hS : LemmaOneSixSetting F H a l :=
    { eq_closure := hF
      transvectionFree := hFt
      isRefl := ha
      reflGen := hH
      splitSupport := hs
      maximal := hmax'
      dLarge := hd
      finrank_eq := hFfin
      degenerate := hdeg }
  have hsup := hS.finrank_sup_eq hp
  have htop : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F = ⊤ := by
    rw [hVtop, top_sup_eq]
  rw [htop, finrank_top] at hsup
  have h1 : 1 ≤ Module.finrank (ZMod p) U := by
    have hle := Submodule.finrank_le
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    rw [hS.degenerate.1] at hle
    exact hle
  omega

theorem lemmaOneSeven_of_maximal (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hH : ReflGen p H) (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hmax : ∀ K ≤ G, H ≤ K → ReflGen p K → SplitSupport K (Module.finrank (ZMod p) U - 1) →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hcop : TFCoprimeWitness p (Module.finrank (ZMod p) U - 1)) : LemmaOneSeven p G H := by
  intro a haG ha hnot W hW
  have haH : a ∉ H := by
    intro haH
    exact hnot ⟨a, haH, 1, Subgroup.one_mem _, by simp⟩
  have haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) := by
    intro haC
    exact hnot ⟨1, H.one_mem, a, haC, by simp⟩
  have hn1 : 1 ≤ Module.finrank (ZMod p) U := dli_one_le_finrank hd
  let F : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))
  have hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) := rfl
  have hFG : F ≤ G := by
    rw [hF]
    exact (Subgroup.closure_le _).mpr (Set.insert_subset haG hHG)
  have hFt : QTwoLin.TransvectionFree F := fun g hg => hG g (hFG hg)
  have hmax' : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 1) → K = H :=
    fun K hKF hHK hKr hKs => hmax K (hKF.trans hFG) hHK hKr hKs
  have htab' : (Module.finrank (ZMod p) U - 1) + 1 < Module.finrank (ZMod p) U →
      TFNegOrGen p ((Module.finrank (ZMod p) U - 1) + 1) :=
    fun hlt => absurd hlt (by omega)
  obtain ⟨hFfin, hcase⟩ := splitSupport_succ_or_degenerate
    (l := Module.finrank (ZMod p) U - 1) hp htab htab' hcop hF hFt ha hH hs hmax' hd haH haC
  have hFfin' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) =
      Module.finrank (ZMod p) U := by omega
  have hVtop : HardMathSupport.Kantor79.commutatorSpace F = ⊤ :=
    Submodule.eq_top_of_finrank_eq hFfin'
  rcases hcase with hsplit | hdeg
  · have hsplit' : SplitSupport F (Module.finrank (ZMod p) U) := by
      simpa only [show (Module.finrank (ZMod p) U - 1) + 1 = Module.finrank (ZMod p) U from
        by omega] using hsplit
    rcases hsplit'.2.2 W bot_le (by rw [hVtop]; exact le_top) hW with hbot | htop
    · exact Or.inl hbot
    · exact Or.inr (by rwa [hVtop] at htop)
  · exact (dli_seven_degenerate_false hp hF hFt ha hH hs hmax' hd hFfin hdeg hVtop).elim

open scoped commutatorElement in
private theorem dli_pair_of_degenerate (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F K : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F K a l)
    (hd : ∃ x ∈ K, ∃ y ∈ K, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
  obtain ⟨x, hxK, -, -, hxr, -, -⟩ := hd
  have hx1 : x ≠ 1 := IsRefl.ne_one hxr
  obtain ⟨t, htT, htnotcomm⟩ := hS.exists_not_commute_kerSection hp hxK hx1
  have hKleF : K ≤ F := by
    rw [hS.eq_closure]
    exact fun y hy => Subgroup.subset_closure (Set.mem_insert_of_mem a hy)
  have hxF : x ∈ F := hKleF hxK
  have htF : t ∈ F := kerSection_le htT
  have hconjF : t * x * t⁻¹ ∈ F := F.mul_mem (F.mul_mem htF hxF) (F.inv_mem htF)
  have hcommT : ⁅x, t⁆ ∈ kerSection F := by
    rw [commutatorElement_def]
    exact (kerSection F).mul_mem (conj_mem_kerSection hxF htT) ((kerSection F).inv_mem htT)
  refine ⟨x, hxF, t * x * t⁻¹, hconjF, hxr, IsRefl.conj hxr t, ?_⟩
  have hxy : x * (t * x * t⁻¹) = ⁅x, t⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hxr.1]
    group
  rw [hxy]
  exact orderOf_eq_prime (hS.pow_eq_one_of_mem_kerSection hp hcommT)
    (fun h1 => htnotcomm (commutatorElement_eq_one_iff_mul_comm.mp h1))

open scoped commutatorElement in
private theorem dli_commutator_data (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F K : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F K a l) {K₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hK₁K : K₁ ≤ K)
    (hK₁ : ReflGen p K₁) (hK₁ne : K₁ ≠ ⊥) {α : ℕ} (hK₁s : SplitSupport K₁ α) :
    (∀ s ∈ ⁅K₁, kerSection F⁆, s ^ p = 1) ∧
      (∀ s ∈ ⁅K₁, kerSection F⁆, ∀ t ∈ ⁅K₁, kerSection F⁆, s * t = t * s) ∧
      p ^ α ≤ Nat.card (⁅K₁, kerSection F⁆ : Subgroup (U ≃ₗ[ZMod p] U)) ∧
      ∀ s ∈ ⁅K₁, kerSection F⁆, s ≠ 1 →
        Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace s) = 2 := by
  have hKleF : K ≤ F := by
    rw [hS.eq_closure]
    exact fun y hy => Subgroup.subset_closure (Set.mem_insert_of_mem a hy)
  have hK₁F : K₁ ≤ F := hK₁K.trans hKleF
  have hTle : ⁅K₁, kerSection F⁆ ≤ kerSection F := by
    rw [Subgroup.commutator_le]
    intro g hg t ht
    rw [commutatorElement_def]
    exact (kerSection F).mul_mem (conj_mem_kerSection (hK₁F hg) ht) ((kerSection F).inv_mem ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hS.pow_eq_one_of_mem_kerSection hp (hTle hs)
  · intro s hs t ht
    exact hS.commute_of_mem_kerSection hp (hTle hs) (hTle ht)
  · have h := hS.pow_finrank_le_card hp hK₁K hK₁ hK₁ne
    simpa [hK₁s.2.1] using h
  · intro s hs hne
    exact (hS.finrank_movedSpace_of_mem_kerSection hp (hTle hs) hne).2.1

private theorem dli_ne_bot_of_dLarge {K₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hd : ∃ x ∈ K₁, ∃ y ∈ K₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) : K₁ ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx, -, -, hxr, -, -⟩ := hd
  exact IsRefl.ne_one hxr (Subgroup.mem_bot.mp (by rwa [hbot] at hx))

theorem degenerateInput_of_tableFacts [Module.Finite (ZMod p) U]
    (G : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ)
    (htab : ∀ m < Module.finrank (ZMod p) U, TFNegOrGen p m)
    (hcop : ∀ m < Module.finrank (ZMod p) U, TFCoprimeWitness p m) :
    DegenerateInput p G l := by
  intro hp hgenG htvG habs hprim hl2 K hKG hK hKs hmax hd a haG ha hnot
  have haK : a ∉ K := by
    intro haK
    exact hnot ⟨a, haK, 1, Subgroup.one_mem _, by simp⟩
  have haC : a ∉ Subgroup.centralizer (K : Set (U ≃ₗ[ZMod p] U)) := by
    intro haC
    exact hnot ⟨1, K.one_mem, a, haC, by simp⟩
  let F : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U)))
  have hF : F = Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U))) := rfl
  have hFG : F ≤ G := by
    rw [hF]
    exact (Subgroup.closure_le _).mpr (Set.insert_subset haG hKG)
  have hFt : QTwoLin.TransvectionFree F := fun g hg => htvG g (hFG hg)
  have hmax' : ∀ K' : Subgroup (U ≃ₗ[ZMod p] U), K' ≤ F → K ≤ K' → ReflGen p K' →
      SplitSupport K' l → K' = K :=
    fun K' hK'F hKK' hK'r hK's => hmax K' (hK'F.trans hFG) hKK' hK'r hK's
  have hlt : l < Module.finrank (ZMod p) U := by omega
  obtain ⟨hFfin, hcase⟩ := splitSupport_succ_or_degenerate (l := l) hp (htab l hlt)
    (fun h => htab (l + 1) h) (hcop l hlt) hF hFt ha hK hKs hmax' hd haK haC
  rcases hcase with hsplit | hdeg
  · exact Or.inl hsplit
  · right
    have hS : LemmaOneSixSetting F K a l :=
      { eq_closure := hF
        transvectionFree := hFt
        isRefl := ha
        reflGen := hK
        splitSupport := hKs
        maximal := hmax'
        dLarge := hd
        finrank_eq := hFfin
        degenerate := hdeg }
    refine ⟨dli_pair_of_degenerate hp hS hd, ?_⟩
    intro K₁ hK₁K hK₁ α _hα hK₁s hdK₁
    have hK₁ne : K₁ ≠ ⊥ := dli_ne_bot_of_dLarge hdK₁
    obtain ⟨B, hBG, hK₁B, hT'B, hBrefl, hBs, -⟩ :=
      exists_splitSupport_enlargement_of_le hp htab ⟨hgenG, htvG⟩ habs.1 hprim hFG hS
        (by omega) hK₁K hK₁ hK₁s hdK₁
    obtain ⟨hpow, hcomm, hcard, hmove⟩ := dli_commutator_data hp hS hK₁K hK₁ hK₁ne hK₁s
    exact ⟨B, hBG, hBrefl, hK₁B, hBs,
      ⁅K₁, kerSection F⁆, hT'B, hpow, hcomm, hcard, hmove⟩

theorem impExtInputs_of_impExtSetting (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : ImpExtSetting G H d)
    (htab : ∀ m < Module.finrank (ZMod p) U, TFNegOrGen p m)
    (hcop : ∀ m < Module.finrank (ZMod p) U, TFCoprimeWitness p m)
    (hT1 : TFPrimCorank p (Module.finrank (ZMod p) U - 1))
    (hT2 : TFDegenerateExt p (Module.finrank (ZMod p) U - 1)) (hT3 : TFNegOfPrimThree p)
    (hT4 : TFSmallThree p) : ImpExtInputs G H := by
  have hlt : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U := by
    have := S.four_le_finrank
    omega
  have hmax : ∀ K ≤ G, H ≤ K → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 1) → K = H := by
    intro K hKG hHK hKr hKs
    have hDMax : DMax p K d := by
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxr hyr
        exact S.dmax.1 x (hKG hx) y (hKG hy) hxr hyr
      · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
        exact ⟨x, hHK hx, y, hHK hy, hxr, hyr, hxy⟩
    have hcard : Nat.card K ≤ Nat.card H := S.maximal K hKG hKr hKs hDMax
    have : Finite U := Module.finite_of_finite (ZMod p)
    let : Finite (U ≃ₗ[ZMod p] U) :=
      Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) LinearEquiv.coe_injective
    exact (Subgroup.eq_of_le_of_card_ge hHK hcard).symm
  have hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact S.three_lt⟩
  refine ⟨?_, ?_, ?_, ?_, hT1, hT2, hT3, hT4⟩
  · exact splitOfIrred_of_tfNegOrGen hp S.transvectionFree (fun h => htab _ h)
  · exact lemmaOneSeven_of_maximal hp S.transvectionFree S.H_le S.reflGen_H S.splitSupport
      hmax hd (htab _ hlt) (hcop _ hlt)
  · exact centreOrderBound_of_primitive S.transvectionFree S.absIrred S.primitive
  · exact degenerateInput_of_tableFacts G (Module.finrank (ZMod p) U - 2) htab hcop

end CFSG.StandardType.ZS

end
