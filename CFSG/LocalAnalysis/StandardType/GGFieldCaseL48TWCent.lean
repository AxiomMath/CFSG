module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWCentAux
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48RestTransfer
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailCent
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_mem_commutator_H0_of_coverP {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hxN : x ∈ Subgroup.normalizer (U₁ : Set G))
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hP : ∀ h ∈ Subgroup.centralizer ({x} : Set G), (∃ k : ℕ, h ^ p ^ k = 1) →
        h ∈ (Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
          L ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)))
    (hLF : x ∉ ⁅Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
          Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)⁆ ⊔
        ggL48U2 x U₁ ⊔ (L ⊓ Subgroup.centralizer
          ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))) :
    x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁ := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxp : x ^ p = 1 := hBsp x hxBs
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  have hNB := normalizer_le_normalizer_of_ggFieldCase hS.1
  have hUC := hS.2.2.2.2.2.2.1.1
  have hU₁U := hS.2.2.2.2.2.2.2.1.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set H := Subgroup.centralizer ({x} : Set G) with hH
  set F := H ⊓ Subgroup.centralizer (B₁ : Set G) with hF
  set Y := H ⊓ Subgroup.centralizer (L : Set G) with hY
  set U₂ := ggL48U2 x U₁ with hU₂
  set W := ⁅F, F⁆ ⊔ U₂ ⊔ (L ⊓ Subgroup.centralizer (B₁ : Set G)) with hW
  have hB₁Bs : B₁ ≤ Bs := inf_le_left
  have hB₁H : B₁ ≤ H := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hBcomm b (hB₁Bs hb) x hxBs)
  have hxH : x ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hxF : x ∈ F := ⟨hxH, mem_centralizer_iff.mpr fun b hb => hBcomm b (hB₁Bs hb) x hxBs⟩
  have hxY : x ∈ Y := ⟨hxH, mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLx hl)⟩
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, ggNormalizer_le_normalizer_centralizer L (hN hh)⟩
  have hB₁p : IsPGroup p B₁ := fun b => ⟨1, Subtype.ext (by simpa using hBsp _ (hB₁Bs b.2))⟩
  have hcycY : ∀ S : Subgroup G, S ≤ Y → IsPGroup p S → IsCyclic S := fun S hSY hSp =>
    hcycL S (hSY.trans inf_le_right) hSp
  have hzc : ∀ g ∈ Y, g * x = x * g := fun g hg => mem_centralizer_singleton_iff.mp hg.1
  obtain ⟨w, O, a, hwY, hxw, ha, hBw, hO, hdec⟩ :=
    GGL48TW.Cent.exists_invariant_cyclic_complement hp2 (hB₁H.trans hHY) hB₁p hcycY hxY hx1 hxp hzc
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hTle : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ zpowers x :=
    GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp) (fun t ht => hBsp t ht.1)
      ⟨hxBs, hxY.2⟩ hx1
  have htriv : ∀ c ∈ B₁, c ∈ zpowers w → c = 1 := by
    intro c hcB hcw
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := (zpowers_le.mpr hwY.2) hcw
    exact GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 (hTle ⟨hB₁Bs hcB, hcL⟩) hcB
  have hBw' := GGL48TW.Cent.commute_of_cyclic_invariant hp2 hBsp hBst.2.2.2 h43.2 hNB hx1 hxp hxw
    (fun b hb => hBcomm b (hB₁Bs hb) x hxBs) hBw htriv ha
  have hwF : zpowers w ≤ F := (zpowers_le).mpr ⟨hwY.1, mem_centralizer_iff.mpr hBw'⟩
  have hOY : O ≤ Y := fun g hg => ((hO g).mp hg).1
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := by
    intro h hh
    apply GGL48TW.Cent.mem_normalizer_of_conj_mem
    intro g hg
    obtain ⟨hgY, hgo⟩ := (hO g).mp hg
    refine (hO _).mpr ⟨(mem_normalizer_iff.mp (hHY hh) g).mp hgY, ?_⟩
    have : orderOf (h * g * h⁻¹) = orderOf g := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj h) g
    rwa [this]
  set N := L ⊔ O with hNdef
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_sup L O ⟨hN hh, hHO hh⟩
  have hFN : F ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hHN
  have hYFN : Y ≤ F ⊔ N := by
    intro g hg
    obtain ⟨o, ho, s, hs, rfl⟩ := hdec g hg
    exact (F ⊔ N).mul_mem (mem_sup_right (mem_sup_right ho)) (mem_sup_left (hwF hs))
  have hM : F ⊔ L ⊔ Y ≤ F ⊔ N :=
    sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right)) hYFN
  obtain ⟨P, hPp, -, hPH₀, hPmax⟩ :=
    exists_maxPSubgroup_of_le (H := ggL48H0 x U₁) (IsPGroup.of_bot (p := p)) bot_le
  have hxH₀ : x ∈ ggL48H0 x U₁ := ⟨hxH, hxN⟩
  have hxP : x ∈ P :=
    mem_of_maxPSubgroup_of_le_centralizer inf_le_left hxH₀ hxp hPp hPH₀ hPmax
  have hPM : P ≤ F ⊔ N := by
    intro g hg
    obtain ⟨k, hk⟩ := hPp ⟨g, hg⟩
    exact hM (hP g (hPH₀ hg).1 ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have hU₂n : ggL48H0 x U₁ ≤ Subgroup.normalizer (U₂ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, Subgroup.le_normalizer hg.1⟩
  have hFF : ⁅F, F⁆ ≤ F := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha)) (F.inv_mem hb)
  have hU₂F : U₂ ≤ F := fun u hu => ⟨hu.2, hUC (hU₁U hu.1)⟩
  have hLF' : L ⊓ Subgroup.centralizer (B₁ : Set G) ≤ F := fun l hl => ⟨hLx hl.1, hl.2⟩
  have hWF : W ≤ F := sup_le (sup_le hFF hU₂F) hLF'
  have hFW : F ≤ Subgroup.normalizer (W : Set G) := by
    intro f hf
    apply GGL48TW.Cent.mem_normalizer_of_conj_mem
    intro v hv
    have : f * v * f⁻¹ = ⁅f, v⁆ * v := by rw [commutatorElement_def]; group
    rw [this]
    exact W.mul_mem (mem_sup_left (mem_sup_left (commutator_mem_commutator hf (hWF hv)))) hv
  have hK : x ∉ W ⊔ N := by
    intro hxK
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right W N (hWF.trans hFN)] at hxK
    obtain ⟨v, hv, n, hn, hvn⟩ := hxK
    have hvn : v * n = x := hvn
    have hnF : n ∈ F := by
      have : n = v⁻¹ * x := by rw [← hvn]; group
      rw [this]; exact F.mul_mem (F.inv_mem (hWF hv)) hxF
    have hn' : n ∈ (L : Set G) * (O : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right L O (hLx.trans hHO)]; exact hn
    obtain ⟨l, hl, o, ho, hlo⟩ := hn'
    obtain ⟨hoY, hm⟩ := (hO o).mp ho
    have hcomm : Commute l o := mem_centralizer_iff.mp hoY.2 l hl
    have hnm : n ^ orderOf o = l ^ orderOf o := by
      rw [← hlo, hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
    have hlm : l ^ orderOf o ∈ W := by
      refine mem_sup_right ⟨L.pow_mem hl _, ?_⟩
      rw [← hnm]; exact (F.pow_mem hnF _).2
    have hxm : x ^ orderOf o ∈ W := by
      have h := GGL48TW.Cent.mul_pow_mul_inv_mem hFW hv hnF (orderOf o)
      rw [hvn, hnm] at h
      have := W.mul_mem h hlm
      simpa using this
    have hxW : x ∈ W := GGL48TW.Cent.mem_of_pow_mem_of_coprime hxm (by rw [hxp]; exact W.one_mem) hm
    exact hLF hxW
  have hFFW : ⁅F, F⁆ ≤ W := by rw [hW]; exact le_sup_left.trans le_sup_left
  have hU₂W : U₂ ≤ W := by rw [hW]; exact le_sup_right.trans le_sup_left
  have hK0 : ⁅P, P⁆ ⊔ U₂ ≤ W ⊔ N := by
    apply sup_le
    · calc ⁅P, P⁆ ≤ ⁅F ⊔ N, F ⊔ N⁆ := Subgroup.commutator_mono hPM hPM
        _ ≤ ⁅F, F⁆ ⊔ N := GGL48TW.Cent.commutator_sup_le_of_le_normalizer hFN
        _ ≤ W ⊔ N := sup_le_sup_right hFFW N
    · exact hU₂W.trans le_sup_left
  exact GGL48.not_mem_commutator_sup_of_le_sylow hPp hPH₀ hPmax inf_le_left hxP hxp hU₂n
    (fun hx => hK (hK0 hx))

end CFSG.StandardType
