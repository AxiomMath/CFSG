module

public import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
public import CFSG.RankThree.GF2n.Tim81.Sec6.Defs
import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Involution
import CFSG.RankThree.GF2n.Tim81.Sec6.L2Extra
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Tools
import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

theorem RootHyp.conj_inf_Pc_eq_bot_of_conj_le (h : RootHyp M V) {g₁ : G}
    (hBM : conjSubgroup g₁ V ≤ M) (hBV : conjSubgroup g₁ V ≠ V) :
    conjSubgroup g₁ V ⊓ Pc M V = ⊥ ∧
      conjSubgroup g₁ V ≤ Subgroup.centralizer (V : Set G) := by
  refine ⟨?_, ?_⟩
  · rcases h.toHyp.conj_le_Pc_or_inf_eq_bot h.rootType hBM with hle | hbot
    · exact absurd (h.weaklyClosed_P.2 g₁ hle) hBV
    · refine le_bot_iff.mp ((inf_le_inf_left (conjSubgroup g₁ V)
        (inf_le_left : Pc M V ≤ inSubgroup (pCore 2) M)).trans hbot.le)
  · have hne : conjSubgroup g₁ V ⊓ M ≠ ⊥ := by
      rw [inf_eq_left.mpr hBM]
      intro hbot
      have h1 := card_conjSubgroup g₁ V
      rw [hbot, Subgroup.card_bot] at h1
      have := h.four_le_card
      omega
    have hc := h.toHyp.commute_of_conj_inf_ne_bot h.rootType hne
    exact fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb

theorem Sec6Hyp.exists_mem_sigmaSet_isPGroup_sup (hS : Sec6Hyp M V) {B : Subgroup G}
    (hBM : B ≤ M) (hB2 : IsPGroup 2 B) : ∃ A ∈ sigmaSet M V, IsPGroup 2 ↥(A ⊔ B) := by
  classical
  have h := hS.sec5.toRootHyp
  obtain ⟨A₀, hA₀⟩ := hS.ne
  have hA₀M : A₀ ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hA₀).1
  have hA₀2 : IsPGroup 2 A₀ := by
    obtain ⟨g, rfl, -⟩ := id hA₀
    exact h.toHyp.isPGroup_V.map (MulAut.conj g).toMonoidHom
  obtain ⟨Q, hBQ⟩ := (hB2.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨Q₀, hA₀Q⟩ := (hA₀2.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥M) Q₀ Q
  refine ⟨conjSubgroup (c : G) A₀, hS.sec5.conj_mem_sigmaSet c.2 hA₀,
    (Q.isPGroup'.map M.subtype).to_le (sup_le ?_ ?_)⟩
  · intro x hx
    have ha : (c : G)⁻¹ * x * c ∈ A₀ := mem_conjSubgroup.mp hx
    have hxM : x ∈ M := by
      have := M.mul_mem (M.mul_mem c.2 (hA₀M ha)) (M.inv_mem c.2)
      rwa [show (c : G) * ((c : G)⁻¹ * x * c) * (c : G)⁻¹ = x by group] at this
    have h1 : (⟨x, hxM⟩ : ↥M) ∈ conjSubgroup c (Q₀ : Subgroup ↥M) :=
      mem_conjSubgroup.mpr (hA₀Q (x := c⁻¹ * ⟨x, hxM⟩ * c) ha)
    have h2 : (⟨x, hxM⟩ : ↥M) ∈ ((c • Q₀ : Sylow 2 ↥M) : Subgroup ↥M) := by
      rw [Sylow.coe_subgroup_smul]
      exact h1
    rw [hc] at h2
    exact ⟨⟨x, hxM⟩, h2, rfl⟩
  · exact fun b hb => ⟨⟨b, hBM hb⟩, hBQ (x := ⟨b, hBM hb⟩) hb, rfl⟩

theorem Sec6Hyp.exists_conj_eq_conj_of_isPGroup_sup (hS : Sec6Hyp M V) (hNC : NoCommPair M V)
    {A B : Subgroup G} (hA : A ∈ sigmaSet M V) (hBM : B ≤ M)
    (h2 : IsPGroup 2 ↥(A ⊔ B)) {b : G} (hb : b ∈ B) :
    ∃ p ∈ Pc M V, conjSubgroup b A = conjSubgroup p A := by
  have h := hS.sec5.toRootHyp
  have hA' : conjSubgroup b A ∈ sigmaSet M V := hS.sec5.conj_mem_sigmaSet (hBM hb) hA
  have hA'le : conjSubgroup b A ≤ A ⊔ B :=
    conjSubgroup_le_of_le_of_mem le_sup_left (Subgroup.mem_sup_right hb)
  rcases hS.res.s513 M V hS.sec5 A hA _ hA' with ⟨hc, -⟩ | ⟨hL, -⟩
  · exact hNC A hA _ hA' hc
  · exact (hL.not_isPGroup (h2.to_le (sup_le le_sup_left hA'le))).elim

theorem Hyp.conjSubgroup_hOf_eq_of_conj_eq_conj (h : Hyp M V) {b g p : G} (hbM : b ∈ M)
    (hp : p ∈ Pc M V)
    (he : conjSubgroup b (conjSubgroup g V) = conjSubgroup p (conjSubgroup g V)) :
    conjSubgroup b (hOf M V g) = hOf M V g := by
  have hPb : conjSubgroup b (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.le_normalizer_Pc hbM)
  have he' : conjSubgroup (b * g) V = conjSubgroup p (conjSubgroup g V) := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact he
  calc conjSubgroup b (hOf M V g) = hOf M V (b * g) := by
        rw [hOf, hOf, CGT.Timmesfeld75.conjSubgroup_sup, hPb,
          CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    _ = hOf M V g := h.hOf_eq_of_conjSubgroup_eq_conj hp he'

theorem Hyp.mem_normalizer_kOf_and_xOf (h : Hyp M V) {b : G} (hbM : b ∈ M)
    (hbH : conjSubgroup b H = H) :
    b ∈ Subgroup.normalizer (kOf V H : Set G) ∧
      b ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) := by
  have hbV : conjSubgroup b V = conjSubgroup 1 V := by
    rw [conjSubgroup_one]
    exact conjSubgroup_eq_self_iff.mpr (h.le_normalizer hbM)
  exact ⟨mem_normalizer_kOf_of_conj_eq hbH H.one_mem hbV,
    mem_normalizer_iff_conjSubgroup_eq.mpr
      (conjSubgroup_xOf_eq_of_conj_eq hbH H.one_mem hbV)⟩

private theorem inner_or_fixes_other {F : Type} [Field F] [Fintype F] [CharP F 2]
    (θ : MulAut SL(2, F)) (hθ : θ * θ = 1) (S₀ : Subgroup SL(2, F)) :
    (∃ s ∈ S₀, θ = MulAut.conj s) ∨ ∃ S₁ : Subgroup SL(2, F), (∀ a ∈ S₁, a * a = 1) ∧
      Nat.card S₁ = Fintype.card F ∧ S₁ ≠ S₀ ∧ S₁.map θ.toMonoidHom = S₁ := by
  obtain ⟨S, hS2, hSc, hSθ, hcase⟩ := Sec2.MulAut.exists_sylow_inner_or_two_fixed θ hθ
  by_cases hSS : S = S₀
  · subst hSS
    rcases hcase with hin | ⟨S', h1, h2, h3, h4⟩
    · exact Or.inl hin
    · exact Or.inr ⟨S', h1, h2, h3, h4⟩
  · exact Or.inr ⟨S, hS2, hSc, hSS, hSθ⟩

theorem Sec45Shape.le_centralizer_xOf_of_fix_two (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {g₁ : G} (hBV : conjSubgroup g₁ V ≤ Subgroup.centralizer (V : Set G))
    (hBH : ∀ a ∈ conjSubgroup g₁ V, conjSubgroup a H = H)
    {b x : G} (hb : b ∈ conjSubgroup g₁ V) (hb1 : b ≠ 1) (hx : x ∈ H)
    (hxV : conjSubgroup x V ≠ V) (hbx : conjSubgroup b (conjSubgroup x V) = conjSubgroup x V) :
    conjSubgroup g₁ V ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  classical
  have hroot : ∀ {a y : G}, a ∈ conjSubgroup g₁ V → a ≠ 1 →
      a ∈ Subgroup.normalizer (conjSubgroup y V : Set G) →
      ∀ a' ∈ conjSubgroup g₁ V, ∀ v ∈ conjSubgroup y V, a' * v = v * a' := by
    intro a y ha ha1 haN
    exact Tim78.commute_of_isRootTypeTI h.rootType (g := g₁) (h := y)
      (Subgroup.ne_bot_iff_exists_ne_one.mpr
        ⟨⟨a, Subgroup.mem_inf.mpr ⟨ha, haN⟩⟩, fun h1 => ha1 (congrArg Subtype.val h1)⟩)
  have hbN : b ∈ Subgroup.normalizer (conjSubgroup x V : Set G) :=
    conjSubgroup_eq_self_iff.mp hbx
  have hA₂ : ∀ a ∈ conjSubgroup g₁ V, conjSubgroup a (conjSubgroup x V) = conjSubgroup x V :=
    fun a ha => conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (hroot hb hb1 hbN a ha v hv).symm))
  have hA₁ : ∀ a ∈ conjSubgroup g₁ V, conjSubgroup a (conjSubgroup 1 V) = conjSubgroup 1 V :=
    fun a ha => by
      rw [conjSubgroup_one]
      exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ (hBV ha))
  have hcard : 2 < Nat.card (conjSubgroup g₁ V) := by
    rw [card_conjSubgroup]
    have := h.four_le_card
    omega
  obtain ⟨a₀, ha₀, ha₀1, ha₀W⟩ := hS.exists_ne_one_mem_centralizer_xOf h
    (fun a ha => h.toHyp.mul_self_eq_one_of_mem_conj ha)
    (fun a ha a' ha' => h.toHyp.commute_of_mem_conj ha ha') hcard hBH H.one_mem hx
    (by rw [conjSubgroup_one]; exact Ne.symm hxV) hA₁ hA₂
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨y, hy, rfl⟩ := hU
  intro v hv
  have ha₀N : a₀ ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (conjSubgroup_le_xOf_of_mem hy)) ha₀W)
  exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => hroot ha₀ ha₀1 ha₀N a' ha' v hv

theorem Sec45Shape.exists_mem_Pc_commutator_mem_kOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {g₁ : G} (hBV : conjSubgroup g₁ V ≤ Subgroup.centralizer (V : Set G))
    (hBH : ∀ a ∈ conjSubgroup g₁ V, conjSubgroup a H = H)
    {b : G} (hb : b ∈ conjSubgroup g₁ V) :
    ∃ u ∈ Pc M V, ∀ x ∈ H, ⁅u⁻¹ * b, x⁆ ∈ kOf V H := by
  classical
  by_cases hb1 : b = 1
  · refine ⟨1, (Pc M V).one_mem, fun x _ => ?_⟩
    rw [hb1, inv_one, one_mul, commutatorElement_one_left]
    exact (kOf V H).one_mem
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hbH' : b ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr (hBH b hb)
  have hbV : conjSubgroup b V = conjSubgroup 1 V := by
    rw [conjSubgroup_one]
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ (hBV hb))
  have hbK : b ∈ Subgroup.normalizer (kOf V H : Set G) :=
    mem_normalizer_kOf_of_conj_eq (hBH b hb) H.one_mem hbV
  have hb2 : b * b = 1 := h.toHyp.mul_self_eq_one_of_mem_conj hb
  have hbar : hBarConj hbH' hbK * hBarConj hbH' hbK = 1 := by
    rw [← hBarConj_mul hbH' hbK hbH' hbK]
    exact (hBarConj_eq_one_iff _ _).mpr fun x _ => by
      rw [hb2, commutatorElement_one_left]
      exact (kOf V H).one_mem
  have hθ2 : MulAut.congr ψ (hBarConj hbH' hbK) * MulAut.congr ψ (hBarConj hbH' hbK) = 1 := by
    rw [← map_mul, hbar, map_one]
  rcases inner_or_fixes_other _ hθ2 ((imgK V H (Pc M V)).map ψ.toMonoidHom) with
    ⟨s, hs, hθs⟩ | ⟨S₁, hS₁2, hS₁c, hS₁ne, hS₁θ⟩
  · obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨z, hzP, rfl⟩ := mem_imgK_iff.mp ht
    refine ⟨(z : G), hzP, ?_⟩
    have hconj : hBarConj hbH' hbK = MulAut.conj (piK V H z) :=
      (MulAut.congr ψ).injective (hθs.trans (CFSG.mulAut_congr_conj ψ (piK V H z)).symm)
    have hzinv : (z : G)⁻¹ ∈ H := H.inv_mem z.2
    have h1 : hBarConj (V := V) (Subgroup.mul_mem _ (Subgroup.le_normalizer hzinv) hbH')
        (Subgroup.mul_mem _ (le_normalizer_kOf V H hzinv) hbK) = 1 := by
      rw [hBarConj_mul (Subgroup.le_normalizer hzinv) (le_normalizer_kOf V H hzinv) hbH' hbK,
        hBarConj_of_mem hzinv, hconj, ← map_mul MulAut.conj, ← map_mul (piK V H)]
      have hz1 : (⟨(z : G)⁻¹, hzinv⟩ : ↥H) * z = 1 := inv_mul_cancel z
      rw [hz1, map_one, map_one]
    exact (hBarConj_eq_one_iff _ _).mp h1
  · obtain ⟨x, hxH, rfl⟩ := hS.exists_mem_eq_map_imgK h ψ hS₁2 hS₁c
    have hxV : conjSubgroup x V ≠ V := by
      intro hxV
      apply hS₁ne
      rw [(hS.imgK_conj_eq_iff h hxH H.one_mem).mpr
        (by rw [conjSubgroup_one]; exact hxV), conjSubgroup_one]
    have hfix : imgK V H (conjSubgroup b (conjSubgroup x (Pc M V))) =
        imgK V H (conjSubgroup x (Pc M V)) := by
      apply Subgroup.map_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective
      have h2 := hS₁θ
      rw [CFSG.map_mulAut_congr, hBarConj_map_imgK hbH' hbK
        (conjSubgroup_le_of_le_of_mem hS.Pc_le hxH)] at h2
      simpa using h2
    have hBW := hS.le_centralizer_xOf_of_fix_two h hBV hBH hb hb1 hxH hxV
      (hS.conj_eq_of_imgK_eq h (hBH b hb) hxH hfix)
    refine ⟨1, (Pc M V).one_mem, fun x' hx' => ?_⟩
    rw [inv_one, one_mul]
    exact commutator_mem_kOf_of_mem_normalizer hbH' (hBW hb) hx'

end CFSG.RankThree.GF2n.Tim81
