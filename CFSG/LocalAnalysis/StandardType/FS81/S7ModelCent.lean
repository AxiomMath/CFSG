module

public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Frame

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

section M3g


variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit
  [Finite K] in
private theorem zpowers_rootThree_le_highRootSL2 :
    Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) ≤
      (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf, coe_rootThree (isRoot_highRoot .E8)]
  exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 (K := K) (uSL 1 * vSL 1)

omit
  [Finite K] [CharP K 2] in
private theorem centralizer_zpowers_rootThree_eq :
    Subgroup.centralizer
        (Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) :
          Set (adjointGroup .E8 K)) =
      Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit
  [Finite K] in
private theorem cyclicity_hyp_rootThree (hK : Nat.card K = 2) :
    (Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) ≤
        (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K)) ∧
      IsCyclic (Subgroup.zpowers (rootThree .E8 K (highRoot .E8))) ∧
      Nat.card (Subgroup.zpowers (rootThree .E8 K (highRoot .E8))) = Nat.card K + 1 := by
  refine ⟨zpowers_rootThree_le_highRootSL2 (K := K), Subgroup.isCyclic_zpowers _,
    ?_⟩
  rw [Nat.card_zpowers, orderOf_rootThree (isRoot_highRoot .E8), hK]

theorem centralizer_rootThree_highRoot_E8 (hK : Nat.card K = 2) :
    Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)) =
      Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) ⊔ EPilot.perpLevi .E8 K := by
  obtain ⟨hXJ, hcyc, hX⟩ := cyclicity_hyp_rootThree (K := K) hK
  have hdesc : E6Pilot.PerpLeviFrobDescent .E8 K := E8Pilot.perpLeviFrobDescent_E8
  obtain ⟨heq, -, -⟩ :=
    E6Pilot.centralizer_nonsplit_of_descent (K := K) (Or.inr (Or.inr rfl)) hdesc hXJ hcyc hX
  rw [← centralizer_zpowers_rootThree_eq (K := K), heq]
  rfl

theorem exists_zpow_mul_of_mem_centralizer_rootThree (hK : Nat.card K = 2)
    {x : adjointGroup .E8 K}
    (hx : x ∈ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K))) :
    ∃ k : ℤ, ∃ d ∈ EPilot.perpLevi .E8 K, x = rootThree .E8 K (highRoot .E8) ^ k * d := by
  obtain ⟨hXJ, hcyc, hX⟩ := cyclicity_hyp_rootThree (K := K) hK
  have hdesc : E6Pilot.PerpLeviFrobDescent .E8 K := E8Pilot.perpLeviFrobDescent_E8
  have hx' : x ∈ Subgroup.centralizer
      (Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) : Set (adjointGroup .E8 K)) := by
    rwa [centralizer_zpowers_rootThree_eq (K := K)]
  obtain ⟨y, hy, d, hd, hxy⟩ :=
    E6Pilot.exists_mul_of_mem_centralizer_nonsplit_of_descent (K := K)
      (Or.inr (Or.inr rfl)) hdesc hXJ hcyc hX hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ⟨k, d, hd, by rw [hxy]⟩

omit
  [Finite K] in
theorem disjoint_zpowers_rootThree_perpLevi_E8 :
    Disjoint (Subgroup.zpowers (rootThree .E8 K (highRoot .E8))) (EPilot.perpLevi .E8 K) := by
  rw [Subgroup.disjoint_def]
  intro g hgX hgD
  exact Subtype.ext (Subgroup.disjoint_def.1
    (E6Pilot.disjoint_highRootSL2_perpLevi (K := K) (Or.inr (Or.inr rfl)))
    (Subgroup.mem_subgroupOf.1 (zpowers_rootThree_le_highRootSL2 (K := K) hgX))
    (Subgroup.mem_subgroupOf.1 hgD))

private theorem map_conj_inv_map_conj' {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

private theorem map_conj_map_conj' {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem mem_rootThree_of_isElemAbelian_card_eight (hK : Nat.card K = 2)
    {F : Subgroup (adjointGroup .E8 K)}
    (hF : F ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (hE : IsElemAbelian 3 F) (hc : Nat.card F = 3 ^ 8) :
    rootThree .E8 K (highRoot .E8) ∈ F := by
  set s := rootThree .E8 K (highRoot .E8) with hs
  set S := Subgroup.zpowers s with hS
  have hs3 : s ^ 3 = 1 := by
    rw [← orderOf_rootThree (K := K) (isRoot_highRoot .E8), ← hs]
    exact pow_orderOf_eq_one s
  have hcomm : ∀ a ∈ F, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hca : Commute a s := Subgroup.mem_centralizer_singleton_iff.1 (hF ha)
    exact (hca.zpow_right k).eq
  have hE' : IsElemAbelian 3 (F ⊔ S) :=
    IsElemAbelian.sup_of_commute hE (isElemAbelian_zpowers hs3) hcomm
  have hcard' : 3 ^ 8 ≤ Nat.card (F ⊔ S : Subgroup (adjointGroup .E8 K)) := by
    rw [← hc]
    exact Subgroup.card_le_of_le le_sup_left
  obtain ⟨c, hc_eq⟩ :=
    CFSG.StandardType.TableBExcTwoTB.exists_conj_frame_of_card_E8 (K := K) hK hE' hcard'
  have hcardF' : Nat.card (F ⊔ S : Subgroup (adjointGroup .E8 K)) = 3 ^ 8 := by
    rw [hc_eq, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact natCard_frameTorusE8 (K := K)
  have hFF' : F = F ⊔ S :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardF', hc])
  rw [hFF']
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)

private theorem eq_sup_inf_perpLevi_of_mem_rootThree (hK : Nat.card K = 2)
    {F : Subgroup (adjointGroup .E8 K)}
    (hF : F ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (hsF : rootThree .E8 K (highRoot .E8) ∈ F) :
    F = Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) ⊔ (F ⊓ EPilot.perpLevi .E8 K) := by
  set s := rootThree .E8 K (highRoot .E8) with hs
  apply le_antisymm
  · intro f hf
    obtain ⟨k, d, hdD, hfd⟩ :=
      exists_zpow_mul_of_mem_centralizer_rootThree (K := K) hK (hF hf)
    have hskF : s ^ k ∈ F := Subgroup.zpow_mem F hsF k
    have hdF : d ∈ F := by
      have h : (s ^ k)⁻¹ * f ∈ F := mul_mem (inv_mem hskF) hf
      rw [hfd, ← mul_assoc, inv_mul_cancel, one_mul] at h
      exact h
    rw [hfd]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers s k))
      (Subgroup.mem_sup_right ⟨hdF, hdD⟩)
  · exact sup_le (Subgroup.zpowers_le.mpr hsF) inf_le_left

theorem card_inf_perpLevi_of_nonsplit_card_eight (hK : Nat.card K = 2)
    {S F : Subgroup (adjointGroup .E8 K)}
    (hSJ : S ≤ (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcyc : IsCyclic S) (hS : Nat.card S = Nat.card K + 1)
    (hF : F ≤ Subgroup.centralizer (S : Set (adjointGroup .E8 K)))
    (hE : IsElemAbelian 3 F) (hc : Nat.card F = 3 ^ 8) :
    Nat.card (F ⊓ EPilot.perpLevi .E8 K : Subgroup (adjointGroup .E8 K)) = 3 ^ 7 := by
  classical
  have hScard : Nat.card S = 3 := by simpa [hK] using hS
  have : IsCyclic S := hcyc
  let : Fintype S := Fintype.ofFinite S
  have hSel : IsElemAbelian 3 S := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have h := congrArg Subtype.val
      (pow_card_eq_one : (⟨x, hx⟩ : S) ^ Fintype.card S = 1)
    simpa [← Nat.card_eq_fintype_card, hScard] using h
  have hcomm : ∀ a ∈ F, ∀ b ∈ S, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hF ha) b hb).symm
  have hsup : IsElemAbelian 3 (F ⊔ S) := hE.sup_of_commute hSel hcomm
  have hsupcard : 3 ^ 8 ≤ Nat.card (F ⊔ S : Subgroup (adjointGroup .E8 K)) := by
    rw [← hc]
    exact Subgroup.card_le_of_le le_sup_left
  obtain ⟨c, hc_eq⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hK hsup hsupcard
  have hcardFS : Nat.card (F ⊔ S : Subgroup (adjointGroup .E8 K)) = 3 ^ 8 := by
    rw [hc_eq, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact natCard_frameTorusE8 (K := K)
  have hSF : S ≤ F := by
    have heq : F = F ⊔ S :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardFS, hc])
    rw [heq]
    exact le_sup_right
  have hdesc : E6Pilot.PerpLeviFrobDescent .E8 K := E8Pilot.perpLeviFrobDescent_E8
  obtain ⟨-, hdisj, hSD⟩ := E6Pilot.centralizer_nonsplit_of_descent
    (Or.inr (Or.inr rfl)) hdesc hSJ hcyc hS
  have hFFD : F = S ⊔ (F ⊓ EPilot.perpLevi .E8 K) := by
    apply le_antisymm
    · intro f hf
      obtain ⟨y, hyS, d, hdD, hfd⟩ := E6Pilot.exists_mul_of_mem_centralizer_nonsplit_of_descent
        (Or.inr (Or.inr rfl)) hdesc hSJ hcyc hS (hF hf)
      have hdF : d ∈ F := by
        have h : y⁻¹ * f ∈ F := mul_mem (inv_mem (hSF hyS)) hf
        rwa [hfd, ← mul_assoc, inv_mul_cancel, one_mul] at h
      rw [hfd]
      exact mul_mem (Subgroup.mem_sup_left hyS) (Subgroup.mem_sup_right ⟨hdF, hdD⟩)
    · exact sup_le hSF inf_le_left
  have hnorm : S ≤ Subgroup.normalizer
      ((F ⊓ EPilot.perpLevi .E8 K) : Set (adjointGroup .E8 K)) :=
    (hSD.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hprod := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (F ⊓ EPilot.perpLevi .E8 K) S hnorm (hdisj.mono_right inf_le_right).symm
  have hcard : Nat.card F = Nat.card (F ⊓ EPilot.perpLevi .E8 K :
      Subgroup (adjointGroup .E8 K)) * 3 := by
    calc Nat.card F = Nat.card (S ⊔ (F ⊓ EPilot.perpLevi .E8 K) :
        Subgroup (adjointGroup .E8 K)) := by conv_lhs => rw [hFFD]
      _ = _ := by rw [sup_comm, hprod, hScard]
  rw [hc] at hcard
  norm_num at hcard ⊢
  omega

private theorem card_inf_perpLevi_of_isElemAbelian_card_eight (hK : Nat.card K = 2)
    {F : Subgroup (adjointGroup .E8 K)}
    (hF : F ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (hE : IsElemAbelian 3 F) (hc : Nat.card F = 3 ^ 8) :
    Nat.card (F ⊓ EPilot.perpLevi .E8 K : Subgroup (adjointGroup .E8 K)) = 3 ^ 7 := by
  obtain ⟨hSJ, hcyc, hS⟩ := cyclicity_hyp_rootThree (K := K) hK
  have hFC : F ≤ Subgroup.centralizer (Subgroup.zpowers
      (rootThree .E8 K (highRoot .E8)) : Set (adjointGroup .E8 K)) := by
    rwa [centralizer_zpowers_rootThree_eq (K := K)]
  exact card_inf_perpLevi_of_nonsplit_card_eight hK hSJ hcyc hS hFC hE hc

private theorem exists_mem_perpLevi_map_conj_inf_eq (hK : Nat.card K = 2)
    {F₁ F₂ : Subgroup (adjointGroup .E8 K)}
    (h₁ : F₁ ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (h₂ : F₂ ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (hE₁ : IsElemAbelian 3 F₁) (hE₂ : IsElemAbelian 3 F₂)
    (hc₁ : Nat.card F₁ = 3 ^ 8) (hc₂ : Nat.card F₂ = 3 ^ 8) :
    ∃ d ∈ EPilot.perpLevi .E8 K,
      (F₁ ⊓ EPilot.perpLevi .E8 K).map (MulAut.conj d).toMonoidHom =
        F₂ ⊓ EPilot.perpLevi .E8 K := by
  have hcard₁ := card_inf_perpLevi_of_isElemAbelian_card_eight (K := K) hK h₁ hE₁ hc₁
  have hcard₂ := card_inf_perpLevi_of_isElemAbelian_card_eight (K := K) hK h₂ hE₂ hc₂
  obtain ⟨m₁, hm₁D, hconj₁⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173O.exists_conj_eq_e8FrameV_of_le_e7Levi (K := K) hK
      (show F₁ ⊓ EPilot.perpLevi .E8 K ≤ E8Pilot.e7Levi K from inf_le_right)
      (hE₁.mono inf_le_left) (by rw [hcard₁])
  obtain ⟨m₂, hm₂D, hconj₂⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173O.exists_conj_eq_e8FrameV_of_le_e7Levi (K := K) hK
      (show F₂ ⊓ EPilot.perpLevi .E8 K ≤ E8Pilot.e7Levi K from inf_le_right)
      (hE₂.mono inf_le_left) (by rw [hcard₂])
  refine ⟨m₂⁻¹ * m₁, mul_mem (inv_mem hm₂D) hm₁D, ?_⟩
  have ha₁ : F₁ ⊓ EPilot.perpLevi .E8 K =
      (CFSG.LocalAnalysis.GLTheoremA.T173O.e8FrameV K).map
        (MulAut.conj m₁⁻¹).toMonoidHom := by
    have h := congrArg (Subgroup.map (MulAut.conj m₁⁻¹).toMonoidHom) hconj₁
    rw [map_conj_inv_map_conj'] at h
    exact h
  have ha₂ : F₂ ⊓ EPilot.perpLevi .E8 K =
      (CFSG.LocalAnalysis.GLTheoremA.T173O.e8FrameV K).map
        (MulAut.conj m₂⁻¹).toMonoidHom := by
    have h := congrArg (Subgroup.map (MulAut.conj m₂⁻¹).toMonoidHom) hconj₂
    rw [map_conj_inv_map_conj'] at h
    exact h
  rw [ha₂, ← map_conj_map_conj' (F₁ ⊓ EPilot.perpLevi .E8 K) m₁ m₂⁻¹, hconj₁]

theorem exists_mem_perpLevi_map_conj_eq_of_le_centralizer_rootThree (hK : Nat.card K = 2)
    {F₁ F₂ : Subgroup (adjointGroup .E8 K)}
    (h₁ : F₁ ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (h₂ : F₂ ≤ Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)))
    (hE₁ : IsElemAbelian 3 F₁) (hE₂ : IsElemAbelian 3 F₂)
    (hc₁ : Nat.card F₁ = 3 ^ 8) (hc₂ : Nat.card F₂ = 3 ^ 8) :
    ∃ d ∈ EPilot.perpLevi .E8 K, F₁.map (MulAut.conj d).toMonoidHom = F₂ := by
  have hs₁ := mem_rootThree_of_isElemAbelian_card_eight (K := K) hK h₁ hE₁ hc₁
  have hs₂ := mem_rootThree_of_isElemAbelian_card_eight (K := K) hK h₂ hE₂ hc₂
  have heq₁ := eq_sup_inf_perpLevi_of_mem_rootThree (K := K) hK h₁ hs₁
  have heq₂ := eq_sup_inf_perpLevi_of_mem_rootThree (K := K) hK h₂ hs₂
  obtain ⟨d, hdD, hconjd⟩ :=
    exists_mem_perpLevi_map_conj_inf_eq (K := K) hK h₁ h₂ hE₁ hE₂ hc₁ hc₂
  refine ⟨d, hdD, ?_⟩
  have hcd : Commute d (rootThree .E8 K (highRoot .E8)) :=
    Subgroup.mem_centralizer_singleton_iff.1 (perpLevi_le_centralizer_rootThree (K := K) hdD)
  have hSmap : (Subgroup.zpowers (rootThree .E8 K (highRoot .E8))).map
      (MulAut.conj d).toMonoidHom = Subgroup.zpowers (rootThree .E8 K (highRoot .E8)) := by
    rw [MonoidHom.map_zpowers]
    apply congrArg Subgroup.zpowers
    show (MulAut.conj d) (rootThree .E8 K (highRoot .E8)) = rootThree .E8 K (highRoot .E8)
    rw [MulAut.conj_apply, hcd.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [heq₁, Subgroup.map_sup, hconjd, hSmap, ← heq₂]

end M3g

end CFSG.StandardType.FrameRoute.FS81

end
