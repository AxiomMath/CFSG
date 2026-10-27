module

public import CFSG.RankThree.GF2n.Stroth80.Sec101SLCard
public import CFSG.RankThree.GF2n.Stroth80.Sec101Comp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem exists_Rt_of_three_factors [(Q.subgroupOf M).Normal]
    (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    (hcs : CompSimple (Mbar M Q)) {X₁ X₂ X₃ : Subgroup (Mbar M Q)}
    (hc12 : ∀ x ∈ X₁, ∀ y ∈ X₂, Commute x y)
    (hc3 : ∀ x ∈ X₁ ⊔ X₂, ∀ y ∈ X₃, Commute x y)
    (h1 : IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))))
    (h2 : IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B))))
    (h3 : IsQSNormalIn X₃ (bar M Q (Lgen M (LB M Q B)))) :
    ∃ (t : ↥M) (c₂ : IsComponent X₂) (c₃ : IsComponent X₃),
      (t : G) ∈ LB M Q B ∧ (t : G) ∉ Q ∧
        X₂ ≤ bar M Q (Rt M (LB M Q B) (t : G)) ∧
        X₃ ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  set S : Subgroup (Mbar M Q) := bar M Q (Lgen M (LB M Q B))
  have hSn : S.Normal := hc.normal_bar_Lgen
  have hc₂ : IsComponent X₂ :=
    ⟨h2.2.2, Subgroup.IsSubnormal.step X₂ S h2.1 hSn.isSubnormal h2.2.1⟩
  have hc₃ : IsComponent X₃ :=
    ⟨h3.2.2, Subgroup.IsSubnormal.step X₃ S h3.1 hSn.isSubnormal h3.2.1⟩
  have hΛX₁ : bar M Q (LB M Q B) ≤ Subgroup.normalizer (X₁ : Set (Mbar M Q)) :=
    hc.bar_LB_le_normalizer_of_normal h1.1 h1.2.1
  have hne : bar M Q (LB M Q B) ⊓ X₁ ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 H.width H.n_gt H.noA2 H.gen h1.2.2 hΛX₁
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxΛ : (x : Mbar M Q) ∈ bar M Q (LB M Q B) := x.2.1
  have hxX₁ : (x : Mbar M Q) ∈ X₁ := x.2.2
  have hxne : (x : Mbar M Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨t, htLB, htQ, htx⟩ := hc.exists_lift_ne_one hxΛ hxne
  have htx₁ : (QuotientGroup.mk t : Mbar M Q) ∈ X₁ := by rw [htx]; exact hxX₁
  have hcent₂ : ∀ y ∈ X₂, y * (QuotientGroup.mk t : Mbar M Q) =
      (QuotientGroup.mk t : Mbar M Q) * y := by
    intro y hy
    exact ((commute_iff_eq _ _).mp (hc12 _ htx₁ _ hy)).symm
  have hcent₃ : ∀ y ∈ X₃, y * (QuotientGroup.mk t : Mbar M Q) =
      (QuotientGroup.mk t : Mbar M Q) * y := by
    intro y hy
    exact ((commute_iff_eq _ _).mp (hc3 _ (Subgroup.mem_sup_left htx₁) _ hy)).symm
  have hR₂ : X₂ ≤ bar M Q (Rt M (LB M Q B) (t : G)) :=
    hc.component_le_bar_Rt h34 H.width H.n_gt H.noA2 H.gen hcs hc₂ htLB hcent₂
  have hR₃ : X₃ ≤ bar M Q (Rt M (LB M Q B) (t : G)) :=
    hc.component_le_bar_Rt h34 H.width H.n_gt H.noA2 H.gen hcs hc₃ htLB hcent₃
  exact ⟨t, hc₂, hc₃, htLB, htQ, hR₂, hR₃⟩

theorem Sec10Hyp.false_of_three_factors [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h44 : Stroth44Statement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {X₁ X₂ X₃ : Subgroup (Mbar M Q)}
    (hc12 : ∀ x ∈ X₁, ∀ y ∈ X₂, Commute x y) (hc3 : ∀ x ∈ X₁ ⊔ X₂, ∀ y ∈ X₃, Commute x y)
    (h1 : IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))))
    (h2 : IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B))))
    (h3 : IsQSNormalIn X₃ (bar M Q (Lgen M (LB M Q B)))) : False := by
  have hcs : CompSimple (Mbar M Q) := hc.compSimple h34 h44 H.width H.n_gt H.noA2 H.gen
  obtain ⟨t, hc₂, hc₃, htLB, htQ, hR₂, hR₃⟩ :=
    exists_Rt_of_three_factors h34 hc H hcs hc12 hc3 h1 h2 h3
  obtain ⟨m, hm2, hm⟩ := H.exists_SLMNat_of_le_bar_Rt htLB htQ hR₂
    (exists_noncomm_of_isComponent hc₂)
  obtain ⟨K, fK, finK, hK, π, hπsurj, hπker⟩ := hc.exists_bar_hom_of_SLMNat htLB hm
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hSL : CFSG.IsQuasisimple ↥(StatedSL m K) := statedSL_quasisimple_of_card m K hm2 h4
  have hN₂ : X₂ ⊓ bar M Q (hc.CN t) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 H.width H.n_gt H.noA2 H.gen hcs htLB hc₂ hR₂
  have hN₃ : X₃ ⊓ bar M Q (hc.CN t) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 H.width H.n_gt H.noA2 H.gen hcs htLB hc₃ hR₃
  set S : Subgroup (Mbar M Q) := bar M Q (Lgen M (LB M Q B))
  have hRleS : bar M Q (Rt M (LB M Q B) (t : G)) ≤ S :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M (Rt_le_Lgen M (LB M Q B) (t : G)))
  have hSnorm₂ : S ≤ Subgroup.normalizer (X₂ : Set (Mbar M Q)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h2.1).mp h2.2.1
  have hX₂n : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t : G)), ∀ y ∈ X₂,
      r * y * r⁻¹ ∈ X₂ := by
    intro r hr y hy
    exact (Subgroup.mem_normalizer_iff.mp (hSnorm₂ (hRleS hr)) y).mp hy
  have hcomm : ∀ y ∈ X₂, ∀ z ∈ X₃, y * z = z * y := by
    intro y hy z hz
    exact (commute_iff_eq _ _).mp (hc3 _ (Subgroup.mem_sup_right hy) _ hz)
  exact false_of_commuting_in_quasisimple (Gc := ↥(StatedSL m K))
    (R := bar M Q (Rt M (LB M Q B) (t : G))) (N := bar M Q (hc.CN t))
    (X₂ := X₂) (X₃ := X₃) hSL π hπsurj hπker hR₂ hR₃ hX₂n hN₂ hN₃ hcomm
    (exists_noncomm_of_isComponent hc₂) (exists_noncomm_of_isComponent hc₃)

end CFSG.RankThree.GF2n.Stroth80
