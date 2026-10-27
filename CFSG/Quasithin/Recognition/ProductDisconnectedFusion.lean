module

public import CFSG.Quasithin.Recognition.ProductDisconnected

public section

namespace CFSG.Quasithin.Recognition

variable {G : Type} [Group G]

theorem centralizer_conj_le {E : Subgroup G} {y e : G} (he : e ∈ E)
    (hy : Subgroup.centralizer ({y} : Set G) ≤ E) :
    Subgroup.centralizer ({e * y * e⁻¹} : Set G) ≤ E := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have h1 : e⁻¹ * c * e ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc e⁻¹ * c * e * y = e⁻¹ * (c * (e * y * e⁻¹)) * e := by group
      _ = e⁻¹ * (e * y * e⁻¹ * c) * e := by rw [hc]
      _ = y * (e⁻¹ * c * e) := by group
  have h2 : c = e * (e⁻¹ * c * e) * e⁻¹ := by group
  rw [h2]
  exact E.mul_mem (E.mul_mem he (hy h1)) (E.inv_mem he)

theorem orderOf_mul_of_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  refine orderOf_eq_prime ?_ ?_
  · rw [Commute.mul_pow hab 2, ha2, hb2, one_mul]
  · intro h
    apply hne
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
    rw [eq_inv_of_mul_eq_one_left h, hbinv]

theorem zd_conditions_of_fusion {E : Subgroup G} {d : G}
    (hCd : Subgroup.centralizer ({d} : Set G) ≤ E)
    (hfus : ∀ a ∈ E, ∀ b ∈ E, orderOf a = 2 → IsConj a b → ∃ e ∈ E, e * a * e⁻¹ = b)
    (hd : orderOf d = 2)
    (hprod : ∀ e : G, IsConj d e → d * e = e * d → e ≠ d →
      Subgroup.centralizer ({d * e} : Set G) ≤ E) :
    ({x : G | IsConj d x} ∩ (E : Set G)).Nonempty ∧
      (∀ x ∈ {x : G | IsConj d x}, x ∈ E → Subgroup.centralizer ({x} : Set G) ≤ E ∧
        ∀ y ∈ {x : G | IsConj d x}, y ∈ E → ∃ e ∈ E, e * x * e⁻¹ = y) ∧
      ∀ x ∈ {x : G | IsConj d x}, ∀ y ∈ {x : G | IsConj d x}, x * y = y * x → x ≠ y →
        x * y ∈ E → Subgroup.centralizer ({x * y} : Set G) ≤ E := by
  have hdE : d ∈ E := hCd (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hDE : ∀ x : G, IsConj d x → x ∈ E → ∃ e ∈ E, e * d * e⁻¹ = x := fun x hx hxE =>
    hfus d hdE x hxE hd hx
  refine ⟨⟨d, IsConj.refl d, hdE⟩, fun x hx hxE => ?_, fun x hx y hy hxy hne hxyE => ?_⟩
  · obtain ⟨e, heE, rfl⟩ := hDE x hx hxE
    refine ⟨centralizer_conj_le heE hCd, fun y hy hyE => ?_⟩
    obtain ⟨e', he'E, rfl⟩ := hDE y hy hyE
    refine ⟨e' * e⁻¹, E.mul_mem he'E (E.inv_mem heE), ?_⟩
    group
  ·
    obtain ⟨g, rfl⟩ := isConj_iff.1 hx
    have hy'D : IsConj d (g⁻¹ * y * g) :=
      hy.trans (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)
    have hcomm : d * (g⁻¹ * y * g) = g⁻¹ * y * g * d := by
      have h1 : g⁻¹ * (g * d * g⁻¹ * y) * g = g⁻¹ * (y * (g * d * g⁻¹)) * g := by rw [hxy]
      calc d * (g⁻¹ * y * g) = g⁻¹ * (g * d * g⁻¹ * y) * g := by group
        _ = g⁻¹ * (y * (g * d * g⁻¹)) * g := h1
        _ = g⁻¹ * y * g * d := by group
    have hne' : g⁻¹ * y * g ≠ d := by
      intro h
      apply hne
      rw [← h]
      group
    have hy'2 : orderOf (g⁻¹ * y * g) = 2 := by
      obtain ⟨c, hc⟩ := hy'D
      rw [← hc.orderOf_eq, hd]
    have hdy'E : d * (g⁻¹ * y * g) ∈ E := hCd (by
      rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, ← hcomm])
    have hconj : IsConj (d * (g⁻¹ * y * g)) (g * d * g⁻¹ * y) := isConj_iff.2 ⟨g, by group⟩
    obtain ⟨e, heE, he⟩ := hfus _ hdy'E _ hxyE
      (orderOf_mul_of_commute hd hy'2 hcomm hne'.symm) hconj
    rw [← he]
    exact centralizer_conj_le heE (hprod _ hy'D hcomm hne')

theorem eq_top_of_fusion
    [Finite G] (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    {E : Subgroup G} (hEs : IsSimpleGroup ↥E) (hEna : ∃ a b : ↥E, a * b ≠ b * a) {d : G}
    (hd : orderOf d = 2) (hCd : Subgroup.centralizer ({d} : Set G) ≤ E)
    (hfus : ∀ a ∈ E, ∀ b ∈ E, orderOf a = 2 → IsConj a b → ∃ e ∈ E, e * a * e⁻¹ = b)
    (hprod : ∀ e : G, IsConj d e → d * e = e * d → e ≠ d →
      Subgroup.centralizer ({d * e} : Set G) ≤ E) : E = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hE
  obtain ⟨ha, hb, hc⟩ := zd_conditions_of_fusion hCd hfus hd hprod
  obtain ⟨-, ⟨S, hS⟩, -⟩ :=
    product_disconnected_bender_recognition hs hna E hE _ ⟨d, hd, rfl⟩ ha hb hc
  have hgN : ∀ g ∈ E, g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := fun g hg => hS ▸ hg
  have hSE : (S : Subgroup G) ≤ E := fun s hs => hS ▸ Subgroup.le_normalizer hs
  have hnorm : ((S : Subgroup G).subgroupOf E).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hgN g g.2) n).mp hn⟩
  rcases hEs.eq_bot_or_eq_top_of_normal ((S : Subgroup G).subgroupOf E) with h | h
  ·
    apply S.ne_bot_of_dvd_card (hd ▸ orderOf_dvd_natCard d)
    rw [eq_bot_iff]
    intro s hs
    have hs' : (⟨s, hSE hs⟩ : ↥E) ∈ (S : Subgroup G).subgroupOf E := hs
    rw [h, Subgroup.mem_bot] at hs'
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hs')
  ·
    have hES : E ≤ (S : Subgroup G) := fun x hx => by
      have hx' : (⟨x, hx⟩ : ↥E) ∈ (S : Subgroup G).subgroupOf E := h ▸ Subgroup.mem_top _
      exact hx'
    have hE2 : IsPGroup 2 ↥E := S.2.to_le hES
    have hZ : Nontrivial (Subgroup.center ↥E) := hE2.center_nontrivial
    rcases hEs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥E) with hZ1 | hZ1
    · exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ hZ1
    · obtain ⟨a, b, hab⟩ := hEna
      apply hab
      have ha : a ∈ Subgroup.center ↥E := hZ1 ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm

end CFSG.Quasithin.Recognition
