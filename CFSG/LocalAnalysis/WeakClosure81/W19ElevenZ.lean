module

public import CFSG.LocalAnalysis.WeakClosure81.W19Five
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem_fin {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge)

theorem normalizer_le_rankThreeGamma_of_isElemAbelian {R Q : Subgroup G} (hQR : Q ≤ R)
    (hQ : IsElemAbelian 2 Q) (hQ1 : Q ≠ ⊥) :
    normalizer (Q : Set G) ≤ rankThreeGamma 1 2 R := by
  obtain ⟨⟨y, hyQ⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ1
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyq : y ∈ Q := hyQ
  have hsq : y ^ 2 = 1 := hQ.2 y hyq
  have hord : orderOf y = 2 := orderOf_eq_prime hsq hy1'
  have hEQ : Subgroup.zpowers y ≤ Q := Subgroup.zpowers_le.2 hyq
  have hE : IsElemAbelian 2 (Subgroup.zpowers y) := CFSG.Open.IsElemAbelian.mono hQ hEQ
  have hcard : Nat.card (Subgroup.zpowers y) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank 2 Q := CFSG.SectionRank.le_pRank (by norm_num) hEQ hE hcard
  rw [rankThreeGamma, GLBCore]
  exact le_sSup ⟨Q, hQR, hrank, rfl⟩

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem isElemAbelian_Z193 (_c : MinCex193 D V₀ V p X) : IsElemAbelian 2 (Z193 D V) :=
  ⟨⟨⟨fun x y => Subtype.ext (A4.mul_comm_of_mem_omegaOneCenterOf x.2 y.2)⟩⟩,
    fun _ hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩

theorem Z193_le_T (_c : MinCex193 D V₀ V p X) : Z193 D V ≤ D.T :=
  (A4.omegaOneCenterOf_le _).trans (E3.wClos_le 1 D.T)

theorem T_le_normalizer_Z193 (_c : MinCex193 D V₀ V p X) :
    D.T ≤ normalizer (Z193 D V : Set G) :=
  Subgroup.le_normalizer.trans ((E3.normalizer_le_normalizer_wClos (V := V) (i := 1) D.T).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _))

theorem V₀_le_Z193 (c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2) : V₀ ≤ Z193 D V := by
  have hne := c.inf_Z193_ne_bot
  have hle : V₀ ⊓ Z193 D V ≤ V₀ := inf_le_left
  have hdvd : Nat.card ↥(V₀ ⊓ Z193 D V) ∣ 2 := h2 ▸ Subgroup.card_dvd_of_le hle
  have h1 : Nat.card ↥(V₀ ⊓ Z193 D V) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hpos : 0 < Nat.card ↥(V₀ ⊓ Z193 D V) := Nat.card_pos
  have hc2 : Nat.card ↥(V₀ ⊓ Z193 D V) = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have heq : V₀ ⊓ Z193 D V = V₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc2, h2])
  exact heq ▸ inf_le_right

theorem exists_v₀ (_c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2) :
    ∃ v ∈ V₀, v ≠ 1 ∧ ∀ x ∈ V₀, x = 1 ∨ x = v := by
  obtain ⟨v, hv, hvu⟩ := (Nat.card_eq_two_iff' (1 : ↥V₀)).1 h2
  refine ⟨v, v.2, fun h => hv (Subtype.ext h), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · refine Or.inr ?_
    have := hvu ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    exact (congrArg Subtype.val this)

theorem conj_eq_of_mem_M (c : MinCex193 D V₀ V p X) {v : G} (hv : v ∈ V₀) (hv1 : v ≠ 1)
    (hV₀ : ∀ x ∈ V₀, x = 1 ∨ x = v) {m : G} (hm : m ∈ D.M) : m * v * m⁻¹ = v := by
  have hm' : m ∈ normalizer (V₀ : Set G) := c.setting.pair.le_normalizer₀ hm
  have h1 : m * v * m⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hm' v).1 hv
  rcases hV₀ _ h1 with h | h
  · exfalso
    apply hv1
    have : v = m⁻¹ * (m * v * m⁻¹) * m := by group
    rw [this, h]
    group
  · exact h

theorem mem_M_of_conj_eq (c : MinCex193 D V₀ V p X) {v : G} (hv : v ∈ V₀)
    (hV₀ : ∀ x ∈ V₀, x = 1 ∨ x = v) {n : G} (hn : n * v * n⁻¹ = v) : n ∈ D.M := by
  have h1 : n ∈ normalizer (V₀ : Set G) := by
    refine mem_normalizer_of_conj_mem_fin fun x hx => ?_
    rcases hV₀ x hx with h | h
    · rw [h]
      simpa using V₀.one_mem
    · rw [h, hn]
      exact hv
  rwa [c.setting.normalizer₀ c.ne_bot] at h1

theorem eq_one_of_centralizes_normalizer_Z193 (c : MinCex193 D V₀ V p X) {a : G}
    (ha : a ∈ Z193 D V) (hfix : ∀ n ∈ normalizer (Z193 D V : Set G), n * a * n⁻¹ = a) :
    a = 1 := by
  by_contra ha1
  have haT : a ∈ D.T := c.Z193_le_T ha
  have hcen : a ∈ centerOf D.T := by
    refine ⟨haT, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have := hfix t (c.T_le_normalizer_Z193 ht)
    calc t * a = t * a * t⁻¹ * t := by group
      _ = a * t := by rw [this]
  have hQ : Subgroup.zpowers a ≤ centerOf D.T := Subgroup.zpowers_le.2 hcen
  have hQe : IsElemAbelian 2 (Subgroup.zpowers a) :=
    CFSG.Open.IsElemAbelian.mono c.isElemAbelian_Z193
      (Subgroup.zpowers_le.2 ha)
  have hQ1 : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    exact ha1 (Subgroup.zpowers_eq_bot.1 h)
  have hΓ : normalizer (Subgroup.zpowers a : Set G) ≤ D.M :=
    (normalizer_le_rankThreeGamma_of_isElemAbelian hQ hQe hQ1).trans c.gamma
  obtain ⟨g, hgN, hgM⟩ := c.exists_mem_normalizer_Z
  apply hgM
  apply hΓ
  refine mem_normalizer_of_conj_mem_fin fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have : g * a ^ k * g⁻¹ = a ^ k := by
    rw [← conj_zpow, hfix g hgN]
  rw [this]
  exact Subgroup.zpow_mem_zpowers a k

theorem exists_ne_one_centralizes_of_normalized (c : MinCex193 D V₀ V p X) {S : Subgroup G}
    (hS : S ≤ Z193 D V) (hS1 : S ≠ ⊥) (hn : ∀ t ∈ D.T, ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    ∃ s ∈ S, s ≠ 1 ∧ ∀ t ∈ D.T, t * s * t⁻¹ = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hST : S ≤ D.T := hS.trans c.Z193_le_T
  haveI hnil : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
  haveI hnorm : (S.subgroupOf D.T).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn (g : G) g.2 (x : G) hx
  have hne : S.subgroupOf D.T ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [← Subgroup.map_subgroupOf_eq_of_le hST, hbot, Subgroup.map_bot]
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have haS : ((a.1 : ↥D.T) : G) ∈ S := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 a.2).1
  have haZ : (a.1 : ↥D.T) ∈ Subgroup.center ↥D.T := (Subgroup.mem_inf.1 a.2).2
  refine ⟨((a.1 : ↥D.T) : G), haS, fun h => ha ?_, fun t ht => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 haZ ⟨t, ht⟩)
    have h2 : t * ((a.1 : ↥D.T) : G) = ((a.1 : ↥D.T) : G) * t := by simpa using h1
    calc t * ((a.1 : ↥D.T) : G) * t⁻¹ = ((a.1 : ↥D.T) : G) * t * t⁻¹ := by rw [h2]
      _ = ((a.1 : ↥D.T) : G) := by group

theorem mem_M_of_normalizes_fixed (c : MinCex193 D V₀ V p X) {Y : Subgroup G}
    (hY : Y ≤ Z193 D V) (hY1 : Y ≠ ⊥) (hT : ∀ y ∈ Y, ∀ t ∈ D.T, t * y * t⁻¹ = y) {n : G}
    (hn : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) : n ∈ D.M := by
  have hcen : Y ≤ centerOf D.T := fun y hy => by
    refine ⟨c.Z193_le_T (hY hy), Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have := hT y hy t ht
    calc t * y = t * y * t⁻¹ * t := by group
      _ = y * t := by rw [this]
  have hYe : IsElemAbelian 2 Y := CFSG.Open.IsElemAbelian.mono c.isElemAbelian_Z193 hY
  exact c.gamma ((normalizer_le_rankThreeGamma_of_isElemAbelian hcen hYe hY1)
    (mem_normalizer_of_conj_mem_fin hn))

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
