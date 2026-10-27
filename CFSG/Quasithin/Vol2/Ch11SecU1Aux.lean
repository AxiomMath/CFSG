module

public import CFSG.Quasithin.Vol2.Ch11SecU1Crit
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G]

omit [Group G] in
theorem mem_zpowers_involution {G : Type*} [Group G] {w x : G} (hw : orderOf w = 2)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ← hw, pow_orderOf_eq_one]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hw2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]

theorem SigmaFacts.conj {L : Subgroup G} (hLn : L.Normal) {b : G} (h : SigmaFacts L b) (g : G) :
    SigmaFacts L (g * b * g⁻¹) := by
  obtain ⟨L₀, hle, hs, ⟨x, y, hxy⟩, hnorm, hcent⟩ := h
  set e : ↥L₀ ≃* ↥(A1b.conjSub g L₀) :=
    L₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective with he
  have hmem : ∀ w : G, w ∈ A1b.conjSub g L₀ ↔ g⁻¹ * w * g ∈ L₀ := fun w => A1b.mem_conjSub_iff
  have hconj : ∀ w c : G, g⁻¹ * w * g * c = c * (g⁻¹ * w * g) →
      w * (g * c * g⁻¹) = g * c * g⁻¹ * w := fun w c h => by
    calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * w := by group
  refine ⟨A1b.conjSub g L₀, fun w hw => ?_, e.symm.isSimpleGroup, ⟨e x, e y, fun h => hxy ?_⟩,
    fun c hc => ?_, ?_⟩
  · have hw' := hle ((hmem w).mp hw)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := hLn.conj_mem _ hw'.1 g
      simpa [mul_assoc] using this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hconj w b (Subgroup.mem_centralizer_singleton_iff.mp hw'.2)
  · exact e.injective (by rw [map_mul, map_mul, h])
  · have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g⁻¹ * c * g * b = g⁻¹ * (c * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b * g⁻¹ * c) * g := by rw [hc]
        _ = b * (g⁻¹ * c * g) := by group
    have hN := hnorm hc'
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro w
    rw [hmem, hmem]
    have := hN (g⁻¹ * w * g)
    rw [show g⁻¹ * c * g * (g⁻¹ * w * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * w * c⁻¹) * g by group]
      at this
    exact this
  · refine le_bot_iff.mp fun w hw => ?_
    have hw' : g⁻¹ * w * g ∈ L ⊓ Subgroup.centralizer (L₀ : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := hLn.conj_mem _ hw.1 g⁻¹
        simpa [mul_assoc] using this
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 := Subgroup.mem_centralizer_iff.mp hw.2 (g * l * g⁻¹)
          ((hmem _).mpr (by simpa [mul_assoc] using hl))
        calc l * (g⁻¹ * w * g) = g⁻¹ * ((g * l * g⁻¹) * w) * g := by group
          _ = g⁻¹ * (w * (g * l * g⁻¹)) * g := by rw [h1]
          _ = g⁻¹ * w * g * l := by group
    rw [hcent, Subgroup.mem_bot] at hw'
    rw [Subgroup.mem_bot]
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [hw']; group

namespace Setting

variable [Finite G] {L : Subgroup G} (h : Setting L)
include h

theorem isSolvable_centralizer {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) := by
  have := h.almostSimple.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G)
  have : Group.IsSolvable ↥(L ⊓ C) := h.inner_solvable z hzL hz2
  have : Group.IsNilpotent (G ⧸ L) := h.almostSimple.isPGroup_quotient.isNilpotent
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_right : L ⊓ C ≤ C))
    ((QuotientGroup.mk' L).comp C.subtype) fun x hx => ?_
  have hxL : (x : G) ∈ L := (QuotientGroup.eq_one_iff _).mp hx
  exact ⟨⟨x, hxL, x.2⟩, rfl⟩

theorem sup_eq_top {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : L ⊔ T = ⊤ := by
  have := h.almostSimple.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (L ⊔ T).index ∣ L.index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : (L ⊔ T).index ∣ T.index := Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp h.almostSimple.isPGroup_quotient)
  rw [← Subgroup.index] at hk
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact Subgroup.index_eq_one.mp hj
  · exact absurd ((hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2) hT2

theorem exists_central_involution {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) :
    ∃ z ∈ L, orderOf z = 2 ∧ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  have hLn := h.almostSimple.normal
  have hSyl : IsSylowIn 2 (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hne : T ⊓ L ≠ ⊥ := by
    intro hbot
    apply hSyl.2.2
    rw [hbot, Subgroup.relIndex_bot_left]
    exact h.two_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
  set M : Subgroup ↥T := (T ⊓ L).subgroupOf T with hM
  have hMn : M.Normal := ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr
    ⟨T.mul_mem (T.mul_mem g.2 x.2) (T.inv_mem g.2),
      hLn.conj_mem _ (Subgroup.mem_subgroupOf.mp hx).2 g⟩⟩
  have hMne : M ≠ ⊥ := by
    intro hbot
    apply hne
    refine le_bot_iff.mp fun x hx => ?_
    have hx' : (⟨x, hx.1⟩ : ↥T) ∈ M := Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hMne
  have hXp : IsPGroup 2 ↥(M ⊓ Subgroup.center ↥T) := hT.2.1.to_subgroup _
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hX (Subgroup.card_eq_one.mp hk)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ Subgroup.center ↥T)) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hyM : (y : ↥T) ∈ M := y.2.1
  have hyZ : (y : ↥T) ∈ Subgroup.center ↥T := y.2.2
  have hyTL : ((y : ↥T) : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hyM
  refine ⟨((y : ↥T) : G), hyTL.2, ?_, hyTL.1, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy2
  · have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨t, ht⟩)
    simpa using this

theorem isCoatom_centralizer {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set G)) := by
  have hLn := h.almostSimple.normal
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  refine ⟨fun htop => hz1 ?_, fun Y hY => ?_⟩
  · have hzc : z ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l _
      have hl : l ∈ C := by rw [htop]; exact Subgroup.mem_top l
      exact Subgroup.mem_centralizer_singleton_iff.mp hl
    rw [h.almostSimple.centralizer_eq] at hzc
    exact Subgroup.mem_bot.mp hzc
  have hzC : z ∈ L ⊓ C := ⟨hzL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCY : L ⊓ C ≤ L ⊓ Y := inf_le_inf_left L hY.le
  by_cases hM : L ⊓ C < L ⊓ Y
  · have hLY : L ≤ Y := by
      have := h.inner_max z hzL hz2 (L ⊓ Y) hM inf_le_left
      rw [← this]
      exact inf_le_right
    refine eq_top_iff.mpr fun g _ => ?_
    have hgz : g * z * g⁻¹ ∈ L := hLn.conj_mem z hzL g
    obtain ⟨l, hlL, hl⟩ := h.inner_conj _ hgz z hzL (by rw [orderOf_conj']; exact hz2) hz2
    have hlg : l * g ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * g * z = (l * (g * z * g⁻¹) * l⁻¹) * (l * g) := by group
        _ = z * (l * g) := by rw [hl]
    have : g = l⁻¹ * (l * g) := by group
    rw [this]
    exact Y.mul_mem (Y.inv_mem (hLY hlL)) (hY.le hlg)
  · exfalso
    have hMeq : L ⊓ Y = L ⊓ C := (eq_of_le_of_not_lt hCY hM).symm
    refine hY.ne (le_antisymm hY.le fun y hy => ?_)
    have hyz : y * z * y⁻¹ ∈ L ⊓ C := by
      rw [← hMeq]
      exact ⟨hLn.conj_mem z hzL y, Y.mul_mem (Y.mul_mem hy (hY.le hzC.2)) (Y.inv_mem hy)⟩
    have hcen : ∀ w ∈ L ⊓ C, y * z * y⁻¹ * w = w * (y * z * y⁻¹) := by
      intro w hw
      have hw' : y⁻¹ * w * y ∈ L ⊓ C := by
        rw [← hMeq]
        refine ⟨?_, Y.mul_mem (Y.mul_mem (Y.inv_mem hy) ?_) hy⟩
        · have := hLn.conj_mem w hw.1 y⁻¹
          simpa using this
        · rw [← hMeq] at hw
          exact hw.2
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hw'.2
      calc y * z * y⁻¹ * w = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by rw [h1]
        _ = w * (y * z * y⁻¹) := by group
    rcases mem_zpowers_involution hz2 (h.inner_center z hzL hz2 _ hyz hcen) with h1 | h1
    · refine absurd ?_ hz1
      calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [h1]

end Setting

end CFSG.Quasithin.Vol2.Ch11.SecU1
