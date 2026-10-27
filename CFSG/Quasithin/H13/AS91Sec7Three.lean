module

public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Plane

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_adjLine (x : G ⧸ c.G1) :
    ∃ ℓ : G ⧸ c.G1 → G ⧸ c.G2, ∀ w, c.Delta.Adj x w → c.OnL x (ℓ w) ∧ c.OnL w (ℓ w) := by
  have hex : ∀ w : G ⧸ c.G1, ∃ n : G ⧸ c.G2, c.Delta.Adj x w → c.OnL x n ∧ c.OnL w n := by
    intro w
    by_cases h : c.Delta.Adj x w
    · obtain ⟨-, n, hxn, hwn⟩ := h
      exact ⟨n, fun _ => ⟨hxn, hwn⟩⟩
    · exact ⟨c.l0, fun h' => absurd h' h⟩
  exact ⟨fun w => (hex w).choose, fun w h => (hex w).choose_spec h⟩

theorem not_onL_of_two_pts (hLU : Stmt5_LineU) (hJ : HypJ4 G z) {x u v : G ⧸ c.G1}
    {m n : G ⧸ c.G2} (hxm : ¬ c.OnL x m) (hu : c.OnL u m) (hv : c.OnL v m) (huv : u ≠ v)
    (hun : c.OnL u n) (hvn : c.OnL v n) : ¬ c.OnL x n := fun hxn =>
  hxm (by rw [c.eq_of_onL hLU hJ huv hu hv hun hvn]; exact hxn)

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)


include ρ in
theorem pair_deltaAt (hI : Sec7Inputs) (hJ : HypJ4 G z) {x : G ⧸ c.G1} {π : G ⧸ c.G3}
    {m : G ⧸ c.G2} (hxπ : c.OnP x π) (hmπ : c.LnP m π) (hxm : ¬ c.OnL x m)
    {w₁ w₂ : G ⧸ c.G1} {n₁ n₂ : G ⧸ c.G2} (hw₁ : c.OnL w₁ m) (hw₂ : c.OnL w₂ m)
    (hw : w₁ ≠ w₂) (hxn₁ : c.OnL x n₁) (hwn₁ : c.OnL w₁ n₁) (hxn₂ : c.OnL x n₂)
    (hwn₂ : c.OnL w₂ n₂) :
    (n₂ ∈ c.deltaAt 1 x n₁ ∧ {a | c.OnL a m ∧ c.Delta.Adj x a}.ncard = 3) ∨
      (n₂ ∈ c.deltaAt 2 x n₁ ∧ ∀ a, c.OnL a m → c.Delta.Adj x a) := by
  have hxw₁ : x ≠ w₁ := fun h => hxm (by rw [h]; exact hw₁)
  have hxw₂ : x ≠ w₂ := fun h => hxm (by rw [h]; exact hw₂)
  have hadj₁ : c.Delta.Adj x w₁ := c.adj_of_onL hxw₁ hxn₁ hwn₁
  have hadj₂ : c.Delta.Adj x w₂ := c.adj_of_onL hxw₂ hxn₂ hwn₂
  have hadj₁₂ : c.Delta.Adj w₁ w₂ := c.adj_of_onL hw hw₁ hw₂
  have hn₁π : c.LnP n₁ π :=
    c.lnP_of_adj hI.gamma2 hJ hxπ (c.inc_pt_plane hw₁ hmπ) hadj₁ hxn₁ hwn₁
  have h56 := (hI.s56 G z hJ c w₁ x w₂ hadj₁.symm hadj₂ hadj₁₂).2.2
  rcases (ρ.coL_iff_deltaAt hwn₁ hw₁).1 ⟨π, hn₁π, hmπ⟩ with h0 | h1 | h2
  · exfalso
    have hmn : m = n₁ := (ρ.mem_deltaAt_zero_iff hwn₁ hw₁).1 h0
    exact hxm (by rw [hmn]; exact hxn₁)
  · exact Or.inl ⟨h56 n₁ m n₂ 1 hwn₁ hxn₁ hw₁ hw₂ hxn₂ hwn₂ h1,
      c.stmt7_1_one hI.s54 hJ hwn₁ hxn₁ hxw₁ h1⟩
  · exact Or.inr ⟨h56 n₁ m n₂ 2 hwn₁ hxn₁ hw₁ hw₂ hxn₂ hwn₂ h2,
      fun a ha => c.stmt7_1_two hI.s54 hJ hwn₁ hxn₁ hxw₁ h2 ha⟩

include ρ in
theorem mem_deltaAt_one_of_ncard (hI : Sec7Inputs) (hJ : HypJ4 G z) {x : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hxπ : c.OnP x π) (hmπ : c.LnP m π) (hxm : ¬ c.OnL x m)
    (h3 : {w | c.OnL w m ∧ c.Delta.Adj x w}.ncard = 3)
    {w₁ w₂ : G ⧸ c.G1} {n₁ n₂ : G ⧸ c.G2} (hw₁ : c.OnL w₁ m) (hw₂ : c.OnL w₂ m)
    (hw : w₁ ≠ w₂) (hxn₁ : c.OnL x n₁) (hwn₁ : c.OnL w₁ n₁) (hxn₂ : c.OnL x n₂)
    (hwn₂ : c.OnL w₂ n₂) : n₂ ∈ c.deltaAt 1 x n₁ := by
  rcases ρ.pair_deltaAt hI hJ hxπ hmπ hxm hw₁ hw₂ hw hxn₁ hwn₁ hxn₂ hwn₂ with ⟨h, -⟩ | ⟨-, h5⟩
  · exact h
  · exfalso
    have hset : {w | c.OnL w m ∧ c.Delta.Adj x w} = {w | c.OnL w m} :=
      Set.ext fun a => ⟨fun h => h.1, fun h => ⟨h, h5 a h⟩⟩
    rw [hset, c.ncard_onL] at h3
    omega

include ρ in
theorem mem_deltaAt_two_of_adj (hI : Sec7Inputs) (hJ : HypJ4 G z) {x : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hxπ : c.OnP x π) (hmπ : c.LnP m π) (hxm : ¬ c.OnL x m)
    (h5 : ∀ w, c.OnL w m → c.Delta.Adj x w)
    {w₁ w₂ : G ⧸ c.G1} {n₁ n₂ : G ⧸ c.G2} (hw₁ : c.OnL w₁ m) (hw₂ : c.OnL w₂ m)
    (hw : w₁ ≠ w₂) (hxn₁ : c.OnL x n₁) (hwn₁ : c.OnL w₁ n₁) (hxn₂ : c.OnL x n₂)
    (hwn₂ : c.OnL w₂ n₂) : n₂ ∈ c.deltaAt 2 x n₁ := by
  rcases ρ.pair_deltaAt hI hJ hxπ hmπ hxm hw₁ hw₂ hw hxn₁ hwn₁ hxn₂ hwn₂ with ⟨-, h3⟩ | ⟨h, -⟩
  · exfalso
    have hset : {w | c.OnL w m ∧ c.Delta.Adj x w} = {w | c.OnL w m} :=
      Set.ext fun a => ⟨fun h => h.1, fun h => ⟨h, h5 a h⟩⟩
    rw [hset, c.ncard_onL] at h3
    omega
  · exact h

theorem exists_lines_at (hI : Sec7Inputs) (hJ : HypJ4 G z) {g : G} {x : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hg : g • c.x0 = x) (hxπ : c.OnP x π) (hmπ : c.LnP m π) :
    ∃ ℓ : G ⧸ c.G1 → G ⧸ c.G2, ∀ w, c.OnL w m → c.Delta.Adj x w →
      c.OnL x (ℓ w) ∧ c.OnL w (ℓ w) ∧ c.LnP (ℓ w) π ∧
        ρ.trio (g⁻¹ • ℓ w) ∈ M24G.triosOf (ρ.sext (g⁻¹ • π)) ∧
        ∀ n, c.OnL x n → c.OnL w n → n = ℓ w := by
  obtain ⟨ℓ, hℓ⟩ := c.exists_adjLine x
  refine ⟨ℓ, fun w hwm hxw => ?_⟩
  obtain ⟨hxl, hwl⟩ := hℓ w hxw
  have hlπ : c.LnP (ℓ w) π :=
    c.lnP_of_adj hI.gamma2 hJ hxπ (c.inc_pt_plane hwm hmπ) hxw hxl hwl
  exact ⟨hxl, hwl, hlπ, ρ.trio_mem_triosOf hg hxπ hxl hlπ,
    fun n hxn hwn => c.eq_of_onL hI.lineU hJ hxw.ne hxn hwn hxl hwl⟩

theorem stmt7_3_one (hI : Sec7Inputs) (hJ : HypJ4 G z) {g : G} {x : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hg : g • c.x0 = x) (hxπ : c.OnP x π) (hmπ : c.LnP m π)
    (hxm : ¬ c.OnL x m) (h3 : {w | c.OnL w m ∧ c.Delta.Adj x w}.ncard = 3) :
    ∃ o ∈ M24G.octsOf (ρ.sext (g⁻¹ • π)), ∀ n, c.OnL x n →
      ((∃ w, c.OnL w m ∧ c.Delta.Adj x w ∧ c.OnL w n) ↔ (c.LnP n π ∧ o ∈ ρ.trio (g⁻¹ • n))) := by
  obtain ⟨ℓ, hℓ⟩ := ρ.exists_lines_at hI hJ hg hxπ hmπ
  obtain ⟨w₁, w₂, w₃, h12, h13, h23, hW3⟩ := Set.ncard_eq_three.1 h3
  have hW : ∀ w, (c.OnL w m ∧ c.Delta.Adj x w) ↔ (w = w₁ ∨ w = w₂ ∨ w = w₃) := fun w => by
    simpa using Set.ext_iff.1 hW3 w
  have hU : IsSextet (ρ.sext (g⁻¹ • π)) := ρ.isSextet_sext_at hg hxπ
  have hpair : ∀ w w', c.OnL w m → c.Delta.Adj x w → c.OnL w' m → c.Delta.Adj x w' → w ≠ w' →
      ρ.trio (g⁻¹ • ℓ w) ≠ ρ.trio (g⁻¹ • ℓ w') ∧
        ¬ Disjoint (ρ.trio (g⁻¹ • ℓ w)) (ρ.trio (g⁻¹ • ℓ w')) := by
    intro w w' hwm hxw hw'm hxw' hne
    obtain ⟨hxl, hwl, -⟩ := hℓ w hwm hxw
    obtain ⟨hxl', hwl', -⟩ := hℓ w' hw'm hxw'
    obtain ⟨h1, h2⟩ := (ρ.mem_deltaAt_one_iff_at hg hxl hxl').1
      (ρ.mem_deltaAt_one_of_ncard hI hJ hxπ hmπ hxm h3 hwm hw'm hne hxl hwl hxl' hwl')
    exact ⟨fun h => h1 (ρ.eq_of_trio_at hg hxl' hxl h.symm), fun h => h2 h.symm⟩
  obtain ⟨hw₁m, hxw₁⟩ := (hW w₁).2 (Or.inl rfl)
  obtain ⟨hw₂m, hxw₂⟩ := (hW w₂).2 (Or.inr (Or.inl rfl))
  obtain ⟨hw₃m, hxw₃⟩ := (hW w₃).2 (Or.inr (Or.inr rfl))
  obtain ⟨-, -, -, hmem₁, -⟩ := hℓ w₁ hw₁m hxw₁
  obtain ⟨-, -, -, hmem₂, -⟩ := hℓ w₂ hw₂m hxw₂
  obtain ⟨-, -, -, hmem₃, -⟩ := hℓ w₃ hw₃m hxw₃
  obtain ⟨hT12, hM12⟩ := hpair w₁ w₂ hw₁m hxw₁ hw₂m hxw₂ h12
  obtain ⟨hT13, hM13⟩ := hpair w₁ w₃ hw₁m hxw₁ hw₃m hxw₃ h13
  obtain ⟨hT23, hM23⟩ := hpair w₂ w₃ hw₂m hxw₂ hw₃m hxw₃ h23
  obtain ⟨o, ho, ho₁, ho₂, ho₃⟩ := M24G.exists_common_octad hU hmem₁ hmem₂ hmem₃ hT12 hT13 hT23
    hM12 hM13 hM23
  have hpen : ({ρ.trio (g⁻¹ • ℓ w₁), ρ.trio (g⁻¹ • ℓ w₂), ρ.trio (g⁻¹ • ℓ w₃)} :
      Finset (Finset (Finset (Fin 24)))) =
      (M24G.triosOf (ρ.sext (g⁻¹ • π))).filter (o ∈ ·) := by
    refine Finset.eq_of_subset_of_card_le (fun t ht => ?_) ?_
    · rw [Finset.mem_filter]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [⟨hmem₁, ho₁⟩, ⟨hmem₂, ho₂⟩, ⟨hmem₃, ho₃⟩]
    · rw [M24G.card_pencil hU ho]
      exact (Finset.card_eq_three.2 ⟨_, _, _, hT12, hT13, hT23, rfl⟩).ge
  refine ⟨o, ho, fun n hxn => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hwm, hxw, hwn⟩
    obtain ⟨-, -, hlπ, -, huniq⟩ := hℓ w hwm hxw
    obtain rfl := huniq n hxn hwn
    refine ⟨hlπ, ?_⟩
    rcases (hW w).1 ⟨hwm, hxw⟩ with rfl | rfl | rfl
    exacts [ho₁, ho₂, ho₃]
  · rintro ⟨hnπ, hon⟩
    have ht : ρ.trio (g⁻¹ • n) ∈ ({ρ.trio (g⁻¹ • ℓ w₁), ρ.trio (g⁻¹ • ℓ w₂),
        ρ.trio (g⁻¹ • ℓ w₃)} : Finset (Finset (Finset (Fin 24)))) := by
      rw [hpen]
      exact Finset.mem_filter.2 ⟨ρ.trio_mem_triosOf hg hxπ hxn hnπ, hon⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ht | ht | ht
    · obtain ⟨hxl, hwl, -⟩ := hℓ w₁ hw₁m hxw₁
      obtain rfl := ρ.eq_of_trio_at hg hxl hxn ht.symm
      exact ⟨w₁, hw₁m, hxw₁, hwl⟩
    · obtain ⟨hxl, hwl, -⟩ := hℓ w₂ hw₂m hxw₂
      obtain rfl := ρ.eq_of_trio_at hg hxl hxn ht.symm
      exact ⟨w₂, hw₂m, hxw₂, hwl⟩
    · obtain ⟨hxl, hwl, -⟩ := hℓ w₃ hw₃m hxw₃
      obtain rfl := ρ.eq_of_trio_at hg hxl hxn ht.symm
      exact ⟨w₃, hw₃m, hxw₃, hwl⟩

theorem stmt7_3_two (hI : Sec7Inputs) (hJ : HypJ4 G z) {g : G} {x : G ⧸ c.G1}
    {π : G ⧸ c.G3} {m : G ⧸ c.G2} (hg : g • c.x0 = x) (hxπ : c.OnP x π) (hmπ : c.LnP m π)
    (hxm : ¬ c.OnL x m) (h5 : ∀ w, c.OnL w m → c.Delta.Adj x w) :
    ∃ D ∈ M24G.spreadsOf (ρ.sext (g⁻¹ • π)), ∀ n, c.OnL x n →
      ((∃ w, c.OnL w m ∧ c.OnL w n) ↔ ρ.trio (g⁻¹ • n) ∈ D) := by
  obtain ⟨ℓ, hℓ⟩ := ρ.exists_lines_at hI hJ hg hxπ hmπ
  have hfin : {w | c.OnL w m}.Finite := Set.finite_of_ncard_pos (by rw [c.ncard_onL]; omega)
  have hinj : Set.InjOn (fun w => ρ.trio (g⁻¹ • ℓ w)) ↑hfin.toFinset := by
    intro w hw w' hw' h
    have hwm : c.OnL w m := hfin.mem_toFinset.1 hw
    have hw'm : c.OnL w' m := hfin.mem_toFinset.1 hw'
    by_contra hne
    obtain ⟨hxl, hwl, -⟩ := hℓ w hwm (h5 w hwm)
    obtain ⟨hxl', hwl', -⟩ := hℓ w' hw'm (h5 w' hw'm)
    have hl : ℓ w = ℓ w' := ρ.eq_of_trio_at hg hxl hxl' h
    have hvn : c.OnL w' (ℓ w) := by rw [hl]; exact hwl'
    exact c.not_onL_of_two_pts hI.lineU hJ hxm hwm hw'm hne hwl hvn hxl
  refine ⟨hfin.toFinset.image fun w => ρ.trio (g⁻¹ • ℓ w), ?_, fun n hxn => ?_⟩
  · rw [M24G.mem_spreadsOf]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Finset.card_image_of_injOn hinj, ← Set.ncard_eq_toFinset_card _ hfin, c.ncard_onL]
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk
      have hwm : c.OnL w m := hfin.mem_toFinset.1 hw
      obtain ⟨hxl, hwl, -, hmem, -⟩ := hℓ w hwm (h5 w hwm)
      obtain ⟨hk1, hk2⟩ := M24G.mem_triosOf.1 hmem
      refine ⟨hk1, hk2, fun k' hk' hne => ?_⟩
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hk'
      have hw'm : c.OnL w' m := hfin.mem_toFinset.1 hw'
      obtain ⟨hxl', hwl', -⟩ := hℓ w' hw'm (h5 w' hw'm)
      have hne' : w ≠ w' := fun h => hne (by rw [h])
      have h2 := ρ.mem_deltaAt_two_of_adj hI hJ hxπ hmπ hxm h5 hwm hw'm hne' hxl hwl hxl' hwl'
      exact ((ρ.mem_deltaAt_two_iff_at hg hxl hxl').1 h2).1.symm
  · constructor
    · rintro ⟨w, hwm, hwn⟩
      obtain ⟨-, -, -, -, huniq⟩ := hℓ w hwm (h5 w hwm)
      refine Finset.mem_image.2 ⟨w, hfin.mem_toFinset.2 hwm, ?_⟩
      rw [huniq n hxn hwn]
    · intro hn
      obtain ⟨w, hw, hwn⟩ := Finset.mem_image.1 hn
      have hwm : c.OnL w m := hfin.mem_toFinset.1 hw
      obtain ⟨hxl, hwl, -⟩ := hℓ w hwm (h5 w hwm)
      obtain rfl := ρ.eq_of_trio_at hg hxl hxn hwn
      exact ⟨w, hwm, hwl⟩

end ResM24

end CFSG.Quasithin.H13.AS91
