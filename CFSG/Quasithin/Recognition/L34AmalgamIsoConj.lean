module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoFactor
public import Certificates.Certificate7080

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem crd_presF : ∀ x : Fin 16, presF (tab (crd x)) = true :=
  Certificates.certificate7080.1

theorem fix_A1 :
    ∀ y : Fin 22, y ≠ 0 → y ≠ 1 → ∃ x : Fin 16, (tab (crd x)).getD y.val 0 ≠ y :=
  Certificates.certificate7080.2.1

theorem fix_A2 : ∀ y : Fin 22, y ∉ m22HexadL →
    ∃ s ∈ a2W, (wtab genTL genTiL s).getD y.val 0 ≠ y :=
  Certificates.certificate7080.2.2.1

theorem count_A1_A2 :
    (Finset.univ.filter fun x : Fin 16 => fixesF (tab (crd x)) = true).card = 4 :=
  Certificates.certificate7080.2.2.2

theorem barA1_le_ptHex :
    barA1 ≤ m22PtHexStab := by
  rintro _ ⟨x, rfl⟩
  rw [mem_ptHex_iff_tab, show (0 : ℕ) = (0 : Fin 22).val from rfl, tab_getD]
  exact ⟨(crd_facts x).1, crd_presF x⟩

theorem mem_barA2_of_a2W {s : String} (hs : s ∈ a2W) :
    evalW gen (word s) ∈ barA2 := by
  have h := a2_ok
  simp only [a2Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rw [← fixesF_tab, ← wtab_eq]
  exact (h.2 s hs).2

theorem card_barA1_inf_barA2 :
    Nat.card ↥(barA1 ⊓ barA2) = 4 := by
  classical
  let f : {x : Fin 16 // fixesF (tab (crd x)) = true} → ↥(barA1 ⊓ barA2) := fun x =>
    ⟨crd x.1, Subgroup.mem_inf.mpr ⟨⟨x.1, rfl⟩, fixesF_tab.mp x.2⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (crd_injective (congrArg Subtype.val hxy)), fun g => ?_⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp g.2
    obtain ⟨x, hx⟩ := h1
    exact ⟨⟨x, by rw [fixesF_tab, hx]; exact h2⟩, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_subtype,
    count_A1_A2]

theorem card_sup_mul_card_inf_of_le_normalizer' {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_barA1_sup_barA2 :
    Nat.card ↥(barA1 ⊔ barA2) = 64 := by
  have hle : barA1 ≤ Subgroup.normalizer (barA2 : Set M22) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact conj_mem_barA2 (barA1_le_ptHex hg) he
    · intro he
      have := conj_mem_barA2 (m22PtHexStab.inv_mem (barA1_le_ptHex hg)) he
      rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at this
  have h := card_sup_mul_card_inf_of_le_normalizer' hle
  rw [card_barA1_inf_barA2, card_barA1, card_barA2] at h
  omega

theorem le_or_le_of_subset_union {G : Type*} [Group G] {K A B : Subgroup G}
    (h : ∀ x ∈ K, x ∈ A ∨ x ∈ B) : K ≤ A ∨ K ≤ B := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨x, hxK, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hc.1
  obtain ⟨y, hyK, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hc.2
  have hxB := (h x hxK).resolve_left hxA
  have hyA := (h y hyK).resolve_right hyB
  rcases h (x * y) (K.mul_mem hxK hyK) with hA | hB
  · exact hxA (by simpa using A.mul_mem hA (A.inv_mem hyA))
  · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) hB)

theorem eq_A1_or_A2
    {K : Subgroup M22} (hK : K ≤ barB) (h2 : ∀ x ∈ K, x * x = 1)
    (hc : Nat.card K = 16) : K = barA1 ∨ K = barA2 := by
  rcases le_or_le_of_subset_union (K := K) (A := barA1) (B := barA2)
    (fun x hx => mem_A1_or_A2 (hK hx) (h2 x hx)) with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [card_barA1, hc]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [card_barA2, hc]))

theorem mem_ptHex_of_normalizes
    {n : M22} (hn : n ∈ m22TwoStab)
    (hN : ∀ e ∈ barA2, n⁻¹ * e * n ∈ barA2) : n ∈ m22PtHexStab := by
  rw [M22Witt.mem_m22PtHexStab_iff]
  refine ⟨(mem_m22TwoStab_iff.mp hn).1, fun y hy => ?_⟩
  by_contra hny
  obtain ⟨s, hs, hne⟩ := fix_A2 _ hny
  have h1 := hN _ (mem_barA2_of_a2W hs) y hy
  apply hne
  rw [wtab_eq, tab_getD]
  have h1' : ((n : Equiv.Perm (Fin 22)))⁻¹
      (((evalW gen (word s) : M22) : Equiv.Perm (Fin 22)) ((n : Equiv.Perm (Fin 22)) y)) = y := by
    have := h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply] at this
    exact this
  exact Equiv.Perm.inv_eq_iff_eq.mp h1'

theorem mem_two_of_normalizes
    {n : M22} (hn : n ∈ m22PtHexStab)
    (hN : ∀ e ∈ barA1, n⁻¹ * e * n ∈ barA1) : n ∈ m22TwoStab := by
  have h0 := (M22Witt.mem_m22PtHexStab_iff.mp hn).1
  rw [mem_m22TwoStab_iff]
  refine ⟨h0, ?_⟩
  by_contra h1
  have hn0 : (n : Equiv.Perm (Fin 22)) 1 ≠ 0 := fun h => by
    rw [← h0] at h
    exact absurd ((n : Equiv.Perm (Fin 22)).injective h) (by decide)
  obtain ⟨x, hx⟩ := fix_A1 _ hn0 h1
  have h := hN (crd x) ⟨x, rfl⟩
  have hfix := (mem_m22TwoStab_iff.mp (barA1_le_two h)).2
  apply hx
  rw [tab_getD]
  have h1' : ((n : Equiv.Perm (Fin 22)))⁻¹
      ((crd x : Equiv.Perm (Fin 22)) ((n : Equiv.Perm (Fin 22)) 1)) = 1 := by
    have := hfix
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply] at this
    exact this
  exact Equiv.Perm.inv_eq_iff_eq.mp h1'

theorem mem_smul_sylow {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g x : G} :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

abbrev bS1 : Subgroup ↥m22TwoStab :=
  (barA1 ⊔ barA2).subgroupOf m22TwoStab

abbrev bS2 : Subgroup ↥m22PtHexStab :=
  (barA1 ⊔ barA2).subgroupOf m22PtHexStab

theorem card_bS1 :
    Nat.card bS1 = 64 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (sup_le barA1_le_two barA2_le_two)).toEquiv, card_barA1_sup_barA2]

theorem card_bS2 :
    Nat.card bS2 = 64 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (sup_le barA1_le_ptHex barA2_le)).toEquiv, card_barA1_sup_barA2]

theorem exists_conj_P1
    {H F : Subgroup ↥m22TwoStab} (hH : Nat.card H = 192)
    (hFn : ∀ h ∈ H, ∀ f ∈ F, h * f * h⁻¹ ∈ F) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFc : Nat.card F = 16) (hFA : F ≠ barA1') :
    ∃ g : ↥m22TwoStab, (∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ bB1) ∧
      ∀ x, x ∈ F ↔ g⁻¹ * x * g ∈ barA2.subgroupOf m22TwoStab := by
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 4) (by rw [hFc]; norm_num)
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  have hS0p : IsPGroup 2 bS1 := IsPGroup.of_card (n := 6) (by rw [card_bS1]; norm_num)
  have hS0i : ¬ 2 ∣ bS1.index := by
    have h := bS1.card_mul_index
    rw [card_bS1, card_m22TwoStab] at h
    have h15 : bS1.index = 15 := by omega
    rw [h15]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥m22TwoStab (hS0p.toSylow hS0i) S
  have hmem : ∀ x ∈ F, ((g⁻¹ * x * g : ↥m22TwoStab) : M22) ∈ barA1 ⊔ barA2 := by
    intro x hx
    have h := hFS hx
    rw [← hg, mem_smul_sylow] at h
    exact h
  set K : Subgroup M22 := (F.map (MulAut.conj g⁻¹).toMonoidHom).map m22TwoStab.subtype with hK
  have hKmem : ∀ y : M22, y ∈ K ↔ ∃ x ∈ F, ((g⁻¹ * x * g : ↥m22TwoStab) : M22) = y := by
    intro y
    simp only [hK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hKB : K ≤ barB := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hKmem y).mp hy
    have h := hmem x hx
    exact ⟨(g⁻¹ * x * g).2, (sup_le barA1_le_ptHex barA2_le) h⟩
  have hK2 : ∀ y ∈ K, y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hKmem y).mp hy
    rw [← Subgroup.coe_mul, show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group,
      hF2 x hx]
    simp
  have hKc : Nat.card K = 16 := by
    rw [hK, Subgroup.card_map_of_injective m22TwoStab.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hFc]
  have hKA2 : K = barA2 := by
    rcases eq_A1_or_A2 hKB hK2 hKc with h | h
    · exfalso
      apply hFA
      ext x
      constructor
      · intro hx
        have h1 : ((g⁻¹ * x * g : ↥m22TwoStab) : M22) ∈ barA1 := h ▸ (hKmem _).mpr ⟨x, hx, rfl⟩
        have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ barA1' :=
          barA1'_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr h1) g
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2
      · intro hx
        have hx' : g⁻¹ * x * g ∈ barA1' := barA1'_normal.conj_mem _ hx g⁻¹ |> fun h' => by
          rwa [inv_inv] at h'
        rw [Subgroup.mem_subgroupOf, ← h] at hx'
        obtain ⟨x', hx'F, e⟩ := (hKmem _).mp hx'
        have : x' = x := by
          have e' := Subtype.ext e
          exact mul_left_cancel (mul_right_cancel e')
        rwa [← this]
    · exact h
  refine ⟨g, fun x => ?_, fun x => ?_⟩
  ·
    have hle : ∀ y ∈ H, ((g⁻¹ * y * g : ↥m22TwoStab) : M22) ∈ m22PtHexStab := by
      intro y hy
      refine mem_ptHex_of_normalizes (g⁻¹ * y * g).2 fun e he => ?_
      rw [← hKA2] at he ⊢
      obtain ⟨f, hf, rfl⟩ := (hKmem e).mp he
      refine (hKmem _).mpr ⟨y⁻¹ * f * y, hFn _ (H.inv_mem hy) f hf |> fun h => by
        rwa [inv_inv] at h, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    let φ : ↥H → ↥bB1 := fun y => ⟨g⁻¹ * y * g, hle y y.2⟩
    have hφ : Function.Injective φ := fun y y' e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
    have hbij := hφ.bijective_of_nat_card_le (by rw [hH, card_bB1])
    constructor
    · intro hx
      exact hle x hx
    · intro hx
      obtain ⟨y, hy⟩ := hbij.2 ⟨g⁻¹ * x * g, hx⟩
      have e := congrArg Subtype.val hy
      have : (y : ↥m22TwoStab) = x := mul_left_cancel (mul_right_cancel e)
      rw [← this]
      exact y.2
  · rw [Subgroup.mem_subgroupOf, ← hKA2]
    constructor
    · intro hx
      exact (hKmem _).mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨x', hx'F, e⟩ := (hKmem _).mp hx
      have : x' = x := mul_left_cancel (mul_right_cancel (Subtype.ext e))
      rwa [← this]

theorem exists_conj_P2
    {H F : Subgroup ↥m22PtHexStab} (hH : Nat.card H = 192)
    (hFn : ∀ h ∈ H, ∀ f ∈ F, h * f * h⁻¹ ∈ F) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFc : Nat.card F = 16) (hFA : F ≠ barA2') :
    ∃ g : ↥m22PtHexStab, (∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ bB2) ∧
      ∀ x, x ∈ F ↔ g⁻¹ * x * g ∈ barA1.subgroupOf m22PtHexStab := by
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 4) (by rw [hFc]; norm_num)
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  have hS0p : IsPGroup 2 bS2 := IsPGroup.of_card (n := 6) (by rw [card_bS2]; norm_num)
  have hS0i : ¬ 2 ∣ bS2.index := by
    have h := bS2.card_mul_index
    rw [card_bS2, M22Witt.card_m22PtHexStab] at h
    have h15 : bS2.index = 15 := by omega
    rw [h15]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥m22PtHexStab (hS0p.toSylow hS0i) S
  have hmem : ∀ x ∈ F, ((g⁻¹ * x * g : ↥m22PtHexStab) : M22) ∈ barA1 ⊔ barA2 := by
    intro x hx
    have h := hFS hx
    rw [← hg, mem_smul_sylow] at h
    exact h
  set K : Subgroup M22 := (F.map (MulAut.conj g⁻¹).toMonoidHom).map m22PtHexStab.subtype
    with hK
  have hKmem : ∀ y : M22, y ∈ K ↔ ∃ x ∈ F, ((g⁻¹ * x * g : ↥m22PtHexStab) : M22) = y := by
    intro y
    simp only [hK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hKB : K ≤ barB := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hKmem y).mp hy
    have h := hmem x hx
    exact ⟨(sup_le barA1_le_two barA2_le_two) h, (g⁻¹ * x * g).2⟩
  have hK2 : ∀ y ∈ K, y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hKmem y).mp hy
    rw [← Subgroup.coe_mul, show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group,
      hF2 x hx]
    simp
  have hKc : Nat.card K = 16 := by
    rw [hK, Subgroup.card_map_of_injective m22PtHexStab.subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hFc]
  have hKA1 : K = barA1 := by
    rcases eq_A1_or_A2 hKB hK2 hKc with h | h
    · exact h
    · exfalso
      apply hFA
      ext x
      constructor
      · intro hx
        have h1 : ((g⁻¹ * x * g : ↥m22PtHexStab) : M22) ∈ barA2 := h ▸ (hKmem _).mpr ⟨x, hx, rfl⟩
        have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ barA2' :=
          barA2'_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr h1) g
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2
      · intro hx
        have hx' : g⁻¹ * x * g ∈ barA2' := barA2'_normal.conj_mem _ hx g⁻¹ |> fun h' => by
          rwa [inv_inv] at h'
        rw [Subgroup.mem_subgroupOf, ← h] at hx'
        obtain ⟨x', hx'F, e⟩ := (hKmem _).mp hx'
        have : x' = x := by
          have e' := Subtype.ext e
          exact mul_left_cancel (mul_right_cancel e')
        rwa [← this]
  refine ⟨g, fun x => ?_, fun x => ?_⟩
  · have hle : ∀ y ∈ H, ((g⁻¹ * y * g : ↥m22PtHexStab) : M22) ∈ m22TwoStab := by
      intro y hy
      refine mem_two_of_normalizes (g⁻¹ * y * g).2 fun e he => ?_
      rw [← hKA1] at he ⊢
      obtain ⟨f, hf, rfl⟩ := (hKmem e).mp he
      refine (hKmem _).mpr ⟨y⁻¹ * f * y, hFn _ (H.inv_mem hy) f hf |> fun h => by
        rwa [inv_inv] at h, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    let φ : ↥H → ↥bB2 := fun y => ⟨g⁻¹ * y * g, hle y y.2⟩
    have hφ : Function.Injective φ := fun y y' e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
    have hbij := hφ.bijective_of_nat_card_le (by rw [hH, card_bB2])
    constructor
    · intro hx
      exact hle x hx
    · intro hx
      obtain ⟨y, hy⟩ := hbij.2 ⟨g⁻¹ * x * g, hx⟩
      have e := congrArg Subtype.val hy
      have : (y : ↥m22PtHexStab) = x := mul_left_cancel (mul_right_cancel e)
      rw [← this]
      exact y.2
  · rw [Subgroup.mem_subgroupOf, ← hKA1]
    constructor
    · intro hx
      exact (hKmem _).mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨x', hx'F, e⟩ := (hKmem _).mp hx
      have : x' = x := mul_left_cancel (mul_right_cancel (Subtype.ext e))
      rwa [← this]

end CFSG.Quasithin.L34Amalgam
