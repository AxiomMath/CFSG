module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type*} [Group G]

abbrev cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g : G} {H : Subgroup G} {x : G} : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem conj_mem_cj {g : G} {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  ⟨x, hx, rfl⟩

theorem cj_mul (g h : G) (H : Subgroup G) : cj (g * h) H = cj g (cj h H) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext x
  simp

theorem cj_inv_cj (g : G) (H : Subgroup G) : cj g⁻¹ (cj g H) = H := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_mono {g : G} {H K : Subgroup G} (h : H ≤ K) : cj g H ≤ cj g K :=
  Subgroup.map_mono h

theorem cj_le_iff {g : G} {H K : Subgroup G} : cj g H ≤ cj g K ↔ H ≤ K := by
  constructor
  · intro h
    have := cj_mono (g := g⁻¹) h
    rwa [cj_inv_cj, cj_inv_cj] at this
  · exact cj_mono

theorem cj_inf (g : G) (H K : Subgroup G) : cj g (H ⊓ K) = cj g H ⊓ cj g K :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem cj_sup (g : G) (H K : Subgroup G) : cj g (H ⊔ K) = cj g H ⊔ cj g K :=
  Subgroup.map_sup _ _ _

theorem cj_bot (g : G) : cj g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem cj_eq_bot_iff {g : G} {H : Subgroup G} : cj g H = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective

theorem cj_normalizer (g : G) (H : Subgroup G) :
    cj g (Subgroup.normalizer (H : Set G)) = Subgroup.normalizer ((cj g H : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)

theorem cj_centralizer (g : G) (H : Subgroup G) :
    cj g (Subgroup.centralizer (H : Set G)) =
      Subgroup.centralizer ((cj g H : Subgroup G) : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [SetLike.mem_coe, mem_cj] at hy
    have := hx _ hy
    calc y * x = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group
  · intro hx y hy
    have := hx (g * y * g⁻¹) (conj_mem_cj hy)
    calc y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * y := by group

theorem cj_centralizer_singleton (g x : G) :
    cj g (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  rw [mem_cj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group

theorem card_cj [Finite G] (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cj_eq_self_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cj g H = H := by
  ext x
  rw [mem_cj]
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g), e]

theorem cj_eq_self_of_mem {g : G} {H : Subgroup G} (hg : g ∈ H) : cj g H = H :=
  cj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)

theorem isCyclic_cj {g : G} {H : Subgroup G} (hH : IsCyclic H) : IsCyclic (cj g H) :=
  isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap H)
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective H)

theorem comm_cj {g : G} {H : Subgroup G} (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    ∀ a ∈ cj g H, ∀ b ∈ cj g H, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hH a ha b hb]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem relIndex_cj [Finite G] {g : G} {H L : Subgroup G} (hg : g ∈ L) :
    (cj g H).relIndex L = H.relIndex L := by
  have h1 := Subgroup.relIndex_mul_card (H := cj g H) (K := L)
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := L)
  have h3 : cj g H ⊓ L = cj g (H ⊓ L) := by rw [cj_inf, cj_eq_self_of_mem hg]
  rw [h3, card_cj] at h1
  have hpos : 0 < Nat.card ↥(H ⊓ L) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

variable [Finite G]

theorem exists_conj_of_sylowIn {r : ℕ} [Fact r.Prime] {L P Q : Subgroup G} (hPL : P ≤ L)
    (hQL : Q ≤ L) (hPc : Nat.card P = r ^ (Nat.card L).factorization r)
    (hQc : Nat.card Q = r ^ (Nat.card L).factorization r) : ∃ ℓ ∈ L, Q = cj ℓ P := by
  have hP' : Nat.card (P.subgroupOf L) = r ^ (Nat.card L).factorization r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hPc]
  have hQ' : Nat.card (Q.subgroupOf L) = r ^ (Nat.card L).factorization r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv, hQc]
  obtain ⟨ℓ, hℓ⟩ := MulAction.exists_smul_eq L (Sylow.ofCard (P.subgroupOf L) hP')
    (Sylow.ofCard (Q.subgroupOf L) hQ')
  refine ⟨ℓ, ℓ.2, ?_⟩
  ext x
  rw [mem_cj]
  constructor
  · intro hx
    have hxQ : (⟨x, hQL hx⟩ : L) ∈ ((Sylow.ofCard (Q.subgroupOf L) hQ' : Sylow r L) :
        Subgroup L) := hx
    rw [← hℓ, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have h2 := Subgroup.mem_subgroupOf.mp hxQ
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h2
  · intro hx
    have hxL : x ∈ L := by
      have h1 := hPL hx
      have h2 : x = (ℓ : G) * ((ℓ : G)⁻¹ * x * ℓ) * (ℓ : G)⁻¹ := by group
      rw [h2]
      exact L.mul_mem (L.mul_mem ℓ.2 h1) (L.inv_mem ℓ.2)
    have hmem : (⟨x, hxL⟩ : L) ∈ ((Sylow.ofCard (Q.subgroupOf L) hQ' : Sylow r L) :
        Subgroup L) := by
      rw [← hℓ, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      show ((MulAut.conj ℓ)⁻¹ • (⟨x, hxL⟩ : L) : L) ∈ P.subgroupOf L
      rw [Subgroup.mem_subgroupOf]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hx
    exact hmem

theorem exists_mul_mem_normalizer_of_sylowIn {r : ℕ} [Fact r.Prime] {L P : Subgroup G}
    (hPL : P ≤ L) (hPc : Nat.card P = r ^ (Nat.card L).factorization r)
    {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    ∃ ℓ ∈ L, ℓ * m ∈ Subgroup.normalizer (P : Set G) := by
  have hQL : cj m P ≤ L := by
    rw [← cj_eq_self_of_mem_normalizer hm]
    exact cj_mono hPL
  obtain ⟨ℓ, hℓL, hℓ⟩ := exists_conj_of_sylowIn hPL hQL hPc (by rw [card_cj, hPc])
  refine ⟨ℓ⁻¹, L.inv_mem hℓL, ?_⟩
  have h : cj (ℓ⁻¹ * m) P = P := by rw [cj_mul, hℓ, ← cj_mul, inv_mul_cancel, cj_one]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (ℓ⁻¹ * m) * x * (ℓ⁻¹ * m)⁻¹ ∈ cj (ℓ⁻¹ * m) P := conj_mem_cj hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_cj] at hx
    simpa [mul_assoc] using hx

omit [Finite G] in
theorem exists_complement_in {C N : Subgroup G} (hCN : C ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (C : Set G)) (hcop : Nat.Coprime (Nat.card C) (C.relIndex N)) :
    ∃ W : Subgroup G, W ≤ N ∧ C ⊓ W = ⊥ ∧ C ⊔ W = N ∧ Nat.card C * Nat.card W = Nat.card N := by
  set C' := C.subgroupOf N
  have : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hnorm
  have hcop' : Nat.Coprime (Nat.card C') C'.index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
    exact hcop
  obtain ⟨W', hW'⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hC : C = C'.map N.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCN]
  refine ⟨W'.map N.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have h := hW'.disjoint.eq_bot
    rw [hC, ← Subgroup.map_inf_eq _ _ _ N.subtype_injective, h, Subgroup.map_bot]
  · have h := hW'.sup_eq_top
    rw [hC, ← Subgroup.map_sup, h, Subgroup.map_top, Subgroup.range_subtype]
  · rw [Subgroup.card_map_of_injective N.subtype_injective, ← hW'.card_mul_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]

theorem exists_conj_complement_in {C N W₁ W₂ : Subgroup G} (hCN : C ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (C : Set G)) (hcop : Nat.Coprime (Nat.card C) (C.relIndex N))
    (hW₁N : W₁ ≤ N) (hW₂N : W₂ ≤ N) (h₁i : C ⊓ W₁ = ⊥) (h₁s : C ⊔ W₁ = N) (h₂i : C ⊓ W₂ = ⊥)
    (h₂s : C ⊔ W₂ = N) : ∃ c ∈ C, W₂ = cj c W₁ := by
  set C' := C.subgroupOf N
  have : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hnorm
  have hcop' : Nat.Coprime (Nat.card C') C'.index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
    exact hcop
  have hcompl : ∀ W : Subgroup G, W ≤ N → C ⊓ W = ⊥ → C ⊔ W = N →
      Subgroup.IsComplement' C' (W.subgroupOf N) := by
    intro W hWN hi hs
    have hC : C'.map N.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCN]
    have hW : (W.subgroupOf N).map N.subtype = W := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWN]
    have hdisj : Disjoint C' (W.subgroupOf N) := by
      rw [disjoint_iff]
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_inf_eq _ _ _ N.subtype_injective, hC, hW, hi, Subgroup.map_bot]
    have hsup : C' ⊔ W.subgroupOf N = ⊤ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_sup, hC, hW, hs, Subgroup.map_top, Subgroup.range_subtype]
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [← Subgroup.normal_mul, hsup]
    rfl
  obtain ⟨c, hc⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    C' (W₁.subgroupOf N) (W₂.subgroupOf N) inferInstance (hcompl W₁ hW₁N h₁i h₁s)
    (hcompl W₂ hW₂N h₂i h₂s) hcop'
  refine ⟨((c : N) : G), c.2, ?_⟩
  have h := congrArg (fun H : Subgroup N => H.map N.subtype) hc
  simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW₂N] at h
  rw [h, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hW₁N hy⟩, hy, by simp⟩

omit [Finite G] in
theorem eq_of_mem_of_cyclic_of_orderOf_two [Finite G] {W : Subgroup G} (hW : IsCyclic W)
    {a b : G} (ha : a ∈ W) (hb : b ∈ W) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  have := Fintype.ofFinite W
  classical
  have hle := IsCyclic.card_pow_eq_one_le (α := W) (n := 2) (by norm_num)
  by_contra hab
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset W) ⊆ Finset.univ.filter fun x : W => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · apply Subtype.ext
      have := pow_orderOf_eq_one a
      rw [ha2] at this
      simpa using this
    · apply Subtype.ext
      have := pow_orderOf_eq_one b
      rw [hb2] at this
      simpa using this
  have hcard : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset W).card = 3 := by
    have ha1 : (1 : W) ≠ ⟨a, ha⟩ := fun h => by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      rw [← this, orderOf_one] at ha2
      exact absurd ha2 (by norm_num)
    have hb1 : (1 : W) ≠ ⟨b, hb⟩ := fun h => by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      rw [← this, orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    have hab' : (⟨a, ha⟩ : W) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    rw [Finset.card_insert_of_notMem (by simp [ha1, hb1]), Finset.card_pair hab']
  have := (Finset.card_le_card hsub).trans hle
  omega

end Sec6

end CFSG.Walter.W67
