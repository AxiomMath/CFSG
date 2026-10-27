module

public import CFSG.Timmesfeld.LocalTwoSubgroups.Omega

public section


namespace CFSG.Timmesfeld.LocalTwoSubgroups


open Subgroup


namespace FrobeniusFixedSpaceBounds


@[to_additive]
theorem card_sup_mul_card_inf {G : Type*} [Group G] (H N : Subgroup G)
    (h : ∀ b ∈ H, ∀ n ∈ N, b * n * b⁻¹ ∈ N) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) = Nat.card H * Nat.card N := by
  have hLE : H ≤ normalizer N := fun b hb => by
    rw [mem_normalizer_iff]; intro n; constructor
    · intro hn; exact h b hb n hn
    · intro hn
      have := h b⁻¹ (inv_mem hb) _ hn
      simpa [mul_assoc] using this
  have h1 : N.relIndex (H ⊔ N) = N.relIndex H := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    unfold relIndex index
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE).toEquiv.symm
  have e1 := relIndex_mul_card (H := N) (K := H ⊔ N)
  have e2 := relIndex_mul_card (H := N) (K := H)
  rw [inf_of_le_left (le_sup_right : N ≤ H ⊔ N)] at e1
  rw [h1] at e1
  rw [inf_comm]
  rw [← e1, ← e2]
  ring


section

variable {F V : Type} [Group F] [AddCommGroup V] [DistribMulAction F V]


def fixSub (B : Subgroup F) : AddSubgroup V where
  carrier := {v | ∀ a ∈ B, a • v = v}
  zero_mem' := by intro a _; simp
  add_mem' := by
    intro x y hx hy a ha
    simp [smul_add, hx a ha, hy a ha]
  neg_mem' := by
    intro x hx a ha
    simp [smul_neg, hx a ha]


theorem fixSub_anti {B B' : Subgroup F} (h : B ≤ B') : fixSub (V := V) B' ≤ fixSub B :=
  fun _ hv a ha => hv a (h ha)


theorem fixSub_sup (B B' : Subgroup F) :
    fixSub (V := V) B ⊓ fixSub B' ≤ fixSub (B ⊔ B') := by
  intro v hv
  have hle : B ⊔ B' ≤ MulAction.stabilizer F v :=
    sup_le (fun a ha => hv.1 a ha) (fun a ha => hv.2 a ha)
  exact fun a ha => hle ha


noncomputable def val (V : Type) [AddCommGroup V] [DistribMulAction F V] (B : Subgroup F) : ℕ :=
  Nat.card B * Nat.card (fixSub (V := V) B)


def cj (k : F) (B : Subgroup F) : Subgroup F := B.map (MulAut.conj k).toMonoidHom


theorem mem_cj {k : F} {B : Subgroup F} {y : F} : y ∈ cj k B ↔ ∃ x ∈ B, k * x * k⁻¹ = y := by
  simp [cj, mem_map]


theorem cj_cj (k k' : F) (B : Subgroup F) : cj k (cj k' B) = cj (k * k') B := by
  ext y
  simp only [mem_cj]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by group⟩


theorem cj_sup (k : F) (B C : Subgroup F) : cj k (B ⊔ C) = cj k B ⊔ cj k C := map_sup _ _ _


theorem card_cj [Finite F] (k : F) (B : Subgroup F) : Nat.card (cj k B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj k).injective


theorem card_fixSub_cj (k : F) (B : Subgroup F) :
    Nat.card (fixSub (V := V) (cj k B)) = Nat.card (fixSub (V := V) B) := by
  refine Nat.card_congr ((MulAction.toPerm k : Equiv.Perm V).subtypeEquiv ?_).symm
  intro v
  show (∀ a ∈ B, a • v = v) ↔ (∀ a ∈ cj k B, a • (k • v) = k • v)
  constructor
  · intro h a ha
    obtain ⟨x, hx, rfl⟩ := mem_cj.1 ha
    have : k * x * k⁻¹ * k = k * x := by group
    rw [← mul_smul, this, mul_smul, h x hx]
  · intro h a ha
    have := h (k * a * k⁻¹) (mem_cj.2 ⟨a, ha, rfl⟩)
    have e : k * a * k⁻¹ * k = k * a := by group
    rw [← mul_smul, e, mul_smul] at this
    exact MulAction.injective k this


end


theorem regular {F : Type} [Group F] [Finite F] {L K : Subgroup F} {n : ℕ} (hLnormal : L.Normal)
    (hfrob : ∀ k ∈ K, k ≠ 1 → ∀ l ∈ L, l ≠ 1 → k * l ≠ l * k)
    (hL : Nat.card L = 2 ^ n) (hK : Nat.card K = 2 ^ n - 1) :
    ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ K, k * x * k⁻¹ = y := by
  intro x hx hx1 y hy hy1
  let f : K → {z : L // z ≠ 1} := fun k =>
    ⟨⟨(k : F) * x * (k : F)⁻¹, hLnormal.conj_mem x hx k⟩, by
      intro h
      apply hx1
      have := congrArg Subtype.val h
      simpa using this⟩
  have hinj : Function.Injective f := by
    intro k k' h
    have h' : (k : F) * x * (k : F)⁻¹ = (k' : F) * x * (k' : F)⁻¹ := by
      have := congrArg (fun z => (z.1 : F)) h
      simpa [f] using this
    by_contra hne
    have hne' : ((k' : F)⁻¹ * k) ≠ 1 := by
      intro h1
      apply hne
      have : (k : F) = k' := by
        have := congrArg ((k' : F) * ·) h1
        simpa using this
      exact Subtype.ext this
    apply hfrob ((k' : F)⁻¹ * k) (mul_mem (inv_mem k'.2) k.2) hne' x hx hx1
    calc (k' : F)⁻¹ * k * x = (k' : F)⁻¹ * (k * x * (k : F)⁻¹) * k := by group
      _ = (k' : F)⁻¹ * (k' * x * (k' : F)⁻¹) * k := by rw [h']
      _ = x * ((k' : F)⁻¹ * k) := by group
  have hcard : Nat.card {z : L // z ≠ 1} = Nat.card K := by
    classical
    have := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card, hL, hK]
    simp
  have hbij := hinj.bijective_of_nat_card_le (le_of_eq hcard)
  obtain ⟨k, hk⟩ := hbij.2 ⟨⟨y, hy⟩, by intro h; apply hy1; simpa using congrArg Subtype.val h⟩
  refine ⟨k, k.2, ?_⟩
  have := congrArg (fun z => (z.1 : F)) hk
  simpa [f] using this


theorem Lcomm {F : Type} [Group F] [Finite F] {L K : Subgroup F} {n : ℕ} (hn : 1 ≤ n)
    (hL : Nat.card L = 2 ^ n)
    (hreg : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ K, k * x * k⁻¹ = y) :
    ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) 2
    (by rw [hL]; exact dvd_pow_self 2 (by omega))
  have hg1 : (g : F) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    omega
  have hgg : (g : F) * g = 1 := by
    have h2 : g * g = 1 := by rw [← pow_two, ← hg]; exact pow_orderOf_eq_one g
    simpa using congrArg Subtype.val h2
  have sq : ∀ x ∈ L, x * x = 1 := by
    intro x hx
    by_cases h1 : x = 1
    · simp [h1]
    obtain ⟨k, _, hk⟩ := hreg g g.2 hg1 x hx h1
    rw [← hk]
    calc k * (g : F) * k⁻¹ * (k * g * k⁻¹) = k * ((g : F) * g) * k⁻¹ := by group
      _ = 1 := by rw [hgg]; group
  intro x hx y hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (sq x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (sq y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (sq _ (mul_mem hx hy))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hx', hy']



theorem core {F V : Type} [Group F] [Finite F] [AddCommGroup V] [Finite V] [DistribMulAction F V]
    {L K : Subgroup F} (hLnormal : L.Normal) (hLcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hreg : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ K, k * x * k⁻¹ = y)
    {A0 : Subgroup F} (hA0L : A0 ≤ L) (hA0 : A0 ≠ ⊥) (hA : Nat.card V ≤ val V A0) :
    Nat.card V ≤ val V L := by
  classical
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have cjL : ∀ (k : F) (B : Subgroup F), B ≤ L → cj k B ≤ L := by
    intro k B hB y hy
    obtain ⟨x, hx, rfl⟩ := mem_cj.1 hy
    exact hLnormal.conj_mem x (hB hx) k
  have Lsup : ∀ B C : Subgroup F, B ≤ L → C ≤ L →
      Nat.card (B ⊔ C : Subgroup F) * Nat.card (B ⊓ C : Subgroup F) = Nat.card B * Nat.card C := by
    intro B C hB hC
    apply card_sup_mul_card_inf
    intro b hb n hn
    rw [hLcomm b (hB hb) n (hC hn), mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  have Vsup : ∀ X Y : AddSubgroup V, Nat.card X * Nat.card Y ≤ Nat.card (X ⊓ Y : AddSubgroup V) * Nat.card V := by
    intro X Y
    rw [← card_sup_add_card_inf X Y (fun b _ n hn => by simpa using hn), mul_comm]
    exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_card_addGroup _)
  set S : Set (Subgroup F) := {B | B ≤ L ∧ B ≠ ⊥} with hS
  obtain ⟨A1, hA1S, hA1max⟩ := Set.exists_max_image S (val V) (Set.toFinite S) ⟨A0, hA0L, hA0⟩
  obtain ⟨A, ⟨hAS, hAval⟩, hAmin⟩ := Set.exists_min_image
    {B | B ∈ S ∧ val V B = val V A1} (fun B => Nat.card B) (Set.toFinite _) ⟨A1, hA1S, rfl⟩
  obtain ⟨hAL, hA1⟩ := hAS
  have hmax : ∀ B : Subgroup F, B ≤ L → B ≠ ⊥ → val V B ≤ val V A :=
    fun B h1 h2 => hAval ▸ hA1max B ⟨h1, h2⟩
  have hmin : ∀ B : Subgroup F, B ≤ L → B ≠ ⊥ → val V B = val V A → Nat.card A ≤ Nat.card B :=
    fun B h1 h2 h3 => hAmin B ⟨⟨h1, h2⟩, h3.trans hAval⟩
  have hPA : Nat.card V ≤ val V A := hA.trans (hmax A0 hA0L hA0)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcpos : 0 < Nat.card (fixSub (V := V) A) := Nat.card_pos
  have hTI : ∀ k ∈ K, A ⊓ cj k A = ⊥ ∨ A ⊓ cj k A = A := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨hD1, hD2⟩ := hcon
    have hA2L : cj k A ≤ L := cjL k A hAL
    have hcardA2 : Nat.card (cj k A) = Nat.card A := card_cj k A
    have hcA2 : Nat.card (fixSub (V := V) (cj k A)) = Nat.card (fixSub (V := V) A) :=
      card_fixSub_cj k A
    have hDL : A ⊓ cj k A ≤ L := inf_le_left.trans hAL
    have hdA : Nat.card (A ⊓ cj k A : Subgroup F) < Nat.card A := by
      by_contra h
      push Not at h
      exact hD2 (Subgroup.eq_of_le_of_card_ge inf_le_left h)
    have hvD : val V (A ⊓ cj k A) < val V A :=
      lt_of_le_of_ne (hmax _ hDL hD1) (fun h => by have := hmin _ hDL hD1 h; omega)
    have hfix_le : fixSub (V := V) A ⊔ fixSub (cj k A) ≤ fixSub (A ⊓ cj k A) :=
      sup_le (fixSub_anti inf_le_left) (fixSub_anti inf_le_right)
    have hs1 := card_sup_add_card_inf (fixSub (V := V) A) (fixSub (cj k A))
      (fun b _ n hn => by simpa using hn)
    have hs2 : Nat.card (fixSub (V := V) A ⊔ fixSub (cj k A) : AddSubgroup V) ≤
        Nat.card (fixSub (V := V) (A ⊓ cj k A)) := AddSubgroup.card_le_of_le hfix_le
    have hsA : Nat.card (A ⊔ cj k A : Subgroup F) * Nat.card (A ⊓ cj k A : Subgroup F) =
        Nat.card A * Nat.card A := by
      rw [Lsup A _ hAL hA2L, hcardA2]
    have hSne : A ⊔ cj k A ≠ ⊥ := fun h => hA1 (le_bot_iff.1 (h ▸ le_sup_left))
    have hv2 := hmax _ (sup_le hAL hA2L) hSne
    have hfix2 : fixSub (V := V) A ⊓ fixSub (cj k A) ≤ fixSub (A ⊔ cj k A) := fixSub_sup _ _
    have he : Nat.card (fixSub (V := V) A ⊓ fixSub (cj k A) : AddSubgroup V) ≤
        Nat.card (fixSub (V := V) (A ⊔ cj k A)) := AddSubgroup.card_le_of_le hfix2
    unfold val at hvD hv2
    rw [hcA2] at hs1
    generalize Nat.card A = a at *
    generalize Nat.card (A ⊓ cj k A : Subgroup F) = d at *
    generalize Nat.card (A ⊔ cj k A : Subgroup F) = s at *
    generalize Nat.card (fixSub (V := V) A) = c at *
    generalize Nat.card (fixSub (V := V) (A ⊓ cj k A)) = cD at *
    generalize Nat.card (fixSub (V := V) (A ⊔ cj k A)) = cS at *
    generalize Nat.card (fixSub (V := V) A ⊓ fixSub (cj k A) : AddSubgroup V) = e at *
    generalize Nat.card (fixSub (V := V) A ⊔ fixSub (cj k A) : AddSubgroup V) = u at *
    have hepos : 0 < e := by
      by_contra h0
      have : e = 0 := by omega
      subst this
      simp at hs1
      omega
    have hdpos : 0 < d := by
      by_contra h0
      have : d = 0 := by omega
      subst this
      simp at hsA
      omega
    have h1 : c * c ≤ e * cD := by
      calc c * c = u * e := hs1.symm
        _ ≤ cD * e := Nat.mul_le_mul_right _ hs2
        _ = e * cD := by ring
    have h2 : d * c < e * a := by
      have h3 : d * c * c < e * a * c := by
        calc d * c * c = d * (c * c) := by ring
          _ ≤ d * (e * cD) := Nat.mul_le_mul_left _ h1
          _ = e * (d * cD) := by ring
          _ < e * (a * c) := Nat.mul_lt_mul_of_pos_left hvD hepos
          _ = e * a * c := by ring
      exact Nat.lt_of_mul_lt_mul_right h3
    have h4 : a * e ≤ c * d := by
      have h5 : a * a * e ≤ a * c * d := by
        calc a * a * e = s * d * e := by rw [hsA]
          _ = s * e * d := by ring
          _ ≤ s * cS * d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)
          _ ≤ a * c * d := Nat.mul_le_mul_right _ hv2
      have : a * (a * e) ≤ a * (c * d) := by
        calc a * (a * e) = a * a * e := by ring
          _ ≤ a * c * d := h5
          _ = a * (c * d) := by ring
      exact Nat.le_of_mul_le_mul_left this hApos
    nlinarith
  have hTI' : ∀ k ∈ K, ∀ x ∈ A, x ≠ 1 → k * x * k⁻¹ ∈ A → cj k A = A := by
    intro k hk x hx hx1 hkx
    have hmem : k * x * k⁻¹ ∈ A ⊓ cj k A := ⟨hkx, mem_cj.2 ⟨x, hx, rfl⟩⟩
    rcases hTI k hk with h | h
    · rw [h, mem_bot] at hmem
      exact absurd (by simpa using hmem) hx1
    · have hle : A ≤ cj k A := h.symm.le.trans inf_le_right
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])).symm
  have hT : ∀ B : Subgroup F, (∀ k ∈ K, cj k A = A → cj k B ≤ B) →
      ∀ k0 ∈ K, B ⊓ cj k0 A ≠ ⊥ → cj k0 A ≤ B := by
    intro B hB k0 hk0 hne
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hx1 : (x : F) ≠ 1 := fun h => hx (Subtype.ext h)
    have hxB : (x : F) ∈ B := x.2.1
    have hxA' : (x : F) ∈ cj k0 A := x.2.2
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact one_mem _
    have hxL : (x : F) ∈ L := cjL k0 A hAL hxA'
    have hyL : y ∈ L := cjL k0 A hAL hy
    obtain ⟨k', hk', hk'xy⟩ := hreg x hxL hx1 y hyL hy1
    obtain ⟨x0, hx0, hx0e⟩ := mem_cj.1 hxA'
    obtain ⟨y0, hy0, hy0e⟩ := mem_cj.1 hy
    have hc : k0 * k' = k' * k0 := hKcomm k0 hk0 k' hk'
    have e : k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = k' * (k0 * x0 * k0⁻¹) * k'⁻¹ := by
      calc k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = (k0 * k') * x0 * (k0 * k')⁻¹ := by group
        _ = (k' * k0) * x0 * (k' * k0)⁻¹ := by rw [hc]
        _ = _ := by group
    have key : k' * x0 * k'⁻¹ = y0 := by
      have h1 : k0 * (k' * x0 * k'⁻¹) * k0⁻¹ = k0 * y0 * k0⁻¹ := by
        rw [e, hx0e, hk'xy, hy0e]
      have := congrArg (fun z => k0⁻¹ * z * k0) h1
      simpa [mul_assoc] using this
    have hx01 : x0 ≠ 1 := by
      intro h; apply hx1; rw [← hx0e, h]; group
    have hconj : cj k' A = A := hTI' k' hk' x0 hx0 hx01 (key ▸ hy0)
    have := hB k' hk' hconj
    have hy' : y ∈ cj k' B := mem_cj.2 ⟨x, hxB, hk'xy⟩
    exact this hy'
  set T : Set (Subgroup F) := {B | B ≤ L ∧ B ≠ ⊥ ∧ (∀ k ∈ K, cj k A = A → cj k B ≤ B) ∧
      Nat.card V ≤ val V B} with hTdef
  have hAT : A ∈ T := by
    refine ⟨hAL, hA1, ?_, hPA⟩
    intro k _ hk
    rw [hk]
  obtain ⟨B, ⟨hBL, hB1, hBinv, hPB⟩, hBmax⟩ := Set.exists_max_image T (fun B => Nat.card B)
    (Set.toFinite _) ⟨A, hAT⟩
  by_cases hBL' : B = L
  · rw [← hBL']; exact hPB
  exfalso
  obtain ⟨x, hxL, hxB⟩ : ∃ x ∈ L, x ∉ B := by
    by_contra h
    push Not at h
    exact hBL' (le_antisymm hBL h)
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ one_mem _)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have ha1 : (a : F) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨k, hk, hkax⟩ := hreg a (hAL a.2) ha1 x hxL hx1
  have hxA' : x ∈ cj k A := mem_cj.2 ⟨a, a.2, hkax⟩
  have hBA' : B ⊓ cj k A = ⊥ := by
    by_contra hne
    exact hxB (hT B hBinv k hk hne hxA')
  have hA'L : cj k A ≤ L := cjL k A hAL
  have hA'ne : cj k A ≠ ⊥ := fun h => hx1 (by simpa [h] using hxA')
  have hA'inv : ∀ k1 ∈ K, cj k1 A = A → cj k1 (cj k A) ≤ cj k A := by
    intro k1 hk1 hk1A
    apply le_of_eq
    rw [cj_cj, hKcomm k1 hk1 k hk, ← cj_cj, hk1A]
  have hcardA' : Nat.card (cj k A) = Nat.card A := card_cj k A
  have hcfA' : Nat.card (fixSub (V := V) (cj k A)) = Nat.card (fixSub (V := V) A) :=
    card_fixSub_cj k A
  have hsB := Lsup B (cj k A) hBL hA'L
  rw [hBA', Subgroup.card_bot, mul_one] at hsB
  have hfs := Vsup (fixSub (V := V) B) (fixSub (cj k A))
  have hfs2 : fixSub (V := V) B ⊓ fixSub (cj k A) ≤ fixSub (B ⊔ cj k A) := fixSub_sup _ _
  have he := AddSubgroup.card_le_of_le hfs2
  have hmemT : B ⊔ cj k A ∈ T := by
    refine ⟨sup_le hBL hA'L, fun h => hB1 (le_bot_iff.1 (h ▸ le_sup_left)), ?_, ?_⟩
    · intro k1 hk1 hk1A
      rw [cj_sup]
      exact sup_le_sup (hBinv k1 hk1 hk1A) (hA'inv k1 hk1 hk1A)
    · have hvA' : Nat.card V ≤ Nat.card (cj k A) * Nat.card (fixSub (V := V) (cj k A)) := by
        rw [hcardA', hcfA']; exact hPA
      unfold val at hPB ⊢
      rw [hsB]
      generalize Nat.card B = b at *
      generalize Nat.card (cj k A) = a' at *
      generalize Nat.card (fixSub (V := V) B) = fb at *
      generalize Nat.card (fixSub (V := V) (cj k A)) = fa at *
      generalize Nat.card (fixSub (V := V) (B ⊔ cj k A)) = fS at *
      generalize Nat.card (fixSub (V := V) B ⊓ fixSub (cj k A) : AddSubgroup V) = e at *
      generalize Nat.card V = v at *
      have h1 : v * v ≤ (b * a' * e) * v := by
        calc v * v ≤ (b * fb) * (a' * fa) := Nat.mul_le_mul hPB hvA'
          _ = b * a' * (fb * fa) := by ring
          _ ≤ b * a' * (e * v) := Nat.mul_le_mul_left _ hfs
          _ = (b * a' * e) * v := by ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hVpos
      calc v ≤ b * a' * e := h2
        _ ≤ b * a' * fS := Nat.mul_le_mul_left _ he
        _ = b * a' * fS := rfl
  have hlt := hBmax _ hmemT
  have hA2 : 1 < Nat.card (cj k A) := by
    rw [hcardA']; exact (Subgroup.one_lt_card_iff_ne_bot A).2 hA1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  rw [hsB] at hlt
  nlinarith


end FrobeniusFixedSpaceBounds


theorem card_le_mul_card_fixedSpace_of_frobenius_action {F V : Type} [Group F] [Finite F] {L K : Subgroup F} {n : ℕ}
    (hn : 2 ≤ n) (hLnormal : L.Normal) (hLK : L ⊔ K = ⊤) (hdisj : Disjoint L K)
    (hfrob : ∀ k ∈ K, k ≠ 1 → ∀ l ∈ L, l ≠ 1 → k * l ≠ l * k)
    (hKab : IsMulCommutative K)
    (hL : Nat.card L = 2 ^ n) (hK : Nat.card K = 2 ^ n - 1)
    [AddCommGroup V] [Finite V] (hV : ∀ v : V, (2 : ℕ) • v = 0) [DistribMulAction F V]
    {A : Subgroup F} (hAL : A ≤ L) (hA1 : A ≠ ⊥)
    (hA : Nat.card V ≤ Nat.card A * Nat.card {v : V // ∀ a ∈ A, a • v = v}) :
    Nat.card V ≤ Nat.card L * Nat.card {v : V // ∀ a ∈ L, a • v = v} := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hreg := FrobeniusFixedSpaceBounds.regular hLnormal hfrob hL hK
  have hLcomm := FrobeniusFixedSpaceBounds.Lcomm hn1 hL hreg
  have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have := hKab.is_comm.comm (⟨a, ha⟩ : K) ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  exact FrobeniusFixedSpaceBounds.core (V := V) hLnormal hLcomm hKcomm hreg hAL hA1 hA


end CFSG.Timmesfeld.LocalTwoSubgroups

public section


namespace CFSG.Timmesfeld.LocalTwoSubgroups


section FaithfulAbelianActionBounds


open Representation


variable {p : ℕ} [Fact p.Prime]


private lemma card_bound_of_irreducible_action {Q G : Type} [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q] [Nontrivial Q]
    [CommGroup G] [Finite G] (ρ : Representation (ZMod p) G Q) (hρ : Function.Injective ρ)
    (hirr : ∀ S : Subrepresentation ρ, S = ⊥ ∨ S = ⊤) :
    Nat.card G ≤ Nat.card Q - 1 ∧
      (Nat.card G = Nat.card Q - 1 → ∀ x y : Q, x ≠ 0 → y ≠ 0 → ∃! g : G, ρ g x = y) := by
  have free : ∀ g : G, ∀ x : Q, x ≠ 0 → ρ g x = x → g = 1 := by
    intro g x hx hgx
    let S : Subrepresentation ρ :=
      ⟨LinearMap.ker (ρ g - 1), by
        intro h v hv
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
        have : ρ g (ρ h v) = ρ h (ρ g v) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
        rw [this, sub_eq_zero.mp hv] ; simp⟩
    rcases hirr S with h | h
    · have : x ∈ S := by
        show x ∈ LinearMap.ker (ρ g - 1)
        simp [sub_eq_zero, hgx]
      have h' : S.toSubmodule = ⊥ := by rw [h]; rfl
      have this' : x ∈ S.toSubmodule := this
      rw [h'] at this'
      exact absurd ((Submodule.mem_bot _).mp this') hx
    · have : ρ g = 1 := by
        ext v
        have hv : v ∈ S := by rw [h]; trivial
        have hv' : v ∈ LinearMap.ker (ρ g - 1) := hv
        simpa [sub_eq_zero] using hv'
      apply hρ
      rw [this, map_one]
  have hne : ∀ x : Q, x ≠ 0 → ∀ g : G, ρ g x ≠ 0 := by
    intro x hx g h0
    apply hx
    have := congrArg (ρ g⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at this
  have finj : ∀ x : Q, ∀ hx : x ≠ 0,
      Function.Injective (fun g : G => (⟨ρ g x, hne x hx g⟩ : {y : Q // y ≠ 0})) := by
    intro x hx g g' h
    have h1 : ρ g x = ρ g' x := congrArg Subtype.val h
    have : g'⁻¹ * g = 1 := by
      apply free _ x hx
      rw [map_mul, Module.End.mul_apply, h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one]; rfl
    exact (inv_mul_eq_one.mp this).symm
  have hcard : Nat.card {y : Q // y ≠ 0} = Nat.card Q - 1 := by
    classical
    haveI := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  obtain ⟨x, hx⟩ := exists_ne (0 : Q)
  have hle : Nat.card G ≤ Nat.card Q - 1 := hcard ▸ Nat.card_le_card_of_injective _ (finj x hx)
  refine ⟨hle, fun heq x' y hx' hy => ?_⟩
  haveI : Finite {y : Q // y ≠ 0} := inferInstance
  have hb := (finj x' hx').bijective_of_nat_card_le (by rw [hcard, heq])
  obtain ⟨g, hg⟩ := hb.2 ⟨y, hy⟩
  refine ⟨g, congrArg Subtype.val hg, fun g' hg' => ?_⟩
  apply (finj x' hx')
  apply Subtype.ext
  simp only
  exact hg'.trans (congrArg Subtype.val hg).symm



private lemma card_bound_of_faithful_abelian_action : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    [Nontrivial Q], Nat.card Q = n → ∀ (G : Type) [CommGroup G] [Finite G],
    Nat.Coprime p (Nat.card G) → ∀ ρ : Representation (ZMod p) G Q, Function.Injective ρ →
    Nat.card G ≤ Nat.card Q - 1 ∧
      (Nat.card G = Nat.card Q - 1 → ∀ x y : Q, x ≠ 0 → y ≠ 0 → ∃! g : G, ρ g x = y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ _ hn G _ _ hcop ρ hρ
  by_cases h : ∀ S : Subrepresentation ρ, S = ⊥ ∨ S = ⊤
  · exact card_bound_of_irreducible_action ρ hρ h
  push Not at h
  obtain ⟨S, hSb, hSt⟩ := h
  haveI : NeZero (Nat.card G : ZMod p) := ⟨by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.Coprime.eq_one_of_dvd hcop h0
    exact (Fact.out : p.Prime).one_lt.ne' this⟩
  obtain ⟨T, hT⟩ := exists_isCompl S
  have hc : IsCompl S.toSubmodule T.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have := hT.disjoint.eq_bot
      have h2 := congrArg Subrepresentation.toSubmodule this
      exact h2
    · rw [codisjoint_iff]
      have := hT.codisjoint.eq_top
      have h2 := congrArg Subrepresentation.toSubmodule this
      exact h2
  have hTb : T ≠ ⊥ := by
    intro h0
    apply hSt
    have := hT.codisjoint.eq_top
    rw [h0, sup_bot_eq] at this
    exact this
  have hTt : T ≠ ⊤ := by
    intro h0
    apply hSb
    have := hT.disjoint.eq_bot
    rw [h0, inf_top_eq] at this
    exact this
  haveI : Nontrivial S.toSubmodule := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h0; apply hSb; exact Subrepresentation.toSubmodule_injective h0
  haveI : Nontrivial T.toSubmodule := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h0; apply hTb; exact Subrepresentation.toSubmodule_injective h0
  haveI : Finite S.toSubmodule := inferInstance
  have hQ : Nat.card Q = Nat.card S.toSubmodule * Nat.card T.toSubmodule := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hc).toEquiv).symm
  have ha : 2 ≤ Nat.card S.toSubmodule := Finite.one_lt_card
  have hb : 2 ≤ Nat.card T.toSubmodule := Finite.one_lt_card
  set ρS := S.toRepresentation with hρS
  set ρT := T.toRepresentation with hρT
  let G1 : Subgroup G := MonoidHom.ker ρS
  let ρ' : G ⧸ G1 →* Module.End (ZMod p) S.toSubmodule := QuotientGroup.lift G1 ρS le_rfl
  have hρ'inj : Function.Injective ρ' := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | _ a =>
    induction b using QuotientGroup.induction_on with | _ b =>
    have hab' : ρS a = ρS b := hab
    rw [QuotientGroup.eq]
    show ρS (a⁻¹ * b) = 1
    rw [map_mul, ← hab', ← map_mul, inv_mul_cancel, map_one]
  let ρ1 : Representation (ZMod p) G1 T.toSubmodule := ρT.comp G1.subtype
  have triv : ∀ g : G, ρS g = 1 → ρT g = 1 → g = 1 := by
    intro g hS hT'
    apply hρ
    rw [map_one]
    ext x
    have hx : x ∈ S.toSubmodule ⊔ T.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    have e1 : ρ g s = s := by
      have := congrArg (fun f => ((f ⟨s, hs⟩ : S.toSubmodule) : Q)) hS
      exact this
    have e2 : ρ g t = t := by
      have := congrArg (fun f => ((f ⟨t, ht⟩ : T.toSubmodule) : Q)) hT'
      exact this
    simp [map_add, e1, e2]
  have hρ1inj : Function.Injective ρ1 := by
    intro a b hab
    have hab' : ρT a = ρT b := hab
    have h1 : ρT (b.1⁻¹ * a.1 : G) = 1 := by
      rw [map_mul, hab', ← map_mul, inv_mul_cancel, map_one]
    have h2 : ρS (b.1⁻¹ * a.1 : G) = 1 := by
      have ha : ρS a = 1 := a.2
      have hb : ρS b = 1 := b.2
      have hbi : ρS (b.1⁻¹) * ρS b.1 = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rw [hb, mul_one] at hbi
      rw [map_mul, hbi, ha, one_mul]
    have := triv _ h2 h1
    apply Subtype.ext
    exact (inv_mul_eq_one.mp this).symm
  have hdvd1 : Nat.card G1 ∣ Nat.card G := Subgroup.card_subgroup_dvd_card G1
  have hdvd2 : Nat.card (G ⧸ G1) ∣ Nat.card G := Subgroup.card_quotient_dvd_card G1
  have hG : Nat.card G = Nat.card (G ⧸ G1) * Nat.card G1 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup G1]
  have h0 := ih _ (by rw [← hn, hQ]; nlinarith) S.toSubmodule rfl (G ⧸ G1)
    (hcop.coprime_dvd_right hdvd2) ρ' hρ'inj
  have h1 := ih _ (by rw [← hn, hQ]; nlinarith) T.toSubmodule rfl G1
    (hcop.coprime_dvd_right hdvd1) ρ1 hρ1inj
  have hlt : Nat.card G < Nat.card Q - 1 := by
    rw [hG, hQ]
    obtain ⟨a, ha'⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨b, hb'⟩ := Nat.exists_eq_add_of_le hb
    have e0 := h0.1
    have e1 := h1.1
    rw [ha'] at e0 ⊢
    rw [hb'] at e1 ⊢
    have e0' : Nat.card (G ⧸ G1) ≤ a + 1 := by omega
    have e1' : Nat.card G1 ≤ b + 1 := by omega
    have := Nat.mul_le_mul e0' e1'
    have e : (2 + a) * (2 + b) = a * b + 2 * a + 2 * b + 4 := by ring
    have e' : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    rw [e]
    rw [e'] at this
    generalize Nat.card (G ⧸ G1) * Nat.card G1 = m at this ⊢
    generalize a * b = c at this ⊢
    omega
  exact ⟨hlt.le, fun h => absurd h hlt.ne⟩


end FaithfulAbelianActionBounds


section RegularNonzeroActions


open Representation


private theorem card_bound_or_regular_action {p : ℕ} [Fact p.Prime] {P K : Type} [AddCommGroup P] [Finite P] [Nontrivial P]
    (hP : ∀ x : P, p • x = 0) [CommGroup K] [Finite K] (hK : Nat.Coprime p (Nat.card K))
    [Module (ZMod p) P] [DistribMulAction K P] [FaithfulSMul K P] :
    Nat.card K < Nat.card P - 1 ∨
      (Nat.card K = Nat.card P - 1 ∧ ∀ x y : P, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : K → Module.End (ZMod p) P := fun k =>
    (({ toFun := fun x => k • x, map_zero' := smul_zero k, map_add' := smul_add k } :
      P →+ P)).toZModLinearMap p
  have h1 : f 1 = 1 := by
    apply LinearMap.ext
    intro x
    exact one_smul K x
  have h2 : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    apply LinearMap.ext
    intro x
    exact mul_smul a b x
  let ρ : Representation (ZMod p) K P := MonoidHom.mk (OneHom.mk f h1) h2
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply eq_of_smul_eq_smul (M := K) (α := P)
    intro x
    exact (LinearMap.congr_fun hab x : _)
  obtain ⟨hle, hreg⟩ := card_bound_of_faithful_abelian_action (Nat.card P) P rfl K hK ρ hρ
  rcases hle.lt_or_eq with h | h
  · left
    exact h
  · right
    exact ⟨h, fun x y hx hy => hreg h x y hx hy⟩


end RegularNonzeroActions


theorem card_lt_or_regular_on_nonzero_of_faithful_coprime_abelian_action {p : ℕ} [Fact p.Prime] {P K : Type} [AddCommGroup P] [Finite P] [Nontrivial P]
    (hP : ∀ x : P, p • x = 0) [CommGroup K] [Finite K] (hK : Nat.Coprime p (Nat.card K))
    [DistribMulAction K P] [FaithfulSMul K P] :
    Nat.card K < Nat.card P - 1 ∨
      (Nat.card K = Nat.card P - 1 ∧ ∀ x y : P, x ≠ 0 → y ≠ 0 → ∃! k : K, k • x = y) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Module (ZMod p) P := AddCommGroup.zmodModule hP
  exact card_bound_or_regular_action hP hK


end CFSG.Timmesfeld.LocalTwoSubgroups
