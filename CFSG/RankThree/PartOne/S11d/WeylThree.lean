module

public import CFSG.RankThree.PartOne.S11d.FactsInner

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace InnerWeyl

section Dihedral

open DihedralGroup

def genMap {n : ℕ} (a b : DihedralGroup n) : DihedralGroup n → DihedralGroup n
  | r i => a ^ i.val
  | sr i => b * a ^ i.val

theorem eq_genMap {n : ℕ} [NeZero n] (s : DihedralGroup n → DihedralGroup n)
    (hs : ∀ x y, s (x * y) = s x * s y) : s = genMap (s (r 1)) (s (sr 0)) := by
  let f : DihedralGroup n →* DihedralGroup n := MonoidHom.mk' s hs
  have hr : ∀ i : ZMod n, s (r i) = (s (r 1)) ^ i.val := by
    intro i
    have h : (r i : DihedralGroup n) = (r 1) ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [h]
    exact map_pow f (r 1) i.val
  funext x
  cases x with
  | r i => exact hr i
  | sr i =>
    have h : (sr i : DihedralGroup n) = sr 0 * r i := by
      rw [sr_mul_r, zero_add]
    calc s (sr i) = s (sr 0 * r i) := by rw [← h]
      _ = s (sr 0) * (s (r 1)) ^ i.val := by rw [hs, hr]
      _ = _ := rfl

theorem genMap_four : ∀ a b : DihedralGroup 4,
    (∀ x y, genMap a b (x * y) = genMap a b x * genMap a b y) →
    (∀ x, genMap a b (genMap a b (genMap a b x)) = x) → ∀ x, genMap a b x = x := by
  decide +kernel

theorem genMap_eight : ∀ a b : DihedralGroup 8,
    (∀ x y, genMap a b (x * y) = genMap a b x * genMap a b y) →
    (∀ x, genMap a b (genMap a b (genMap a b x)) = x) → ∀ x, genMap a b x = x := by
  decide +kernel

theorem dihedral_aut_trivial {n : ℕ} (hn : n = 4 ∨ n = 8) (s : DihedralGroup n → DihedralGroup n)
    (hs : ∀ x y, s (x * y) = s x * s y) (h3 : ∀ x, s (s (s x)) = x) (x : DihedralGroup n) :
    s x = x := by
  rcases hn with rfl | rfl
  · obtain ⟨a, b, hab⟩ : ∃ a b, s = genMap a b := ⟨_, _, eq_genMap s hs⟩
    subst hab
    exact genMap_four a b hs h3 x
  · obtain ⟨a, b, hab⟩ : ∃ a b, s = genMap a b := ⟨_, _, eq_genMap s hs⟩
    subst hab
    exact genMap_eight a b hs h3 x

theorem aut_dihedral_trivial {Γ : Type*} [Group Γ] {n : ℕ} (hn : n = 4 ∨ n = 8)
    (e : Γ ≃* DihedralGroup n) (s : Γ → Γ) (hs : ∀ x y, s (x * y) = s x * s y)
    (h3 : ∀ x, s (s (s x)) = x) (x : Γ) : s x = x := by
  have key := dihedral_aut_trivial hn (fun d => e (s (e.symm d)))
    (fun d d' => by simp [hs]) (fun d => by simp [h3]) (e x)
  simpa using key

theorem perm_three_order_three : ∃ w : Equiv.Perm (Fin 3), w ≠ 1 ∧ w ^ 3 = 1 ∧
    ∀ u : Equiv.Perm (Fin 3), u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹ :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide, by decide⟩

theorem dihedral_six_order_three : ∃ w : DihedralGroup 6, w ≠ 1 ∧ w ^ 3 = 1 ∧
    ∀ u : DihedralGroup 6, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹ :=
  ⟨r 2, by decide, by decide, by decide⟩

end Dihedral

theorem exists_order_three_of_equiv {Γ D : Type*} [Group Γ] [Group D] (e : Γ ≃* D)
    (h : ∃ w : D, w ≠ 1 ∧ w ^ 3 = 1 ∧ ∀ u : D, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹) :
    ∃ w : Γ, w ≠ 1 ∧ w ^ 3 = 1 ∧ ∀ u : Γ, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹ := by
  obtain ⟨w, hw1, hw3, hu⟩ := h
  refine ⟨e.symm w, fun h => hw1 (by simpa using congrArg e h),
    by rw [← map_pow, hw3, map_one], ?_⟩
  intro u hu3
  rcases hu (e u) (by rw [← map_pow, hu3, map_one]) with h | h | h
  · exact Or.inl (e.injective (by simpa using h))
  · exact Or.inr (Or.inl (e.injective (by simpa using h)))
  · exact Or.inr (Or.inr (e.injective (by simp [h])))

theorem exists_order_three {Γ : Type*} [Group Γ]
    (h : Nonempty (Γ ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (Γ ≃* DihedralGroup 6)) :
    ∃ w : Γ, w ≠ 1 ∧ w ^ 3 = 1 ∧ ∀ u : Γ, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹ := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact exists_order_three_of_equiv e perm_three_order_three
  · exact exists_order_three_of_equiv e dihedral_six_order_three

theorem conj_cube {M : Type*} [Group M] (ξ : M) (hξ : ξ ^ 3 = 1) (g : M) :
    ξ * (ξ * (ξ * g * ξ⁻¹) * ξ⁻¹) * ξ⁻¹ = g := by
  have h : ξ * (ξ * (ξ * g * ξ⁻¹) * ξ⁻¹) * ξ⁻¹ = ξ ^ 3 * g * (ξ ^ 3)⁻¹ := by
    simp [pow_succ, mul_assoc]
  rw [h, hξ]
  simp

theorem exists_commuting_order_three {M : Type*} [Group M] {Γ : Subgroup M}
    (hW : Nonempty (Γ ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (Γ ≃* DihedralGroup 6))
    (ξ : M) (hξ : ξ ^ 3 = 1) (hN : ∀ g ∈ Γ, ξ * g * ξ⁻¹ ∈ Γ) :
    ∃ w ∈ Γ, w ≠ 1 ∧ w ^ 3 = 1 ∧ (∀ u ∈ Γ, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹) ∧
      ξ * w = w * ξ := by
  obtain ⟨w₀, hw1, hw3, hu⟩ := exists_order_three hW
  have hwΓ : (w₀ : M) ∈ Γ := w₀.2
  have hw1' : (w₀ : M) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw3' : (w₀ : M) ^ 3 = 1 := by simpa using congrArg Subtype.val hw3
  have hu' : ∀ u ∈ Γ, u ^ 3 = 1 → u = 1 ∨ u = w₀ ∨ u = (w₀ : M)⁻¹ := by
    intro u huΓ hu3
    rcases hu ⟨u, huΓ⟩ (Subtype.ext (by simpa using hu3)) with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  refine ⟨w₀, hwΓ, hw1', hw3', hu', ?_⟩
  have hv : ξ * w₀ * ξ⁻¹ ∈ Γ := hN _ hwΓ
  have hv3 : (ξ * (w₀ : M) * ξ⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hw3', mul_one, mul_inv_cancel]
  rcases hu' _ hv hv3 with h | h | h
  · exact absurd (by simpa using h) hw1'
  · calc ξ * (w₀ : M) = ξ * w₀ * ξ⁻¹ * ξ := by group
      _ = w₀ * ξ := by rw [h]
  · exfalso
    have h2 : ξ * (w₀ : M)⁻¹ * ξ⁻¹ = w₀ := by
      calc ξ * (w₀ : M)⁻¹ * ξ⁻¹ = (ξ * w₀ * ξ⁻¹)⁻¹ := by group
        _ = w₀ := by rw [h, inv_inv]
    have h3 : ξ * (ξ * (ξ * (w₀ : M) * ξ⁻¹) * ξ⁻¹) * ξ⁻¹ = (w₀ : M)⁻¹ := by rw [h, h2, h]
    rw [conj_cube ξ hξ] at h3
    have hww : (w₀ : M) * w₀ = 1 := by
      calc (w₀ : M) * w₀ = w₀ * (w₀ : M)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    apply hw1'
    calc (w₀ : M) = (w₀ : M) ^ 3 * ((w₀ : M) * w₀)⁻¹ := by group
      _ = 1 := by rw [hw3', hww]; simp

section Weyl

variable {G : Type} [Group G] (E : Subgroup G)

theorem fixed_trivial {Γ : Subgroup (MulAut E)}
    (hirr : ∀ B : Subgroup E, (∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤)
    {w : MulAut E} (hwΓ : w ∈ Γ) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hu : ∀ u ∈ Γ, u ^ 3 = 1 → u = 1 ∨ u = w ∨ u = w⁻¹) (b : E) (hb : w b = b) : b = 1 := by
  have hinv : ∀ b : E, w b = b → w⁻¹ b = b := fun b hb => by
    calc w⁻¹ b = w⁻¹ (w b) := by rw [hb]
      _ = b := by simp
  have hB : ∀ g ∈ Γ, ∀ b ∈ autFixed E w, g b ∈ autFixed E w := by
    intro g hg b hb
    have hb' : w b = b := hb
    have hug : g⁻¹ * w * g ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) hwΓ) hg
    have hu3 : (g⁻¹ * w * g) ^ 3 = 1 := by
      have h := conj_pow (i := 3) (a := g⁻¹) (b := w)
      rw [inv_inv, hw3] at h
      rw [h]
      simp
    have hfix : (g⁻¹ * w * g) b = b := by
      rcases hu _ hug hu3 with h | h | h
      · rw [h]; rfl
      · rw [h]; exact hb'
      · rw [h]; exact hinv b hb'
    show w (g b) = g b
    calc w (g b) = (w * g) b := rfl
      _ = (g * (g⁻¹ * w * g)) b := by group
      _ = g ((g⁻¹ * w * g) b) := rfl
      _ = g b := by rw [hfix]
  rcases hirr _ hB with h | h
  · have : b ∈ autFixed E w := hb
    rw [h] at this
    exact this
  · exfalso
    apply hw1
    refine MulEquiv.ext fun b => ?_
    have hb : b ∈ autFixed E w := by rw [h]; trivial
    have hb' : w b = b := hb
    simpa using hb'

theorem false_of_dihedral {Γ : Subgroup (MulAut E)} {n : ℕ} (hn : n = 4 ∨ n = 8)
    (e : Γ ≃* DihedralGroup n)
    (hirr : ∀ B : Subgroup E, (∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤)
    (ξ : MulAut E) (hξ : ξ ^ 3 = 1) (hN : ∀ g ∈ Γ, ξ * g * ξ⁻¹ ∈ Γ)
    {c f : E} (hc : c ≠ 1) (hξc : ξ c = c) (hf : ξ f ≠ f) : False := by
  have hcomm : ∀ g ∈ Γ, ξ * g = g * ξ := by
    intro g hg
    have h1 := aut_dihedral_trivial hn e (fun g => ⟨ξ * g * ξ⁻¹, hN g g.2⟩)
      (fun x y => Subtype.ext (by simp [mul_assoc]))
      (fun x => Subtype.ext (conj_cube ξ hξ x)) ⟨g, hg⟩
    have h2 : ξ * g * ξ⁻¹ = g := congrArg Subtype.val h1
    calc ξ * g = ξ * g * ξ⁻¹ * ξ := by group
      _ = g * ξ := by rw [h2]
  have hB : ∀ g ∈ Γ, ∀ b ∈ autFixed E ξ, g b ∈ autFixed E ξ := by
    intro g hg b hb
    have hb' : ξ b = b := hb
    show ξ (g b) = g b
    calc ξ (g b) = (ξ * g) b := rfl
      _ = (g * ξ) b := by rw [hcomm g hg]
      _ = g (ξ b) := rfl
      _ = g b := by rw [hb']
  rcases hirr _ hB with h | h
  · have : c ∈ autFixed E ξ := hξc
    rw [h] at this
    exact hc this
  · have : f ∈ autFixed E ξ := by rw [h]; trivial
    exact hf this

variable [Finite G]

theorem fixed_le_zpowers [IsElementaryAbelian 7 E] (hcard : Nat.card E = 49)
    (ξ : MulAut E) {c f : E} (hc : c ≠ 1) (hξc : ξ c = c) (hf : ξ f ≠ f) (b : E)
    (hb : ξ b = b) : b ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc7 : c ^ 7 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 7 E) c
  have hord : orderOf c = 7 := orderOf_eq_prime hc7 hc
  have hle : Subgroup.zpowers c ≤ autFixed E ξ := by
    rw [Subgroup.zpowers_le]
    exact hξc
  have hcardz : Nat.card (Subgroup.zpowers c) = 7 := by rw [Nat.card_zpowers, hord]
  have hdvd1 : 7 ∣ Nat.card (autFixed E ξ) := hcardz ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (autFixed E ξ) ∣ 7 ^ 2 := by
    have := Subgroup.card_subgroup_dvd_card (autFixed E ξ)
    rwa [hcard] at this
  have hne : Nat.card (autFixed E ξ) ≠ 49 := by
    intro h
    have htop : autFixed E ξ = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 (h.trans hcard.symm)
    have : f ∈ autFixed E ξ := by rw [htop]; trivial
    exact hf this
  have h7 : Nat.card (autFixed E ξ) = 7 := by
    obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hdvd2
    interval_cases m
    · rw [hmeq] at hdvd1
      omega
    · simpa using hmeq
    · exact absurd (by simpa using hmeq) hne
  have heq : Subgroup.zpowers c = autFixed E ξ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h7, hcardz])
  rw [heq]
  exact hb

end Weyl

section Concrete

variable {G : Type} [Group G]

theorem mem_torusImage_iff {E Y : Subgroup G} {g : MulAut E} :
    g ∈ torusImage E Y ↔ ∃ z : Subgroup.normalizer (E : Set G), (z : G) ∈ Y ∧
      E.normalizerMonoidHom z = g := by
  constructor
  · intro h
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.1 h
    exact ⟨z, Subgroup.mem_subgroupOf.1 hz, hzg⟩
  · rintro ⟨z, hz, hzg⟩
    exact Subgroup.mem_map.2 ⟨z, Subgroup.mem_subgroupOf.2 hz, hzg⟩

theorem conj_mem_torusImage {K F : Subgroup G} {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G))
    {g : MulAut F} (hg : g ∈ torusImage F K) :
    F.normalizerMonoidHom ⟨x, hxF⟩ * g * (F.normalizerMonoidHom ⟨x, hxF⟩)⁻¹ ∈ torusImage F K := by
  obtain ⟨z, hz, rfl⟩ := mem_torusImage_iff.1 hg
  refine mem_torusImage_iff.2 ⟨⟨x, hxF⟩ * z * ⟨x, hxF⟩⁻¹, ?_, by simp⟩
  have h := (Subgroup.mem_normalizer_iff.1 hxK (z : G)).1 hz
  simpa using h

theorem irreducible_of_rowData {K F : Subgroup G}
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F K B → B = ⊥ ∨ B = F)
    (B : Subgroup F) (hB : ∀ g ∈ torusImage F K, ∀ b ∈ B, g b ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hinv : torusInvariant F K (B.map F.subtype) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    have hwN' : w ∈ Subgroup.normalizer (F : Set G) := hwN
    have hg : F.normalizerMonoidHom ⟨w, hwN'⟩ ∈ torusImage F K :=
      mem_torusImage_iff.2 ⟨⟨w, hwN'⟩, hwK, rfl⟩
    exact Subgroup.mem_map.2 ⟨_, hB _ hg b' hb', rfl⟩
  rcases hirr _ (Subgroup.map_subtype_le B) hinv with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective B F.subtype_injective).1 h)
  · right
    refine eq_top_iff.2 fun b _ => ?_
    have hb : (b : G) ∈ B.map F.subtype := by rw [h]; exact b.2
    obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.1 hb
    have hbb' : b' = b := Subtype.ext hbb
    rw [← hbb']
    exact hb'

theorem coe_mem_zpowers {F : Subgroup G} {c : G} (hcF : c ∈ F) {b : F}
    (hb : b ∈ Subgroup.zpowers (⟨c, hcF⟩ : F)) : (b : G) ∈ Subgroup.zpowers c := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [Subgroup.coe_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) j

theorem mem_normalizer_zpowers {y c : G} (h1 : y * c * y⁻¹ ∈ Subgroup.zpowers c)
    (h2 : y⁻¹ * c * y ∈ Subgroup.zpowers c) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 j
  · intro hh
    have h' : h = y⁻¹ * (y * h * y⁻¹) * y := by group
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [h', ← hj]
    have h'' := conj_zpow (i := j) (a := y⁻¹) (b := c)
    rw [inv_inv] at h''
    rw [← h'']
    exact Subgroup.zpow_mem _ h2 j

theorem exists_three_element [Finite G] {K F : Subgroup G} {c : G} (hcF : c ∈ F) (hc1 : c ≠ 1)
    {ξ w : MulAut F} (hwΓ : w ∈ torusImage F K) (hw3 : w ^ 3 = 1) (hξw : ξ * w = w * ξ)
    (hξc : ξ ⟨c, hcF⟩ = ⟨c, hcF⟩) (hwfix : ∀ b : F, w b = b → b = 1)
    (hξfix : ∀ b : F, ξ b = b → b ∈ Subgroup.zpowers (⟨c, hcF⟩ : F)) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      (∃ k : ℕ, y ^ (3 ^ k) = 1) ∧ y * c * y⁻¹ ≠ c := by
  obtain ⟨z₀, hz₀, hz₀w⟩ := mem_torusImage_iff.1 hwΓ
  obtain ⟨e, m, hm3, hem⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z₀).ne' 3 (by norm_num)
  obtain ⟨z, hz⟩ : ∃ z : Subgroup.normalizer (F : Set G), z = z₀ ^ m := ⟨_, rfl⟩
  have hzK : (z : G) ∈ K := by
    rw [hz, Subgroup.coe_pow]
    exact pow_mem hz₀ m
  have hz3 : z ^ (3 ^ e) = 1 := by
    rw [hz, ← pow_mul, mul_comm, ← hem]
    exact pow_orderOf_eq_one z₀
  have hφz : F.normalizerMonoidHom z = w ^ m := by rw [hz, map_pow, hz₀w]
  have hu_mod : w ^ m = w ∨ w ^ m = w⁻¹ := by
    have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
    have hu : w ^ m = w ^ (m % 3) := by
      conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hw3, one_pow, one_mul]
    rcases hmod with h | h
    · left
      rw [hu, h, pow_one]
    · right
      rw [hu, h]
      have h2 : w ^ 2 * w = 1 := by rw [← pow_succ, hw3]
      exact eq_inv_of_mul_eq_one_left h2
  have hufix : ∀ b : F, (w ^ m) b = b → b = 1 := by
    intro b hb
    rcases hu_mod with h | h
    · rw [h] at hb
      exact hwfix b hb
    · rw [h] at hb
      apply hwfix b
      calc w b = w (w⁻¹ b) := by rw [hb]
        _ = b := by simp
  have hξu : ξ * w ^ m = w ^ m * ξ := (Commute.pow_right (show Commute ξ w from hξw) m).eq
  have hξu' : ξ * (w ^ m)⁻¹ = (w ^ m)⁻¹ * ξ :=
    ((Commute.pow_right (show Commute ξ w from hξw) m).inv_right).eq
  have hmem : ∀ v : MulAut F, ξ * v = v * ξ → v ⟨c, hcF⟩ ∈ Subgroup.zpowers (⟨c, hcF⟩ : F) := by
    intro v hv
    apply hξfix
    calc ξ (v ⟨c, hcF⟩) = (ξ * v) ⟨c, hcF⟩ := rfl
      _ = (v * ξ) ⟨c, hcF⟩ := by rw [hv]
      _ = v (ξ ⟨c, hcF⟩) := rfl
      _ = v ⟨c, hcF⟩ := by rw [hξc]
  have hc1' : ((w ^ m) ⟨c, hcF⟩ : G) = (z : G) * c * (z : G)⁻¹ := by
    rw [← hφz]
    rfl
  have hc2' : ((w ^ m)⁻¹ ⟨c, hcF⟩ : G) = (z : G)⁻¹ * c * (z : G) := by
    rw [← hφz, ← map_inv]
    simp
  refine ⟨z, hzK, mem_normalizer_zpowers ?_ ?_, ⟨e, ?_⟩, ?_⟩
  · rw [← hc1']
    exact coe_mem_zpowers hcF (hmem _ hξu)
  · rw [← hc2']
    exact coe_mem_zpowers hcF (hmem _ hξu')
  · have h := congrArg Subtype.val hz3
    simpa using h
  · intro h
    have h1 : (w ^ m) ⟨c, hcF⟩ = ⟨c, hcF⟩ := Subtype.ext (by rw [hc1']; exact h)
    exact hc1 (congrArg Subtype.val (hufix _ h1))

variable [Finite G]

theorem inner_weyl_core {K F : Subgroup G} [IsElementaryAbelian 7 F] (hcard : Nat.card F = 49)
    (hirr : ∀ B : Subgroup F, (∀ g ∈ torusImage F K, ∀ b ∈ B, g b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hW : (Nonempty (torusImage F K ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (torusImage F K ≃* DihedralGroup 6)) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 8) ∧ Nonempty (torusImage F K ≃* DihedralGroup n))
    {x c : G} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxF : x ∈ Subgroup.normalizer (F : Set G)) (hx3 : x ^ 3 = 1) (hcF : c ∈ F) (hc1 : c ≠ 1)
    (hxc : x * c = c * x) (hmoved : ∃ f ∈ F, x * f * x⁻¹ ≠ f) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      (∃ k : ℕ, y ^ (3 ^ k) = 1) ∧ y * c * y⁻¹ ≠ c := by
  obtain ⟨f, hfF, hfx⟩ := hmoved
  obtain ⟨ξ, hξ⟩ : ∃ ξ : MulAut F, ξ = F.normalizerMonoidHom ⟨x, hxF⟩ := ⟨_, rfl⟩
  have hξ3 : ξ ^ 3 = 1 := by
    have h : (⟨x, hxF⟩ : Subgroup.normalizer (F : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [hξ, ← map_pow, h, map_one]
  have hξapp : ∀ b : F, ((ξ b : F) : G) = x * b * x⁻¹ := by
    intro b
    rw [hξ]
    rfl
  have hξc : ξ ⟨c, hcF⟩ = ⟨c, hcF⟩ := Subtype.ext (by rw [hξapp, hxc]; simp)
  have hξf : ξ ⟨f, hfF⟩ ≠ ⟨f, hfF⟩ := fun h => hfx (by
    have h' := congrArg Subtype.val h
    rw [hξapp] at h'
    exact h')
  have hc1' : (⟨c, hcF⟩ : F) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hN : ∀ g ∈ torusImage F K, ξ * g * ξ⁻¹ ∈ torusImage F K := fun g hg => by
    rw [hξ]
    exact conj_mem_torusImage hxK hxF hg
  have hfix := fixed_le_zpowers F hcard ξ hc1' hξc hξf
  rcases hW with hW | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨w, hwΓ, hw1, hw3, hu, hξw⟩ := exists_commuting_order_three hW ξ hξ3 hN
    exact exists_three_element hcF hc1 hwΓ hw3 hξw hξc
      (fixed_trivial F hirr hwΓ hw1 hw3 hu) hfix
  · exact (false_of_dihedral F hn e hirr ξ hξ3 hN hc1' hξc hξf).elim

end Concrete

end InnerWeyl

theorem innerWeylFact : InnerWeylFact := by
  intro G _ _ K F r hFK hF h1r hr8 hRow c x hxK hxF hx3 hcF hc1 hxc hmoved
  obtain ⟨-, hcard, hW, -, hirr, -⟩ := hRow
  have hRR : RowRank r = 2 := by interval_cases r <;> rfl
  have hcard' : Nat.card F = 49 := by rw [hcard, hRR]; norm_num
  refine InnerWeyl.inner_weyl_core hcard' (InnerWeyl.irreducible_of_rowData (hirr (by omega)))
    ?_ hxK hxF hx3 hcF hc1 hxc hmoved
  interval_cases r
  · exact Or.inl (Or.inl hW)
  · exact Or.inl (Or.inr hW)
  · exact Or.inl (Or.inr hW)
  · exact Or.inr ⟨8, Or.inr rfl, hW⟩
  · exact Or.inr ⟨4, Or.inl rfl, hW⟩
  · exact Or.inr ⟨4, Or.inl rfl, hW⟩
  · exact Or.inr ⟨4, Or.inl rfl, hW⟩
  · exact Or.inr ⟨4, Or.inl rfl, hW⟩

end CFSG.RankThree.PartOne
