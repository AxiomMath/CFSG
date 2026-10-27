module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open scoped commutatorElement

section Two

variable {K : Type} [Field K]

theorem eq_zero_or_one_of_card_two (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  obtain ⟨a₀, rfl⟩ := (castTwo_bijective hK).2 a
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a₀ with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

theorem zornNorm_add_one {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0) :
    zornNorm (x + zornOne) = zornNorm x + 1 := by
  simp only [zornNorm, zornOne, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply,
    add_zero]
  linear_combination hx

theorem zornOne_tr : (zornOne : quasithinZorn K).1 + (zornOne : quasithinZorn K).2.2.2 = 2 := by
  simp [zornOne, one_add_one_eq_two]

@[expose] def zornClsD [DecidableEq K] (x : quasithinZorn K) : ℕ :=
  if x = 0 then 2 else if x = zornOne then 3 else if zornNorm x = 0 then 0 else 1

theorem zornClsD_g2 [DecidableEq K] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) (x : quasithinZorn K) : zornClsD (g x) = zornClsD x := by
  have h0 : g x = 0 ↔ x = 0 := ⟨fun h => g.injective (h.trans (map_zero g).symm),
    fun h => by rw [h, map_zero]⟩
  have h1 : g x = zornOne ↔ x = zornOne :=
    ⟨fun h => g.injective (h.trans (quasithinG2_one hg).symm),
      fun h => by rw [h, quasithinG2_one hg]⟩
  simp only [zornClsD, h0, h1, quasithinG2_norm hg]

theorem zornClsD_zornMap [DecidableEq K] (hK : Nat.card K = 2) (x : quasithinZorn (ZMod 2)) :
    zornClsD (zornMap (castTwo hK) x) = zornClsD x := by
  have hinj := zornMap_injective hK
  have h0 : zornMap (castTwo hK) x = 0 ↔ x = 0 :=
    ⟨fun h => hinj (h.trans (zornMap_zero hK).symm), fun h => by rw [h, zornMap_zero]⟩
  have h1 : zornMap (castTwo hK) x = zornOne ↔ x = zornOne :=
    ⟨fun h => hinj (h.trans (zornMap_one hK).symm), fun h => by rw [h, zornMap_one]⟩
  have hn : zornNorm (zornMap (castTwo hK) x) = 0 ↔ zornNorm x = 0 := by
    rw [zornMap_norm]
    exact ⟨fun h => (castTwo_bijective hK).1 (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  simp only [zornClsD, h0, h1, hn]

theorem card_zorn_subtype (hK : Nat.card K = 2) (P : quasithinZorn K → Prop) (Q : Fin 256 → Prop)
    [DecidablePred Q] (hPQ : ∀ c : Fin 256, P (zornMap (castTwo hK) (decodeZ c)) ↔ Q c) :
    Nat.card {x : quasithinZorn K // P x} = (Finset.univ.filter Q).card := by
  have hbij : Function.Bijective fun c : Fin 256 => zornMap (castTwo hK) (decodeZ c) := by
    refine ⟨fun a b h => Fin.ext (decodeZ_injective a.2 b.2 (zornMap_injective hK h)), ?_⟩
    intro x
    obtain ⟨m₀, rfl⟩ := exists_zornMap_eq hK x
    obtain ⟨c, hc, hcm⟩ := decodeZ_surjective m₀
    exact ⟨⟨c, hc⟩, by rw [← hcm]⟩
  let e := Equiv.ofBijective _ hbij
  rw [← Nat.card_congr (e.subtypeEquiv fun c => (hPQ c).symm), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem g2_counts : ∀ k : Fin 4,
    (Finset.univ.filter fun c : Fin 256 =>
      (decodeZ c).1 + (decodeZ c).2.2.2 = 0 ∧ zornClsD (decodeZ c) = k).card =
        if (k : ℕ) < 2 then 63 else 1 := by
  decide +kernel

theorem g2_count_O0 :
    (Finset.univ.filter fun c : Fin 256 => (decodeZ c).1 + (decodeZ c).2.2.2 = 0).card = 128 := by
  decide +kernel

theorem card_class [DecidableEq K] (hK : Nat.card K = 2) (k : ℕ) (hk : k < 4) :
    Nat.card {x : quasithinZorn K // x.1 + x.2.2.2 = 0 ∧ zornClsD x = k} =
      if k < 2 then 63 else 1 := by
  rw [card_zorn_subtype hK _ (fun c => (decodeZ c).1 + (decodeZ c).2.2.2 = 0 ∧
    zornClsD (decodeZ c) = k)]
  · exact g2_counts ⟨k, hk⟩
  · intro c
    rw [zornMap_tr, zornClsD_zornMap]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(castTwo_bijective hK).1 (h1.trans (map_zero _).symm), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, map_zero], h2⟩

theorem card_O0 (hK : Nat.card K = 2) :
    Nat.card {x : quasithinZorn K // x.1 + x.2.2.2 = 0} = 128 := by
  rw [card_zorn_subtype hK _ (fun c => (decodeZ c).1 + (decodeZ c).2.2.2 = 0)]
  · exact g2_count_O0
  · intro c
    rw [zornMap_tr]
    exact ⟨fun h => (castTwo_bijective hK).1 (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩

theorem exists_g2Derived_of_cls [DecidableEq K] (hK : Nat.card K = 2) {m m' : quasithinZorn K}
    (hm : m.1 + m.2.2.2 = 0) (hm' : m'.1 + m'.2.2.2 = 0) (h : zornClsD m = zornClsD m') :
    ∃ γ ∈ ⁅quasithinG2 K, quasithinG2 K⁆, γ m = m' := by
  unfold zornClsD at h
  by_cases h0 : m = 0
  · by_cases h0' : m' = 0
    · exact ⟨1, Subgroup.one_mem _, by rw [h0, h0']; rfl⟩
    · exfalso
      rw [ite_eq_left h0, ite_eq_right h0'] at h
      split_ifs at h <;> omega
  by_cases h1 : m = zornOne
  · by_cases h0' : m' = 0
    · exfalso
      rw [ite_eq_right h0, ite_eq_left h0'] at h
      split_ifs at h
      omega
    by_cases h1' : m' = zornOne
    · exact ⟨1, Subgroup.one_mem _, by rw [h1, h1']; rfl⟩
    · exfalso
      rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h0', ite_eq_right h1'] at h
      split_ifs at h
      omega
  by_cases h0' : m' = 0
  · exfalso
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h0'] at h
    split_ifs at h
    omega
  by_cases h1' : m' = zornOne
  · exfalso
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h0', ite_eq_left h1'] at h
    split_ifs at h
    omega
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h0', ite_eq_right h1'] at h
  have hn : zornNorm m = 0 ↔ zornNorm m' = 0 := by
    constructor
    · intro hn
      by_contra hn'
      rw [ite_eq_left hn, ite_eq_right hn'] at h
      exact absurd h (by norm_num)
    · intro hn'
      by_contra hn
      rw [ite_eq_right hn, ite_eq_left hn'] at h
      exact absurd h (by norm_num)
  obtain ⟨hA, hB⟩ := exists_g2Derived_apply_eq hK hm h0 h1
  obtain ⟨hA', hB'⟩ := exists_g2Derived_apply_eq hK hm' h0' h1'
  have key : ∀ (b : quasithinZorn K) (γ γ' : quasithinZorn K ≃ₗ[K] quasithinZorn K),
      γ ∈ ⁅quasithinG2 K, quasithinG2 K⁆ → γ' ∈ ⁅quasithinG2 K, quasithinG2 K⁆ →
        γ b = m → γ' b = m' → ∃ γ ∈ ⁅quasithinG2 K, quasithinG2 K⁆, γ m = m' := by
    intro b γ γ' hγ hγ' hγm hγm'
    refine ⟨γ' * γ⁻¹, Subgroup.mul_mem _ hγ' (Subgroup.inv_mem _ hγ), ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.coe_inv, ← hγm, LinearEquiv.symm_apply_apply, hγm']
  by_cases hn0 : zornNorm m = 0
  · obtain ⟨γ, hγ, hγm⟩ := hA hn0
    obtain ⟨γ', hγ', hγm'⟩ := hA' (hn.1 hn0)
    exact key _ γ γ' hγ hγ' hγm hγm'
  · obtain ⟨γ, hγ, hγm⟩ := hB hn0
    obtain ⟨γ', hγ', hγm'⟩ := hB' (fun h' => hn0 (hn.2 h'))
    exact key _ γ γ' hγ hγ' hγm hγm'

theorem zornClsD_add_one [DecidableEq K] (hK : Nat.card K = 2) {x : quasithinZorn K}
    (hx : x.1 + x.2.2.2 = 0) (hx0 : x ≠ 0) (hx1 : x ≠ zornOne) :
    zornClsD (x + zornOne) = 1 - zornClsD x := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hK
  have hy0 : x + zornOne ≠ 0 := by
    intro h
    apply hx1
    have h' : x = -zornOne := eq_neg_of_add_eq_zero_left h
    rw [h']
    apply zorn_ext <;> (try intro i) <;> simp [zornOne]
    all_goals exact neg_eq_of_add_eq_zero_left (by rw [one_add_one_eq_two, h2])
  have hy1 : x + zornOne ≠ zornOne := fun h => hx0 (add_eq_right.1 h)
  unfold zornClsD
  rw [ite_eq_right hy0, ite_eq_right hy1, ite_eq_right hx0, ite_eq_right hx1,
    zornNorm_add_one hx]
  rcases eq_zero_or_one_of_card_two hK (zornNorm x) with h | h
  · rw [h, zero_add, ite_eq_right one_ne_zero, ite_eq_left rfl]
  · rw [h, one_add_one_eq_two, h2, ite_eq_left rfl, ite_eq_right one_ne_zero]

theorem zornClsD_lt_two [DecidableEq K] {x : quasithinZorn K} (hx0 : x ≠ 0) (hx1 : x ≠ zornOne) :
    zornClsD x < 2 := by
  unfold zornClsD
  rw [ite_eq_right hx0, ite_eq_right hx1]
  split_ifs <;> norm_num

theorem zornClsD_add_one_eq [DecidableEq K] (hK : Nat.card K = 2) {x y : quasithinZorn K}
    (hx : x.1 + x.2.2.2 = 0) (hx0 : x ≠ 0) (hx1 : x ≠ zornOne) (hy0 : y ≠ 0)
    (hy1 : y ≠ zornOne) (h : zornClsD y ≠ zornClsD x) : zornClsD y = zornClsD (x + zornOne) := by
  rw [zornClsD_add_one hK hx hx0 hx1]
  have := zornClsD_lt_two hx0 hx1
  have := zornClsD_lt_two hy0 hy1
  omega

theorem zornOne_add_mem {x : quasithinZorn K} (hK : Nat.card K = 2) (hx : x.1 + x.2.2.2 = 0) :
    (x + zornOne).1 + (x + zornOne).2.2.2 = 0 := by
  simp only [Prod.fst_add, Prod.snd_add]
  rw [add_add_add_comm, hx, zornOne_tr, two_eq_zero_of_card_two hK, zero_add]

end Two

theorem derived_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem orbitG2Natural :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
      G2NaturalDerived H ⊤ ⊥ 1 → OrbitLengthsIn H [63] ∧ OrbitsSeparated H := by
  intro V _ _ H hH
  obtain ⟨K, _, _, hK, hR⟩ := hH
  classical
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨π, β, hR⟩ := (realizes_iff _ H ⊤ ⊥).1 hR
  have htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g ∈ H, (g : MulAut V) v = w := by
    intro v w hv hw
    refine exists_eq_of_transitive hR (fun m hm m' hm' hmk hmk' => ?_) hv hw
    obtain ⟨x, rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m :=
      ⟨Multiplicative.toAdd m, rfl⟩
    obtain ⟨x', rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m' :=
      ⟨Multiplicative.toAdd m', rfl⟩
    have hx : x.1 + x.2.2.2 = 0 := hm
    have hx' : x'.1 + x'.2.2.2 = 0 := hm'
    have hx0 : x ≠ 0 := fun h => hmk (by rw [h]; exact ⟨0, rfl⟩)
    have hx1 : x ≠ zornOne := fun h => hmk (by rw [h]; exact ⟨1, rfl⟩)
    have hx0' : x' ≠ 0 := fun h => hmk' (by rw [h]; exact ⟨0, rfl⟩)
    have hx1' : x' ≠ zornOne := fun h => hmk' (by rw [h]; exact ⟨1, rfl⟩)
    by_cases hc : zornClsD x = zornClsD x'
    · obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hx hx' hc
      refine ⟨⟨γ, hγ⟩, 1, Subgroup.one_mem _, ?_⟩
      change Multiplicative.ofAdd (γ x) = Multiplicative.ofAdd x' * 1
      rw [mul_one, hγm]
    · have hc' := zornClsD_add_one_eq hK2 hx' hx0' hx1' hx0 hx1 hc
      obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hx (zornOne_add_mem hK2 hx') hc'
      refine ⟨⟨γ, hγ⟩, Multiplicative.ofAdd zornOne, ⟨1, rfl⟩, ?_⟩
      change Multiplicative.ofAdd (γ x) = Multiplicative.ofAdd x' * Multiplicative.ofAdd zornOne
      rw [hγm]
      rfl
  have h := orbits_of_transitive H htrans
  have hcard : Nat.card V = 64 := by
    have h1 := card_eq_of_realizesBy hR
    have h2 : Nat.card ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker = 2 := by
      change Nat.card ↥(zornR K) = 2
      rw [← hK2]
      exact Nat.card_congr
        { toFun := fun x => (Multiplicative.toAdd (α := quasithinZorn K) x.1).1
          invFun := fun c => ⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩
          left_inv := fun x => by
            obtain ⟨x, c, hc⟩ := x
            apply Subtype.ext
            apply Multiplicative.toAdd.injective
            change ((Multiplicative.toAdd x).1, 0, 0, (Multiplicative.toAdd x).1) =
              Multiplicative.toAdd x
            rw [hc]
          right_inv := fun _ => rfl }
    have h3 : Nat.card ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec = 128 := by
      rw [← card_O0 hK2]
      exact Nat.card_congr
        { toFun := fun x => ⟨Multiplicative.toAdd (α := quasithinZorn K) x.1, x.2⟩
          invFun := fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h2, h3] at h1
    omega
  rwa [hcard] at h

theorem orbitG2Weyl : OrbitG2Weyl := by
  intro V _ _ H z hz1 hzH hH
  obtain ⟨K, _, _, hK, hR⟩ := hH
  classical
  have hK2 : Nat.card K = 2 := hK
  obtain ⟨π, β, hR⟩ := (realizes_iff _ H ⊤ ⊥).1 hR
  let f : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Amb → ℕ :=
    fun x => zornClsD (Multiplicative.toAdd (α := quasithinZorn K) x)
  have hker : ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      ∀ k ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker, f (m * k) = f m := by
    intro m _ k hk
    rw [(Subgroup.mem_bot.1 hk : k = 1), mul_one]
  have hact : ∀ γ : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
      ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
        f ((zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).act γ m) = f m := by
    intro γ m _
    exact zornClsD_g2 (derived_le _ γ.2) _
  have htrans : ∀ m ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      ∀ m' ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec, f m = f m' →
        ∃ γ : (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
          ∃ k ∈ (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker,
            (zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).act γ m = m' * k := by
    intro m hm m' hm' h
    obtain ⟨γ, hγ, hγm⟩ := exists_g2Derived_of_cls hK2 hm hm' h
    refine ⟨⟨γ, hγ⟩, 1, Subgroup.one_mem _, ?_⟩
    rw [mul_one]
    change Multiplicative.ofAdd (γ (Multiplicative.toAdd m)) = m'
    rw [hγm]
    rfl
  have hN : ∀ m : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      Nat.card {m' : ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).sec // f m' = f m} =
        if f m < 2 then 63 else 1 := by
    intro m
    have hlt : f m < 4 := by
      change zornClsD _ < 4
      unfold zornClsD
      split_ifs <;> norm_num
    rw [← card_class hK2 (f m) hlt]
    exact Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (α := quasithinZorn K) x.1.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨Multiplicative.ofAdd x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hk1 : Nat.card ↥(zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆).ker = 1 := Subgroup.card_bot
  obtain ⟨z₀, hz₀, hz₀k⟩ := exists_coordOf_eq hR hz1
  have hz₀0 : Multiplicative.toAdd (α := quasithinZorn K) z₀.1 ≠ 0 :=
    fun h => hz₀k (Subgroup.mem_bot.2 (Multiplicative.toAdd.injective h))
  have hz₀1 : Multiplicative.toAdd (α := quasithinZorn K) z₀.1 = zornOne := by
    by_contra hne
    have hc := card_orbitIn_of_classFn f hR hker hact htrans hz₀
    have ho : orbitIn H z = {z} := by
      ext w
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact hzH h hh
      · rintro rfl
        exact ⟨1, H.one_mem, rfl⟩
    have h1 : Nat.card ↑(orbitIn H z) = 1 := by
      rw [ho]
      exact Nat.card_unique
    rw [h1, hk1, hN, ite_eq_left (zornClsD_lt_two hz₀0 hne)] at hc
    norm_num at hc
  refine orbitsMod_of_classFn hR f hker hact htrans z₀ hz₀ {0, 1}
    (fun c => if c < 2 then 63 else 1) [63] (by rw [hk1]; norm_num)
    (fun m hm hmz => ?_) hN (by rw [hk1]; decide) (fun m m' hmS hm'S _ => ?_)
  · have hm0 : Multiplicative.toAdd (α := quasithinZorn K) m.1 ≠ 0 :=
      fun h => hm (Subgroup.mem_bot.2 (Multiplicative.toAdd.injective h))
    have hm1 : Multiplicative.toAdd (α := quasithinZorn K) m.1 ≠ zornOne := by
      intro h
      apply hmz
      have : m = z₀ := Subtype.ext (Multiplicative.toAdd.injective (h.trans hz₀1.symm))
      rw [this, inv_mul_cancel]
      exact Subgroup.one_mem _
    have := zornClsD_lt_two hm0 hm1
    simp only [Finset.mem_insert, Finset.mem_singleton]
    change zornClsD _ = 0 ∨ zornClsD _ = 1
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmS hm'S
    by_cases h : f m = f m'
    · exact Or.inl h
    · right
      have hm'0 : Multiplicative.toAdd (α := quasithinZorn K) m'.1 ≠ 0 := by
        intro h0
        change zornClsD _ = 0 ∨ zornClsD _ = 1 at hm'S
        rw [h0] at hm'S
        simp [zornClsD] at hm'S
      have hm'1 : Multiplicative.toAdd (α := quasithinZorn K) m'.1 ≠ zornOne := by
        intro h1
        change zornClsD _ = 0 ∨ zornClsD _ = 1 at hm'S
        rw [h1] at hm'S
        have : zornOne ≠ (0 : quasithinZorn K) := fun h' => by
          have := congrArg Prod.fst h'
          simp [zornOne] at this
        simp [zornClsD, this] at hm'S
      have hm0 : Multiplicative.toAdd (α := quasithinZorn K) m.1 ≠ 0 := by
        intro h0
        change zornClsD _ = 0 ∨ zornClsD _ = 1 at hmS
        rw [h0] at hmS
        simp [zornClsD] at hmS
      have hm1 : Multiplicative.toAdd (α := quasithinZorn K) m.1 ≠ zornOne := by
        intro h1
        change zornClsD _ = 0 ∨ zornClsD _ = 1 at hmS
        rw [h1] at hmS
        have : zornOne ≠ (0 : quasithinZorn K) := fun h' => by
          have := congrArg Prod.fst h'
          simp [zornOne] at this
        simp [zornClsD, this] at hmS
      have := zornClsD_add_one_eq hK2 m'.2 hm'0 hm'1 hm0 hm1 h
      change zornClsD (Multiplicative.toAdd (α := quasithinZorn K) m.1) =
        zornClsD (Multiplicative.toAdd (α := quasithinZorn K) m'.1 +
          Multiplicative.toAdd (α := quasithinZorn K) z₀.1)
      rw [hz₀1]
      exact this

end CFSG.Quasithin.H13.Orbit
