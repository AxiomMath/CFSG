module

public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Vol2.F134U33Native

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Quasithin

theorem card_u33G
    : Nat.card U33G = 6048 := card_u33Pres

instance
    : Finite U33G := Nat.finite_of_card_ne_zero (by rw [card_u33G]; norm_num)

private theorem card_eq_96
    {H : Subgroup U33G} (hTH : u33Data.T ≤ H) (hne : u33Data.T ≠ H)
    (hle : Nat.card H ≤ 160) : Nat.card H = 96 := by
  have h1 := relIndex_mul_card u33Data.T H
  rw [inf_of_le_left hTH, u33_card_T] at h1
  have h2 := card_mul_index H
  rw [card_u33G] at h2
  have hr : u33Data.T.relIndex H ≠ 1 := by
    intro h
    exact hne (le_antisymm hTH (relIndex_eq_one.1 h))
  have hr5 : u33Data.T.relIndex H ≤ 5 := by omega
  have hdvd : u33Data.T.relIndex H ∣ 189 := by
    refine ⟨H.index, ?_⟩
    have : 32 * (u33Data.T.relIndex H * H.index) = 32 * 189 := by
      rw [← mul_assoc, mul_comm 32, h1, h2]
    omega
  interval_cases h : u33Data.T.relIndex H <;> omega

theorem card_u33_A
    : Nat.card u33Data.A = 96 :=
  card_eq_96 u33Data.T_le_A u33Data.T_ne_A F134.card_u33_A_le

theorem card_u33_B
    : Nat.card u33Data.B = 96 :=
  card_eq_96 u33Data.T_le_B u33Data.T_ne_B F134.card_u33_B_le

theorem index_u33_T
    : u33Data.T.index = 189 := by
  have h := card_mul_index u33Data.T
  rw [card_u33G, u33_card_T] at h
  omega

theorem index_u33_A
    : u33Data.A.index = 63 := by
  have h := card_mul_index u33Data.A
  rw [card_u33G, card_u33_A] at h
  omega

theorem index_u33_B
    : u33Data.B.index = 63 := by
  have h := card_mul_index u33Data.B
  rw [card_u33G, card_u33_B] at h
  omega

private theorem normalizer_eq_self
    {H : Subgroup U33G} (hTH : u33Data.T ≤ H)
    (hidx : H.index = 63) : normalizer (H : Set U33G) = H := by
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  have hHN : H ≤ normalizer (H : Set U33G) := le_normalizer
  have hNtop : normalizer (H : Set U33G) ≠ ⊤ := by
    intro htop
    have hn : H.Normal := normalizer_eq_top_iff.1 htop
    rcases hn.eq_bot_or_eq_top with h | h
    · have hT : u33Data.T = ⊥ := le_bot_iff.1 (by rw [← h]; exact hTH)
      have := u33_card_T
      rw [hT, card_bot] at this
      norm_num at this
    · rw [h, index_top] at hidx
      norm_num at hidx
  have hdvd : (normalizer (H : Set U33G)).index ∣ 63 := hidx ▸ index_dvd_of_le hHN
  have h1 := relIndex_mul_index hHN
  rcases u33Data.lattice _ (hTH.trans hHN) with h | h | h | h
  · rw [h, index_u33_T] at hdvd
    norm_num at hdvd
  · rw [h, index_u33_A, hidx] at h1
    rw [h] at hHN ⊢
    have h2 : H.relIndex u33Data.A = 1 := by omega
    exact le_antisymm (relIndex_eq_one.1 h2) hHN
  · rw [h, index_u33_B, hidx] at h1
    rw [h] at hHN ⊢
    have h2 : H.relIndex u33Data.B = 1 := by omega
    exact le_antisymm (relIndex_eq_one.1 h2) hHN
  · exact absurd h hNtop

theorem normalizer_u33_A
    : normalizer (u33Data.A : Set U33G) = u33Data.A :=
  normalizer_eq_self u33Data.T_le_A index_u33_A

theorem normalizer_u33_B
    : normalizer (u33Data.B : Set U33G) = u33Data.B :=
  normalizer_eq_self u33Data.T_le_B index_u33_B

theorem mem_normalizer_of_map_conj_eq {X : Type*} [Group X] {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    exact this ▸ hy

theorem stab_orbit_of_lattice {X V : Type*} [Group X] [Finite X] [Group V] [Finite V]
    (hV : Nat.card V = 64) (ψ : X →* MulAut V) (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1)
    {S A B : Subgroup X} (hSidx : 63 < S.index)
    (hlat : ∀ H : Subgroup X, S ≤ H → H = S ∨ H = A ∨ H = B ∨ H = ⊤)
    (hA : A.index = 63) (hB : B.index = 63) {v : V} (hv1 : v ≠ 1) (hvS : ∀ s ∈ S, ψ s v = v) :
    ((∀ g, ψ g v = v ↔ g ∈ A) ∨ (∀ g, ψ g v = v ↔ g ∈ B)) ∧
      ∀ w : V, w ≠ 1 → ∃ g, ψ g v = w := by
  classical
  let _ : MulAction X V := MulAction.compHom V ψ
  have hne1 : ∀ (g : X) (v : V), v ≠ 1 → ψ g v ≠ 1 := fun g v hv h =>
    hv ((ψ g).injective (h.trans (map_one (ψ g)).symm))
  have hcard1 : {w : V | w ≠ 1}.ncard = 63 := by
    have h1 : {w : V | w ≠ 1} = Set.univ \ {1} := by
      ext w
      simp
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_univ, hV, Set.ncard_singleton]
  have hSle : S ≤ MulAction.stabilizer X v := fun s hs => hvS s hs
  have hsub : MulAction.orbit X v ⊆ {w : V | w ≠ 1} := by
    rintro _ ⟨g, rfl⟩
    exact hne1 g v hv1
  have hle63 : (MulAction.orbit X v).ncard ≤ 63 := hcard1 ▸ Set.ncard_le_ncard hsub
  have hidx := MulAction.index_stabilizer X v
  have hst : ∀ H : Subgroup X, MulAction.stabilizer X v = H → ∀ g, ψ g v = v ↔ g ∈ H :=
    fun H h g => by rw [← h]; exact Iff.rfl
  have horb : MulAction.orbit X v = {w : V | w ≠ 1} → ∀ w : V, w ≠ 1 → ∃ g, ψ g v = w := by
    intro h w hw
    have hw' : w ∈ MulAction.orbit X v := by rw [h]; exact hw
    obtain ⟨g, hg⟩ := hw'
    exact ⟨g, hg⟩
  rcases hlat _ hSle with h | h | h | h
  · rw [h] at hidx
    omega
  · refine ⟨Or.inl (hst A h), horb (Set.eq_of_subset_of_ncard_le hsub ?_)⟩
    rw [hcard1, ← hidx, h, hA]
  · refine ⟨Or.inr (hst B h), horb (Set.eq_of_subset_of_ncard_le hsub ?_)⟩
    rw [hcard1, ← hidx, h, hB]
  · exfalso
    exact hv1 (hfix v fun g => (show g ∈ MulAction.stabilizer X v from h ▸ mem_top g))

theorem fixed_card_two_of_lattice {X V : Type*} [Group X] [Finite X] [Group V] [Finite V]
    (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 64) (ψ : X →* MulAut V)
    (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1) {S A B : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSidx : 63 < S.index) (hlat : ∀ H : Subgroup X, S ≤ H → H = S ∨ H = A ∨ H = B ∨ H = ⊤)
    (hA : A.index = 63) (hB : B.index = 63) (hAn : normalizer (A : Set X) = A)
    (hBn : normalizer (B : Set X) = B) :
    Nat.card {v : V // ∀ s ∈ S, ψ s v = v} = 2 := by
  classical
  let _ : MulAction X V := MulAction.compHom V ψ
  have hsmul : ∀ (g : X) (v : V), g • v = ψ g v := fun _ _ => rfl
  have hne1 : ∀ (g : X) (v : V), v ≠ 1 → ψ g v ≠ 1 := fun g v hv h =>
    hv ((ψ g).injective (h.trans (map_one (ψ g)).symm))
  have hcard1 : {w : V | w ≠ 1}.ncard = 63 := by
    have h1 : {w : V | w ≠ 1} = Set.univ \ {1} := by
      ext w
      simp
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_univ, hV, Set.ncard_singleton]
  have hstab : ∀ v : V, v ≠ 1 → (∀ s ∈ S, ψ s v = v) →
      (MulAction.stabilizer X v = A ∨ MulAction.stabilizer X v = B) ∧
        MulAction.orbit X v = {w : V | w ≠ 1} := by
    intro v hv1 hvS
    have hSle : S ≤ MulAction.stabilizer X v := fun s hs => hvS s hs
    have hsub : MulAction.orbit X v ⊆ {w : V | w ≠ 1} := by
      rintro _ ⟨g, rfl⟩
      exact hne1 g v hv1
    have hle63 : (MulAction.orbit X v).ncard ≤ 63 := hcard1 ▸ Set.ncard_le_ncard hsub
    have hidx := MulAction.index_stabilizer X v
    rcases hlat _ hSle with h | h | h | h
    · rw [h] at hidx
      omega
    · refine ⟨Or.inl h, Set.eq_of_subset_of_ncard_le hsub ?_⟩
      rw [hcard1, ← hidx, h, hA]
    · refine ⟨Or.inr h, Set.eq_of_subset_of_ncard_le hsub ?_⟩
      rw [hcard1, ← hidx, h, hB]
    · exfalso
      exact hv1 (hfix v fun g => (show g ∈ MulAction.stabilizer X v from h ▸ mem_top g))
  have hsame : ∀ p q : V, p ≠ 1 → q ≠ 1 → (∀ s ∈ S, ψ s p = p) → (∀ s ∈ S, ψ s q = q) →
      MulAction.stabilizer X p = MulAction.stabilizer X q → p = q := by
    intro p q hp1 hq1 hpS hqS hpq
    obtain ⟨hHp, horb⟩ := hstab p hp1 hpS
    have hq : q ∈ MulAction.orbit X p := by rw [horb]; exact hq1
    obtain ⟨g, rfl⟩ := hq
    have h1 := MulAction.stabilizer_smul_eq_stabilizer_map_conj g p
    rw [← hpq] at h1
    have hgN : g ∈ normalizer ((MulAction.stabilizer X p : Subgroup X) : Set X) :=
      mem_normalizer_of_map_conj_eq h1.symm
    have hg : g ∈ MulAction.stabilizer X p := by
      rcases hHp with h | h
      · rw [h, hAn] at hgN
        rwa [h]
      · rw [h, hBn] at hgN
        rwa [h]
    exact (hg : g • p = p).symm
  have huniq : ∀ v w : V, v ≠ 1 → w ≠ 1 → (∀ s ∈ S, ψ s v = v) → (∀ s ∈ S, ψ s w = w) →
      v = w := by
    intro v w hv1 hw1 hvS hwS
    by_contra hvw
    have huS : ∀ s ∈ S, ψ s (v * w) = v * w := fun s hs => by rw [map_mul, hvS s hs, hwS s hs]
    have hinv : ∀ x : V, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hV2 x)
    have hu1 : v * w ≠ 1 := fun h => hvw (by rw [← hinv v]; exact (inv_eq_of_mul_eq_one_right h))
    have huv : v * w ≠ v := fun h => hw1 (by simpa using h)
    have huw : v * w ≠ w := fun h => hv1 (by simpa using h)
    rcases (hstab v hv1 hvS).1 with hv | hv <;> rcases (hstab w hw1 hwS).1 with hw | hw <;>
      rcases (hstab (v * w) hu1 huS).1 with hu | hu
    all_goals first
      | exact hvw (hsame v w hv1 hw1 hvS hwS (hv.trans hw.symm))
      | exact huv (hsame _ _ hu1 hv1 huS hvS (hu.trans hv.symm))
      | exact huw (hsame _ _ hu1 hw1 huS hwS (hu.trans hw.symm))
  have hmod : Nat.card V ≡ Nat.card (MulAction.fixedPoints S V) [MOD 2] :=
    hS2.card_modEq_card_fixedPoints V
  have hfp : ∀ v : V, v ∈ MulAction.fixedPoints S V ↔ ∀ s ∈ S, ψ s v = v := by
    intro v
    constructor
    · intro h s hs
      exact h ⟨s, hs⟩
    · intro h s
      exact h s s.2
  have hcardeq : Nat.card (MulAction.fixedPoints S V) = Nat.card {v : V // ∀ s ∈ S, ψ s v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfp)
  rw [hcardeq, hV] at hmod
  have hpos : 1 ≤ Nat.card {v : V // ∀ s ∈ S, ψ s v = v} :=
    Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨1, fun s _ => map_one _⟩⟩, inferInstance⟩)
  have h2 : 2 ≤ Nat.card {v : V // ∀ s ∈ S, ψ s v = v} := by
    have := Nat.ModEq.symm hmod
    unfold Nat.ModEq at this
    omega
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ : ∃ x : {v : V // ∀ s ∈ S, ψ s v = v}, x ≠ ⟨1, fun s _ => map_one _⟩ :=
    by
    by_contra h
    push Not at h
    have : Nat.card {v : V // ∀ s ∈ S, ψ s v = v} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have hset : {v : V | ∀ s ∈ S, ψ s v = v} = {1, v₀} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hv
      by_cases h1 : v = 1
      · exact Or.inl h1
      · exact Or.inr (huniq v v₀ h1 hv₀1' hv hv₀)
    · rintro (rfl | rfl)
      · exact fun s _ => map_one _
      · exact hv₀
  calc Nat.card {v : V // ∀ s ∈ S, ψ s v = v}
      = Nat.card ({v : V | ∀ s ∈ S, ψ s v = v} : Set V) := rfl
    _ = Nat.card ({1, v₀} : Set V) := by rw [hset]
    _ = 2 := by
        rw [Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hv₀1')]

theorem u33_sylow_fixed_card_two
    {V : Type*} [Group V] [Finite V]
    (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 64) (ψ : U33G →* MulAut V)
    (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1) (S : Sylow 2 U33G) :
    Nat.card {v : V // ∀ s ∈ S, ψ s v = v} = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T₀ : Sylow 2 U33G := u33_syl.1.toSylow u33_syl.2
  have hT : Nat.card {v : V // ∀ s ∈ (T₀ : Subgroup U33G), ψ s v = v} = 2 :=
    fixed_card_two_of_lattice hV2 hV ψ hfix u33_syl.1
      (by show 63 < u33Data.T.index; rw [index_u33_T]; norm_num)
      u33Data.lattice index_u33_A index_u33_B normalizer_u33_A normalizer_u33_B
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U33G T₀ S
  subst hg
  have hmulv : ∀ (a b : U33G) (v : V), ψ a (ψ b v) = ψ (a * b) v := fun a b v => by
    rw [map_mul, MulAut.mul_apply]
  have honev : ∀ v : V, ψ 1 v = v := fun v => by rw [map_one, MulAut.one_apply]
  refine (Nat.card_congr ?_).trans hT
  refine
    { toFun := fun v => ⟨ψ g⁻¹ v, fun s hs => ?_⟩
      invFun := fun v => ⟨ψ g v, fun s hs => ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun v => Subtype.ext ?_ }
  · have hs' : g * s * g⁻¹ ∈ ((g • T₀ : Sylow 2 U33G) : Subgroup U33G) := by
      rw [Sylow.coe_subgroup_smul]
      have := Subgroup.smul_mem_pointwise_smul s (MulAut.conj g) (T₀ : Subgroup U33G) hs
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have h1 := v.2 _ hs'
    calc ψ s (ψ g⁻¹ v) = ψ g⁻¹ (ψ (g * s * g⁻¹) v) := by
          rw [hmulv, hmulv, show g⁻¹ * (g * s * g⁻¹) = s * g⁻¹ by group]
      _ = ψ g⁻¹ v := by rw [h1]
  · have hs2 : s ∈ ((g • T₀ : Sylow 2 U33G) : Subgroup U33G) := hs
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hs2
    have hs' : g⁻¹ * s * g ∈ (T₀ : Subgroup U33G) := by
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs2
    have h1 := v.2 _ hs'
    calc ψ s (ψ g v) = ψ g (ψ (g⁻¹ * s * g) v) := by
          rw [hmulv, hmulv, show g * (g⁻¹ * s * g) = s * g by group]
      _ = ψ g v := by rw [h1]
  · change ψ g (ψ g⁻¹ v) = v
    rw [hmulv, mul_inv_cancel, honev]
  · change ψ g⁻¹ (ψ g v) = v
    rw [hmulv, inv_mul_cancel, honev]

theorem u33_stab_orbit
    {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 64)
    (ψ : U33G →* MulAut V) (hfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1) {v : V} (hv1 : v ≠ 1)
    (hvT : ∀ s ∈ u33Data.T, ψ s v = v) :
    ((∀ g, ψ g v = v ↔ g ∈ u33Data.A) ∨ (∀ g, ψ g v = v ↔ g ∈ u33Data.B)) ∧
      ∀ w : V, w ≠ 1 → ∃ g, ψ g v = w :=
  stab_orbit_of_lattice hV ψ hfix (by rw [index_u33_T]; norm_num) u33Data.lattice index_u33_A
    index_u33_B hv1 hvT

end CFSG.Quasithin.H13.U3
