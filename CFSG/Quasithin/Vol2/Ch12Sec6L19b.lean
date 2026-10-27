module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19a Equiv
open scoped IsMulCommutative

namespace S126L19b

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem pow_three_of_mem (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {x : G} (hxL : x ∈ L) (hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G)) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) : x ^ 3 = 1 := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨σ, -, hσ⟩ := exists_actsAs_of_mem_L F hxL (hLV hxL)
  have hσm := pow_eq_one_of_actsAs hσ (hLV hxL) hxm
  have h3 : (σ : Perm (Fin 8)) ^ 3 = 1 :=
    pow_three_of_odd (pow_24 (blocks_of_mem_V1 F hx1 hσ)) hm hσm
  have hx3 : ActsAs F (x ^ 3) 1 := by
    have := hσ.pow (hLV hxL) 3
    rwa [h3] at this
  have hx3C := mem_centralizer_of_mem_L F (L.pow_mem hxL 3) (Subgroup.pow_mem _ (hLV hxL) 3) hx3
  obtain ⟨k, hk⟩ := isPGroup_ker h1222 hH ⟨⟨x ^ 3, L.pow_mem hxL 3⟩, hx3C⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg
      (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) => ((z : ↥L) : G)) hk
    simpa using this
  have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have h1 : orderOf (x ^ 3) ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
  rw [hc, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem L1_eq (F : Frame126 T L V) : Li L F.V1 = Subgroup.closure
    {x | x ∈ L ⊓ Subgroup.normalizer (F.V1 : Set G) ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} := rfl

theorem conj_L1_le_L (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {g : G}
    (hg : (Li L F.V1).map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (L : Set G)) :
    (Li L F.V1).map (MulAut.conj g).toMonoidHom ≤ L := by
  have h5 := part5 h1222 h1228 hH
  refine le_trans ?_ h5.le
  rw [Subgroup.map_le_iff_le_comap, L1_eq F]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨⟨hxL, hx1⟩, m, hm, hxm⟩ := hx
  have h3 := pow_three_of_mem h1222 F hH hxL hx1 hm hxm
  have hxL1 : x ∈ Li L F.V1 := Subgroup.subset_closure ⟨⟨hxL, hx1⟩, m, hm, hxm⟩
  refine Subgroup.subset_closure ⟨hg ⟨x, hxL1, rfl⟩, 1, ?_⟩
  change ((MulAut.conj g) x) ^ 3 ^ 1 = 1
  rw [pow_one, ← map_pow, h3, map_one]

@[expose] noncomputable def L1bar (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Subgroup ↥(alternatingGroup (Fin 8)) :=
  ((Li L F.V1).subgroupOf L).map (psi F hH)

omit [Finite G] in
theorem L1_le_L (F : Frame126 T L V) : Li L F.V1 ≤ L :=
  (oTwoRes_le _).trans inf_le_left

omit [Finite G] in
theorem L1_le_normalizer (F : Frame126 T L V) :
    Li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) :=
  (oTwoRes_le _).trans inf_le_right

theorem blocks_of_mem_L1bar (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {σ : ↥(alternatingGroup (Fin 8))} (hσ : σ ∈ L1bar F hH) :
    (∀ i : Fin 8, (i.val < 4 ↔ ((σ : Perm (Fin 8)) i).val < 4)) ∨
      (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ ((σ : Perm (Fin 8)) i).val)) := by
  obtain ⟨l, hl, rfl⟩ := hσ
  exact blocks_of_mem_V1 F (L1_le_normalizer F (Subgroup.mem_subgroupOf.1 hl)) (actsAs_psi F hH l)

theorem not_five_dvd_L1bar (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ¬ 5 ∣ Nat.card (L1bar F hH) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := L1bar F hH) 5 h5
  have h24 := pow_24 (blocks_of_mem_L1bar F hH σ.2)
  have hσ5 : ((σ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) ^ 5 = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hσ] at this
    have := congrArg (fun y : L1bar F hH => ((y : ↥(alternatingGroup (Fin 8))) :
      Perm (Fin 8))) this
    simpa using this
  have h1 := eq_one_of_pow_five h24 hσ5
  have h2 : σ = 1 := Subtype.ext (Subtype.ext h1)
  rw [h2, orderOf_one] at hσ
  exact absurd hσ (by norm_num)

theorem c1_mul_c2 : c1 * c2 = c2 * c1 := by
  decide

theorem mem_zpowers_c (c : Perm (Fin 8)) (hc : c ^ 3 = 1) (hc1 : c ≠ 1) {x : Perm (Fin 8)}
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c ∨ x = c ^ 2 := by
  classical
  have ho : orderOf c = 3 := orderOf_eq_prime hc hc1
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  interval_cases k <;> simp

theorem c1_ne_one : c1 ≠ 1 := by
  decide

theorem c2_ne_one : c2 ≠ 1 := by
  decide

theorem zpowers_inf : Subgroup.zpowers c1 ⊓ Subgroup.zpowers c2 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases mem_zpowers_c c1 c1_pow_three c1_ne_one hx.1 with h | h | h <;>
    rcases mem_zpowers_c c2 c2_pow_three c2_ne_one hx.2 with h' | h' | h' <;>
    first
    | exact h ▸ Subgroup.one_mem _
    | exact absurd (h.symm.trans h') (by decide)

theorem card_E9 : Nat.card ↥(Subgroup.zpowers c1 ⊔ Subgroup.zpowers c2) = 9 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers c1, ∀ b ∈ Subgroup.zpowers c2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (show Commute c1 c2 from c1_mul_c2) i j)).eq
  have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [zpowers_inf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime c1_pow_three c1_ne_one, orderOf_eq_prime c2_pow_three c2_ne_one] at h1
  exact h1

theorem nine_dvd_L1bar (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    9 ∣ Nat.card (L1bar F hH) := by
  have hmem : ∀ c : Perm (Fin 8), c ∈ alternatingGroup (Fin 8) → c ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) →
      c ∈ (L1bar F hH).map (alternatingGroup (Fin 8)).subtype := by
    intro c hc hc3 hcb
    obtain ⟨l, hlL1, hlV, hl⟩ := exists_mem_L1 F hc hc3 hcb
    have hlL : l ∈ L := L1_le_L F hlL1
    have h1 := (actsAs_psi F hH ⟨l, hlL⟩).unique hl hlV
    exact ⟨psi F hH ⟨l, hlL⟩, ⟨⟨l, hlL⟩, hlL1, rfl⟩, h1⟩
  have hle : Subgroup.zpowers c1 ⊔ Subgroup.zpowers c2 ≤
      (L1bar F hH).map (alternatingGroup (Fin 8)).subtype :=
    sup_le (Subgroup.zpowers_le.2 (hmem c1 c1_mem c1_pow_three c1_block))
      (Subgroup.zpowers_le.2 (hmem c2 c2_mem c2_pow_three c2_block))
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_E9, ← Nat.card_congr (Subgroup.equivMapOfInjective _ _
    Subtype.val_injective).toEquiv] at h1
  exact h1

omit [IsMulCommutative ↥V] in
theorem coprime_pow_two {a n : ℕ} (hn : Odd n) : Nat.Coprime n (2 ^ a) :=
  Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hn)

theorem card_L1 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    9 ∣ Nat.card (Li L F.V1) ∧ ¬ 5 ∣ Nat.card (Li L F.V1) := by
  have hc := card_eq F hH (L1_le_L F)
  obtain ⟨a, ha⟩ := card_inf_eq_pow h1222 hH (L1_le_L F)
  change Nat.card (Li L F.V1) = Nat.card (L1bar F hH) * _ at hc
  rw [ha] at hc
  rw [hc]
  refine ⟨Dvd.dvd.mul_right (nine_dvd_L1bar F hH) _, fun h5 => ?_⟩
  have hc5 : Nat.Coprime 5 (2 ^ a) := coprime_pow_two (by decide)
  exact not_five_dvd_L1bar F hH (hc5.dvd_of_dvd_mul_right h5)

omit [Finite G] [IsMulCommutative ↥V] in
theorem normalizer_inf_le_sup (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  have hA : g ∈ Subgroup.normalizer (A : Set G) := hg.1
  have hB : g ∈ Subgroup.normalizer (B : Set G) := hg.2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] [IsMulCommutative ↥V] in
theorem normalizer_inf_le_inf (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  have hA : g ∈ Subgroup.normalizer (A : Set G) := hg.1
  have hB : g ∈ Subgroup.normalizer (B : Set G) := hg.2
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun h => ⟨(hA x).1 h.1, (hB x).1 h.2⟩, fun h => ⟨(hA x).2 h.1, (hB x).2 h.2⟩⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem normalizer_le_normalizer_oTwoRes' (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoRes X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ y ∈ oTwoRes X, g * y * g⁻¹ ∈ oTwoRes X := by
    intro g hg y hy
    have hle : oTwoRes X ≤ (oTwoRes X).comap (MulAut.conj g).toMonoidHom := by
      rw [oTwoRes, Subgroup.closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx, m, hm, ?_⟩
      change (g * x * g⁻¹) ^ m = 1
      rw [conj_pow, hxm]
      group
    exact hle hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

theorem dAct_e0123' {σ : Perm (Fin 8)}
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val))) :
    dAct σ e0123 = e0123 := by
  rw [e0123, dAct_mk]
  rcases hb with h | h
  · congr 1
    exact Subtype.ext (by rw [coreAct_coe]; exact permAct_eset h)
  · rw [mk_eq_iff]
    right
    rw [coreAct_coe]
    exact permAct_eset_swap h

theorem blocks_inv {σ : Perm (Fin 8)}
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val))) :
    (∀ i : Fin 8, (i.val < 4 ↔ (σ⁻¹ i).val < 4)) ∨
      (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ⁻¹ i).val)) := by
  rcases hb with h | h
  · left
    intro i
    have := h (σ⁻¹ i)
    rw [S126Ex.perm_apply_inv] at this
    exact this.symm
  · right
    intro i
    have := h (σ⁻¹ i)
    rw [S126Ex.perm_apply_inv] at this
    omega

omit [Finite G] in
theorem conj_mem_V1' (F : Frame126 T L V) {g : G} {σ : Perm (Fin 8)}
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hg : ActsAs F g σ)
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)))
    {x : G} (hx : x ∈ F.V1) : g * x * g⁻¹ ∈ F.V1 := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨⟨g * v * g⁻¹, conj_mem hgN v⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap] at hv ⊢
  rw [hg v _ rfl]
  rcases mem_W1 hv with h | h
  · rw [h, map_one]
    exact Subgroup.one_mem _
  · rw [h, dAct_e0123' hb]
    exact e0123_mem_W1

omit [Finite G] in
theorem mem_normalizer_V1' (F : Frame126 T L V) {g : G} {σ : Perm (Fin 8)}
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hg : ActsAs F g σ)
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val))) :
    g ∈ Subgroup.normalizer (F.V1 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_V1' F hgN hg hb, fun hx => ?_⟩
  have h := conj_mem_V1' F (Subgroup.inv_mem _ hgN) hg.inv (blocks_inv hb) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

variable {F : Frame126 T L V} (E : Frame126E F)

@[expose] noncomputable def v4 : ↥V := E.γ.symm ⟨eset {0, 1, 2, 3}, e0123_mem⟩

@[expose] noncomputable def z0 : ↥V := E.γ.symm eOm

omit [Finite G] in
theorem gamma_v4 : E.γ (v4 E) = ⟨eset {0, 1, 2, 3}, e0123_mem⟩ := by
  rw [v4, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem gamma_z0 : E.γ (z0 E) = eOm := by
  rw [z0, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem beta_v4 : F.β (v4 E) = e0123 := by
  rw [E.β_eq, gamma_v4]
  rfl

omit [Finite G] in
theorem beta_z0 : F.β (z0 E) = 1 := by
  rw [E.β_eq, gamma_z0]
  exact (mk_eq_one_iff _).2 (Or.inr rfl)

omit [Finite G] in
theorem z0_mem : ((z0 E : ↥V) : G) ∈ Subgroup.centralizer (L : Set G) :=
  (F.β_ker _).1 (beta_z0 E)

omit [Finite G] in
theorem conj_v4 {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) {σ : Perm (Fin 8)} (hσ : ActsAs F x σ)
    (hb : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) :
    x * ((v4 E : ↥V) : G) * x⁻¹ = v4 E := by
  have h := E.act x hxL hxV σ hσ (v4 E) ⟨_, conj_mem hxV (v4 E)⟩ rfl
  have h2 : coreAct 8 σ (E.γ (v4 E)) = E.γ (v4 E) := by
    rw [gamma_v4]
    exact Subtype.ext (by rw [coreAct_coe]; exact permAct_eset hb)
  rw [h2] at h
  exact congrArg Subtype.val (E.γ.injective h)

omit [Finite G] in
theorem conj_v4_swap {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) {σ : Perm (Fin 8)} (hσ : ActsAs F x σ)
    (hb : ∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)) :
    x * ((v4 E : ↥V) : G) * x⁻¹ = ((v4 E * z0 E : ↥V) : G) := by
  have h := E.act x hxL hxV σ hσ (v4 E) ⟨_, conj_mem hxV (v4 E)⟩ rfl
  have h2 : coreAct 8 σ (E.γ (v4 E)) = E.γ (v4 E * z0 E) := by
    rw [map_mul, gamma_v4, gamma_z0]
    exact Subtype.ext (by rw [coreAct_coe]; exact permAct_eset_swap hb)
  rw [h2] at h
  exact congrArg Subtype.val (E.γ.injective h)

theorem L1_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    Li L F.V1 ≤ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  rw [L1_eq F]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨⟨hxL, hx1⟩, m, hm, hxm⟩ := hx
  have h3 := pow_three_of_mem h1222 F hH hxL hx1 hm hxm
  have hσ := actsAs_psi F hH ⟨x, hxL⟩
  set σ : Perm (Fin 8) := (psi F hH ⟨x, hxL⟩ : Perm (Fin 8)) with hσdef
  have hσ3 : σ ^ 3 = 1 := pow_eq_one_of_actsAs hσ (hLV hxL) h3
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hxL
  rcases blocks_of_mem_V1 F hx1 hσ with hb | hb
  · have h1 := conj_v4 E hxN (hLV hxL) hσ hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc x * ((v4 E : ↥V) : G) = x * ((v4 E : ↥V) : G) * x⁻¹ * x := by group
      _ = ((v4 E : ↥V) : G) * x := by rw [h1]
  · exfalso
    have h0 : (σ (σ (σ 0))).val ≥ 4 := by
      have e1 := hb 0
      have e2 := hb (σ 0)
      have e3 := hb (σ (σ 0))
      simp only [Fin.val_zero] at e1
      omega
    have : (σ ^ 3) 0 = σ (σ (σ 0)) := by
      rw [pow_succ, pow_succ, pow_one, Perm.mul_apply, Perm.mul_apply]
    rw [hσ3, Perm.one_apply] at this
    rw [← this] at h0
    exact absurd h0 (by decide)

theorem tf_blocks : ∀ u v : Fin 4, ∀ i : Fin 8, (i.val < 4 ↔ (tf u v i).val < 4) := by
  decide

theorem R1_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    Ri T L F.V1 ≤ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  intro r hr
  have hrT := hR1T hr
  obtain ⟨σ, -, hσ⟩ := actsAs_of_mem_T F hrT
  obtain ⟨u, v, huv⟩ := mem_E16 F hTV hR1T hr hσ
  have hb : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4) := by
    intro i
    rw [huv, tau_apply]
    exact tf_blocks u v i
  have h1 := conj_v4 E (hyp.normalizes hrT) (hTV hrT) hσ hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc r * ((v4 E : ↥V) : G) = r * ((v4 E : ↥V) : G) * r⁻¹ * r := by group
    _ = ((v4 E : ↥V) : G) * r := by rw [h1]

section T4

variable (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
  (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)

omit [IsMulCommutative ↥V] in
include h1222 hH in
theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (V : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  exact (hall V hyp.irrPlus).1.2.1

include h1222 hH in
theorem T_le_normalizer_V1 : T ≤ Subgroup.normalizer (F.V1 : Set G) := by
  intro t ht
  obtain ⟨σ, hσP, hσ⟩ := actsAs_of_mem_T F ht
  exact mem_normalizer_V1' F (T_le_normalizer_V h1222 hH ht) hσ (blocks_of_presPart hσP)

include h1222 hH in
theorem T_le_normalizer_L1 : T ≤ Subgroup.normalizer (Li L F.V1 : Set G) := fun _ ht =>
  normalizer_le_normalizer_oTwoRes' _ (normalizer_inf_le_inf L
    (Subgroup.normalizer (F.V1 : Set G)) ⟨hH.hyp.normalizes ht,
      Subgroup.le_normalizer (T_le_normalizer_V1 h1222 hH ht)⟩)

include h1222 hH in
theorem T_conj {t : G} (ht : t ∈ T) :
    t * ((v4 E : ↥V) : G) * t⁻¹ = v4 E ∨
      t * ((v4 E : ↥V) : G) * t⁻¹ = ((v4 E * z0 E : ↥V) : G) := by
  obtain ⟨σ, hσP, hσ⟩ := actsAs_of_mem_T F ht
  rcases blocks_of_presPart hσP with hb | hb
  · exact Or.inl (conj_v4 E (hH.hyp.normalizes ht) (T_le_normalizer_V h1222 hH ht) hσ hb)
  · exact Or.inr (conj_v4_swap E (hH.hyp.normalizes ht) (T_le_normalizer_V h1222 hH ht) hσ hb)

include h1222 hH hZ in
theorem z0_comm {t : G} (ht : t ∈ T) : t * ((z0 E : ↥V) : G) = z0 E * t := by
  have h := (part2 h1222 hH hZ).2
  have hz : ((z0 E : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨(z0 E).2, z0_mem E⟩
  rw [h] at hz
  exact (Subgroup.mem_centralizer_iff.1 hz.2 t ht)

include h1222 hH hZ in
theorem T_le_normalizer_T4 :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) :
      Subgroup G) : Set G) := by
  have hz : ∀ t ∈ T, t * ((z0 E : ↥V) : G) = z0 E * t := fun t ht => z0_comm E h1222 hH hZ ht
  have key : ∀ t ∈ T, ∀ s ∈ T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G),
      t * s * t⁻¹ ∈ T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) := by
    intro t ht s hs
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsv := Subgroup.mem_centralizer_singleton_iff.1 hs.2
    have hs' : s * (t⁻¹ * (v4 E : G) * t) = (t⁻¹ * (v4 E : G) * t) * s := by
      rcases T_conj E h1222 hH (T.inv_mem ht) with h | h
      · rw [show t⁻¹ * ((v4 E : ↥V) : G) * t = t⁻¹ * ((v4 E : ↥V) : G) * t⁻¹⁻¹ by group, h]
        exact hsv
      · rw [show t⁻¹ * ((v4 E : ↥V) : G) * t = t⁻¹ * ((v4 E : ↥V) : G) * t⁻¹⁻¹ by group, h]
        have hzs := hz s hs.1
        change s * (((v4 E : ↥V) : G) * ((z0 E : ↥V) : G)) =
          (((v4 E : ↥V) : G) * ((z0 E : ↥V) : G)) * s
        rw [← mul_assoc, hsv, mul_assoc, hzs, mul_assoc]
    calc t * s * t⁻¹ * ((v4 E : ↥V) : G) = t * (s * (t⁻¹ * (v4 E : G) * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * (v4 E : G) * t) * s) * t⁻¹ := by rw [hs']
      _ = ((v4 E : ↥V) : G) * (t * s * t⁻¹) := by group
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key t ht s, fun h => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ h
  rwa [show t⁻¹ * (t * s * t⁻¹) * t⁻¹⁻¹ = s by group] at this

include h1222 hH hZ in
theorem relIndex_T4 :
    (T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G)).relIndex T = 2 := by
  have hz : ∀ t ∈ T, t * ((z0 E : ↥V) : G) = z0 E * t := fun t ht => z0_comm E h1222 hH hZ ht
  have hmem : ∀ b ∈ T, b ∈ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) ↔
      b * ((v4 E : ↥V) : G) * b⁻¹ = v4 E := by
    intro b _
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc b * ((v4 E : ↥V) : G) = b * ((v4 E : ↥V) : G) * b⁻¹ * b := by group
        _ = ((v4 E : ↥V) : G) * b := by rw [h]
  obtain ⟨t₀, ht₀, ht₀v⟩ : ∃ t₀ ∈ T, t₀ * ((v4 E : ↥V) : G) * t₀⁻¹ ≠ v4 E := by
    by_contra hc
    push Not at hc
    have hvT : ((v4 E : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
      refine ⟨(v4 E).2, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
      calc t * ((v4 E : ↥V) : G) = t * ((v4 E : ↥V) : G) * t⁻¹ * t := by group
        _ = ((v4 E : ↥V) : G) * t := by rw [hc t ht]
    rw [← (part2 h1222 hH hZ).2] at hvT
    have h1 := (F.β_ker (v4 E)).2 hvT.2
    rw [beta_v4] at h1
    exact e0123_ne_one h1
  have ht₀z : t₀ * ((v4 E : ↥V) : G) * t₀⁻¹ = ((v4 E * z0 E : ↥V) : G) :=
    (T_conj E h1222 hH ht₀).resolve_left ht₀v
  have hzz : ((z0 E : ↥V) : G) * ((z0 E : ↥V) : G) = 1 := by
    have h1 : z0 E * z0 E = 1 := by
      apply E.γ.injective
      rw [map_mul, gamma_z0, eOm_mul_self, map_one]
    exact congrArg Subtype.val h1
  have hvz : ((v4 E * z0 E : ↥V) : G) ≠ v4 E := by
    intro h
    apply eOm_ne_one
    have h1 : z0 E = 1 := by
      have h2 : v4 E * z0 E = v4 E := Subtype.ext h
      calc z0 E = (v4 E)⁻¹ * (v4 E * z0 E) := by group
        _ = 1 := by rw [h2, inv_mul_cancel]
    rw [← gamma_z0 E, h1, map_one]
  show ((T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G)).subgroupOf T).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t₀, ht₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbt : (b : G) * t₀ ∈ T := T.mul_mem b.2 ht₀
  rw [hmem _ hbt, hmem _ b.2]
  have e1 : (b : G) * t₀ * (v4 E : G) * ((b : G) * t₀)⁻¹ =
      (b : G) * (v4 E : G) * (b : G)⁻¹ * (z0 E : G) := by
    have hbz : (b : G) * (z0 E : G) * (b : G)⁻¹ = z0 E := by
      rw [hz b b.2, mul_inv_cancel_right]
    calc (b : G) * t₀ * (v4 E : G) * ((b : G) * t₀)⁻¹
        = (b : G) * (t₀ * (v4 E : G) * t₀⁻¹) * (b : G)⁻¹ := by group
      _ = (b : G) * ((v4 E : G) * (z0 E : G)) * (b : G)⁻¹ := by rw [ht₀z]; rfl
      _ = (b : G) * (v4 E : G) * (b : G)⁻¹ * ((b : G) * (z0 E : G) * (b : G)⁻¹) := by group
      _ = (b : G) * (v4 E : G) * (b : G)⁻¹ * (z0 E : G) := by rw [hbz]
  rw [e1]
  have hvz' : ((v4 E : ↥V) : G) * ((z0 E : ↥V) : G) ≠ v4 E := hvz
  rcases T_conj E h1222 hH b.2 with h | h
  · rw [h]
    exact Or.inr ⟨⟨b.2, rfl⟩, fun h' => hvz' h'.2⟩
  · have h2 : ((v4 E * z0 E : ↥V) : G) * ((z0 E : ↥V) : G) = v4 E := by
      change ((v4 E : ↥V) : G) * ((z0 E : ↥V) : G) * ((z0 E : ↥V) : G) = v4 E
      rw [mul_assoc, hzz, mul_one]
    rw [h, h2]
    exact Or.inl ⟨⟨hbt, rfl⟩, fun h' => hvz h'.2⟩

end T4

section R1

variable (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
  (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)

include h1222 hH hZ in
theorem R1_eq : Ri T L F.V1 = pCoreOf 2 (Li L F.V1 ⊔
    (T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hR1T4 : Ri T L F.V1 ≤ T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) :=
    le_inf hR1T (R1_le E h1222 hH)
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR1T4.trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_left inf_le_left _).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left inf_le_left _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    refine le_trans ?_ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => ?_
    exact normalizer_inf_le_sup _ _ ⟨T_le_normalizer_L1 h1222 hH ht,
      T_le_normalizer_T4 E h1222 hH hZ ht⟩

end R1

end S126L19b

end CFSG.Quasithin.H13
