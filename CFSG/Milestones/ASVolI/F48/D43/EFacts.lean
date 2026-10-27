module

public import Certificates.Certificate7810

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

section Three

variable {G : Type*} [Group G]

theorem burnsideF48dE_mem_sup_iff {H : Subgroup G} {φ : G} (h3 : φ ^ 3 = 1)
    (hn : φ ∈ Subgroup.normalizer (H : Set G)) (z : G) :
    z ∈ H ⊔ Subgroup.zpowers φ ↔ ∃ e < 3, ∃ x ∈ H, z = x * φ ^ e := by
  have hle : Subgroup.zpowers φ ≤ Subgroup.normalizer (H : Set G) := Subgroup.zpowers_le.2 hn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H _ hle, Set.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h3' : φ ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact h3
    have hk : φ ^ k = φ ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
      rw [zpow_add, zpow_mul, h3', one_zpow, mul_one]
    have hnn : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    refine ⟨(k % 3).toNat, by omega, x, hx, ?_⟩
    rw [hk, ← zpow_natCast, Int.toNat_of_nonneg hnn]
  · rintro ⟨e, -, x, hx, rfl⟩
    exact ⟨x, hx, φ ^ e, Subgroup.npow_mem_zpowers φ e, rfl⟩

theorem burnsideF48dE_normal_sup {H : Subgroup G} {φ : G}
    (hn : φ ∈ Subgroup.normalizer (H : Set G)) :
    (H.subgroupOf (H ⊔ Subgroup.zpowers φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hn)

theorem burnsideF48dE_pow_not_mem {A : Subgroup G} {φ : G} (h3 : φ ^ 3 = 1) (hφA : φ ∉ A)
    {n : ℕ} (hn : n % 3 ≠ 0) : φ ^ n ∉ A := by
  have hmod : φ ^ n = φ ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3]
    rw [pow_add, pow_mul, h3, one_pow, mul_one]
  rw [hmod]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  intro h
  rcases (show n % 3 = 1 ∨ n % 3 = 2 by omega) with h1 | h2
  · rw [h1, pow_one] at h
    exact hφA h
  · rw [h2] at h
    apply hφA
    have e : φ = (φ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [e]
    exact A.pow_mem h 2

theorem burnsideF48dE_card_three {A H : Subgroup G} {φ : G} (hAH : A ≤ H) (hφ : φ ∈ H)
    (h3 : φ ^ 3 = 1) (hφA : φ ∉ A) (hdec : ∀ z ∈ H, ∃ e < 3, ∃ x ∈ A, z = x * φ ^ e) :
    Nat.card ↥H = 3 * Nat.card ↥A := by
  let f : ↥A × Fin 3 → ↥H := fun p =>
    ⟨(p.1 : G) * φ ^ (p.2 : ℕ), H.mul_mem (hAH p.1.2) (H.pow_mem hφ _)⟩
  have hinv : ∀ e : ℕ, (φ ^ e)⁻¹ = φ ^ (2 * e) := by
    intro e
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show e + 2 * e = 3 * e by ring, pow_mul, h3, one_pow]
  have hinj : Function.Injective f := by
    rintro ⟨x, e⟩ ⟨x', e'⟩ h
    have h' : (x : G) * φ ^ (e : ℕ) = x' * φ ^ (e' : ℕ) := congrArg Subtype.val h
    have hmem : φ ^ (e : ℕ) * (φ ^ (e' : ℕ))⁻¹ ∈ A := by
      have e1 : φ ^ (e : ℕ) * (φ ^ (e' : ℕ))⁻¹ = (x : G)⁻¹ * x' := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h', inv_mul_cancel_left]
      rw [e1]
      exact A.mul_mem (A.inv_mem x.2) x'.2
    have hee : e = e' := by
      by_contra hne
      rw [hinv, ← pow_add] at hmem
      have hne' : (e : ℕ) ≠ e' := fun h => hne (Fin.ext h)
      have he := e.2
      have he' := e'.2
      exact burnsideF48dE_pow_not_mem h3 hφA (n := (e : ℕ) + 2 * e') (by omega) hmem
    subst hee
    have : x = x' := Subtype.ext (mul_right_cancel h')
    rw [this]
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨e, he, x, hx, rfl⟩ := hdec z hz
    exact ⟨(⟨x, hx⟩, ⟨e, he⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, mul_comm]

end Three

theorem burnsideF48dE_σ_two : burnsideF48dE_σ 2 = burnsideF48d_frob := by
  unfold burnsideF48dE_σ
  rw [if_pos rfl]

theorem burnsideF48dE_σ_ne {j : ℕ} (h2 : j ≠ 2) :
    burnsideF48dE_σ j = burnsideF48d_σ (if j < 2 then j else j - 1) := by
  unfold burnsideF48dE_σ
  rw [if_neg h2]

theorem burnsideF48dE_σ_mem_X {j : ℕ} (h2 : j ≠ 2) : burnsideF48dE_σ j ∈ burnsideF48d_X := by
  rw [burnsideF48dE_σ_ne h2]
  exact burnsideF48d_σ_mem _

theorem burnsideF48dE_mem_aptF_iff (q : Fin 26572) :
    q ∈ burnsideF48d_aptF ↔ q.val ∈ burnsideF48d_apt := by
  simp only [burnsideF48d_aptF, burnsideF48d_apt, Finset.mem_insert, Finset.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  exact Iff.rfl

section Letters

theorem burnsideF48dE_rel (_hM : burnsideF48d_ModelFacts) {r : List (Fin 18 × Bool)}
    (hr : r ∈ burnsideF48d_R13 ++ burnsideF48d_R23) :
    burnsideF48s_ev (fun j : Fin 18 => burnsideF48dE_σ j) r = 1 :=
  Certificates.certificate7810.2.2.2.2.2.2.2.2 r hr

theorem burnsideF48dE_frob_cube (_hM : burnsideF48d_ModelFacts) : burnsideF48d_frob ^ 3 = 1 :=
  Certificates.certificate7810.1

theorem burnsideF48dE_frob_ne_one (_hM : burnsideF48d_ModelFacts) : burnsideF48d_frob ≠ 1 :=
  Certificates.certificate7810.2.1

theorem burnsideF48dE_frob_apt (_hM : burnsideF48d_ModelFacts) :
    ∀ p ∈ burnsideF48d_aptF, burnsideF48d_frob p = p :=
  Certificates.certificate7810.2.2.1

theorem burnsideF48dE_frob_line (_hM : burnsideF48d_ModelFacts) :
    ∀ p ∈ burnsideF48d_line, burnsideF48d_frob p ∈ burnsideF48d_line :=
  Certificates.certificate7810.2.2.2.1

theorem burnsideF48dE_frob_comm_x (_hM : burnsideF48d_ModelFacts) :
    burnsideF48d_frob * burnsideF48d_σ 0 = burnsideF48d_σ 0 * burnsideF48d_frob :=
  Certificates.certificate7810.2.2.2.2.1

theorem burnsideF48dE_frob_comm_y (_hM : burnsideF48d_ModelFacts) :
    burnsideF48d_frob * burnsideF48d_σ 1 = burnsideF48d_σ 1 * burnsideF48d_frob :=
  Certificates.certificate7810.2.2.2.2.2.1

theorem burnsideF48dE_xy_six (_hM : burnsideF48d_ModelFacts) :
    (burnsideF48d_σ 0 * burnsideF48d_σ 1) ^ 6 = 1 :=
  Certificates.certificate7810.2.2.2.2.2.2.1

theorem burnsideF48dE_frob_conj_eq (_hM : burnsideF48d_ModelFacts) {k : ℕ} (hk : k < 15) :
    burnsideF48d_frob⁻¹ * (burnsideF48d_σ (k + 2) * burnsideF48d_frob) =
      burnsideF48s_ev (fun j : Fin 18 => burnsideF48dE_σ j) (burnsideF48dE_PhiW.getD k []) :=
  Certificates.certificate7810.2.2.2.2.2.2.2.1 k hk

theorem burnsideF48dE_frob_conj_letter (hM : burnsideF48d_ModelFacts) (j : Fin 17) :
    burnsideF48d_frob⁻¹ * burnsideF48d_σ j * burnsideF48d_frob ∈ burnsideF48d_X := by
  by_cases h0 : (j : ℕ) = 0
  · rw [h0, mul_assoc, ← burnsideF48dE_frob_comm_x hM, inv_mul_cancel_left]
    exact burnsideF48d_σ_mem 0
  by_cases h1 : (j : ℕ) = 1
  · rw [h1, mul_assoc, ← burnsideF48dE_frob_comm_y hM, inv_mul_cancel_left]
    exact burnsideF48d_σ_mem 1
  have hj := j.2
  have e : (j : ℕ) = ((j : ℕ) - 2) + 2 := by omega
  rw [e, mul_assoc, burnsideF48dE_frob_conj_eq hM (by omega)]
  refine burnsideF48s_ev_mem _ _ fun l hl => burnsideF48dE_σ_mem_X ?_
  have hw : ∀ w ∈ burnsideF48dE_PhiW, ∀ l ∈ w, (l.1 : ℕ) ≠ 2 := by decide
  have hk : (j : ℕ) - 2 < burnsideF48dE_PhiW.length := by
    rw [show burnsideF48dE_PhiW.length = 15 from rfl]
    omega
  rw [List.getD_eq_getElem _ _ hk] at hl
  exact hw _ (List.getElem_mem _) l hl

theorem burnsideF48dE_sup_X (hM : burnsideF48d_ModelFacts) :
    burnsideF48d_P1 ⊔ burnsideF48d_P2 = ⊤ := by
  by_contra hne
  have h1 : burnsideF48d_P1 < burnsideF48d_P1 ⊔ burnsideF48d_P2 := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have h2 : burnsideF48d_P2 ≤ burnsideF48d_P1 :=
      calc burnsideF48d_P2 ≤ burnsideF48d_P1 ⊔ burnsideF48d_P2 := le_sup_right
        _ = burnsideF48d_P1 := h.symm
    have h3 : burnsideF48d_P2 < burnsideF48d_P1 := lt_of_le_of_ne h2 (Ne.symm hM.P1_ne_P2)
    exact hM.P1_max.2.2.1 (hM.P2_max.2.2.2 _ h3 le_top)
  exact hne (hM.P1_max.2.2.2 _ h1 le_top)

theorem burnsideF48dE_mem_closure_L (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48d_X) :
    z ∈ Subgroup.closure (Set.range burnsideF48d_L) := by
  have h : (⊤ : Subgroup ↥burnsideF48d_X) ≤ Subgroup.closure (Set.range burnsideF48d_L) := by
    rw [← burnsideF48dE_sup_X hM]
    exact sup_le (Subgroup.closure_mono (Set.image_subset_range _ _))
      (Subgroup.closure_mono (Set.image_subset_range _ _))
  exact h (Subgroup.mem_top z)

theorem burnsideF48dE_frob_conj_mem (hM : burnsideF48d_ModelFacts) {g : Equiv.Perm (Fin 26572)}
    (hg : g ∈ burnsideF48d_X) : burnsideF48d_frob⁻¹ * g * burnsideF48d_frob ∈ burnsideF48d_X := by
  have key : ∀ z : ↥burnsideF48d_X,
      burnsideF48d_frob⁻¹ * (z : Equiv.Perm (Fin 26572)) * burnsideF48d_frob ∈ burnsideF48d_X := by
    intro z
    induction burnsideF48dE_mem_closure_L hM z using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact burnsideF48dE_frob_conj_letter hM j
    | one =>
      rw [Subgroup.coe_one, mul_one, inv_mul_cancel]
      exact burnsideF48d_X.one_mem
    | mul a b _ _ ha hb =>
      have e : burnsideF48d_frob⁻¹ * ((a * b : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) *
          burnsideF48d_frob = (burnsideF48d_frob⁻¹ * (a : Equiv.Perm (Fin 26572)) *
            burnsideF48d_frob) * (burnsideF48d_frob⁻¹ * (b : Equiv.Perm (Fin 26572)) *
              burnsideF48d_frob) := by
        rw [Subgroup.coe_mul]
        group
      rw [e]
      exact burnsideF48d_X.mul_mem ha hb
    | inv a _ ha =>
      have e : burnsideF48d_frob⁻¹ * ((a⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) *
          burnsideF48d_frob = (burnsideF48d_frob⁻¹ * (a : Equiv.Perm (Fin 26572)) *
            burnsideF48d_frob)⁻¹ := by
        rw [Subgroup.coe_inv]
        group
      rw [e]
      exact burnsideF48d_X.inv_mem ha
  exact key ⟨g, hg⟩

theorem burnsideF48dE_frob_conj_mem' (hM : burnsideF48d_ModelFacts) {g : Equiv.Perm (Fin 26572)}
    (hg : g ∈ burnsideF48d_X) : burnsideF48d_frob * g * burnsideF48d_frob⁻¹ ∈ burnsideF48d_X := by
  have h3 := burnsideF48dE_frob_cube hM
  have e1 : burnsideF48d_frob⁻¹ * burnsideF48d_frob⁻¹ = burnsideF48d_frob := by
    rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_three', h3]
  have e2 : burnsideF48d_frob * burnsideF48d_frob = burnsideF48d_frob⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', h3]
  have e : burnsideF48d_frob * g * burnsideF48d_frob⁻¹ =
      burnsideF48d_frob⁻¹ * (burnsideF48d_frob⁻¹ * g * burnsideF48d_frob) * burnsideF48d_frob := by
    calc burnsideF48d_frob * g * burnsideF48d_frob⁻¹ =
        (burnsideF48d_frob⁻¹ * burnsideF48d_frob⁻¹) * g *
          (burnsideF48d_frob * burnsideF48d_frob) := by
          rw [e1, e2]
      _ = _ := by simp only [mul_assoc]
  rw [e]
  exact burnsideF48dE_frob_conj_mem hM (burnsideF48dE_frob_conj_mem hM hg)

theorem burnsideF48dE_frob_normalizer (hM : burnsideF48d_ModelFacts) :
    burnsideF48d_frob ∈ Subgroup.normalizer (burnsideF48d_X : Set (Equiv.Perm (Fin 26572))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact burnsideF48dE_frob_conj_mem' hM
  · intro hg
    have := burnsideF48dE_frob_conj_mem hM hg
    rwa [show burnsideF48d_frob⁻¹ * (burnsideF48d_frob * g * burnsideF48d_frob⁻¹) *
      burnsideF48d_frob = g by group] at this

theorem burnsideF48dE_frob_not_mem (hM : burnsideF48d_ModelFacts) :
    burnsideF48d_frob ∉ burnsideF48d_X := by
  intro h
  have hT : (⟨burnsideF48d_frob, h⟩ : ↥burnsideF48d_X) ∈ burnsideF48d_T :=
    (hM.mem_T _).2 (burnsideF48dE_frob_apt hM)
  have hc : burnsideF48d_L 0 * burnsideF48d_L 1 * ⟨burnsideF48d_frob, h⟩ =
      ⟨burnsideF48d_frob, h⟩ * (burnsideF48d_L 0 * burnsideF48d_L 1) := by
    apply Subtype.ext
    show burnsideF48d_σ 0 * burnsideF48d_σ 1 * burnsideF48d_frob =
      burnsideF48d_frob * (burnsideF48d_σ 0 * burnsideF48d_σ 1)
    rw [mul_assoc, ← burnsideF48dE_frob_comm_y hM, ← mul_assoc, ← burnsideF48dE_frob_comm_x hM,
      mul_assoc]
  have := hM.comm_T _ hT hc
  exact burnsideF48dE_frob_ne_one hM (congrArg Subtype.val this)

end Letters

@[expose] noncomputable def burnsideF48dE_Xh : Subgroup (Equiv.Perm (Fin 26572)) :=
  burnsideF48d_X ⊔ Subgroup.zpowers burnsideF48d_frob

@[expose] noncomputable def burnsideF48dE_Xs : Subgroup ↥burnsideF48dE_Xh :=
  burnsideF48d_X.subgroupOf burnsideF48dE_Xh

theorem burnsideF48dE_X_le : burnsideF48d_X ≤ burnsideF48dE_Xh := le_sup_left

theorem burnsideF48dE_frob_mem : burnsideF48d_frob ∈ burnsideF48dE_Xh :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

noncomputable abbrev burnsideF48dE_ι : ↥burnsideF48d_X →* ↥burnsideF48dE_Xh :=
  Subgroup.inclusion burnsideF48dE_X_le

@[expose] noncomputable def burnsideF48dE_F : ↥burnsideF48dE_Xh :=
  ⟨burnsideF48d_frob, burnsideF48dE_frob_mem⟩

theorem burnsideF48dE_mem_map_ι {Q : Subgroup ↥burnsideF48d_X} (z : ↥burnsideF48dE_Xh) :
    z ∈ Q.map burnsideF48dE_ι ↔ ∃ h : (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X,
      (⟨z, h⟩ : ↥burnsideF48d_X) ∈ Q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hz⟩
    exact ⟨_, hz, rfl⟩

section Model

theorem burnsideF48dE_mem_Xh (hM : burnsideF48d_ModelFacts) (z : Equiv.Perm (Fin 26572)) :
    z ∈ burnsideF48dE_Xh ↔ ∃ e < 3, ∃ x ∈ burnsideF48d_X, z = x * burnsideF48d_frob ^ e :=
  burnsideF48dE_mem_sup_iff (burnsideF48dE_frob_cube hM) (burnsideF48dE_frob_normalizer hM) z

theorem burnsideF48dE_normal (hM : burnsideF48d_ModelFacts) : burnsideF48dE_Xs.Normal :=
  burnsideF48dE_normal_sup (burnsideF48dE_frob_normalizer hM)

theorem burnsideF48dE_dec (hM : burnsideF48d_ModelFacts) (z : ↥burnsideF48dE_Xh) :
    ∃ e < 3, ∃ x : ↥burnsideF48d_X, z = burnsideF48dE_ι x * burnsideF48dE_F ^ e := by
  obtain ⟨e, he, x, hx, hz⟩ := (burnsideF48dE_mem_Xh hM z).1 z.2
  refine ⟨e, he, ⟨x, hx⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, SubgroupClass.coe_pow]
  exact hz

theorem burnsideF48dE_card_Xh (hM : burnsideF48d_ModelFacts) :
    Nat.card ↥burnsideF48dE_Xh = 61682494700736 := by
  rw [burnsideF48dE_card_three burnsideF48dE_X_le burnsideF48dE_frob_mem
    (burnsideF48dE_frob_cube hM) (burnsideF48dE_frob_not_mem hM)
    fun z hz => (burnsideF48dE_mem_Xh hM z).1 hz, hM.card_X]

theorem burnsideF48dE_card_Xs (hM : burnsideF48d_ModelFacts) :
    Nat.card ↥burnsideF48dE_Xs = 20560831566912 := by
  rw [burnsideF48dE_Xs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe burnsideF48dE_X_le).toEquiv,
    hM.card_X]

theorem burnsideF48dE_index (hM : burnsideF48d_ModelFacts) : burnsideF48dE_Xs.index = 3 := by
  have h := Subgroup.card_mul_index burnsideF48dE_Xs
  rw [burnsideF48dE_card_Xs hM, burnsideF48dE_card_Xh hM] at h
  omega

end Model

end CFSG.ASVolI
