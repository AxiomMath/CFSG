module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement

theorem mem_closure_pair_involutions_ch615 {X : Type*} [Group X] {u w : X} (hu : u * u = 1)
    (hw : w * w = 1) {x : X} (hx : x ∈ Subgroup.closure ({u, w} : Set X)) :
    ∃ k : ℤ, x = (u * w) ^ k ∨ x = (u * w) ^ k * u := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  have hconj : ∀ b : ℤ, u * (u * w) ^ b = (u * w) ^ (-b) * u := by
    intro b
    have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
      rw [huinv, mul_inv_rev, huinv, hwinv, ← mul_assoc, hu, one_mul]
    have h2 : u * (u * w) ^ b * u⁻¹ = (u * w) ^ (-b) := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow']
    calc u * (u * w) ^ b = u * (u * w) ^ b * u⁻¹ * u := by group
      _ = (u * w) ^ (-b) * u := by rw [h2]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, huinv, hwinv, mul_assoc, hu, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha | ha⟩ := hy <;> obtain ⟨b, hb | hb⟩ := hz <;> subst ha <;> subst hb
    · exact ⟨a + b, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨a + b, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨a - b, Or.inr ?_⟩
      rw [mul_assoc, hconj, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨a - b, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc u, hconj, mul_assoc, hu, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv y _ hy =>
    obtain ⟨a, ha | ha⟩ := hy <;> subst ha
    · exact ⟨-a, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨a, Or.inr ?_⟩
      rw [mul_inv_rev, huinv, ← zpow_neg, hconj, neg_neg]

theorem isPGroup_closure_pair_involutions_ch615 {X : Type*} [Group X] {u w : X} (hu : u * u = 1)
    (hw : w * w = 1) {n : ℕ} (huw : (u * w) ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.closure ({u, w} : Set X)) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  intro x
  refine ⟨n + 1, Subtype.ext ?_⟩
  obtain ⟨k, hk | hk⟩ := mem_closure_pair_involutions_ch615 hu hw x.2
  · simp only [Subgroup.coe_pow, hk, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_succ, pow_mul, huw,
      one_pow, one_zpow]
  · simp only [Subgroup.coe_pow, hk, Subgroup.coe_one]
    have h2 : ((u * w) ^ k * u) ^ 2 = 1 := by
      have h1 : u * (u * w) * u⁻¹ = (u * w)⁻¹ := by
        rw [huinv, mul_inv_rev, huinv, hwinv, ← mul_assoc, hu, one_mul]
      have h3 : u * (u * w) ^ k * u⁻¹ = (u * w) ^ (-k) := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow']
      calc ((u * w) ^ k * u) ^ 2 = (u * w) ^ k * (u * (u * w) ^ k * u⁻¹) := by
            rw [sq, huinv]; group
        _ = 1 := by rw [h3, ← zpow_add, add_neg_cancel, zpow_zero]
    rw [pow_succ', pow_mul, h2, one_pow]

theorem perm3_three_ch615 : ∀ σ σ' : Equiv.Perm (Fin 3), σ * σ = 1 → σ' * σ' = 1 →
    σ ≠ 1 → σ' ≠ 1 → σ ≠ σ' → (σ * σ') ^ 3 = 1 ∧ ∀ k : ℕ, k < 4 → (σ * σ') ^ 2 ^ k ≠ 1 := by
  decide +kernel

theorem perm3_two_ch615 : ∀ σ : Equiv.Perm (Fin 3), (∃ k : ℕ, k < 4 ∧ σ ^ 2 ^ k = 1) →
    σ * σ = 1 := by decide +kernel

theorem perm3_conj_ch615 : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ∃ ρ : Equiv.Perm (Fin 3), ρ * σ * ρ⁻¹ ≠ σ := by decide +kernel

theorem card_perm3_ch615 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem perm3_sq_of_pow_ch615 {σ : Equiv.Perm (Fin 3)} {k : ℕ} (h : σ ^ 2 ^ k = 1) :
    σ * σ = 1 := by
  have hdvd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h6 : orderOf σ ∣ 6 := card_perm3_ch615 ▸ orderOf_dvd_natCard σ
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have : 2 ^ 2 ∣ 6 := by
      rw [hjk] at h6
      exact (pow_dvd_pow 2 (by omega)).trans h6
    norm_num at this
  apply perm3_two_ch615 σ
  refine ⟨1, by norm_num, ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one, hjk]
  exact pow_dvd_pow 2 hj1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem perm3_normal_two_eq_bot_ch615 {N : Subgroup (Equiv.Perm (Fin 3))} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hσ1
  obtain ⟨k, hk⟩ := h2 ⟨σ, hσ⟩
  have hk' : σ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hσ2 := perm3_sq_of_pow_ch615 hk'
  obtain ⟨ρ, hρ⟩ := perm3_conj_ch615 σ hσ2 hσ1
  set σ' := ρ * σ * ρ⁻¹ with hσ'
  have hσ'N : σ' ∈ N := hN.conj_mem σ hσ ρ
  have hσ'2 : σ' * σ' = 1 := by
    rw [hσ']
    calc ρ * σ * ρ⁻¹ * (ρ * σ * ρ⁻¹) = ρ * (σ * σ) * ρ⁻¹ := by group
      _ = 1 := by rw [hσ2, mul_one, mul_inv_cancel]
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    apply hσ1
    calc σ = ρ⁻¹ * σ' * ρ := by rw [hσ']; group
      _ = 1 := by rw [h1]; group
  obtain ⟨h3, -⟩ := perm3_three_ch615 σ σ' hσ2 hσ'2 hσ1 hσ'1 (Ne.symm hρ)
  obtain ⟨j, hj⟩ := h2 ⟨σ * σ', N.mul_mem hσ hσ'N⟩
  have hj' : (σ * σ') ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hord : orderOf (σ * σ') = 1 := by
    have h1 : orderOf (σ * σ') ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2' : orderOf (σ * σ') ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right j (by norm_num)) h1 h2'
  have h1 : σ * σ' = 1 := orderOf_eq_one_iff.mp hord
  apply hρ
  have : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this, inv_eq_of_mul_eq_one_left hσ2]

omit [Group G] in
theorem le_ker_of_normal_two_ch615 {G : Type} [Group G] {X W : Subgroup G} (hWX : W ≤ X)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hW2 : IsPGroup 2 W)
    (φ : ↥X →* Equiv.Perm (Fin 3)) (hφ : Function.Surjective φ) :
    ∀ w (hw : w ∈ W), φ ⟨w, hWX hw⟩ = 1 := by
  have hn : (W.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW
  have hb := perm3_normal_two_eq_bot_ch615 (hn.map φ hφ)
    (IsPGroup.map (hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWX).symm) φ)
  intro w hw
  have : φ ⟨w, hWX hw⟩ ∈ (W.subgroupOf X).map φ := ⟨⟨w, hWX hw⟩, hw, rfl⟩
  rwa [hb, Subgroup.mem_bot] at this

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_not_two_ch615 (h6210 : Stmt6_2_10) {v : G} (hv : v ∈ V)
    (hvC : v ∉ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)) :
    ∃ g ∈ hCh611 T, ∀ k : ℕ,
      (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := hCh611 T with hHdef
  set C := centralizerMod (zCh611 T) H (uCh611 T L V) with hCdef
  obtain ⟨-, -, hO2, -, -⟩ := h6210 G T M L V h
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hg)
      (Subgroup.le_normalizer hg) (le_normalizer_conjClosure _ H hg)
  have hvH : v ∈ H := h.V_le_hCh611 hv
  have hv2 : v * v = 1 := by rw [← pow_two]; exact h.toHyp611.isElemAbelian.2 v hv
  by_contra hall
  push Not at hall
  have hnC : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
  set Q := ↥H ⧸ C.subgroupOf H
  set π := QuotientGroup.mk' (C.subgroupOf H)
  set x : Q := π ⟨v, hvH⟩ with hx
  have hx2 : x * x = 1 := by
    rw [hx, ← map_mul]
    have : (⟨v, hvH⟩ : ↥H) * ⟨v, hvH⟩ = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hpair : ∀ q : Q, IsPGroup 2 (Subgroup.closure ({x, q * x * q⁻¹} : Set Q)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf H) q
    have hy2 : π g * x * (π g)⁻¹ * (π g * x * (π g)⁻¹) = 1 := by
      calc π g * x * (π g)⁻¹ * (π g * x * (π g)⁻¹) = π g * (x * x) * (π g)⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
    obtain ⟨k, hk⟩ := hall ((g⁻¹ : ↥H) : G) (g⁻¹ : ↥H).2
    refine isPGroup_closure_pair_involutions_ch615 hx2 hy2 (n := k) ?_
    have e : x * (π g * x * (π g)⁻¹) = π (⟨v, hvH⟩ * (g * ⟨v, hvH⟩ * g⁻¹)) := by
      simp [hx, map_mul, map_inv]
    rw [e, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    have e2 : (((⟨v, hvH⟩ * (g * ⟨v, hvH⟩ * g⁻¹)) ^ 2 ^ k : ↥H) : G) =
        (v * ((g⁻¹ : ↥H)⁻¹ * v * (g⁻¹ : ↥H))) ^ 2 ^ k := by
      simp
    rw [e2]
    exact hk
  have hxO : x ∈ CFSG.pCore 2 Q := (CFSG.BaerSuzuki.baer_suzuki_iff x).mpr hpair
  set P : Subgroup G := ((CFSG.pCore 2 Q).comap π).map H.subtype with hP
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    have hN : ((CFSG.pCore 2 Q).comap π).Normal :=
      (CFSG.BaerSuzuki.Helpers.pCore_normal 2).comap π
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, hN.conj_mem y' hy' _, rfl⟩
    · rintro ⟨y', hy', hy'e⟩
      have hy'e' : (y' : G) = g * y * g⁻¹ := hy'e
      have hyH : y ∈ H := by
        have : (y' : G) ∈ H := y'.2
        rw [hy'e'] at this
        have := H.mul_mem (H.mul_mem (H.inv_mem hg) this) hg
        simpa [mul_assoc] using this
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      have e : (⟨y, hyH⟩ : ↥H) = ⟨g, hg⟩⁻¹ * y' * ⟨g, hg⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hy'e']
        group
      rw [e]
      have := hN.conj_mem y' hy' (⟨g, hg⟩⁻¹)
      simpa using this
  have hP2 : ∀ p ∈ P, ∃ k : ℕ, p ^ 2 ^ k ∈ C := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.BaerSuzuki.Helpers.pCore_isPGroup (G := Q) 2 ⟨π p, hp⟩
    refine ⟨k, ?_⟩
    have h1 : π (p ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hPC := hO2 P hPH hHP hP2
  exact hvC (hPC ⟨⟨v, hvH⟩, hxO, rfl⟩)

theorem two_six_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G}
    (hv : v ∈ V) {g : G} (hg : g ∈ hCh611 T)
    (hgk : ∀ k : ℕ, (v * (g⁻¹ * v * g)) ^ 2 ^ k ∉
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)) :
    (v * (g⁻¹ * v * g)) ^ 3 ∈ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) ∧
    (∃ D : Subgroup G, D ≤ V ⊔ conjSubgroup V g ∧
      V ⊔ conjSubgroup V g ≤ Subgroup.normalizer (D : Set G) ∧ E2.IsExtraspecialPlus 2 D ∧
      ∃ φ : ↥(V ⊔ conjSubgroup V g) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
        φ.ker = D.subgroupOf (V ⊔ conjSubgroup V g)) ∧
    (V ⊓ uCh611 T L V) ⊔ conjSubgroup (V ⊓ uCh611 T L V) g =
      pCoreOf 2 (V ⊔ conjSubgroup V g) ∧
    pCoreOf 2 (V ⊔ conjSubgroup V g) ≤ uCh611 T L V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := uCh611 T L V with hUdef
  set H := hCh611 T with hHdef
  set C := centralizerMod (zCh611 T) H U with hCdef
  set Vg := conjSubgroup V g with hVg
  set VU := V ⊓ U with hVU
  set VUg := conjSubgroup VU g with hVUg
  set X := V ⊔ Vg with hX
  have hV := h.toHyp611.isElemAbelian
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV ha hb
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hVU8 : Nat.card VU = 8 := by
    have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
    rw [this]; norm_num
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have hcommVU : ∀ x ∈ V, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ VU := by
    intro x hx u hu
    have := hVUc (Subgroup.commutator_mem_commutator hx hu)
    rwa [commutatorElement_def] at this
  have hgU : g ∈ Subgroup.normalizer (U : Set G) := hCh611_le_normalizer_u T L V hg
  have hUg : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hgU u).mp hu
  have hUg' : ∀ u ∈ U, g⁻¹ * u * g ∈ U := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
    simpa using this
  have hcommVUg : ∀ y ∈ Vg, ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ VUg := by
    intro y hy u hu
    rw [hVUg, mem_conjSubgroup_iff]
    rw [hVg, mem_conjSubgroup_iff] at hy
    have h1 := hcommVU _ hy _ (hUg u hu)
    have e : g * (y * u * y⁻¹ * u⁻¹) * g⁻¹ =
        g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  have hVUgU : VUg ≤ U := fun y hy => by
    rw [hVUg, mem_conjSubgroup_iff] at hy
    have := hUg' _ hy.2
    simpa [mul_assoc] using this
  have hVUgVg : VUg ≤ Vg := fun y hy => by
    rw [hVUg, mem_conjSubgroup_iff] at hy
    rw [hVg, mem_conjSubgroup_iff]
    exact hy.1
  have hVgab : ∀ a ∈ Vg, ∀ b ∈ Vg, a * b = b * a := by
    intro a ha b hb
    rw [hVg, mem_conjSubgroup_iff] at ha hb
    have h1 := hVab _ ha _ hb
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h1
        _ = g * (b * a) * g⁻¹ := by group
    simpa using this
  have hN1 : VU ≤ Subgroup.normalizer (Vg : Set G) := by
    intro x hx
    refine mem_normalizer_of_forall_conj_mem_of_le fun y hy => ?_
    have h1 := hcommVUg y hy x hx.2
    have h2 : x * y * x⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ * y := by group
    rw [h2]
    exact Vg.mul_mem (Vg.inv_mem (hVUgVg h1)) hy
  have hN2 : VUg ≤ Subgroup.normalizer (V : Set G) := by
    intro y hy
    refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
    have h1 := hcommVU x hx y (hVUgU hy)
    have h2 : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
    rw [h2]
    exact V.mul_mem (V.inv_mem h1.1) hx
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hVg2 : IsPGroup 2 Vg := by
    rw [hVg]
    exact hV2.map _
  have hnot2 : ¬ IsPGroup 2 X := by
    intro hX2
    obtain ⟨k, hk⟩ := hX2 ⟨v * (g⁻¹ * v * g), X.mul_mem (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right (by rw [hVg, mem_conjSubgroup_iff]; simpa [mul_assoc] using hv))⟩
    apply hgk k
    have : (v * (g⁻¹ * v * g)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact C.one_mem
  have hVgcard : Nat.card Vg = 16 := by rw [hVg, card_conjSubgroup, hV16]
  have hVUgcard : Nat.card VUg = 8 := by rw [hVUg, card_conjSubgroup, hVU8]
  have hU' : V ⊓ Subgroup.normalizer (Vg : Set G) = VU := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hN1)
    have hlt' : V ⊓ Subgroup.normalizer (Vg : Set G) < V := by
      refine lt_of_le_of_ne inf_le_left fun he => hnot2 ?_
      exact IsPGroup.to_sup_of_normal_right' hV2 hVg2 (he ▸ inf_le_right)
    have h1 := Subgroup.card_lt_of_lt hlt'
    have h2 : Nat.card ↥(V ⊓ Subgroup.normalizer (Vg : Set G)) ∣ 16 :=
      hV16 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : 8 ∣ Nat.card ↥(V ⊓ Subgroup.normalizer (Vg : Set G)) :=
      hVU8 ▸ Subgroup.card_dvd_of_le (le_inf inf_le_left hN1)
    rw [hVU8]
    obtain ⟨c, hc⟩ := h3
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  have hA' : Vg ⊓ Subgroup.normalizer (V : Set G) = VUg := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf hVUgVg hN2)
    have hlt' : Vg ⊓ Subgroup.normalizer (V : Set G) < Vg := by
      refine lt_of_le_of_ne inf_le_left fun he => hnot2 ?_
      exact IsPGroup.to_sup_of_normal_left' hV2 hVg2 (he ▸ inf_le_right)
    have h1 := Subgroup.card_lt_of_lt hlt'
    have h2 : Nat.card ↥(Vg ⊓ Subgroup.normalizer (V : Set G)) ∣ 16 :=
      hVgcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : 8 ∣ Nat.card ↥(Vg ⊓ Subgroup.normalizer (V : Set G)) :=
      hVUgcard ▸ Subgroup.card_dvd_of_le (le_inf hVUgVg hN2)
    rw [hVUgcard]
    obtain ⟨c, hc⟩ := h3
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  have hU2 : (V ⊓ Subgroup.normalizer (Vg : Set G)).relIndex V = 2 := by
    rw [hU']
    have h1 := Subgroup.relIndex_mul_card VU V
    rw [inf_of_le_left inf_le_left, hVU8, hV16] at h1
    omega
  have hA2 : (Vg ⊓ Subgroup.normalizer (V : Set G)).relIndex Vg = 2 := by
    rw [hA']
    have h1 := Subgroup.relIndex_mul_card VUg Vg
    rw [inf_of_le_left hVUgVg, hVUgcard, hVgcard] at h1
    omega
  have h66 := h626 G T M L V h g hA2 hU2
  rcases h66 with ⟨-, -, -, -, hp⟩ | ⟨-, -, -, hDdata, -, hcard2, -⟩
  · exact absurd hp hnot2
  obtain ⟨D, hDX, hXD, hDext, φ, hφs, hφk⟩ := hDdata
  set W := VU ⊔ VUg with hW
  have hWU : W ≤ U := sup_le inf_le_right hVUgU
  have hWX : W ≤ X := sup_le (inf_le_left.trans le_sup_left) (hVUgVg.trans le_sup_right)
  have hUT : U ≤ T := h.uCh611_le_T h331 h432 h512 h614 h615
  have hW2 : IsPGroup 2 W := h.sylow.1.to_le (hWU.trans hUT)
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := by
    refine sup_le (fun x hx => mem_normalizer_of_forall_conj_mem_of_le fun w hw => ?_)
      (fun y hy => mem_normalizer_of_forall_conj_mem_of_le fun w hw => ?_)
    · have hconj : W.map (MulAut.conj x).toMonoidHom ≤ W := by
        rw [hW, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨a, ha, rfl⟩
          refine Subgroup.mem_sup_left ⟨?_, ?_⟩
          · show x * a * x⁻¹ ∈ V
            rw [hVab x hx a ha.1, mul_inv_cancel_right]
            exact ha.1
          · show x * a * x⁻¹ ∈ U
            rw [hVab x hx a ha.1, mul_inv_cancel_right]
            exact ha.2
        · rintro _ ⟨a, ha, rfl⟩
          show x * a * x⁻¹ ∈ W
          have h1 := hcommVU x hx a (hVUgU ha)
          have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
          rw [e]
          exact W.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right ha)
      exact hconj ⟨w, hw, rfl⟩
    · have hconj : W.map (MulAut.conj y).toMonoidHom ≤ W := by
        rw [hW, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨a, ha, rfl⟩
          show y * a * y⁻¹ ∈ W
          have h1 := hcommVUg y hy a ha.2
          have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
          rw [e]
          exact W.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left ha)
        · rintro _ ⟨a, ha, rfl⟩
          refine Subgroup.mem_sup_right ?_
          show y * a * y⁻¹ ∈ VUg
          rw [hVgab y hy a (hVUgVg ha), mul_inv_cancel_right]
          exact ha
      exact hconj ⟨w, hw, rfl⟩
  have hφW := le_ker_of_normal_two_ch615 hWX hXW hW2 φ hφs
  have hWD : W ≤ D := by
    intro w hw
    have h1 : (⟨w, hWX hw⟩ : ↥X) ∈ φ.ker := hφW w hw
    rw [hφk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hD32 : Nat.card D = 32 := by rw [hDext.2.1]; norm_num
  have hWcard : 32 ≤ Nat.card W := by
    have hnorm : VUg ≤ Subgroup.normalizer (VU : Set G) := by
      intro y hy
      refine mem_normalizer_of_forall_conj_mem_of_le fun a ha => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hN2 hy) a).mp ha.1
      · exact U.mul_mem (U.mul_mem (hVUgU hy) ha.2) (U.inv_mem (hVUgU hy))
    have h1 := relIndex_sup_ch611 hnorm
    have h2 : Nat.card ↥(VU ⊓ VUg) ≤ 2 := by
      have : VU ⊓ VUg ≤ V ⊓ Vg := inf_le_inf inf_le_left hVUgVg
      exact hcard2 ▸ Subgroup.card_le_of_le this
    have h3 := Subgroup.relIndex_mul_card VU VUg
    rw [hVUgcard] at h3
    have h4 := Subgroup.relIndex_mul_card VU (VUg ⊔ VU)
    rw [inf_of_le_left le_sup_right, hVU8, h1, sup_comm, ← hW] at h4
    have h5 : 0 < Nat.card ↥(VU ⊓ VUg) := Nat.card_pos
    have h6 : 4 ≤ VU.relIndex VUg := by
      by_contra hcon
      push Not at hcon
      have : VU.relIndex VUg * Nat.card ↥(VU ⊓ VUg) ≤ 3 * 2 :=
        Nat.mul_le_mul (by omega) h2
      omega
    rw [← h4]
    nlinarith
  have hWeq : W = D := Subgroup.eq_of_le_of_card_ge hWD (by rw [hD32]; exact hWcard)
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 5) (by rw [hD32]; norm_num)
  have hDO : D ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hDX hXD hD2
  have hOD : pCoreOf 2 X ≤ D := by
    have hφO := le_ker_of_normal_two_ch615 (pCoreOf_le 2 X)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) (pCoreOf_isPGroup 2 X) φ hφs
    intro w hw
    have h1 : (⟨w, pCoreOf_le 2 X hw⟩ : ↥X) ∈ φ.ker := hφO w hw
    rw [hφk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hOeq : pCoreOf 2 X = D := le_antisymm hOD hDO
  have hUC : U ≤ C := fun u hu => mem_centralizerMod.mpr ⟨h.uCh611_le_h h331 h432 h512 h614 h615 hu,
    hCh611_le_normalizer_z T (h.uCh611_le_h h331 h432 h512 h614 h615 hu),
    fun u' hu' => h.comm_mem_ch615 h331 h432 h512 h614 h615 hu hu'⟩
  have hDC : D ≤ C := hWeq ▸ hWU.trans hUC
  have hvX : v ∈ X := Subgroup.mem_sup_left hv
  have hvgX : g⁻¹ * v * g ∈ X := Subgroup.mem_sup_right
    (by rw [hVg, mem_conjSubgroup_iff]; simpa [mul_assoc] using hv)
  set σ := φ ⟨v, hvX⟩ with hσ
  set σ' := φ ⟨g⁻¹ * v * g, hvgX⟩ with hσ'
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hV.2 v hv
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨v, hvX⟩ : ↥X) * ⟨v, hvX⟩ = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hσ'2 : σ' * σ' = 1 := by
    rw [hσ', ← map_mul]
    have : (⟨g⁻¹ * v * g, hvgX⟩ : ↥X) * ⟨g⁻¹ * v * g, hvgX⟩ = 1 := Subtype.ext (by
      show g⁻¹ * v * g * (g⁻¹ * v * g) = 1
      calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
        _ = 1 := by rw [hv2]; group)
    rw [this, map_one]
  have hmem : ∀ k : ℕ, (σ * σ') ^ k = 1 → (v * (g⁻¹ * v * g)) ^ k ∈ C := by
    intro k hk
    have h1 : (⟨v, hvX⟩ * ⟨g⁻¹ * v * g, hvgX⟩ : ↥X) ^ k ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul]
      exact hk
    rw [hφk, Subgroup.mem_subgroupOf] at h1
    exact hDC (by simpa using h1)
  have h3 : (σ * σ') ^ 3 = 1 := by
    by_cases hσ1 : σ = 1
    · exfalso
      apply hgk 1
      refine hmem _ ?_
      rw [hσ1, one_mul, pow_one, pow_two, hσ'2]
    by_cases hσ'1 : σ' = 1
    · exfalso
      apply hgk 1
      refine hmem _ ?_
      rw [hσ'1, mul_one, pow_one, pow_two, hσ2]
    by_cases hσσ : σ = σ'
    · exfalso
      apply hgk 1
      refine hmem _ ?_
      rw [← hσσ, hσ2, one_pow]
    exact (perm3_three_ch615 σ σ' hσ2 hσ'2 hσ1 hσ'1 hσσ).1
  refine ⟨hmem 3 h3, ⟨D, hDX, hXD, hDext, φ, hφs, hφk⟩, ?_, ?_⟩
  · rw [hOeq, ← hWeq]
  · rw [hOeq, ← hWeq]
    exact hWU

end Hyp6Sec2

end CFSG.Quasithin.H13
