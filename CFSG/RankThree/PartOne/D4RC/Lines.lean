module

public import CFSG.RankThree.PartOne.D4RC.Order3

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Lines

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

structure RceLines (F : RclFrame ℓ f K σ ε p L) (S : Sylow p 𝒞[K, σ]) (c : 𝒞[K, σ])
    (E : Subgroup 𝒞[K, σ]) where
  hc : RclConj F S c
  hES : E ≤ S
  hEp : ∀ y ∈ E, y ^ p = 1
  hEc : Nat.card E = p ^ 2
  x : Fin 4 → 𝒞[K, σ]
  hx : ∀ j, x j ∈ E ∧ x j ≠ 1
  sp : ∀ j, RclSpecial F (x j) j
  hspc : ∀ j, (sp j).c = c
  hinj : ∀ j j', Subgroup.zpowers (x j) = Subgroup.zpowers (x j') → j = j'
  hcover : ∀ y ∈ E, y ≠ 1 → (∃ j, y ∈ Subgroup.zpowers (x j)) ∨
    ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∧
      rootCharKernel b = ∅

theorem rce_exists_lines (F : RclFrame ℓ f K σ ε p L) (S : Sylow p 𝒞[K, σ]) {c : 𝒞[K, σ]}
    (hc : RclConj F S c) {E : Subgroup 𝒞[K, σ]} (hES : E ≤ S) (hEp : ∀ y ∈ E, y ^ p = 1)
    (hEc : Nat.card E = p ^ 2) : Nonempty (RceLines F S c E) := by
  obtain ⟨x, hx, hsp, hinj, -, hcover⟩ :=
    rcl_special_lines_of_conj F E hEp hEc c (fun y hy => hc y (hES hy))
  choose sp hspc using hsp
  exact ⟨⟨hc, hES, hEp, hEc, x, hx, sp, hspc, fun j j' h => hinj j j' h, hcover⟩⟩

variable {F : RclFrame ℓ f K σ ε p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]}
  {E : Subgroup 𝒞[K, σ]}

theorem rce_conj_mem (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) {y : 𝒞[K, σ]}
    (hy : y ∈ E) : n * y * n⁻¹ ∈ E := by
  obtain ⟨-, -, -, -, κ, hκ, -⟩ := rcy_coord F Ln.hc
  have hyS : n * y * n⁻¹ ∈ (S : Subgroup 𝒞[K, σ]) :=
    (Subgroup.mem_normalizer_iff.1 hn y).1 (Ln.hES hy)
  refine rcy_mem_of_pow_eq_one F.hp κ hκ Ln.hES Ln.hEp Ln.hEc hyS ?_
  rw [conj_pow, Ln.hEp y hy, mul_one, mul_inv_cancel]

theorem rce_card_centralizer_conj {G : Type*} [Group G] (n y : G) :
    Nat.card (Subgroup.centralizer ({n * y * n⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨n⁻¹ * z * n, ?_⟩
      invFun := fun z => ⟨n * z * n⁻¹, ?_⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc]) }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (Subgroup.mem_centralizer_singleton_iff.1 z.2)
    calc n⁻¹ * z * n * y = n⁻¹ * (z * (n * y * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * y * n⁻¹) * z) * n := by rw [h]
      _ = y * (n⁻¹ * z * n) := by group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (Subgroup.mem_centralizer_singleton_iff.1 z.2)
    calc n * z * n⁻¹ * (n * y * n⁻¹) = n * (z * y) * n⁻¹ := by group
      _ = n * (y * z) * n⁻¹ := by rw [h]
      _ = n * y * n⁻¹ * (n * z * n⁻¹) := by group

theorem rce_conj_mem_lines (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (j : Fin 4) :
    ∃ j', n * Ln.x j * n⁻¹ ∈ Subgroup.zpowers (Ln.x j') := by
  have : Fact p.Prime := ⟨F.hp⟩
  have hy := rce_conj_mem Ln hn (Ln.hx j).1
  have hy1 : n * Ln.x j * n⁻¹ ≠ 1 := fun h => (Ln.hx j).2 (by
    have : Ln.x j = n⁻¹ * (n * Ln.x j * n⁻¹) * n := by group
    rw [this, h]
    group)
  rcases Ln.hcover _ hy hy1 with h | ⟨b, hb, hker⟩
  · exact h
  · exfalso
    have hord : orderOf (n * Ln.x j * n⁻¹) = p := orderOf_eq_prime (Ln.hEp _ hy) hy1
    have hodd := rcr_odd_card_centralizer F hord hb hker
    rw [rce_card_centralizer_conj] at hodd
    exact (Nat.not_odd_iff_even.2 (rcr_even_card_centralizer F (Ln.sp j))) hodd

theorem rce_idx_unique (Ln : RceLines F S c E) {y : 𝒞[K, σ]} (hy1 : y ≠ 1) {a b : Fin 4}
    (ha : y ∈ Subgroup.zpowers (Ln.x a)) (hb : y ∈ Subgroup.zpowers (Ln.x b)) : a = b := by
  have hp := F.hp
  have hza : Subgroup.zpowers y = Subgroup.zpowers (Ln.x a) := by
    have h1 := rcr_centralizer_eq hp (Ln.hEp _ (Ln.hx a).1) (Ln.hx a).2 ha hy1
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers (Ln.x a) := Subgroup.zpowers_le.2 ha
    have : Fact p.Prime := ⟨hp⟩
    have hox : orderOf (Ln.x a) = p := orderOf_eq_prime (Ln.hEp _ (Ln.hx a).1) (Ln.hx a).2
    have hcard : Nat.card (Subgroup.zpowers (Ln.x a)) = p := by rw [Nat.card_zpowers, hox]
    have : Finite (Subgroup.zpowers (Ln.x a)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    have hne : Subgroup.zpowers y ≠ ⊥ := fun h => hy1 (by
      have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have hdvd : Nat.card (Subgroup.zpowers y) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1' | hp'
    · exact absurd (Subgroup.card_eq_one.1 h1') hne
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hp'])
  have hzb : Subgroup.zpowers y = Subgroup.zpowers (Ln.x b) := by
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers (Ln.x b) := Subgroup.zpowers_le.2 hb
    have : Fact p.Prime := ⟨hp⟩
    have hox : orderOf (Ln.x b) = p := orderOf_eq_prime (Ln.hEp _ (Ln.hx b).1) (Ln.hx b).2
    have hcard : Nat.card (Subgroup.zpowers (Ln.x b)) = p := by rw [Nat.card_zpowers, hox]
    have : Finite (Subgroup.zpowers (Ln.x b)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    have hne : Subgroup.zpowers y ≠ ⊥ := fun h => hy1 (by
      have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have hdvd : Nat.card (Subgroup.zpowers y) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1' | hp'
    · exact absurd (Subgroup.card_eq_one.1 h1') hne
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hp'])
  exact Ln.hinj a b (hza.symm.trans hzb)

@[expose] def rceIdx (Ln : RceLines F S c E) (n : 𝒞[K, σ]) (j : Fin 4) : Fin 4 :=
  if h : ∃ j', n * Ln.x j * n⁻¹ ∈ Subgroup.zpowers (Ln.x j') then h.choose else j

theorem rceIdx_spec (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (j : Fin 4) :
    n * Ln.x j * n⁻¹ ∈ Subgroup.zpowers (Ln.x (rceIdx Ln n j)) := by
  have h := rce_conj_mem_lines Ln hn j
  unfold rceIdx
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem rceIdx_eq (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) {j j' : Fin 4}
    (h : n * Ln.x j * n⁻¹ ∈ Subgroup.zpowers (Ln.x j')) : rceIdx Ln n j = j' := by
  have h1 : n * Ln.x j * n⁻¹ ≠ 1 := fun h0 => (Ln.hx j).2 (by
    have : Ln.x j = n⁻¹ * (n * Ln.x j * n⁻¹) * n := by group
    rw [this, h0]
    group)
  exact rce_idx_unique Ln h1 (rceIdx_spec Ln hn j) h

theorem rceIdx_mul (Ln : RceLines F S c E) {n n' : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]))
    (hn' : n' ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (j : Fin 4) :
    rceIdx Ln (n * n') j = rceIdx Ln n (rceIdx Ln n' j) := by
  apply rceIdx_eq Ln (Subgroup.mul_mem _ hn hn')
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 (rceIdx_spec Ln hn' j)
  have h1 : n * n' * Ln.x j * (n * n')⁻¹ = (n * Ln.x (rceIdx Ln n' j) * n⁻¹) ^ e := by
    rw [conj_zpow, he]
    group
  rw [h1]
  exact Subgroup.zpow_mem _ (rceIdx_spec Ln hn _) e

theorem rceIdx_of_commute (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) {j : Fin 4}
    (h : n * Ln.x j = Ln.x j * n) : rceIdx Ln n j = j := by
  apply rceIdx_eq Ln hn
  rw [h, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers _

theorem rceIdx_one (Ln : RceLines F S c E) (j : Fin 4) : rceIdx Ln 1 j = j :=
  rceIdx_of_commute Ln (Subgroup.one_mem _) (by rw [one_mul, mul_one])

theorem rceIdx_pow (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (k : ℕ) (j : Fin 4) :
    rceIdx Ln (n ^ k) j = (rceIdx Ln n)^[k] j := by
  induction k generalizing j with
  | zero => rw [pow_zero, rceIdx_one, Function.iterate_zero, id]
  | succ k ih =>
    rw [pow_succ', rceIdx_mul Ln hn (Subgroup.pow_mem _ hn k), ih,
      Function.iterate_succ_apply']

theorem rceIdx_bijective (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) :
    Function.Bijective (rceIdx Ln n) := by
  refine Finite.injective_iff_bijective.1 fun j j' h => ?_
  have hn' := Subgroup.inv_mem _ hn
  have h1 := rceIdx_mul Ln hn' hn j
  have h2 := rceIdx_mul Ln hn' hn j'
  rw [inv_mul_cancel, rceIdx_one] at h1 h2
  rw [h1, h2, h]

@[expose] def rcePerm (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ (rceIdx_bijective Ln hn)

theorem rcePerm_apply (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (j : Fin 4) :
    rcePerm Ln hn j = rceIdx Ln n j := rfl

theorem rcePerm_pow_apply (Ln : RceLines F S c E) {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) (k : ℕ) (j : Fin 4) :
    (rcePerm Ln hn ^ k) j = rceIdx Ln (n ^ k) j := by
  rw [Equiv.Perm.coe_pow, rceIdx_pow Ln hn]
  rfl

theorem rce_exists_rotation (Ln : RceLines F S c E) [Fact p.Prime] (k : Fin 4) :
    ∃ g ∈ rclPx (Ln.sp k), ∃ hgN : g ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]),
      rcePerm Ln hgN k = k ∧ (∀ v, v ≠ k → rcePerm Ln hgN v ≠ v) ∧ rcePerm Ln hgN ^ 3 = 1 := by
  classical
  have hxS : Ln.x k ∈ (S : Subgroup 𝒞[K, σ]) := Ln.hES (Ln.hx k).1
  obtain ⟨g, hgP, hgN, hline⟩ := rcy_exists_normalizer_line F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS
    Ln.hES Ln.hEp Ln.hEc
  obtain ⟨-, -, -, -, hxZ, hsplit⟩ := rcy_sylow_split F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS
  have h3 := rco_pow_three_conj F S Ln.hc (Ln.sp k) (Ln.hspc k) hxS hgP hgN
  have hg3 : ∀ s ∈ (S : Subgroup 𝒞[K, σ]), g ^ 3 * s * (g ^ 3)⁻¹ = s := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit s hs
    have hgb : g ^ 3 * b = b * g ^ 3 :=
      Subgroup.mem_centralizer_iff.1 hb.2 _ (Subgroup.pow_mem _ hgP 3)
    calc g ^ 3 * (a * b) * (g ^ 3)⁻¹ = (g ^ 3 * a * (g ^ 3)⁻¹) * (g ^ 3 * b * (g ^ 3)⁻¹) := by
          group
      _ = a * b := by rw [h3 a ha, hgb, mul_inv_cancel_right]
  have hfix3 : rcePerm Ln hgN ^ 3 = 1 := by
    ext v
    rw [rcePerm_pow_apply, Equiv.Perm.one_apply]
    refine congrArg Fin.val (rceIdx_of_commute Ln (Subgroup.pow_mem _ hgN 3) ?_)
    have := hg3 _ (Ln.hES (Ln.hx v).1)
    calc g ^ 3 * Ln.x v = g ^ 3 * Ln.x v * (g ^ 3)⁻¹ * g ^ 3 := by group
      _ = Ln.x v * g ^ 3 := by rw [this]
  have hk : rcePerm Ln hgN k = k := by
    rw [rcePerm_apply]
    exact rceIdx_of_commute Ln hgN
      ((Subgroup.mem_centralizer_iff.1 hxZ.2 g hgP))
  have hfixed : ∀ w, rcePerm Ln hgN w = w → w = k ∨
      Subgroup.zpowers (Ln.x w) = E ⊓ rclPx (Ln.sp k) := by
    intro w hw
    rw [rcePerm_apply] at hw
    have hinv : ∀ y ∈ Subgroup.zpowers (Ln.x w), g * y * g⁻¹ ∈ Subgroup.zpowers (Ln.x w) := by
      intro y hy
      obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← conj_zpow]
      have := rceIdx_spec Ln hgN w
      rw [hw] at this
      exact Subgroup.zpow_mem _ this e
    have hle : Subgroup.zpowers (Ln.x w) ≤ E := Subgroup.zpowers_le.2 (Ln.hx w).1
    have hcard : Nat.card (Subgroup.zpowers (Ln.x w)) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime (Ln.hEp _ (Ln.hx w).1) (Ln.hx w).2]
    rcases hline _ hle hcard hinv with h | h
    · exact Or.inr h
    · left
      have hxk : Ln.x k ∈ Subgroup.zpowers (Ln.x w) := by
        rw [h]
        exact ⟨(Ln.hx k).1, hxZ.2⟩
      exact rce_idx_unique Ln (Ln.hx k).2 hxk (Subgroup.mem_zpowers _)
  refine ⟨g, hgP, hgN, hk, fun v hv hvv => ?_, hfix3⟩
  rcases hfixed v hvv with h | hv'
  · exact hv h
  · have hothers : ∀ w, w ≠ v → w ≠ k → rcePerm Ln hgN w ≠ w := by
      intro w hwv hwk hww
      rcases hfixed w hww with h | hw'
      · exact hwk h
      · exact hwv (Ln.hinj w v (hw'.trans hv'.symm))
    exact (show ∀ τ : Equiv.Perm (Fin 4), ∀ j k : Fin 4,
        ¬ (j ≠ k ∧ τ k = k ∧ τ j = j ∧ τ ^ 3 = 1 ∧ ∀ v, v ≠ j → v ≠ k → τ v ≠ v) by decide)
      (rcePerm Ln hgN) v k ⟨hv, hk, hvv, hfix3, hothers⟩

@[expose] def rceR (y : 𝒞[K, σ]) : Subgroup 𝒞[K, σ] :=
  Subgroup.closure {z | z ∈ Subgroup.centralizer ({y} : Set 𝒞[K, σ]) ∧ ∃ k : ℕ, z ^ (2 ^ k) = 1}

omit [Finite K] in
theorem rceR_congr {y y' : 𝒞[K, σ]}
    (h : Subgroup.centralizer ({y} : Set 𝒞[K, σ]) = Subgroup.centralizer ({y'} : Set 𝒞[K, σ])) :
    rceR y = rceR y' := by
  unfold rceR
  rw [h]

omit [Finite K] in
theorem rceR_conj (n y : 𝒞[K, σ]) :
    rceR (n * y * n⁻¹) = (rceR y).map (MulAut.conj n).toMonoidHom := by
  unfold rceR
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hz, k, hk⟩
    refine ⟨n⁻¹ * z * n, ⟨?_, k, ?_⟩, by group⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      calc n⁻¹ * z * n * y = n⁻¹ * (z * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * y * n⁻¹) * z) * n := by rw [hz]
        _ = y * (n⁻¹ * z * n) := by group
    · have h1 : n⁻¹ * z * n = n⁻¹ * z * n⁻¹⁻¹ := by rw [inv_inv]
      rw [h1, conj_pow, hk]
      group
  · rintro ⟨w, ⟨hw, k, hk⟩, rfl⟩
    refine ⟨?_, k, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      calc n * w * n⁻¹ * (n * y * n⁻¹) = n * (w * y) * n⁻¹ := by group
        _ = n * (y * w) * n⁻¹ := by rw [hw]
        _ = n * y * n⁻¹ * (n * w * n⁻¹) := by group
    · rw [conj_pow, hk]
      group

theorem rceR_eq_rclPx {x : 𝒞[K, σ]} {i : Fin 4} (sp : RclSpecial F x i) : rceR x = rclPx sp := by
  classical
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro z ⟨hz, k, hk⟩
    exact rct_mem_rclPx_of_two F sp hz hk
  · obtain ⟨hQfin, hq, -, -, -, hQψ, -, -⟩ := rcl_psi_props F sp
    have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
    set W := (rclQ F i).comap (rclPsi sp) with hW
    have hWQ : W.map (rclPsi sp) = rclQ F i := by
      rw [hW, Subgroup.map_comap_eq, inf_eq_right.2 hQψ]
    let e1 : ↥(rclPx sp) ≃* ↥W :=
      (Subgroup.equivMapOfInjective W _ (Subgroup.subtype_injective _)).symm
    let e2 : ↥W ≃* ↥(W.map (rclPsi sp)) := Subgroup.equivMapOfInjective W _ hψ
    let e : ↥(rclPx sp) ≃* ↥(rclQ F i) := (e1.trans e2).trans (MulEquiv.subgroupCongr hWQ)
    set M' : Subgroup ↥(rclPx sp) := (rceR x).subgroupOf (rclPx sp) with hM'
    have hM'n : M'.Normal := ⟨fun z hz g => by
      rw [hM', Subgroup.mem_subgroupOf] at hz ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hgx := rclPx_le_centralizer sp g.2
      have h1 : rceR x = rceR ((g : 𝒞[K, σ]) * x * (g : 𝒞[K, σ])⁻¹) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hgx
        rw [show (g : 𝒞[K, σ]) * x * (g : 𝒞[K, σ])⁻¹ = x by rw [hgx]; group]
      rw [h1, rceR_conj]
      exact ⟨z, hz, rfl⟩⟩
    have hM''n : (M'.map e.toMonoidHom).Normal := Subgroup.Normal.map hM'n _ e.surjective
    rcases rct_normal_dichotomy hq (M'.map e.toMonoidHom) with hZ | hT
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hfin : Finite ↥(rclPx sp) := Nat.finite_of_card_ne_zero (by
        rw [card_rclPx]
        exact Nat.card_pos.ne')
      have h2 : 2 ∣ Nat.card ↥(rclPx sp) := by
        have h8 : 2 ∣ ℓ ^ f := by rw [F.hℓ2]; exact dvd_pow_self 2 (by have := F.hf; omega)
        have h9 : 2 ∣ (ℓ ^ f) ^ 3 := dvd_pow h8 (by norm_num)
        obtain ⟨hc1, hc2⟩ := rcl_card_rclQ F i
        rw [card_rclPx]
        rcases F.hε with h | h
        · rw [hc1 h]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h9 _) _
        · rw [hc2 h]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h9 _) _
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(rclPx sp)) 2 h2
      have hzx : (z : 𝒞[K, σ]) ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) :=
        rclPx_le_centralizer sp z.2
      have hz2 : (z : 𝒞[K, σ]) ^ (2 ^ 1) = 1 := by
        rw [pow_one, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
      have hzR : z ∈ M' := by
        rw [hM', Subgroup.mem_subgroupOf]
        exact Subgroup.subset_closure ⟨hzx, 1, hz2⟩
      have hzc : z ∈ Subgroup.center ↥(rclPx sp) := by
        have h1 : e z ∈ Subgroup.center ↥(rclQ F i) := hZ ⟨z, hzR, rfl⟩
        rw [Subgroup.mem_center_iff] at h1 ⊢
        intro g
        apply e.injective
        rw [map_mul, map_mul]
        exact h1 (e g)
      have hzC : (z : 𝒞[K, σ]) ∈ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨u, hu⟩)
      have h3 := rcy_pow_three_of_mem_center F sp z.2 hzC
      have h4 : (z : 𝒞[K, σ]) = 1 := by
        have h5 : (z : 𝒞[K, σ]) ^ 3 = (z : 𝒞[K, σ]) ^ 2 * z := pow_succ _ 2
        rw [h3, show (z : 𝒞[K, σ]) ^ 2 = 1 by simpa using hz2, one_mul] at h5
        exact h5.symm
      have h6 : z = 1 := Subtype.ext h4
      rw [h6, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · have hM'top : M' = ⊤ := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [hT, Subgroup.map_top_of_surjective _ e.surjective]
      intro u hu
      have : (⟨u, hu⟩ : ↥(rclPx sp)) ∈ M' := by
        rw [hM'top]
        exact Subgroup.mem_top _
      exact this

end Lines

end CFSG.RankThree.PartOne.D4RC
