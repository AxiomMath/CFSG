module

public import CFSG.Milestones.ASVolI.A3L3.Lin
public import CFSG.Milestones.ASVolI.A3L3.Defs

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open scoped Pointwise

structure burnsideA315y_Model (F : Type) [Field F] (X : Type) [Group X] where
  Γ : Subgroup (GL (Fin 3) F)
  c : ↥Γ →* X
  ker_c : ∀ g : ↥Γ, c g = 1 ↔
    ∃ μ : Fˣ, (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ
  zh : ↥Γ
  zh_val : (zh : GL (Fin 3) F) = negDiag3 F
  x : F
  y : F
  cc : F
  hxy : x ^ 2 + y ^ 2 ≠ 0
  hcc : cc ≠ 0
  Da : ↥Γ
  Db : ↥Γ
  Da_val : ((Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1
  Db_val : ((Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat (cc • burnsideA315y_qb x y) 1
  S₀ : Subgroup ↥Γ
  S₀_two : IsPGroup 2 ↥S₀
  zh_mem : zh ∈ S₀
  Da_mem : Da ∈ S₀
  Db_mem : Db ∈ S₀
  S₀_comm : ∀ s ∈ S₀, s * zh = zh * s
  S₀_det : ∀ s ∈ S₀, ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
  two_ne : (2 : F) ≠ 0

theorem burnsideA315y_exists_prime_order {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hodd : Odd (Nat.card ↥B)) (h3 : ¬ IsPGroup 3 ↥B) :
    ∃ a ∈ B, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ orderOf a = r := by
  have hex : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card ↥B ∧ r ≠ 3 := by
    by_contra h
    push Not at h
    apply h3
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card ↥B = 3 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun hd hdB => h _ hd hdB)⟩
    exact IsPGroup.of_card hk
  obtain ⟨r, hr, hrB, hr3⟩ := hex
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrB)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
  exact ⟨b, b.2, r, hr, hr2, hr3, by rw [← Subgroup.orderOf_coe] at hb; exact hb⟩

theorem burnsideA315y_commute_of_pow_coprime {G : Type} [Group G] {a z : G} {k : ℕ}
    (hk : Nat.Coprime k (orderOf a)) (h : a ^ k * z = z * a ^ k) : a * z = z * a := by
  have hc : Commute (a ^ k) z := h
  by_cases h0 : orderOf a = 0
  · rw [h0, Nat.coprime_zero_right] at hk
    rw [hk, pow_one] at h
    exact h
  by_cases h1 : orderOf a = 1
  · rw [orderOf_eq_one_iff.mp h1, one_mul, mul_one]
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk
    (by have := Nat.pos_of_ne_zero h0; omega)
  have ha : a = (a ^ k) ^ k' := by
    rw [← pow_mul, ← pow_mod_orderOf, hk', pow_one]
  have : Commute a z := by rw [ha]; exact hc.pow_left k'
  exact this

theorem burnsideA315y_exists_central_involution {G : Type} [Group G] [Finite G] {R S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hRS : R ≤ S) (hR : R ≠ ⊥) (hSR : S ≤ Subgroup.normalizer (R : Set G)) :
    ∃ y ∈ R, y ≠ 1 ∧ y * y = 1 ∧ ∀ s ∈ S, s * y = y * s := by
  classical
  set H : Subgroup ↥S := R.subgroupOf S with hH
  haveI : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hSR g.2) (n : G)).mp hn
    simpa using this
  have hHne : H ≠ ⊥ := by
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
    have hr1 : r ≠ 1 := fun h' => hr1 (Subtype.ext h')
    intro h
    have : (⟨r, hRS hr⟩ : ↥S) ∈ H := by rw [hH, Subgroup.mem_subgroupOf]; exact hr
    rw [h, Subgroup.mem_bot] at this
    exact hr1 (congrArg Subtype.val this)
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 ↥(H ⊓ Subgroup.center ↥S) := (hS.to_subgroup _)
  haveI : Nontrivial ↥(H ⊓ Subgroup.center ↥S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ Subgroup.center ↥S) := by
    rcases hZ2.card_eq_or_dvd with h | h
    · exfalso
      have := (Subgroup.nontrivial_iff_ne_bot _).mp ‹_›
      exact this (Subgroup.eq_bot_of_card_eq _ h)
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ Subgroup.center ↥S)) 2 hdvd
  refine ⟨((w : ↥S) : G), ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp w.2).1
  · intro h
    have h1 : w = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hw
    exact absurd hw (by norm_num)
  · have h1 : w * w = 1 := by rw [← sq, ← hw, pow_orderOf_eq_one]
    have := congrArg (fun v : ↥(H ⊓ Subgroup.center ↥S) => ((v : ↥S) : G)) h1
    simpa using this
  · intro s hs
    have hc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp w.2).2 ⟨s, hs⟩
    exact congrArg Subtype.val hc

namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X] (M : burnsideA315y_Model F X)

@[expose] def Γ₁ : Subgroup ↥M.Γ where
  carrier := {g | ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul] at ha hb ⊢
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
    have h := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (a : GL (Fin 3) F)))
    rw [Units.val_mul, Matrix.det_mul, ha, one_mul, Units.val_one, Matrix.det_one] at h
    exact h

@[expose] def L : Subgroup X := M.Γ₁.map M.c

theorem mem_L {x : X} : x ∈ M.L ↔
    ∃ g : ↥M.Γ, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ M.c g = x := by
  simp [L, Γ₁, Subgroup.mem_map]

@[expose] def S : Subgroup X := M.S₀.map M.c

@[expose] def z : X := M.c M.zh

theorem exists_scalar_of_c_eq_one {g : ↥M.Γ} (h : M.c g = 1) :
    ∃ μ : Fˣ, (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ :=
  (M.ker_c g).mp h

theorem exists_scalar_conj {g h : ↥M.Γ} (hc : M.c g * M.c h = M.c h * M.c g) :
    ∃ μ : Fˣ, (g : GL (Fin 3) F) * h * (g : GL (Fin 3) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μ * h := by
  have h1 : M.c (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
  refine ⟨μ, ?_⟩
  have : (g : GL (Fin 3) F) * h * (g : GL (Fin 3) F)⁻¹ * (h : GL (Fin 3) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [← hμ]
    simp
  rw [← this]
  group

theorem commute_of_trace {g h : ↥M.Γ} (hc : M.c g * M.c h = M.c h * M.c g)
    (htr : trace ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 0) :
    (g : GL (Fin 3) F) * h = h * g := by
  obtain ⟨μ, hμ⟩ := M.exists_scalar_conj hc
  have h1 := burnsideA315y_scalar_eq_one_of_trace hμ htr
  rw [h1, map_one, one_mul] at hμ
  calc (g : GL (Fin 3) F) * h = (g : GL (Fin 3) F) * h * (g : GL (Fin 3) F)⁻¹ * g := by group
    _ = h * g := by rw [hμ]

theorem commute_of_pow {g h : ↥M.Γ} (hc : M.c g * M.c h = M.c h * M.c g) {m : ℕ}
    (hm : M.c h ^ m = 1) (hm3 : Nat.Coprime m 3) :
    (g : GL (Fin 3) F) * h = h * g := by
  obtain ⟨μ, hμ⟩ := M.exists_scalar_conj hc
  obtain ⟨ν, hν⟩ := M.exists_scalar_of_c_eq_one (by rw [map_pow]; exact hm : M.c (h ^ m) = 1)
  have h1 := burnsideA315y_scalar_eq_one_of_pow hμ (by simpa using hν) hm3
  rw [h1, map_one, one_mul] at hμ
  calc (g : GL (Fin 3) F) * h = (g : GL (Fin 3) F) * h * (g : GL (Fin 3) F)⁻¹ * g := by group
    _ = h * g := by rw [hμ]

theorem lift_unique {g₁ g₂ : ↥M.Γ} {m : ℕ} (hm3 : Nat.Coprime m 3)
    (hd₁ : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hd₂ : ((g₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hp₁ : g₁ ^ m = 1) (hp₂ : g₂ ^ m = 1) (hc : M.c g₁ = M.c g₂) : g₁ = g₂ := by
  have h1 : M.c (g₁ * g₂⁻¹) = 1 := by rw [map_mul, map_inv, hc, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
  have hg : (g₁ : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g₂ := by
    rw [← hμ]
    simp
  have hμ3 : μ ^ 3 = 1 := by
    have h2 := congrArg Matrix.GeneralLinearGroup.det hg
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h2
    have e₁ : Matrix.GeneralLinearGroup.det (g₁ : GL (Fin 3) F) = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hd₁, Units.val_one])
    have e₂ : Matrix.GeneralLinearGroup.det (g₂ : GL (Fin 3) F) = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hd₂, Units.val_one])
    rw [e₁, e₂, mul_one] at h2
    exact h2.symm
  have hμm : μ ^ m = 1 := by
    have h2 : (g₁ : GL (Fin 3) F) ^ m = (Matrix.GeneralLinearGroup.scalar (Fin 3) μ) ^ m *
        (g₂ : GL (Fin 3) F) ^ m := by
      rw [hg, Commute.mul_pow (burnsideA315y_scalar_comm μ (g₂ : GL (Fin 3) F))]
    have hp₁' : (g₁ : GL (Fin 3) F) ^ m = 1 := by
      rw [← Subgroup.coe_pow, hp₁, Subgroup.coe_one]
    have hp₂' : (g₂ : GL (Fin 3) F) ^ m = 1 := by
      rw [← Subgroup.coe_pow, hp₂, Subgroup.coe_one]
    rw [hp₁', hp₂', mul_one, ← map_pow] at h2
    have h3 := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F) 0 0) h2
    simp only [Units.val_one, Matrix.one_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h3
    exact Units.ext h3.symm
  have hd : orderOf μ ∣ Nat.gcd m 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hμm)
    (orderOf_dvd_of_pow_eq_one hμ3)
  rw [hm3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  rw [hd, map_one, one_mul] at hg
  exact Subtype.ext hg

theorem exists_lift {x : X} (hx : x ∈ M.L) {m : ℕ} (hm3 : Nat.Coprime m 3) (hxm : x ^ m = 1) :
    ∃ g : ↥M.Γ, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ g ^ m = 1 ∧
      M.c g = x := by
  obtain ⟨g₀, hd, rfl⟩ := M.mem_L.mp hx
  have hc : M.c (g₀ ^ m) = 1 := by rw [map_pow, hxm]
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one hc
  have hμ3 : μ ^ 3 = 1 := by
    have h2 := congrArg Matrix.GeneralLinearGroup.det hμ
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Subgroup.coe_pow, map_pow] at h2
    have e₀ : Matrix.GeneralLinearGroup.det (g₀ : GL (Fin 3) F) = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hd, Units.val_one])
    rw [e₀, one_pow] at h2
    exact h2.symm
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 + j * m) % 3 = 0 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by
      have h := Nat.Coprime.symm hm3
      have : ¬ 3 ∣ m := fun h3 => by
        have := Nat.Coprime.coprime_dvd_right h3 hm3.symm
        norm_num at this
      omega
    rcases this with h | h
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  refine ⟨g₀ * (g₀ ^ m) ^ j, ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      Matrix.det_mul, Matrix.det_pow, hd, one_pow, mul_one]
  · have e1 : (g₀ : GL (Fin 3) F) ^ m = Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [← Subgroup.coe_pow]; exact hμ
    have hcomm : Commute (g₀ : GL (Fin 3) F) (((g₀ : GL (Fin 3) F) ^ m) ^ j) :=
      ((Commute.refl (g₀ : GL (Fin 3) F)).pow_right m).pow_right j
    have hμj : μ * (μ ^ j) ^ m = 1 := by
      rw [← pow_mul, ← pow_succ', show j * m + 1 = 1 + j * m by ring,
        ← Nat.div_add_mod (1 + j * m) 3, hj, add_zero, pow_mul, hμ3, one_pow]
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
    rw [hcomm.mul_pow, e1, ← map_pow, ← map_pow, ← map_mul, hμj, map_one]
  · rw [map_mul, map_pow, hc, one_pow, mul_one]

theorem trace_conj' (g h : GL (Fin 3) F) :
    trace (((g * h * g⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      trace (h : Matrix (Fin 3) (Fin 3) F) := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.trace_units_conj g (h : Matrix (Fin 3) (Fin 3) F)

theorem trace_zh : trace ((M.zh : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = -1 := by
  rw [M.zh_val, coe_negDiag3, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp

theorem trace_zh_ne : trace ((M.zh : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  rw [M.trace_zh]
  exact neg_ne_zero.mpr one_ne_zero

theorem trace_Da : trace ((M.Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [M.Da_val, Matrix.trace_fin_three]
  simp [blkMat, burnsideA315y_qa]

theorem trace_Db : trace ((M.Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [M.Db_val, Matrix.trace_fin_three]
  simp [blkMat, burnsideA315y_qb]

theorem S_le_L : M.S ≤ M.L := by
  rintro _ ⟨s, hs, rfl⟩
  exact M.mem_L.mpr ⟨s, M.S₀_det s hs, rfl⟩

theorem conj_mem_L {g : ↥M.Γ} {l : X} (hl : l ∈ M.L) : M.c g * l * (M.c g)⁻¹ ∈ M.L := by
  obtain ⟨h, hd, rfl⟩ := M.mem_L.mp hl
  refine M.mem_L.mpr ⟨g * h * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [Matrix.det_units_conj, hd]

theorem z_mem_S : M.z ∈ M.S := ⟨M.zh, M.zh_mem, rfl⟩

theorem z_sq : M.z * M.z = 1 := by
  have h : M.zh * M.zh = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, M.zh_val, Subgroup.coe_one, burnsideA315y_negDiag3_sq]
  rw [z, ← map_mul, h, map_one]

theorem zh_sq : M.zh * M.zh = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, M.zh_val, Subgroup.coe_one, burnsideA315y_negDiag3_sq]

theorem det_zh : ((M.zh : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [M.zh_val]; exact burnsideA315y_det_negDiag3

theorem det_conj (g h : ↥M.Γ) :
    (((g * h * g⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj (g : GL (Fin 3) F) _

theorem eq_z_of_central {y : X} (hy : y ∈ M.S) (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hcen : ∀ s ∈ M.S, s * y = y * s) : y = M.z := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hcz := M.commute_of_trace (g := s) (h := M.zh) (hcen _ M.z_mem_S).symm M.trace_zh_ne
  have hca := M.commute_of_trace (g := s) (h := M.Da) (hcen _ ⟨M.Da, M.Da_mem, rfl⟩).symm
    (by rw [M.trace_Da]; exact one_ne_zero)
  have hcb := M.commute_of_trace (g := s) (h := M.Db) (hcen _ ⟨M.Db, M.Db_mem, rfl⟩).symm
    (by rw [M.trace_Db]; exact one_ne_zero)
  have hcz' := congrArg Units.val hcz
  have hca' := congrArg Units.val hca
  have hcb' := congrArg Units.val hcb
  rw [Units.val_mul, Units.val_mul, M.zh_val, coe_negDiag3] at hcz'
  rw [Units.val_mul, Units.val_mul, M.Da_val] at hca'
  rw [Units.val_mul, Units.val_mul, M.Db_val] at hcb'
  have hxy0 : M.x ≠ 0 ∨ M.y ≠ 0 := by
    by_contra h
    push Not at h
    apply M.hxy
    rw [h.1, h.2]
    ring
  obtain ⟨e01, e10, e11, e02, e12, e20, e21⟩ :=
    burnsideA315y_commutant M.two_ne hxy0 M.hcc hcz' hca' hcb'
  set S0 := ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hS0
  set u := S0 0 0
  set w := S0 2 2
  have hsq : M.c (s * s) = 1 := by rw [map_mul, hy2]
  obtain ⟨ν, hν⟩ := M.exists_scalar_of_c_eq_one hsq
  have hν' := congrArg Units.val hν
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hν'
  have q00 := congrFun (congrFun hν' 0) 0
  have q22 := congrFun (congrFun hν' 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, ← hS0, e01, e10, e11, e02, e12, e20, e21] at q00 q22
  have huw : u ^ 2 = w ^ 2 := by
    rw [sq, sq]
    exact q00.trans q22.symm
  have hu0 : u ≠ 0 := by
    intro h
    have hdet := M.S₀_det s hs
    rw [← hS0, Matrix.det_fin_three] at hdet
    simp [e01, e10, e11, e02, e12, e20, e21, ← hS0] at hdet
    rw [show S0 0 0 = u from rfl, h] at hdet
    simp at hdet
  have hS0eq : S0 = !![u, 0, 0; 0, u, 0; 0, 0, w] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10, e11, e02, e12, e20, e21] <;> rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp huw.symm with h | h
  ·
    exfalso
    apply hy1
    rw [M.ker_c]
    refine ⟨Units.mk0 u hu0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, ← hS0, hS0eq, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  ·
    have hsz : M.c (s * M.zh⁻¹) = 1 := by
      rw [M.ker_c]
      refine ⟨Units.mk0 (-u) (neg_ne_zero.mpr hu0), Units.ext ?_⟩
      have hzinv : ((M.zh⁻¹ : ↥M.Γ) : GL (Fin 3) F) = negDiag3 F := by
        have : M.zh⁻¹ = M.zh := inv_eq_of_mul_eq_one_right M.zh_sq
        rw [this, M.zh_val]
      rw [Subgroup.coe_mul, hzinv, Units.val_mul, coe_negDiag3, Matrix.GeneralLinearGroup.coe_scalar,
        ← hS0, hS0eq, h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
        diagonal]
    rw [map_mul, map_inv, mul_inv_eq_one] at hsz
    exact hsz

theorem exists_inv_lift {y : X} (hy : y ∈ M.L) (hy2 : y * y = 1) :
    ∃ g : ↥M.Γ, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ g * g = 1 ∧
      M.c g = y := by
  obtain ⟨g, hd, hg, hc⟩ := M.exists_lift hy (m := 2) (by norm_num) (by rw [sq]; exact hy2)
  exact ⟨g, hd, by rw [← sq]; exact hg, hc⟩

theorem burnsideA315y_closure_sq {G : Type} [Group G] {T : Set G} (hT : ∀ t ∈ T, t * t = 1)
    (hc : T.Pairwise Commute) : ∀ x ∈ Subgroup.closure T, x * x = 1 := by
  have hab := Subgroup.isMulCommutative_closure hc
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact hT t ht
  | one => simp
  | mul a b ha hb iha ihb =>
    have hcomm : a * b = b * a := by
      have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← _root_.mul_inv_rev, iha, inv_one]

theorem three_involutions [Finite F] [Finite X] {y₁ y₂ y₃ : X} (h₁ : y₁ ∈ M.L) (h₂ : y₂ ∈ M.L)
    (h₃ : y₃ ∈ M.L) (s₁ : y₁ * y₁ = 1) (s₂ : y₂ * y₂ = 1) (s₃ : y₃ * y₃ = 1) (n₁ : y₁ ≠ 1)
    (n₂ : y₂ ≠ 1) (n₃ : y₃ ≠ 1) (c₁₂ : y₁ * y₂ = y₂ * y₁) (c₁₃ : y₁ * y₃ = y₃ * y₁)
    (c₂₃ : y₂ * y₃ = y₃ * y₂) (d₁₂ : y₁ ≠ y₂) (d₁₃ : y₁ ≠ y₃) (d₂₃ : y₂ ≠ y₃) :
    y₃ = y₁ * y₂ := by
  classical
  by_contra hne
  obtain ⟨g₁, hd₁, hg₁, rfl⟩ := M.exists_inv_lift h₁ s₁
  obtain ⟨g₂, hd₂, hg₂, rfl⟩ := M.exists_inv_lift h₂ s₂
  obtain ⟨g₃, hd₃, hg₃, rfl⟩ := M.exists_inv_lift h₃ s₃
  have hcomm : ∀ {g h : ↥M.Γ}, M.c g * M.c h = M.c h * M.c g → M.c h * M.c h = 1 → g * h = h * g :=
    fun {g h} hgh hh => Subtype.ext (M.commute_of_pow hgh (m := 2) (by rw [sq]; exact hh)
      (by norm_num))
  set T : Set ↥M.Γ := {g₁, g₂, g₃} with hTdef
  have hTsq : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    rcases ht with rfl | rfl | rfl
    · exact hg₁
    · exact hg₂
    · exact hg₃
  have hTc : T.Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hcomm c₁₂ s₂ | exact hcomm c₁₂.symm s₁ | exact hcomm c₁₃ s₃
      | exact hcomm c₁₃.symm s₁ | exact hcomm c₂₃ s₃ | exact hcomm c₂₃.symm s₂
  set E := Subgroup.closure T with hE
  have hEsq := burnsideA315y_closure_sq hTsq hTc
  have hEdet : ∀ x ∈ E, ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    intro x hx
    have hle : E ≤ M.Γ₁ := by
      rw [hE, Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | rfl | rfl
      · exact hd₁
      · exact hd₂
      · exact hd₃
    exact hle hx
  have h4 : Nat.card ↥(E.map M.Γ.subtype) ≤ 4 := by
    refine card_le_four_of_sq_eq_one_sl3 M.two_ne _ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hEsq x hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact hEdet x hx
  have hEcard : Nat.card ↥E ≤ 4 := by
    rwa [Subgroup.card_map_of_injective M.Γ.subtype_injective] at h4
  have hmem : ∀ g ∈ E, M.c g ∈ E.map M.c := fun g hg => ⟨g, hg, rfl⟩
  have hsub : (({1, M.c g₁, M.c g₂, M.c g₃, M.c g₁ * M.c g₂} : Finset X) : Set X) ⊆
      (E.map M.c : Set X) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact (E.map M.c).one_mem
    · exact hmem _ (Subgroup.subset_closure (by simp [hTdef]))
    · exact hmem _ (Subgroup.subset_closure (by simp [hTdef]))
    · exact hmem _ (Subgroup.subset_closure (by simp [hTdef]))
    · rw [← map_mul]
      exact hmem _ (E.mul_mem (Subgroup.subset_closure (by simp [hTdef]))
        (Subgroup.subset_closure (by simp [hTdef])))
  have hp1 : M.c g₁ * M.c g₂ ≠ 1 := by
    intro h
    apply d₁₂
    calc M.c g₁ = M.c g₁ * (M.c g₂ * M.c g₂) := by rw [s₂, mul_one]
      _ = (M.c g₁ * M.c g₂) * M.c g₂ := by group
      _ = M.c g₂ := by rw [h, one_mul]
  have hp2 : M.c g₁ * M.c g₂ ≠ M.c g₁ := by
    intro h
    apply n₂
    calc M.c g₂ = (M.c g₁)⁻¹ * (M.c g₁ * M.c g₂) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hp3 : M.c g₁ * M.c g₂ ≠ M.c g₂ := by
    intro h
    apply n₁
    calc M.c g₁ = (M.c g₁ * M.c g₂) * (M.c g₂)⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have hcard5 : ({1, M.c g₁, M.c g₂, M.c g₃, M.c g₁ * M.c g₂} : Finset X).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hne h
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨d₂₃, fun h => hp3 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨d₁₂, d₁₃, fun h => hp2 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => n₁ h.symm, fun h => n₂ h.symm, fun h => n₃ h.symm, fun h => hp1 h.symm⟩
  have h5 : 5 ≤ Nat.card ↥(E.map M.c) := by
    calc 5 = Nat.card ↥(({1, M.c g₁, M.c g₂, M.c g₃, M.c g₁ * M.c g₂} : Finset X) : Set X) := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard5]
      _ ≤ Nat.card ↥((E.map M.c : Subgroup X) : Set X) := Nat.card_mono (Set.toFinite _) hsub
      _ = Nat.card ↥(E.map M.c) := rfl
  have hle : Nat.card ↥(E.map M.c) ≤ Nat.card ↥E :=
    Nat.card_le_card_of_surjective _ (M.c.subgroupMap_surjective E)
  omega

theorem caseI [Finite F] [Finite X] {B R : Subgroup X} (hBc : B ≤ M.c.range)
    (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B)) (h3 : ¬ IsPGroup 3 ↥B)
    (hRS : R ≤ M.S) (hR : R ≠ ⊥) (hBR : B ≤ Subgroup.normalizer (R : Set X))
    (hSR : M.S ≤ Subgroup.normalizer (R : Set X)) :
    ∀ b ∈ B, b * M.z = M.z * b := by
  classical
  have hS2 : IsPGroup 2 ↥M.S := M.S₀_two.map M.c
  obtain ⟨y, hyR, hy1, hy2, hyc⟩ := burnsideA315y_exists_central_involution hS2 hRS hR hSR
  have hyz : y = M.z := M.eq_z_of_central (hRS hyR) hy1 hy2 hyc
  have hzR : M.z ∈ R := hyz ▸ hyR
  have hzcR : ∀ r ∈ R, r * M.z = M.z * r := fun r hr => by
    rw [← hyz]; exact hyc r (hRS hr)
  have hconjR : ∀ b ∈ B, b * M.z * b⁻¹ ∈ R := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp (hBR hb) M.z).mp hzR
  have hcommR : ∀ b ∈ B, ∀ r ∈ R, (b * M.z * b⁻¹) * r = r * (b * M.z * b⁻¹) := by
    intro b hb r hr
    have hr' : b⁻¹ * r * b ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hBR (B.inv_mem hb)) r).mp hr
      simpa using this
    have := hzcR _ hr'
    calc b * M.z * b⁻¹ * r = b * (M.z * (b⁻¹ * r * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * r * b) * M.z) * b⁻¹ := by rw [this]
      _ = r * (b * M.z * b⁻¹) := by group
  have hcc : ∀ b ∈ B, ∀ b' ∈ B, (b * M.z * b⁻¹) * (b' * M.z * b'⁻¹) =
      (b' * M.z * b'⁻¹) * (b * M.z * b⁻¹) := fun b hb b' hb' =>
    hcommR b hb _ (hconjR b' hb')
  have hzL : M.z ∈ M.L := M.S_le_L M.z_mem_S
  have hconjL : ∀ b ∈ B, b * M.z * b⁻¹ ∈ M.L := by
    intro b hb
    obtain ⟨g, rfl⟩ := hBc hb
    exact M.conj_mem_L hzL
  have hconj_sq : ∀ b : X, (b * M.z * b⁻¹) * (b * M.z * b⁻¹) = 1 := by
    intro b
    calc b * M.z * b⁻¹ * (b * M.z * b⁻¹) = b * (M.z * M.z) * b⁻¹ := by group
      _ = 1 := by rw [M.z_sq, mul_one, mul_inv_cancel]
  have hz1 : M.z ≠ 1 := by
    intro h
    have := (M.ker_c M.zh).mp h
    obtain ⟨μ, hμ⟩ := this
    have h00 := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F) 0 0) hμ
    have h22 := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F) 2 2) hμ
    simp only [M.zh_val, coe_negDiag3, Matrix.GeneralLinearGroup.coe_scalar] at h00 h22
    simp at h00 h22
    apply M.two_ne
    linear_combination h22 - h00
  have hconj_ne : ∀ b : X, b * M.z * b⁻¹ ≠ 1 := by
    intro b h
    apply hz1
    calc M.z = b⁻¹ * (b * M.z * b⁻¹) * b := by group
      _ = 1 := by rw [h]; group
  have hcomm_conj : ∀ b : X, b * M.z * b⁻¹ = M.z ↔ b * M.z = M.z * b := by
    intro b
    constructor
    · intro h
      calc b * M.z = b * M.z * b⁻¹ * b := by group
        _ = M.z * b := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀, hb₀z⟩ := hcon
  obtain ⟨a, haB, r, hr, hr2, hr3, hra⟩ := burnsideA315y_exists_prime_order hodd h3
  have hBc' : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hr5 : 5 ≤ r := by
    have := hr.two_le
    rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with h | h | h | h
    · exact absurd h hr2
    · exact absurd h hr3
    · subst h; exact absurd hr (by norm_num)
    · exact h
  have hcopr : ∀ k, 1 ≤ k → k ≤ 3 → Nat.Coprime k (orderOf a) := by
    intro k hk1 hk3
    rw [hra]
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have haz : a * M.z = M.z * a := by
    by_contra haz
    have hpowz : ∀ k, 1 ≤ k → k ≤ 3 → a ^ k * M.z ≠ M.z * a ^ k := fun k hk1 hk3 h =>
      haz (burnsideA315y_commute_of_pow_coprime (hcopr k hk1 hk3) h)
    set z₁ := a * M.z * a⁻¹
    set z₂ := a ^ 2 * M.z * (a ^ 2)⁻¹
    set z₃ := a ^ 3 * M.z * (a ^ 3)⁻¹
    have hdist : ∀ i j : ℕ, i < j → j ≤ 3 → a ^ i * M.z * (a ^ i)⁻¹ ≠ a ^ j * M.z * (a ^ j)⁻¹ := by
      intro i j hij hj h
      apply hpowz (j - i) (by omega) (by omega)
      have h' : a ^ (j - i) * M.z * (a ^ (j - i))⁻¹ = M.z := by
        have e : a ^ j = a ^ i * a ^ (j - i) := by rw [← pow_add]; congr 1; omega
        rw [e] at h
        have := congrArg (fun w => (a ^ i)⁻¹ * w * a ^ i) h
        rw [show (a ^ i)⁻¹ * (a ^ i * M.z * (a ^ i)⁻¹) * a ^ i = M.z by group,
          show (a ^ i)⁻¹ * (a ^ i * a ^ (j - i) * M.z * (a ^ i * a ^ (j - i))⁻¹) * a ^ i =
            a ^ (j - i) * M.z * (a ^ (j - i))⁻¹ by group] at this
        exact this.symm
      exact (hcomm_conj _).mp h'
    have hpB : ∀ k : ℕ, a ^ k ∈ B := fun k => B.pow_mem haB k
    have e1 := M.three_involutions hzL (hconjL _ (hpB 1)) (hconjL _ (hpB 2)) M.z_sq
      (by simpa using hconj_sq (a ^ 1)) (hconj_sq _) hz1 (by simpa using hconj_ne (a ^ 1))
      (hconj_ne _)
      (by simpa using (hcc 1 (B.one_mem) _ (hpB 1)))
      (by simpa using (hcc 1 (B.one_mem) _ (hpB 2)))
      (hcc _ (hpB 1) _ (hpB 2))
      (by simpa using hdist 0 1 (by norm_num) (by norm_num))
      (by simpa using hdist 0 2 (by norm_num) (by norm_num))
      (hdist 1 2 (by norm_num) (by norm_num))
    have e2 := M.three_involutions hzL (hconjL _ (hpB 1)) (hconjL _ (hpB 3)) M.z_sq
      (by simpa using hconj_sq (a ^ 1)) (hconj_sq _) hz1 (by simpa using hconj_ne (a ^ 1))
      (hconj_ne _)
      (by simpa using (hcc 1 (B.one_mem) _ (hpB 1)))
      (by simpa using (hcc 1 (B.one_mem) _ (hpB 3)))
      (hcc _ (hpB 1) _ (hpB 3))
      (by simpa using hdist 0 1 (by norm_num) (by norm_num))
      (by simpa using hdist 0 3 (by norm_num) (by norm_num))
      (hdist 1 3 (by norm_num) (by norm_num))
    exact hdist 2 3 (by norm_num) (by norm_num) (e1.trans e2.symm)
  set z' := b₀ * M.z * b₀⁻¹ with hz'
  set z'' := b₀ * z' * b₀⁻¹ with hz''
  have hz'z : z' ≠ M.z := fun h => hb₀z ((hcomm_conj b₀).mp h)
  have hb₀odd : Odd (orderOf b₀) := by
    have h1 : orderOf (⟨b₀, hb₀⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hz''z : z'' ≠ M.z := by
    intro h
    apply hb₀z
    have h2 : b₀ ^ 2 * M.z = M.z * b₀ ^ 2 := by
      rw [← hcomm_conj]
      rw [hz'', hz'] at h
      calc b₀ ^ 2 * M.z * (b₀ ^ 2)⁻¹ = b₀ * (b₀ * M.z * b₀⁻¹) * b₀⁻¹ := by rw [sq]; group
        _ = M.z := h
    exact burnsideA315y_commute_of_pow_coprime (Nat.coprime_two_left.mpr hb₀odd) h2
  have hz''z' : z'' ≠ z' := by
    intro h
    apply hz'z
    have := congrArg (fun w => b₀⁻¹ * w * b₀) h
    simp only [hz'', hz'] at this
    rw [show b₀⁻¹ * (b₀ * (b₀ * M.z * b₀⁻¹) * b₀⁻¹) * b₀ = b₀ * M.z * b₀⁻¹ by group,
      show b₀⁻¹ * (b₀ * M.z * b₀⁻¹) * b₀ = M.z by group] at this
    exact this
  have hz''eq : z'' = M.z * z' := by
    have hb2 : b₀ * b₀ ∈ B := B.mul_mem hb₀ hb₀
    have e : z'' = (b₀ * b₀) * M.z * (b₀ * b₀)⁻¹ := by rw [hz'', hz']; group
    refine M.three_involutions hzL (hconjL _ hb₀) (e ▸ hconjL _ hb2) M.z_sq (hconj_sq _)
      (e ▸ hconj_sq _) hz1 (hconj_ne _) (e ▸ hconj_ne _) ?_ ?_ ?_ hz'z.symm hz''z.symm hz''z'.symm
    · simpa using hcc 1 B.one_mem _ hb₀
    · rw [e]; simpa using hcc 1 B.one_mem _ hb2
    · rw [e]; exact hcc _ hb₀ _ hb2
  obtain ⟨ah, rfl⟩ := hBc haB
  obtain ⟨bh, rfl⟩ := hBc hb₀
  set th : ↥M.Γ := bh * M.zh * bh⁻¹ with hth
  have hcth : M.c th = z' := by rw [hth, map_mul, map_mul, map_inv]; rfl
  have htr : trace ((th : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    rw [hth, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, trace_conj']
    exact M.trace_zh_ne
  have h_az : (ah : GL (Fin 3) F) * M.zh = M.zh * ah := M.commute_of_trace haz M.trace_zh_ne
  have h_at : (ah : GL (Fin 3) F) * th = th * ah := by
    refine M.commute_of_trace ?_ htr
    rw [hcth, hz']
    calc M.c ah * (M.c bh * M.z * (M.c bh)⁻¹) = M.c bh * (M.c ah * M.z) * (M.c bh)⁻¹ := by
          rw [show M.c ah * (M.c bh * M.z * (M.c bh)⁻¹) =
            (M.c ah * M.c bh) * M.z * (M.c bh)⁻¹ by group, hBc' _ haB _ hb₀]
          group
      _ = M.c bh * (M.z * M.c ah) * (M.c bh)⁻¹ := by rw [haz]
      _ = M.c bh * M.z * (M.c bh)⁻¹ * M.c ah := by
          rw [show M.c bh * (M.z * M.c ah) * (M.c bh)⁻¹ =
            M.c bh * M.z * ((M.c bh)⁻¹ * M.c bh) * (M.c ah * (M.c bh)⁻¹) by group]
          rw [inv_mul_cancel, mul_one]
          have : M.c ah * (M.c bh)⁻¹ = (M.c bh)⁻¹ * M.c ah := by
            have h1 := hBc' _ haB _ hb₀
            calc M.c ah * (M.c bh)⁻¹ = (M.c bh)⁻¹ * (M.c bh * M.c ah) * (M.c bh)⁻¹ := by group
              _ = (M.c bh)⁻¹ * (M.c ah * M.c bh) * (M.c bh)⁻¹ := by rw [h1]
              _ = (M.c bh)⁻¹ * M.c ah := by group
          rw [this]
          group
  have h_ab : (ah : GL (Fin 3) F) * bh = bh * ah := by
    have := M.commute_of_pow (g := bh) (h := ah) (hBc' _ hb₀ _ haB) (m := r)
      (by rw [← hra, pow_orderOf_eq_one]) ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
    exact this.symm
  have h_tz : (th : GL (Fin 3) F) * M.zh = M.zh * th := by
    refine M.commute_of_trace ?_ M.trace_zh_ne
    rw [hcth]
    have := hcc 1 B.one_mem _ hb₀
    simp only [one_mul, inv_one, mul_one] at this
    exact this.symm
  have h_tne : (th : GL (Fin 3) F) ≠ negDiag3 F := by
    intro h
    apply hz'z
    rw [← hcth, z]
    congr 1
    apply Subtype.ext
    rw [h, M.zh_val]
  have h_bt : (bh : GL (Fin 3) F) * th * (bh : GL (Fin 3) F)⁻¹ = negDiag3 F * th := by
    have h1 : bh * th * bh⁻¹ = M.zh * th := by
      refine M.lift_unique (m := 2) (by norm_num) ?_ ?_ ?_ ?_ ?_
      · rw [M.det_conj, hth, M.det_conj, M.det_zh]
      · rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hth, M.det_conj, M.det_zh, mul_one]
      · rw [sq, hth]
        calc bh * (bh * M.zh * bh⁻¹) * bh⁻¹ * (bh * (bh * M.zh * bh⁻¹) * bh⁻¹) =
            bh * bh * (M.zh * M.zh) * bh⁻¹ * bh⁻¹ := by group
          _ = 1 := by rw [M.zh_sq, mul_one]; group
      · have hc' : (M.zh : GL (Fin 3) F) * th = th * M.zh := h_tz.symm
        have hc'' : M.zh * th = th * M.zh := Subtype.ext hc'
        rw [sq, show M.zh * th * (M.zh * th) = M.zh * (th * M.zh) * th by group, ← hc'',
          show M.zh * (M.zh * th) * th = (M.zh * M.zh) * (th * th) by group, M.zh_sq, one_mul,
          hth]
        calc bh * M.zh * bh⁻¹ * (bh * M.zh * bh⁻¹) = bh * (M.zh * M.zh) * bh⁻¹ := by group
          _ = 1 := by rw [M.zh_sq, mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv, hcth, map_mul, hcth]
        exact hz''eq
    have := congrArg Subtype.val h1
    simpa [M.zh_val] using this
  have hscal := burnsideA315y_frame M.two_ne (a := ah) (b := bh) (t := th)
    (by rw [← M.zh_val]; exact h_az) (by rw [hth]; simp [M.zh_val])
    h_at h_ab (by rw [← M.zh_val]; exact h_tz) h_tne h_bt
  have ha1 : M.c ah = 1 := by
    rw [M.ker_c]
    have hw0 : ((ah : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
      intro h0
      have hdet := congrArg Matrix.det hscal
      rw [h0, zero_smul, Matrix.det_zero] at hdet
      exact (Matrix.isUnit_iff_isUnit_det _ |>.mp (ah : GL (Fin 3) F).isUnit).ne_zero hdet
    refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    conv_lhs => rw [hscal]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [ha1, orderOf_one] at hra
  exact absurd hra.symm hr.ne_one

@[expose] def burnsideA315y_m3 (n : ℕ) : ℕ := n / 3 ^ n.factorization 3

theorem burnsideA315y_m3_coprime {n : ℕ} (hn : n ≠ 0) : Nat.Coprime (burnsideA315y_m3 n) 3 :=
  (Nat.coprime_ordCompl Nat.prime_three hn).symm

theorem burnsideA315y_m3_dvd (n : ℕ) : burnsideA315y_m3 n ∣ n := Nat.ordCompl_dvd n 3

theorem burnsideA315y_dvd_m3 {n r : ℕ} (hn : n ≠ 0) (hr : r.Prime) (hr3 : r ≠ 3) (hrn : r ∣ n) :
    r ∣ burnsideA315y_m3 n := by
  have hcop : Nat.Coprime r (3 ^ n.factorization 3) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
  have h := Nat.ordProj_mul_ordCompl_eq_self n 3
  rw [← h] at hrn
  exact hcop.dvd_of_dvd_mul_left hrn

@[expose] def burnsideA315y_powSub {G : Type} [Group G] (B : Subgroup G) (hab : IsMulCommutative ↥B)
    (m : ℕ) : Subgroup G where
  carrier := {x | x ∈ B ∧ x ^ m = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨B.mul_mem hx hy, ?_⟩
    have hc : Commute x y := congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hc.mul_pow, hxm, hym, one_mul]
  one_mem' := ⟨B.one_mem, one_pow m⟩
  inv_mem' := by
    rintro x ⟨hx, hxm⟩
    exact ⟨B.inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩

@[expose] def DichE (B : Subgroup X) : Prop :=
  ∃ E : Subgroup ↥M.Γ, E ≠ ⊥ ∧ (∀ e ∈ E, ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1) ∧
    ((∀ e ∈ E, burnsideA315y_IsUW ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∨
      (∀ e ∈ E, burnsideA315y_IsUl ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) ∧
    E.map M.c ≤ B ∧
    (∀ e ∈ E, M.Da⁻¹ * e * M.Da ∈ E ∧ M.Da * e * M.Da⁻¹ ∈ E) ∧
    (∀ e ∈ E, M.Db⁻¹ * e * M.Db ∈ E ∧ M.Db * e * M.Db⁻¹ ∈ E) ∧
    ∀ b ∈ B, ∃ g : ↥M.Γ, M.c g = b ∧ ∀ e ∈ E, g * e = e * g

theorem caseII [Finite F] [Finite X] {B : Subgroup X} (hBc : B ≤ M.c.range)
    (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B)) (h3 : ¬ IsPGroup 3 ↥B)
    (hSB : M.S ≤ Subgroup.normalizer (B : Set X)) :
    (∀ b ∈ B, b * M.z = M.z * b) ∨ M.DichE B := by
  classical
  set m := burnsideA315y_m3 (Nat.card ↥B) with hm
  have hn0 : Nat.card ↥B ≠ 0 := Nat.card_pos.ne'
  have hm3 : Nat.Coprime m 3 := burnsideA315y_m3_coprime hn0
  have hmodd : Odd m := Odd.of_dvd_nat hodd (burnsideA315y_m3_dvd _)
  set A := burnsideA315y_powSub B hab m with hA
  have hAB : A ≤ B := fun x hx => hx.1
  have hBc' : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hSA : ∀ s ∈ M.S, ∀ x ∈ A, s * x * s⁻¹ ∈ A := by
    rintro s hs x ⟨hx, hxm⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hSB hs) x).mp hx, ?_⟩
    rw [conj_pow, hxm, mul_one, mul_inv_cancel]
  have hSA' : ∀ s ∈ M.S, ∀ x ∈ A, s⁻¹ * x * s ∈ A := by
    intro s hs x hx
    have := hSA s⁻¹ (M.S.inv_mem hs) x hx
    rwa [inv_inv] at this
  obtain ⟨a, haB, r, hr, hr2, hr3, hra⟩ := burnsideA315y_exists_prime_order hodd h3
  have haA : a ∈ A := by
    refine ⟨haB, ?_⟩
    have hrB : r ∣ Nat.card ↥B := by
      rw [← hra, ← Subgroup.orderOf_mk a haB]
      exact orderOf_dvd_natCard _
    rw [← orderOf_dvd_iff_pow_eq_one, hra]
    exact burnsideA315y_dvd_m3 hn0 hr hr3 hrB
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hra
    exact hr.ne_one hra.symm
  have hz2 : M.z * M.z = 1 := M.z_sq
  have hzinv : M.z⁻¹ = M.z := inv_eq_of_mul_eq_one_right hz2
  have hzS : M.z ∈ M.S := M.z_mem_S
  have hDaS : M.c M.Da ∈ M.S := ⟨M.Da, M.Da_mem, rfl⟩
  have hDbS : M.c M.Db ∈ M.S := ⟨M.Db, M.Db_mem, rfl⟩
  have hDaz : M.Da * M.zh = M.zh * M.Da := M.S₀_comm _ M.Da_mem
  have hDbz : M.Db * M.zh = M.zh * M.Db := M.S₀_comm _ M.Db_mem
  have hAm : ∀ x ∈ A, x ^ m = 1 := fun x hx => hx.2
  by_cases hAz : ∀ x ∈ A, x * M.z = M.z * x
  ·
    left
    set 𝒜 : Set (GL (Fin 3) F) := {g | ∃ γ : ↥M.Γ, (γ : GL (Fin 3) F) = g ∧ M.c γ ∈ A ∧
      (γ : GL (Fin 3) F) * negDiag3 F = negDiag3 F * γ} with h𝒜
    have hzhv : (M.zh : GL (Fin 3) F) = negDiag3 F := M.zh_val
    have h𝒜z : ∀ g ∈ 𝒜, g * negDiag3 F = negDiag3 F * g := by
      rintro _ ⟨γ, rfl, -, hγ⟩
      exact hγ
    have hconj𝒜 : ∀ D : ↥M.Γ, M.c D ∈ M.S → D * M.zh = M.zh * D → ∀ g ∈ 𝒜,
        ((D : GL (Fin 3) F))⁻¹ * g * D ∈ 𝒜 ∧ (D : GL (Fin 3) F) * g * (D : GL (Fin 3) F)⁻¹ ∈ 𝒜 := by
      rintro D hD hDz _ ⟨γ, rfl, hγA, hγz⟩
      have hDz' : (D : GL (Fin 3) F) * negDiag3 F = negDiag3 F * D := by
        rw [← hzhv, ← Subgroup.coe_mul, hDz, Subgroup.coe_mul]
      constructor
      · refine ⟨D⁻¹ * γ * D, by simp, ?_, ?_⟩
        · rw [map_mul, map_mul, map_inv]
          exact hSA' _ hD _ hγA
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          have h1 : Commute (D : GL (Fin 3) F)⁻¹ (negDiag3 F) := Commute.inv_left hDz'
          exact Commute.mul_left (Commute.mul_left h1 hγz) hDz'
      · refine ⟨D * γ * D⁻¹, by simp, ?_, ?_⟩
        · rw [map_mul, map_mul, map_inv]
          exact hSA _ hD _ hγA
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          have h1 : Commute (D : GL (Fin 3) F)⁻¹ (negDiag3 F) := Commute.inv_left hDz'
          exact Commute.mul_left (Commute.mul_left hDz' hγz) h1
    obtain ⟨γa, rfl⟩ := hBc haB
    have hγaz : (γa : GL (Fin 3) F) * negDiag3 F = negDiag3 F * γa := by
      rw [← hzhv]; exact M.commute_of_trace (hAz _ haA) M.trace_zh_ne
    have h𝒜ns : ∃ g ∈ 𝒜, ∃ v : Fin 3 → F,
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ≠ (g : Matrix (Fin 3) (Fin 3) F) 2 2 • v := by
      refine ⟨γa, ⟨γa, rfl, haA, hγaz⟩, ?_⟩
      by_contra hall
      push Not at hall
      apply ha1
      rw [M.ker_c]
      have hw0 : ((γa : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
        intro h0
        have := hall ![0, 0, 1]
        rw [h0, zero_smul] at this
        have hinj := (Matrix.mulVec_injective_iff_isUnit).mpr (γa : GL (Fin 3) F).isUnit
        have : (![0, 0, 1] : Fin 3 → F) = 0 := hinj (by rw [this, Matrix.mulVec_zero])
        have := congrFun this 2
        simp at this
      refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one] at this
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm] using this
    intro b hb
    obtain ⟨bh, rfl⟩ := hBc hb
    have hbcomm : ∀ g ∈ 𝒜, (bh : GL (Fin 3) F) * g = g * bh := by
      rintro _ ⟨γ, rfl, hγA, -⟩
      exact M.commute_of_pow (hBc' _ hb _ (hAB hγA)) (hAm _ hγA) hm3
    have hbz := burnsideA315y_caseII1 M.two_ne M.hxy M.hcc M.Da_val M.Db_val 𝒜 h𝒜z h𝒜ns
      (hconj𝒜 M.Da hDaS hDaz) (hconj𝒜 M.Db hDbS hDbz) bh hbcomm
    have h1 : bh * M.zh = M.zh * bh := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hzhv]; exact hbz)
    rw [z, ← map_mul, h1, map_mul]
  ·
    right
    push Not at hAz
    obtain ⟨a₀, ha₀A, ha₀z⟩ := hAz
    have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => hBc' u (hAB hu) v (hAB hv)
    let E₁ : Subgroup X :=
      { carrier := {e | e ∈ A ∧ e ∈ M.L ∧ M.z * e * M.z⁻¹ = e⁻¹}
        mul_mem' := by
          rintro e f ⟨heA, heL, he⟩ ⟨hfA, hfL, hf⟩
          refine ⟨A.mul_mem heA hfA, M.L.mul_mem heL hfL, ?_⟩
          calc M.z * (e * f) * M.z⁻¹ = (M.z * e * M.z⁻¹) * (M.z * f * M.z⁻¹) := by group
            _ = e⁻¹ * f⁻¹ := by rw [he, hf]
            _ = (e * f)⁻¹ := by
              rw [_root_.mul_inv_rev]
              have := hAc _ (A.inv_mem heA) _ (A.inv_mem hfA)
              exact this
        one_mem' := ⟨A.one_mem, M.L.one_mem, by group⟩
        inv_mem' := by
          rintro e ⟨heA, heL, he⟩
          refine ⟨A.inv_mem heA, M.L.inv_mem heL, ?_⟩
          rw [inv_inv]
          calc M.z * e⁻¹ * M.z⁻¹ = (M.z * e * M.z⁻¹)⁻¹ := by group
            _ = e := by rw [he, inv_inv] }
    have hE₁m : ∀ e ∈ E₁, e ^ m = 1 := fun e he => hAm e he.1
    have hE₁S : ∀ s ∈ M.S, M.c M.zh * s = s * M.c M.zh → ∀ e ∈ E₁,
        s * e * s⁻¹ ∈ E₁ ∧ s⁻¹ * e * s ∈ E₁ := by
      rintro s hs hsz e ⟨heA, heL, he⟩
      have hsz' : M.z * s = s * M.z := hsz
      have hLconj : ∀ t ∈ M.S, t * e * t⁻¹ ∈ M.L := by
        rintro t ⟨σ, -, rfl⟩
        exact M.conj_mem_L heL
      have hz1 : M.z = s * M.z * s⁻¹ := by rw [← hsz', mul_inv_cancel_right]
      have hz2 : M.z = s⁻¹ * M.z * s := by rw [mul_assoc, hsz', inv_mul_cancel_left]
      refine ⟨⟨hSA s hs e heA, hLconj s hs, ?_⟩, ⟨hSA' s hs e heA, ?_, ?_⟩⟩
      · calc M.z * (s * e * s⁻¹) * M.z⁻¹ = s * (M.z * e * M.z⁻¹) * s⁻¹ := by
              conv_lhs => rw [hz1]
              group
          _ = (s * e * s⁻¹)⁻¹ := by rw [he]; group
      · have := hLconj s⁻¹ (M.S.inv_mem hs)
        rwa [inv_inv] at this
      · calc M.z * (s⁻¹ * e * s) * M.z⁻¹ = s⁻¹ * (M.z * e * M.z⁻¹) * s := by
              conv_lhs => rw [hz2]
              group
          _ = (s⁻¹ * e * s)⁻¹ := by rw [he]; group
    let Eh : Subgroup ↥M.Γ :=
      { carrier := {γ | ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ γ ^ m = 1 ∧
          M.c γ ∈ E₁}
        mul_mem' := by
          rintro g h ⟨hgd, hgm, hgE⟩ ⟨hhd, hhm, hhE⟩
          have hc : g * h = h * g := Subtype.ext (M.commute_of_pow
            (hAc _ hgE.1 _ hhE.1) (hE₁m _ hhE) hm3)
          refine ⟨?_, ?_, ?_⟩
          · rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hgd, hhd, mul_one]
          · rw [Commute.mul_pow hc, hgm, hhm, one_mul]
          · rw [map_mul]; exact E₁.mul_mem hgE hhE
        one_mem' := ⟨by simp, one_pow m, by rw [map_one]; exact E₁.one_mem⟩
        inv_mem' := by
          rintro g ⟨hgd, hgm, hgE⟩
          refine ⟨?_, by rw [inv_pow, hgm, inv_one], by rw [map_inv]; exact E₁.inv_mem hgE⟩
          have h := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (g : GL (Fin 3) F)))
          rw [Units.val_mul, Matrix.det_mul, hgd, one_mul, Units.val_one, Matrix.det_one] at h
          simpa using h }
    have hEhm : ∀ γ ∈ Eh, γ ^ m = 1 := fun γ h => h.2.1
    have hEhd : ∀ γ ∈ Eh, ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
      fun γ h => h.1
    have hEhE : ∀ γ ∈ Eh, M.c γ ∈ E₁ := fun γ h => h.2.2
    have hEhcomm : ∀ g ∈ Eh, ∀ h ∈ Eh, g * h = h * g := by
      intro g hg h hh
      exact Subtype.ext (M.commute_of_pow (hAc _ (hEhE g hg).1 _ (hEhE h hh).1) (hE₁m _ (hEhE h hh))
        hm3)
    have hEhconj : ∀ D : ↥M.Γ, D ∈ M.S₀ → ∀ γ ∈ Eh, D * γ * D⁻¹ ∈ Eh ∧ D⁻¹ * γ * D ∈ Eh := by
      intro D hD γ hγ
      have hDS : M.c D ∈ M.S := ⟨D, hD, rfl⟩
      have hDz : M.c M.zh * M.c D = M.c D * M.c M.zh := by
        rw [← map_mul, ← map_mul, M.S₀_comm D hD]
      obtain ⟨h1, h2⟩ := hE₁S _ hDS hDz _ (hEhE γ hγ)
      refine ⟨⟨by rw [M.det_conj]; exact hEhd γ hγ, by rw [conj_pow, hEhm γ hγ, mul_one,
        mul_inv_cancel], by rw [map_mul, map_mul, map_inv]; exact h1⟩, ⟨?_, ?_, ?_⟩⟩
      · have := M.det_conj D⁻¹ γ
        rw [inv_inv] at this
        rw [this]; exact hEhd γ hγ
      · have := conj_pow (a := D⁻¹) (b := γ) (i := m)
        rw [inv_inv] at this
        rw [this, hEhm γ hγ, mul_one, inv_mul_cancel]
      · rw [map_mul, map_mul, map_inv]; exact h2
    have hzhinv : M.zh⁻¹ = M.zh := inv_eq_of_mul_eq_one_right M.zh_sq
    have hEhinv : ∀ γ ∈ Eh, M.zh * γ * M.zh = γ⁻¹ := by
      intro γ hγ
      have hzE := (hEhconj M.zh M.zh_mem γ hγ).1
      rw [hzhinv] at hzE
      refine M.lift_unique hm3 (hEhd _ hzE) (hEhd _ (Eh.inv_mem hγ)) (hEhm _ hzE)
        (hEhm _ (Eh.inv_mem hγ)) ?_
      rw [map_mul, map_mul, map_inv]
      have := (hEhE γ hγ).2.2
      rw [hzinv] at this
      exact this
    have hzA : ∀ x ∈ A, M.z * x * M.z⁻¹ ∈ A := fun x hx => hSA _ hzS x hx
    set κ := a₀ * M.z * a₀⁻¹ * M.z⁻¹ with hκ
    have hκA : κ ∈ A := by
      have h1 : a₀ * (M.z * a₀⁻¹ * M.z⁻¹) ∈ A := A.mul_mem ha₀A (hzA _ (A.inv_mem ha₀A))
      rw [hκ]
      simpa [mul_assoc] using h1
    have hκL : κ ∈ M.L := by
      have h1 : a₀ * M.z * a₀⁻¹ ∈ M.L := by
        obtain ⟨g, hg⟩ := hBc (hAB ha₀A)
        rw [← hg]
        exact M.conj_mem_L (M.S_le_L hzS)
      exact M.L.mul_mem h1 (M.L.inv_mem (M.S_le_L hzS))
    have hκinv : M.z * κ * M.z⁻¹ = κ⁻¹ := by
      calc M.z * κ * M.z⁻¹ = M.z * a₀ * M.z * a₀⁻¹ * (M.z * M.z)⁻¹ := by rw [hκ]; group
        _ = M.z * a₀ * M.z * a₀⁻¹ := by rw [hz2, inv_one, mul_one]
        _ = M.z * a₀ * M.z⁻¹ * a₀⁻¹ := by rw [hzinv]
        _ = κ⁻¹ := by rw [hκ]; group
    have hκE : κ ∈ E₁ := ⟨hκA, hκL, hκinv⟩
    have hκ1 : κ ≠ 1 := by
      intro h
      apply ha₀z
      calc a₀ * M.z = (a₀ * M.z * a₀⁻¹ * M.z⁻¹) * M.z * a₀ := by group
        _ = M.z * a₀ := by rw [← hκ, h, one_mul]
    obtain ⟨γ₀, hγ₀d, hγ₀m, hγ₀c⟩ := M.exists_lift hκL hm3 (hE₁m _ hκE)
    have hγ₀E : γ₀ ∈ Eh := ⟨hγ₀d, hγ₀m, hγ₀c ▸ hκE⟩
    have hEhne : Eh ≠ ⊥ := by
      intro h
      have : γ₀ ∈ (⊥ : Subgroup ↥M.Γ) := h ▸ hγ₀E
      rw [Subgroup.mem_bot] at this
      apply hκ1
      rw [← hγ₀c, this, map_one]
    have hE1 := burnsideA315y_E1 M.two_ne M.hxy M.hcc M.Da_val M.Db_val (Eh.map M.Γ.subtype)
      (by rintro _ ⟨γ, hγ, rfl⟩; exact hEhd γ hγ)
      (by
        rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
        exact congrArg Subtype.val (hEhcomm g hg h hh))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        have := congrArg Subtype.val (hEhinv γ hγ)
        simpa [M.zh_val] using this)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        have h1 : orderOf γ ∣ m := orderOf_dvd_of_pow_eq_one (hEhm γ hγ)
        have h2 : orderOf (M.Γ.subtype γ) = orderOf γ := Subgroup.orderOf_coe γ
        rw [h2]
        exact Odd.of_dvd_nat hmodd h1)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨M.Da⁻¹ * γ * M.Da, (hEhconj M.Da M.Da_mem γ hγ).2, by simp⟩)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨M.Db⁻¹ * γ * M.Db, (hEhconj M.Db M.Db_mem γ hγ).2, by simp⟩)
    refine ⟨Eh, hEhne, hEhd, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hE1 with h | h
      · exact Or.inl fun γ hγ => h _ ⟨γ, hγ, rfl⟩
      · exact Or.inr fun γ hγ => h _ ⟨γ, hγ, rfl⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      exact hAB (hEhE γ hγ).1
    · intro γ hγ
      exact ⟨(hEhconj M.Da M.Da_mem γ hγ).2, (hEhconj M.Da M.Da_mem γ hγ).1⟩
    · intro γ hγ
      exact ⟨(hEhconj M.Db M.Db_mem γ hγ).2, (hEhconj M.Db M.Db_mem γ hγ).1⟩
    · intro b hb
      obtain ⟨g, rfl⟩ := hBc hb
      exact ⟨g, rfl, fun e he => Subtype.ext (M.commute_of_pow
        (hBc' _ hb _ (hAB (hEhE e he).1)) (hE₁m _ (hEhE e he)) hm3)⟩

theorem dichotomy [Finite F] [Finite X] (hfit : burnsideA315y_FittingStatement) {B : Subgroup X}
    (hBc : B ≤ M.c.range) (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B))
    (h3 : ¬ IsPGroup 3 ↥B) (hperm : (B : Set X) * (M.S : Set X) = (M.S : Set X) * (B : Set X)) :
    (∀ b ∈ B, b * M.z = M.z * b) ∨ M.DichE B := by
  rcases hfit X B M.S hab hodd (M.S₀_two.map M.c) hperm with ⟨R, hRS, hR, hBR, hSR⟩ | hSB
  · exact Or.inl (M.caseI hBc hab hodd h3 hRS hR hBR hSR)
  · exact M.caseII hBc hab hodd h3 hSB

@[expose] def burnsideA315y_IsK (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 2 2 = 1

@[expose] def K₀ : Subgroup ↥M.Γ where
  carrier := {g | ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
    burnsideA315y_IsK ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)}
  mul_mem' := by
    rintro a b ⟨had, ha02, ha12, ha20, ha21, ha22⟩ ⟨hbd, hb02, hb12, hb20, hb21, hb22⟩
    refine ⟨by rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, had, hbd, mul_one], ?_⟩
    simp only [Subgroup.coe_mul, Units.val_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, ha02, ha12, ha20, ha21, ha22, hb02, hb12, hb20,
        hb21, hb22]
  one_mem' := by
    refine ⟨by simp, ?_⟩
    simp [burnsideA315y_IsK]
  inv_mem' := by
    rintro a ⟨had, ha02, ha12, ha20, ha21, ha22⟩
    have hdet : (((a⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      have h := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (a : GL (Fin 3) F)))
      rw [Units.val_mul, Matrix.det_mul, had, one_mul, Units.val_one, Matrix.det_one] at h
      simpa using h
    refine ⟨hdet, ?_⟩
    have hcomm : (a : GL (Fin 3) F) * negDiag3 F = negDiag3 F * a := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_negDiag3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, ha02,
        ha12, ha20, ha21]
    set ai : GL (Fin 3) F := (a : GL (Fin 3) F)⁻¹ with hai
    have hcinv : ai * negDiag3 F = negDiag3 F * ai := Commute.inv_left hcomm
    have hm : (ai : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
        diagonal ![-1, -1, 1] * (ai : Matrix (Fin 3) (Fin 3) F) := by
      rw [← coe_negDiag3, ← Units.val_mul, hcinv, Units.val_mul]
    obtain ⟨h02, h12, h20, h21⟩ := block_eq_zero_of_commute_negDiag M.two_ne hm
    have he3 := burnsideA315y_inv_e3 (D := (a : GL (Fin 3) F)) (by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ha02, ha12, ha22])
    have h22 : (ai : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      have h := congrFun he3 2
      rw [burnsideA315y_mulVec_e3_apply] at h
      rw [h]
      rfl
    have hcoe : (((a⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (ai : Matrix (Fin 3) (Fin 3) F) := by rw [Subgroup.coe_inv]
    rw [hcoe]
    exact ⟨h02, h12, h20, h21, h22⟩

@[expose] def K : Subgroup X := M.K₀.map M.c

@[expose] def Mz : Subgroup X := M.c.range ⊓ Subgroup.centralizer ({M.z} : Set X)

@[expose] def D₀ : Subgroup ↥M.Γ := Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)

theorem mem_K₀_of {g : ↥M.Γ} (hg : (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g)
    (h22 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1)
    (hd : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1) : g ∈ M.K₀ := by
  have hm : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, hg, Units.val_mul]
  obtain ⟨h02, h12, h20, h21⟩ := block_eq_zero_of_commute_negDiag M.two_ne hm
  exact ⟨hd, h02, h12, h20, h21, h22⟩

theorem K₀_comm {k : ↥M.Γ} (hk : k ∈ M.K₀) : (k : GL (Fin 3) F) * negDiag3 F = negDiag3 F * k := by
  obtain ⟨-, h02, h12, h20, h21, -⟩ := hk
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, h02, h12,
    h20, h21]

theorem zh_mem_K₀ : M.zh ∈ M.K₀ := by
  refine ⟨M.det_zh, ?_⟩
  rw [M.zh_val, coe_negDiag3]
  simp [burnsideA315y_IsK]

theorem Da_mem_K₀ : M.Da ∈ M.K₀ := by
  refine ⟨M.S₀_det _ M.Da_mem, ?_⟩
  rw [M.Da_val]
  simp [burnsideA315y_IsK, blkMat]

theorem Db_mem_K₀ : M.Db ∈ M.K₀ := by
  refine ⟨M.S₀_det _ M.Db_mem, ?_⟩
  rw [M.Db_val]
  simp [burnsideA315y_IsK, blkMat]

theorem comm_zh_of_comm {g : ↥M.Γ} (hg : M.c g * M.z = M.z * M.c g) :
    (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g := by
  rw [← M.zh_val]
  exact M.commute_of_trace hg M.trace_zh_ne

theorem K_le_Mz : M.K ≤ M.Mz := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨⟨k, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h0 : (k : GL (Fin 3) F) * M.zh = M.zh * k := by
    rw [M.zh_val]
    exact M.K₀_comm hk
  have h1 : k * M.zh = M.zh * k := Subtype.ext h0
  rw [z, ← map_mul, ← map_mul, h1]

theorem S_le_Mz : M.S ≤ M.Mz := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [z, ← map_mul, ← map_mul, M.S₀_comm s hs]

theorem exists_lift_Mz {m : X} (hm : m ∈ M.Mz) :
    ∃ g : ↥M.Γ, M.c g = m ∧ (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g := by
  obtain ⟨⟨g, rfl⟩, hz⟩ := hm
  refine ⟨g, rfl, M.comm_zh_of_comm ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp hz

theorem Mz_le_normalizer : M.Mz ≤ Subgroup.normalizer (M.K : Set X) := by
  have key : ∀ m ∈ M.Mz, ∀ k ∈ M.K, m * k * m⁻¹ ∈ M.K := by
    intro m hm k hk
    obtain ⟨g, rfl, hgz⟩ := M.exists_lift_Mz hm
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    refine ⟨g * k₀ * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hkz := M.K₀_comm hk₀
    refine M.mem_K₀_of ?_ ?_ ?_
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Commute.mul_left (Commute.mul_left hgz hkz) (Commute.inv_left hgz)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [burnsideA315y_conj_22' M.two_ne hgz hkz]
      exact hk₀.2.2.2.2.2
    · rw [M.det_conj]; exact hk₀.1
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact key m hm k
  · intro h
    have := key m⁻¹ (M.Mz.inv_mem hm) _ h
    simpa [mul_assoc] using this

theorem D₀_form {d : ↥M.Γ} (hd : d ∈ M.D₀) :
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 =
      ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hz := Subgroup.mem_centralizer_iff.mp hd M.zh (by simp)
  have ha := Subgroup.mem_centralizer_iff.mp hd M.Da (by simp)
  have hb := Subgroup.mem_centralizer_iff.mp hd M.Db (by simp)
  have hz' := congrArg (fun g : ↥M.Γ => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hz
  have ha' := congrArg (fun g : ↥M.Γ => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ha
  have hb' := congrArg (fun g : ↥M.Γ => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hb
  simp only [Subgroup.coe_mul, Units.val_mul, M.zh_val, coe_negDiag3, M.Da_val, M.Db_val] at hz' ha' hb'
  have hxy0 : M.x ≠ 0 ∨ M.y ≠ 0 := by
    by_contra h
    push Not at h
    apply M.hxy
    rw [h.1, h.2]
    ring
  exact burnsideA315y_commutant M.two_ne hxy0 M.hcc hz'.symm ha'.symm hb'.symm

theorem D₀_comm {d g : ↥M.Γ} (hd : d ∈ M.D₀)
    (hg : (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g) : d * g = g * d := by
  have hm : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, hg, Units.val_mul]
  have h := burnsideA315y_diag_comm_block (M.D₀_form hd) (block_eq_zero_of_commute_negDiag M.two_ne hm)
  apply Subtype.ext
  apply Units.ext
  simpa using h

theorem Mz_inf_centralizer : M.Mz ⊓ Subgroup.centralizer (M.K : Set X) = M.D₀.map M.c := by
  apply le_antisymm
  · rintro m ⟨hm, hmK⟩
    obtain ⟨g, rfl, hgz⟩ := M.exists_lift_Mz hm
    refine ⟨g, ?_, rfl⟩
    have hK : ∀ k ∈ M.K₀, M.c k * M.c g = M.c g * M.c k := fun k hk =>
      (Subgroup.mem_centralizer_iff.mp hmK _ ⟨k, hk, rfl⟩)
    show g ∈ Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)
    rw [Subgroup.mem_centralizer_iff]
    rintro h (rfl | rfl | rfl)
    · exact (Subtype.ext (M.commute_of_trace (hK _ M.zh_mem_K₀).symm M.trace_zh_ne)).symm
    · exact (Subtype.ext (M.commute_of_trace (hK _ M.Da_mem_K₀).symm
        (by rw [M.trace_Da]; exact one_ne_zero))).symm
    · exact (Subtype.ext (M.commute_of_trace (hK _ M.Db_mem_K₀).symm
        (by rw [M.trace_Db]; exact one_ne_zero))).symm
  · rintro _ ⟨d, hd, rfl⟩
    have hdz : (d : GL (Fin 3) F) * negDiag3 F = negDiag3 F * d := by
      have := Subgroup.mem_centralizer_iff.mp hd M.zh (by simp)
      have := congrArg (fun g : ↥M.Γ => (g : GL (Fin 3) F)) this
      simp only [Subgroup.coe_mul, M.zh_val] at this
      exact this.symm
    refine ⟨⟨⟨d, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · have hzz : (M.zh : GL (Fin 3) F) * negDiag3 F = negDiag3 F * M.zh := by rw [M.zh_val]
      rw [z, ← map_mul, ← map_mul, M.D₀_comm hd hzz]
    · show M.c d ∈ Subgroup.centralizer (M.K : Set X)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, M.D₀_comm hd (M.K₀_comm hk)]

theorem central : ∀ c ∈ M.Mz ⊓ Subgroup.centralizer (M.K : Set X), ∀ m ∈ M.Mz, c * m = m * c := by
  intro c hc m hm
  rw [M.Mz_inf_centralizer] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  obtain ⟨g, rfl, hgz⟩ := M.exists_lift_Mz hm
  rw [← map_mul, ← map_mul, M.D₀_comm hd hgz]

theorem split [Finite F]
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    {b : X} (hb : b ∈ M.Mz) (hodd : Odd (orderOf b)) :
    ∃ k ∈ M.K, ∃ c ∈ M.Mz ⊓ Subgroup.centralizer (M.K : Set X), b = k * c := by
  obtain ⟨g, rfl, hgz⟩ := M.exists_lift_Mz hb
  set G := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hG
  have hgm : G * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * G := by
    rw [hG, ← coe_negDiag3, ← Units.val_mul, hgz, Units.val_mul]
  obtain ⟨g02, g12, g20, g21⟩ := block_eq_zero_of_commute_negDiag M.two_ne hgm
  have hw0 : G 2 2 ≠ 0 := by
    intro h0
    have := (Matrix.isUnit_iff_isUnit_det G).mp (g : GL (Fin 3) F).isUnit
    rw [Matrix.det_fin_three, g02, g12, g20, g21, h0] at this
    simp at this
  set μ : Fˣ := Units.mk0 (G 2 2) hw0 with hμ
  set σ : ↥M.Γ := ⟨_, hΓscal g hgz μ rfl⟩ with hσ
  have hcσ : M.c σ = 1 := (M.ker_c σ).mpr ⟨μ, rfl⟩
  have hσc : ∀ h : GL (Fin 3) F, (σ : GL (Fin 3) F) * h = h * σ := fun h =>
    burnsideA315y_scalar_comm μ h
  set g₁ : ↥M.Γ := σ⁻¹ * g with hg₁
  have hcg₁ : M.c g₁ = M.c g := by rw [hg₁, map_mul, map_inv, hcσ, inv_one, one_mul]
  have hg₁z : (g₁ : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g₁ := by
    simp only [hg₁, Subgroup.coe_mul, Subgroup.coe_inv]
    have h1 : (σ : GL (Fin 3) F)⁻¹ * negDiag3 F = negDiag3 F * (σ : GL (Fin 3) F)⁻¹ :=
      Commute.inv_left (hσc _)
    exact Commute.mul_left h1 hgz
  have hg₁e3 : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [burnsideA315y_mulVec_e3 M.two_ne hg₁z]
    have : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      simp only [hg₁, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hσ,
        Matrix.GeneralLinearGroup.coe_scalar]
      rw [show ((((Matrix.GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ : GL (Fin 3) F)) :
          Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) ((μ⁻¹ : Fˣ) : F) by
        rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar]]
      simp [Matrix.mul_apply, Fin.sum_univ_three, g20, g21, hμ, hw0, ← hG]
    rw [this, one_smul]
  have hg₁22 : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have := congrFun hg₁e3 2
    rw [burnsideA315y_mulVec_e3_apply] at this
    rw [this]; rfl
  set m := orderOf (M.c g) with hm
  have hg₁m : g₁ ^ m = 1 := by
    have hc1 : M.c (g₁ ^ m) = 1 := by rw [map_pow, hcg₁, hm, pow_orderOf_eq_one]
    obtain ⟨ν, hν⟩ := M.exists_scalar_of_c_eq_one hc1
    have hg₁e3' : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
        (1 : F) • ![0, 0, 1] := by rw [one_smul]; exact hg₁e3
    have he := burnsideA315y_pow_e3 hg₁e3' m
    rw [one_pow, one_smul, ← Subgroup.coe_pow, hν, Matrix.GeneralLinearGroup.coe_scalar] at he
    have h2 := congrFun he 2
    simp at h2
    apply Subtype.ext
    rw [hν]
    rw [h2, map_one, Subgroup.coe_one]
  have hg₁blk : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have hm' : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
        diagonal ![-1, -1, 1] * ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← coe_negDiag3, ← Units.val_mul, hg₁z, Units.val_mul]
    obtain ⟨a, b, -, -⟩ := block_eq_zero_of_commute_negDiag M.two_ne hm'
    exact ⟨a, b⟩
  set d := (ulBlock ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det with hd
  have hdm : d ^ m = 1 := by
    have h1 := burnsideA315y_ulBlock_pow hg₁blk m
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hg₁m, Subgroup.coe_one, Units.val_one,
      ulBlock_one] at h1
    rw [hd, ← Matrix.det_pow, ← h1, Matrix.det_one]
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := hodd.pos; omega)] at hdm
    exact zero_ne_one hdm
  set dU : Fˣ := Units.mk0 d hd0 with hdU
  have hdUm : dU ^ m = 1 := Units.ext (by simp [hdU, hdm])
  obtain ⟨j, hj⟩ := hodd
  set sU : Fˣ := dU ^ (j + 1) with hsU
  have hs2 : sU * sU = dU := by
    rw [hsU, ← pow_add, show j + 1 + (j + 1) = m + 1 by omega, pow_succ, hdUm, one_mul]
  set δ : ↥M.Γ := ⟨burnsideA315y_dgl sU, hΓdiag g₁ hg₁z hg₁22 (j + 1) sU (by
    rw [hsU, Units.val_pow_eq_pow_val, hdU, Units.val_mk0])⟩
    with hδ
  have hδD : δ ∈ M.D₀ := by
    show δ ∈ Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)
    rw [Subgroup.mem_centralizer_iff]
    have hblk : ∀ (A : Matrix (Fin 2) (Fin 2) F) (h : ↥M.Γ),
        ((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat A 1 → h * δ = δ * h := by
      intro A h hA
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hA, hδ, burnsideA315y_dgl_val, blkMat_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, mul_one]
    rintro h (rfl | rfl | rfl)
    · refine hblk (-1) M.zh ?_
      rw [M.zh_val, coe_negDiag3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blkMat]
    · exact hblk _ M.Da M.Da_val
    · exact hblk _ M.Db M.Db_val
  have hδz : (δ : GL (Fin 3) F) * negDiag3 F = negDiag3 F * δ := by
    have := Subgroup.mem_centralizer_iff.mp hδD M.zh (by simp)
    have := congrArg (fun g : ↥M.Γ => (g : GL (Fin 3) F)) this
    simp only [Subgroup.coe_mul, M.zh_val] at this
    exact this.symm
  set k : ↥M.Γ := δ⁻¹ * g₁ with hk
  have hkK : k ∈ M.K₀ := by
    refine M.mem_K₀_of ?_ ?_ ?_
    · simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Commute.mul_left (Commute.inv_left hδz) hg₁z
    · have he3 : ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
        simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
        rw [← Matrix.mulVec_mulVec, hg₁e3]
        exact burnsideA315y_inv_e3 (D := (δ : GL (Fin 3) F))
          (by rw [hδ]; exact burnsideA315y_blkMat_e3 _)
      have := congrFun he3 2
      rw [burnsideA315y_mulVec_e3_apply] at this
      rw [this]; rfl
    · have hdetδ : ((δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = (sU : F) * sU := by
        simp only [hδ, burnsideA315y_dgl_val, det_blkMat, mul_one, Matrix.det_smul,
          Fintype.card_fin, Matrix.det_one]
        ring
      have hdetg₁ : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = d := by
        obtain ⟨h02, h12⟩ := hg₁blk
        have hm' : ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
            diagonal ![-1, -1, 1] * ((g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [← coe_negDiag3, ← Units.val_mul, hg₁z, Units.val_mul]
        obtain ⟨-, -, h20, h21⟩ := block_eq_zero_of_commute_negDiag M.two_ne hm'
        rw [hd, Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21, hg₁22]
        simp [ulBlock]
      have h1 : (sU : F) * sU = d := by rw [← Units.val_mul, hs2, hdU, Units.val_mk0]
      simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.det_mul]
      rw [hdetg₁, ← h1]
      have hinvdet : (((δ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
          ((δ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      rw [hdetδ] at hinvdet
      exact hinvdet
  refine ⟨M.c k, ⟨k, hkK, rfl⟩, M.c δ, ?_, ?_⟩
  · rw [M.Mz_inf_centralizer]
    exact ⟨δ, hδD, rfl⟩
  · rw [← hcg₁, ← map_mul]
    congr 1
    rw [hk, mul_assoc, ← M.D₀_comm hδD hg₁z]
    group

theorem steps [Finite F] [Finite X] (hsteps : burnsideA315y_StepsStatement) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    {B : Subgroup X} (hBc : B ≤ M.c.range) (hBz : ∀ b ∈ B, b * M.z = M.z * b)
    (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B))
    (hperm : (B : Set X) * (M.S : Set X) = (M.S : Set X) * (B : Set X))
    (hSK : Nat.card ↥(M.S ⊓ M.K) = 2 ^ (Nat.card ↥M.K).factorization 2)
    (hScard : Nat.card ↥M.S = 2 ^ (Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(M.S ⊓ Subgroup.centralizer (M.K : Set X))) :
    B = (B ⊓ M.K) ⊔ (B ⊓ Subgroup.centralizer (M.K : Set X)) ∧ IsCyclic ↥(B ⊓ M.K) ∧
    (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ M.K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        ∃ t ∈ M.S ⊓ M.K, ∀ x ∈ B ⊓ M.K, t * x * t⁻¹ = x⁻¹) ∨
     ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ M.K) = 3 ∧
        ∃ t ∈ M.S ⊓ Subgroup.normalizer (B : Set X), ∀ x ∈ B ⊓ M.K, t * x * t⁻¹ = x⁻¹)) := by
  have hBM : B ≤ M.Mz := fun b hb =>
    ⟨hBc hb, Subgroup.mem_centralizer_singleton_iff.mpr (hBz b hb)⟩
  refine hsteps X p hp2 M.K M.Mz B M.S hK M.K_le_Mz M.Mz_le_normalizer M.central hBM hab hodd
    ?_ M.S_le_Mz (M.S₀_two.map M.c) hperm hSK hScard
  intro b hb
  have hob : Odd (orderOf b) := by
    have h1 : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  exact M.split hΓscal hΓdiag (hBM hb) hob

end burnsideA315y_Model

end CFSG.ASVolI
