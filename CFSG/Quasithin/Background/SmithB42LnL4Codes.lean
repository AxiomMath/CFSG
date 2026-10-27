module

public import CFSG.Quasithin.Background.SmithB42LnL4Out

public section

namespace CFSG.Quasithin.B42Ln

open Matrix
open scoped Pointwise

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem card_G4 : Nat.card G4 = 20160 := by
  have hdet : ∀ g : GL (Fin 4) (ZMod 2), (g : 𝕄₄).det = 1 := det_eq_one_GL4
  let e : G4 ≃ GL (Fin 4) (ZMod 2) :=
    { toFun := Matrix.SpecialLinearGroup.toGL
      invFun := fun g => ⟨g, hdet g⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Units.ext (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _) }
  rw [Nat.card_congr e, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

theorem exists_conj_le_U4 {B : Subgroup G4} (hB : IsPGroup 2 B) :
    ∃ h : G4, ∀ b ∈ B, h * b * h⁻¹ ∈ U4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hB.exists_le_sylow
  have hUi : ¬ 2 ∣ U4.index := by
    have h := U4.index_mul_card
    rw [card_U4, card_G4] at h
    generalize U4.index = n at h ⊢
    have h315 : n = 315 := by omega
    subst h315
    decide
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G4 P (isPGroup_U4.toSylow hUi)
  have h1 : MulAut.conj h • (P : Subgroup G4) = U4 :=
    congrArg (fun P : Sylow 2 G4 => (P : Subgroup G4)) hh
  refine ⟨h, fun b hb => ?_⟩
  rw [← h1]
  have h2 := Subgroup.smul_mem_pointwise_smul b (MulAut.conj h) (P : Subgroup G4) (hP hb)
  rwa [MulAut.smul_def, MulAut.conj_apply] at h2

theorem up4_mul_self_of {u : G4} (hu : u ∈ U4) (h2 : u * u = 1) :
    up4 (code4 (u : 𝕄₄)) * up4 (code4 (u : 𝕄₄)) = 1 := by
  rw [up4_code4 hu, ← Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.SpecialLinearGroup.coe_one]

theorem exists_conj_of_mem_U4 {u : G4} (hu : u ∈ U4) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g : G4, g * u * g⁻¹ = uOf 1 ∨ g * u * g⁻¹ = uOf 18 := by
  set c := code4 (u : 𝕄₄) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu1
    rw [eq_uOf hu, ← hc, h0]
    exact Subtype.ext up4_zero
  have hcs := invol_cases c (up4_mul_self_of hu hu2) hc0
  have hspec := invTab4_spec c hcs
  unfold InvGood4 at hspec
  split at hspec
  · rename_i t _
    obtain ⟨hgi, htv, hntv⟩ := hspec
    have hig : toM4 t.2.2 * toM4 t.2.1 = 1 :=
      (mul_eq_one_comm_of_card_eq (Fin 4) (Fin 4) (ZMod 2) rfl).mp hgi
    refine ⟨ofMI (toM4 t.2.1) (toM4 t.2.2) hgi, ?_⟩
    have hinv : ((ofMI (toM4 t.2.1) (toM4 t.2.2) hgi)⁻¹ : G4) =
        ofMI (toM4 t.2.2) (toM4 t.2.1) hig := inv_eq_of_mul_eq_one_right (Subtype.ext hgi)
    rw [hinv]
    have hum : (u : 𝕄₄) = up4 c := (up4_code4 hu).symm
    rcases hcs with h | h
    · left
      apply Subtype.ext
      show toM4 t.2.1 * (u : 𝕄₄) * toM4 t.2.2 = up4 1
      rw [hum]
      exact htv h
    · right
      apply Subtype.ext
      show toM4 t.2.1 * (u : 𝕄₄) * toM4 t.2.2 = up4 18
      rw [hum]
      exact hntv h
  · exact hspec.elim

theorem exists_conj_t0_or_s0_4 {u : G4} (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g : G4, g * u * g⁻¹ = uOf 1 ∨ g * u * g⁻¹ = uOf 18 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two, hu2]) hu1
  have hQ : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨h, hh⟩ := exists_conj_le_U4 hQ
  have hmem := hh u (Subgroup.mem_zpowers u)
  have h2 : h * u * h⁻¹ * (h * u * h⁻¹) = 1 := by
    calc h * u * h⁻¹ * (h * u * h⁻¹) = h * (u * u) * h⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have h1 : h * u * h⁻¹ ≠ 1 := fun h0 => hu1 (by
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
      _ = 1 := by rw [h0]; group)
  obtain ⟨g, hg⟩ := exists_conj_of_mem_U4 hmem h2 h1
  refine ⟨g * h, ?_⟩
  have e : g * h * u * (g * h)⁻¹ = g * (h * u * h⁻¹) * g⁻¹ := by group
  rw [e]
  exact hg

@[expose] noncomputable def codesOf (S : Subgroup G4) (h : G4) : Finset (Fin 64) := by
  classical
  exact Finset.univ.filter fun c => h⁻¹ * uOf c * h ∈ S

theorem mem_codesOf {S : Subgroup G4} {h : G4} {c : Fin 64} :
    c ∈ codesOf S h ↔ h⁻¹ * uOf c * h ∈ S := by
  classical
  unfold codesOf
  simp

variable {S : Subgroup G4} {h : G4}

theorem card_codesOf (hU : ∀ b ∈ S, h * b * h⁻¹ ∈ U4) : (codesOf S h).card = Nat.card S := by
  classical
  have e : ↥S ≃ ↥(codesOf S h) :=
    { toFun := fun b => ⟨code4 ((h * b * h⁻¹ : G4) : 𝕄₄), mem_codesOf.2 (by
        rw [← eq_uOf (hU b b.2)]
        have : h⁻¹ * (h * (b : G4) * h⁻¹) * h = b := by group
        rw [this]
        exact b.2)⟩
      invFun := fun c => ⟨h⁻¹ * uOf c * h, mem_codesOf.1 c.2⟩
      left_inv := fun b => Subtype.ext (by
        show h⁻¹ * uOf (code4 ((h * b * h⁻¹ : G4) : 𝕄₄)) * h = b
        rw [← eq_uOf (hU b b.2)]
        group)
      right_inv := fun c => Subtype.ext (by
        show code4 ((h * (h⁻¹ * uOf c * h) * h⁻¹ : G4) : 𝕄₄) = c
        have : h * (h⁻¹ * uOf c * h) * h⁻¹ = uOf c := by group
        rw [this]
        exact code4_up4 c) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem zero_mem_codesOf : (0 : Fin 64) ∈ codesOf S h := by
  rw [mem_codesOf]
  have : uOf 0 = 1 := Subtype.ext up4_zero
  rw [this, mul_one, inv_mul_cancel]
  exact S.one_mem

theorem codesOf_sq (h2 : ∀ b ∈ S, b * b = 1) {c : Fin 64} (hc : c ∈ codesOf S h) :
    up4 c * up4 c = 1 := by
  have h1 := h2 _ (mem_codesOf.1 hc)
  have e : uOf c * uOf c = 1 := by
    calc uOf c * uOf c = h * ((h⁻¹ * uOf c * h) * (h⁻¹ * uOf c * h)) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact congrArg (fun g : G4 => (g : 𝕄₄)) e

theorem codesOf_comm (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {c d : Fin 64}
    (hcS : c ∈ codesOf S h) (hdS : d ∈ codesOf S h) : up4 c * up4 d = up4 d * up4 c := by
  have h1 := hc _ (mem_codesOf.1 hcS) _ (mem_codesOf.1 hdS)
  have e : uOf c * uOf d = uOf d * uOf c := by
    calc uOf c * uOf d = h * ((h⁻¹ * uOf c * h) * (h⁻¹ * uOf d * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * uOf d * h) * (h⁻¹ * uOf c * h)) * h⁻¹ := by rw [h1]
      _ = uOf d * uOf c := by group
  exact congrArg (fun g : G4 => (g : 𝕄₄)) e

theorem uOf_code_mul (c d : Fin 64) : uOf (code4 (up4 c * up4 d)) = uOf c * uOf d := by
  have hm : uOf c * uOf d ∈ U4 := U4.mul_mem (uOf_mem c) (uOf_mem d)
  exact (eq_uOf hm).symm

theorem codesOf_mul {c d : Fin 64} (hcS : c ∈ codesOf S h) (hdS : d ∈ codesOf S h) :
    code4 (up4 c * up4 d) ∈ codesOf S h := by
  rw [mem_codesOf, uOf_code_mul]
  have e : h⁻¹ * (uOf c * uOf d) * h = (h⁻¹ * uOf c * h) * (h⁻¹ * uOf d * h) := by group
  rw [e]
  exact S.mul_mem (mem_codesOf.1 hcS) (mem_codesOf.1 hdS)

theorem code_mul_ne_zero {c d : Fin 64} (hd : up4 d * up4 d = 1) (hcd : c ≠ d) :
    code4 (up4 c * up4 d) ≠ 0 := by
  intro h0
  apply hcd
  have h1 : up4 c * up4 d = 1 := by
    rw [← up4_code4 (isUp4_mul (isUp4_up4 c) (isUp4_up4 d)), h0, up4_zero]
  have h2 : up4 c = up4 d := by
    calc up4 c = up4 c * (up4 d * up4 d) := by rw [hd, Matrix.mul_one]
      _ = (up4 c * up4 d) * up4 d := by rw [Matrix.mul_assoc]
      _ = up4 d := by rw [h1, Matrix.one_mul]
  rw [← code4_up4 c, ← code4_up4 d, h2]

structure IsCodeGroup (T : Finset (Fin 64)) : Prop where
  zero_mem : (0 : Fin 64) ∈ T
  sq : ∀ c ∈ T, up4 c * up4 c = 1
  comm : ∀ c ∈ T, ∀ d ∈ T, up4 c * up4 d = up4 d * up4 c
  mul_mem : ∀ c ∈ T, ∀ d ∈ T, code4 (up4 c * up4 d) ∈ T

theorem isCodeGroup_codesOf (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h2 : ∀ b ∈ S, b * b = 1) :
    IsCodeGroup (codesOf S h) :=
  ⟨zero_mem_codesOf, fun _ hc' => codesOf_sq h2 hc', fun _ hc' _ hd => codesOf_comm hc hc' hd,
    fun _ hc' _ hd => codesOf_mul hc' hd⟩

variable {T : Finset (Fin 64)}

theorem IsCodeGroup.inv_cases (hT : IsCodeGroup T) {c : Fin 64} (hc : c ∈ T) (hc0 : c ≠ 0) :
    c ∈ tvL ∨ c ∈ ntvL :=
  invol_cases c (hT.sq c hc) hc0

theorem codes_q4 (hT : IsCodeGroup T) (h16 : 16 ≤ T.card) :
    T.card = 16 ∧ (4 : Fin 64) ∈ T ∧ (18 : Fin 64) ∈ T := by
  classical
  have hsub : T ⊆ Finset.univ.filter InQ4 := by
    intro c hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, mem_q4 c (hT.sq c hc) (h16.trans (Finset.card_le_card ?_))⟩
    intro d hd
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hT.sq d hd, hT.comm c hc d hd⟩
  have hle := Finset.card_le_card hsub
  rw [card_q4] at hle
  have heq : T = Finset.univ.filter InQ4 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_q4]; omega)
  refine ⟨by omega, ?_, ?_⟩ <;> rw [heq, Finset.mem_filter] <;>
    exact ⟨Finset.mem_univ _, by decide⟩

theorem card_le_of_forall_mem_list {X : Finset (Fin 64)} {l : List (Fin 64)}
    (h : ∀ c ∈ X, c ∈ l) : X.card ≤ l.length :=
  (Finset.card_le_card (s := X) (t := l.toFinset) fun c hc => List.mem_toFinset.2 (h c hc)).trans
    (List.toFinset_card_le l)

theorem card_erase_le_of_nb (hT : IsCodeGroup T) (h8 : T.card = 8) {x : Fin 64} (hx : x ∈ T)
    (hx0 : x ≠ 0) {l : List (Fin 64)} (hl : ∀ y ∈ T, y ≠ 0 → y ≠ x → y ∈ l) :
    6 ≤ l.length := by
  have h1 : ((T.erase 0).erase x).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hx0, hx⟩),
      Finset.card_erase_of_mem hT.zero_mem, h8]
  rw [← h1]
  refine card_le_of_forall_mem_list fun y hy => ?_
  obtain ⟨hyx, hy'⟩ := Finset.mem_erase.1 hy
  obtain ⟨hy0, hyT⟩ := Finset.mem_erase.1 hy'
  exact hl y hyT hy0 hyx

theorem codes_not_ntv (hT : IsCodeGroup T) (h8 : T.card = 8)
    (hall : ∀ c ∈ T, c ≠ 0 → c ∈ ntvL) : False := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, x ∈ ((T.erase 0).erase 18).erase 22 := by
    apply Finset.card_pos.1
    have h2 : 5 ≤ (((T.erase 0).erase 18).erase 22).card := by
      have a1 := Finset.pred_card_le_card_erase (s := (T.erase 0).erase 18) (a := 22)
      have a2 := Finset.pred_card_le_card_erase (s := T.erase 0) (a := 18)
      have a3 := Finset.pred_card_le_card_erase (s := T) (a := 0)
      omega
    omega
  simp only [Finset.mem_erase] at hx
  obtain ⟨hx22, hx18, hx0, hxT⟩ := hx
  have hxn := hall x hxT hx0
  have hle := nbN_short x hxn hx18 hx22
  have h6 := card_erase_le_of_nb hT h8 hxT hx0 (l := nbN x) fun y hyT hy0 hyx => by
    rw [nbN, List.mem_filter]
    refine ⟨hall y hyT hy0, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hyx, hT.comm x hxT y hyT, hall _ (hT.mul_mem x hxT y hyT)
      (code_mul_ne_zero (hT.sq y hyT) (Ne.symm hyx))⟩
  omega

@[expose] def te0L : List (Fin 64) := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def te3L : List (Fin 64) := [0, 4, 16, 20, 32, 36, 48, 52]

theorem low_mem_te0 : ∀ x : Fin 64, x ∈ ([1, 2, 3, 5, 6, 7] : List (Fin 64)) → x ∈ te0L := by
  decide

theorem lt8_mem_te0 : ∀ c : Fin 64, (c : ℕ) < 8 → c ∈ te0L := by
  decide

theorem mem_te3 : ∀ c : Fin 64, c ∈ tvL → c ∉ ([8, 10, 24, 30] : List (Fin 64)) →
    c ∉ ([1, 2, 3, 5, 6, 7] : List (Fin 64)) → c ∈ te3L := by
  decide

theorem mem_of_subset_list (h8 : T.card = 8) {l : List (Fin 64)} (hl : l.length = 8)
    (hnd : l.Nodup) (hsub : ∀ c ∈ T, c ∈ l) {c : Fin 64} (hc : c ∈ l) : c ∈ T := by
  classical
  have hsub' : T ⊆ l.toFinset := fun c hc => List.mem_toFinset.2 (hsub c hc)
  have heq : T = l.toFinset := Finset.eq_of_subset_of_card_le hsub'
    (by rw [List.toFinset_card_of_nodup hnd, hl, h8])
  rw [heq]
  exact List.mem_toFinset.2 hc

theorem codes_regular (hT : IsCodeGroup T) (h8 : T.card = 8)
    (hall : ∀ c ∈ T, c ≠ 0 → c ∈ tvL) :
    ((1 : Fin 64) ∈ T ∧ (2 : Fin 64) ∈ T ∧ (4 : Fin 64) ∈ T) ∨
      ((4 : Fin 64) ∈ T ∧ (16 : Fin 64) ∈ T ∧ (32 : Fin 64) ∈ T) := by
  classical
  have hnb : ∀ x ∈ T, x ≠ 0 → ∀ y ∈ T, y ≠ 0 → y ≠ x → y ∈ nbT x := by
    intro x hxT hx0 y hyT hy0 hyx
    rw [nbT, List.mem_filter]
    refine ⟨hall y hyT hy0, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hyx, hT.comm x hxT y hyT, hall _ (hT.mul_mem x hxT y hyT)
      (code_mul_ne_zero (hT.sq y hyT) (Ne.symm hyx))⟩
  have hbig : ∀ x ∈ T, x ≠ 0 → x ∉ ([8, 10, 24, 30] : List (Fin 64)) := by
    intro x hxT hx0 hx
    have := nbT_short x hx
    have h6 := card_erase_le_of_nb hT h8 hxT hx0 (hnb x hxT hx0)
    omega
  by_cases hlow : ∃ x ∈ T, x ∈ ([1, 2, 3, 5, 6, 7] : List (Fin 64))
  · left
    obtain ⟨x, hxT, hxl⟩ := hlow
    have hx0 : x ≠ 0 := by
      rintro rfl
      revert hxl
      decide
    have hsub : ∀ c ∈ T, c ∈ te0L := by
      intro c hcT
      by_cases hc0 : c = 0
      · rw [hc0]
        decide
      by_cases hcx : c = x
      · rw [hcx]
        exact low_mem_te0 x hxl
      refine lt8_mem_te0 c (Nat.lt_of_not_le fun h8 => ?_)
      exact nbT_low x hxl c (tv_high c (hall c hcT hc0) (hbig c hcT hc0) h8)
        ⟨hT.comm x hxT c hcT,
          hall _ (hT.mul_mem x hxT c hcT) (code_mul_ne_zero (hT.sq c hcT) (Ne.symm hcx))⟩
    exact ⟨mem_of_subset_list h8 (by decide) (by decide) hsub (by decide),
      mem_of_subset_list h8 (by decide) (by decide) hsub (by decide),
      mem_of_subset_list h8 (by decide) (by decide) hsub (by decide)⟩
  · right
    push Not at hlow
    have hsub : ∀ c ∈ T, c ∈ te3L := by
      intro c hcT
      by_cases hc0 : c = 0
      · rw [hc0]
        decide
      exact mem_te3 c (hall c hcT hc0) (hbig c hcT hc0) (hlow c hcT)
    exact ⟨mem_of_subset_list h8 (by decide) (by decide) hsub (by decide),
      mem_of_subset_list h8 (by decide) (by decide) hsub (by decide),
      mem_of_subset_list h8 (by decide) (by decide) hsub (by decide)⟩

end CFSG.Quasithin.B42Ln
