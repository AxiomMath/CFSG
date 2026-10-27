module

public import CFSG.Quasithin.Background.H156K
public import CFSG.Quasithin.Background.H156Gen

public section

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc

@[expose] def c2 : List ℕ := [1, 2, 0, 1, 1, 3, 3, 0, 3, 1, 2]

@[expose] def c3 : List ℕ := [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 4]

@[expose] def c6 : List ℕ := [0, 0, 27, 48, 16, 27, 35, 3, 63, 37, 40]

@[expose] def v9Basis : List ℕ := [4, 24, 39, 71, 78, 128, 292, 578, 1035]

@[expose] def beta2 : W11 →* Wn 2 := maskHom 11 2 c2

@[expose] def beta3 : W11 →* Wn 3 := maskHom 11 3 c3

@[expose] def beta6 : W11 →* Mat32 := matOfW.comp (maskHom 11 6 c6)

@[expose] def V9 : Subgroup W11 := beta2.ker

theorem c2_len : c2.length = 11 := by decide
theorem c3_len : c3.length = 11 := by decide
theorem c6_len : c6.length = 11 := by decide

theorem beta2_toW (m : ℕ) : beta2 (toW 11 m) = toW 2 (actM c2 m) := maskHom_toW c2_len m

theorem beta3_toW (m : ℕ) : beta3 (toW 11 m) = toW 3 (actM c3 m) := maskHom_toW c3_len m

theorem c2_lt : ∀ c ∈ c2, c < 2 ^ 2 := by decide
theorem c3_lt : ∀ c ∈ c3, c < 2 ^ 3 := by decide
theorem c6_lt : ∀ c ∈ c6, c < 2 ^ 6 := by decide

theorem beta2_eq_one_iff (m : ℕ) : beta2 (toW 11 m) = 1 ↔ actM c2 m = 0 := by
  rw [beta2_toW, ← toW_zero 2]
  exact ⟨fun h => toW_inj (actM_lt c2_lt m) (by decide) h, fun h => by rw [h]⟩

theorem mem_V9_iff (m : ℕ) : toW 11 m ∈ V9 ↔ actM c2 m = 0 := by
  rw [V9, MonoidHom.mem_ker, beta2_eq_one_iff]

theorem beta2_surjective : Function.Surjective beta2 := by
  intro w
  obtain ⟨y, hy, rfl⟩ := toW_surj 2 w
  have : ∀ y < 4, ∃ m < 2 ^ 11, actM c2 m = y := by decide +kernel
  obtain ⟨m, -, hm⟩ := this y hy
  exact ⟨toW 11 m, by rw [beta2_toW, hm]⟩

theorem card_V9 : Nat.card ↥V9 = 512 := by
  have h := Subgroup.card_ker_mul_card_of_surjective beta2_surjective
  have h1 : Nat.card (Wn 2) = 4 := by
    rw [Nat.card_eq_fintype_card, card_Wn]
    norm_num
  have h2 : Nat.card W11 = 2 ^ 11 := by
    rw [Nat.card_eq_fintype_card]
    exact card_Wn 11
  rw [h1, h2] at h
  have : Nat.card ↥(beta2.ker) = 512 := by omega
  exact this

theorem rkIdx_V9 : rkIdx V9 = 2 := by
  have h : V9.index = 4 := by
    rw [V9, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ beta2_surjective,
      Subgroup.card_top, Nat.card_eq_fintype_card, card_Wn]
    norm_num
  unfold rkIdx
  rw [h]
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this, padicValNat.prime_pow]

@[expose] def t3Cols : List ℕ := [834, 554, 163, 256, 227, 492, 1024, 1104, 1440, 18, 20]

@[expose] def t2Cols : List ℕ := [626, 817, 472, 176, 372, 64, 60, 156, 412, 2035, 1055]

theorem t3Cols_eq : matOf 11 (act11 t3Arr) = t3Cols := by decide +kernel

theorem t2Cols_eq : matOf 11 (act11 t2Arr) = t2Cols := by decide +kernel

@[expose] noncomputable def gA : MulAut W11 := rhoTrA

@[expose] noncomputable def gB : MulAut W11 := rhoTrB

@[expose] noncomputable def gT3 : MulAut W11 := rhoM24 ⟨t3P, t3_mem⟩

@[expose] noncomputable def gT2 : MulAut W11 := rhoM24 ⟨t2P, t2_mem⟩

theorem actsBy_gA : ActsBy gA trACols := actsBy_rhoTrA

theorem actsBy_gB : ActsBy gB trBCols := actsBy_rhoTrB

theorem actsBy_gT3 : ActsBy gT3 t3Cols := by
  rw [← t3Cols_eq]
  exact actsBy_of_xorLin (xorLin_act11 _) (rho11_toW AutPerm le_rfl _ hasArr_t3)

theorem actsBy_gT2 : ActsBy gT2 t2Cols := by
  rw [← t2Cols_eq]
  exact actsBy_of_xorLin (xorLin_act11 _) (rho11_toW AutPerm le_rfl _ hasArr_t2)

@[expose] def genSet : Set (MulAut W11) := {gA, gB, gT3, gT2}

theorem img11_closure_le {S : Set (Equiv.Perm (Fin 24))} {N : Subgroup (MulAut W11)}
    (hS : ∀ σ ∈ S, ∃ h : σ ∈ AutPerm, rhoM24 ⟨σ, h⟩ ∈ N) : img11 (Subgroup.closure S) ≤ N := by
  have key : ∀ σ : Equiv.Perm (Fin 24), σ ∈ Subgroup.closure S →
      ∃ h : σ ∈ AutPerm, rhoM24 ⟨σ, h⟩ ∈ N := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem y hy => exact hS y hy
    | one => exact ⟨AutPerm.one_mem, by
        have : (⟨1, AutPerm.one_mem⟩ : ↥AutPerm) = 1 := rfl
        rw [this, map_one]; exact N.one_mem⟩
    | mul a b _ _ ha hb =>
      obtain ⟨h1, h1'⟩ := ha
      obtain ⟨h2, h2'⟩ := hb
      refine ⟨AutPerm.mul_mem h1 h2, ?_⟩
      have : (⟨a * b, AutPerm.mul_mem h1 h2⟩ : ↥AutPerm) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
      rw [this, map_mul]
      exact N.mul_mem h1' h2'
    | inv a _ ha =>
      obtain ⟨h1, h1'⟩ := ha
      refine ⟨AutPerm.inv_mem h1, ?_⟩
      have : (⟨a⁻¹, AutPerm.inv_mem h1⟩ : ↥AutPerm) = ⟨a, h1⟩⁻¹ := rfl
      rw [this, map_inv]
      exact N.inv_mem h1'
  rintro _ ⟨⟨σ, hσA⟩, hx, rfl⟩
  obtain ⟨h, hh⟩ := key σ (Subgroup.mem_subgroupOf.1 hx)
  exact hh

theorem img11_stabUTP :
    img11 stabUTP = Subgroup.closure genSet := by
  refine le_antisymm ?_ ?_
  · rw [← stabUTP_eq_genT, genT]
    refine img11_closure_le ?_
    rintro σ (rfl | rfl | rfl | rfl)
    · exact ⟨trA_mem, Subgroup.subset_closure (by simp [genSet, gA, rhoTrA])⟩
    · exact ⟨trB_mem, Subgroup.subset_closure (by simp [genSet, gB, rhoTrB])⟩
    · exact ⟨t3_mem, Subgroup.subset_closure (by simp [genSet, gT3])⟩
    · exact ⟨t2_mem, Subgroup.subset_closure (by simp [genSet, gT2])⟩
  · rw [Subgroup.closure_le]
    have hmem : ∀ σ ∈ stabUTP, ∀ h : σ ∈ AutPerm, rhoM24 ⟨σ, h⟩ ∈ img11 stabUTP :=
      fun σ hσ h => ⟨⟨σ, h⟩, Subgroup.mem_subgroupOf.2 hσ, rfl⟩
    have hgen : ∀ σ ∈ genT, σ ∈ stabUTP := fun σ hσ => stabUTP_eq_genT ▸ hσ
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hmem trA (hgen _ (Subgroup.subset_closure (by simp))) trA_mem
    · exact hmem trB (hgen _ (Subgroup.subset_closure (by simp))) trB_mem
    · exact hmem t3P (hgen _ (Subgroup.subset_closure (by simp))) t3_mem
    · exact hmem t2P (hgen _ (Subgroup.subset_closure (by simp))) t2_mem

theorem v9_comm : ∀ b ∈ v9Basis, ∃ i < 6, ∃ m < 2 ^ 11, actM (ktCols i) m ^^^ m = b := by
  intro b hb
  simp only [v9Basis, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, 1, by norm_num, by decide +kernel⟩
  · exact ⟨4, by norm_num, 10, by norm_num, by decide +kernel⟩
  · exact ⟨2, by norm_num, 263, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 519, by norm_num, by decide +kernel⟩
  · exact ⟨5, by norm_num, 7, by norm_num, by decide +kernel⟩
  · exact ⟨0, by norm_num, 256, by norm_num, by decide +kernel⟩
  · exact ⟨1, by norm_num, 512, by norm_num, by decide +kernel⟩
  · exact ⟨2, by norm_num, 256, by norm_num, by decide +kernel⟩
  · exact ⟨3, by norm_num, 18, by norm_num, by decide +kernel⟩

theorem v9_nodup : (combos v9Basis).Nodup := by decide +kernel

theorem v9_lt : ∀ a ∈ v9Basis, a < 2 ^ 11 := by decide

theorem UT_le_V9 : UT ≤ V9 := by
  rintro _ ⟨m, hm, rfl⟩
  have hlt : m < 2 ^ 11 := combos_lt uTBasis_lt m hm
  rw [mem_V9_iff]
  have : ∀ m ∈ uTMasks, actM c2 m = 0 := by decide +kernel
  exact this m ((uT_combos m hlt).1 hm)

theorem comm_toW {g : MulAut W11} {cols : List ℕ} (hg : ActsBy g cols) (m : ℕ) :
    g (toW 11 m) * (toW 11 m)⁻¹ = toW 11 (actM cols m ^^^ m) := by
  have h2 : g (toW 11 m) = toW 11 (actM cols m) := hg m
  rw [h2, toW_inv_self, ← toW_xor]

@[expose] def Ntriv : Subgroup (MulAut W11) where
  carrier := {g | ∀ v, beta2 (g v) = beta2 v}
  mul_mem' {a b} ha hb v := by
    have h2 : (a * b : MulAut W11) v = a (b v) := rfl
    rw [h2, ha, hb]
  one_mem' _ := rfl
  inv_mem' {a} ha v := by
    have h1 := ha (a⁻¹ v)
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm

theorem commV_le_V9 {X : Subgroup (MulAut W11)} (hX : X ≤ Ntriv) :
    CFSG.Quasithin.commV X ≤ V9 := by
  refine (Subgroup.closure_le V9).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  show beta2 (x v * v⁻¹) = 1
  have h1 : beta2 (x v) = beta2 v := hX hx v
  calc beta2 (x v * v⁻¹) = beta2 (x v) * beta2 v⁻¹ := map_mul _ _ _
    _ = beta2 v * beta2 v⁻¹ := by rw [h1]
    _ = 1 := by
      rw [← map_mul]
      exact (congrArg beta2 (mul_inv_cancel v)).trans (map_one _)

theorem mem_Ntriv_of_cols {g : MulAut W11} {cols : List ℕ} (hg : ActsBy g cols)
    (h : ∀ m < 2 ^ 11, actM c2 (actM cols m) = actM c2 m) : g ∈ Ntriv := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  rw [hg m, beta2_toW, beta2_toW, h m hm]

theorem gA_mem_Ntriv : gA ∈ Ntriv :=
  mem_Ntriv_of_cols actsBy_gA (by decide +kernel)

theorem gB_mem_Ntriv : gB ∈ Ntriv :=
  mem_Ntriv_of_cols actsBy_gB (by decide +kernel)

theorem img11_trQ_le_Ntriv : img11 trQ ≤ Ntriv := by
  refine img11_closure_le (S := {trA, trB}) ?_
  rintro σ (rfl | rfl)
  · exact ⟨trA_mem, gA_mem_Ntriv⟩
  · exact ⟨trB_mem, gB_mem_Ntriv⟩

theorem maskSub_v9_le_commV :
    maskSub 11 v9Basis ≤ CFSG.Quasithin.commV (img11 trQ ⊓ centSub UT) := by
  rintro _ ⟨m, hm, rfl⟩
  refine (MaskCoords.std 11).vm_mem_of_combos (CFSG.Quasithin.commV (img11 trQ ⊓ centSub UT))
    (l := v9Basis) ?_ m hm
  intro b hb
  obtain ⟨i, hi, m', hm', rfl⟩ := v9_comm b hb
  have hk : ktRho i ∈ img11 trQ ⊓ centSub UT := ⟨ktRho_mem_img i, ktRho_mem_cent hi⟩
  have := mem_commV hk (toW 11 m')
  have e : ktRho i (toW 11 m') * (toW 11 m')⁻¹ = toW 11 (actM (ktCols i) m' ^^^ m') :=
    comm_toW (actsBy_ktRho hi) m'
  have e' : (MaskCoords.std 11).vm (actM (ktCols i) m' ^^^ m') =
      ktRho i (toW 11 m') * (toW 11 m')⁻¹ := e.symm
  rw [e']
  exact this

theorem maskSub_v9_eq : maskSub 11 v9Basis = V9 := by
  have h1 := maskSub_v9_le_commV
  have h2 : CFSG.Quasithin.commV (img11 trQ ⊓ centSub UT) ≤ V9 :=
    commV_le_V9 (inf_le_left.trans img11_trQ_le_Ntriv)
  have hcard : Nat.card ↥(maskSub 11 v9Basis) = 512 := by
    rw [card_maskSub v9_lt v9_nodup]
    rfl
  exact Subgroup.eq_of_le_of_card_ge (h1.trans h2) (by rw [hcard, card_V9])

theorem commV_cent : CFSG.Quasithin.commV (img11 trQ ⊓ centSub UT) = V9 := by
  have h1 := maskSub_v9_le_commV
  have h2 : CFSG.Quasithin.commV (img11 trQ ⊓ centSub UT) ≤ V9 :=
    commV_le_V9 (inf_le_left.trans img11_trQ_le_Ntriv)
  exact le_antisymm h2 (maskSub_v9_eq ▸ h1)

theorem commV_img11_Kperm : CFSG.Quasithin.commV (img11 Kperm) = V9 := by
  rw [img11_Kperm]
  exact commV_cent

theorem commV_img11_trQ : CFSG.Quasithin.commV (img11 trQ) = V9 := by
  refine le_antisymm (commV_le_V9 img11_trQ_le_Ntriv) ?_
  rw [← commV_cent]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact ⟨x, hx.1, v, rfl⟩

end CFSG.Quasithin.H156
