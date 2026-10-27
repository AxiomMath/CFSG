module

public import CFSG.GroupTheory.SupCommute
public import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot
public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Setup
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem mem_closure_bt_iff {b t : H} (htb : t * b * t⁻¹ = b⁻¹) (ht2 : t * t = 1) {y : H}
    (hy : y ∈ Subgroup.closure ({b, t} : Set H)) : ∃ i : ℤ, y = b ^ i ∨ y = b ^ i * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ j : ℤ, t * b ^ j * t⁻¹ = b ^ (-j) := by
    intro j
    have := map_zpow (MulAut.conj t) b j
    simp only [MulAut.conj_apply] at this
    rw [this, htb, inv_zpow', zpow_neg]
  have hconj' : ∀ j : ℤ, t * b ^ j = b ^ (-j) * t := by
    intro j
    calc t * b ^ j = (t * b ^ j * t⁻¹) * t := by group
      _ = b ^ (-j) * t := by rw [hconj]
  let S : Subgroup H :=
    { carrier := {y | ∃ i : ℤ, y = b ^ i ∨ y = b ^ i * t}
      one_mem' := ⟨0, Or.inl (by simp)⟩
      mul_mem' := by
        rintro _ _ ⟨i, hi | hi⟩ ⟨j, hj | hj⟩
        · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
        · exact ⟨i + j, Or.inr (by rw [hi, hj, zpow_add, mul_assoc])⟩
        · refine ⟨i - j, Or.inr ?_⟩
          rw [hi, hj]
          calc b ^ i * t * b ^ j = b ^ i * (t * b ^ j) := by group
            _ = b ^ i * (b ^ (-j) * t) := by rw [hconj']
            _ = b ^ (i - j) * t := by rw [← mul_assoc, ← zpow_add, ← sub_eq_add_neg]
        · refine ⟨i - j, Or.inl ?_⟩
          rw [hi, hj]
          calc b ^ i * t * (b ^ j * t) = b ^ i * (t * b ^ j) * t := by group
            _ = b ^ i * (b ^ (-j) * t) * t := by rw [hconj']
            _ = b ^ (i - j) * (t * t) := by
              rw [← mul_assoc, ← zpow_add, ← sub_eq_add_neg, mul_assoc]
            _ = b ^ (i - j) := by rw [ht2, mul_one]
      inv_mem' := by
        rintro _ ⟨i, hi | hi⟩
        · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [hi]
          calc (b ^ i * t)⁻¹ = t⁻¹ * (b ^ i)⁻¹ := by rw [mul_inv_rev]
            _ = t * b ^ (-i) := by rw [htinv, zpow_neg]
            _ = b ^ i * t := by rw [hconj', neg_neg] }
  have hle : Subgroup.closure ({b, t} : Set H) ≤ S := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨1, Or.inl (by simp)⟩
    · exact ⟨0, Or.inr (by simp)⟩
  exact hle hy


theorem FS79Hyp.Y_comm_J (h : FS79Hyp b t b₁ b₂ J) {y j : H}
    (hy : y ∈ Subgroup.closure ({b, t} : Set H)) (hj : j ∈ J) : y * j = j * y := by
  have hle : Subgroup.closure ({b, t} : Set H) ≤ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t hj)
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) j hj).symm

theorem mem_Nor_self (b : H) : b ∈ Nor (Subgroup.zpowers b) :=
  Subgroup.le_normalizer (Subgroup.mem_zpowers b)

theorem FS79Hyp.t_mem_Nor (h : FS79Hyp b t b₁ b₂ J) : t ∈ Nor (Subgroup.zpowers b) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : (Subgroup.zpowers b).map (MulAut.conj t) = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    have hconj : (↑(MulAut.conj t) : H →* H) b = b⁻¹ := by
      simpa [MulAut.conj_apply] using h.inv_b
    rw [hconj, Subgroup.zpowers_inv]
  exact hmap

theorem FS79Hyp.Y_le_Nor (h : FS79Hyp b t b₁ b₂ J) :
    Subgroup.closure ({b, t} : Set H) ≤ Nor (Subgroup.zpowers b) := by
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | rfl
  · exact mem_Nor_self _
  · exact h.t_mem_Nor

theorem FS79Hyp.J_le_Nor (h : FS79Hyp b t b₁ b₂ J) : J ≤ Nor (Subgroup.zpowers b) :=
  fun x hx => h.cen_le_nor (h.J_le_cen_b hx)

theorem FS79Hyp.eq_bot_of_normal_in_J (h : FS79Hyp b t b₁ b₂ J) {X : Subgroup H} (hXJ : X ≤ J)
    (hXn : ∀ j ∈ J, ∀ x ∈ X, j * x * j⁻¹ ∈ X) (hX : ¬ 360 ∣ Nat.card X) : X = ⊥ := by
  classical
  obtain ⟨e⟩ := h.J_perm
  let Xj : Subgroup ↥J := X.subgroupOf J
  have hXjn : Xj.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hXn (g : H) g.2 (x : H) hx⟩
  let N : Subgroup (Equiv.Perm (Fin 6)) := Xj.map e.toMonoidHom
  haveI hNn : N.Normal := Subgroup.Normal.map hXjn e.toMonoidHom e.surjective
  have hcardN : Nat.card N = Nat.card X := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv
  by_cases hN : N = ⊥
  · have hXj : Xj = ⊥ := (Subgroup.map_eq_bot_iff_of_injective Xj e.injective).mp hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hXJ hx⟩ : ↥J) ∈ Xj := hx
    rw [hXj, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · exfalso
    have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
    have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hnt
    have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card N := Subgroup.card_dvd_of_le hA
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    rw [h360, hcardN] at hdvd
    exact hX hdvd

theorem FS79Hyp.eq_one_of_comm_J (h : FS79Hyp b t b₁ b₂ J) {j : H} (hj : j ∈ J)
    (hc : ∀ j' ∈ J, j * j' = j' * j) : j = 1 := by
  obtain ⟨e⟩ := h.J_perm
  have hZ : (⟨j, hj⟩ : ↥J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc (g : H) g.2).symm
  have hZ' : e ⟨j, hj⟩ ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨⟨j, hj⟩, hZ, rfl⟩
  rw [CFSG.ClassicalInvolution.Sp62Rec.I1.center_perm_fin_six_eq_bot, Subgroup.mem_bot] at hZ'
  have h1 : (⟨j, hj⟩ : ↥J) = 1 := by
    apply e.injective
    rw [map_one]
    exact hZ'
  exact congrArg Subtype.val h1


theorem Opp_eq_one_of_pow_three {Y : Subgroup H} {x : H} (hx : x ∈ Opp 3 Y) (h3 : x ^ 3 = 1) :
    x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (Opp 3 Y)) := L14.Opp_coprime 3 Y
  have h1 : orderOf (⟨x, hx⟩ : ↥(Opp 3 Y)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨x, hx⟩ : ↥(Opp 3 Y)) ∣ Nat.card (Opp 3 Y) := orderOf_dvd_natCard _
  have h3' := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := orderOf_eq_one_iff.1 h3'
  simpa using congrArg Subtype.val this

theorem FS79Hyp.K_comm_J (h : FS79Hyp b t b₁ b₂ J) {k j : H}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hj : j ∈ J) : k * j = j * k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup H := Opp 3 (Nor (Subgroup.zpowers b)) with hK
  have hKN : K ≤ Nor (Subgroup.zpowers b) := L14.Opp_le 3 _
  have hX : J ⊓ K = ⊥ := by
    refine h.eq_bot_of_normal_in_J inf_le_left ?_ ?_
    · intro j' hj' x hx
      exact ⟨J.mul_mem (J.mul_mem hj' hx.1) (J.inv_mem hj'),
        L14.Opp_conj_mem (h.J_le_Nor hj') hx.2⟩
    · intro h360
      have h3 : 3 ∣ Nat.card ↥(J ⊓ K) := (show 3 ∣ 360 by norm_num).trans h360
      have hcop : Nat.Coprime 3 (Nat.card ↥(J ⊓ K)) :=
        (L14.Opp_coprime 3 _).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3
  have hkJ : k * j * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (h.N_le_NJ (hKN hk)) j).mp hj
  have hjk : j * k⁻¹ * j⁻¹ ∈ K := L14.Opp_conj_mem (h.J_le_Nor hj) (K.inv_mem hk)
  have hw : (k * j * k⁻¹) * j⁻¹ ∈ J ⊓ K := by
    refine ⟨J.mul_mem hkJ (J.inv_mem hj), ?_⟩
    have : (k * j * k⁻¹) * j⁻¹ = k * (j * k⁻¹ * j⁻¹) := by group
    rw [this]
    exact K.mul_mem hk hjk
  rw [hX, Subgroup.mem_bot] at hw
  calc k * j = (k * j * k⁻¹) * k := by group
    _ = j * k := by rw [mul_inv_eq_one.mp hw]

theorem FS79Hyp.K_inf_Y (h : FS79Hyp b t b₁ b₂ J) :
    Opp 3 (Nor (Subgroup.zpowers b)) ⊓ Subgroup.closure ({b, t} : Set H) = ⊥ := by
  classical
  set K : Subgroup H := Opp 3 (Nor (Subgroup.zpowers b)) with hK
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.ord_t]
    exact pow_orderOf_eq_one t
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwY⟩
  obtain ⟨i, hw | hw⟩ := mem_closure_bt_iff h.inv_b ht2 hwY
  · have : w ^ 3 = 1 := by
      rw [hw, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    exact Subgroup.mem_bot.mpr (Opp_eq_one_of_pow_three hwK this)
  · exfalso
    have hcomm : b * w * b⁻¹ * w⁻¹ ∈ K :=
      K.mul_mem (L14.Opp_conj_mem (mem_Nor_self b) hwK) (K.inv_mem hwK)
    have htb : t * b⁻¹ * t⁻¹ = b := by
      have := congrArg (fun x => x⁻¹) h.inv_b
      simpa [mul_inv_rev, mul_assoc] using this
    have hb2 : b * w * b⁻¹ * w⁻¹ = b ^ 2 := by
      rw [hw]
      calc b * (b ^ i * t) * b⁻¹ * (b ^ i * t)⁻¹
          = b * b ^ i * (t * b⁻¹ * t⁻¹) * (b ^ i)⁻¹ := by group
        _ = b * b ^ i * b * (b ^ i)⁻¹ := by rw [htb]
        _ = b ^ 2 := by group
    rw [hb2] at hcomm
    have hb2K : (b ^ 2) ^ 2 = b := by
      calc (b ^ 2) ^ 2 = b ^ 4 := by group
        _ = b * b ^ 3 := by group
        _ = b := by rw [hb3, mul_one]
    have hbK : b ∈ K := by
      rw [← hb2K]
      exact K.pow_mem hcomm 2
    have := Opp_eq_one_of_pow_three hbK hb3
    have h1 : orderOf b = 1 := by rw [this]; exact orderOf_one
    rw [h.ord_b] at h1
    omega

theorem FS79Hyp.K_inf_M0 (h : FS79Hyp b t b₁ b₂ J) :
    Opp 3 (Nor (Subgroup.zpowers b)) ⊓ (Subgroup.closure ({b, t} : Set H) ⊔ J) = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwM⟩
  obtain ⟨y, hy, j, hj, rfl⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hwM
  have hj1 : j = 1 := by
    refine h.eq_one_of_comm_J hj fun j' hj' => ?_
    have h1 := h.K_comm_J hwK hj'
    have h2 : y * j' = j' * y := h.Y_comm_J hy hj'
    calc j * j' = y⁻¹ * (y * j * j') := by group
      _ = y⁻¹ * (j' * (y * j)) := by rw [h1]
      _ = y⁻¹ * ((j' * y) * j) := by group
      _ = y⁻¹ * ((y * j') * j) := by rw [← h2]
      _ = j' * j := by group
  subst hj1
  have hyK : y * 1 ∈ Opp 3 (Nor (Subgroup.zpowers b)) ⊓ Subgroup.closure ({b, t} : Set H) :=
    ⟨hwK, by simpa using hy⟩
  rw [h.K_inf_Y, Subgroup.mem_bot] at hyK
  rw [Subgroup.mem_bot]
  simpa using hyK


theorem FS79Hyp.M0_le_Nor (h : FS79Hyp b t b₁ b₂ J) :
    Subgroup.closure ({b, t} : Set H) ⊔ J ≤ Nor (Subgroup.zpowers b) :=
  sup_le h.Y_le_Nor h.J_le_Nor

theorem FS79Hyp.exists_rho (h : FS79Hyp b t b₁ b₂ J) {n : H} (hn : n ∈ Nor (Subgroup.zpowers b)) :
    ∃ m ∈ Subgroup.closure ({b, t} : Set H) ⊔ J,
      n * m⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b)) := by
  have hmem : n ∈ setMul (Opp 3 (Nor (Subgroup.zpowers b)))
      (Subgroup.closure ({b, t} : Set H) ⊔ J) := by
    rw [h.N_eq]
    exact hn
  obtain ⟨k, hk, m, hm, hnkm⟩ := hmem
  refine ⟨m, hm, ?_⟩
  rw [hnkm]
  simpa using hk

theorem FS79Hyp.M0_eq_of_mul_inv_mem (h : FS79Hyp b t b₁ b₂ J) {m m' : H}
    (hm : m ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hm' : m' ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hk : m * m'⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b))) : m = m' := by
  have hmem : m * m'⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b)) ⊓
      (Subgroup.closure ({b, t} : Set H) ⊔ J) :=
    ⟨hk, Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hm')⟩
  rw [h.K_inf_M0, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

open _root_.Classical in
noncomputable def FS79Hyp.rho (h : FS79Hyp b t b₁ b₂ J) (n : H) : H :=
  if hn : n ∈ Nor (Subgroup.zpowers b) then Classical.choose (h.exists_rho hn) else 1

theorem FS79Hyp.rho_spec (h : FS79Hyp b t b₁ b₂ J) {n : H} (hn : n ∈ Nor (Subgroup.zpowers b)) :
    h.rho n ∈ Subgroup.closure ({b, t} : Set H) ⊔ J ∧
      n * (h.rho n)⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b)) := by
  unfold FS79Hyp.rho
  rw [dif_pos hn]
  exact Classical.choose_spec (h.exists_rho hn)

theorem FS79Hyp.rho_eq (h : FS79Hyp b t b₁ b₂ J) {n m : H} (hn : n ∈ Nor (Subgroup.zpowers b))
    (hm : m ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hk : n * m⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b))) : h.rho n = m := by
  obtain ⟨hr, hrk⟩ := h.rho_spec hn
  refine h.M0_eq_of_mul_inv_mem hr hm ?_
  have := (Opp 3 (Nor (Subgroup.zpowers b))).mul_mem
    ((Opp 3 (Nor (Subgroup.zpowers b))).inv_mem hrk) hk
  have e : (n * (h.rho n)⁻¹)⁻¹ * (n * m⁻¹) = h.rho n * m⁻¹ := by group
  rwa [e] at this

theorem FS79Hyp.rho_of_mem_M0 (h : FS79Hyp b t b₁ b₂ J) {m : H}
    (hm : m ∈ Subgroup.closure ({b, t} : Set H) ⊔ J) : h.rho m = m :=
  h.rho_eq (h.M0_le_Nor hm) hm (by simp)

theorem FS79Hyp.rho_of_mem_K (h : FS79Hyp b t b₁ b₂ J) {k : H}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) : h.rho k = 1 :=
  h.rho_eq (L14.Opp_le 3 _ hk) (Subgroup.one_mem _) (by simpa using hk)

theorem FS79Hyp.mem_K_of_rho_eq_one (h : FS79Hyp b t b₁ b₂ J) {n : H}
    (hn : n ∈ Nor (Subgroup.zpowers b)) (h1 : h.rho n = 1) :
    n ∈ Opp 3 (Nor (Subgroup.zpowers b)) := by
  have := (h.rho_spec hn).2
  rwa [h1, inv_one, mul_one] at this

theorem FS79Hyp.rho_mul (h : FS79Hyp b t b₁ b₂ J) {n n' : H} (hn : n ∈ Nor (Subgroup.zpowers b))
    (hn' : n' ∈ Nor (Subgroup.zpowers b)) : h.rho (n * n') = h.rho n * h.rho n' := by
  obtain ⟨hr, hrk⟩ := h.rho_spec hn
  obtain ⟨hr', hrk'⟩ := h.rho_spec hn'
  refine h.rho_eq ((Nor (Subgroup.zpowers b)).mul_mem hn hn')
    (Subgroup.mul_mem _ hr hr') ?_
  have hconj : h.rho n * (n' * (h.rho n')⁻¹) * (h.rho n)⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers b)) :=
    L14.Opp_conj_mem (h.M0_le_Nor hr) hrk'
  have := (Opp 3 (Nor (Subgroup.zpowers b))).mul_mem hrk hconj
  have e : n * (h.rho n)⁻¹ * (h.rho n * (n' * (h.rho n')⁻¹) * (h.rho n)⁻¹) =
      n * n' * (h.rho n * h.rho n')⁻¹ := by group
  rwa [e] at this

theorem FS79Hyp.rho_one (h : FS79Hyp b t b₁ b₂ J) : h.rho 1 = 1 :=
  h.rho_of_mem_M0 (Subgroup.one_mem _)

theorem FS79Hyp.rho_inv (h : FS79Hyp b t b₁ b₂ J) {n : H} (hn : n ∈ Nor (Subgroup.zpowers b)) :
    h.rho n⁻¹ = (h.rho n)⁻¹ := by
  have h1 := h.rho_mul hn ((Nor (Subgroup.zpowers b)).inv_mem hn)
  rw [mul_inv_cancel, h.rho_one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem FS79Hyp.rho_conj (h : FS79Hyp b t b₁ b₂ J) {n m : H}
    (hn : n ∈ Nor (Subgroup.zpowers b)) (hm : m ∈ Nor (Subgroup.zpowers b)) :
    h.rho (n * m * n⁻¹) = h.rho n * h.rho m * (h.rho n)⁻¹ := by
  rw [h.rho_mul ((Nor (Subgroup.zpowers b)).mul_mem hn hm) ((Nor (Subgroup.zpowers b)).inv_mem hn),
    h.rho_mul hn hm, h.rho_inv hn]

end CFSG.RankThree.PartTwo.Sec21.FF81
