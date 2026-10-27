module

public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.DCE.B433Maximal

public section

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived)
open CFSG.YGroups.DCE.B433 (psi psi_range_maximal)

@[expose] noncomputable def qc : Q343 := Q343.π (Y343.F 1 2 3)

theorem y443Q343Hom_gen
    {c : ℕ} (hc : c < 11) :
    y443Q343Hom (Q343.π (yGen 3 4 3 c)) = y443Tl (shiftAt 3 c) := y443Q343Hom_π hc

theorem y443Q343Hom_qc :
    y443Q343Hom qc = y443C := by
  have e : ∀ c < 11, y443Q343Hom (Q343.π (yGen 3 4 3 c)) = y443Tl (shiftAt 3 c) :=
    fun c hc => y443Q343Hom_gen hc
  have hF : Y343.F 1 2 3 = (yGen 3 4 3 0 * yGen 3 4 3 1 * yGen 3 4 3 2 * yGen 3 4 3 3 *
      yGen 3 4 3 4 * yGen 3 4 3 5 * yGen 3 4 3 8) ^ 9 := rfl
  have hF0 : y443F0 = (y443Gen 0 * y443Gen 1 * y443Gen 2 * y443Gen 3 * y443Gen 5 * y443Gen 6 *
      y443Gen 9) ^ 9 := rfl
  rw [← y443Pi_F0, qc, hF, hF0]
  simp only [map_pow, map_mul]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num), e 8 (by norm_num), y443Pi_gen, y443Pi_gen, y443Pi_gen,
    y443Pi_gen, y443Pi_gen, y443Pi_gen, y443Pi_gen]
  have h4 : shiftAt 3 4 = 5 := by decide
  have h5 : shiftAt 3 5 = 6 := by decide
  have h8 : shiftAt 3 8 = 9 := by decide
  have h0 : shiftAt 3 0 = 0 := by decide
  have h1 : shiftAt 3 1 = 1 := by decide
  have h2 : shiftAt 3 2 = 2 := by decide
  have h3 : shiftAt 3 3 = 3 := by decide
  rw [h0, h1, h2, h3, h4, h5, h8]

@[expose] noncomputable def beta :
    Q343 →* B433 :=
  R433.toB433.comp Q343EquivR433.toMonoidHom

theorem beta_surjective :
    Function.Surjective beta := by
  intro b
  obtain ⟨r, rfl⟩ := R433.toB433_surjective b
  refine ⟨Q343EquivR433.symm r, ?_⟩
  rw [beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem Q343EquivR433_qc :
    Q343EquivR433 qc = R433.c312 := by
  rw [qc, Q343EquivR433_π, cyc343Equiv_F123]
  rfl

theorem ker_beta :
    beta.ker = Subgroup.zpowers qc := by
  ext q
  rw [MonoidHom.mem_ker, beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
    R433.ker_toB433, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Q343EquivR433.injective ?_⟩
    rw [map_zpow, Q343EquivR433_qc, hn]
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [map_zpow, Q343EquivR433_qc]⟩

theorem qc_mul_self :
    qc * qc = 1 := by
  apply Q343EquivR433.injective
  rw [map_mul, Q343EquivR433_qc, R433.c312_mul_self, map_one]

theorem qc_comm
    (q : Q343) : q * qc = qc * q := by
  apply Q343EquivR433.injective
  rw [map_mul, map_mul, Q343EquivR433_qc]
  exact (Subgroup.mem_center_iff.1 R433.c312_mem_center _)

theorem commutator_Q343 :
    commutator Q343 = ⊤ := by
  have : Group.IsPerfect R433 := R433.isPerfect
  have : Group.IsPerfect Q343 :=
    Group.IsPerfect.ofSurjective (f := Q343EquivR433.symm.toMonoidHom)
      Q343EquivR433.symm.surjective
  exact Group.isPerfect_def.1 this

@[expose] noncomputable def Kq : Subgroup Q343 :=
  Subgroup.closure ((fun c => Q343.π (yGen 3 4 3 c)) '' {c | c < 11 ∧ c ≠ 3})

theorem map_eta_Kq_le :
    Kq.map y443Q343Hom ≤ y443K := by
  rw [Kq, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, ⟨hc, hc3⟩, rfl⟩, rfl⟩
  show y443Q343Hom (Q343.π (yGen 3 4 3 c)) ∈ y443K
  rw [y443Q343Hom_gen hc]
  have hl : shiftAt 3 c < 12 := by unfold shiftAt; split_ifs <;> omega
  have h4 : shiftAt 3 c ≠ 4 := by unfold shiftAt; split_ifs <;> omega
  have h3 : shiftAt 3 c ≠ 3 := by unfold shiftAt; split_ifs <;> omega
  refine y443T_mem_K ?_ ?_
  · intro h
    apply h4
    rw [← y443LetterOfGen_eq_four_iff] at h
    rwa [y443LetterOfGen_genOfLetter _ hl] at h
  · intro h
    apply h3
    rw [← y443LetterOfGen_eq_three_iff] at h
    rwa [y443LetterOfGen_genOfLetter _ hl] at h

theorem beta_gen
    {c : ℕ} (hc : c < 11) :
    beta (Q343.π (yGen 3 4 3 c)) = DCE.B433.qB (yGen 4 3 3 (cyc343Letter c)) := by
  rw [beta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Q343EquivR433_π,
    cyc343Equiv_yGen hc, R433.toB433_π]
  rfl

theorem psi_range_eq :
    psi.range = Subgroup.closure ((fun l => DCE.B433.qB (yGen 4 3 3 l)) '' Set.Iio 10) := by
  rw [MonoidHom.range_eq_map, ← closure_yGen 4 3 2, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, by rw [DCE.B433.psi, MonoidHom.comp_apply, DCE.B433.psiU_yGen hl]⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨yGen 4 3 2 l, ⟨l, hl, rfl⟩, by rw [DCE.B433.psi, MonoidHom.comp_apply,
      DCE.B433.psiU_yGen hl]⟩

theorem map_beta_Kq :
    Kq.map beta = psi.range := by
  rw [Kq, MonoidHom.map_closure, psi_range_eq]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_Iio]
  constructor
  · rintro ⟨_, ⟨c, ⟨hc, hc3⟩, rfl⟩, rfl⟩
    refine ⟨cyc343Letter c, ?_, (beta_gen hc).symm⟩
    have := cyc343Letter_lt c hc
    interval_cases c <;> simp_all [cyc343Letter]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨Q343.π (yGen 3 4 3 (cyc433Letter l)), ⟨cyc433Letter l, ⟨cyc433Letter_lt l (by omega),
      ?_⟩, rfl⟩, ?_⟩
    · interval_cases l <;> simp [cyc433Letter]
    · rw [beta_gen (cyc433Letter_lt l (by omega)), cyc343Letter_cyc433Letter l (by omega)]

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

@[expose] noncomputable def rho :
    Q343 →* G := f.comp y443Q343Hom

theorem range_rho :
    (rho f).range = y443H.map f := by
  rw [rho, MonoidHom.range_comp, y443Q343Hom_range]

theorem rho_injective
    (hN : Q343N ≤ Nat.card (y443H.map f)) : Function.Injective (rho f) := by
  have := Q343_finite_card_le.1
  have hle : Nat.card Q343 ≤ Nat.card (rho f).range := by
    rw [range_rho]
    exact Q343_finite_card_le.2.trans hN
  have hb := (rho f).rangeRestrict_surjective.bijective_of_nat_card_le hle
  intro a b hab
  apply hb.1
  exact Subtype.ext hab

theorem card_B433_ge
    (hN : Q343N ≤ Nat.card (y443H.map f)) :
    4154781481226426191177580544000000 ≤ Nat.card B433 := by
  have := Q343_finite_card_le.1
  have h1 : Q343N ≤ Nat.card Q343 := by
    have := Nat.card_le_card_of_surjective _ (rho f).rangeRestrict_surjective
    rw [range_rho] at this
    exact hN.trans this
  have h2 : Nat.card Q343 = Nat.card R433 := Nat.card_congr Q343EquivR433.toEquiv
  have h3 := R433.card_eq_mul
  have h4 : Nat.card (Subgroup.zpowers R433.c312) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) R433.c312_pow_two
  have hQ : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
  rw [h2, h3, hQ] at h1
  have := Nat.mul_le_mul_right (Nat.card B433) h4
  omega

@[expose] noncomputable def S :
    Subgroup Q343 :=
  (y443H.map f ⊓ (y443H.map f).comap (MulAut.conj (f y443X)).toMonoidHom).comap (rho f)

theorem mem_S
    {q : Q343} :
    q ∈ S f ↔ rho f q ∈ y443H.map f ∧ f y443X * rho f q * f y443X ∈ y443H.map f := by
  have hx : (f y443X)⁻¹ = f y443X := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right y443X_mul_self]
  simp only [S, Subgroup.mem_comap, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hx]

theorem Kq_le_S :
    Kq ≤ S f := by
  intro q hq
  have hk : y443Q343Hom q ∈ y443K := map_eta_Kq_le ⟨q, hq, rfl⟩
  obtain ⟨hH, hxH⟩ := y443K_le hk
  rw [mem_S]
  refine ⟨⟨_, hH, rfl⟩, ?_⟩
  obtain ⟨h, hh, he⟩ := hxH
  have hxx : y443X * y443Q343Hom q * y443X = h := by
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inv_eq_of_mul_eq_one_right y443X_mul_self]
    calc y443X * (y443X * h * y443X) * y443X = (y443X * y443X) * h * (y443X * y443X) := by group
      _ = h := by rw [y443X_mul_self, one_mul, mul_one]
  refine ⟨h, hh, ?_⟩
  rw [rho, MonoidHom.comp_apply, ← hxx, map_mul, map_mul]

theorem fC_comm
    {h : G} (hh : h ∈ y443H.map f) : h * f y443C = f y443C * h := by
  obtain ⟨hc, hcen⟩ := (y443_terminal_central_map f).1
  have := Subgroup.mem_center_iff.1 hcen ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem xcx_not_mem
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    f y443X * f y443C * f y443X ∉ y443H.map f := fun h => hd (fC_comm f h).symm

theorem x_not_mem
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    f y443X ∉ y443H.map f := by
  intro hx
  apply xcx_not_mem f hd
  have hc : f y443C ∈ y443H.map f := ⟨y443C, y443C_mem_H, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hc) hx

theorem qc_not_mem_S
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    qc ∉ S f := by
  intro h
  rw [mem_S] at h
  have e : rho f qc = f y443C := by rw [rho, MonoidHom.comp_apply, y443Q343Hom_qc]
  rw [e] at h
  exact xcx_not_mem f hd h.2

theorem zpowers_qc_le_center :
    Subgroup.zpowers qc ≤ Subgroup.center Q343 :=
  Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 fun g => qc_comm g)

instance zpowers_qc_normal :
    (Subgroup.zpowers qc).Normal :=
  Subgroup.normal_of_le_center zpowers_qc_le_center

theorem mem_sup_zpowers_qc
    {A : Subgroup Q343} {g : Q343} (hg : g ∈ A ⊔ Subgroup.zpowers qc) :
    g ∈ A ∨ g * qc ∈ A := by
  have hg' : g ∈ (↑(A ⊔ Subgroup.zpowers qc) : Set Q343) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.1 hg'
  rcases mem_zpowers_involution qc_mul_self hz with rfl | rfl
  · left; rwa [mul_one]
  · right; rwa [mul_assoc, qc_mul_self, mul_one]

theorem S_le_Kq
    (hN : Q343N ≤ Nat.card (y443H.map f))
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    S f ≤ Kq := by
  have hqc := qc_not_mem_S f hd
  have hle : psi.range ≤ (S f).map beta := by
    rw [← map_beta_Kq]
    exact Subgroup.map_mono (Kq_le_S f)
  rcases psi_range_maximal (card_B433_ge f hN) _ hle with h | h
  ·
    intro s hs
    have hs' : s ∈ (Kq.map beta).comap beta := by
      rw [map_beta_Kq, ← h]
      exact Subgroup.mem_comap.2 ⟨s, hs, rfl⟩
    rw [Subgroup.comap_map_eq, ker_beta] at hs'
    rcases mem_sup_zpowers_qc hs' with hk | hk
    · exact hk
    · exact absurd (by
        have := (S f).mul_mem ((S f).inv_mem hs) (Kq_le_S f hk)
        rwa [inv_mul_cancel_left] at this) hqc
  ·
    exfalso
    have htop : S f ⊔ Subgroup.zpowers qc = ⊤ := by
      rw [← ker_beta, ← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    have hnormal : (S f).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ S f ⊔ Subgroup.zpowers qc := by rw [htop]; trivial
      rcases mem_sup_zpowers_qc hg with hg1 | hg1
      · exact (S f).mul_mem ((S f).mul_mem hg1 hn) ((S f).inv_mem hg1)
      · have e : g * n * g⁻¹ = (g * qc) * n * (g * qc)⁻¹ := by
          rw [mul_inv_rev, show (g * qc) * n * (qc⁻¹ * g⁻¹) = g * (qc * n * qc⁻¹) * g⁻¹ by
            group, ← qc_comm n, mul_assoc n qc qc⁻¹, mul_inv_cancel, mul_one]
        rw [e]
        exact (S f).mul_mem ((S f).mul_mem hg1 hn) ((S f).inv_mem hg1)
    have hcomm : commutator Q343 ≤ S f :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop inferInstance
    rw [commutator_Q343, top_le_iff] at hcomm
    exact hqc (hcomm ▸ Subgroup.mem_top qc)

theorem edge_intersection
    (hN : Q343N ≤ Nat.card (y443H.map f))
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    f y443X ∉ y443H.map f ∧
      ∀ h ∈ y443H.map f, f y443X * h * f y443X ∈ y443H.map f →
        ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ f k = h := by
  refine ⟨x_not_mem f hd, fun h hh hxh => ?_⟩
  rw [← range_rho] at hh
  obtain ⟨q, rfl⟩ := hh
  have hq : q ∈ S f := (mem_S f).2 ⟨by rw [← range_rho]; exact ⟨q, rfl⟩, hxh⟩
  have hk : y443Q343Hom q ∈ y443K := map_eta_Kq_le ⟨q, S_le_Kq f hN hd hq, rfl⟩
  obtain ⟨hH, hxH⟩ := y443K_le hk
  refine ⟨y443Q343Hom q, hH, ?_, rfl⟩
  obtain ⟨h', hh', he⟩ := hxH
  have : y443X * y443Q343Hom q * y443X = h' := by
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inv_eq_of_mul_eq_one_right y443X_mul_self]
    calc y443X * (y443X * h' * y443X) * y443X = (y443X * y443X) * h' * (y443X * y443X) := by
          group
      _ = h' := by rw [y443X_mul_self, one_mul, mul_one]
  rw [this]
  exact hh'

theorem injOn_H
    (hN : Q343N ≤ Nat.card (y443H.map f)) : Set.InjOn f y443H := by
  intro a ha b hb hab
  rw [SetLike.mem_coe, ← y443Q343Hom_range] at ha hb
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨q', rfl⟩ := hb
  have : q = q' := rho_injective f hN hab
  rw [this]

theorem inf_conj_eq
    (hN : Q343N ≤ Nat.card (y443H.map f))
    (hd : f y443C * (f y443X * f y443C * f y443X) ≠ (f y443X * f y443C * f y443X) * f y443C) :
    y443H.map f ⊓ (y443H.map f).map (MulAut.conj (f y443X)).toMonoidHom = y443K.map f := by
  have hx : (f y443X)⁻¹ = f y443X := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right y443X_mul_self]
  apply le_antisymm
  · rintro g ⟨hg, hxg⟩
    obtain ⟨h, hh, rfl⟩ := hxg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx] at hg ⊢
    have hxx : f y443X * (f y443X * h * f y443X) * f y443X = h := by
      calc f y443X * (f y443X * h * f y443X) * f y443X
          = (f y443X * f y443X) * h * (f y443X * f y443X) := by group
        _ = h := by rw [← map_mul, y443X_mul_self, map_one, one_mul, mul_one]
    have hg' := hg
    rw [← range_rho] at hg'
    obtain ⟨q, hq⟩ := hg'
    have hS : q ∈ S f := (mem_S f).2 ⟨by rw [hq]; exact hg, by rw [hq, hxx]; exact hh⟩
    exact ⟨y443Q343Hom q, map_eta_Kq_le ⟨q, S_le_Kq f hN hd hS, rfl⟩, hq⟩
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨hH, hxH⟩ := y443K_le hk
    refine ⟨⟨k, hH, rfl⟩, ?_⟩
    obtain ⟨h', hh', he⟩ := hxH
    refine ⟨f h', ⟨h', hh', rfl⟩, ?_⟩
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end CFSG.YGroups.Y443Edge
