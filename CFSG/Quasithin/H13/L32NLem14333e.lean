module

public import CFSG.Quasithin.H13.L32NLem14333d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

namespace L14333

theorem sl2_fix_of_pow_three : ∀ A : SL(2, RuType.F4), A ^ 3 = 1 → A ≠ 1 →
    ∀ v : Fin 2 → RuType.F4, (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = v → v = 0 := by
  decide

theorem sl2_exists_mulVec_eq : ∀ v w : Fin 2 → RuType.F4, v ≠ 0 → w ≠ 0 →
    ∃ A : SL(2, RuType.F4), (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = w := by
  decide

theorem sl2_card_fix_of_sq : ∀ A : SL(2, RuType.F4), A ^ 2 = 1 → A ≠ 1 →
    (Finset.univ.filter fun v : Fin 2 → RuType.F4 =>
      (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = v).card = 4 := by
  decide

theorem sigma_right_eq_one {y : RuType.SigmaL2F4} {n : ℕ} (hn : Odd n) (hy : y ^ n = 1) :
    y.right = 1 := by
  have h := congrArg SemidirectProduct.rightHom hy
  rw [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  obtain ⟨k, rfl⟩ := hn
  have hsq : ∀ m : Multiplicative (ZMod 2), m ^ 2 = 1 := by decide
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at h
  exact h

theorem sigmaAct_of_right_eq_one {y : RuType.SigmaL2F4} (hy : y.right = 1)
    (v : Fin 2 → RuType.F4) :
    RuType.sigmaAct y v = (y.left : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v := by
  have h : Multiplicative.toAdd y.right = 0 := by rw [hy]; rfl
  simp [RuType.sigmaAct, RuType.frobVec, h]

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem x_ne_one : x ≠ 1 := by
  intro h
  have := c.x_a
  rw [h] at this
  simp only [one_mul, inv_one, mul_one] at this
  exact c.b_nmem (this ▸ c.ctx.aV₂)

theorem eq_one_of_imgHom {y : G} (hy : y ∈ l32nH T V) {n : ℕ} (hn : Odd n) (hyn : y ^ n = 1)
    (h1 : imgHom D ⟨y, hy⟩ = 1) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyQ : y ∈ pCoreOf 2 (l32nH T V) := by
    rw [c.q_eq]
    have := congrArg Subtype.val h1
    rw [imgHom_apply] at this
    exact (rho_eq_one_iff_mem hy _).mp this
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (l32nH T V)) ⟨y, hyQ⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)
  have h1' := orderOf_dvd_of_pow_eq_one hk'
  have h2' := orderOf_dvd_of_pow_eq_one hyn
  have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1' h2'
  exact orderOf_eq_one_iff.mp this

theorem eq_zero_of_fix_x {w : D.V}
    (hw : D.ρ ⟨x, l32nH_le_normalizer_fsuU T V c.x_mem_H⟩ w = w) : w = 0 := by
  obtain ⟨φ, ψ, hψ⟩ := c.ii.natural
  set γ := imgHom D ⟨x, c.x_mem_H⟩ with hγ
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨x, c.x_mem_H⟩ : ↥(l32nH T V)) ^ 3 = 1 := Subtype.ext (by simpa using c.x_cube)
    rw [this, map_one]
  have hγ1 : γ ≠ 1 := fun h => c.x_ne_one (c.eq_one_of_imgHom c.x_mem_H (by decide) c.x_cube h)
  have hr : (φ γ).right = 1 := sigma_right_eq_one (by decide : Odd 3) (by rw [← map_pow, hγ3,
    map_one])
  have hA3 : (φ γ).left ^ 3 = 1 := by
    have h := congrArg SemidirectProduct.left (show (φ γ) ^ 3 = 1 by rw [← map_pow, hγ3, map_one])
    have e : ∀ y : RuType.SigmaL2F4, y.right = 1 → (y ^ 3).left = y.left ^ 3 := by
      intro y hy
      have hy' : y = SemidirectProduct.inl y.left := by
        ext
        · rfl
        · rw [hy]; rfl
      rw [hy', ← map_pow]
      rfl
    rw [e _ hr] at h
    exact h
  have hA1 : (φ γ).left ≠ 1 := by
    intro h
    apply hγ1
    apply φ.injective
    rw [map_one]
    exact SemidirectProduct.ext h hr
  have h1 := hψ γ w
  rw [hγ, imgHom_apply] at h1
  rw [hw, sigmaAct_of_right_eq_one hr] at h1
  have h2 := sl2_fix_of_pow_three _ hA3 hA1 (ψ w) h1.symm
  exact ψ.injective (by rw [h2, map_zero])

theorem mem_zU_of_comm_U {u : G} (hu : u ∈ fsuU T V) (hux : x * u * x⁻¹ = u) :
    u ∈ centerOf (fsuU T V) := by
  have h := D.ρ_π ⟨x, l32nH_le_normalizer_fsuU T V c.x_mem_H⟩ u hu
  simp only at h
  rw [hux] at h
  exact (L128A.HatU.π_eq_zero_iff D hu).mp (c.eq_zero_of_fix_x h)

theorem zpowers_x_le_normalizer_U :
    Subgroup.zpowers x ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  Subgroup.zpowers_le.mpr (l32nH_le_normalizer_fsuU T V c.x_mem_H)

theorem exists_mul_U {u : G} (hu : u ∈ fsuU T V) :
    ∃ q ∈ ⁅fsuU T V, Subgroup.zpowers x⁆, ∃ e ∈ centerOf (fsuU T V), q * e = u := by
  have hcop : Nat.Coprime 3 (Nat.card ↥(fsuU T V)) := by rw [c.card_U]; norm_num
  obtain ⟨q, hq, r, hr, hrx, rfl⟩ := c.exists_mul_of_coprime c.zpowers_x_le_normalizer_U hcop hu
  exact ⟨q, hq, r, c.mem_zU_of_comm_U hr hrx, rfl⟩

theorem U_le_L (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) : fsuU T V ≤ L := by
  have hcomm : ⁅fsuU T V, Subgroup.zpowers x⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    have hyL : y ∈ L := (Subgroup.zpowers_le.mpr c.x_mem) hy
    have h1 : u * y * u⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (c.T_le_normL (c.U_le_T hu)) y).mp hyL
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hyL)
  have hZL : centerOf (fsuU T V) ≤ L := by
    have h := (c.sup_zU_le_P hyp).trans (pCoreOf_le 2 L)
    exact le_sup_right.trans h
  intro u hu
  obtain ⟨q, hq, e, he, rfl⟩ := c.exists_mul_U hu
  exact L.mul_mem (hcomm hq) (hZL he)

omit c in
theorem coprime_three_Q : Nat.Coprime 3 (Nat.card ↥(pCoreOf 2 (l32nH T V))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (l32nH T V)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem exists_mul_Q {q : G} (hq : q ∈ pCoreOf 2 (l32nH T V)) :
    ∃ u ∈ fsuU T V, ∃ r ∈ pCoreOf 2 (l32nH T V), x * r * x⁻¹ = r ∧ u * r = q := by
  have hxQ : Subgroup.zpowers x ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 _ c.x_mem_H)
  obtain ⟨u, hu, r, hr, hrx, rfl⟩ := c.exists_mul_of_coprime hxQ coprime_three_Q hq
  have hle : ⁅pCoreOf 2 (l32nH T V), Subgroup.zpowers x⁆ ≤ fsuU T V := by
    refine le_trans ?_ c.KQ
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr c.x_mem_K) le_rfl
  exact ⟨u, hle hu, r, hr, hrx, rfl⟩

theorem comm_Q_U_mem {q u : G} (hq : q ∈ pCoreOf 2 (l32nH T V)) (hu : u ∈ fsuU T V) :
    q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  rw [← c.ctx.q_tilde] at hq
  exact hq.2.2 u hu

theorem comm_of_mem_commutator {r : G} (hr : r ∈ pCoreOf 2 (l32nH T V)) (hrx : x * r * x⁻¹ = r)
    {w : G} (hw : w ∈ ⁅fsuU T V, Subgroup.zpowers x⁆) : r * w = w * r := by
  have hle : ⁅fsuU T V, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyH : y ∈ l32nH T V := (Subgroup.zpowers_le.mpr c.x_mem_H) hy
    have hry : r * y = y * r := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hrx' : Commute x r := by
        show x * r = r * x
        calc x * r = x * r * x⁻¹ * x := by group
          _ = r * x := by rw [hrx]
      exact ((hrx'.zpow_left k).eq).symm
    set e := r * u * r⁻¹ * u⁻¹ with he
    have heV : e ∈ fsuV1 T V := c.comm_Q_U_mem hr hu
    have huH : u ∈ l32nH T V := c.ctx.U_le hu
    have hcomm_e : ∀ h ∈ l32nH T V, e * h = h * e := fun h hh => by
      have := c.ctx.H_V1 h hh e heV
      calc e * h = (h * e * h⁻¹) * h := by rw [this]
        _ = h * e := by group
    have huyH : u * y * u⁻¹ ∈ l32nH T V := mul_mem (mul_mem huH hyH) (inv_mem huH)
    have hru : r * u * r⁻¹ = e * u := by rw [he]; group
    have hryr : r * y * r⁻¹ = y := by rw [hry]; group
    have key : r * ⁅u, y⁆ * r⁻¹ = ⁅u, y⁆ := by
      have e1 : r * ⁅u, y⁆ * r⁻¹ = ⁅r * u * r⁻¹, r * y * r⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [e1, hryr, hru, commutatorElement_def, commutatorElement_def]
      calc e * u * y * (e * u)⁻¹ * y⁻¹ = e * (u * y * u⁻¹) * e⁻¹ * y⁻¹ := by group
        _ = (u * y * u⁻¹) * e * e⁻¹ * y⁻¹ := by rw [hcomm_e _ huyH]
        _ = u * y * u⁻¹ * y⁻¹ := by group
    calc ⁅u, y⁆ * r = (r * ⁅u, y⁆ * r⁻¹) * r := by rw [key]
      _ = r * ⁅u, y⁆ := by group
  have := hle hw
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem comm_U_of_comm {r : G} (hr : r ∈ pCoreOf 2 (l32nH T V)) (hrx : x * r * x⁻¹ = r)
    (hrZ : ∀ e ∈ centerOf (fsuU T V), r * e = e * r) {u : G} (hu : u ∈ fsuU T V) :
    r * u = u * r := by
  obtain ⟨q, hq, e, he, rfl⟩ := c.exists_mul_U hu
  have h1 := c.comm_of_mem_commutator hr hrx hq
  have h2 := hrZ e he
  calc r * (q * e) = (r * q) * e := by group
    _ = (q * r) * e := by rw [h1]
    _ = q * (r * e) := by group
    _ = q * (e * r) := by rw [h2]
    _ = q * e * r := by group

end Ctx

end L14333

end CFSG.Quasithin.H13
