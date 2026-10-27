module

public import CFSG.RankThree.GF2n.Stroth78.Sec2QaAbelian
public import CFSG.RankThree.GF2n.Stroth78.Sec2Eleven
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.GroupTheory.SuzukiTwoGroupsCoprime

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

private theorem h_acts_on_inf_H
    (S : Setting z E F) {a h : G}
    (hha : h * a * h⁻¹ = a) (hhH : h ∈ H z)
    (hconj : IsConj z a) (hza : z ∈ QaOf a) (hzaZ : z ∉ centerIn (QaOf a))
    (hhCa : h ∈ Subgroup.centralizer ({a} : Set G)) :
    h ∈ Subgroup.normalizer ((QaOf a ⊓ H z : Subgroup G) : Set G) ∧
      ∀ x ∈ QaOf a, h * x * h⁻¹ * x⁻¹ ∈ QaOf a ⊓ H z := by
  classical
  have hQaNorm : ∀ x ∈ QaOf a, h * x * h⁻¹ ∈ QaOf a :=
    fun x hx => fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hhCa hx
  have hK_iff : ∀ y : G, y ∈ QaOf a ⊓ H z ↔ h * y * h⁻¹ ∈ QaOf a ⊓ H z := by
    intro y
    constructor
    · rintro ⟨hyQ, hyH⟩
      refine ⟨hQaNorm y hyQ, ?_⟩
      exact (H z).mul_mem ((H z).mul_mem hhH hyH) ((H z).inv_mem hhH)
    · rintro ⟨hyQ, hyH⟩
      have hy' : y = h⁻¹ * (h * y * h⁻¹) * h := by group
      constructor
      · rw [hy']
        have := fStar_normal (M := Subgroup.centralizer ({a} : Set G))
          (Subgroup.inv_mem _ hhCa) hyQ
        simpa [QaOf, Qa] using this
      · rw [hy']
        exact (H z).mul_mem ((H z).mul_mem ((H z).inv_mem hhH) hyH) hhH
  have hKNorm : h ∈ Subgroup.normalizer ((QaOf a ⊓ H z : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff.mpr hK_iff
  have hidx : ((QaOf a ⊓ H z).subgroupOf (QaOf a)).index = 2 := by
    have hmul := Subgroup.index_mul_card ((QaOf a ⊓ H z).subgroupOf (QaOf a))
    have hcard_sub : Nat.card ((QaOf a ⊓ H z).subgroupOf (QaOf a)) =
        Nat.card (QaOf a ⊓ H z : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hcard_sub] at hmul
    have hcard := card_QaOf_eq_two_mul_card_inf_H_of_isConj S hconj hza hzaZ
    rw [hcard] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥(QaOf a ⊓ H z))) hmul
  refine ⟨hKNorm, ?_⟩
  intro x hx
  have hstep : (⟨h * x * h⁻¹, hQaNorm x hx⟩ : ↥(QaOf a)) * ⟨x, hx⟩⁻¹ ∈
      (QaOf a ⊓ H z).subgroupOf (QaOf a) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change h * x * h⁻¹ ∈ QaOf a ⊓ H z ↔ (x : G)⁻¹ ∈ QaOf a ⊓ H z
    rw [Subgroup.inv_mem_iff]
    exact (hK_iff x).symm
  have hmem : h * x * h⁻¹ * x⁻¹ ∈ QaOf a ⊓ H z := by
    have := Subgroup.mem_subgroupOf.mp hstep
    simpa using this
  simpa using hmem

private theorem commutator_mem_Q_of_mem_inf_H
    (S : Setting z E F) {a h u : G}
    (hhH : h ∈ H z) (huQa : u ∈ QaOf a) (huH : u ∈ H z)
    (hy : QuotientGroup.mk' ((Q z).subgroupOf (H z)) ⟨h, hhH⟩ ∈
      Subgroup.centralizer (Lbar S a : Set (Hbar z))) :
    ⁅u, h⁆ ∈ Q z := by
  classical
  have huLa : u ∈ La S a :=
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨huQa, huH⟩)
  have hmemL : QuotientGroup.mk' ((Q z).subgroupOf (H z)) ⟨u, huH⟩ ∈ Lbar S a := by
    rw [Lbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr huLa)
  have hcomm := Subgroup.mem_centralizer_iff.mp hy _ hmemL
  have hprod : (⟨u, huH⟩ * ⟨h, hhH⟩ * ⟨u, huH⟩⁻¹ * ⟨h, hhH⟩⁻¹ : ↥(H z)) ∈
      (Q z).subgroupOf (H z) := by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' ((Q z).subgroupOf (H z))
      (⟨u, huH⟩ * ⟨h, hhH⟩ * ⟨u, huH⟩⁻¹ * ⟨h, hhH⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm]
    group
  have hmemG : u * h * u⁻¹ * h⁻¹ ∈ Q z := by
    have := Subgroup.mem_subgroupOf.mp hprod
    simpa using this
  simpa [commutatorElement_def] using hmemG

private theorem commutator_inf_H_zpowers_le_Q
    (S : Setting z E F) {a h : G}
    (hhH : h ∈ H z)
    (hy : QuotientGroup.mk' ((Q z).subgroupOf (H z)) ⟨h, hhH⟩ ∈
      Subgroup.centralizer (Lbar S a : Set (Hbar z))) :
    ⁅QaOf a ⊓ H z, Subgroup.zpowers h⁆ ≤ Q z := by
  refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem ?_ ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact fStar_normal (M := H z) hhH hq
    · intro hq
      have hq' : q = h⁻¹ * (h * q * h⁻¹) * h := by group
      rw [hq']
      have := fStar_normal (M := H z) (Subgroup.inv_mem _ hhH) hq
      simpa [Q, QaOf, Qa] using this
  · intro u hu
    exact commutator_mem_Q_of_mem_inf_H S hhH (Subgroup.mem_inf.mp hu).1
      (Subgroup.mem_inf.mp hu).2 hy

private theorem commutator_mem_centerIn_of_centralizes_U
    {a h u : G} {Qa U : Subgroup G}
    (hhCa : h ∈ Subgroup.centralizer ({a} : Set G))
    (hQaNorm : ∀ x ∈ Qa, h * x * h⁻¹ ∈ Qa)
    (hQaNorm_inv : ∀ x ∈ Qa, h⁻¹ * x * h ∈ Qa)
    (hUQa : U ≤ Qa)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hU_comm : ∀ x ∈ Qa, h * x * h⁻¹ * x⁻¹ ∈ U)
    (hQa_deriv : ⁅Qa, Qa⁆ = Subgroup.zpowers a)
    (haz : Subgroup.zpowers a ≤ centerIn Qa)
    (huQa : u ∈ Qa) (huU : u ∈ U) :
    h * u * h⁻¹ * u⁻¹ ∈ centerIn Qa := by
  classical
  have hha_comm : h * a = a * h := by
    have := Subgroup.mem_centralizer_iff.mp hhCa a (Set.mem_singleton a)
    exact this.symm
  have hha_zpow : ∀ k : ℤ, h * a ^ k * h⁻¹ = a ^ k := by
    intro k
    have hcomm : a ^ k * h = h * a ^ k := (Commute.zpow_right hha_comm k).eq.symm
    calc h * a ^ k * h⁻¹ = (a ^ k * h) * h⁻¹ := by rw [hcomm]
      _ = a ^ k := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have key : ∀ x ∈ Qa, ⁅h * u * h⁻¹ * u⁻¹, h * x * h⁻¹⁆ = 1 := by
    intro x hx
    have huφ : h * u * h⁻¹ ∈ Qa := hQaNorm u huQa
    have hdxU : h * x * h⁻¹ * x⁻¹ ∈ U := hU_comm x hx
    have hdxQa : h * x * h⁻¹ * x⁻¹ ∈ Qa := hUQa hdxU
    have hux_mem : ⁅u, x⁆ ∈ Subgroup.zpowers a := by
      rw [← hQa_deriv]
      exact Subgroup.commutator_mem_commutator huQa hx
    have hux_cent : ⁅u, x⁆ ∈ centerIn Qa := haz hux_mem
    have hux_cent_Qa : ⁅u, x⁆ ∈ Qa := (Subgroup.mem_inf.mp hux_cent).1
    have hux_cent' : ⁅u, x⁆ ∈ Subgroup.centralizer (Qa : Set G) :=
      (Subgroup.mem_inf.mp hux_cent).2
    have hdx_comm : (h * x * h⁻¹ * x⁻¹) * ⁅u, x⁆ = ⁅u, x⁆ * (h * x * h⁻¹ * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hux_cent' _ hdxQa
    have hdx_conj : (h * x * h⁻¹ * x⁻¹) * ⁅u, x⁆ * (h * x * h⁻¹ * x⁻¹)⁻¹ = ⁅u, x⁆ := by
      rw [hdx_comm, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : ⁅u, h * x * h⁻¹⁆ = ⁅u, x⁆ := by
      have hφx_eq : h * x * h⁻¹ = (h * x * h⁻¹ * x⁻¹) * x := by group
      conv_lhs => rw [hφx_eq]
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hUab u huU _ hdxU)]
      rw [one_mul, hdx_conj]
    have h2 : ⁅h * u * h⁻¹, h * x * h⁻¹⁆ = ⁅u, x⁆ := by
      have hconj : h * ⁅u, x⁆ * h⁻¹ = ⁅h * u * h⁻¹, h * x * h⁻¹⁆ :=
        conjugate_commutatorElement u x h
      have hfix : h * ⁅u, x⁆ * h⁻¹ = ⁅u, x⁆ := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hux_mem
        rw [← hk, hha_zpow k]
      rw [← hconj]
      exact hfix
    have hcomm_u : u * ⁅u, x⁆ = ⁅u, x⁆ * u :=
      Subgroup.mem_centralizer_iff.mp hux_cent' u huQa
    have hinv_comm : ⁅u⁻¹, h * x * h⁻¹⁆ = ⁅u, x⁆⁻¹ := by
      rw [commutatorElement_inv_left]
      have hφx_u : ⁅h * x * h⁻¹, u⁆ = ⁅u, x⁆⁻¹ := by
        rw [show ⁅h * x * h⁻¹, u⁆ = ⁅u, h * x * h⁻¹⁆⁻¹ from
          (commutatorElement_inv (g₁ := u) (g₂ := h * x * h⁻¹)).symm]
        rw [h1]
      rw [hφx_u]
      calc u⁻¹ * ⁅u, x⁆⁻¹ * u = (u⁻¹ * ⁅u, x⁆ * u)⁻¹ := by group
        _ = ⁅u, x⁆⁻¹ := by
          have hux_conj : u⁻¹ * ⁅u, x⁆ * u = ⁅u, x⁆ := by
            calc u⁻¹ * ⁅u, x⁆ * u = u⁻¹ * (⁅u, x⁆ * u) := by group
              _ = u⁻¹ * (u * ⁅u, x⁆) := by rw [← hcomm_u]
              _ = ⁅u, x⁆ := by group
          rw [hux_conj]
    have hphi_comm : (h * u * h⁻¹) * ⁅u, x⁆ = ⁅u, x⁆ * (h * u * h⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hux_cent' _ huφ
    have hphi_conj : (h * u * h⁻¹) * ⁅u, x⁆⁻¹ * (h * u * h⁻¹)⁻¹ = ⁅u, x⁆⁻¹ := by
      calc (h * u * h⁻¹) * ⁅u, x⁆⁻¹ * (h * u * h⁻¹)⁻¹ =
            ((h * u * h⁻¹) * ⁅u, x⁆ * (h * u * h⁻¹)⁻¹)⁻¹ := by group
        _ = ⁅u, x⁆⁻¹ := by rw [hphi_comm]; group
    calc ⁅h * u * h⁻¹ * u⁻¹, h * x * h⁻¹⁆
        = (h * u * h⁻¹) * ⁅u⁻¹, h * x * h⁻¹⁆ * (h * u * h⁻¹)⁻¹ *
            ⁅h * u * h⁻¹, h * x * h⁻¹⁆ :=
          commutatorElement_mul_left_eq_conj_mul (h * u * h⁻¹) u⁻¹ (h * x * h⁻¹)
      _ = (h * u * h⁻¹) * ⁅u, x⁆⁻¹ * (h * u * h⁻¹)⁻¹ * ⁅u, x⁆ := by
          rw [hinv_comm, h2]
      _ = ⁅u, x⁆⁻¹ * ⁅u, x⁆ := by rw [hphi_conj]
      _ = 1 := by group
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Qa.mul_mem (hQaNorm u huQa) (Qa.inv_mem huQa)
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxmem : h⁻¹ * y * h ∈ Qa := hQaNorm_inv y hy
    have := key (h⁻¹ * y * h) hxmem
    have hy_eq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [hy_eq] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm

theorem eq_one_of_odd_prime_power_mem_centralizer_Lbar_of_centralizes_a
    (S : Setting z E F) {a h : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hhH : h ∈ H z) (hha : h * a * h⁻¹ = a)
    {l k : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hord : orderOf h = l ^ k)
    (hy : QuotientGroup.mk' ((Q z).subgroupOf (H z)) ⟨h, hhH⟩ ∈
      Subgroup.centralizer (Lbar S a : Set (Hbar z))) :
    QuotientGroup.mk' ((Q z).subgroupOf (H z)) ⟨h, hhH⟩ = 1 := by
  classical
  have hhCa : h ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hha_comm' : h * a = a * h := by
      have := congrArg (· * h) hha
      simpa [mul_assoc] using this
    exact hha_comm'.symm
  have hQaNorm : ∀ x ∈ QaOf a, h * x * h⁻¹ ∈ QaOf a :=
    fun x hx => fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hhCa hx
  have hQaNorm_mem : h ∈ Subgroup.normalizer (QaOf a : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hQaNorm q, fun hq => by
      have hq' : q = h⁻¹ * (h * q * h⁻¹) * h := by group
      rw [hq']
      have := fStar_normal (M := Subgroup.centralizer ({a} : Set G))
        (Subgroup.inv_mem _ hhCa) hq
      simpa [QaOf, Qa] using this⟩
  have hQaNorm_inv : ∀ x ∈ QaOf a, h⁻¹ * x * h ∈ QaOf a := by
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hQaNorm_mem (h⁻¹ * x * h)).mpr (by
      rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
      exact hx)
  obtain ⟨hKNorm, hcommK⟩ := h_acts_on_inf_H S hha hhH hconj hza
    (z_not_mem_centerIn_Qa S haQ hconj haZ hza) hhCa
  let K : Subgroup G := QaOf a ⊓ H z
  let R : Subgroup G := Subgroup.zpowers h
  let U : Subgroup G := ⁅QaOf a, R⁆
  have hcommK' : ∀ x ∈ QaOf a, h * x * h⁻¹ * x⁻¹ ∈ K := hcommK
  have hKNorm' : h ∈ Subgroup.normalizer (K : Set G) := hKNorm
  have hU_K : U ≤ K := by
    have hUK : ⁅QaOf a, R⁆ ≤ K :=
      CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hKNorm'
        (fun x hx => by
          have h1 : h * x * h⁻¹ * x⁻¹ ∈ K := hcommK' x hx
          have hxr : ⁅x, h⁆ = (h * x * h⁻¹ * x⁻¹)⁻¹ := by
            rw [commutatorElement_def]
            group
          rw [hxr]
          exact K.inv_mem h1)
    simpa [U] using hUK
  have hUQa : U ≤ QaOf a := hU_K.trans inf_le_left
  have hKR_Q : ⁅K, R⁆ ≤ Q z := by
    have := commutator_inf_H_zpowers_le_Q S hhH hy
    simpa [K, R] using this
  have hUmap : U.map (MulAut.conj h).toMonoidHom = U := by
    dsimp [U, R]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    have hQamap : Subgroup.map (↑(MulAut.conj h)) (QaOf a) = QaOf a := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hQaNorm x hx
      · intro x hx
        refine ⟨h⁻¹ * x * h, hQaNorm_inv x hx, ?_⟩
        change h * (h⁻¹ * x * h) * h⁻¹ = x
        group
    have hconjh : (↑(MulAut.conj h) : G →* G) h = h := by
      change h * h * h⁻¹ = h
      group
    simp only [hQamap, hconjh]
  have hUNorm : h ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hUmap
  have hUNorm_conj : ∀ x ∈ U, h * x * h⁻¹ ∈ U :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hUNorm x).mp hx
  have hUNorm_conj_inv : ∀ x ∈ U, h⁻¹ * x * h ∈ U := by
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hUNorm (h⁻¹ * x * h)).mpr (by
      rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
      exact hx)
  letI : Fact l.Prime := ⟨hl⟩
  have hRp : IsPGroup l R := by
    change IsPGroup l ↥(Subgroup.zpowers h)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
  have hRQa : R ≤ Subgroup.normalizer (QaOf a : Set G) :=
    Subgroup.zpowers_le.mpr hQaNorm_mem
  have hRQaNot : ¬ l ∣ Nat.card (QaOf a) := by
    obtain ⟨m, hm⟩ := (QaOf_isPGroup S hconj).exists_card_dvd_pow
    intro hdiv
    have h2 : l ∣ 2 ^ m := hdiv.trans hm
    have h2' : l ∣ 2 := hl.dvd_of_dvd_pow h2
    have hle : l ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    have h2le : 2 ≤ l := hl.two_le
    omega
  have hUeq : U = ⁅U, R⁆ := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq
      hl hRp hRQa hRQaNot
    simpa [U] using h.symm
  have hU_Q : U ≤ Q z := by
    have h1 : ⁅U, R⁆ ≤ Q z := (Subgroup.commutator_mono hU_K le_rfl).trans hKR_Q
    rw [hUeq]
    exact h1
  have hU_inf : U ≤ QaOf a ⊓ Q z := le_inf hUQa hU_Q
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x :=
    fun x hx y hy => commute_of_mem_QaOf_inf_Q S hconj haZ (hU_inf hx) (hU_inf hy)
  let dG : ↥U →* G :=
  { toFun := fun u => ⁅h, (u : G)⁆
    map_one' := by simp
    map_mul' := by
      intro u v
      change ⁅h, (u : G) * (v : G)⁆ = ⁅h, (u : G)⁆ * ⁅h, (v : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hvU : ⁅h, (v : G)⁆ ∈ U := by
        have hv' : ⁅(v : G), h⁆ ∈ U :=
          Subgroup.commutator_mem_commutator (hUQa v.2) (Subgroup.mem_zpowers h)
        rw [← commutatorElement_inv]
        exact U.inv_mem hv'
      have hcomm : (u : G) * ⁅h, (v : G)⁆ = ⁅h, (v : G)⁆ * (u : G) :=
        hUab (u : G) u.2 ⁅h, (v : G)⁆ hvU
      calc ⁅h, (u : G)⁆ * (u : G) * ⁅h, (v : G)⁆ * (u : G)⁻¹
          = ⁅h, (u : G)⁆ * ((u : G) * ⁅h, (v : G)⁆) * (u : G)⁻¹ := by group
        _ = ⁅h, (u : G)⁆ * (⁅h, (v : G)⁆ * (u : G)) * (u : G)⁻¹ := by rw [hcomm]
        _ = ⁅h, (u : G)⁆ * ⁅h, (v : G)⁆ := by group }
  let D : Subgroup G := dG.range
  have dG_mem_U : ∀ u : ↥U, dG u ∈ U := by
    intro u
    change ⁅h, (u : G)⁆ ∈ U
    have hv' : ⁅(u : G), h⁆ ∈ U :=
      Subgroup.commutator_mem_commutator (hUQa u.2) (Subgroup.mem_zpowers h)
    rw [← commutatorElement_inv]
    exact U.inv_mem hv'
  have hDmap_le : D.map (MulAut.conj h).toMonoidHom ≤ D := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
    change h * dG u * h⁻¹ ∈ D
    refine MonoidHom.mem_range.mpr ⟨⟨h * (u : G) * h⁻¹, hUNorm_conj (u : G) u.2⟩, ?_⟩
    change ⁅h, h * (u : G) * h⁻¹⁆ = h * ⁅h, (u : G)⁆ * h⁻¹
    simp only [commutatorElement_def]
    group
  have hDmap_ge : D ≤ D.map (MulAut.conj h).toMonoidHom := by
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨dG ⟨h⁻¹ * (u : G) * h, hUNorm_conj_inv (u : G) u.2⟩,
      ⟨⟨h⁻¹ * (u : G) * h, hUNorm_conj_inv (u : G) u.2⟩, rfl⟩, ?_⟩
    change h * dG ⟨h⁻¹ * (u : G) * h, _⟩ * h⁻¹ = dG u
    change h * ⁅h, h⁻¹ * (u : G) * h⁆ * h⁻¹ = ⁅h, (u : G)⁆
    simp only [commutatorElement_def]
    group
  have hDmap : D.map (MulAut.conj h).toMonoidHom = D := le_antisymm hDmap_le hDmap_ge
  have hDnorm : h ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hDmap
  have hcommD : ∀ u ∈ U, ⁅u, h⁆ ∈ D := by
    intro u hu
    have hmem : dG ⟨u, hu⟩ ∈ D := ⟨⟨u, hu⟩, rfl⟩
    have hinv : (dG ⟨u, hu⟩)⁻¹ ∈ D := D.inv_mem hmem
    have hd : (dG ⟨u, hu⟩)⁻¹ = ⁅u, h⁆ := by
      change (⁅h, u⁆)⁻¹ = ⁅u, h⁆
      rw [commutatorElement_inv]
    rwa [hd] at hinv
  have hUD : U ≤ D := by
    rw [hUeq]
    exact CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem hDnorm hcommD
  have hDU : D ≤ U := by
    rintro _ ⟨u, rfl⟩
    exact dG_mem_U u
  have hDUeq : D = U := le_antisymm hDU hUD
  have hU_comm : ∀ x ∈ QaOf a, h * x * h⁻¹ * x⁻¹ ∈ U := by
    intro x hx
    have hmem : ⁅x, h⁆ ∈ U :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers h)
    have hinv : ⁅h, x⁆ ∈ U := by
      rw [← commutatorElement_inv]
      exact U.inv_mem hmem
    simpa [commutatorElement_def] using hinv
  have hDcenter : D ≤ centerIn (QaOf a) := by
    rintro _ ⟨u, rfl⟩
    exact commutator_mem_centerIn_of_centralizes_U hhCa hQaNorm hQaNorm_inv hUQa hUab
      hU_comm (QaOf_deriv_eq_zpowers S hconj) (zpowers_mem_centerIn_QaOf S a) (hUQa u.2)
      u.2
  have hUcenter : U ≤ centerIn (QaOf a) := hDUeq ▸ hDcenter
  have hact : ∀ y ∈ QaOf a, h * y * h⁻¹ * y⁻¹ ∈ centerIn (QaOf a) := by
    intro y hy
    have hmem : ⁅y, h⁆ ∈ U :=
      Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers h)
    have hinv : ⁅h, y⁆ ∈ U := by
      rw [← commutatorElement_inv]
      exact U.inv_mem hmem
    exact hUcenter (by simpa [commutatorElement_def] using hinv)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hhQa : h ∈ QaOf a :=
    mem_QaOf_of_forall_commutator_mem_centerIn S hg hhCa hact
  have hodd : Odd (l ^ k) := (hl.odd_of_ne_two hl2).pow
  have hpow : (⟨h, hhQa⟩ : ↥(QaOf a)) ^ (l ^ k) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hord]
    exact pow_orderOf_eq_one h
  have h1 : (⟨h, hhQa⟩ : ↥(QaOf a)) = 1 :=
    CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd
      (QaOf_isPGroup S hconj) hodd hpow
  have hh1 : h = 1 := congrArg Subtype.val h1
  have hsub : (⟨h, hhH⟩ : ↥(H z)) = 1 := by
    ext
    exact hh1
  rw [hsub, map_one]

end CFSG.RankThree.GF2n.Stroth78
