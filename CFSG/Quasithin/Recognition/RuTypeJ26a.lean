module

public import CFSG.Quasithin.Recognition.RuTypeJ24

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

namespace Sigma

@[expose] def g0 : SigmaL2F4 := ⟨⟨!![0, 1; 1, 0], by decide⟩, Multiplicative.ofAdd 1⟩

theorem conj_g0 : ∀ g : SigmaL2F4, (g ^ 2 = 1 ∧ g.right ≠ 1) →
    ∃ x : SigmaL2F4, x * g * x⁻¹ = g0 := by
  decide +kernel

theorem fix_outside : ∀ g : SigmaL2F4, (g ^ 2 = 1 ∧ g.right ≠ 1) →
    ∀ v : Fin 2 → F4, sigmaAct g v = v → ∃ w, v = w + sigmaAct g w := by
  decide +kernel

theorem card_fix_outside : ∀ g : SigmaL2F4, (g ^ 2 = 1 ∧ g.right ≠ 1) →
    Fintype.card {v : Fin 2 → F4 // sigmaAct g v = v} = 4 := by
  decide +kernel

theorem card_outside : Fintype.card {g : SigmaL2F4 // g ^ 2 = 1 ∧ g.right ≠ 1} = 10 := by
  decide +kernel

theorem exists_outside_comm : ∀ t : SigmaL2F4, (t ^ 3 = 1 ∧ t ≠ 1) →
    ∃ j : SigmaL2F4, (j ^ 2 = 1 ∧ j.right ≠ 1) ∧ j * t = t * j := by
  decide +kernel

theorem eq_of_ne_one : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide

end Sigma

namespace SL3

theorem n0_b0mat : stAct n0 !![1, 0, 0; 0, 0, 1; 0, 1, 1] = !![1, 0, 0; 0, 1, 1; 0, 1, 0] := by
  decide +kernel

theorem not_isRow0_b0 :
    ¬ IsRow0 (!![1, 0, 0; 0, 0, 1; 0, 1, 1] + stAct n0 !![1, 0, 0; 0, 0, 1; 0, 1, 1]) := by
  decide +kernel

end SL3

theorem inv_eq_self_of_sq {i : G} (hi2 : i ^ 2 = 1) : i⁻¹ = i :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hi2)

theorem sq_mul_eq_one_iff {j u : G} (hj : j ^ 2 = 1) (hu : u ^ 2 = 1) :
    (j * u) ^ 2 = 1 ↔ u * j = j * u := by
  have hj' := inv_eq_self_of_sq hj
  have hu' := inv_eq_self_of_sq hu
  rw [pow_two] at hj hu ⊢
  constructor
  · intro h
    calc u * j = u⁻¹ * j⁻¹ := by rw [hu', hj']
      _ = (j * u)⁻¹ := by group
      _ = j * u := inv_eq_of_mul_eq_one_right h
  · intro h
    calc j * u * (j * u) = j * (u * j) * u := by group
      _ = j * (j * u) * u := by rw [h]
      _ = (j * j) * (u * u) := by group
      _ = 1 := by rw [hj, hu, one_mul]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

@[expose] noncomputable def nel : M.L := (M.θ_surj SL3.n0).choose

omit [Finite G] in
theorem θ_nel : M.θ M.nel = SL3.n0 := (M.θ_surj SL3.n0).choose_spec

theorem nel_mem_H : (M.nel : G) ∈ ruH M.T := by
  have : (M.nel : G) ∈ M.LT1 := mem_pullL.mpr ⟨M.nel.2, by rw [M.θ_nel]; exact SL3.n0_mem_Stab0⟩
  rw [← M.L_inf_H] at this
  exact this.2

theorem nel_moves {t : G} (ht : t ∈ ruS M.L)
    (hχ : Multiplicative.toAdd (M.χ ⟨t, ht⟩) = !![1, 0, 0; 0, 0, 1; 0, 1, 1]) :
    t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹) ∉ ruU M.L M.T := by
  intro hU
  have hnt : (M.nel : G) * t * (M.nel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.nel.2) t).mp ht
  have hmem : t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹) ∈ ruS M.L := mul_mem (inv_mem ht) hnt
  have h := (M.mem_U_iff hmem).mp hU
  rw [show (⟨t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹), hmem⟩ : ruS M.L) =
    (⟨t, ht⟩ : ruS M.L)⁻¹ * ⟨_, hnt⟩ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv,
    M.χ_conj M.nel ⟨t, ht⟩, M.θ_nel, hχ] at h
  exact SL3.not_isRow0_b0 h

theorem nel_not_mem_K : (M.nel : G) ∉ M.K := by
  intro hK
  obtain ⟨t, ht, hb, hχ⟩ := M.exists_t1
  have htHC : t ∈ M.HC := M.HB_le_HC (M.mem_HB.mpr ⟨ht, hb⟩)
  have h := M.comm_K_HC hK t htHC
  apply M.nel_moves ht hχ
  have e : t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹) =
      t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹ * t⁻¹) * t := by group
  rw [e]
  have := M.conj_mem_U (inv_mem (Subgroup.mem_inf.mp htHC).1) h
  simpa using this

theorem φ_nel_right : (M.φ ⟨M.nel, M.nel_mem_H⟩).right ≠ 1 := fun h =>
  M.nel_not_mem_K (M.mem_K_iff.mpr ⟨M.nel_mem_H, h⟩)

theorem mul_nel_inv_mem_K {h : G} (hh : h ∈ ruH M.T) (hK : h ∉ M.K) :
    h * (M.nel : G)⁻¹ ∈ M.K := by
  have hr : (M.φ ⟨h, hh⟩).right ≠ 1 := fun h1 => hK (M.mem_K_iff.mpr ⟨hh, h1⟩)
  have hmem : h * (M.nel : G)⁻¹ ∈ ruH M.T := mul_mem hh (inv_mem M.nel_mem_H)
  refine M.mem_K_iff.mpr ⟨hmem, ?_⟩
  have e : M.φ ⟨h * (M.nel : G)⁻¹, hmem⟩ = M.φ ⟨h, hh⟩ * (M.φ ⟨M.nel, M.nel_mem_H⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    Sigma.eq_of_ne_one _ _ hr M.φ_nel_right, mul_inv_cancel]

theorem conj_HC_of_mem_K {k x : G} (hk : k ∈ M.K) (hx : x ∈ M.HC) :
    x⁻¹ * (k * x * k⁻¹) ∈ ruU M.L M.T := by
  have h := M.comm_K_HC hk x hx
  have e : x⁻¹ * (k * x * k⁻¹) = x⁻¹ * (k * x * k⁻¹ * x⁻¹) * x := by group
  rw [e]
  have := M.conj_mem_U (inv_mem (Subgroup.mem_inf.mp hx).1) h
  simpa using this

theorem conj_HC_of_not_mem_K {h x : G} (hh : h ∈ ruH M.T) (hK : h ∉ M.K) (hx : x ∈ M.HC) :
    (h * x * h⁻¹)⁻¹ * ((M.nel : G) * x * (M.nel : G)⁻¹) ∈ ruU M.L M.T := by
  set k := h * (M.nel : G)⁻¹
  have hk := M.mul_nel_inv_mem_K hh hK
  have hy : (M.nel : G) * x * (M.nel : G)⁻¹ ∈ M.HC := M.conj_mem_HC M.nel_mem_H hx
  have h1 := M.conj_HC_of_mem_K hk hy
  have e : h * x * h⁻¹ = k * ((M.nel : G) * x * (M.nel : G)⁻¹) * k⁻¹ := by
    simp only [k]
    group
  set y := (M.nel : G) * x * (M.nel : G)⁻¹
  rw [e, show (k * y * k⁻¹)⁻¹ * y = (y⁻¹ * (k * y * k⁻¹))⁻¹ by group]
  exact inv_mem h1

theorem nel_moves' {t : G} (ht : t ∈ ruS M.L)
    (hχ : Multiplicative.toAdd (M.χ ⟨t, ht⟩) = !![1, 0, 0; 0, 1, 1; 0, 1, 0]) :
    t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹) ∉ ruU M.L M.T := by
  intro hU
  have hnt : (M.nel : G) * t * (M.nel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.nel.2) t).mp ht
  have hmem : t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹) ∈ ruS M.L := mul_mem (inv_mem ht) hnt
  have h := (M.mem_U_iff hmem).mp hU
  rw [show (⟨t⁻¹ * ((M.nel : G) * t * (M.nel : G)⁻¹), hmem⟩ : ruS M.L) =
    (⟨t, ht⟩ : ruS M.L)⁻¹ * ⟨_, hnt⟩ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv,
    M.χ_conj M.nel ⟨t, ht⟩, M.θ_nel, hχ, SL3.n0_swap] at h
  have hD : (!![1, 0, 0; 0, 1, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      !![1, 0, 0; 0, 0, 1; 0, 1, 1] =
      !![1, 0, 0; 0, 0, 1; 0, 1, 1] + stAct SL3.n0 !![1, 0, 0; 0, 0, 1; 0, 1, 1] := by
    decide +kernel
  rw [hD] at h
  exact SL3.not_isRow0_b0 h

abbrev UQ : Subgroup (ruQ M.T) := (ruU M.L M.T).subgroupOf (ruQ M.T)

instance UQ_normal : (M.UQ).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact M.conj_mem_U (pCoreOf_le 2 _ g.2) hx⟩

abbrev Qbar : Type _ := ↥(ruQ M.T) ⧸ M.UQ

omit [Finite G] in
theorem mk_eq_mk_iff {q q' : ruQ M.T} :
    (q : M.Qbar) = (q' : M.Qbar) ↔ (q : G)⁻¹ * q' ∈ ruU M.L M.T := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem card_Qbar : Nat.card M.Qbar = 64 := by
  show Nat.card (↥(ruQ M.T) ⧸ M.UQ) = 64
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup M.UQ
  rw [M.toRuData.card_Q, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
  norm_num at h
  omega

omit [Finite G] in
theorem Qbar_comm (a b : M.Qbar) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  induction b using QuotientGroup.induction_on with
  | H q' =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, M.mk_eq_mk_iff]
  have h := (M.two.QU_elem _ (inv_mem q'.2) _ (inv_mem q.2)).1
  have e : ((q : G) * q')⁻¹ * ((q' : G) * q) =
      (q' : G)⁻¹ * (q : G)⁻¹ * ((q' : G)⁻¹)⁻¹ * ((q : G)⁻¹)⁻¹ := by group
  simp only [Subgroup.coe_mul]
  rw [e]
  exact h

omit [Finite G] in
theorem Qbar_sq (a : M.Qbar) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have := (M.two.QU_elem _ q.2 _ q.2).2
  simpa [pow_two] using this

@[expose] def conjQ (h : ruH M.T) : ruQ M.T →* ruQ M.T where
  toFun q := ⟨h * q * (h : G)⁻¹, M.conj_mem_Q h.2 q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q q' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def actQ (h : ruH M.T) : M.Qbar →* M.Qbar :=
  QuotientGroup.map M.UQ M.UQ (M.conjQ h) (fun u hu => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact M.conj_mem_U h.2 (Subgroup.mem_subgroupOf.mp hu))

omit [Finite G] in
theorem actQ_mk (h : ruH M.T) (q : ruQ M.T) :
    M.actQ h (q : M.Qbar) = ((M.conjQ h q : ruQ M.T) : M.Qbar) := rfl

@[expose] noncomputable def ψQbar : M.Qbar →* Multiplicative (Fin 2 → F4) :=
  QuotientGroup.lift M.UQ M.ψQ (fun u hu => by
    rw [M.ψQ_ker, Subgroup.mem_subgroupOf]
    exact M.U_le_HC (Subgroup.mem_subgroupOf.mp hu))

theorem ψQbar_mk (q : ruQ M.T) : M.ψQbar (q : M.Qbar) = M.ψQ q := rfl

theorem ψQbar_actQ (h : ruH M.T) (a : M.Qbar) :
    Multiplicative.toAdd (M.ψQbar (M.actQ h a)) =
      sigmaAct (M.φ h) (Multiplicative.toAdd (M.ψQbar a)) := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [M.actQ_mk, M.ψQbar_mk, M.ψQbar_mk]
  exact M.ψQ_conj h q

omit [Finite G] in
theorem actQ_actQ {i : G} (hiH : i ∈ ruH M.T) (hi2 : i ^ 2 = 1) (a : M.Qbar) :
    M.actQ ⟨i, hiH⟩ (M.actQ ⟨i, hiH⟩ a) = a := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [M.actQ_mk, M.actQ_mk]
  congr 1
  apply Subtype.ext
  show i * (i * q * i⁻¹) * i⁻¹ = q
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hii
  rw [hi']
  calc i * (i * q * i) * i = (i * i) * q * (i * i) := by group
    _ = q := by rw [hii, one_mul, mul_one]

@[expose] noncomputable def normQ {i : G} (hiH : i ∈ ruH M.T) : M.Qbar →* M.Qbar where
  toFun a := a * M.actQ ⟨i, hiH⟩ a
  map_one' := by rw [map_one, mul_one]
  map_mul' a b := by
    rw [map_mul]
    calc a * b * (M.actQ ⟨i, hiH⟩ a * M.actQ ⟨i, hiH⟩ b)
        = a * (b * M.actQ ⟨i, hiH⟩ a) * M.actQ ⟨i, hiH⟩ b := by group
      _ = a * (M.actQ ⟨i, hiH⟩ a * b) * M.actQ ⟨i, hiH⟩ b := by rw [M.Qbar_comm b]
      _ = a * M.actQ ⟨i, hiH⟩ a * (b * M.actQ ⟨i, hiH⟩ b) := by group

noncomputable abbrev fixQ {i : G} (hiH : i ∈ ruH M.T) : Subgroup M.Qbar := (M.normQ hiH).ker

omit [Finite G] in
theorem mem_fixQ {i : G} (hiH : i ∈ ruH M.T) {a : M.Qbar} :
    a ∈ M.fixQ hiH ↔ M.actQ ⟨i, hiH⟩ a = a := by
  rw [MonoidHom.mem_ker]
  show a * M.actQ ⟨i, hiH⟩ a = 1 ↔ _
  constructor
  · intro h
    calc M.actQ ⟨i, hiH⟩ a = a * a * M.actQ ⟨i, hiH⟩ a := by rw [M.Qbar_sq, one_mul]
      _ = a * (a * M.actQ ⟨i, hiH⟩ a) := by group
      _ = a := by rw [h, mul_one]
  · intro h
    rw [h, M.Qbar_sq]

omit [Finite G] in
theorem range_normQ_le {i : G} (hiH : i ∈ ruH M.T) (hi2 : i ^ 2 = 1) :
    (M.normQ hiH).range ≤ M.fixQ hiH := by
  rintro _ ⟨a, rfl⟩
  rw [M.mem_fixQ]
  show M.actQ ⟨i, hiH⟩ (a * M.actQ ⟨i, hiH⟩ a) = a * M.actQ ⟨i, hiH⟩ a
  rw [map_mul, M.actQ_actQ hiH hi2, M.Qbar_comm]

theorem card_fixQ_mul {i : G} (hiH : i ∈ ruH M.T) :
    Nat.card (M.fixQ hiH) * Nat.card (M.normQ hiH).range = 64 := by
  rw [← M.card_Qbar]
  exact Subgroup.card_ker_mul_card_range _

theorem card_fixQ_ge {i : G} (hiH : i ∈ ruH M.T) (hi2 : i ^ 2 = 1) :
    8 ≤ Nat.card (M.fixQ hiH) := by
  have h := M.card_fixQ_mul hiH
  have hle : Nat.card (M.normQ hiH).range ≤ Nat.card (M.fixQ hiH) :=
    Subgroup.card_le_of_le (M.range_normQ_le hiH hi2)
  by_contra hlt
  push Not at hlt
  have : Nat.card (M.fixQ hiH) * Nat.card (M.normQ hiH).range ≤ 7 * 7 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem U_comm {u v : G} (hu : u ∈ ruU M.L M.T) (hv : v ∈ ruU M.L M.T) : u * v = v * u :=
  congrArg Subtype.val (M.U_elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem eq_of_mem_HC_fixed {h t3 : G} (hh : h ∈ ruH M.T) (hK : h ∉ M.K) (ht3 : t3 ∈ ruS M.L)
    (hb3 : (M.bel : G) * t3 = t3 * M.bel)
    (hχ3 : Multiplicative.toAdd (M.χ ⟨t3, ht3⟩) = !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    {q : G} (hq : q ∈ M.HC) (hfix : q⁻¹ * (h * q * h⁻¹) ∈ ruU M.L M.T) :
    q ∈ ruU M.L M.T ∨ t3⁻¹ * q ∈ ruU M.L M.T := by
  obtain ⟨x, hx, u, hu, rfl⟩ := M.exists_HB_U hq
  obtain ⟨hxS, hxb⟩ := M.mem_HB.mp hx
  have hxHC := M.HB_le_HC hx
  have hfx : x⁻¹ * (h * x * h⁻¹) ∈ ruU M.L M.T := by
    have e : x⁻¹ * (h * x * h⁻¹) = u * ((x * u)⁻¹ * (h * (x * u) * h⁻¹)) *
        (h * u⁻¹ * h⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem hu hfix) (M.conj_mem_U hh (inv_mem hu))
  have hnx : x⁻¹ * ((M.nel : G) * x * (M.nel : G)⁻¹) ∈ ruU M.L M.T := by
    have e : x⁻¹ * ((M.nel : G) * x * (M.nel : G)⁻¹) =
        x⁻¹ * (h * x * h⁻¹) * ((h * x * h⁻¹)⁻¹ * ((M.nel : G) * x * (M.nel : G)⁻¹)) := by group
    rw [e]
    exact mul_mem hfx (M.conj_HC_of_not_mem_K hh hK hxHC)
  rcases M.isFixB0_χ hxS hxb with h0 | h0 | h0 | h0
  · left
    have hk : (⟨x, hxS⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact mul_mem (M.V_le_U hk) hu
  · right
    have hk : (⟨t3, ht3⟩ : ruS M.L)⁻¹ * ⟨x, hxS⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [M.toAdd_χ_mul, M.toAdd_χ_inv, hχ3, h0, toAdd_one]
      decide
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    have hw : t3⁻¹ * x ∈ ruV M.L := hk
    have hwb : (M.bel : G) * (t3⁻¹ * x) = (t3⁻¹ * x) * M.bel := by
      have e2 : (M.bel : G) * t3⁻¹ = t3⁻¹ * M.bel := (Commute.inv_right hb3).eq
      rw [← mul_assoc, e2, mul_assoc, hxb, mul_assoc]
    have hwU : t3⁻¹ * x ∈ ruU M.L M.T := by
      rcases M.eq_of_mem_V_comm_bel hw hwb with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact M.V_le_U M.z_mem_V
    rw [← mul_assoc]
    exact mul_mem hwU hu
  · exact absurd hnx (M.nel_moves hxS h0)
  · exact absurd hnx (M.nel_moves' hxS h0)

omit [Finite G] in
theorem φ_inv_props {j : G} (hjH : j ∈ ruH M.T) (hK : j ∉ M.K) (hj2 : j ^ 2 = 1) :
    M.φ ⟨j, hjH⟩ ^ 2 = 1 ∧ (M.φ ⟨j, hjH⟩).right ≠ 1 := by
  refine ⟨?_, fun h1 => hK (M.mem_K_iff.mpr ⟨hjH, h1⟩)⟩
  rw [← map_pow, show (⟨j, hjH⟩ : ruH M.T) ^ 2 = 1 from Subtype.ext hj2, map_one]

theorem card_fixQ {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1) :
    Nat.card (M.fixQ hiH) = 8 := by
  classical
  refine le_antisymm ?_ (M.card_fixQ_ge hiH hi2)
  obtain ⟨t3, ht3, hb3, hχ3⟩ := M.exists_centralizer_S_B (A := !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    (Or.inr (Or.inl rfl))
  have ht3HC : t3 ∈ M.HC := M.HB_le_HC (M.mem_HB.mpr ⟨ht3, hb3⟩)
  have ht3Q : t3 ∈ ruQ M.T := M.HC_le_Q ht3HC
  let g : M.fixQ hiH →* Multiplicative (Fin 2 → F4) := M.ψQbar.comp (M.fixQ hiH).subtype
  have h := Subgroup.card_ker_mul_card_range g
  have hrange : Nat.card g.range ≤ 4 := by
    have h4 : Nat.card {v : Fin 2 → F4 // sigmaAct (M.φ ⟨i, hiH⟩) v = v} = 4 := by
      rw [Nat.card_eq_fintype_card]
      exact Sigma.card_fix_outside _ (M.φ_inv_props hiH hK hi2)
    rw [← h4]
    refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩) ?_
    · obtain ⟨a, ha⟩ := y.2
      rw [← ha]
      have hfa := (M.mem_fixQ hiH).mp a.2
      have e := M.ψQbar_actQ ⟨i, hiH⟩ a.1
      rw [hfa] at e
      exact e.symm
    · intro y y' hy
      have hy' := Subtype.ext_iff.mp hy
      exact Subtype.ext (Multiplicative.toAdd.injective hy')
  have hker : Nat.card g.ker ≤ 2 := by
    let f : g.ker → Fin 2 := fun a => if (a : M.fixQ hiH).1 = 1 then 0 else 1
    refine (Nat.card_le_card_of_injective f ?_).trans (by simp)
    have hmem : ∀ a : g.ker, (a : M.fixQ hiH).1 = 1 ∨
        (a : M.fixQ hiH).1 = ((⟨t3, ht3Q⟩ : ruQ M.T) : M.Qbar) := by
      intro a
      obtain ⟨⟨a, ha⟩, hag⟩ := a
      induction a using QuotientGroup.induction_on with
      | H q =>
      have hq1 : M.ψQ q = 1 := hag
      have hqHC : (q : G) ∈ M.HC := by
        have : q ∈ M.ψQ.ker := hq1
        rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at this
        exact this
      have hfix := (M.mem_fixQ hiH).mp ha
      rw [M.actQ_mk, M.mk_eq_mk_iff] at hfix
      have hfix' : (q : G)⁻¹ * (i * q * i⁻¹) ∈ ruU M.L M.T := by
        have := inv_mem hfix
        rw [mul_inv_rev, inv_inv] at this
        exact this
      rcases M.eq_of_mem_HC_fixed hiH hK ht3 hb3 hχ3 hqHC hfix' with h1 | h1
      · left
        show (q : M.Qbar) = 1
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h1
      · right
        show (q : M.Qbar) = ((⟨t3, ht3Q⟩ : ruQ M.T) : M.Qbar)
        rw [M.mk_eq_mk_iff]
        have : (q : G)⁻¹ * t3 = (t3⁻¹ * q)⁻¹ := by group
        rw [this]
        exact inv_mem h1
    intro a a' haa
    apply Subtype.ext
    apply Subtype.ext
    simp only [f] at haa
    rcases hmem a with h1 | h1 <;> rcases hmem a' with h2 | h2
    · rw [h1, h2]
    · rw [ite_eq_left h1] at haa
      by_cases h3 : (a' : M.fixQ hiH).1 = 1
      · rw [h1, h3]
      · rw [ite_eq_right h3] at haa
        exact absurd haa (by decide)
    · by_cases h3 : (a : M.fixQ hiH).1 = 1
      · rw [h3, h2]
      · rw [ite_eq_right h3, ite_eq_left h2] at haa
        exact absurd haa (by decide)
    · rw [h1, h2]
  calc Nat.card (M.fixQ hiH) = Nat.card g.ker * Nat.card g.range := h.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

theorem fixQ_eq_range {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1) :
    (M.normQ hiH).range = M.fixQ hiH := by
  refine Subgroup.eq_of_le_of_card_ge (M.range_normQ_le hiH hi2) ?_
  have h := M.card_fixQ_mul hiH
  rw [M.card_fixQ hiH hK hi2] at h ⊢
  omega

theorem card_centralizer_U {j : G} (hjH : j ∈ ruH M.T) (hK : j ∉ M.K) (hj2 : j ^ 2 = 1) :
    Nat.card ↥(ruU M.L M.T ⊓ Subgroup.centralizer ({j} : Set G)) = 8 := by
  classical
  set CU := ruU M.L M.T ⊓ Subgroup.centralizer ({j} : Set G)
  have hCU : CU ≤ ruU M.L M.T := inf_le_left
  have hjj : j * j = 1 := by rw [← pow_two]; exact hj2
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right hjj
  let f : CU.subgroupOf (ruU M.L M.T) →* Multiplicative (Fin 2 → F4) :=
    M.ψU.comp (CU.subgroupOf (ruU M.L M.T)).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hCU] at h
  have hker : Nat.card f.ker = 2 := by
    refine Eq.trans ?_ M.toRuData.card_Z
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_⟩
        invFun := fun w => ⟨⟨⟨w.1, M.two.Z_le_U w.2⟩, Subgroup.mem_subgroupOf.mpr
          ⟨M.two.Z_le_U w.2, Subgroup.mem_centralizer_singleton_iff.mpr
            (M.Z_comm_H w.2 hjH)⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      exact (M.ψU_eq_one_iff _).mp hx
    · show M.ψU ⟨w.1, _⟩ = 1
      exact (M.ψU_eq_one_iff _).mpr w.2
  have hrange : Nat.card f.range = 4 := by
    refine Eq.trans ?_ ((Nat.card_eq_fintype_card).trans
      (Sigma.card_fix_outside _ (M.φ_inv_props hjH hK hj2)))
    refine Nat.card_congr
      { toFun := fun y => ⟨Multiplicative.toAdd y.1, ?_⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun v => rfl }
    · obtain ⟨u, hu⟩ := y.2
      rw [← hu]
      have hc : j * u.1.1 * j⁻¹ = u.1.1 := by
        have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp u.2).2
        rw [← this, mul_inv_cancel_right]
      have e := M.ψU_conj ⟨j, hjH⟩ u.1
      have hu' : (⟨j * u.1.1 * j⁻¹, M.conj_mem_U hjH u.1.2⟩ : ruU M.L M.T) = u.1 :=
        Subtype.ext hc
      rw [hu'] at e
      exact e.symm
    · obtain ⟨w, hw⟩ := Sigma.fix_outside _ (M.φ_inv_props hjH hK hj2) v.1 v.2
      set y := M.uOf w
      have hjy : j * (y : G) * j⁻¹ ∈ ruU M.L M.T := M.conj_mem_U hjH y.2
      have humem : (y : G) * (j * y * j⁻¹) ∈ ruU M.L M.T := mul_mem y.2 hjy
      have hufix : j * ((y : G) * (j * y * j⁻¹)) * j⁻¹ = (y : G) * (j * y * j⁻¹) := by
        calc j * ((y : G) * (j * y * j⁻¹)) * j⁻¹ = (j * y * j⁻¹) * ((j * j) * y * (j⁻¹ * j⁻¹)) := by
              group
          _ = (j * y * j⁻¹) * y := by rw [hjj, ← mul_inv_rev, hjj, inv_one, one_mul, mul_one]
          _ = (y : G) * (j * y * j⁻¹) := (M.U_comm hjy y.2)
      refine ⟨⟨⟨_, humem⟩, Subgroup.mem_subgroupOf.mpr ⟨humem,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩⟩, ?_⟩
      · calc (y : G) * (j * y * j⁻¹) * j = (j * ((y : G) * (j * y * j⁻¹)) * j⁻¹) * j := by
              rw [hufix]
          _ = j * ((y : G) * (j * y * j⁻¹)) := by group
      · show M.ψU ⟨_, humem⟩ = Multiplicative.ofAdd v.1
        apply Multiplicative.toAdd.injective
        have e : (⟨(y : G) * (j * y * j⁻¹), humem⟩ : ruU M.L M.T) = y * ⟨_, hjy⟩ := rfl
        rw [e, M.toAdd_ψU_mul, show (⟨j * (y : G) * j⁻¹, hjy⟩ : ruU M.L M.T) =
          ⟨((⟨j, hjH⟩ : ruH M.T) : G) * (y : G) * ((⟨j, hjH⟩ : ruH M.T) : G)⁻¹,
            M.conj_mem_U hjH y.2⟩ from rfl, M.ψU_conj, M.ψU_uOf, toAdd_ofAdd, hw]
  rw [hker, hrange] at h
  omega

omit [Finite G] in
theorem conj_eq_mul_q0 {i : G} (hiH : i ∈ ruH M.T) (hi2 : i ^ 2 = 1) (x : ruQ M.T) :
    (x : G)⁻¹ * i * x = i * (((M.conjQ ⟨i, hiH⟩ x)⁻¹ * x : ruQ M.T) : G) := by
  have hi' := inv_eq_self_of_sq hi2
  show (x : G)⁻¹ * i * x = i * ((i * x * i⁻¹)⁻¹ * x)
  rw [hi']
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  calc (x : G)⁻¹ * i * x = (i * i) * (x : G)⁻¹ * i * x := by rw [hii, one_mul]
    _ = i * (i * x * i)⁻¹ * x := by
        rw [show (i * (x : G) * i)⁻¹ = i⁻¹ * (x : G)⁻¹ * i⁻¹ by group, hi']
        group
    _ = i * ((i * x * i)⁻¹ * x) := by group

omit [Finite G] in
theorem mk_q0 {i : G} (hiH : i ∈ ruH M.T) (x : ruQ M.T) :
    (((M.conjQ ⟨i, hiH⟩ x)⁻¹ * x : ruQ M.T) : M.Qbar) = M.normQ hiH x := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  show (M.actQ ⟨i, hiH⟩ (x : M.Qbar))⁻¹ * (x : M.Qbar) = (x : M.Qbar) * M.actQ ⟨i, hiH⟩ x
  have h2 := M.Qbar_sq (M.actQ ⟨i, hiH⟩ (x : M.Qbar))
  rw [inv_eq_of_mul_eq_one_right h2, M.Qbar_comm]

omit [Finite G] in
theorem conj_mem_K {g k : G} (hg : g ∈ ruH M.T) (hk : k ∈ M.K) : g * k * g⁻¹ ∈ M.K := by
  obtain ⟨hkH, hk1⟩ := M.mem_K_iff.mp hk
  have hmem : g * k * g⁻¹ ∈ ruH M.T := mul_mem (mul_mem hg hkH) (inv_mem hg)
  refine M.mem_K_iff.mpr ⟨hmem, ?_⟩
  have e : M.φ ⟨g * k * g⁻¹, hmem⟩ = M.φ ⟨g, hg⟩ * M.φ ⟨k, hkH⟩ * (M.φ ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e, SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    hk1, mul_one, mul_inv_cancel]

omit [Finite G] in
theorem mk_fixQ {i : G} (hiH : i ∈ ruH M.T) (hi2 : i ^ 2 = 1) {q : ruQ M.T}
    (hq : (i * (q : G)) ^ 2 = 1) : (q : M.Qbar) ∈ M.fixQ hiH := by
  rw [M.mem_fixQ, M.actQ_mk, M.mk_eq_mk_iff]
  have hi' := inv_eq_self_of_sq hi2
  have e : ((M.conjQ ⟨i, hiH⟩ q : ruQ M.T) : G)⁻¹ * q = (q : G) ^ 2 := by
    show (i * q * i⁻¹)⁻¹ * q = (q : G) ^ 2
    rw [hi', pow_two]
    have h := hq
    rw [pow_two] at h
    have h' : i * q * i = (q : G)⁻¹ := by
      calc i * q * i = i * q * i * (q * (q : G)⁻¹) := by group
        _ = (i * q * (i * q)) * (q : G)⁻¹ := by group
        _ = (q : G)⁻¹ := by rw [h, one_mul]
    rw [h']
    group
  rw [e]
  exact (M.two.QU_elem _ q.2 _ q.2).2

abbrev invFiber (i : G) (a : M.Qbar) : Type _ :=
  {q : ruQ M.T // (i * (q : G)) ^ 2 = 1 ∧ (q : M.Qbar) = a}

omit [Finite G] in
theorem j0_props {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1) (x : ruQ M.T) :
    (x : G)⁻¹ * i * x ∈ ruH M.T ∧ (x : G)⁻¹ * i * x ∉ M.K ∧ ((x : G)⁻¹ * i * x) ^ 2 = 1 := by
  have hxH : (x : G) ∈ ruH M.T := pCoreOf_le 2 _ x.2
  refine ⟨mul_mem (mul_mem (inv_mem hxH) hiH) hxH, fun hK0 => hK ?_, ?_⟩
  · have := M.conj_mem_K hxH hK0
    simpa [mul_assoc] using this
  · rw [pow_two]
    calc (x : G)⁻¹ * i * x * ((x : G)⁻¹ * i * x) = (x : G)⁻¹ * (i * i) * x := by group
      _ = 1 := by rw [← pow_two, hi2]; group

theorem card_invFiber {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1)
    {a : M.Qbar} (ha : a ∈ M.fixQ hiH) : Nat.card (M.invFiber i a) = 8 := by
  rw [← M.fixQ_eq_range hiH hK hi2] at ha
  obtain ⟨xbar, rfl⟩ := ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  set q0 : ruQ M.T := (M.conjQ ⟨i, hiH⟩ x)⁻¹ * x
  have hj0 : (x : G)⁻¹ * i * x = i * q0 := M.conj_eq_mul_q0 hiH hi2 x
  obtain ⟨hj0H, hj0K, hj02⟩ := M.j0_props hiH hK hi2 x
  set j0 : G := (x : G)⁻¹ * i * x
  have hq0 : (q0 : M.Qbar) = M.normQ hiH x := M.mk_q0 hiH x
  rw [← M.card_centralizer_U hj0H hj0K hj02]
  have hfib : ∀ q : M.invFiber i (M.normQ hiH x), (q0 : G)⁻¹ * q.1 ∈ ruU M.L M.T := by
    intro q
    have h : (q0 : M.Qbar) = (q.1 : M.Qbar) := by rw [hq0, q.2.2]
    exact (M.mk_eq_mk_iff).mp h
  refine Nat.card_congr
    { toFun := fun q => ⟨(q0 : G)⁻¹ * q.1, Subgroup.mem_inf.mpr ⟨hfib q, ?_⟩⟩
      invFun := fun u => ⟨q0 * ⟨u.1, M.U_le_Q (Subgroup.mem_inf.mp u.2).1⟩, ?_, ?_⟩
      left_inv := fun q => Subtype.ext (Subtype.ext (by simp))
      right_inv := fun u => Subtype.ext (by simp) }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := q.2.1
    have e : i * ((q.1 : ruQ M.T) : G) = j0 * ((q0 : G)⁻¹ * q.1) := by
      rw [hj0]
      group
    rw [e] at h
    exact (sq_mul_eq_one_iff hj02 (M.U_sq (hfib q))).mp h
  · have hu := u.2
    have e : i * ((q0 * ⟨u.1, M.U_le_Q (Subgroup.mem_inf.mp u.2).1⟩ : ruQ M.T) : G) =
        j0 * u.1 := by
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, ← hj0]
    rw [e]
    exact (sq_mul_eq_one_iff hj02 (M.U_sq (Subgroup.mem_inf.mp hu).1)).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2)
  · rw [QuotientGroup.mk_mul, hq0]
    have : ((⟨u.1, M.U_le_Q (Subgroup.mem_inf.mp u.2).1⟩ : ruQ M.T) : M.Qbar) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_inf.mp u.2).1
    rw [this, mul_one]

theorem card_inv_coset {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1) :
    Nat.card {q : ruQ M.T // (i * (q : G)) ^ 2 = 1} = 64 := by
  classical
  let g : {q : ruQ M.T // (i * (q : G)) ^ 2 = 1} → M.fixQ hiH := fun q =>
    ⟨(q.1 : M.Qbar), M.mk_fixQ hiH hi2 q.2⟩
  have hfib : ∀ a : M.fixQ hiH, Nat.card {q // g q = a} = 8 := by
    intro a
    rw [← M.card_invFiber hiH hK hi2 a.2]
    exact Nat.card_congr
      { toFun := fun q => ⟨q.1.1, q.1.2, congrArg Subtype.val q.2⟩
        invFun := fun q => ⟨⟨q.1, q.2.1⟩, Subtype.ext q.2.2⟩
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
  have : Fintype (M.fixQ hiH) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, M.card_fixQ hiH hK hi2]
  rfl

theorem conj_of_inv_coset {i : G} (hiH : i ∈ ruH M.T) (hK : i ∉ M.K) (hi2 : i ^ 2 = 1)
    {q : ruQ M.T} (hq : (i * (q : G)) ^ 2 = 1) :
    ∃ y ∈ ruQ M.T, i * q = y⁻¹ * i * y ∨ i * q = y⁻¹ * (i * M.z) * y := by
  have ha := M.mk_fixQ hiH hi2 hq
  rw [← M.fixQ_eq_range hiH hK hi2] at ha
  obtain ⟨xbar, hx⟩ := ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  set q0 : ruQ M.T := (M.conjQ ⟨i, hiH⟩ x)⁻¹ * x
  have hj0 : (x : G)⁻¹ * i * x = i * q0 := M.conj_eq_mul_q0 hiH hi2 x
  obtain ⟨hj0H, hj0K, hj02⟩ := M.j0_props hiH hK hi2 x
  set j0 : G := (x : G)⁻¹ * i * x
  have hj0i : j0⁻¹ = j0 := inv_eq_self_of_sq hj02
  have hu : (q0 : G)⁻¹ * q ∈ ruU M.L M.T := by
    have h : (q0 : M.Qbar) = (q : M.Qbar) := by rw [M.mk_q0 hiH x, hx]
    exact (M.mk_eq_mk_iff).mp h
  set u : G := (q0 : G)⁻¹ * q
  have hiq : i * (q : G) = j0 * u := by rw [hj0]; simp only [u]; group
  have huj : u * j0 = j0 * u := by
    rw [hiq] at hq
    exact (sq_mul_eq_one_iff hj02 (M.U_sq hu)).mp hq
  have hfixu : sigmaAct (M.φ ⟨j0, hj0H⟩) (Multiplicative.toAdd (M.ψU ⟨u, hu⟩)) =
      Multiplicative.toAdd (M.ψU ⟨u, hu⟩) := by
    rw [← M.ψU_conj ⟨j0, hj0H⟩ ⟨u, hu⟩]
    congr 3
    show j0 * u * j0⁻¹ = u
    rw [← huj, mul_inv_cancel_right]
  obtain ⟨w, hw⟩ := Sigma.fix_outside _ (M.φ_inv_props hj0H hj0K hj02) _ hfixu
  set y := M.uOf w
  have hjy : j0 * (y : G) * j0⁻¹ ∈ ruU M.L M.T := M.conj_mem_U hj0H y.2
  have hu'mem : (y : G) * (j0 * y * j0⁻¹) ∈ ruU M.L M.T := mul_mem y.2 hjy
  have hψ : M.ψU ⟨_, hu'mem⟩ = M.ψU ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    have e : (⟨(y : G) * (j0 * y * j0⁻¹), hu'mem⟩ : ruU M.L M.T) = y * ⟨_, hjy⟩ := rfl
    rw [e, M.toAdd_ψU_mul, show (⟨j0 * (y : G) * j0⁻¹, hjy⟩ : ruU M.L M.T) =
      ⟨((⟨j0, hj0H⟩ : ruH M.T) : G) * (y : G) * ((⟨j0, hj0H⟩ : ruH M.T) : G)⁻¹,
        M.conj_mem_U hj0H y.2⟩ from rfl, M.ψU_conj, M.ψU_uOf, ← hw]
  have hZ : ((y : G) * (j0 * y * j0⁻¹))⁻¹ * u ∈ ruZ M.T := by
    have hk : (⟨_, hu'mem⟩ : ruU M.L M.T)⁻¹ * ⟨u, hu⟩ ∈ M.ψU.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψ]
      exact inv_mul_cancel _
    rw [M.ψU_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hconj : (y : G)⁻¹ * j0 * y = j0 * ((y : G) * (j0 * y * j0⁻¹)) := by
    have hv2 : (j0 * (y : G) * j0⁻¹) * (j0 * y * j0⁻¹) = 1 := by
      rw [← pow_two]; exact M.U_sq hjy
    have hvi : (j0 * (y : G) * j0⁻¹)⁻¹ = j0 * y * j0⁻¹ := inv_eq_of_mul_eq_one_right hv2
    have hyv := M.U_comm y.2 hjy
    have e1 : j0⁻¹ * (y : G)⁻¹ * j0 = (j0 * y * j0⁻¹)⁻¹ := by
      calc j0⁻¹ * (y : G)⁻¹ * j0 = j0 * (y : G)⁻¹ * j0⁻¹ := by rw [hj0i]
        _ = (j0 * y * j0⁻¹)⁻¹ := by group
    calc (y : G)⁻¹ * j0 * y = j0 * (j0⁻¹ * (y : G)⁻¹ * j0) * y := by group
      _ = j0 * (j0 * y * j0⁻¹)⁻¹ * y := by rw [e1]
      _ = j0 * (j0 * y * j0⁻¹) * y := by rw [hvi]
      _ = j0 * ((j0 * y * j0⁻¹) * y) := by group
      _ = j0 * ((y : G) * (j0 * y * j0⁻¹)) := by rw [← hyv]
  have hxH : (x : G) ∈ ruQ M.T := x.2
  refine ⟨(x : G) * y, mul_mem hxH (M.U_le_Q y.2), ?_⟩
  rcases M.mem_Z_iff.mp hZ with h1 | h1
  · left
    rw [inv_mul_eq_one] at h1
    rw [hiq, ← h1, ← hconj]
    simp only [j0]
    group
  · right
    have hu' : u = (y : G) * (j0 * y * j0⁻¹) * M.z := by
      rw [← h1]; group
    have hzc : M.z * ((x : G) * y) = ((x : G) * y) * M.z :=
      M.Z_comm_H M.z_mem_Z (mul_mem (pCoreOf_le 2 _ x.2) (pCoreOf_le 2 _ (M.U_le_Q y.2)))
    rw [hiq, hu', ← mul_assoc, ← hconj]
    simp only [j0]
    calc (y : G)⁻¹ * ((x : G)⁻¹ * i * x) * y * M.z =
        ((x : G) * y)⁻¹ * i * (((x : G) * y) * M.z) := by group
      _ = ((x : G) * y)⁻¹ * i * (M.z * ((x : G) * y)) := by rw [hzc]
      _ = ((x : G) * y)⁻¹ * (i * M.z) * ((x : G) * y) := by group

end RuDataM

end CFSG.Quasithin.RuType
