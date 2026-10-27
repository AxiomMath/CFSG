module

public import CFSG.Sporadic.Recognition.ThMultiplierConfig2
public import CFSG.GroupTheory.GLnTwoSplitting.NoPerfectCover
public import CFSG.Sporadic.Recognition.ThMultiplierOdd

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.GroupTheory.GLnTwoSplitting CFSG.LocalAnalysis.DempwolffFive
open scoped commutatorElement

namespace Config

variable {Γ : Type*} [Group Γ] (X : Config Γ)

theorem zpowers_le_Vsub : Subgroup.zpowers (X.v 0) ≤ X.Vsub :=
  Subgroup.zpowers_le.2 (X.v_mem_Vsub 0)

theorem Q_le_Hsub : X.Q ≤ X.Hsub := by
  intro q hq
  refine X.mem_normalizer_of_conj fun j => ?_
  have hc := X.Q_comm q hq (X.v j) (X.v_mem_Q j)
  have h1 : q * X.v j * q⁻¹ = ⁅q, X.v j⁆ * X.v j := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact Subgroup.mul_mem _ (X.zpowers_le_Vsub hc) (X.v_mem_Vsub j)

@[expose] def CV : Subgroup Γ := Subgroup.centralizer (X.Vsub : Set Γ)

theorem mem_CV {g : Γ} : g ∈ X.CV ↔ ∀ v ∈ X.Vsub, v * g = g * v := Subgroup.mem_centralizer_iff

theorem Vsub_le_CV : X.Vsub ≤ X.CV := by
  intro v hv
  rw [mem_CV]
  rintro w ⟨c, rfl⟩
  obtain ⟨c', rfl⟩ := hv
  exact X.iota_comm c c'

theorem CV_le_Hsub : X.CV ≤ X.Hsub := fun g hg =>
  X.mem_normalizer_of_conj fun j => by
    have h := (X.mem_CV.1 hg) (X.v j) (X.v_mem_Vsub j)
    rw [← h, mul_inv_cancel_right]
    exact X.v_mem_Vsub j

theorem actV_ker : X.actV.ker = X.CV.subgroupOf X.Hsub := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_CV]
  constructor
  · intro h v hv
    obtain ⟨c, rfl⟩ := hv
    have h1 := X.actV_spec g c
    rw [h] at h1
    have h2 : (g : Γ) * X.iota c * (g : Γ)⁻¹ = X.iota c := congrArg Subtype.val h1
    rw [← h2, mul_assoc, inv_mul_cancel, mul_one]
    rw [h2]
  · intro h
    refine LinearEquiv.ext fun c => X.iotaH_injective ?_
    rw [← X.actV_spec]
    apply Subtype.ext
    show (g : Γ) * X.iota c * (g : Γ)⁻¹ = X.iota c
    have h2 := h (X.iota c) (X.iota_mem_Vsub c)
    rw [← h2, mul_inv_cancel_right]

theorem card_GLV : Nat.card ((Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)) = 9999360 := by
  have hE : Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 := Module.finrank_fin_fun _
  rw [card_linearEquiv_eq hE, Matrix.card_GL_field]
  simp [Fin.prod_univ_five, ZMod.card]

theorem card_Hsub_eq : Nat.card X.Hsub = 9999360 * Nat.card X.CV := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup X.actV.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective X.actV X.actV_surjective).toEquiv,
    card_GLV] at h1
  rw [h1, X.actV_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe X.CV_le_Hsub).toEquiv]

theorem CV_le_M : X.CV ≤ X.M := fun g hg =>
  X.cent_M g ((X.mem_CV.1 hg) (X.v 0) (X.v_mem_Vsub 0)).symm

theorem conj_mem_CV {h : Γ} (hh : h ∈ X.Hsub) {c : Γ} (hc : c ∈ X.CV) : h * c * h⁻¹ ∈ X.CV := by
  rw [mem_CV]
  intro v hv
  have hw : h⁻¹ * v * h ∈ X.Vsub := (Subgroup.mem_normalizer_iff''.1 hh v).1 hv
  have h1 := (X.mem_CV.1 hc) (h⁻¹ * v * h) hw
  calc v * (h * c * h⁻¹) = h * ((h⁻¹ * v * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * v * h)) * h⁻¹ := by rw [h1]
    _ = h * c * h⁻¹ * v := by group

theorem CV_le_Vsub [Finite Γ] (hΓ : Nat.card Γ = 90745943887872000) : X.CV ≤ X.Vsub := by
  have hdvd : Nat.card X.Hsub ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card X.Hsub
  rw [hΓ, X.card_Hsub_eq] at hdvd
  have hVC : X.Vsub ≤ X.CV := X.Vsub_le_CV
  have h32 : 32 ∣ Nat.card X.CV := by
    rw [← X.card_Vsub]
    exact Subgroup.card_dvd_of_le hVC
  obtain ⟨n, hn⟩ := h32
  have hn2 : n ∣ 283599225 := by
    rw [hn] at hdvd
    have h3 : 32 * n ∣ 32 * 283599225 := by
      refine Nat.dvd_of_mul_dvd_mul_left (show 0 < 9999360 by norm_num) ?_
      rw [show 9999360 * (32 * 283599225) = 90745943887872000 by norm_num]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (show 0 < 32 by norm_num) h3
  have hodd : Odd n := Odd.of_dvd_nat (by decide) hn2
  let V' : Subgroup X.CV := X.Vsub.subgroupOf X.CV
  have hV'c : V' ≤ Subgroup.center X.CV := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact ((X.mem_CV.1 c.2) v hv).symm
  have hV'card : Nat.card V' = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv]
    exact X.card_Vsub
  obtain ⟨O, hOcard, hOchar⟩ := exists_central_two_complement V' hV'c hV'card n hodd hn
  have key : ∀ o : X.CV, o ∈ O → o = 1 := by
    intro o ho
    have hxC : (o : Γ) ∈ X.CV := o.2
    have hxn : (o : Γ) ^ n = 1 := congrArg Subtype.val ((hOchar o).1 ho)
    have hxM : (o : Γ) ∈ X.M := X.CV_le_M hxC
    have hcomm : ∀ q ∈ X.Q, (o : Γ) * q = q * (o : Γ) := by
      intro q hq
      have hqH : q ∈ X.Hsub := X.Q_le_Hsub hq
      have hy : q * (o : Γ)⁻¹ * q⁻¹ ∈ X.CV := X.conj_mem_CV hqH (X.CV.inv_mem hxC)
      have hyn : (q * (o : Γ)⁻¹ * q⁻¹) ^ n = 1 := by
        have : (q * (o : Γ)⁻¹ * q⁻¹) ^ n = q * ((o : Γ)⁻¹ ^ n) * q⁻¹ := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
        rw [this, inv_pow, hxn]
        group
      have hyO : (⟨q * (o : Γ)⁻¹ * q⁻¹, hy⟩ : X.CV) ∈ O :=
        (hOchar _).2 (Subtype.ext (by simpa using hyn))
      have huO := O.mul_mem ho hyO
      have hun : ((o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹)) ^ n = 1 :=
        congrArg Subtype.val ((hOchar _).1 huO)
      have huQ : (o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹) ∈ X.Q := by
        have h1 : (o : Γ) * q * (o : Γ)⁻¹ ∈ X.Q := X.M_conj_Q _ hxM q hq
        have h2 : (o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹) = ((o : Γ) * q * (o : Γ)⁻¹) * q⁻¹ := by group
        rw [h2]
        exact X.Q.mul_mem h1 (X.Q.inv_mem hq)
      have hu512 : ((o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹)) ^ 512 = 1 := by
        have h := pow_card_eq_one' (G := X.Q) (x := ⟨_, huQ⟩)
        rw [X.card_Q] at h
        exact congrArg Subtype.val h
      have hu1 : (o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹) = 1 := by
        have hord : orderOf ((o : Γ) * (q * (o : Γ)⁻¹ * q⁻¹)) ∣ Nat.gcd n 512 :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hun) (orderOf_dvd_of_pow_eq_one hu512)
        have hg : Nat.gcd n 512 = 1 := by
          rw [show (512 : ℕ) = 2 ^ 9 by norm_num]
          exact (Nat.coprime_two_right.2 hodd).pow_right 9
        rw [hg] at hord
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
      have h3 : (o : Γ) * q * (o : Γ)⁻¹ * q⁻¹ = 1 := by simpa [mul_assoc] using hu1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3
    have hxz : (o : Γ) ∈ Subgroup.zpowers (X.v 0) :=
      X.cent_Q _ hxM fun q hq => (hcomm q hq).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hsq : (o : Γ) * (o : Γ) = 1 := by
      rw [← hk]
      have h2 : X.v 0 ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact X.v_sq 0
      calc X.v 0 ^ k * X.v 0 ^ k = X.v 0 ^ (k + k) := (zpow_add _ _ _).symm
        _ = (X.v 0 ^ (2 : ℤ)) ^ k := by rw [← zpow_mul, two_mul]
        _ = 1 := by rw [h2, one_zpow]
    have hx1 : (o : Γ) = 1 := by
      obtain ⟨m, hm⟩ := hodd
      have h1 : (o : Γ) ^ n = (o : Γ) := by
        rw [hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
      rw [← h1]
      exact hxn
    exact Subtype.ext hx1
  have hO : O = ⊥ := (Subgroup.eq_bot_iff_forall O).2 key
  have hn1 : n = 1 := by
    rw [← hOcard, hO, Subgroup.card_bot]
  have hCV32 : Nat.card X.CV = 32 := by rw [hn, hn1, mul_one]
  have : X.Vsub = X.CV :=
    Subgroup.eq_of_le_of_card_ge hVC (by rw [hCV32, X.card_Vsub])
  rw [← this]

noncomputable def natExt [Finite Γ] (hΓ : Nat.card Γ = 90745943887872000) :
    NatExt X.Hsub (Fin 5 → ZMod 2) :=
  natExtOfConj X.iotaH X.iotaH_add X.iotaH_injective X.iotaH_norm X.actV_surjective
    (fun g hg => by
      have hgC : (g : Γ) ∈ X.CV := by
        rw [mem_CV]
        intro v hv
        obtain ⟨c, rfl⟩ := hv
        have h1 := hg c
        have h2 : (g : Γ) * X.iota c * (g : Γ)⁻¹ = X.iota c := congrArg Subtype.val h1
        rw [← h2, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
      obtain ⟨c, hc⟩ := X.CV_le_Vsub hΓ hgC
      exact ⟨c, Subtype.ext hc⟩)

include X in
theorem exists_subgroup [Finite Γ] (hΓ : Nat.card Γ = 90745943887872000) :
    ∃ H : Subgroup Γ, Odd H.index ∧ Group.IsPerfect H ∧
      CFSG.Monster.Schur.NoPerfectDoubleCover H := by
  have hE : Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 := Module.finrank_fin_fun _
  refine ⟨X.Hsub, ?_, (X.natExt hΓ).isPerfect hE, (X.natExt hΓ).noPerfectDoubleCover hE⟩
  have hCV : Nat.card X.CV = 32 := by
    have : X.Vsub = X.CV := le_antisymm X.Vsub_le_CV (X.CV_le_Vsub hΓ)
    rw [← this]
    exact X.card_Vsub
  have h1 := X.Hsub.card_mul_index
  rw [hΓ, X.card_Hsub_eq, hCV] at h1
  have : X.Hsub.index = 283599225 := by omega
  rw [this]
  decide

end Config

end CFSG.Sporadic.Recognition.ThMultiplier
