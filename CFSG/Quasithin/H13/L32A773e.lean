module

public import CFSG.Quasithin.H13.L32A773d
public import CFSG.Quasithin.H13.L32A772
public import CFSG.Quasithin.H13.L32A773b
public import CFSG.Quasithin.H13.L32A773c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem sL_le_kz : sL T L V ≤ kz T V := C.sL_le_l1.trans (l1_le_kz C.hyp C.hMod)

theorem sL_not_le_QH : ¬ sL T L V ≤ pCoreOf 2 (hz T V) := by
  intro h
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  rw [← C.sup_eq_R1, sup_eq_right.mpr h, Subgroup.relIndex_self] at h4
  norm_num at h4

theorem eq_kz_of_normal {N : Subgroup G} (hNK : N ≤ kz T V)
    (hn : kz T V ≤ Subgroup.normalizer (N : Set G)) (hSN : sL T L V ≤ N) : N = kz T V := by
  obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
  exact eq_oTwoUpper_of_normal hs hk hNK hn fun h => C.sL_not_le_QH (hSN.trans h)

omit C in
theorem mem_pCoreOf_kz {x : G} :
    x ∈ pCoreOf 2 (kz T V) ↔ x ∈ kz T V ∧ x ∈ pCoreOf 2 (hz T V) := by
  rw [show kz T V = oTwoUpper (hz T V) from rfl, pCoreOf_oTwoUpper_eq, Subgroup.mem_inf]

theorem comm_mem_fsuV1_of_mem_Q {c : G} (hc : c ∈ pCoreOf 2 (L ⊔ T))
    (hcL : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V) {q : G} (hq : q ∈ pCoreOf 2 (kz T V)) :
    q * c * q⁻¹ * c⁻¹ ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe ha hb
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQHT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hV1U : fsuV1 T V ≤ fsuU T V := fun x hx => v_le_fsuU (Subgroup.mem_inf.mp hx).1
  have hcen : ∀ h ∈ hz T V, ∀ v ∈ fsuV1 T V, h * v * h⁻¹ = v := fun h hh v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp hh v hv).symm, mul_inv_cancel_right]
  have hOK : ∀ {x : G}, x ∈ pCoreOf 2 (kz T V) → x ∈ kz T V := fun hx =>
    (mem_pCoreOf_kz.mp hx).1
  have hOQ : ∀ {x : G}, x ∈ pCoreOf 2 (kz T V) → x ∈ pCoreOf 2 (hz T V) := fun hx =>
    (mem_pCoreOf_kz.mp hx).2
  have hOn : ∀ k ∈ kz T V, ∀ x ∈ pCoreOf 2 (kz T V), k * x * k⁻¹ ∈ pCoreOf 2 (kz T V) :=
    fun k hk x hx => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hk) x).mp hx
  have hcS : ∀ {s : G}, s ∈ sL T L V → c * s = s * c := fun hs => C.comm_sL_eq_one_Q hc hcL hs
  have hcU : ∀ u ∈ fsuU T V, c * u = u * c := fun u hu => hcS (le_conjClosure _ _ hu)
  have hcV := C.mem_centralizer_of_mem_Q hc
  have hcH : c ∈ hz T V := by
    show c ∈ Subgroup.centralizer (fsuV1 T V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp hcV w (Subgroup.mem_inf.mp hw).1
  have hcC : c ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
    Subgroup.mem_inf.mpr ⟨C.mem_QH_of hcH hcU,
      Subgroup.mem_centralizer_iff.mpr fun u hu => (hcU u hu).symm⟩
  have hκU : ∀ k ∈ kz T V, k * c * k⁻¹ * c⁻¹ ∈ fsuU T V := fun k hk => by
    have h := (C.l71 G T L V C.hyp).1.2 (Subgroup.commutator_mem_commutator hcC hk)
    have := inv_mem h
    rwa [commutatorElement_def, show (c * k * c⁻¹ * k⁻¹)⁻¹ = k * c * k⁻¹ * c⁻¹ by group]
      at this
  let W : Subgroup G :=
    { carrier := {w | w ∈ pCoreOf 2 (kz T V) ∧ w * c * w⁻¹ * c⁻¹ ∈ fsuV1 T V}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [show a * b * c * (a * b)⁻¹ * c⁻¹ =
          (a * (b * c * b⁻¹ * c⁻¹) * a⁻¹) * (a * c * a⁻¹ * c⁻¹) by group,
          hcen a (hKH (hOK ha.1)) _ hb.2]
        exact mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [show a⁻¹ * c * a⁻¹⁻¹ * c⁻¹ = a⁻¹ * (a * c * a⁻¹ * c⁻¹)⁻¹ * a⁻¹⁻¹ by group,
          hcen a⁻¹ (inv_mem (hKH (hOK ha.1))) _ (inv_mem ha.2)]
        exact inv_mem ha.2⟩ }
  have hmemW : ∀ {w : G}, w ∈ W ↔ w ∈ pCoreOf 2 (kz T V) ∧ w * c * w⁻¹ * c⁻¹ ∈ fsuV1 T V :=
    Iff.rfl
  have hWK : ∀ k ∈ kz T V, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    obtain ⟨hwO, hwc⟩ := hmemW.mp hw
    refine hmemW.mpr ⟨hOn k hk w hwO, ?_⟩
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = k * c * k⁻¹ * c⁻¹ := ⟨_, rfl⟩
    obtain ⟨w', hw'⟩ : ∃ w', w' = k * w * k⁻¹ := ⟨_, rfl⟩
    have hκU' : κ ∈ fsuU T V := by rw [hκ]; exact hκU k hk
    have hw'O : w' ∈ pCoreOf 2 (kz T V) := by rw [hw']; exact hOn k hk w hwO
    have h1 : w' * κ * w'⁻¹ * κ⁻¹ ∈ fsuV1 T V := C.comm_mem_fsuV1 (hOQ hw'O) hκU'
    have hkwc : k * (w * c * w⁻¹ * c⁻¹) * k⁻¹ = w * c * w⁻¹ * c⁻¹ := hcen k (hKH hk) _ hwc
    have e : w' * c * w'⁻¹ * c⁻¹ =
        κ⁻¹ * ((w' * κ * w'⁻¹ * κ⁻¹)⁻¹ * (k * (w * c * w⁻¹ * c⁻¹) * k⁻¹)) * κ := by
      rw [hκ, hw']
      group
    have hY : (w' * κ * w'⁻¹ * κ⁻¹)⁻¹ * (w * c * w⁻¹ * c⁻¹) ∈ fsuV1 T V :=
      mul_mem (inv_mem h1) hwc
    rw [← hw', e, hkwc, hUc κ⁻¹ (inv_mem hκU') _ (hV1U hY), inv_mul_cancel_right]
    exact hY
  let K₀ : Subgroup G :=
    { carrier := {k | k ∈ kz T V ∧ ∀ w ∈ pCoreOf 2 (kz T V), k * w * k⁻¹ * w⁻¹ ∈ W}
      one_mem' := ⟨one_mem _, fun w _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun w hw => by
        rw [show a * b * w * (a * b)⁻¹ * w⁻¹ = (a * (b * w * b⁻¹ * w⁻¹) * a⁻¹) *
          (a * w * a⁻¹ * w⁻¹) by group]
        exact mul_mem (hWK a ha.1 _ (hb.2 w hw)) (ha.2 w hw)⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun w hw => by
        have hw' : a⁻¹ * w * a ∈ pCoreOf 2 (kz T V) := by
          have := hOn a⁻¹ (inv_mem ha.1) w hw
          simpa using this
        rw [show a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ = (a * (a⁻¹ * w * a) * a⁻¹ * (a⁻¹ * w * a)⁻¹)⁻¹ by group]
        exact inv_mem (ha.2 _ hw')⟩ }
  have hmemK₀ : ∀ {k : G}, k ∈ K₀ ↔
      k ∈ kz T V ∧ ∀ w ∈ pCoreOf 2 (kz T V), k * w * k⁻¹ * w⁻¹ ∈ W := Iff.rfl
  have hK₀ : K₀ = kz T V := by
    refine C.eq_kz_of_normal (fun k hk => (hmemK₀.mp hk).1)
      (le_normalizer_of_conj_mem' fun k hk k₀ hk₀ => hmemK₀.mpr
        ⟨mul_mem (mul_mem hk (hmemK₀.mp hk₀).1) (inv_mem hk), fun w hw => ?_⟩)
      fun s hs => hmemK₀.mpr ⟨C.sL_le_kz hs, fun w hw => ?_⟩
    · have hw' : k⁻¹ * w * k ∈ pCoreOf 2 (kz T V) := by
        have := hOn k⁻¹ (inv_mem hk) w hw
        simpa using this
      rw [show k * k₀ * k⁻¹ * w * (k * k₀ * k⁻¹)⁻¹ * w⁻¹ =
        k * (k₀ * (k⁻¹ * w * k) * k₀⁻¹ * (k⁻¹ * w * k)⁻¹) * k⁻¹ by group]
      exact hWK k hk _ ((hmemK₀.mp hk₀).2 _ hw')
    · have hsK := C.sL_le_kz hs
      have hx : s * w * s⁻¹ * w⁻¹ ∈ sL T L V := by
        have hwN : w ∈ Subgroup.normalizer (sL T L V : Set G) :=
          C.T_le_normalizer_sL (hQHT (hOQ hw))
        rw [show s * w * s⁻¹ * w⁻¹ = s * (w * s⁻¹ * w⁻¹) by group]
        exact mul_mem hs ((Subgroup.mem_normalizer_iff.mp hwN _).mp (inv_mem hs))
      refine hmemW.mpr ⟨mul_mem (hOn s hsK w hw) (inv_mem hw), ?_⟩
      rw [(hcS hx).symm, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hqK := hOK hq
  have huU := hκU q hqK
  refine (C.lemma14_7_72).2.2.2.1 _ huU fun k hk => ?_
  have hd : k * q * k⁻¹ * q⁻¹ ∈ W := by
    have h : k ∈ K₀ := by
      rw [hK₀]
      exact hk
    exact (hmemK₀.mp h).2 q hq
  obtain ⟨hdO, hdc⟩ := hmemW.mp hd
  obtain ⟨d, hd_def⟩ : ∃ d, d = k * q * k⁻¹ * q⁻¹ := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u, u = q * c * q⁻¹ * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨κ, hκ_def⟩ : ∃ κ, κ = k * c * k⁻¹ * c⁻¹ := ⟨_, rfl⟩
  rw [← hd_def] at hdO hdc
  rw [← hu_def] at huU
  rw [← hu_def]
  have hκU' : κ ∈ fsuU T V := by rw [hκ_def]; exact hκU k hk
  have hdu : d * u * d⁻¹ * u⁻¹ ∈ fsuV1 T V := C.comm_mem_fsuV1 (hOQ hdO) huU
  have hq' := hOn k hk q hq
  have h1 : (k * q * k⁻¹) * κ * (k * q * k⁻¹)⁻¹ * κ⁻¹ ∈ fsuV1 T V :=
    C.comm_mem_fsuV1 (hOQ hq') hκU'
  obtain ⟨X, hX⟩ : ∃ X, X = (d * u * d⁻¹ * u⁻¹) * u * (d * c * d⁻¹ * c⁻¹) := ⟨_, rfl⟩
  have hx : X ∈ fsuU T V := by
    rw [hX]
    exact mul_mem (mul_mem (hV1U hdu) huU) (hV1U hdc)
  have e1 : k * u * k⁻¹ * u⁻¹ = ((k * q * k⁻¹) * κ * (k * q * k⁻¹)⁻¹ * κ⁻¹) *
      (κ * X * κ⁻¹) * u⁻¹ := by
    rw [hX, hd_def, hu_def, hκ_def]
    group
  have hκX : κ * X * κ⁻¹ = X := by rw [hUc κ hκU' X hx, mul_inv_cancel_right]
  have huX : X * u⁻¹ = (d * u * d⁻¹ * u⁻¹) * (d * c * d⁻¹ * c⁻¹) := by
    calc X * u⁻¹ = (d * u * d⁻¹ * u⁻¹) * (u * (d * c * d⁻¹ * c⁻¹)) * u⁻¹ := by
          rw [hX]; group
      _ = (d * u * d⁻¹ * u⁻¹) * ((d * c * d⁻¹ * c⁻¹) * u) * u⁻¹ := by
          rw [hUc u huU _ (hV1U hdc)]
      _ = (d * u * d⁻¹ * u⁻¹) * (d * c * d⁻¹ * c⁻¹) := by group
  have e3 : k * u * k⁻¹ * u⁻¹ = ((k * q * k⁻¹) * κ * (k * q * k⁻¹)⁻¹ * κ⁻¹) *
      ((d * u * d⁻¹ * u⁻¹) * (d * c * d⁻¹ * c⁻¹)) := by
    rw [e1, hκX, ← huX]
    group
  rw [e3]
  exact mul_mem h1 (mul_mem hdu hdc)

end Ctx73

end CFSG.Quasithin.H13.L32A
