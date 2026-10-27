module

public import CFSG.Quasithin.H13.L32A723a

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

omit [Finite G] in
theorem not_three_dvd_card {X : Subgroup G} (hX : IsPGroup 2 ↥X) [Finite ↥X] :
    ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  rw [hn]
  intro h3
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

omit [Finite G] in
theorem isPGroup_u (D : Data T L V θ c) : IsPGroup 2 ↥(fsuU T V) := fun x =>
  ⟨1, Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one D.elem_u x.2)⟩

theorem comm_mem_v1_of_comm_mem_e (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {e : G}
    (hKe : ∀ y ∈ oTwoUpper H, y * e * y⁻¹ * e⁻¹ ∈ fsuU T V)
    (hPe : ∀ x ∈ pCoreOf 2 (oTwoUpper H), x * e * x⁻¹ * e⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) :
    ∀ x ∈ pCoreOf 2 (oTwoUpper H), x * e * x⁻¹ * e⁻¹ ∈ fsuV1 T V := by
  have hEU := e_le_u C D
  set A := Subgroup.closure ({y | ∃ x ∈ pCoreOf 2 (oTwoUpper H), x * e * x⁻¹ * e⁻¹ = y} ∪
    (fsuV1 T V : Set G)) with hA
  set N := conjClosure A (oTwoUpper H) with hN
  have hV₁A : fsuV1 T V ≤ A := fun v hv => Subgroup.subset_closure (Or.inr hv)
  have hNE : N ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
    refine conjClosure_le fun y hy a ha => ?_
    have hyH : y ∈ H := oTwoUpper_le H hy
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨x, hx, rfl⟩ | hv
      · set x' := y * x * y⁻¹ with hx'
        have hx'P : x' ∈ pCoreOf 2 (oTwoUpper H) :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_p hyH) x).mp hx
        set u₀ := y * e * y⁻¹ * e⁻¹ with hu₀
        have hu₀U : u₀ ∈ fsuU T V := hKe y hy
        have e1 : y * (x * e * x⁻¹ * e⁻¹) * y⁻¹ =
            (x' * u₀ * x'⁻¹ * u₀⁻¹) * (u₀ * (x' * e * x'⁻¹ * e⁻¹) * u₀⁻¹) := by
          rw [hx', hu₀]; group
        rw [e1]
        refine mul_mem (v1_le_e C (comm_mem_v1 C D (p_le_qh hx'P) hu₀U)) ?_
        have h1 := hPe x' hx'P
        rw [u_comm C hu₀U (hEU h1), mul_inv_cancel_right]
        exact h1
      · rw [conj_v1 C hyH hv]
        exact v1_le_e C hv
    | one => simp
    | mul a b _ _ iha ihb =>
      have e2 : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e2]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e2 : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e2]
      exact inv_mem iha
  have hNV : N = fsuV1 T V := by
    rcases C.irred_u N (hV₁A.trans (le_conjClosure _ _)) (hNE.trans hEU)
        (le_normalizer_conjClosure _ _) with h | h
    · exact h
    · exfalso
      have h1 : ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆.relIndex (fsuU T V) = 1 :=
        Subgroup.relIndex_eq_one.mpr (h ▸ hNE)
      rw [C.relIndex_eu] at h1
      norm_num at h1
  intro x hx
  have : x * e * x⁻¹ * e⁻¹ ∈ N :=
    le_conjClosure _ _ (Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩))
  rwa [hNV] at this

theorem exists_central (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {e : G}
    (heP : e ∈ pCoreOf 2 (oTwoUpper H)) (heU : e ∉ fsuU T V)
    (hKe : ∀ y ∈ oTwoUpper H, y * e * y⁻¹ * e⁻¹ ∈ fsuU T V)
    (hPe : ∀ x ∈ pCoreOf 2 (oTwoUpper H), x * e * x⁻¹ * e⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) :
    ∃ d ∈ pCoreOf 2 (oTwoUpper H), d ∉ fsuV1 T V ∧ ∀ y ∈ oTwoUpper H, y * d = d * y := by
  have hPV := comm_mem_v1_of_comm_mem_e C D hKe hPe
  have heH : e ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) heP
  have hUP := u_le_p C D
  have hcU : ∀ n ∈ fsuU T V, c * n * c⁻¹ ∈ fsuU T V := fun n hn => conj_c_mem_u C D hn
  have hce : e⁻¹ * (c * e * c⁻¹) ∈ fsuU T V := by
    have h1 := hKe c (c_mem_k C D)
    have e1 : e⁻¹ * (c * e * c⁻¹) = e⁻¹ * (c * e * c⁻¹ * e⁻¹) * e⁻¹⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D (inv_mem heH)) _).mp h1
  obtain ⟨n, hnU, hcd⟩ := exists_comm_mul_of_conj_mem D.c3
    (not_three_dvd_card (isPGroup_u D)) hcU hce
  set d := e * n with hd
  have hdP : d ∈ pCoreOf 2 (oTwoUpper H) := mul_mem heP (hUP hnU)
  have hdH : d ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) hdP
  refine ⟨d, hdP, fun hdV => heU ?_, ?_⟩
  · have e1 : e = d * n⁻¹ := by rw [hd]; group
    rw [e1]
    exact mul_mem (v1_le_u hdV) (inv_mem hnU)
  have hPd : ∀ x ∈ pCoreOf 2 (oTwoUpper H), x * d * x⁻¹ * d⁻¹ ∈ fsuV1 T V := by
    intro x hx
    have e1 : x * d * x⁻¹ * d⁻¹ = (x * e * x⁻¹ * e⁻¹) * (e * (x * n * x⁻¹ * n⁻¹) * e⁻¹) := by
      rw [hd]; group
    rw [e1, conj_v1 C heH (comm_mem_v1 C D (p_le_qh hx) hnU)]
    exact mul_mem (hPV x hx) (comm_mem_v1 C D (p_le_qh hx) hnU)
  have hKd : ∀ y ∈ oTwoUpper H, y * d * y⁻¹ * d⁻¹ ∈ fsuU T V := by
    intro y hy
    have hyH : y ∈ H := oTwoUpper_le H hy
    have hn' : y * n * y⁻¹ * n⁻¹ ∈ fsuU T V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D hyH) n).mp hnU) (inv_mem hnU)
    have e1 : y * d * y⁻¹ * d⁻¹ = (y * e * y⁻¹ * e⁻¹) * (e * (y * n * y⁻¹ * n⁻¹) * e⁻¹) := by
      rw [hd]; group
    rw [e1]
    exact mul_mem (hKe y hy) ((Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D heH) _).mp hn')
  have hKd1 : ∀ y ∈ oTwoUpper H, y * d * y⁻¹ * d⁻¹ ∈ fsuV1 T V := by
    intro y hy
    set u := y * d * y⁻¹ * d⁻¹ with hu
    have huU : u ∈ fsuU T V := hKd y hy
    set p := y * c * y⁻¹ * c⁻¹ with hp
    have hpP : p ∈ pCoreOf 2 (oTwoUpper H) := comm_c_mem_p C D hy
    have hcuU : c * u * c⁻¹ ∈ fsuU T V := conj_c_mem_u C D huU
    set w := p * d * p⁻¹ * d⁻¹ with hw
    have hwV : w ∈ fsuV1 T V := hPd p hpP
    set w' := p * (c * u * c⁻¹) * p⁻¹ * (c * u * c⁻¹)⁻¹ with hw'
    have hw'V : w' ∈ fsuV1 T V := comm_mem_v1 C D (p_le_qh hpP) hcuU
    have hcd' : c * d * c⁻¹ = d := hcd
    have h1 : (p * c) * (u * d) * (p * c)⁻¹ = u * d := by
      have e1 : u * d = y * d * y⁻¹ := by rw [hu]; group
      have e2 : p * c = y * c * y⁻¹ := by rw [hp]; group
      rw [e1, e2]
      calc y * c * y⁻¹ * (y * d * y⁻¹) * (y * c * y⁻¹)⁻¹ = y * (c * d * c⁻¹) * y⁻¹ := by group
        _ = y * d * y⁻¹ := by rw [hcd']
    have h2 : w' * (c * u * c⁻¹) * w * d = u * d := by
      have e1 : w' * (c * u * c⁻¹) * w * d = (p * c) * (u * (c⁻¹ * d * c)) * (p * c)⁻¹ := by
        rw [hw', hw]; group
      have e2 : c⁻¹ * d * c = d := by
        calc c⁻¹ * d * c = c⁻¹ * (c * d * c⁻¹) * c := by rw [hcd']
          _ = d := by group
      rw [e1, e2, h1]
    have h3 : w' * (c * u * c⁻¹) * w = u := mul_right_cancel h2
    have e3 : c * u * c⁻¹ * u⁻¹ = w⁻¹ * w'⁻¹ := by
      have hcomm := v1_comm C (u_le_h C hcuU) (inv_mem hwV)
      calc c * u * c⁻¹ * u⁻¹ = c * u * c⁻¹ * (w' * (c * u * c⁻¹) * w)⁻¹ := by rw [h3]
        _ = (c * u * c⁻¹) * w⁻¹ * (c * u * c⁻¹)⁻¹ * w'⁻¹ := by group
        _ = w⁻¹ * w'⁻¹ := by rw [hcomm, mul_inv_cancel_right]
    exact fpf_u C D u huU (by rw [e3]; exact mul_mem (inv_mem hwV) (inv_mem hw'V))
  have hle : oTwoUpper H ≤ Subgroup.centralizer ({d} : Set G) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxH, hxo⟩ := hx
    have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hxH hxo
    have hv := hKd1 x hxK
    have hv2 : (x * d * x⁻¹ * d⁻¹) ^ 2 = 1 :=
      F7.isElemAbelian_pow_eq_one D.elem_v (Subgroup.mem_inf.mp hv).1
    have hx2 : x ^ 2 ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      set v := x * d * x⁻¹ * d⁻¹ with hvdef
      have e1 : x * d * x⁻¹ = v * d := by rw [hvdef]; group
      have e2 : x * v * x⁻¹ = v := conj_v1 C hxH hv
      have e3 : x ^ 2 * d * (x ^ 2)⁻¹ = d := by
        calc x ^ 2 * d * (x ^ 2)⁻¹ = x * (x * d * x⁻¹) * x⁻¹ := by rw [sq]; group
          _ = x * (v * d) * x⁻¹ := by rw [e1]
          _ = (x * v * x⁻¹) * (x * d * x⁻¹) := by group
          _ = v * (v * d) := by rw [e2, e1]
          _ = d := by rw [← mul_assoc, ← sq, hv2, one_mul]
      calc x ^ 2 * d = (x ^ 2 * d * (x ^ 2)⁻¹) * x ^ 2 := by group
        _ = d * x ^ 2 := by rw [e3]
    have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr hxo
    exact (Subgroup.zpowers_le.mpr hx2) (A4.mem_zpowers_pow_of_coprime hcop)
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem exists_d (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {d : G}
    (hdP : d ∈ pCoreOf 2 (oTwoUpper H)) (hdV : d ∉ fsuV1 T V)
    (hdK : ∀ y ∈ oTwoUpper H, y * d = d * y) :
    ∃ D' : Subgroup G, D' ≤ oTwoUpper H ∧ (∀ x ∈ D', ∀ y ∈ oTwoUpper H, x * y = y * x) ∧
      Nat.card D' = 4 ∧ fsuV1 T V < D' ∧ H ≤ Subgroup.normalizer (D' : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := C.hypF98.toHypF91
  have hTH : T ≤ H := le_sup_right.trans hF.L₁T_le_H
  set Y := pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hY
  have hYp : IsPGroup 2 ↥Y := (pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hV₁Y : fsuV1 T V ≤ Y := fun v hv => ⟨v1_le_p C D hv,
    Subgroup.mem_centralizer_iff.mpr fun y hy => (v1_comm C (oTwoUpper_le H hy) hv)⟩
  have hlt : fsuV1 T V < Y := lt_of_le_of_ne hV₁Y fun h => hdV (h ▸ ⟨hdP,
    Subgroup.mem_centralizer_iff.mpr fun y hy => hdK y hy⟩)
  have hcent : ∀ v ∈ fsuV1 T V, ∀ y ∈ Y, v * y = y * v := fun v hv y hy =>
    (v1_comm C ((pCoreOf_le 2 _).trans (oTwoUpper_le H) hy.1) hv).symm
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    F7.mem_normalizer_inf (le_normalizer_p (hTH ht))
      (mem_normalizer_centralizer' (le_normalizer_oTwoUpper H (hTH ht)))
  obtain ⟨D', hlt', hD'Y, hD'4, hTD'⟩ := exists_card_four_of_lt hF.sylow.2.1 hYp hlt D.card_v1
    hcent hTY D.t_v1
  have hD'c : ∀ x ∈ D', ∀ y ∈ oTwoUpper H, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hD'Y hx).2 y hy).symm
  refine ⟨D', fun x hx => (pCoreOf_le 2 _) (hD'Y hx).1, hD'c, hD'4, hlt', ?_⟩
  rw [C.eq_kt]
  refine sup_le (fun y hy => mem_normalizer_of_forall_conj (Q := oTwoUpper H)
    (fun y hy x hx => ?_) hy) hTD'
  rw [← hD'c x hx y hy, mul_inv_cancel_right]
  exact hx

end CFSG.Quasithin.H13.S4
