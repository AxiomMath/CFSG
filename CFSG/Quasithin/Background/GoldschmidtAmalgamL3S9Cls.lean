module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YNA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem conj_comm_eq_inv_of_sq {x c : D} (hx : x * x = 1) :
    x * (x * c * x⁻¹ * c⁻¹) * x⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ := by
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  calc x * (x * c * x⁻¹ * c⁻¹) * x⁻¹ = (x * x) * c * x⁻¹ * c⁻¹ * x⁻¹ := by group
    _ = c * x⁻¹ * c⁻¹ * x⁻¹ := by rw [hx, one_mul]
    _ = c * x * c⁻¹ * x⁻¹ := by rw [hinv]
    _ = (x * c * x⁻¹ * c⁻¹)⁻¹ := by group

omit [Finite D] in
theorem conj_comm_fixed_of_sq {x c : D} (hx : x * x = 1)
    (hw : (x * c * x⁻¹ * c⁻¹) * (x * c * x⁻¹ * c⁻¹) = 1) :
    x * (x * c * x⁻¹ * c⁻¹) * x⁻¹ = x * c * x⁻¹ * c⁻¹ := by
  rw [conj_comm_eq_inv_of_sq hx]
  exact inv_eq_of_mul_eq_one_right hw

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem inf_Vv_le_sup_Theta {β a a' t t' : CosetGeom (A ⊔ B) A B}
    (hU : Nat.card (conjClosure V B) = 16) (hβ : vtype β = true)
    (hβa : (graph (A ⊔ B) A B).Adj β a) (hβa' : (graph (A ⊔ B) A B).Adj β a')
    (hat : (graph (A ⊔ B) A B).Adj a t)
    (ha't' : (graph (A ⊔ B) A B).Adj a' t') (ht'β : t' ≠ β)
    (hX4 : Nat.card ↥(Vv V t ⊓ Vv V t') ≤ 4)
    {x₀ : D} (hx₀a' : x₀ ∈ ballStab 1 a') (hx₀t : x₀ ∈ stab t) (hx₀t' : x₀ ∈ stab t')
    (hx₀n : x₀ ∉ ballStab 1 t') (hx₀sq : x₀ * x₀ = 1) :
    Vv V t ⊓ Vv V t' ≤ Vv V a' ⊔ Theta z V a' t' := by
  have ha : vtype a = false := vtype_eq_false_of_adj hβa hβ
  have ha' : vtype a' = false := vtype_eq_false_of_adj hβa' hβ
  have ht' : vtype t' = true := vtype_eq_true_of_adj ha't' ha'
  have hab : IsElemAbelian 2 (Vv V t') := h.isElemAbelian_Vv_B ht'
  have hU' : Nat.card ↥(Vv V t') = 16 := h.card_Vv_B_of_card hU ht'
  have hΘc : Nat.card ↥(Theta z V a' t') = 4 := h.card_Theta ha' ha't' hU'
  have hΘle : Theta z V a' t' ≤ Vv V t' := h.Theta_le_Vv ha' ha't'
  have hΘV : Theta z V a' t' ⊓ Vv V a' = Zv z t' := h.Theta_inf_Vv ha' ha't' hU'
  have hVa'U : Vv V a' ≤ Vv V t' := Vv_le_Vv_of_adj ha't' ha'
  have hx₀st : x₀ ∈ stab a' ⊓ stab t' := ⟨ballStab_le_stab 1 a' hx₀a', hx₀t'⟩
  have hcenV : ∀ w ∈ Vv V a', x₀ * w * x₀⁻¹ = w := fun w hw =>
    h.ballStab_one_le_centralizer_Vv ha' hx₀a' hw
  have hx₀Vt' : ∀ c ∈ Vv V t', x₀ * c * x₀⁻¹ ∈ Vv V t' := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Vv h.natural.reduced.2.1 t' hx₀t') c).mp hc
  have hx₀Vt : ∀ c ∈ Vv V t, x₀ * c * x₀⁻¹ ∈ Vv V t := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Vv h.natural.reduced.2.1 t hx₀t) c).mp hc
  set Cx : Subgroup D := Subgroup.centralizer ({x₀} : Set D) with hCx
  have hmemCx : ∀ g : D, x₀ * g * x₀⁻¹ = g → g ∈ Cx := fun g hg => by
    rw [hCx, Subgroup.mem_centralizer_singleton_iff]
    calc g * x₀ = (x₀ * g * x₀⁻¹) * x₀ := by rw [hg]
      _ = x₀ * g := by group
  have hcomm_of : ∀ g ∈ Cx, x₀ * g * x₀⁻¹ = g := fun g hg => by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc x₀ * g * x₀⁻¹ = (g * x₀) * x₀⁻¹ := by rw [← this]
      _ = g := by group
  obtain ⟨u, hu, hdu⟩ : ∃ u ∈ Vv V t', x₀ * u * x₀⁻¹ * u⁻¹ ∉ Zv z t' := by
    by_contra hcon
    push Not at hcon
    exact hx₀n (h.mem_ballStab_one_of_commutator ht' hx₀t' hcon)
  set d : D := x₀ * u * x₀⁻¹ * u⁻¹ with hd
  have hdΘ : d ∈ Theta z V a' t' := comm_mem_Theta hx₀st hu z
  have hdU : d ∈ Vv V t' := hΘle hdΘ
  have hdd : d * d = 1 := by
    have := hab.2 d hdU
    rwa [pow_two] at this
  have hd1 : d ≠ 1 := fun e => hdu (e ▸ (Zv z t').one_mem)
  have hdCx : d ∈ Cx := hmemCx d (conj_comm_fixed_of_sq hx₀sq hdd)
  have hdV : d ∉ Vv V a' := fun hdV => hdu (by
    have : d ∈ Theta z V a' t' ⊓ Vv V a' := ⟨hdΘ, hdV⟩
    rwa [hΘV] at this)
  have hZΘ : Zv z t' ≤ Theta z V a' t' := le_sup_left
  have hZV : Zv z t' ≤ Vv V a' := h.Zv_le_Vv ha't' ha'
  have hΘeq : Theta z V a' t' = Zv z t' ⊔ Subgroup.zpowers d := by
    have hle : Zv z t' ⊔ Subgroup.zpowers d ≤ Theta z V a' t' :=
      sup_le hZΘ (Subgroup.zpowers_le.mpr hdΘ)
    have h2 : 2 * Nat.card ↥(Zv z t') ≤ Nat.card ↥(Zv z t' ⊔ Subgroup.zpowers d) :=
      two_mul_card_le_of_lt le_sup_left (k := d)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) (fun hdZ => hdu hdZ)
    rw [h.card_Zv ht'] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hΘc]; omega)).symm
  have hΘCx : Theta z V a' t' ≤ Cx := by
    rw [hΘeq]
    refine sup_le (fun g hg => hmemCx g (hcenV g (hZV hg))) ?_
    exact Subgroup.zpowers_le.mpr hdCx
  have hVCx : Vv V a' ≤ Cx := fun g hg => hmemCx g (hcenV g hg)
  set Q : Subgroup D := Vv V a' ⊔ Theta z V a' t' with hQ
  have hQCx : Q ≤ Cx := sup_le hVCx hΘCx
  have hQU : Q ≤ Vv V t' := sup_le hVa'U hΘle
  have hQ8 : 8 ≤ Nat.card ↥Q := by
    have := two_mul_card_le_of_lt (le_sup_left : Vv V a' ≤ Q) (k := d)
      (Subgroup.mem_sup_right hdΘ) hdV
    rw [h.card_Vv_A ha'] at this
    omega
  have hC8 : Nat.card ↥(Vv V t' ⊓ Cx : Subgroup D) ≤ 8 := by
    have hle : (Vv V t' ⊓ Cx : Subgroup D) ≤ Vv V t' := inf_le_left
    have hdvd : Nat.card ↥(Vv V t' ⊓ Cx : Subgroup D) ∣ 16 := hU' ▸ Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(Vv V t' ⊓ Cx : Subgroup D) ≠ 16 := fun e => by
      have heq : (Vv V t' ⊓ Cx : Subgroup D) = Vv V t' :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hU', e])
      have huC : u ∈ (Vv V t' ⊓ Cx : Subgroup D) := by
        rw [heq]
        exact hu
      have := hcomm_of u huC.2
      apply hd1
      rw [hd]
      calc x₀ * u * x₀⁻¹ * u⁻¹ = u * u⁻¹ := by rw [this]
        _ = 1 := by group
    have hle16 : Nat.card ↥(Vv V t' ⊓ Cx : Subgroup D) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(Vv V t' ⊓ Cx : Subgroup D) = n at hdvd hne hle16 ⊢
    interval_cases n <;> omega
  have hQeq : Vv V t' ⊓ Cx = Q :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hQU hQCx) (by omega)).symm
  have hZβ : Zv z β ≤ Vv V t ⊓ Vv V t' := by
    refine le_inf ?_ ?_
    · exact (h.Zv_le_Vv hβa.symm ha).trans (Vv_le_Vv_of_adj hat ha)
    · exact (h.Zv_le_Vv hβa'.symm ha').trans hVa'U
  have hZβV : Zv z β ≤ Vv V a' := h.Zv_le_Vv hβa'.symm ha'
  have hXCx : Vv V t ⊓ Vv V t' ≤ Cx := by
    intro c hc
    by_contra hcn
    set e : D := x₀ * c * x₀⁻¹ * c⁻¹ with he
    have hecx : x₀ * c * x₀⁻¹ ≠ c := fun hh => hcn (hmemCx c hh)
    have he1 : e ≠ 1 := fun hh => hecx (mul_inv_eq_one.mp hh)
    have heX : e ∈ Vv V t ⊓ Vv V t' :=
      (Vv V t ⊓ Vv V t').mul_mem ⟨hx₀Vt c hc.1, hx₀Vt' c hc.2⟩ ((Vv V t ⊓ Vv V t').inv_mem hc)
    have heΘ : e ∈ Theta z V a' t' := comm_mem_Theta hx₀st hc.2 z
    have heZ : e ∉ Zv z β := fun heZ => by
      have h1 : e ∈ Theta z V a' t' ⊓ Vv V a' := ⟨heΘ, hZβV heZ⟩
      rw [hΘV] at h1
      have h2 : e ∈ Zv z β ⊓ Zv z t' := ⟨heZ, h1⟩
      rw [h.inf_Zv_eq_bot ha' hβa'.symm ha't' (Ne.symm ht'β)] at h2
      exact he1 (Subgroup.mem_bot.mp h2)
    have hee : e * e = 1 := by
      have := hab.2 e heX.2
      rwa [pow_two] at this
    have heCx : e ∈ Cx := hmemCx e (conj_comm_fixed_of_sq hx₀sq hee)
    have hL : Zv z β ⊔ Subgroup.zpowers e ≤ Vv V t ⊓ Vv V t' :=
      sup_le hZβ (Subgroup.zpowers_le.mpr heX)
    have hL4 : 2 * Nat.card ↥(Zv z β) ≤ Nat.card ↥(Zv z β ⊔ Subgroup.zpowers e) :=
      two_mul_card_le_of_lt le_sup_left (k := e)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)) heZ
    rw [h.card_Zv hβ] at hL4
    have hLX : Zv z β ⊔ Subgroup.zpowers e = Vv V t ⊓ Vv V t' :=
      Subgroup.eq_of_le_of_card_ge hL (by omega)
    have hLCx : Zv z β ⊔ Subgroup.zpowers e ≤ Cx :=
      sup_le (fun g hg => hmemCx g (hcenV g (hZβV hg))) (Subgroup.zpowers_le.mpr heCx)
    exact hcn (hLCx (hLX ▸ hc))
  intro c hc
  have : c ∈ Vv V t' ⊓ Cx := ⟨hc.2, hXCx hc⟩
  rw [hQeq] at this
  exact this

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
