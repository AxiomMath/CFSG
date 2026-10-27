module

public import CFSG.Quasithin.Background.Harris.R1.QbetaData
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem conj_zg {w0 : G} (hw0S : w0 ∈ S) (hw0Q : w0 ∉ Q) :
    w0 * (g * z * g⁻¹) * w0⁻¹ = z * (g * z * g⁻¹) := by
  set z' := g * z * g⁻¹ with hz'
  have hzV : z ∈ Z ⊔ conjSub g Z := Subgroup.mem_sup_left h.hzZ
  have hz'V : z' ∈ Z ⊔ conjSub g Z := Subgroup.mem_sup_right h.zg_mem
  have hzw : z * w0 = w0 * z := Subgroup.mem_centralizer_iff.mp (h.hSZ hw0S) z h.hzZ
  have hz2 : z * z = 1 := h.z_sq
  have huV : w0 * z' * w0⁻¹ ∈ Z ⊔ conjSub g Z :=
    (Subgroup.mem_normalizer_iff.mp (h.hVN (h.vh.sp hw0S)) z').mp hz'V
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply h.hz1
    have : z = g⁻¹ * z' * g := by rw [hz']; group
    rw [this, h1]
    group
  have hu1 : w0 * z' * w0⁻¹ ≠ 1 := by
    intro h1
    apply hz'1
    have : z' = w0⁻¹ * (w0 * z' * w0⁻¹) * w0 := by group
    rw [this, h1]
    group
  have hu2 : w0 * z' * w0⁻¹ ≠ z' := by
    intro h1
    apply hw0Q
    refine h.hQV w0 hw0S (fun v hv => ?_)
    have e1 : w0 * z' = z' * w0 := by
      calc w0 * z' = (w0 * z' * w0⁻¹) * w0 := by group
        _ = z' * w0 := by rw [h1]
    rcases h.V_cases hv with h2 | h2 | h2 | h2
    · rw [h2]; simp
    · rw [h2]; exact hzw.symm
    · rw [h2]; exact e1
    · rw [h2]
      calc w0 * (z * z') = (w0 * z) * z' := by rw [mul_assoc]
        _ = (z * w0) * z' := by rw [hzw]
        _ = z * (w0 * z') := by rw [mul_assoc]
        _ = z * (z' * w0) := by rw [e1]
        _ = (z * z') * w0 := (mul_assoc _ _ _).symm
  have hu3 : w0 * z' * w0⁻¹ ≠ z := by
    intro h1
    have h2 : z' = z := by
      have : z' = w0⁻¹ * (w0 * z' * w0⁻¹) * w0 := by group
      rw [this, h1]
      calc w0⁻¹ * z * w0 = w0⁻¹ * (z * w0) := by rw [mul_assoc]
        _ = w0⁻¹ * (w0 * z) := by rw [hzw]
        _ = z := by group
    have hzg : z ∈ Z ⊓ conjSub g Z := ⟨h.hzZ, by rw [← h2]; exact h.zg_mem⟩
    rw [h.hZZ, Subgroup.mem_bot] at hzg
    exact h.hz1 hzg
  rcases h.V_cases huV with h1 | h1 | h1 | h1
  · exact absurd h1 hu1
  · exact absurd h1 hu3
  · exact absurd h1 hu2
  · exact h1

theorem V_le_of_normal {N : Subgroup G} (hNQ : N ≤ Q) (hN1 : N ≠ ⊥)
    (hNP : P ≤ Subgroup.normalizer (N : Set G)) : Z ⊔ conjSub g Z ≤ N := by
  have hQ2 : IsPGroup 2 Q := h.hS2.to_le h.vh.qs
  obtain ⟨u, huN, hu1, hu2, huc⟩ := exists_involution_central hQ2 hNQ hN1
    (fun q hq => hNP (h.vh.sp (h.vh.qs hq)))
  have huQ : u ∈ Q := hNQ huN
  have huV : u ∈ Z ⊔ conjSub g Z :=
    h.mem_V_of_mem_center huQ (fun q hq => (huc q hq).symm) hu2
  set z' := g * z * g⁻¹ with hz'
  have hconjN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N := fun p hp n hn =>
    (Subgroup.mem_normalizer_iff.mp (hNP hp) n).mp hn
  have hZN : z ∈ N → Z ⊔ conjSub g Z ≤ N := by
    intro hz
    have hz'N : z' ∈ N := hconjN g h.hg z hz
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rcases h.hZcases x hx with h1 | h1
      · rw [h1]; exact N.one_mem
      · rw [h1]; exact hz
    · rcases h.conj_cases hx with h1 | h1
      · rw [h1]; exact N.one_mem
      · rw [h1]; exact hz'N
  have hz'N : z' ∈ N → z ∈ N := by
    intro hzp
    have := hconjN g⁻¹ (P.inv_mem h.hg) z' hzp
    have e : g⁻¹ * z' * g⁻¹⁻¹ = z := by rw [hz']; group
    rwa [e] at this
  obtain ⟨w0, hw0W, hw0Q⟩ := IsConcreteLE.not_le_iff_exists.mp h.vh.wq
  have hw0S : w0 ∈ S := h.vh.ws hw0W
  rcases h.V_cases huV with h1 | h1 | h1 | h1
  · exact absurd h1 hu1
  · exact hZN (h1 ▸ huN)
  · exact hZN (hz'N (by rw [hz', ← h1]; exact huN))
  ·
    have hzw : z * w0 = w0 * z := Subgroup.mem_centralizer_iff.mp (h.hSZ hw0S) z h.hzZ
    have hwu : w0 * u * w0⁻¹ = z' := by
      rw [h1]
      have e : w0 * (z * z') * w0⁻¹ = (w0 * z * w0⁻¹) * (w0 * z' * w0⁻¹) := by group
      rw [e, h.conj_zg hw0S hw0Q]
      have e2 : w0 * z * w0⁻¹ = z := by rw [← hzw]; group
      rw [e2, ← mul_assoc, h.z_sq, one_mul]
    have := hconjN w0 (h.vh.sp hw0S) u huN
    rw [hwu] at this
    exact hZN (hz'N this)

theorem no_sq_eq_z {m : G} (hm : m ∈ conjSub g M) : m * m ≠ z := by
  intro hmz
  have hm0 : g⁻¹ * m * g ∈ M := mem_conjSub.mp hm
  obtain ⟨w, hwW, d, hdD, hwd⟩ := h.hMWD _ hm0
  have hdw : d * w = w * d := h.hDc d hdD w hwW
  have hsq : (g⁻¹ * m * g) * (g⁻¹ * m * g) = g⁻¹ * z * g := by
    have e : (g⁻¹ * m * g) * (g⁻¹ * m * g) = g⁻¹ * (m * m) * g := by group
    rw [e, hmz]
  have hsq2 : (g⁻¹ * m * g) * (g⁻¹ * m * g) = (w * w) * (d * d) := by
    rw [hwd]
    calc w * d * (w * d) = w * (d * w) * d := by simp only [mul_assoc]
      _ = w * (w * d) * d := by rw [hdw]
      _ = (w * w) * (d * d) := by simp only [mul_assoc]
  have hww : w * w ∈ Z := h.hsqW w hwW
  have hzW' : g⁻¹ * z * g ∈ W := by
    have := h.vh.zw g⁻¹ (P.inv_mem h.hg)
    simpa using this (mul_mem_conjSub (g := g⁻¹) h.hzZ)
  have hdd : d * d ∈ D ⊓ W := by
    refine ⟨D.mul_mem hdD hdD, ?_⟩
    have e : d * d = (w * w)⁻¹ * (g⁻¹ * z * g) := by
      have h1 : (w * w) * (d * d) = g⁻¹ * z * g := by rw [← hsq2, hsq]
      calc d * d = (w * w)⁻¹ * ((w * w) * (d * d)) := by group
        _ = (w * w)⁻¹ * (g⁻¹ * z * g) := by rw [h1]
    rw [e]
    exact W.mul_mem (W.inv_mem (VertT.Z_le_W h.vh hww)) hzW'
  have hddZ : d * d ∈ Z := h.hDW hdd
  have hzhat : g⁻¹ * z * g ∈ Z := by
    have h1 : (w * w) * (d * d) = g⁻¹ * z * g := by rw [← hsq2, hsq]
    rw [← h1]
    exact Z.mul_mem hww hddZ
  have hzg : z ∈ Z ⊓ conjSub g Z := by
    refine ⟨h.hzZ, ?_⟩
    have := mul_mem_conjSub (g := g) hzhat
    have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rwa [e] at this
  rw [h.hZZ, Subgroup.mem_bot] at hzg
  exact h.hz1 hzg

theorem Tb_normal : P ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) :=
  VertT.P_le_normalizer_T h.vh h.hMS h.hg h.hyg h.hyS

theorem Tb_le_Q : M ⊓ conjSub g M ≤ Q := VertT.T_le_Q h.vh h.hMS h.hg h.hyg h.hyS

theorem comm_Tb_V {t v : G} (ht : t ∈ M ⊓ conjSub g M) (hv : v ∈ Z ⊔ conjSub g Z) :
    t * v = v * t := by
  have h1 := Subgroup.commutator_mem_commutator ht hv
  rw [VertT.commutator_T_V_eq_bot h.vh h.hg h.hZZ, Subgroup.mem_bot, commutatorElement_def] at h1
  calc t * v = (t * v * t⁻¹ * v⁻¹) * (v * t) := by group
    _ = v * t := by rw [h1, one_mul]

omit h in
theorem le_normalizer_of_comm {H L : Subgroup G} (hc : ∀ x ∈ H, ∀ a ∈ L, x * a = a * x) :
    H ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have e : ∀ x' ∈ H, ∀ a' ∈ L, x' * a' * x'⁻¹ = a' := fun x' hx' a' ha' => by
    rw [hc x' hx' a' ha']
    group
  constructor
  · intro ha
    rw [e x hx a ha]
    exact ha
  · intro ha
    have := e x⁻¹ (H.inv_mem hx) _ ha
    have e2 : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
    rw [e2] at this
    rwa [← this] at ha

theorem X0V_normal :
    P ≤ Subgroup.normalizer
      (((D ⊓ (M ⊓ conjSub g M)) ⊔ (Z ⊔ conjSub g Z) : Subgroup G) : Set G) := by
  set Tb := M ⊓ conjSub g M with hTb
  set X0 := D ⊓ Tb with hX0
  set V := Z ⊔ conjSub g Z with hV
  have hQX : Q ≤ Subgroup.normalizer (X0 : Set G) :=
    F7.le_normalizer_inf (fun q hq => h.hDS (h.vh.qs hq))
      (fun q hq => h.Tb_normal (h.vh.sp (h.vh.qs hq)))
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := fun q hq => h.hVN (h.vh.sp (h.vh.qs hq))
  have hVX : V ≤ Subgroup.normalizer (X0 : Set G) :=
    le_normalizer_of_comm (fun v hv a ha => (h.comm_Tb_V ha.2 hv).symm)
  have hWX : W ≤ Subgroup.normalizer (X0 : Set G) :=
    le_normalizer_of_comm (fun w hw a ha => (h.hDc a ha.1 w hw).symm)
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := fun w hw =>
    h.hVN (h.vh.sp (h.vh.ws hw))
  have hQK : Q ≤ Subgroup.normalizer ((X0 ⊔ V : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hQX hQV
  have hWK : W ≤ Subgroup.normalizer ((X0 ⊔ V : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hWX hWV
  have hmem : ∀ k ∈ X0 ⊔ V, ∃ a ∈ X0, ∃ v ∈ V, k = a * v := fun k hk =>
    (F1.mem_sup_iff_exists_mul_of_normalizes hVX).mp hk
  have hconjg : ∀ w' ∈ conjSub g W, ∀ k ∈ X0 ⊔ V, w' * k * w'⁻¹ ∈ X0 ⊔ V := by
    intro w' hw' k hk
    obtain ⟨a, ha, v, hv, rfl⟩ := hmem k hk
    have hw'P : w' ∈ P := conjSub_le_of_mem (h.vh.ws.trans h.vh.sp) h.hg hw'
    have hcZg : a * w' * a⁻¹ * w'⁻¹ ∈ conjSub g Z := by
      have h1 := Subgroup.commutator_mem_commutator ha.2 hw'
      rw [commutatorElement_def] at h1
      exact VertT.commutator_T_conjSub_W_le h.vh h1
    have hcV : a * w' * a⁻¹ * w'⁻¹ ∈ V := Subgroup.mem_sup_right hcZg
    have hv' : w' * v * w'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h.hVN hw'P) v).mp hv
    have e1 : w' * a * w'⁻¹ = (a * w' * a⁻¹ * w'⁻¹)⁻¹ * a := by group
    have hca : (a * w' * a⁻¹ * w'⁻¹)⁻¹ * a = a * (a * w' * a⁻¹ * w'⁻¹)⁻¹ :=
      (h.comm_Tb_V ha.2 (V.inv_mem hcV)).symm
    have e2 : w' * (a * v) * w'⁻¹ = a * ((a * w' * a⁻¹ * w'⁻¹)⁻¹ * (w' * v * w'⁻¹)) := by
      calc w' * (a * v) * w'⁻¹ = (w' * a * w'⁻¹) * (w' * v * w'⁻¹) := by group
        _ = ((a * w' * a⁻¹ * w'⁻¹)⁻¹ * a) * (w' * v * w'⁻¹) := by rw [e1]
        _ = (a * (a * w' * a⁻¹ * w'⁻¹)⁻¹) * (w' * v * w'⁻¹) := by rw [hca]
        _ = a * ((a * w' * a⁻¹ * w'⁻¹)⁻¹ * (w' * v * w'⁻¹)) := by rw [mul_assoc]
    rw [e2]
    exact (X0 ⊔ V).mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (V.mul_mem (V.inv_mem hcV) hv'))
  have hgW : conjSub g W ≤ Subgroup.normalizer ((X0 ⊔ V : Subgroup G) : Set G) := by
    have key : ∀ w' ∈ conjSub g W, conjSub w' (X0 ⊔ V) ≤ X0 ⊔ V := by
      intro w' hw' x hx
      have hx' : w'⁻¹ * x * w' ∈ X0 ⊔ V := mem_conjSub.mp hx
      have := hconjg w' hw' _ hx'
      have e : w' * (w'⁻¹ * x * w') * w'⁻¹ = x := by group
      rwa [e] at this
    intro w' hw'
    exact F7.mem_normalizer_of_conj_le (key w' hw') (key w'⁻¹ ((conjSub g W).inv_mem hw'))
  have hS : S ≤ Subgroup.normalizer ((X0 ⊔ V : Subgroup G) : Set G) := by
    rw [← VertT.S_eq h.vh]
    exact sup_le hQK hWK
  have hSg : conjSub g S ≤ Subgroup.normalizer ((X0 ⊔ V : Subgroup G) : Set G) := by
    have hgS : conjSub g S = Q ⊔ conjSub g W := by
      rw [← VertT.S_eq h.vh, conjSub_sup, conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)]
    rw [hgS]
    exact sup_le hQK hgW
  rw [← VertT.sup_conjSub_S h.vh h.hg h.hyg h.hyS]
  exact sup_le hS hSg

theorem N1_le :
    ⁅Q, (D ⊓ (M ⊓ conjSub g M)) ⊔ (Z ⊔ conjSub g Z)⁆ ≤ D ⊓ (M ⊓ conjSub g M) := by
  set Tb := M ⊓ conjSub g M with hTb
  set X0 := D ⊓ Tb with hX0
  set V := Z ⊔ conjSub g Z with hV
  have hQX : Q ≤ Subgroup.normalizer (X0 : Set G) :=
    F7.le_normalizer_inf (fun q hq => h.hDS (h.vh.qs hq))
      (fun q hq => h.Tb_normal (h.vh.sp (h.vh.qs hq)))
  have hVX : V ≤ Subgroup.normalizer (X0 : Set G) :=
    le_normalizer_of_comm (fun v hv a ha => (h.comm_Tb_V ha.2 hv).symm)
  rw [Subgroup.commutator_le]
  intro q hq k hk
  obtain ⟨a, ha, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVX).mp hk
  have hqv : q * v = v * q := h.hVQ v hv q hq
  have e : ⁅q, a * v⁆ = (q * a * q⁻¹) * a⁻¹ := by
    rw [commutatorElement_def]
    calc q * (a * v) * q⁻¹ * (a * v)⁻¹ = q * a * (v * q⁻¹) * v⁻¹ * a⁻¹ := by group
      _ = q * a * (q⁻¹ * v) * v⁻¹ * a⁻¹ := by
          have : v * q⁻¹ = q⁻¹ * v := by
            have h1 : q * v = v * q := hqv
            calc v * q⁻¹ = q⁻¹ * (q * v) * q⁻¹ := by group
              _ = q⁻¹ * (v * q) * q⁻¹ := by rw [h1]
              _ = q⁻¹ * v := by group
          rw [this]
      _ = (q * a * q⁻¹) * a⁻¹ := by group
  rw [e]
  have hqa : q * a * q⁻¹ ∈ X0 := (Subgroup.mem_normalizer_iff.mp (hQX hq) a).mp ha
  exact X0.mul_mem hqa (X0.inv_mem ha)

theorem N1_normal :
    P ≤ Subgroup.normalizer
      ((⁅Q, (D ⊓ (M ⊓ conjSub g M)) ⊔ (Z ⊔ conjSub g Z)⁆ : Subgroup G) : Set G) := by
  intro p hp
  apply Vert.mem_normalizer_of_conjSub_eq
  rw [← conjSub_commutator, conjSub_eq_of_mem_normalizer (h.vh.qn hp),
    conjSub_eq_of_mem_normalizer (h.X0V_normal hp)]

theorem D_inf_conjSub_M_le_Z : D ⊓ conjSub g M ≤ Z := by
  set Tb := M ⊓ conjSub g M with hTb
  set X0 := D ⊓ Tb with hX0
  set V := Z ⊔ conjSub g Z with hV
  have hQ2 : IsPGroup 2 Q := h.hS2.to_le h.vh.qs
  have hVQ : V ≤ Q := h.V_le_Q
  have hX0Q : X0 ≤ Q := fun x hx => h.Tb_le_Q hx.2
  have hKQ : X0 ⊔ V ≤ Q := sup_le hX0Q hVQ
  have hN1 : ⁅Q, X0 ⊔ V⁆ = ⊥ := by
    by_contra hne
    have hVN := h.V_le_of_normal (N := ⁅Q, X0 ⊔ V⁆) (Vert.commutator_le_of_le le_rfl hKQ) hne
      h.N1_normal
    have hz'X : g * z * g⁻¹ ∈ X0 := h.N1_le (hVN (Subgroup.mem_sup_right h.zg_mem))
    have hz'W : g * z * g⁻¹ ∈ W := h.V_le_W (Subgroup.mem_sup_right h.zg_mem)
    have hz'Z : g * z * g⁻¹ ∈ Z := h.hDW ⟨hz'X.1, hz'W⟩
    have hzg : g * z * g⁻¹ ∈ Z ⊓ conjSub g Z := ⟨hz'Z, h.zg_mem⟩
    rw [h.hZZ, Subgroup.mem_bot] at hzg
    apply h.hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, hzg]
    group
  have hX0c : ∀ x ∈ X0, ∀ q ∈ Q, q * x = x * q := by
    intro x hx q hq
    have h1 := Subgroup.commutator_mem_commutator hq (Subgroup.mem_sup_left hx : x ∈ X0 ⊔ V)
    rw [hN1, Subgroup.mem_bot, commutatorElement_def] at h1
    calc q * x = (q * x * q⁻¹ * x⁻¹) * (x * q) := by group
      _ = x * q := by rw [h1, one_mul]
  have hX0sq : ∀ x ∈ X0, x * x = 1 := by
    intro x hx
    by_contra hx2
    have hy : x * x ∈ X0 := X0.mul_mem hx hx
    have hyS : x * x ∈ S := h.vh.qs (hX0Q hy)
    obtain ⟨u, huy, hu1, hu2, -⟩ := exists_involution_central
      (R := Subgroup.zpowers (x * x)) (D := Subgroup.zpowers (x * x))
      (h.hS2.to_le (Subgroup.zpowers_le.mpr hyS))
      le_rfl (fun hbot => hx2 (by
        have : x * x ∈ Subgroup.zpowers (x * x) := Subgroup.mem_zpowers _
        rw [hbot, Subgroup.mem_bot] at this
        exact this))
      Subgroup.le_normalizer
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp huy
    have e : u = x ^ n * x ^ n := by
      rw [← hn]
      calc (x * x) ^ n = (x ^ (2 : ℤ)) ^ n := by rw [zpow_two]
        _ = x ^ ((2 : ℤ) * n) := (zpow_mul x 2 n).symm
        _ = x ^ (n * 2) := by rw [mul_comm]
        _ = (x ^ n) ^ (2 : ℤ) := zpow_mul x n 2
        _ = x ^ n * x ^ n := zpow_two _
    have hxn : x ^ n ∈ X0 := X0.zpow_mem hx n
    have huX : u ∈ X0 := by rw [e]; exact X0.mul_mem hxn hxn
    have huV : u ∈ V := h.mem_V_of_mem_center (hX0Q huX) (fun q hq => hX0c u huX q hq) hu2
    have huZ : u ∈ Z := h.hDW ⟨huX.1, h.V_le_W huV⟩
    rcases h.hZcases u huZ with h1 | h1
    · exact hu1 h1
    · exact h.no_sq_eq_z hxn.2.2 (e.symm.trans h1)
  intro x hx
  have hxX0 : x ∈ X0 := ⟨hx.1, h.hD hx.1, hx.2⟩
  have hxV : x ∈ V :=
    h.mem_V_of_mem_center (hX0Q hxX0) (fun q hq => hX0c x hxX0 q hq) (hX0sq x hxX0)
  exact h.hDW ⟨hx.1, h.V_le_W hxV⟩

end QD

end CFSG.Quasithin.Background.Harris.R1
