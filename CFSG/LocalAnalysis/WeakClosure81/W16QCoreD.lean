module

public import CFSG.LocalAnalysis.WeakClosure81.W16QCfg

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace KTCfg16

variable {U V₀ V I K T Q : Subgroup G}

private lemma w16q_mem_sup_of_comm {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hA : A ≤ Subgroup.centralizer (B : Set G) :=
    fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hN : A ≤ Subgroup.normalizer (B : Set G) :=
    le_trans hA (Subgroup.centralizer_le_normalizer (B : Set G))
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right A B hN
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← hcoe]
    exact hx
  exact Set.mem_mul.mp hx'

private lemma w16q_comm_of_sq_one {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx]

private lemma w16q_C_le_centralizer_V (h : KTCfg16 U V₀ V I K T Q) :
    T ⊓ centralizer (K : Set G) ≤ centralizer (V : Set G) :=
  le_trans inf_le_right (Subgroup.centralizer_le h.V_le_K)

private lemma w16q_C_le_centralizer_I (h : KTCfg16 U V₀ V I K T Q) :
    T ⊓ centralizer (K : Set G) ≤ centralizer (I : Set G) :=
  le_trans inf_le_right (Subgroup.centralizer_le h.I_le_K)

private lemma w16q_comm_I_C (h : KTCfg16 U V₀ V I K T Q) :
    ∀ i ∈ I, ∀ c ∈ T ⊓ centralizer (K : Set G), i * c = c * i :=
  fun i hi c hc => Subgroup.mem_centralizer_iff.mp hc.2 i (h.I_le_K hi)

private lemma w16q_comm_V_C (h : KTCfg16 U V₀ V I K T Q) :
    ∀ v ∈ V, ∀ c ∈ T ⊓ centralizer (K : Set G), v * c = c * v :=
  fun v hv c hc => Subgroup.mem_centralizer_iff.mp (w16q_C_le_centralizer_V h hc) v hv

theorem I_inf_centralizer_le (h : KTCfg16 U V₀ V I K T Q) :
    I ⊓ centralizer (V : Set G) ≤ U ⊔ V₀ := by
  obtain ⟨v, hv, hvU⟩ := Set.not_subset.mp h.not_le
  intro w hw
  exact h.mem_of_comm v hv hvU w hw.1 (Subgroup.mem_centralizer_iff.mp hw.2 v hv)

theorem V_inf_centralizer_le (h : KTCfg16 U V₀ V I K T Q) :
    V ⊓ centralizer (K : Set G) ≤ U := by
  intro v hv
  by_cases hvU : v ∈ U ⊔ V₀
  · obtain ⟨u, hu, w, hw, huw⟩ := w16q_mem_sup_of_comm
      (fun a ha b hb => h.comm_V a (h.le_V (Subgroup.mem_sup_left ha)) b
        (h.le_V (Subgroup.mem_sup_right hb))) hvU
    have hwC : w ∈ centralizer (K : Set G) := by
      have hw_eq : w = u⁻¹ * v := by rw [← huw]; group
      rw [hw_eq]
      exact (centralizer (K : Set G)).mul_mem ((centralizer (K : Set G)).inv_mem (h.U_le hu)) hv.2
    have hwbot : w = 1 := by
      have hwin : w ∈ V₀ ⊓ centralizer (K : Set G) := ⟨hw, hwC⟩
      rw [h.inf_eq_bot] at hwin
      exact Subgroup.mem_bot.mp hwin
    have hvu : v = u := by rw [← huw, hwbot, mul_one]
    rw [hvu]
    exact hu
  · exfalso
    have hIle : I ≤ U ⊔ V₀ := fun w hw =>
      h.mem_of_comm v hv.1 hvU w hw (Subgroup.mem_centralizer_iff.mp hv.2 w (h.I_le_K hw)).symm
    have hIV : I ≤ V := hIle.trans h.le_V
    have hcard : Nat.card V ≤ Nat.card I := by rw [h.card_eq]
    have hIVeq : I = V := Subgroup.eq_of_le_of_card_ge hIV hcard
    exact h.not_le (hIVeq ▸ hIle)

theorem I_inf_centralizer_K_le (h : KTCfg16 U V₀ V I K T Q) :
    I ⊓ centralizer (K : Set G) ≤ U := by
  intro x hx
  have hx1 : x ∈ I ⊓ centralizer (V : Set G) :=
    ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp hx.2 v (h.V_le_K hv)⟩
  have hxV : x ∈ V := h.le_V (I_inf_centralizer_le h hx1)
  exact V_inf_centralizer_le h ⟨hxV, hx.2⟩

theorem mul_self_mem_centralizer (h : KTCfg16 U V₀ V I K T Q) {y : G} (hy : y ∈ Q) :
    y * y ∈ centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hj : k * y * k⁻¹ * y⁻¹ ∈ I := h.comm_mem y hy k hk
  have hcomm : (k * y * k⁻¹ * y⁻¹) * y = y * (k * y * k⁻¹ * y⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (h.Q_le hy) _ hj
  have hkey : k * y * k⁻¹ = (k * y * k⁻¹ * y⁻¹) * y := by group
  have hsq : ((k * y * k⁻¹ * y⁻¹) * y) * ((k * y * k⁻¹ * y⁻¹) * y) = y * y := by
    calc ((k * y * k⁻¹ * y⁻¹) * y) * ((k * y * k⁻¹ * y⁻¹) * y)
        = (k * y * k⁻¹ * y⁻¹) * (y * (k * y * k⁻¹ * y⁻¹)) * y := by group
      _ = (k * y * k⁻¹ * y⁻¹) * ((k * y * k⁻¹ * y⁻¹) * y) * y := by rw [hcomm]
      _ = ((k * y * k⁻¹ * y⁻¹) * (k * y * k⁻¹ * y⁻¹)) * (y * y) := by group
      _ = y * y := by rw [h.sq_I _ hj, one_mul]
  have hconj : k * (y * y) * k⁻¹ = y * y := by
    calc k * (y * y) * k⁻¹ = (k * y * k⁻¹) * (k * y * k⁻¹) := by group
      _ = y * y := by rw [hkey, hsq]
  have := congrArg (· * k) hconj
  simpa [mul_assoc] using this

theorem isElementaryAbelian_sup (h : KTCfg16 U V₀ V I K T Q) :
    IsElementaryAbelian 2 ↥(I ⊔ (T ⊓ centralizer (K : Set G))) := by
  have hI : IsElementaryAbelian 2 ↥I :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mpr
      ⟨h.comm_I, fun a ha => by simpa [pow_two] using h.sq_I a ha⟩
  have hC : IsElementaryAbelian 2 ↥(T ⊓ centralizer (K : Set G)) :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mpr
      ⟨fun a ha b hb => w16q_comm_of_sq_one (h.sq_C a ha) (h.sq_C b hb)
        (h.sq_C (a * b) ((T ⊓ centralizer (K : Set G)).mul_mem ha hb)),
        fun a ha => by simpa [pow_two] using h.sq_C a ha⟩
  exact CFSG.QuasithinUnique.Setup.Campbell.isElementaryAbelian_sup_of_le_centralizer hI hC
    (w16q_C_le_centralizer_I h)

theorem inf_centralizer_eq_sup (h : KTCfg16 U V₀ V I K T Q) :
    T ⊓ centralizer (V : Set G) = V ⊔ (T ⊓ centralizer (K : Set G)) := by
  apply le_antisymm
  · intro d hd
    obtain ⟨v, hv, hq⟩ := h.exists_mul d hd.1
    set q : G := v⁻¹ * d with hqdef
    have hqQ : q ∈ Q := by rw [hqdef]; exact hq
    have hqcent : q ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [hqdef]
      have hdu : d * u = u * d := (Subgroup.mem_centralizer_iff.mp hd.2 u hu).symm
      have hvu : v⁻¹ * u = u * v⁻¹ := h.comm_V v⁻¹ (V.inv_mem hv) u hu
      calc u * (v⁻¹ * d) = (u * v⁻¹) * d := by group
        _ = (v⁻¹ * u) * d := by rw [← hvu]
        _ = v⁻¹ * (u * d) := by group
        _ = v⁻¹ * (d * u) := by rw [← hdu]
        _ = v⁻¹ * d * u := by group
    obtain ⟨i, hi, c, hc, hic⟩ :=
      w16q_mem_sup_of_comm (w16q_comm_I_C h) (h.inf_centralizer_le ⟨hqQ, hqcent⟩)
    have hq_eq : q = i * c := hic.symm
    have hcV : c ∈ centralizer (V : Set G) := w16q_C_le_centralizer_V h hc
    have hiV : i ∈ I ⊓ centralizer (V : Set G) := by
      refine ⟨hi, ?_⟩
      have hi_eq : i = q * c⁻¹ := by rw [hq_eq]; group
      rw [hi_eq]
      exact (centralizer (V : Set G)).mul_mem hqcent ((centralizer (V : Set G)).inv_mem hcV)
    have hiV' : i ∈ V := h.le_V (I_inf_centralizer_le h hiV)
    have hvq : d = v * q := by rw [hqdef]; group
    have hd_eq : d = (v * i) * c := by rw [hvq, hq_eq]; group
    rw [hd_eq]
    exact Subgroup.mul_mem_sup (V.mul_mem hv hiV') hc
  · refine sup_le (le_inf h.V_le_T ?_) (le_inf inf_le_left (w16q_C_le_centralizer_V h))
    intro v hv
    exact Subgroup.mem_centralizer_iff.mpr fun u hu => h.comm_V u hu v hv

theorem card_sup_eq (h : KTCfg16 U V₀ V I K T Q) :
    Nat.card ↥(I ⊔ (T ⊓ centralizer (K : Set G))) =
      Nat.card ↥(T ⊓ centralizer (V : Set G)) := by
  have hVC : V ⊓ (T ⊓ centralizer (K : Set G)) = U := by
    apply le_antisymm
    · intro x hx
      exact V_inf_centralizer_le h ⟨hx.1, hx.2.2⟩
    · intro u hu
      exact ⟨h.le_V (Subgroup.mem_sup_left hu), h.V_le_T (h.le_V (Subgroup.mem_sup_left hu)),
        h.U_le hu⟩
  have hIC : I ⊓ (T ⊓ centralizer (K : Set G)) = U := by
    apply le_antisymm
    · intro x hx
      exact I_inf_centralizer_K_le h ⟨hx.1, hx.2.2⟩
    · intro u hu
      exact ⟨h.le_I (Subgroup.mem_sup_left hu), h.V_le_T (h.le_V (Subgroup.mem_sup_left hu)),
        h.U_le hu⟩
  have hcardVC := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V
    (T ⊓ centralizer (K : Set G)) (w16q_comm_V_C h)).1
  have hcardIC := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute I
    (T ⊓ centralizer (K : Set G)) (w16q_comm_I_C h)).1
  have h1 : Nat.card ↥(V ⊔ (T ⊓ centralizer (K : Set G))) * Nat.card ↥U =
      Nat.card V * Nat.card ↥(T ⊓ centralizer (K : Set G)) := by
    rw [← hVC]
    exact hcardVC
  have h2 : Nat.card ↥(I ⊔ (T ⊓ centralizer (K : Set G))) * Nat.card ↥U =
      Nat.card V * Nat.card ↥(T ⊓ centralizer (K : Set G)) := by
    rw [← hIC, ← h.card_eq]
    exact hcardIC
  have hmain : Nat.card ↥(V ⊔ (T ⊓ centralizer (K : Set G))) * Nat.card ↥U =
      Nat.card ↥(I ⊔ (T ⊓ centralizer (K : Set G))) * Nat.card ↥U := by
    rw [h1, h2]
  have hUpos : 0 < Nat.card ↥U := Nat.card_pos_iff.mpr ⟨⟨1, U.one_mem⟩, inferInstance⟩
  rw [inf_centralizer_eq_sup h]
  exact (Nat.mul_right_cancel hUpos hmain).symm

end KTCfg16

end CFSG.LocalAnalysis.WeakClosure81

end
