module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem pw_mul {x y : D} (hxy : x * y = y * x) (e f e' f' : ℕ) :
    (x ^ e * y ^ f) * (x ^ e' * y ^ f') = x ^ (e + e') * y ^ (f + f') := by
  have h : Commute (y ^ f) (x ^ e') := Commute.pow_pow (show Commute y x from hxy.symm) f e'
  rw [pow_add, pow_add, Commute.mul_mul_mul_comm h]

omit [Finite D] in
theorem pw_inv {x y : D} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) (e f : ℕ) :
    (x ^ e * y ^ f)⁻¹ = x ^ e * y ^ f := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h : Commute (x ^ e) (y ^ f) := Commute.pow_pow hxy e f
  rw [mul_inv_rev, ← inv_pow, ← inv_pow, hx', hy']
  exact h.symm.eq

@[expose] def NF {c : Ctx A B z V} (g : Gen c) (w : D) : Prop :=
  ∃ e₀ e₁ e₂ : ℕ, ⁅g.u₀, w⁆ = g.z₂ ^ e₁ * g.z₁ ^ e₂ ∧ ⁅g.u₁, w⁆ = g.z₂ ^ e₀ * z ^ e₂ ∧
    ⁅g.u₂, w⁆ = g.z₁ ^ e₀ * z ^ e₁

theorem Ctx.comm_mul_W (c : Ctx A B z V) {x w w' : D} (hx : x ∈ Wsub A B V) (hw : w ∈ pCoreOf 2 A)
    (hw' : w' ∈ pCoreOf 2 A) : ⁅x, w * w'⁆ = ⁅x, w⁆ * ⁅x, w'⁆ :=
  comm_mul_right_of_comm (c.V_comm (c.comm_W_Q hx hw') hw).symm

theorem Ctx.comm_inv_W (c : Ctx A B z V) {x w : D} (hx : x ∈ Wsub A B V) (hw : w ∈ pCoreOf 2 A) :
    ⁅x, w⁻¹⁆ = ⁅x, w⁆⁻¹ := by
  rw [comm_inv_right]
  have hV : ⁅x, w⁆⁻¹ ∈ V := V.inv_mem (c.comm_W_Q hx hw)
  have := c.conj_V hV ((pCoreOf 2 A).inv_mem hw)
  simpa using this

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

theorem comm10 : ⁅g.u₁, g.u₀⁆ = g.z₂ := by
  rw [← commutatorElement_inv, g.comm01]; exact c.inv_eq_self g.z₂_mem

theorem comm21 : ⁅g.u₂, g.u₁⁆ = z := by
  rw [← commutatorElement_inv, g.comm12]; exact c.inv_eq_self c.z_mem_V

theorem comm02 : ⁅g.u₀, g.u₂⁆ = g.z₁ := by
  rw [← commutatorElement_inv, g.comm20]; exact c.inv_eq_self g.z₁_mem

omit [Finite D] in
theorem nf_one : NF g 1 :=
  ⟨0, 0, 0, by simp [commutatorElement_def], by simp [commutatorElement_def],
    by simp [commutatorElement_def]⟩

theorem nf_inv {w : D} (hxw : w ∈ pCoreOf 2 A) (h : NF g w) : NF g w⁻¹ := by
  obtain ⟨e₀, e₁, e₂, h0, h1, h2⟩ := h
  refine ⟨e₀, e₁, e₂, ?_, ?_, ?_⟩
  · rw [c.comm_inv_W g.u₀_mem_W hxw, h0]
    exact pw_inv g.z₂_mul_z₂ g.z₁_mul_z₁ (c.V_comm_V g.z₂_mem g.z₁_mem) e₁ e₂
  · rw [c.comm_inv_W g.u₁_mem_W hxw, h1]
    exact pw_inv g.z₂_mul_z₂ c.z_sq (c.V_comm_V g.z₂_mem c.z_mem_V) e₀ e₂
  · rw [c.comm_inv_W g.u₂_mem_W hxw, h2]
    exact pw_inv g.z₁_mul_z₁ c.z_sq (c.V_comm_V g.z₁_mem c.z_mem_V) e₀ e₁

theorem nf_mul {w w' : D} (hw : w ∈ pCoreOf 2 A) (hw' : w' ∈ pCoreOf 2 A) (h : NF g w)
    (h' : NF g w') : NF g (w * w') := by
  obtain ⟨e₀, e₁, e₂, h0, h1, h2⟩ := h
  obtain ⟨f₀, f₁, f₂, h0', h1', h2'⟩ := h'
  refine ⟨e₀ + f₀, e₁ + f₁, e₂ + f₂, ?_, ?_, ?_⟩
  · rw [c.comm_mul_W g.u₀_mem_W hw hw', h0, h0']
    exact pw_mul (c.V_comm_V g.z₂_mem g.z₁_mem) e₁ e₂ f₁ f₂
  · rw [c.comm_mul_W g.u₁_mem_W hw hw', h1, h1']
    exact pw_mul (c.V_comm_V g.z₂_mem c.z_mem_V) e₀ e₂ f₀ f₂
  · rw [c.comm_mul_W g.u₂_mem_W hw hw', h2, h2']
    exact pw_mul (c.V_comm_V g.z₁_mem c.z_mem_V) e₀ e₁ f₀ f₁

theorem nf_V {v : D} (hv : v ∈ V) : NF g v := by
  have hvQ : v ∈ pCoreOf 2 A := c.U_le_Q (c.V_le_U hv)
  have hc : ∀ x ∈ pCoreOf 2 A, ⁅x, v⁆ = 1 := fun x hx =>
    comm_eq_one_iff.mpr (c.V_comm hv hx).symm
  exact ⟨0, 0, 0, by simp [hc _ g.u₀_mem_Q], by simp [hc _ g.u₁_mem_Q], by simp [hc _ g.u₂_mem_Q]⟩

theorem nf_V_mul₀ {v : D} (hv : v ∈ V) : NF g (v * g.u₀) := by
  refine ⟨1, 0, 0, ?_, ?_, ?_⟩ <;>
  rw [c.comm_V_mul_right hv g.u₀_mem_Q
    (by first | exact g.u₀_mem_Q | exact g.u₁_mem_Q | exact g.u₂_mem_Q)]
  · simp
  · simp [g.comm10]
  · simp [g.comm20]

theorem nf_V_mul₁ {v : D} (hv : v ∈ V) : NF g (v * g.u₁) := by
  refine ⟨0, 1, 0, ?_, ?_, ?_⟩ <;>
  rw [c.comm_V_mul_right hv g.u₁_mem_Q
    (by first | exact g.u₀_mem_Q | exact g.u₁_mem_Q | exact g.u₂_mem_Q)]
  · simp [g.comm01]
  · simp
  · simp [g.comm21]

theorem nf_V_mul₂ {v : D} (hv : v ∈ V) : NF g (v * g.u₂) := by
  refine ⟨0, 0, 1, ?_, ?_, ?_⟩ <;>
  rw [c.comm_V_mul_right hv g.u₂_mem_Q
    (by first | exact g.u₀_mem_Q | exact g.u₁_mem_Q | exact g.u₂_mem_Q)]
  · simp [g.comm02]
  · simp [g.comm12]
  · simp

theorem nf_of_mem_W {w : D} (hw : w ∈ Wsub A B V) : NF g w := by
  have key : ∀ w ∈ Wsub A B V, w ∈ pCoreOf 2 A ∧ NF g w := by
    intro w hw
    unfold Wsub conjClosure at hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g', hg', u, hu, rfl⟩ := hx
      refine ⟨pCoreOf_conj_mem hg' (c.U_le_Q hu), ?_⟩
      obtain ⟨v, hv, h | h | h | h⟩ := g.gen_form hg' hu <;> rw [h]
      · exact g.nf_V hv
      · exact g.nf_V_mul₀ hv
      · exact g.nf_V_mul₁ hv
      · exact g.nf_V_mul₂ hv
    | one => exact ⟨Subgroup.one_mem _, g.nf_one⟩
    | mul x y _ _ ihx ihy =>
      exact ⟨(pCoreOf 2 A).mul_mem ihx.1 ihy.1, g.nf_mul ihx.1 ihy.1 ihx.2 ihy.2⟩
    | inv x _ ih => exact ⟨(pCoreOf 2 A).inv_mem ih.1, g.nf_inv ih.1 ih.2⟩
  exact (key w hw).2

theorem mem_M_of_comm {q : D} (hq : q ∈ pCoreOf 2 A) (h0 : ⁅g.u₀, q⁆ = 1) (h1 : ⁅g.u₁, q⁆ = 1)
    (h2 : ⁅g.u₂, q⁆ = 1) : q ∈ Msub A B V := by
  rw [c.mem_M_iff]
  refine ⟨hq, ?_⟩
  have key : ∀ v ∈ V, ∀ u : D, q * u = u * q → q * (v * u) = (v * u) * q := fun v hv u hu => by
    calc q * (v * u) = (q * v) * u := by rw [mul_assoc]
      _ = (v * q) * u := by rw [(c.V_comm hv hq).symm]
      _ = v * (q * u) := by rw [mul_assoc]
      _ = v * (u * q) := by rw [hu]
      _ = (v * u) * q := by rw [mul_assoc]
  have hW : Wsub A B V ≤ Subgroup.centralizer ({q} : Set D) := by
    refine conjClosure_le fun g' hg' u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨v, hv, h | h | h | h⟩ := g.gen_form hg' hu <;> rw [h]
    · exact (c.V_comm hv hq).symm
    · exact key v hv _ (comm_eq_one_iff.mp h0).symm
    · exact key v hv _ (comm_eq_one_iff.mp h1).symm
    · exact key v hv _ (comm_eq_one_iff.mp h2).symm
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hW hw) q (Set.mem_singleton q)).symm

theorem mem_K_of_comm0 {k : D} (hk : k ∈ pCoreOf 2 A) (h : ⁅g.u₀, k⁆ = 1) :
    k ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  rw [c.mem_K_iff]
  refine ⟨hk, fun u hu => ?_⟩
  obtain ⟨v, hv, e | e⟩ := g.U_form hu
  · subst e; exact c.V_comm hv hk
  · subst e
    have h0 : g.u₀ * k = k * g.u₀ := comm_eq_one_iff.mp h
    calc v * g.u₀ * k = v * (g.u₀ * k) := by rw [mul_assoc]
      _ = v * (k * g.u₀) := by rw [h0]
      _ = (v * k) * g.u₀ := by rw [mul_assoc]
      _ = (k * v) * g.u₀ := by rw [c.V_comm hv hk]
      _ = k * (v * g.u₀) := by rw [mul_assoc]

include g in
theorem exists_mul_of_mem_Q {q : D} (hq : q ∈ pCoreOf 2 A) :
    ∃ w ∈ Wsub A B V, ∃ k ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B, q = w * k := by
  have hθ : ⁅g.u₀, q⁆ ∈ V := c.comm_U_Q g.u₀_mem hq
  have hex : ∃ w ∈ Wsub A B V, ⁅g.u₀, w⁆ = ⁅g.u₀, q⁆ := by
    rcases g.V_cases hθ with e | e | e | e <;> rw [e]
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · refine ⟨g.u₁ * g.u₂, Subgroup.mul_mem _ g.u₁_mem_W g.u₂_mem_W, ?_⟩
      rw [c.comm_mul_W g.u₀_mem_W g.u₁_mem_Q g.u₂_mem_Q, g.comm01, g.comm02, g.z₂_mul_z₁]
    · exact ⟨g.u₂, g.u₂_mem_W, g.comm02⟩
    · exact ⟨g.u₁, g.u₁_mem_W, g.comm01⟩
  obtain ⟨w, hw, hwq⟩ := hex
  have hwQ := c.W_le_Q hw
  refine ⟨w, hw, w⁻¹ * q, ?_, by group⟩
  apply g.mem_K_of_comm0 ((pCoreOf 2 A).mul_mem ((pCoreOf 2 A).inv_mem hwQ) hq)
  rw [c.comm_mul_W g.u₀_mem_W ((pCoreOf 2 A).inv_mem hwQ) hq, c.comm_inv_W g.u₀_mem_W hwQ, hwq]
  exact inv_mul_cancel _

end Gen

theorem Ctx.comm_Q_Q_M (c : Ctx A B z V) {x y : D} (hx : x ∈ pCoreOf 2 A)
    (hy : y ∈ pCoreOf 2 A) : ⁅x, y⁆ ∈ Msub A B V := by
  rw [c.mem_M_iff]
  have hxQ := (pCoreOf 2 A).inv_mem hx
  have hyQ := (pCoreOf 2 A).inv_mem hy
  have hxy : x * y * x⁻¹ ∈ pCoreOf 2 A := (pCoreOf 2 A).mul_mem ((pCoreOf 2 A).mul_mem hx hy) hxQ
  refine ⟨(pCoreOf 2 A).mul_mem hxy hyQ, fun w hw => ?_⟩
  have ha : ⁅w, x⁆ ∈ V := c.comm_W_Q hw hx
  have hb : ⁅w, y⁆ ∈ V := c.comm_W_Q hw hy
  have e : ⁅w, ⁅x, y⁆⁆ = 1 := by
    have h1 : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := rfl
    rw [h1, c.comm_mul_W hw hxy hyQ, c.comm_mul_W hw ((pCoreOf 2 A).mul_mem hx hy) hxQ,
      c.comm_mul_W hw hx hy, c.comm_inv_W hw hx, c.comm_inv_W hw hy, c.V_comm_V ha hb]
    group
  exact comm_eq_one_iff.mp e

theorem Ctx.sq_Q_M (c : Ctx A B z V) {x : D} (hx : x ∈ pCoreOf 2 A) : x * x ∈ Msub A B V := by
  rw [c.mem_M_iff]
  refine ⟨(pCoreOf 2 A).mul_mem hx hx, fun w hw => ?_⟩
  have e : ⁅w, x * x⁆ = 1 := by
    rw [c.comm_mul_W hw hx hx]
    exact c.V_sq (c.comm_W_Q hw hx)
  exact comm_eq_one_iff.mp e

omit [Finite D] in
theorem Ctx.comm_W_M (c : Ctx A B z V) {w m : D} (hw : w ∈ Wsub A B V) (hm : m ∈ Msub A B V) :
    ⁅w, m⁆ = 1 := by
  rw [c.mem_M_iff] at hm
  exact comm_eq_one_iff.mpr (hm.2 w hw)

end GoldAmL3E

end F6

end CFSG.Quasithin
