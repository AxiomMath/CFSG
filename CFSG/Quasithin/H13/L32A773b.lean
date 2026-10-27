module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32A774j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def stG1 : H6.Γ := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

@[expose] def stG2 : H6.Γ := ⟨!![0, 1, 0; 1, 1, 1; 0, 0, 1], by decide⟩

theorem stG1_mem : stG1 ∈ H6.Ll ∧ stG1 ^ 3 = 1 := by decide

theorem stG2_mem : stG2 ∈ H6.Ll ∧ stG2 ^ 3 = 1 := by decide

@[expose] def stWB (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 0; 0, 0, 0; A 2 0 + A 2 1 + A 0 0 + A 1 1, A 0 1 + A 1 0 + A 2 0 + A 1 1, 0]

@[expose] def stWC (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, A 1 2 + A 1 1; A 0 1, A 0 1 + A 0 0, A 0 1 + A 0 2 + A 1 2 + A 1 1;
    A 0 0 + A 1 1, A 0 1 + A 1 0 + A 1 1, A 0 1 + A 0 0]

theorem st_eq_sum_aux : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (stWB A).trace = 0 ∧ (stWC A).trace = 0 ∧
      A = (RuType.stAct stG1 (stWB A) - stWB A) + (RuType.stAct stG2 (stWC A) - stWC A) := by
  decide +kernel

theorem st_eq_sum (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : RuType.IsTraceZero A) :
    ∃ B C : Matrix (Fin 3) (Fin 3) (ZMod 2), RuType.IsTraceZero B ∧ RuType.IsTraceZero C ∧
      A = (RuType.stAct stG1 B - B) + (RuType.stAct stG2 C - C) :=
  ⟨stWB A, stWC A, (st_eq_sum_aux A hA).1, (st_eq_sum_aux A hA).2.1, (st_eq_sum_aux A hA).2.2⟩

omit [Group G] [Finite G] in
theorem pow_four_pow {M : Type} [Monoid M] {g : M} (hg : g ^ 3 = 1) (e : ℕ) : g ^ 4 ^ e = g := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, pow_mul, ih, show g ^ 4 = g ^ 3 * g by rw [← pow_succ], hg, one_mul]

theorem exists_mem_l1_of {L V₁ : Subgroup G} {θ : ↥L →* H6.Γ} (hθs : Function.Surjective θ)
    (hθL : ∀ l : ↥L, θ l ∈ H6.Ll → (l : G) ∈ Subgroup.normalizer (V₁ : Set G)) {g : H6.Γ}
    (hg : g ∈ H6.Ll) (hg3 : g ^ 3 = 1) : ∃ l : ↥L, (l : G) ∈ L₁Of L V₁ ∧ θ l = g := by
  obtain ⟨l, rfl⟩ := hθs g
  obtain ⟨e, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hθ : θ (l ^ 2 ^ (2 * e)) = θ l := by
    rw [map_pow, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, pow_four_pow hg3]
  refine ⟨l ^ 2 ^ (2 * e), Subgroup.subset_closure ⟨⟨(l ^ 2 ^ (2 * e)).2, hθL _ (hθ ▸ hg)⟩,
    m, hm, ?_⟩, hθ⟩
  have h1 : (l ^ 2 ^ (2 * e)) ^ m = 1 := by
    rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.mp]
    rw [hlm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact Nat.mul_dvd_mul_right (by
      rw [show (4 : ℕ) ^ e = 2 ^ e * 2 ^ e by rw [← mul_pow]; norm_num]
      exact Dvd.intro _ rfl) m
  have h2 := congrArg Subtype.val h1
  simpa using h2

omit [Finite G] in
theorem comm_mem_l1 {L V₁ : Subgroup G} {x g : G} (hx : x ∈ L₁Of L V₁) (hgL : g ∈ L)
    (hgN : g ∈ Subgroup.normalizer (V₁ : Set G)) : x * g * x⁻¹ * g⁻¹ ∈ L₁Of L V₁ := by
  rw [show x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) by group]
  exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp
    (le_normalizer_oTwoRes _ (Subgroup.mem_inf.mpr ⟨hgL, hgN⟩)) _).mp (inv_mem hx))

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem exists_basis_l1 : ∃ (V₂ : Subgroup G) (z a b x y : G), A6.IsV2 T V V₂ ∧
    z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧ b ∈ V ∧ b ∉ V₂ ∧
    x ∈ L₁Of L (fsuV1 T V) ∧ y ∈ L₁Of L (fsuV1 T V) ∧ x * a * x⁻¹ = b ∧
    x * b * x⁻¹ = a * b ∧ y * a * y⁻¹ = z * a := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe (v_le_fsuU ha) (v_le_fsuU hb)
  have hV2' : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (v_le_fsuU ha)
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x₁, hx₁L, hx₁3, hx₁z, hx₁a, hx₁b⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  obtain ⟨x₂, hx₂L, hx₂3, hx₂z, hx₂a, hx₂b⟩ := S14.exists_rot hzV haV' (mul_mem hzV hb)
    (fun h => haV (h ▸ one_mem _))
    (fun h => hbV (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem hzV₂))
    (fun h => haV (h ▸ hz0))
    (fun h => hbV (by
      have : b = 1 := by
        calc b = z⁻¹ * (z * b) := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      rw [this]
      exact one_mem _))
    (fun h => hbV (by
      have : b = z⁻¹ * a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * a := by rw [← h]
      rw [this]
      exact mul_mem (inv_mem hzV₂) ha))
    (fun h => hbV (by
      have : b = a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * (z * a) := by rw [h]
          _ = a := by group
      rw [this]
      exact ha))
  have hx₁L1 : x₁ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₁L, S14.mem_g1 hz0 hz1 hx₁z⟩, 3, by decide, hx₁3⟩
  have hx₂L1 : x₂ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₂L, S14.mem_g1 hz0 hz1 hx₂z⟩, 3, by decide, hx₂3⟩
  have hx₁z' : x₁⁻¹ * z * x₁ = z := by
    calc x₁⁻¹ * z * x₁ = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by rw [hx₁z]
      _ = z := by group
  have hx₁b' : x₁⁻¹ * b * x₁ = a := by
    calc x₁⁻¹ * b * x₁ = x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ := by rw [hx₁a]
      _ = a := by group
  have hya : (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = z * a := by
    calc (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = x₁⁻¹ * (x₂ * a * x₂⁻¹) * x₁ := by group
      _ = x₁⁻¹ * (z * b) * x₁ := by rw [hx₂a]
      _ = (x₁⁻¹ * z * x₁) * (x₁⁻¹ * b * x₁) := by group
      _ = z * a := by rw [hx₁z', hx₁b']
  exact ⟨V₂, z, a, b, x₁, x₁⁻¹ * x₂, hV2, hz0, hz1, ha, haV, hb, hbV, hx₁L1,
    mul_mem (inv_mem hx₁L1) hx₂L1, hx₁a, hx₁b, hya⟩

theorem v_le_l1 : V ≤ L₁Of L (fsuV1 T V) := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨V₂, z, a, b, x, y, hV2, hz0, hz1, ha, haV, hb, hbV, hxL1, hyL1, hxa, hxb, hya⟩ :=
    C.exists_basis_l1
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (fsuV1 T V : Set G) := fun v hv => by
    rw [normalizer_eq_centralizer_of_card_two hV1, Subgroup.mem_centralizer_iff]
    intro w hw
    exact F7.isElemAbelian_comm hUe (v_le_fsuU (Subgroup.mem_inf.mp hw).1) (v_le_fsuU hv)
  have haV' : a ∈ V := hV2.2.1 ha
  have hz : z ∈ L₁Of L (fsuV1 T V) := by
    have h := comm_mem_l1 hyL1 (C.v_le_L haV') (hVN a haV')
    rwa [hya, mul_inv_cancel_right] at h
  have ha1 : a ∈ L₁Of L (fsuV1 T V) := by
    have h := comm_mem_l1 hxL1 (C.v_le_L hb) (hVN b hb)
    rwa [hxb, mul_inv_cancel_right] at h
  have hb1 : b ∈ L₁Of L (fsuV1 T V) := by
    have h := comm_mem_l1 hxL1 (C.v_le_L haV') (hVN a haV')
    rw [hxa] at h
    have := mul_mem h ha1
    rwa [inv_mul_cancel_right] at this
  have hV1 : fsuV1 T V ≤ L₁Of L (fsuV1 T V) := fun v hv => by
    rcases S14.eq_of_mem_V1 hz0 hz1 hv with rfl | rfl
    · exact one_mem _
    · exact hz
  have hV2le : V₂ ≤ L₁Of L (fsuV1 T V) := fun v hv => by
    rcases S14.mem_V2 ha haV hv with h | h
    · exact hV1 h
    · rw [show v = a⁻¹ * (a * v) by group]
      exact mul_mem (inv_mem ha1) (hV1 h)
  intro v hv
  rcases S14.mem_V hb hbV hv with h | h
  · exact hV2le h
  · rw [show v = b⁻¹ * (b * v) by group]
    exact mul_mem (inv_mem hb1) (hV2le h)

theorem sL_le_l1 : sL T L V ≤ L₁Of L (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
  obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hρs := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h1281)
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  obtain ⟨A₀, hA₀⟩ := exists_sl3_e1 (Multiplicative.toAdd (e ⟨z, hzV⟩)) (by
    intro h0
    apply hz1
    have h1 : e ⟨z, hzV⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨z, hzV⟩), h0]
      rfl
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
  set θ := theta1 hLV e A₀ with hθ
  have hθs : Function.Surjective θ := theta1_surjective hLV e A₀ hρs
  have hθLl : ∀ l : ↥L, θ l ∈ H6.Ll → (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
    fun l hl => (mem_normalizer_iff_of_gen hzV1 hz1 hgen).mpr
      ((theta1_mem_Ll_iff hLV e A₀ hzV hA₀ l).mp hl)
  have hS := C.pCoreOf_eq_sL
  have hθk : θ.ker = (sL T L V).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, theta1_eq_one_iff hLV e A₀, Subgroup.mem_subgroupOf, ← hS,
      C.pCoreOf_eq, Subgroup.mem_inf]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  obtain ⟨χ, hχk, hχtr, hχs, hχe⟩ :=
    C.isSteinbergSection C.u0_eq C.vh63 C.vh65 C.l71 θ hθs hθk
  have hχ1 : ∀ s : ↥(sL T L V), χ s = 1 ↔ (s : G) ∈ V := fun s => by
    rw [← MonoidHom.mem_ker, hχk, Subgroup.mem_subgroupOf]
  have hVL1 := C.v_le_l1
  obtain ⟨l₁, hl₁L1, hl₁⟩ := exists_mem_l1_of hθs hθLl stG1_mem.1 stG1_mem.2
  obtain ⟨l₂, hl₂L1, hl₂⟩ := exists_mem_l1_of hθs hθLl stG2_mem.1 stG2_mem.2
  have hSL : sL T L V ≤ L := C.sL_le_L C.u0_eq
  have hSN : ∀ s ∈ sL T L V, s ∈ Subgroup.normalizer (fsuV1 T V : Set G) := fun s hs => by
    have h : s ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← C.pCoreOf_eq, hS]
      exact hs
    rw [normalizer_eq_centralizer_of_card_two hV1, Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 w (Subgroup.mem_inf.mp hw).1
  have hconj : ∀ (l : ↥L) (s : ↥(sL T L V)), (l : G) * s * (l : G)⁻¹ ∈ sL T L V := fun l s =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ l.2) s).mp s.2
  intro s hs
  obtain ⟨B, Cm, hB, hC, hA⟩ := st_eq_sum (Multiplicative.toAdd (χ ⟨s, hs⟩)) (hχtr _)
  obtain ⟨sB, hsB⟩ := hχs B hB
  obtain ⟨sC, hsC⟩ := hχs Cm hC
  have h1 : χ ⟨_, hconj l₁ sB⟩ = Multiplicative.ofAdd (RuType.stAct stG1 B) := by
    rw [hχe l₁ sB ⟨_, hconj l₁ sB⟩ rfl, hsB, toAdd_ofAdd, hl₁]
  have h2 : χ ⟨_, hconj l₂ sC⟩ = Multiplicative.ofAdd (RuType.stAct stG2 Cm) := by
    rw [hχe l₂ sC ⟨_, hconj l₂ sC⟩ rfl, hsC, toAdd_ofAdd, hl₂]
  set w : ↥(sL T L V) := ⟨_, hconj l₁ sB⟩ * sB⁻¹ * (⟨_, hconj l₂ sC⟩ * sC⁻¹) with hw
  have hχw : χ w = χ ⟨s, hs⟩ := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, h1, h2, hsB, hsC]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    rw [hA]
    abel
  have hwV : ((w⁻¹ * ⟨s, hs⟩ : ↥(sL T L V)) : G) ∈ V :=
    (hχ1 _).mp (by
      rw [map_mul, map_inv, hχw]
      exact inv_mul_cancel _)
  have hwL1 : (w : G) ∈ L₁Of L (fsuV1 T V) := by
    have e1 : (w : G) = ((l₁ : G) * sB * (l₁ : G)⁻¹ * (sB : G)⁻¹) *
        ((l₂ : G) * sC * (l₂ : G)⁻¹ * (sC : G)⁻¹) := by
      rw [hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1]
    exact mul_mem (comm_mem_l1 hl₁L1 (hSL sB.2) (hSN _ sB.2))
      (comm_mem_l1 hl₂L1 (hSL sC.2) (hSN _ sC.2))
  have e2 : s = (w : G) * ((w⁻¹ * ⟨s, hs⟩ : ↥(sL T L V)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e2]
  exact mul_mem hwL1 (hVL1 hwV)

end Ctx73

end CFSG.Quasithin.H13.L32A
