module

public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.H13.L32NLem14332g
public import CFSG.Quasithin.H13.L32NLem14332l

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332
open scoped commutatorElement

namespace L14333

structure Ctx (G : Type) [Group G] [Finite G] (T L V V₂ K : Subgroup G) (g a z b d x : G)
    (D : HatModelU (fsuU T V)) : Prop where
  ctx : Ctx14332 G T L V V₂ g a D
  ii : Case14323ii T V g D
  dim : Module.finrank (ZMod 2) D.V = 4
  card_zU : Nat.card ↥(centerOf (fsuU T V)) = 4
  q_eq : pCoreOf 2 (l32nH T V) = l32nCHat T V
  q_le : pCoreOf 2 (l32nH T V) ≤ T
  comp : K ∈ cComp (l32nH T V)
  K_norm : l32nH T V ≤ Subgroup.normalizer (K : Set G)
  H_eq : l32nH T V = K ⊔ T
  card_kd : Nat.card ↥((K.subgroupOf (l32nH T V)).map (L14332.imgHom D)) = 60
  KQ : ⁅K, pCoreOf 2 (l32nH T V)⁆ ≤ fsuU T V
  U_eq : fsuU T V = ⁅pCoreOf 2 K, K⁆
  odd_mem : ∀ y ∈ l32nH T V, ∀ m : ℕ, Odd m → y ^ m = 1 → y ∈ K
  setting : ∃ _ : IsMulCommutative ↥V, L32NSet14.Setting G T L V V₂
  z_mem : z ∈ fsuV1 T V
  z_ne : z ≠ 1
  b_mem : b ∈ V
  b_nmem : b ∉ V₂
  x_mem : x ∈ L
  x_cube : x ^ 3 = 1
  x_z : x * z * x⁻¹ = z
  x_a : x * a * x⁻¹ = b
  x_b : x * b * x⁻¹ = a * b
  d_mem : d ∈ centerOf (fsuU T V)
  d_sq : d * d = z
  vZ : V ⊓ centerOf (fsuU T V) = fsuV1 T V
  card_hatV : Nat.card ↥(D.hat V) = 4

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1288 : Lemma12_8_8_two) (h12810 : Lemma12_8_10) (h12811 : Lemma12_8_11)
    (h12811h : Lemma12_8_11_hat) (h12812 : Lemma12_8_12_two) (h12813 : Lemma12_8_13)
    (h14323 : Lemma14323Rest) (h14324 : Lemma14324One) (h14331 : Lemma14331One)
    (hKG22 : KGG22PointStab) (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line)
    (hKGL24 : KGL24Quad) {T L V : Subgroup G}
    (h : Hyp14310One G T L V) (hlt : fsuV1 T V < centerOf (fsuU T V)) :
    ∃ (V₂ K : Subgroup G) (g a z b d x : G) (D : HatModelU (fsuU T V)),
      Ctx G T L V V₂ K g a z b d x D := by
  obtain ⟨V₂, g, a, D, C⟩ := exists_ctx14332 h1332 h1334 h1222 h12213 h37 h38 h39 h12810 h12813
    h14331 h hlt
  rcases h14324 G T L V h hlt V₂ g C.plane C.gP C.gN D with h6 | ⟨hd, hi | hii | hiii⟩
  · exact (not_g22 h1222 h12213 h12811 h12811h h12812 hKGr hKG22 C h6).elim
  · exact (not_case_i h1332 h1334 h1222 h14323 C hd hi).elim
  swap
  · exact (not_case_iii h1288 h14323 hKGq hKGl C hd hiii).elim
  have h4 : Nat.card ↥(centerOf (fsuU T V)) = 4 := by
    have := C.card_zU
    rw [hii.card_zU] at this
    omega
  have hQ := C.q_eq h4
  have hQT : pCoreOf 2 (l32nH T V) ≤ T :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (h.isSylowTwoOf_l32nH (stmtL32NModule_of_inputs h1332 h1334))
  obtain ⟨K, hK⟩ := exists_mem_cComp hii
  obtain ⟨hVc, S⟩ := exists_setting h1332 h1334 h1222 C.hyp C.plane
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.plane.2 hz
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  obtain ⟨x, hxL, hx3, hxz, hxa, hxb⟩ := S.exists_rot hzV haV hbV
    (fun h => C.a1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => C.a1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ C.aV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ C.aV₂))
  obtain ⟨y, hy, hyy⟩ := C.exists_sq_ne_of_case_ii h1288 hKGL24 hii
  have hyz : y * y = z := (S.eq_of_mem_V1 hz hz1 (C.sq y (Subgroup.mem_inf.mp hy).1)).resolve_left
    hyy
  have hE := (h14323 G T L V h V₂ g C.plane C.gP C.gN D hd).1
  exact ⟨V₂, K, g, a, z, b, y, x, D,
    { ctx := C
      ii := hii
      dim := hd
      card_zU := h4
      q_eq := hQ
      q_le := hQT
      comp := hK
      K_norm := le_normalizer_cComp hii hQ hK
      H_eq := eq_sup_T C hii hQ hQT hK
      card_kd := card_kd hii hQ hK
      KQ := commutator_K_Q_le h1222 h12213 h14323 C hii hd hQ hQT hK
      U_eq := fsuU_eq_commutator h1332 h1334 h1222 h12213 h14323 C hii hd hQ hQT hK
      odd_mem := fun y hy m hm hym => mem_cComp_of_odd hii hQ hK hy hm hym
      setting := ⟨hVc, S⟩
      z_mem := hz
      z_ne := hz1
      b_mem := hbV
      b_nmem := hbV₂
      x_mem := hxL
      x_cube := hx3
      x_z := hxz
      x_a := hxa
      x_b := hxb
      d_mem := hy
      d_sq := hyz
      vZ := lemma12_8_8_three h1222 h12213 C.setting
      card_hatV := hE.2 }⟩

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem card_U : Nat.card ↥(fsuU T V) = 64 := L14332.card_fsuU c.card_zU c.dim

theorem d_mem_U : d ∈ fsuU T V := (Subgroup.mem_inf.mp c.d_mem).1

theorem z_mem_V : z ∈ V := (Subgroup.mem_inf.mp c.z_mem).1

theorem a_mem_V : a ∈ V := c.ctx.plane.1.1 c.ctx.aV₂

theorem z_sq : z * z = 1 := by
  obtain ⟨_, S⟩ := c.setting
  exact S.mul_self_V c.z_mem_V

theorem eq_of_mem_V1 {v : G} (hv : v ∈ fsuV1 T V) : v = 1 ∨ v = z := by
  obtain ⟨_, S⟩ := c.setting
  exact S.eq_of_mem_V1 c.z_mem c.z_ne hv

theorem orderOf_d : orderOf d = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : orderOf d = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · intro h
      apply c.z_ne
      rw [← c.d_sq, ← pow_two]
      simpa using h
    · calc d ^ 2 ^ (1 + 1) = (d * d) * (d * d) := by
            rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]
        _ = 1 := by rw [c.d_sq, c.z_sq]
  rw [h]
  norm_num

theorem zpowers_d : Subgroup.zpowers d = centerOf (fsuU T V) := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr c.d_mem)
  rw [c.card_zU, Nat.card_zpowers, c.orderOf_d]

theorem x_mem_H : x ∈ l32nH T V := by
  obtain ⟨_, S⟩ := c.setting
  exact S.mem_g1 c.z_mem c.z_ne c.x_z

theorem x_mem_K : x ∈ K := c.odd_mem x c.x_mem_H 3 (by decide) c.x_cube

theorem odd_orderOf_x : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one c.x_cube)

theorem x_comm_zU {y : G} (hy : y ∈ centerOf (fsuU T V)) : x * y * x⁻¹ = y :=
  L14332.odd_centralizes_of_card_four c.ctx c.card_zU x c.x_mem_H c.odd_orderOf_x y hy

theorem x_comm_d : x * d * x⁻¹ = d := c.x_comm_zU c.d_mem

theorem card_sup_zU : Nat.card ↥(V ⊔ centerOf (fsuU T V)) = 16 := by
  obtain ⟨_, S⟩ := c.setting
  have hVN : V ≤ Subgroup.normalizer (centerOf (fsuU T V) : Set G) :=
    fun v hv => L14332.l32nH_le_normalizer_zU (c.ctx.U_le (c.ctx.V_U hv))
  have h := L32NSet14.card_sup_mul_card_inf hVN
  rw [c.vZ, S.card_V, c.card_zU, c.ctx.card_V1] at h
  omega

theorem π_mem_hatV {u : G} (hu : u ∈ fsuU T V) (hc : ∀ v ∈ V, u * v = v * u) :
    D.π u ∈ D.hat V := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have hiso := D.isotropic_hat c.ctx.V_U c.ctx.V_comm
  have hle : D.hat V ≤ D.B.orthogonal (D.hat V) := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => hiso w hw y hy
  have hfr : Module.finrank (ZMod 2) ↥(D.hat V) = 2 := by
    have h := c.card_hatV
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
    have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥(D.hat V) = 2 ^ 2 := by rw [h]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hfo : Module.finrank (ZMod 2) ↥(D.B.orthogonal (D.hat V)) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal D.nondegenerate, c.dim, hfr]
  have heq : D.hat V = D.B.orthogonal (D.hat V) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hfo])
  rw [heq]
  refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => ?_
  have hspan : D.hat V ≤ LinearMap.ker (D.B.flip (D.π u)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, ⟨hv, hvU⟩, rfl⟩
    show D.B (D.π v) (D.π u) = 0
    rw [D.B_spec v hvU u hu]
    calc v * u * v⁻¹ * u⁻¹ = (u * v) * v⁻¹ * u⁻¹ := by rw [hc v hv]
      _ = 1 := by group
  have := hspan hw
  rw [LinearMap.mem_ker] at this
  exact this

theorem exists_of_mem_hatV {w : D.V} (hw : w ∈ D.hat V) : ∃ v ∈ V, D.π v = w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, ⟨hv, -⟩, rfl⟩ := hw
    exact ⟨v, hv, rfl⟩
  | zero => exact ⟨1, V.one_mem, D.π_one⟩
  | add w w' _ _ ih ih' =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨v', hv', rfl⟩ := ih'
    exact ⟨v * v', V.mul_mem hv hv', D.π_mul v (c.ctx.V_U hv) v' (c.ctx.V_U hv')⟩
  | smul r w _ ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    rcases (show ∀ r : ZMod 2, r = 0 ∨ r = 1 by decide) r with rfl | rfl
    · exact ⟨1, V.one_mem, by rw [zero_smul, D.π_one]⟩
    · exact ⟨v, hv, by rw [one_smul]⟩

theorem mem_sup_of_comm {u : G} (hu : u ∈ fsuU T V) (hc : ∀ v ∈ V, u * v = v * u) :
    u ∈ V ⊔ centerOf (fsuU T V) := by
  obtain ⟨v, hv, hvu⟩ := c.exists_of_mem_hatV (c.π_mem_hatV hu hc)
  have hvU := c.ctx.V_U hv
  have hz : v⁻¹ * u ∈ centerOf (fsuU T V) := (D.π_eq_iff v hvU u hu).mp hvu
  have : u = v * (v⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hz)

theorem eq_oTwoUpper : K = oTwoUpper (l32nH T V) := by
  have hKH : K ≤ l32nH T V := le_of_mem_cComp c.comp
  have hle : oTwoUpper (l32nH T V) ≤ K := by
    refine (Subgroup.closure_le K).mpr fun y hy => ?_
    exact c.odd_mem y hy.1 (orderOf y) hy.2 (pow_orderOf_eq_one y)
  refine eq_oTwoUpper_of_pow_mem hKH (fun y hy => ?_)
    (C2Nine.oTwoUpper_eq_of_perfect (perfect_of_mem_cComp c.comp)).symm
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (l32nH T V) hy
  exact ⟨k, hle hk⟩

end Ctx

end L14333

end CFSG.Quasithin.H13
