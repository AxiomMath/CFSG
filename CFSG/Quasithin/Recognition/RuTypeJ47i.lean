module

public import CFSG.Quasithin.Recognition.RuTypeJ47h
public import CFSG.Quasithin.Recognition.RuTypeJ47c
public import CFSG.Quasithin.Recognition.RuTypeJ47g

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Sigma47

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {M : RuDataM G}

omit [Finite G] in
theorem z_mem_Q47 (M : RuDataM G) : M.z ∈ ruQ M.T := M.U_le_Q (M.V_le_U M.z_mem_V)

theorem z_mem_H47 (M : RuDataM G) : M.z ∈ ruH M.T := M.mem_H_iff_comm.mpr rfl

omit [Finite G] in
theorem phiG_one47 (M : RuDataM G) : M.phiG 1 = 1 := by
  rw [M.phiG_of_mem (one_mem _)]
  exact map_one _

namespace Conf47

variable (C : Conf47 M)

structure Fives where
  τ : G
  bu : G
  bt : G
  bu' : G
  τ_mem : τ ∈ M.T5 C.b
  τ_conj : τ * C.u * τ⁻¹ = C.u * M.z
  bu_mem : bu ∈ P5 C.b
  bu_comm : bu * C.u = C.u * bu
  bu_pow : bu ^ 5 = 1
  bu_ne : bu ≠ 1
  bu_gen : ∀ y ∈ P5 C.b, y * C.u = C.u * y → ∃ n : ℕ, bu ^ n = y
  z_inv_bu : M.z * bu * M.z⁻¹ = bu⁻¹
  bt_mem : bt ∈ P5 C.b
  bt_comm : bt * C.t = C.t * bt
  bt_pow : bt ^ 5 = 1
  bt_ne : bt ≠ 1
  z_inv_bt : M.z * bt * M.z⁻¹ = bt⁻¹
  u_inv_bt : C.u * bt * C.u⁻¹ = bt⁻¹
  comm_bu_bt : bu * bt * bu⁻¹ * bt⁻¹ ∈ Subgroup.zpowers C.b
  comm_bu_bt_ne : bu * bt * bu⁻¹ * bt⁻¹ ≠ 1
  bu'_comm : bu' * C.u = C.u * bu'
  bu'_pow : bu' ^ 5 = 1
  bu'_ne : bu' ≠ 1
  bu'_comm_bt : bu' * bt = bt * bu'
  bu'_conj_b : ∃ m : ℕ, bu' * C.b * bu'⁻¹ = C.b * bt ^ m ∧ bt ^ m ≠ 1
  z_norm_bu' : ∃ k : ℕ, M.z * bu' * M.z⁻¹ = bu' ^ k

theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

theorem exists_pow_pow_eq {X : Type*} [Group X] {x : X} (hx : x ^ 5 = 1) {n : ℕ}
    (hn : x ^ n ≠ 1) : ∃ r : ℕ, (x ^ n) ^ r = x := by
  obtain ⟨k, hk⟩ := powOfG_symm hx hn (powOfG_pow x n hx)
  exact ⟨k, hk.symm⟩

theorem nonempty_fives :
    Nonempty C.Fives := by
  obtain ⟨τ, hτT, hτu⟩ := C.exists_tau
  obtain ⟨bu, hbuP, hbuu, hbu5, hbu1, hbugen, hzbu⟩ := C.exists_bu
  obtain ⟨bt, hbtP, hbtt, hbt5, hbt1, -, hzbt, hubt⟩ := C.exists_bt
  have hcomm := C.comm_bu_bt hbuP hbuu hbu5 hbu1 hbtP hbtt hbt5 hbt1 hubt
  set ct := C.j * τ⁻¹ with hct
  have hctz : ct * M.z * ct⁻¹ = C.u := C.ct_conj_z hτT
  set b'' := ct * bt * ct⁻¹ with hb''
  have hb''H : b'' ∈ ruH M.T := C.ctconj_mem_H hτT hτu hbtt
  have hb''5 : orderOf b'' = 5 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, fun h => hbt1 ?_⟩
    · rw [hb'', conj_pow, hbt5]; group
    · calc bt = ct⁻¹ * b'' * ct := by rw [hb'']; group
        _ = 1 := by rw [h]; group
  have hg : ct⁻¹ * b'' * ct⁻¹⁻¹ = bt := by rw [hb'']; group
  have hK := card_P5c_inf_centralizer hb''H hb''5 (g := ct⁻¹) C.isConj_u C.u_mul_self
    (by rw [hg]; exact hubt)
  obtain ⟨bu', hbu'K, hbu'5, hbu'1, hbu'gen⟩ := exists_gen_of_card_five hK
  have hbu'P : bu' ∈ P5c b'' ct⁻¹ := (Subgroup.mem_inf.mp hbu'K).1
  have hbu'u : bu' * C.u = C.u * bu' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hbu'K).2
  have hbu'gen' : ∀ y ∈ P5c b'' ct⁻¹, y * C.u = C.u * y → ∃ n : ℕ, bu' ^ n = y :=
    fun y hy hyu =>
      hbu'gen y (Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyu⟩)
  have hbu'bt : bu' * bt = bt * bu' := by
    have h := comm_center_P5c hbu'P
    rwa [hg] at h
  have hbP : C.b ∈ P5c b'' ct⁻¹ :=
    mem_P5c_of_pow_five hb''H hb''5 (by rw [hg]; exact (comm_b_P5 hbtP).symm) C.b_pow_five
  have hcb := comm_mem_P5c hb''H hb''5 hbu'P hbP
  rw [hg] at hcb
  obtain ⟨m, hm⟩ := exists_pow_of_mem_zpowers hcb
  have hbbt : C.b * bt = bt * C.b := (comm_b_P5 hbtP).symm
  have hconj : bu' * C.b * bu'⁻¹ = C.b * bt ^ m := by
    have hcm : Commute C.b (bt ^ m) := (Commute.pow_right hbbt m)
    calc bu' * C.b * bu'⁻¹ = bu' * C.b * bu'⁻¹ * C.b⁻¹ * C.b := by group
      _ = bt ^ m * C.b := by rw [hm]
      _ = C.b * bt ^ m := hcm.eq.symm
  have hm1 : bt ^ m ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hconj
    have hbu'b : bu' * C.b = C.b * bu' := by
      calc bu' * C.b = bu' * C.b * bu'⁻¹ * bu' := by group
        _ = C.b * bu' := by rw [hconj]
    have hbu'P5 : bu' ∈ P5 C.b :=
      mem_P5_of_pow_five C.b_mem_H C.orderOf_b (mem_G5.mpr hbu'b) hbu'5
    obtain ⟨n, hn⟩ := hbugen bu' hbu'P5 hbu'u
    have hn1 : bu ^ n ≠ 1 := by rw [hn]; exact hbu'1
    obtain ⟨r, hr⟩ := exists_pow_pow_eq hbu5 hn1
    have hc : Commute (bu ^ n) bt := by rw [hn]; exact hbu'bt
    have hc' : Commute bu bt := by
      rw [← hr]
      exact hc.pow_left r
    apply hcomm.2
    rw [hc'.eq]
    group
  have hzP : M.z * bu' * M.z⁻¹ ∈ P5c b'' ct⁻¹ := by
    rw [mem_P5c, inv_inv]
    have h1 : ct * bu' * ct⁻¹ ∈ P5 b'' := by
      have := mem_P5c.mp hbu'P
      rwa [inv_inv] at this
    have hub : C.u * b'' * C.u⁻¹ = b''⁻¹ := by
      rw [← hctz, hb'']
      calc ct * M.z * ct⁻¹ * (ct * bt * ct⁻¹) * (ct * M.z * ct⁻¹)⁻¹ =
            ct * (M.z * bt * M.z⁻¹) * ct⁻¹ := by group
        _ = (ct * bt * ct⁻¹)⁻¹ := by rw [hzbt]; group
    have h2 := conj_mem_P5_of_inv hub h1
    have e : C.u * (ct * bu' * ct⁻¹) * C.u⁻¹ = ct * (M.z * bu' * M.z⁻¹) * ct⁻¹ := by
      rw [← hctz]
      group
    rwa [e] at h2
  have hzu : M.z * bu' * M.z⁻¹ * C.u = C.u * (M.z * bu' * M.z⁻¹) := by
    have hzu' : M.z⁻¹ * C.u = C.u * M.z⁻¹ := by rw [M.z_inv47]; exact C.u_comm_z.symm
    calc M.z * bu' * M.z⁻¹ * C.u = M.z * bu' * (M.z⁻¹ * C.u) := by group
      _ = M.z * (bu' * C.u) * M.z⁻¹ := by rw [hzu']; group
      _ = M.z * (C.u * bu') * M.z⁻¹ := by rw [hbu'u]
      _ = (M.z * C.u) * bu' * M.z⁻¹ := by group
      _ = C.u * (M.z * bu' * M.z⁻¹) := by rw [← C.u_comm_z]; group
  obtain ⟨k, hk⟩ := hbu'gen' _ hzP hzu
  exact ⟨{
      τ := τ, bu := bu, bt := bt, bu' := bu', τ_mem := hτT, τ_conj := hτu,
      bu_mem := hbuP, bu_comm := hbuu, bu_pow := hbu5, bu_ne := hbu1, bu_gen := hbugen,
      z_inv_bu := hzbu, bt_mem := hbtP, bt_comm := hbtt, bt_pow := hbt5, bt_ne := hbt1,
      z_inv_bt := hzbt, u_inv_bt := hubt, comm_bu_bt := hcomm.1, comm_bu_bt_ne := hcomm.2,
      bu'_comm := hbu'u, bu'_pow := hbu'5, bu'_ne := hbu'1, bu'_comm_bt := hbu'bt,
      bu'_conj_b := ⟨m, hconj, hm1⟩, z_norm_bu' := ⟨k, hk.symm⟩ }⟩

@[expose] noncomputable def rhoU (w : G) : SigmaL2F4 := M.phiG (C.j * w * C.j⁻¹)

theorem rhoU_mul {w w' : G} (hw : w * C.u = C.u * w) (hw' : w' * C.u = C.u * w') :
    C.rhoU (w * w') = C.rhoU w * C.rhoU w' := by
  unfold rhoU
  rw [show C.j * (w * w') * C.j⁻¹ = (C.j * w * C.j⁻¹) * (C.j * w' * C.j⁻¹) by group,
    M.phiG_mul (C.jconj_mem_H hw) (C.jconj_mem_H hw')]

theorem rhoU_pow {w : G} (hw : w * C.u = C.u * w) (n : ℕ) : C.rhoU (w ^ n) = C.rhoU w ^ n := by
  unfold rhoU
  rw [← conj_pow, M.phiG_pow (C.jconj_mem_H hw)]

omit [Finite G] in
theorem rhoU_one : C.rhoU 1 = 1 := by
  unfold rhoU
  rw [mul_one, mul_inv_cancel]
  exact M.phiG_one47

omit [Finite G] in
theorem comm_u_pow {w : G} (hw : w * C.u = C.u * w) (n : ℕ) :
    w ^ n * C.u = C.u * w ^ n :=
  ((Commute.pow_left (show Commute w C.u from hw) n)).eq

omit [Finite G] in
theorem comm_u_mul {w w' : G} (hw : w * C.u = C.u * w) (hw' : w' * C.u = C.u * w') :
    (w * w') * C.u = C.u * (w * w') :=
  ((show Commute w C.u from hw).mul_left (show Commute w' C.u from hw')).eq

theorem pow_eq_one_of_rhoU {w : G} (hw : w * C.u = C.u * w) (h : C.rhoU w = 1) :
    w ^ 2048 = 1 := by
  have hQ := (M.phiG_eq_one_iff (C.jconj_mem_H hw)).mp h
  have h1 := M.pow_eq_one_of_mem_Q hQ
  rw [conj_pow] at h1
  calc w ^ 2048 = C.j⁻¹ * (C.j * w ^ 2048 * C.j⁻¹) * C.j := by group
    _ = 1 := by rw [h1]; group

omit [Finite G] in
theorem t_comm_t : C.t * C.t = C.t * C.t := rfl

theorem z_comm_t : M.z * C.t = C.t * M.z := C.t_comm_z.symm

theorem j_comm_t : C.j * C.t = C.t * C.j := by
  have h1 : C.j * C.t * C.j⁻¹ = C.t := by
    show C.j * (C.u * M.z) * C.j⁻¹ = C.u * M.z
    calc C.j * (C.u * M.z) * C.j⁻¹ = (C.j * C.u * C.j⁻¹) * (C.j * M.z * C.j⁻¹) := by group
      _ = M.z * C.u := by rw [C.j_conj_u, C.j_conj_z]
      _ = C.u * M.z := C.u_comm_z.symm
  calc C.j * C.t = C.j * C.t * C.j⁻¹ * C.j := by group
    _ = C.t * C.j := by rw [h1]

namespace Fives

variable {C} (D : C.Fives)

omit [Finite G] in
theorem orderOf_bt : orderOf D.bt = 5 := orderOf_eq_prime D.bt_pow D.bt_ne

omit [Finite G] in
theorem b_comm_bt : C.b * D.bt = D.bt * C.b := (comm_b_P5 D.bt_mem).symm

omit [Finite G] in
theorem bu_comm_b : D.bu * C.b = C.b * D.bu := comm_b_P5 D.bu_mem

theorem exists_bu_conj_bt : ∃ l : ℕ, D.bu * D.bt * D.bu⁻¹ = D.bt * C.b ^ l ∧
    (l : ZMod 5) ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_pow_of_mem_zpowers D.comm_bu_bt
  refine ⟨l, ?_, zmod_ne_zero_of_pow_ne_one C.orderOf_b (by rw [hl]; exact D.comm_bu_bt_ne)⟩
  have hc : Commute (C.b ^ l) D.bt := Commute.pow_left (show Commute C.b D.bt from D.b_comm_bt) l
  calc D.bu * D.bt * D.bu⁻¹ = (D.bu * D.bt * D.bu⁻¹ * D.bt⁻¹) * D.bt := by group
    _ = C.b ^ l * D.bt := by rw [hl]
    _ = D.bt * C.b ^ l := hc.eq

theorem not_powOfG_bu : ¬ PowOfG (C.rhoU D.bu) (C.rhoU D.bu') := by
  rintro ⟨r, hr⟩
  obtain ⟨l, hl, hl0⟩ := D.exists_bu_conj_bt
  obtain ⟨m, hm, hm1⟩ := D.bu'_conj_b
  have hm0 : (m : ZMod 5) ≠ 0 := zmod_ne_zero_of_pow_ne_one D.orderOf_bt hm1
  have hbub : D.bu * C.b * D.bu⁻¹ = C.b := by rw [D.bu_comm_b]; group
  have hbu'bt : D.bu' * D.bt * D.bu'⁻¹ = D.bt := by rw [D.bu'_comm_bt]; group
  obtain ⟨k, hk3b, hk3c⟩ := exists_conj_pow_three D.b_comm_bt C.b_pow_five D.bt_pow
    (l := l) (m := m) hl0 hm0 hbub hl hm hbu'bt
  set x := D.bu * D.bu' ^ k with hx
  have hxu : x * C.u = C.u * x := C.comm_u_mul D.bu_comm (C.comm_u_pow D.bu'_comm k)
  have hxbt : x * D.bt * x⁻¹ = D.bt * C.b ^ l := by
    have h1 := conj_pow_of_conj_eq hbu'bt k
    calc x * D.bt * x⁻¹ = D.bu * (D.bu' ^ k * D.bt * (D.bu' ^ k)⁻¹) * D.bu⁻¹ := by
          rw [hx]; group
      _ = D.bt * C.b ^ l := by rw [h1, hl]
  have hbl : C.b ^ l ≠ 1 := pow_ne_one_of_zmod_ne_zero C.orderOf_b hl0
  have hρb : C.rhoU D.bu ^ 5 = 1 := by
    rw [← C.rhoU_pow D.bu_comm, D.bu_pow, C.rhoU_one]
  have hρ : C.rhoU (x ^ 5) = 1 := by
    rw [C.rhoU_pow hxu, hx, C.rhoU_mul D.bu_comm (C.comm_u_pow D.bu'_comm k),
      C.rhoU_pow D.bu'_comm, hr, ← pow_mul, ← pow_succ', ← pow_mul, pow_mul', hρb, one_pow]
  have hx10240 : x ^ 10240 = 1 := by
    have h := C.pow_eq_one_of_rhoU (C.comm_u_pow hxu 5) hρ
    rw [← pow_mul] at h
    norm_num at h
    exact h
  have hx3 : x ^ 3 * D.bt * (x ^ 3)⁻¹ = D.bt := hk3c
  have h3 := conj_pow_of_conj_eq hx3 3413
  have e : x ^ 10240 = (x ^ 3) ^ 3413 * x := by rw [← pow_mul, ← pow_succ]
  have h4 : x ^ 10240 * D.bt * (x ^ 10240)⁻¹ = x * D.bt * x⁻¹ := by
    rw [e]
    calc (x ^ 3) ^ 3413 * x * D.bt * ((x ^ 3) ^ 3413 * x)⁻¹ =
          (x ^ 3) ^ 3413 * (x * D.bt * x⁻¹) * ((x ^ 3) ^ 3413)⁻¹ := by group
      _ = (x ^ 3) ^ 3413 * (D.bt * C.b ^ l) * ((x ^ 3) ^ 3413)⁻¹ := by rw [hxbt]
      _ = ((x ^ 3) ^ 3413 * D.bt * ((x ^ 3) ^ 3413)⁻¹) *
          ((x ^ 3) ^ 3413 * C.b ^ l * ((x ^ 3) ^ 3413)⁻¹) := by group
      _ = D.bt * C.b ^ l := by
          rw [h3, ← conj_pow, conj_pow_of_conj_eq hk3b 3413]
      _ = x * D.bt * x⁻¹ := hxbt.symm
  rw [hx10240, one_mul, inv_one, mul_one, hxbt] at h4
  apply hbl
  calc C.b ^ l = D.bt⁻¹ * (D.bt * C.b ^ l) := by group
    _ = 1 := by rw [← h4]; group

@[expose] noncomputable def ct : G := C.j * D.τ⁻¹

@[expose] noncomputable def rhoT (w : G) : SigmaL2F4 := M.phiG (D.ct * w * D.ct⁻¹)

theorem ctconj_mem_H {w : G} (hw : w * C.t = C.t * w) : D.ct * w * D.ct⁻¹ ∈ ruH M.T :=
  C.ctconj_mem_H D.τ_mem D.τ_conj hw

theorem ct_conj_t : D.ct * C.t * D.ct⁻¹ = M.z := C.ct_conj_t D.τ_mem D.τ_conj

theorem ct_conj_z : D.ct * M.z * D.ct⁻¹ = C.u := C.ct_conj_z D.τ_mem

omit [Finite G] in
theorem rhoT_one : D.rhoT 1 = 1 := by
  unfold rhoT
  rw [mul_one, mul_inv_cancel]
  exact M.phiG_one47

theorem rhoT_mul {w w' : G} (hw : w * C.t = C.t * w) (hw' : w' * C.t = C.t * w') :
    D.rhoT (w * w') = D.rhoT w * D.rhoT w' := by
  unfold rhoT
  rw [show D.ct * (w * w') * D.ct⁻¹ = (D.ct * w * D.ct⁻¹) * (D.ct * w' * D.ct⁻¹) by group,
    M.phiG_mul (D.ctconj_mem_H hw) (D.ctconj_mem_H hw')]

theorem rhoT_pow {w : G} (hw : w * C.t = C.t * w) (n : ℕ) : D.rhoT (w ^ n) = D.rhoT w ^ n := by
  unfold rhoT
  rw [← conj_pow, M.phiG_pow (D.ctconj_mem_H hw)]

theorem rhoT_inv {w : G} (hw : w * C.t = C.t * w) : D.rhoT w⁻¹ = (D.rhoT w)⁻¹ := by
  unfold rhoT
  rw [show D.ct * w⁻¹ * D.ct⁻¹ = (D.ct * w * D.ct⁻¹)⁻¹ by group,
    M.phiG_inv (D.ctconj_mem_H hw)]

theorem rhoT_conj {g w : G} (hg : g * C.t = C.t * g) (hw : w * C.t = C.t * w) :
    D.rhoT (g * w * g⁻¹) = D.rhoT g * D.rhoT w * (D.rhoT g)⁻¹ := by
  have hgi : g⁻¹ * C.t = C.t * g⁻¹ := (Commute.inv_left (show Commute g C.t from hg)).eq
  have hgw : (g * w) * C.t = C.t * (g * w) :=
    ((show Commute g C.t from hg).mul_left (show Commute w C.t from hw)).eq
  rw [D.rhoT_mul hgw hgi, D.rhoT_mul hg hw, D.rhoT_inv hg]

theorem rhoT_eq_one_iff {w : G} (hw : w * C.t = C.t * w) :
    D.rhoT w = 1 ↔ D.ct * w * D.ct⁻¹ ∈ ruQ M.T :=
  M.phiG_eq_one_iff (D.ctconj_mem_H hw)

theorem rhoT_t : D.rhoT C.t = 1 := by
  unfold rhoT
  rw [D.ct_conj_t, M.phiG_eq_one_iff M.z_mem_H47]
  exact M.z_mem_Q47

theorem rhoT_z : D.rhoT M.z = M.phiG C.u := by
  unfold rhoT
  rw [D.ct_conj_z]

theorem rhoT_bt_props : D.rhoT D.bt ^ 5 = 1 ∧ D.rhoT D.bt ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [← D.rhoT_pow D.bt_comm, D.bt_pow, D.rhoT_one]
  · have hQ := (D.rhoT_eq_one_iff D.bt_comm).mp h
    have h1 := M.pow_eq_one_of_mem_Q hQ
    rw [conj_pow] at h1
    have h2 : D.bt ^ 2048 = 1 := by
      calc D.bt ^ 2048 = D.ct⁻¹ * (D.ct * D.bt ^ 2048 * D.ct⁻¹) * D.ct := by group
        _ = 1 := by rw [h1]; group
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [D.orderOf_bt] at h3
    norm_num at h3

theorem not_powOfG_bt : ¬ PowOfG (D.rhoT D.bt) (D.rhoT (C.j * D.bt * C.j⁻¹)) := by
  set d := D.rhoT M.z with hd
  set c := D.rhoT C.j with hc
  set y' := D.rhoT C.y with hy'
  set σ := D.rhoT D.bt with hσ
  have hd1 : d ≠ 1 := by rw [hd, D.rhoT_z]; exact C.phiG_u_ne_one
  have hd2 : d * d = 1 := by
    rw [hd, ← D.rhoT_mul C.z_comm_t C.z_comm_t, M.z_mul_self, D.rhoT_one]
  have hc2 : c * c = 1 := by
    rw [hc, ← D.rhoT_mul C.j_comm_t C.j_comm_t, C.j_mul_self, D.rhoT_one]
  have hyd : y' * d * y'⁻¹ = c := by
    rw [hy', hd, hc, ← D.rhoT_conj C.y_comm_t C.z_comm_t, C.y_conj_z]
  have hcd : c * d = d * c := by
    have hjz : C.j * M.z = C.t * (M.z * C.j) := by
      have h1 : C.j * M.z * C.j⁻¹ = C.u := C.j_conj_z
      have h2 : C.t * (M.z * C.j) = C.u * (M.z * M.z) * C.j := by
        show C.u * M.z * (M.z * C.j) = C.u * (M.z * M.z) * C.j
        group
      calc C.j * M.z = C.j * M.z * C.j⁻¹ * C.j := by group
        _ = C.u * C.j := by rw [h1]
        _ = C.t * (M.z * C.j) := by rw [h2, M.z_mul_self, mul_one]
    have hzj : (M.z * C.j) * C.t = C.t * (M.z * C.j) :=
      ((show Commute M.z C.t from C.z_comm_t).mul_left (show Commute C.j C.t from C.j_comm_t)).eq
    rw [hc, hd, ← D.rhoT_mul C.j_comm_t C.z_comm_t, hjz, D.rhoT_mul C.t_comm_t hzj,
      D.rhoT_t, one_mul, D.rhoT_mul C.z_comm_t C.j_comm_t]
  obtain ⟨hσ5, hσ1⟩ := D.rhoT_bt_props
  have hdσ : d * σ * d⁻¹ = σ⁻¹ := by
    rw [hd, hσ, ← D.rhoT_conj C.z_comm_t D.bt_comm, D.z_inv_bt, D.rhoT_inv D.bt_comm]
  have hσ4 : σ⁻¹ = σ ^ 4 := by
    calc σ⁻¹ = σ ^ 5 * σ⁻¹ := by rw [hσ5, one_mul]
      _ = σ ^ 4 := by group
  have hσN : NormBy d σ := ⟨4, by rw [hdσ, hσ4]; rfl⟩
  have hc1 : c ≠ 1 := by
    intro h
    apply hd1
    calc d = y'⁻¹ * (y' * d * y'⁻¹) * y' := by group
      _ = 1 := by rw [hyd, h]; group
  have hy3 : y' ^ 3 = 1 := by
    rw [hy', ← D.rhoT_pow C.y_comm_t, C.y_pow_three, D.rhoT_one]
  have hcd' : c ≠ d := by
    intro h
    have hyc : y' * d = d * y' := by
      calc y' * d = y' * d * y'⁻¹ * y' := by group
        _ = d * y' := by rw [hyd, h]
    have hy1 := eq_one_of_comm_of_pow_three hd2 hd1 hσ5 hσ1 hσN hyc hy3
    have hQ := (D.rhoT_eq_one_iff C.y_comm_t).mp hy1
    have h1 := M.pow_eq_one_of_mem_Q hQ
    rw [conj_pow] at h1
    have h2 : C.y ^ 2048 = 1 := by
      calc C.y ^ 2048 = D.ct⁻¹ * (D.ct * C.y ^ 2048 * D.ct⁻¹) * D.ct := by group
        _ = 1 := by rw [h1]; group
    apply C.y_ne_one
    have := (pow_gcd_eq_one (a := C.y)).mpr ⟨C.y_pow_three, h2⟩
    rwa [show Nat.gcd 3 2048 = 1 by norm_num, pow_one] at this
  have h := not_powOf_conj_of_comm hd2 hd1 hσ5 hσ1 hσN hcd hc2 hc1 hcd'
  rw [hc, ← D.rhoT_conj C.j_comm_t D.bt_comm] at h
  exact h

end Fives

end Conf47

end RuDataM

end CFSG.Quasithin.RuType
