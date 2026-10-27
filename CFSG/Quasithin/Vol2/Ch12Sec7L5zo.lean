module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zn
public import CFSG.RankThree.PartOne.K1214.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

omit [Finite G] in
theorem comm_of_mem_zpowers {c g : G} (hc : c ∈ Subgroup.zpowers z)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : g * c = c * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) k).eq

theorem card_le_two_mul_inf_centralizer {A : Subgroup G} {a : G}
    (hzA : ∀ x ∈ A, z * x = x * z) (hz2 : z * z = 1)
    (ha : ∀ x ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hcz : ∀ x ∈ A, ∀ c ∈ Subgroup.zpowers z, x * c = c * x := by
    intro x hx c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left (show Commute z x from hzA x hx) k)).symm.eq
  let f : ↥A →* ↥(Subgroup.zpowers z) :=
    { toFun := fun x => ⟨a * x * a⁻¹ * (x : G)⁻¹, ha x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show a * ((x : G) * y) * a⁻¹ * ((x : G) * y)⁻¹ =
          a * x * a⁻¹ * (x : G)⁻¹ * (a * y * a⁻¹ * (y : G)⁻¹)
        have h := hcz x x.2 _ (ha y y.2)
        calc a * ((x : G) * y) * a⁻¹ * ((x : G) * y)⁻¹
            = a * x * a⁻¹ * ((x : G)⁻¹ * ((x : G) * (a * y * a⁻¹ * (y : G)⁻¹)) * (x : G)⁻¹) := by
              group
          _ = a * x * a⁻¹ * ((x : G)⁻¹ * ((a * y * a⁻¹ * (y : G)⁻¹) * x) * (x : G)⁻¹) := by
              rw [h]
          _ = _ := by group) }
  have hker : ∀ x : ↥A, x ∈ f.ker ↔ (x : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : a * x * a⁻¹ * (x : G)⁻¹ = 1 := congrArg Subtype.val h
      calc (x : G) * a = (a * x * a⁻¹ * (x : G)⁻¹)⁻¹ * (a * x) := by group
        _ = a * x := by rw [h', inv_one, one_mul]
    · intro h
      refine Subtype.ext ?_
      show a * x * a⁻¹ * (x : G)⁻¹ = 1
      rw [← h]
      group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have h2 : Nat.card ↥f.range ≤ 2 := by
    calc Nat.card ↥f.range ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_card_group _
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2))
  have h3 : Nat.card ↥f.ker = Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hker x.1).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hker _).mpr y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h3] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ h2

variable (s : Set714 G T L V t z)
include s

abbrev Qz (h1222 : Stmt12_2_2) : Subgroup G := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)

structure N3 (h1222 : Stmt12_2_2) : Prop where
  card_Ut : Nat.card ↥(Ut T L V z) = 2 ^ 3
  card_U : Nat.card ↥(U714 T L V z) = 16
  sq_U : ∀ u ∈ U714 T L V z, u ^ 2 = 1
  hs_top : Hs T L V z = ⊤
  card_Q : Nat.card ↥(s.Qz h1222) = 2 ^ 7
  card_H : Nat.card ↥(H714 T L V z) = 2 ^ 10 * 21
  pCore_H : pCoreOf 2 (H714 T L V z) = s.Qz h1222
  cent_U : H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G) = U714 T L V z
  card_VQ : Nat.card ↥(V ⊓ s.Qz h1222) = 16
  UV : U714 T L V z ⊓ V ≤ V1 T L V
  cent_V : Subgroup.centralizer (V : Set G) = V

theorem n3
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) :
    s.N3 h1222 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, h3⟩ := s.card_cTil_eq_and h1222 h1226 h129 h1241 h10 h11 h37 h38 h39 hU hd
  refine ⟨hd, by rw [s.card_U h1222, hd]; norm_num, s.sq_eq_one_U h1222 h37 h38 h39 hU,
    (s.Hs_eq_top h1222 h37 h38 h39 hU).1, h1, h2, h3,
    s.centralizer_U_eq h1222 h1226 h129 h1241 h10 h11 h37 h38 h39 hU hd,
    s.card_V_inf_cTil h1222 h37 h38 h39 hU hd, s.inf_V_le_V1 h1222 h37 h38 h39 hU, ?_⟩
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hTL := hy.normalizes
  have hQL := s.comm_le_V h1222 hU hd (by norm_num)
  have hOQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hcommL : ⁅pCoreOf 2 L, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro q hq l' hl'
    rw [commutatorElement_def]
    have e : q * l' * q⁻¹ * l'⁻¹ = (l' * q * l'⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem (hQL q (hOQ hq) l' hl')
  exact centralizer_V_eq h1222 h1226 h129 h1241 h10 h11 s.setting hcommL

theorem comm_U {h1222 : Stmt12_2_2} (hn : s.N3 h1222) {a b : G} (ha : a ∈ U714 T L V z)
    (hb : b ∈ U714 T L V z) : a * b = b * a := by
  have hinv : ∀ x ∈ U714 T L V z, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hn.sq_U x hx)
  have := hinv (a * b) (Subgroup.mul_mem _ ha hb)
  rw [mul_inv_rev, hinv a ha, hinv b hb] at this
  exact this.symm

theorem U_le_Qz
    {h1222 : Stmt12_2_2} (hn : s.N3 h1222) : U714 T L V z ≤ s.Qz h1222 := fun u hu =>
  ⟨T_le_H ((s.U_le_T h1222).1 hu), fun u' hu' => by
    rw [s.comm_U hn hu hu', mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _⟩

theorem Qz_le_H (h1222 : Stmt12_2_2) : s.Qz h1222 ≤ H714 T L V z := fun _ hx => hx.1

theorem z_comm_H (h1222 : Stmt12_2_2) {x : G} (hx : x ∈ H714 T L V z) : z * x = x * z :=
  (Subgroup.mem_centralizer_singleton_iff.mp (s.H_le_Gz h1222 hx)).symm

theorem z_mul_z : z * z = 1 := by
  rw [← pow_two, ← s.orderOf_z]
  exact pow_orderOf_eq_one z

theorem isMulCommutative_V
    (h1222 : Stmt12_2_2) : IsMulCommutative ↥V :=
  (S127.card_eq_of_1222 h1222 s.setting.hyp).1

theorem comm_V
    (h1222 : Stmt12_2_2) {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val ((s.isMulCommutative_V h1222).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem card_V1
    (h1222 : Stmt12_2_2) : Nat.card ↥(V1 T L V) = 4 := by
  have := s.isMulCommutative_V h1222
  exact (S127.Mod.lemma12_7_2_two h1222 s.setting.hyp).1.2

theorem exists_v
    (h1222 : Stmt12_2_2) : ∃ v ∈ V1 T L V, v ∉ Subgroup.zpowers z := by
  have hV14 := s.card_V1 h1222
  by_contra hno
  push Not at hno
  have hle : V1 T L V ≤ Subgroup.zpowers z := fun v hv => hno v hv
  have := Subgroup.card_le_of_le hle
  rw [hV14, Nat.card_zpowers, s.orderOf_z] at this
  omega

namespace N3

variable {s} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem exists_conj {u u' : G}
    (hu : u ∈ U714 T L V z) (hu' : u' ∈ U714 T L V z) (huz : u ∉ Subgroup.zpowers z)
    (hu'z : u' ∉ Subgroup.zpowers z) :
    ∃ h ∈ H714 T L V z, (h * u * h⁻¹)⁻¹ * u' ∈ Subgroup.zpowers z := by
  have : IsMulCommutative ↥(Ut T L V z) := (s.elemAbelian_Ut h1222).1
  have hW : ∀ w : ↥(Ut T L V z), w ^ 2 = 1 := fun w =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)
  have hne : ∀ {x : G} (hx : x ∈ U714 T L V z), x ∉ Subgroup.zpowers z →
      s.piU h1222 ⟨x, hx⟩ ≠ 1 := by
    intro x hx hxz
    rw [Ne, s.piU_eq_one_iff]
    rintro (h | h)
    · exact hxz (by rw [show x = 1 from congrArg Subtype.val h]; exact Subgroup.one_mem _)
    · exact hxz (by rw [show x = z from congrArg Subtype.val h]; exact Subgroup.mem_zpowers z)
  obtain ⟨φ, hφ⟩ := ElemAb.exists_mulAut_apply_eq hW (hne hu huz) (hne hu' hu'z)
  have hφr : φ ∈ (s.rho h1222).range := by
    rw [s.range_rho h1222, hn.hs_top]
    exact Subgroup.mem_top φ
  obtain ⟨h, rfl⟩ := hφr
  have hv' := congrArg Subtype.val hφ
  rw [s.rho_apply, s.piU_coe, s.piU_coe] at hv'
  have e : tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h) *
      tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.U_le_N h1222) ⟨u, hu⟩) *
      (tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h))⁻¹ =
      tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h *
        Subgroup.inclusion (s.U_le_N h1222) ⟨u, hu⟩ *
          (Subgroup.inclusion (s.H_le_N h1222) h)⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e] at hv'
  exact ⟨(h : G), h.2, secMk_eq_secMk_iff.mp hv'⟩

theorem exists_common {a b : G}
    (ha : a ∈ s.Qz h1222) (hb : b ∈ s.Qz h1222) :
    ∃ u ∈ U714 T L V z, u ∉ Subgroup.zpowers z ∧ a * u = u * a ∧ b * u = u * b := by
  have hzU : ∀ x ∈ U714 T L V z, z * x = x * z := fun x hx =>
    s.z_comm_H h1222 (T_le_H ((s.U_le_T h1222).1 hx))
  have h1 := card_le_two_mul_inf_centralizer hzU s.z_mul_z (fun x hx => ha.2 x hx)
  have h2 := card_le_two_mul_inf_centralizer (A := U714 T L V z ⊓ Subgroup.centralizer {a})
    (fun x hx => hzU x hx.1) s.z_mul_z (fun x hx => hb.2 x hx.1)
  rw [hn.card_U] at h1
  by_contra hno
  push Not at hno
  have hle : U714 T L V z ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} ≤
      Subgroup.zpowers z := by
    intro x hx
    by_contra hxz
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    exact hno x hx.1.1 hxz hxa.symm hxb.symm
  have h3 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, s.orderOf_z] at h3
  omega

theorem not_le_centralizer
    {u₀ : G} (hu₀ : u₀ ∈ U714 T L V z) (hu₀z : u₀ ∉ Subgroup.zpowers z) :
    ¬ s.Qz h1222 ≤ Subgroup.centralizer ({u₀} : Set G) := by
  intro hle
  have hQU : s.Qz h1222 ≤ H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G) := by
    intro a ha
    refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    by_cases huz : u ∈ Subgroup.zpowers z
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp huz
      exact (Commute.zpow_left (show Commute z a from s.z_comm_H h1222 ha.1) k).eq
    · obtain ⟨h, hh, hk⟩ := hn.exists_conj hu₀ hu hu₀z huz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hu' : u = h * u₀ * h⁻¹ * z ^ k := by rw [hk]; group
      have ha' : h⁻¹ * a * h ∈ s.Qz h1222 := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _
          ((H714 T L V z).inv_mem hh)) a).mp ha
        simpa using this
      have hc : (h⁻¹ * a * h) * u₀ = u₀ * (h⁻¹ * a * h) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hle ha')
      have hza : Commute (z ^ k) a := Commute.zpow_left (s.z_comm_H h1222 ha.1) k
      have hc' : a * (h * u₀ * h⁻¹) = (h * u₀ * h⁻¹) * a := by
        calc a * (h * u₀ * h⁻¹) = h * ((h⁻¹ * a * h) * u₀) * h⁻¹ := by group
          _ = h * (u₀ * (h⁻¹ * a * h)) * h⁻¹ := by rw [hc]
          _ = (h * u₀ * h⁻¹) * a := by group
      rw [hu']
      calc h * u₀ * h⁻¹ * z ^ k * a = h * u₀ * h⁻¹ * (z ^ k * a) := by group
        _ = h * u₀ * h⁻¹ * (a * z ^ k) := by rw [hza.eq]
        _ = (h * u₀ * h⁻¹ * a) * z ^ k := by group
        _ = a * (h * u₀ * h⁻¹) * z ^ k := by rw [hc']
        _ = a * (h * u₀ * h⁻¹ * z ^ k) := by group
  rw [hn.cent_U] at hQU
  have := Subgroup.card_le_of_le hQU
  rw [hn.card_Q, hn.card_U] at this
  norm_num at this

theorem card_C0 :
    Nat.card ↥(V ⊓ s.Qz h1222 ⊔ U714 T L V z) = 64 := by
  have hV14 := s.card_V1 h1222
  have hN : V ⊓ s.Qz h1222 ≤ Subgroup.normalizer (U714 T L V z : Set G) :=
    fun x hx => s.H_le_normalizer_U h1222 (V_le_H714 T L V z hx.1)
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  have hinf : U714 T L V z ⊓ (V ⊓ s.Qz h1222) = V1 T L V := by
    apply le_antisymm
    · exact fun x hx => hn.UV ⟨hx.1, hx.2.1⟩
    · intro x hx
      have hxU : x ∈ U714 T L V z := le_conjClosure _ _ hx
      exact ⟨hxU, (inf_le_left : V1 T L V ≤ V) hx, s.U_le_Qz hn hxU⟩
  rw [hinf, hV14, hn.card_U, hn.card_VQ, sup_comm] at h
  omega

theorem inf_centralizer_eq {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) :
    s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) = V ⊓ s.Qz h1222 ⊔ U714 T L V z := by
  have hvV : v ∈ V := (inf_le_left : V1 T L V ≤ V) hv
  have hvU : v ∈ U714 T L V z := le_conjClosure _ _ hv
  have hle : V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine sup_le (fun x hx => ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
      (fun x hx => ⟨s.U_le_Qz hn hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
    · exact s.comm_V h1222 hx.1 hvV
    · exact s.comm_U hn hx hvU
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hn.card_C0]
  have hlt : s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) < s.Qz h1222 :=
    lt_of_le_of_ne inf_le_left fun heq =>
      hn.not_le_centralizer hvU hvz (heq ▸ inf_le_right)
  have hQ : Nat.card ↥(s.Qz h1222) = 128 := by rw [hn.card_Q]; norm_num
  have h1 := Subgroup.card_dvd_of_le hlt.le
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [hQ] at h1 h2
  obtain ⟨k, hk⟩ := h1
  rcases k with _ | _ | k
  · simp at hk
  · omega
  · have : 128 ≥ Nat.card ↥(s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G)) * 2 := by
      rw [hk]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

@[expose] def zComm (z g : G) : Subgroup G where
  carrier := {w | w ∈ Subgroup.centralizer ({z} : Set G) ∧ g * w * g⁻¹ * w⁻¹ ∈ Subgroup.zpowers z}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hga⟩ ⟨hb, hgb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e, comm_of_mem_zpowers hgb ha, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ hga hgb
  inv_mem' := by
    rintro a ⟨ha, hga⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    have e : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * ((g * a * g⁻¹ * a⁻¹)⁻¹ * a) := by group
    rw [e, ← comm_of_mem_zpowers (Subgroup.inv_mem _ hga) ha, inv_mul_cancel_left]
    exact Subgroup.inv_mem _ hga

theorem comm_mem_C0 {a b : G}
    (ha : a ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z) (hb : b ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
  have hCz : V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun x hx => s.H_le_Gz h1222 hx.2.1)
      (fun x hx => s.H_le_Gz h1222 (T_le_H ((s.U_le_T h1222).1 hx)))
  have hgen : ∀ g, (g ∈ V ⊓ s.Qz h1222 ∨ g ∈ U714 T L V z) →
      V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ zComm z g := by
    intro g hg
    refine sup_le (fun y hy => ⟨hCz (Subgroup.mem_sup_left hy), ?_⟩)
      (fun u hu => ⟨hCz (Subgroup.mem_sup_right hu), ?_⟩)
    · rcases hg with hg | hg
      · rw [s.comm_V h1222 hg.1 hy.1, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have e : g * y * g⁻¹ * y⁻¹ = (y * g * y⁻¹ * g⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ (hy.2.2 g hg)
    · rcases hg with hg | hg
      · exact hg.2.2 u hu
      · rw [s.comm_U hn hg hu, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
  have hb' : V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ zComm z b := by
    refine sup_le (fun y hy => ⟨hCz (Subgroup.mem_sup_left hy), ?_⟩)
      (fun u hu => ⟨hCz (Subgroup.mem_sup_right hu), ?_⟩)
    · have e : b * y * b⁻¹ * y⁻¹ = (y * b * y⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ (hgen y (Or.inl hy) hb).2
    · have e : b * u * b⁻¹ * u⁻¹ = (u * b * u⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ (hgen u (Or.inr hu) hb).2
  have e : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ (hb' ha).2

theorem sq_mem_C0 {a : G}
    (ha : a ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z) : a ^ 2 ∈ Subgroup.zpowers z := by
  have h := s.setting.hyp
  have := s.isMulCommutative_V h1222
  have hN : V ⊓ s.Qz h1222 ≤ Subgroup.normalizer (U714 T L V z : Set G) :=
    fun x hx => s.H_le_normalizer_U h1222 (V_le_H714 T L V z hx.1)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at ha
  obtain ⟨y, hy, u, hu, rfl⟩ := ha
  have hy2 : y ^ 2 = 1 := S127.sq_eq_one_of_mem h.hyp hy.1
  have hu2 : u ^ 2 = 1 := hn.sq_U u hu
  have hc := hy.2.2 u hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hyu : y * u = z ^ k * (u * y) := by
    calc y * u = (y * u * y⁻¹ * u⁻¹) * (u * y) := by group
      _ = z ^ k * (u * y) := by rw [← hk]
  have hy1 : y * y = 1 := by rw [← pow_two]; exact hy2
  have hu1 : u * u = 1 := by rw [← pow_two]; exact hu2
  have e : (y * u) ^ 2 = z ^ k * (u * (y * y) * u) := by
    calc (y * u) ^ 2 = y * u * y * u := by rw [pow_two, ← mul_assoc]
      _ = z ^ k * (u * y) * y * u := by rw [hyu]
      _ = z ^ k * (u * (y * y) * u) := by group
  rw [e, hy1, mul_one, hu1, mul_one]
  exact Subgroup.zpow_mem_zpowers z k

end N3

end CFSG.Quasithin.H13.S127.L715.Set714
