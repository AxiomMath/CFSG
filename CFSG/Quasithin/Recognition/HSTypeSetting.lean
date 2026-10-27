module

public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Goldschmidt.Steps.Sec89a

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open

variable {G : Type*} [Group G]

abbrev hsH (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

abbrev hsQ (z : G) : Subgroup G := quasithinGenFitting (hsH z)

abbrev hsM (V : Subgroup G) : Subgroup G := Subgroup.normalizer (V : Set G)

abbrev hsP (V : Subgroup G) : Subgroup G := quasithinGenFitting (hsM V)

structure HSSetting (z : G) (V : Subgroup G) : Prop where
  orderOf_z : orderOf z = 2
  elem : IsElemAbelian 2 V
  card_V : Nat.card V = 8
  one : HSOne z
  two : HSTwo z V

theorem card_eq_card_mul_of_surjective {X N : Subgroup G} {Y : Type*} [Group Y] (hNX : N ≤ X)
    (φ : ↥X →* Y) (hφ : Function.Surjective φ) (hker : φ.ker = N.subgroupOf X) :
    Nat.card X = Nat.card N * Nat.card Y := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, mul_comm]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem card_Q (h : HSSetting z V) : Nat.card (hsQ z) = 64 :=
  card_of_isZ4Q8Q8 h.one.fstar

theorem Q_le_H (_h : HSSetting z V) : hsQ z ≤ hsH z :=
  quasithinGenFitting_le _

theorem card_H (h : HSSetting z V) : Nat.card (hsH z) = 64 * 120 := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  rw [card_eq_card_mul_of_surjective h.Q_le_H φ hφ hker, h.card_Q, Nat.card_perm,
    Nat.card_fin]
  rfl

theorem card_P (h : HSSetting z V) : Nat.card (hsP V) = 64 := by
  obtain ⟨e⟩ := h.two.fstar
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem P_le_M (_h : HSSetting z V) : hsP V ≤ hsM V :=
  quasithinGenFitting_le _

theorem card_M (h : HSSetting z V) : Nat.card (hsM V) = 64 * 168 := by
  obtain ⟨θ, hθ, hker⟩ := h.two.quot
  rw [card_eq_card_mul_of_surjective h.P_le_M θ hθ hker, h.card_P, card_SL_three_two]

theorem mem_H (_h : HSSetting z V) : z ∈ hsH z :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem mem_Q [Finite G] (h : HSSetting z V) : z ∈ hsQ z := by
  have hc : z ∈ Subgroup.centralizer (hsQ z : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun q hq => Subgroup.mem_centralizer_singleton_iff.mp (h.Q_le_H hq)
  exact centralizer_quasithinGenFitting_le (hsH z) ⟨h.mem_H, hc⟩

theorem sq_z (h : HSSetting z V) : z ^ 2 = 1 := by
  rw [← h.orderOf_z]
  exact pow_orderOf_eq_one z

theorem mem_V [Finite G] (h : HSSetting z V) : z ∈ V := by
  by_contra hzV
  have hzc : ∀ a ∈ V, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.Q_le_H (h.two.le ha))
  obtain ⟨hE, hcard⟩ :=
    CFSG.Goldschmidt.Sec89.isElemAbelian_sup_zpowers h.elem hzV h.sq_z hzc
  set E := V ⊔ Subgroup.zpowers z with hEdef
  have hEQ : E ≤ hsQ z := sup_le h.two.le ((Subgroup.zpowers_le).mpr h.mem_Q)
  have h8 := card_le_eight_of_isZ4Q8Q8 h.one.fstar (E.subgroupOf (hsQ z))
    (fun x hx y hy => Subtype.ext (by
      have := congrArg Subtype.val (hE.1.is_comm.comm (⟨x.1, hx⟩ : ↥E) ⟨y.1, hy⟩)
      simpa using this))
    (fun x hx => Subtype.ext (by
      have := hE.2 (x : G) hx
      simpa [sq] using this))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv] at h8
  rw [h.card_V] at hcard
  omega

theorem comm_z_of_mem_Q (h : HSSetting z V) {q : G} (hq : q ∈ hsQ z) : q * z = z * q :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.Q_le_H hq)

theorem z_ne_one (h : HSSetting z V) : z ≠ 1 := by
  intro h1
  have := h.orderOf_z
  rw [h1, orderOf_one] at this
  omega

theorem mul_comm_or_mul_z [Finite G] (h : HSSetting z V) {x y : G} (hx : x ∈ hsQ z)
    (hy : y ∈ hsQ z) : x * y = y * x ∨ x * y = y * x * z := by
  have hzQ := h.mem_Q
  rcases mul_comm_or_of_isZ4Q8Q8 h.one.fstar (z := ⟨z, hzQ⟩)
      (fun q => Subtype.ext (h.comm_z_of_mem_Q q.2).symm)
      (Subtype.ext (by simpa [sq] using h.sq_z))
      (fun h1 => h.z_ne_one (congrArg Subtype.val h1)) ⟨x, hx⟩ ⟨y, hy⟩ with hc | hc
  · exact Or.inl (congrArg Subtype.val hc)
  · exact Or.inr (congrArg Subtype.val hc)

theorem Q_le_M [Finite G] (h : HSSetting z V) : hsQ z ≤ hsM V := by
  have key : ∀ q ∈ hsQ z, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    rcases h.mul_comm_or_mul_z hq (h.two.le hv) with hc | hc
    · rw [hc, mul_inv_cancel_right]
      exact hv
    · have hzq : q * z = z * q := h.comm_z_of_mem_Q hq
      have : q * v * q⁻¹ = v * z := by
        rw [hc, mul_assoc, mul_assoc, ← mul_assoc q z, hzq]
        group
      rw [this]
      exact V.mul_mem hv h.mem_V
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key q hq v, fun hv => ?_⟩
  have := key q⁻¹ ((hsQ z).inv_mem hq) _ hv
  simpa [mul_assoc] using this

theorem P_comm (h : HSSetting z V) {x y : G} (hx : x ∈ hsP V) (hy : y ∈ hsP V) :
    x * y = y * x := by
  obtain ⟨e⟩ := h.two.fstar
  have := congrArg (fun w => (e.symm w : G)) (mul_comm (e ⟨x, hx⟩) (e ⟨y, hy⟩))
  simpa only [← map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using this

theorem isPGroup_P (h : HSSetting z V) : IsPGroup 2 (hsP V) :=
  IsPGroup.of_card (n := 6) (by rw [h.card_P]; norm_num)

theorem isPGroup_V (h : HSSetting z V) : IsPGroup 2 V :=
  IsPGroup.of_card (n := 3) (by rw [h.card_V]; norm_num)

theorem P_eq_pCoreOf [Finite G] (h : HSSetting z V) : hsP V = pCoreOf 2 (hsM V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPO : hsP V ≤ pCoreOf 2 (hsM V) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.P_le_M
      (le_normalizer_quasithinGenFitting _) h.isPGroup_P
  refine (quasithinGenFitting_eq_pCoreOf_iff (hsM V) 2).mpr ?_
  intro x hx
  refine hPO (centralizer_quasithinGenFitting_le (hsM V) ⟨hx.1, ?_⟩)
  exact Subgroup.centralizer_le (by exact_mod_cast hPO) hx.2

theorem V_le_P [Finite G] (h : HSSetting z V) : V ≤ hsP V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.P_eq_pCoreOf]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    h.isPGroup_V

theorem mem_V_of_mem_P [Finite G] (h : HSSetting z V) {x : G} (hx : x ∈ hsP V)
    (hx2 : x * x = 1) : x ∈ V := by
  classical
  have := Fintype.ofFinite ↥(hsP V)
  obtain ⟨e⟩ := h.two.fstar
  set S := (Finset.univ.filter fun y : ↥(hsP V) => y * y = 1) with hS
  set T := (Finset.univ.filter fun y : ↥(hsP V) => (y : G) ∈ V) with hT
  have hTS : T ⊆ S := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, Subtype.ext ?_⟩
    have := h.elem.2 _ hy.2
    simpa [sq] using this
  have hScard : S.card = 8 := by
    rw [hS, ← Fintype.card_subtype,
      Fintype.card_congr (e.toEquiv.subtypeEquiv (q := fun b : Z4Cube => b * b = 1) fun y => by
        simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
        rw [← map_mul, MulEquiv.map_eq_one_iff]),
      Fintype.card_subtype]
    exact Z4Cube.card_sq_eq_one
  have hTcard : T.card = 8 := by
    have hc : Fintype.card {y : ↥(hsP V) // (y : G) ∈ V} = Nat.card V := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le_P).toEquiv
    rw [hT, ← Fintype.card_subtype, hc, h.card_V]
  have hEq : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hScard, hTcard])
  have hxS : (⟨x, hx⟩ : ↥(hsP V)) ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hx2⟩
  rw [← hEq] at hxS
  exact (Finset.mem_filter.mp hxS).2

theorem P_le_centralizer_V [Finite G] (h : HSSetting z V) :
    hsP V ≤ Subgroup.centralizer (V : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hv => h.P_comm (h.V_le_P hv) hx

theorem P_le_H [Finite G] (h : HSSetting z V) : hsP V ≤ hsH z := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (h.P_le_centralizer_V hx) z h.mem_V).symm

theorem centralizer_subgroupOf_normal :
    ((Subgroup.centralizer (V : Set G)).subgroupOf (hsM V)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have hw : (g : G)⁻¹ * v * (g : G) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((hsM V).inv_mem g.2) v).mp hv
    simpa using this
  have hc := hn _ hw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc v * ((g : G) * n * (g : G)⁻¹)
      = (g : G) * ((g : G)⁻¹ * v * (g : G) * n) * (g : G)⁻¹ := by group
    _ = (g : G) * (n * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [hc]
    _ = (g : G) * n * (g : G)⁻¹ * v := by group

theorem centralizer_V_eq [Finite G] (h : HSSetting z V) :
    hsM V ⊓ Subgroup.centralizer (V : Set G) = hsP V := by
  refine le_antisymm ?_ (le_inf h.P_le_M h.P_le_centralizer_V)
  obtain ⟨θ, hθ, hker⟩ := h.two.quot
  set N := (Subgroup.centralizer (V : Set G)).subgroupOf (hsM V) with hN
  have hNn : N.Normal := centralizer_subgroupOf_normal
  have hkN : θ.ker ≤ N := by
    rw [hker]
    intro y hy
    exact h.P_le_centralizer_V hy
  have := hNn.map θ hθ
  rcases isSimpleGroup_SL_three_two.eq_bot_or_eq_top_of_normal (N.map θ) with hb | ht
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥(hsM V)) ∈ N := hx.2
    have h1 : θ ⟨x, hx.1⟩ = 1 := by
      have := Subgroup.mem_map_of_mem θ hxN
      rwa [hb, Subgroup.mem_bot] at this
    have hxk : (⟨x, hx.1⟩ : ↥(hsM V)) ∈ θ.ker := h1
    rw [hker] at hxk
    exact hxk
  · exfalso
    have hNtop : N = ⊤ := by
      have := Subgroup.comap_map_eq θ N
      rw [ht, Subgroup.comap_top, sup_eq_left.mpr hkN] at this
      exact this.symm
    have hMH : hsM V ≤ hsH z := by
      intro m hm
      have hmN : (⟨m, hm⟩ : ↥(hsM V)) ∈ N := hNtop ▸ Subgroup.mem_top _
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hmN z h.mem_V).symm
    have hdvd := Subgroup.card_dvd_of_le hMH
    rw [h.card_M, h.card_H] at hdvd
    norm_num at hdvd

theorem card_H_inf_M [Finite G] (h : HSSetting z V) :
    Nat.card ↥(hsH z ⊓ hsM V) = 512 * 3 := by
  classical
  let : MulAction ↥(hsM V) G :=
    MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp (hsM V).subtype)
  have hsmul : ∀ (m : ↥(hsM V)) (g : G), m • g = (m : G) * g * (m : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥(hsM V) z = (hsH z ⊓ hsM V).subgroupOf (hsM V) := by
    ext m
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hm
      refine ⟨?_, m.2⟩
      calc (m : G) * z = (m : G) * z * (m : G)⁻¹ * (m : G) := by group
        _ = z * (m : G) := by rw [hm]
    · rintro ⟨hm, -⟩
      rw [hm, mul_inv_cancel_right]
  have hcardstab : Nat.card (MulAction.stabilizer ↥(hsM V) z) = Nat.card ↥(hsH z ⊓ hsM V) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have horb : MulAction.orbit ↥(hsM V) z ⊆ (V : Set G) \ {1} := by
    rintro _ ⟨m, rfl⟩
    show m • z ∈ (V : Set G) \ {1}
    rw [hsmul]
    refine ⟨(Subgroup.mem_normalizer_iff.mp m.2 z).mp h.mem_V, ?_⟩
    · rw [Set.mem_singleton_iff]
      intro h1
      apply h.z_ne_one
      have : z = (m : G)⁻¹ * ((m : G) * z * (m : G)⁻¹) * (m : G) := by group
      rw [this, h1]
      group
  have hV7 : ((V : Set G) \ {1}).ncard = 7 := by
    rw [Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ (V : Set G) from V.one_mem),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_V]
  have horb7 : (MulAction.orbit ↥(hsM V) z).ncard ≤ 7 :=
    hV7 ▸ Set.ncard_le_ncard horb (Set.toFinite _)
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(hsM V) z)
  rw [MulAction.index_stabilizer, hcardstab, h.card_M] at hmul
  have hdvdH : Nat.card ↥(hsH z ⊓ hsM V) ∣ 64 * 120 :=
    h.card_H ▸ Subgroup.card_dvd_of_le inf_le_left
  set k := (MulAction.orbit ↥(hsM V) z).ncard with hk
  have hkpos : 0 < k := (Set.ncard_pos (Set.toFinite _)).mpr (MulAction.nonempty_orbit z)
  have h7 : 7 ∣ Nat.card ↥(hsH z ⊓ hsM V) * k := by
    rw [hmul]
    norm_num
  have hc7 : ¬ 7 ∣ Nat.card ↥(hsH z ⊓ hsM V) := fun h7c => by
    have := h7c.trans hdvdH
    norm_num at this
  obtain ⟨j, hj⟩ := ((Nat.Prime.dvd_mul (by norm_num)).mp h7).resolve_left hc7
  have hk7 : k = 7 := by omega
  rw [hk7] at hmul
  omega

end HSSetting

end CFSG.Quasithin.HSType
