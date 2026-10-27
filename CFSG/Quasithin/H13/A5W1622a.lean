module

public import CFSG.Quasithin.H13.A5W1618j

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_comm_mem {H Z : Subgroup G} (hH : CharTwo H) (hZ2 : IsPGroup 2 ↥Z)
    (hZc : ∀ ζ ∈ Z, ∀ h ∈ H, ζ * h = h * ζ) {x : G} (hx : x ∈ H)
    (hxc : ∀ r ∈ pCoreOf 2 H, x * r * x⁻¹ * r⁻¹ ∈ Z) : x ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hRdef
  have hRH : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmul : ∀ a b : G, (a ∈ H ∧ ∀ r ∈ R, a * r * a⁻¹ * r⁻¹ ∈ Z) →
      (b ∈ H ∧ ∀ r ∈ R, b * r * b⁻¹ * r⁻¹ ∈ Z) →
      (a * b ∈ H ∧ ∀ r ∈ R, a * b * r * (a * b)⁻¹ * r⁻¹ ∈ Z) := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨H.mul_mem ha hb, fun r hr => ?_⟩
    set ζ := b * r * b⁻¹ * r⁻¹ with hζ
    have hζZ : ζ ∈ Z := hbc r hr
    have e : a * b * r * (a * b)⁻¹ * r⁻¹ = a * (ζ * r) * a⁻¹ * r⁻¹ := by
      rw [hζ]; group
    have hζa : ζ * a = a * ζ := hZc ζ hζZ a ha
    have e2 : a * (ζ * r) * a⁻¹ * r⁻¹ = ζ * (a * r * a⁻¹ * r⁻¹) := by
      calc a * (ζ * r) * a⁻¹ * r⁻¹ = (a * ζ) * r * a⁻¹ * r⁻¹ := by group
        _ = (ζ * a) * r * a⁻¹ * r⁻¹ := by rw [hζa]
        _ = ζ * (a * r * a⁻¹ * r⁻¹) := by group
    rw [e, e2]
    exact Z.mul_mem hζZ (hac r hr)
  have hinv : ∀ a : G, (a ∈ H ∧ ∀ r ∈ R, a * r * a⁻¹ * r⁻¹ ∈ Z) →
      (a⁻¹ ∈ H ∧ ∀ r ∈ R, a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ ∈ Z) := by
    rintro a ⟨ha, hac⟩
    refine ⟨H.inv_mem ha, fun r hr => ?_⟩
    have hr' : a⁻¹ * r * a ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hHR (H.inv_mem ha)) r).mp hr
      simpa using this
    have e : a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ =
        (a * (a⁻¹ * r * a) * a⁻¹ * (a⁻¹ * r * a)⁻¹)⁻¹ := by group
    rw [e]
    exact Z.inv_mem (hac _ hr')
  let C : Subgroup G :=
    { carrier := {h | h ∈ H ∧ ∀ r ∈ R, h * r * h⁻¹ * r⁻¹ ∈ Z}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := ⟨H.one_mem, fun r _ => by simp [Z.one_mem]⟩
      inv_mem' := fun {a} ha => hinv a ha }
  have hmemC : ∀ {h : G}, h ∈ C ↔ h ∈ H ∧ ∀ r ∈ R, h * r * h⁻¹ * r⁻¹ ∈ Z := Iff.rfl
  have hCH : C ≤ H := fun h hh => hh.1
  have key : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcH, hcc⟩ := hmemC.mp hc
    refine hmemC.mpr ⟨H.mul_mem (H.mul_mem hg hcH) (H.inv_mem hg), fun r hr => ?_⟩
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hHR (H.inv_mem hg)) r).mp hr
      simpa using this
    have hζ := hcc _ hr'
    set ζ := c * (g⁻¹ * r * g) * c⁻¹ * (g⁻¹ * r * g)⁻¹ with hζdef
    have e : g * c * g⁻¹ * r * (g * c * g⁻¹)⁻¹ * r⁻¹ = g * ζ * g⁻¹ := by
      rw [hζdef]; group
    rw [e, ← hZc ζ hζ g hg, mul_inv_cancel_right]
    exact hζ
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (key g hg) fun c hc => by
      have := key g⁻¹ (H.inv_mem hg) c hc
      rwa [inv_inv] at this
  have hodd : ∀ c ∈ C, Odd (orderOf c) → c = 1 := by
    intro c hc hco
    obtain ⟨hcH, hcc⟩ := hmemC.mp hc
    have hcR : c ∈ R := by
      refine hH ⟨hcH, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      set ζ := c * r * c⁻¹ * r⁻¹ with hζdef
      have hζZ : ζ ∈ Z := hcc r hr
      have hζc : ζ * c = c * ζ := hZc ζ hζZ c hcH
      have hpow : ∀ j : ℕ, c ^ j * r * (c ^ j)⁻¹ = ζ ^ j * r := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have hζj : ζ ^ j * c = c * ζ ^ j := (Commute.pow_left hζc j).eq
          calc c ^ (j + 1) * r * (c ^ (j + 1))⁻¹ = c * (c ^ j * r * (c ^ j)⁻¹) * c⁻¹ := by
                rw [pow_succ']; group
            _ = c * (ζ ^ j * r) * c⁻¹ := by rw [ih]
            _ = (c * ζ ^ j) * r * c⁻¹ := by group
            _ = (ζ ^ j * c) * r * c⁻¹ := by rw [hζj]
            _ = ζ ^ j * (c * r * c⁻¹ * r⁻¹) * r := by group
            _ = ζ ^ (j + 1) * r := by rw [pow_succ]
      have hm := hpow (orderOf c)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
      have hζm : ζ ^ orderOf c = 1 := by
        have := congrArg (· * r⁻¹) hm
        simpa using this.symm
      obtain ⟨e, he⟩ := hZ2 ⟨ζ, hζZ⟩
      have hζe : ζ ^ 2 ^ e = 1 := by
        have := congrArg Subtype.val he
        simpa using this
      have h1 : orderOf ζ ∣ Nat.gcd (orderOf c) (2 ^ e) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hζm) (orderOf_dvd_of_pow_eq_one hζe)
      have hcop : Nat.gcd (orderOf c) (2 ^ e) = 1 :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hco)
      rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
      have h2 : c * r * c⁻¹ * r⁻¹ = 1 := h1
      calc r * c = (c * r * c⁻¹ * r⁻¹)⁻¹ * c * r := by group
        _ = c * r := by rw [h2]; group
    obtain ⟨f, hf⟩ := hR2 ⟨c, hcR⟩
    have hcf : c ^ 2 ^ f = 1 := by
      have := congrArg Subtype.val hf
      simpa using this
    have h1 : orderOf c ∣ Nat.gcd (orderOf c) (2 ^ f) :=
      Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hcf)
    have hcop : Nat.gcd (orderOf c) (2 ^ f) = 1 :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hco)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨k, ?_⟩
    have hck : ((c : G) ^ 2 ^ k) ∈ C := C.pow_mem c.2 _
    have hord : orderOf ((c : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, by rw [Subgroup.orderOf_coe]; exact hn⟩,
        Subgroup.orderOf_coe, hn]
      exact Nat.mul_div_cancel_left m (by positivity)
    have h1 := hodd _ hck (hord ▸ hm)
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h1)
  exact le_pCoreOf_of_normalizes hCH hHC hC2 (hmemC.mpr ⟨hx, hxc⟩)

theorem comm_mem_blockU_of_mem_pCoreOf {H K₀ : Subgroup G} (hK₀H : K₀ ≤ H) (hK₀p : ⁅K₀, K₀⁆ = K₀)
    {x : G} (hxO : x ∈ pCoreOf 2 H) (hxK₀ : x ∈ Subgroup.normalizer (K₀ : Set G)) :
    ∀ k ∈ K₀, k⁻¹ * x * k * x⁻¹ ∈ blockU K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH : H ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQK : blockQ K₀ ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hQn : K₀ ≤ Subgroup.normalizer (blockQ K₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  refine comm_mem_commutator_of_perfect hQK hQn hK₀p hxK₀ fun k hk => ?_
  have hmem : k⁻¹ * x * k * x⁻¹ ∈ K₀ ⊓ pCoreOf 2 H := by
    refine ⟨?_, ?_⟩
    · have e : k⁻¹ * x * k * x⁻¹ = k⁻¹ * (x * k * x⁻¹) := by group
      rw [e]
      exact K₀.mul_mem (K₀.inv_mem hk) ((Subgroup.mem_normalizer_iff.mp hxK₀ k).mp hk)
    · have hkx : k⁻¹ * x * k ∈ pCoreOf 2 H := by
        have := (Subgroup.mem_normalizer_iff.mp (hOH (hK₀H (K₀.inv_mem hk))) x).mp hxO
        simpa using this
      exact (pCoreOf 2 H).mul_mem hkx ((pCoreOf 2 H).inv_mem hxO)
  refine le_pCoreOf_of_normalizes inf_le_left (fun k' hk' => ?_) (hO2.to_le inf_le_right) hmem
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk', hOH (hK₀H hk')⟩

end General

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isPGroup_zpowers_v12 : IsPGroup 2 ↥(Subgroup.zpowers S.v12) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  have hv : S.v12 ^ 2 = 1 := S.elemAbelian_V.2 _ S.v12_mem_V
  rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hv, one_zpow, Subgroup.coe_one]

theorem zpowers_v12_comm {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    ∀ ζ ∈ Subgroup.zpowers S.v12, ∀ h ∈ H, ζ * h = h * ζ := by
  intro ζ hζ h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
  have hc : Commute h S.v12 := Subgroup.mem_centralizer_singleton_iff.mp (hH hh)
  exact (hc.zpow_right k).eq.symm

theorem a_mem_pCoreOf (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {H : Subgroup G} (hTH : S.Tv ≤ H) (hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hH : CharTwo H) : S.a ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) hTH hHG
  have hOT : pCoreOf 2 H ≤ S.Tv :=
    le_of_isPGroup_of_le_normalizer hsyl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  exact mem_pCoreOf_of_comm_mem hH S.isPGroup_zpowers_v12 (S.zpowers_v12_comm hHG)
    (hTH S.a_mem_Tv) fun r hr => S.comm_a_Tv (hOT hr)

theorem z_mem_Tv : S.z ∈ S.Tv :=
  (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1) (S.V1_le_omega_Tv (Subgroup.mem_zpowers _))

theorem z_mem_pCoreOf (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {H : Subgroup G} (hTH : S.Tv ≤ H) (hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hH : CharTwo H) : S.z ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) hTH hHG
  have hOT : pCoreOf 2 H ≤ S.Tv :=
    le_of_isPGroup_of_le_normalizer hsyl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  refine mem_pCoreOf_of_comm_mem hH S.isPGroup_zpowers_v12 (S.zpowers_v12_comm hHG)
    (hTH S.z_mem_Tv) fun r hr => ?_
  have hr' : r ∈ T := (Subgroup.mem_inf.mp (hOT hr)).1
  have h1 : r * S.z * r⁻¹ = S.z := S.conj_z_of_mem_T hr'
  have hc : S.z * r = r * S.z := by
    calc S.z * r = (r * S.z * r⁻¹) * r := by rw [h1]
      _ = r * S.z := by group
  have e : S.z * r * S.z⁻¹ * r⁻¹ = 1 := by rw [hc]; group
  rw [e]
  exact Subgroup.one_mem _

theorem comm_mem_blockU (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) :
    (∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ blockU K₀) ∧
      ∀ k ∈ K₀, k⁻¹ * S.z * k * S.z⁻¹ ∈ blockU K₀ := by
  have hHG : K₀ ⊔ S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  exact ⟨comm_mem_blockU_of_mem_pCoreOf le_sup_left hK₀p
      (S.a_mem_pCoreOf h1222 h517 le_sup_right hHG hchar) (hTK₀ S.a_mem_Tv),
    comm_mem_blockU_of_mem_pCoreOf le_sup_left hK₀p
      (S.z_mem_pCoreOf h1222 h517 le_sup_right hHG hchar) (hTK₀ S.z_mem_Tv)⟩

theorem false_of_comm_mem_of_fixed (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hK₀A : K₀ ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ A) {Y : Subgroup G} (hYK : Y ≤ K₀)
    (hYa : ∀ y ∈ Y, y * S.a * y⁻¹ = S.a)
    (hfix : ∀ m ∈ A, (∀ y ∈ Y, y * m * y⁻¹ = m) → ∀ k ∈ K₀, k * m * k⁻¹ = m) : False := by
  classical
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hsylH : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right
      (sup_le hK₀G S.Tv_le_Gv)
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  let ρ : ↥K₀ →* MulAut ↥A := (conjAct A).comp (Subgroup.inclusion hK₀A)
  have hρ : ∀ (g : ↥K₀) (u : ↥A), ((ρ g u : ↥A) : G) = g * u * (g : G)⁻¹ := fun g u =>
    InternalSec.coe_conjAct_apply _ u
  let δ : ↥K₀ → ↥A := fun k => ⟨(k : G)⁻¹ * S.a * k * S.a⁻¹, hcomm k k.2⟩
  have hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h := by
    intro g h
    apply Subtype.ext
    rw [Subgroup.coe_mul, hρ]
    simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hA2' : ∀ u : ↥A, u ^ 2 = 1 := fun u =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA2 u u.2)
  have : IsMulCommutative ↥A := ⟨⟨fun u w => Subtype.ext (hAc u u.2 w w.2)⟩⟩
  set Z₀ : Subgroup ↥A := (Subgroup.zpowers S.v12).subgroupOf A with hZ₀def
  have hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hρ]
    have hzv : (z : G) ∈ Subgroup.zpowers S.v12 := hz
    rw [← S.zpowers_v12_comm hK₀G _ hzv _ g.2, mul_inv_cancel_right]
  set D : Subgroup ↥K₀ := (S.Tv ⊓ K₀).subgroupOf K₀ with hDdef
  have hD : ∀ d ∈ D, δ d ∈ Z₀ := by
    intro d hd
    have hdT : (d : G) ∈ S.Tv := (Subgroup.mem_subgroupOf.mp hd).1
    show (d : G)⁻¹ * S.a * d * S.a⁻¹ ∈ Subgroup.zpowers S.v12
    have h1 := S.comm_a_Tv (S.Tv.inv_mem hdT)
    have e : (d : G)⁻¹ * S.a * d * S.a⁻¹ = (S.a * (d : G)⁻¹ * S.a⁻¹ * (d : G)⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hodd : ¬ 2 ∣ D.index := hS₀.2.2
  have hperf : commutator ↥K₀ = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK₀p)
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index hA2' ρ δ hδ Z₀ hZ₀ D hD hodd hperf
  have hmk : ∀ k : ↥K₀, (k : G)⁻¹ * S.a * k * S.a⁻¹ = (k : G)⁻¹ * m * k * (m : G)⁻¹ := by
    intro k
    have h1 := congrArg Subtype.val (hm k)
    rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv] at h1
    simp only [δ, Subgroup.coe_inv, inv_inv] at h1
    rw [h1]
  have hmY : ∀ y ∈ Y, y * (m : G) * y⁻¹ = m := by
    intro y hy
    have h1 := hmk ⟨y, hYK hy⟩
    have h2 : y⁻¹ * S.a * y * S.a⁻¹ = 1 := by
      have h3 : S.a * y = y * S.a := by
        calc S.a * y = (y * S.a * y⁻¹) * y := by rw [hYa y hy]
          _ = y * S.a := by group
      calc y⁻¹ * S.a * y * S.a⁻¹ = y⁻¹ * (S.a * y) * S.a⁻¹ := by group
        _ = 1 := by rw [h3]; group
    have h4 : y⁻¹ * (m : G) * y * (m : G)⁻¹ = 1 := by rw [← h2]; exact h1.symm
    calc y * (m : G) * y⁻¹ = y * (y⁻¹ * (m : G) * y * (m : G)⁻¹)⁻¹ * y⁻¹ * m := by group
      _ = m := by rw [h4]; group
  have hmK := hfix m m.2 hmY
  have hK₀a : K₀ ≤ Subgroup.centralizer ({S.a} : Set G) := by
    intro k hk
    have h1 := hmk ⟨k, hk⟩
    have h3 : k⁻¹ * (m : G) * k * (m : G)⁻¹ = 1 := by
      have h5 : (m : G) * k = k * m := by
        calc (m : G) * k = (k * m * k⁻¹) * k := by rw [hmK k hk]
          _ = k * m := by group
      calc k⁻¹ * (m : G) * k * (m : G)⁻¹ = k⁻¹ * ((m : G) * k) * (m : G)⁻¹ := by group
        _ = 1 := by rw [h5]; group
    have h4 : k⁻¹ * S.a * k * S.a⁻¹ = 1 := h1.trans h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : S.a * k = k * S.a := by
      calc S.a * k = k * (k⁻¹ * S.a * k * S.a⁻¹) * S.a := by group
        _ = k * S.a := by rw [h4]; group
    exact h5.symm
  obtain ⟨g, -, hga⟩ := S.exists_conj_a
  refine S.not_le_centralizer_conj h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz g (fun t ht => by rw [hga]; exact S.comm_a_Tv ht) ?_
  rw [hga]
  exact hK₀a

end Setting

end CFSG.Quasithin.H13.A5
