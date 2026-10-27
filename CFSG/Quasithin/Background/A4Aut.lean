module

public import CFSG.Quasithin.Background.A4
public import CFSG.Quasithin.Background.A4Coprime

public section

namespace CFSG.Quasithin.A4

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type*} [Group G]

theorem mem_normalizer_centralizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : g⁻¹ * r * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg r).mp hr
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hr'
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * r := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem exists_minimal_le_subgroup [Finite G] {p : Subgroup G → Prop} {a : Subgroup G}
    (h : p a) : ∃ b, b ≤ a ∧ Minimal p b := by
  obtain ⟨b, hb, hmax⟩ := Finite.exists_le_maximal (α := (Subgroup G)ᵒᵈ)
    (p := fun x => p (OrderDual.ofDual x)) (a := OrderDual.toDual a) h
  exact ⟨OrderDual.ofDual b, hb, hmax⟩

@[expose] noncomputable def actionOn (V H : Subgroup G) (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    H →* MulAut V :=
  (conjAct V).comp (Subgroup.inclusion hH)

theorem actionOn_apply_coe {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) (h : H)
    (v : V) : ((actionOn V H hH h v : V) : G) = h * v * (h : G)⁻¹ := rfl

theorem actionOn_eq_one_iff {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (h : H) : actionOn V H hH h = 1 ↔ (h : G) ∈ Subgroup.centralizer (V : Set G) :=
  normalizerMonoidHom_eq_one_iff

theorem mem_autOn_iff {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    {a : MulAut V} : a ∈ autOn H V ↔ ∃ h : H, actionOn V H hH h = a := by
  unfold autOn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨Subgroup.inclusion hH h, h.2, rfl⟩

theorem autOn_mono {V H K : Subgroup G} (h : H ≤ K) : autOn H V ≤ autOn K V :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem autOn_subnormal {V H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (autOn H V) (autOn K V) :=
  subnormal_map (conjAct V) (subnormal_subgroupOf _ h)

theorem conjAct_eq_one_iff {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  normalizerMonoidHom_eq_one_iff

theorem autOn_le_centralizer_autOn {V X R : Subgroup G}
    (hc : ⁅X, R⁆ ≤ Subgroup.centralizer (V : Set G)) :
    autOn R V ≤ Subgroup.centralizer (autOn X V : Set (MulAut V)) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hb
  have hyR : (y : G) ∈ R := hy
  have hzX : (z : G) ∈ X := hz
  have hc' : (z : G) * y * (z : G)⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    hc (Subgroup.commutator_mem_commutator hzX hyR)
  have h1 : conjAct V (z * y * z⁻¹ * y⁻¹) = 1 := conjAct_eq_one_iff.mpr hc'
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : conjAct V z * conjAct V y * (conjAct V z)⁻¹ = conjAct V y := mul_inv_eq_one.mp h1
  calc conjAct V z * conjAct V y = conjAct V z * conjAct V y * (conjAct V z)⁻¹ * conjAct V z := by
        group
    _ = conjAct V y * conjAct V z := by rw [h2]

theorem exists_preimage_section {V X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    {Q : Subgroup (MulAut V)} (hQA : Q ≤ autOn X V)
    (hQn : autOn X V ≤ Subgroup.normalizer (Q : Set (MulAut V))) (hQ2 : IsPGroup 2 Q) :
    ∃ D : Subgroup G, D ≤ X ∧ X ≤ Subgroup.normalizer (D : Set G) ∧
      (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ X ⊓ Subgroup.centralizer (V : Set G)) ∧
      (∀ x : X, (x : G) ∈ D → actionOn V X hXV x ∈ Q) ∧
      ∀ q ∈ Q, ∃ x : X, (x : G) ∈ D ∧ actionOn V X hXV x = q := by
  set D : Subgroup G := (Q.comap (actionOn V X hXV)).map X.subtype with hD
  have hmem : ∀ x : G, x ∈ D ↔ ∃ y : X, (y : G) = x ∧ actionOn V X hXV y ∈ Q := by
    intro x
    rw [hD, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, rfl, hy⟩
    · rintro ⟨y, rfl, hy⟩
      exact ⟨y, hy, rfl⟩
  refine ⟨D, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · have key : ∀ g ∈ X, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
      intro g hg x hx
      obtain ⟨y, rfl, hy⟩ := (hmem x).mp hx
      refine (hmem _).mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, rfl, ?_⟩
      rw [map_mul, map_mul, map_inv]
      have hgA : actionOn V X hXV ⟨g, hg⟩ ∈ autOn X V :=
        (mem_autOn_iff hXV).mpr ⟨⟨g, hg⟩, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQn hgA) _).mp hy
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ (X.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  · intro d hd
    obtain ⟨y, rfl, hy⟩ := (hmem d).mp hd
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hy⟩
    refine ⟨k, X.pow_mem y.2 _, ?_⟩
    have h1 : actionOn V X hXV (y ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (actionOn_eq_one_iff hXV _).mp h1
  · intro x hx
    obtain ⟨y, hyx, hy⟩ := (hmem x).mp hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro q hq
    obtain ⟨y, hy⟩ := (mem_autOn_iff hXV).mp (hQA hq)
    exact ⟨y, (hmem _).mpr ⟨y, rfl, hy ▸ hq⟩, hy⟩

variable [Finite G]

theorem oTwoUpper_subgroupOf {H N : Subgroup G} (hHN : H ≤ N) :
    oTwoUpper (H.subgroupOf N) = (oTwoUpper H).subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hHN,
    Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le H).trans hHN)]

theorem oTwoUpper_autOn {V H : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    oTwoUpper (autOn H V) = autOn (oTwoUpper H) V := by
  unfold autOn
  rw [oTwoUpper_map, oTwoUpper_subgroupOf hH]

theorem pCoreOf_autOn_le_centerOf {V X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hX : X = oTwoUpper X) (hchief : NoncentralTwoChiefFactorsInO2 X)
    (hO : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G)) :
    pCoreOf 2 (autOn X V) ≤ centerOf (autOn X V) := by
  obtain ⟨D, hDX, hXD, hD2, -, hDQ⟩ := exists_preimage_section hXV (pCoreOf_le 2 (autOn X V))
    (le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  have hXN : X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer (hXV hg))
  have hcomm := commutator_le_of_chief_central hX hchief
    (le_inf (pCoreOf_le 2 X) hO) hXN inf_le_left hDX hXD hD2
  intro q hq
  obtain ⟨x, hxD, hxq⟩ := hDQ q hq
  refine ⟨pCoreOf_le 2 _ hq, ?_⟩
  show q ∈ Subgroup.centralizer (autOn X V : Set (MulAut V))
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨y, rfl⟩ := (mem_autOn_iff hXV).mp ha
  have hc : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (hcomm (Subgroup.commutator_mem_commutator hxD y.2)).2
  have h1 : actionOn V X hXV (x * y * x⁻¹ * y⁻¹) = 1 := (actionOn_eq_one_iff hXV _).mpr hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxq] at h1
  have h2 : q * actionOn V X hXV y * q⁻¹ = actionOn V X hXV y := mul_inv_eq_one.mp h1
  calc actionOn V X hXV y * q = q * actionOn V X hXV y * q⁻¹ * q := by rw [h2]
    _ = q * actionOn V X hXV y := by group

theorem pCoreOf_autOn_eq_bot {V X : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hall : TwoChiefFactorsInO2 X) (hO : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G)) :
    pCoreOf 2 (autOn X V) = ⊥ := by
  obtain ⟨D, hDX, hXD, hD2, -, hDQ⟩ := exists_preimage_section hXV (pCoreOf_le 2 (autOn X V))
    (le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  set N : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G) with hN
  have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
    fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer (hXV hg))
  have hDN : D ≤ N := by
    by_contra hDN
    have hND : N < D ⊔ N := lt_of_le_of_ne le_sup_right (fun h => hDN (h ▸ le_sup_left))
    obtain ⟨B, -, hB⟩ := exists_chief_factor (le_inf (pCoreOf_le 2 X) hO) hND
      (sup_le hDX inf_le_left)
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hXD hg, hXN hg⟩) hXN
      (exists_pow_mem_sup_of_pow_mem (hDX.trans hXN) hD2)
    exact hall _ _ hB
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hxD, hxq⟩ := hDQ q hq
  have h1 : actionOn V X hXV x = 1 := (actionOn_eq_one_iff hXV _).mpr (hDN hxD).2
  rw [Subgroup.mem_bot, ← hxq, h1]

end CFSG.Quasithin.A4
