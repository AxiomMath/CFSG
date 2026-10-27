module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.Sporadic.J4
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

namespace NoJ4

theorem pow_mul_mul_inv_pow {X : Type*} [Group X] {x y : X} (h : Commute ⁅x, y⁆ x) (n : ℕ) :
    x ^ n * y * (x ^ n)⁻¹ = ⁅x, y⁆ ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]
      group
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x ^ n * (x * y * x⁻¹) * (x ^ n)⁻¹ := by group
      _ = x ^ n * (⁅x, y⁆ * y) * (x ^ n)⁻¹ := by rw [e1]
      _ = ⁅x, y⁆ * (x ^ n * y * (x ^ n)⁻¹) := by
        have hc : Commute ⁅x, y⁆ (x ^ n) := h.pow_right n
        calc x ^ n * (⁅x, y⁆ * y) * (x ^ n)⁻¹ = (x ^ n * ⁅x, y⁆) * y * (x ^ n)⁻¹ := by group
          _ = (⁅x, y⁆ * x ^ n) * y * (x ^ n)⁻¹ := by rw [hc.eq]
          _ = ⁅x, y⁆ * (x ^ n * y * (x ^ n)⁻¹) := by group
      _ = ⁅x, y⁆ ^ (n + 1) * y := by rw [ih, pow_succ', mul_assoc]

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_isSporadic {X : Type} [Group X]
    (hX : IsSporadic .J4 X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := hX
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.isSimpleGroup_J4
  exact MulEquiv.isSimpleGroup e

theorem exists_e9 {X : Type} [Group X] (hX : IsSporadic .J4 X) :
    ∃ a b : X, orderOf a = 3 ∧ orderOf b = 3 ∧ Commute a b ∧ b ∉ Subgroup.zpowers a := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* CFSG.Blueprint.NativeSporadic.J4 := e₀
  obtain ⟨x, y, -, hx3, -, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := by
    have h := pow_mul_mul_inv_pow hzx 3
    rw [hx3, one_mul, inv_one, mul_one] at h
    have h2 := congrArg (· * y⁻¹) h
    simpa using h2.symm
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hz1 (by simp)
  have hoz : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hz3 hz1
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨e.symm ⁅x, y⁆, e.symm x, by rw [MulEquiv.orderOf_eq]; exact hoz,
    by rw [MulEquiv.orderOf_eq]; exact hox, hzx.map e.symm, fun hb => hz1 ?_⟩
  have hzy2 : Commute (e.symm ⁅x, y⁆) (e.symm y) := hzy.map e.symm
  have hzy' : e.symm ⁅x, y⁆ ∈ Subgroup.centralizer ({e.symm y} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzy2.eq
  have hxy : e.symm x ∈ Subgroup.centralizer ({e.symm y} : Set X) :=
    (Subgroup.zpowers_le.mpr hzy') hb
  have hxy' := Subgroup.mem_centralizer_singleton_iff.mp hxy
  have h2 : x * y = y * x := by
    have := congrArg e hxy'
    simpa using this
  rw [commutatorElement_def, h2]
  group

theorem exists_ne_comm {X : Type} [Group X]
    (hX : IsSporadic .J4 X) : ∃ c d : X, c * d ≠ d * c := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* CFSG.Blueprint.NativeSporadic.J4 := e₀
  obtain ⟨x, y, -, -, -, hz1, -, -, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  refine ⟨e.symm x, e.symm y, fun h => hz1 ?_⟩
  have h' := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at h'
  rw [commutatorElement_def, h']
  group

theorem isComponentOf
    {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) (hK : IsSporadic .J4 ↥K) :
    IsComponentOf K H := by
  have : IsSimpleGroup ↥K := isSimpleGroup_of_isSporadic hK
  obtain ⟨a, b, hab⟩ := exists_ne_comm hK
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1
  exact ⟨le_of_mem_cComp c.K_mem, subnormal_of_mem_cComp c.K_mem,
    A3.isQuasisimple_iff_open.mp hq⟩

omit [Finite G] in
theorem eq_one_of_mem_centralizer
    {K : Subgroup G} (hK : IsSporadic .J4 ↥K) {g : G} (hgK : g ∈ K)
    (hg : ∀ k ∈ K, k * g = g * k) : g = 1 := by
  have : IsSimpleGroup ↥K := isSimpleGroup_of_isSporadic hK
  obtain ⟨a, b, hab⟩ := exists_ne_comm hK
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).2
  have hgZ : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hg k k.2)
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact congrArg Subtype.val hgZ

omit [Finite G] in
theorem inf_centralizer_eq_bot
    {K : Subgroup G} (hK : IsSporadic .J4 ↥K) :
    K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_
  exact eq_one_of_mem_centralizer hK hg.1 fun k hk =>
    Subgroup.mem_centralizer_iff.mp hg.2 k hk

theorem normal
    {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H)
    (c : Conf4212 G T M L I H K) (hK : IsSporadic .J4 ↥K) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := isComponentOf c hK
  intro h hh
  by_contra hN
  set K' := K.map (MulAut.conj h).toMonoidHom with hK'
  have hc' : IsComponentOf K' H := B113.isComponentOf_conj hc hh
  have hne : K ≠ K' := by
    intro he
    apply hN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [he]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [he] at hx
      obtain ⟨y, hy', hyx⟩ := hx
      have : y = x := by
        simpa [MulAut.conj_apply] using hyx
      rwa [← this]
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x :=
    (F918V5G.isComponentOf_eq_or_commute hc hc').resolve_left hne
  have hKK' : ∀ g ∈ K, g ∈ K' → g = 1 := fun g hgK hgK' =>
    eq_one_of_mem_centralizer hK hgK fun k hk => hcomm k hk g hgK'
  obtain ⟨a, b, ha, hb, hab, hbA⟩ := exists_e9 hK
  have ha' : orderOf (a : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
  have hE₀ : IsElemAbelian 3 (⊥ : Subgroup G) :=
    ⟨⟨⟨fun x y => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  have ha1 : (a : G) ∉ (⊥ : Subgroup G) := by
    intro h0
    rw [Subgroup.mem_bot] at h0
    rw [h0, orderOf_one] at ha'
    omega
  obtain ⟨hE₁, hE₁c⟩ := exists_elemAbelian_sup_zpowers hE₀ ha' (fun e he => by
    rw [Subgroup.mem_bot.mp he]; exact Commute.one_left _) ha1
  rw [bot_sup_eq] at hE₁ hE₁c
  have hbE₁ : (b : G) ∉ Subgroup.zpowers (a : G) := by
    rintro ⟨k, hk⟩
    apply hbA
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hk
  have hcb : ∀ e ∈ Subgroup.zpowers (a : G), Commute e (b : G) := by
    intro e he
    have hle : Subgroup.zpowers (a : G) ≤ Subgroup.centralizer ({(b : G)} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := congrArg Subtype.val hab.eq
        simpa using this))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE₂, hE₂c⟩ := exists_elemAbelian_sup_zpowers hE₁ hb' hcb hbE₁
  set E₂ := Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers (b : G) with hE₂def
  have hE₂K : E₂ ≤ K := sup_le (Subgroup.zpowers_le.mpr a.2) (Subgroup.zpowers_le.mpr b.2)
  set w : G := h * (b : G) * h⁻¹ with hw
  have hwK' : w ∈ K' := ⟨b, b.2, rfl⟩
  have hw3 : orderOf w = 3 := by
    rw [hw, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hb'
  have hcw : ∀ e ∈ E₂, Commute e w := fun e he => hcomm e (hE₂K he) w hwK'
  have hwE₂ : w ∉ E₂ := by
    intro hwE
    have h1 := hKK' w (hE₂K hwE) hwK'
    rw [h1, orderOf_one] at hw3
    omega
  obtain ⟨hE₃, hE₃c⟩ := exists_elemAbelian_sup_zpowers hE₂ hw3 hcw hwE₂
  have hE₃H : E₂ ⊔ Subgroup.zpowers w ≤ H :=
    sup_le (hE₂K.trans hc.1) (Subgroup.zpowers_le.mpr (hc'.1 hwK'))
  have hcard : Nat.card ↥(E₂ ⊔ Subgroup.zpowers w) = 3 ^ 3 := by
    rw [hE₃c, hE₂c, hE₁c]
    norm_num
  have h3 := le_pRank Nat.prime_three hE₃H hE₃ hcard
  have h4 := A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hIH.1.1
  have h5 : evenRank G ≤ 2 := hy.qtke.2.2
  omega

omit [Finite G] in
theorem exists_mem_centralizer (hOut : J4OutTrivial) {K : Subgroup G} (hK : IsSporadic .J4 ↥K)
    {h : G} (hh : h ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * h ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨x, hx⟩ := hOut ↥K hK (K.normalizerMonoidHom ⟨h, hh⟩)
  refine ⟨x, x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := congrArg Subtype.val (hx ⟨y, hy⟩)
  have h2 : h * y * h⁻¹ = (x : G) * y * (x : G)⁻¹ := h1
  calc y * ((x : G)⁻¹ * h) = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * h := by group
    _ = (x : G)⁻¹ * (h * y * h⁻¹) * h := by rw [h2]
    _ = (x : G)⁻¹ * h * y := by group

end NoJ4

end CFSG.Quasithin.H13.Ch4
