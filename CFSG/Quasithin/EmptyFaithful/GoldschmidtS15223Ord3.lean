module

public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def GenByOrderThree (X : Subgroup G) : Prop :=
  X ≤ Subgroup.closure {x : G | x ∈ X ∧ orderOf x = 3}

theorem orderOf_conj_eq_ord3 (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using h

theorem GenByOrderThree.eq_oPrimeResidualOf {X : Subgroup G} (h : GenByOrderThree X) :
    X = oPrimeResidualOf 3 X := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun x hx => hx.1)
  refine h.trans (Subgroup.closure_mono fun x hx => ⟨hx.1, 1, ?_⟩)
  rw [pow_one]
  exact hx.2

theorem GenByOrderThree.conj_mem {Y Y' : Subgroup G} {g : G} (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y')
    (hY : GenByOrderThree Y) {x : G} (hx : x ∈ Y) :
    g * x * g⁻¹ ∈ Subgroup.closure {z : G | z ∈ Y' ∧ orderOf z = 3} := by
  have hx' := hY hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    exact Subgroup.subset_closure ⟨hg x hx.1, by rw [orderOf_conj_eq_ord3]; exact hx.2⟩
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using inv_mem ha

theorem closure_orderThree_mono {Y Y' : Subgroup G} (h : Y ≤ Y') :
    Subgroup.closure {z : G | z ∈ Y ∧ orderOf z = 3} ≤
      Subgroup.closure {z : G | z ∈ Y' ∧ orderOf z = 3} :=
  Subgroup.closure_mono fun _ hz => ⟨h hz.1, hz.2⟩

theorem genByOrderThree_conjClosure {X I : Subgroup G} (hX : GenByOrderThree X) :
    GenByOrderThree (conjClosure X I) :=
  conjClosure_le fun _ hg _ hx =>
    hX.conj_mem (fun _ hy => mem_conjClosure hg hy) hx

theorem conj_mem_closure_orderThree {Y : Subgroup G} {g : G} (hg : g ∈ Y) {x : G}
    (hx : x ∈ Subgroup.closure {z : G | z ∈ Y ∧ orderOf z = 3}) :
    g * x * g⁻¹ ∈ Subgroup.closure {z : G | z ∈ Y ∧ orderOf z = 3} := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact Subgroup.subset_closure
      ⟨Y.mul_mem (Y.mul_mem hg hx.1) (Y.inv_mem hg), by rw [orderOf_conj_eq_ord3]; exact hx.2⟩
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using inv_mem ha

theorem isPGroup_quotient_of_map_eq_top_ord3 {Y : Subgroup G} {A : Type} [Group A] {α : ↥Y →* A}
    (hk : α.ker = CFSG.pCore 2 ↥Y) {N : Subgroup ↥Y} [N.Normal] (hN : N.map α = ⊤) :
    IsPGroup 2 (↥Y ⧸ N) := by
  intro c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hy : α y ∈ N.map α := by rw [hN]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  have hq : x⁻¹ * y ∈ CFSG.pCore 2 ↥Y := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, hq⟩
  have hm' : (x⁻¹ * y) ^ 2 ^ m = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥Y) => (y : ↥Y)) hm
    simpa using this
  refine ⟨m, ?_⟩
  have hmk : (QuotientGroup.mk y : ↥Y ⧸ N) = QuotientGroup.mk (x⁻¹ * y) := by
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hx) y⁻¹
  rw [hmk, ← QuotientGroup.mk_pow, hm']
  rfl

variable [Finite G]

theorem genByOrderThree_of_epi_simple {Y : Subgroup G}
    (hY : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → N = ⊤)
    {A : Type} [Group A] [IsSimpleGroup A] {α : ↥Y →* A} (hs : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥Y) (h3 : 3 ∣ Nat.card ↥Y) : GenByOrderThree Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3
  set N₃ : Subgroup G := Subgroup.closure {z : G | z ∈ Y ∧ orderOf z = 3} with hN₃
  have hNY : N₃ ≤ Y := (Subgroup.closure_le _).mpr fun x hx => hx.1
  set N' : Subgroup ↥Y := N₃.subgroupOf Y with hN'
  have hNn : N'.Normal := by
    rw [hN', Subgroup.normal_subgroupOf_iff_le_normalizer hNY]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => conj_mem_closure_orderThree hg hx
    · intro hx
      have := conj_mem_closure_orderThree (Y.inv_mem hg) hx
      simpa [mul_assoc] using this
  have hkN : k ∈ N' := by
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨k.2, ?_⟩)
    rw [Subgroup.orderOf_coe]
    exact hk3
  have hAn : (N'.map α).Normal := hNn.map α hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map α) with hbot | htop
  ·
    exfalso
    have hk1 : α k = 1 := by
      have : α k ∈ N'.map α := Subgroup.mem_map_of_mem α hkN
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hkq : k ∈ CFSG.pCore 2 ↥Y := by rw [← hk]; exact hk1
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨k, hkq⟩
    have hm1 : k ^ 2 ^ m = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥Y) => (y : ↥Y)) hm
      simpa using this
    have h3dvd : 3 ∣ 2 ^ m := hk3 ▸ orderOf_dvd_of_pow_eq_one hm1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)
  ·
    have htop' : N' = ⊤ := hY N' (isPGroup_quotient_of_map_eq_top_ord3 hk htop)
    exact Subgroup.subgroupOf_eq_top.mp htop'

end CFSG.Quasithin.S15223
