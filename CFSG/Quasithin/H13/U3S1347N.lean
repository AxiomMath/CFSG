module

public import CFSG.Quasithin.H13.U3S1347H
public import CFSG.Quasithin.H13.U3S1347K
public import CFSG.Quasithin.H13.U3S1347L

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem inX1_iff_fix :
    ∀ g : H6.Γ, g • (![1, 0, 0] : Fin 3 → ZMod 2) = ![1, 0, 0] ↔ SL3.InX1 g := by
  decide +kernel

theorem Lp_iff_X1 (g : H6.Γ) : g ∈ H6.Lp ↔ g ∈ SL3.X1 := by
  rw [show g ∈ H6.Lp ↔ g • (![1, 0, 0] : Fin 3 → ZMod 2) = ![1, 0, 0] from
    MulAction.mem_stabilizer_iff, inX1_iff_fix]
  rfl

theorem borel_iff_P0 (g : H6.Γ) : g ∈ H6.borel ↔ g ∈ SL3.P0 := by
  rw [show H6.borel = H6.Lp ⊓ H6.Ll from rfl, show SL3.P0 = SL3.X1 ⊓ SL3.X2 from rfl, mem_inf,
    mem_inf, Lp_iff_X1]
  rfl

theorem s1347_V0_le_T (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) : v0Of T H₁ H₂ ≤ T := by
  have hred := s1347_reduced S hH₀
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  refine (le_pCoreOf_of_le_normalizer hred.1 hred.2.1 ?_).trans
    (pCoreOf_two_le_of_isSylowTwoOf hsyl₀)
  rintro ⟨w, hw⟩
  exact ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 w hw)⟩

theorem s1347_centralizer_T_le (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {w : G} (hw : w ∈ v0Of T H₁ H₂)
    (hwT : w ∈ centralizer (T : Set G)) : w ∈ quasithinOmegaOneCenter T :=
  subset_closure ⟨mem_inf.2 ⟨s1347_V0_le_T S hH₀ hw, hwT⟩,
    (s1347_reduced S hH₀).2.2.1.2 w hw⟩

omit [Finite G] in
theorem s1347_fix_iff {H₁ H₂ : Subgroup G} {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹)
    [IsMulCommutative ↥(v0Of T H₁ H₂)] (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)) :
    L32Mod.toAddRep σ (ψ k) (Additive.ofMul w) = Additive.ofMul w ↔ (k : G) * w = w * k := by
  rw [L32Mod.toAddRep_apply]
  constructor
  · intro h1
    have h2 : ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = w :=
      congrArg Subtype.val (Additive.ofMul.injective h1)
    rw [hσ, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · intro h1
    congr 1
    apply Subtype.ext
    rw [hσ, mul_inv_eq_iff_eq_mul]
    exact h1

omit [Finite G] in
theorem s1347_l32_hyps {H₁ H₂ : Subgroup G} {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹)
    {Hp Hl : Subgroup G} (hpX : (Hp.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1)
    (hlX : (Hl.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2) (hHl : Hl ≤ H₁ ⊔ H₂)
    (hHp : Hp ≤ H₁ ⊔ H₂) {x y : ↥(v0Of T H₁ H₂)}
    (hxp : (x : G) ∈ centralizer (Hp : Set G)) (hyl : (y : G) ∈ centralizer (Hl : Set G))
    (hxl : (x : G) ∉ centralizer (Hl : Set G)) (hyp : (y : G) ∉ centralizer (Hp : Set G))
    [IsMulCommutative ↥(v0Of T H₁ H₂)] :
    (∀ g ∈ H6.Lp, L32Mod.toAddRep σ g (Additive.ofMul x) = Additive.ofMul x) ∧
    (∀ g ∈ H6.Ll, L32Mod.toAddRep σ g (Additive.ofMul y) = Additive.ofMul y) ∧
    (∃ g ∈ H6.Ll, L32Mod.toAddRep σ g (Additive.ofMul x) ≠ Additive.ofMul x) ∧
    (∃ g ∈ H6.Lp, L32Mod.toAddRep σ g (Additive.ofMul y) ≠ Additive.ofMul y) := by
  have hfix := s1347_fix_iff hσ
  have hfixed : ∀ {P : Subgroup G} {w : ↥(v0Of T H₁ H₂)}, (w : G) ∈ centralizer (P : Set G) →
      ∀ g ∈ (P.subgroupOf (H₁ ⊔ H₂)).map ψ,
        L32Mod.toAddRep σ g (Additive.ofMul w) = Additive.ofMul w := by
    intro P w hw g hg
    obtain ⟨k, hk, rfl⟩ := hg
    exact (hfix k w).2 (mem_centralizer_iff.1 hw k (mem_subgroupOf.1 hk))
  have hmoved : ∀ {P : Subgroup G} {w : ↥(v0Of T H₁ H₂)}, P ≤ H₁ ⊔ H₂ →
      (w : G) ∉ centralizer (P : Set G) → ∃ g ∈ (P.subgroupOf (H₁ ⊔ H₂)).map ψ,
        L32Mod.toAddRep σ g (Additive.ofMul w) ≠ Additive.ofMul w := by
    intro P w hP hw
    rw [mem_centralizer_iff] at hw
    push Not at hw
    obtain ⟨k, hk, hkw⟩ := hw
    exact ⟨ψ ⟨k, hP hk⟩, mem_map_of_mem _ (mem_subgroupOf.2 hk),
      fun h1 => hkw ((hfix _ w).1 h1)⟩
  have hX2 : ∀ g : H6.Γ, g ∈ SL3.X2 ↔ g ∈ H6.Ll := fun _ => Iff.rfl
  refine ⟨fun g hg => hfixed hxp g (hpX ▸ (Lp_iff_X1 g).1 hg),
    fun g hg => hfixed hyl g (hlX ▸ (hX2 g).2 hg), ?_, ?_⟩
  · obtain ⟨g, hg, hg'⟩ := hmoved hHl hxl
    exact ⟨g, (hX2 g).1 (hlX ▸ hg), hg'⟩
  · obtain ⟨g, hg, hg'⟩ := hmoved hHp hyp
    exact ⟨g, (Lp_iff_X1 g).2 (hpX ▸ hg), hg'⟩

omit [Finite G] in
theorem s1347_l32_gen {H₁ H₂ : Subgroup G} {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹) {x y : ↥(v0Of T H₁ H₂)}
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = (x : G) * y)
    [IsMulCommutative ↥(v0Of T H₁ H₂)] (N : AddSubgroup (Additive ↥(v0Of T H₁ H₂)))
    (hNx : ∀ g, L32Mod.toAddRep σ g (Additive.ofMul x) ∈ N)
    (hNy : ∀ g, L32Mod.toAddRep σ g (Additive.ofMul y) ∈ N) : N = ⊤ := by
  set N' : Subgroup G := (AddSubgroup.toSubgroup' N).map (v0Of T H₁ H₂).subtype with hN'
  have hk : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      (∀ g, L32Mod.toAddRep σ g (Additive.ofMul w) ∈ N) → (k : G) * w * (k : G)⁻¹ ∈ N' := by
    intro k w hw
    rw [← hσ]
    exact mem_map_of_mem _ (hw (ψ k))
  have hle : v0Of T H₁ H₂ ≤ N' := by
    refine conjClosure_le fun k hk' z hz => ?_
    rcases hZ z hz with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact N'.one_mem
    · exact hk ⟨k, hk'⟩ x hNx
    · exact hk ⟨k, hk'⟩ y hNy
    · have e : k * ((x : G) * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [e]
      exact N'.mul_mem (hk ⟨k, hk'⟩ x hNx) (hk ⟨k, hk'⟩ y hNy)
  refine eq_top_iff.2 fun m _ => ?_
  obtain ⟨n, hn, hnm⟩ := hle (Additive.toMul m).2
  have : n = Additive.toMul m := Subtype.ext hnm
  rw [this] at hn
  exact hn

theorem s1347_l32_fixed (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    (hTψ : (T.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.P0) {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹) {x y : ↥(v0Of T H₁ H₂)}
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = (x : G) * y)
    [IsMulCommutative ↥(v0Of T H₁ H₂)] (m : Additive ↥(v0Of T H₁ H₂))
    (hm : ∀ t ∈ H6.borel, L32Mod.toAddRep σ t m = m) :
    m = 0 ∨ m = Additive.ofMul x ∨ m = Additive.ofMul y ∨
      m = Additive.ofMul x + Additive.ofMul y := by
  set w := Additive.toMul m with hw
  have hwT : (w : G) ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    have hψt : ψ ⟨t, hH₀.1 ht⟩ ∈ H6.borel := (borel_iff_P0 _).2
      (hTψ ▸ mem_map_of_mem _ (mem_subgroupOf.2 ht))
    have h1 := hm _ hψt
    rw [L32Mod.toAddRep_apply] at h1
    have h2 : ((σ (ψ ⟨t, hH₀.1 ht⟩) w : ↥(v0Of T H₁ H₂)) : G) = w :=
      congrArg Subtype.val (Additive.ofMul.injective h1)
    rw [hσ, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hmw : m = Additive.ofMul w := rfl
  rcases hZ _ (s1347_centralizer_T_le S hH₀ w.2 hwT) with h | h | h | h
  · left
    rw [hmw, show w = 1 from Subtype.ext h]
    rfl
  · right; left
    rw [hmw, show w = x from Subtype.ext h]
  · right; right; left
    rw [hmw, show w = y from Subtype.ext h]
  · right; right; right
    rw [hmw, show w = x * y from Subtype.ext h]
    rfl

theorem s1347_module_core (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {K₀ : Subgroup G} (hKH : K₀ ≤ H₁ ⊔ H₂)
    {ψ : ↥(H₁ ⊔ H₂) →* SL3.S} (hker : ψ.ker = Open.pCore 2 ↥(H₁ ⊔ H₂))
    (hTψ : (T.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.P0)
    (hKψ : (K₀.subgroupOf (H₁ ⊔ H₂)).map ψ = ⊤)
    (hcent : (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂))
    {σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂)}
    (hσ : ∀ (k : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ k) w : ↥(v0Of T H₁ H₂)) : G) = k * w * (k : G)⁻¹)
    {Hp Hl : Subgroup G} (hHp : Hp ≤ H₁ ⊔ H₂) (hHl : Hl ≤ H₁ ⊔ H₂)
    (hpX : (Hp.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1)
    (hlX : (Hl.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2) {x y : ↥(v0Of T H₁ H₂)}
    (hxp : (x : G) ∈ centralizer (Hp : Set G)) (hyl : (y : G) ∈ centralizer (Hl : Set G))
    (hxl : (x : G) ∉ centralizer (Hl : Set G)) (hyp : (y : G) ∉ centralizer (Hp : Set G))
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = (x : G) * y) :
    (IsSumNatDual3 K₀ (v0Of T H₁ H₂) ∨ IsFanoCore K₀ (v0Of T H₁ H₂)) ∧
      ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
  have hred := s1347_reduced S hH₀
  have hcomm : IsMulCommutative ↥(v0Of T H₁ H₂) := hred.2.2.1.1
  have h2 : ∀ m : Additive ↥(v0Of T H₁ H₂), m + m = 0 := by
    intro m
    have : Additive.toMul m * Additive.toMul m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hred.2.2.1.2 _ (Additive.toMul m).2)
    exact congrArg Additive.ofMul this
  obtain ⟨hx, hy, hxl', hyp'⟩ := s1347_l32_hyps hσ hpX hlX hHl hHp hxp hyl hxl hyp
  have hgen := s1347_l32_gen hσ hZ
  have hC := s1347_l32_fixed S hH₀ hTψ hσ hZ
  have hN := hred.2.1
  have hσK : ∀ g, σ g ∈ autOn K₀ (v0Of T H₁ H₂) := by
    intro g
    obtain ⟨k, hk, rfl⟩ : g ∈ (K₀.subgroupOf (H₁ ⊔ H₂)).map ψ := hKψ ▸ mem_top g
    refine ⟨⟨k, hN k.2⟩, mem_subgroupOf.2 (mem_subgroupOf.1 hk), ?_⟩
    ext w
    rw [hσ]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w
  have hσs : ∀ a ∈ autOn K₀ (v0Of T H₁ H₂), ∃ g, σ g = a := by
    rintro a ⟨k, hk, rfl⟩
    refine ⟨ψ ⟨k, hKH (mem_subgroupOf.1 hk)⟩, ?_⟩
    ext w
    rw [hσ]
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w).symm
  have key : (IsSumNatDual3 K₀ (v0Of T H₁ H₂) ∨ IsFanoCore K₀ (v0Of T H₁ H₂)) ∧
      ∀ {A' : Subgroup SL3.S}, A' ≤ H6.borel → A' ≠ ⊥ → (∀ a ∈ A', a * a = 1) →
        Nat.card A' * Nat.card (L32Mod.Fix (L32Mod.toAddRep σ) A') <
          Nat.card (Additive ↥(v0Of T H₁ H₂)) := by
    rcases L32Mod.l32_cases h2 hx hy hxl' hyp' hgen hC with hiso | hiso |
      ⟨U₁, U₂, hsup, hinf, hinv₁, hinv₂, ⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
    · exact ⟨Or.inr ⟨hcomm, L32Mod.realizes_fanoCore σ hσK hσs hiso⟩,
        fun hAT hA hA2 => L32Mod.noOffender_core hiso hAT hA hA2⟩
    · refine ⟨Or.inr ⟨hcomm, L32Mod.realizes_fanoCore (σ.comp H6.graph.toMonoidHom)
        (fun g => hσK _) (fun a ha => ?_) hiso⟩,
        fun hAT hA hA2 => L32Mod.noOffender_core_graph hiso hAT hA hA2⟩
      obtain ⟨g, hg⟩ := hσs a ha
      refine ⟨H6.graph g, ?_⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, L32Mod.graph_graph, hg]
    · obtain ⟨U₁', U₂', h1, h2', π, hπ1, hπ2⟩ :=
        L32Mod.sumNatDual_of σ hσK hσs hsup hinf hinv₁ hinv₂ e₁ he₁ e₂ he₂
      exact ⟨Or.inl ⟨hcomm, U₁', U₂', h1, h2', π, hπ1, hπ2⟩, fun hAT hA hA2 =>
        L32Mod.noOffender_sum (L32Mod.isoMod_sum hsup hinf e₁ he₁ hinv₁ hinv₂ e₂ he₂)
          hAT hA hA2⟩
  refine ⟨key.1, fun A hA => ?_⟩
  by_contra hAC
  have hineq := card_le_relIndex_mul_card hred.2.2.1 (s1347_V0_le_T S hH₀) hA
  have hAH : A ≤ H₁ ⊔ H₂ := hA.1.trans hH₀.1
  have hA'T : (A.subgroupOf (H₁ ⊔ H₂)).map ψ ≤ H6.borel := fun g hg =>
    (borel_iff_P0 g).2 (hTψ ▸ map_mono (fun a ha => mem_subgroupOf.2
      (hA.1 (mem_subgroupOf.1 ha))) hg)
  have hA'1 : (A.subgroupOf (H₁ ⊔ H₂)).map ψ ≠ ⊥ := by
    intro hb
    apply hAC
    intro a ha
    have h1 : ψ ⟨a, hAH ha⟩ = 1 := by
      have : ψ ⟨a, hAH ha⟩ ∈ (A.subgroupOf (H₁ ⊔ H₂)).map ψ :=
        mem_map_of_mem _ (mem_subgroupOf.2 ha)
      rw [hb, mem_bot] at this
      exact this
    have := (map_eq_one_iff_of_ker hker _).1 h1
    rw [← hcent] at this
    exact this.2
  have hA'2 : ∀ a ∈ (A.subgroupOf (H₁ ⊔ H₂)).map ψ, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : (a : G) * a = 1 := by
      rw [← pow_two]
      exact hA.2.1.2 _ (mem_subgroupOf.1 ha)
    rw [show a * a = 1 from Subtype.ext this, map_one]
  have hcardA : Nat.card ↥((A.subgroupOf (H₁ ⊔ H₂)).map ψ) =
      (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)).relIndex A := by
    rw [← relIndex_ker, hker, ← pCoreOf_subgroupOf_eq_pCore,
      relIndex_subgroupOf hAH, ← hcent, inf_comm A, ← inf_relIndex_right]
    congr 1
    rw [inf_comm (H₁ ⊔ H₂), inf_assoc, inf_eq_right.2 hAH]
  have hcardF : Nat.card (L32Mod.Fix (L32Mod.toAddRep σ) ((A.subgroupOf (H₁ ⊔ H₂)).map ψ)) =
      Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer (A : Set G)) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨((Additive.toMul m.1 : ↥(v0Of T H₁ H₂)) : G),
          mem_inf.2 ⟨(Additive.toMul m.1).2,
          mem_centralizer_iff.2 fun a ha => ?_⟩⟩
        invFun := fun w => ⟨Additive.ofMul ⟨w, (mem_inf.1 w.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := m.2 (ψ ⟨a, hAH ha⟩) (mem_map_of_mem _ (mem_subgroupOf.2 ha))
      exact ((s1347_fix_iff hσ _ _).1 this)
    · rintro _ ⟨a, ha, rfl⟩
      exact (s1347_fix_iff hσ _ _).2 (mem_centralizer_iff.1 (mem_inf.1 w.2).2 a
        (mem_subgroupOf.1 ha))
  have := key.2 hA'T hA'1 hA'2
  rw [hcardA, hcardF] at this
  exact absurd hineq (not_le.2 this)

end CFSG.Quasithin.H13.U3
