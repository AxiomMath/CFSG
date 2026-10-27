module

public import CFSG.Quasithin.EmptyFaithful.S153E59E
public import CFSG.Quasithin.EmptyFaithful.S153E59C
public import CFSG.Quasithin.EmptyFaithful.S153E59D
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section O2

variable {G : Type*} [Group G] [Finite G]

theorem oTwoUpper_subgroupOf {X Y : Subgroup G} (hXY : X ≤ Y) :
    (oTwoUpper X).subgroupOf Y = oTwoUpper (X.subgroupOf Y) := by
  have h1 := oTwoUpper_map Y.subtype (X.subgroupOf Y)
  rw [Subgroup.map_subgroupOf_eq_of_le hXY] at h1
  rw [h1, map_subtype_subgroupOf']

end O2

section Star

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem map_rho_oTwoUpper (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ((oTwoUpper Mc).subgroupOf Mc).map (rho cx) = oTwoUpper (HStar153 T M V₁ Mc) := by
  rw [oTwoUpper_subgroupOf (le_refl Mc), Subgroup.subgroupOf_self, ← oTwoUpper_map,
    ← MonoidHom.range_eq_map, range_rho]

theorem mem_tilde_conj_iff (cx : Ctx15350 T Mc M V₁ V₂ t) {U₁ : Subgroup G} {g : G} (hg : g ∈ Mc)
    (w : ↥(UT T M V₁ Mc)) :
    w ∈ (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ g)).subgroupOf (UT T M V₁ Mc) ↔
      ∃ v ∈ (tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf (UT T M V₁ Mc),
        rho cx ⟨g⁻¹, Mc.inv_mem hg⟩ v = w := by
  have hsec : ∀ h : ↥Mc, secH cx h =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)
        (Subgroup.inclusion cx.hF.H_normalizes_V₁ h) := fun h => rfl
  constructor
  · intro hw
    obtain ⟨y, hy, hyw⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hw)
    rw [mem_conjSubgroup_iff] at hy
    refine ⟨rho cx ⟨g, hg⟩ w, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · refine mem_secImg.mpr ⟨Subgroup.inclusion cx.hF.H_normalizes_V₁ ⟨g, hg⟩ * y *
        (Subgroup.inclusion cx.hF.H_normalizes_V₁ ⟨g, hg⟩)⁻¹, ?_, ?_⟩
      · simpa using hy
      · rw [rho_apply_coe, ← hyw, hsec]
        simp only [map_mul, map_inv]
    · rw [← MulAut.mul_apply, ← map_mul]
      have : (⟨g⁻¹, Mc.inv_mem hg⟩ * ⟨g, hg⟩ : ↥Mc) = 1 := Subtype.ext (by simp)
      rw [this, map_one, MulAut.one_apply]
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨x, hx, hxv⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hv)
    refine Subgroup.mem_subgroupOf.mpr (mem_secImg.mpr ⟨Subgroup.inclusion cx.hF.H_normalizes_V₁
      ⟨g⁻¹, Mc.inv_mem hg⟩ * x * (Subgroup.inclusion cx.hF.H_normalizes_V₁ ⟨g⁻¹, Mc.inv_mem hg⟩)⁻¹,
      ?_, ?_⟩)
    · rw [mem_conjSubgroup_iff]
      have : g * (((Subgroup.inclusion cx.hF.H_normalizes_V₁ ⟨g⁻¹, Mc.inv_mem hg⟩ * x *
          (Subgroup.inclusion cx.hF.H_normalizes_V₁ ⟨g⁻¹, Mc.inv_mem hg⟩)⁻¹ : ↥(Subgroup.normalizer
          (quasithinOmegaOneCenter T : Set G))) : G)) * g⁻¹ = (x : G) := by
        simp
        group
      rw [this]
      exact hx
    · rw [← hvw, rho_apply_coe, ← hxv, hsec]
      simp only [map_mul, map_inv]

theorem card_eq_of_realizesVia {V : Type*} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) (hsec : D.sec = ⊤)
    (hker : D.ker = ⊥) : Nat.card ↥U = Nat.card D.Amb := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  rw [Nat.card_congr (Equiv.ofBijective β hbij)]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.ker.subgroupOf D.sec)
  have h2 : Nat.card ↥(D.ker.subgroupOf D.sec) = 1 := by
    rw [hker]
    simp
  have h3 : Nat.card ↥D.sec = Nat.card D.Amb := by
    rw [hsec]
    simp
  rw [h2, mul_one, h3] at h1
  exact h1.symm

structure HStarFacts (cx : Ctx15350 T Mc M V₁ V₂ t) : Prop where
  card_Hs : Nat.card ↥(HStar153 T M V₁ Mc) = 336
  card_Ks : Nat.card ↥(oTwoUpper (HStar153 T M V₁ Mc)) = 168
  idx : (oTwoUpper (HStar153 T M V₁ Mc)).relIndex (HStar153 T M V₁ Mc) = 2
  simple : IsSimpleGroup ↥(oTwoUpper (HStar153 T M V₁ Mc))
  center : ∀ a ∈ HStar153 T M V₁ Mc, (∀ b ∈ HStar153 T M V₁ Mc, a * b = b * a) → a = 1
  swap : ∃ W₁ W₂ : Subgroup ↥(UT T M V₁ Mc), W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧ Nat.card W₁ = 8 ∧
    ∀ x : ↥Mc, rho cx x ∉ oTwoUpper (HStar153 T M V₁ Mc) →
      (∀ w ∈ W₁, rho cx x w ∈ W₂) ∧ (∀ w ∈ W₂, rho cx x w ∈ W₁)

theorem hstarFacts (cx : Ctx15350 T Mc M V₁ V₂ t) {s : ℕ} (h58 : Concl15358 cx s) {t₁ : G}
    (ht₁T : t₁ ∈ T) (ht₁ : t₁ ∉ UCT153 T M V₁ Mc) : HStarFacts cx := by
  let _ : CommGroup ↥(UT T M V₁ Mc) := commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨π, U₁, -, -, hdir, hnat, hdual⟩ := h58.three t₁ ht₁T ht₁
  obtain ⟨hHs, hKs, hidx, hsimple, hcenter⟩ := autL32Data (HStar153 T M V₁ Mc) h58.one π hnat.1
  refine ⟨hHs, hKs, hidx, hsimple, hcenter, ?_⟩
  have hcard1 := card_eq_of_realizesVia hnat rfl rfl
  have hcard8 : Nat.card (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))).Amb = 8 := by
    show Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8
    simp [Nat.card_eq_fintype_card]
  refine ⟨(tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf (UT T M V₁ Mc),
    (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ t₁)).subgroupOf (UT T M V₁ Mc),
    hdir.2, hdir.1, by rw [hcard1, hcard8], ?_⟩
  intro x hx
  have hne : (tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf (UT T M V₁ Mc) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, hcard8] at hcard1
    omega
  have hsx : ∀ y : ↥Mc, rho cx y ∈ HStar153 T M V₁ Mc := fun y => by
    rw [← range_rho cx]; exact ⟨y, rfl⟩
  refine swap_of_index_two hidx (A₀ := oTwoUpper (HStar153 T M V₁ Mc))
    (A := HStar153 T M V₁ Mc) (W₁ := (tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf (UT T M V₁ Mc))
    (W₂ := (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ t₁)).subgroupOf (UT T M V₁ Mc))
    (fun a ha w hw => hnat.2.2.2.1 ⟨a, ha⟩ w hw) hdir.2 hne
    (x₀ := rho cx ⟨t₁⁻¹, Mc.inv_mem (S153E.T_le_Mc cx ht₁T)⟩) (hsx _) ?_ (hsx x) hx
  intro w
  exact mem_tilde_conj_iff cx (S153E.T_le_Mc cx ht₁T) w

end Star

end S153E59

end CFSG.Quasithin
