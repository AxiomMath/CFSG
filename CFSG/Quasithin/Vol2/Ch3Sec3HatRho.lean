module

public import CFSG.Quasithin.Vol2.Ch3Sec3HatModel
public import CFSG.Quasithin.Vol2.Ch3Sec3G2Rho

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

namespace HatR

open CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

variable {G : Type} [Group G]

theorem blockU_comm {L : Subgroup G} (hL : IsShort2 L) {a b : G} (ha : a ∈ blockU L)
    (hb : b ∈ blockU L) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 hb).2 a (hL.2.2.1.1 ha).1

theorem conjU_eq_one_iff {L : Subgroup G} (g : ↥(Subgroup.normalizer (L : Set G))) :
    G2Rho.conjU L g = 1 ↔ (g : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 u hu
    have h2 : (g : G) * u * (g : G)⁻¹ = u :=
      congrArg (fun a : MulAut ↥(blockU L) => ((a ⟨u, hu⟩ : ↥(blockU L)) : G)) h1
    calc u * g = (g : G) * u * (g : G)⁻¹ * g := by rw [h2]
      _ = g * u := by group
  · intro h1
    ext u
    show (g : G) * u * (g : G)⁻¹ = u
    rw [← h1 u u.2]
    group

theorem card_of_isHat {X : Type} [Group X] (hX : IsHat X ↥(alternatingGroup (Fin 6))) :
    Nat.card X = 1080 := by
  obtain ⟨-, hZ3, ⟨θ⟩⟩ := hX
  have h1 := (Subgroup.center X).card_mul_index
  rw [hZ3, Subgroup.index, Nat.card_congr θ.toEquiv, nat_card_alternatingGroup,
    Nat.card_fin] at h1
  exact h1.symm.trans (by decide)

theorem exists_rho₀ [Finite G] (hE : HatA6Embed) {L : Subgroup G}
    (hH : CFSG.Quasithin.IsHatA6Block L) :
    Nat.card ↥Gam0 = 1080 ∧
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut W6) (β : ↥(blockU L) ≃* W6),
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
        β (G2Rho.conjU L g u) = ρ g (β u)) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ Gam0) ∧
      (∀ x ∈ Gam0, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x) ∧
      ∀ g, ρ g = 1 → (g : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  have : IsMulCommutative ↥(blockU L) := ⟨⟨fun a b => Subtype.ext (blockU_comm hH.1 a.2 b.2)⟩⟩
  set φ : ↥L →* MulAut ↥(blockU L) :=
    (G2Rho.conjU L).comp (Subgroup.inclusion Subgroup.le_normalizer) with hφ
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    ext ℓ
    rw [MonoidHom.mem_ker]
    show G2Rho.conjU L ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1 ↔ _
    rw [conjU_eq_one_iff]
    constructor
    · intro hc
      have h1 : (ℓ : G) ∈ pCoreOf 2 L := by
        rw [← hH.2.2.2]
        exact ⟨ℓ.2, hc⟩
      obtain ⟨x, hx, hxe⟩ := h1
      rwa [show x = ℓ from Subtype.ext hxe] at hx
    · intro hp
      have h1 : (ℓ : G) ∈ pCoreOf 2 L := ⟨ℓ, hp, rfl⟩
      rw [← hH.2.2.2] at h1
      exact h1.2
  have hK : IsHat ↥φ.range ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)) hH.2.1
  have hU2 : ∀ v : ↥(blockU L), v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hH.1.2.2.1.2 v v.2)
  obtain ⟨e, he⟩ := hE ↥(blockU L) hU2 hH.2.2.1 φ.range hK
  have hcard : Nat.card ↥Gam0 = 1080 := by
    rw [← he]
    exact (Subgroup.card_map_of_injective (CFSG.Quasithin.H.congrHom_injective e)).trans
      (card_of_isHat hK)
  refine ⟨hcard, (CFSG.Quasithin.H.congrHom e).comp (G2Rho.conjU L), e, fun g u => ?_,
    fun ℓ hℓ => ?_, fun x hx => ?_, fun g hg => ?_⟩
  · show e (G2Rho.conjU L g u) = e (G2Rho.conjU L g (e.symm (e u)))
    rw [MulEquiv.symm_apply_apply]
  · rw [← he]
    exact ⟨φ ⟨ℓ, hℓ⟩, ⟨⟨ℓ, hℓ⟩, rfl⟩, rfl⟩
  · rw [← he] at hx
    obtain ⟨k, ⟨ℓ, rfl⟩, rfl⟩ := hx
    exact ⟨ℓ, ℓ.2, rfl⟩
  · rw [← conjU_eq_one_iff]
    exact CFSG.Quasithin.H.congrHom_injective e (hg.trans (map_one _).symm)

theorem exists_rho [Finite G] (hE : HatA6Embed) (hN : HatA6Normalizer) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hH : CFSG.Quasithin.IsHatA6Block L) :
    Nat.card ↥Gam0 = 1080 ∧
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut W6) (β : ↥(blockU L) ≃* W6),
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ → β u' = ρ g (β u)) ∧
      (∀ g, ρ g ∈ Nor0) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ Gam0) ∧
      (∀ x ∈ Gam0, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x) ∧
      (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ S0) ∧
      (∀ g, ρ g = 1 → (g : G) ∈ Subgroup.centralizer (blockU L : Set G)) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
        g ∈ qL L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, ρ₀, β₀, hβ₀, hρL, hρL', hρC⟩ := exists_rho₀ hE hH
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hρN : ∀ g, ρ₀ g ∈ Nor0 := by
    intro g
    rw [← hN, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨ℓ, hℓ, rfl⟩ := hρL' y hy
      have hℓ' : (g : G) * ℓ * (g : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp g.2 ℓ).mp hℓ
      have e : ρ₀ g * ρ₀ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * (ρ₀ g)⁻¹ =
          ρ₀ ⟨_, Subgroup.le_normalizer hℓ'⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact hρL _ hℓ'
    · intro hy
      obtain ⟨ℓ, hℓ, hℓe⟩ := hρL' _ hy
      have hℓ' : (g : G)⁻¹ * ℓ * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2) ℓ).mp hℓ
        simpa using this
      have e : y = ρ₀ ⟨_, Subgroup.le_normalizer hℓ'⟩ := by
        have e2 : (⟨(g : G)⁻¹ * ℓ * g, Subgroup.le_normalizer hℓ'⟩ :
            ↥(Subgroup.normalizer (L : Set G))) = g⁻¹ * ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * g :=
          Subtype.ext rfl
        rw [e2, map_mul, map_mul, hℓe, map_inv]
        group
      rw [e]
      exact hρL _ hℓ'
  obtain ⟨hSp, hSidx⟩ := isSylow_S0 hcard
  have : Finite ↥Nor0 := Nat.finite_of_card_ne_zero (by rw [card_Nor0, hcard]; norm_num)
  obtain ⟨x, hxN, hx⟩ : ∃ x ∈ Nor0, ∀ t (ht : t ∈ T), x * ρ₀ ⟨t, hTL ht⟩ * x⁻¹ ∈ S0 := by
    let f : ↥T →* ↥Nor0 := (ρ₀.codRestrict Nor0 hρN).comp (Subgroup.inclusion hTL)
    have hf : IsPGroup 2 ↥f.range := hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨Q, hQ⟩ := hf.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Nor0 Q (hSp.toSylow hSidx)
    refine ⟨g, g.2, fun t ht => ?_⟩
    have h1 : f ⟨t, ht⟩ ∈ (Q : Subgroup ↥Nor0) := hQ ⟨⟨t, ht⟩, rfl⟩
    have h2 : g * f ⟨t, ht⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 _) : Subgroup ↥Nor0) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hg, IsPGroup.toSylow_coe] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hxn : ∀ y : MulAut W6, y ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6)) →
      ∀ z ∈ Gam0, y * z * y⁻¹ ∈ Gam0 := fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp hy z).mp hz
  have hxG : x ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6)) := by rw [hN]; exact hxN
  have hxG' : x⁻¹ ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6)) := Subgroup.inv_mem _ hxG
  have hker : ∀ g, x * ρ₀ g * x⁻¹ = 1 → ρ₀ g = 1 := by
    intro g h1
    have h3 := congrArg (fun y => x⁻¹ * y * x) h1
    simpa [mul_assoc] using h3
  refine ⟨hcard, (MulAut.conj x).toMonoidHom.comp ρ₀, β₀.trans x, ?_, fun g => ?_,
    fun ℓ hℓ => ?_, fun y hy => ?_, hx, fun g h1 => hρC g (hker g h1), ?_⟩
  · intro g u u' hu'
    have e1 : u' = G2Rho.conjU L g u := Subtype.ext hu'
    rw [e1]
    show x (β₀ (G2Rho.conjU L g u)) = (x * ρ₀ g * x⁻¹) (x (β₀ u))
    rw [hβ₀, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · exact Nor0.mul_mem (Nor0.mul_mem hxN (hρN g)) (Nor0.inv_mem hxN)
  · exact hxn x hxG _ (hρL ℓ hℓ)
  · have h1 := hxn x⁻¹ hxG' y hy
    rw [inv_inv] at h1
    obtain ⟨ℓ, hℓ, e⟩ := hρL' _ h1
    refine ⟨ℓ, hℓ, ?_⟩
    show x * ρ₀ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * x⁻¹ = y
    rw [e]
    group
  · intro g hg hgN h1
    refine G2Rho.mem_qL_of_rho ρ₀ hTL hT2 (fun ℓ hℓ h2 => ?_) hg hgN (hker _ h1)
    have h3 : ℓ ∈ pCoreOf 2 L := by
      rw [← hH.2.2.2]
      exact ⟨hℓ, hρC _ h2⟩
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨ℓ, h3⟩
    exact ⟨b, by simpa using congrArg Subtype.val hb⟩

end HatR

end CFSG.Quasithin.H13
