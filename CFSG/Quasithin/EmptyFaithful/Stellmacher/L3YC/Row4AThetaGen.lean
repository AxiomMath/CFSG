module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaLin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.ImageSylow

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace Stellmacher.L3YC

section Gen

variable {G : Type} [Group G] [Finite G]

theorem le_of_gen {L S U B' : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α)
    (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hpc : pCoreOf 2 L ≤ S) {u₀ : G} (hu₀U : u₀ ∈ U) (hu₀1 : u₀ ≠ 1)
    (hSu : ∀ s ∈ S ⊓ L, s * u₀ * s⁻¹ = u₀) (hSB : S ⊓ L ≤ B')
    {x : G} (hxL : x ∈ L) (hx3 : orderOf x = 3) (hxu : x * u₀ * x⁻¹ = u₀) (hxB : x ∈ B')
    {e : G} (heL : e ∈ L) (heB : e ∈ B') (heu : e * u₀ * e⁻¹ ≠ u₀) : L ≤ B' := by
  classical
  let Γ := StatedSL 3 F
  let α₁ : ↥L →* GL (Fin 3) F := Γ.subtype.comp α
  have hα₁ : Function.Surjective α₁ := by
    intro g
    have hg : g ∈ Γ := by
      show g ∈ StatedSL 3 F
      rw [Stellmacher.PU.L3YC.statedSL_eq_top_of_card_two hF]; trivial
    obtain ⟨l₀, hl₀⟩ := hα.1 ⟨g, hg⟩
    exact ⟨l₀, by simp [α₁, hl₀]⟩
  have hker : ∀ l : ↥L, α₁ l = 1 → l ∈ CFSG.pCore 2 ↥L := by
    intro l hl
    rw [← hα.2]
    have : α l = 1 := Subtype.ext (by simpa [α₁] using hl)
    exact this
  obtain ⟨Bc, hB⟩ := Stellmacher.PU.L3YC.natural_coord α hnat
  have hmem : ∀ l : ↥L, (l : G) * u₀ * (l : G)⁻¹ ∈ U := fun l => by
    have : (l : G) ∈ Subgroup.normalizer (U : Set G) := hnat.1 l.2
    exact (Subgroup.mem_normalizer_iff.mp this u₀).mp hu₀U
  let w₀ : Fin 3 → F := Multiplicative.toAdd (Bc ⟨u₀, hu₀U⟩)
  have hw₀ : w₀ ≠ 0 := by
    intro h
    have h1 : Bc ⟨u₀, hu₀U⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa [w₀] using h
    have h2 : (⟨u₀, hu₀U⟩ : ↥U) = 1 := Bc.injective (by simpa using h1)
    exact hu₀1 (congrArg Subtype.val h2)
  have hact : ∀ l : ↥L, glAct (α₁ l) w₀ =
      Multiplicative.toAdd (Bc ⟨(l : G) * u₀ * (l : G)⁻¹, hmem l⟩) := fun l =>
    (hB l ⟨u₀, hu₀U⟩ ⟨_, hmem l⟩ rfl).symm
  have hfix : ∀ l : ↥L, (l : G) * u₀ * (l : G)⁻¹ = u₀ → α₁ l ∈ stabAct w₀ := by
    intro l hl
    show glAct (α₁ l) w₀ = w₀
    rw [hact l]
    have : (⟨(l : G) * u₀ * (l : G)⁻¹, hmem l⟩ : ↥U) = ⟨u₀, hu₀U⟩ := Subtype.ext hl
    rw [this]
  have hmove : ∀ l : ↥L, (l : G) * u₀ * (l : G)⁻¹ ≠ u₀ → α₁ l ∉ stabAct w₀ := by
    intro l hl hs
    apply hl
    have h1 : glAct (α₁ l) w₀ = w₀ := hs
    rw [hact l] at h1
    have h2 : Bc ⟨(l : G) * u₀ * (l : G)⁻¹, hmem l⟩ = Bc ⟨u₀, hu₀U⟩ :=
      Multiplicative.toAdd.injective h1
    exact congrArg Subtype.val (Bc.injective h2)
  let Q : Subgroup (GL (Fin 3) F) := (B'.subgroupOf L).map α₁
  let D : Subgroup (GL (Fin 3) F) := ((S ⊓ L).subgroupOf L).map α₁
  have hD : Nat.card D = 8 := card_image_sylow_eight hF α hα.1 hsyl
  have hDQ : D ≤ Q := Subgroup.map_mono (fun l hl => hSB hl)
  have hDw : D ≤ stabAct w₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact hfix l (hSu _ (Subgroup.mem_subgroupOf.mp hl))
  let x' : ↥L := ⟨x, hxL⟩
  let e' : ↥L := ⟨e, heL⟩
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hg₃1 : α₁ x' ≠ 1 := by
    intro h1
    have h2 := hker x' h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x', h2⟩
    have h3 : x' ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h4 : orderOf x' ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h3
    have h5 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
    rw [h5] at h4
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4)
    omega
  have hg₃ : orderOf (α₁ x') = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx'3, map_one]) hg₃1
  have hQ : Q = ⊤ := eq_top_of_gen hF hw₀ hD hDQ hDw
    (Subgroup.mem_map.mpr ⟨x', Subgroup.mem_subgroupOf.mpr hxB, rfl⟩) (hfix x' hxu) hg₃
    (Subgroup.mem_map.mpr ⟨e', Subgroup.mem_subgroupOf.mpr heB, rfl⟩) (hmove e' heu)
  intro l hl
  have hmemQ : α₁ ⟨l, hl⟩ ∈ Q := by rw [hQ]; trivial
  obtain ⟨b, hb, hbl⟩ := Subgroup.mem_map.mp hmemQ
  have hker' : b⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := hker _ (by rw [map_mul, map_inv, hbl]; simp)
  have hpcl : ((b⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := by
    exact ⟨_, hker', rfl⟩
  have hS : ((b⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ B' :=
    hSB ⟨hpc hpcl, ((b⁻¹ * ⟨l, hl⟩ : ↥L)).2⟩
  have hbB : (b : G) ∈ B' := Subgroup.mem_subgroupOf.mp hb
  have : l = (b : G) * ((b⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [this]
  exact B'.mul_mem hbB hS

end Gen

end Stellmacher.L3YC

end CFSG.Quasithin
