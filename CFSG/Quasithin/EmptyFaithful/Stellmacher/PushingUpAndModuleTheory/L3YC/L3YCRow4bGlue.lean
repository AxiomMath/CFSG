module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCL5B2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCLemmaUBar
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod CFSG.Open
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7
open scoped commutatorElement

namespace Stellmacher.PU.L3YC

theorem glue_omega {Y : Type} [Group Y] {K B : Subgroup Y} (hBK : B ≤ K)
    (ψ : ↥K ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) (g : SpecialLinearGroup (Fin 5) (ZMod 2))
    (θ : ↥B →* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hθ : ∀ x : ↥B, θ x = g⁻¹ * ψ ⟨x, hBK x.2⟩ * g) (N : Subgroup ↥B)
    (ω : SpecialLinearGroup (Fin 5) (ZMod 2))
    (hωn : ω ∈ Subgroup.normalizer (((⊤ : Subgroup ↥B).map θ : Subgroup (SpecialLinearGroup
      (Fin 5) (ZMod 2))) : Set (SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hω3 : ω ^ 3 = 1)
    (hωc : ∀ (b : ↥B) (c : SpecialLinearGroup (Fin 5) (ZMod 2)),
      (∀ n ∈ N, θ n * c = c * θ n) → ω ≠ θ b * c) :
    ∃ x : Y, x ∈ K ∧ x ∈ Subgroup.normalizer (B : Set Y) ∧ x ^ 3 = 1 ∧
      ∀ b ∈ B, ∀ c : Y, (∀ n ∈ N, c * (n : Y) = (n : Y) * c) → x ≠ b * c := by
  classical
  set ωK : ↥K := ψ.symm (g * ω * g⁻¹) with hωK
  have hψω : ψ ωK = g * ω * g⁻¹ := ψ.apply_symm_apply _
  have hω : ω = g⁻¹ * ψ ωK * g := by rw [hψω]; group
  have hthθ : ∀ b : ↥B, ψ ⟨b, hBK b.2⟩ = g * θ b * g⁻¹ := fun b => by rw [hθ b]; group
  refine ⟨(ωK : Y), ωK.2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : θ ⟨y, hy⟩ ∈ ((⊤ : Subgroup ↥B).map θ) := ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
      obtain ⟨b', -, hb'⟩ := (Subgroup.mem_normalizer_iff.mp hωn _).mp h1
      have h2 : ψ ⟨b', hBK b'.2⟩ = ψ (ωK * ⟨y, hBK hy⟩ * ωK⁻¹) := by
        rw [map_mul, map_mul, map_inv, hψω, hthθ b', hb', hthθ ⟨y, hy⟩]
        group
      have h3 := ψ.injective h2
      have h4 := congrArg Subtype.val h3
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h4
      rw [← h4]
      exact b'.2
    · intro hy
      have hyK : y ∈ K := by
        have : y = (ωK : Y)⁻¹ * ((ωK : Y) * y * (ωK : Y)⁻¹) * (ωK : Y) := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem ωK.2) (hBK hy)) ωK.2
      have h1 : θ ⟨_, hy⟩ ∈ ((⊤ : Subgroup ↥B).map θ) := ⟨⟨_, hy⟩, Subgroup.mem_top _, rfl⟩
      have h1' : ω⁻¹ * θ ⟨_, hy⟩ * ω ∈ ((⊤ : Subgroup ↥B).map θ) := by
        rw [Subgroup.mem_normalizer_iff] at hωn
        have := (hωn (ω⁻¹ * θ ⟨_, hy⟩ * ω)).mpr (by
          have e : ω * (ω⁻¹ * θ ⟨_, hy⟩ * ω) * ω⁻¹ = θ ⟨_, hy⟩ := by group
          rw [e]; exact h1)
        exact this
      obtain ⟨b'', -, hb''⟩ := h1'
      have h2 : ψ ⟨b'', hBK b''.2⟩ = ψ ⟨y, hyK⟩ := by
        have e : (⟨y, hyK⟩ : ↥K) = ωK⁻¹ * ⟨_, hBK hy⟩ * ωK := Subtype.ext (by
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group)
        rw [e, map_mul, map_mul, map_inv, hψω, hthθ b'', hb'', hthθ ⟨_, hy⟩]
        group
      have h3 := ψ.injective h2
      have h4 := congrArg Subtype.val h3
      simp only at h4
      rw [← h4]
      exact b''.2
  · have h1 : ψ (ωK ^ 3) = 1 := by
      rw [map_pow, hψω]
      have hω3' : ω * ω * ω = 1 := by
        have : ω * ω * ω = ω ^ 3 := by simp only [pow_three, mul_assoc]
        rw [this, hω3]
      calc (g * ω * g⁻¹) ^ 3 = (g * ω * g⁻¹) * (g * ω * g⁻¹) * (g * ω * g⁻¹) := by
            simp only [pow_three, mul_assoc]
        _ = g * (ω * ω * ω) * g⁻¹ := by group
        _ = 1 := by rw [hω3']; group
    have h2 : ωK ^ 3 = 1 := ψ.injective (by rw [h1, map_one])
    have := congrArg Subtype.val h2
    simpa using this
  · intro b hb c hc hX
    have hcK : c ∈ K := by
      have : c = b⁻¹ * (ωK : Y) := by rw [hX]; group
      rw [this]
      exact K.mul_mem (K.inv_mem (hBK hb)) ωK.2
    let c' : SpecialLinearGroup (Fin 5) (ZMod 2) := g⁻¹ * ψ ⟨c, hcK⟩ * g
    have hcomm : ∀ n ∈ N, θ n * c' = c' * θ n := by
      intro n hn
      have h1 : ψ ⟨n, hBK n.2⟩ * ψ ⟨c, hcK⟩ = ψ ⟨c, hcK⟩ * ψ ⟨n, hBK n.2⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc n hn).symm
      rw [hθ n]
      show g⁻¹ * ψ ⟨n, hBK n.2⟩ * g * (g⁻¹ * ψ ⟨c, hcK⟩ * g) =
        g⁻¹ * ψ ⟨c, hcK⟩ * g * (g⁻¹ * ψ ⟨n, hBK n.2⟩ * g)
      calc g⁻¹ * ψ ⟨n, hBK n.2⟩ * g * (g⁻¹ * ψ ⟨c, hcK⟩ * g)
          = g⁻¹ * (ψ ⟨n, hBK n.2⟩ * ψ ⟨c, hcK⟩) * g := by group
        _ = g⁻¹ * (ψ ⟨c, hcK⟩ * ψ ⟨n, hBK n.2⟩) * g := by rw [h1]
        _ = g⁻¹ * ψ ⟨c, hcK⟩ * g * (g⁻¹ * ψ ⟨n, hBK n.2⟩ * g) := by group
    apply hωc ⟨b, hb⟩ c' hcomm
    have hωK' : ωK = ⟨b, hBK hb⟩ * ⟨c, hcK⟩ := Subtype.ext hX
    rw [hω, hωK', map_mul, hθ ⟨b, hb⟩]
    show g⁻¹ * (ψ ⟨b, hBK hb⟩ * ψ ⟨c, hcK⟩) * g =
      g⁻¹ * ψ ⟨b, hBK (⟨b, hb⟩ : ↥B).2⟩ * g * (g⁻¹ * ψ ⟨c, hcK⟩ * g)
    group

section Bar

variable {G : Type} [Group G] [Finite G]

theorem Qbar_eq_map {H G₀ L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) :
    Qbar H G₀ L = (((c134Q G₀ L).subgroupOf L).map (toModO2Image hLH)).map
      (modO2Image H L).subtype := by
  have hQL : c134Q G₀ L ≤ L := (MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L)
  rw [Subgroup.map_map]
  have : (modO2Image H L).subtype.comp (toModO2Image hLH) = toBar hLH := rfl
  rw [this, map_subgroupOf_toBar hLH hQL]
  rfl

theorem Qbar_eq_pCore
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L)
    (hN : ⁅CFSG.pCore 2 ↥(modO2Image H L), (⊤ : Subgroup ↥(modO2Image H L))⁆ =
      CFSG.pCore 2 ↥(modO2Image H L)) :
    Qbar H G₀ L = (CFSG.pCore 2 ↥(modO2Image H L)).map (modO2Image H L).subtype := by
  obtain ⟨-, hle⟩ := card_pCore_modO2Image_le hLH hLG hGL hq hperf h
  refine le_antisymm hle ?_
  rw [Qbar_eq_map hLH hLG hGL]
  refine Subgroup.map_mono ?_
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  set π := toModO2Image hLH with hπ
  have hπs := toModO2Image_surjective hLH
  have hK := isPGroup_ker_toModO2Image hLH
  calc CFSG.pCore 2 ↥(modO2Image H L)
      = ⁅CFSG.pCore 2 ↥(modO2Image H L), (⊤ : Subgroup ↥(modO2Image H L))⁆ := hN.symm
    _ ≤ ⁅(CFSG.pCore 2 ↥L).map π, (⊤ : Subgroup ↥(modO2Image H L))⁆ :=
        Subgroup.commutator_mono (pCore_le_map π hπs hK) le_rfl
    _ = (⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆).map π := by
        rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπs]
    _ ≤ ((c134Q G₀ L).subgroupOf L).map π :=
        Subgroup.map_mono (commutator_pCore_le_subgroupOf hLG hGL h)

theorem row4_L5_omega
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) {K P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hK5 : IsPSL 5 2 1 ↥K) (hpar : IsParabolic2 K P) (hBP : modO2Image H L = perfectCore P) :
    Qbar H G₀ L = (CFSG.pCore 2 ↥(modO2Image H L)).map (modO2Image H L).subtype ∧
    ∃ x : ↥H ⧸ CFSG.pCore 2 ↥H, x ∈ K ∧
      x ∈ Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧ x ^ 3 = 1 ∧
      ∀ b ∈ modO2Image H L, ∀ c ∈ Subgroup.centralizer (Qbar H G₀ L : Set (↥H ⧸ CFSG.pCore 2 ↥H)),
        x ≠ b * c := by
  classical
  obtain ⟨ψ, g, a, hamn, α, ha, hαs, hker, hblk, hcross⟩ :=
    row4_L5_not_middle hLH hLG hGL hq hperf h hK5 hpar hBP
  have hBK : modO2Image H L ≤ K := (hBP ▸ perfectCore_le P : modO2Image H L ≤ P).trans hpar.1
  let θ : ↥(modO2Image H L) →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (ψ.toMonoidHom.comp (Subgroup.inclusion hBK))
  have hθ : ∀ x : ↥(modO2Image H L), θ x = g⁻¹ * ψ ⟨x, hBK x.2⟩ * g := fun x => by
    simp [θ, Subgroup.inclusion]
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have h1 : g⁻¹ * ψ ⟨x, hBK x.2⟩ * g = g⁻¹ * ψ ⟨y, hBK y.2⟩ * g := by
      rw [← hθ, ← hθ]; exact hxy
    have h2 : ψ ⟨x, hBK x.2⟩ = ψ ⟨y, hBK y.2⟩ := mul_left_cancel (mul_right_cancel h1)
    have h3 := ψ.injective h2
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext h4
  have hmain : ∃ ω : SpecialLinearGroup (Fin 5) (ZMod 2),
      ω ∈ Subgroup.normalizer (((⊤ : Subgroup ↥(modO2Image H L)).map θ : Subgroup
        (SpecialLinearGroup (Fin 5) (ZMod 2))) : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
      ω ^ 3 = 1 ∧
      (∀ (b : ↥(modO2Image H L)) (c : SpecialLinearGroup (Fin 5) (ZMod 2)),
        (∀ n ∈ CFSG.pCore 2 ↥(modO2Image H L), θ n * c = c * θ n) → ω ≠ θ b * c) ∧
      ⁅CFSG.pCore 2 ↥(modO2Image H L), (⊤ : Subgroup ↥(modO2Image H L))⁆ =
        CFSG.pCore 2 ↥(modO2Image H L) := by
    rcases ha with rfl | rfl
    · refine config_a0 θ α hθinj hαs hker (fun x => ?_) (fun k l hc => ?_)
      · rw [hθ]; exact hblk x
      · obtain ⟨p, hp, hpe⟩ := hcross k l hc
        exact ⟨p, hp, by rw [hθ]; exact hpe⟩
    · refine config_a2 θ α hθinj hαs hker (fun x => ?_) (fun k l hc => ?_)
      · rw [hθ]; exact hblk x
      · obtain ⟨p, hp, hpe⟩ := hcross k l hc
        exact ⟨p, hp, by rw [hθ]; exact hpe⟩
  obtain ⟨ω, hωn, hω3, hωc, hcomm⟩ := hmain
  have hQ := Qbar_eq_pCore hLH hLG hGL hq hperf h hcomm
  refine ⟨hQ, ?_⟩
  obtain ⟨x, hxK, hxn, hx3, hxc⟩ := glue_omega hBK ψ g θ hθ (CFSG.pCore 2 ↥(modO2Image H L)) ω
    hωn hω3 hωc
  refine ⟨x, hxK, hxn, hx3, fun b hb c hc => hxc b hb c (fun n hn => ?_)⟩
  rw [hQ] at hc
  exact (Subgroup.mem_centralizer_iff.mp hc (n : ↥H ⧸ CFSG.pCore 2 ↥H)
    ⟨n, hn, rfl⟩).symm

theorem row4_L5_conj
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) {K P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hK5 : IsPSL 5 2 1 ↥K) (hpar : IsParabolic2 K P) (hBP : modO2Image H L = perfectCore P) :
    ∃ ω : ↥H ⧸ CFSG.pCore 2 ↥H, ω ∈ K ∧
      ω ∈ Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧ ω ^ 3 = 1 ∧
      ∀ b ∈ modO2Image H L, ∃ q ∈ Qbar H G₀ L, ω * q * ω⁻¹ ≠ b * q * b⁻¹ := by
  obtain ⟨-, x, hxK, hxn, hx3, hxc⟩ :=
    row4_L5_omega hLH hLG hGL hq hperf h hK5 hpar hBP
  refine ⟨x, hxK, hxn, hx3, fun b hb => ?_⟩
  by_contra hall
  push Not at hall
  refine hxc b hb (b⁻¹ * x) ?_ (by group)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq'
  have h1 := hall q hq'
  calc q * (b⁻¹ * x) = b⁻¹ * (b * q * b⁻¹) * x := by group
    _ = b⁻¹ * (x * q * x⁻¹) * x := by rw [h1]
    _ = b⁻¹ * x * q := by group

end Bar

end Stellmacher.PU.L3YC

end CFSG.Quasithin
