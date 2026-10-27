module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCharSum
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameLift
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

private lemma qtwoDB42_corr_comm {G H : Type} [Group G] [Group H] {Bs : Subgroup G}
    (ψ : H →* G) (β : ↥Bs →* H)
    (hcompat : ∀ (b : ↥Bs) (y : H), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    (b : ↥Bs) (y : H) :
    (ψ (β b))⁻¹ * (b : G) * ψ y = ψ y * ((ψ (β b))⁻¹ * (b : G)) := by
  have h1 : ψ (β b) * ψ y * (ψ (β b))⁻¹ = (b : G) * ψ y * (b : G)⁻¹ := by
    rw [← hcompat b y, map_mul, map_mul, map_inv]
  have h2 : (b : G) * ψ y = ψ (β b) * ψ y * (ψ (β b))⁻¹ * (b : G) := by
    rw [h1]
    group
  calc
    (ψ (β b))⁻¹ * (b : G) * ψ y = (ψ (β b))⁻¹ * ((b : G) * ψ y) := by group
    _ = (ψ (β b))⁻¹ * (ψ (β b) * ψ y * (ψ (β b))⁻¹ * (b : G)) := by rw [h2]
    _ = ψ y * ((ψ (β b))⁻¹ * (b : G)) := by group

private lemma qtwoDB42_mem_range {G H : Type} [Group G] [Group H] {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (ψ : H →* G) (hψ : Function.Injective ψ) (β : ↥Bs →* H)
    (hcompat : ∀ (b : ↥Bs) (y : H), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    (hconj : ∀ u v : H, (∀ y, u * y * u⁻¹ = v * y * v⁻¹) → u = v)
    {g : H} (hg3 : g ^ 3 = 1) (hgc : ∀ b : ↥Bs, g * β b = β b * g) : g ∈ β.range := by
  have hcen : ψ g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let b : ↥Bs := ⟨x, hx⟩
    have hx_eq : x = ψ (β b) * ((ψ (β b))⁻¹ * (b : G)) := by
      change x = ψ (β b) * ((ψ (β b))⁻¹ * x)
      group
    have h1 : ψ g * ψ (β b) = ψ (β b) * ψ g := by
      rw [← map_mul, ← map_mul, hgc b]
    have h2 := qtwoDB42_corr_comm ψ β hcompat b g
    calc x * ψ g = ψ (β b) * (((ψ (β b))⁻¹ * (b : G)) * ψ g) := by
          conv_lhs => rw [hx_eq]
          group
      _ = ψ (β b) * (ψ g * ((ψ (β b))⁻¹ * (b : G))) := by rw [h2]
      _ = (ψ (β b) * ψ g) * ((ψ (β b))⁻¹ * (b : G)) := by group
      _ = (ψ g * ψ (β b)) * ((ψ (β b))⁻¹ * (b : G)) := by rw [h1]
      _ = ψ g * (ψ (β b) * ((ψ (β b))⁻¹ * (b : G))) := by group
      _ = ψ g * x := by rw [← hx_eq]
  have hmem : ψ g ∈ Bs := hSC (ψ g) hcen (by rw [← map_pow, hg3, map_one])
  let b₀ : ↥Bs := ⟨ψ g, hmem⟩
  have hg : g = β b₀ := by
    apply hconj
    intro y
    apply hψ
    rw [hcompat b₀ y]
    show ψ (g * y * g⁻¹) = ψ g * ψ y * (ψ g)⁻¹
    simp only [map_mul, map_inv]
  exact ⟨b₀, hg.symm⟩

theorem qtwoDB42_frameCore_of_model {G : Type} [Group G] [Finite G] {Bs Y : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {d : ℕ}
    (hd : 4 ≤ d) (hdim : Module.finrank (ZMod 2) V = 2 * d) (htype : IsPlusType Q ↔ Even d)
    (ψ : ↥(orthDerived Q) →* G) (hψ : Function.Injective ψ) (hY : ψ.range = Y)
    (β : ↥Bs →* ↥(orthDerived Q))
    (hcompat : ∀ (b : ↥Bs) (y : ↥(orthDerived Q)),
      ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    (hne : ∃ b : ↥Bs, β b ≠ 1) :
    (∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = d) ∧
      Subgroup.center ↥Y = ⊥ := by
  classical
  subst hY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ∃ U : Submodule (ZMod 2) V, Module.finrank (ZMod 2) U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hd hdim
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hZ : Subgroup.center ↥(orthDerived Q) = ⊥ :=
    CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  have hconj : ∀ u v : ↥(orthDerived Q), (∀ y, u * y * u⁻¹ = v * y * v⁻¹) → u = v := by
    intro u v h
    have hc : v⁻¹ * u ∈ Subgroup.center ↥(orthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : v⁻¹ * u * y * (v⁻¹ * u)⁻¹ = y := by
        calc v⁻¹ * u * y * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * y * u⁻¹) * v := by group
          _ = y := by rw [h y]; group
      calc y * (v⁻¹ * u) = (v⁻¹ * u * y * (v⁻¹ * u)⁻¹) * (v⁻¹ * u) := by rw [h1]
        _ = v⁻¹ * u * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc |>.symm
  have hcomm : ∀ b b' : ↥Bs, β b * β b' = β b' * β b := by
    intro b b'
    have h : b * b' = b' * b := Subtype.ext (hBs.comm b.2 b'.2)
    rw [← map_mul, ← map_mul, h]
  have hβpow : ∀ b : ↥Bs, β b ^ 3 = 1 := by
    intro b
    have hb : b ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 (b : G) b.2)
    rw [← map_pow, hb, map_one]
  let A : Subgroup (V ≃ₗ[ZMod 2] V) := β.range.map (orthDerived Q).subtype
  have hβA : ∀ b : ↥Bs, (β b : V ≃ₗ[ZMod 2] V) ∈ A := fun b => ⟨β b, ⟨b, rfl⟩, rfl⟩
  have hβsurj : ∀ a ∈ A, ∃ b : ↥Bs, (β b : V ≃ₗ[ZMod 2] V) = a := by
    rintro a ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro _ ⟨x, ⟨b, rfl⟩, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hβpow b)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, ⟨b, rfl⟩, rfl⟩ _ ⟨y, ⟨b', rfl⟩, rfl⟩
    exact congrArg Subtype.val (hcomm b b')
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hg3 hgc
    have hmem := qtwoDB42_mem_range hSC ψ hψ β hcompat hconj (g := ⟨g, hg⟩)
      (Subtype.ext (by simpa using hg3))
      (fun b => Subtype.ext (hgc (β b : V ≃ₗ[ZMod 2] V) (hβA b)))
    exact ⟨⟨g, hg⟩, hmem, rfl⟩
  have hne' : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨(β b : V ≃ₗ[ZMod 2] V), hβA b, fun h => hb (Subtype.ext h)⟩
  have hpqF : 3 ∣ Nat.card (ZMod 2) + 1 := by simp [Nat.card_zmod]
  obtain ⟨r, τ, Fframe, D, hDadd, hDmod, hDfin, c, θ, hτF, hτinj, hτrange, hfinD,
    hcpow, hcfix, hctwist, hcroot, hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsign,
    hnoFixed, hexFixed⟩ :=
    OrthTorus.exists_torus_blocks (K := ZMod 2) (V := V) (Q := Q) (p := 3)
      (by norm_num) (Or.inr hpqF) hQ hT hAΩ hApow hAcomm hmax hne'
  letI : AddCommGroup D := hDadd
  letI : Module (ZMod 2) D := hDmod
  letI : FiniteDimensional (ZMod 2) D := hDfin
  let Δ : OrthTorus.TBJOmData Q 3 A r :=
    { τ := τ
      F := Fframe
      D := D
      c := c
      θ := θ
      τ_eq := hτF
      τ_inj := hτinj
      τ_range := hτrange
      finrank_D := hfinD
      c_pow := hcpow
      c_fix := hcfix
      c_twist := hctwist
      c_roots := hcroot
      θ_inj := hθinj
      θ_range := hθrange
      θ_act := hθact
      normalizer := hnorm
      swapMove := hswap
      dinvMove := hdinv
      signMove := hsign
      noFixed := hnoFixed
      exFixed := hexFixed }
  have htype' : (IsPlusType Q ∧ Even d) ∨ (¬ IsPlusType Q ∧ Odd d) := by
    by_cases hev : Even d
    · exact Or.inl ⟨htype.mpr hev, hev⟩
    · exact Or.inr ⟨fun h => hev (htype.mp h), Nat.not_even_iff_odd.mp hev⟩
  have hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] :=
    OrthTorus.charSum_top_modEq_one_of_witt hQ (r := d) (by omega) hdim hpqF htype'
  have hfinrank : Module.finrank (ZMod 2) V = 2 * r :=
    OrthTorus.finrank_eq_two_mul_of_charSum (p := 3) (by norm_num) (Or.inr hpqF) hQ hT hAΩ
      hApow hAcomm hmax hne' hτinj hτrange hchar
  have hr_eq : r = d := by omega
  have hr4 : 4 ≤ r := by omega
  have hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0 := Δ.noFixed hchar
  refine ⟨⟨{ F := ZMod 2, V := V, Q := Q, A := A, r := r, Δ := Δ, ψ := ψ, β := β,
             hA := hAΩ, hr := hr4, hpq := hpqF, hfix := hfix, hinj := hψ, hrange := rfl,
             hβA := hβA, hβsurj := hβsurj, hcompat := hcompat, swapReal := ?_,
             dinvReal := ?_ }, Nat.card_zmod 2, hr_eq⟩, ?_⟩
  · intro i j hij
    obtain ⟨w, hwmem, -, hwact⟩ := hswap i j hij
    refine ⟨⟨w, hwmem⟩, fun f' => hwact f', ?_⟩
    apply OrthTorus.mem_normalizer_of_conj_mem_range ψ β hBs hSC hcompat hcomm
    intro b
    obtain ⟨f, hf⟩ : (β b : V ≃ₗ[ZMod 2] V) ∈ τ.range := by
      rw [hτrange]
      exact hβA b
    have humem : τ (SpCoord.permAut (Equiv.swap i j) f) ∈ A := by
      rw [← hτrange]
      exact ⟨SpCoord.permAut (Equiv.swap i j) f, rfl⟩
    have hu_od : τ (SpCoord.permAut (Equiv.swap i j) f) ∈ orthDerived Q := hAΩ humem
    obtain ⟨y, hy, hyval⟩ := humem
    have hu_eq : (⟨τ (SpCoord.permAut (Equiv.swap i j) f), hu_od⟩ : ↥(orthDerived Q)) = y :=
      Subtype.ext hyval.symm
    obtain ⟨b', hb'⟩ : (⟨τ (SpCoord.permAut (Equiv.swap i j) f), hu_od⟩ :
        ↥(orthDerived Q)) ∈ β.range := by
      rw [hu_eq]
      exact hy
    refine ⟨b', ?_⟩
    rw [hb']
    apply Subtype.ext
    change (w : V ≃ₗ[ZMod 2] V) * (β b : V ≃ₗ[ZMod 2] V) * (w : V ≃ₗ[ZMod 2] V)⁻¹ =
      τ (SpCoord.permAut (Equiv.swap i j) f)
    rw [← hf]
    exact hwact f
  · intro i j hij
    obtain ⟨w, hwmem, -, hwact⟩ := hdinv i j hij
    refine ⟨⟨w, hwmem⟩, fun f' => hwact f', ?_⟩
    apply OrthTorus.mem_normalizer_of_conj_mem_range ψ β hBs hSC hcompat hcomm
    intro b
    obtain ⟨f, hf⟩ : (β b : V ≃ₗ[ZMod 2] V) ∈ τ.range := by
      rw [hτrange]
      exact hβA b
    have humem : τ (NbrOrth.dinv i j f) ∈ A := by
      rw [← hτrange]
      exact ⟨NbrOrth.dinv i j f, rfl⟩
    have hu_od : τ (NbrOrth.dinv i j f) ∈ orthDerived Q := hAΩ humem
    obtain ⟨y, hy, hyval⟩ := humem
    have hu_eq : (⟨τ (NbrOrth.dinv i j f), hu_od⟩ : ↥(orthDerived Q)) = y :=
      Subtype.ext hyval.symm
    obtain ⟨b', hb'⟩ : (⟨τ (NbrOrth.dinv i j f), hu_od⟩ : ↥(orthDerived Q)) ∈ β.range := by
      rw [hu_eq]
      exact hy
    refine ⟨b', ?_⟩
    rw [hb']
    apply Subtype.ext
    change (w : V ≃ₗ[ZMod 2] V) * (β b : V ≃ₗ[ZMod 2] V) * (w : V ≃ₗ[ZMod 2] V)⁻¹ =
      τ (NbrOrth.dinv i j f)
    rw [← hf]
    exact hwact f
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨u, rfl⟩ := (MonoidHom.ofInjective hψ).surjective z
    have hu : u ∈ Subgroup.center ↥(orthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := Subgroup.mem_center_iff.mp hz (MonoidHom.ofInjective hψ y)
      apply (MonoidHom.ofInjective hψ).injective
      rw [map_mul, map_mul]
      exact h
    rw [hZ, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact Subgroup.one_mem _

end CFSG.StandardType.QTwo

end
