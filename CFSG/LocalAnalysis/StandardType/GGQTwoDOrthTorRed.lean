module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorDefs

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

section Red

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X)

@[expose] def OrthFrameCore.toral (b : ↥Bs) : Φ.V ≃ₗ[Φ.F] Φ.V :=
  ((Φ.β b : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)

theorem OrthFrameCore.toral_mem (b : ↥Bs) : Φ.toral b ∈ Φ.A :=
  Φ.hβA b

private lemma plh_commute_toral_iff (b : ↥Bs) (y : ↥(orthDerived Φ.Q)) :
    (Φ.β b * y = y * Φ.β b) ↔
      ((Φ.toral b : Φ.V ≃ₗ[Φ.F] Φ.V) * (y : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (y : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.toral b : Φ.V ≃ₗ[Φ.F] Φ.V)) := by
  constructor
  · intro h
    have h' := congrArg (fun z : ↥(orthDerived Φ.Q) => (z : Φ.V ≃ₗ[Φ.F] Φ.V)) h
    simpa [OrthFrameCore.toral] using h'
  · intro h
    apply Subtype.ext
    simpa [OrthFrameCore.toral] using h

theorem OrthFrameCore.inf_centralizer_eq_img (b : ↥Bs) :
    X ⊓ Subgroup.centralizer ({(b : G)} : Set G) = Φ.img (Φ.torC (Φ.toral b)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_centralizer_iff] at hgC
    have hgC' : (b : G) * g = g * (b : G) := hgC (b : G) (Set.mem_singleton _)
    rw [OrthFrameCore.img, Subgroup.mem_map]
    rw [← Φ.hrange] at hgX
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hgX
    refine ⟨y, ?_, hy⟩
    rw [Subgroup.mem_subgroupOf, OrthFrameCore.torC, Subgroup.mem_inf]
    refine ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hconj : Φ.β b * y * (Φ.β b)⁻¹ = y := by
      apply Φ.hinj
      rw [Φ.hcompat b y, hy, hgC']
      group
    have hcomm : Φ.β b * y = y * Φ.β b := by
      calc Φ.β b * y = (Φ.β b * y * (Φ.β b)⁻¹) * (Φ.β b) := by group
        _ = y * (Φ.β b) := by rw [hconj]
    exact (plh_commute_toral_iff Φ b y).mp hcomm
  · intro g hg
    rw [OrthFrameCore.img, Subgroup.mem_map] at hg
    obtain ⟨y, hy, hgy⟩ := hg
    rw [Subgroup.mem_subgroupOf, OrthFrameCore.torC, Subgroup.mem_inf] at hy
    obtain ⟨-, hyC⟩ := hy
    rw [Subgroup.mem_centralizer_iff] at hyC
    have hyc : (Φ.toral b : Φ.V ≃ₗ[Φ.F] Φ.V) * (y : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (y : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.toral b : Φ.V ≃ₗ[Φ.F] Φ.V) :=
      hyC (Φ.toral b) (Set.mem_singleton _)
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [← Φ.hrange]
      exact MonoidHom.mem_range.mpr ⟨y, hgy⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      have hcomm : Φ.β b * y = y * Φ.β b := (plh_commute_toral_iff Φ b y).mpr hyc
      have hconj : Φ.β b * y * (Φ.β b)⁻¹ = y := by
        rw [hcomm]
        group
      have hcom := Φ.hcompat b y
      rw [hconj, hgy] at hcom
      have hb : (b : G) * g * (b : G)⁻¹ = g := hcom.symm
      calc (b : G) * g = (b : G) * g * (b : G)⁻¹ * (b : G) := by group
        _ = g * (b : G) := by rw [hb]

theorem OrthFrameCore.toral_eq_one (hZ : Subgroup.center ↥X = ⊥) {b : ↥Bs}
    (hb : X ≤ Subgroup.centralizer ({(b : G)} : Set G)) : Φ.toral b = 1 := by
  have hXmem : Φ.ψ (Φ.β b) ∈ X := by
    have h : Φ.ψ (Φ.β b) ∈ Φ.ψ.range := MonoidHom.mem_range.mpr ⟨Φ.β b, rfl⟩
    rwa [Φ.hrange] at h
  have hcen : (⟨Φ.ψ (Φ.β b), hXmem⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * Φ.ψ (Φ.β b) = Φ.ψ (Φ.β b) * (g : G)
    have hgX : (g : G) ∈ X := g.2
    have hgrange : (g : G) ∈ Φ.ψ.range := by
      rw [Φ.hrange]
      exact hgX
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hgrange
    have hbC : (b : G) * (g : G) = (g : G) * (b : G) := by
      have h := hb g.2
      rw [Subgroup.mem_centralizer_iff] at h
      exact h (b : G) (Set.mem_singleton _)
    have hconj : Φ.β b * y * (Φ.β b)⁻¹ = y := by
      apply Φ.hinj
      rw [Φ.hcompat b y, hy, hbC]
      group
    have hcomm : Φ.β b * y = y * Φ.β b := by
      calc Φ.β b * y = (Φ.β b * y * (Φ.β b)⁻¹) * (Φ.β b) := by group
        _ = y * (Φ.β b) := by rw [hconj]
    rw [← hy, ← map_mul, ← map_mul, Φ.hinj.eq_iff]
    exact hcomm.symm
  have h1 : (⟨Φ.ψ (Φ.β b), hXmem⟩ : ↥X) = 1 := by
    have h := hcen
    rw [hZ] at h
    simpa using h
  have hψ : Φ.ψ (Φ.β b) = 1 := by
    have h := congrArg (fun z : ↥X => (z : G)) h1
    simpa using h
  have hβ : Φ.β b = 1 := Φ.hinj (by rw [hψ, map_one])
  rw [OrthFrameCore.toral, hβ]
  rfl

theorem OrthFrameCore.exists_torC_eq_inf_centralizer [Fact p.Prime] {D : Subgroup G} {x : G}
    (hD : D ≤ Bs) (hDab : CFSG.Open.IsElemAbelian p D) (hDcard : Nat.card ↥D = p ^ 2)
    (hxD : x ∈ D) (hx1 : x ≠ 1) (hxX : X ≤ Subgroup.centralizer ({x} : Set G))
    (hZ : Subgroup.center ↥X = ⊥) :
    ∃ t ∈ Φ.A, X ⊓ Subgroup.centralizer (D : Set G) = Φ.img (Φ.torC t) := by
  classical
  have hp : p.Prime := Fact.out
  let ρ : ↥D →* ↥(orthDerived Φ.Q) := Φ.β.comp (Subgroup.inclusion hD)
  have hρβ : ∀ z : ↥D, ρ z = Φ.β ⟨z.1, hD z.2⟩ := by
    intro z
    rfl
  have hρx : ρ ⟨x, hxD⟩ = 1 := by
    have ht : Φ.toral (⟨x, hD hxD⟩ : ↥Bs) = 1 := Φ.toral_eq_one hZ hxX
    have hβx : Φ.β (⟨x, hD hxD⟩ : ↥Bs) = 1 := by
      apply Subtype.ext
      simpa [OrthFrameCore.toral] using ht
    show Φ.β (⟨x, hD hxD⟩ : ↥Bs) = 1
    exact hβx
  have hxpow : (⟨x, hxD⟩ : ↥D) ^ p = 1 := by
    apply Subtype.ext
    simpa using hDab.2 x hxD
  have hxne : (⟨x, hxD⟩ : ↥D) ≠ 1 := by
    intro h
    exact hx1 (by
      have h' := congrArg (fun z : ↥D => (z : G)) h
      simpa using h')
  have hord : orderOf (⟨x, hxD⟩ : ↥D) = p := orderOf_eq_prime hxpow hxne
  have hzp : Subgroup.zpowers (⟨x, hxD⟩ : ↥D) ≤ ρ.ker := by
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr hρx
  have hkerdvd : Nat.card (ρ.ker) ∣ p ^ 2 := by
    have h := Subgroup.card_subgroup_dvd_card (ρ.ker)
    rwa [hDcard] at h
  have hkerne : Nat.card (ρ.ker) ≠ 0 := by
    intro h0
    rw [h0] at hkerdvd
    obtain ⟨c, hc⟩ := hkerdvd
    rw [zero_mul] at hc
    exact (pow_ne_zero 2 hp.ne_zero) hc
  haveI : Finite ↥(ρ.ker) := Nat.finite_of_card_ne_zero hkerne
  have hkerge : p ≤ Nat.card (ρ.ker) := by
    have h := Subgroup.card_le_of_le hzp
    rw [Nat.card_zpowers, hord] at h
    exact h
  have hprod : Nat.card (ρ.ker) * Nat.card (ρ.range) = p ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rwa [hDcard] at h
  have hrange_le : Nat.card (ρ.range) ≤ p := by
    have h1 : p * Nat.card (ρ.range) ≤ Nat.card (ρ.ker) * Nat.card (ρ.range) :=
      Nat.mul_le_mul_right _ hkerge
    rw [hprod] at h1
    exact Nat.le_of_mul_le_mul_left (by simpa [pow_two] using h1) hp.pos
  have hrange_dvd : Nat.card (ρ.range) ∣ p := by
    have hdvd : Nat.card (ρ.range) ∣ p ^ 2 :=
      ⟨Nat.card (ρ.ker), by rw [mul_comm]; exact hprod.symm⟩
    obtain ⟨j, hj, hj_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hjle : j ≤ 1 := by
      rw [hj_eq] at hrange_le
      interval_cases j
      · exact Nat.zero_le 1
      · exact le_refl 1
      · exfalso
        have hpge2 : 2 ≤ p := hp.two_le
        rw [pow_two] at hrange_le
        have h2 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp.two_le
        omega
    rw [hj_eq]
    interval_cases j <;> simp
  have hcyc : IsCyclic ↥(ρ.range) := isCyclic_of_card_dvd_prime hrange_dvd
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  obtain ⟨d₀, hd₀⟩ := MonoidHom.mem_range.mp g.2
  refine ⟨Φ.toral ⟨d₀, hD d₀.2⟩, Φ.toral_mem ⟨d₀, hD d₀.2⟩, ?_⟩
  apply le_antisymm
  · intro g' hg'
    rw [← Φ.inf_centralizer_eq_img (⟨d₀, hD d₀.2⟩ : ↥Bs)]
    rw [Subgroup.mem_inf] at hg'
    obtain ⟨hg'X, hg'C⟩ := hg'
    rw [Subgroup.mem_centralizer_iff] at hg'C
    rw [Subgroup.mem_inf]
    refine ⟨hg'X, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact hg'C d₀ d₀.2
  · intro g' hg'
    rw [OrthFrameCore.img, Subgroup.mem_map] at hg'
    obtain ⟨y, hy, hgy⟩ := hg'
    rw [Subgroup.mem_subgroupOf, OrthFrameCore.torC, Subgroup.mem_inf] at hy
    obtain ⟨-, hyC⟩ := hy
    rw [Subgroup.mem_centralizer_iff] at hyC
    have hyc : (Φ.toral ⟨d₀, hD d₀.2⟩ : Φ.V ≃ₗ[Φ.F] Φ.V) * (y : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (y : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.toral ⟨d₀, hD d₀.2⟩ : Φ.V ≃ₗ[Φ.F] Φ.V) :=
      hyC (Φ.toral ⟨d₀, hD d₀.2⟩) (Set.mem_singleton _)
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [← Φ.hrange]
      exact MonoidHom.mem_range.mpr ⟨y, hgy⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hmem : (⟨ρ ⟨d, hd⟩, MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩⟩ : ↥(ρ.range)) ∈
          Subgroup.zpowers g := by
        rw [hg]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hρd : ρ ⟨d, hd⟩ = (ρ d₀) ^ k := by
        have hcoe := congrArg (fun z : ↥(ρ.range) => (z : ↥(orthDerived Φ.Q))) hk
        rw [Subgroup.coe_zpow, ← hd₀] at hcoe
        simpa using hcoe.symm
      have hβd : Φ.β ⟨d, hD hd⟩ = (Φ.β ⟨d₀, hD d₀.2⟩) ^ k := by
        have h := hρd
        rw [hρβ ⟨d, hd⟩, hρβ d₀] at h
        simpa using h
      have htd : Φ.toral ⟨d, hD hd⟩ = (Φ.toral ⟨d₀, hD d₀.2⟩) ^ k := by
        have hcoe := congrArg (fun z : ↥(orthDerived Φ.Q) =>
          (z : Φ.V ≃ₗ[Φ.F] Φ.V)) hβd
        rw [Subgroup.coe_zpow] at hcoe
        simpa only [OrthFrameCore.toral] using hcoe
      have hcomm : Commute (Φ.toral ⟨d₀, hD d₀.2⟩) (y : Φ.V ≃ₗ[Φ.F] Φ.V) := hyc
      have hcu : (Φ.toral ⟨d, hD hd⟩ : Φ.V ≃ₗ[Φ.F] Φ.V) * (y : Φ.V ≃ₗ[Φ.F] Φ.V) =
          (y : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.toral ⟨d, hD hd⟩ : Φ.V ≃ₗ[Φ.F] Φ.V) := by
        rw [htd]
        exact (hcomm.zpow_left k).eq
      have hconj : (Φ.β ⟨d, hD hd⟩ : ↥(orthDerived Φ.Q)) * y *
          (Φ.β ⟨d, hD hd⟩)⁻¹ = y := by
        apply Subtype.ext
        change (Φ.toral ⟨d, hD hd⟩ : Φ.V ≃ₗ[Φ.F] Φ.V) * (y : Φ.V ≃ₗ[Φ.F] Φ.V) *
          (Φ.toral ⟨d, hD hd⟩ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = (y : Φ.V ≃ₗ[Φ.F] Φ.V)
        rw [hcu]
        group
      have hcom := Φ.hcompat ⟨d, hD hd⟩ y
      rw [hconj, hgy] at hcom
      have hb : d * g' * d⁻¹ = g' := hcom.symm
      calc d * g' = d * g' * d⁻¹ * d := by group
        _ = g' * d := by rw [hb]

end Red

end OrthTorus

end CFSG.StandardType

end
