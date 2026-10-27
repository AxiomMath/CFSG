module

public import CFSG.RankThree.GF2n.Parrott.FusionE16
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoSylow

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

variable {H X : Type} [Group H] [Finite H] [Group X] [Finite X]

theorem E16Config.exists_transport (cfg : E16Config H) (ψ : H →* X)
    (hψ : Function.Injective ψ) {x : X} (hx : x = ψ (cfg.u 0))
    (hrange : ψ.range = Subgroup.centralizer ({x} : Set X)) :
    ∃ cfg' : E16Config X, cfg'.u 0 = x ∧ cfg'.u 1 = ψ (cfg.u 1) := by
  classical
  have hu0 : cfg.u 0 ≠ 1 := by
    intro h
    have := cfg.ev_inj 1 (by norm_num) 0 (by norm_num) (by rw [cfg.ev_one, cfg.ev_zero, h])
    omega
  have hord0 : orderOf (cfg.u 0) = 2 := orderOf_eq_prime (by simpa using cfg.hsq 0) hu0
  have hxord : orderOf x = 2 := by
    rw [hx, orderOf_injective ψ hψ]
    exact hord0
  obtain ⟨R, hR⟩ := cfg.hPsyl
  have hP2 : IsPGroup 2 cfg.P := hR ▸ R.isPGroup'
  set P' : Subgroup X := cfg.P.map ψ with hP'
  have hT : IsPGroup 2 P' := hP2.map ψ
  have hxP' : x ∈ P' := hx ▸ Subgroup.mem_map_of_mem ψ (cfg.hSP 0)
  have hP'r : P' ≤ ψ.range := by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  have hP'le : P' ≤ Subgroup.centralizer ({x} : Set X) := hrange ▸ hP'r
  have hcardP' : Nat.card P' = Nat.card cfg.P := Subgroup.card_map_of_injective hψ
  have hmax : ∀ Pp : Subgroup X, IsPGroup 2 Pp → Pp ≤ Subgroup.centralizer ({x} : Set X) →
      Nat.card Pp ≤ Nat.card P' := by
    intro Pp hPp hPpC
    rw [← hrange] at hPpC
    have hQ : IsPGroup 2 (Pp.comap ψ) := hPp.comap_of_injective ψ hψ
    obtain ⟨R', hR'⟩ := hQ.exists_le_sylow
    have hcardR : Nat.card (R' : Subgroup H) = Nat.card (R : Subgroup H) := by
      rw [R'.card_eq_multiplicity, R.card_eq_multiplicity]
    have h1 : Nat.card (Pp.comap ψ) ≤ Nat.card (R' : Subgroup H) := Subgroup.card_le_of_le hR'
    have h2 : (Pp.comap ψ).map ψ = Pp := Subgroup.map_comap_eq_self hPpC
    calc Nat.card Pp = Nat.card ((Pp.comap ψ).map ψ) := by rw [h2]
      _ = Nat.card (Pp.comap ψ) := Subgroup.card_map_of_injective hψ
      _ ≤ Nat.card (R' : Subgroup H) := h1
      _ = Nat.card (R : Subgroup H) := hcardR
      _ = Nat.card cfg.P := by rw [hR]
      _ = Nat.card P' := hcardP'.symm
  have hZ : ∀ t ∈ P', (∀ s ∈ P', t * s = s * t) → t ∈ Subgroup.zpowers x := by
    rintro _ ⟨t₀, ht₀, rfl⟩ hcomm
    have h1 : ∀ s ∈ cfg.P, t₀ * s = s * t₀ := fun s hs =>
      hψ (by rw [map_mul, map_mul]; exact hcomm (ψ s) (Subgroup.mem_map_of_mem ψ hs))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (cfg.mem_zpowers_of_central ht₀ h1)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [hx, ← map_zpow, hk]⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_center_le_zpowers hxord hT hxP' hP'le hmax hZ
  have hclos : Subgroup.closure (Set.range fun i => ψ (cfg.u i)) =
      (Subgroup.closure (Set.range cfg.u)).map ψ := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have map_conj : ∀ {g y z : H}, g * y * g⁻¹ = z → ψ g * ψ y * (ψ g)⁻¹ = ψ z := fun h => by
    simpa only [map_mul, map_inv] using congrArg ψ h
  refine ⟨⟨fun i => ψ (cfg.u i), ψ cfg.a, ψ cfg.b₁, ψ cfg.ρ, P',
    fun i => by rw [← map_pow, cfg.hsq, map_one],
    fun i j => (cfg.hcomm i j).map ψ,
    ?_, ?_, ?_, ?_,
    fun i => Subgroup.mem_map_of_mem ψ (cfg.hSP i),
    Subgroup.mem_map_of_mem ψ cfg.haP, Subgroup.mem_map_of_mem ψ cfg.hbP,
    ⟨S, hS⟩, ?_, ?_, ?_⟩, hx.symm, rfl⟩
  · intro c hc h
    apply cfg.hker c hc
    apply hψ
    have h1 : ψ (List.ofFn fun i => cfg.u i ^ (c i : ℕ)).prod =
        (List.ofFn fun i => ψ (cfg.u i) ^ (c i : ℕ)).prod := by
      rw [map_list_prod, List.map_ofFn]
      simp [Function.comp_def, map_pow]
    rw [h1, h, map_one]
  · obtain ⟨h0, h1, h2, h3⟩ := cfg.act_a
    refine ⟨map_conj h0, map_conj h1, ?_, ?_⟩
    · have := map_conj h2
      rwa [map_mul] at this
    · have := map_conj h3
      rwa [map_mul, map_mul] at this
  · obtain ⟨h0, h1, h2, h3⟩ := cfg.act_b
    refine ⟨map_conj h0, ?_, map_conj h2, ?_⟩
    · have := map_conj h1
      rwa [map_mul] at this
    · have := map_conj h3
      rwa [map_mul, map_mul] at this
  · obtain ⟨h0, h1, h2, h3⟩ := cfg.act_ρ
    refine ⟨map_conj h0, map_conj h1, ?_, map_conj h3⟩
    have := map_conj h2
    rwa [map_mul] at this
  · rintro _ ⟨p₀, hp₀, rfl⟩
    obtain ⟨s, hs, i, j, rfl⟩ := cfg.hPcos p₀ hp₀
    refine ⟨ψ s, ?_, i, j, by simp [map_mul, map_pow]⟩
    rw [hclos]
    exact Subgroup.mem_map_of_mem ψ hs
  · intro E hE hEel hEc
    rw [hclos]
    have hEmap : (E.comap ψ).map ψ = E := Subgroup.map_comap_eq_self (hE.trans hP'r)
    have hE₀P : E.comap ψ ≤ cfg.P := by
      intro e he
      obtain ⟨p, hp, hpe⟩ := hE he
      exact hψ hpe ▸ hp
    have hEel₀ : CFSG.Open.IsElemAbelian 2 (E.comap ψ) := hEel.comap hψ
    have hEc₀ : Nat.card (E.comap ψ) = 16 :=
      calc Nat.card (E.comap ψ) = Nat.card ((E.comap ψ).map ψ) :=
            (Subgroup.card_map_of_injective hψ).symm
        _ = Nat.card E := by rw [hEmap]
        _ = 16 := hEc
    have := cfg.hunique _ hE₀P hEel₀ hEc₀
    calc E = (E.comap ψ).map ψ := hEmap.symm
      _ = _ := by rw [this]
  · intro g hg
    rw [hclos] at hg ⊢
    have hxS : x ∈ (Subgroup.closure (Set.range cfg.u)).map ψ := by
      rw [hx]
      exact Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure ⟨0, rfl⟩)
    have hgC : g ∈ Subgroup.centralizer ({x} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hg x hxS)
    rw [← hrange] at hgC
    obtain ⟨g₀, rfl⟩ := hgC
    refine Subgroup.mem_map_of_mem ψ (cfg.hCS g₀ fun s hs => hψ ?_)
    rw [map_mul, map_mul]
    exact hg (ψ s) (Subgroup.mem_map_of_mem ψ hs)

end CFSG.RankThree.GF2n.Parrott.FusionE16
