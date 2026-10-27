module

public import CFSG.Quasithin.Background.RonanE51One

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open
open scoped commutatorElement

theorem comap_pCore_le_of_cover {Γ : Type} [Group Γ] [Finite Γ] {A' D' S' U : Subgroup Γ}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPA : CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ) =
      ⁅CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ), A'.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))⁆)
    [hSn : S'.Normal] (hD2 : IsPGroup 2 D') (hDS : D' ≤ S')
    (hDA : ∀ d ∈ D', ∀ a ∈ A', d * a = a * d) (hQU : CFSG.pCore 2 Γ ≤ U)
    (hSU : twoResidual S' ≤ U)
    (hcov : ∀ c : Γ, QuotientGroup.mk' (CFSG.pCore 2 Γ) c ∈ CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ) →
      QuotientGroup.mk' (CFSG.pCore 2 Γ) c ∈ Subgroup.centralizer
        ((D'.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) : Subgroup (Γ ⧸ CFSG.pCore 2 Γ)) :
          Set (Γ ⧸ CFSG.pCore 2 Γ)) →
      ∀ a ∈ A', ⁅c, a⁆ ∈ U) :
    (CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ)).comap (QuotientGroup.mk' (CFSG.pCore 2 Γ)) ≤ U := by
  have : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore 2 Γ with hQ
  set π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set P₀ : Subgroup (Γ ⧸ Q) := CFSG.pCore p (Γ ⧸ Q) with hP₀
  have hP₀p : IsPGroup p P₀ := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hP₀n : P₀.Normal := CFSG.LieType.BorelTits.pCore_normal p
  set Ā : Subgroup (Γ ⧸ Q) := A'.map π with hĀ
  set D₁ : Subgroup (Γ ⧸ Q) := D'.map π with hD₁
  set S₁ : Subgroup (Γ ⧸ Q) := S'.map π with hS₁
  set Ū : Subgroup (Γ ⧸ Q) := U.map π with hŪ
  have hS₁n : S₁.Normal := Subgroup.Normal.map hSn π hπs
  have hUpre : Ū.comap π = U := by
    rw [hŪ, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
    exact sup_eq_left.2 hQU
  suffices hP₀Ū : P₀ ≤ Ū by
    rw [← hUpre]
    exact Subgroup.comap_mono hP₀Ū
  have hD₁S₁ : D₁ ≤ S₁ := Subgroup.map_mono hDS
  have hA : ⁅P₀, D₁⁆ ≤ Ū := by
    have h1 : ⁅P₀, D₁⁆ ≤ P₀ ⊓ S₁ :=
      (Subgroup.commutator_mono le_rfl hD₁S₁).trans (Subgroup.commutator_le_inf P₀ S₁)
    have hSP : S₁ ⊓ P₀ ≤ twoResidual S₁ := RonanE51.inf_le_twoResidual_of_isPGroup hp hp2 hP₀p
    have hres : twoResidual S₁ ≤ Ū := by
      rw [← E1.map_twoResidual π S']
      exact Subgroup.map_mono hSU
    exact h1.trans ((inf_comm P₀ S₁ ▸ hSP).trans hres)
  have hB : ⁅P₀ ⊓ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q)), Ā⁆ ≤ Ū := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨c, rfl⟩ := hπs x
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have e : ⁅π c, π a⁆ = π ⁅c, a⁆ := (map_commutatorElement π c a).symm
    rw [e]
    exact Subgroup.mem_map_of_mem π (hcov c hx.1 hx.2 a ha)
  have hD₁2 : IsPGroup 2 ↥D₁ := hD2.map π
  have hnormP : ∀ g : Γ ⧸ Q, g ∈ Subgroup.normalizer (P₀ : Set (Γ ⧸ Q)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hP₀n]
    exact Subgroup.mem_top g
  have hcop : Nat.Coprime 2 (Nat.card P₀) := by
    obtain ⟨n, hn⟩ := hP₀p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm)
  have hsolv₀ : Group.IsSolvable ↥P₀ := by
    have := hP₀p.isNilpotent
    infer_instance
  have hfac := E1.comm_sup_inf_centralizer_eq (fun g _ => hnormP g) hD₁2 hcop hsolv₀
  have hĀD : ∀ y ∈ Ā, ∀ d ∈ D₁, y * d = d * y := by
    intro y hy d hd
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.1 hd
    rw [← map_mul, ← map_mul, (hDA d' hd' a ha).symm]
  have hĀnorm : ∀ y ∈ Ā, y ∈ Subgroup.normalizer (D₁ : Set (Γ ⧸ Q)) := fun y hy =>
    (Subgroup.centralizer_le_normalizer _)
      (Subgroup.mem_centralizer_iff.2 fun d hd => (hĀD y hy d hd).symm)
  set L : Subgroup (Γ ⧸ Q) :=
    ⁅P₀, D₁⁆ ⊔ ⁅P₀ ⊓ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q)), Ā⁆ with hL
  have hcnorm : P₀ ⊓ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q)) ≤
      Subgroup.normalizer ((⁅P₀, D₁⁆ : Subgroup (Γ ⧸ Q)) : Set (Γ ⧸ Q)) := fun c hc =>
    E1.mem_normalizer_commutator (hnormP c) ((Subgroup.centralizer_le_normalizer _) hc.2)
  have hcomm : ⁅P₀, Ā⁆ ≤ L := by
    refine Subgroup.commutator_le.2 fun z hz a ha => ?_
    have hz' : z ∈ ⁅P₀, D₁⁆ ⊔ (P₀ ⊓ Subgroup.centralizer (D₁ : Set (Γ ⧸ Q))) := by
      rw [hfac]
      exact hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hcnorm] at hz'
    obtain ⟨d, hd, c, hc, rfl⟩ := hz'
    rw [E1.comm_mul_left]
    have hdL : d ∈ L := Subgroup.mem_sup_left hd
    have hca : ⁅c, a⁆ ∈ L :=
      Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hc ha)
    have hanorm := E1.mem_normalizer_commutator (hnormP a) (hĀnorm a ha)
    have hda : ⁅d, a⁆ ∈ ⁅P₀, D₁⁆ := by
      have e : ⁅d, a⁆ = d * (a * d⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hd ((Subgroup.mem_normalizer_iff.1 hanorm d⁻¹).1
        (Subgroup.inv_mem _ hd))
    exact L.mul_mem (L.mul_mem (L.mul_mem hdL hca) (L.inv_mem hdL))
      (Subgroup.mem_sup_left hda)
  calc P₀ = ⁅P₀, Ā⁆ := hPA
    _ ≤ L := hcomm
    _ ≤ Ū := sup_le hA hB

end CFSG.Quasithin.RonanE52
