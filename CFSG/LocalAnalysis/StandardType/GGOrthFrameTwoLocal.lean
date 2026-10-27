module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGOrthTorusMixed
public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs

public section

namespace CFSG.StandardType.OrthTorus

open CFSG.Assembly CFSG.RankThree.Classical2

variable {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}

noncomputable def OrthFrameCore.componentEquiv (Φ : OrthFrameCore p Bs L) :
    ↥(orthDerived Φ.Q) ≃* ↥L :=
  MulEquiv.ofBijective
    (Φ.ψ.codRestrict L fun y => by
      have h : Φ.ψ y ∈ Φ.ψ.range := ⟨y, rfl⟩
      rwa [Φ.hrange] at h)
    ⟨fun x y h => Φ.hinj (congrArg Subtype.val h), by
      intro l
      obtain ⟨y, hy⟩ := (show (l : G) ∈ Φ.ψ.range from by rw [Φ.hrange]; exact l.2)
      exact ⟨y, Subtype.ext hy⟩⟩

variable [Finite G] [Fact p.Prime]

theorem OrthFrameCore.beta_eq_one_iff (Φ : OrthFrameCore p Bs L)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (b : ↥Bs) (hbP : b ^ p = 1) :
    Φ.β b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro hb
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨y, rfl⟩ := (show l ∈ Φ.ψ.range from by rw [Φ.hrange]; exact hl)
    have h := Φ.hcompat b y
    rw [hb, one_mul, inv_one, mul_one] at h
    calc (Φ.ψ y) * (b : G) = ((b : G) * Φ.ψ y * (b : G)⁻¹) * (b : G) := by rw [← h]
      _ = (b : G) * Φ.ψ y := by group
  · intro hb
    have hc : Φ.β b ∈ Subgroup.center ↥(orthDerived Φ.Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hcomm := Subgroup.mem_centralizer_iff.mp hb (Φ.ψ y)
        (by
          have h : Φ.ψ y ∈ Φ.ψ.range := ⟨y, rfl⟩
          rwa [Φ.hrange] at h)
      have h : Φ.β b * y * (Φ.β b)⁻¹ = y := by
        apply Φ.hinj
        rw [Φ.hcompat, ← hcomm]
        group
      calc y * Φ.β b = (Φ.β b * y * (Φ.β b)⁻¹) * Φ.β b := by rw [h]
        _ = Φ.β b * y := by group
    have he : Φ.componentEquiv (Φ.β b) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro l
      obtain ⟨y, rfl⟩ := Φ.componentEquiv.surjective l
      simpa only [map_mul] using congrArg Φ.componentEquiv (hc y)
    let z : ↥(Subgroup.center ↥L) := ⟨Φ.componentEquiv (Φ.β b), he⟩
    have hzP : z ^ p = 1 := by
      apply Subtype.ext
      change Φ.componentEquiv (Φ.β b) ^ p = 1
      rw [← map_pow, ← map_pow, hbP, map_one, map_one]
    have hz : z = 1 := by
      by_contra hn
      have ho : orderOf z = p := orderOf_eq_prime hzP hn
      exact hpZ (ho ▸ orderOf_dvd_natCard z)
    apply Φ.componentEquiv.injective
    exact (congrArg Subtype.val hz).trans (map_one Φ.componentEquiv).symm

theorem OrthFrameCore.card_beta_range_mul
    (Φ : OrthFrameCore p Bs L) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {B E : Subgroup G} {x : G} (hS : LargeEvenSStar p B x L)
    (hEBs : E ≤ Bs) (hE : IsElemAbelian p E) (hxE : x ∈ E) :
    Nat.card (Φ.β.comp (Subgroup.inclusion hEBs)).range * p = Nat.card E := by
  have hp : p.Prime := Fact.out
  let f := Φ.β.comp (Subgroup.inclusion hEBs)
  have hker : f.ker = (E ⊓ Subgroup.centralizer (L : Set G)).subgroupOf E := by
    ext e
    change Φ.β ⟨(e : G), hEBs e.2⟩ = 1 ↔ _
    simpa only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, e.2, true_and] using
      Φ.beta_eq_one_iff hpZ ⟨(e : G), hEBs e.2⟩ (by
        apply Subtype.ext
        exact hE.2 e e.2)
  have hC : E ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
    have hEA := CFSG.Open.IsElemAbelian.mono hE
      (show E ⊓ Subgroup.centralizer (L : Set G) ≤ E from inf_le_left)
    have hcyc := hS.2.2.2.2 _ inf_le_right (CFSG.Open.IsElemAbelian.isPGroup hEA)
    have hxC := mem_centralizer_of_le_centralizer hS.2.2.2.1.1
    have hle : Subgroup.zpowers x ≤ E ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hxE, hxC⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hS.2.2.1]
    exact TableB.card_le_of_isCyclic hp.pos hcyc hEA.2
  have hkerCard : Nat.card f.ker = p := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show E ⊓ Subgroup.centralizer (L : Set G) ≤ E from inf_le_left)).toEquiv,
      hC, Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hS.2.2.1]
  simpa only [hkerCard] using TableB.card_range_mul_card_ker f

theorem OrthFrameCore.beta_range_card (Φ : OrthFrameCore p Bs L) :
    Nat.card Φ.β.range = p ^ Φ.r := by
  have hmap : Φ.β.range.map (orthDerived Φ.Q).subtype = Φ.A := by
    apply le_antisymm
    · rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
      exact Φ.hβA b
    · intro a ha
      obtain ⟨b, hb⟩ := Φ.hβsurj a ha
      exact ⟨Φ.β b, ⟨b, rfl⟩, hb⟩
  have hc : Nat.card (Φ.β.range.map (orthDerived Φ.Q).subtype) = Nat.card Φ.β.range :=
    Subgroup.card_map_of_injective (orthDerived Φ.Q).subtype_injective
  rw [← hc, hmap, ← Φ.Δ.τ_range,
    ← Nat.card_congr (MonoidHom.ofInjective (f := Φ.Δ.τ) Φ.Δ.τ_inj).toEquiv]
  rw [Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem OrthFrameCore.card_beta_B (Φ : OrthFrameCore p Bs L)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {B : Subgroup G} {x : G} {D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hne : B ≠ Bs) :
    Nat.card (Φ.β.comp (Subgroup.inclusion hC.2.1.1)).range = p ^ (Φ.r - 1) := by
  have hp : p.Prime := Fact.out
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hcard : Nat.card Bs = p * Nat.card B :=
    le_antisymm hC.2.1.2.2.1 (mul_card_le_card_of_lt hp hC.2.1.2.1
      (lt_of_le_of_ne hC.2.1.1 hne))
  have hcBs := Φ.card_beta_range_mul hpZ hS le_rfl hC.2.1.2.1
    (hC.2.1.1 hS.2.1)
  have hcB := Φ.card_beta_range_mul hpZ hS hC.2.1.1 hS.1.1 hS.2.1
  have hcBs' : p ^ Φ.r * p = Nat.card Bs := by
    change Nat.card Φ.β.range * p = Nat.card Bs at hcBs
    rwa [Φ.beta_range_card] at hcBs
  have hmul : Nat.card (Φ.β.comp (Subgroup.inclusion hC.2.1.1)).range * p = p ^ Φ.r := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [hcB, hcBs', hcard]
    exact Nat.mul_comm _ _
  have hr := Φ.hr
  have hrpow : p ^ Φ.r = p ^ (Φ.r - 1) * p := by
    conv_lhs => rw [show Φ.r = (Φ.r - 1) + 1 by omega, pow_succ]
  exact Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans hrpow)

theorem OrthFrameCore.exists_slTwo_centralizing_B (Φ : OrthFrameCore p Bs L)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Φ.Q).Nondegenerate) (hq : 4 ≤ Nat.card Φ.F)
    {B : Subgroup G} {x : G} {D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hne : B ≠ Bs)
    {U : Subgroup G} (hUL : U ≤ L) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) Φ.F →* G,
      Function.Injective θ ∧ θ.range ≤ L ∧
        θ.range ≤ Subgroup.centralizer (B : Set G) := by
  haveI := Φ.finite_linearEquiv
  let βB := Φ.β.comp (Subgroup.inclusion hC.2.1.1)
  let H := βB.range
  let S := U.comap Φ.ψ
  have hS1 : S ≠ ⊥ := by
    intro hs
    have hmap : S.map Φ.ψ = U := by
      change (U.comap Φ.ψ).map Φ.ψ = U
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (show U ≤ Φ.ψ.range from by rw [Φ.hrange]; exact hUL)
    rw [hs, Subgroup.map_bot] at hmap
    exact hU1 hmap.symm
  have hS2 : IsPGroup 2 S := hU2.comap_of_injective Φ.ψ Φ.hinj
  have hHS : H ≤ Subgroup.normalizer (S : Set ↥(orthDerived Φ.Q)) := by
    rintro _ ⟨b, rfl⟩
    apply Subgroup.mem_normalizer_iff.mpr
    intro y
    change Φ.ψ y ∈ U ↔ Φ.ψ (Φ.β ⟨(b : G), hC.2.1.1 b.2⟩ * y *
      (Φ.β ⟨(b : G), hC.2.1.1 b.2⟩)⁻¹) ∈ U
    rw [Φ.hcompat]
    exact Subgroup.mem_normalizer_iff.mp (hBU b.2) (Φ.ψ y)
  have hHT : H ≤ (Φ.Δ.τΩ Φ.hA).range := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨f, hf⟩ := (show (Φ.β ⟨(b : G), hC.2.1.1 b.2⟩ : Φ.V ≃ₗ[Φ.F] Φ.V)
      ∈ Φ.Δ.τ.range from by rw [Φ.Δ.τ_range]; exact Φ.hβA _)
    exact ⟨f, Subtype.ext hf⟩
  obtain ⟨θ, hθ, hcomm⟩ := Φ.Δ.exists_slTwo_centralizing_of_twoLocal hp2 Φ.hpq
    Φ.hA hQ Φ.hr hq Φ.hfix hHT (Φ.card_beta_B hpZ hC hne) hS2 hS1 hHS
  refine ⟨Φ.ψ.comp θ, Φ.hinj.comp hθ, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    have h : Φ.ψ (θ g) ∈ Φ.ψ.range := ⟨θ g, rfl⟩
    rwa [Φ.hrange] at h
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hc := hcomm (βB ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ g
    have h : b * Φ.ψ (θ g) * b⁻¹ = Φ.ψ (θ g) := by
      rw [← Φ.hcompat ⟨b, hC.2.1.1 hb⟩ (θ g)]
      change Φ.ψ (βB ⟨b, hb⟩ * θ g * (βB ⟨b, hb⟩)⁻¹) = _
      rw [hc]
      simp
    calc b * Φ.ψ (θ g) = (b * Φ.ψ (θ g) * b⁻¹) * b := by group
      _ = Φ.ψ (θ g) * b := by rw [h]

end CFSG.StandardType.OrthTorus

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGConfig.innLocal_of_twD_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G}
    (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twD ∧ 4 ≤ lab.rank) p Bs L)
    (hne : B ≠ Bs) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  have hMO := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twD ∧ 4 ≤ lab.rank)
    (P' := fun R _ I _ => GGOutdiagOdd p R I)
    (fun lab _ hs => by
      rcases lab with ⟨tag, r, n⟩
      rcases hs with ⟨ht, hr⟩
      dsimp only at ht hr
      subst tag
      intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      split_ifs at hQ ⊢ with h2 h3
      · omega
      · omega
      · obtain ⟨F, _, _, hF, b, c, hbc, hQ⟩ := hQ
        exact ⟨F, inferInstance, inferInstance, hF, b, c, hbc, hQ,
          ggOutdiagOdd_of_prime fun _ hφ _ => hφ⟩)
    (fun _ _ _ _ _ _ h => h.1) hM
  obtain ⟨hL, _, _, hraw⟩ := hMO
  obtain ⟨R, _, I, F, _, _, θ, ⟨_, hN, h3⟩, hOD⟩ := largeEvenRawDatum_exists hraw
  exact hC.innLocal_of_ne hnc hL θ (hC.2.1.1.trans hN)
    (fun b hb => h3 b (hC.2.1.1 hb)) hOD hne

end CFSG.StandardType

end
