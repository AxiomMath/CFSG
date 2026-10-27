module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSix

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

theorem false_of_nonsolvJ {L₂ : Subgroup H} [L₂.Normal] (hCJ : Input15338NonsolvJ)
    (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hJ : IsSporadic .J2 (↥L₂ ⧸ Subgroup.center ↥L₂) ∨ IsPSL 3 7 1 (↥L₂ ⧸ Subgroup.center ↥L₂))
    {u₀ : H} (hu₀ : u₀ * u₀ = 1)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({u₀} : Set H))) : False := by
  let ψ : H →* MulAut ↥L₂ := MulAut.conjNormal
  have hψ : ∀ (g : H) (n : ↥L₂), ((ψ g n : ↥L₂) : H) = g * n * g⁻¹ := fun g n =>
    MulAut.conjNormal_apply g n
  refine hCJ ↥L₂ hq₂ hJ (ψ u₀) (by rw [← map_mul, hu₀, map_one]) ?_
  have hmem : ∀ x : ↥(SBd18.fixedSub (ψ u₀)),
      (((x : ↥L₂) : H)) ∈ Subgroup.centralizer ({u₀} : Set H) := by
    intro x
    have hx : ψ u₀ (x : ↥L₂) = x := (SBd18.mem_fixedSub).mp x.2
    have h1 := congrArg Subtype.val hx
    rw [hψ] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((x : ↥L₂) : H) * u₀ = (u₀ * ((x : ↥L₂) : H) * u₀⁻¹) * u₀ := by rw [h1]
      _ = u₀ * ((x : ↥L₂) : H) := by group
  let f : ↥(SBd18.fixedSub (ψ u₀)) →* ↥(Subgroup.centralizer ({u₀} : Set H)) :=
    { toFun := fun x => ⟨((x : ↥L₂) : H), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥(Subgroup.centralizer ({u₀} : Set H)) =>
      (z : H)) h))
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem false_of_final34 {L₂ : Subgroup H} [L₂.Normal]
    (hsqtk : SQTKGroup H) (hCL : Input15338FinalL34)
    (hZ : Input15338CenterRank) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hrk₂ : CFSG.Open.pRank 3 L₂ = 2)
    (h34 : IsPSL 3 2 2 (↥L₂ ⧸ Subgroup.center ↥L₂))
    {U : Subgroup H} (hU4 : Nat.card U = 4) (hUel : CFSG.Assembly.IsElemAbelian 2 U)
    (hsolv : ∀ u ∈ U, u ≠ 1 → Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set H)))
    {y : H} (hyN : y ∈ Subgroup.normalizer (U : Set H)) (hy3 : y ^ 3 = 1)
    (hyU : ∃ u ∈ U, y * u * y⁻¹ ≠ u)
    {F : Subgroup H} (hFel : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hFU : ∀ a ∈ F, ∀ w ∈ U, a * w = w * a)
    (hFnorm : ∀ u ∈ U, u ≠ 1 → ∀ g : H, g * u = u * g →
      g ∈ Subgroup.normalizer (F : Set H)) : False := by
  classical
  let ψ : H →* MulAut ↥L₂ := MulAut.conjNormal
  have hψ : ∀ (g : H) (n : ↥L₂), ((ψ g n : ↥L₂) : H) = g * n * g⁻¹ := fun g n =>
    MulAut.conjNormal_apply g n
  have hnt : Nontrivial ↥L₂ := isQuasisimple_nontrivial hq₂
  have hψU : ∀ u ∈ U, u ≠ 1 → ψ u ≠ 1 := by
    intro u hu hu1 hψ1
    have hc : L₂ ≤ Subgroup.centralizer ({u} : Set H) := by
      intro l hl
      have h1 := congrArg (fun e : MulAut ↥L₂ => ((e ⟨l, hl⟩ : ↥L₂) : H)) hψ1
      simp only [hψ, MulAut.one_apply] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * u = (u * l * u⁻¹) * u := by rw [h1]
        _ = u * l := by group
    have := hsolv u hu hu1
    have hsolv₂ : Group.IsSolvable ↥L₂ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hc)
    have : Group.IsPerfect ↥L₂ := hq₂.1
    exact Group.IsPerfect.not_isSolvable ↥L₂ hsolv₂
  have hinjU : ∀ a ∈ U, ∀ b ∈ U, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    by_contra hne
    have hne' : a * b⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
    apply hψU (a * b⁻¹) (U.mul_mem ha (U.inv_mem hb)) hne'
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  set U' : Subgroup (MulAut ↥L₂) := U.map ψ with hU'
  have hU'4 : Nat.card U' = 4 := by
    let ψU : ↥U →* MulAut ↥L₂ := ψ.comp U.subtype
    have hinj : Function.Injective ψU := fun a b hab =>
      Subtype.ext (hinjU a a.2 b b.2 hab)
    have hrange : ψU.range = U' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hU4]
  have hU'el : CFSG.Assembly.IsElemAbelian 2 U' := CFSG.SectionRank.isElemAbelian_map hUel ψ
  obtain ⟨u₁, hu₁, hmove⟩ := hyU
  have hy'N : ψ y ∈ Subgroup.normalizer (U' : Set (MulAut ↥L₂)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN u).mp hu, by simp⟩
    · intro hw
      obtain ⟨u, hu, hu'⟩ := hw
      have hyinv : y⁻¹ ∈ Subgroup.normalizer (U : Set H) := Subgroup.inv_mem _ hyN
      refine ⟨y⁻¹ * u * y, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hyinv u).mp hu
        simpa using this
      · have : w = (ψ y)⁻¹ * ψ u * ψ y := by
          rw [show ψ u = ψ y * w * (ψ y)⁻¹ from hu']; group
        rw [this]; simp
  have hy'3 : orderOf (ψ y) = 3 := by
    have h3 : ψ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    refine orderOf_eq_prime h3 (fun h1 => hmove ?_)
    apply hinjU _ ((Subgroup.mem_normalizer_iff.mp hyN u₁).mp hu₁) _ hu₁
    rw [map_mul, map_mul, h1, map_inv, h1]; simp
  have hy'move : ψ y * ψ u₁ * (ψ y)⁻¹ ≠ ψ u₁ := by
    intro h
    apply hmove
    apply hinjU _ ((Subgroup.mem_normalizer_iff.mp hyN u₁).mp hu₁) _ hu₁
    rw [map_mul, map_mul, map_inv]; exact h
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at hU4
    omega
  have hψF : ∀ a ∈ F, ψ a = 1 := by
    intro a ha
    by_contra ha1
    have h3 : ψ a ^ 3 = 1 := by rw [← map_pow, hFel.2 a ha, map_one]
    have hord : orderOf (ψ a) = 3 := orderOf_eq_prime h3 ha1
    let M : Subgroup ↥L₂ := F.subgroupOf L₂
    have hfixc : ∀ g : ↥(SBd18.fixedSub (ψ u₀)), ((g : ↥L₂) : H) * u₀ = u₀ * ((g : ↥L₂) : H) := by
      intro g
      have hgfix : ψ u₀ (g : ↥L₂) = g := (SBd18.mem_fixedSub).mp g.2
      have h1 := congrArg Subtype.val hgfix
      rw [hψ] at h1
      calc ((g : ↥L₂) : H) * u₀ = (u₀ * ((g : ↥L₂) : H) * u₀⁻¹) * u₀ := by rw [h1]
        _ = u₀ * ((g : ↥L₂) : H) := by group
    have hMfix : M ≤ SBd18.fixedSub (ψ u₀) := by
      intro l hl
      rw [SBd18.mem_fixedSub]
      apply Subtype.ext
      rw [hψ]
      have hlF : ((l : ↥L₂) : H) ∈ F := hl
      have h1 := hFU _ hlF u₀ hu₀
      calc u₀ * (l : H) * u₀⁻¹ = (l : H) * u₀ * u₀⁻¹ := by rw [h1]
        _ = l := by group
    have hM3 : IsPGroup 3 ↥M := fun x => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hFel.2 ((x : ↥L₂) : H) x.2⟩
    have hMnorm : (M.subgroupOf (SBd18.fixedSub (ψ u₀))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hnF : (((n : ↥(SBd18.fixedSub (ψ u₀))) : ↥L₂) : H) ∈ F := hn
      have hgN := hFnorm u₀ hu₀ hu₀1 _ (hfixc g)
      change ((((g * n * g⁻¹ : ↥(SBd18.fixedSub (ψ u₀))) : ↥L₂)) : H) ∈ F
      exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hnF
    have hcomm : ∀ w ∈ U', ψ a * w = w * ψ a := by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, hFU a ha w hw]
    have hcl : ∀ d ∈ SBd18.fixedSub (ψ u₀), ψ a d * d⁻¹ ∈ M := by
      intro d hd
      have hdN := hFnorm u₀ hu₀ hu₀1 _ (hfixc ⟨d, hd⟩)
      change (((ψ a d * d⁻¹ : ↥L₂)) : H) ∈ F
      have e : (((ψ a d * d⁻¹ : ↥L₂)) : H) = a * ((d : H) * a⁻¹ * (d : H)⁻¹) := by
        rw [Subgroup.coe_mul, hψ, Subgroup.coe_inv]; group
      rw [e]
      exact F.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hdN _).mp (F.inv_mem ha))
    exact hCL ↥L₂ hq₂ h34 U' hU'4 hU'el ⟨ψ y, hy'N, hy'3, ψ u₁, ⟨u₁, hu₁, rfl⟩, hy'move⟩
      (ψ u₀) ⟨u₀, hu₀, rfl⟩ (hψU u₀ hu₀ hu₀1) M hMfix hM3 hMnorm (ψ a) hord hcomm hcl
  have hcent : ∀ a ∈ F, ∀ l ∈ L₂, a * l = l * a := by
    intro a ha l hl
    have h1 := congrArg (fun e : MulAut ↥L₂ => ((e ⟨l, hl⟩ : ↥L₂) : H)) (hψF a ha)
    simp only [hψ, MulAut.one_apply] at h1
    calc a * l = (a * l * a⁻¹) * a := by group
      _ = l * a := by rw [h1]
  have hFL₂ : F ≤ L₂ := fun a ha => by
    by_cases ha1 : a = 1
    · rw [ha1]; exact L₂.one_mem
    · have hord : orderOf a = 3 := orderOf_eq_prime (hFel.2 a ha) ha1
      exact eq_of_orderThree_centralizes hsqtk.1 hrk₂ hord (fun l hl => hcent a ha l hl)
  have hFc : F ≤ Subgroup.centralizer (L₂ : Set H) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcent a ha l hl).symm
  have := card_le_three_of_le_center hZ hq₂ (sqtkGroup_subgroup hsqtk L₂) hFL₂ hFc hFel
  omega

end CFSG.Quasithin.SBd19F
