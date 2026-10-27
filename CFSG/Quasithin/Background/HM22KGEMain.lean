module

public import CFSG.Quasithin.Background.HM22KGE
public import CFSG.Quasithin.Background.HM22Recog
public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26
public import CFSG.Quasithin.Background.HM22InvConj
public import CFSG.Quasithin.Background.HM22KGEData

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.MatNCert Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_involution_of_conj {K : Type} [Group K] (hZ : Nat.card ↥(Subgroup.center K) = 3)
    {α : MulAut K} (hα2 : α * α = 1) (hα1 : α ≠ 1) {k₁ : K} (hk₁ : α = MulAut.conj k₁) :
    orderOf (k₁ ^ 3) = 2 ∧ α = MulAut.conj (k₁ ^ 3) := by
  have hc2 : k₁ ^ 2 ∈ Subgroup.center K := by
    rw [← ker_conj_eq_center, MonoidHom.mem_ker, map_pow, ← hk₁, pow_two, hα2]
  have h3 : (k₁ ^ 2) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center K)) (x := ⟨k₁ ^ 2, hc2⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hα3 : α = MulAut.conj (k₁ ^ 3) := by
    rw [map_pow, ← hk₁, pow_three, ← mul_assoc, hα2, one_mul]
  refine ⟨orderOf_eq_prime ?_ ?_, hα3⟩
  · rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, h3]
  · intro h
    apply hα1
    rw [hα3, h, map_one]

theorem eq_of_comm_restrict
    {K : Type} [Group K] [Finite K]
    (hK : IsHat K (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {U : Type} [CommGroup U] [Finite U] (hU : Nat.card U = 2 ^ 12) (hU2 : ∀ u : U, u ^ 2 = 1)
    {σ : K →* MulAut U} (hσ : Function.Injective σ) {τ : MulAut U} (hτ2 : τ * τ = 1) {k' : K}
    (hk'2 : k' * k' = 1) (hτ : ∀ x : K, τ * σ x * τ⁻¹ = σ (k' * x * k'⁻¹)) : τ = σ k' := by
  have hq : CFSG.Open.IsQuasisimple K := by
    have := hK.1.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hK.1.2.1⟩
  have hcent := kg82HatM22Twelve_holds K hq hK.2.1 hK.2.2 U hU hU2 σ hσ
  set χ := (σ k')⁻¹ * τ
  have hχ : χ ∈ Subgroup.centralizer (σ.range : Set (MulAut U)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h1 := hτ x
    have h2 : τ * σ x = σ k' * σ x * (σ k')⁻¹ * τ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_right]
    calc σ x * χ = σ x * ((σ k')⁻¹ * τ) := rfl
      _ = (σ k')⁻¹ * (σ k' * σ x * (σ k')⁻¹ * τ) := by group
      _ = (σ k')⁻¹ * (τ * σ x) := by rw [h2]
      _ = χ * σ x := by simp only [χ]; group
  rw [hcent] at hχ
  obtain ⟨ζ, hζ, hζχ⟩ := hχ
  have hτeq : τ = σ (k' * ζ) := by
    rw [map_mul, hζχ]
    simp only [χ]
    group
  have hζc := Subgroup.mem_center_iff.mp hζ
  have hsq : (k' * ζ) * (k' * ζ) = 1 := by
    apply hσ
    rw [map_mul, ← hτeq, hτ2, map_one]
  have hζ2 : ζ * ζ = 1 := by
    calc ζ * ζ = (k' * k') * (ζ * ζ) := by rw [hk'2, one_mul]
      _ = k' * (k' * ζ) * ζ := by group
      _ = k' * (ζ * k') * ζ := by rw [hζc k']
      _ = (k' * ζ) * (k' * ζ) := by group
      _ = 1 := hsq
  have hζ3 : ζ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center K)) (x := ⟨ζ, hζ⟩)
    rw [hK.2.1] at this
    exact congrArg Subtype.val this
  have hζ1 : ζ = 1 := by
    calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by group
      _ = 1 := by rw [hζ3, hζ2, inv_one, mul_one]
  rw [hτeq, hζ1, mul_one]

theorem neg_eq_self_vec (v : Fin 12 → ZMod 2) : -v = v := by
  funext i
  have h : ∀ a : ZMod 2, -a = a := by decide
  exact h (v i)

theorem not_isSolvable_fixSub_comm
    {U : Type} [CommGroup U] {L : Subgroup (MulAut U)} {ψ : ↥H12Cert.G ≃* ↥L}
    {θ : U ≃* Multiplicative (Fin 12 → ZMod 2)}
    (hψθ : ∀ (g : ↥H12Cert.G) (w : U), Multiplicative.toAdd (θ (((ψ g : ↥L) : MulAut U) w)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (Multiplicative.toAdd (θ w)))
    {g' : ↥H12Cert.G} (hg' : orderOf g' = 2) (u : U)
    (hw : u⁻¹ * ((ψ g' : ↥L) : MulAut U) u ≠ 1) :
    ¬ Group.IsSolvable ↥(H12Cert.G ⊓
      fixSub (Multiplicative.toAdd (θ (u⁻¹ * ((ψ g' : ↥L) : MulAut U) u)))) := by
  have hG : IsHat ↥H12Cert.G (CFSG.Blueprint.NativeSporadic.Carrier .M22) := isHat_G
  have hk0 : orderOf (⟨k0, k0_mem⟩ : ↥H12Cert.G) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_k0
  obtain ⟨c, hc⟩ := exists_conj_of_orderOf_two hG hk0 hg'
  set v := Multiplicative.toAdd (θ u)
  set cM := (((c : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
  set ciM := (((c⁻¹ : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
  have hcci : cM * ciM = 1 := by
    simp only [cM, ciM, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hg'M : (((g' : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      cM * ((k0 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * ciM := by
    rw [← hc]
    simp only [cM, ciM, Subgroup.coe_mul, Units.val_mul]
  have hvw : Multiplicative.toAdd (θ (u⁻¹ * ((ψ g' : ↥L) : MulAut U) u)) =
      cM *ᵥ (((k0 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ (ciM *ᵥ v) +
        ciM *ᵥ v) := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hψθ, neg_eq_self_vec, hg'M, mulVec_add,
      mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hcci, one_mulVec, add_comm]
  obtain ⟨x, hx, hxv⟩ := mem_commL (ciM *ᵥ v)
  rw [hxv] at hvw
  have hx0 : x ≠ 0 := by
    intro h
    apply hw
    have h1 : Multiplicative.toAdd (θ (u⁻¹ * ((ψ g' : ↥L) : MulAut U) u)) = 0 := by
      rw [hvw, h, vecN_zero, mulVec_zero]
    rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h1
    exact h1
  have hns := not_isSolvable_fix hx hx0
  rw [hvw]
  have hconj : H12Cert.G ⊓ fixSub (cM *ᵥ vecN 12 x) =
      (H12Cert.G ⊓ fixSub (vecN 12 x)).map
        (MulAut.conj (c : GL (Fin 12) (ZMod 2))).toMonoidHom := by
    rw [fixSub_mulVec, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
    congr 1
    ext g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hg
      exact ⟨(c : GL (Fin 12) (ZMod 2))⁻¹ * g * c,
        H12Cert.G.mul_mem (H12Cert.G.mul_mem (H12Cert.G.inv_mem c.2) hg) c.2, by group⟩
    · rintro ⟨h, hh, rfl⟩
      exact H12Cert.G.mul_mem (H12Cert.G.mul_mem c.2 hh) (H12Cert.G.inv_mem c.2)
  intro hsolv
  rw [hconj] at hsolv
  exact hns (isSolvable_of_mulEquiv' ((H12Cert.G ⊓ fixSub (vecN 12 x)).equivMapOfInjective
    (MulAut.conj (c : GL (Fin 12) (ZMod 2))).toMonoidHom (MulAut.conj _).injective))

theorem factM22Twelve12626_holds :
    FactM22Twelve12626 := by
  intro Y W _ _ _ _ hWc hW2 ρ K hK hρK t ht2 htN htK hcard
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hWc }
  set σ : ↥K →* MulAut W := ρ.comp K.subtype with hσdef
  have hσ : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 : (k : Y) ∈ K ⊓ ρ.ker := ⟨k.2, hk⟩
    rw [hρK, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  let e₁ : ↥K ≃* ↥σ.range := MonoidHom.ofInjective hσ
  have he₁ : ∀ k : ↥K, ((e₁ k : ↥σ.range) : MulAut W) = ρ k := fun _ => rfl
  have hL : IsHat ↥σ.range (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv' e₁ hK
  obtain ⟨f₀⟩ := HM22.nonempty_mulEquiv_hatM22Γ₀ hK
  set f : ↥H12Cert.G ≃* ↥K := hatEquivG'.symm.trans f₀
  set z₁ : ↥K := (f zGU)⁻¹ with hz₁def
  have hz₁c : z₁ ∈ Subgroup.center ↥K :=
    Subgroup.inv_mem _ (mem_center_of_mulEquiv f zGU_mem_center)
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply zGU_ne_one
    apply f.injective
    rw [map_one]
    exact inv_eq_one.mp h
  have hz₁3 : z₁ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center ↥K)) (x := ⟨z₁, hz₁c⟩)
    rw [hK.2.1] at this
    exact congrArg Subtype.val this
  set zL : ↥σ.range := e₁ z₁
  have hzLc : zL ∈ Subgroup.center ↥σ.range := mem_center_of_mulEquiv e₁ hz₁c
  set zW : MulAut W := (zL : MulAut W) with hzWdef
  have hzW : zW = ρ z₁ := rfl
  have hz3 : ∀ w, zW (zW (zW w)) = w := fun w => by
    have h : zW ^ 3 = 1 := by
      rw [hzW, ← map_pow, ← Subgroup.coe_pow, hz₁3, Subgroup.coe_one, map_one]
    have := congrArg (fun φ : MulAut W => φ w) h
    simpa [pow_succ, MulAut.mul_apply] using this
  have hzW1 : zW ≠ 1 := fun h => hz₁1 (hσ (by rw [map_one]; exact h))
  set U := kerSum zW with hUdef
  have hU : U ≠ ⊥ := kerSum_ne_bot hW2 hz3 hzW1
  have htK' : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp htN k).mp hk
  let αh : ↥K →* ↥K :=
    { toFun := fun k => ⟨t * k * t⁻¹, htK' k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαinj : Function.Injective αh := fun a b h => Subtype.ext (by
    have h1 : t * (a : Y) * t⁻¹ = t * b * t⁻¹ := congrArg Subtype.val h
    simpa using h1)
  let α : MulAut ↥K := MulEquiv.ofBijective αh (Finite.injective_iff_bijective.mp hαinj)
  have hα : ∀ k : ↥K, ((α k : ↥K) : Y) = t * k * t⁻¹ := fun _ => rfl
  have hα2 : α * α = 1 := by
    ext k
    simp only [MulAut.mul_apply, hα, MulAut.one_apply]
    rw [show t * (t * (k : Y) * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ by group, ← pow_two, ht2]
    simp
  have hα1 : α ≠ 1 := by
    obtain ⟨k, hk, hkt⟩ := htK
    intro h
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Y)) h
    simp only [hα, MulAut.one_apply] at h1
    apply hkt
    calc t * k = t * k * t⁻¹ * t := by group
      _ = k * t := by rw [h1]
  set tW : MulAut W := ρ t with htWdef
  have hcomm_le : Nat.card ↥(commImg U tW) ≤ 2 ^ 4 := by
    refine le_trans ?_ hcard
    have hsub : ((commImg U tW : Subgroup W) : Set W) ⊆ {x : W | ∃ w, x = w⁻¹ * ρ t w} := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    exact Nat.card_mono (Set.toFinite _) hsub
  by_cases hinner : ∃ k₁ : ↥K, α = MulAut.conj k₁
  swap
  ·
    exfalso
    have hnot : ∀ k : ↥K, α ≠ MulAut.conj k := fun k h => hinner ⟨k, h⟩
    have hq : CFSG.Open.IsQuasisimple ↥K := by
      have := hK.1.1
      exact ⟨Group.IsPerfect.commutator_eq_top, hK.1.2.1⟩
    have hinv := kg82HatM22Out_holds ↥K hq hK.2.1 hK.2.2 α hnot z₁ hz₁c
    have h1 : t * (z₁ : Y) * t⁻¹ = (z₁ : Y)⁻¹ := by
      rw [← hα, hinv, Subgroup.coe_inv]
    have hzz : ∀ w, zW (zW w) = zW⁻¹ w := fun w => by
      apply zW.injective
      rw [MulAut.apply_inv_self, hz3]
    have htz : ∀ w, tW (zW w) = zW (zW (tW w)) := fun w => by
      have h2 : tW * zW = zW⁻¹ * tW := by
        rw [htWdef, hzW, ← map_mul, ← map_inv, ← map_mul, ← h1, inv_mul_cancel_right]
      have h3 := congrArg (fun φ : MulAut W => φ w) h2
      simp only [MulAut.mul_apply] at h3
      rw [h3, hzz]
    have h2 := card_le_comm_sq hW2 hz3 htz
    have h3 : Nat.card ↥U ≤ 2 ^ 8 :=
      h2.trans ((Nat.pow_le_pow_left hcomm_le 2).trans (by norm_num))
    have h4 : 4096 ≤ Nat.card ↥U := card_kerSum_ge hW2 hL hzLc hU (lt_of_le_of_lt h3 (by norm_num))
    omega
  obtain ⟨k₁, hk₁⟩ := hinner
  obtain ⟨hk'o, hαk'⟩ := exists_involution_of_conj hK.2.1 hα2 hα1 hk₁
  set k' : ↥K := k₁ ^ 3 with hk'def
  have hk'2 : k' * k' = 1 := by rw [← pow_two, ← hk'o, pow_orderOf_eq_one]
  have htk : ∀ x : ↥K, t * (x : Y) * t⁻¹ = ((k' * x * k'⁻¹ : ↥K) : Y) := fun x => by
    rw [← hα, hαk', MulAut.conj_apply]
  have hfk0 : orderOf (f ⟨k0, k0_mem⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_k0
  obtain ⟨c, hc⟩ := exists_conj_of_orderOf_two hK hfk0 hk'o
  set yK : ↥K := c * f ⟨y0, y0_mem⟩ * c⁻¹ with hyKdef
  set y'K : ↥K := c * f ⟨y0', y0'_mem⟩ * c⁻¹ with hy'Kdef
  have hk0y : (⟨k0, k0_mem⟩ : ↥H12Cert.G) * ⟨y0, y0_mem⟩ * (⟨k0, k0_mem⟩ : ↥H12Cert.G)⁻¹ =
      (⟨y0, y0_mem⟩ : ↥H12Cert.G)⁻¹ := Subtype.ext k0_conj_y0
  have hy03 : (⟨y0, y0_mem⟩ : ↥H12Cert.G) ^ 3 = 1 := Subtype.ext y0_pow_three
  have hy0' : (⟨y0', y0'_mem⟩ : ↥H12Cert.G) * ⟨y0, y0_mem⟩ * (⟨y0', y0'_mem⟩ : ↥H12Cert.G)⁻¹ =
      ⟨y0, y0_mem⟩ * zGU⁻¹ := Subtype.ext y0'_conj_y0
  have r1 : k' * yK * k'⁻¹ = yK⁻¹ := by
    rw [← hc, hyKdef]
    have := congrArg f hk0y
    rw [map_mul, map_mul, map_inv, map_inv] at this
    calc c * f ⟨k0, k0_mem⟩ * c⁻¹ * (c * f ⟨y0, y0_mem⟩ * c⁻¹) * (c * f ⟨k0, k0_mem⟩ * c⁻¹)⁻¹
        = c * (f ⟨k0, k0_mem⟩ * f ⟨y0, y0_mem⟩ * (f ⟨k0, k0_mem⟩)⁻¹) * c⁻¹ := by group
      _ = c * (f ⟨y0, y0_mem⟩)⁻¹ * c⁻¹ := by rw [this]
      _ = (c * f ⟨y0, y0_mem⟩ * c⁻¹)⁻¹ := by group
  have r2 : yK ^ 3 = 1 := by
    rw [hyKdef]
    have h1 : (c * f ⟨y0, y0_mem⟩ * c⁻¹) ^ 3 = c * f (⟨y0, y0_mem⟩ ^ 3) * c⁻¹ := by
      rw [map_pow]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [h1, hy03, map_one, mul_one, mul_inv_cancel]
  have r3 : y'K * yK = yK * z₁ * y'K := by
    rw [hy'Kdef, hyKdef, hz₁def]
    have := congrArg f hy0'
    rw [map_mul, map_mul, map_inv, map_mul, map_inv] at this
    have hzc := Subgroup.mem_center_iff.mp hz₁c
    have hcz : c * (f zGU)⁻¹ = (f zGU)⁻¹ * c := hzc c
    calc c * f ⟨y0', y0'_mem⟩ * c⁻¹ * (c * f ⟨y0, y0_mem⟩ * c⁻¹)
        = c * (f ⟨y0', y0'_mem⟩ * f ⟨y0, y0_mem⟩ * (f ⟨y0', y0'_mem⟩)⁻¹) * f ⟨y0', y0'_mem⟩ *
            c⁻¹ := by
          group
      _ = c * (f ⟨y0, y0_mem⟩ * (f zGU)⁻¹) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by rw [this]
      _ = c * f ⟨y0, y0_mem⟩ * (c⁻¹ * (c * (f zGU)⁻¹)) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by group
      _ = c * f ⟨y0, y0_mem⟩ * (c⁻¹ * ((f zGU)⁻¹ * c)) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by rw [hcz]
      _ = c * f ⟨y0, y0_mem⟩ * c⁻¹ * (f zGU)⁻¹ * (c * f ⟨y0', y0'_mem⟩ * c⁻¹) := by group
  set y : MulAut W := ρ yK
  set y' : MulAut W := ρ y'K
  have hρK : ∀ a b : ↥K, ρ (a : Y) * ρ (b : Y) = ρ ((a * b : ↥K) : Y) := fun a b => by
    rw [← map_mul, Subgroup.coe_mul]
  have hy3 : ∀ w, y (y (y w)) = w := fun w => by
    have h : y ^ 3 = 1 := by
      simp only [y]
      rw [← map_pow, ← Subgroup.coe_pow, r2, Subgroup.coe_one, map_one]
    have := congrArg (fun φ : MulAut W => φ w) h
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcomm_z : ∀ a : ↥K, ∀ w, ρ (a : Y) (zW w) = zW (ρ (a : Y) w) := fun a w => by
    have h1 : a * z₁ = z₁ * a := Subgroup.mem_center_iff.mp hz₁c a
    have h2 := congrArg (fun x : ↥K => ρ (x : Y) w) h1
    simpa only [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hzW] using h2
  have hyz : ∀ w, y (zW w) = zW (y w) := hcomm_z yK
  have hy'z : ∀ w, y' (zW w) = zW (y' w) := hcomm_z y'K
  have hy' : ∀ w, y' (y w) = y (zW (y' w)) := fun w => by
    have h2 := congrArg (fun x : ↥K => ρ (x : Y) w) r3
    simpa only [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hzW] using h2
  have ht2' : ∀ w, tW (tW w) = w := fun w => by
    have h := congrArg (fun φ : MulAut W => φ w) (show tW * tW = 1 by
      rw [htWdef, ← map_mul, ← pow_two, ht2, map_one])
    simpa [MulAut.mul_apply] using h
  have hty : ∀ w, tW (y w) = y (y (tW w)) := fun w => by
    have h1 : t * (yK : Y) = (yK : Y) * yK * t := by
      have h2 := htk yK
      rw [r1, Subgroup.coe_inv] at h2
      have hy2 : (yK : Y)⁻¹ = (yK : Y) * yK := by
        rw [inv_eq_iff_mul_eq_one, ← pow_three, ← Subgroup.coe_pow, r2, Subgroup.coe_one]
      calc t * (yK : Y) = t * yK * t⁻¹ * t := by group
        _ = (yK : Y) * yK * t := by rw [h2, hy2]
    have h2 := congrArg (fun x : Y => ρ x w) h1
    simpa only [map_mul, MulAut.mul_apply] using h2
  have hcnt := card_sq_le_comm_pow_six hW2 hz3 hy3 hyz hy'z hy' ht2' hty
  have hUle : Nat.card ↥U ≤ 2 ^ 12 := by
    have h1 : Nat.card ↥U ^ 2 ≤ (2 ^ 12) ^ 2 :=
      hcnt.trans ((Nat.pow_le_pow_left hcomm_le 6).trans (by norm_num))
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hUge : 4096 ≤ Nat.card ↥U :=
    card_kerSum_ge hW2 hL hzLc hU (lt_of_le_of_lt hUle (by norm_num))
  have hU12 : Nat.card ↥U = 4096 := by omega
  have hcomm_ge : 2 ^ 4 ≤ Nat.card ↥(commImg U tW) := by
    have h1 : (2 ^ 4) ^ 6 ≤ Nat.card ↥(commImg U tW) ^ 6 := by
      rw [hU12] at hcnt
      exact le_trans (by norm_num) hcnt
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hSeq : ∀ x ∈ ({x : W | ∃ w, x = w⁻¹ * ρ t w} : Set W), x ∈ commImg U tW := by
    have hsub : ((commImg U tW : Subgroup W) : Set W) ⊆ {x : W | ∃ w, x = w⁻¹ * ρ t w} := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcard.trans hcomm_ge) (Set.toFinite _)
    intro x hx
    rw [← heq] at hx
    exact hx
  refine ⟨?_, ?_⟩
  ·
    have hsolv := isSolvable_centralizer hK hk'o
    let φ : ↥(K ⊓ Subgroup.centralizer ({t} : Set Y)) →*
        ↥(Subgroup.centralizer ({k'} : Set ↥K)) :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxt := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
          have h1 := htk ⟨x, x.2.1⟩
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          have h2 : t * (x : Y) * t⁻¹ = x := by rw [← hxt, mul_inv_cancel_right]
          rw [h2] at h1
          have h3 : ((k' * ⟨x, x.2.1⟩ * k'⁻¹ : ↥K) : Y) = (k' : Y) * x * (k' : Y)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [h3] at h1
          calc (x : Y) * k' = (k' : Y) * x * (k' : Y)⁻¹ * k' := by rw [← h1]
            _ = k' * x := by group⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := fun a b h => Subtype.ext (by
      have := congrArg (fun z : ↥(Subgroup.centralizer ({k'} : Set ↥K)) => ((z : ↥K) : Y)) h
      exact this)
    exact Group.isSolvable_of_isSolvable_injective hφ
  ·
    intro w hw hw1
    obtain ⟨u, hu, rfl⟩ := hSeq w hw
    have hLU := le_stabSub_kerSum hzLc
    have hfaith := faithful_kerSum hW2 hL hzLc hU
    set eU := autSubEquivOfFaithful hLU hfaith
    have hLU' : IsHat ↥(autSub σ.range U) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      isHat_of_mulEquiv' eU hL
    have hV : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v)
    obtain ⟨ψ, θ, hψθ⟩ := exists_model_of_isHat hV hU12 hLU'
    let σU : ↥K →* MulAut ↥U := (autSub σ.range U).subtype.comp (eU.toMonoidHom.comp e₁.toMonoidHom)
    have hσU : ∀ (k : ↥K) (v : ↥U), ((σU k v : ↥U) : W) = ρ k v := fun k v =>
      H12Pf.autSubEquivOfFaithful_apply_val hLU hfaith (e₁ k) v
    have hσUinj : Function.Injective σU := fun a b h => e₁.injective (eU.injective
      (Subtype.ext h))
    have htz : ∀ w, tW (zW w) = zW (tW w) := fun w => by
      have h1 := htk z₁
      have h2 : ((k' * z₁ * k'⁻¹ : ↥K) : Y) = z₁ := by
        have h5 : k' * z₁ * k'⁻¹ = z₁ := by
          rw [Subgroup.mem_center_iff.mp hz₁c k', mul_inv_cancel_right]
        rw [h5]
      rw [h2] at h1
      have h3 : tW * zW = zW * tW := by
        rw [htWdef, hzW, ← map_mul, ← map_mul]
        congr 1
        calc t * (z₁ : Y) = t * z₁ * t⁻¹ * t := by group
          _ = z₁ * t := by rw [h1]
      have h4 := congrArg (fun φ : MulAut W => φ w) h3
      simpa only [MulAut.mul_apply] using h4
    have htU : tW ∈ stabSub U := mem_stabSub_kerSum htz
    set τ : MulAut ↥U := resHom U ⟨tW, htU⟩
    have hτ : ∀ v : ↥U, ((τ v : ↥U) : W) = tW v := fun v => rfl
    have hτ2 : τ * τ = 1 := by
      ext v
      simp only [MulAut.mul_apply, MulAut.one_apply]
      rw [hτ, hτ, ht2']
    have hτinv : ∀ v : ↥U, ((τ⁻¹ v : ↥U) : W) = tW⁻¹ v := fun v => by
      apply tW.injective
      rw [MulAut.apply_inv_self, ← hτ, MulAut.apply_inv_self]
    have hτconj : ∀ x : ↥K, τ * σU x * τ⁻¹ = σU (k' * x * k'⁻¹) := by
      intro x
      ext v
      simp only [MulAut.mul_apply]
      rw [hτ, hσU, hτinv, hσU, ← htk x, map_mul, map_mul, map_inv]
      rfl
    have hτeq := eq_of_comm_restrict hK (by rw [hU12]; norm_num) hV hσUinj hτ2 hk'2 hτconj
    set g' : ↥H12Cert.G := ψ.symm (eU (e₁ k'))
    have hg'o : orderOf g' = 2 := by
      rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
      exact hk'o
    have hψg' : ((ψ g' : ↥(autSub σ.range U)) : MulAut ↥U) = σU k' := by
      simp only [g', MulEquiv.apply_symm_apply]
      rfl
    set uU : ↥U := ⟨u, hu⟩
    have hwU : ((uU⁻¹ * ((ψ g' : ↥(autSub σ.range U)) : MulAut ↥U) uU : ↥U) : W) =
        commHom tW u := by
      rw [hψg', ← hτeq]
      rfl
    have hw1' : uU⁻¹ * ((ψ g' : ↥(autSub σ.range U)) : MulAut ↥U) uU ≠ 1 := fun h => hw1 (by
      rw [← hwU, h]
      rfl)
    have hns := not_isSolvable_fixSub_comm hψθ hg'o uU hw1'
    set wU : ↥U := uU⁻¹ * ((ψ g' : ↥(autSub σ.range U)) : MulAut ↥U) uU
    intro hsolv
    apply hns
    let Φ₀ : ↥(H12Cert.G ⊓ fixSub (Multiplicative.toAdd (θ wU))) →* Y :=
      K.subtype.comp (e₁.symm.toMonoidHom.comp (eU.symm.toMonoidHom.comp (ψ.toMonoidHom.comp
        (Subgroup.inclusion inf_le_left))))
    have hΦ₀ : ∀ g, Φ₀ g ∈ K ⊓ (MulAction.stabilizer (MulAut W) (commHom tW u)).comap ρ := by
      intro g
      set k := e₁.symm (eU.symm (ψ (Subgroup.inclusion inf_le_left g)))
      have hk : σU k = (ψ (Subgroup.inclusion inf_le_left g) : MulAut ↥U) := by
        simp only [σU, k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
          Subgroup.coe_subtype]
      have hfix : ((ψ (Subgroup.inclusion inf_le_left g) : MulAut ↥U)) wU = wU := by
        apply θ.injective
        apply Multiplicative.toAdd.injective
        rw [hψθ]
        exact g.2.2
      have h1 := hσU k wU
      rw [hk, hfix] at h1
      refine Subgroup.mem_inf.mpr ⟨k.2, Subgroup.mem_comap.mpr
        (MulAction.mem_stabilizer_iff.mpr ?_)⟩
      rw [MulAut.smul_def, ← hwU]
      exact h1.symm
    let Φ := Φ₀.codRestrict _ hΦ₀
    have hΦ₀inj : Function.Injective Φ₀ := by
      intro a b h
      simp only [Φ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] at h
      exact Subgroup.inclusion_injective _
        (ψ.injective (eU.symm.injective (e₁.symm.injective (Subtype.ext h))))
    have hΦ : Function.Injective Φ := fun a b h =>
      hΦ₀inj (congrArg (fun x : ↥(K ⊓ (MulAction.stabilizer (MulAut W) (commHom tW u)).comap ρ) =>
        (x : Y)) h)
    exact Group.isSolvable_of_isSolvable_injective hΦ

end CFSG.Quasithin.H.Mathieu.M22Link
