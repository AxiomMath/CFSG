module

public import CFSG.Quasithin.AppendixH.H12.Setting
public import CFSG.Quasithin.Background.HM22KGEMain

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH
open CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.M22Link
open CFSG.Quasithin.H.Mathieu.H12Pf

private lemma mem_kerSum_conj {W : Type*} [CommGroup W] (φ z : MulAut W) (w : W) :
    w ∈ kerSum z ↔ φ w ∈ kerSum (φ * z * φ⁻¹) := by
  have h1 : ∀ v : W, (φ * z * φ⁻¹) (φ v) = φ (z v) := by
    intro v
    show φ (z (φ⁻¹ (φ v))) = φ (z v)
    rw [show φ⁻¹ (φ v) = v from MulAut.apply_inv_self W φ⁻¹ v]
  rw [mem_kerSum, mem_kerSum, h1 w, h1 (z w)]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h, map_one]
  · intro h
    exact φ.injective (by rw [map_mul, map_mul, h, map_one])

private lemma kerSum_mul_self {W : Type*} [CommGroup W] (z : MulAut W)
    (hz : ∀ w, z (z (z w)) = w) : kerSum (z * z) = kerSum z := by
  ext w
  rw [mem_kerSum, mem_kerSum]
  simp only [MulAut.mul_apply]
  rw [hz (z w)]
  have heq : w * z (z w) * z w = w * z w * z (z w) := by ac_rfl
  rw [heq]

theorem faithIrr12_of_small_comm
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    {U : Type} [CommGroup U] (σ : G →* MulAut U) (hU2 : ∀ u : U, u ^ 2 = 1)
    (hinj : Function.Injective σ) (hirr : IsIrredOn σ.range ⊤)
    (ht : ∃ t : G, orderOf t = 2 ∧ rk ↥(commV (Subgroup.zpowers (σ t))) ≤ 4) :
    IsFaithIrr12 (σ.comp L.subtype) := by
  haveI : Finite U := by
    obtain ⟨⟨u₀, _⟩, hu₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hirr.1
    have hu₀1 : u₀ ≠ 1 := fun h => hu₀ne (Subtype.ext h)
    let S : Set U := Set.range fun g : G => σ g u₀
    let N : Subgroup U := Subgroup.closure S
    have hNfg : N.FG := (Subgroup.fg_iff N).mpr ⟨S, rfl, Set.toFinite S⟩
    haveI : Group.FG ↥N := (Group.fg_iff_subgroup_fg N).mpr hNfg
    have htors : IsMulTorsion ↥N := fun y => isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by norm_num, Subtype.ext (by simpa using hU2 (y : U))⟩
    haveI : Finite ↥N := CommGroup.finite_of_fg_isMulTorsion ↥N htors
    have hNne : N ≠ ⊥ := by
      intro h
      have hu₀N : u₀ ∈ N := by
        simpa using Subgroup.subset_closure (show σ (1 : G) u₀ ∈ S from ⟨1, rfl⟩)
      rw [h] at hu₀N
      exact hu₀1 (Subgroup.mem_bot.mp hu₀N)
    have hinvN : ∀ l ∈ σ.range, ∀ u ∈ N, l u ∈ N := by
      rintro l ⟨g, rfl⟩ u hu
      have hmap : N.map (σ g).toMonoidHom ≤ N := by
        rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
        rintro _ ⟨h, rfl⟩
        exact Subgroup.subset_closure (show σ g (σ h u₀) ∈ S from
          ⟨g * h, by simp only [map_mul, MulAut.mul_apply]⟩)
      exact hmap (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    have htop : N = ⊤ := (hirr.2 N le_top hinvN).resolve_left hNne
    exact Finite.of_injective (fun u : U => (⟨u, by rw [htop]; exact Subgroup.mem_top u⟩ : ↥N))
      (fun a b h => Subtype.ext_iff.mp h)
  obtain ⟨f₀⟩ := HM22.nonempty_mulEquiv_hatM22Γ₀ hL
  set f : ↥H12Cert.G ≃* ↥L := hatEquivG'.symm.trans f₀ with hfdef
  set z₁ : ↥L := (f zGU)⁻¹ with hz₁def
  have hz₁c : z₁ ∈ Subgroup.center ↥L :=
    Subgroup.inv_mem _ (mem_center_of_mulEquiv f zGU_mem_center)
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply zGU_ne_one
    apply f.injective
    rw [map_one]
    exact inv_eq_one.mp h
  have hz₁3 : z₁ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨z₁, hz₁c⟩)
    rw [hL.2.1] at this
    exact congrArg Subtype.val this
  let σK : ↥L →* MulAut U := σ.comp L.subtype
  have hσK : Function.Injective σK := fun a b h => Subtype.ext (hinj h)
  let e₁ : ↥L ≃* ↥σK.range := MonoidHom.ofInjective hσK
  have he₁ : ∀ k : ↥L, ((e₁ k : ↥σK.range) : MulAut U) = σ (k : G) := fun _ => rfl
  have hL' : IsHat ↥σK.range (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv' e₁ hL
  have hrange : σK.range = L.map σ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  set zL : ↥σK.range := e₁ z₁ with hzLdef
  have hzLc : zL ∈ Subgroup.center ↥σK.range := mem_center_of_mulEquiv e₁ hz₁c
  set zW : MulAut U := (zL : MulAut U) with hzWdef
  have hzW : zW = σ (z₁ : G) := rfl
  have hzW3 : zW ^ 3 = 1 := by
    have h : zL ^ 3 = 1 := by rw [← map_pow, hz₁3, map_one]
    have hval := congrArg Subtype.val h
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at hval
  have hzL1 : zL ≠ 1 := by
    intro h
    exact hz₁1 (e₁.injective (by rw [map_one]; exact h))
  have hzW1 : zW ≠ 1 := by
    intro h
    apply hzL1
    apply Subtype.ext
    rw [← hzWdef]
    exact h
  have hz3 : ∀ w, zW (zW (zW w)) = w := fun w => by
    have h := congrArg (fun φ : MulAut U => φ w) hzW3
    simpa [pow_succ, MulAut.mul_apply] using h
  set U₀ : Subgroup U := kerSum zW with hU₀def
  have hU₀ : U₀ ≠ ⊥ := kerSum_ne_bot hU2 hz3 hzW1
  have hU₀inv : ∀ l ∈ σ.range, ∀ u ∈ U₀, l u ∈ U₀ := by
    rintro l ⟨g, rfl⟩ u hu
    have hnorm : σ g ∈ Subgroup.normalizer ((σK.range : Subgroup (MulAut U)) :
        Set (MulAut U)) := by
      rw [hrange]
      exact range_le_normalizer hF (Set.mem_range_self g)
    let φ : MulAut ↥σK.range := σK.range.normalizerMonoidHom ⟨σ g, hnorm⟩
    have hφval : ∀ x : ↥σK.range,
        ((φ x : ↥σK.range) : MulAut U) = σ g * (x : MulAut U) * (σ g)⁻¹ :=
      fun x => Subgroup.normalizerMonoidHom_apply_apply_coe σK.range ⟨σ g, hnorm⟩ x
    let z' : ↥σK.range := φ zL
    have hz'c : z' ∈ Subgroup.center ↥σK.range := mem_center_of_mulEquiv φ hzLc
    have hzL1' : zL ≠ 1 := fun h => hzW1 (congrArg Subtype.val h)
    have hz'1 : z' ≠ 1 := by
      intro h
      apply hzL1'
      apply φ.injective
      rw [show φ zL = 1 from h, map_one]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_center hL'.2.1 hz'c hzLc hzL1')
    have hkval : zW ^ k = σ g * zW * (σ g)⁻¹ := by
      calc zW ^ k = (z' : MulAut U) := by
            rw [← Subgroup.coe_zpow]
            exact congrArg Subtype.val hk
        _ = σ g * zW * (σ g)⁻¹ := hφval zL
    have hmod := zpow_eq_zpow_emod' (x := zW) k hzW3
    have hcases : σ g * zW * (σ g)⁻¹ = zW ∨ σ g * zW * (σ g)⁻¹ = zW * zW := by
      have hnonneg : 0 ≤ k % (↑(3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
      have hlt : k % (↑(3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hkmod : k % (↑(3 : ℕ) : ℤ) = 0 ∨ k % (↑(3 : ℕ) : ℤ) = 1 ∨
          k % (↑(3 : ℕ) : ℤ) = 2 := by omega
      rcases hkmod with h0 | h1 | h2
      · exfalso
        apply hz'1
        apply Subtype.ext
        show σ g * zW * (σ g)⁻¹ = 1
        rw [← hkval, hmod, h0, zpow_zero]
      · left
        rw [← hkval, hmod, h1, zpow_one]
      · right
        rw [← hkval, hmod, h2]
        norm_num [zpow_natCast, pow_two]
    have hmem : σ g u ∈ kerSum ((σ g) * zW * (σ g)⁻¹) :=
      (mem_kerSum_conj (σ g) zW u).mp hu
    rcases hcases with h | h
    · rwa [h] at hmem
    · rw [h, kerSum_mul_self zW hz3] at hmem
      exact hmem
  have hker_top : U₀ = ⊤ := (hirr.2 U₀ le_top hU₀inv).resolve_left hU₀
  have hzf : ∀ u : U, zW u = u → u = 1 := fun u hu =>
    fix_kerSum hU2 (hU₀def ▸ (hker_top ▸ Subgroup.mem_top u)) hu
  obtain ⟨t, hto, htrk⟩ := ht
  have ht2 : t ^ 2 = 1 := by rw [← hto, pow_orderOf_eq_one]
  have hLnorm : L.Normal := normal_of_fitting hF
  have htN : t ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLnorm]
    exact Subgroup.mem_top t
  have hnotcenter : ∃ k ∈ L, t * k ≠ k * t := by
    by_contra hall
    push Not at hall
    have htcent : t ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hall k hk).symm
    have htL : t ∈ L := centralizer_le_of_fitting hF htcent
    have htcen : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hall (y : G) y.2).symm
    have hdvd : orderOf t ∣ 3 := by
      have hmem : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := htcen
      have h := orderOf_dvd_natCard (⟨⟨t, htL⟩, hmem⟩ : ↥(Subgroup.center ↥L))
      rw [← Subgroup.orderOf_coe (⟨⟨t, htL⟩, hmem⟩ : ↥(Subgroup.center ↥L)),
        ← Subgroup.orderOf_coe (⟨t, htL⟩ : ↥L), hL.2.1] at h
      exact h
    rw [hto] at hdvd
    norm_num at hdvd
  have htK' : ∀ k ∈ L, t * k * t⁻¹ ∈ L := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp htN k).mp hk
  let αh : ↥L →* ↥L :=
    { toFun := fun k => ⟨t * k * t⁻¹, htK' k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαinj : Function.Injective αh := fun a b h => Subtype.ext (by
    have h1 : t * (a : G) * t⁻¹ = t * b * t⁻¹ := congrArg Subtype.val h
    simpa using h1)
  let α : MulAut ↥L := MulEquiv.ofBijective αh (Finite.injective_iff_bijective.mp hαinj)
  have hα : ∀ k : ↥L, ((α k : ↥L) : G) = t * k * t⁻¹ := fun _ => rfl
  have hα2 : α * α = 1 := by
    ext k
    simp only [MulAut.mul_apply, hα, MulAut.one_apply]
    rw [show t * (t * (k : G) * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ by group, ← pow_two, ht2]
    simp
  have hα1 : α ≠ 1 := by
    obtain ⟨k, hk, hkt⟩ := hnotcenter
    intro h
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨k, hk⟩ : ↥L) : G)) h
    simp only [hα, MulAut.one_apply] at h1
    apply hkt
    calc t * k = t * k * t⁻¹ * t := by group
      _ = k * t := by rw [h1]
  set tW : MulAut U := σ t with htWdef
  have hcommV_card : Nat.card ↥(commV (Subgroup.zpowers (σ t))) ≤ 2 ^ 4 := by
    rw [card_eq_two_pow hU2 (commV (Subgroup.zpowers (σ t)))]
    exact Nat.pow_le_pow_right (by norm_num) htrk
  have hcomm_le : Nat.card ↥(commImg U₀ tW) ≤ 2 ^ 4 := by
    refine le_trans (Subgroup.card_le_of_le ?_) hcommV_card
    intro x hx
    rw [commImg, Subgroup.mem_map] at hx
    obtain ⟨u, -, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨tW, Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one tW⟩, u, ?_⟩
    exact mul_comm _ _
  have hU12 : Nat.card U = 2 ^ 12 := by
    by_cases hinner : ∃ k₁ : ↥L, α = MulAut.conj k₁
    ·
      obtain ⟨k₁, hk₁⟩ := hinner
      obtain ⟨hk'o, hαk'⟩ := exists_involution_of_conj hL.2.1 hα2 hα1 hk₁
      set k' : ↥L := k₁ ^ 3 with hk'def
      have hk'2 : k' * k' = 1 := by rw [← pow_two, ← hk'o, pow_orderOf_eq_one]
      have htk : ∀ x : ↥L, t * (x : G) * t⁻¹ = ((k' * x * k'⁻¹ : ↥L) : G) := fun x => by
        rw [← hα, hαk', MulAut.conj_apply]
      have hfk0 : orderOf (f ⟨k0, k0_mem⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
        exact orderOf_k0
      obtain ⟨c, hc⟩ := exists_conj_of_orderOf_two hL hfk0 hk'o
      set yK : ↥L := c * f ⟨y0, y0_mem⟩ * c⁻¹ with hyKdef
      set y'K : ↥L := c * f ⟨y0', y0'_mem⟩ * c⁻¹ with hy'Kdef
      have hk0y : (⟨k0, k0_mem⟩ : ↥H12Cert.G) * ⟨y0, y0_mem⟩ *
          (⟨k0, k0_mem⟩ : ↥H12Cert.G)⁻¹ = (⟨y0, y0_mem⟩ : ↥H12Cert.G)⁻¹ :=
        Subtype.ext k0_conj_y0
      have hy03 : (⟨y0, y0_mem⟩ : ↥H12Cert.G) ^ 3 = 1 := Subtype.ext y0_pow_three
      have hy0' : (⟨y0', y0'_mem⟩ : ↥H12Cert.G) * ⟨y0, y0_mem⟩ *
          (⟨y0', y0'_mem⟩ : ↥H12Cert.G)⁻¹ = ⟨y0, y0_mem⟩ * zGU⁻¹ :=
        Subtype.ext y0'_conj_y0
      have r1 : k' * yK * k'⁻¹ = yK⁻¹ := by
        rw [← hc, hyKdef]
        have := congrArg f hk0y
        rw [map_mul, map_mul, map_inv, map_inv] at this
        calc c * f ⟨k0, k0_mem⟩ * c⁻¹ * (c * f ⟨y0, y0_mem⟩ * c⁻¹) *
              (c * f ⟨k0, k0_mem⟩ * c⁻¹)⁻¹
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
            = c * (f ⟨y0', y0'_mem⟩ * f ⟨y0, y0_mem⟩ * (f ⟨y0', y0'_mem⟩)⁻¹) *
                f ⟨y0', y0'_mem⟩ * c⁻¹ := by group
          _ = c * (f ⟨y0, y0_mem⟩ * (f zGU)⁻¹) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by rw [this]
          _ = c * f ⟨y0, y0_mem⟩ * (c⁻¹ * (c * (f zGU)⁻¹)) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by group
          _ = c * f ⟨y0, y0_mem⟩ * (c⁻¹ * ((f zGU)⁻¹ * c)) * f ⟨y0', y0'_mem⟩ * c⁻¹ := by rw [hcz]
          _ = c * f ⟨y0, y0_mem⟩ * c⁻¹ * (f zGU)⁻¹ * (c * f ⟨y0', y0'_mem⟩ * c⁻¹) := by group
      set y : MulAut U := σ (yK : G) with hydef
      set y' : MulAut U := σ (y'K : G) with hy'def
      have hρK : ∀ a b : ↥L, σ (a : G) * σ (b : G) = σ ((a * b : ↥L) : G) := fun a b => by
        rw [← map_mul, Subgroup.coe_mul]
      have hy3 : ∀ w, y (y (y w)) = w := fun w => by
        have h : y ^ 3 = 1 := by
          simp only [y]
          rw [← map_pow, ← Subgroup.coe_pow, r2, Subgroup.coe_one, map_one]
        have := congrArg (fun φ : MulAut U => φ w) h
        simpa [pow_succ, MulAut.mul_apply] using this
      have hcomm_z : ∀ a : ↥L, ∀ w, σ (a : G) (zW w) = zW (σ (a : G) w) := fun a w => by
        have h1 : a * z₁ = z₁ * a := Subgroup.mem_center_iff.mp hz₁c a
        have h2 := congrArg (fun x : ↥L => σ (x : G) w) h1
        simpa only [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hzW] using h2
      have hyz : ∀ w, y (zW w) = zW (y w) := hcomm_z yK
      have hy'z : ∀ w, y' (zW w) = zW (y' w) := hcomm_z y'K
      have hy' : ∀ w, y' (y w) = y (zW (y' w)) := fun w => by
        have h2 := congrArg (fun x : ↥L => σ (x : G) w) r3
        simpa only [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hzW] using h2
      have ht2' : ∀ w, tW (tW w) = w := fun w => by
        have h := congrArg (fun φ : MulAut U => φ w) (show tW * tW = 1 by
          rw [htWdef, ← map_mul, ← pow_two, ht2, map_one])
        simpa [MulAut.mul_apply] using h
      have hty : ∀ w, tW (y w) = y (y (tW w)) := fun w => by
        have h1 : t * (yK : G) = (yK : G) * yK * t := by
          have h2 := htk yK
          rw [r1, Subgroup.coe_inv] at h2
          have hy2 : (yK : G)⁻¹ = (yK : G) * yK := by
            rw [inv_eq_iff_mul_eq_one, ← pow_three, ← Subgroup.coe_pow, r2, Subgroup.coe_one]
          calc t * (yK : G) = t * yK * t⁻¹ * t := by group
            _ = (yK : G) * yK * t := by rw [h2, hy2]
        have h2 := congrArg (fun x : G => σ x w) h1
        simpa only [map_mul, MulAut.mul_apply] using h2
      have hcnt := card_sq_le_comm_pow_six hU2 hz3 hy3 hyz hy'z hy' ht2' hty
      have hUle : Nat.card ↥U₀ ≤ 2 ^ 12 := by
        have h1 : Nat.card ↥U₀ ^ 2 ≤ (2 ^ 12) ^ 2 :=
          hcnt.trans ((Nat.pow_le_pow_left hcomm_le 6).trans (by norm_num))
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have hUge : 4096 ≤ Nat.card ↥U₀ :=
        card_kerSum_ge hU2 hL' hzLc hU₀ (lt_of_le_of_lt hUle (by norm_num))
      have hU12' : Nat.card ↥U₀ = 4096 := by omega
      rw [← Subgroup.card_top (G := U), ← hker_top, hU12']
      norm_num
    ·
      exfalso
      have hnot : ∀ k : ↥L, α ≠ MulAut.conj k := fun k h => hinner ⟨k, h⟩
      have hq : CFSG.Open.IsQuasisimple ↥L := by
        have := hL.1.1
        exact ⟨Group.IsPerfect.commutator_eq_top, hL.1.2.1⟩
      have hinv := kg82HatM22Out_holds ↥L hq hL.2.1 hL.2.2 α hnot z₁ hz₁c
      have h1 : t * (z₁ : G) * t⁻¹ = (z₁ : G)⁻¹ := by
        rw [← hα, hinv, Subgroup.coe_inv]
      have hzz : ∀ w, zW (zW w) = zW⁻¹ w := fun w => by
        apply zW.injective
        rw [MulAut.apply_inv_self, hz3]
      have htz : ∀ w, tW (zW w) = zW (zW (tW w)) := fun w => by
        have h2 : tW * zW = zW⁻¹ * tW := by
          rw [htWdef, hzW, ← map_mul, ← map_inv, ← map_mul]
          exact congrArg σ (by rw [← h1]; group)
        have h3 := congrArg (fun φ : MulAut U => φ w) h2
        simp only [MulAut.mul_apply] at h3
        rw [h3, hzz]
      have h2 := card_le_comm_sq hU2 hz3 htz
      have h3 : Nat.card ↥U₀ ≤ 2 ^ 8 :=
        h2.trans ((Nat.pow_le_pow_left hcomm_le 2).trans (by norm_num))
      have h4 : 4096 ≤ Nat.card ↥U₀ :=
        card_kerSum_ge hU2 hL' hzLc hU₀ (lt_of_le_of_lt h3 (by norm_num))
      omega
  refine ⟨hU2, hU12, ?_, ?_⟩
  · exact fun a b h => Subtype.ext (hinj h)
  · refine ⟨?_, fun J hJ hinv => ?_⟩
    · intro hbot
      have : Nat.card ↥(⊤ : Subgroup U) = 1 := by rw [hbot, Subgroup.card_bot]
      rw [Subgroup.card_top, hU12] at this
      norm_num at this
    · by_cases hJ0 : J = ⊥
      · exact Or.inl hJ0
      · right
        have hge : 4096 ≤ Nat.card ↥J :=
          le_card_of_fpf hU2 hL' (by rw [hU12]; norm_num) hzLc _ J rfl hJ0
            (fun g u hu => hinv g g.2 u hu) (fun u _ hu => hzf u hu)
        have hle : Nat.card ↥J ≤ Nat.card ↥(⊤ : Subgroup U) := Subgroup.card_le_of_le hJ
        rw [Subgroup.card_top, hU12] at hle
        have heq : Nat.card ↥J = Nat.card U := by rw [hU12]; omega
        exact Subgroup.eq_top_of_card_eq J heq

end CFSG.Quasithin.AppendixH.H12
