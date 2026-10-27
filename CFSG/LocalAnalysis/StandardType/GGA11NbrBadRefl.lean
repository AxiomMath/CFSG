module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.Walter.Bender1970.S1.Burnside

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private lemma a11br_fpow_mul {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hp : ∀ i, f i ^ 7 = 1)
    (v w : Fin 4 → ZMod 7) : fPow f (v + w) = fPow f v * fPow f w := by
  let C : Subgroup G := Subgroup.closure (Set.range f)
  have hpair : (Set.range f).Pairwise Commute := fun a ha b hb _ => by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : CommGroup C := Subgroup.closureCommGroupOfComm hpair
  let F : Fin 4 → C := fun i => ⟨f i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hFpow : ∀ i, F i ^ 7 = 1 := fun i => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hp i
  have key : (∏ i : Fin 4, F i ^ ((v + w) i).val) =
      (∏ i : Fin 4, F i ^ (v i).val) * (∏ i : Fin 4, F i ^ (w i).val) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add]
    exact pow_eq_pow_of_modEq (by rw [Pi.add_apply, ZMod.val_add]; exact Nat.mod_modEq _ _)
      (hFpow i)
  have hcoe : ∀ u : Fin 4 → ℕ,
      (((∏ i : Fin 4, F i ^ u i) : C) : G) =
        f 0 ^ u 0 * f 1 ^ u 1 * f 2 ^ u 2 * f 3 ^ u 3 := by
    intro u
    rw [Fin.prod_univ_four]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rfl
  have h := congrArg (fun x : C => (x : G)) key
  rw [Subgroup.coe_mul, hcoe, hcoe, hcoe] at h
  simpa only [fPow] using h

private lemma a11br_fpow_zero {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f 0 = 1 := by
  simp [fPow]

private lemma a11br_fpow_single {G : Type} [Group G] (f : Fin 4 → G) (i : Fin 4) :
    fPow f (Pi.single i 1) = f i := by
  have hval0 : (0 : ZMod 7).val = 0 := by decide
  have hval1 : (1 : ZMod 7).val = 1 := by decide
  fin_cases i <;> simp [fPow, hval0, hval1]

private lemma a11br_fpow_zpow {G : Type} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hp : ∀ i, f i ^ 7 = 1)
    (k : ℤ) (v : Fin 4 → ZMod 7) : (fPow f v) ^ k = fPow f (k • v) := by
  let C : Subgroup G := Subgroup.closure (Set.range f)
  have hpair : (Set.range f).Pairwise Commute := fun a ha b hb _ => by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : CommGroup C := Subgroup.closureCommGroupOfComm hpair
  let F : Fin 4 → C := fun i => ⟨f i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hmem : ∀ u : Fin 4 → ZMod 7, fPow f u ∈ C := by
    intro u
    have : (fPow f u : G) = ((∏ i : Fin 4, F i ^ (u i).val : C) : G) := by
      rw [show (fPow f u : G) = f 0 ^ (u 0).val * f 1 ^ (u 1).val * f 2 ^ (u 2).val * f 3 ^ (u 3).val from rfl]
      rw [Fin.prod_univ_four]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rfl
    exact this ▸ (∏ i : Fin 4, F i ^ (u i).val : C).2
  let φ : Multiplicative (Fin 4 → ZMod 7) →* C :=
    { toFun := fun u => ⟨fPow f u.toAdd, hmem u.toAdd⟩
      map_one' := by
        apply Subtype.ext
        simp [a11br_fpow_zero]
      map_mul' := fun u w => by
        apply Subtype.ext
        exact a11br_fpow_mul f hcomm hp u.toAdd w.toAdd }
  have hcoe : ∀ u : Fin 4 → ZMod 7, ((φ (Multiplicative.ofAdd u) : C) : G) = fPow f u :=
    fun u => rfl
  have hzpow := map_zpow φ (Multiplicative.ofAdd v) k
  have htoAdd : Multiplicative.ofAdd v ^ k = Multiplicative.ofAdd (k • v) :=
    (ofAdd_zsmul k v).symm
  calc (fPow f v) ^ k = ((φ (Multiplicative.ofAdd v) : C) : G) ^ k := by rw [← hcoe v]
    _ = ((φ (Multiplicative.ofAdd v) ^ k : C) : G) := (Subgroup.coe_zpow C _ k).symm
    _ = ((φ (Multiplicative.ofAdd v ^ k) : C) : G) := by rw [← hzpow]
    _ = fPow f (k • v) := by rw [htoAdd]; exact hcoe (k • v)

private lemma a11br_fpow_injective {G : Type} [Group G] [Finite G] (f : Fin 4 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hp : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4) :
    Function.Injective (fPow f) := by
  let C : Subgroup G := Subgroup.closure (Set.range f)
  have hpair : (Set.range f).Pairwise Commute := fun a ha b hb _ => by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : CommGroup C := Subgroup.closureCommGroupOfComm hpair
  let F : Fin 4 → C := fun i => ⟨f i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hmem : ∀ u : Fin 4 → ZMod 7, fPow f u ∈ C := by
    intro u
    have : (fPow f u : G) = ((∏ i : Fin 4, F i ^ (u i).val : C) : G) := by
      rw [show (fPow f u : G) = f 0 ^ (u 0).val * f 1 ^ (u 1).val * f 2 ^ (u 2).val * f 3 ^ (u 3).val from rfl]
      rw [Fin.prod_univ_four]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rfl
    exact this ▸ (∏ i : Fin 4, F i ^ (u i).val : C).2
  let φ : Multiplicative (Fin 4 → ZMod 7) →* C :=
    { toFun := fun u => ⟨fPow f u.toAdd, hmem u.toAdd⟩
      map_one' := by
        apply Subtype.ext
        simp [a11br_fpow_zero]
      map_mul' := fun u w => by
        apply Subtype.ext
        exact a11br_fpow_mul f hcomm hp u.toAdd w.toAdd }
  have hcoe : ∀ u : Fin 4 → ZMod 7, ((φ (Multiplicative.ofAdd u) : C) : G) = fPow f u :=
    fun u => rfl
  have hsurj : Function.Surjective φ := by
    intro c
    have hle : Subgroup.closure (Set.range f) ≤ (φ.range).map (Subgroup.subtype C) := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨φ (Multiplicative.ofAdd (Pi.single i 1)),
        ⟨Multiplicative.ofAdd (Pi.single i 1), rfl⟩,
        by show fPow f (Pi.single i 1) = f i; exact a11br_fpow_single f i⟩
    have hc : (c : G) ∈ (φ.range).map (Subgroup.subtype C) := hle c.2
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc
    obtain ⟨u, hu⟩ := hy
    exact ⟨u, by rw [hu]; exact Subtype.ext hyc⟩
  letI : Fintype C := Fintype.ofFinite C
  have hcardC : Nat.card C = 7 ^ 4 := hcard
  have hcarddom : Nat.card (Multiplicative (Fin 4 → ZMod 7)) = 7 ^ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  have hcardF : Fintype.card (Multiplicative (Fin 4 → ZMod 7)) = Fintype.card C := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcarddom, hcardC]
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcardF⟩
  intro v w h
  have hφ : φ (Multiplicative.ofAdd v) = φ (Multiplicative.ofAdd w) := by
    apply Subtype.ext
    show fPow f v = fPow f w
    exact h
  simpa using congrArg Multiplicative.toAdd (hbij.1 hφ)

private lemma a11br_fPow_vec_one {G : Type} [Group G] (f : Fin 4 → G) :
    fPow f ![1, 1, 1, 1] = f 0 * f 1 * f 2 * f 3 := by
  have hval1 : (1 : ZMod 7).val = 1 := by decide
  simp [fPow, hval1]

private lemma a11br_fPow_vec_c {G : Type} [Group G] (f : Fin 4 → G) (c : ZMod 7) :
    fPow f ![1, 1, 1, c] = ell f c := by
  have hval1 : (1 : ZMod 7).val = 1 := by decide
  simp [fPow, ell, hval1]

private lemma a11br_mem_sup_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let M : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by rw [mul_one]⟩
      mul_mem' := by
        rintro x y ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * h₂ * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [hcomm h₂ hh₂ k₁ hk₁]
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [_root_.mul_inv_rev]
        exact hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk) }
  constructor
  · intro hx
    have hHM : H ≤ M := fun h hh => ⟨h, hh, 1, K.one_mem, by rw [mul_one]⟩
    have hKM : K ≤ M := fun k hk => ⟨1, H.one_mem, k, hk, by rw [one_mul]⟩
    exact sup_le hHM hKM hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

theorem a11NbrBadReflInput_holds
    : A11NbrBadReflInput := by
  intro hAM hLR hBF hRF hSS hMp hLB hRig G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx
    y' K' hnb hlabel hrefl c hc hline
  have hctx' : A11Ctx B Bs x L D J y K φ₃ f n Φ ρ := hctx
  obtain ⟨hrest, hconfig, hframe, hfextra, hcoh, hrho⟩ := hctx
  obtain ⟨hglue, hrange, hnbK, hBs, hx_eq, hy_f3, hD, hnL, hJK, hJ9, hLgen⟩ := hframe
  obtain ⟨hφinj, hφf, hfcomm, hford, hcard4, hn3, hnswap, hcomp⟩ := hglue
  obtain ⟨E, hEK, hEBs, hperf, hEcard, hnotdvd, hBssup, hyE⟩ :=
    hSS hMp hLB hRig G B Bs x L D J y K φ₃ f n Φ ρ hctx' y' K' hnb hlabel
  have hpair : (Set.range f).Pairwise Commute := fun a ha b hb _ => by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hfcomm i j
  have hcommC : IsMulCommutative (Subgroup.closure (Set.range f)) :=
    Subgroup.isMulCommutative_closure hpair
  have hcommB : IsMulCommutative ↥Bs := hBs ▸ hcommC
  have hp : ∀ i, f i ^ 7 = 1 := fun i => by
    rw [← hford i]
    exact pow_orderOf_eq_one (f i)
  have hinj : Function.Injective (fPow f) := a11br_fpow_injective f hfcomm hp hcard4
  have hy'Bs : Subgroup.zpowers y' ≤ Bs := by rw [hBssup]; exact le_sup_left
  have hcomm_sup : ∀ a ∈ Subgroup.zpowers y', ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hcommB.is_comm.comm (⟨a, hy'Bs ha⟩ : Bs) (⟨b, hEBs hb⟩ : Bs))
  have decomp : ∀ ⦃h : G⦄, h ∈ Bs → ∃ j : ℤ, ∃ e ∈ E, h = y' ^ j * e := by
    intro h hh
    have hmem : h ∈ Subgroup.zpowers y' ⊔ E := by rw [← hBssup]; exact hh
    obtain ⟨a, ha, e, he, hae⟩ := (a11br_mem_sup_of_commute hcomm_sup).mp hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨j, e, he, by rw [← hae, ← hj]⟩
  have hxBs : x ∈ Bs := by
    rw [hx_eq, ← hBs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_range_self 0))
      (Subgroup.subset_closure (Set.mem_range_self 1)))
      (Subgroup.subset_closure (Set.mem_range_self 2)))
      (Subgroup.subset_closure (Set.mem_range_self 3))
  obtain ⟨k, z, hzE, hx_decomp⟩ := decomp hxBs
  have hzK : z ∈ K' := hEK hzE
  have hfixx : ∀ g ∈ K', g ∈ Subgroup.normalizer (Bs : Set G) → g * x * g⁻¹ = x :=
    hRF hAM hLR hBF G B Bs x L D J y K φ₃ f n Φ ρ hctx' y' K' hnb hrefl c hc hline
  have hzne : z ≠ 1 := by
    intro hz1
    have hx_zp : x ∈ Subgroup.zpowers (ell f c) := by
      rw [← hline]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [hx_decomp, hz1, mul_one]⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx_zp
    have hpowone : fPow f ![1, 1, 1, 1] = x := by rw [a11br_fPow_vec_one, ← hx_eq]
    have hm' : (fPow f ![1, 1, 1, c]) ^ m = fPow f ![1, 1, 1, 1] := by
      rw [a11br_fPow_vec_c, hpowone]
      exact hm
    have hmvec : m • ![1, 1, 1, c] = ![1, 1, 1, 1] := by
      apply hinj
      rw [← a11br_fpow_zpow f hfcomm hp m ![1, 1, 1, c], hm']
    have h0 : (m : ZMod 7) = 1 := by
      have := congrFun hmvec 0
      simpa [Pi.smul_apply, zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ] using this
    have h3 : (m : ZMod 7) * c = 1 := by
      have := congrFun hmvec 3
      simpa [Pi.smul_apply, zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_succ] using this
    have hc_eq : c = 1 := by
      rw [h0] at h3
      simpa using h3
    have hcne : c ≠ 1 := by
      rcases hc with h | h | h | h <;> rw [h] <;> decide
    exact hcne hc_eq
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcard_sub : Nat.card ↥(E.subgroupOf K') = 7 ^ 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv).trans hEcard
  have hEsubP : IsPGroup 7 ↥(E.subgroupOf K') := IsPGroup.of_card hcard_sub
  have hTmax : ∀ {Q : Subgroup ↥K'}, IsPGroup 7 ↥Q → E.subgroupOf K' ≤ Q →
      Q = E.subgroupOf K' := by
    intro Q hQ hle
    obtain ⟨j, hj⟩ := hQ.exists_card_eq
    have hle3 : 3 ≤ j := by
      have h73 : 7 ^ 3 ≤ Nat.card Q := by
        rw [← hcard_sub]
        exact Subgroup.card_le_of_le hle
      rw [hj] at h73
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp h73
    have hle3' : j ≤ 3 := by
      by_contra hj4
      push Not at hj4
      exact hnotdvd ((pow_dvd_pow 7 hj4).trans (hj ▸ Subgroup.card_subgroup_dvd_card Q))
    have hjeq : j = 3 := le_antisymm hle3' hle3
    have hcardQ : Nat.card Q = Nat.card ↥(E.subgroupOf K') := by rw [hj, hjeq, hcard_sub]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardQ)).symm
  let T : Sylow 7 ↥K' := Sylow.mk (E.subgroupOf K') hEsubP hTmax
  have hEcomm : ∀ a b : ↥(E.subgroupOf K'), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    change ((a : ↥K') : G) * ((b : ↥K') : G) = ((b : ↥K') : G) * ((a : ↥K') : G)
    simpa using congrArg Subtype.val (hcommB.is_comm.comm
      (⟨((a : ↥K') : G), hEBs (Subgroup.mem_subgroupOf.mp a.2)⟩ : Bs)
      (⟨((b : ↥K') : G), hEBs (Subgroup.mem_subgroupOf.mp b.2)⟩ : Bs))
  have hEcommI : IsMulCommutative ↥(E.subgroupOf K') :=
    IsMulCommutative.mk (Std.Commutative.mk hEcomm)
  haveI : IsMulCommutative ↥(E.subgroupOf K') := hEcommI
  have hTcoe : (T : Subgroup ↥K') = E.subgroupOf K' := rfl
  haveI : IsMulCommutative (T : Subgroup ↥K') := hTcoe.symm ▸ hEcommI
  have hK'leC : K' ≤ Subgroup.centralizer ({y'} : Set G) := hnb.1.2.2.2.1
  have hnorm_of : ∀ g : G, g * y' = y' * g → (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      (∀ e ∈ E, g⁻¹ * e * g ∈ E) → g ∈ Subgroup.normalizer (Bs : Set G) := by
    intro g hgy' hgE hgEinv
    have hconj : g * y' * g⁻¹ = y' := by rw [hgy']; group
    have hconjpow : ∀ j : ℤ, g * y' ^ j * g⁻¹ = y' ^ j := by
      intro j
      have h := map_zpow (MulAut.conj g) y' j
      rw [MulAut.conj_apply, MulAut.conj_apply] at h
      rw [hconj] at h
      exact h
    have hconjpow_inv : ∀ j : ℤ, g⁻¹ * y' ^ j * g = y' ^ j := by
      intro j
      have hgy'inv : g⁻¹ * y' = y' * g⁻¹ := by
        calc g⁻¹ * y' = g⁻¹ * (y' * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * y') * g⁻¹ := by rw [← hgy']
          _ = y' * g⁻¹ := by group
      have hconj₂ : g⁻¹ * y' * (g⁻¹)⁻¹ = y' := by rw [inv_inv, hgy'inv]; group
      have h := map_zpow (MulAut.conj g⁻¹) y' j
      rw [MulAut.conj_apply, MulAut.conj_apply] at h
      rw [hconj₂] at h
      simpa using h
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨j, e, he, rfl⟩ := decomp hh
      have heq : g * (y' ^ j * e) * g⁻¹ = y' ^ j * (g * e * g⁻¹) := by
        calc g * (y' ^ j * e) * g⁻¹ = (g * y' ^ j * g⁻¹) * (g * e * g⁻¹) := by group
          _ = y' ^ j * (g * e * g⁻¹) := by rw [hconjpow]
      rw [heq, hBssup]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩))
        (Subgroup.mem_sup_right (hgE e he))
    · intro hh
      obtain ⟨j, e, he, hheq⟩ := decomp hh
      have heq : g⁻¹ * (y' ^ j * e) * g = y' ^ j * (g⁻¹ * e * g) := by
        calc g⁻¹ * (y' ^ j * e) * g = (g⁻¹ * y' ^ j * g) * (g⁻¹ * e * g) := by group
          _ = y' ^ j * (g⁻¹ * e * g) := by rw [hconjpow_inv]
      have hh_eq : h = y' ^ j * (g⁻¹ * e * g) := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = g⁻¹ * (y' ^ j * e) * g := by rw [hheq]
          _ = y' ^ j * (g⁻¹ * e * g) := heq
      rw [hh_eq, hBssup]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩))
        (Subgroup.mem_sup_right (hgEinv e he))
  let zK : ↥K' := ⟨z, hzK⟩
  have hzN : ∀ nn ∈ Subgroup.normalizer ((T : Subgroup ↥K') : Set ↥K'), nn * zK = zK * nn := by
    intro nn hnn
    have hnn' : nn ∈ Subgroup.normalizer ((E.subgroupOf K' : Subgroup ↥K') : Set ↥K') := hnn
    have hnyy : (nn : G) * y' = y' * (nn : G) :=
      ((Subgroup.mem_centralizer_iff.mp (hK'leC nn.2)) y' (Set.mem_singleton y')).symm
    have hnnE : ∀ e ∈ E, (nn : G) * e * (nn : G)⁻¹ ∈ E := by
      intro e he
      have h1 : (⟨e, hEK he⟩ : ↥K') ∈ E.subgroupOf K' := by
        rw [Subgroup.mem_subgroupOf]; exact he
      have h2 := (Subgroup.mem_normalizer_iff.mp hnn' (⟨e, hEK he⟩ : ↥K')).mp h1
      simpa using (Subgroup.mem_subgroupOf.mp h2)
    have hnnEinv : ∀ e ∈ E, (nn : G)⁻¹ * e * (nn : G) ∈ E := by
      intro e he
      have h1 : (⟨e, hEK he⟩ : ↥K') ∈ E.subgroupOf K' := by
        rw [Subgroup.mem_subgroupOf]; exact he
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ hnn') (⟨e, hEK he⟩ : ↥K')).mp h1
      simpa using (Subgroup.mem_subgroupOf.mp h2)
    have hnng : (nn : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      hnorm_of (nn : G) hnyy hnnE hnnEinv
    have hfixnn : (nn : G) * x * (nn : G)⁻¹ = x := hfixx (nn : G) nn.2 hnng
    have hyj : (nn : G) * y' ^ k * (nn : G)⁻¹ = y' ^ k := by
      have h := map_zpow (MulAut.conj (nn : G)) y' k
      rw [MulAut.conj_apply, MulAut.conj_apply] at h
      have hconj : (nn : G) * y' * (nn : G)⁻¹ = y' := by rw [hnyy]; group
      rw [hconj] at h
      exact h
    have hconjz : (nn : G) * z * (nn : G)⁻¹ = z := by
      have h1 : y' ^ k * ((nn : G) * z * (nn : G)⁻¹) = y' ^ k * z := by
        calc y' ^ k * ((nn : G) * z * (nn : G)⁻¹)
            = (nn : G) * (y' ^ k * z) * (nn : G)⁻¹ := by
              rw [show (nn : G) * (y' ^ k * z) * (nn : G)⁻¹ =
                ((nn : G) * y' ^ k * (nn : G)⁻¹) * ((nn : G) * z * (nn : G)⁻¹)
                by group]
              rw [hyj]
          _ = (nn : G) * x * (nn : G)⁻¹ := by rw [← hx_decomp]
          _ = x := hfixnn
          _ = y' ^ k * z := hx_decomp
      exact mul_left_cancel h1
    apply Subtype.ext
    calc (nn : G) * z = ((nn : G) * z * (nn : G)⁻¹) * (nn : G) := by group
      _ = z * (nn : G) := by rw [hconjz]
  have hzT : zK ∈ (T : Subgroup ↥K') := by
    change (⟨z, hzK⟩ : ↥K') ∈ E.subgroupOf K'
    rw [Subgroup.mem_subgroupOf]
    exact hzE
  have hz1 : zK = 1 :=
    CFSG.Walter.eq_one_of_mem_sylow_of_commute_normalizer T hzT
      (by rw [hperf]; exact Subgroup.mem_top _) hzN
  exact hzne (by
    have h := congrArg Subtype.val hz1
    simpa [zK] using h)

end CFSG.StandardType.A11

end
