module

public import CFSG.RankThree.PartOne.N143.Statements
public import CFSG.RankThree.PartOne.S12.Sec138LocLinear
public import CFSG.RankThree.PartOne.S12.ReflHessianGroup

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option synthInstance.maxSize 1024 in
theorem center_model : ∀ x : HIdx, (∀ w : HIdx, HIdx.mul x w = HIdx.mul w x) →
    x = HIdx.one ∨ x = hzH ∨ x = HIdx.mul hzH hzH := by decide +kernel

set_option synthInstance.maxSize 1024 in
theorem heis_model : ∀ x₀ ∈ ({hzH, HIdx.mul hzH hzH} : Finset HIdx), ∀ x : HIdx,
    HIdx.mul x (HIdx.mul x x) = HIdx.one → x ≠ HIdx.one → x ≠ x₀ → x ≠ HIdx.mul x₀ x₀ →
    ∃ g : HIdx, HIdx.mul g (HIdx.mul g g) = HIdx.one ∧
      HIdx.mul (HIdx.mul g x) (HIdx.inv g) = HIdx.mul x x₀ := by decide +kernel

section PsiGrp

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  (e : Module.Basis (Fin 3) K V) (η : K)

@[expose] def psiGrp (h3 : η ^ 3 = 1) : Subgroup (V ≃ₗ[K] V) where
  carrier := Set.range (psi e η h3)
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨HIdx.mul x y, psi_mul e η h3 x y⟩
  one_mem' := ⟨HIdx.one, psi_one e η h3⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨HIdx.inv x, psi_inv e η h3 x⟩

theorem closure_R9_psiGrp (h3 : η ^ 3 = 1) [DecidableEq (V ≃ₗ[K] V)] :
    Subgroup.closure ((R9.image (psi e η h3) : Finset (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) =
      psiGrp e η h3 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    have hgen : ∀ a ∈ insert HIdx.one R9, psi e η h3 a ∈
        Subgroup.closure ((R9.image (psi e η h3) : Finset (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [psi_one]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha))
    obtain ⟨p, hp, q, hq, rfl⟩ := HIdx_cover x
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.1 hq
    rw [Finset.mem_product] at hab hcd
    simp only [psi_mul e η h3]
    exact mul_mem (mul_mem (hgen a hab.1) (hgen b hab.2))
      (mul_mem (hgen c hcd.1) (hgen d hcd.2))

theorem card_psiGrp (h3 : η ^ 3 = 1) (h1 : η ≠ 1) : Nat.card (psiGrp e η h3) = 54 := by
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at h3
  have : Nat.card (psiGrp e η h3) = Nat.card (Set.range (psi e η h3)) := rfl
  rw [this, Nat.card_range_of_injective (psi_injective e η h3 h1 h0), Nat.card_eq_fintype_card,
    card_HIdx]

end PsiGrp

structure HessianSpec (p : ℕ) {G : Type} [Group G] (E : Subgroup G) (P : Subgroup (MulAut E))
    (z : MulAut E) : Prop where
  P_le : P ≤ reflectionGroup p E
  card_P : Nat.card P = 27
  mem_P : ∀ y ∈ reflectionGroup p E, y ∈ P ↔ y ^ 3 = 1
  z_mem : z ∈ P
  z_ne : z ≠ 1
  z_cube : z ^ 3 = 1
  z_central : ∀ g : MulAut E, z * g = g * z
  z_scalar : ∃ k : ℕ, k % p ≠ 1 ∧ k ^ 3 % p = 1 ∧ ∀ a : E, z a = a ^ k
  prod_refl : ∀ y ∈ reflectionGroup p E, y ^ 3 = 1 → y ∉ Subgroup.zpowers z →
    ∃ s ∈ reflectionSet p E, ∃ t ∈ reflectionSet p E, s ≠ t ∧ (y = s * t ∨ y = t * s)
  heis : ∀ y ∈ P, y ∉ Subgroup.zpowers z → ∃ g ∈ P, g * y * g⁻¹ = y * z

section Core

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem hessianGeometry [IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 3) (hp5 : 5 ≤ p)
    (hD3 : ThreeTranspD p E) (hirr : torusIrreducible E) (hne : (reflectionSet p E).Nonempty)
    (hess : HessianCase p E) :
    Nat.card (reflectionGroup p E) = 54 ∧
      ∃ (P : Subgroup (MulAut E)) (z : MulAut E), HessianSpec p E P z := by
  classical
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E hcard
  have hdim : Module.finrank (ZMod p) (Fin 3 → ZMod p) = 3 := Module.finrank_fin_fun _
  have h2 := Sec138Loc.two_ne_zero_of_five_le (p := p) hp5
  have h3 := Sec138Loc.three_ne_zero_of_five_le (p := p) hp5
  have hR := Sec138Loc.isRSet_dstar f hp5 hD3
  have hU := Sec138Loc.uspan_dstar f hp5 hirr hne
  have hnc : ∀ T ∈ Sec138Loc.dstar f, ∀ S ∈ Sec138Loc.dstar f, T ≠ S → T * S ≠ S * T := by
    intro T hT S hS hTS
    obtain ⟨s, hs, rfl⟩ := (Sec138Loc.mem_dstar f).1 hT
    obtain ⟨t, ht, rfl⟩ := (Sec138Loc.mem_dstar f).1 hS
    intro hc
    have hst : s ≠ t := fun e => hTS (by rw [e])
    exact hess s hs t ht hst ((Sec138Loc.coordHom_comm_iff f).1 hc)
  obtain ⟨-, -, ω, zV, hω, hzVmem, hzVs, hzV1, hzV3, hzVc, hprodV, PV, hPVle, hPVcard,
    hzVP, hPViff⟩ := hessian_structure hdim h2 h3 hR hU hnc
  obtain ⟨e, η, hη3, hη1, hη, hdesc⟩ := hessian_eq_image hdim h2 h3 hR hU hnc
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at hη3
  set φ := LinAlg.coordHom f with hφ
  have hφinj : Function.Injective φ := LinAlg.coordHom_injective f
  set X := reflectionGroup p E with hX
  have hD : ((Sec138Loc.dstar f : Finset _) : Set _) = φ '' reflectionSet p E := by
    ext T
    simp only [Finset.mem_coe, Sec138Loc.mem_dstar, Set.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hXmap : X.map φ = Subgroup.closure ((Sec138Loc.dstar f : Finset _) : Set _) := by
    rw [hX, reflectionGroup, MonoidHom.map_closure, hD]
  have hcl : Subgroup.closure ((Sec138Loc.dstar f : Finset _) : Set _) = psiGrp e η hη3 := by
    have : Sec138Loc.dstar f = R9.image (psi e η hη3) := by
      ext T
      rw [hdesc T, Finset.mem_image]
    rw [this]
    exact closure_R9_psiGrp e η hη3
  have hXmapR : X.map φ = psiGrp e η hη3 := hXmap.trans hcl
  have hcardX' : Nat.card X = 54 := by
    rw [← Subgroup.card_map_of_injective hφinj, hXmapR]
    exact card_psiGrp e η hη3 hη1
  refine ⟨hcardX', ?_⟩
  have hmemX : ∀ y ∈ X, φ y ∈ psiGrp e η hη3 := fun y hy => by
    rw [← hXmapR]
    exact Subgroup.mem_map_of_mem φ hy
  have hlift : ∀ T ∈ psiGrp e η hη3, ∃ y ∈ X, φ y = T := fun T hT => by
    rw [← hXmapR] at hT
    exact Subgroup.mem_map.1 hT
  have hmodel : ∀ T ∈ psiGrp e η hη3, ∃ x : HIdx, psi e η hη3 x = T := fun T hT => hT
  have hzVmem' : zV ∈ psiGrp e η hη3 := by rw [← hcl]; exact hzVmem
  have hPVle' : PV ≤ psiGrp e η hη3 := hPVle.trans hcl.le
  have hPViff' : ∀ y ∈ psiGrp e η hη3, y ∈ PV ↔ y ^ 3 = 1 := fun y hy => by
    apply hPViff
    rw [hcl]
    exact hy
  have hprodV' : ∀ y ∈ psiGrp e η hη3, y ^ 3 = 1 → y ∉ Subgroup.zpowers zV →
      ∃ s ∈ Sec138Loc.dstar f, ∃ t ∈ Sec138Loc.dstar f, s ≠ t ∧ (y = s * t ∨ y = t * s) :=
    fun y hy => by
      apply hprodV
      rw [hcl]
      exact hy
  set P : Subgroup (MulAut E) := PV.comap φ with hPdef
  have hPmem : ∀ y : MulAut E, y ∈ P ↔ φ y ∈ PV := fun y => Iff.rfl
  have hPX : P ≤ X := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hlift _ (hPVle' hy)
    rw [← hφinj hxy]
    exact hx
  have hPVrange : PV ≤ φ.range := fun T hT => by
    obtain ⟨y, -, hy⟩ := hlift T (hPVle' hT)
    exact ⟨y, hy⟩
  have hPcard : Nat.card P = 27 := by
    have : P.map φ = PV := Subgroup.map_comap_eq_self hPVrange
    rw [← Subgroup.card_map_of_injective hφinj, this]
    exact hPVcard
  have hPiff : ∀ y ∈ X, y ∈ P ↔ y ^ 3 = 1 := fun y hy => by
    rw [hPmem, hPViff' _ (hmemX y hy), ← map_pow]
    exact map_eq_one_iff φ hφinj
  obtain ⟨z, hzX, hzφ⟩ := hlift zV hzVmem'
  have hzP : z ∈ P := by
    rw [hPmem, hzφ]
    exact hzVP
  have hz1 : z ≠ 1 := fun h => hzV1 (by rw [← hzφ, h, map_one])
  have hz3 : z ^ 3 = 1 := hφinj (by rw [map_pow, hzφ, hzV3, map_one])
  have hzc : ∀ g : MulAut E, z * g = g * z := fun g =>
    hφinj (by rw [map_mul, map_mul, hzφ]; exact hzVc (φ g))
  have hωne : ω ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hω
  have hzs : ∃ k : ℕ, k % p ≠ 1 ∧ k ^ 3 % p = 1 ∧ ∀ a : E, z a = a ^ k := by
    have hp := (Fact.out : p.Prime)
    have hp1 : 1 < p := hp.one_lt
    have : Fact (1 < p) := ⟨hp1⟩
    refine ⟨ω.val, ?_, ?_, fun a => ?_⟩
    · rw [Nat.mod_eq_of_lt (ZMod.val_lt ω)]
      intro h
      apply hωne
      rw [← ZMod.natCast_zmod_val ω, h]
      simp
    · have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
      have hc : (((ω.val ^ 3 : ℕ)) : ZMod p) = 1 := by
        push_cast
        rw [ZMod.natCast_zmod_val ω]
        exact hω3
      have h1 := ZMod.val_natCast p (ω.val ^ 3)
      rw [hc, ZMod.val_one p] at h1
      exact h1.symm
    · obtain ⟨v, rfl⟩ : ∃ v : Fin 3 → ZMod p, f (Multiplicative.ofAdd v) = a :=
        ⟨Multiplicative.toAdd (f.symm a), by simp⟩
      have h1 := LinAlg.apply_coordLin f z v
      have h2 : LinAlg.coordLin f z v = ω • v := by
        have := hzVs v
        rw [← hzφ] at this
        exact this
      rw [h2] at h1
      rw [← h1, ← map_pow, ← ofAdd_nsmul]
      congr 2
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have hprod : ∀ y ∈ X, y ^ 3 = 1 → y ∉ Subgroup.zpowers z →
      ∃ s ∈ reflectionSet p E, ∃ t ∈ reflectionSet p E, s ≠ t ∧ (y = s * t ∨ y = t * s) := by
    intro y hy hy3 hyz
    have hy3' : (φ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hyz' : φ y ∉ Subgroup.zpowers zV := by
      intro hmem
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
      apply hyz
      refine Subgroup.mem_zpowers_iff.2 ⟨i, hφinj ?_⟩
      rw [map_zpow, hzφ, hi]
    obtain ⟨S, hS, T, hT, hST, hc⟩ := hprodV' (φ y) (hmemX y hy) hy3' hyz'
    obtain ⟨s, hs, rfl⟩ := (Sec138Loc.mem_dstar f).1 hS
    obtain ⟨t, ht, rfl⟩ := (Sec138Loc.mem_dstar f).1 hT
    refine ⟨s, hs, t, ht, fun e' => hST (by rw [e']), ?_⟩
    rcases hc with h | h
    · left
      exact hφinj (by rw [map_mul]; exact h)
    · right
      exact hφinj (by rw [map_mul]; exact h)
  obtain ⟨x₀, hx₀⟩ := hmodel zV hzVmem'
  have hx₀c : ∀ w : HIdx, HIdx.mul x₀ w = HIdx.mul w x₀ := by
    intro w
    apply psi_injective e η hη3 hη1 h0
    rw [psi_mul, psi_mul, hx₀]
    exact hzVc _
  have hx₀ne : x₀ ≠ HIdx.one := fun h => hzV1 (by rw [← hx₀, h, psi_one])
  have hx₀mem : x₀ ∈ ({hzH, HIdx.mul hzH hzH} : Finset HIdx) := by
    rcases center_model x₀ hx₀c with h | h | h
    · exact absurd h hx₀ne
    · simp [h]
    · simp [h]
  have hheis : ∀ y ∈ P, y ∉ Subgroup.zpowers z → ∃ g ∈ P, g * y * g⁻¹ = y * z := by
    intro y hyP hyz
    have hyX : y ∈ X := hPX hyP
    obtain ⟨x, hx⟩ := hmodel (φ y) (hmemX y hyX)
    have hy3 : y ^ 3 = 1 := (hPiff y hyX).1 hyP
    have hx3 : HIdx.mul x (HIdx.mul x x) = HIdx.one := by
      apply psi_injective e η hη3 hη1 h0
      rw [psi_mul, psi_mul, psi_one, hx, ← pow_three, ← map_pow, hy3, map_one]
    have hxz1 : x ≠ HIdx.one := by
      rintro rfl
      apply hyz
      rw [psi_one] at hx
      have : y = 1 := hφinj (by rw [← hx, map_one])
      rw [this]
      exact Subgroup.one_mem _
    have hxz2 : x ≠ x₀ := by
      rintro rfl
      apply hyz
      have : y = z := hφinj (by rw [hzφ, ← hx, hx₀])
      rw [this]
      exact Subgroup.mem_zpowers z
    have hxz3 : x ≠ HIdx.mul x₀ x₀ := by
      rintro rfl
      apply hyz
      have : y = z ^ 2 := hφinj (by rw [map_pow, hzφ, ← hx₀, ← hx, psi_mul, pow_two])
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) 2
    obtain ⟨g, hg3, hgx⟩ := heis_model x₀ hx₀mem x hx3 hxz1 hxz2 hxz3
    obtain ⟨g', hg'X, hg'φ⟩ := hlift (psi e η hη3 g) ⟨g, rfl⟩
    have hg'3 : g' ^ 3 = 1 := hφinj (by
      rw [map_pow, hg'φ, pow_three, ← psi_mul, ← psi_mul, hg3, psi_one, map_one])
    refine ⟨g', (hPiff g' hg'X).2 hg'3, hφinj ?_⟩
    rw [map_mul, map_mul, map_inv, hg'φ, ← hx, ← psi_inv, ← psi_mul, ← psi_mul, hgx, psi_mul,
      hx, hx₀, map_mul, hzφ]
  exact ⟨P, z, ⟨hPX, hPcard, hPiff, hzP, hz1, hz3, hzc, hzs, hprod, hheis⟩⟩

end Core

end CFSG.RankThree.PartOne.N143
