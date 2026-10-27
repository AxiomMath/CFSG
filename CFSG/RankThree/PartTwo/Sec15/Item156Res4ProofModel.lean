module

public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156Res4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree Subgroup Equiv
open CFSG.RankThree.Native.ONTriple

variable {X : Type} [Group X]

theorem inf_zpowers_eq_bot_of_not_mem' [Finite X] {D : Subgroup X} {w : X}
    (hw3 : orderOf w = 3) (hwD : w ∉ D) : D ⊓ zpowers w = ⊥ := by
  have hcard : Nat.card (zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
  have : Fact (Nat.card (zpowers w)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (D.subgroupOf (zpowers w)) with h | h
  · rw [eq_bot_iff]
    intro y ⟨hyD, hyw⟩
    have hy : (⟨y, hyw⟩ : zpowers w) ∈ D.subgroupOf (zpowers w) := hyD
    rw [h] at hy
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hy))
  · exfalso
    have hd : (⟨w, mem_zpowers w⟩ : zpowers w) ∈ D.subgroupOf (zpowers w) := by rw [h]; trivial
    exact hwD hd

theorem orderOf_eq_three {w : X} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) : orderOf w = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hw3 hw1

theorem card_sup_zpowers_three [Finite X] {W : Subgroup X} {v : X}
    (hWc : IsMulCommutative W) (hW3 : ∀ w ∈ W, w ^ 3 = 1) (hvW : v ∈ centralizer (W : Set X))
    (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (hvn : v ∉ W) :
    Nat.card (W ⊔ zpowers v : Subgroup X) = Nat.card W * 3 ∧
      IsMulCommutative (W ⊔ zpowers v : Subgroup X) ∧ ∀ w ∈ W ⊔ zpowers v, w ^ 3 = 1 :=
  CFSG.RankThree.card_sup_zpowers_of_disjoint hvW hWc hW3 (orderOf_eq_three hv3 hv1)
    (inf_zpowers_eq_bot_of_not_mem' (orderOf_eq_three hv3 hv1) hvn)

theorem mem_centralizer_sup_zpowers {W : Subgroup X} {x v : X}
    (hW : v ∈ centralizer (W : Set X)) (hx : x * v = v * x) :
    v ∈ centralizer ((W ⊔ zpowers x : Subgroup X) : Set X) := by
  have h1 : W ≤ centralizer ({v} : Set X) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hW w hw)
  have h2 : zpowers x ≤ centralizer ({v} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hx)
  rw [mem_centralizer_iff]
  intro w hw
  exact mem_centralizer_singleton_iff.mp (sup_le h1 h2 hw)

section Model

theorem card_le_27_of_comm
    (ψ : X ≃* GM) {B : Subgroup X} (hB : IsPGroup 3 B)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B' := B.map ψ.toMonoidHom with hB'
  have hB'3 : IsPGroup 3 B' := hB.map _
  obtain ⟨P, hP⟩ := hB'3.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  have hB'Q : B' ≤ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := hg ▸ hP
  have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBc x hx y hy]
  have h := hr.card_le_of_abelian (B'.subgroupOf _) fun a ha b hb =>
    Subtype.ext (hB'c _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hB'Q).toEquiv, hB',
    Subgroup.card_map_of_injective ψ.injective] at h

theorem exists_E27_le_centralizer
    [Finite X] (ψ : X ≃* GM) (hZ3 : Nat.card (center X) = 3)
    {b : X} (hb3 : b ^ 3 = 1) :
    ∃ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      F ≤ centralizer ({b} : Set X) := by
  obtain ⟨b', hb'3, hb'z, hb'C⟩ : ∃ b' : X, b' ^ 3 = 1 ∧ b' ∉ center X ∧
      ∀ y : X, y * b' = b' * y → (∀ u ∈ center X, u * b = b * u) → y * b = b * y := by
    by_cases hbz : b ∈ center X
    · refine ⟨ψ.symm (xG 0), ?_, ?_, fun y _ _ => mem_center_iff.mp hbz y⟩
      · rw [← map_pow, xG0_cube, map_one]
      · rw [Sec13.ON134.mem_center_iff_model ψ, MulEquiv.apply_symm_apply]
        intro hx
        have h0 := (relG.coord_eq_zero_iff ⟨xG 0, ThreeQRel.v_mem 0⟩).2 hx
        rw [coord_xG] at h0
        exact absurd (congrFun h0 0) (by decide)
    · exact ⟨b, hb3, hbz, fun y hy _ => hy⟩
  obtain ⟨x, hx3, hxb, hxn⟩ := Sec13.ON134.exists_centralizer ψ hb'3 hb'z
  have hb'1 : b' ≠ 1 := fun h => hb'z (h ▸ one_mem _)
  have hx1 : x ≠ 1 := fun h => hxn (h ▸ one_mem _)
  have hZc : IsMulCommutative (center X) := inferInstance
  have hZ3' : ∀ w ∈ center X, w ^ 3 = 1 := by
    intro w hw
    have h := pow_card_eq_one' (G := center X) (x := ⟨w, hw⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hb'Z : b' ∈ centralizer (center X : Set X) :=
    mem_centralizer_iff.mpr fun w hw => (mem_center_iff.mp hw b').symm
  obtain ⟨h9, h9c, h93⟩ := card_sup_zpowers_three hZc hZ3' hb'Z hb'3 hb'1 hb'z
  have hxW : x ∈ centralizer ((center X ⊔ zpowers b' : Subgroup X) : Set X) := by
    refine mem_centralizer_sup_zpowers ?_ hxb.symm
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_center_iff.mp hw x).symm
  have hxn' : x ∉ center X ⊔ zpowers b' := by rwa [sup_comm]
  obtain ⟨h27, h27c, h273⟩ := card_sup_zpowers_three h9c h93 hxW hx3 hx1 hxn'
  refine ⟨center X ⊔ zpowers b' ⊔ zpowers x, ⟨h27c, h273⟩, by rw [h27, h9, hZ3], ?_⟩
  have hZb : ∀ u ∈ center X, u * b = b * u := fun u hu => (mem_center_iff.mp hu b).symm
  have h1 : center X ≤ centralizer ({b} : Set X) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (hZb u hu)
  have h2 : zpowers b' ≤ centralizer ({b} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hb'C b' rfl hZb))
  have h3 : zpowers x ≤ centralizer ({b} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hb'C x hxb hZb))
  exact sup_le (sup_le h1 h2) h3

omit [Group X] in
theorem map_centralizer_singleton_equiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (b : X) :
    (centralizer ({b} : Set X)).map ψ.toMonoidHom = centralizer ({ψ b} : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨ψ.symm y, ?_, MulEquiv.apply_symm_apply ψ y⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rw [mem_centralizer_singleton_iff] at hy
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem exists_centralizer_eq
    (ψ : X ≃* GM) {b : X}
    (hb3 : b ^ 3 = 1) (hbz : b ∉ center X) :
    ∃ K : Subgroup X, centralizer ({b} : Set X) = zpowers b ⊔ K ∧ zpowers b ⊓ K = ⊥ ∧
      center X ≤ K ∧ ∃ ρ : ↥K →* Perm (Fin 6), ρ.range = alternatingGroup (Fin 6) ∧
        ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := ψ b with ha
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hb3, map_one]
  have haz : a ∉ zpowers zG := fun h => hbz ((Sec13.ON134.mem_center_iff_model ψ).2 h)
  have ha1 : a ≠ 1 := fun h => haz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ha3 ha1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have haP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers a))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 haP (conj_not_mem_zpowers haz g)
  set n := g⁻¹ * wordN w with hn
  have han : a = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← han] at h1 h2
  set KM := K0G.map (MulAut.conj n).toMonoidHom with hKM
  set K := KM.map ψ.symm.toMonoidHom with hK
  have hmapK : K.map ψ.toMonoidHom = KM := by
    rw [hK, Subgroup.map_map]
    convert Subgroup.map_id KM
    ext y
    simp
  have hinj := Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  have hzKM : zG ∈ KM := ⟨zG, zG_mem_K0', by rw [conj_zG]⟩
  have hmem : ∀ k : ↥K, n⁻¹ * ψ k * n ∈ K0G := by
    intro k
    have hk : ψ k ∈ KM := by
      rw [← hmapK]
      exact mem_map_of_mem _ k.2
    obtain ⟨m, hm, hme⟩ := hk
    have e : n⁻¹ * ψ k * n = m := by
      rw [← hme]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hm
  let ι : ↥K →* ↥K0G :=
    { toFun := fun k => ⟨n⁻¹ * ψ k * n, hmem k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k l => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]
        group) }
  have hιs : Function.Surjective ι := by
    intro y
    have hy : ψ.symm (n * y * n⁻¹) ∈ K := ⟨n * y * n⁻¹, ⟨y, y.2, rfl⟩, rfl⟩
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    show n⁻¹ * ψ (ψ.symm (n * y * n⁻¹)) * n = y
    rw [MulEquiv.apply_symm_apply]
    group
  refine ⟨K, ?_, ?_, ?_, actK.comp ι, ?_, ?_⟩
  · apply hinj
    rw [map_centralizer_singleton_equiv, h1, Subgroup.map_sup, MonoidHom.map_zpowers, hmapK]
    rfl
  · apply hinj
    rw [Subgroup.map_inf_eq _ _ _ ψ.injective, MonoidHom.map_zpowers, hmapK, Subgroup.map_bot]
    exact h2
  · intro z hz
    have hz' : ψ z ∈ zpowers zG := (Sec13.ON134.mem_center_iff_model ψ).1 hz
    have hzK : ψ z ∈ KM := zpowers_le.mpr hzKM hz'
    rw [← hmapK] at hzK
    obtain ⟨k, hk, hke⟩ := hzK
    rwa [← ψ.injective hke]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hιs, ← MonoidHom.range_eq_map,
      range_actK]
  · intro k
    have hcz : ∀ j : ℤ, n⁻¹ * zG ^ j * n = zG ^ j := fun j => by
      rw [mul_assoc, (Commute.zpow_left (zG_central n) j).eq, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have hcz' : ∀ j : ℤ, n * zG ^ j * n⁻¹ = zG ^ j := fun j => by
      rw [(Commute.zpow_left (zG_central n) j).eq.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_actK, Sec13.ON134.mem_center_iff_model ψ]
    constructor
    · intro hk
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk
      have hj' : zG ^ j = n⁻¹ * ψ k * n := congrArg Subtype.val hj
      refine mem_zpowers_iff.mpr ⟨j, ?_⟩
      have e : ψ k = n * (n⁻¹ * ψ k * n) * n⁻¹ := by group
      rw [e, ← hj', hcz']
    · intro hk
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk
      refine mem_zpowers_iff.mpr ⟨j, Subtype.ext ?_⟩
      show zG ^ j = n⁻¹ * ψ k * n
      rw [← hj, hcz]

theorem isPerfect_of_centralizer_eq
    [Finite X] (ψ : X ≃* GM) (hZ3 : Nat.card (center X) = 3)
    {b : X} (hb3 : b ^ 3 = 1) (hbz : b ∉ center X) {K : Subgroup X}
    (hKb : K ≤ centralizer ({b} : Set X)) (hbK : zpowers b ⊓ K = ⊥) (hZK : center X ≤ K)
    {ρ : ↥K →* Perm (Fin 6)} (hρ : ρ.range = alternatingGroup (Fin 6))
    (hker : ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X) : Group.IsPerfect ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := commutator ↥K with hD
  have hDmap : D.map ρ = alternatingGroup (Fin 6) := by
    rw [hD, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hρ,
      commutator_alternatingGroup_eq_self (by simp)]
  have hDρ : ∀ σ ∈ alternatingGroup (Fin 6), ∃ d ∈ D, ρ d = σ := by
    intro σ hσ
    rw [← hDmap] at hσ
    obtain ⟨d, hd, rfl⟩ := hσ
    exact ⟨d, hd, rfl⟩
  refine ⟨?_⟩
  by_contra hne
  have hZD : ∀ k ∈ D, (k : X) ∈ center X → k = 1 := by
    intro k hkD hkZ
    by_contra hk1
    apply hne
    rw [eq_top_iff]
    intro y _
    have hρy : ρ y ∈ alternatingGroup (Fin 6) := hρ ▸ ⟨y, rfl⟩
    obtain ⟨d, hd, hdy⟩ := hDρ _ hρy
    have hc : ((d⁻¹ * y : ↥K) : X) ∈ center X := by
      rw [← hker, map_mul, map_inv, hdy, inv_mul_cancel]
    have hZK3 : Nat.card ((center X).subgroupOf K) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ3]
    have hkZ' : k ∈ (center X).subgroupOf K := Subgroup.mem_subgroupOf.mpr hkZ
    have hzp : zpowers k = (center X).subgroupOf K := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hkZ')
      rw [hZK3, Nat.card_zpowers]
      have hk3 : k ^ 3 = 1 := by
        have h := pow_card_eq_one' (G := (center X).subgroupOf K) (x := ⟨k, hkZ'⟩)
        rw [hZK3] at h
        exact congrArg Subtype.val h
      rw [orderOf_eq_prime hk3 hk1]
    have hm : d⁻¹ * y ∈ zpowers k := hzp ▸ Subgroup.mem_subgroupOf.mpr hc
    have hmD : d⁻¹ * y ∈ D := zpowers_le.mpr hkD hm
    have e : y = d * (d⁻¹ * y) := by group
    rw [e]
    exact mul_mem hd hmD
  have hf1 : KFacts.K412.fOne ∈ alternatingGroup (Fin 6) :=
    KFacts.K412.eSix_le_alternatingGroup KFacts.K412.fOne_mem_eSix
  have hf2 : KFacts.K412.fTwo ∈ alternatingGroup (Fin 6) :=
    KFacts.K412.eSix_le_alternatingGroup KFacts.K412.fTwo_mem_eSix
  obtain ⟨d₁, hd₁D, hd₁⟩ := hDρ _ hf1
  obtain ⟨d₂, hd₂D, hd₂⟩ := hDρ _ hf2
  have hinjD : ∀ u ∈ D, ρ u = 1 → u = 1 := fun u hu h1 => hZD u hu ((hker u).mp h1)
  have hd₁3 : d₁ ^ 3 = 1 := hinjD _ (pow_mem hd₁D 3) (by
    rw [map_pow, hd₁]
    decide +kernel)
  have hd₂3 : d₂ ^ 3 = 1 := hinjD _ (pow_mem hd₂D 3) (by
    rw [map_pow, hd₂]
    decide +kernel)
  have hd₁₂ : d₁ * d₂ = d₂ * d₁ := by
    have h := hinjD (d₁ * d₂ * d₁⁻¹ * d₂⁻¹)
      (mul_mem (mul_mem (mul_mem hd₁D hd₂D) (inv_mem hd₁D)) (inv_mem hd₂D)) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hd₁, hd₂]
        decide +kernel)
    calc d₁ * d₂ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ * (d₂ * d₁) := by group
      _ = d₂ * d₁ := by rw [h, one_mul]
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    rw [h, map_one] at hd₁
    exact absurd hd₁.symm (by decide +kernel)
  have hd₂n : d₂ ∉ zpowers d₁ := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' := congrArg ρ hk
    rw [map_zpow, hd₁, hd₂] at hk'
    have hord : orderOf KFacts.K412.fOne = 3 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hk'
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k % 3 = m := ⟨(k % 3).toNat, (Int.toNat_of_nonneg h0).symm⟩
    rw [hm, zpow_natCast] at hk'
    have hm3 : m < 3 := by omega
    interval_cases m <;> exact absurd hk' (by decide +kernel)
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ center X, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : center X = ⊥ := eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr (hcon z hz)
    rw [hbot, Subgroup.card_bot] at hZ3
    omega
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := center X) (x := ⟨z, hzZ⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  set e₁ : X := (d₁ : X) with he₁
  set e₂ : X := (d₂ : X) with he₂
  have he₁3 : e₁ ^ 3 = 1 := by rw [he₁, ← Subgroup.coe_pow, hd₁3, Subgroup.coe_one]
  have he₂3 : e₂ ^ 3 = 1 := by rw [he₂, ← Subgroup.coe_pow, hd₂3, Subgroup.coe_one]
  have he₁1 : e₁ ≠ 1 := fun h => hd₁1 (Subtype.ext h)
  have he₂1 : e₂ ≠ 1 := fun h => hd₂n (by
    rw [show d₂ = 1 from Subtype.ext h]
    exact one_mem _)
  have he₁₂ : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val hd₁₂
  have hW0c : IsMulCommutative (zpowers e₁) := inferInstance
  have hW03 : ∀ w ∈ zpowers e₁, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he₁3, one_zpow]
  have he₂W0 : e₂ ∈ centralizer (zpowers e₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_left he₁₂ k).eq
  have he₂n : e₂ ∉ zpowers e₁ := by
    intro h
    apply hd₂n
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  obtain ⟨h9, h9c, h93⟩ := card_sup_zpowers_three hW0c hW03 he₂W0 he₂3 he₂1 he₂n
  have hW1D : zpowers e₁ ⊔ zpowers e₂ ≤ D.map K.subtype :=
    sup_le (zpowers_le.mpr ⟨d₁, hd₁D, rfl⟩) (zpowers_le.mpr ⟨d₂, hd₂D, rfl⟩)
  have hzW1 : z ∉ zpowers e₁ ⊔ zpowers e₂ := by
    intro h
    obtain ⟨u, huD, hu⟩ := hW1D h
    have hu' : (u : X) ∈ center X := by
      rw [show (u : X) = z from hu]
      exact hzZ
    have h1 := hZD u huD hu'
    apply hz1
    rw [← show (u : X) = z from hu, h1]
    rfl
  have hzW1c : z ∈ centralizer ((zpowers e₁ ⊔ zpowers e₂ : Subgroup X) : Set X) :=
    mem_centralizer_iff.mpr fun w _ => mem_center_iff.mp hzZ w
  obtain ⟨h27, h27c, h273⟩ := card_sup_zpowers_three h9c h93 hzW1c hz3 hz1 hzW1
  have hW2K : zpowers e₁ ⊔ zpowers e₂ ⊔ zpowers z ≤ K :=
    sup_le (sup_le (zpowers_le.mpr d₁.2) (zpowers_le.mpr d₂.2)) (zpowers_le.mpr (hZK hzZ))
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  have hbW2 : b ∉ zpowers e₁ ⊔ zpowers e₂ ⊔ zpowers z := by
    intro h
    have hbb : b ∈ zpowers b ⊓ K := ⟨mem_zpowers b, hW2K h⟩
    rw [hbK] at hbb
    exact hb1 hbb
  have hbW2c :
      b ∈ centralizer ((zpowers e₁ ⊔ zpowers e₂ ⊔ zpowers z : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hKb (hW2K hw))
  obtain ⟨h81, h81c, h813⟩ := card_sup_zpowers_three h27c h273 hbW2c hb3 hb1 hbW2
  have hp3 : IsPGroup 3 (zpowers e₁ ⊔ zpowers e₂ ⊔ zpowers z ⊔ zpowers b : Subgroup X) :=
    fun w => ⟨1, Subtype.ext (by simpa using h813 _ w.2)⟩
  have hle := card_le_27_of_comm ψ hp3 fun u hu v hv =>
    congrArg Subtype.val (h81c.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  rw [h81, h27, h9, Nat.card_zpowers, orderOf_eq_three he₁3 he₁1] at hle
  norm_num at hle

end Model

end CFSG.RankThree.PartTwo.Sec15.Proof156Res4
