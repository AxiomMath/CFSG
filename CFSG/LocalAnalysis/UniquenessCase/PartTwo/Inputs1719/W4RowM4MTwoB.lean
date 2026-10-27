module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Chain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4MLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4HeisIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup ArithmeticFunction

private theorem m4_orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (x := (2 : ZMod 3)) (p := 2) (by decide) (by decide)

theorem two_pow_four_le_index_of_twoB {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup CFSG.Blueprint.NativeSporadic.B] (ι : G →* MulAut W)
    (hι : Function.Injective ι) {a t : G} (ha2 : orderOf a = 2) (ht2 : orderOf t = 2)
    (hat : a * t = t * a) (hne : t ≠ a)
    (hA : CFSG.Monster.Existence.IsTwoACentralizer a)
    (hΩ : cardFactors (Nat.card ↥(Subgroup.centralizer ({a} : Set G))) ≤ 70)
    (hB : ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.B)
      (z u : CFSG.Blueprint.NativeSporadic.B), HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
        u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) ∧
        u ∉ Subgroup.zpowers z ∧ IsConj u z) :
    2 ^ 4 ≤ (fixV (zpowers (ι t))).index := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective
  let K : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have hmemt : t ∈ K := by
    change t ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hat.symm
  have hKperf : Group.IsPerfect ↥K := hA.1
  have hcenter : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers a := hA.2.1
  have hAe : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* CFSG.Blueprint.NativeSporadic.B) :=
    hA.2.2
  obtain ⟨e⟩ := hAe
  let π : ↥K →* CFSG.Blueprint.NativeSporadic.B :=
    { toFun := fun k => e (QuotientGroup.mk' (Subgroup.center ↥K) k)
      map_one' := by simp
      map_mul' := by intro p q; simp only [map_mul] }
  have hker_eq : π.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hk' : e (QuotientGroup.mk' (Subgroup.center ↥K) k) = 1 := hk
      have h1 : QuotientGroup.mk' (Subgroup.center ↥K) k = 1 :=
        e.injective (by rw [hk', map_one])
      have h2 : k ∈ (QuotientGroup.mk' (Subgroup.center ↥K)).ker := MonoidHom.mem_ker.2 h1
      rwa [QuotientGroup.ker_mk'] at h2
    · intro hk
      have h2 : QuotientGroup.mk' (Subgroup.center ↥K) k = 1 := by
        have h1 : k ∈ (QuotientGroup.mk' (Subgroup.center ↥K)).ker := by
          rwa [QuotientGroup.ker_mk']
        exact MonoidHom.mem_ker.1 h1
      show e (QuotientGroup.mk' (Subgroup.center ↥K) k) = 1
      rw [h2, map_one]
  have hπ_surj : Function.Surjective π := by
    intro b
    obtain ⟨q, rfl⟩ := e.surjective b
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) q
    exact ⟨k, rfl⟩
  have ht_ne_one : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hπt : π ⟨t, hmemt⟩ ≠ 1 := by
    intro h1
    have hker : (⟨t, hmemt⟩ : ↥K) ∈ π.ker := MonoidHom.mem_ker.2 h1
    rw [hker_eq] at hker
    have hmem_zp : t ∈ Subgroup.zpowers a := by
      have h2 : t ∈ (Subgroup.center ↥K).map K.subtype :=
        ⟨⟨t, hmemt⟩, hker, rfl⟩
      rwa [hcenter] at h2
    rw [Subgroup.mem_zpowers_iff] at hmem_zp
    obtain ⟨k, hk⟩ := hmem_zp
    have hmod : a ^ (k % (2 : ℤ)) = t := by
      have h1 : a ^ (k % (orderOf a : ℤ)) = t := by
        rw [zpow_mod_orderOf a k]
        exact hk
      rwa [ha2] at h1
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · rw [hk0, zpow_zero] at hmod
      exact ht_ne_one hmod.symm
    · rw [hk1, zpow_one] at hmod
      exact hne hmod.symm
  have htop : Subgroup.closure {v : ↥K | ∃ k : ↥K, v = k * (⟨t, hmemt⟩ : ↥K) * k⁻¹} = ⊤ :=
    closure_conj_eq_top_of_perfect_cover hKperf π hπ_surj hker_eq.le hπt
  let Φ : ↥K →* MulAut W := ι.comp K.subtype
  have hΦinj : Function.Injective Φ := hι.comp K.subtype_injective
  let K' : Subgroup (MulAut W) := K.map ι
  let s : Set ↥K := {v | ∃ k : ↥K, v = k * (⟨t, hmemt⟩ : ↥K) * k⁻¹}
  have htop_s : Subgroup.closure s = ⊤ := htop
  have hrange : Φ.range = K' := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_map_of_mem ι k.2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsubset : Φ '' s ⊆ (fun h : MulAut W => h * ι t * h⁻¹) '' (K' : Set (MulAut W)) := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨k, rfl⟩ := hv
    refine ⟨Φ k, Subgroup.mem_map_of_mem ι k.2, ?_⟩
    show Φ k * ι t * (Φ k)⁻¹ = Φ (k * (⟨t, hmemt⟩ : ↥K) * k⁻¹)
    rw [map_mul, map_mul, map_inv]
    rfl
  have hL : K' ≤ Subgroup.closure ((fun h : MulAut W => h * ι t * h⁻¹) '' K') := by
    have hEq : K' = Subgroup.closure (Φ '' s) := by
      rw [← hrange]
      calc Φ.range = (⊤ : Subgroup ↥K).map Φ := MonoidHom.range_eq_map Φ
        _ = (Subgroup.closure s).map Φ := by rw [← htop_s]
        _ = Subgroup.closure (Φ '' s) := MonoidHom.map_closure Φ s
    exact hEq.le.trans (Subgroup.closure_mono hsubset)
  have hf : ∀ h ∈ K', (fun h : MulAut W => h * ι t * h⁻¹) h ∈ K' := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
    have hmul : k * t * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hmemt) (K.inv_mem hk)
    have heq : ι k * ι t * (ι k)⁻¹ = ι (k * t * k⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    show ι k * ι t * (ι k)⁻¹ ∈ K'
    rw [heq]
    exact Subgroup.mem_map_of_mem ι hmul
  obtain ⟨hs, hlen, hclos⟩ := exists_list_le_closure K' K'
    (fun h : MulAut W => h * ι t * h⁻¹) hf hL
  have hcardK' : Nat.card K' = Nat.card ↥K := by
    show Nat.card (K.map ι) = Nat.card ↥K
    exact Subgroup.card_map_of_injective (K := K) (f := ι) hι
  have hlen70 : hs.length ≤ 70 := by
    rw [hcardK'] at hlen
    exact hlen.trans hΩ
  have hchain : (fixV K').index ≤ (fixV (zpowers (ι t))).index ^ 70 := by
    calc (fixV K').index
        ≤ (fixV (Subgroup.closure {y | ∃ h ∈ hs, y = h * ι t * h⁻¹})).index :=
          index_fixV_le_of_le hclos
      _ ≤ (fixV (Subgroup.zpowers (ι t))).index ^ hs.length :=
          B42Disp.index_fixV_closure_conj_elt_le (ι t) hs
      _ ≤ (fixV (Subgroup.zpowers (ι t))).index ^ 70 :=
          Nat.pow_le_pow_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hlen70
  obtain ⟨x, y, z, u, hHeis, hy, hu, huz, hconj⟩ := hB
  have hc2 : Nat.card (Subgroup.center ↥K) = 2 := by
    rw [← Subgroup.card_map_of_injective (K := Subgroup.center ↥K) (f := K.subtype)
      K.subtype_injective, hcenter, Nat.card_zpowers, ha2]
  obtain ⟨x', y', z', u', hHeis', hy', hu', huz', hconj'⟩ :=
    exists_lift_noncentral_isConj π hπ_surj hker_eq hc2 hHeis hy hu huz hconj
  have hz'ne : Φ z' ≠ 1 := fun hz => hHeis'.z1 (hΦinj (by rw [hz, map_one]))
  have hHeis'' : HeisCfg 3 4 (fun i => Φ (x' i)) (fun i => Φ (y' i)) (Φ z') :=
    HeisCfg.map Φ hHeis' hz'ne
  have hy'' : ∀ i, Φ (y' i) ^ 3 = 1 := fun i => by rw [← map_pow, hy' i, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbound : 2 ^ (3 ^ 4 * orderOf (2 : ZMod 3)) ≤
      Nat.card (CFSG.QuasithinUnique.Setup.X1.imgT (Φ z')) :=
    two_pow_le_card_imgT_of_heisCfg (p := 3) (n := 4) hW (by norm_num) hHeis''
  have hord : orderOf (2 : ZMod 3) = 2 := m4_orderOf_two_zmod_three
  have hbound' : 2 ^ 162 ≤ Nat.card (CFSG.QuasithinUnique.Setup.X1.imgT (Φ z')) := by
    have hexp : 3 ^ 4 * 2 = 162 := by norm_num
    simpa only [hord, hexp] using hbound
  have hcard :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.index_fixV_zpowers_eq_card_imgT
      (W := W) (Φ z')
  have hz162 : 2 ^ 162 ≤ (fixV (Subgroup.zpowers (Φ z'))).index := by
    rw [hcard]; exact hbound'
  have hxr : Φ '' Set.range x' = Set.range (fun i => Φ (x' i)) :=
    (Set.range_comp' Φ x').symm
  have hyr : Φ '' Set.range y' = Set.range (fun i => Φ (y' i)) :=
    (Set.range_comp' Φ y').symm
  have himg : Φ '' (Set.range x' ∪ Set.range y' ∪ {z'}) =
      Set.range (fun i => Φ (x' i)) ∪ Set.range (fun i => Φ (y' i)) ∪ {Φ z'} := by
    rw [Set.image_union, Set.image_union, Set.image_singleton, hxr, hyr]
  have hu'' : Φ u' ∈ Subgroup.closure
      (Set.range (fun i => Φ (x' i)) ∪ Set.range (fun i => Φ (y' i)) ∪ {Φ z'}) := by
    have h1 : Φ u' ∈ (Subgroup.closure (Set.range x' ∪ Set.range y' ∪ {z'})).map Φ :=
      Subgroup.mem_map_of_mem Φ hu'
    rwa [MonoidHom.map_closure, himg] at h1
  have huz'' : Φ u' ∉ Subgroup.zpowers (Φ z') := by
    intro hmem
    apply huz'
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hΦinj (by rw [map_zpow, hk])⟩
  have hconj'' : ∃ g : MulAut W, g * Φ z' * g⁻¹ = Φ u' := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj'
    refine ⟨(Φ c)⁻¹, ?_⟩
    rw [← hc]
    simp only [map_mul, map_inv]
    group
  have hE3 : 2 ^ (4 * 162) ≤
      (fixV (Subgroup.zpowers (Φ u') ⊔ Subgroup.zpowers (Φ z'))).index ^ 3 :=
    two_pow_four_mul_le_index_cube_of_heis_conj hW hHeis'' hy'' hz162 hu'' huz'' hconj''
  have hEK' : Subgroup.zpowers (Φ u') ⊔ Subgroup.zpowers (Φ z') ≤ K' := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map_of_mem ι u'.2
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map_of_mem ι z'.2
  have hIdxE : (fixV (Subgroup.zpowers (Φ u') ⊔ Subgroup.zpowers (Φ z'))).index ≤
      (fixV K').index :=
    index_fixV_le_of_le hEK'
  obtain ⟨m, hm⟩ :=
    CFSG.QuasithinUnique.Setup.X1.index_fixV_eq_two_pow hW (Subgroup.zpowers (ι t))
  have hpow : 2 ^ (4 * 162) ≤ (fixV (zpowers (ι t))).index ^ 210 := by
    calc 2 ^ (4 * 162)
        ≤ (fixV (Subgroup.zpowers (Φ u') ⊔ Subgroup.zpowers (Φ z'))).index ^ 3 := hE3
      _ ≤ (fixV K').index ^ 3 := Nat.pow_le_pow_left hIdxE 3
      _ ≤ ((fixV (zpowers (ι t))).index ^ 70) ^ 3 := Nat.pow_le_pow_left hchain 3
      _ = (fixV (zpowers (ι t))).index ^ 210 := by rw [← pow_mul]
  rw [hm] at hpow
  rw [← pow_mul] at hpow
  have h648 : 4 * 162 ≤ m * 210 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow
  have hm4 : 4 ≤ m := by omega
  calc 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    _ = (fixV (zpowers (ι t))).index := hm.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
