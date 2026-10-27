module

public import CFSG.Quasithin.EmptyFaithful.LRed5Plumb

public section

namespace CFSG.Quasithin

namespace LRed5

section FFCase3

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_isFFModule_simple_of_isHTM
    (h56 : AsB56) {T M : Subgroup G} (S : Setting146 G T M)
    {H : Subgroup G} (hHTM : IsHTM T M H)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKnorm : (K.subgroupOf H).Normal) (hHeq : H = K ⊔ T)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (ρ : ↥H →* MulAut W)
    (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H)
    (hff : IsFFModule ρ.range) : False := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hHTM.1.1
  have hsqtk : SQTKGroup ↥H := S.sqtkGroup_of_isHTM hHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hS' : IsSimpleGroup (KBar K) := (c19 _ hHTM).2 K hK
  obtain ⟨hKL, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  set s' : ↥H := ⟨s, hTH hsT⟩ with hs'
  set Γ := ρ.range with hΓ
  set L := (K.subgroupOf H).map ρ with hL
  obtain ⟨e⟩ := kbar_equiv_image hK ρ hker
  have hLsimple : IsSimpleGroup ↥L := e.symm.isSimpleGroup
  have hLΓ : L ≤ Γ := Subgroup.map_le_range ρ _
  have hn : (L.subgroupOf Γ).Normal := by
    have hrs : L.subgroupOf Γ = (K.subgroupOf H).map ρ.rangeRestrict := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hrs]
    exact hKnorm.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  set T₀ := (T.subgroupOf H).map ρ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ρ
  have hT₀Γ : T₀ ≤ Γ := Subgroup.map_le_range ρ _
  have hΓeq : Γ = L ⊔ T₀ := by
    have h1 : (K.subgroupOf H) ⊔ (T.subgroupOf H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHeq]
      exact Subgroup.subgroupOf_self _
    rw [hΓ, MonoidHom.range_eq_map, ← h1, Subgroup.map_sup]
  have hO2 : pCoreOf 2 Γ = ⊥ := pCoreOf_range_eq_bot ρ hker
  have hnc : ¬ IsMulCommutative ↥L := by
    intro hc
    apply not_isMulCommutative_kbar hK
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact mul_comm' _ _)⟩⟩
  have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
    intro x hx hxc
    have : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun z => Subtype.ext (hxc z z.2).symm
    rw [hcenter, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hC := centralizer_eq_bot_of_two_quotient hLΓ hn hZ hT₀Γ hT₀2 hΓeq hO2
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have hpKbar : Group.IsPerfect (KBar K) := inferInstance
  have hperfL : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hnc' : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc ⟨⟨fun a b => h a b⟩⟩
  have hq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_simple_nonabelian hperfL hnc'
  have hcard : Nat.card ↥L = 168 ∨ Nat.card ↥L = 360 := by
    rw [← Nat.card_congr e.toEquiv]
    rcases hKL with he3 | he6
    · left
      obtain ⟨e3⟩ := he3
      rw [Nat.card_congr e3.toEquiv]
      exact card_sl3_zmod
    · right
      obtain ⟨e6⟩ := he6
      rw [Nat.card_congr e6.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial]
  have hQ : G64.IsQuotientOfSQTKCat ↥Γ :=
    ⟨↥H, inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hsqtk,
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  have hoff : ∃ A : Subgroup (MulAut W), IsFFStarOffender Γ A := B6.exists_isFFStarOffender hff
  have hsΓ : ρ s' ∈ Γ := ⟨s', rfl⟩
  have hout168 : Nat.card ↥L = 168 →
      ¬ ∃ g ∈ L, ∀ x ∈ L, ρ s' * x * (ρ s')⁻¹ = g * x * g⁻¹ := by
    intro h168
    rcases hdyn with ⟨-, hout⟩ | ⟨he6, -⟩
    · exact outer_transfer hK ρ hker hsK hout
    · exfalso
      obtain ⟨e6⟩ := he6
      rw [← Nat.card_congr e.toEquiv, Nat.card_congr e6.toEquiv,
        card_alternatingGroup1527d 6 (by norm_num)] at h168
      norm_num [Nat.factorial] at h168
  have hout360 : Nat.card ↥L = 360 → ∃ y ∈ L, y ^ 3 = 1 ∧ y ≠ 1 ∧
      ∀ g ∈ L, ρ s' * y * (ρ s')⁻¹ ≠ g * y * g⁻¹ := by
    intro h360
    rcases hdyn with ⟨he3, -⟩ | ⟨-, hf⟩
    · exfalso
      obtain ⟨e3⟩ := he3
      rw [← Nat.card_congr e.toEquiv, Nat.card_congr e3.toEquiv, card_sl3_zmod] at h360
      omega
    · exact fuse_transfer hK ρ hker hsK hf
  have hV : ∀ v : W, v * v = 1 := fun v => by rw [← sq]; exact hW v
  exact false_of_simple_outer h56 hV hQ hLΓ hn hC hq hcard hoff hsΓ hout168 hout360

end FFCase3

end LRed5

section Case3

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem hasNoFaithfulFF_conjClosure_sup_of_normal
    (h56 : AsB56) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (S : Setting146 G T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    {K : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (hnK : mcOf T ≤ Subgroup.normalizer (K : Set G)) :
    HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 (conjClosure K T ⊔ T)) := by
  have hHTM' : IsHTM T M (conjClosure K T ⊔ T) := S.isHTM_conjClosure_sup h37 h38 hK
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hTH : T ≤ mcOf T := (S.isHTM_mcOf).1.1
  have hHle : conjClosure K T ⊔ T ≤ mcOf T := conjClosure_sup_le hKH hTH
  have hK₀ : conjClosure K T = K := by
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hnK (hTH ht)) z).mp hz
    · exact le_conjClosure K T
  have hKH' : K ≤ conjClosure K T ⊔ T := (le_conjClosure K T).trans le_sup_left
  have hK' : K ∈ cComp (conjClosure K T ⊔ T) := cComp_mem_of_le hK hKH' hHle
  have hKnorm : (K.subgroupOf (conjClosure K T ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH').2 (hHle.trans hnK)
  intro W _ _ hW ρ hker hff
  exact LRed5.false_of_isFFModule_simple_of_isHTM h56 S hHTM' c19 c20 hK' hKnorm
    (by rw [hK₀]) hW ρ hker hff

end Case3

end CFSG.Quasithin
