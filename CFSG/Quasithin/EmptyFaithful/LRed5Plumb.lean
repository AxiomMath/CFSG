module

public import CFSG.Quasithin.EmptyFaithful.LRed5Quot
public import CFSG.Quasithin.EmptyFaithful.LRed5Simple
public import CFSG.Quasithin.EmptyFaithful.F918C18
public import CFSG.Quasithin.Background.A3StructureListNative

public section

namespace CFSG.Quasithin

namespace LRed5

section PlumbFile

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

theorem isQuasisimple_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hperf : Group.IsPerfect X) (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) :=
    (QuotientGroup.quotientBot (G := X)).isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient ⊥ bot_le hperf hs ?_
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
  have h' : (QuotientGroup.mk (a * b) : X ⧸ (⊥ : Subgroup X)) = QuotientGroup.mk (b * a) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h
  rw [QuotientGroup.eq, Subgroup.mem_bot, inv_mul_eq_one] at h'
  exact h'

variable {G : Type} [Group G] [Finite G]

theorem ker_comp_inclusion {H K : Subgroup G} (hK : K ∈ cComp H) {W : Type} [CommGroup W]
    (ρ : ↥H →* MulAut W) (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) (k : ↥K) :
    ρ (Subgroup.inclusion (le_of_mem_cComp hK) k) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hker]
  constructor
  · intro h
    have hN : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
      refine le_pCoreOf 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_inf_right)
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (le_of_mem_cComp hK g.2)) n).mp hn.2
      simpa using this
    exact hN ⟨k.2, h⟩
  · intro h
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) h

theorem kbar_equiv_image {H K : Subgroup G} (hK : K ∈ cComp H) {W : Type} [CommGroup W]
    (ρ : ↥H →* MulAut W) (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    Nonempty (KBar K ≃* ↥((K.subgroupOf H).map ρ)) := by
  have hKH := le_of_mem_cComp hK
  let ρK : ↥K →* MulAut W := ρ.comp (Subgroup.inclusion hKH)
  have hrange : ρK.range = (K.subgroupOf H).map ρ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkerK : ρK.ker = (pCoreOf 2 K).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ker_comp_inclusion hK ρ hker k
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerK.symm).trans
    ((QuotientGroup.quotientKerEquivRange ρK).trans (MulEquiv.subgroupCongr hrange))⟩

end PlumbFile

section Transfer

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_of_mem_map {H K : Subgroup G} {W : Type} [CommGroup W] (ρ : ↥H →* MulAut W)
    {g : MulAut W} (hg : g ∈ (K.subgroupOf H).map ρ) :
    ∃ (k : ↥H), (k : G) ∈ K ∧ ρ k = g := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨k, hk, rfl⟩

theorem outer_transfer {H K : Subgroup G} (hK : K ∈ cComp H) {W : Type} [CommGroup W]
    (ρ : ↥H →* MulAut W) (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {s : ↥H}
    (hsK : (s : G) ∈ Subgroup.normalizer (K : Set G)) (hout : KbarInducesOuter K (s : G)) :
    ¬ ∃ g ∈ (K.subgroupOf H).map ρ, ∀ x ∈ (K.subgroupOf H).map ρ,
      ρ s * x * (ρ s)⁻¹ = g * x * g⁻¹ := by
  rintro ⟨g, hg, hx⟩
  obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hg
  have hKH := le_of_mem_cComp hK
  have hk₁ : (s : G)⁻¹ * k * s ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsK) (k : G)).mp hkK
    simpa using this
  obtain ⟨x, hxK, hxn⟩ := hout _ hk₁
  have hcs : (s : G) * ((s : G)⁻¹ * k * s)⁻¹ = (k : G)⁻¹ * s := by group
  rw [hcs] at hxn
  have hcN : (k : G)⁻¹ * s ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hkK)) hsK
  have hmem : ⁅(k : G)⁻¹ * s, x⁆ ∈ K := by
    rw [commutatorElement_def]
    refine K.mul_mem ?_ (K.inv_mem hxK)
    exact (Subgroup.mem_normalizer_iff.mp hcN x).mp hxK |> fun h => by
      simpa [mul_assoc] using h
  set x' : ↥H := ⟨x, hKH hxK⟩ with hx'
  have hρx : ρ x' ∈ (K.subgroupOf H).map ρ := Subgroup.mem_map_of_mem ρ hxK
  have h1 := hx _ hρx
  have h2 : ρ (k⁻¹ * s * x' * (k⁻¹ * s)⁻¹ * x'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc (ρ k)⁻¹ * ρ s * ρ x' * ((ρ s)⁻¹ * ρ k) * (ρ x')⁻¹
        = (ρ k)⁻¹ * (ρ s * ρ x' * (ρ s)⁻¹) * ρ k * (ρ x')⁻¹ := by group
      _ = (ρ k)⁻¹ * (ρ k * ρ x' * (ρ k)⁻¹) * ρ k * (ρ x')⁻¹ := by rw [h1]
      _ = 1 := by group
  have h3 : ρ (Subgroup.inclusion hKH ⟨⁅(k : G)⁻¹ * s, x⁆, hmem⟩) = 1 := by
    have : Subgroup.inclusion hKH ⟨⁅(k : G)⁻¹ * s, x⁆, hmem⟩ = k⁻¹ * s * x' * (k⁻¹ * s)⁻¹ * x'⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def, hx'])
    rw [this]
    exact h2
  exact hxn ((ker_comp_inclusion hK ρ hker ⟨_, hmem⟩).1 h3)

theorem fuse_transfer {H K : Subgroup G} (hK : K ∈ cComp H) {W : Type} [CommGroup W]
    (ρ : ↥H →* MulAut W) (hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {s : ↥H}
    (hsK : (s : G) ∈ Subgroup.normalizer (K : Set G)) (hf : KbarFusesThrees K (s : G)) :
    ∃ y ∈ (K.subgroupOf H).map ρ, y ^ 3 = 1 ∧ y ≠ 1 ∧
      ∀ g ∈ (K.subgroupOf H).map ρ, ρ s * y * (ρ s)⁻¹ ≠ g * y * g⁻¹ := by
  obtain ⟨x, hxK, hx3, hxn, hfuse⟩ := hf
  have hKH := le_of_mem_cComp hK
  set x' : ↥H := ⟨x, hKH hxK⟩ with hx'
  refine ⟨ρ x', Subgroup.mem_map_of_mem ρ hxK, ?_, ?_, ?_⟩
  · have h3 : ρ (Subgroup.inclusion hKH ⟨x ^ 3, K.pow_mem hxK 3⟩) = 1 :=
      (ker_comp_inclusion hK ρ hker ⟨x ^ 3, K.pow_mem hxK 3⟩).2 hx3
    have : Subgroup.inclusion hKH ⟨x ^ 3, K.pow_mem hxK 3⟩ = x' ^ 3 := Subtype.ext (by simp [hx'])
    rw [this, map_pow] at h3
    exact h3
  · intro h
    exact hxn ((ker_comp_inclusion hK ρ hker ⟨x, hxK⟩).1 h)
  · intro g hg hcon
    obtain ⟨k, hkK, rfl⟩ := exists_of_mem_map ρ hg
    have hz : ρ ((k * x' * k⁻¹)⁻¹ * (s * x' * s⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcon]
      group
    have hmem : ((k : G) * x * (k : G)⁻¹)⁻¹ * ((s : G) * x * (s : G)⁻¹) ∈ K := by
      refine K.mul_mem (K.inv_mem (K.mul_mem (K.mul_mem hkK hxK) (K.inv_mem hkK))) ?_
      have := (Subgroup.mem_normalizer_iff.mp hsK x).mp hxK
      exact this
    have h4 : ρ (Subgroup.inclusion hKH ⟨((k : G) * x * (k : G)⁻¹)⁻¹ * ((s : G) * x * (s : G)⁻¹), hmem⟩) = 1 := by
      have : Subgroup.inclusion hKH ⟨((k : G) * x * (k : G)⁻¹)⁻¹ * ((s : G) * x * (s : G)⁻¹), hmem⟩ =
          (k * x' * k⁻¹)⁻¹ * (s * x' * s⁻¹) := Subtype.ext (by simp [hx'])
      rw [this]
      exact hz
    exact hfuse (k : G) hkK ((ker_comp_inclusion hK ρ hker ⟨_, hmem⟩).1 h4)

end Transfer

section MainSimple

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_sl3_zmod : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv]
  rw [card_statedSL_three1527d, Nat.card_zmod]
  norm_num

theorem false_of_isFFModule_simple
    (h56 : AsB56) {T M : Subgroup G} (S : Setting146 G T M)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M) {K : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (hKnorm : (K.subgroupOf (mcOf T)).Normal) (hHeq : mcOf T = K ⊔ T)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (ρ : ↥(mcOf T) →* MulAut W)
    (hker : ∀ x : ↥(mcOf T), ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 (mcOf T))
    (hff : IsFFModule ρ.range) : False := by
  classical
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hsqtk : SQTKGroup ↥(mcOf T) := S.sqtkGroup_of_isHTM hHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hS' : IsSimpleGroup (KBar K) := (c19 _ hHTM).2 K hK
  obtain ⟨hKL, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  set s' : ↥(mcOf T) := ⟨s, hTH hsT⟩ with hs'
  set Γ := ρ.range with hΓ
  set L := (K.subgroupOf (mcOf T)).map ρ with hL
  obtain ⟨e⟩ := kbar_equiv_image hK ρ hker
  have hLsimple : IsSimpleGroup ↥L := e.symm.isSimpleGroup
  have hLΓ : L ≤ Γ := Subgroup.map_le_range ρ _
  have hn : (L.subgroupOf Γ).Normal := by
    have hrs : L.subgroupOf Γ = (K.subgroupOf (mcOf T)).map ρ.rangeRestrict := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hrs]
    exact hKnorm.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  set T₀ := (T.subgroupOf (mcOf T)).map ρ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ρ
  have hT₀Γ : T₀ ≤ Γ := Subgroup.map_le_range ρ _
  have hΓeq : Γ = L ⊔ T₀ := by
    have h1 : (K.subgroupOf (mcOf T)) ⊔ (T.subgroupOf (mcOf T)) = ⊤ := by
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
    ⟨↥(mcOf T), inferInstance, inferInstance, ρ.ker, inferInstance, SQTKGroup.isSQTKCat hsqtk,
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
end MainSimple

section Top

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_sup_two {H N T₁ P : Subgroup G} (hNH : N ≤ H) (hTH : T₁ ≤ H) (hPH : P ≤ H)
    (hN : (N.subgroupOf H).Normal) (hsup : N ⊔ T₁ = H) (hT₁ : IsPGroup 2 T₁) (hP : ⁅P, P⁆ = P) :
    P ≤ N := by
  have hsup' : N.subgroupOf H ⊔ T₁.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hTH, hsup]
    exact Subgroup.subgroupOf_self _
  have hT₁' : IsPGroup 2 (T₁.subgroupOf H) := hT₁.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hP' : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPH, hP]
  intro x hx
  have := le_of_perfect_of_quotient_two (N := N.subgroupOf H) hsup' hT₁' hP'
    (show (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H from hx)
  exact this

@[expose] def NoFaithfulFFPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T), IsCase2 T K → KbarIsL3Two K →
      mcOf T = conjClosure K T ⊔ T →
      HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 (mcOf T))

theorem noFaithfulFF_of_inputs
    (h56 : AsB56) (h21 : Stage14621) (hPair : NoFaithfulFFPair) :
    NoFaithfulFFInput := by
  intro G _ _ T M S hB c19 c20 K hK hHeq hKL
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hcperf : perfectCore (mcOf T) ≤ mcOf T := perfectCore_le _
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hconj : mcOf T ≤ Subgroup.normalizer (K : Set G) → conjClosure K T = K := fun hnormK => by
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hnormK (hTH ht)) z).mp hz
    · exact le_conjClosure K T
  rcases h21 G T M S hB c19 c20 K hK with ⟨hper, -⟩ | ⟨hcase2, hL32⟩ |
    ⟨Kp, hKp, hne, hnK, hnKp, hper, -, -⟩
  ·
    have hnormK : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer hcperf).mp (perfectCore_normal (mcOf T))
      rwa [hper] at this
    have hK₀ := hconj hnormK
    rw [hK₀] at hHeq ⊢
    rw [← hHeq]
    intro W _ _ hW ρ hker hff
    exact false_of_isFFModule_simple h56 S c19 c20 hK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hnormK) hHeq hW ρ hker hff
  · exact hPair G T M S hB c19 c20 K hK hcase2 hL32 hHeq
  ·
    exfalso
    have hK₀ := hconj hnK
    rw [hK₀] at hHeq
    have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
    have hle : Kp ≤ K :=
      le_of_perfect_of_sup_two hKH hTH hKpH ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hnK)
        hHeq.symm hT2 (perfect_of_mem_cComp hKp)
    exact hne (eq_of_le_cComp hK hKp hle)

end Top

end LRed5

end CFSG.Quasithin
