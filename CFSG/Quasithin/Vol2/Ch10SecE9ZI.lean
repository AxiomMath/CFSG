module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZH
public import CFSG.Quasithin.EmptyFaithful.LRed5Final
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecB6Bar
public import CFSG.Quasithin.Vol2.Ch10SecBCoordPsi
public import CFSG.Quasithin.Vol2.Ch10SecEBlock

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem map_convI_comp_eq {Z H K : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hN : H ≤ Subgroup.normalizer (Z : Set G)) (hKH : K ≤ H) :
    (K.subgroupOf H).map ((convI hZ).comp (Subgroup.inclusion hN)) = autI hZ K := by
  ext φ
  rw [Subgroup.mem_map, mem_autI]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Subgroup.inclusion hN k, hk, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hKH hg⟩, hg, rfl⟩

omit [Finite G] in
theorem range_convI_comp_eq {Z H : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hN : H ≤ Subgroup.normalizer (Z : Set G)) :
    ((convI hZ).comp (Subgroup.inclusion hN)).range = autI hZ H := by
  rw [← map_convI_comp_eq hZ hN le_rfl, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem pairData_ZQ (h3228 : TmpL6_3_2_2_eight)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    LRed5.PairData (autI (isElemAbelian_ZQ T L I) (fsuL0 T L ⊔ T))
      (autI (isElemAbelian_ZQ T L I) L) (autI (isElemAbelian_ZQ T L I) (CFSG.conjugate L t))
      (convI (isElemAbelian_ZQ T L I)
        ⟨t⁻¹, le_normalizer_ZQ h37 h38 hyp (Subgroup.mem_sup_right (T.inv_mem ht))⟩) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  set H := fsuL0 T L ⊔ T with hHdef
  set hZ := isElemAbelian_ZQ T L I
  have hN : H ≤ Subgroup.normalizer (ZQ T L I : Set G) := le_normalizer_ZQ h37 h38 hyp
  set ρ : ↥H →* MulAut (IntMod (ZQ T L I) hZ) := (convI hZ).comp (Subgroup.inclusion hN) with hρ
  have hker : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    rw [hρ, MonoidHom.comp_apply, convI_eq_one_iff]
    exact mem_centralizer_ZQ_iff h3228 h37 h38 hyp h3 x.2
  have htH : t ∈ H := Subgroup.mem_sup_right ht
  have hLH : L ≤ H := (SecA.le_fsuL0 T L).trans le_sup_left
  have hLtH : CFSG.conjugate L t ≤ H := (SecA.conjugate_le_fsuL0 ht).trans le_sup_left
  have hK : L ∈ cComp H := SecE.mem_cComp_L0T hyp
  have hK₂ : CFSG.conjugate L t ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj t⁻¹) hK
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ htH))] at h1
  have hsL : IsSimpleGroup (ModO2 L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  obtain ⟨eLt⟩ := nonempty_modO2_conjugate L t
  have hS₁ : IsSimpleGroup (KBar L) := (kbarEquivQuot L).isSimpleGroup
  have hsLt : IsSimpleGroup (ModO2 (CFSG.conjugate L t)) := eLt.isSimpleGroup
  have hS₂ : IsSimpleGroup (KBar (CFSG.conjugate L t)) := (kbarEquivQuot _).isSimpleGroup
  obtain ⟨hq₁, hz₁, ⟨e₁⟩⟩ := LRed5.image_facts hK hS₁ ρ hker
  obtain ⟨hq₂, hz₂, -⟩ := LRed5.image_facts hK₂ hS₂ ρ hker
  rw [← range_convI_comp_eq hZ hN, ← map_convI_comp_eq hZ hN hLH,
    ← map_convI_comp_eq hZ hN hLtH]
  set L₁ := (L.subgroupOf H).map ρ with hL₁
  set L₂ := ((CFSG.conjugate L t).subgroupOf H).map ρ with hL₂
  set t' : ↥H := ⟨t⁻¹, H.inv_mem htH⟩ with ht'
  show LRed5.PairData ρ.range L₁ L₂ (ρ t')
  have hL₁Γ : L₁ ≤ ρ.range := Subgroup.map_le_range ρ _
  have hL₂Γ : L₂ ≤ ρ.range := Subgroup.map_le_range ρ _
  have hcard₁ : Nat.card ↥L₁ = 168 := by
    rw [← Nat.card_congr e₁.toEquiv, Nat.card_congr (kbarEquivQuot L).toEquiv,
      Nat.card_congr h3.1.some.toEquiv]
    exact card_Γ
  have hswap₁ : ∀ x ∈ L₁, ρ t' * x * (ρ t')⁻¹ ∈ L₂ := by
    intro x hx
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hx
    have : ρ t' * ρ k * (ρ t')⁻¹ = ρ (t' * k * t'⁻¹) := by simp [map_mul, map_inv]
    rw [this]
    refine Subgroup.mem_map_of_mem ρ ?_
    show t⁻¹ * (k : G) * t⁻¹⁻¹ ∈ CFSG.conjugate L t
    exact ⟨k, hkK, by simp⟩
  have hswap₂ : ∀ y ∈ L₂, (ρ t')⁻¹ * y * ρ t' ∈ L₁ := by
    intro y hy
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hy
    have : (ρ t')⁻¹ * ρ k * ρ t' = ρ (t'⁻¹ * k * t') := by simp [map_mul, map_inv]
    rw [this]
    refine Subgroup.mem_map_of_mem ρ ?_
    obtain ⟨l, hl, hlk⟩ := hkK
    show t⁻¹⁻¹ * (k : G) * t⁻¹ ∈ L
    have hk : (k : G) = t⁻¹ * l * t := by
      rw [show (k : G) = H.subtype k from rfl, ← hlk]
      simp
    rw [hk]
    simpa [mul_assoc] using hl
  have hcard₂ : Nat.card ↥L₂ = 168 := by
    have h1 : Nat.card ↥L₁ ≤ Nat.card ↥L₂ :=
      Nat.card_le_card_of_injective
        (fun x : ↥L₁ => (⟨ρ t' * x * (ρ t')⁻¹, hswap₁ x x.2⟩ : ↥L₂)) (by
          intro a b h
          exact Subtype.ext (by simpa using congrArg Subtype.val h))
    have h2 : Nat.card ↥L₂ ≤ Nat.card ↥L₁ :=
      Nat.card_le_card_of_injective
        (fun y : ↥L₂ => (⟨(ρ t')⁻¹ * y * ρ t', hswap₂ y y.2⟩ : ↥L₁)) (by
          intro a b h
          exact Subtype.ext (by simpa using congrArg Subtype.val h))
    omega
  have hcomm₀ : ⁅L, CFSG.conjugate L t⁆ ≤ pCoreOf 2 H :=
    (SecA.commutator_conjugate_le h37 hyp ht htn).trans (inf_le_left.trans
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)))
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨k₂, hk₂, rfl⟩ := Subgroup.mem_map.mp hb
    have h1 : ρ (k * k₂ * k⁻¹ * k₂⁻¹) = 1 := (hker _).2 (by
      have := hcomm₀ (Subgroup.commutator_mem_commutator hkK hk₂)
      simpa [commutatorElement_def] using this)
    simp only [map_mul, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1)
  have hL0 : fsuL0 T L = L ⊔ CFSG.conjugate L t := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  have hL0H : fsuL0 T L ≤ H := le_sup_left
  have hLsup : L₁ ⊔ L₂ = ((fsuL0 T L).subgroupOf H).map ρ := by
    rw [hL₁, hL₂, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLH hLtH, ← hL0]
  have hL0n : ((fsuL0 T L).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL0H).mpr
      (sup_le Subgroup.le_normalizer (SecA.le_fsuM T L))
  have hLΓ : L₁ ⊔ L₂ ≤ ρ.range := sup_le hL₁Γ hL₂Γ
  have hLn : ((L₁ ⊔ L₂).subgroupOf ρ.range).Normal := by
    rw [hLsup]
    exact LRed5.normal_map_range ρ hL0n
  have hnormal : ∀ g ∈ ρ.range, ∀ x ∈ L₁ ⊔ L₂, g * x * g⁻¹ ∈ L₁ ⊔ L₂ := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (EmptyFaithfulMultiple.FFL.le_normalizer_of_normal hLΓ hLn hg) x).mp hx
  set T₀ := (T.subgroupOf H).map ρ with hT₀
  have hTH : T ≤ H := le_sup_right
  have hT₀2 : IsPGroup 2 T₀ :=
    (hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ρ
  have hT₀Γ : T₀ ≤ ρ.range := Subgroup.map_le_range ρ _
  have hΓeq : ρ.range = (L₁ ⊔ L₂) ⊔ T₀ := by
    have h1 : (fsuL0 T L).subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hL0H hTH]
      exact Subgroup.subgroupOf_self _
    rw [MonoidHom.range_eq_map, ← h1, Subgroup.map_sup, hLsup]
  have hO2 : pCoreOf 2 ρ.range = ⊥ := LRed5.pCoreOf_range_eq_bot ρ hker
  have hZc := LRed5.centerless_sup hcomm hz₁ hz₂
  have hC := LRed5.centralizer_eq_bot_of_two_quotient hLΓ hLn hZc hT₀Γ hT₀2 hΓeq hO2
  have hQ : G64.IsQuotientOfSQTKCat ↥ρ.range :=
    ⟨↥H, inferInstance, inferInstance, ρ.ker, inferInstance,
      SQTKGroup.isSQTKCat (SecA.sqtkGroup_L0T hyp),
      ⟨(QuotientGroup.quotientKerEquivRange ρ).symm⟩⟩
  have hoff : ∃ A, IsFFStarOffender ρ.range A := by
    obtain ⟨A₀, hA₀, hA₀V⟩ : ∃ A₀ : Subgroup G, IsMaxElemAbelian T A₀ ∧
        ¬ A₀ ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hJ (iSup₂_le fun A hA => hcon A hA)
    have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTH
    have hZH : ZQ T L I ≤ H :=
      (A4.omegaOneCenterOf_le _).trans (inf_le_left.trans hTH)
    refine ⟨autI hZ A₀, ?_⟩
    rw [range_convI_comp_eq hZ hN]
    exact offenderImages_isFFStarOffender hZ hZH hN
      ⟨A₀, ⟨isMaxElemAbelian_of_isSylowTwoOf hTsyl hA₀, fun h => hA₀V (h.trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (fsuVM_le_ZQ hyp))))⟩, rfl⟩
  exact
    { le₁ := hL₁Γ
      le₂ := hL₂Γ
      q₁ := hq₁
      q₂ := hq₂
      z₁ := hz₁
      z₂ := hz₂
      c₁ := hcard₁
      c₂ := hcard₂
      comm := hcomm
      tΓ := ⟨t', rfl⟩
      swap₁ := hswap₁
      swap₂ := hswap₂
      normal := hnormal
      cent := fun g hg hx => by
        have : g ∈ ρ.range ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup _) : Set _) :=
          ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh => (hx h hh).symm⟩
        rw [hC] at this
        exact Subgroup.mem_bot.1 this
      two := LRed5.card_eq_mul_two_pow hLΓ hLn hT₀Γ hT₀2 hΓeq
      o2 := hO2
      sqtk := hQ
      off := hoff }

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
