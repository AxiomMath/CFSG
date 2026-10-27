module

public import CFSG.RankThree.PartOne.KF.SU5Core
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SU5Final
public import CFSG.RankThree.PartOne.S12.Sec12TwoAssembly

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem inSU5Contained_of_inputs (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h108 : InSec10EightMoving) :
    InSU5Contained := by
  intro G _ _ p A c L E h hZ
  have hqs : CFSG.IsQuasisimple L :=
    h106 hSchreier hTwoAction G p A h.setup L (Sec12Two.L_mem_zeroStar h)
  have hns := Sec12TwoAssembly.not_isSimpleGroup_quotient_theta h.prime hqs hZ
  rcases h108 G p A h.setup c h.c_mem h.c_ne_one L ⟨h.L_mem.1.1, h.L_mem.2⟩ with
    hs | ⟨hp5, hcen, hcard, hmodel, hcont⟩
  · exact absurd hs hns
  subst hp5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA := h.A_elem
  obtain ⟨S₀, hS₀L, hS₀ne, hS₀2, hAS₀, -⟩ := h.L_mem.1.1.1.2
  have hAL : A ≤ L := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]; exact L.one_mem
    · have ha5 : a ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := A) a ha
      have hord : orderOf a = 5 := orderOf_eq_prime ha5 ha1
      have hca : Commute c a := by
        have := hA.is_comm.comm ⟨c, h.c_mem⟩ ⟨a, ha⟩
        exact congrArg Subtype.val this
      refine hcont (Subgroup.zpowers a) ?_ (by rw [Nat.card_zpowers, hord])
        ⟨S₀, hS₀ne, hS₀2, hS₀L, (Subgroup.zpowers_le.mpr ha).trans hAS₀⟩ (Subgroup.mem_zpowers a)
      refine (Subgroup.zpowers_le.mpr ?_)
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨k, rfl⟩
      exact (hca.zpow_left k).eq
  by_contra hEL
  obtain ⟨e, heE, heL⟩ := IsConcreteLE.not_le_iff_exists.mp hEL
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    h.E_normalizes_thetaComponentsAt h81 hcE h.L_mem.2
  have heN := hEN heE
  have hec : e ∈ Subgroup.centralizer (A : Set G) := h.E_le heE
  have he5 : e ^ 5 = 1 := by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := E) e heE
  obtain ⟨f, hf, hmodel'⟩ := hmodel
  obtain ⟨-, F, _, _, hFcard, ⟨emod⟩⟩ := hmodel'
  have : Group.IsPerfect ↥L := hqs.1
  set A₀ : Subgroup ↥L := A.subgroupOf L with hA₀
  have hA₀exp : ∀ a ∈ A₀, a ^ 5 = 1 := fun a ha => Subtype.ext (by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := A) (a : G)
      (Subgroup.mem_subgroupOf.mp ha)
    simpa using this)
  have hA₀comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := fun a ha b hb => Subtype.ext (by
    have := hA.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩
      ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩
    simpa using congrArg Subtype.val this)
  have hA₀card : Nat.card A₀ = 5 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact h.A_card
  obtain ⟨h5, ψ, hψ⟩ := KFSU5.exists_diagonal_su5_iso hcard hf hFcard emod A₀ hA₀exp hA₀comm hA₀card
  have hU : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  set ψ' : ↥(unitarySU 2 f F 5) →* G := L.subtype.comp ψ.toMonoidHom with hψ'
  have hψ'inj : Function.Injective ψ' := L.subtype_injective.comp ψ.injective
  have hψ'L : ∀ g : ↥(unitarySU 2 f F 5), ψ' g ∈ L := fun g => (ψ g).2
  have hψ'range : ∀ x ∈ L, ∃ g : ↥(unitarySU 2 f F 5), ψ' g = x := fun x hx => by
    obtain ⟨g, hg⟩ := ψ.surjective ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  set Ãγ : Subgroup ↥(unitarySU 2 f F 5) := A.comap ψ' with hÃγ
  set Ã : Subgroup (GL (Fin 5) F) := Ãγ.map (unitarySU 2 f F 5).subtype with hÃ
  have hdiag : ∀ a ∈ Ã, ((a : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    exact hψ g (by rw [hA₀, Subgroup.mem_subgroupOf]; exact hg)
  have hexp : ∀ a ∈ Ã, a ^ 5 = 1 := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    have h1 : g ^ 5 = 1 := by
      apply hψ'inj
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := A) _ hg
    have := congrArg Subtype.val h1
    simpa using this
  have hAψ : (A.comap ψ').map ψ' = A := Subgroup.map_comap_eq_self (fun x hx => by
    obtain ⟨g, hg⟩ := hψ'range x (hAL hx)
    exact ⟨g, hg⟩)
  have hcard5 : 5 < Nat.card Ã := by
    have h1 : Nat.card Ã = Nat.card Ãγ :=
      Subgroup.card_map_of_injective (unitarySU 2 f F 5).subtype_injective
    have h2 : Nat.card (Ãγ.map ψ') = Nat.card Ãγ := Subgroup.card_map_of_injective hψ'inj
    rw [h1, ← h2, hÃγ, hAψ, h.A_card]
    norm_num
  set Sγ : Subgroup ↥(unitarySU 2 f F 5) := S₀.comap ψ' with hSγ
  set Sgl : Subgroup (GL (Fin 5) F) := Sγ.map (unitarySU 2 f F 5).subtype with hSgl
  have hSle : Sgl ≤ unitarySU 2 f F 5 := Subgroup.map_subtype_le _
  have hSgl2 : IsPGroup 2 Sgl := by
    intro s
    obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp s.2
    obtain ⟨k, hk⟩ := hS₀2 ⟨ψ' g, hg⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (ψ' g) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : g ^ 2 ^ k = 1 := by
      apply hψ'inj
      rw [map_pow, map_one]
      exact h1
    have h3 : ((g : GL (Fin 5) F)) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val h2
      simpa using this
    rw [Subgroup.coe_pow, ← hgs]
    exact h3
  have hSne : Sgl ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS₀ne
    obtain ⟨g, hg⟩ := hψ'range x (hS₀L hx)
    intro hbot
    have hgS : ((g : GL (Fin 5) F)) ∈ Sgl :=
      Subgroup.mem_map.mpr ⟨g, (show ψ' g ∈ S₀ by rw [hg]; exact hx), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hgS
    have hg1 : g = 1 := Subtype.ext hgS
    apply hx1
    have hx' : x = 1 := by rw [← hg, hg1, map_one]
    exact Subtype.ext hx'
  have hnorm : ∀ a ∈ Ã, ∀ s ∈ Sgl, a * s * a⁻¹ ∈ Sgl := by
    intro a ha s hs
    obtain ⟨ga, hga, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨gs, hgs, rfl⟩ := Subgroup.mem_map.mp hs
    refine Subgroup.mem_map.mpr ⟨ga * gs * ga⁻¹, ?_, by simp⟩
    have hN := (Subgroup.mem_normalizer_iff.mp (hAS₀ hga) (ψ' gs)).mp hgs
    show ψ' (ga * gs * ga⁻¹) ∈ S₀
    rw [map_mul, map_mul, map_inv]
    exact hN
  obtain ⟨t, htΓ, ht2, htc⟩ :=
    KFSU5.exists_involution_commuting hU Ã Sgl hdiag hSle hSgl2 hSne hnorm
  set XL : Set G := {x | x ∈ L ∧ x ∈ Subgroup.centralizer (A : Set G) ∧
    ∃ k : ℕ, orderOf x = 2 ^ k} with hXL
  set K : Subgroup G := Subgroup.closure XL with hK
  have hKL : K ≤ L := (Subgroup.closure_le L).mpr fun x hx => hx.1
  have hKc : K ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.2.1
  have hconj : ∀ g ∈ E, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := hEN hg
    have hgc : g ∈ Subgroup.centralizer (A : Set G) := h.E_le hg
    have hmap : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [hK, MonoidHom.map_closure]
      refine (Subgroup.closure_le K).mpr ?_
      rintro _ ⟨y, ⟨hyL, hyc, k, hk⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_, k, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgN y).mp hyL
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : Commute a g := (Subgroup.mem_centralizer_iff.mp hgc a ha).symm.symm
        have h2 : Commute a y := (Subgroup.mem_centralizer_iff.mp hyc a ha)
        have := (h1.mul_right h2).mul_right h1.inv_right
        exact this.eq
      · rw [← hk]
        exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have heK : e ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj e heE x, fun hx => ?_⟩
    have := hconj e⁻¹ (E.inv_mem heE) _ hx
    simpa [mul_assoc] using this
  have hcentA : ∀ g : ↥(unitarySU 2 f F 5), ψ' g ∈ Subgroup.centralizer (A : Set G) ↔
      ∀ g' : ↥(unitarySU 2 f F 5), ψ' g' ∈ A → g * g' = g' * g := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hg g' hg'
      apply hψ'inj
      rw [map_mul, map_mul]
      exact (hg _ hg').symm
    · intro hg a ha
      obtain ⟨g', hg'⟩ := hψ'range a (hAL ha)
      subst hg'
      have := hg g' ha
      rw [← map_mul, ← map_mul, this]
  have hK2 : 2 ∣ Nat.card K := by
    set tΓ : ↥(unitarySU 2 f F 5) := ⟨t, htΓ⟩ with htΓdef
    have hxt : ψ' tΓ ∈ XL := by
      refine ⟨hψ'L tΓ, (hcentA tΓ).mpr fun g' hg' => ?_, 1, ?_⟩
      · apply Subtype.ext
        have := htc ((g' : GL (Fin 5) F)) (Subgroup.mem_map.mpr ⟨g', hg', rfl⟩)
        simpa using this
      · rw [pow_one, orderOf_injective ψ' hψ'inj tΓ]
        rw [← Subgroup.orderOf_coe tΓ]
        exact ht2
    have hxtK : ψ' tΓ ∈ K := Subgroup.subset_closure hxt
    have hord : orderOf (ψ' tΓ) = 2 := by
      rw [orderOf_injective ψ' hψ'inj tΓ, ← Subgroup.orderOf_coe tΓ]
      exact ht2
    have := Subgroup.orderOf_dvd_natCard K hxtK
    rwa [hord] at this
  have hKA : K ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxA⟩
    rw [Subgroup.mem_bot]
    set Xs : Set ↥(unitarySU 2 f F 5) := {y | ψ' y ∈ XL} with hXs
    have hXimg : ψ' '' Xs = XL := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        obtain ⟨y, hy⟩ := hψ'range z hz.1
        exact ⟨y, show ψ' y ∈ XL by rw [hy]; exact hz, hy⟩
    have hKimg : K = (Subgroup.closure Xs).map ψ' := by
      rw [MonoidHom.map_closure, hXimg]
    rw [hKimg] at hxK
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxK
    have hyÃ : (y : GL (Fin 5) F) ∈ Ã := Subgroup.mem_map.mpr ⟨y, hxA, rfl⟩
    have hyc : (y : GL (Fin 5) F) ∈ Subgroup.closure {z : GL (Fin 5) F |
        z ∈ Subgroup.centralizer (Ã : Set (GL (Fin 5) F)) ∧ ∃ k : ℕ, orderOf z = 2 ^ k} := by
      have h1 : (y : GL (Fin 5) F) ∈ (Subgroup.closure Xs).map (unitarySU 2 f F 5).subtype :=
        Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [MonoidHom.map_closure] at h1
      refine (Subgroup.closure_mono ?_) h1
      rintro _ ⟨y', hy', rfl⟩
      obtain ⟨-, hy'c, k, hk⟩ := hy'
      refine ⟨?_, k, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp ha
        have := congrArg Subtype.val ((hcentA y').mp hy'c g' hg').symm
        simpa using this
      · rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, ← orderOf_injective ψ' hψ'inj y']
        exact hk
    have hy1 : (y : GL (Fin 5) F) = 1 :=
      KFSU5.eq_one_of_mem_closure_twoElements_su5 hU Ã hdiag hexp hcard5 hyc hyÃ
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hy1', map_one]
  have hlt := KFSU5.three_lt_evenRank_of_outer_element hA h.A_card hAL hKL hKA hKc hec heK he5
    heL hK2
  rw [h.evenRank_eq] at hlt
  exact lt_irrefl _ hlt

end CFSG.RankThree.PartOne
