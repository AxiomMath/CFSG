module

public import CFSG.RankThree.PartOne.S12.Sec159FiveDefs
public import CFSG.RankThree.PartOne.S12.Sec159FiveSyl
public import CFSG.RankThree.PartOne.K159F.SzAbs
public import CFSG.RankThree.PartOne.K159F.OuterFacts
public import CFSG.RankThree.PartOne.K159F.QbarAction
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
import CFSG.RankThree.PartOne.S12.Sec159Tr
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.PartOne.S12.Sec136Inputs
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec158Defs
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.S12.Sec159Fin
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Census3 (IsoLie)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {G : Type} [Group G] [Finite G]

section Sylow

theorem exists_sylow_normalizer {p : ℕ} (hp : p.Prime) (h155 : Node155) {A E : Subgroup G} {c : G}
    {L : Subgroup G} (X : Subgroup G) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∃ P : Subgroup G, IsSylowOf p P (X ⊔ E) ∧ E ≤ P ∧ P ≤ torusNormalizer E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h := h15.h12
  have hEp : IsPGroup p ↥E := (h.E_elem).isPGroup p ↥E
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hle : E ≤ (X ⊔ E) ⊓ Subgroup.normalizer (E : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  obtain ⟨Q₀, hQ0, hEQ⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hle hEp
  exact ⟨Q₀, Sec15FA.sylow_of_torus_normalizer hJ hQ0 hEQ, hEQ, hQ0.1.trans inf_le_right⟩

end Sylow

section Five

omit [Finite G] in
theorem eq_one_of_mem_E_theta {E X : Subgroup G} (hEel : IsElementaryAbelian 5 ↥E)
    (hθ : ¬ 5 ∣ Nat.card ↥(aschbacherSolvableCore 5 ↥X)) {z : G} (hzE : z ∈ E)
    (hzθ : z ∈ inSubgroup (aschbacherSolvableCore 5) X) : z = 1 := by
  have h5 : z ^ 5 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := E) z hzE
  have hz5 : orderOf z ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  obtain ⟨t, ht, hzt⟩ := hzθ
  have hzo : orderOf z ∣ Nat.card ↥(aschbacherSolvableCore 5 ↥X) := by
    have h1 : orderOf (⟨t, ht⟩ : ↥(aschbacherSolvableCore 5 ↥X)) ∣
        Nat.card ↥(aschbacherSolvableCore 5 ↥X) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨t, ht⟩ : ↥(aschbacherSolvableCore 5 ↥X)) = orderOf z := by
      rw [← hzt, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      rfl
    rwa [h2] at h1
  have hcop : Nat.Coprime 5 (Nat.card ↥(aschbacherSolvableCore 5 ↥X)) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hθ
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hz5 hzo)

theorem sz_inner_of_five
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : Sec153.ModData 5 E) (hEcard : Nat.card ↥E = 5 ^ 4) {X : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hθ : ¬ 5 ∣ Nat.card ↥(aschbacherSolvableCore 5 ↥X))
    (hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 5 ↥X))
    [IsSimpleGroup (Qbar 5 X)] (hnab : ∃ a b : Qbar 5 X, a * b ≠ b * a)
    (hiso : IsoLie (Qbar 5 X) (.suzuki 2)) {P : Subgroup G} (hP : IsSylowOf 5 P (X ⊔ E))
    (hEP : E ≤ P) (hPW : P ≤ Subgroup.normalizer (E : Set G)) :
    ∀ e (he : e ∈ E), qbarAction 5 X ⟨e, hEX he⟩ ∈ Inn (Qbar 5 X) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  set N₀ := Subgroup.normalizer (X : Set G) with hN₀
  set ρ := qbarAction 5 X with hρ
  have hXN : X ≤ N₀ := Subgroup.le_normalizer
  have hEN : E ≤ N₀ := hEX
  have hXEN : X ⊔ E ≤ N₀ := sup_le hXN hEN
  have hPN : P ≤ N₀ := hP.1.trans hXEN
  set X₁ : Subgroup ↥N₀ := X.subgroupOf N₀ with hX₁
  set E₁ : Subgroup ↥N₀ := E.subgroupOf N₀ with hE₁
  set P₁ : Subgroup ↥N₀ := P.subgroupOf N₀ with hP₁
  set K₁ : Subgroup ↥N₀ := (X ⊔ E).subgroupOf N₀ with hK₁
  have hX₁n : X₁.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).2 le_rfl
  have hXK : X₁ ≤ K₁ := fun x hx => (le_sup_left : X ≤ X ⊔ E) hx
  have hK : K₁ ≤ Subgroup.normalizer (X₁ : Set ↥N₀) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hX₁n]
    exact le_top
  have hPsyl : IsSylowOf 5 P₁ K₁ := by
    refine ⟨fun x hx => hP.1 hx, hP.2.1.comap_subtype, ?_⟩
    have := hP.2.2
    rwa [← Subgroup.relIndex_subgroupOf hXEN] at this
  have hEP₁ : E₁ ≤ P₁ := fun x hx => hEP hx
  have hmapX : X₁.map ρ = Inn (Qbar 5 X) := map_qbarAction_eq_inner 5 X
  have hE₁ab : IsElementaryAbelian 5 ↥E₁ := Sec159Tr.isElementaryAbelian_subgroupOf hEel
  have hE₁card : Nat.card ↥E₁ = 5 ^ 4 := by
    rw [Sec159Tr.card_subgroupOf hEN, hEcard]
  set ψ : ↥E₁ →* MulAut (Qbar 5 X) := ρ.comp E₁.subtype with hψ
  have hψrange : ψ.range = E₁.map ρ := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrange : Nat.card ψ.range ≤ 25 := by
    rw [hψrange]
    exact card_map_le_twentyfive hnab hiso ρ hE₁ab
  have hker25 : 25 ≤ Nat.card ψ.ker := by
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hE₁card] at hmul
    by_contra hlt
    push Not at hlt
    have : Nat.card ψ.ker * Nat.card ψ.range ≤ 24 * 25 := Nat.mul_le_mul (by omega) hrange
    omega
  have hcommG : ∀ y ∈ P ⊓ X, ∀ e ∈ E, y * e = e * y := by
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyX : y ∈ X := hy.2
    have hyN : y ∈ Subgroup.normalizer (E : Set G) := hPW hyP
    by_contra hnc
    push Not at hnc
    obtain ⟨e, he, hne⟩ := hnc
    have hτ1 : conjAut E y hyN ≠ 1 := by
      intro h1
      have h2 := Equivariance.coe_conjAut hyN ⟨e, he⟩
      rw [h1] at h2
      apply hne
      have h3 : e = y * e * y⁻¹ := h2
      rw [eq_mul_inv_iff_mul_eq] at h3
      exact h3.symm
    obtain ⟨k, hk⟩ := hP.2.1 ⟨y, hyP⟩
    have hykpow : y ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hpow : conjAut E y hyN ^ (5 ^ k) = 1 := by
      unfold conjAut
      rw [← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (5 ^ k) = 1 :=
        Subtype.ext (by simpa using hykpow)
      rw [this, map_one]
    have hfix := outer_facts' h M hyN hpow hτ1
    have hfixmem : ∀ u : ↥ψ.ker, ((u.1.1 : ↥N₀) : G) ∈ E := fun u => u.1.2
    have hker_comm : ∀ u : ↥ψ.ker, y * ((u.1.1 : ↥N₀) : G) * y⁻¹ = ((u.1.1 : ↥N₀) : G) := by
      intro u
      have hu1 : ρ u.1.1 = 1 := MonoidHom.mem_ker.1 u.2
      have hθmem := (qbarAction_eq_one_iff 5 X hperf u.1.1).1 hu1 y hyX
      have huE : ((u.1.1 : ↥N₀) : G) ∈ E := hfixmem u
      have hzE : ((u.1.1 : ↥N₀) : G) * y * ((u.1.1 : ↥N₀) : G)⁻¹ * y⁻¹ ∈ E := by
        have h1 : y * ((u.1.1 : ↥N₀) : G)⁻¹ * y⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.1 hyN _).1 (E.inv_mem huE)
        have : ((u.1.1 : ↥N₀) : G) * y * ((u.1.1 : ↥N₀) : G)⁻¹ * y⁻¹ =
            ((u.1.1 : ↥N₀) : G) * (y * ((u.1.1 : ↥N₀) : G)⁻¹ * y⁻¹) := by group
        rw [this]
        exact E.mul_mem huE h1
      have hz1 := eq_one_of_mem_E_theta hEel hθ hzE hθmem
      have h2 : ((u.1.1 : ↥N₀) : G) * y = y * ((u.1.1 : ↥N₀) : G) := by
        have h3 : ((u.1.1 : ↥N₀) : G) * y * ((u.1.1 : ↥N₀) : G)⁻¹ = y := mul_inv_eq_one.1 hz1
        calc ((u.1.1 : ↥N₀) : G) * y = ((u.1.1 : ↥N₀) : G) * y * ((u.1.1 : ↥N₀) : G)⁻¹ *
              ((u.1.1 : ↥N₀) : G) := by group
          _ = y * ((u.1.1 : ↥N₀) : G) := by rw [h3]
      calc y * ((u.1.1 : ↥N₀) : G) * y⁻¹ = ((u.1.1 : ↥N₀) : G) * y * y⁻¹ := by rw [h2]
        _ = ((u.1.1 : ↥N₀) : G) := by group
    let f : ↥ψ.ker → {u : ↥E // conjAut E y hyN u = u} := fun u =>
      ⟨⟨((u.1.1 : ↥N₀) : G), hfixmem u⟩,
        Subtype.ext (by rw [Equivariance.coe_conjAut]; exact hker_comm u)⟩
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun z : {u : ↥E // conjAut E y hyN u = u} => ((z.1 : ↥E) : G)) hab
      simp only [f] at this
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    have hle := Nat.card_le_card_of_injective f hf
    omega
  have hcomm : ∀ y ∈ P₁ ⊓ X₁, ∀ e ∈ E₁, ρ y * ρ e = ρ e * ρ y := by
    intro y hy e he
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcommG (y : G) ⟨hy.1, hy.2⟩ (e : G) he
  have hin := sz_inner_of_commute hnab hiso ρ hmapX hXK hK hPsyl hEP₁ hcomm
  intro e he
  exact hin (Subgroup.mem_map.2 ⟨⟨e, hEN he⟩, he, rfl⟩)

end Five

section Final

theorem kf159Sz_of_inputs
    (h155 : Node155) (hMod : KFU5Mod) : KF159Sz := by
  intro G _ _ p A c L E h15 hF hout X hX hiso e he
  classical
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨B, hB, hXB⟩ := hX
  obtain ⟨x, hxB, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
  have hxE : x ∈ E := hB.1 hxB
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hxE hXx
  have hQq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx
  have hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore p ↥X) := hQq.1
  have hsimple : IsSimpleGroup (Qbar p X) := hQq.2.1
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hnab : ∃ a b : Qbar p X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup (Qbar p X) := { (inferInstance : Group (Qbar p X)) with mul_comm := hcon }
    have := IsSimpleGroup.prime_card (α := Qbar p X)
    rw [hSz.card] at this
    norm_num at this
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization hp).2.2.1
  have hexp : ∀ z ∈ E, z ^ p = 1 := fun z hz =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) z hz
  suffices hin : qbarAction p X ⟨e, hEX he⟩ ∈ Inn (Qbar p X) by
    have hin' : qbarAction p X ⟨e, hEX he⟩ ∈
        (X.subgroupOf (Subgroup.normalizer (X : Set G))).map (qbarAction p X) := by
      rw [map_qbarAction_eq_inner]; exact hin
    obtain ⟨m, hm, hmρ⟩ := hin'
    have hmX : (m : G) ∈ X := hm
    refine ⟨(m : G), hmX, ?_⟩
    rw [mem_thetaQuotientCentralizer_iff]
    refine ⟨Subgroup.mem_top _, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hmX)) (hEX he)
    · intro k hk
      set me : ↥(Subgroup.normalizer (X : Set G)) := ⟨e, hEX he⟩ with hme
      have h1 : qbarAction p X (m⁻¹ * me) = 1 := by
        rw [map_mul, map_inv, hmρ, inv_mul_cancel]
      have h2 := (qbarAction_eq_one_iff p X hperf (m⁻¹ * me)).1 h1 k hk
      have h3 : ((m⁻¹ * me : ↥(Subgroup.normalizer (X : Set G))) : G) = (m : G)⁻¹ * e := rfl
      rw [h3] at h2
      exact h2
  by_cases hp5' : p = 5
  · subst hp5'
    obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
    obtain ⟨P, hP, hEP, hPW⟩ := exists_sylow_normalizer hp h155 X h15 hF hout
    have hEcard : Nat.card ↥E = 5 ^ 4 := by
      obtain ⟨-, -, -, -, -, hc, -⟩ := hout
      exact hc
    exact sz_inner_of_five h M hEcard hEX hθp hperf hnab hiso hP hEP hPW e he
  ·
    have hdvd5 := card_outer_dvd_five hiso
    set φ := qbarAction p X ⟨e, hEX he⟩ with hφ
    have hφp : φ ^ p = 1 := by
      rw [hφ, ← map_pow]
      have : (⟨e, hEX he⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ p = 1 :=
        Subtype.ext (by simpa using hexp e he)
      rw [this, map_one]
    have hπ : orderOf (QuotientGroup.mk φ : Outer (Qbar p X)) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hφp, QuotientGroup.mk_one])
    have hπ' : orderOf (QuotientGroup.mk φ : Outer (Qbar p X)) ∣ 5 :=
      (orderOf_dvd_natCard _).trans hdvd5
    have hcop : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).2 hp5'
    have h1 : orderOf (QuotientGroup.mk φ : Outer (Qbar p X)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hπ hπ'
    exact (QuotientGroup.eq_one_iff φ).1 (orderOf_eq_one_iff.1 h1)

end Final

end CFSG.RankThree.PartOne.K159F
