module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeisCore
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.Asc83Table.E27
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.RankThree.PartTwo.KFacts.KS18Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem commutator_eq_of_isHeisSL {X : Type} [Group X] {U V : Subgroup X} (hsup : U ⊔ V = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : Sec4.IsHeisThree U)
    (hV : Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) : commutator X = V := by
  obtain ⟨eV⟩ := hV
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := L34.exists_mul_eq_of_sup_eq_top hsup hUV x
    obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := L34.exists_mul_eq_of_sup_eq_top hsup hUV y
    have hw : v₁ * v₂ * v₁⁻¹ ∈ V := V.mul_mem (V.mul_mem hv₁ hv₂) (V.inv_mem hv₁)
    have hw' : v₁ * v₂ * v₁⁻¹ * v₂⁻¹ ∈ V := V.mul_mem hw (V.inv_mem hv₂)
    have e1 : v₁ * u₂ = u₂ * v₁ := (hUV u₂ hu₂ v₁ hv₁).symm
    have e2 : v₁ * v₂ * v₁⁻¹ * u₁⁻¹ = u₁⁻¹ * (v₁ * v₂ * v₁⁻¹) :=
      (hUV _ (U.inv_mem hu₁) _ hw).symm
    have e3 : v₁ * v₂ * v₁⁻¹ * v₂⁻¹ * u₂⁻¹ = u₂⁻¹ * (v₁ * v₂ * v₁⁻¹ * v₂⁻¹) :=
      (hUV _ (U.inv_mem hu₂) _ hw').symm
    have hc : ⁅u₁ * v₁, u₂ * v₂⁆ = ⁅u₁, u₂⁆ * ⁅v₁, v₂⁆ := by
      calc ⁅u₁ * v₁, u₂ * v₂⁆ = u₁ * (v₁ * u₂) * v₂ * v₁⁻¹ * u₁⁻¹ * v₂⁻¹ * u₂⁻¹ := by
            rw [commutatorElement_def]; group
        _ = u₁ * u₂ * (v₁ * v₂ * v₁⁻¹ * u₁⁻¹) * v₂⁻¹ * u₂⁻¹ := by rw [e1]; group
        _ = u₁ * u₂ * u₁⁻¹ * (v₁ * v₂ * v₁⁻¹ * v₂⁻¹ * u₂⁻¹) := by rw [e2]; group
        _ = ⁅u₁, u₂⁆ * ⁅v₁, v₂⁆ := by
            rw [e3, commutatorElement_def, commutatorElement_def]; group
    rw [hc]
    refine V.mul_mem ?_ (by rw [commutatorElement_def]; exact hw')
    have h1 : ⁅u₁, u₂⁆ ∈ ⁅U, U⁆ := Subgroup.commutator_mem_commutator hu₁ hu₂
    rw [← Subgroup.map_subtype_commutator, hU.1.2.1,
      ← L34.inf_eq_map_center_left hUV hU h3] at h1
    exact h1.2
  · have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
    have : Group.IsPerfect V :=
      Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have h1 : ⁅V, V⁆ = V := by
      rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h1, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top

variable {Y : Type} [Group Y]

theorem outer_involution_heis_of [Finite Y] (hO : CFSG.pCore 2 Y = ⊥) {X : Subgroup Y}
    (hX : X.Normal) {U V : Subgroup X} (hsup : U ⊔ V = ⊤)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : Sec4.IsHeisThree U)
    (eV : V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) {L : Subgroup Y} [L.Normal]
    (hLV : L = V.map X.subtype) (hLX : ⁅X, X⁆ = L) {t : Y} {E : Subgroup Y} (htX : t ∉ X)
    (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (hEX : E ≤ X)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y))
    (hB : ∀ B : Subgroup Y, B ≤ E → Nat.card B = 9 →
      ¬ CFSG.perfectResidual Y ≤ Subgroup.centralizer (B : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  have := hX
  have hk : Nat.card (GaloisField 2 2) = 4 := L34.card_galoisField_two_two
  let φ : L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
    (MulEquiv.subgroupCongr hLV).trans
      ((V.equivMapOfInjective X.subtype X.subtype_injective).symm.trans eV)
  let ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 (GaloisField 2 2) :=
    QuotientGroup.congr (Subgroup.center L) (scalars 3 (GaloisField 2 2)) φ
      ((Subgroup.map_center_eq φ).trans (scalars_eq_center 3 (GaloisField 2 2)).symm)
  have hL : commutator L = ⊤ := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
    have : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hCLn : (Subgroup.centralizer (L : Set Y)).Normal := Subgroup.normal_centralizer
  have hUL : ∀ u ∈ U.map X.subtype, ∀ l ∈ L, u * l = l * u := by
    rintro _ ⟨u, hu, rfl⟩ l hl
    rw [hLV] at hl
    obtain ⟨v, hv, rfl⟩ := hl
    exact congrArg Subtype.val (hUV u hu v hv)
  have hU'C : U.map X.subtype ≤ Subgroup.centralizer (L : Set Y) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => (hUL u hu l hl).symm
  have hXC : X ⊓ Subgroup.centralizer (L : Set Y) ≤ U.map X.subtype := by
    rintro y ⟨hy, hc⟩
    have : (⟨y, hy⟩ : X) ∈ Subgroup.centralizer (V : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply Subtype.ext
      refine Subgroup.mem_centralizer_iff.mp hc (v : Y) ?_
      rw [hLV]
      exact ⟨v, hv, rfl⟩
    rw [L34.centralizer_eq_of_isHeisSL hsup hUV ⟨eV⟩ h3] at this
    exact ⟨⟨y, hy⟩, this, rfl⟩
  have hdec : ∀ x ∈ X, ∃ l ∈ L, ∃ u ∈ U.map X.subtype, x = l * u := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := L34.exists_mul_eq_of_sup_eq_top hsup hUV ⟨x, hx⟩
    refine ⟨v, by rw [hLV]; exact ⟨v, hv, rfl⟩, u, ⟨u, hu, rfl⟩, ?_⟩
    have h1 : x = (u : Y) * (v : Y) := (congrArg Subtype.val huv).symm
    have h2 : (u : Y) * (v : Y) = (v : Y) * (u : Y) := congrArg Subtype.val (hUV u hu v hv)
    rw [h1, h2]
  have hXLC : ∀ x ∈ X, ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), x = l * c := by
    intro x hx
    obtain ⟨l, hl, u, hu, rfl⟩ := hdec x hx
    exact ⟨l, hl, u, hU'C hu, rfl⟩
  have hU'3 : IsPGroup 3 (U.map X.subtype) := hU.1.1.map X.subtype
  have hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)) := hU'3.to_le hXC
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 _ x.2)⟩
  have hres : CFSG.perfectResidual Y ≤ L := hLX ▸ perfectResidual_le_commutator hYt
  have hEC : Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (hE3.to_le (inf_le_left :
      E ⊓ Subgroup.centralizer (L : Set Y) ≤ E)).exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;> simp_all
    have hdvd : 3 ^ 2 ∣ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Y)) :=
      hn ▸ pow_dvd_pow 3 hn2
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    refine hB (K.map (E ⊓ Subgroup.centralizer (L : Set Y)).subtype)
      ((Subgroup.map_subtype_le K).trans inf_le_left) ?_ ?_
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num
    · refine hres.trans ?_
      rw [Subgroup.le_centralizer_iff]
      exact (Subgroup.map_subtype_le K).trans inf_le_right
  have hU27 : Nat.card (U.map X.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hU.2.1
  have hUL3 : Nat.card ↥(U.map X.subtype ⊓ L) = 3 := by
    rw [hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact h3
  have hEL : Nat.card ↥(E ⊓ L) ≤ 9 := by
    refine card_inf_le_nine hE ?_
    rw [CFSG.RankThree.Asc83Table.pRank_congr φ, L34.pRank_three_specialLinearGroup hk]
  have hW9 := nine_le_card_inf_sup hEL hE27 hUL3 (fun e he => hdec e (hEX he))
  have hcommU : ∀ a ∈ U.map X.subtype, ∀ b ∈ U.map X.subtype,
      ⁅a, b⁆ ∈ U.map X.subtype ⊓ L := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ⁅U, U⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [← Subgroup.map_subtype_commutator, hU.1.2.1,
      ← L34.inf_eq_map_center_left hUV hU h3] at h1
    rw [← map_commutatorElement, hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective]
    exact ⟨_, h1, rfl⟩
  have hKX : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R ≤ Subgroup.centralizer (X : Set Y) := by
    intro R hR hRL hRE r hr
    have hrEL : ∀ x ∈ E ⊔ L, r * x = x * r := by
      intro x hx
      have hle : E ⊔ L ≤ Subgroup.centralizer ({r} : Set Y) := by
        refine sup_le (fun e he => ?_) (fun l hl => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hRE hr) e he)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hRL hr) l hl)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
    have hrU : ∀ u ∈ U.map X.subtype, r * u * r⁻¹ ∈ U.map X.subtype := fun u hu =>
      hXC ⟨hX.conj_mem u (Subgroup.map_subtype_le U hu) r, hCLn.conj_mem u (hU'C hu) r⟩
    have hrU' : ∀ u ∈ U.map X.subtype, r * u = u * r := by
      obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
      have hm' : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hWU : U.map X.subtype ⊓ (E ⊔ L) ≤ U.map X.subtype := inf_le_left
      have hZW : U.map X.subtype ⊓ L ≤ U.map X.subtype ⊓ (E ⊔ L) :=
        inf_le_inf_left _ le_sup_right
      have hrW : ∀ x ∈ U.map X.subtype ⊓ (E ⊔ L), r * x = x * r := fun x hx => hrEL x hx.2
      have hdvd : Nat.card ↥(U.map X.subtype ⊓ (E ⊔ L)) ∣ 3 ^ 3 := by
        rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hU27]
        exact Subgroup.card_dvd_of_le hWU
      obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases i
      · rw [hci] at hW9; norm_num at hW9
      · rw [hci] at hW9; norm_num at hW9
      · have hW9' : Nat.card ↥(U.map X.subtype ⊓ (E ⊔ L)) = 9 := by rw [hci]; norm_num
        have hlt : U.map X.subtype ⊓ L < U.map X.subtype ⊓ (E ⊔ L) := by
          refine lt_of_le_of_ne hZW fun h => ?_
          rw [← h, hUL3] at hW9'
          norm_num at hW9'
        obtain ⟨w, hwW, hwZ⟩ := IsConcreteLE.exists_of_lt hlt
        have hwnc : ∃ x ∈ U.map X.subtype, x * w ≠ w * x := by
          by_contra hcon
          push Not at hcon
          apply hwZ
          obtain ⟨w₀, hw₀, rfl⟩ := hWU hwW
          have hc : (⟨w₀, hw₀⟩ : U) ∈ Subgroup.center U := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            apply Subtype.ext
            exact hcon _ ⟨g, g.2, rfl⟩
          have : w₀ ∈ U ⊓ V := by
            rw [L34.inf_eq_map_center_left hUV hU h3]
            exact ⟨_, hc, rfl⟩
          rw [hLV, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective]
          exact ⟨w₀, this, rfl⟩
        intro u hu
        refine commute_of_heis hWU hwW ?_ ?_ ?_ hrU hrW hm' hu
        · intro a ha b hb
          exact ⟨hZW (hcommU a ha b hb), fun c hc => (hUL c hc _ (hcommU a ha b hb).2).symm⟩
        · exact fun x hx hxw => mem_of_commute_of_card hU27 hW9' hWU hwW hwnc hx hxw
        · intro x hx hx2
          obtain ⟨n, hn⟩ := hU'3 ⟨x, hWU hx⟩
          exact eq_one_of_pow_two_of_pow_three hx2 (congrArg Subtype.val hn)
      · have hWeq : U.map X.subtype ⊓ (E ⊔ L) = U.map X.subtype :=
          Subgroup.eq_of_le_of_card_ge hWU (by rw [hU27, hci]; norm_num)
        intro u hu
        exact hrW u (by rw [hWeq]; exact hu)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨l, hl, u, hu, rfl⟩ := hdec x hx
    have h1 : l * r = r * l := Subgroup.mem_centralizer_iff.mp (hRL hr) l hl
    have h2 : u * r = r * u := (hrU' u hu).symm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  exact outer_involution_of_inner hk hO hX hL ψ hXLC hCX hEC hKX htX hYt ht2 hEX hE3 hE27 hEt

theorem outer_involution_heis [Finite Y] (hO : CFSG.pCore 2 Y = ⊥) {X : Subgroup Y}
    (hX : X.Normal) (hXH : Sec4.IsHeisSLThreeFour X) {t : Y} {E : Subgroup Y} (htX : t ∉ X)
    (hYt : X ⊔ Subgroup.zpowers t = ⊤) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (hEX : E ≤ X)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y))
    (hB : ∀ B : Subgroup Y, B ≤ E → Nat.card B = 9 →
      ¬ CFSG.perfectResidual Y ≤ Subgroup.centralizer (B : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  have := hX
  obtain ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩ := hXH
  have hLV : ⁅X, X⁆ = V.map X.subtype := by
    rw [← Subgroup.map_subtype_commutator, commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3]
  exact outer_involution_heis_of hO hX hsup hUV hU eV h3 hLV rfl htX hYt ht2 hEX hE hE27 hEt hB

end CFSG.RankThree.PartTwo.KFacts.KS18
