module

public import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofTorus
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof158Cartan

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

variable {G : Type} [Group G] [Finite G]

theorem exists_of_ne_omegaOneThree {F P : Subgroup G} (hFP : F ≤ P)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hP : IsPGroup 3 P) (hne : F ≠ omegaOneThree P) :
    ∃ x ∈ P, x ∈ Subgroup.normalizer (F : Set G) ∧ x ∉ F ∧ x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hΩN : ∀ x ∈ P, x ∈ Subgroup.normalizer (F : Set G) → x ^ 3 = 1 → x ∈ F := by
    intro x hxP hxN hx3
    by_contra hxF
    exact hcon x hxP hxN hxF hx3
  have hFN : F ≤ Subgroup.normalizer (F : Set G) := Subgroup.le_normalizer
  set N : Subgroup ↥P := (Subgroup.normalizer (F : Set G)).subgroupOf P with hNdef
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hnc
  have hself : Subgroup.normalizer (N : Set ↥P) = N := by
    refine le_antisymm (fun y hy => ?_) Subgroup.le_normalizer
    rw [hNdef, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_normalizer_fintype fun f hf => ?_
    have hfP : f ∈ P := hFP hf
    have hfN : (⟨f, hfP⟩ : ↥P) ∈ N := Subgroup.mem_subgroupOf.mpr (hFN hf)
    have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨f, hfP⟩).mp hfN
    have h2 : (y : G) * f * (y : G)⁻¹ ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.mem_subgroupOf.mp h1
    have h3 : ((y : G) * f * (y : G)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hF.2 f hf, mul_one, mul_inv_cancel]
    exact hΩN _ (P.mul_mem (P.mul_mem y.2 hfP) (P.inv_mem y.2)) h2 h3
  have hNtop : N = ⊤ := hnc N hself
  have hPN : P ≤ Subgroup.normalizer (F : Set G) := fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥P) ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1
  apply hne
  apply le_antisymm
  · intro f hf
    exact Subgroup.subset_closure ⟨hFP hf, hF.2 f hf⟩
  · rw [omegaOneThree, Subgroup.closure_le]
    rintro x ⟨hxP, hx3⟩
    exact hΩN x hxP (hPN hxP) hx3

theorem eq_one_of_mem_theta_of_isPGroup {L P : Subgroup G} (hP : IsPGroup 3 P) {g : G}
    (hgP : g ∈ P) (hgθ : g ∈ inSubgroup (aschbacherSolvableCore 3) L) : g = 1 := by
  obtain ⟨g', hg', rfl⟩ := hgθ
  obtain ⟨k, hk⟩ := hP ⟨g', hgP⟩
  have hk' : g' ^ 3 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [Sec19.Step1914TriProof.eq_one_of_mem_theta' hg' hk', map_one]

theorem exists_cartan_of_pair (hFE : partTwoF G = partTwoE G) {L P F U : Subgroup G} {c : G}
    (hcL : c ∉ L) (hc3 : c ^ 3 = 1) (hLc : ∀ l ∈ L, l * c = c * l)
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hP3 : IsPGroup 3 P)
    (hFP : F ≤ P) (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF27 : Nat.card F = 27)
    (hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L))
    (hsecF : ∀ a ∈ F, a ∈ thetaQuotCentralizer L → a ∈ Subgroup.zpowers c)
    (hΩ : F ≠ omegaOneThree P)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8))
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projImage (slPi π 3 (p ^ f) K)) :
    ∃ E : Subgroup G, E ≤ P ∧ c ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      IsTypeCOn E L ∧ F ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcF : c ∈ F := by rw [hFeq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  obtain ⟨x, hxP, hxN, hxF, hx3⟩ := exists_of_ne_omegaOneThree hFP hF hP3 hΩ
  have hx1 : x ≠ 1 := fun h1 => hxF (h1 ▸ F.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxc : x * c = c * x := by
    have hmem : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hPH hxP) c).mp (Subgroup.mem_zpowers c)
    exact Sec12.commute_of_conj_mem_zpowers hco hmem (k := 1) (by rw [pow_one]; exact hx3)
  have hxFN : ∀ t ∈ F, x * t * x⁻¹ ∈ F := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp hxN t).mp ht
  set P' := F ⊔ Subgroup.zpowers x with hP'def
  have hP'P : P' ≤ P := sup_le hFP (Subgroup.zpowers_le.mpr hxP)
  have hP'3 : IsPGroup 3 P' := hP3.to_le hP'P
  have hcP' : c ∈ P' := Subgroup.mem_sup_left hcF
  have hP'81 : Nat.card P' = 81 := by
    have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have h1 := Sec6.card_sup_mul_card_inf hXN
    rw [Sec13.zpowers_inf_eq_bot hx3 hxF, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo,
      hF27, sup_comm] at h1
    rw [hP'def]
    omega
  have hP'N : P' ≤ Subgroup.normalizer (L : Set G) := hP'P.trans hPL
  set φ : ↥P' →* Subgroup.normalizer (L : Set G) ⧸
      L.subgroupOf (Subgroup.normalizer (L : Set G)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hP'N) with hφdef
  have hφ1 : ∀ g : ↥P', φ g = 1 → (g : G) ∈ L := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact h
  have hφL : ∀ g : ↥P', (g : G) ∈ L → φ g = 1 := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  have hpow : ∀ g : ↥P', (g : G) ^ 3 = 1 → g ^ 3 = 1 := fun g h =>
    Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  have hxP' : x ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  set Q := Subgroup.zpowers (φ ⟨c, hcP'⟩) ⊔ Subgroup.zpowers (φ ⟨x, hxP'⟩) with hQdef
  have hQab : CFSG.Assembly.IsElemAbelian 3 Q :=
    Sec13.isElemAbelian_zpowers_sup (by rw [← map_pow, hpow _ hc3, map_one])
      (by rw [← map_pow, hpow _ hx3, map_one])
      (by rw [← map_mul, ← map_mul]; exact congrArg φ (Subtype.ext hxc.symm))
  have hφQ : ∀ g : ↥P', φ g ∈ Q := by
    have hle : P' ≤ (Q.comap φ).map P'.subtype := by
      refine sup_le (hFeq.le.trans (sup_le ?_ ?_)) ?_
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨c, hcP'⟩, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), rfl⟩
      · intro b hb
        have hbP' : b ∈ P' := Subgroup.mem_sup_left hb.1
        refine ⟨⟨b, hbP'⟩, ?_, rfl⟩
        change φ ⟨b, hbP'⟩ ∈ Q
        rw [hφL _ hb.2]
        exact Q.one_mem
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨x, hxP'⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), rfl⟩
    intro g
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have := hQab.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  have hmodL : ∀ a ∈ P', ∀ b ∈ P', a * b * a⁻¹ * b⁻¹ ∈ L := by
    intro a ha b hb
    have h1 := hφ1 (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommQ _ (hφQ _) _ (hφQ _)]
      group)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hcubeL : ∀ a ∈ P', a ^ 3 ∈ L := by
    intro a ha
    have h1 := hφ1 (⟨a, ha⟩ ^ 3) (by rw [map_pow]; exact hQab.2 _ (hφQ _))
    simpa only [Subgroup.coe_pow] using h1
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hker : ∀ a ∈ P', a ∈ thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a ha haC
    obtain ⟨-, haθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp haC
    have haB : ∀ b ∈ F ⊓ L, a * b = b * a := by
      intro b hb
      have h1 := haθ b hb.2
      have hbP' : b ∈ P' := Subgroup.mem_sup_left hb.1
      have h2 : b⁻¹ * (a * b * a⁻¹) ∈ P' :=
        P'.mul_mem (P'.inv_mem hbP') (P'.mul_mem (P'.mul_mem ha hbP') (P'.inv_mem ha))
      have h3 := eq_one_of_mem_theta_of_isPGroup hP'3 h2 h1
      calc a * b = b * (b⁻¹ * (a * b * a⁻¹)) * a := by group
        _ = b * a := by rw [h3, mul_one]
    have hac : a * c = c * a := by
      have hmem : a * c * a⁻¹ ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff.mp (hPH (hP'P ha)) c).mp (Subgroup.mem_zpowers c)
      obtain ⟨k, hk⟩ := hP'3 ⟨a, ha⟩
      have hk' : a ^ 3 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      exact Sec12.commute_of_conj_mem_zpowers hco hmem hk'
    have haF : a ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Subgroup.zpowers c ⊔ (F ⊓ L) := hFeq ▸ hh
      have hcB : c * a = a * c := hac.symm
      have hc' : ∀ g ∈ Subgroup.zpowers c ⊔ (F ⊓ L), g * a = a * g := by
        intro g hg
        have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤ Subgroup.centralizer ({a} : Set G) :=
          sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac.symm))
            (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (haB b hb).symm)
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg))
      exact hc' h hh'
    obtain ⟨t, htF, m, hm3, rfl⟩ := Sec13.exists_mul_pow_of_mem_sup hx3 hxFN ha
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · rw [pow_zero, mul_one] at haF haC ⊢
      exact hsecF t htF haC
    all_goals exfalso
    all_goals
      have htC : t⁻¹ ∈ Subgroup.centralizer (F : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun h hh => hFc h hh _ (F.inv_mem htF)
    · have hxC : x ∈ Subgroup.centralizer (F : Set G) := by
        have := Subgroup.mul_mem _ htC haF
        rwa [← mul_assoc, inv_mul_cancel, one_mul, pow_one] at this
      exact Sec12.false_of_le_E81 hFE hF hF27 hU hU2 (hFP.trans hPU) hxC hxo hxF
    · have hx2C : x ^ 2 ∈ Subgroup.centralizer (F : Set G) := by
        have := Subgroup.mul_mem _ htC haF
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      have hxC : x ∈ Subgroup.centralizer (F : Set G) := by
        have h4 := Subgroup.pow_mem _ hx2C 2
        rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one] at h4
      exact Sec12.false_of_le_E81 hFE hF hF27 hU hU2 (hFP.trans hPU) hxC hxo hxF
  obtain ⟨E, hEP', hcE, hE, hE27, hsec, hTC, hNE⟩ :=
    exists_cartan_of_card hcL hc3 hLc hP'N hP'3 hcP' hmodL hcubeL hker hP'81 hK hq hq2 h9 e
  exact ⟨E, hEP'.trans hP'P, hcE, hE, hE27, hsec, hTC, le_sup_left.trans hNE⟩

end CFSG.RankThree.PartTwo.Sec15.Proof158Cartan
