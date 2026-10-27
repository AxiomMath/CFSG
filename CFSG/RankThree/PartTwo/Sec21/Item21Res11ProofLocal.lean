module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofU4Sig
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4KFinal
public import CFSG.RankThree.PartTwo.Sec21.Item21Res11ProofGroup
public import CFSG.RankThree.PartTwo.Sec21.Item21Res11ProofBlock
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofCyclic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item21Res11Proof

open Subgroup
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec21.U4OddLines

variable {G : Type} [Group G] [Finite G]

theorem no_comm_of_item45 (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {n : ℕ} (hn1 : 1 < n) (eL : L ≃* projSU 4 2 n)
    {f : ℕ} {K : Type} [Field K] (C : U4OddCtx G L A c f K)
    (hPsyl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤
      normalizer ((zpowers c : Subgroup G) : Set G))
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ normalizer ((zpowers c : Subgroup G) : Set G) →
      g * c * g⁻¹ ∈ zpowers c)
    (x y : G) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : ⁅x, y⁆ ∈ zpowers c) (hxy1 : ⁅x, y⁆ ≠ 1)
    (hp : IsPGroup 3 (closure ({x, y} : Set G))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.hAe
  have hc3 : c ^ 3 = 1 := hAe.2 c C.hcA
  obtain ⟨P, hPH⟩ := hPsyl
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q P
  have hmem : ∀ u ∈ (Q : Subgroup G), h * u * h⁻¹ ∈ (P : Subgroup G) := by
    intro u hu
    rw [← hh, Sylow.coe_subgroup_smul]
    have := smul_mem_pointwise_smul u (MulAut.conj h) (Q : Subgroup G) hu
    simpa [MulAut.smul_def] using this
  have hxP : h * x * h⁻¹ ∈ (P : Subgroup G) :=
    hmem x (hQ (subset_closure (Set.mem_insert _ _)))
  have hyP : h * y * h⁻¹ ∈ (P : Subgroup G) :=
    hmem y (hQ (subset_closure (Set.mem_insert_of_mem _ rfl)))
  have hx3 : (h * x * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hy3 : (h * y * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hy, mul_one, mul_inv_cancel]
  obtain ⟨ℓ₁, hℓ₁, -, i, hi⟩ :=
    Item2113Res3Proof.exists_mul_zpow_of_mem_normalizer h45 hpair hn1 eL C (hPH hxP) hx3
  obtain ⟨ℓ₂, hℓ₂, -, j, hj⟩ :=
    Item2113Res3Proof.exists_mul_zpow_of_mem_normalizer h45 hpair hn1 eL C (hPH hyP) hy3
  have hu1 : c ^ i * ℓ₂ = ℓ₂ * c ^ i :=
    ((Commute.zpow_right (show Commute ℓ₂ c from C.comm_c hℓ₂) i)).eq.symm
  have hv1 : c ^ j * ℓ₁⁻¹ = ℓ₁⁻¹ * c ^ j :=
    ((Commute.zpow_right (show Commute ℓ₁⁻¹ c from C.comm_c (L.inv_mem hℓ₁)) j)).eq.symm
  have huv : c ^ i * c ^ j * (c ^ i)⁻¹ = c ^ j := by
    rw [← zpow_add, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  have hcomm : h * ⁅x, y⁆ * h⁻¹ = ⁅ℓ₁, ℓ₂⁆ := by
    have e1 : h * ⁅x, y⁆ * h⁻¹ = ⁅h * x * h⁻¹, h * y * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hi, hj]
    simp only [commutatorElement_def]
    calc ℓ₁ * c ^ i * (ℓ₂ * c ^ j) * (ℓ₁ * c ^ i)⁻¹ * (ℓ₂ * c ^ j)⁻¹
        = ℓ₁ * (c ^ i * ℓ₂) * c ^ j * (c ^ i)⁻¹ * ℓ₁⁻¹ * (c ^ j)⁻¹ * ℓ₂⁻¹ := by group
      _ = ℓ₁ * ℓ₂ * (c ^ i * c ^ j * (c ^ i)⁻¹) * ℓ₁⁻¹ * (c ^ j)⁻¹ * ℓ₂⁻¹ := by
          rw [hu1]; group
      _ = ℓ₁ * ℓ₂ * (c ^ j * ℓ₁⁻¹) * (c ^ j)⁻¹ * ℓ₂⁻¹ := by rw [huv]; group
      _ = ℓ₁ * ℓ₂ * ℓ₁⁻¹ * ℓ₂⁻¹ := by rw [hv1]; group
  have hcomL : h * ⁅x, y⁆ * h⁻¹ ∈ L := by
    rw [hcomm, commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hℓ₁ hℓ₂) (L.inv_mem hℓ₁)) (L.inv_mem hℓ₂)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxy
  have hc3' : c ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hc3]
  have hk3 : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨k', rfl⟩
    apply hxy1
    rw [← hk, zpow_mul, hc3', one_zpow]
  have hcl : c ∈ zpowers ⁅x, y⁆ := hk ▸ Item21Res9Proof.mem_zpowers_zpow_of_cube hc3 hk3
  have hhcL : h * c * h⁻¹ ∈ L := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hcl
    rw [← hm, ← conj_zpow]
    exact L.zpow_mem hcomL m
  have hLH : L ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
    intro l hl
    apply mem_normalizer_fintype
    intro z hz
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hz
    rw [C.conj_zpow_c hl m]
    exact zpow_mem (mem_zpowers c) m
  have hhc := hfus h (hLH hhcL)
  have hc1 : c ≠ 1 := fun h1 => C.hcL (h1 ▸ L.one_mem)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hhc1 : h * c * h⁻¹ ≠ 1 := by
    intro h1
    apply hc1
    calc c = h⁻¹ * (h * c * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  have hZ3 : Nat.card (zpowers c) = 3 := by rw [Nat.card_zpowers, hco]
  have heq := Sec17.Proof176Steps.eq_zpowers_of_card_three hZ3 hhc hhc1
  apply C.hcL
  have hcz : c ∈ zpowers (h * c * h⁻¹) := heq ▸ mem_zpowers c
  exact (zpowers_le.mpr hhcL) hcz

omit [Finite G] in
theorem mem_normalizer_sup {S O : Subgroup G} {g : G} (hS : g ∈ normalizer (S : Set G))
    (hO : g ∈ normalizer (O : Set G)) : g ∈ normalizer ((S ⊔ O : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hS hO ⊢
  rw [Subgroup.map_sup, hS, hO]

theorem eq_bot_of_le_normalClosureIn
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo)
    (h45 : Sec4.Item4_5)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) {n : ℕ} (hn1 : 1 < n)
    (eL : L ≃* projSU 4 2 n) {K : Type} [Field K] (C : U4OddCtx G L A c n K)
    (hPsyl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤
      normalizer ((zpowers c : Subgroup G) : Set G))
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ normalizer ((zpowers c : Subgroup G) : Set G) →
      g * c * g⁻¹ ∈ zpowers c)
    {F : Subgroup G} (hFE : F ≤ E) (hF9 : Nat.card F = 9) (hcF : c ∉ F)
    {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Late.normalClosureIn (centralizer (F : Set G)) c)
    (hcS : c ∈ normalizer (S : Set G)) : S = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := hpair.standing.toTheoremFourHyp
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hpair.mem_E.1.1
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hcE : c ∈ E := hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c C.hcA
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hFA : F ≤ A := hFE.trans hEA
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => C.commA ha hb
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  obtain ⟨i, hri⟩ := exists_root_not_mem C hζ hcE hE27
  set r := C.theta (rootVec ζ hζ.pow_eq_one i) with hr
  obtain ⟨Λ, hΛp, hΛL, hrΛ, hΛcen⟩ := exists_perfect_block C hζ.pow_eq_one i
  obtain ⟨f, hfF, hf1, d, k, hd, hfd⟩ := exists_mem_block C hFA (by rw [hF9]; norm_num) i
  have hΛc : Λ ≤ centralizer ({c} : Set G) := hΛL.trans C.hLc
  have hΛf : Λ ≤ centralizer ({f} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff, hfd]
    have h1 : x * C.theta d = C.theta d * x := mem_centralizer_singleton_iff.mp (hΛcen d hd hx)
    have h2 : x * c ^ k = c ^ k * x :=
      (Commute.zpow_right (show Commute x c from mem_centralizer_singleton_iff.mp (hΛc hx)) k).eq
    calc x * (C.theta d * c ^ k) = (x * C.theta d) * c ^ k := by group
      _ = C.theta d * (x * c ^ k) := by rw [h1]; group
      _ = C.theta d * c ^ k * x := by rw [h2]; group
  set Cf := centralizer ({f} : Set G) with hCfdef
  have hCf : Cf ≠ ⊤ := Sec6.centralizer_ne_top_of_ne_one hG hf1
  have hcCf : c ∈ Cf := mem_centralizer_singleton_iff.mpr (hAc c C.hcA f (hFA hfF))
  have hrank : CFSG.Open.pRank 3 (Late.normalClosureIn Cf c) ≤ 1 :=
    Sec20.Res5.pRank_normalClosureIn_le_one h432 h41 hG2 hG hCf hco hcCf
      (Item21Res9Proof.weak_of_fus hfus) (no_comm_of_item45 h45 hpair hn1 eL C hPsyl hfus)
  set X := Late.normalClosureIn Cf c with hXdef
  have hXtop : X ≠ ⊤ := fun h => hCf (eq_top_iff.mpr (h ▸ normalClosureIn_le hcCf))
  have hK : CFSG.IsKGroup ↥X := (hG.sectionFourHyp hXtop).kGroup
  have hrA : r ∈ A := C.theta_mem_A _
  have hr3 : r ^ 3 = 1 := hAe.2 r hrA
  have := hΛp
  obtain ⟨j, hj⟩ := exists_zpow_act_trivial hSch hco hrank hK hΛf hΛc hrΛ hr3
  set Y := Late.normalClosureIn (centralizer (F : Set G)) c with hYdef
  have hYX : Y ≤ X :=
    normalClosureIn_mono (centralizer_le (Set.singleton_subset_iff.mpr hfF)) c
  have hAF : A ≤ centralizer (F : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro x hx
    exact hAc x (hFA hx) a ha
  have hAY : A ≤ normalizer (Y : Set G) :=
    hAF.trans (le_normalizer_normalClosureIn (centralizer (F : Set G)) c)
  set dd := r * c ^ (-j) with hdd
  have hddA : dd ∈ A := A.mul_mem hrA (A.zpow_mem C.hcA _)
  have hddY := act_trivial_of_le hYX (hAY hddA) hj
  set O : Subgroup G := (CFSG.pPrimeCore 3 ↥Y).map Y.subtype with hO
  set Γ : Subgroup G := S ⊔ O with hΓ
  have hcF' : c ∈ centralizer (F : Set G) := hAF C.hcA
  have hYF : Y ≤ centralizer (F : Set G) := normalClosureIn_le hcF'
  have hOY : O ≤ Y := map_subtype_le _
  have hΓY : Γ ≤ Y := sup_le hSY hOY
  have hFΓ : F ≤ normalizer (Γ : Set G) := by
    intro x hx
    apply mem_normalizer_fintype
    intro g hg
    have hgx : x * g = g * x := mem_centralizer_iff.mp (hYF (hΓY hg)) x hx
    have : x * g * x⁻¹ = g := by rw [hgx]; group
    rw [this]
    exact hg
  have hcY : c ∈ Y := self_mem_normalClosureIn _ c
  have hcΓ : c ∈ normalizer (Γ : Set G) :=
    mem_normalizer_sup hcS (mem_normalizer_core (le_normalizer hcY))
  have hddO : dd ∈ normalizer (O : Set G) := mem_normalizer_core (hAY hddA)
  have hddΓ : dd ∈ normalizer (Γ : Set G) := by
    apply mem_normalizer_fintype
    have hmap : Γ.map (MulAut.conj dd).toMonoidHom ≤ Γ := by
      rw [hΓ, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have h1 := hddY s (hSY hs)
        have e : dd * s * dd⁻¹ = (dd * s * dd⁻¹ * s⁻¹) * s := by group
        rw [e]
        exact Γ.mul_mem (mem_sup_right h1) (mem_sup_left hs)
      · rintro _ ⟨o, ho, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.mp hddO o).mp ho)
    intro g hg
    exact hmap ⟨g, hg, rfl⟩
  have hrΓ : r ∈ normalizer (Γ : Set G) := by
    have e : r = dd * c ^ j := by rw [hdd, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
      mul_one]
    rw [e]
    exact mul_mem hddΓ (zpow_mem hcΓ j)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := Sec5.isElemAbelian_of_le hEe hFE
  obtain ⟨hFc, hFccard⟩ := Sec5.isElemAbelian_sup_zpowers hFe hcF hc3
    (fun a ha => hAc a (hFA ha) c C.hcA)
  have hFcE : F ⊔ zpowers c = E := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hFE (zpowers_le.mpr hcE))
    rw [hE27, hFccard, hF9]
  have hrE : r ∉ F ⊔ zpowers c := by rw [hFcE]; exact hri
  obtain ⟨-, hAcard⟩ := Sec5.isElemAbelian_sup_zpowers hFc hrE hr3
    (fun a ha => hAc a ((sup_le hFA (zpowers_le.mpr C.hcA)) ha) r hrA)
  have hAgen : A ≤ F ⊔ zpowers c ⊔ zpowers r := by
    have hle : F ⊔ zpowers c ⊔ zpowers r ≤ A :=
      sup_le (sup_le hFA (zpowers_le.mpr C.hcA)) (zpowers_le.mpr hrA)
    have heq : F ⊔ zpowers c ⊔ zpowers r = A := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [C.hA81, hAcard, hFccard, hF9]
      norm_num
    exact heq.ge
  have hAΓ : A ≤ normalizer (Γ : Set G) :=
    hAgen.trans (sup_le (sup_le hFΓ (zpowers_le.mpr hcΓ)) (zpowers_le.mpr hrΓ))
  have hΓ3 := not_three_dvd_card_sup hS2 hSY
  obtain ⟨P, hP⟩ := exists_sylow_two_normalized (Sec5.isPGroup_of_isElemAbelian hAe) hAΓ hΓ3
  by_contra hS1
  have h2 : 2 ∣ Nat.card Γ := by
    obtain ⟨m, hm⟩ := hS2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hS1 (Subgroup.eq_bot_of_card_eq S (by rw [hm, pow_zero]))
    exact (dvd_pow_self 2 hm0).trans (hm ▸ Subgroup.card_dvd_of_le le_sup_left)
  have hP1 : (P : Subgroup Γ).map Γ.subtype ≠ ⊥ := by
    intro h
    apply Sylow.ne_bot_of_dvd_card P h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h
  have h27 := Sec5.card_le_of_le_normalizer hpair.standing.evenRank_eq hP1 (P.isPGroup'.map _)
    hAe hP
  rw [C.hA81] at h27
  norm_num at h27

end Item21Res11Proof

open Item21Res11Proof
open Subgroup
open scoped commutatorElement

theorem item2115U4Local_of_res11
    (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo) (h45 : Sec4.Item4_5)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    Item2115U4Local := by
  intro G _ _ A E U c L hpair ⟨n, hn1, hno, ⟨eL⟩⟩ h81 hS4 _ hPsyl hfus e he _ T hT2 hET
  obtain ⟨C⟩ := Item2113Res3Proof.nonempty_u4OddCtx_of_pair hpair hn1 hno eL h81 hS4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hpair.mem_E.1.1
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hcE : c ∈ E := hpairs.1.1
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : ∀ H : Subgroup G, H ≤ E →
      E ≤ normalizer ((T ⊓ centralizer (H : Set G) : Subgroup G) : Set G) := by
    intro H hHE x hx
    apply mem_normalizer_fintype
    rintro t ⟨htT, htH⟩
    refine ⟨(mem_normalizer_iff.mp (hET hx) t).mp htT, mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hth : Commute h t := mem_centralizer_iff.mp htH h hh
    have hhx : Commute h x := hEc h (hHE hh) x hx
    exact ((hhx.mul_right hth).mul_right hhx.inv_right).eq
  have heE : zpowers e ≤ E := zpowers_le.mpr he
  have hTe : T ⊓ centralizer ({e} : Set G) =
      T ⊓ centralizer ((zpowers e : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcop : Nat.Coprime 3 (Nat.card (T ⊓ centralizer ({e} : Set G) : Subgroup G)) := by
    obtain ⟨m, hm⟩ := (hT2.to_le inf_le_left).exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  have hETe : E ≤ normalizer ((T ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G) := by
    rw [hTe]
    exact hnorm _ heE
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hEe
    (by rw [hE27]; norm_num) hETe hcop ?_
  intro H hHE hH9
  by_cases hcH : c ∈ H
  · intro t ht
    exact (centralizer_le (Set.singleton_subset_iff.mpr hcH)) ht.2
  ·
    set R : Subgroup G := T ⊓ centralizer ({e} : Set G) ⊓ centralizer (H : Set G) with hR
    have hR2 : IsPGroup 2 R := hT2.to_le (inf_le_left.trans inf_le_left)
    have hcR : c ∈ normalizer (R : Set G) := by
      have h1 : c ∈ normalizer ((T ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G) :=
        hETe hcE
      apply mem_normalizer_fintype
      rintro t ⟨htTe, htH⟩
      refine ⟨(mem_normalizer_iff.mp h1 t).mp htTe, mem_centralizer_iff.mpr ?_⟩
      intro h hh
      have hth : Commute h t := mem_centralizer_iff.mp htH h hh
      have hhc : Commute h c := hEc h (hHE hh) c hcE
      exact ((hhc.mul_right hth).mul_right hhc.inv_right).eq
    have hzc : zpowers c ≤ normalizer (R : Set G) := zpowers_le.mpr hcR
    set S := ⁅R, zpowers c⁆ with hSdef
    have hSR : S ≤ R := by
      rw [hSdef, commutator_le]
      intro t ht w hw
      have hw' : w * t⁻¹ * w⁻¹ ∈ R := (mem_normalizer_iff.mp (hzc hw) t⁻¹).mp (inv_mem ht)
      rw [commutatorElement_def]
      have e1 : t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
      rw [e1]
      exact mul_mem ht hw'
    have hS2 : IsPGroup 2 S := hR2.to_le hSR
    have hSY : S ≤ Late.normalClosureIn (centralizer (H : Set G)) c := by
      rw [hSdef, commutator_le]
      intro t ht w hw
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
      have hcY := self_mem_normalClosureIn (centralizer (H : Set G)) c
      have hgen : t * c * t⁻¹ ∈ Late.normalClosureIn (centralizer (H : Set G)) c :=
        Subgroup.subset_closure ⟨t, ht.2, rfl⟩
      have h1 : t * c ^ m * t⁻¹ ∈ Late.normalClosureIn (centralizer (H : Set G)) c := by
        rw [← conj_zpow]
        exact zpow_mem hgen m
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem (zpow_mem hcY m))
    have hcS : c ∈ normalizer (S : Set G) := by
      have h1 : R.map (MulAut.conj c).toMonoidHom ≤ R := by
        rintro _ ⟨t, ht, rfl⟩
        exact (mem_normalizer_iff.mp hcR t).mp ht
      have h2 : (zpowers c).map (MulAut.conj c).toMonoidHom ≤ zpowers c := by
        rw [MonoidHom.map_zpowers, zpowers_le]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_cancel_right]
        exact mem_zpowers c
      apply mem_normalizer_fintype
      intro s hs
      have h3 : (MulAut.conj c).toMonoidHom s ∈ S.map (MulAut.conj c).toMonoidHom :=
        mem_map_of_mem _ hs
      rw [hSdef, map_commutator] at h3
      exact commutator_mono h1 h2 h3
    have hS1 := eq_bot_of_le_normalClosureIn h432 h41 hG2 h45 hSch hpair hn1 eL C hPsyl hfus
      hHE hH9 hcH hS2 hSY hcS
    have hRc : R ≤ centralizer ((zpowers c : Subgroup G) : Set G) :=
      (commutator_eq_bot_iff_le_centralizer).mp hS1
    intro t ht
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hRc ht) c (mem_zpowers c)).symm

theorem item2115U4Ten_of_res11
    (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo) (h45 : Sec4.Item4_5)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    Item2115U4Ten :=
  Item2113Res2Proof.item2115U4Ten_of (Item2113Res3Proof.item2115U4Fusion_of_item45 h45)
    (item2115U4Local_of_res11 h432 h41 hG2 h45 hSch)

theorem item2115U4Signalizer_of_res11
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo)
    (h45 : Sec4.Item4_5)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    Item2115U4Signalizer := by
  intro G _ _ A E U c L hpair hU4 h81 hS4 hW
  exact (item2115U4Ten_of_res11 h432 h41 hG2 h45 hSch G A E U c L hpair hU4 h81 hS4 hW).elim

end CFSG.RankThree.PartTwo.Sec21
