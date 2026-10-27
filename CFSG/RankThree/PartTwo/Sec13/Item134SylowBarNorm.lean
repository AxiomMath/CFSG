module

public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem eq_S_of_le_K (H : Base A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S)
    {X : Subgroup G} (hSX : S ≤ X) (hXK : X ≤ K) (hX : IsPGroup 3 X) : X = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X' := X.subgroupOf K with hX'
  have hX'p : IsPGroup 3 X' := hX.comap_subtype
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hX'p
  have hdvd : Nat.card X' ∣ 1080 := by
    rw [← card_map_eq_of_injOn _ hinj, ← card_eq_of_isTripleCover_six H.tripleCover]
    exact Subgroup.card_subgroup_dvd_card _
  have hXX' : Nat.card X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hXX', hn] at hdvd
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h81 : 3 ^ 4 ∣ 1080 := (pow_dvd_pow 3 (by omega : 4 ≤ n)).trans hdvd
    norm_num at h81
  refine (Subgroup.eq_of_le_of_card_ge hSX ?_).symm
  rw [hn, hSD.card_eq]
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 27 := by norm_num

omit [Finite G] in
theorem B_le_centralizer {S T : Subgroup G} (hTD : TData A c L d S T) :
    Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer (T : Set G) := by
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · exact Subgroup.mem_centralizer_iff.mpr fun τ hτ =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_c hτ)
  · exact Subgroup.mem_centralizer_iff.mpr fun τ hτ =>
      Subgroup.mem_centralizer_singleton_iff.mp (hTD.le_d hτ)

theorem conj_mem_B (H : Base A c L d K) {S T : Subgroup G} (hTD : TData A c L d S T) {y : G}
    (hyT : y ∈ Subgroup.normalizer (T : Set G)) {b : G}
    (hb : b ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    y * b * y⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have hbA : b ∈ A := H.B_le hb
  have hbT : b ∈ T := hTD.A_le hbA
  refine hTD.mem_B _ ((Subgroup.mem_normalizer_iff.mp hyT b).mp hbT) (fun τ hτ => ?_) ?_
  · have hτ' : y⁻¹ * τ * y ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyT) τ).mp hτ
      simpa using this
    have h1 : b * (y⁻¹ * τ * y) = (y⁻¹ * τ * y) * b :=
      (Subgroup.mem_centralizer_iff.mp (B_le_centralizer hTD hb) _ hτ').symm
    calc y * b * y⁻¹ * τ = y * (b * (y⁻¹ * τ * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * τ * y) * b) * y⁻¹ := by rw [h1]
      _ = τ * (y * b * y⁻¹) := by group
  · rw [conj_pow, H.data.isElemAbelian.2 b hbA, mul_one, mul_inv_cancel]

theorem commute_c_of_pow
    (H : Base A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) {y : G} (hyT : y ∈ Subgroup.normalizer (T : Set G))
    (hyd : y * d = d * y) {k : ℕ} (hy : y ^ 3 ^ k = 1) : y * c = c * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdL := H.d_mem_L
  have hSp : IsPGroup 3 S := hSD.isSylowOf.isPGroup
  have hTp : IsPGroup 3 T := hTD.isSylowOf.isPGroup
  have hY3 : IsPGroup 3 (Subgroup.zpowers y) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  set Y₁ := T ⊔ Subgroup.zpowers y with hY₁def
  have hY₁ : IsPGroup 3 Y₁ := hTp.to_sup_of_normal_left' hY3 (Subgroup.zpowers_le.mpr hyT)
  have hY₁d : Y₁ ≤ Subgroup.centralizer ({d} : Set G) :=
    sup_le hTD.le_d (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hyd))
  have hY₁K : Y₁ ≤ Subgroup.normalizer (K : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt H.h45 H.data.toTheoremFourHyp H.orderOf_d
      H.mem_K hY₁ (fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hY₁d hx))
  have hSeq : Y₁ ⊓ K = S :=
    H.eq_S_of_le_K hSD (le_inf (hTD.S_le.trans le_sup_left) hSD.le_K) inf_le_right
      (hY₁.to_le inf_le_left)
  have hyY : y ∈ Y₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro s hs
    have hsY : s ∈ Y₁ ⊓ K := hSeq.symm ▸ hs
    rw [← hSeq]
    exact Subgroup.mem_inf.mpr ⟨Y₁.mul_mem (Y₁.mul_mem hyY hsY.1) (Y₁.inv_mem hyY),
      (Subgroup.mem_normalizer_iff.mp (hY₁K hyY) s).mp hsY.2⟩
  have hyNS : Subgroup.zpowers y ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun s hs => hyS s hs)
  set C₀ := ⁅S, Subgroup.zpowers y⁆ with hC₀def
  have hSne : S ≠ ⊥ := by
    intro h
    have := hSD.card_eq
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hC₀ : C₀ < S :=
    CFSG.GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups S (Subgroup.zpowers y) hSp
      hY3 hyNS hSne
  have hC₀S : C₀ ≤ S := hC₀.le
  have hcommC₀ : ∀ e ∈ S, y * e * y⁻¹ * e⁻¹ ∈ C₀ := by
    intro e he
    have h1 : ⁅e, y⁆ ∈ C₀ := Subgroup.commutator_mem_commutator he (Subgroup.mem_zpowers y)
    have h2 : y * e * y⁻¹ * e⁻¹ = ⁅e, y⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [h2]
    exact inv_mem h1
  have hdS : d ∈ S := hSD.inf_le ⟨H.mem_A, hdL⟩
  obtain ⟨E, hES, hdE, hE9, hC₀E⟩ : ∃ E : Subgroup G, E ≤ S ∧ d ∈ E ∧ Nat.card E = 9 ∧
      C₀ ≤ E := by
    by_cases hC₀d : C₀ ≤ Subgroup.zpowers d
    · exact ⟨A ⊓ L, hSD.inf_le, ⟨H.mem_A, hdL⟩, H.card_inf,
        hC₀d.trans (Subgroup.zpowers_le.mpr ⟨H.mem_A, hdL⟩)⟩
    · refine ⟨C₀ ⊔ Subgroup.zpowers d, sup_le hC₀S (Subgroup.zpowers_le.mpr hdS),
        Subgroup.mem_sup_right (Subgroup.mem_zpowers d), ?_, le_sup_left⟩
      have hdvd : Nat.card C₀ ∣ 27 := hSD.card_eq ▸ Subgroup.card_dvd_of_le hC₀S
      have hne27 : Nat.card C₀ ≠ 27 := fun h =>
        hC₀.ne (Subgroup.eq_of_le_of_card_ge hC₀S (by rw [h, hSD.card_eq]))
      have hcd : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, H.orderOf_d]
      have hcomm : ∀ x ∈ C₀, ∀ z ∈ Subgroup.zpowers d, x * z = z * x := by
        intro x hx z hz
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
          (hSD.le_centralizer (hC₀S hx))) j).eq
      obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
      have hdiv27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      have hmem : Nat.card C₀ ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      rw [hdiv27] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h3 | h9 | h27
      · exact absurd ((Subgroup.eq_bot_of_card_eq C₀ h1).symm ▸ bot_le) hC₀d
      · have hinf : C₀ ⊓ Subgroup.zpowers d = ⊥ := by
          have hdvd' : Nat.card ↥(C₀ ⊓ Subgroup.zpowers d) ∣ 3 :=
            h3 ▸ Subgroup.card_dvd_of_le inf_le_left
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h | h
          · exact Subgroup.eq_bot_of_card_eq _ h
          · exfalso
            apply hC₀d
            have heq : C₀ ⊓ Subgroup.zpowers d = C₀ :=
              Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h3])
            exact heq ▸ inf_le_right
        rw [hinf, Subgroup.card_bot, mul_one, h3, hcd] at hcard
        exact hcard
      · have hdC₀ : d ∈ C₀ := hSD.mem_of_card C₀ hC₀S h9
        rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hdC₀), h9]
      · exact absurd h27 hne27
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    have h1 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
    rw [h1]
    exact mul_mem (hC₀E (hcommC₀ e (hES he))) he
  have hEL : E ≤ L := hES.trans hSD.isSylowOf.le
  set A' := Subgroup.zpowers c ⊔ E with hA'def
  have hcE : ∀ x ∈ Subgroup.zpowers c, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (H.comm_L (hEL he)).symm j).eq
  have hA'27 : Nat.card A' = 27 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcE
    rw [zpowers_inf_eq_bot H.c_pow (fun hcE' => H.not_mem_L (hEL hcE')), Subgroup.card_bot,
      mul_one, H.data.card_zpowers, hE9] at hcard
    exact hcard
  have hBA' : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A' :=
    sup_le le_sup_left ((Subgroup.zpowers_le.mpr hdE).trans le_sup_right)
  have hyA' : y ∈ Subgroup.normalizer (A' : Set G) := by
    have hle : A' ≤ A'.comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun e he => ?_)
      · exact hBA' (H.conj_mem_B hTD hyT (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
      · exact le_sup_right (b := E) (hyE e he)
    exact Subgroup.mem_normalizer_fintype fun a ha => hle ha
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hcC : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => H.comm_L hl
  have hAle : A ≤ Subgroup.zpowers c ⊔ L := by
    conv_lhs => rw [H.eq_sup]
    exact sup_le_sup_left inf_le_right _
  obtain ⟨g, hgL, hgA⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot H.h415
    hN3 H.quot hcC H.not_mem_L H.c_pow (sup_le_sup_left hEL _) hAle
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) H.data.mem_A hA'27 H.data.card_eq
  have hconjA : ∀ a ∈ A', g⁻¹ * a * g ∈ A := by
    intro a ha
    rw [hgA]
    exact ⟨a, ha, by simp⟩
  have hconjA' : ∀ a ∈ A, g * a * g⁻¹ ∈ A' := by
    intro a ha
    rw [hgA] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    simpa [MulAut.conj_apply, mul_assoc] using ha'
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [H.data.card_eq]; norm_num)
  have hgdA : g⁻¹ * d * g ∈ A := hconjA d (hBA' (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  have hgdL : g⁻¹ * d * g ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hgL) hdL) hgL
  have hgd1 : g⁻¹ * d * g ≠ 1 := by
    intro h
    apply H.ne_one
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨hdL', S₀, hdS₀, hS₀d⟩ := H.exists_d_mem_L
  have hcgd := central_conj (Subgroup.le_normalizer (L.inv_mem hgL)) hdL ⟨S₀, hdS₀, hS₀d⟩
    (by rw [inv_inv]; exact hgdL)
  simp only [inv_inv] at hcgd
  have hzz := zpowers_eq_of_central_of_quot_j2 H.h415 H.quot hAp H.mem_A hgdA hdL hgdL H.ne_one
    hgd1 ⟨S₀, hdS₀, hS₀d⟩ hcgd
  set y' := g⁻¹ * y * g with hy'
  have hy'A : y' ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hyA' _).mp (hconjA' a ha)
    have h2 := hconjA _ h1
    have h3 : g⁻¹ * (y * (g * a * g⁻¹) * y⁻¹) * g = y' * a * y'⁻¹ := by rw [hy']; group
    rw [h3] at h2
    exact h2
  have hy'gd : y' * (g⁻¹ * d * g) = (g⁻¹ * d * g) * y' := by
    calc y' * (g⁻¹ * d * g) = g⁻¹ * (y * d) * g := by rw [hy']; group
      _ = g⁻¹ * (d * y) * g := by rw [hyd]
      _ = (g⁻¹ * d * g) * y' := by rw [hy']; group
  have hy'd : y' * d = d * y' := by
    have hdmem : d ∈ Subgroup.zpowers (g⁻¹ * d * g) := hzz ▸ Subgroup.mem_zpowers d
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hdmem
    rw [← hj]
    exact (Commute.zpow_right (show Commute y' (g⁻¹ * d * g) from hy'gd) j).eq
  have hy'k : y' ^ 3 ^ k = 1 := by
    rw [hy', show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv, hy, mul_one,
      inv_mul_cancel]
  have hY'3 : IsPGroup 3 (Subgroup.zpowers y') := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy'k)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hle : Subgroup.zpowers y' ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hy'A, mem_normalizer_zpowers_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hy'd)⟩
  obtain ⟨P, hP, hyP⟩ := exists_isSylowOf_le hle hY'3
  have hPc := le_centralizer_of_mem_center_map
    (H.le_center P hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
  have hy'c : y' * c = c * y' :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPc (hyP (Subgroup.mem_zpowers y')))
  have hgc : g * c = c * g := H.comm_L hgL
  have hgc' : g⁻¹ * c = c * g⁻¹ := (Commute.inv_left (show Commute g c from hgc)).eq
  calc y * c = g * y' * g⁻¹ * c := by rw [hy']; group
    _ = g * (y' * c) * g⁻¹ := by rw [mul_assoc (g * y'), hgc']; group
    _ = g * (c * y') * g⁻¹ := by rw [hy'c]
    _ = c * y := by rw [← mul_assoc, hgc, hy']; group

theorem mem_normalizer_zpowers_c
    (H : Base A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) {x : G} (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxd : x ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨t, htT, htc, htd⟩ := H.exists_conj_inv hTD
  have hd3 := H.d_pow
  have htinv : ∀ δ ∈ Subgroup.zpowers d, t * δ * t⁻¹ = δ⁻¹ := by
    intro δ hδ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    rw [← conj_zpow, htd, inv_zpow]
  have hxinvd : ∀ δ ∈ Subgroup.zpowers d, x⁻¹ * δ * x ∈ Subgroup.zpowers d := by
    intro δ hδ
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxd) δ).mp hδ
    simpa using this
  have hxdd : ∀ δ ∈ Subgroup.zpowers d, x * δ * x⁻¹ ∈ Subgroup.zpowers d := fun δ hδ =>
    (Subgroup.mem_normalizer_iff.mp hxd δ).mp hδ
  have hu : x⁻¹ * c * x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    have := H.conj_mem_B hTD (inv_mem hxT) (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    simpa using this
  have hcC : c ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro δ hδ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
    exact (Commute.zpow_left (show Commute d c from H.comm_cd.symm) j).eq
  obtain ⟨i, ℓ, hℓ, hui⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcC hu
  set w := x * t * x⁻¹ * t⁻¹ with hw
  have hwT : w ∈ Subgroup.normalizer (T : Set G) :=
    mul_mem (mul_mem (mul_mem hxT htT) (inv_mem hxT)) (inv_mem htT)
  have htinv' : t⁻¹ * d * t = d⁻¹ := by
    have h1 : t⁻¹ * d⁻¹ * t = d := by rw [← htd]; group
    calc t⁻¹ * d * t = (t⁻¹ * d⁻¹ * t)⁻¹ := by group
      _ = d⁻¹ := by rw [h1]
  have hwd : w * d * w⁻¹ = d := by
    have h1 : t * (x⁻¹ * d * x)⁻¹ * t⁻¹ = x⁻¹ * d * x := by
      rw [htinv _ (inv_mem (hxinvd d (Subgroup.mem_zpowers d))), inv_inv]
    calc w * d * w⁻¹ = x * (t * (x⁻¹ * (t⁻¹ * d * t) * x) * t⁻¹) * x⁻¹ := by rw [hw]; group
      _ = x * (t * (x⁻¹ * d * x)⁻¹ * t⁻¹) * x⁻¹ := by rw [htinv']; group
      _ = d := by rw [h1]; group
  have hwc : w * c * w⁻¹ = c * (x * ℓ⁻¹ ^ 2 * x⁻¹) := by
    have htc' : t⁻¹ * c * t = c := by
      rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
    have htl : t * (c ^ i * ℓ) * t⁻¹ = c ^ i * ℓ⁻¹ := by
      have h1 : t * c ^ i * t⁻¹ = c ^ i := by
        rw [← conj_zpow, htc, mul_inv_cancel_right]
      calc t * (c ^ i * ℓ) * t⁻¹ = (t * c ^ i * t⁻¹) * (t * ℓ * t⁻¹) := by group
        _ = c ^ i * ℓ⁻¹ := by rw [h1, htinv ℓ hℓ]
    have hxu : x * (c ^ i * ℓ) * x⁻¹ = c := by rw [← hui]; group
    calc w * c * w⁻¹ = x * (t * (x⁻¹ * (t⁻¹ * c * t) * x) * t⁻¹) * x⁻¹ := by rw [hw]; group
      _ = x * (t * (c ^ i * ℓ) * t⁻¹) * x⁻¹ := by rw [htc', hui]
      _ = x * (c ^ i * ℓ) * x⁻¹ * (x * ℓ⁻¹ ^ 2 * x⁻¹) := by rw [htl]; group
      _ = c * (x * ℓ⁻¹ ^ 2 * x⁻¹) := by rw [hxu]
  set δ := x * ℓ⁻¹ ^ 2 * x⁻¹ with hδdef
  have hδ : δ ∈ Subgroup.zpowers d := hxdd _ (pow_mem (inv_mem hℓ) 2)
  have hwδ : w * δ = δ * w := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hδ
    have hwd' : w * d = d * w := by
      calc w * d = w * d * w⁻¹ * w := by group
        _ = d * w := by rw [hwd]
    rw [← hj]
    exact (Commute.zpow_right (show Commute w d from hwd') j).eq
  have hpow : ∀ n : ℕ, w ^ n * c * (w ^ n)⁻¹ = c * δ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hwδn : w * δ ^ n * w⁻¹ = δ ^ n := by
        rw [← conj_pow, show w * δ * w⁻¹ = δ by rw [hwδ, mul_inv_cancel_right]]
      calc w ^ (n + 1) * c * (w ^ (n + 1))⁻¹ = w * (w ^ n * c * (w ^ n)⁻¹) * w⁻¹ := by
            rw [pow_succ']; group
        _ = w * c * w⁻¹ * (w * δ ^ n * w⁻¹) := by rw [ih]; group
        _ = c * δ ^ (n + 1) := by rw [hwc, hwδn, pow_succ', mul_assoc]
  obtain ⟨e, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' 3
    (by norm_num)
  set y := w ^ m with hydef
  have hy3 : y ^ 3 ^ e = 1 := by
    rw [hydef, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hyT : y ∈ Subgroup.normalizer (T : Set G) := pow_mem hwT m
  have hyd : y * d = d * y := by
    have hwd' : w * d = d * w := by
      calc w * d = w * d * w⁻¹ * w := by group
        _ = d * w := by rw [hwd]
    exact (Commute.pow_left (show Commute w d from hwd') m).eq
  have hyc := H.commute_c_of_pow hSD hTD hyT hyd hy3
  have hδm : δ ^ m = 1 := by
    have h1 := hpow m
    rw [← hydef, show y * c * y⁻¹ = c by rw [hyc, mul_inv_cancel_right]] at h1
    have h2 : c * δ ^ m = c * 1 := by rw [mul_one, ← h1]
    exact mul_left_cancel h2
  have hδ1 : δ = 1 := by
    have hδ3 : δ ^ 3 = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hδ
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
    have h1 : orderOf δ ∣ Nat.gcd 3 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδ3) (orderOf_dvd_of_pow_eq_one hδm)
    have hcop : Nat.gcd 3 m = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hℓ1 : ℓ = 1 := by
    have h1 : ℓ⁻¹ ^ 2 = 1 := by
      have : x * ℓ⁻¹ ^ 2 * x⁻¹ = 1 := hδ1
      calc ℓ⁻¹ ^ 2 = x⁻¹ * (x * ℓ⁻¹ ^ 2 * x⁻¹) * x := by group
        _ = 1 := by rw [this]; group
    have hℓ3 : ℓ ^ 3 = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hℓ
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
    calc ℓ = ℓ ^ 3 * (ℓ⁻¹ ^ 2) := by group
      _ = 1 := by rw [hℓ3, h1, one_mul]
  rw [hℓ1, mul_one] at hui
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hconj : x⁻¹ * c ^ j * x⁻¹⁻¹ = (x⁻¹ * c * x) ^ j := by
      have := conj_zpow (a := x⁻¹) (b := c) (i := j)
      simpa using this.symm
    rw [SetLike.mem_coe, hconj, hui, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers c _
  simpa using inv_mem hxinv

end Base

end CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
