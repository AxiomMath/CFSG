module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenPairB
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenKFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup CFSG.ASVolI.ChIJK
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s716C_conjSubgroup_le {K V : Subgroup G} (hVK : V ≤ K) {a : G} (ha : a ∈ K) :
    conjSubgroup V a ≤ K := by
  intro y hy
  have h1 : a * y * a⁻¹ ∈ V := Quasithin.mem_conjSubgroup_iff.mp hy
  have h2 : a * y * a⁻¹ ∈ K := hVK h1
  have h3 : y = a⁻¹ * (a * y * a⁻¹) * a := by group
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) h2) ha

theorem s716C_isMulCommutative_sup {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsMulCommutative ↥(A ⊔ B) := by
  have hle : (A ⊔ B : Subgroup Q) ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Q) : Set Q) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact setLike_mul_comm hu ht
    · exact (hAB t ht u hu).symm
    · exact hAB u hu t ht
    · exact setLike_mul_comm hu ht
  exact ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle x.2) y y.2).symm⟩⟩

theorem exists_good_conjugates (hF : PSUThreeRootFacts) {K V X : Subgroup G} (hVK : V ≤ K)
    (hV : IsElemAbelian 2 V) {P : Type} [Group P] [Finite P] {ψ : ↥K →* P}
    (hψ : Function.Surjective ψ) {n : ℕ} (hP : IsPSUGp P 3 n)
    (hcard : Nat.card ↥(barSub K ψ V) = 2 ^ n) (hXK : X ≤ K) (hXodd : Odd (Nat.card ↥X))
    (hXV : ∀ x v : ↥K, (x : G) ∈ X → (v : G) ∈ V → Commute (ψ x) (ψ v)) :
    ∃ a b : ↥K, ⁅V, conjSubgroup V (a : G)⁆ ≠ ⊥ ∧
      IsL2Gp ↥(barSub K ψ (V ⊔ conjSubgroup V (a : G))) n ∧
      barSub K ψ (V ⊔ conjSubgroup V (a : G) ⊔ conjSubgroup V (b : G)) = ⊤ ∧
      ∀ x w : ↥K, (x : G) ∈ X → (w : G) ∈ conjSubgroup V (a : G) → Commute (ψ x) (ψ w) := by
  have hn2 : 2 ≤ n := two_le_of_isPSUGp hP
  have hRab : IsElemAbelian 2 (barSub K ψ V) := isElemAbelian_barSub hV ψ
  obtain ⟨hF1, hF2⟩ := hF P n hP (barSub K ψ V) hRab hcard
  have hXt : Odd (Nat.card ↥(barSub K ψ X)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  have hXtc : barSub K ψ X ≤ Subgroup.centralizer (barSub K ψ V : Set P) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_barSub.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨v, hv, rfl⟩ := mem_barSub.mp hr
    exact (hXV x v hx hv).symm.eq
  obtain ⟨g, hgR, hXg⟩ := hF2 (barSub K ψ X) hXt hXtc
  obtain ⟨hL2, h, hh⟩ := hF1 g hgR
  obtain ⟨a, rfl⟩ := hψ g
  obtain ⟨b, rfl⟩ := hψ h
  have hVa : barSub K ψ (conjSubgroup V (a : G)) = conjSubgroup (barSub K ψ V) (ψ a) :=
    barSub_conjSubgroup ψ V a
  have hVb : barSub K ψ (conjSubgroup V (b : G)) = conjSubgroup (barSub K ψ V) (ψ b) :=
    barSub_conjSubgroup ψ V b
  have hVaK : conjSubgroup V (a : G) ≤ K := s716C_conjSubgroup_le hVK a.2
  have hVbK : conjSubgroup V (b : G) ≤ K := s716C_conjSubgroup_le hVK b.2
  have hsupL : barSub K ψ (V ⊔ conjSubgroup V (a : G)) =
      barSub K ψ V ⊔ conjSubgroup (barSub K ψ V) (ψ a) := by
    rw [barSub_sup hVK hVaK, hVa]
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hcomm : ∀ r ∈ barSub K ψ V, ∀ t ∈ conjSubgroup (barSub K ψ V) (ψ a), r * t = t * r := by
      intro r hr t ht
      obtain ⟨v, hv, rfl⟩ := mem_barSub.mp hr
      obtain ⟨w, hw, rfl⟩ := mem_barSub.mp (hVa ▸ ht)
      have h1 : ⁅(v : G), (w : G)⁆ ∈ ⁅V, conjSubgroup V (a : G)⁆ :=
        Subgroup.commutator_mem_commutator hv hw
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : (v : G) * w = w * v := commutatorElement_eq_one_iff_commute.mp h1
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h2)
    haveI : IsMulCommutative ↥(barSub K ψ V ⊔ conjSubgroup (barSub K ψ V) (ψ a)) :=
      s716C_isMulCommutative_sup hRab.1 (isElemAbelian_conjSubgroup' hRab (ψ a)).1 hcomm
    have htop := commutator_eq_top_of_isL2Gp hn2 hL2
    rw [(commutator_eq_bot_iff _).mpr this] at htop
    have hcard1 : Nat.card ↥(barSub K ψ V ⊔ conjSubgroup (barSub K ψ V) (ψ a)) = 1 := by
      rw [← Subgroup.card_top, ← htop, Subgroup.card_bot]
    have h3 := three_dvd_card_of_isL2Gp hL2
    rw [hcard1] at h3
    exact absurd h3 (by norm_num)
  · rw [hsupL]
    exact hL2
  · rw [barSub_sup (sup_le hVK hVaK) hVbK, barSub_sup hVK hVaK, hVa, hVb]
    exact hh
  · intro x w hx hw
    have hwR : ψ w ∈ conjSubgroup (barSub K ψ V) (ψ a) :=
      hVa ▸ mem_barSub.mpr ⟨w, hw, rfl⟩
    have hxX : ψ x ∈ barSub K ψ X := mem_barSub.mpr ⟨x, hx, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hXg hxX) (ψ w) hwR).symm

theorem commutator_mem_of_odd {K N : Subgroup G} {Q : Type} [Group Q] {φ : ↥K →* Q}
    (hφ : IsBarMap K N φ) {x w : ↥K} {m : ℕ} (hm : Odd m) (hx : x ^ m = 1) (hw : w * w = 1)
    (hc : Commute (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) x)
      (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) w)) :
    ((⁅x, w⁆ : ↥K) : G) ∈ N := by
  have hcen : ⁅φ x, φ w⁆ ∈ Subgroup.center Q := by
    have h1 : (QuotientGroup.mk' (Subgroup.center Q)) ⁅φ x, φ w⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hc
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center Q) _).mp h1
  have hone : ⁅φ x, φ w⁆ = 1 :=
    commutator_eq_one_of_mem_center_of_odd hm (by rw [← map_pow, hx, map_one])
      (by rw [← map_mul, hw, map_one]) hcen
  have h2 : φ ⁅x, w⁆ = 1 := by rw [map_commutatorElement]; exact hone
  exact (hφ.ker_iff _).mp h2

theorem commutator_eq_top_of_pair {K I : Subgroup G} {Q : Type} [Group Q] {φ : ↥K →* Q}
    (hφ : IsBarMap K I φ) {V A : Subgroup G} (hVK : V ≤ K) (hAK : A ≤ K) {n : ℕ} (hn : 2 ≤ n)
    (hS : IsL2Gp ↥(barSub K ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) (V ⊔ A)) n)
    (hker : ∀ l : ↥K, (l : G) ∈ V ⊔ A →
      (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) l = 1 ↔ (l : G) ∈ pairY V A))
    (hYI : pairY V A ≤ I) (hncl : Subgroup.normalClosure (barSub K φ V : Set Q) = ⊤) :
    commutator Q = ⊤ := by
  set ψ := (QuotientGroup.mk' (Subgroup.center Q)).comp φ with hψ
  have hLK : V ⊔ A ≤ K := sup_le hVK hAK
  let f : ↥(V ⊔ A) →* Q := φ.comp (Subgroup.inclusion hLK)
  let g : ↥(V ⊔ A) →* ↥(barSub K ψ (V ⊔ A)) :=
    (ψ.comp (Subgroup.inclusion hLK)).codRestrict _
      (fun x => ⟨Subgroup.inclusion hLK x, x.2, rfl⟩)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨k, hk, hkx⟩ := mem_barSub.mp x.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩
  have hperf : commutator ↥(barSub K ψ (V ⊔ A)) = ⊤ := commutator_eq_top_of_isL2Gp hn hS
  have hmapc : (commutator ↥(V ⊔ A)).map g = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hg,
      ← _root_.commutator_def]
    exact hperf
  have hVle : barSub K φ V ≤ commutator Q := by
    intro x hx
    obtain ⟨v, hvV, rfl⟩ := mem_barSub.mp hx
    have hvL : (v : G) ∈ V ⊔ A := Subgroup.mem_sup_left hvV
    have hmem : g ⟨v, hvL⟩ ∈ (commutator ↥(V ⊔ A)).map g := by
      rw [hmapc]
      trivial
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hmem
    have h1 : ψ (Subgroup.inclusion hLK c) = ψ v := congrArg Subtype.val hcg
    have h2 : ψ ((Subgroup.inclusion hLK c)⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (((Subgroup.inclusion hLK c)⁻¹ * v : ↥K) : G) ∈ V ⊔ A :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ c.2) hvL
    have h4 := (hker _ h3).mp h2
    have h5 : φ ((Subgroup.inclusion hLK c)⁻¹ * v) = 1 := (hφ.ker_iff _).mpr (hYI h4)
    rw [map_mul, map_inv] at h5
    have h6 : φ v = f c := (inv_mul_eq_one.mp h5).symm
    rw [h6]
    have hmem2 : f c ∈ (commutator ↥(V ⊔ A)).map f := Subgroup.mem_map_of_mem f hc
    have hle : (commutator ↥(V ⊔ A)).map f ≤ commutator Q := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact hle hmem2
  have hncl' : Subgroup.normalClosure (barSub K φ V : Set Q) ≤ commutator Q :=
    Subgroup.normalClosure_le_normal hVle
  rw [hncl] at hncl'
  exact top_le_iff.mp hncl'

theorem eq_sup_of_perfect {K N M : Subgroup G} {Q : Type} [Group Q] {φ : ↥K →* Q}
    (hφ : IsBarMap K N φ) (hN : N ≤ K) (hM : M ≤ K) (hperf : commutator Q = ⊤)
    (hMtop : barSub K ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) M = ⊤) :
    K = N ⊔ M := by
  rw [← barSub_eq_top_iff hM hN hφ]
  rw [barSub_comp] at hMtop
  have hsup : barSub K φ M ⊔ Subgroup.center Q = ⊤ := by
    have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center Q))) hMtop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h1
  have hcomm : commutator Q ≤ barSub K φ M := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hg₁ : g₁ ∈ barSub K φ M ⊔ Subgroup.center Q := by rw [hsup]; trivial
    have hg₂ : g₂ ∈ barSub K φ M ⊔ Subgroup.center Q := by rw [hsup]; trivial
    obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₁
    obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₂
    have e : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
      have hz1 := Subgroup.mem_center_iff.mp hz₁
      have hz2 := Subgroup.mem_center_iff.mp hz₂
      rw [commutatorElement_def, commutatorElement_def]
      calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹
          = m₁ * (z₁ * (m₂ * z₂ * z₁⁻¹)) * m₁⁻¹ * (z₂⁻¹ * m₂⁻¹) := by group
        _ = m₁ * ((m₂ * z₂ * z₁⁻¹) * z₁) * m₁⁻¹ * (z₂⁻¹ * m₂⁻¹) := by
          rw [← hz1 (m₂ * z₂ * z₁⁻¹)]
        _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by group
        _ = m₁ * m₂ * (m₁⁻¹ * z₂) * z₂⁻¹ * m₂⁻¹ := by rw [← hz2 m₁⁻¹]
        _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)
  rw [hperf] at hcomm
  exact top_le_iff.mp hcomm

theorem false_of_card_bounds {I Y C T : Subgroup G} (hYI : Y ≤ I) (hCI : C ≤ I)
    (hYC : Y ⊓ C = ⊥) (hT : T ≠ ⊥) (hY : Nat.card ↥Y = Nat.card ↥T ^ 2)
    (hC : Nat.card ↥Y ≤ Nat.card ↥C) (hI : Nat.card ↥I ≤ Nat.card ↥T ^ 3) : False := by
  let F : ↥Y × ↥C → ↥I := fun p => ⟨(p.1 : G) * p.2, mul_mem (hYI p.1.2) (hCI p.2.2)⟩
  have hinj : Function.Injective F := by
    rintro ⟨y, c⟩ ⟨y', c'⟩ h
    have h' : (y : G) * c = y' * c' := congrArg Subtype.val h
    have h1 : (y' : G)⁻¹ * y = c' * (c : G)⁻¹ := by
      calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * c) * (c : G)⁻¹ := by group
        _ = (y' : G)⁻¹ * (y' * c') * (c : G)⁻¹ := by rw [h']
        _ = c' * (c : G)⁻¹ := by group
    have hbot : (y' : G)⁻¹ * y ∈ Y ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y'.2) y.2
      · rw [h1]
        exact Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2)
    rw [hYC, Subgroup.mem_bot] at hbot
    have hyy : y = y' := Subtype.ext (inv_mul_eq_one.mp hbot).symm
    have hcc : c = c' := by
      apply Subtype.ext
      have := h'
      rw [show (y : G) = y' from congrArg Subtype.val hyy] at this
      exact mul_left_cancel this
    rw [hyy, hcc]
  have hle := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod] at hle
  have hT1 : 1 < Nat.card ↥T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT
  have h4 : Nat.card ↥T ^ 4 ≤ Nat.card ↥T ^ 3 := by
    calc Nat.card ↥T ^ 4 = Nat.card ↥Y * Nat.card ↥Y := by rw [hY]; ring
      _ ≤ Nat.card ↥Y * Nat.card ↥C := Nat.mul_le_mul_left _ hC
      _ ≤ Nat.card ↥I := hle
      _ ≤ Nat.card ↥T ^ 3 := hI
  exact absurd h4 (not_le.mpr (Nat.pow_lt_pow_right hT1 (by norm_num)))

theorem card_inf_centralizer_conj {I : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    Nat.card ↥(I ⊓ Subgroup.centralizer ({k⁻¹ * x * k} : Set G)) =
      Nat.card ↥(I ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hk' : k⁻¹ ∈ Subgroup.normalizer (I : Set G) := inv_mem hk
  have key : (I ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj k⁻¹).toMonoidHom =
      I ⊓ Subgroup.centralizer ({k⁻¹ * x * k} : Set G) := by
    ext c
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨hdI, hdx⟩ := Subgroup.mem_inf.mp hd
      rw [Subgroup.mem_centralizer_singleton_iff] at hdx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hk' d).mp hdI
        simpa using this
      · rw [Subgroup.mem_centralizer_singleton_iff]
        change (k⁻¹ * d * k⁻¹⁻¹) * (k⁻¹ * x * k) = (k⁻¹ * x * k) * (k⁻¹ * d * k⁻¹⁻¹)
        calc (k⁻¹ * d * k⁻¹⁻¹) * (k⁻¹ * x * k) = k⁻¹ * (d * x) * k := by group
          _ = k⁻¹ * (x * d) * k := by rw [hdx]
          _ = (k⁻¹ * x * k) * (k⁻¹ * d * k⁻¹⁻¹) := by group
    · intro hc
      obtain ⟨hcI, hcx⟩ := Subgroup.mem_inf.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hcx
      refine ⟨k * c * k⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hk c).mp hcI
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc k * c * k⁻¹ * x = k * (c * (k⁻¹ * x * k)) * k⁻¹ := by group
          _ = k * ((k⁻¹ * x * k) * c) * k⁻¹ := by rw [hcx]
          _ = x * (k * c * k⁻¹) := by group
      · change k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c
        group
  rw [← key]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
    (MulAut.conj k⁻¹).injective

end CFSG.LocalAnalysis.WeakClosure81
