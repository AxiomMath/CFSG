module

public import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
public import CFSG.OddTranspositions.FusionStep

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
private theorem pResidualOf_le (hC : HypothesisC D) :
    CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
  Subgroup.map_subtype_le _

omit [Finite G] in
private theorem conj_mem_pResidualOf (hC : HypothesisC D) {h l : G} (hh : h ∈ Halpha D hC.alpha)
    (hl : l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    h * l * h⁻¹ ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
    (Subgroup.le_normalizer hh)) l).mp hl

omit [Finite G] in
private theorem commute_of_mem_alpha (hC : HypothesisC D) {a h : G} (ha : a ∈ hC.alpha)
    (hh : h ∈ Halpha D hC.alpha) : Commute a h :=
  (Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_of_forall_commute hC
    (fun _ he => (commute_of_mem_alpha_of_mem_DalphaStar hC ha he).symm) hh)).symm

omit [Finite G] in
private theorem ncard_eq_of_mem_blockClass {α β : Set G} (hβ : β ∈ blockClass α) :
    β.ncard = α.ncard := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  exact Set.ncard_image_of_injective _ fun a b h => by simpa using h

omit [Finite G] in
private theorem conj_noncommProd_eq {s : Finset G} (comm : (s : Set G).Pairwise Commute)
    {n : G} (hn : ∀ x ∈ s, n * x * n⁻¹ ∈ s) :
    n * s.noncommProd id comm * n⁻¹ = s.noncommProd id comm := by
  have hinj : Function.Injective fun x : G => n * x * n⁻¹ := fun a b h => by simpa using h
  have hmap : s.map ⟨_, hinj⟩ = s :=
    Finset.eq_of_subset_of_card_le (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hn y hy) (by rw [Finset.card_map])
  have h1 := Finset.map_noncommProd s id comm (MulAut.conj n)
  rw [MulAut.conj_apply] at h1
  rw [h1]
  unfold Finset.noncommProd
  congr 1
  have h2 := congrArg Finset.val hmap
  rw [Finset.map_val] at h2
  rw [Multiset.map_id]
  exact h2

private theorem two_mul_ncard_diff_le {z : G} {X β : Set G} {U : Subgroup G}
    (hU : ∀ g, g ∈ U ↔ g = 1 ∨ z * g ∈ X) (hX2 : ∀ x ∈ X, x * x = 1)
    (hX3 : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → z * x * y ∈ X) {v w : G} (hv : v ∈ X) (hw : w ∈ X)
    (hwβ : w ∉ β) (hvW : v ∉ Subgroup.closure (X \ β)) :
    2 * (X \ β).ncard ≤ Nat.card U := by
  set W := Subgroup.closure (X \ β)
  have hwW : w ∈ W := Subgroup.subset_closure ⟨hw, hwβ⟩
  have hmul : ∀ y ∈ X, w * y ∈ U := fun y hy => by
    rw [hU]
    by_cases hyw : y = w
    · exact Or.inl (by rw [hyw]; exact hX2 w hw)
    · exact Or.inr (by rw [← mul_assoc]; exact hX3 w hw y hy (Ne.symm hyw))
  have hWU : W ⊓ U ≠ U := fun h => hvW (by
    have hwvW : w * v ∈ W := (Subgroup.mem_inf.mp (h.symm ▸ hmul v hv)).1
    simpa using W.mul_mem (W.inv_mem hwW) hwvW)
  have hcnt1 : (X \ β).ncard ≤ Nat.card (W ⊓ U : Subgroup G) := by
    calc (X \ β).ncard ≤ ((W ⊓ U : Subgroup G) : Set G).ncard :=
          Set.ncard_le_ncard_of_injOn (fun y => w * y) (fun y hy => Subgroup.mem_inf.mpr
            ⟨W.mul_mem hwW (Subgroup.subset_closure hy), hmul y hy.1⟩)
            (mul_right_injective w).injOn (Set.toFinite _)
      _ = Nat.card (W ⊓ U : Subgroup G) := (Nat.card_coe_set_eq _).symm
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_right : W ⊓ U ≤ U)
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k
    · rw [mul_zero] at hk
      omega
    · rw [mul_one] at hk
      exact hWU (Subgroup.eq_of_le_of_card_ge inf_le_right hk.le)
  calc 2 * (X \ β).ncard ≤ k * Nat.card (W ⊓ U : Subgroup G) :=
        Nat.mul_le_mul hk2 hcnt1
    _ = Nat.card U := by rw [hk, mul_comm]

private structure ZFacts (hC : HypothesisC D) (z : G) : Prop where
  mem : z ∈ Halpha D hC.alpha
  comm : ∀ h ∈ Halpha D hC.alpha, Commute z h
  sq : z * z = 1
  not_mem : z ∉ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  cases : ∀ h ∈ Halpha D hC.alpha, h ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∨
    z * h ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  central : ∀ c ∈ Halpha D hC.alpha, (∀ h ∈ Halpha D hC.alpha, Commute c h) →
    (∃ k : ℕ, c ^ 2 ^ k = 1) → c = 1 ∨ c = z
  mem_sylow : ∀ T : Sylow 2 (Halpha D hC.alpha),
    z ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype

private theorem zFacts (hC : HypothesisC D) (hH : Th91Hyp D hC) {z : G}
    (hzP : (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers z) (hz1 : z ≠ 1) : ZFacts hC z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Halpha D hC.alpha
  set L := CFSG.Quasithin.pResidualOf 2 H
  obtain ⟨hPZ, hcard, hsup, hdisj⟩ := Halpha_pCore_split hC hH
  rw [hzP] at hPZ hcard hsup hdisj
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp (hPZ (Subgroup.mem_zpowers z))
  have hzH : z ∈ H := hcz ▸ c.2
  have hcomm : ∀ h ∈ H, Commute z h := fun h hh => by
    rw [← hcz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨h, hh⟩).symm
  have hz2 : orderOf z = 2 := by
    rw [Nat.card_zpowers] at hcard
    have h0 := orderOf_pos z
    have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    omega
  have hsq : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzp : ∀ a ∈ Subgroup.zpowers z, a = 1 ∨ a = z := by
    intro a ha
    rw [mem_zpowers_iff_mem_range_orderOf, hz2] at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    interval_cases i <;> simp
  have hzL : z ∉ L := fun h => hz1 (Subgroup.disjoint_def.mp hdisj (Subgroup.mem_zpowers z) h)
  refine ⟨hzH, hcomm, hsq, hzL, ?_, ?_, ?_⟩
  · intro h hh
    have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.zpowers_le).mpr (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
        (Subgroup.le_normalizer hzH))
    have hmem : h ∈ ((Subgroup.zpowers z ⊔ L : Subgroup G) : Set G) := by rw [hsup]; exact hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hmem
    obtain ⟨a, ha, l, hl, rfl⟩ := Set.mem_mul.mp hmem
    rcases hzp a ha with rfl | rfl
    · left
      rwa [one_mul]
    · right
      rwa [← mul_assoc, hsq, one_mul]
  · intro x hxH hxc ⟨k, hk⟩
    let x' : H := ⟨x, hxH⟩
    have hx'Z : x' ∈ Subgroup.center H :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hxc g g.2).eq.symm
    have hp : IsPGroup 2 (Subgroup.zpowers x') := by
      have hdvd : orderOf x' ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hxP : x ∈ (CFSG.pCore 2 H).map H.subtype :=
      Subgroup.mem_map_of_mem _ (mem_pCore_of_mem_center hx'Z hp)
    rw [hzP] at hxP
    exact hzp x hxP
  · intro T
    have hzP' : z ∈ (CFSG.pCore 2 H).map H.subtype := by
      rw [hzP]
      exact Subgroup.mem_zpowers z
    exact Subgroup.map_mono (CFSG.fitting_pCore_le_sylow T) hzP'

namespace ZFacts

variable {hC : HypothesisC D} {z : G}

omit [Finite G] in
private theorem eq_one (zf : ZFacts hC z) {c : G} (hcH : c ∈ Halpha D hC.alpha)
    (hcL : c ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hcc : ∀ h ∈ Halpha D hC.alpha, Commute c h) (hk : ∃ k : ℕ, c ^ 2 ^ k = 1) : c = 1 :=
  (zf.central c hcH hcc hk).resolve_right fun h => zf.not_mem (h ▸ hcL)

private theorem not_mem_DalphaStar (zf : ZFacts hC z) (hH : Th91Hyp D hC) :
    z ∉ DalphaStar D hC.alpha := by
  intro hz
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute_DalphaStar hC hH
  have hfix : ∀ c ∈ DalphaStar D hC.alpha, c = z := by
    intro c hc
    obtain ⟨k, hk, hkc⟩ := hC.Halpha_transitive z hz c hc
    rw [← hkc, ← (zf.comm k hk).eq, mul_inv_cancel_right]
  exact hab (by rw [hfix a ha, hfix b hb])

private theorem mul_mem (zf : ZFacts hC z) {x : G} (hx : x ∈ DalphaStar D hC.alpha) :
    z * x ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  refine (zf.cases x (Subgroup.subset_closure hx)).resolve_left fun hxL => ?_
  have hDL : DalphaStar D hC.alpha ⊆ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive x hx y hy
    exact conj_mem_pResidualOf hC hh hxL
  exact zf.not_mem ((Subgroup.closure_le _).mpr hDL zf.mem)

private theorem mem_alpha (zf : ZFacts hC z) (hH : Th91Hyp D hC) (hzD : z ∈ D) :
    z ∈ hC.alpha :=
  (mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hC.d_mem_alpha hzD
    (commute_of_mem_alpha hC hC.d_mem_alpha zf.mem)).resolve_right (zf.not_mem_DalphaStar hH)

private theorem not_mem_Halpha (zf : ZFacts hC z) (hzD : z ∉ D) {a : G} (ha : a ∈ hC.alpha) :
    a ∉ Halpha D hC.alpha := by
  intro haH
  have haD : a ∈ D := hC.isBlock_alpha.subset ha
  rcases zf.central a haH (fun h hh => commute_of_mem_alpha hC ha hh)
      ⟨1, by rw [pow_one, pow_two]; exact hC.setup.oddT.mul_self_eq_one haD⟩ with h | h
  · exact hC.setup.oddT.ne_one haD h
  · exact hzD (h ▸ haD)

private theorem mem_DalphaStar (zf : ZFacts hC z) (hzD : z ∉ D) {d : G}
    (hdH : d ∈ Halpha D hC.alpha) (hdD : d ∈ D) : d ∈ DalphaStar D hC.alpha :=
  (mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hC.d_mem_alpha hdD
    (commute_of_mem_alpha hC hC.d_mem_alpha hdH)).resolve_left (zf.not_mem_Halpha hzD · hdH)

omit [Finite G] in
private theorem mul_mul_mul_eq (zf : ZFacts hC z) {x y : G} (hx : x ∈ Halpha D hC.alpha)
    (hy : y ∈ Halpha D hC.alpha) (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : Commute x y) :
    x * y * (z * x * y) = z := by
  have hzl : Commute z (x * y) := (zf.comm x hx).mul_right (zf.comm y hy)
  have hl2 : x * y * (x * y) = 1 := by rw [hxy.symm.mul_mul_mul_comm, hx2, hy2, one_mul]
  calc x * y * (z * x * y) = x * y * (z * (x * y)) := by rw [mul_assoc z]
    _ = z * (x * y * (x * y)) := by rw [← mul_assoc, hzl.symm.eq, mul_assoc]
    _ = z := by rw [hl2, mul_one]

private theorem exists_conj (zf : ZFacts hC z) (hH : Th91Hyp D hC) {l l₀ : G}
    (hlL : l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hl2 : l * l = 1)
    (hl1 : l ≠ 1) (hl₀L : l₀ ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hl₀2 : l₀ * l₀ = 1) (hl₀1 : l₀ ≠ 1) :
    ∃ g ∈ Halpha D hC.alpha, g * l₀ * g⁻¹ = l := by
  classical
  set H := Halpha D hC.alpha
  set L := CFSG.Quasithin.pResidualOf 2 H
  have hlH : l ∈ H := pResidualOf_le hC hlL
  have hl₀H : l₀ ∈ H := pResidualOf_le hC hl₀L
  let π := QuotientGroup.mk' (Subgroup.center H)
  have hord : ∀ {m : G} (hmH : m ∈ H), m ∈ L → m * m = 1 → m ≠ 1 →
      orderOf (π ⟨m, hmH⟩) = 2 := by
    intro m hmH hmL hm2 hm1
    refine orderOf_eq_prime ?_ fun h => hm1 ?_
    · rw [pow_two, ← map_mul, show (⟨m, hmH⟩ : H) * ⟨m, hmH⟩ = 1 from Subtype.ext hm2, map_one]
    · have hZ : (⟨m, hmH⟩ : H) ∈ Subgroup.center H := (QuotientGroup.eq_one_iff _).mp h
      refine zf.eq_one hmH hmL (fun h hh => ?_) ⟨1, by rw [pow_one, pow_two]; exact hm2⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ ⟨h, hh⟩).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hH.bender
    (hord hl₀H hl₀L hl₀2 hl₀1) (hord hlH hlL hl2 hl1))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
  set y : H := g * ⟨l₀, hl₀H⟩ * g⁻¹ with hy
  have hπ : π y = π ⟨l, hlH⟩ := by simpa only [hy, map_mul, map_inv] using hc
  have hwZ : y⁻¹ * ⟨l, hlH⟩ ∈ Subgroup.center H := QuotientGroup.eq.mp hπ
  have hyG : (y : G) = g * l₀ * (g : G)⁻¹ := rfl
  have hyL : (y : G) ∈ L := hyG ▸ conj_mem_pResidualOf hC g.2 hl₀L
  set w : G := (y : G)⁻¹ * l with hw
  have hwc : ∀ h ∈ H, Commute w h := fun h hh =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨h, hh⟩).symm
  have hy2 : (y : G) * y = 1 := by
    rw [hyG]
    calc (g : G) * l₀ * (g : G)⁻¹ * ((g : G) * l₀ * (g : G)⁻¹) = g * (l₀ * l₀) * (g : G)⁻¹ := by
          group
      _ = 1 := by rw [hl₀2, mul_one, mul_inv_cancel]
  have hlyw : l = y * w := by rw [hw, mul_inv_cancel_left]
  have hw2 : w * w = 1 := by
    have h := hl2
    rwa [hlyw, (hwc _ y.2).mul_mul_mul_comm, hy2, one_mul] at h
  have hw1 : w = 1 := zf.eq_one (H.mul_mem (H.inv_mem y.2) hlH) (L.mul_mem (L.inv_mem hyL) hlL)
    hwc ⟨1, by rw [pow_one, pow_two]; exact hw2⟩
  exact ⟨g, g.2, by rw [← hyG, hlyw, hw1, mul_one]⟩

private theorem mul_mem_DalphaStar (zf : ZFacts hC z) (hH : Th91Hyp D hC) {l : G}
    (hlL : l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hl2 : l * l = 1)
    (hl1 : l ≠ 1) : z * l ∈ DalphaStar D hC.alpha := by
  obtain ⟨x₀, hx₀⟩ := DstarH_nonempty hC
  have hx : (x₀ : G) ∈ DalphaStar D hC.alpha := hx₀
  have hxD : (x₀ : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  have hzx : Commute z x₀ := zf.comm _ x₀.2
  have h2 : z * x₀ * (z * x₀) = 1 := by
    rw [hzx.symm.mul_mul_mul_comm, zf.sq, hC.setup.oddT.mul_self_eq_one hxD, one_mul]
  have h1 : z * x₀ ≠ 1 := fun h => zf.not_mem_DalphaStar hH (by
    rwa [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right zf.sq] at hx)
  obtain ⟨g, hg, hgl⟩ := zf.exists_conj hH hlL hl2 hl1 (zf.mul_mem hx) h2 h1
  have hzg : z * g = g * z := (zf.comm g hg).eq
  have key : z * l = g * x₀ * g⁻¹ := by
    rw [← hgl]
    calc z * (g * (z * x₀) * g⁻¹) = g * (z * z * x₀) * g⁻¹ := by
          simp only [← mul_assoc, hzg]
      _ = g * x₀ * g⁻¹ := by rw [zf.sq, one_mul]
  rw [key]
  exact (Halpha_le_normalizer hC.setup.normal hg (x₀ : G)).mp hx

private theorem commute_of_mem_sylow (zf : ZFacts hC z) (hH : Th91Hyp D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) {l t : G}
    (hlT : l ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hlL : l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hl2 : l * l = 1)
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    Commute l t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haT, rfl⟩ := Subgroup.mem_map.mp hlT
  obtain ⟨b, hbT, rfl⟩ := Subgroup.mem_map.mp htT
  let π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Tb : Sylow 2 (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    T.mapSurjective hπs
  have hmem : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)),
      π x ∈ (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) :=
    fun x hx => by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π hx
  have hsq : π a * π a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext hl2, map_one]
  have hc := IsBenderGroup.commute_of_mul_self_eq_one hH.bender Tb (hmem a haT) hsq (π b)
    (hmem b hbT)
  have hcZ : (a * b)⁻¹ * (b * a) ∈ Subgroup.center (Halpha D hC.alpha) :=
    QuotientGroup.eq.mp (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc.eq)
  have hcT : (a * b)⁻¹ * (b * a) ∈ (T : Subgroup (Halpha D hC.alpha)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ haT hbT))
      (Subgroup.mul_mem _ hbT haT)
  have hcL : (((a * b)⁻¹ * (b * a) : Halpha D hC.alpha) : G) ∈
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    have h1 : (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ ∈
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :=
      conj_mem_pResidualOf hC (Subgroup.inv_mem _ b.2) (Subgroup.inv_mem _ hlL)
    have h2 : (((a * b)⁻¹ * (b * a) : Halpha D hC.alpha) : G) =
        (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * a := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact Subgroup.mul_mem _ h1 hlL
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨_, hcT⟩
  have hk' : (((a * b)⁻¹ * (b * a) : Halpha D hC.alpha) : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun x : (T : Subgroup (Halpha D hC.alpha)) => ((x : Halpha D hC.alpha) : G))
      hk
    simpa using this
  have hc1 := zf.eq_one ((a * b)⁻¹ * (b * a)).2 hcL
    (fun h hh => congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨h, hh⟩).symm) ⟨k, hk'⟩
  have hab : a * b = b * a := inv_mul_eq_one.mp (Subtype.ext hc1)
  exact congrArg Subtype.val hab

private theorem exists_ne_mem_sylow (zf : ZFacts hC z) (hH : Th91Hyp D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) :
    ∃ x ∈ DalphaStar D hC.alpha,
      x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
      ∃ y ∈ DalphaStar D hC.alpha,
        y ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧ x ≠ y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Tb : Sylow 2 (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    T.mapSurjective hπs
  have hzT := zf.mem_sylow T
  have hzZ : (⟨z, zf.mem⟩ : Halpha D hC.alpha) ∈ Subgroup.center (Halpha D hC.alpha) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (zf.comm g g.2).eq.symm
  have hπz : π ⟨z, zf.mem⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hzZ
  have hlift : ∀ e : Subgroup.center
      (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))),
      ∃ l : G, ∃ hlH : l ∈ Halpha D hC.alpha,
        l ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ∧
        l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧ l * l = 1 ∧
        π ⟨l, hlH⟩ = ((e : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) := by
    intro e
    have hec : ∀ y ∈ (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))),
        Commute ((e : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) y :=
      fun y hy => (congrArg Subtype.val (Subgroup.mem_center_iff.mp e.2 ⟨y, hy⟩)).symm
    have he2 := IsBenderGroup.mul_self_eq_one_of_commute hH.bender Tb (e : Tb).2 hec
    have heT : ((e : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) ∈
        (T : Subgroup (Halpha D hC.alpha)).map π := by
      rw [← Sylow.coe_mapSurjective hπs T]
      exact (e : Tb).2
    obtain ⟨t, htT, hte⟩ := Subgroup.mem_map.mp heT
    have hzt : Commute z t := zf.comm _ t.2
    have hzz : z * t * (z * t) = t * t := by
      rw [hzt.symm.mul_mul_mul_comm, zf.sq, one_mul]
    have httL : (t : G) * t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
      rcases zf.cases t t.2 with h | h
      · exact Subgroup.mul_mem _ h h
      · rw [← hzz]
        exact Subgroup.mul_mem _ h h
    have httZ : t * t ∈ Subgroup.center (Halpha D hC.alpha) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      change π t * π t = 1
      rw [hte]
      exact he2
    have htt : (t : G) * t = 1 := by
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨_, Subgroup.mul_mem _ htT htT⟩
      refine zf.eq_one (t * t).2 httL
        (fun h hh => congrArg Subtype.val (Subgroup.mem_center_iff.mp httZ ⟨h, hh⟩).symm)
        ⟨k, ?_⟩
      have := congrArg (fun x : (T : Subgroup (Halpha D hC.alpha)) =>
        ((x : Halpha D hC.alpha) : G)) hk
      simpa using this
    have htTG : (t : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
      Subgroup.mem_map_of_mem _ htT
    rcases zf.cases t t.2 with h | h
    · exact ⟨t, t.2, htTG, h, htt, hte⟩
    · refine ⟨z * t, Subgroup.mul_mem _ zf.mem t.2, Subgroup.mul_mem _ hzT htTG, h,
        by rw [hzz, htt], ?_⟩
      rw [← hte, show (⟨z * t, Subgroup.mul_mem _ zf.mem t.2⟩ : Halpha D hC.alpha) =
        ⟨z, zf.mem⟩ * t from rfl, map_mul, hπz, one_mul]
  have h4 := IsBenderGroup.four_le_card_center hH.bender Tb
  obtain ⟨e₁, e₂, he₁, he₂, he₁₂⟩ : ∃ e₁ e₂ : Subgroup.center
      (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))),
      e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ := by
    have h3 : 2 < (Set.univ : Set (Subgroup.center
        (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))))).ncard := by
      rw [Set.ncard_univ]
      omega
    obtain ⟨a, b, c, -, -, -, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp h3
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨l₁, hl₁H, hl₁T, hl₁L, hl₁2, hl₁e⟩ := hlift e₁
  obtain ⟨l₂, hl₂H, hl₂T, hl₂L, hl₂2, hl₂e⟩ := hlift e₂
  have hval : ∀ {e e' : Subgroup.center
      (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)))},
      ((e : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) =
        ((e' : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) → e = e' :=
    fun h => Subtype.ext (Subtype.ext h)
  have hl1 : ∀ {l : G} {hlH : l ∈ Halpha D hC.alpha} {e : Subgroup.center
      (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)))},
      π ⟨l, hlH⟩ = ((e : Tb) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) →
        e ≠ 1 → l ≠ 1 := by
    rintro l hlH e hle he rfl
    exact he (hval (by rw [← hle]; exact map_one π))
  refine ⟨z * l₁, zf.mul_mem_DalphaStar hH hl₁L hl₁2 (hl1 hl₁e he₁),
    Subgroup.mul_mem _ hzT hl₁T, z * l₂, zf.mul_mem_DalphaStar hH hl₂L hl₂2 (hl1 hl₂e he₂),
    Subgroup.mul_mem _ hzT hl₂T, fun h => he₁₂ (hval ?_)⟩
  rw [← hl₁e, ← hl₂e]
  congr 2
  exact mul_left_cancel h

private theorem sylow_inter (zf : ZFacts hC z) (hH : Th91Hyp D hC) (hzD : z ∉ D)
    (T : Sylow 2 (Halpha D hC.alpha)) {X : Set G}
    (hX : X = ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G) ∩ D) :
    (∀ x ∈ X, x ∈ DalphaStar D hC.alpha) ∧ (∀ x ∈ X, ∀ y ∈ X, x ≠ y → z * x * y ∈ X) ∧
      ∀ γ ∈ Dalpha D hC.alpha, ∀ w ∈ γ, w ∈ X → γ ⊆ X := by
  subst hX
  have hTGH : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Halpha D hC.alpha := Subgroup.map_subtype_le _
  have hXstar : ∀ x ∈ ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :
      Set G) ∩ D, x ∈ DalphaStar D hC.alpha := fun x hx =>
    zf.mem_DalphaStar hzD (hTGH hx.1) hx.2
  have hzT := zf.mem_sylow T
  refine ⟨hXstar, ?_, ?_⟩
  · intro x hx y hy hxy
    have hc : Commute x y :=
      hC.setup.oddT.commute_of_isPGroup (T.isPGroup'.map _) hx.2 hy.2 hx.1 hy.1
    have hl : z * x * (z * y) = x * y := by
      rw [(zf.comm x (hTGH hx.1)).symm.mul_mul_mul_comm, zf.sq, one_mul]
    have hlL : x * y ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) :=
      hl ▸ Subgroup.mul_mem _ (zf.mul_mem (hXstar x hx)) (zf.mul_mem (hXstar y hy))
    have hl2 : x * y * (x * y) = 1 := by
      rw [hc.symm.mul_mul_mul_comm, hC.setup.oddT.mul_self_eq_one hx.2,
        hC.setup.oddT.mul_self_eq_one hy.2, one_mul]
    have hl1 : x * y ≠ 1 := fun h =>
      hxy (by rw [eq_inv_of_mul_eq_one_left h, hC.setup.oddT.inv_eq hy.2])
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzT hx.1) hy.1, ?_⟩
    rw [mul_assoc]
    exact DalphaStar_subset hC.isBlock_alpha (zf.mul_mem_DalphaStar hH hlL hl2 hl1)
  · intro γ hγ w hwγ hwX
    have hcent : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)), (t : G) * w * (t : G)⁻¹ = w := by
      intro t ht
      have hzw2 : z * w * (z * w) = 1 := by
        rw [(zf.comm w (hTGH hwX.1)).symm.mul_mul_mul_comm, zf.sq,
          hC.setup.oddT.mul_self_eq_one hwX.2, one_mul]
      have h1 := zf.commute_of_mem_sylow hH T (Subgroup.mul_mem _ hzT hwX.1)
        (zf.mul_mem (hXstar w hwX)) hzw2 (Subgroup.mem_map_of_mem _ ht)
      have h2 : Commute w t := by
        have : w = z * (z * w) := by rw [← mul_assoc, zf.sq, one_mul]
        rw [this]
        exact (zf.comm _ t.2).mul_left h1
      rw [← h2.eq, mul_inv_cancel_right]
    have hsub := block_subset_sylow hC hH hγ hwγ T hwX.1 hcent
    exact fun y hy => ⟨hsub hy, hγ.2.1 hy⟩

private theorem exists_subgroup (zf : ZFacts hC z) (hzD : z ∉ D) {X : Set G} (hXD : X ⊆ D)
    (hXH : X ⊆ Halpha D hC.alpha) {P : Subgroup G} (hP : IsPGroup 2 P) (hzP : z ∈ P)
    (hXP : X ⊆ P) (hX3 : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → z * x * y ∈ X) :
    ∃ U : Subgroup G, (∀ g, g ∈ U ↔ g = 1 ∨ z * g ∈ X) ∧ Nat.card U = X.ncard + 1 ∧
      ∃ j : ℕ, Nat.card U = 2 ^ j := by
  have hzz : ∀ g, z * (z * g) = g := fun g => by rw [← mul_assoc, zf.sq, one_mul]
  have hgH : ∀ g, z * g ∈ X → g ∈ Halpha D hC.alpha := fun g hg =>
    hzz g ▸ (Halpha D hC.alpha).mul_mem zf.mem (hXH hg)
  have hg2 : ∀ g, z * g ∈ X → g * g = 1 := fun g hg => by
    have h := hC.setup.oddT.mul_self_eq_one (hXD hg)
    rwa [(zf.comm g (hgH g hg)).symm.mul_mul_mul_comm, zf.sq, one_mul] at h
  have hkey : ∀ g h, g ∈ Halpha D hC.alpha → z * (z * g) * (z * h) = z * (g * h) := by
    intro g h hg
    calc z * (z * g) * (z * h) = z * z * (g * z) * h := by group
      _ = g * z * h := by rw [zf.sq, one_mul]
      _ = z * (g * h) := by rw [← (zf.comm g hg).eq, mul_assoc]
  let U : Subgroup G :=
    { carrier := {g | g = 1 ∨ z * g ∈ X}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro g h (rfl | hg) (rfl | hh)
        · exact Or.inl (one_mul 1)
        · exact Or.inr (by rwa [one_mul])
        · exact Or.inr (by rwa [mul_one])
        · by_cases hgh : z * g = z * h
          · exact Or.inl (by rw [mul_left_cancel hgh]; exact hg2 h hh)
          · exact Or.inr (by rw [← hkey g h (hgH g hg)]; exact hX3 _ hg _ hh hgh)
      inv_mem' := by
        rintro g (rfl | hg)
        · exact Or.inl inv_one
        · exact Or.inr (by rwa [inv_eq_of_mul_eq_one_right (hg2 g hg)]) }
  have hUP : U ≤ P := by
    rintro g (rfl | hg)
    · exact P.one_mem
    · exact hzz g ▸ P.mul_mem hzP (hXP hg)
  have hset : (U : Set G) = insert 1 ((fun x => z * x) '' X) := by
    ext g
    change g = 1 ∨ z * g ∈ X ↔ g ∈ insert 1 ((fun x => z * x) '' X)
    rw [Set.mem_insert_iff, Set.mem_image]
    constructor
    · rintro (rfl | hg)
      · exact Or.inl rfl
      · exact Or.inr ⟨z * g, hg, hzz g⟩
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (by rwa [hzz])
  have h1 : (1 : G) ∉ (fun x => z * x) '' X := by
    rintro ⟨x, hx, hzx⟩
    have hxz : x = z := by
      rw [eq_inv_of_mul_eq_one_right hzx, inv_eq_of_mul_eq_one_right zf.sq]
    exact hzD (hxz ▸ hXD hx)
  refine ⟨U, fun g => Iff.rfl, ?_, (hP.to_le hUP).exists_card_eq⟩
  calc Nat.card U = (U : Set G).ncard := Nat.card_coe_set_eq _
    _ = X.ncard + 1 := by
      rw [hset, Set.ncard_insert_of_notMem h1 (Set.toFinite _),
        Set.ncard_image_of_injective _ (mul_right_injective z)]

private theorem eq_one_of_mem_closure (zf : ZFacts hC z) (hH : Th91Hyp D hC)
    (hαc : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hz : z ∈ Subgroup.closure β) : z = 1 := by
  obtain ⟨v, hvβ⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hβ.1
  have hzu : ∀ e ∈ D, Commute e hC.d → Commute z e := by
    intro e he heu
    rcases mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hC.d_mem_alpha he
      heu.symm with heα | heα
    · exact (commute_of_mem_alpha hC heα zf.mem).symm
    · exact zf.comm e (Subgroup.subset_closure heα)
  have hzv : ∀ e ∈ D, Commute e v → Commute z e := by
    intro e he hev
    rcases mem_block_or_DalphaStar_of_commute hC hβ.1 hvβ he hev.symm with heβ | ⟨δ, hδ, heδ⟩
    · exact zf.comm e (Subgroup.subset_closure (subset_DalphaStar hβ heβ))
    · have hle : Subgroup.closure β ≤ Subgroup.centralizer ({e} : Set G) :=
        (Subgroup.closure_le _).mpr fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
          ((mem_Dalpha_iff.mp hδ).2.2.2 b hb e heδ).eq
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  exact eq_one_of_commute_centSet hC hH hαc ⟨β, hβ, hvβ⟩ hzu hzv

private theorem not_mem_closure (zf : ZFacts hC z) (hzD : z ∉ D) (S : Sylow 2 G)
    (huS : hC.d ∈ (S : Subgroup G)) {β : Set G} (hβ : β ∈ blockClass hC.alpha) {v : G}
    (hvβ : v ∈ β) (hv : v ∈ (S : Set G) ∩ D) {Y : Set G} (hY : Y ⊆ ((S : Set G) ∩ D) \ β) :
    v ∉ Subgroup.closure Y := by
  intro hvY
  obtain ⟨n, hn, hnv⟩ :=
    sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S hv ⟨huS, hC.hd⟩
  have hsub : ∀ y ∈ Y, n * y * n⁻¹ ∈ Halpha D hC.alpha := by
    intro y hy
    have hyΔ : n * y * n⁻¹ ∈ (S : Set G) ∩ D := (hn y).mp (hY hy).1
    refine Subgroup.subset_closure ((mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _)
      hC.d_mem_alpha hyΔ.2 (hC.setup.oddT.commute_of_isPGroup S.isPGroup' hC.hd hyΔ.2 huS
        hyΔ.1)).resolve_left fun hyα => (hY hy).2 ?_)
    have hβ' : (fun x => n⁻¹ * x * n⁻¹⁻¹) '' hC.alpha ∈ blockClass hC.alpha :=
      mem_blockClass_iff.mpr ⟨n⁻¹, rfl⟩
    have hv' : v ∈ (fun x => n⁻¹ * x * n⁻¹⁻¹) '' hC.alpha :=
      ⟨hC.d, hC.d_mem_alpha, by rw [← hnv]; group⟩
    have hy' : y ∈ (fun x => n⁻¹ * x * n⁻¹⁻¹) '' hC.alpha := ⟨_, hyα, by group⟩
    rwa [eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ' hβ ⟨v, hv', hvβ⟩] at hy'
  have hle : Subgroup.closure Y ≤ (Halpha D hC.alpha).comap (MulAut.conj n).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun y hy => hsub y hy
  have huH := hle hvY
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hnv] at huH
  exact zf.not_mem_Halpha hzD hC.d_mem_alpha huH

private theorem false_of_ncard_eq_three (zf : ZFacts hC z) (hH : Th91Hyp D hC) (hzD : z ∉ D)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (huS : hC.d ∈ (S : Subgroup G)) {X : Set G}
    (hX : X = ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G) ∩ D)
    (hX3 : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → z * x * y ∈ X) (hα1 : hC.alpha.ncard = 1)
    (hX3card : X.ncard = 3) {v w : G} (hvX : v ∈ X) (hwX : w ∈ X) (hvw : v ≠ w)
    (hvs : v ∈ DalphaStar D hC.alpha) : False := by
  classical
  have hXH : ∀ x ∈ X, x ∈ Halpha D hC.alpha := fun x hx =>
    Subgroup.map_subtype_le _ (hX ▸ hx).1
  have hXD : ∀ x ∈ X, x ∈ D := fun x hx => (hX ▸ hx).2
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hα1
  have hαu : hC.alpha = {hC.d} := by
    have h := hC.d_mem_alpha
    rw [ha, Set.mem_singleton_iff] at h
    rw [ha, h]
  have hx3 := hX3 v hvX w hwX hvw
  have hzw : z * w ≠ 1 := fun h => by
    have : w = z := by rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right zf.sq]
    exact hzD (this ▸ hXD w hwX)
  have hne1 : z * v * w ≠ v := fun h => hzw (mul_left_cancel (a := v) (by
    rw [mul_one, ← mul_assoc, ← (zf.comm v (hXH v hvX)).eq, h]))
  have hne2 : z * v * w ≠ w := fun h => by
    have h1 : z * v = 1 := mul_right_cancel (b := w) (by rw [h, one_mul])
    have : v = z := by rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right zf.sq]
    exact hzD (this ▸ hXD v hvX)
  have hXeq : X = {v, w, z * v * w} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
    · rintro x (rfl | rfl | rfl)
      · exact hvX
      · exact hwX
      · exact hx3
    · have hv' : v ∉ ({w, z * v * w} : Set G) := by
        rintro (h | h)
        · exact hvw h
        · exact hne1 h.symm
      rw [hX3card, Set.ncard_insert_of_notMem hv', Set.ncard_pair hne2.symm]
  have hΔeq : (S : Set G) ∩ D = {hC.d, v, w, z * v * w} := by
    ext d
    constructor
    · intro hd
      by_cases hdα : d ∈ hC.alpha
      · rw [hαu] at hdα
        exact Or.inl hdα
      ·
        have hdH : d ∈ Halpha D hC.alpha := Subgroup.subset_closure
          ((mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hC.d_mem_alpha hd.2
            (hC.setup.oddT.commute_of_isPGroup S.isPGroup' hC.hd hd.2 huS
              hd.1)).resolve_left hdα)
        have hTK : (T : Subgroup (Halpha D hC.alpha)) ≤
            (S : Subgroup G).comap (Halpha D hC.alpha).subtype :=
          fun t ht => hTS (Subgroup.mem_map_of_mem _ ht)
        have hdT : (⟨d, hdH⟩ : Halpha D hC.alpha) ∈ (T : Subgroup (Halpha D hC.alpha)) := by
          rw [← T.is_maximal' S.isPGroup'.comap_subtype hTK]
          exact hd.1
        have hdX : d ∈ X := hX ▸ ⟨Subgroup.mem_map_of_mem _ hdT, hd.2⟩
        rw [hXeq] at hdX
        exact Or.inr hdX
    · have hXS : ∀ x ∈ X, x ∈ (S : Set G) ∩ D := fun x hx => ⟨hTS (hX ▸ hx).1, (hX ▸ hx).2⟩
      rintro (rfl | hd)
      · exact ⟨huS, hC.hd⟩
      · exact hXS d (by rw [hXeq]; exact hd)
  obtain ⟨n, hn, hnu⟩ := sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S
    (show hC.d ∈ (S : Set G) ∩ D by rw [hΔeq]; exact Or.inl rfl)
    (show v ∈ (S : Set G) ∩ D by rw [hΔeq]; exact Or.inr (Or.inl rfl))
  have hnd : [hC.d, v, w, z * v * w].Nodup := by
    have huX : hC.d ∉ X := fun h => zf.not_mem_Halpha hzD hC.d_mem_alpha (hXH _ h)
    have hu1 : hC.d ≠ v := fun h => huX (h ▸ hvX)
    have hu2 : hC.d ≠ w := fun h => huX (h ▸ hwX)
    have hu3 : hC.d ≠ z * v * w := fun h => huX (h ▸ hx3)
    simp [hu1, hu2, hu3, hvw, hne1.symm, hne2.symm]
  have hFΔ : (([hC.d, v, w, z * v * w].toFinset : Finset G) : Set G) = (S : Set G) ∩ D := by
    rw [hΔeq]
    ext d
    simp
  have hcomm : (([hC.d, v, w, z * v * w].toFinset : Finset G) : Set G).Pairwise Commute := by
    rw [hFΔ]
    intro a ha b hb _
    exact hC.setup.oddT.commute_of_isPGroup S.isPGroup' ha.2 hb.2 ha.1 hb.1
  have hfix := conj_noncommProd_eq hcomm (n := n) fun x hx => by
    have hx' : x ∈ (([hC.d, v, w, z * v * w].toFinset : Finset G) : Set G) := hx
    rw [hFΔ] at hx'
    have h : n * x * n⁻¹ ∈ (S : Set G) ∩ D := (hn x).mp hx'
    rw [← hFΔ] at h
    exact h
  have hprod : ([hC.d, v, w, z * v * w].toFinset).noncommProd id hcomm = hC.d * z := by
    rw [Finset.noncommProd_toFinset _ _ _ hnd]
    simp only [List.map_id, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc v, zf.mul_mul_mul_eq (hXH v hvX) (hXH w hwX)
      (hC.setup.oddT.mul_self_eq_one (hXD v hvX)) (hC.setup.oddT.mul_self_eq_one (hXD w hwX))
      (hC.setup.oddT.commute_of_isPGroup S.isPGroup' (hXD v hvX) (hXD w hwX)
        (hTS (hX ▸ hvX).1) (hTS (hX ▸ hwX).1))]
  rw [hprod] at hfix
  have hpu : ∀ e ∈ D, Commute e hC.d → Commute (hC.d * z) e := by
    intro e he heu
    refine heu.symm.mul_left ?_
    rcases mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hC.d_mem_alpha he
      heu.symm with heα | heα
    · exact (commute_of_mem_alpha hC heα zf.mem).symm
    · exact zf.comm e (Subgroup.subset_closure heα)
  have hpv : ∀ e ∈ D, Commute e v → Commute (hC.d * z) e := by
    intro e he hev
    have hc : Commute (n⁻¹ * e * n⁻¹⁻¹) hC.d := by
      have := hev.conj n⁻¹
      rwa [← hnu, show n⁻¹ * (n * hC.d * n⁻¹) * n⁻¹⁻¹ = hC.d by group] at this
    have h := (hpu _ (hC.setup.conj_mem n⁻¹ he) hc).conj n
    rwa [hfix, show n * (n⁻¹ * e * n⁻¹⁻¹) * n⁻¹ = e by group] at h
  have hαc : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b := by
    rw [hαu]
    rintro a rfl b rfl
    exact Commute.refl _
  have h1 := eq_one_of_commute_centSet hC hH hαc hvs hpu hpv
  have : z = hC.d := by rw [eq_inv_of_mul_eq_one_right h1, hC.setup.oddT.inv_eq hC.hd]
  exact hzD (this ▸ hC.hd)

private theorem false_of_not_mem (zf : ZFacts hC z) (hH : Th91Hyp D hC) (hzD : z ∉ D)
    (hz1 : z ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨v, hvH⟩, hv⟩ := DstarH_nonempty hC
  have hvs : v ∈ DalphaStar D hC.alpha := hv
  have hvD : v ∈ D := DalphaStar_subset hC.isBlock_alpha hvs
  obtain ⟨β, hβ, hvβ⟩ := id hvs
  have hvp : IsPGroup 2 (Subgroup.zpowers (⟨v, hvH⟩ : Halpha D hC.alpha)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hC.setup.oddT.orderOf_eq_two hvD
  obtain ⟨T, hvT⟩ := hvp.exists_le_sylow
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  set X : Set G := (TG : Set G) ∩ D with hX
  obtain ⟨hXstar, hX3, hblock⟩ := zf.sylow_inter hH hzD T hX
  have hTGH : TG ≤ Halpha D hC.alpha := Subgroup.map_subtype_le _
  have hTGp : IsPGroup 2 TG := T.isPGroup'.map _
  have hvX : v ∈ X := ⟨Subgroup.mem_map_of_mem _ (hvT (Subgroup.mem_zpowers _)), hvD⟩
  have hβX : β ⊆ X := hblock β hβ v hvβ hvX
  have hαc : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
    intro a ha b hb
    have hga : g * a * g⁻¹ ∈ X := hβX (by rw [hg]; exact ⟨a, ha, rfl⟩)
    have hgb : g * b * g⁻¹ ∈ X := hβX (by rw [hg]; exact ⟨b, hb, rfl⟩)
    have h := (hC.setup.oddT.commute_of_isPGroup hTGp hga.2 hgb.2 hga.1 hgb.1).conj g⁻¹
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group,
      show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at h
  by_cases hXβ : X ⊆ β
  ·
    obtain ⟨x, hxs, hxT, y, hys, hyT, hxy⟩ := zf.exists_ne_mem_sylow hH T
    have hx : x ∈ X := ⟨hxT, DalphaStar_subset hC.isBlock_alpha hxs⟩
    have hy : y ∈ X := ⟨hyT, DalphaStar_subset hC.isBlock_alpha hys⟩
    refine hz1 (zf.eq_one_of_mem_closure hH hαc hβ ?_)
    rw [← zf.mul_mul_mul_eq (hTGH hx.1) (hTGH hy.1) (hC.setup.oddT.mul_self_eq_one hx.2)
      (hC.setup.oddT.mul_self_eq_one hy.2) (hC.setup.oddT.commute_of_isPGroup hTGp hx.2 hy.2
        hx.1 hy.1)]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (hXβ hx))
      (Subgroup.subset_closure (hXβ hy))) (Subgroup.subset_closure (hXβ (hX3 x hx y hy hxy)))
  obtain ⟨w, hwX, hwβ⟩ := Set.not_subset.mp hXβ
  have hup : IsPGroup 2 (Subgroup.zpowers hC.d) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact hC.setup.oddT.orderOf_eq_two hC.hd
  have hTGu : TG ≤ Subgroup.normalizer (Subgroup.zpowers hC.d : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((commute_of_mem_alpha hC hC.d_mem_alpha (hTGH ht)).zpow_left k).eq
  obtain ⟨S, hS⟩ := (hTGp.to_sup_of_normal_right' hup hTGu).exists_le_sylow
  have hTS : TG ≤ S := le_sup_left.trans hS
  have huS : hC.d ∈ (S : Subgroup G) := hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hXS : ∀ x ∈ X, x ∈ (S : Set G) ∩ D := fun x hx => ⟨hTS hx.1, hx.2⟩
  have hvW := zf.not_mem_closure hzD S huS hβ.1 hvβ (hXS v hvX) (Y := X \ β)
    fun y hy => ⟨hXS y hy.1, hy.2⟩
  obtain ⟨U, hU, hUcard, j, hj⟩ := zf.exists_subgroup hzD (X := X) (fun x hx => hx.2)
    (fun x hx => hTGH hx.1) hTGp (zf.mem_sylow T) (fun x hx => hx.1) hX3
  have h2c : 2 * (X \ β).ncard ≤ X.ncard + 1 := hUcard ▸ two_mul_ncard_diff_le hU
    (fun x hx => hC.setup.oddT.mul_self_eq_one hx.2) hX3 hvX hwX hwβ hvW
  have hb : ∀ {γ : Set G}, γ ∈ Dalpha D hC.alpha → γ.ncard = hC.alpha.ncard :=
    fun hγ => ncard_eq_of_mem_blockClass hγ.1
  have hb1 : 1 ≤ hC.alpha.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr hC.isBlock_alpha.nonempty
  have hdisj : ∀ {γ δ : Set G}, γ ∈ Dalpha D hC.alpha → δ ∈ Dalpha D hC.alpha →
      ∀ {x : G}, x ∈ γ → x ∉ δ → ∀ y ∈ γ, y ∉ δ := by
    intro γ δ hγ hδ x hxγ hxδ y hyγ hyδ
    exact hxδ (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hδ.1 ⟨y, hyγ, hyδ⟩ ▸ hxγ)
  obtain ⟨γ, hγ, hwγ⟩ := hXstar w hwX
  have hγXβ : γ ⊆ X \ β := fun y hy =>
    ⟨hblock γ hγ w hwγ hwX hy, hdisj hγ hβ hwγ hwβ y hy⟩
  have hXβcard : (X \ β).ncard = X.ncard - hC.alpha.ncard := by
    rw [Set.ncard_diff hβX, hb hβ]
  have hβle : hC.alpha.ncard ≤ X.ncard := hb hβ ▸ Set.ncard_le_ncard hβX
  have hγle : hC.alpha.ncard ≤ (X \ β).ncard := hb hγ ▸ Set.ncard_le_ncard hγXβ
  have hrest : ((X \ β) \ γ).ncard = (X \ β).ncard - hC.alpha.ncard := by
    rw [Set.ncard_diff hγXβ, hb hγ]
  have h3b : 3 * hC.alpha.ncard ≤ X.ncard := by
    rcases ((X \ β) \ γ).eq_empty_or_nonempty with he | ⟨w', ⟨hw'X, hw'β⟩, hw'γ⟩
    ·
      exfalso
      rw [he, Set.ncard_empty] at hrest
      rw [hUcard] at hj
      rcases j with _ | j
      · rw [pow_zero] at hj
        omega
      · rw [pow_succ] at hj
        generalize 2 ^ j = t at hj
        omega
    · obtain ⟨δ, hδ, hw'δ⟩ := hXstar w' hw'X
      have hδrest : δ ⊆ (X \ β) \ γ := fun y hy =>
        ⟨⟨hblock δ hδ w' hw'δ hw'X hy, hdisj hδ hβ hw'δ hw'β y hy⟩, hdisj hδ hγ hw'δ hw'γ y hy⟩
      have := Set.ncard_le_ncard hδrest
      rw [hb hδ, hrest, hXβcard] at this
      omega
  exact zf.false_of_ncard_eq_three hH hzD T S hTS huS hX hX3 (by omega) (by omega) hvX hwX
    (fun h => hwβ (h ▸ hvβ)) ⟨β, hβ, hvβ⟩

end ZFacts

theorem mem_alpha_of_pCore (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (_hs : IsSimpleGroup (commutator G)) {z : G}
    (hzP : (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers z)
    (hz1 : z ≠ 1) : z ∈ hC.alpha := by
  have zf := zFacts hC hH hzP hz1
  by_cases hzD : z ∈ D
  · exact zf.mem_alpha hH hzD
  · exact (zf.false_of_not_mem hH hzD hz1).elim

end CFSG.OddTranspositions.PartThree.Nine
