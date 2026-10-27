module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPAutQuot
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Defs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

section Generic

variable {G : Type*} [Group G]

theorem pow_three_eq_one_of_mem_center (hZ : Nat.card (center G) ∣ 3) {z : G} (hz : z ∈ center G) :
    z ^ 3 = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : center G) ∣ Nat.card (center G) := orderOf_dvd_natCard _
  have h2 : (⟨z, hz⟩ : center G) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 (h1.trans hZ)
  simpa using congrArg Subtype.val h2

theorem mul_comm_of_conj_modulo_center (hZ3 : ∀ z ∈ center G, z ^ 3 = 1) {x y h : G}
    (hc : x * y * x⁻¹ * y⁻¹ ∈ center G) (hx : h * x * h⁻¹ * x⁻¹ ∈ center G)
    (hy : h * y * h⁻¹ * y ∈ center G) : x * y = y * x := by
  have hconj : ∀ z ∈ center G, ∀ w : G, z * w * z⁻¹ = w := fun z hz w => by
    rw [← Subgroup.mem_center_iff.1 hz w, mul_inv_cancel_right]
  obtain ⟨a, ha, e1⟩ : ∃ a ∈ center G, h * x * h⁻¹ = a * x := ⟨_, hx, by group⟩
  obtain ⟨b, hb, e2⟩ : ∃ b ∈ center G, h * y * h⁻¹ = b * y⁻¹ := ⟨_, hy, by group⟩
  obtain ⟨c, hc', e3⟩ : ∃ c ∈ center G, x * y * x⁻¹ * y⁻¹ = c := ⟨_, hc, rfl⟩
  have e4 : h * c * h⁻¹ = c := by
    rw [Subgroup.mem_center_iff.1 hc' h, mul_inv_cancel_right]
  have e5 : h * c * h⁻¹ = (a * x) * (b * y⁻¹) * (a * x)⁻¹ * (b * y⁻¹)⁻¹ := by
    calc h * c * h⁻¹ = h * (x * y * x⁻¹ * y⁻¹) * h⁻¹ := by rw [e3]
      _ = (h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ * (h * y * h⁻¹)⁻¹ := by group
      _ = (a * x) * (b * y⁻¹) * (a * x)⁻¹ * (b * y⁻¹)⁻¹ := by rw [e1, e2]
  have e6 : (a * x) * (b * y⁻¹) * (a * x)⁻¹ * (b * y⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ * y := by
    calc (a * x) * (b * y⁻¹) * (a * x)⁻¹ * (b * y⁻¹)⁻¹
        = a * (x * b * y⁻¹ * x⁻¹) * a⁻¹ * y * b⁻¹ := by group
      _ = (x * b * y⁻¹ * x⁻¹) * y * b⁻¹ := by rw [hconj a ha]
      _ = x * (b * (y⁻¹ * x⁻¹ * y) * b⁻¹) := by group
      _ = x * (y⁻¹ * x⁻¹ * y) := by rw [hconj b hb]
      _ = x * y⁻¹ * x⁻¹ * y := by group
  have e7 : x * y * x⁻¹ = c * y := by rw [← e3]; group
  have e8 : x * y⁻¹ * x⁻¹ = y⁻¹ * c⁻¹ := by
    calc x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
      _ = y⁻¹ * c⁻¹ := by rw [e7, mul_inv_rev]
  have e9 : c = c⁻¹ := by
    calc c = x * y⁻¹ * x⁻¹ * y := e4.symm.trans (e5.trans e6)
      _ = y⁻¹ * c⁻¹ * y := by rw [e8]
      _ = c⁻¹ * y⁻¹ * y := by rw [Subgroup.mem_center_iff.1 (inv_mem hc') y⁻¹]
      _ = c⁻¹ := by group
  have e10 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← e9]
      _ = 1 := mul_inv_cancel c
  have e11 : c = 1 := by
    have h3 := hZ3 c hc'
    rwa [pow_three', e10, one_mul] at h3
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 (e3.trans e11))

theorem mul_comm_of_lift {e f g : G ⧸ center G} (hZ : Nat.card (center G) ∣ 3)
    (hef : e * f = f * e) (hge : g * e = e * g) (hgf : g * f = f⁻¹ * g) {x y h : G}
    (hx : (QuotientGroup.mk x : G ⧸ center G) = e) (hy : (QuotientGroup.mk y : G ⧸ center G) = f)
    (hh : (QuotientGroup.mk h : G ⧸ center G) = g) : x * y = y * x := by
  refine mul_comm_of_conj_modulo_center
    (fun z hz => pow_three_eq_one_of_mem_center hZ hz) (h := h) ?_ ?_ ?_
  · refine (QuotientGroup.eq_one_iff _).1 ?_
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, hy]
    rw [hef]; group
  · refine (QuotientGroup.eq_one_iff _).1 ?_
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, hh]
    rw [hge]; group
  · refine (QuotientGroup.eq_one_iff _).1 ?_
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, hh]
    rw [hgf]; group

theorem mul_comm_of_mem_closure_pair {e f : G ⧸ center G} {x y w : G}
    (hx : (QuotientGroup.mk x : G ⧸ center G) = e) (hy : (QuotientGroup.mk y : G ⧸ center G) = f)
    (hwx : x * w = w * x) (hwy : y * w = w * y) {a : G}
    (ha : (QuotientGroup.mk a : G ⧸ center G) ∈ closure ({e, f} : Set (G ⧸ center G))) :
    a * w = w * a := by
  have hD : closure ({e, f} : Set (G ⧸ center G)) ≤
      (centralizer ({w} : Set G)).map (QuotientGroup.mk' (center G)) := by
    rw [closure_le]
    rintro u (rfl | rfl)
    · exact ⟨x, mem_centralizer_singleton_iff.2 hwx, hx⟩
    · exact ⟨y, mem_centralizer_singleton_iff.2 hwy, hy⟩
  have hker : (QuotientGroup.mk' (center G)).ker ≤ centralizer ({w} : Set G) := by
    rw [QuotientGroup.ker_mk']
    exact center_le_centralizer _
  have h2 : a ∈ centralizer ({w} : Set G) := by
    have h3 : a ∈ ((centralizer ({w} : Set G)).map (QuotientGroup.mk' (center G))).comap
        (QuotientGroup.mk' (center G)) := hD ha
    rwa [comap_map_eq_self hker] at h3
  exact mem_centralizer_singleton_iff.1 h2

theorem card_sup_eq_mul_of_commute_of_inf_eq_bot {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hcomm : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective H.subtype K.subtype hcomm).2 ?_
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(H ⊔ K) = Nat.card (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

theorem exists_mulEquiv_of_center_eq_bot (h : center G = ⊥) :
    ∃ φ : G ≃* G ⧸ center G, ∀ x, φ x = QuotientGroup.mk x := by
  have hinj : Function.Injective (QuotientGroup.mk' (center G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', h]
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩, fun x => rfl⟩

theorem closure_pair_isElemAbelian_card [Finite G] {a b : G} (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : a * b = b * a) (hn : b ∉ zpowers a) :
    IsElemAbelian 3 (closure ({a, b} : Set G)) ∧ Nat.card (closure ({a, b} : Set G)) = 3 ^ 2 := by
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  refine ⟨IsElemAbelian.closure_of_commute ?_ ?_, ?_⟩
  · rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  · rintro x (rfl | rfl)
    · exact ha3
    · exact hb3
  · have hdisj : zpowers a ⊓ zpowers b = ⊥ := by
      have hle : zpowers a ⊓ zpowers b ≤ zpowers b := inf_le_right
      have hdvd : Nat.card ↥(zpowers a ⊓ zpowers b) ∣ 3 := by
        simpa [Nat.card_zpowers, hb] using Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : zpowers a ⊓ zpowers b = zpowers b :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hb])
        apply hn
        have hbm : b ∈ zpowers a ⊓ zpowers b := by rw [heq]; exact mem_zpowers b
        exact hbm.1
    have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
    have hcl : closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    rw [hcl, card_sup_eq_mul_of_commute_of_inf_eq_bot hcomm hdisj, Nat.card_zpowers,
      Nat.card_zpowers, ha, hb]
    norm_num

theorem closure_pair_central_isElemAbelian_card [Finite G] {z ζ : G} (hz : orderOf z = 3)
    (hζ : orderOf ζ = 3) (hzc : z ∉ center G) (hζc : ζ ∈ center G) :
    IsElemAbelian 3 (closure ({z, ζ} : Set G)) ∧ Nat.card (closure ({z, ζ} : Set G)) = 3 ^ 2 := by
  refine closure_pair_isElemAbelian_card hz hζ (Subgroup.mem_center_iff.1 hζc z) ?_
  intro hmem
  have hle : zpowers ζ ≤ zpowers z := zpowers_le.2 hmem
  have heq : zpowers ζ = zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, hζ])
  apply hzc
  have hzz : z ∈ zpowers ζ := heq ▸ mem_zpowers z
  exact zpowers_le.2 hζc hzz

theorem exists_central_order_three [Finite G] (h3 : Nat.card (center G) = 3) :
    ∃ ζ : G, ζ ∈ center G ∧ orderOf ζ = 3 := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := center G) 3 (by rw [h3])
  exact ⟨ζ, ζ.2, by rw [Subgroup.orderOf_coe]; exact hζ⟩

theorem exists_cube_one_lift [Finite G] (hZ : Nat.card (center G) ∣ 3) {e f g : G ⧸ center G}
    (he : orderOf e = 3) (hf : orderOf f = 3) (hef : e * f = f * e) (hn : f ∉ zpowers e)
    (hge : g * e = e * g) (hgf : g * f = f⁻¹ * g) :
    ∃ w : G, w ^ 3 = 1 ∧ w ∉ center G ∧
      ∀ a : G, (QuotientGroup.mk a : G ⧸ center G) ∈ closure ({e, f} : Set (G ⧸ center G)) →
        a * w = w * a := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective e
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective f
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective g
  have hxy : x * y = y * x := mul_comm_of_lift hZ hef hge hgf hx hy hh
  have he3 : e ^ 3 = 1 := he ▸ pow_orderOf_eq_one e
  have hf3 : f ^ 3 = 1 := hf ▸ pow_orderOf_eq_one f
  have hx3 : x ^ 3 ∈ center G :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow, hx, he3])
  have hy3 : y ^ 3 ∈ center G :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow, hy, hf3])
  by_cases hu : x ^ 3 = 1
  · refine ⟨x, hu, fun hxc => ?_, fun a ha => mul_comm_of_mem_closure_pair hx hy rfl hxy.symm ha⟩
    have h1 : e = 1 := by rw [← hx]; exact (QuotientGroup.eq_one_iff _).2 hxc
    rw [h1, orderOf_one] at he
    exact absurd he (by norm_num)
  · have h3 : Nat.card (center G) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
      · exfalso
        have hb : center G = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        rw [hb, Subgroup.mem_bot] at hx3
        exact hu hx3
      · exact h3
    have hu1 : (⟨x ^ 3, hx3⟩ : center G) ≠ 1 := fun h => hu (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_of_prime_card (g' := (⟨y ^ 3, hy3⟩ : center G)) h3 hu1)
    have hk' : (x ^ 3) ^ k = y ^ 3 := congrArg Subtype.val hk
    have hcw : Commute y (x ^ k)⁻¹ := ((show Commute y x from hxy.symm).pow_right k).inv_right
    refine ⟨y * (x ^ k)⁻¹, ?_, ?_, fun a ha => mul_comm_of_mem_closure_pair hx hy ?_ ?_ ha⟩
    · rw [hcw.mul_pow, inv_pow, pow_right_comm, hk', mul_inv_cancel]
    · intro hwc
      have h1 : (QuotientGroup.mk (y * (x ^ k)⁻¹) : G ⧸ center G) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hwc
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hx, hy,
        mul_inv_eq_one] at h1
      apply hn
      rw [h1]
      exact pow_mem (mem_zpowers e) k
    · exact ((show Commute x y from hxy).mul_right ((Commute.refl x).pow_right k).inv_right).eq
    · exact ((Commute.refl y).mul_right hcw).eq

end Generic

section Main

variable {X : Type} [Group X] [Finite X]

theorem exists_isElemAbelian_of_center_eq_bot (hZ1 : center X = ⊥)
    (hC : YCoverPlus (X ⧸ center X)) {t : X ⧸ center X} (ht : orderOf t = 3) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∀ a : X, (QuotientGroup.mk a : X ⧸ center X) = t → a ∈ E := by
  obtain ⟨e, f, g, he, hf, hef, hn, hte, -, -⟩ := hC t ht
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_center_eq_bot hZ1
  obtain ⟨hel, hcard⟩ := closure_pair_isElemAbelian_card he hf hef hn
  refine ⟨(closure ({e, f} : Set (X ⧸ center X))).map φ.symm.toMonoidHom,
    hel.map _, ?_, fun a ha => ⟨t, hte, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard]
  · rw [← ha, ← hφ]
    simp

theorem exists_isElemAbelian_of_central_order_three (hZ : Nat.card (center X) ∣ 3)
    (hC : YCoverPlus (X ⧸ center X)) {t : X ⧸ center X} (ht : orderOf t = 3) {ζ : X}
    (hζ : ζ ∈ center X) (hζ3 : orderOf ζ = 3) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ζ ∈ E ∧
      ∀ a : X, (QuotientGroup.mk a : X ⧸ center X) = t → ∀ b ∈ E, a * b = b * a := by
  obtain ⟨e, f, g, he, hf, hef, hn, hte, hge, hgf⟩ := hC t ht
  obtain ⟨w, hw3, hwc, hwcomm⟩ := exists_cube_one_lift hZ he hf hef hn hge hgf
  have hw : orderOf w = 3 := orderOf_eq_prime hw3 (fun h => hwc (h ▸ one_mem _))
  obtain ⟨hel, hcard⟩ := closure_pair_central_isElemAbelian_card hw hζ3 hwc hζ
  refine ⟨closure ({w, ζ} : Set X), hel, hcard, subset_closure (by simp), ?_⟩
  intro a ha b hb
  have hat : (QuotientGroup.mk a : X ⧸ center X) ∈ closure ({e, f} : Set (X ⧸ center X)) := by
    rw [ha]; exact hte
  have hle : closure ({w, ζ} : Set X) ≤ centralizer ({a} : Set X) := by
    rw [closure_le]
    rintro u (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 (hwcomm a hat).symm
    · exact mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hζ a).symm
  exact (mem_centralizer_singleton_iff.1 (hle hb)).symm

theorem exists_isElemAbelian_centralized_by_lift (hZ : Nat.card (center X) ∣ 3)
    (hC : YCoverPlus (X ⧸ center X)) {t : X ⧸ center X} (ht : orderOf t = 3) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∀ a : X, (QuotientGroup.mk a : X ⧸ center X) = t → ∀ b ∈ E, a * b = b * a := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
  · obtain ⟨E, hE, hcard, hmem⟩ :=
      exists_isElemAbelian_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ h1) hC ht
    exact ⟨E, hE, hcard, fun a ha b hb => hE.comm (hmem a ha) hb⟩
  · obtain ⟨ζ, hζ, hζ3⟩ := exists_central_order_three h3
    obtain ⟨E, hE, hcard, -, hcomm⟩ :=
      exists_isElemAbelian_of_central_order_three hZ hC ht hζ hζ3
    exact ⟨E, hE, hcard, hcomm⟩

theorem u3E9Cover_of_Y (hZ : Nat.card (center X) ∣ 3) (hC : YCoverPlus (X ⧸ center X))
    (hex : ∃ t : X ⧸ center X, orderOf t = 3) :
    ∀ z : X, orderOf z = 3 → ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ z ∈ E := by
  intro z hz
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
  · have hcen : center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_center_eq_bot hcen
    have ht : orderOf (QuotientGroup.mk z : X ⧸ center X) = 3 := by
      rw [← hφ, MulEquiv.orderOf_eq]; exact hz
    obtain ⟨E, hE, hcard, hmem⟩ := exists_isElemAbelian_of_center_eq_bot hcen hC ht
    exact ⟨E, hE, hcard, hmem z rfl⟩
  · by_cases hzc : z ∈ center X
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨E, hE, hcard, hzE, -⟩ :=
        exists_isElemAbelian_of_central_order_three hZ hC ht hzc hz
      exact ⟨E, hE, hcard, hzE⟩
    · obtain ⟨ζ, hζ, hζ3⟩ := exists_central_order_three h3
      obtain ⟨hE, hcard⟩ := closure_pair_central_isElemAbelian_card hz hζ3 hzc hζ
      exact ⟨_, hE, hcard, subset_closure (by simp)⟩

theorem u3Fix3Inner_of_Y (hZ : Nat.card (center X) ∣ 3) (hW : YFix3Wit (X ⧸ center X))
    (hex : ∃ t : X ⧸ center X, orderOf t = 3) :
    ∀ α : MulAut X, α ^ 7 = 1 → α ∈ (MulAut.conj : X →* MulAut X).range →
      ∃ z : X, orderOf z = 3 ∧ α z = z := by
  intro α hα7 hαr
  obtain ⟨s, rfl⟩ := hαr
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
  · have hcen : center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨φ, -⟩ := exists_mulEquiv_of_center_eq_bot hcen
    have hs7 : s ^ 7 = 1 := by
      have hc : s ^ 7 ∈ center X := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hh : (MulAut.conj (s ^ 7) : MulAut X) = 1 := by rw [map_pow]; exact hα7
        have h2 : (MulAut.conj (s ^ 7) : MulAut X) y = y := by rw [hh]; rfl
        rw [MulAut.conj_apply] at h2
        exact (mul_inv_eq_iff_eq_mul.1 h2).symm
      rw [hcen, Subgroup.mem_bot] at hc
      exact hc
    by_cases hs1 : s = 1
    · obtain ⟨t, ht⟩ := hex
      refine ⟨φ.symm t, ?_, ?_⟩
      · rw [MulEquiv.orderOf_eq]; exact ht
      · simp [hs1]
    · have h7 : orderOf (φ s) = 7 := by
        haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        rw [MulEquiv.orderOf_eq]; exact orderOf_eq_prime hs7 hs1
      obtain ⟨zb, hz3, hzs⟩ := hW (φ s) h7
      refine ⟨φ.symm zb, ?_, ?_⟩
      · rw [MulEquiv.orderOf_eq]; exact hz3
      · have hcomm : φ.symm zb * s = s * φ.symm zb := by
          apply φ.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact hzs
        rw [MulAut.conj_apply, ← hcomm, mul_inv_cancel_right]
  · obtain ⟨ζ, hζ, hζ3⟩ := exists_central_order_three h3
    refine ⟨ζ, hζ3, ?_⟩
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.1 hζ s, mul_inv_cancel_right]

theorem u3E9Fix_of_Y (hP : commutator X = ⊤) (hZ : Nat.card (center X) ∣ 3)
    (hC : YCoverPlus (X ⧸ center X)) (hF : YFixClaim (X ⧸ center X))
    (hex : ∃ t : X ⧸ center X, orderOf t = 3) :
    ∀ x : X, orderOf x = 7 → ∀ β : MulAut X, β ^ 3 = 1 → β x = x →
      ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ e ∈ E, β e = e := by
  intro x hx7 β hβ3 hβx
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx7' : x ^ 7 = 1 := hx7 ▸ pow_orderOf_eq_one x
  have hxc : (QuotientGroup.mk x : X ⧸ center X) ≠ 1 := by
    intro h1
    have h3 := pow_three_eq_one_of_mem_center hZ ((QuotientGroup.eq_one_iff _).1 h1)
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [hx7] at hd
    omega
  have hxo : orderOf (QuotientGroup.mk x : X ⧸ center X) = 7 := by
    refine orderOf_eq_prime ?_ hxc
    rw [← QuotientGroup.mk_pow, hx7', QuotientGroup.mk_one]
  have hb3 : autQuot β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hbx : autQuot β (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [autQuot_mk, hβx]
  obtain ⟨tb, htb3, htb⟩ := hF (autQuot β) hb3 _ hxo hbx
  obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective tb
  have hβ : β = MulAut.conj t' := by
    refine autQuot_injective hP ?_
    rw [autQuot_conj]
    ext y
    exact htb y
  by_cases h1 : (QuotientGroup.mk t' : X ⧸ center X) = 1
  · obtain ⟨t0, ht0⟩ := hex
    obtain ⟨E, hE, hcard, -⟩ := exists_isElemAbelian_centralized_by_lift hZ hC ht0
    refine ⟨E, hE, hcard, fun e _ => ?_⟩
    rw [hβ, MulAut.conj_apply, ← Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 h1) e,
      mul_inv_cancel_right]
  · have ho : orderOf (QuotientGroup.mk t' : X ⧸ center X) = 3 := orderOf_eq_prime htb3 h1
    obtain ⟨E, hE, hcard, hcomm⟩ := exists_isElemAbelian_centralized_by_lift hZ hC ho
    refine ⟨E, hE, hcard, fun e he => ?_⟩
    rw [hβ, MulAut.conj_apply, hcomm t' rfl e he, mul_inv_cancel_right]

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
