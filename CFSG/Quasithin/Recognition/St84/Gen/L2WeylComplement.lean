module

public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
import CFSG.CGT.Timmesfeld75.L2Swap
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem wElt_conj_torusElt_inv {F : Type} [Field F] [CharP F 2] (a : Fˣ) :
    (wElt : SL(2, F)) * torusElt a * wElt⁻¹ = (torusElt a)⁻¹ := by
  apply sl2_ext
  all_goals
    sl2_simp
    simp only [CharTwo.neg_eq, inv_inv]
    ring

theorem borel_sup_zpowers_wElt {F : Type} [Field F] :
    borel F ⊔ Subgroup.zpowers (wElt : SL(2, F)) = ⊤ := by
  rw [eq_top_iff, ← utri_sup_ltri (F := F)]
  apply sup_le
  · intro x hx
    exact Subgroup.mem_sup_left (utri_le_borel hx)
  · rw [← conjSubgroup_wElt_utri (F := F)]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers wElt))
      (Subgroup.mem_sup_left (utri_le_borel hy)))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers wElt)))

theorem exists_mulEquiv_of_complement {G M : Type*} [Group G] [Group M] {L Q K : Subgroup G}
    (α : ↥L →* M) (hα : Function.Surjective α)
    (hQL : Q ≤ L) (hKL : K ≤ L) (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q)
    (hsup : Q ⊔ K = L) (hinf : Q ⊓ K = ⊥) :
    ∃ eK : ↥K ≃* M, ∀ k : ↥K, eK k = α ⟨k, hKL k.2⟩ := by
  classical
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk q hq
    have hkL : k ∈ L := hKL hk
    have hqL : q ∈ L := hQL hq
    have hsub : (⟨k * q * k⁻¹, L.mul_mem (L.mul_mem hkL hqL) (L.inv_mem hkL)⟩ : ↥L) =
        ⟨k, hkL⟩ * ⟨q, hqL⟩ * ⟨k, hkL⟩⁻¹ := Subtype.ext rfl
    refine (hker ⟨k * q * k⁻¹, L.mul_mem (L.mul_mem hkL hqL) (L.inv_mem hkL)⟩).mp ?_
    rw [hsub, map_mul, map_mul, map_inv, (hker ⟨q, hqL⟩).mpr hq]
    group
  let αK : ↥K →* M := α.comp (Subgroup.inclusion hKL)
  have hinj : Function.Injective αK := by
    intro a b hab
    have h1 : αK (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥K) : G) ∈ Q :=
      (hker ⟨a * b⁻¹, hKL (a * b⁻¹).2⟩).mp h1
    have h3 : ((a * b⁻¹ : ↥K) : G) ∈ K := (a * b⁻¹).2
    have h4 : (a * b⁻¹ : ↥K) = 1 := by
      have hmem : ((a * b⁻¹ : ↥K) : G) ∈ Q ⊓ K := ⟨h2, h3⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    rwa [mul_inv_eq_one] at h4
  have hsurj : Function.Surjective αK := by
    intro y
    obtain ⟨x, hx⟩ := hα y
    have hxL : (x : G) ∈ Q ⊔ K := by rw [hsup]; exact x.2
    obtain ⟨q, hq, k, hk, hqk⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKQ).mp hxL
    refine ⟨⟨k, hk⟩, ?_⟩
    have hq1 : α ⟨q, hQL hq⟩ = 1 := (hker ⟨q, hQL hq⟩).mpr hq
    have hxeq : (⟨q, hQL hq⟩ * ⟨k, hKL hk⟩ : ↥L) = x := Subtype.ext hqk.symm
    calc αK ⟨k, hk⟩ = α ⟨k, hKL hk⟩ := rfl
      _ = α ⟨q, hQL hq⟩ * α ⟨k, hKL hk⟩ := by rw [hq1, one_mul]
      _ = α (⟨q, hQL hq⟩ * ⟨k, hKL hk⟩ : ↥L) := (map_mul α _ _).symm
      _ = α x := by rw [hxeq]
      _ = y := hx
  exact ⟨MulEquiv.ofBijective αK ⟨hinj, hsurj⟩, fun _ => rfl⟩

private theorem image_le_borel_card {G : Type*} [Group G] {L S K T : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hSL : S ≤ L) (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hKL : K ≤ L)
    (eK : ↥K ≃* SL(2, F)) (heK : ∀ k : ↥K, (eK k : SL(2, F)) = α ⟨k, hKL k.2⟩)
    (hTK : T ≤ K) (hTN : T ≤ Subgroup.normalizer (S : Set G))
    (hTcard : Nat.card T = Nat.card F - 1) :
    (T.subgroupOf K).map eK.toMonoidHom ≤ borel F ∧
      Nat.card ((T.subgroupOf K).map eK.toMonoidHom) = Nat.card F - 1 := by
  constructor
  · rintro x ⟨t, ht, rfl⟩
    show (eK t : SL(2, F)) ∈ borel F
    rw [heK t]
    exact (mem_normalizer_iff_alpha_mem_borel hSL α hα hmem ⟨t, hKL t.2⟩).mp (hTN ht)
  · rw [Subgroup.card_map_of_injective eK.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hTcard]

private theorem exists_weyl_inverting {G : Type*} [Group G] {L S K T : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hSL : S ≤ L) (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hKL : K ≤ L)
    (eK : ↥K ≃* SL(2, F)) (heK : ∀ k : ↥K, (eK k : SL(2, F)) = α ⟨k, hKL k.2⟩)
    (hTK : T ≤ K) (hTN : T ≤ Subgroup.normalizer (S : Set G))
    (hTcard : Nat.card T = Nat.card F - 1) :
    ∃ w : ↥K, ∃ u ∈ utri F, eK w = u⁻¹ * wElt * u ∧
      ∀ t ∈ T, (w : G) * t * (w : G)⁻¹ = t⁻¹ := by
  classical
  let A : Subgroup SL(2, F) := (T.subgroupOf K).map eK.toMonoidHom
  obtain ⟨hA_le, hAcard⟩ := image_le_borel_card α hα hSL hmem hKL eK heK hTK hTN hTcard
  obtain ⟨u, hu, hAconj⟩ := exists_utri_conj_eq_torus (T := A) hA_le hAcard
  let w₀ : SL(2, F) := u⁻¹ * wElt * u
  let w : ↥K := eK.symm w₀
  have heKw : eK w = w₀ := eK.apply_symm_apply w₀
  refine ⟨w, u, hu, heKw, ?_⟩
  intro t ht
  have htK : t ∈ K := hTK ht
  have hgt : u * eK ⟨t, htK⟩ * u⁻¹ ∈ torus F := by
    have hmemA : eK ⟨t, htK⟩ ∈ A :=
      Subgroup.mem_map_of_mem eK.toMonoidHom
        (show (⟨t, htK⟩ : ↥K) ∈ T.subgroupOf K from ht)
    have h := Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hmemA
    rw [hAconj] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hwg : wElt * (u * eK ⟨t, htK⟩ * u⁻¹) * wElt⁻¹ =
      (u * eK ⟨t, htK⟩ * u⁻¹)⁻¹ := by
    obtain ⟨a, ha⟩ := mem_torus_iff.mp hgt
    rw [ha]
    exact wElt_conj_torusElt_inv a
  have hmem1 : (w : G) * t * (w : G)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem w.2 htK) (K.inv_mem w.2)
  have hmem2 : t⁻¹ ∈ K := K.inv_mem htK
  have hEqK : (⟨(w : G) * t * (w : G)⁻¹, hmem1⟩ : ↥K) = ⟨t⁻¹, hmem2⟩ := by
    apply eK.injective
    have h1 : eK ⟨(w : G) * t * (w : G)⁻¹, hmem1⟩ =
        w₀ * eK ⟨t, htK⟩ * w₀⁻¹ := by
      rw [show (⟨(w : G) * t * (w : G)⁻¹, hmem1⟩ : ↥K) =
        w * ⟨t, htK⟩ * w⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv, heKw]
    have h2 : w₀ * eK ⟨t, htK⟩ * w₀⁻¹ = (eK ⟨t, htK⟩)⁻¹ := by
      have h := hwg
      dsimp only [w₀] at h ⊢
      calc u⁻¹ * wElt * u * eK ⟨t, htK⟩ * (u⁻¹ * wElt * u)⁻¹
          = u⁻¹ * (wElt * (u * eK ⟨t, htK⟩ * u⁻¹) * wElt⁻¹) * u := by group
        _ = u⁻¹ * (u * eK ⟨t, htK⟩ * u⁻¹)⁻¹ * u := by rw [h]
        _ = (eK ⟨t, htK⟩)⁻¹ := by group
    have h3 : eK ⟨t⁻¹, hmem2⟩ = (eK ⟨t, htK⟩)⁻¹ := by
      rw [show (⟨t⁻¹, hmem2⟩ : ↥K) = ⟨t, htK⟩⁻¹ from Subtype.ext rfl, map_inv]
    rw [h1, h2, h3]
  exact congrArg Subtype.val hEqK

private theorem closure_eq_of_complement {G : Type*} [Group G] {L S K : Subgroup G}
    {F : Type} [Field F] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hSL : S ≤ L) (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hKL : K ≤ L)
    (eK : ↥K ≃* SL(2, F)) (heK : ∀ k : ↥K, (eK k : SL(2, F)) = α ⟨k, hKL k.2⟩)
    (w : ↥K) (hw : ∃ b₁ ∈ borel F, ∃ b₂ ∈ borel F, b₁ * eK w * b₂ = wElt) :
    Subgroup.closure (((K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪
      {(w : G)}) = K := by
  classical
  let C : Subgroup G :=
    Subgroup.closure (((K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {(w : G)})
  have hCK : C ≤ K := by
    refine (Subgroup.closure_le K).mpr ?_
    rintro x (hx | hx)
    · exact hx.1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact w.2
  have hwC : (w : G) ∈ C := Subgroup.subset_closure (Or.inr (Set.mem_singleton (w : G)))
  have hKC : K ≤ C := by
    let A' : Subgroup SL(2, F) := (C.subgroupOf K).map eK.toMonoidHom
    have hborel : borel F ≤ A' := by
      intro b hb
      let k : ↥K := eK.symm b
      have hkb : (eK k : SL(2, F)) = b := eK.apply_symm_apply b
      have hkN : (k : G) ∈ Subgroup.normalizer (S : Set G) :=
        (mem_normalizer_iff_alpha_mem_borel hSL α hα hmem ⟨k, hKL k.2⟩).mpr (by
          rw [← heK k, hkb]
          exact hb)
      have hkC : (k : G) ∈ C :=
        Subgroup.subset_closure (Or.inl (show (k : G) ∈ K ⊓ Subgroup.normalizer (S : Set G)
          from ⟨k.2, hkN⟩))
      have hmem : eK k ∈ A' :=
        Subgroup.mem_map_of_mem eK.toMonoidHom (show k ∈ C.subgroupOf K from hkC)
      rwa [hkb] at hmem
    have hwEltA : (wElt : SL(2, F)) ∈ A' := by
      obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := hw
      have h1 : b₁ ∈ A' := hborel hb₁
      have h2 : eK w ∈ A' :=
        Subgroup.mem_map_of_mem eK.toMonoidHom (show w ∈ C.subgroupOf K from hwC)
      have h3 : b₂ ∈ A' := hborel hb₂
      rw [← hb]
      exact A'.mul_mem (A'.mul_mem h1 h2) h3
    have htop : A' = ⊤ := by
      rw [eq_top_iff, ← borel_sup_zpowers_wElt (F := F)]
      exact sup_le hborel (Subgroup.zpowers_le.mpr hwEltA)
    intro k hk
    have hkA : eK ⟨k, hk⟩ ∈ A' := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp hkA
    have hceq : c = ⟨k, hk⟩ := eK.injective hck
    have hval : (c : G) = k := congrArg Subtype.val hceq
    have hcC : (c : G) ∈ C := hc
    rwa [hval] at hcC
  exact le_antisymm hCK hKC

variable {G : Type*} [Group G] {L Q S K T : Subgroup G} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem exists_weyl_of_complement (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hSL : S ≤ L)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hsup : Q ⊔ K = L) (hinf : Q ⊓ K = ⊥)
    (hTK : T ≤ K) (hTN : T ≤ Subgroup.normalizer (S : Set G))
    (hTcard : Nat.card T = Nat.card F - 1) :
    ∃ w ∈ K, (∀ t ∈ T, w * t * w⁻¹ = t⁻¹) ∧
      Subgroup.closure
        (((K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w}) = K := by
  classical
  have hQL : Q ≤ L := hsup ▸ (show Q ≤ Q ⊔ K from le_sup_left)
  have hKL : K ≤ L := hsup ▸ (show K ≤ Q ⊔ K from le_sup_right)
  obtain ⟨eK, heK⟩ := exists_mulEquiv_of_complement α hα hQL hKL hker hsup hinf
  obtain ⟨w, u, hu, hw0, hInvert⟩ :=
    exists_weyl_inverting α hα hSL hmem hKL eK heK hTK hTN hTcard
  refine ⟨(w : G), w.2, hInvert, ?_⟩
  refine closure_eq_of_complement α hα hSL hmem hKL eK heK w
    ⟨u, utri_le_borel hu, u⁻¹, Subgroup.inv_mem _ (utri_le_borel hu), ?_⟩
  rw [hw0]
  group

private theorem exists_weyl_core (A : Subgroup SL(2, F)) (hA : A ≤ borel F)
    (hAcard : Nat.card A = Nat.card F - 1) {y : SL(2, F)} (hy : y ∈ utri F) (hy1 : y ≠ 1) :
    ∃ u w : SL(2, F), u ∈ utri F ∧ A.map (MulAut.conj u).toMonoidHom = torus F ∧
      (∃ b₁ ∈ borel F, ∃ b₂ ∈ borel F, b₁ * w * b₂ = wElt) ∧
      (∀ z ∈ torus F, w * z * w⁻¹ = z⁻¹) ∧
      (w * (u * y * u⁻¹)) ^ 3 = 1 := by
  classical
  obtain ⟨u, hu, hAconj⟩ := exists_utri_conj_eq_torus hA hAcard
  have hy' : u * y * u⁻¹ ∈ utri F := conj_mem_utri_of_mem_borel (utri_le_borel hu) hy
  have hy'1 : u * y * u⁻¹ ≠ 1 := by
    intro h1
    apply hy1
    have h2 : y = u⁻¹ * (u * y * u⁻¹) * u := by group
    rw [h2, h1]
    group
  let q : F := (u * y * u⁻¹) 0 1
  have hy'q : u * y * u⁻¹ = utriElt q := eq_utriElt_of_mem_utri hy'
  have hq : q ≠ 0 := by
    intro h0
    exact hy'1 (by rw [hy'q, h0, utriElt_zero])
  let lam : Fˣ := (Units.mk0 q hq)⁻¹
  let w : SL(2, F) := wElt * torusElt lam
  have hlam : (lam : F) = q⁻¹ := by
    rw [show lam = (Units.mk0 q hq)⁻¹ from rfl, Units.val_inv_eq_inv_val, Units.val_mk0]
  let M : SL(2, F) := wElt * torusElt lam * utriElt q
  have htr : M 0 0 + M 1 1 = 1 := by
    have hmain : M 0 0 + M 1 1 = (lam : F) * q := by
      show (wElt * torusElt lam * utriElt q : SL(2, F)) 0 0 +
        (wElt * torusElt lam * utriElt q : SL(2, F)) 1 1 = (lam : F) * q
      sl2_simp
      simp only [CharTwo.neg_eq]
      ring
    rw [hmain, hlam, inv_mul_cancel₀ hq]
  refine ⟨u, w, hu, hAconj, ?_, ?_, ?_⟩
  · refine ⟨1, one_mem _, (torusElt lam)⁻¹,
      inv_mem (torus_le_borel (torusElt_mem_torus lam)), ?_⟩
    show (1 : SL(2, F)) * (wElt * torusElt lam) * (torusElt lam)⁻¹ = wElt
    group
  · intro z hz
    obtain ⟨μ, rfl⟩ := mem_torus_iff.mp hz
    have hcomm : torusElt lam * torusElt μ = torusElt μ * torusElt lam := by
      rw [← torusElt_mul, ← torusElt_mul, mul_comm]
    show (wElt * torusElt lam) * torusElt μ * (wElt * torusElt lam)⁻¹ = (torusElt μ)⁻¹
    calc (wElt * torusElt lam) * torusElt μ * (wElt * torusElt lam)⁻¹
        = wElt * (torusElt lam * torusElt μ * (torusElt lam)⁻¹) * wElt⁻¹ := by group
      _ = wElt * torusElt μ * wElt⁻¹ := by rw [hcomm]; group
      _ = (torusElt μ)⁻¹ := wElt_conj_torusElt_inv μ
  · show (wElt * torusElt lam * (u * y * u⁻¹)) ^ 3 = 1
    rw [hy'q]
    exact pow_three_eq_one_of_trace_eq_one htr

theorem exists_weyl_of_complement_pow_three (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hSL : S ≤ L)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (hsup : Q ⊔ K = L) (hinf : Q ⊓ K = ⊥)
    (hTK : T ≤ K) (hTN : T ≤ Subgroup.normalizer (S : Set G))
    (hTcard : Nat.card T = Nat.card F - 1) {y : G} (hyK : y ∈ K) (hyS : y ∈ S) (hyQ : y ∉ Q) :
    ∃ w ∈ K, (∀ t ∈ T, w * t * w⁻¹ = t⁻¹) ∧
      Subgroup.closure
        (((K ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) ∪ {w}) = K ∧
      (w * y) ^ 3 = 1 := by
  classical
  have hQL : Q ≤ L := hsup ▸ le_sup_left
  have hKL : K ≤ L := hsup ▸ le_sup_right
  obtain ⟨eK, heK⟩ := exists_mulEquiv_of_complement α hα hQL hKL hker hsup hinf
  let A : Subgroup SL(2, F) := (T.subgroupOf K).map eK.toMonoidHom
  obtain ⟨hA_le, hAcard⟩ := image_le_borel_card α hα hSL hmem hKL eK heK hTK hTN hTcard
  have hy' : eK ⟨y, hyK⟩ ∈ utri F := by
    rw [heK ⟨y, hyK⟩]
    exact (hmem ⟨y, hKL hyK⟩).mp hyS
  have hy'1 : eK ⟨y, hyK⟩ ≠ 1 := by
    intro h1
    apply hyQ
    rw [← hker ⟨y, hKL hyK⟩, ← heK ⟨y, hyK⟩, h1]
  obtain ⟨u, w, hu, hAconj, hbruhat, hinvT, hcube⟩ := exists_weyl_core A hA_le hAcard hy' hy'1
  let wK : ↥K := eK.symm (u⁻¹ * w * u)
  have heKwK : eK wK = u⁻¹ * w * u := eK.apply_symm_apply _
  let φ : ↥K →* SL(2, F) := (MulAut.conj u).toMonoidHom.comp eK.toMonoidHom
  have hφ_apply : ∀ k : ↥K, φ k = u * eK k * u⁻¹ := by
    intro k
    simp [φ, MulAut.conj_apply]
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have h1 : u * eK a * u⁻¹ = u * eK b * u⁻¹ := by
      rw [← hφ_apply a, ← hφ_apply b]
      exact hab
    exact eK.injective (mul_left_cancel (mul_right_cancel h1))
  have hφw : φ wK = w := by
    rw [hφ_apply, heKwK]
    group
  have hφtorus : ∀ t (ht : t ∈ T), φ ⟨t, hTK ht⟩ ∈ torus F := by
    intro t ht
    have h1 : eK ⟨t, hTK ht⟩ ∈ A :=
      Subgroup.mem_map_of_mem eK.toMonoidHom
        (show (⟨t, hTK ht⟩ : ↥K) ∈ T.subgroupOf K from ht)
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom h1
    rw [hAconj] at h2
    rw [hφ_apply]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2
  refine ⟨(wK : G), wK.2, ?_, ?_, ?_⟩
  · intro t ht
    have htK : t ∈ K := hTK ht
    have hsub : wK * ⟨t, htK⟩ * wK⁻¹ = ⟨t, htK⟩⁻¹ := by
      have hinv := hinvT (φ ⟨t, htK⟩) (hφtorus t ht)
      apply hφ_inj
      simp only [map_mul, map_inv, hφw]
      exact hinv
    simpa using congrArg Subtype.val hsub
  · refine closure_eq_of_complement α hα hSL hmem hKL eK heK wK ?_
    obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := hbruhat
    have hb' : (b₁ * u) * eK wK * (u⁻¹ * b₂) = wElt := by
      rw [heKwK]
      calc (b₁ * u) * (u⁻¹ * w * u) * (u⁻¹ * b₂) = b₁ * w * b₂ := by group
        _ = wElt := hb
    exact ⟨b₁ * u, Subgroup.mul_mem _ hb₁ (utri_le_borel hu),
      u⁻¹ * b₂, Subgroup.mul_mem _ (Subgroup.inv_mem _ (utri_le_borel hu)) hb₂, hb'⟩
  · have hkwy : φ ⟨(wK : G) * y, K.mul_mem wK.2 hyK⟩ =
        w * (u * eK ⟨y, hyK⟩ * u⁻¹) := by
      have h1 : (⟨(wK : G) * y, K.mul_mem wK.2 hyK⟩ : ↥K) = wK * ⟨y, hyK⟩ := Subtype.ext rfl
      rw [h1, map_mul, hφw, hφ_apply]
    have hφ3 : φ (⟨(wK : G) * y, K.mul_mem wK.2 hyK⟩ ^ 3) = 1 := by
      rw [map_pow, hkwy, hcube]
    have hkwy3 : (⟨(wK : G) * y, K.mul_mem wK.2 hyK⟩ : ↥K) ^ 3 = 1 := by
      apply hφ_inj
      rw [hφ3, map_one]
    simpa using congrArg Subtype.val hkwy3

end CFSG.Quasithin.F112R.St84

end
