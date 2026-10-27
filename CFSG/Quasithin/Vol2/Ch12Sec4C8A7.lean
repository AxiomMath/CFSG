module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace A7I

open Equiv

@[expose] def s₁ : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

@[expose] def s₂ : Perm (Fin 7) := swap 0 2 * swap 4 5

@[expose] def D : Fin 8 → Perm (Fin 7) :=
  ![1, swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3,
    swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5, swap 0 2 * swap 4 5, swap 0 1 * swap 2 3,
    swap 1 3 * swap 4 5, swap 0 3 * swap 1 2]

@[expose] def E : Fin 4 → Perm (Fin 7) :=
  ![1, swap 0 2 * swap 1 3, swap 4 5, swap 0 2 * swap 1 3 * swap 4 5]

@[expose] def T3 : Fin 4 → Perm (Fin 7) :=
  ![swap 0 1 * swap 1 4, swap 4 5 * swap 5 6, swap 0 1 * swap 1 2,
    swap 0 1 * swap 1 4 * swap 2 3 * swap 3 5]

theorem D_mul : ∀ i j : Fin 8, ∃ k : Fin 8, D i * D j = D k := by decide

theorem D_inv : ∀ i : Fin 8, ∃ k : Fin 8, (D i)⁻¹ = D k := by decide

theorem D_inj : Function.Injective D := by decide

theorem D_sign : ∀ i : Fin 8, Perm.sign (D i) = 1 := by decide

theorem T3_sign : ∀ i : Fin 4, Perm.sign (T3 i) = 1 := by decide

theorem T3_cube : ∀ i : Fin 4, T3 i ^ 3 = 1 := by decide

theorem T3_comm : ∀ i : Fin 4, T3 i * E i = E i * T3 i := by decide

theorem T3_move : ∀ i j : Fin 4, E j ≠ 1 → E j * E i ≠ 1 → T3 i * E j ≠ E j * T3 i := by
  decide

theorem cent_aux : ∀ i : Fin 7, ∀ σ : Perm (Fin 6),
    Perm.decomposeFin.symm (i, σ) * s₁ = s₁ * Perm.decomposeFin.symm (i, σ) →
    Perm.decomposeFin.symm (i, σ) * s₂ = s₂ * Perm.decomposeFin.symm (i, σ) →
    ∃ j : Fin 4, Perm.decomposeFin.symm (i, σ) = E j := by
  decide +kernel

theorem cent (τ : Perm (Fin 7)) (h₁ : τ * s₁ = s₁ * τ) (h₂ : τ * s₂ = s₂ * τ) :
    ∃ j : Fin 4, τ = E j := by
  obtain ⟨⟨i, σ⟩, rfl⟩ := Perm.decomposeFin.symm.surjective τ
  exact cent_aux i σ h₁ h₂

@[expose] def P₀ : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {x | ∃ i, (x : Perm (Fin 7)) = D i}
  mul_mem' := by
    rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := D_mul i j
    exact ⟨k, by rw [Subgroup.coe_mul, hi, hj, hk]⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro x ⟨i, hi⟩
    obtain ⟨k, hk⟩ := D_inv i
    exact ⟨k, by rw [Subgroup.coe_inv, hi, hk]⟩

theorem card_P₀ : Nat.card P₀ = 8 := by
  have hD : ∀ i, D i ∈ alternatingGroup (Fin 7) := fun i => (Perm.mem_alternatingGroup).2 (D_sign i)
  let f : Fin 8 → P₀ := fun i => ⟨⟨D i, hD i⟩, i, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => D_inj (congrArg (fun x : P₀ => ((x : alternatingGroup (Fin 7)) :
      Perm (Fin 7))) h), ?_⟩
    rintro ⟨x, i, hi⟩
    exact ⟨i, Subtype.ext (Subtype.ext hi.symm)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_alt : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isPGroup_P₀ : IsPGroup 2 P₀ := IsPGroup.of_card (n := 3) (by rw [card_P₀]; norm_num)

theorem not_dvd_index_P₀ : ¬ 2 ∣ P₀.index := by
  have h := P₀.card_mul_index
  rw [card_P₀, card_alt] at h
  have h315 : P₀.index = 315 := by omega
  rw [h315]
  decide

theorem s₁_mem : (⟨s₁, (Perm.mem_alternatingGroup).2 (D_sign 1)⟩ : alternatingGroup (Fin 7)) ∈ P₀ :=
  ⟨1, rfl⟩

theorem s₂_mem : (⟨s₂, (Perm.mem_alternatingGroup).2 (D_sign 4)⟩ : alternatingGroup (Fin 7)) ∈ P₀ :=
  ⟨4, rfl⟩

section Action

variable {Y : Type} [Group Y] {K : Subgroup Y}

theorem exists_perm (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7)) {g : Y}
    (hg : g ∈ Subgroup.normalizer (K : Set Y)) :
    ∃ σ : Perm (Fin 7), ∀ x : ↥K,
      ((φ (K.normalizerMonoidHom ⟨g, hg⟩ x : ↥K ⧸ Subgroup.center ↥K) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        σ * (φ (x : ↥K ⧸ Subgroup.center ↥K) : Perm (Fin 7)) * σ⁻¹ := by
  set e := K.normalizerMonoidHom ⟨g, hg⟩ with he_def
  have he : (Subgroup.center ↥K).map (e : ↥K →* ↥K) = Subgroup.center ↥K :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance e
  set c := QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) e he with hc
  set α : MulAut (alternatingGroup (Fin 7)) := (φ.symm.trans c).trans φ with hα
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 α
  refine ⟨σ, fun x => ?_⟩
  have h1 : φ (e x : ↥K ⧸ Subgroup.center ↥K) = α (φ (x : ↥K ⧸ Subgroup.center ↥K)) := by
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hc,
      QuotientGroup.congr_mk]
  rw [h1, ← hσ]
  rfl

theorem mem_centralizer_of_mk_eq (hperf : commutator ↥K = ⊤) {g : Y}
    (hg : g ∈ Subgroup.normalizer (K : Set Y))
    (h : ∀ x : ↥K, (K.normalizerMonoidHom ⟨g, hg⟩ x : ↥K ⧸ Subgroup.center ↥K) =
      (x : ↥K ⧸ Subgroup.center ↥K)) :
    g ∈ Subgroup.centralizer (K : Set Y) := by
  set e := K.normalizerMonoidHom ⟨g, hg⟩ with he_def
  have hc : ∀ x : ↥K, ∃ c ∈ Subgroup.center ↥K, e x = x * c := by
    intro x
    have h1 : x⁻¹ * e x ∈ Subgroup.center ↥K := QuotientGroup.eq.1 (h x).symm
    exact ⟨x⁻¹ * e x, h1, by group⟩
  have hfix : commutator ↥K ≤ MonoidHom.eqLocus (e : ↥K →* ↥K) (MonoidHom.id ↥K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨c, hcZ, hcx⟩ := hc x
    obtain ⟨d, hdZ, hdy⟩ := hc y
    show e ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement, hcx, hdy]
    have hcy : c * y = y * c := ((Subgroup.mem_center_iff.1 hcZ) y).symm
    have hcd : c * d = d * c := ((Subgroup.mem_center_iff.1 hcZ) d).symm
    have hdx : d * x⁻¹ = x⁻¹ * d := ((Subgroup.mem_center_iff.1 hdZ) x⁻¹).symm
    calc ⁅x * c, y * d⁆ = x * (c * y) * d * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * (y * c) * d * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcy]
      _ = x * y * (c * d) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by group
      _ = x * y * (d * c) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcd]
      _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hdx]
      _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group
  rw [hperf] at hfix
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h2 : e ⟨k, hk⟩ = ⟨k, hk⟩ := hfix (Subgroup.mem_top _)
  have h3 : g * k * g⁻¹ = k := congrArg Subtype.val h2
  calc k * g = g * k * g⁻¹ * g := by rw [h3]
    _ = g * k := by group

end Action

section Core

variable {Y : Type} [Group Y] {K S : Subgroup Y}

theorem image_mul (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7)) (x y : ↥K) :
    ((φ ((x * y : ↥K) : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((φ (x : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
        ((φ (y : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
  rw [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul]

theorem mk_eq_of_image_eq (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7)) {x y : ↥K}
    (h : ((φ (x : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((φ (y : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7))) :
    (x : ↥K ⧸ Subgroup.center ↥K) = (y : ↥K ⧸ Subgroup.center ↥K) :=
  φ.injective (Subtype.ext h)

theorem core (hperf : commutator ↥K = ⊤)
    (φ : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7))
    (h₁ : ∃ t : ↥K, (t : Y) ∈ S ∧
      ((φ (t : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = s₁)
    (h₂ : ∃ t : ↥K, (t : Y) ∈ S ∧
      ((φ (t : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = s₂)
    {z u : Y} (hzK : z ∈ Subgroup.normalizer (K : Set Y))
    (hzS : z ∈ Subgroup.centralizer (S : Set Y)) (hz2 : z ^ 2 = 1)
    (huK : u ∈ Subgroup.normalizer (K : Set Y)) (huS : u ∈ Subgroup.centralizer (S : Set Y))
    (hu : u ∉ Subgroup.centralizer (K : Set Y))
    (huz : u * z ∉ Subgroup.centralizer (K : Set Y)) :
    ∃ k ∈ K, k * z = z * k ∧ k * u ≠ u * k := by
  classical
  obtain ⟨σz, hσz⟩ := exists_perm φ hzK
  obtain ⟨σu, hσu⟩ := exists_perm φ huK
  have hfixS : ∀ {g : Y} (hg : g ∈ Subgroup.normalizer (K : Set Y)),
      g ∈ Subgroup.centralizer (S : Set Y) → ∀ t : ↥K, (t : Y) ∈ S →
        K.normalizerMonoidHom ⟨g, hg⟩ t = t := by
    intro g hg hgS t ht
    apply Subtype.ext
    show g * t * g⁻¹ = t
    have h := Subgroup.mem_centralizer_iff.1 hgS t ht
    calc g * (t : Y) * g⁻¹ = t * g * g⁻¹ := by rw [h]
      _ = t := by group
  have hcomm : ∀ {g : Y} (hg : g ∈ Subgroup.normalizer (K : Set Y)) (σ : Perm (Fin 7)),
      (∀ x : ↥K, ((φ (K.normalizerMonoidHom ⟨g, hg⟩ x : ↥K ⧸ Subgroup.center ↥K) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) =
          σ * (φ (x : ↥K ⧸ Subgroup.center ↥K) : Perm (Fin 7)) * σ⁻¹) →
      g ∈ Subgroup.centralizer (S : Set Y) → ∃ j : Fin 4, σ = E j := by
    intro g hg σ hσ hgS
    obtain ⟨t₁, ht₁S, ht₁⟩ := h₁
    obtain ⟨t₂, ht₂S, ht₂⟩ := h₂
    have e1 := hσ t₁
    have e2 := hσ t₂
    rw [hfixS hg hgS t₁ ht₁S, ht₁] at e1
    rw [hfixS hg hgS t₂ ht₂S, ht₂] at e2
    refine cent σ ?_ ?_
    · calc σ * s₁ = σ * s₁ * σ⁻¹ * σ := by group
        _ = s₁ * σ := by rw [← e1]
    · calc σ * s₂ = σ * s₂ * σ⁻¹ * σ := by group
        _ = s₂ * σ := by rw [← e2]
  obtain ⟨i, rfl⟩ := hcomm hzK σz hσz hzS
  obtain ⟨j, rfl⟩ := hcomm huK σu hσu huS
  have hj : E j ≠ 1 := by
    intro hj1
    apply hu
    refine mem_centralizer_of_mk_eq hperf huK fun x => mk_eq_of_image_eq φ ?_
    rw [hσu x, hj1]
    group
  have hji : E j * E i ≠ 1 := by
    intro h1
    apply huz
    have huzK : u * z ∈ Subgroup.normalizer (K : Set Y) := Subgroup.mul_mem _ huK hzK
    refine mem_centralizer_of_mk_eq hperf huzK fun x => mk_eq_of_image_eq φ ?_
    have hx : K.normalizerMonoidHom ⟨u * z, huzK⟩ x =
        K.normalizerMonoidHom ⟨u, huK⟩ (K.normalizerMonoidHom ⟨z, hzK⟩ x) := by
      apply Subtype.ext
      show u * z * x * (u * z)⁻¹ = u * (z * x * z⁻¹) * u⁻¹
      group
    rw [hx, hσu, hσz]
    calc E j * (E i * (φ (x : ↥K ⧸ Subgroup.center ↥K) : Perm (Fin 7)) * (E i)⁻¹) * (E j)⁻¹
        = (E j * E i) * (φ (x : ↥K ⧸ Subgroup.center ↥K) : Perm (Fin 7)) * (E j * E i)⁻¹ := by
          group
      _ = (φ (x : ↥K ⧸ Subgroup.center ↥K) : Perm (Fin 7)) := by rw [h1]; group
  set y : alternatingGroup (Fin 7) := ⟨T3 i, (Perm.mem_alternatingGroup).2 (T3_sign i)⟩ with hy
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm y)
  have hxy : ((φ (x : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      T3 i := by
    rw [hx, MulEquiv.apply_symm_apply]
  set ez := K.normalizerMonoidHom ⟨z, hzK⟩ with hez
  set eu := K.normalizerMonoidHom ⟨u, huK⟩ with heu
  have hzx : ((φ (ez x : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) = T3 i := by
    rw [hσz, hxy, ← T3_comm i]
    group
  have hc : x⁻¹ * ez x ∈ Subgroup.center ↥K :=
    QuotientGroup.eq.1 (mk_eq_of_image_eq φ (hxy.trans hzx.symm))
  set w : ↥K := x * ez x with hw
  have hezx : ((ez x : ↥K) : Y) = z * x * z⁻¹ := rfl
  have hxe : x * ez x = ez x * x := by
    have h1 : ez x = x * (x⁻¹ * ez x) := by group
    have h2 := (Subgroup.mem_center_iff.1 hc) x
    calc x * ez x = x * (x * (x⁻¹ * ez x)) := by rw [← h1]
      _ = x * ((x⁻¹ * ez x) * x) := by rw [h2]
      _ = ez x * x := by group
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hzi : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, hzz]
  have hwz : (w : Y) * z = z * w := by
    have h1 : ((x : Y) * (z * x * z⁻¹)) = (z * x * z⁻¹) * x := by
      have := congrArg Subtype.val hxe
      simpa [hezx] using this
    show (x : Y) * (z * x * z⁻¹) * z = z * ((x : Y) * (z * x * z⁻¹))
    calc (x : Y) * (z * x * z⁻¹) * z = (z * x * z⁻¹) * x * z := by rw [h1]
      _ = z * ((x : Y) * (z * x * z⁻¹)) := by rw [hzi]; group
  have hψw : ((φ (w : ↥K ⧸ Subgroup.center ↥K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      T3 i * T3 i := by
    rw [hw, image_mul, hxy, hzx]
  refine ⟨w, w.2, hwz, fun hwu => ?_⟩
  have hew : eu w = w := by
    apply Subtype.ext
    show u * (w : Y) * u⁻¹ = w
    calc u * (w : Y) * u⁻¹ = w * u * u⁻¹ := by rw [hwu]
      _ = w := by group
  have h1 := hσu w
  rw [hew, hψw] at h1
  apply T3_move i j hj hji
  have h4 : T3 i = (T3 i * T3 i) * (T3 i * T3 i) := by
    calc T3 i = T3 i * T3 i ^ 3 := by rw [T3_cube i, mul_one]
      _ = (T3 i * T3 i) * (T3 i * T3 i) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hc2 : (T3 i * T3 i) * E j = E j * (T3 i * T3 i) := by
    calc (T3 i * T3 i) * E j = E j * (T3 i * T3 i) * (E j)⁻¹ * E j := by rw [← h1]
      _ = E j * (T3 i * T3 i) := by group
  calc T3 i * E j = (T3 i * T3 i) * (T3 i * T3 i) * E j := by rw [← h4]
    _ = (T3 i * T3 i) * ((T3 i * T3 i) * E j) := by group
    _ = (T3 i * T3 i) * (E j * (T3 i * T3 i)) := by rw [hc2]
    _ = ((T3 i * T3 i) * E j) * (T3 i * T3 i) := by group
    _ = (E j * (T3 i * T3 i)) * (T3 i * T3 i) := by rw [hc2]
    _ = E j * ((T3 i * T3 i) * (T3 i * T3 i)) := by group
    _ = E j * T3 i := by rw [← h4]

end Core

end A7I

theorem a7Insp1248 : A7Insp1248 := by
  intro Y _ _ K S z u hKq hA7 hS hzK hzS hz2 huK huS _ hu huz
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨φ⟩, -⟩ := hA7
  have hS2 : IsPGroup 2 (S.subgroupOf K) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 ↥K := hS2.toSylow hS.2.2
  let f : ↥K →* alternatingGroup (Fin 7) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hf : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pb : Sylow 2 (alternatingGroup (Fin 7)) := P.mapSurjective hf
  let P0 : Sylow 2 (alternatingGroup (Fin 7)) := A7I.isPGroup_P₀.toSylow A7I.not_dvd_index_P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) Pb P0
  let φ' : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7) := φ.trans (MulAut.conj g)
  have hmem : ∀ t : alternatingGroup (Fin 7), t ∈ A7I.P₀ →
      ∃ s : ↥K, (s : Y) ∈ S ∧ φ' (s : ↥K ⧸ Subgroup.center ↥K) = t := by
    intro t ht
    have ht' : t ∈ ((g • Pb : Sylow 2 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [hg]
      exact ht
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ht'
    obtain ⟨y, hy, rfl⟩ := ht'
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, rfl⟩
  obtain ⟨t₁, ht₁S, ht₁⟩ := hmem _ A7I.s₁_mem
  obtain ⟨t₂, ht₂S, ht₂⟩ := hmem _ A7I.s₂_mem
  exact A7I.core hKq.1.commutator_eq_top φ' ⟨t₁, ht₁S, by rw [ht₁]⟩ ⟨t₂, ht₂S, by rw [ht₂]⟩
    hzK hzS hz2 huK huS hu huz

end CFSG.Quasithin.H13
