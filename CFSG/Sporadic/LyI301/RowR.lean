module

public import CFSG.Sporadic.LyI301.Inputs
public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Monster.Existence.TwoB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Recognition.LyonsAS4Local
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.Sporadic.LyI301

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.LyonsSims CFSG.Certificates

@[expose] def lyC : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0, 1, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0]]

theorem lyU_rel : ExtraspecialNF.Rel (1 : Perm (Fin 11)) lyU 0 where
  z_sq := mul_one 1
  z_comm := fun i => by rw [one_mul, mul_one]
  q_sq := by decide +kernel
  comm := fun i j => by
    rw [Pi.zero_apply, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
    revert i j
    decide +kernel

theorem lyMon_mul (v w : Fin 4 → ZMod 2) :
    ExtraspecialNF.mon lyU v * ExtraspecialNF.mon lyU w = ExtraspecialNF.mon lyU (v + w) := by
  rw [ExtraspecialNF.mon_mul_mon lyU_rel, one_pow, one_mul]

@[expose] def lyVS : Subgroup (Perm (Fin 11)) where
  carrier := {π | ∃ v : Fin 4 → ZMod 2, ExtraspecialNF.mon lyU v = π}
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, (lyMon_mul v w).symm⟩
  one_mem' := ⟨0, ExtraspecialNF.mon_zero_vec lyU⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    refine ⟨v, (eq_inv_of_mul_eq_one_left ?_)⟩
    rw [lyMon_mul, show v + v = 0 by ext i; exact CharTwo.add_self_eq_zero (v i),
      ExtraspecialNF.mon_zero_vec]

private def vIdx (v : Fin 4 → ZMod 2) : Fin 16 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val, by
    have h0 := (v 0).val_lt; have h1 := (v 1).val_lt; have h2 := (v 2).val_lt
    have h3 := (v 3).val_lt; omega⟩

private theorem mon_eq_get : ∀ v : Fin 4 → ZMod 2,
    ExtraspecialNF.mon lyU v = lyV.get ⟨(vIdx v).val, by simp [lyV]⟩ := by
  decide +kernel

private theorem get_eq_mon : ∀ k : Fin 16, ∃ v : Fin 4 → ZMod 2,
    ExtraspecialNF.mon lyU v = lyV.get ⟨k.val, by simp [lyV]⟩ := by
  decide +kernel

theorem mem_lyVS_iff {π : Perm (Fin 11)} : π ∈ lyVS ↔ π ∈ lyV := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [mon_eq_get v]
    exact List.get_mem _ _
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
    obtain ⟨v, hv⟩ := get_eq_mon ⟨k, by simpa [lyV] using hk⟩
    exact ⟨v, hv⟩

theorem conj_mem_lyVS {π : Perm (Fin 11)} (h : ∀ i, π * lyU i * π⁻¹ ∈ lyVS)
    {σ : Perm (Fin 11)} (hσ : σ ∈ lyVS) : π * σ * π⁻¹ ∈ lyVS := by
  obtain ⟨v, rfl⟩ := hσ
  have e : π * ExtraspecialNF.mon lyU v * π⁻¹ = MulAut.conj π (ExtraspecialNF.mon lyU v) :=
    (MulAut.conj_apply _ _).symm
  rw [e, ExtraspecialNF.mon, map_list_prod]
  refine lyVS.list_prod_mem fun a ha => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hb
  rw [map_pow, MulAut.conj_apply]
  exact pow_mem (h i) _

theorem comm_lyVS {π : Perm (Fin 11)} (h : ∀ i, lyU i * π = π * lyU i) {σ : Perm (Fin 11)}
    (hσ : σ ∈ lyVS) : σ * π = π * σ := by
  obtain ⟨v, rfl⟩ := hσ
  refine (Commute.list_prod_left _ _ fun a ha => ?_).eq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact Commute.pow_left (h i) _

theorem lyU_mem (i : Fin 4) : lyU i ∈ lyVS :=
  ⟨Pi.single i 1, ExtraspecialNF.mon_single lyU i⟩

theorem lyMon_injective : Function.Injective (ExtraspecialNF.mon lyU) := by
  intro v w h
  have h' : lyV.get ⟨(vIdx v).val, by simp [lyV]⟩ = lyV.get ⟨(vIdx w).val, by simp [lyV]⟩ := by
    rw [← mon_eq_get, ← mon_eq_get, h]
  revert v w
  decide +kernel

theorem sign_lyU : ∀ i : Fin 4, sign (lyU i) = 1 := by decide

theorem cycleType_lyU (i : Fin 4) : (lyU i).cycleType = {2, 2, 2, 2} := by
  refine cycleType_type2222_of_card_11 ?_ ?_ <;> revert i <;> decide +kernel

theorem cycleType_lyU_mul_of_one {i j : Fin 4} (h : lyC i j = 1) :
    (lyU i * lyU j).cycleType = {2, 2} := by
  refine cycleType_type22_of_card_11 ?_ ?_ <;> revert i j <;> decide +kernel

theorem cycleType_lyU_mul_of_zero {i j : Fin 4} (hij : i ≠ j) (h : lyC i j = 0) :
    (lyU i * lyU j).cycleType = {2, 2, 2, 2} := by
  refine cycleType_type2222_of_card_11 ?_ ?_ <;> revert i j <;> decide +kernel

theorem lyC_nondegenerate : ExtraspecialNF.Nondegenerate lyC := by decide

theorem lyC_diag : ∀ i : Fin 4, lyC i i = 0 := by decide

variable {G : Type} [Group G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}

@[expose] def lyR (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)) : Subgroup G :=
  (lyVS.comap ρ).map (centralizer ({t} : Set G)).subtype

theorem mem_lyR {g : G} :
    g ∈ lyR ρ ↔ ∃ h : ↥(centralizer ({t} : Set G)), ρ h ∈ lyVS ∧ (h : G) = g := by
  simp only [lyR, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]

theorem lyR_le_centralizer : lyR ρ ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

private theorem mul_comm_of_sq {E : Type*} [Group E] {a b z : E} (hz : ∀ x, x * z = z * x)
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 2 = z) : a * b = b * a * z := by
  rw [← hab, pow_two]
  symm
  calc b * a * (a * b * (a * b)) = b * (a * a) * b * (a * b) := by group
    _ = a * b := by rw [ha, mul_one, hb, one_mul]

abbrev lyZ (t : G) : ↥(centralizer ({t} : Set G)) := ⟨t, self_mem_centralizer_singleton t⟩

theorem rho_lyZ (D : LyData G t ρ) : ρ (lyZ t) = 1 := D.cover.rho_z

theorem orderOf_lyZ (D : LyData G t ρ) : orderOf (lyZ t) = 2 := D.cover.orderOf_z

@[expose] def lyQ (D : LyData G t ρ) (i : Fin 4) : ↥(centralizer ({t} : Set G)) :=
  (D.cover.exists_lift (sign_lyU i)).choose

theorem rho_lyQ (D : LyData G t ρ) (i : Fin 4) : ρ (lyQ D i) = lyU i :=
  (D.cover.exists_lift (sign_lyU i)).choose_spec

theorem lyRel (D : LyData G t ρ) : ExtraspecialNF.Rel (lyZ t) (lyQ D) lyC where
  z_sq := D.cover.z_mul_z
  z_comm := fun i => (D.cover.mul_z_comm (lyQ D i)).symm
  q_sq := fun i => by
    have h := D.cover.sq_eq_one_of_type2222_lift (x := lyQ D i)
      (by rw [rho_lyQ D i]; exact cycleType_lyU i)
    rwa [pow_two] at h
  comm := fun i j => by
    have hsq : ∀ k, lyQ D k * lyQ D k = 1 := fun k => by
      have h := D.cover.sq_eq_one_of_type2222_lift (x := lyQ D k)
        (by rw [rho_lyQ D k]; exact cycleType_lyU k)
      rwa [pow_two] at h
    by_cases hij : i = j
    · subst hij
      rw [lyC_diag i, ZMod.val_zero, pow_zero, mul_one]
    · rcases ExtraspecialNF.zmod_two_cases (lyC i j) with h0 | h1
      · rw [h0, ZMod.val_zero, pow_zero, mul_one]
        have h := D.cover.sq_eq_one_of_type2222_lift (x := lyQ D i * lyQ D j)
          (by rw [map_mul, rho_lyQ D i, rho_lyQ D j]; exact cycleType_lyU_mul_of_zero hij h0)
        have h' := mul_comm_of_sq (fun x => (mul_one x).trans (one_mul x).symm) (hsq i) (hsq j) h
        rwa [mul_one] at h'
      · rw [h1, ExtraspecialNF.val_one_two, pow_one]
        exact mul_comm_of_sq D.cover.mul_z_comm (hsq i) (hsq j)
          (D.cover.sq_eq_z_of_type22 (x := lyQ D i * lyQ D j)
            (by rw [map_mul, rho_lyQ D i, rho_lyQ D j]; exact cycleType_lyU_mul_of_one h1))

theorem rho_nf (D : LyData G t ρ) (s : ZMod 2) (v : Fin 4 → ZMod 2) :
    ρ (ExtraspecialNF.nf (lyZ t) (lyQ D) s v) = ExtraspecialNF.mon lyU v := by
  unfold ExtraspecialNF.nf ExtraspecialNF.mon
  rw [map_mul, map_pow, rho_lyZ D, one_pow, one_mul, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply, map_pow, rho_lyQ]

theorem lyNf_injective (D : LyData G t ρ) :
    Function.Injective (Function.uncurry (ExtraspecialNF.nf (lyZ t) (lyQ D))) := by
  rintro ⟨s, v⟩ ⟨s', v'⟩ h
  simp only [Function.uncurry_apply_pair] at h
  have hv : v = v' := lyMon_injective (by rw [← rho_nf D s v, ← rho_nf D s' v', h])
  subst hv
  have hs : (lyZ t) ^ s.val = (lyZ t) ^ s'.val := by
    unfold ExtraspecialNF.nf at h
    exact mul_right_cancel h
  have hz : (lyZ t : ↥(centralizer ({t} : Set G))) ≠ 1 := D.cover.ne_one
  rcases ExtraspecialNF.zmod_two_cases s with rfl | rfl <;>
    rcases ExtraspecialNF.zmod_two_cases s' with rfl | rfl
  · rfl
  · rw [ZMod.val_zero, ExtraspecialNF.val_one_two, pow_zero, pow_one] at hs
    exact absurd hs.symm hz
  · rw [ZMod.val_zero, ExtraspecialNF.val_one_two, pow_zero, pow_one] at hs
    exact absurd hs hz
  · rfl

theorem comap_lyVS_eq_closure (D : LyData G t ρ) :
    lyVS.comap ρ = Subgroup.closure (insert (lyZ t) (Set.range (lyQ D))) := by
  apply le_antisymm
  · intro h hh
    obtain ⟨v, hv⟩ := hh
    have e : ρ (ExtraspecialNF.nf (lyZ t) (lyQ D) 0 v) = ρ h := by rw [rho_nf, hv]
    rcases D.cover.eq_or_eq_mul_z e with h1 | h1
    · rw [h1]
      exact ExtraspecialNF.nf_mem_closure _ _ 0 v
    · rw [h1]
      exact mul_mem (ExtraspecialNF.nf_mem_closure _ _ 0 v) (ExtraspecialNF.z_mem_closure _ _)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · show ρ (lyZ t) ∈ lyVS
      rw [rho_lyZ D]
      exact lyVS.one_mem
    · show ρ (lyQ D i) ∈ lyVS
      rw [rho_lyQ]
      exact lyU_mem i

theorem comap_lyVS_extraspecial (D : LyData G t ρ) : IsExtraspecialPGroup 2 ↥(lyVS.comap ρ) := by
  rw [comap_lyVS_eq_closure D]
  exact ExtraspecialNF.isExtraspecialPGroup (lyRel D) (lyNf_injective D) lyC_nondegenerate
    (by norm_num)

theorem card_comap_lyVS (D : LyData G t ρ) : Nat.card ↥(lyVS.comap ρ) = 32 := by
  rw [comap_lyVS_eq_closure D, ExtraspecialNF.card_closure (lyRel D) (lyNf_injective D)]
  rfl

theorem center_comap_lyVS (D : LyData G t ρ) {h : ↥(centralizer ({t} : Set G))}
    (hh : h ∈ lyVS.comap ρ) (hc : ∀ r ∈ lyVS.comap ρ, r * h = h * r) : h = 1 ∨ h = lyZ t := by
  have hcl := comap_lyVS_eq_closure D
  rw [hcl] at hh hc
  have hmem : (⟨h, hh⟩ : ↥(Subgroup.closure (insert (lyZ t) (Set.range (lyQ D))))) ∈
      Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro r
    exact Subtype.ext (hc r r.2)
  rw [ExtraspecialNF.center_eq (lyRel D) (lyNf_injective D) lyC_nondegenerate,
    Subgroup.mem_subgroupOf] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk' : (lyZ t) ^ k = h := hk
  rw [← zpow_mod_orderOf, orderOf_lyZ D] at hk'
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    have := Int.emod_two_eq_zero_or_one k
    simpa using this
  rcases h2 with h2 | h2
  · left
    rw [← hk', h2, zpow_zero]
  · right
    rw [← hk', h2, zpow_one]

@[expose] def lyREquiv : ↥(lyVS.comap ρ) ≃* ↥(lyR ρ) :=
  (lyVS.comap ρ).equivMapOfInjective _ (centralizer ({t} : Set G)).subtype_injective

theorem lyR_extraspecial (D : LyData G t ρ) : IsExtraspecialPGroup 2 ↥(lyR ρ) :=
  CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv lyREquiv (comap_lyVS_extraspecial D)

theorem card_lyR (D : LyData G t ρ) : Nat.card ↥(lyR ρ) = 32 := by
  rw [← Nat.card_congr (lyREquiv (ρ := ρ)).toEquiv, card_comap_lyVS D]

theorem t_mem_lyR (D : LyData G t ρ) : t ∈ lyR ρ := by
  refine mem_lyR.2 ⟨lyZ t, ?_, rfl⟩
  rw [rho_lyZ D]
  exact lyVS.one_mem

theorem eq_one_or_eq_t_of_central (D : LyData G t ρ) {g : G} (hg : g ∈ lyR ρ)
    (hc : ∀ r ∈ lyR ρ, r * g = g * r) : g = 1 ∨ g = t := by
  obtain ⟨h, hh, rfl⟩ := mem_lyR.1 hg
  have hc' : ∀ r ∈ lyVS.comap ρ, r * h = h * r := by
    intro r hr
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hc _ (mem_lyR.2 ⟨r, hr, rfl⟩)
  rcases center_comap_lyVS D hh hc' with h1 | h1
  · left
    rw [h1, Subgroup.coe_one]
  · right
    rw [h1]

theorem normalizer_lyR_le (D : LyData G t ρ) :
    Subgroup.normalizer (lyR ρ : Set G) ≤ centralizer ({t} : Set G) := by
  intro g hg
  have h1 : g * t * g⁻¹ ∈ lyR ρ := (Subgroup.mem_normalizer_iff.1 hg t).1 (t_mem_lyR D)
  have hc : ∀ r ∈ lyR ρ, r * (g * t * g⁻¹) = g * t * g⁻¹ * r := by
    intro r hr
    have hr' : g⁻¹ * r * g ∈ lyR ρ := by
      have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) r).1 hr
      rwa [inv_inv] at h
    have hrt : (g⁻¹ * r * g) * t = t * (g⁻¹ * r * g) :=
      mem_centralizer_singleton_iff.1 (lyR_le_centralizer hr')
    calc r * (g * t * g⁻¹) = g * ((g⁻¹ * r * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * r * g)) * g⁻¹ := by rw [hrt]
      _ = g * t * g⁻¹ * r := by group
  rcases eq_one_or_eq_t_of_central D h1 hc with h | h
  · exfalso
    have ht : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact D.cover.ne_one (Subtype.ext ht)
  · rw [mem_centralizer_singleton_iff]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h]

theorem mem_normalizer_lyR {x : ↥(centralizer ({t} : Set G))}
    (hx : ∀ π ∈ lyVS, ρ x * π * (ρ x)⁻¹ ∈ lyVS) (hx' : ∀ π ∈ lyVS, (ρ x)⁻¹ * π * ρ x ∈ lyVS) :
    (x : G) ∈ Subgroup.normalizer (lyR ρ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    obtain ⟨h, hh, rfl⟩ := mem_lyR.1 hr
    refine mem_lyR.2 ⟨x * h * x⁻¹, ?_, by simp⟩
    rw [map_mul, map_mul, map_inv]
    exact hx _ hh
  · intro hr
    obtain ⟨h, hh, he⟩ := mem_lyR.1 hr
    refine mem_lyR.2 ⟨x⁻¹ * h * x, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact hx' _ hh
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he]
      group

theorem le_centralizer_lyR (D : LyData G t ρ) {x : ↥(centralizer ({t} : Set G))} (hx3 : x ^ 3 = 1)
    (hx : ∀ π ∈ lyVS, π * ρ x = ρ x * π) :
    lyR ρ ≤ centralizer ({(x : G)} : Set G) := by
  intro r hr
  obtain ⟨h, hh, rfl⟩ := mem_lyR.1 hr
  have e := D.cover.commute_of_rho_commute_pow_three hx3 (g := h) (hx _ hh)
  rw [mem_centralizer_singleton_iff]
  have e' := congrArg Subtype.val e
  rwa [Subgroup.coe_mul, Subgroup.coe_mul] at e'

end CFSG.Sporadic.LyI301
