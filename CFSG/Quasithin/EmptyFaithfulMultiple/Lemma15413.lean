module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Quasithin Equiv

section Fusion

variable {G : Type*} [Group G]

private theorem conj_eq_of_forall_mul_self_mem {P : Subgroup G} {x z : G} (hx : x ∈ P)
    (hxz : x * x = z) (hsq : ∀ y ∈ P, y * y = 1 ∨ y * y = z) (hz : z ≠ 1) {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) : n⁻¹ * z * n = z := by
  have hy : n⁻¹ * x * n ∈ P := (Subgroup.mem_normalizer_iff''.mp hn x).mp hx
  have hyy : n⁻¹ * x * n * (n⁻¹ * x * n) = n⁻¹ * z * n := by
    rw [← hxz]
    group
  rcases hsq _ hy with h | h
  · rw [hyy] at h
    refine absurd ?_ hz
    calc z = n * (n⁻¹ * z * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rwa [hyy] at h

private theorem eq_one_of_conj_eq_mul [Finite G] {P : Subgroup G} (hP : ¬ 2 ∣ P.index) {u z n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) (hu : ∀ y ∈ P, u * y = y * u)
    (hzz : z * z = 1) (hnz : n⁻¹ * z * n = z) (hnu : n⁻¹ * u * n = u * z) : z = 1 := by
  set N := Subgroup.normalizer (P : Set G)
  set k := (P.subgroupOf N).index
  have hk : n ^ k ∈ P := by
    have := Subgroup.pow_index_mem (P.subgroupOf N) ⟨n, hn⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hkodd : ¬ 2 ∣ k := fun h =>
    hP (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  have hzpow : ∀ j : ℕ, n⁻¹ * z ^ j * n = z ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n⁻¹ * z ^ (j + 1) * n = (n⁻¹ * z ^ j * n) * (n⁻¹ * z * n) := by group
        _ = z ^ (j + 1) := by rw [ih, hnz, pow_succ]
  have hpow : ∀ j : ℕ, (n ^ j)⁻¹ * u * n ^ j = u * z ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (n ^ (j + 1))⁻¹ * u * n ^ (j + 1) = n⁻¹ * ((n ^ j)⁻¹ * u * n ^ j) * n := by group
        _ = (n⁻¹ * u * n) * (n⁻¹ * z ^ j * n) := by rw [ih]; group
        _ = u * z ^ (j + 1) := by rw [hnu, hzpow, pow_succ', mul_assoc]
  have hfix : (n ^ k)⁻¹ * u * n ^ k = u := by
    rw [mul_assoc, hu _ hk, inv_mul_cancel_left]
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  have hzk : z ^ k = z := by
    rw [hm, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
  have := (hpow k).symm.trans hfix
  rwa [hzk, mul_eq_left] at this

private theorem exists_mem_normalizer_conj_eq [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) {u v : G} (hu : ∀ y ∈ P, u * y = y * u)
    (hv : ∀ y ∈ P, v * y = y * v) (huv : IsConj u v) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), n⁻¹ * u * n = v := by
  let S : Sylow 2 G := hP.toSylow hPidx
  have hWC : IsWeaklyClosedIn P (S : Subgroup G) := by
    intro g hg
    refine Subgroup.eq_of_le_of_card_ge hg ?_
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  obtain ⟨c, hc⟩ := isConj_iff.mp huv
  exact burnside_fusion_lemma_centralizer S (W := P) le_rfl hWC
    (Subgroup.mem_centralizer_iff.mpr fun y hy => (hu y hy).symm)
    (Subgroup.mem_centralizer_iff.mpr fun y hy => (hv y hy).symm) (g := c⁻¹)
    (by rw [inv_inv]; exact hc)

private theorem isConj_of_conj_eq {u r h : G} (hh : h⁻¹ * u * h = r) : IsConj u r :=
  isConj_iff.mpr ⟨h⁻¹, by rw [inv_inv]; exact hh⟩

private theorem mul_comm_of_forall_mul_self_eq_one (h : ∀ w : G, w * w = 1) (b c : G) :
    b * c = c * b := by
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b)
  have hc : c⁻¹ = c := inv_eq_of_mul_eq_one_right (h c)
  calc b * c = (b * c)⁻¹ := (inv_eq_of_mul_eq_one_right (h (b * c))).symm
    _ = c * b := by rw [mul_inv_rev, hb, hc]

private theorem false_of_forall_isConj_of_mem [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {P R : Subgroup G} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hRP : R ≤ P) (hRidx : R.relIndex P = 2) {x z a t : G}
    (hx : x ∈ P) (hxz : x * x = z) (hsq : ∀ y ∈ P, y * y = 1 ∨ y * y = z)
    (hz : ∀ y ∈ P, z * y = y * z) (ha : ∀ y ∈ P, a * y = y * a) (hz1 : z ≠ 1) (ha1 : a ≠ 1)
    (haz : a ≠ z) (haa : a * a = 1)
    (hR : ∀ r ∈ R, r * r = 1 → r = 1 ∨ IsConj t r ∨ IsConj z r) : False := by
  have hzP : z ∈ P := hxz ▸ P.mul_mem hx hx
  have hzz : z * z = 1 := by
    rcases hsq z hzP with h | h
    · exact h
    · exact absurd (mul_eq_left.mp h) hz1
  have hfix : ∀ n ∈ Subgroup.normalizer (P : Set G), n⁻¹ * z * n = z := fun n hn =>
    conj_eq_of_forall_mul_self_mem hx hxz hsq hz1 hn
  have hazc : ∀ y ∈ P, a * z * y = y * (a * z) := fun y hy => by
    rw [mul_assoc, hz y hy, ← mul_assoc, ha y hy, mul_assoc]
  have h1 : ¬ IsConj z a := by
    intro h
    obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_conj_eq hP hPidx hz ha h
    exact haz (hnz.symm.trans (hfix n hn))
  have h2 : ¬ IsConj z (a * z) := by
    intro h
    obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_conj_eq hP hPidx hz hazc h
    rw [hfix n hn, eq_comm, mul_eq_right] at hnz
    exact ha1 hnz
  have h3 : ¬ IsConj a (a * z) := by
    intro h
    obtain ⟨n, hn, hna⟩ := exists_mem_normalizer_conj_eq hP hPidx ha hazc h
    exact hz1 (eq_one_of_conj_eq_mul hPidx hn ha hzz (hfix n hn) hna)
  obtain ⟨i, hi1, hii, hit, hiz⟩ :
      ∃ i : G, i ≠ 1 ∧ i * i = 1 ∧ ¬ IsConj t i ∧ ¬ IsConj z i := by
    by_cases hta : IsConj t a
    · refine ⟨a * z, fun h => haz ?_, ?_, fun h => h3 (hta.symm.trans h), h2⟩
      · calc a = a * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = z := by rw [h, one_mul]
      · calc a * z * (a * z) = a * a * (z * z) := by
              rw [mul_assoc, ← mul_assoc z, ← ha z hzP, mul_assoc, mul_assoc, ← mul_assoc a]
          _ = 1 := by rw [haa, hzz, one_mul]
    · exact ⟨a, ha1, haa, hta, h1⟩
  have hiR : ∀ g : G, g⁻¹ * i * g ∉ R := by
    intro g hg
    have hrr : g⁻¹ * i * g * (g⁻¹ * i * g) = 1 := by
      calc g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g := by group
        _ = 1 := by rw [hii]; group
    have hconj : IsConj (g⁻¹ * i * g) i := isConj_iff.mpr ⟨g, by group⟩
    rcases hR _ hg hrr with h | h | h
    · refine hi1 ?_
      calc i = g * (g⁻¹ * i * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exact hit (h.trans hconj)
    · exact hiz (h.trans hconj)
  have hio : orderOf i = 2 := orderOf_eq_prime (by rw [sq]; exact hii) hi1
  obtain ⟨N, hN, hsqN, hiN⟩ :=
    thompson_transfer_exists_normal (hP.toSylow hPidx) hRP hRidx hio hiR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · obtain ⟨b, c, hbc⟩ := hnonab
    refine hbc (mul_comm_of_forall_mul_self_eq_one (fun w => ?_) b c)
    have := hsqN w
    rwa [Subgroup.mem_bot, sq] at this
  · exact hiN (Subgroup.mem_top i)

end Fusion

section Model

private def InDihedral (σ : Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, (i.val / 2 = j.val / 2 ↔ (σ i).val / 2 = (σ j).val / 2)

private instance : DecidablePred InDihedral := fun σ => by unfold InDihedral; infer_instance

private def InDihedralOne (x : Multiplicative (ZMod 2) × Perm (Fin 4)) : Prop :=
  x.1 = 1 ∧ InDihedral x.2

private instance : DecidablePred InDihedralOne := fun x => by
  unfold InDihedralOne; infer_instance

private def sylowModel : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 4)) where
  carrier := {x | InDihedral x.2}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {_ y} hx hy i j => (hy i j).trans (hx (y.2 i) (y.2 j))
  inv_mem' := fun {x} hx i j => by
    have h := hx (x.2⁻¹ i) (x.2⁻¹ j)
    simp only [Perm.coe_inv, Equiv.apply_symm_apply] at h
    exact h.symm

private def dihedralModel : Subgroup (Multiplicative (ZMod 2) × Perm (Fin 4)) where
  carrier := {x | InDihedralOne x}
  one_mem' := ⟨rfl, fun _ _ => Iff.rfl⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨by simp [hx.1, hy.1], fun i j => (hy.2 i j).trans (hx.2 (y.2 i) (y.2 j))⟩
  inv_mem' := fun {x} hx => ⟨by rw [Prod.fst_inv, hx.1]; decide, fun i j => by
    have h := hx.2 (x.2⁻¹ i) (x.2⁻¹ j)
    simp only [Perm.coe_inv, Equiv.apply_symm_apply] at h
    exact h.symm⟩

private def zModel : Multiplicative (ZMod 2) × Perm (Fin 4) := (1, swap 0 1 * swap 2 3)

private def aModel : Multiplicative (ZMod 2) × Perm (Fin 4) := (Multiplicative.ofAdd 1, 1)

private def tModel : Multiplicative (ZMod 2) × Perm (Fin 4) := (1, swap 0 1)

private def xModel : Multiplicative (ZMod 2) × Perm (Fin 4) := (1, swap 0 3 * swap 0 1 * swap 0 2)

private theorem card_model : Nat.card (Multiplicative (ZMod 2) × Perm (Fin 4)) = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem card_sylowModel : Nat.card sylowModel = 16 := by
  change Nat.card {x : Multiplicative (ZMod 2) × Perm (Fin 4) // InDihedral x.2} = 16
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem card_dihedralModel : Nat.card dihedralModel = 8 := by
  change Nat.card {x : Multiplicative (ZMod 2) × Perm (Fin 4) // InDihedralOne x} = 8
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem dihedralModel_le : dihedralModel ≤ sylowModel := fun _ hx => hx.2

private theorem relIndex_dihedralModel : dihedralModel.relIndex sylowModel = 2 := by
  have h := Subgroup.relIndex_mul_card dihedralModel sylowModel
  rw [inf_of_le_left dihedralModel_le, card_dihedralModel, card_sylowModel] at h
  omega

private theorem model_elements :
    InDihedral xModel.2 ∧ xModel * xModel = zModel ∧ zModel ≠ 1 ∧ aModel ≠ 1 ∧
      aModel ≠ zModel ∧ aModel * aModel = 1 := by
  decide +kernel

private theorem model_sq :
    ∀ y : Multiplicative (ZMod 2) × Perm (Fin 4), InDihedral y.2 → y * y = 1 ∨ y * y = zModel := by
  decide +kernel

private theorem model_z_central :
    ∀ y : Multiplicative (ZMod 2) × Perm (Fin 4), InDihedral y.2 → zModel * y = y * zModel := by
  decide +kernel

private theorem model_a_central :
    ∀ y : Multiplicative (ZMod 2) × Perm (Fin 4), aModel * y = y * aModel := by
  decide +kernel

private theorem model_conj :
    ∀ r : Multiplicative (ZMod 2) × Perm (Fin 4), InDihedralOne r → r * r = 1 → r = 1 ∨
      (∃ h : Multiplicative (ZMod 2) × Perm (Fin 4), h⁻¹ * tModel * h = r) ∨
      (∃ h : Multiplicative (ZMod 2) × Perm (Fin 4), h⁻¹ * zModel * h = r) := by
  decide +kernel

end Model

theorem isEmpty_mulEquiv_zTwo_prod_sFour {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} (hK : ¬ 2 ∣ K.index) :
    IsEmpty (K ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  refine ⟨fun e => ?_⟩
  let φ : Multiplicative (ZMod 2) × Perm (Fin 4) →* G := K.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := K.subtype_injective.comp e.symm.injective
  have hKcard : Nat.card K = 48 := by rw [Nat.card_congr e.toEquiv]; exact card_model
  have hPcard : Nat.card (sylowModel.map φ) = 16 := by
    rw [Subgroup.card_map_of_injective hφ, card_sylowModel]
  have hPidx : ¬ 2 ∣ (sylowModel.map φ).index := by
    have h1 := (sylowModel.map φ).card_mul_index
    have h2 := K.card_mul_index
    rw [hPcard] at h1
    rw [hKcard] at h2
    omega
  obtain ⟨hxD, hxz, hz1, ha1, haz, haa⟩ := model_elements
  refine false_of_forall_isConj_of_mem hnonab (P := sylowModel.map φ) (R := dihedralModel.map φ)
    (IsPGroup.of_card (n := 4) hPcard) hPidx (Subgroup.map_mono dihedralModel_le)
    (by rw [Subgroup.relIndex_map_map_of_injective _ _ hφ, relIndex_dihedralModel])
    (x := φ xModel) (z := φ zModel) (a := φ aModel) (t := φ tModel)
    (Subgroup.mem_map_of_mem φ hxD) (by rw [← map_mul, hxz]) ?_ ?_ ?_
    (fun h => hz1 (hφ (h.trans (map_one φ).symm)))
    (fun h => ha1 (hφ (h.trans (map_one φ).symm))) (fun h => haz (hφ h))
    (by rw [← map_mul, haa, map_one]) ?_
  · rintro _ ⟨y, hy, rfl⟩
    rcases model_sq y hy with h | h
    · exact Or.inl (by rw [← map_mul, h, map_one])
    · exact Or.inr (by rw [← map_mul, h])
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, model_z_central y hy]
  · rintro _ ⟨y, -, rfl⟩
    rw [← map_mul, ← map_mul, model_a_central y]
  · rintro _ ⟨r, hr, rfl⟩ hrr
    have hrr' : r * r = 1 := hφ (by rw [map_mul, hrr, map_one])
    rcases model_conj r hr hrr' with h | ⟨h, hh⟩ | ⟨h, hh⟩
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (Or.inl (φ.map_isConj (isConj_of_conj_eq hh)))
    · exact Or.inr (Or.inr (φ.map_isConj (isConj_of_conj_eq hh)))

theorem stmt15413_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) : Stmt15413 G T := by
  intro Y _
  have := hyp.simple
  exact isEmpty_mulEquiv_zTwo_prod_sFour hyp.nonabelian
    (fun h => hyp.sylow.2 (h.trans (Subgroup.index_dvd_of_le le_sup_right)))

end CFSG.Quasithin.EmptyFaithfulMultiple
