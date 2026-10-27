module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourTypes
public import CFSG.Quasithin.SteinbergCBI16Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.B45Exc3A7

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family

theorem alt7_le_closure :
    alternatingGroup (Fin 7) ≤
      Subgroup.closure ({SteinbergCB.I16.a7, SteinbergCB.I16.b7} : Set (Perm (Fin 7))) := by
  intro s hs
  have h1 : (⟨s, hs⟩ : alternatingGroup (Fin 7)) ∈
      Subgroup.closure (Set.range SteinbergCB.I16.gens7) := by
    rw [SteinbergCB.I16.closure_gens7]
    trivial
  have h2 := Subgroup.mem_map_of_mem (alternatingGroup (Fin 7)).subtype h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gen_a_facts :
    sign (c[1, 6, 3, 4] * c[2, 5] : Perm (Fin 7)) = 1 ∧
    SteinbergCB.I16.a7 =
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 2 * swap 1 3) *
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3) *
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 1 * swap 2 3) *
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) ∧
    SteinbergCB.I16.b7 =
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 2 * swap 1 3) *
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 2 * swap 1 3) *
      ((c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹) *
      (swap 0 1 * swap 2 3) := by
  decide +kernel

theorem gen_b_facts :
    sign (c[1, 6, 3, 5, 4] : Perm (Fin 7)) = 1 ∧
    SteinbergCB.I16.a7 =
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 4 5) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 4 5) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 2 3) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 2 3) ∧
    SteinbergCB.I16.b7 =
      (swap 0 1 * swap 4 5) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 4 5) *
      (c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹) *
      (swap 0 1 * swap 2 3) * (swap 0 1 * swap 4 5) := by
  decide +kernel

theorem exists_perm_extend {n : ℕ} (hn : n ≤ 7) (y : Fin n ↪ Fin 7) :
    ∃ ρ : Perm (Fin 7), ∀ i : Fin n, ρ (Fin.castLE hn i) = y i := by
  have hmt := Equiv.Perm.isMultiplyPretransitive (Fin 7) n
  let x : Fin n ↪ Fin 7 := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) x y
  refine ⟨ρ, fun i => ?_⟩
  have := DFunLike.congr_fun hρ i
  simpa [x] using this

theorem gen_four {B : Subgroup (Perm (Fin 7))} (hT : B42A57.Type7A (B : Set (Perm (Fin 7))) 4) :
    ∃ f : Fin 2 → Perm (Fin 7), (∀ i, f i ∈ alternatingGroup (Fin 7)) ∧
      alternatingGroup (Fin 7) ≤
        Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} := by
  classical
  have htrans : ∀ (ρ g : Perm (Fin 7)) (u₁ u₂ : Perm (Fin 7)),
      sign g = 1 → ρ * u₁ * ρ⁻¹ ∈ B → ρ * u₂ * ρ⁻¹ ∈ B →
      SteinbergCB.I16.a7 ∈ Subgroup.closure ({u₁, u₂, g * u₁ * g⁻¹, g * u₂ * g⁻¹} :
        Set (Perm (Fin 7))) →
      SteinbergCB.I16.b7 ∈ Subgroup.closure ({u₁, u₂, g * u₁ * g⁻¹, g * u₂ * g⁻¹} :
        Set (Perm (Fin 7))) →
      ∃ f : Fin 2 → Perm (Fin 7), (∀ i, f i ∈ alternatingGroup (Fin 7)) ∧
        alternatingGroup (Fin 7) ≤
          Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} := by
    intro ρ g u₁ u₂ hg h1 h2 ha hb
    refine ⟨![1, ρ * g * ρ⁻¹], fun i => ?_, ?_⟩
    · fin_cases i
      · exact one_mem _
      · show ρ * g * ρ⁻¹ ∈ alternatingGroup (Fin 7)
        rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hg]
        simp
    set T := Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = ![1, ρ * g * ρ⁻¹] i * b *
      (![1, ρ * g * ρ⁻¹] i)⁻¹} with hT
    have hgen : Subgroup.closure ({u₁, u₂, g * u₁ * g⁻¹, g * u₂ * g⁻¹} :
        Set (Perm (Fin 7))) ≤ T.comap (MulAut.conj ρ).toMonoidHom := by
      rw [Subgroup.closure_le]
      have hmem0 : ∀ b ∈ B, b ∈ T := fun b hb =>
        Subgroup.subset_closure ⟨0, b, hb, by simp⟩
      have hmem1 : ∀ b ∈ B, ρ * g * ρ⁻¹ * b * (ρ * g * ρ⁻¹)⁻¹ ∈ T := fun b hb =>
        Subgroup.subset_closure ⟨1, b, hb, by simp⟩
      rintro x (rfl | rfl | rfl | rfl)
      · exact hmem0 _ h1
      · exact hmem0 _ h2
      · show ρ * (g * u₁ * g⁻¹) * ρ⁻¹ ∈ T
        have := hmem1 _ h1
        convert this using 1
        group
      · show ρ * (g * u₂ * g⁻¹) * ρ⁻¹ ∈ T
        have := hmem1 _ h2
        convert this using 1
        group
    intro s hs
    have hs' : ρ⁻¹ * s * ρ ∈ alternatingGroup (Fin 7) := by
      have := (alternatingGroup.normal (α := Fin 7)).conj_mem s hs ρ⁻¹
      simpa using this
    have h7 := alt7_le_closure hs'
    have hab : Subgroup.closure ({SteinbergCB.I16.a7, SteinbergCB.I16.b7} :
        Set (Perm (Fin 7))) ≤ T.comap (MulAut.conj ρ).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hgen ha
      · exact hgen hb
    have h8 := hab h7
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h8
    convert h8 using 1
    group
  rcases hT with ⟨-, a, b, c, d, hnd, h1, h2, -⟩ | ⟨-, a, b, c, d, e, f, hnd, h1, h2, -⟩
  ·
    obtain ⟨hgs, hwa, hwb⟩ := gen_a_facts
    let y : Fin 4 ↪ Fin 7 := ⟨[a, b, c, d].get, List.nodup_iff_injective_get.1 hnd⟩
    obtain ⟨ρ, hρ⟩ := exists_perm_extend (by norm_num) y
    have hρ0 : ρ 0 = a := hρ 0
    have hρ1 : ρ 1 = b := hρ 1
    have hρ2 : ρ 2 = c := hρ 2
    have hρ3 : ρ 3 = d := hρ 3
    refine htrans ρ _ (swap 0 1 * swap 2 3) (swap 0 2 * swap 1 3) hgs ?_ ?_ ?_ ?_
    · have e : ρ * (swap 0 1 * swap 2 3) * ρ⁻¹ = swap a b * swap c d := by
        rw [← hρ0, ← hρ1, ← hρ2, ← hρ3, swap_apply_apply, swap_apply_apply]
        group
      rw [e]
      exact h1
    · have e : ρ * (swap 0 2 * swap 1 3) * ρ⁻¹ = swap a c * swap b d := by
        rw [← hρ0, ← hρ1, ← hρ2, ← hρ3, swap_apply_apply, swap_apply_apply]
        group
      rw [e]
      exact h2
    · rw [hwa]
      have hm : ∀ x ∈ ({swap (0 : Fin 7) 1 * swap 2 3, swap 0 2 * swap 1 3,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹} :
          Set (Perm (Fin 7))), x ∈ Subgroup.closure ({swap (0 : Fin 7) 1 * swap 2 3,
          swap 0 2 * swap 1 3,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹} :
          Set (Perm (Fin 7))) := fun x hx => Subgroup.subset_closure hx
      refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_)
        ?_) ?_) ?_) ?_ <;> exact hm _ (by simp)
    · rw [hwb]
      have hm : ∀ x ∈ ({swap (0 : Fin 7) 1 * swap 2 3, swap 0 2 * swap 1 3,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹} :
          Set (Perm (Fin 7))), x ∈ Subgroup.closure ({swap (0 : Fin 7) 1 * swap 2 3,
          swap 0 2 * swap 1 3,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹,
          (c[1, 6, 3, 4] * c[2, 5]) * (swap 0 2 * swap 1 3) * (c[1, 6, 3, 4] * c[2, 5])⁻¹} :
          Set (Perm (Fin 7))) := fun x hx => Subgroup.subset_closure hx
      refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
        exact hm _ (by simp)
  ·
    obtain ⟨hgs, hwa, hwb⟩ := gen_b_facts
    let y : Fin 6 ↪ Fin 7 := ⟨[a, b, c, d, e, f].get, List.nodup_iff_injective_get.1 hnd⟩
    obtain ⟨ρ, hρ⟩ := exists_perm_extend (by norm_num) y
    have hρ0 : ρ 0 = a := hρ 0
    have hρ1 : ρ 1 = b := hρ 1
    have hρ2 : ρ 2 = c := hρ 2
    have hρ3 : ρ 3 = d := hρ 3
    have hρ4 : ρ 4 = e := hρ 4
    have hρ5 : ρ 5 = f := hρ 5
    refine htrans ρ _ (swap 0 1 * swap 2 3) (swap 0 1 * swap 4 5) hgs ?_ ?_ ?_ ?_
    · have e : ρ * (swap 0 1 * swap 2 3) * ρ⁻¹ = swap a b * swap c d := by
        rw [← hρ0, ← hρ1, ← hρ2, ← hρ3, swap_apply_apply, swap_apply_apply]
        group
      rw [e]
      exact h1
    · have hconj : ρ * (swap 0 1 * swap 4 5) * ρ⁻¹ = swap a b * swap e f := by
        rw [← hρ0, ← hρ1, ← hρ4, ← hρ5, swap_apply_apply, swap_apply_apply]
        group
      rw [hconj]
      exact h2
    · rw [hwa]
      have hm : ∀ x ∈ ({swap (0 : Fin 7) 1 * swap 2 3, swap 0 1 * swap 4 5,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹} :
          Set (Perm (Fin 7))), x ∈ Subgroup.closure ({swap (0 : Fin 7) 1 * swap 2 3,
          swap 0 1 * swap 4 5,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹} :
          Set (Perm (Fin 7))) := fun x hx => Subgroup.subset_closure hx
      refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_)
        ?_) ?_) ?_) ?_) ?_) ?_ <;> exact hm _ (by simp)
    · rw [hwb]
      have hm : ∀ x ∈ ({swap (0 : Fin 7) 1 * swap 2 3, swap 0 1 * swap 4 5,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹} :
          Set (Perm (Fin 7))), x ∈ Subgroup.closure ({swap (0 : Fin 7) 1 * swap 2 3,
          swap 0 1 * swap 4 5,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 2 3) * (c[1, 6, 3, 5, 4])⁻¹,
          c[1, 6, 3, 5, 4] * (swap 0 1 * swap 4 5) * (c[1, 6, 3, 5, 4])⁻¹} :
          Set (Perm (Fin 7))) := fun x hx => Subgroup.subset_closure hx
      refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
        exact hm _ (by simp)

section Bound

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_index_pow_of_le (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E) (hEL : E ≤ L)
    (e : CQ L ≃* alternatingGroup (Fin 7)) {r : ℕ} (f : Fin r → Perm (Fin 7))
    (hf : ∀ i, f i ∈ alternatingGroup (Fin 7))
    (hcl : alternatingGroup (Fin 7) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈
      (imgSub L E hEL e).map (alternatingGroup (Fin 7)).subtype, x = f i * b * (f i)⁻¹}) :
    Nat.card W ≤ (fixV E).index ^ r := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  have hcf : ∀ s : alternatingGroup (Fin 7), cEquiv (s : Perm (Fin 7)) = MulAut.conj s :=
    fun s => MulAut.conjNormal_val
  let cs : List (MulAut (alternatingGroup (Fin 7))) :=
    List.ofFn fun i => MulAut.conj (⟨f i, hf i⟩ : alternatingGroup (Fin 7))
  have hcs : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact conj_mem_range_actS hE e _
  have hgen : ∀ s : alternatingGroup (Fin 7), MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (alternatingGroup (Fin 7)) | ∃ c ∈ cs, ∃ b : ↥(L ⊔ E),
        (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    have h1 := hcl s.2
    have h2 := Subgroup.mem_map_of_mem cEquiv.toMonoidHom h1
    rw [MonoidHom.map_closure] at h2
    have h3 : cEquiv.toMonoidHom (s : Perm (Fin 7)) = MulAut.conj s := hcf s
    rw [h3] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨x, ⟨i, b, hb, rfl⟩, rfl⟩
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨b₀, rfl⟩ := mem_imgSub.1 hb'
    refine ⟨MulAut.conj ⟨f i, hf i⟩, List.mem_ofFn.2 ⟨i, rfl⟩,
      ⟨(b₀ : MulAut W), Subgroup.mem_sup_right b₀.2⟩, b₀.2, ?_⟩
    have h4 : cEquiv (f i) = MulAut.conj ⟨f i, hf i⟩ := hcf ⟨f i, hf i⟩
    have h5 : actS hE e ⟨(b₀ : MulAut W), Subgroup.mem_sup_right b₀.2⟩ =
        MulAut.conj (redHom L e (Subgroup.inclusion hEL b₀)) :=
      actS_of_mem hE e (Subgroup.inclusion hEL b₀)
    show cEquiv (f i * ((redHom L e (Subgroup.inclusion hEL b₀) : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) * (f i)⁻¹) = _
    rw [map_mul, map_mul, map_inv, h4, hcf, h5]
  have := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcs hgen
  rwa [List.length_ofFn] at this

theorem card_le_of_le (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E) (hEL : E ≤ L)
    (hE1 : E ≠ ⊥) (e : CQ L ≃* alternatingGroup (Fin 7)) :
    (Nat.card E = 2 ∧ Nat.card W ≤ (fixV E).index ^ 3) ∨
      (Nat.card E = 4 ∧ Nat.card W ≤ (fixV E).index ^ 2) := by
  classical
  set B : Subgroup (Perm (Fin 7)) := (imgSub L E hEL e).map (alternatingGroup (Fin 7)).subtype
    with hB
  have hBcard : Nat.card B = Nat.card E := by
    rw [hB, Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective,
      card_imgSub hW hirr hEL hEel e]
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    exact hE1 (Subgroup.card_eq_one.1 hBcard.symm)
  have hBA : B ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := imgSub_comm hEel x hx y hy
    exact congrArg Subtype.val this
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := imgSub_sq hEel x hx
    exact congrArg Subtype.val this
  have hidx1 : 1 ≤ (fixV E).index := Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  rcases B42A57.classify7A hB1 hBA hBc hB2 with ⟨h2, r, f, hf, hr, hcl⟩ | hT
  · left
    refine ⟨hBcard ▸ h2, ?_⟩
    calc Nat.card W ≤ (fixV E).index ^ r :=
          card_le_index_pow_of_le hW hperf hirr hL hE hEel hEL e f hf hcl
      _ ≤ (fixV E).index ^ 3 := Nat.pow_le_pow_right hidx1 hr
  · right
    have h4 : Nat.card B = 4 := by
      rcases hT with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    rw [h4] at hT
    obtain ⟨f, hf, hcl⟩ := gen_four hT
    exact ⟨hBcard ▸ h4, card_le_index_pow_of_le hW hperf hirr hL hE hEel hEL e f hf hcl⟩

end Bound

end CFSG.Quasithin.B45Exc3A7
