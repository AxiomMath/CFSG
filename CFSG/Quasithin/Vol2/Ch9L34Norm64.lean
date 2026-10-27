module

public import CFSG.Quasithin.Vol2.Ch9L34M64
public import Certificates.Certificate7252

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M


abbrev img64 : Subgroup (MulAut (Wn 64)) := img rho64GL

@[expose] def gen64 : Set (MulAut (Wn 64)) :=
  {slRep rho64GL (uSL (f4c 1) 0 0), slRep rho64GL (uSL (f4c 2) 0 0),
    slRep rho64GL (uSL 0 0 (f4c 1)), slRep rho64GL (uSL 0 0 (f4c 2))}

abbrev P64 : Subgroup (MulAut (Wn 64)) := Subgroup.closure gen64

theorem P64_le : P64 ≤ img64 := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;> exact slRep_mem_img _ _

theorem actsBy_gen64 :
    (ActsBy (MaskCoords.std 64) (slRep rho64GL (uSL (f4c 1) 0 0)) (tabX12_64.getD 1 []) ∧
      AllLt 64 (tabX12_64.getD 1 []) = true) ∧
    (ActsBy (MaskCoords.std 64) (slRep rho64GL (uSL (f4c 2) 0 0)) (tabX12_64.getD 2 []) ∧
      AllLt 64 (tabX12_64.getD 2 []) = true) ∧
    (ActsBy (MaskCoords.std 64) (slRep rho64GL (uSL 0 0 (f4c 1))) (tabX23_64.getD 1 []) ∧
      AllLt 64 (tabX23_64.getD 1 []) = true) ∧
    (ActsBy (MaskCoords.std 64) (slRep rho64GL (uSL 0 0 (f4c 2))) (tabX23_64.getD 2 []) ∧
      AllLt 64 (tabX23_64.getD 2 []) = true) := by
  simp only [slRep_uSL]
  exact ⟨(actsBy_x64 (by norm_num : 1 < 4)).1, (actsBy_x64 (by norm_num : 2 < 4)).1,
    (actsBy_x64 (by norm_num : 1 < 4)).2.2, (actsBy_x64 (by norm_num : 2 < 4)).2.2⟩

theorem card_fixV_P64_le : Nat.card (fixV P64) ≤ 2 := by
  obtain ⟨⟨h₁, c₁⟩, ⟨h₂, c₂⟩, ⟨h₃, c₃⟩, ⟨h₄, c₄⟩⟩ := actsBy_gen64
  obtain ⟨⟨hl, hws, hech⟩, -⟩ := chkN64_spec Certificates.certificate7252
  have h := two_pow_mul_card_le_four (MaskCoords.std 64) h₁ h₂ h₃ h₄ c₁ c₂ c₃ c₄ hws hech
    (F := fixV P64) fun v hv => ⟨hv _ (Subgroup.subset_closure (Or.inl rfl)),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inl rfl))),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl))))⟩
  rw [hl] at h
  have h2 : (2 : ℕ) ^ 64 = 2 ^ 63 * 2 := by norm_num
  rw [h2] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

theorem mem_fixV_P64 : toW 64 512 ∈ fixV P64 := by
  obtain ⟨⟨h₁, -⟩, ⟨h₂, -⟩, ⟨h₃, -⟩, ⟨h₄, -⟩⟩ := actsBy_gen64
  obtain ⟨-, ⟨e₁, e₂, e₃, e₄⟩, -⟩ := chkN64_spec Certificates.certificate7252
  have hlt : (512 : ℕ) < 2 ^ 64 := by norm_num
  apply mem_fixV_closure
  rintro _ (rfl | rfl | rfl | rfl)
  · exact (h₁ 512 hlt).trans (congrArg _ e₁)
  · exact (h₂ 512 hlt).trans (congrArg _ e₂)
  · exact (h₃ 512 hlt).trans (congrArg _ e₃)
  · exact (h₄ 512 hlt).trans (congrArg _ e₄)

theorem toW64_512_ne : toW 64 512 ≠ 1 := fun h =>
  absurd (toW_inj (n := 64) (by norm_num) (by norm_num) (h.trans (toW_zero 64).symm))
    (by norm_num)

theorem fixV_P64 {w : Wn 64} (hw : w ∈ fixV P64) : w = 1 ∨ w = toW 64 512 := by
  classical
  set T : Finset (Wn 64) := {1, toW 64 512} with hT
  have hTcard : T.card = 2 := Finset.card_pair toW64_512_ne.symm
  have hsub : (T : Set (Wn 64)) ⊆ (fixV P64 : Set (Wn 64)) := by
    intro x hx
    simp only [hT, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (fixV P64).one_mem
    · exact mem_fixV_P64
  have hfin : (fixV P64 : Set (Wn 64)).Finite := Set.toFinite _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
    exact card_fixV_P64_le) hfin
  have hw' : w ∈ (T : Set (Wn 64)) := heq ▸ hw
  simpa [hT] using hw'

theorem closure_orbit64 :
    Subgroup.closure {x | ∃ γ ∈ img64, γ (toW 64 512) = x} = ⊤ := by
  obtain ⟨-, -, hc, hp, -⟩ := chkN64_spec Certificates.certificate7252
  refine eq_top_of_comb (MaskCoords.std 64) hc hp fun o ho => ?_
  obtain ⟨p, hp64, rfl⟩ := List.mem_map.1 ho
  rw [List.mem_range] at hp64
  refine Subgroup.subset_closure ⟨slRep rho64GL (uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)) *
    w0SL), slRep_mem_img _ _, ?_⟩
  obtain ⟨hw, hwl⟩ := actsBy_rho64GL_cols w0GL
  have lt1 := actM_lt (allLt_spec hwl) 512
  change slRep rho64GL _ ((MaskCoords.std 64).vm 512) = _
  simp only [map_mul, MulAut.mul_apply, slRep_uSL, slRep_w0SL]
  rw [hw 512 (by norm_num), actsBy_uGL64 p _ lt1, Nat.mod_eq_of_lt hp64]
  rfl

theorem nc64 : ∃ a b : SpecialLinearGroup (Fin 3) F4,
    slRep rho64GL a * slRep rho64GL b ≠ slRep rho64GL b * slRep rho64GL a := by
  refine ⟨uSL (f4c 1) 0 0, uSL 0 0 (f4c 1), fun h => ?_⟩
  obtain ⟨⟨h₁, c₁⟩, -, ⟨h₃, c₃⟩, -⟩ := actsBy_gen64
  obtain ⟨-, -, -, -, hne⟩ := chkN64_spec Certificates.certificate7252
  have e := congrArg (fun F : MulAut (Wn 64) => F ((MaskCoords.std 64).vm 4)) h
  simp only [MulAut.mul_apply] at e
  rw [h₃ 4 (by norm_num), h₁ _ (actM_lt (allLt_spec c₃) 4), h₁ 4 (by norm_num),
    h₃ _ (actM_lt (allLt_spec c₁) 4)] at e
  exact hne ((MaskCoords.std 64).vm_inj _ _ (actM_lt (allLt_spec c₁) _)
    (actM_lt (allLt_spec c₃) _) e)

theorem rho64GL_mem_range (g : GL (Fin 3) F4) : rho64GL g ∈ rho64.range :=
  ⟨SemidirectProduct.inl g, by rw [rho64_apply]; simp⟩

theorem fld64_mem_range : fld64 ∈ rho64.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1, 0)), ?_⟩
  rw [rho64_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out64, c22Hom_apply]
  simp

theorem gr64_mem_range : gr64 ∈ rho64.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (0, 1)), ?_⟩
  rw [rho64_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out64, c22Hom_apply]
  simp

theorem range_le_normalizer64 :
    rho64.range ≤ Subgroup.normalizer (img64 : Set (MulAut (Wn 64))) := by
  rintro _ ⟨x, rfl⟩
  rw [rho64_apply, out64]
  exact mul_c22Hom_mem_normalizer rho64GL rho64GL_frobGL rho64GL_grGL _ _ _ _ _

theorem odd64 : Odd (Nat.card {w : Wn 64 // w ≠ 1 ∧ (∀ p ∈ P64, p w = w) ∧
    Subgroup.closure {v | ∃ γ ∈ img64, γ w = v} = ⊤}) := by
  have hset : {w : Wn 64 | w ≠ 1 ∧ (∀ p ∈ P64, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img64, γ w = v} = ⊤} = {toW 64 512} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact (fixV_P64 h2).resolve_left h1
    · rintro rfl
      exact ⟨toW64_512_ne, mem_fixV_P64, closure_orbit64⟩
  have hcard : Nat.card {w : Wn 64 // w ≠ 1 ∧ (∀ p ∈ P64, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img64, γ w = v} = ⊤} = Set.ncard {w : Wn 64 | w ≠ 1 ∧
        (∀ p ∈ P64, p w = w) ∧ Subgroup.closure {v | ∃ γ ∈ img64, γ w = v} = ⊤} :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_singleton]
  decide

theorem exists_conj_le64 {A : Subgroup (MulAut (Wn 64))}
    (hA : A ≤ Subgroup.normalizer (img64 : Set (MulAut (Wn 64)))) (h2 : IsPGroup 2 A) :
    ∃ n ∈ Subgroup.normalizer (img64 : Set (MulAut (Wn 64))),
      A.map (MulAut.conj n).toMonoidHom ≤ rho64.range :=
  exists_conj_le_of_normalizer rho64GL rho64GL_frobGL rho64GL_grGL nc64 rho64GL_mem_range
    fld64_mem_range gr64_mem_range range_le_normalizer64 P64_le odd64 hA h2

end CFSG.Quasithin.H13.Ch9.L34N
