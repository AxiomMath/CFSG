module

import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Quasithin.Vol2.Ch3E213MP6ED

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

theorem map_centralizer_eq {P : Type*} [Group P] (τ : MulAut P) (X : Subgroup P) :
    (Subgroup.centralizer (X : Set P)).map τ.toMonoidHom =
      Subgroup.centralizer ((X.map τ.toMonoidHom : Subgroup P) : Set P) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hz w hw]
  · intro h
    refine ⟨τ.symm y, fun w hw => ?_, by simp⟩
    have h1 := h (τ w) ⟨w, hw, rfl⟩
    apply τ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1

variable {A : Type} [Group A] {K E : Subgroup A} [K.Normal] [(K ⊔ E).Normal] {e : ↥K ≃* M6}
  {χ : ↥(K ⊔ E) ≃* Equiv.Perm (Fin 6)}

theorem tau_apply (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (t : A) {y : P6} (hy : y ∈ A6s) :
    (MulAut.congr χ (MulAut.conjNormal t)) y =
      ((MulAut.congr e (MulAut.conjNormal t)) ⟨y, hy⟩ : P6) := by
  set k : K := e.symm ⟨y, hy⟩ with hk
  have h1 : χ.symm y = ⟨k, (le_sup_left : K ≤ K ⊔ E) k.2⟩ := by
    apply χ.injective
    rw [MulEquiv.apply_symm_apply, hχ _ k.2]
    simp [hk]
  have h2 : MulAut.conjNormal t (⟨k, (le_sup_left : K ≤ K ⊔ E) k.2⟩ : ↥(K ⊔ E)) =
      ⟨_, (le_sup_left : K ≤ K ⊔ E) (MulAut.conjNormal t k).2⟩ :=
    Subtype.ext (by simp only [MulAut.conjNormal_apply])
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [h1, h2, hχ _ (MulAut.conjNormal t k).2]

theorem map_VA (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    {t : A} (hab : Ra.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Rb) :
    VA.map (MulAut.congr χ (MulAut.conjNormal t)).toMonoidHom = VB := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    have hyA := VA_le_A6 hy
    rw [MulEquiv.coe_toMonoidHom, tau_apply hχ t hyA]
    have h1 : (MulAut.congr e (MulAut.conjNormal t)) ⟨y, hyA⟩ ∈ Rb := hab ▸ ⟨⟨y, hyA⟩, hy, rfl⟩
    exact h1
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_VA, card_VB]

theorem map_VB (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    {t : A} (hab : Rb.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Ra) :
    VB.map (MulAut.congr χ (MulAut.conjNormal t)).toMonoidHom = VA := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    have hyA := VB_le_A6 hy
    rw [MulEquiv.coe_toMonoidHom, tau_apply hχ t hyA]
    have h1 : (MulAut.congr e (MulAut.conjNormal t)) ⟨y, hyA⟩ ∈ Ra := hab ▸ ⟨⟨y, hyA⟩, hy, rfl⟩
    exact h1
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_VA, card_VB]

theorem map_E_eq {S : Subgroup A} (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (hSF : ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom = S06) {t : A} (htS : t ∈ S)
    (hab : Ra.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Rb ∧
      Rb.map (MulAut.congr e (MulAut.conjNormal t)).toMonoidHom = Ra)
    (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set A)) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE4 : 4 ≤ Nat.card E) : (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom = Z6 := by
  set τ := MulAut.congr χ (MulAut.conjNormal t) with hτdef
  have hle : (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom ≤ S06 := by
    rw [← hSF]
    exact Subgroup.map_mono fun f hf => ⟨hES hf, f.2⟩
  have h2 : ∀ y ∈ (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom, y * y = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul]
    have h1 : w * w = 1 := Subtype.ext (by simpa using hE2 _ hw)
    rw [h1, map_one]
  have hinv : ((E.subgroupOf (K ⊔ E)).map χ.toMonoidHom).map τ.toMonoidHom =
      (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom := by
    rw [hτdef, map_congr_conj, ← Subgroup.inf_subgroupOf_right E (K ⊔ E),
      P5.map_conjNormal_eq (hSE htS)]
  have hA1 : A1.map τ.toMonoidHom = A2 := by
    rw [← centralizer_VA, map_centralizer_eq, map_VA hχ hab.1, centralizer_VB]
  have hA2 : A2.map τ.toMonoidHom = A1 := by
    rw [← centralizer_VB, map_centralizer_eq, map_VB hχ hab.2, centralizer_VA]
  have hZ : (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom ≤ Z6 := by
    rw [← A1_inf_A2]
    rcases le_or_le_S06 hle h2 with h | h
    · refine le_inf h ?_
      rw [← hinv, ← hA1]
      exact Subgroup.map_mono h
    · refine le_inf ?_ h
      rw [← hinv, ← hA2]
      exact Subgroup.map_mono h
  refine Subgroup.eq_of_le_of_card_ge hZ (card_Z6_le.trans ?_)
  rw [Subgroup.card_map_of_injective χ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : E ≤ K ⊔ E)).toEquiv]
  exact hE4

omit [K.Normal] [(K ⊔ E).Normal] in
theorem sup_eq (hEZ : (E.subgroupOf (K ⊔ E)).map χ.toMonoidHom = Z6) :
    K ⊔ E = E ⊔ CFSG.conjugate E ((χ.symm x0 : ↥(K ⊔ E)) : A) := by
  set x : ↥(K ⊔ E) := χ.symm x0 with hxdef
  have hχx : χ x = x0 := MulEquiv.apply_symm_apply χ x0
  set W := E ⊔ CFSG.conjugate E (x : A) with hWdef
  have hconjF : CFSG.conjugate E (x : A) ≤ K ⊔ E := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 : (x : A)⁻¹ * w * (x : A) ∈ K ⊔ E :=
      (K ⊔ E).mul_mem ((K ⊔ E).mul_mem ((K ⊔ E).inv_mem x.2) ((le_sup_right : E ≤ K ⊔ E) hw)) x.2
    simpa using h1
  refine le_antisymm (fun f hf => ?_) (sup_le le_sup_right hconjF)
  have htop : (W.subgroupOf (K ⊔ E)).map χ.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← sup_Z6_conj_eq_top]
    refine sup_le ?_ ?_
    · rw [← hEZ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_left)
    · rintro _ ⟨z, hz, rfl⟩
      rw [← hEZ] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine ⟨x⁻¹ * w * x, ?_, ?_⟩
      · show ((x : A)⁻¹ * w * (x : A)) ∈ W
        refine (le_sup_right : CFSG.conjugate E (x : A) ≤ W) ⟨w, hw, ?_⟩
        simp
      · simp [map_mul, map_inv, hχx]
  have hf' : χ ⟨f, hf⟩ ∈ (W.subgroupOf (K ⊔ E)).map χ.toMonoidHom := htop ▸ Subgroup.mem_top _
  obtain ⟨w, hw, hwf⟩ := hf'
  have h1 : w = ⟨f, hf⟩ := χ.injective hwf
  have h2 : (w : A) ∈ W := hw
  rw [h1] at h2
  exact h2

omit [(K ⊔ E).Normal] in
theorem eq_bot_of_normal (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) (e : ↥K ≃* M6)
    {N : Subgroup A} (hNF : N ≤ K ⊔ E) (hN2 : IsPGroup 2 N)
    (hNn : (N.subgroupOf (K ⊔ E)).Normal) : N = ⊥ := by
  have hconj : ∀ n ∈ N, ∀ f ∈ K ⊔ E, f * n * f⁻¹ ∈ N := fun n hn f hf =>
    hNn.conj_mem ⟨n, hNF hn⟩ hn ⟨f, hf⟩
  have hM : ((N ⊓ K).subgroupOf K).Normal := ⟨fun n hn k => ⟨hconj _ hn.1 _
    ((le_sup_left : K ≤ K ⊔ E) k.2), (k * n * k⁻¹).2⟩⟩
  have hM' := hM.map e.toMonoidHom e.surjective
  have : IsSimpleGroup M6 := alternatingGroup.isSimpleGroup (by simp)
  have hNK : N ⊓ K = ⊥ := by
    rcases hM'.eq_bot_or_eq_top with h | h
    · rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective, Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      have hP : IsPGroup 2 ↥((N ⊓ K).subgroupOf K) :=
        (hN2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hP' := hP.map e.toMonoidHom
      rw [h] at hP'
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := hP'.exists_card_eq
      rw [Subgroup.card_top, card_A6] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 360)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  refine hC n fun k hk => ?_
  have hw : n * k * n⁻¹ * k⁻¹ ∈ N ⊓ K := by
    refine ⟨?_, K.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hk n) (K.inv_mem hk)⟩
    have h1 := hconj _ (N.inv_mem hn) k ((le_sup_left : K ≤ K ⊔ E) hk)
    have h2 := N.mul_mem hn h1
    rwa [show n * (k * n⁻¹ * k⁻¹) = n * k * n⁻¹ * k⁻¹ by group] at h2
  rw [hNK, Subgroup.mem_bot] at hw
  calc n * k = n * k * n⁻¹ * k⁻¹ * k * n := by group
    _ = k * n := by rw [hw, one_mul]

end CFSG.Quasithin.Ch3E213M.P6E
