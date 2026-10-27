module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W2
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def c5_627 : Equiv.Perm (Fin 5) := finRotate 5

@[expose] def klein627 (a b : Equiv.Perm (Fin 5)) : Prop :=
  Equiv.Perm.sign a = 1 ∧ Equiv.Perm.sign b = 1 ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b

instance (a b : Equiv.Perm (Fin 5)) : Decidable (klein627 a b) := by
  unfold klein627; infer_instance

@[expose] def ordP627 (p : ℕ) (a b : Equiv.Perm (Fin 5)) : Prop :=
  ∃ x ∈ [a, b, a * b], ∃ y ∈ [a, b, a * b],
    (x * (c5_627 * y * c5_627⁻¹)) ^ p = 1 ∧ x * (c5_627 * y * c5_627⁻¹) ≠ 1

instance (p : ℕ) (a b : Equiv.Perm (Fin 5)) : Decidable (ordP627 p a b) := by
  unfold ordP627; infer_instance

theorem fc_a5gen627 : ∀ a b : Equiv.Perm (Fin 5), klein627 a b →
    ordP627 3 a b ∧ ordP627 5 a b := by
  decide +kernel

theorem sign_c5_627 : Equiv.Perm.sign c5_627 = 1 := by decide

variable {Q : Type} [CommGroup Q]

theorem commV_sup_le627 (A B : Subgroup (MulAut Q)) : commV (A ⊔ B) ≤ commV A ⊔ commV B :=
  CFSG.Quasithin.FixVLat.commV_sup_le A B

theorem fixV_sup627 (A B : Subgroup (MulAut Q)) : fixV (A ⊔ B) = fixV A ⊓ fixV B :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq A B

theorem commV_conj627 (A : Subgroup (MulAut Q)) (k : MulAut Q) :
    commV (A.map (MulAut.conj k).toMonoidHom) = (commV A).map k.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq A k

theorem fixV_conj627 (A : Subgroup (MulAut Q)) (k : MulAut Q) :
    fixV (A.map (MulAut.conj k).toMonoidHom) = (fixV A).map k.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq A k

theorem card_sup_eq627 [Finite Q] (H K : Subgroup Q) :
    Nat.card ↥(H ⊔ K) = K.relIndex H * Nat.card K := by
  have : K.Normal := Subgroup.normal_of_isMulCommutative K
  have h1 := Subgroup.relIndex_mul_card K (H ⊔ K)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right] at h1
  exact h1.symm

theorem card_sup_le_mul627 [Finite Q] (H K : Subgroup Q) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  rw [card_sup_eq627]
  refine Nat.mul_le_mul_right _ ?_
  have h1 := Subgroup.relIndex_mul_card K H
  have h2 : 0 < Nat.card ↥(K ⊓ H) := Nat.card_pos
  calc K.relIndex H ≤ K.relIndex H * Nat.card ↥(K ⊓ H) := Nat.le_mul_of_pos_right _ h2
    _ = Nat.card H := h1

theorem card_alt5_627 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  have := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin] at this
  rw [Nat.card_eq_fintype_card]
  have h120 : Nat.factorial 5 = 120 := by decide
  omega

theorem exists_sup_conj_eq627 [Finite (MulAut Q)] {L A : Subgroup (MulAut Q)}
    (φ : ↥L ≃* ↥(alternatingGroup (Fin 5))) (hAL : A ≤ L) (hA4 : Nat.card A = 4)
    (hAab : IsElemAbelian2 A) :
    ∃ k ∈ L, A ⊔ A.map (MulAut.conj k).toMonoidHom = L := by
  classical
  have : Fintype ↥A := Fintype.ofFinite _
  have hcA : Fintype.card ↥A = 4 := by rw [← Nat.card_eq_fintype_card]; exact hA4
  have : Nontrivial ↥A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : ↥A)
  obtain ⟨⟨b, hb⟩, hb1, hba⟩ : ∃ b : ↥A, b ≠ 1 ∧ b ≠ ⟨a, ha⟩ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset ↥A) ⊆ {1, ⟨a, ha⟩} := fun x _ => by
      by_cases hx : x = 1
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (1 : ↥A) {⟨a, ha⟩}
    rw [Finset.card_univ, hcA] at h1
    rw [Finset.card_singleton] at h2
    omega
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hba' : b ≠ a := fun h => hba (Subtype.ext h)
  set f : ↥L →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp φ.toMonoidHom
    with hf
  have hfi : Function.Injective f := fun x y h => φ.injective (Subtype.ext h)
  have hfA : ∀ x : ↥L, Equiv.Perm.sign (f x) = 1 := fun x => (φ x).2
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by
    have := hAab.2 x hx
    rwa [pow_two] at this
  set σ := f ⟨a, hAL ha⟩ with hσ
  set τ := f ⟨b, hAL hb⟩ with hτ
  have hfmul : ∀ x y : ↥L, f (x * y) = f x * f y := fun x y => map_mul f x y
  have hkl : klein627 σ τ := by
    refine ⟨hfA _, hfA _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hσ, ← hfmul, show (⟨a, hAL ha⟩ : ↥L) * ⟨a, hAL ha⟩ = 1 from Subtype.ext (hsq a ha),
        map_one]
    · rw [hτ, ← hfmul, show (⟨b, hAL hb⟩ : ↥L) * ⟨b, hAL hb⟩ = 1 from Subtype.ext (hsq b hb),
        map_one]
    · rw [hσ, hτ, ← hfmul, ← hfmul]
      congr 1
      exact Subtype.ext (hAab.1 a ha b hb)
    · intro h
      exact ha1' (congrArg Subtype.val (hfi (h.trans (map_one f).symm)))
    · intro h
      exact hb1' (congrArg Subtype.val (hfi (h.trans (map_one f).symm)))
    · intro h
      exact hba' (congrArg Subtype.val (hfi h)).symm
  obtain ⟨h3, h5⟩ := fc_a5gen627 σ τ hkl
  set c : ↥(alternatingGroup (Fin 5)) := ⟨c5_627, Equiv.Perm.mem_alternatingGroup.mpr sign_c5_627⟩
    with hc
  set k : MulAut Q := (φ.symm c : MulAut Q) with hk
  have hkL : k ∈ L := (φ.symm c).2
  have hfk : f ⟨k, hkL⟩ = c5_627 := by
    rw [hf, MonoidHom.comp_apply]
    show ((φ (φ.symm c)) : Equiv.Perm (Fin 5)) = c5_627
    rw [MulEquiv.apply_symm_apply]
  set S := A ⊔ A.map (MulAut.conj k).toMonoidHom with hS
  have hBL : A.map (MulAut.conj k).toMonoidHom ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    show k * y * k⁻¹ ∈ L
    exact L.mul_mem (L.mul_mem hkL (hAL hy)) (L.inv_mem hkL)
  have hSL : S ≤ L := sup_le hAL hBL
  have hlift : ∀ x ∈ [σ, τ, σ * τ], ∃ x₀ ∈ A, ∃ h : x₀ ∈ L, f ⟨x₀, h⟩ = x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨a, ha, hAL ha, rfl⟩
    · exact ⟨b, hb, hAL hb, rfl⟩
    · exact ⟨a * b, A.mul_mem ha hb, L.mul_mem (hAL ha) (hAL hb), by rw [hσ, hτ, ← hfmul]; rfl⟩
  have hord : ∀ p : ℕ, p.Prime → ordP627 p σ τ → p ∣ Nat.card S := by
    rintro p hp ⟨x, hx, y, hy, hxp, hx1⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x₀, hx₀A, hx₀L, hx₀⟩ := hlift x hx
    obtain ⟨y₀, hy₀A, hy₀L, hy₀⟩ := hlift y hy
    set g : MulAut Q := x₀ * (k * y₀ * k⁻¹) with hg
    have hgS : g ∈ S := S.mul_mem (Subgroup.mem_sup_left hx₀A)
      (Subgroup.mem_sup_right ⟨y₀, hy₀A, by simp [MulAut.conj_apply]⟩)
    have hgL : g ∈ L := hSL hgS
    have hfg : f ⟨g, hgL⟩ = x * (c5_627 * y * c5_627⁻¹) := by
      have e : (⟨g, hgL⟩ : ↥L) = ⟨x₀, hx₀L⟩ * (⟨k, hkL⟩ * ⟨y₀, hy₀L⟩ * ⟨k, hkL⟩⁻¹) := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, hx₀, hy₀, hfk]
    have hgo : orderOf g = p := by
      have h1 : orderOf (f ⟨g, hgL⟩) = p := by
        rw [hfg]
        exact orderOf_eq_prime hxp hx1
      rw [orderOf_injective f hfi, Subgroup.orderOf_mk] at h1
      exact h1
    rw [← hgo]
    exact Subgroup.orderOf_dvd_natCard S hgS
  have hL60 : Nat.card L = 60 := by rw [Nat.card_congr φ.toEquiv, card_alt5_627]
  have h4 : 4 ∣ Nat.card S := hA4 ▸ Subgroup.card_dvd_of_le le_sup_left
  have h60 : 60 ∣ Nat.card S := by
    have h12 : 12 ∣ Nat.card S :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 (hord 3 Nat.prime_three h3)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12
      (hord 5 (by norm_num) h5)
  refine ⟨k, hkL, Subgroup.eq_of_le_of_card_ge hSL ?_⟩
  rw [hL60]
  exact Nat.le_of_dvd Nat.card_pos h60

theorem natural_sl24627 [Finite Q] [Finite (MulAut Q)] {L A : Subgroup (MulAut Q)}
    (hnat : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 2) (hAL : A ≤ L)
    (hA4 : Nat.card A = 4) (hAab : IsElemAbelian2 A) (hcomm : Nat.card (commV A) ≤ 4)
    (hidx : (fixV A).index ≤ 4) :
    fixV L ⊓ commV L = ⊥ ∧ IsIntDirect (commV L) (fixV L) ⊤ := by
  classical
  obtain ⟨K, _, _, hK4, π, hπ⟩ := hnat
  have hK4' : Nat.card K = 4 := by simpa using hK4
  have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK4
  have e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
  have hSL60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
    rw [SL2Model.card_SL2, hK4']
    norm_num
  obtain ⟨e₁⟩ := A5Model.sl2_four_equiv_alt5 K hK4' hSL60
  set φ : ↥L ≃* ↥(alternatingGroup (Fin 5)) :=
    e.symm.trans ((specialLinearGroupEquivStatedSL 2 K).symm.trans e₁) with hφ
  obtain ⟨k, -, hS⟩ := exists_sup_conj_eq627 φ hAL hA4 hAab
  set B := A.map (MulAut.conj k).toMonoidHom with hB
  have hcL : Nat.card (commV L) ≤ 16 := by
    have h1 : commV L ≤ commV A ⊔ commV B := hS ▸ commV_sup_le627 A B
    have h2 : Nat.card (commV B) = Nat.card (commV A) := by
      rw [hB, commV_conj627, Subgroup.card_map_of_injective k.injective]
    calc Nat.card (commV L) ≤ Nat.card ↥(commV A ⊔ commV B) := Subgroup.card_le_of_le h1
      _ ≤ Nat.card (commV A) * Nat.card (commV B) := card_sup_le_mul627 _ _
      _ ≤ 4 * 4 := Nat.mul_le_mul hcomm (h2 ▸ hcomm)
  obtain ⟨-, -, β, hβs, hβk, -⟩ := natReal627 hπ
  have hker : β.ker = (fixV L ⊓ commV L).subgroupOf (commV L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hcard16 : Nat.card (Multiplicative (Fin 2 → K)) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK4']
    norm_num
  have hcardM : Nat.card ((fixV L ⊓ commV L).subgroupOf (commV L)) * 16 =
      Nat.card (commV L) := by
    have h1 := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hcard16, hker] at h1
    exact h1
  have hZ1 : Nat.card ((fixV L ⊓ commV L).subgroupOf (commV L)) = 1 := by
    have : 0 < Nat.card ((fixV L ⊓ commV L).subgroupOf (commV L)) := Nat.card_pos
    omega
  have hZ : fixV L ⊓ commV L = ⊥ := by
    have h1 := Subgroup.card_eq_one.mp hZ1
    rw [eq_bot_iff]
    intro v hv
    have h2 : (⟨v, hv.2⟩ : ↥(commV L)) ∈ (fixV L ⊓ commV L).subgroupOf (commV L) := hv
    rw [h1, Subgroup.mem_bot] at h2
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h2)
  have hM16 : Nat.card (commV L) = 16 := by rw [← hcardM, hZ1, one_mul]
  have hfL : fixV L = fixV A ⊓ fixV B := hS ▸ fixV_sup627 A B
  have hidxL : (fixV L).index ≤ 16 := by
    have h2 : (fixV B).index = (fixV A).index := by
      rw [hB, fixV_conj627]
      exact Subgroup.index_map_equiv _ k
    calc (fixV L).index ≤ (fixV A).index * (fixV B).index := hfL ▸ Subgroup.index_inf_le
      _ ≤ 4 * 4 := Nat.mul_le_mul hidx (h2 ▸ hidx)
  have hinf : commV L ⊓ fixV L = ⊥ := by rw [inf_comm]; exact hZ
  refine ⟨hZ, ?_, hinf⟩
  have hrel : (fixV L).relIndex (commV L) = 16 := by
    have h1 := Subgroup.relIndex_mul_card (fixV L) (commV L)
    rw [hZ, Subgroup.card_bot, mul_one, hM16] at h1
    exact h1
  have hsup : Nat.card ↥(commV L ⊔ fixV L) = 16 * Nat.card (fixV L) := by
    rw [card_sup_eq627, hrel]
  have hQ := (fixV L).card_mul_index
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (Subgroup.card_le_card_group _)
  rw [hsup, ← hQ, mul_comm]
  exact Nat.mul_le_mul_right _ hidxL

end CFSG.Quasithin.H13
