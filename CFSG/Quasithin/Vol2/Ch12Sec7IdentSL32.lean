module

public import CFSG.LargeExtraspecial.DW3Split
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.LargeExtraspecial.DW.W3 Subgroup
open scoped Pointwise

@[expose] noncomputable def slEquivGL :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      have hg : g ∈ (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* GL (Fin 3) (ZMod 2)).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
        exact Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hg
      exact ⟨y, hy⟩⟩

theorem card_sl32 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_congr slEquivGL.toEquiv, card_GL_three]

abbrev dihElt (p : Fin 2 × Fin 4) : GL (Fin 3) (ZMod 2) :=
  sU ^ (p.1 : ℕ) * (sU * tU) ^ (p.2 : ℕ)

theorem dihElt_mul : ∀ p q : Fin 2 × Fin 4, ∃ r : Fin 2 × Fin 4,
    dihElt r = dihElt p * dihElt q := by
  decide

theorem dihElt_inv : ∀ p : Fin 2 × Fin 4, ∃ r : Fin 2 × Fin 4, dihElt r = (dihElt p)⁻¹ := by
  decide

@[expose] def dih : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := Set.range dihElt
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    obtain ⟨r, hr⟩ := dihElt_mul p q
    exact ⟨r, hr⟩
  one_mem' := ⟨(0, 0), by simp [dihElt]⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨r, hr⟩ := dihElt_inv p
    exact ⟨r, hr⟩

theorem dihElt_injective : Function.Injective dihElt := by
  rintro ⟨b, k⟩ ⟨b', k'⟩ h
  obtain ⟨rfl, rfl⟩ := sU_pow_mul_injective b b' k k' h
  rfl

theorem card_dih : Nat.card dih = 8 := by
  have h : Nat.card dih = Nat.card (Set.range dihElt) := rfl
  rw [h, Nat.card_range_of_injective dihElt_injective, Nat.card_eq_fintype_card]
  simp

theorem sU_mem_dih : sU ∈ dih := ⟨(1, 0), by simp [dihElt]⟩

theorem tU_mem_dih : tU ∈ dih := ⟨(1, 1), by
  simp only [dihElt, Fin.val_one, Fin.isValue, pow_one]
  rw [← mul_assoc, sU_mul_self, one_mul]⟩

theorem sU_mul_tU_ne : sU * tU ≠ tU * sU := by decide

theorem dih_isPGroup : IsPGroup 2 dih := by
  refine IsPGroup.iff_card.2 ⟨3, ?_⟩
  rw [card_dih]
  norm_num

theorem dih_index_not_dvd : ¬ 2 ∣ dih.index := by
  have h := Subgroup.index_mul_card (H := dih)
  rw [card_dih, card_GL_three] at h
  omega

theorem gl32_card_ne_eight (E : Subgroup (GL (Fin 3) (ZMod 2))) (hE : IsElemAbelian 2 E) :
    Nat.card E ≠ 8 := by
  intro h8
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Sylow 2 (GL (Fin 3) (ZMod 2)) := IsPGroup.toSylow dih_isPGroup dih_index_not_dvd
  have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) D Q
  have hQD : (Q : Subgroup (GL (Fin 3) (ZMod 2))) = MulAut.conj g • dih := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hQcard : Nat.card Q = 8 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have hmul := Subgroup.card_mul_index (H := (Q : Subgroup (GL (Fin 3) (ZMod 2))))
    rw [card_GL_three, hn] at hmul
    have hle : Nat.card E ≤ Nat.card Q := Subgroup.card_le_of_le hEQ
    rw [h8, hn] at hle
    have hn3 : n ≤ 3 := by
      by_contra hn4
      have h16 : 2 ^ 4 ∣ 2 ^ n * Q.index := Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
      rw [hmul] at h16
      norm_num at h16
    have hn3' : n = 3 := by
      interval_cases n <;> first | rfl | (norm_num at hle)
    rw [hn, hn3']
    norm_num
  have hEQeq : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (by rw [hQcard, h8])
  have hsQ : MulAut.conj g sU ∈ (Q : Subgroup (GL (Fin 3) (ZMod 2))) := by
    rw [hQD]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ sU_mem_dih
  have htQ : MulAut.conj g tU ∈ (Q : Subgroup (GL (Fin 3) (ZMod 2))) := by
    rw [hQD]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ tU_mem_dih
  have hcomm := hE.1.is_comm.comm (⟨MulAut.conj g sU, hEQeq ▸ hsQ⟩ : E)
    ⟨MulAut.conj g tU, hEQeq ▸ htQ⟩
  have hcomm' : MulAut.conj g sU * MulAut.conj g tU = MulAut.conj g tU * MulAut.conj g sU :=
    congrArg Subtype.val hcomm
  have hconj : MulAut.conj g (sU * tU) = MulAut.conj g (tU * sU) := by
    rw [map_mul, map_mul]
    exact hcomm'
  exact sU_mul_tU_ne ((MulAut.conj g).injective hconj)

theorem sl32_card_le_four (R : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hR : IsElemAbelian 2 R) : Nat.card R ≤ 4 := by
  have hRp : IsPGroup 2 R := fun g => ⟨1, Subtype.ext (by simpa using hR.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hRp
  have hdvd : Nat.card R ∣ 168 := by
    rw [← card_sl32]
    exact Subgroup.card_subgroup_dvd_card R
  have hle3 : n ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ Nat.card R := by
      rw [hn]
      exact pow_dvd_pow 2 (by omega)
    have := dvd_trans h16 hdvd
    norm_num at this
  have hne3 : n ≠ 3 := by
    rintro rfl
    have hcomm : ∀ x ∈ R.map slEquivGL.toMonoidHom, ∀ y ∈ R.map slEquivGL.toMonoidHom,
        x * y = y * x := by
      rintro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      have hab : a * b = b * a := congrArg Subtype.val (hR.1.is_comm.comm
        (⟨a, ha⟩ : R) ⟨b, hb⟩)
      rw [← map_mul, ← map_mul, hab]
    have hmap : IsElemAbelian 2 (R.map slEquivGL.toMonoidHom) := by
      refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
      rintro x ⟨a, ha, rfl⟩
      rw [← map_pow, hR.2 a ha, map_one]
    have hcard : Nat.card (R.map slEquivGL.toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective (f := slEquivGL.toMonoidHom) slEquivGL.injective
    apply gl32_card_ne_eight _ hmap
    rw [hcard, hn]
    norm_num
  rw [hn]
  interval_cases n <;> first | exact absurd rfl hne3 | norm_num

end CFSG.Quasithin.H13.I1277
