module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataPhi
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Pair
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Sylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

noncomputable def phiAut : MulAut S4 := autOf phiE

private theorem w183finSp44_autConj_mul (g h : MulAut S4) (A : Subgroup (MulAut S4)) :
    autConj (g * h) A = autConj g (autConj h A) := by
  rw [autConj, autConj, autConj, Subgroup.map_map]
  congr 1

private theorem w183finSp44_le_inn_of_autConj_le (A : Subgroup (MulAut S4)) (k : MulAut S4)
    (h : autConj k A ≤ innAutOf S4) : A ≤ innAutOf S4 := by
  have hmap : (autConj k A).map (MulAut.conj k⁻¹).toMonoidHom ≤ innAutOf S4 := by
    rw [← (conj_innAutOf (k⁻¹)).1]
    exact Subgroup.map_mono h
  have heq : (autConj k A).map (MulAut.conj k⁻¹).toMonoidHom = A := by
    rw [autConj, Subgroup.map_map]
    have hcomp : ((MulAut.conj k⁻¹ : MulAut (MulAut S4)).toMonoidHom.comp
        (MulAut.conj k : MulAut (MulAut S4)).toMonoidHom) = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  rwa [heq] at hmap

private theorem w183finSp44_phiE_mem_Pel : phiE ∈ Pel := by decide +kernel

theorem exists_conj_phi_le_Psub (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A)
    (hout : ¬ A ≤ innAutOf S4) :
    ∃ h : MulAut S4, autConj h A ≤ Psub ∧ phiAut ∈ autConj h A := by
  obtain ⟨k, -, hk⟩ := W183L34.exists_conj_le_isSylowIn (H := ⊤) (A := A) (P := Psub)
    le_top hel.isPGroup Psub_sylow
  have hkA : autConj k A ≤ Psub := hk
  have houtk : ¬ autConj k A ≤ innAutOf S4 :=
    fun h => hout (w183finSp44_le_inn_of_autConj_le A k h)
  obtain ⟨σ, hσA, hσnotinn⟩ := SetLike.not_le_iff_exists.mp houtk
  have hσP : σ ∈ Psub := hkA hσA
  obtain ⟨x, hxPel, hxaut⟩ := (mem_Psub_iff σ).mp hσP
  have hxval : validB x = true := Pel_valid x hxPel
  have hx2ne : x.2 ≠ 0 := fun h0 =>
    hσnotinn (hxaut ▸ (autOf_inner_iff hxval).mpr h0)
  have hσsq : σ * σ = 1 := by
    obtain ⟨a, haA, haσ⟩ := Subgroup.mem_map.mp hσA
    have ha2 : a * a = 1 := by simpa [pow_two] using hel.2 a haA
    rw [← haσ, ← map_mul, ha2, map_one]
  have hxx : gmulE x x = oneE := by
    apply autOf_inj (validB_gmulE hxval hxval) validB_oneE
    rw [autOf_gmulE hxval hxval, autOf_oneE, hxaut]
    exact hσsq
  have hxne : x ≠ oneE := by
    intro h1
    exact hσnotinn (by rw [← hxaut, h1, autOf_oneE]; exact one_mem _)
  have hxinv : x ∈ invs := by
    rw [invs, List.mem_filter]
    exact ⟨hxPel, by simp [hxne, hxx]⟩
  have hx2 : x.2 = 2 := by
    have hlt : x.2 < 4 := (validB_iff.mp hxval).2.2
    have hmod : (x.2 + x.2) % 4 = 0 := by
      simpa [gmulE, oneE] using congrArg Prod.snd hxx
    omega
  obtain ⟨p, hpConj, hpconj⟩ := outer_to_phi x hxinv hx2
  have hpPel : p ∈ Pel := phiConj_mem p hpConj
  have hpval : validB p = true := Pel_valid p hpPel
  have hpP : autOf p ∈ Psub := (mem_Psub_iff (autOf p)).mpr ⟨p, hpPel, rfl⟩
  refine ⟨autOf p * k, ?_, ?_⟩
  · rw [w183finSp44_autConj_mul]
    rintro y ⟨b, hb, rfl⟩
    exact Psub.mul_mem (Psub.mul_mem hpP (hkA hb)) (Psub.inv_mem hpP)
  · rw [w183finSp44_autConj_mul]
    have hmem : autOf p * autOf x * (autOf p)⁻¹ ∈ autConj (autOf p) (autConj k A) :=
      ⟨autOf x, by rw [hxaut]; exact hσA, rfl⟩
    rw [← autOf_conjE hpval hxval, hpconj] at hmem
    exact hmem

theorem exists_codes_of_le_Psub (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A)
    (hP : A ≤ Psub) (hφ : phiAut ∈ A) :
    ∃ K : Finset El, (∀ x ∈ K, x ∈ SClist) ∧ (∀ x ∈ K, gmulE x x = oneE) ∧
      (∀ x ∈ K, ∀ y ∈ K, gmulE x y = gmulE y x) ∧ (∀ x ∈ K, ∀ y ∈ K, gmulE x y ∈ K) ∧
      phiE ∈ K ∧ K.card = Nat.card A ∧ ∀ α : MulAut S4, α ∈ A ↔ ∃ x ∈ K, autOf x = α := by
  classical
  let K : Finset El := Pel.toFinset.filter fun x => autOf x ∈ A
  have hmem : ∀ x, x ∈ K ↔ x ∈ Pel ∧ autOf x ∈ A := by
    intro x
    dsimp only [K]
    rw [Finset.mem_filter, List.mem_toFinset]
  have hKP : ∀ x ∈ K, x ∈ Pel := fun x hx => (hmem x).mp hx |>.1
  have hKA : ∀ x ∈ K, autOf x ∈ A := fun x hx => (hmem x).mp hx |>.2
  have hφP : phiE ∈ Pel := w183finSp44_phiE_mem_Pel
  have hφK : phiE ∈ K := (hmem phiE).mpr ⟨hφP, hφ⟩
  refine ⟨K, ?_, ?_, ?_, ?_, hφK, ?_, ?_⟩
  · intro x hx
    apply sc_of_commute x (hKP x hx)
    have hxval : validB x = true := Pel_valid x (hKP x hx)
    have hpval : validB phiE = true := Pel_valid phiE hφP
    apply autOf_inj (validB_gmulE hxval hpval) (validB_gmulE hpval hxval)
    rw [autOf_gmulE hxval hpval, autOf_gmulE hpval hxval]
    haveI : IsMulCommutative ↥A := hel.1
    exact congrArg Subtype.val (mul_comm' (⟨autOf x, hKA x hx⟩ : A) ⟨phiAut, hφ⟩)
  · intro x hx
    have hxval : validB x = true := Pel_valid x (hKP x hx)
    apply autOf_inj (validB_gmulE hxval hxval) validB_oneE
    rw [autOf_gmulE hxval hxval, autOf_oneE]
    simpa [pow_two] using hel.2 (autOf x) (hKA x hx)
  · intro x hx y hy
    have hxval : validB x = true := Pel_valid x (hKP x hx)
    have hyval : validB y = true := Pel_valid y (hKP y hy)
    apply autOf_inj (validB_gmulE hxval hyval) (validB_gmulE hyval hxval)
    rw [autOf_gmulE hxval hyval, autOf_gmulE hyval hxval]
    haveI : IsMulCommutative ↥A := hel.1
    exact congrArg Subtype.val (mul_comm' (⟨autOf x, hKA x hx⟩ : A) ⟨autOf y, hKA y hy⟩)
  · intro x hx y hy
    rw [hmem]
    refine ⟨Pel_closed x (hKP x hx) y (hKP y hy), ?_⟩
    rw [autOf_gmulE (Pel_valid x (hKP x hx)) (Pel_valid y (hKP y hy))]
    exact A.mul_mem (hKA x hx) (hKA y hy)
  · let f : ↥K → ↥A := fun x => ⟨autOf x.1, (hmem x.1).mp x.2 |>.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact autOf_inj (Pel_valid x.1 (hKP x.1 x.2)) (Pel_valid y.1 (hKP y.1 y.2))
          (congrArg Subtype.val hxy)
      · intro β
        obtain ⟨x, hxPel, hxaut⟩ := (mem_Psub_iff β.1).mp (hP β.2)
        refine ⟨⟨x, (hmem x).mpr ⟨hxPel, ?_⟩⟩, ?_⟩
        · rw [hxaut]; exact β.2
        · apply Subtype.ext; exact hxaut
    have hKcard : Nat.card ↥K = K.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hbij : Nat.card ↥K = Nat.card ↥A := Nat.card_congr (Equiv.ofBijective f hf)
    rw [← hKcard]
    exact hbij
  · intro α
    constructor
    · intro hα
      obtain ⟨x, hxPel, hxaut⟩ := (mem_Psub_iff α).mp (hP hα)
      exact ⟨x, (hmem x).mpr ⟨hxPel, by rw [hxaut]; exact hα⟩, hxaut⟩
    · rintro ⟨x, hxK, rfl⟩
      exact hKA x hxK

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
