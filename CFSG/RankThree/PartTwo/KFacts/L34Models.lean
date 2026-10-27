module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.RankThree.PartTwo.Sec4

variable {k : Type*} [Field k]

section Heis

theorem not_isMulCommutative_qSub (hk : Nat.card k = 4) :
    ¬ IsMulCommutative (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)) := by
  intro h
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hc := h.is_comm.comm (⟨hSL u, hSL_mem_qSub⟩ : qSub) ⟨rSL, rSL_mem_qSub⟩
  have hc' : hSL u * rSL = rSL * hSL u := congrArg Subtype.val hc
  have h1 : hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = 1 := by rw [hc']; group
  rw [hSL_commutator hk, inv_eq_one] at h1
  have h0 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
    (g : Matrix (Fin 3) (Fin 3) k)) h1) 0) 0
  simp only [zSL, coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h0
  simp at h0
  exact hu h0

theorem qSub_pow_three (hk : Nat.card k = 4)
    (x : (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k))) : x ^ 3 = 1 := by
  obtain ⟨g, hg⟩ := x
  rw [← SetLike.mem_coe, coe_qSub] at hg
  obtain ⟨y, rfl⟩ := hg
  exact Subtype.ext (qElt_pow_three hk y)

theorem isHeisThree_of_mulEquiv {P : Type} [Group P] {k : Type*} [Field k]
    (hk : Nat.card k = 4)
    (e : P ≃* (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k))) : IsHeisThree P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card P = 27 := by rw [Nat.card_congr e.toEquiv, card_qSub hk]
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hexp : ∀ x : P, x ^ 3 = 1 := fun x =>
    e.injective (by rw [map_pow, qSub_pow_three hk, map_one])
  have hnc : ¬ IsMulCommutative P := fun h => not_isMulCommutative_qSub hk
    ⟨⟨fun a b => e.symm.injective (by
      rw [map_mul, map_mul]
      exact h.is_comm.comm _ _)⟩⟩
  have hP : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  refine ⟨CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP hexp
    (by rw [hcard]; norm_num) hnc, hcard, ?_⟩
  have hdvd : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a = 1 := by
      have := Monoid.pow_exponent_eq_one a
      rwa [h, pow_one] at this
    have hb : b = 1 := by
      have := Monoid.pow_exponent_eq_one b
      rwa [h, pow_one] at this
    rw [ha, hb]
  · exact h

end Heis

section Preimage

theorem exists_comap_proj_eq (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) k,
      E.comap (proj 3 k) = (qSub (k := k)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨x, rfl⟩ := exists_eq_map_conj_eZero hk hE
  obtain ⟨g, rfl⟩ := proj_surjective 3 k x
  refine ⟨g, ?_⟩
  have hq : ∀ z, z ∈ (qSub (k := k)) ↔ proj 3 k z ∈ eZero k := by
    intro z
    have h := Subgroup.comap_map_eq_self (f := proj 3 k) (H := qSub (k := k))
      (by rw [ker_proj]; exact scalars_le_qSub)
    rw [← h]
    rfl
  ext y
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨e, he, hey⟩
    refine ⟨g⁻¹ * y * g, (hq _).mpr ?_, by group⟩
    rw [map_mul, map_mul, map_inv, ← hey]
    convert he using 1
    group
  · rintro ⟨z, hz, rfl⟩
    refine ⟨proj 3 k z, (hq z).mp hz, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem isHeisThree_comap_proj {k : Type} [Field k] (hk : Nat.card k = 4)
    {E : Subgroup (projectiveSL 3 k)} (hE : Nat.card E = 9) :
    IsHeisThree (E.comap (proj 3 k)) := by
  obtain ⟨g, hg⟩ := exists_comap_proj_eq hk hE
  rw [hg]
  exact isHeisThree_of_mulEquiv hk
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm

theorem scalars_le_of_card_eq_nine (hk : Nat.card k = 4)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)} (hE : Nat.card E = 9) :
    scalars 3 k ≤ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 := card_scalars hk (k := k)
  by_contra hZE
  have hinf : ∀ z ∈ E, z ∈ scalars 3 k → z = 1 := by
    intro z hzE hzZ
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : scalars 3 k ⊓ E ≤ scalars 3 k)
    rw [hZ3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · have := Subgroup.eq_bot_of_card_eq _ h
      have hz : z ∈ scalars 3 k ⊓ E := ⟨hzZ, hzE⟩
      rw [this] at hz
      exact hz
    · exfalso
      apply hZE
      have : Finite (scalars 3 k) := Nat.finite_of_card_ne_zero (by rw [hZ3]; norm_num)
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : scalars 3 k ⊓ E ≤ scalars 3 k)
        (by rw [h, hZ3])
      rw [← heq]
      exact inf_le_right
  have hinj : Function.Injective ((proj 3 k).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    exact Subtype.ext (hinf z z.2 (proj_eq_one_iff.mp hz))
  have hcard : Nat.card (E.map (proj 3 k)) = 9 := by
    rw [← hE, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  obtain ⟨g, hg⟩ := exists_comap_proj_eq hk hcard
  have hEc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (show Nat.card E = 3 ^ 2 by rw [hE]; norm_num)).is_comm.comm
  have hdec : ∀ y ∈ (E.map (proj 3 k)).comap (proj 3 k), ∃ e ∈ E, ∃ z ∈ scalars 3 k, y = e * z := by
    rintro y ⟨e, he, hey⟩
    refine ⟨e, he, e⁻¹ * y, proj_eq_one_iff.mp ?_, by group⟩
    rw [map_mul, map_inv, hey, inv_mul_cancel]
  have hcomm : ∀ a ∈ (E.map (proj 3 k)).comap (proj 3 k),
      ∀ b ∈ (E.map (proj 3 k)).comap (proj 3 k), a * b = b * a := by
    intro a ha b hb
    obtain ⟨e₁, he₁, z₁, hz₁, rfl⟩ := hdec a ha
    obtain ⟨e₂, he₂, z₂, hz₂, rfl⟩ := hdec b hb
    have c₁ := Subgroup.mem_center_iff.mp (scalars_le_center 3 k hz₁)
    have c₂ := Subgroup.mem_center_iff.mp (scalars_le_center 3 k hz₂)
    have hee : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val (hEc ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
    calc e₁ * z₁ * (e₂ * z₂) = e₁ * (z₁ * e₂) * z₂ := by group
      _ = e₁ * (e₂ * z₁) * z₂ := by rw [c₁ e₂]
      _ = (e₁ * e₂) * (z₁ * z₂) := by group
      _ = (e₂ * e₁) * (z₂ * z₁) := by rw [hee, c₂ z₁]
      _ = e₂ * (e₁ * z₂) * z₁ := by group
      _ = e₂ * (z₂ * e₁) * z₁ := by rw [c₂ e₁]
      _ = e₂ * z₂ * (e₁ * z₁) := by group
  apply not_isMulCommutative_qSub hk
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : (MulAut.conj g) a ∈ (E.map (proj 3 k)).comap (proj 3 k) := by
    rw [hg]
    exact ⟨a, a.2, rfl⟩
  have hb : (MulAut.conj g) b ∈ (E.map (proj 3 k)).comap (proj 3 k) := by
    rw [hg]
    exact ⟨b, b.2, rfl⟩
  have h := hcomm _ ha _ hb
  rw [← map_mul, ← map_mul] at h
  exact (MulAut.conj g).injective h

end Preimage

section Model

theorem isZ3L34OrHeisSL34_prod :
    IsZ3L34OrHeisSL34
      (Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
  Or.inl ⟨MulEquiv.refl _⟩

@[expose] noncomputable def scalarDiag (k : Type*) [Field k] :
    scalars 3 k →* ↥(qSub (k := k)) ×
      Matrix.SpecialLinearGroup (Fin 3) k where
  toFun z := (⟨z, scalars_le_qSub z.2⟩, (z : Matrix.SpecialLinearGroup (Fin 3) k)⁻¹)
  map_one' := by
    refine Prod.ext (Subtype.ext rfl) ?_
    simp
  map_mul' z w := by
    refine Prod.ext (Subtype.ext rfl) ?_
    have hw := (Subgroup.mem_center_iff.mp (scalars_le_center 3 k w.2)) (z : _)
    simp only [Subgroup.coe_mul, Prod.snd_mul, _root_.mul_inv_rev]
    have hw' := (Subgroup.mem_center_iff.mp (scalars_le_center 3 k (inv_mem w.2)))
      ((z : Matrix.SpecialLinearGroup (Fin 3) k)⁻¹)
    exact hw'.symm

@[expose] noncomputable def heisDiag (k : Type*) [Field k] :
    Subgroup (↥(qSub (k := k)) ×
      Matrix.SpecialLinearGroup (Fin 3) k) :=
  (scalarDiag k).range

theorem heisDiag_le_center :
    heisDiag k ≤ Subgroup.center (↥(qSub (k := k)) ×
      Matrix.SpecialLinearGroup (Fin 3) k) := by
  rintro _ ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  have hz := Subgroup.mem_center_iff.mp (scalars_le_center 3 k z.2)
  have hzi := Subgroup.mem_center_iff.mp (scalars_le_center 3 k (inv_mem z.2))
  refine Prod.ext (Subtype.ext (hz _)) (hzi _)

instance heisDiag_normal : (heisDiag k).Normal :=
  Subgroup.normal_of_le_center heisDiag_le_center

abbrev HeisSL (k : Type*) [Field k] : Type _ :=
  (↥(qSub (k := k)) ×
    Matrix.SpecialLinearGroup (Fin 3) k) ⧸ heisDiag k

@[expose] noncomputable def heisU (k : Type*) [Field k] :
    ↥(qSub (k := k)) →* HeisSL k :=
  (QuotientGroup.mk' (heisDiag k)).comp (MonoidHom.inl _ _)

@[expose] noncomputable def heisV (k : Type*) [Field k] :
    Matrix.SpecialLinearGroup (Fin 3) k →* HeisSL k :=
  (QuotientGroup.mk' (heisDiag k)).comp (MonoidHom.inr _ _)

theorem heisU_injective : Function.Injective (heisU k) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hmem : ((q, 1) : ↥(qSub (k := k)) ×
      Matrix.SpecialLinearGroup (Fin 3) k) ∈ heisDiag k :=
    (QuotientGroup.eq_one_iff _).mp hq
  obtain ⟨z, hz⟩ := hmem
  have h2 := congrArg Prod.snd hz
  have h1 := congrArg Prod.fst hz
  simp only [scalarDiag, MonoidHom.coe_mk, OneHom.coe_mk, inv_eq_one] at h1 h2
  rw [← h1]
  exact Subtype.ext h2

theorem heisV_injective : Function.Injective (heisV k) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hmem : ((1, s) : ↥(qSub (k := k)) ×
      Matrix.SpecialLinearGroup (Fin 3) k) ∈ heisDiag k :=
    (QuotientGroup.eq_one_iff _).mp hs
  obtain ⟨z, hz⟩ := hmem
  have h1 := congrArg (fun p => ((p.1 : Matrix.SpecialLinearGroup (Fin 3) k))) hz
  have h2 := congrArg Prod.snd hz
  simp only [scalarDiag, MonoidHom.coe_mk, OneHom.coe_mk] at h1 h2
  rw [← h2, h1]
  simp

theorem heisU_mul_heisV (q : ↥(qSub (k := k)))
    (s : Matrix.SpecialLinearGroup (Fin 3) k) : heisU k q * heisV k s = heisV k s * heisU k q := by
  simp only [heisU, heisV, MonoidHom.coe_comp, Function.comp_apply, ← map_mul]
  congr 1
  ext <;> simp

theorem heisU_scalar {z : Matrix.SpecialLinearGroup (Fin 3) k} (hz : z ∈ scalars 3 k) :
    heisU k ⟨z, scalars_le_qSub hz⟩ = heisV k z := by
  simp only [heisU, heisV, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  refine ⟨⟨z, hz⟩⁻¹, Prod.ext (Subtype.ext ?_) ?_⟩ <;> simp [scalarDiag]

theorem range_heisU_inf_range_heisV :
    (heisU k).range ⊓ (heisV k).range =
      ((scalars 3 k).subgroupOf (qSub (k := k))).map
        (heisU k) := by
  apply le_antisymm
  · rintro x ⟨⟨q, rfl⟩, ⟨s, hs⟩⟩
    have h : heisU k q * (heisV k s)⁻¹ = 1 := by rw [hs, mul_inv_cancel]
    simp only [heisU, heisV, MonoidHom.coe_comp, Function.comp_apply, ← map_inv,
      ← map_mul] at h
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp h
    have h1 := congrArg Prod.fst hz
    simp only [scalarDiag, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_mul, MonoidHom.inl_apply,
      MonoidHom.inr_apply, mul_one] at h1
    refine ⟨q, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← h1]
    exact z.2
  · rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, rfl⟩, ⟨q, ?_⟩⟩
    exact (heisU_scalar (k := k) hq).symm

theorem card_range_heisU_inf_range_heisV (hk : Nat.card k = 4) :
    Nat.card ((heisU k).range ⊓ (heisV k).range : Subgroup (HeisSL k)) = 3 := by
  rw [range_heisU_inf_range_heisV, Subgroup.card_map_of_injective heisU_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe scalars_le_qSub).toEquiv, card_scalars hk]

theorem range_heisU_sup_range_heisV : (heisU k).range ⊔ (heisV k).range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨q, s⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have : (QuotientGroup.mk (q, s) : HeisSL k) = heisU k q * heisV k s := by
    simp only [heisU, heisV, MonoidHom.coe_comp, Function.comp_apply, ← map_mul]
    congr 1
    ext <;> simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨q, rfl⟩) (Subgroup.mem_sup_right ⟨s, rfl⟩)

theorem isHeisSLThreeFour_heisSL : IsHeisSLThreeFour (HeisSL (GaloisField 2 2)) := by
  have hk := card_galoisField_two_two
  refine ⟨(heisU _).range, (heisV _).range, range_heisU_sup_range_heisV, ?_, ?_, ?_,
    card_range_heisU_inf_range_heisV hk⟩
  · rintro _ ⟨q, rfl⟩ _ ⟨s, rfl⟩
    exact heisU_mul_heisV q s
  · exact isHeisThree_of_mulEquiv hk (MonoidHom.ofInjective heisU_injective).symm
  · exact ⟨(MonoidHom.ofInjective heisV_injective).symm⟩

theorem isZ3L34OrHeisSL34_heisSL : IsZ3L34OrHeisSL34 (HeisSL (GaloisField 2 2)) :=
  Or.inr isHeisSLThreeFour_heisSL

end Model


end CFSG.RankThree.PartTwo.KFacts.L34
