module

public import CFSG.Quasithin.Background.A318PC1

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.Asc83Table Matrix

section Linear

variable {K : Type} [Field K]

@[expose] noncomputable def matEnd (K : Type) [Field K] :
    GL (Fin 3) K →* Module.End K (Fin 3 → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Module.End K (Fin 3 → K)).toMonoidHom.comp
    (Units.coeHom _)

theorem matEnd_apply (g : GL (Fin 3) K) (v : Fin 3 → K) :
    matEnd K g v = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v :=
  Matrix.toLin'_apply _ _

theorem false_of_irreducible_of_normalizes [Finite K] [CharP K 2] {P : Subgroup (GL (Fin 3) K)}
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) {y : GL (Fin 3) K} (hyP : ∀ g ∈ P, y⁻¹ * g * y ∈ P)
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {v | ∀ g ∈ P, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
      add_mem' := fun {a b} ha hb g hg => by
        rw [Matrix.mulVec_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv g hg => by
        rw [Matrix.mulVec_smul, hv g hg] }
  have hmemW : ∀ v, v ∈ W ↔ ∀ g ∈ P, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun v => Iff.rfl
  have hWy : ∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro v hv g hg
    have h1 := (hmemW v).mp hv _ (hyP g hg)
    have h2 : (y : Matrix (Fin 3) (Fin 3) K) *
        ((y⁻¹ * g * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    calc (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = ((g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
      _ = (y : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((y⁻¹ * g * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, h2]
      _ = (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by rw [h1]
  rcases hirr W hWy with h | h
  · obtain ⟨v, hv0, hv⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero (matEnd K) 2 P hP
    have hvW : v ∈ W := fun g hg => by rw [← matEnd_apply]; exact hv g hg
    rw [h] at hvW
    exact hv0 ((Submodule.mem_bot K).mp hvW)
  · apply hP1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W := by rw [h]; trivial
    rw [Matrix.toLin'_apply, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    exact (hmemW v).mp hv g hg

theorem two_dvd_card_slPi [Finite K] [CharP K 2] {π : Bool} {f : ℕ}
    (hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) :
    2 ∣ Nat.card ↥(slPi π 3 (2 ^ f) K) := by
  classical
  set P : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hP
  have hPP : P * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_three]
  let g : GL (Fin 3) K := ⟨P, P, hPP, hPP⟩
  have hdet : P.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [hP, CharTwo.neg_eq]
  have hg : g ∈ slPi π 3 (2 ^ f) K := by
    rw [CFSG.RankThree.PartTwo.Sec4.mem_slPi_iff hπ]
    refine ⟨?_, hdet⟩
    cases π
    · rw [CFSG.RankThree.PartTwo.Sec4.mem_glPi_false (hπ rfl)]
      have hmap : P.map (hπ rfl).bar = P := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hP]
      have htr : Pᵀ = P := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hP]
      change (P.map (hπ rfl).bar)ᵀ * P = 1
      rw [hmap, htr, hPP]
    · exact CFSG.RankThree.PartTwo.Sec4.mem_glPi_true _ g
  set s : ↥(slPi π 3 (2 ^ f) K) := ⟨g, hg⟩
  have hs2 : s ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq]
    exact hPP
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg (fun y : ↥(slPi π 3 (2 ^ f) K) =>
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [s, g, hP] at this
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have h := orderOf_dvd_natCard s
  rwa [hord] at h

end Linear

section Group

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal]

omit hSn in
theorem two_le_pRank_of_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (e : ↥S ≃* slPi π 3 (p ^ f) K) :
    2 ≤ CFSG.Open.pRank 3 S := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, a, b, -, -, -, ha3, hb3, hab, ha1, hb1, hba, hba2⟩ :=
    A318P.exists_E9_slPi hK hq hτ hτ1 (one_mem (glPi π 3 (p ^ f) K))
  have hinj : ∀ {u v : slPi π 3 (p ^ f) K}, ((e.symm u : ↥S) : X) = ((e.symm v : ↥S) : X) →
      u = v := fun h => e.symm.injective (Subtype.ext h)
  have ha'3 : ((e.symm a : ↥S) : X) ^ 3 = 1 := by
    have : (e.symm a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    exact congrArg Subtype.val this
  have hb'3 : ((e.symm b : ↥S) : X) ^ 3 = 1 := by
    have : (e.symm b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    exact congrArg Subtype.val this
  have hab' : Commute ((e.symm a : ↥S) : X) ((e.symm b : ↥S) : X) := by
    have : e.symm a * e.symm b = e.symm b * e.symm a := by rw [← map_mul, hab, map_mul]
    exact congrArg Subtype.val this
  have h1 : ((e.symm 1 : ↥S) : X) = 1 := by rw [map_one]; rfl
  have ha'1 : ((e.symm a : ↥S) : X) ≠ 1 := fun h => ha1 (hinj (h.trans h1.symm))
  have hb'1 : ((e.symm b : ↥S) : X) ≠ 1 := fun h => hb1 (hinj (h.trans h1.symm))
  have hba' : ((e.symm b : ↥S) : X) ≠ ((e.symm a : ↥S) : X) := fun h => hba (hinj h)
  have hba2' : ((e.symm b : ↥S) : X) ≠ ((e.symm a : ↥S) : X) ^ 2 := fun h => hba2 (hinj (by
    rw [h, map_pow]
    rfl))
  let E : E9Basis X := E9Basis.ofNe ha'3 hb'3 hab' ha'1 hb'1 hba' hba2'
  have hES : E.sub ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    rintro _ (rfl | rfl)
    exacts [(e.symm a).2, (e.symm b).2]
  have hEel : CFSG.Open.IsElemAbelian 3 E.sub :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 E.isElementaryAbelian
  have hEcard : Nat.card E.sub = 3 ^ 2 := by
    rw [E.card]
    norm_num
  exact CFSG.SectionRank.le_pRank (by norm_num) hES hEel hEcard

theorem false_of_normalizes_slPi
    (hQ : CFSG.IsQuasisimple ↥S) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {π : Bool}
    {f : ℕ} {K : Type} [Field K] (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (hq2 : 2 < 2 ^ f) (e : ↥S ≃* slPi π 3 (2 ^ f) K) {x : X} (hx : orderOf x = 3)
    (hxS : x ∉ S) {P : Subgroup X} (hPS : P ≤ S) (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    (hxP : ∀ g ∈ P, x * g * x⁻¹ ∈ P) : False := by
  classical
  have : Finite K := hK.finite
  have hKc : Nat.card K = 2 ^ (cond π f (2 * f)) := by
    rw [hK.card]
    cases π
    · simp [piCard, ← pow_mul, mul_comm]
    · simp [piCard]
  have hfpos : 1 ≤ cond π f (2 * f) := by
    have := hK.one_le
    cases π <;> simp <;> omega
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hfpos hKc
  obtain ⟨y, hy, -, hirr, -⟩ :=
    A318P.central_type_iii hQ (two_le_pRank_of_slPi hK hq e) hX hK hq hq2 e hx hxS
  set P' : Subgroup (GL (Fin 3) K) :=
    ((P.subgroupOf S).map e.toMonoidHom).map (slPi π 3 (2 ^ f) K).subtype with hP'
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxinv : x ^ 2 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx3
  have hxP' : ∀ g ∈ P, x⁻¹ * g * x ∈ P := by
    intro g hg
    have e1 : x * (x * g * x⁻¹) * x⁻¹ = x⁻¹ * g * x := by
      calc x * (x * g * x⁻¹) * x⁻¹ = x ^ 2 * g * (x ^ 2)⁻¹ := by rw [sq]; group
        _ = x⁻¹ * g * x := by rw [hxinv, inv_inv]
    rw [← e1]
    exact hxP _ (hxP g hg)
  refine false_of_irreducible_of_normalizes (P := P') ?_ ?_ (y := y) ?_ hirr
  · have h1 : IsPGroup 2 ↥(P.subgroupOf S) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
    exact (h1.map e.toMonoidHom).map _
  · intro hbot
    apply hP1
    rw [eq_bot_iff]
    intro g hg
    have hgP' : (((e ⟨g, hPS hg⟩ : slPi π 3 (2 ^ f) K)) : GL (Fin 3) K) ∈ P' :=
      ⟨e ⟨g, hPS hg⟩, ⟨⟨g, hPS hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hgP'
    have h2 : e ⟨g, hPS hg⟩ = 1 := Subtype.ext hgP'
    rw [MulEquiv.map_eq_one_iff] at h2
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hsP : (s : X) ∈ P := Subgroup.mem_subgroupOf.mp hs
    have hsS : x⁻¹ * (s : X) * x ∈ S := by
      have h1 := hSn.conj_mem _ s.2 x⁻¹
      rwa [inv_inv] at h1
    have hkey := hy.2 (e ⟨x⁻¹ * s * x, hsS⟩)
    rw [coe_slAct_eq] at hkey
    have hsimp : (⟨x * ((e.symm (e ⟨x⁻¹ * s * x, hsS⟩) : ↥S) : X) * x⁻¹,
        hSn.conj_mem _ (e.symm (e ⟨x⁻¹ * s * x, hsS⟩)).2 x⟩ : ↥S) = s := by
      apply Subtype.ext
      rw [MulEquiv.symm_apply_apply]
      group
    rw [hsimp] at hkey
    refine ⟨e ⟨x⁻¹ * s * x, hsS⟩, ⟨⟨x⁻¹ * s * x, hsS⟩,
      Subgroup.mem_subgroupOf.mpr (hxP' _ hsP), rfl⟩, ?_⟩
    change ((e ⟨x⁻¹ * s * x, hsS⟩ : slPi π 3 (2 ^ f) K) : GL (Fin 3) K) =
      y⁻¹ * ((e s : slPi π 3 (2 ^ f) K) : GL (Fin 3) K) * y
    rw [hkey]
    group

end Group

end CFSG.Quasithin.H13.A6.A6S20
