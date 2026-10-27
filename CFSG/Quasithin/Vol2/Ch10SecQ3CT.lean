module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CS

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conj_mem_autOn {V L : Subgroup G} {z : G} (hzN : z ∈ Subgroup.normalizer (V : Set G))
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) {φ : MulAut ↥V} (hφ : φ ∈ autOn L V) :
    conjAct V ⟨z, hzN⟩ * φ * (conjAct V ⟨z, hzN⟩)⁻¹ ∈ autOn L V := by
  obtain ⟨ℓ, hℓL, rfl⟩ := SecA.mem_autOn_iff'.mp hφ
  refine SecA.mem_autOn_iff'.mpr ⟨⟨z, hzN⟩ * ℓ * ⟨z, hzN⟩⁻¹, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hzL _).mp hℓL
    simpa using this
  · rw [map_mul, map_mul, map_inv]

omit [Finite G] in
theorem commutator_fix_of_torus [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n) (c : SecA.NatCoord T L I F)
    {z : G} (hzN : z ∈ Subgroup.normalizer (fsuUL T L I : Set G))
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hzr : z ^ r = 1) (hrq : ¬ r ∣ 2 ^ n - 1) {d : G}
    (hdN : d ∈ Subgroup.normalizer (fsuUL T L I : Set G)) (hzd : z * d = d * z) {μ : Fˣ}
    (hμ : ∀ y : Fˣ, y ∈ Subgroup.zpowers μ) {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hd : conjAct (fsuUL T L I) ⟨d, hdN⟩ =
      ((c.eρ (x * dU μ * x⁻¹) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))) :
    ∀ l ∈ L, ∀ w ∈ fsuUL T L I,
      (z * l * z⁻¹ * l⁻¹) * w * (z * l * z⁻¹ * l⁻¹)⁻¹ = w := by
  set V := fsuUL T L I with hV
  set A := conjAct V ⟨z, hzN⟩ with hA
  have hzN' : z⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hzN
  have hzL' : z⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hzL
  have hAinv : A⁻¹ = conjAct V ⟨z⁻¹, hzN'⟩ := by rw [hA, ← map_inv]; rfl
  have hmap : (autOn L V).map ((MulAut.conj A : MulAut (MulAut ↥V)) : MulAut ↥V →* MulAut ↥V) =
      autOn L V := by
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      exact conj_mem_autOn hzN hzL hφ
    · intro φ hφ
      refine ⟨A⁻¹ * φ * A, ?_, ?_⟩
      · have h := conj_mem_autOn hzN' hzL' hφ
        rwa [← hAinv, inv_inv] at h
      · change A * (A⁻¹ * φ * A) * A⁻¹ = φ
        group
  set α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
    c.eρ.trans (((MulAut.conj A).subgroupMap (autOn L V)).trans
      ((MulEquiv.subgroupCongr hmap).trans c.eρ.symm)) with hα
  have hkey : ∀ γ, ((c.eρ (α γ) : ↥(autOn L V)) : MulAut ↥V) =
      A * ((c.eρ γ : ↥(autOn L V)) : MulAut ↥V) * A⁻¹ := by
    intro γ
    simp only [hα, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hpowk : ∀ k : ℕ, ∀ γ, ((c.eρ ((α ^ k) γ) : ↥(autOn L V)) : MulAut ↥V) =
      A ^ k * ((c.eρ γ : ↥(autOn L V)) : MulAut ↥V) * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro γ; simp
    | succ k ih =>
      intro γ
      rw [pow_succ', MulAut.mul_apply, hkey, ih]
      group
  have hAr : A ^ r = 1 := by
    have h1 : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ r = 1 :=
      Subtype.ext (by simpa using hzr)
    rw [hA, ← map_pow, h1, map_one]
  have hαr : α ^ r = 1 := by
    refine MulEquiv.ext fun γ => ?_
    have h := hpowk r γ
    rw [hAr, one_mul, inv_one, mul_one] at h
    exact c.eρ.injective (Subtype.ext h)
  have hfix : α (x * dU μ * x⁻¹) = x * dU μ * x⁻¹ := by
    apply c.eρ.injective
    apply Subtype.ext
    rw [hkey, ← hd, hA, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hzd, mul_inv_cancel_right]
  set β := MulAut.conj x⁻¹ * α * (MulAut.conj x⁻¹)⁻¹ with hβ
  have hβapp : ∀ y, β y = x⁻¹ * α (x * y * x⁻¹) * x := by
    intro y
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, inv_inv, MulAut.conj_apply,
      MulAut.conj_apply, inv_inv]
  have hβμ : β (dU μ) = dU μ := by rw [hβapp, hfix]; group
  have hβfix : ∀ l : Fˣ, β (dU l) = dU l := by
    intro l
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hμ l)
    rw [← dU_pow, map_pow, hβμ]
  have hβr : β ^ r = 1 := by rw [hβ, conj_pow, hαr, mul_one, mul_inv_cancel]
  have hcop : Nat.Coprime r (2 ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrq
  have hβ1 : β = 1 := eq_one_of_torus hF hn β (hr.odd_of_ne_two hr2) hcop hβr
    (fun l => ⟨l, hβfix l⟩) (fun l => by rw [hβfix, mul_inv_cancel, map_one])
  have hα1 : α = 1 := by
    have e : α = (MulAut.conj x⁻¹)⁻¹ * β * MulAut.conj x⁻¹ := by rw [hβ]; group
    rw [e, hβ1, mul_one, inv_mul_cancel]
  intro l hl w hw
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := le_normalizer_fsuUL T L I hl
  have hAl : conjAct V ⟨l, hlN⟩ ∈ autOn L V := SecA.mem_autOn_iff'.mpr ⟨_, hl, rfl⟩
  have h1 := hkey (c.eρ.symm ⟨_, hAl⟩)
  rw [hα1, MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
  have hcN : z * l * z⁻¹ * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hzN hlN) hzN')
      (Subgroup.inv_mem _ hlN)
  have h2 : conjAct V ⟨z * l * z⁻¹ * l⁻¹, hcN⟩ = 1 := by
    have e : conjAct V ⟨z * l * z⁻¹ * l⁻¹, hcN⟩ =
        A * conjAct V ⟨l, hlN⟩ * A⁻¹ * (conjAct V ⟨l, hlN⟩)⁻¹ := by
      rw [hA, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e, ← h1, mul_inv_cancel]
  have h3 := congrArg (fun f : MulAut ↥V => ((f ⟨w, hw⟩ : ↥V) : G)) h2
  simp only [SecA.coe_conjAct_apply', MulAut.one_apply] at h3
  exact h3

theorem mem_centralizer_of_fix (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {y : G} (hyL : y ∈ L)
    (hU : ∀ u ∈ fsuUL T L I, y * u * y⁻¹ = u) :
    y ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hV := (ha t ht htn).1
  have hUC := SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn
  have hyL0 := SecA.le_fsuL0 T L hyL
  have hcomm : ∀ u, y * u * y⁻¹ = u → u ∈ Subgroup.centralizer ({y} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact mul_inv_eq_iff_eq_mul.mp hu
  have hle : fsuVM T L I ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [← hV]
    refine sup_le (sup_le (fun u hu => hcomm u (hU u hu)) (fun u hu => hcomm u ?_))
      fun c hc => hcomm c ?_
    · rw [Subgroup.mem_centralizer_iff.mp (hUC hu) y hyL, mul_inv_cancel_right]
    · rw [Subgroup.mem_centralizer_iff.mp hc.2 y hyL0, mul_inv_cancel_right]
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hle hv) y rfl).symm

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
