module

public import CFSG.Milestones.ASVolI.H1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]

theorem mem_conjAut {g : MulAut V} {A : Subgroup (MulAut V)} {x : MulAut V} :
    x ∈ conjAut g A ↔ g⁻¹ * x * g ∈ A := by
  unfold conjAut
  rw [Subgroup.mem_map_equiv]
  simp

theorem conj_mem_conjAut {g : MulAut V} {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) :
    g * a * g⁻¹ ∈ conjAut g A := by
  rw [conjAut]
  exact Subgroup.mem_map_of_mem _ ha

theorem conjAut_one (A : Subgroup (MulAut V)) : conjAut 1 A = A := by
  ext x
  rw [mem_conjAut]
  simp

theorem conjAut_mul (g h : MulAut V) (A : Subgroup (MulAut V)) :
    conjAut (g * h) A = conjAut g (conjAut h A) := by
  ext x
  rw [mem_conjAut, mem_conjAut, mem_conjAut]
  have h2 : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [h2]

theorem conjAut_inf (g : MulAut V) (A B : Subgroup (MulAut V)) :
    conjAut g (A ⊓ B) = conjAut g A ⊓ conjAut g B := by
  unfold conjAut
  exact Subgroup.map_inf A B _ (MulAut.conj g).injective

theorem conjAut_sup (g : MulAut V) (A B : Subgroup (MulAut V)) :
    conjAut g (A ⊔ B) = conjAut g A ⊔ conjAut g B := by
  unfold conjAut
  exact Subgroup.map_sup A B _

theorem conjAut_mono (g : MulAut V) {A B : Subgroup (MulAut V)} (h : A ≤ B) :
    conjAut g A ≤ conjAut g B := by
  unfold conjAut
  exact Subgroup.map_mono h

theorem conjAut_le_conjAut_iff (g : MulAut V) {A B : Subgroup (MulAut V)} :
    conjAut g A ≤ conjAut g B ↔ A ≤ B := by
  unfold conjAut
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem conjAut_eq_self_of_mem {g : MulAut V} {A : Subgroup (MulAut V)} (hg : g ∈ A) :
    conjAut g A = A := by
  apply le_antisymm
  · intro x hx
    rw [conjAut] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact A.mul_mem (A.mul_mem hg hy) (A.inv_mem hg)
  · intro x hx
    rw [conjAut]
    refine ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem card_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (conjAut g A) = Nat.card A := by
  unfold conjAut
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjAut_zpowers (g t : MulAut V) :
    conjAut g (Subgroup.zpowers t) = Subgroup.zpowers (g * t * g⁻¹) := by
  rw [conjAut, MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

private theorem isElemAbelian_map {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {E : Subgroup X} (h : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  haveI : IsMulCommutative E := h.1
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← map_pow, h.2 y hy, map_one]

theorem isElemAbelian_conjAut_iff (p : ℕ) (g : MulAut V) (A : Subgroup (MulAut V)) :
    IsElemAbelian p (conjAut g A) ↔ IsElemAbelian p A := by
  constructor
  · intro h
    have h' := isElemAbelian_map (MulAut.conj g⁻¹).toMonoidHom h
    rw [← conjAut] at h'
    rw [← conjAut_mul, inv_mul_cancel, conjAut_one] at h'
    exact h'
  · intro h
    exact isElemAbelian_map (MulAut.conj g).toMonoidHom h

private theorem isElemAbelian2_conjAut_of_mem {g : MulAut V} {A : Subgroup (MulAut V)}
    (h : IsElemAbelian2 A) : IsElemAbelian2 (conjAut g A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := h.1 _ (mem_conjAut.1 hx) _ (mem_conjAut.1 hy)
    have h2 := congrArg (fun t => g * t * g⁻¹) h1
    simpa [mul_assoc] using h2
  · have h2 := h.2 _ (mem_conjAut.1 hx)
    have h3 : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      simp [pow_two, mul_assoc]
    rw [h3] at h2
    have h4 : g * (g⁻¹ * x ^ 2 * g) * g⁻¹ = x ^ 2 := by group
    rw [← h4, h2]
    simp

theorem isElemAbelian2_conjAut_iff (g : MulAut V) (A : Subgroup (MulAut V)) :
    IsElemAbelian2 (conjAut g A) ↔ IsElemAbelian2 A := by
  constructor
  · intro h
    have h' := isElemAbelian2_conjAut_of_mem (g := g⁻¹) h
    rw [← conjAut_mul, inv_mul_cancel, conjAut_one] at h'
    exact h'
  · exact isElemAbelian2_conjAut_of_mem

theorem map_zpowers (g : MulAut V) (v : V) :
    (Subgroup.zpowers v).map (g : MulAut V).toMonoidHom = Subgroup.zpowers (g v) :=
  MonoidHom.map_zpowers (g : MulAut V).toMonoidHom v

theorem conjAut_centSub (g : MulAut V) (U : Subgroup V) :
    conjAut g (centSub U) = centSub (U.map (g : MulAut V).toMonoidHom) := by
  ext x
  rw [mem_conjAut, mem_centSub, mem_centSub]
  constructor
  · intro h w hw
    obtain ⟨u, hu, rfl⟩ := hw
    have h1 := h u hu
    simp only [MulAut.mul_apply] at h1
    have h2 := congrArg g h1
    simpa [MulAut.apply_inv_self] using h2
  · intro h u hu
    have h1 := h (g u) (Subgroup.mem_map_of_mem _ hu)
    simp only [MulAut.mul_apply]
    have h2 : g (g⁻¹ (x (g u))) = g u := by
      rw [MulAut.apply_inv_self, h1]
    exact g.injective h2

theorem conjAut_stabSub (g : MulAut V) (U : Subgroup V) :
    conjAut g (stabSub U) = stabSub (U.map (g : MulAut V).toMonoidHom) := by
  ext x
  rw [mem_conjAut, mem_stabSub, mem_stabSub]
  constructor
  · intro h u
    have h1 := h (g⁻¹ u)
    simp only [MulAut.mul_apply, MulAut.apply_inv_self] at h1
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa using h1
  · intro h u
    have h1 := h (g u)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
    simp only [MulAut.mul_apply]
    simpa [MulAut.inv_apply_self] using h1

theorem conjAut_eq_map (g : MulAut V) (A : Subgroup (MulAut V)) :
    conjAut g A = A.map (MulAut.conj g).toMonoidHom := rfl

theorem commOn_conjAut (g : MulAut V) (W : Subgroup V) (A : Subgroup (MulAut V)) :
    commOn (W.map (g : MulAut V).toMonoidHom) (conjAut g A) =
      (commOn W A).map (g : MulAut V).toMonoidHom := by
  apply le_antisymm
  · unfold commOn
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨a', ha', w', hw', rfl⟩
    rw [mem_conjAut] at ha'
    rw [Subgroup.mem_map_equiv] at hw'
    refine Subgroup.subset_closure ⟨(g⁻¹ * a' * g) (g⁻¹ w') * (g⁻¹ w')⁻¹,
      ⟨g⁻¹ * a' * g, ha', g⁻¹ w', hw', rfl⟩, ?_⟩
    simp [MulAut.mul_apply]
  · unfold commOn
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, ?_, g w,
      Subgroup.mem_map_of_mem (g : MulAut V).toMonoidHom hw, ?_⟩
    · rw [mem_conjAut]
      simpa [mul_assoc] using ha
    · simp [MulAut.mul_apply]

theorem map_inf_subgroup (g : MulAut V) (U W : Subgroup V) :
    (U ⊓ W).map (g : MulAut V).toMonoidHom =
      U.map (g : MulAut V).toMonoidHom ⊓ W.map (g : MulAut V).toMonoidHom :=
  Subgroup.map_inf U W (g : MulAut V).toMonoidHom (g : MulAut V).injective

theorem map_sup_subgroup (g : MulAut V) (U W : Subgroup V) :
    (U ⊔ W).map (g : MulAut V).toMonoidHom =
      U.map (g : MulAut V).toMonoidHom ⊔ W.map (g : MulAut V).toMonoidHom :=
  Subgroup.map_sup U W _

theorem relIndex_map_aut (g : MulAut V) (U W : Subgroup V) :
    (U.map (g : MulAut V).toMonoidHom).relIndex (W.map (g : MulAut V).toMonoidHom) = U.relIndex W :=
  Subgroup.relIndex_map_map_of_injective U W (g : MulAut V).injective

theorem card_map_aut (g : MulAut V) (U : Subgroup V) :
    Nat.card (U.map (g : MulAut V).toMonoidHom) = Nat.card U :=
  Subgroup.card_map_of_injective (g : MulAut V).injective

private theorem isPGroup_conjAut_iff (g : MulAut V) (A : Subgroup (MulAut V)) :
    IsPGroup 2 (conjAut g A) ↔ IsPGroup 2 A := by
  constructor
  · intro h
    have h' : IsPGroup 2 ((conjAut g A).map (MulAut.conj g⁻¹).toMonoidHom) := h.map _
    rw [← conjAut] at h'
    rw [← conjAut_mul, inv_mul_cancel, conjAut_one] at h'
    exact h'
  · intro h
    exact h.map (MulAut.conj g).toMonoidHom

theorem isSylowIn_conjAut_iff (g : MulAut V) (P H : Subgroup (MulAut V)) :
    IsSylowIn 2 (conjAut g P) (conjAut g H) ↔ IsSylowIn 2 P H := by
  have hri : (conjAut g P).relIndex (conjAut g H) = P.relIndex H := by
    unfold conjAut
    exact Subgroup.relIndex_map_map_of_injective P H (MulAut.conj g).injective
  unfold IsSylowIn
  rw [conjAut_le_conjAut_iff, isPGroup_conjAut_iff, hri]

private def H9Good (H N : Subgroup (MulAut V)) : Prop :=
  N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set (MulAut V)) ∧
    ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N

private theorem conjAut_normalizer (g : MulAut V) (N : Subgroup (MulAut V)) :
    conjAut g (Subgroup.normalizer (N : Set (MulAut V))) =
      Subgroup.normalizer (conjAut g N : Set (MulAut V)) := by
  unfold conjAut
  exact Subgroup.map_normalizer_eq_of_bijective N (MulAut.conj g).bijective

private theorem conjAut_pow (g y : MulAut V) (n : ℕ) :
    (g * y * g⁻¹) ^ n = g * y ^ n * g⁻¹ := by
  rw [← MulAut.conj_apply g y, ← map_pow, MulAut.conj_apply]

private theorem h9Good_conjAut_iff (g : MulAut V) (H N : Subgroup (MulAut V)) :
    H9Good (conjAut g H) N ↔ H9Good H (conjAut g⁻¹ N) := by
  unfold H9Good
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← conjAut_le_conjAut_iff (g := g), ← conjAut_mul, mul_inv_cancel, conjAut_one]
      exact h1
    · have hh := conjAut_mono g⁻¹ h2
      rwa [← conjAut_mul, inv_mul_cancel, conjAut_one, conjAut_normalizer] at hh
    · intro y hy
      obtain ⟨k, hk⟩ := h3 (g * y * g⁻¹) (conj_mem_conjAut hy)
      refine ⟨k, ?_⟩
      rw [mem_conjAut, inv_inv, ← conjAut_pow g y (2 ^ k)]
      exact hk
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · have hh := conjAut_mono g h1
      rwa [← conjAut_mul, mul_inv_cancel, conjAut_one] at hh
    · have hh := conjAut_mono g h2
      rwa [conjAut_normalizer, ← conjAut_mul, mul_inv_cancel, conjAut_one] at hh
    · intro z hz
      have hy : g⁻¹ * z * g ∈ H := mem_conjAut.1 hz
      obtain ⟨k, hk⟩ := h3 (g⁻¹ * z * g) hy
      refine ⟨k, ?_⟩
      rw [mem_conjAut] at hk
      have hp : (g⁻¹ * z * g) ^ (2 ^ k) = g⁻¹ * z ^ (2 ^ k) * g := by
        simpa [inv_inv] using conjAut_pow g⁻¹ z (2 ^ k)
      rw [hp, inv_inv] at hk
      convert hk using 1
      group

theorem twoResidual_conjAut (g : MulAut V) (H : Subgroup (MulAut V)) :
    twoResidual (conjAut g H) = conjAut g (twoResidual H) := by
  ext x
  rw [mem_twoResidual_iff, mem_conjAut, mem_twoResidual_iff]
  constructor
  · intro h M hM1 hM2 hM3
    have hM : H9Good (conjAut g H) (conjAut g M) := by
      rw [h9Good_conjAut_iff, ← conjAut_mul, inv_mul_cancel, conjAut_one]
      exact ⟨hM1, hM2, hM3⟩
    obtain ⟨h1, h2, h3⟩ := hM
    exact mem_conjAut.mp (h (conjAut g M) h1 h2 h3)
  · intro h N hN1 hN2 hN3
    have hN : H9Good H (conjAut g⁻¹ N) :=
      (h9Good_conjAut_iff g H N).mp ⟨hN1, hN2, hN3⟩
    obtain ⟨h1, h2, h3⟩ := hN
    have hx : g⁻¹ * x * g ∈ conjAut g⁻¹ N := h (conjAut g⁻¹ N) h1 h2 h3
    rw [mem_conjAut] at hx
    convert hx using 1
    group

private theorem isExtOf_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (C E : Subgroup X) (Q : Type*) [Group Q] :
    IsExtOf (C.map e.toMonoidHom) (E.map e.toMonoidHom) Q ↔ IsExtOf C E Q := by
  let eC : ↥C ≃* ↥(C.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
  have hcoe : ∀ x : ↥C, ((eC x : ↥(C.map e.toMonoidHom)) : Y) = e (x : X) :=
    fun x => Subgroup.coe_equivMapOfInjective_apply C e.toMonoidHom e.injective x
  constructor
  · rintro ⟨hCE, f, hf, hker⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hCE,
      f.comp eC.toMonoidHom, hf.comp eC.surjective, ?_⟩
    apply Subgroup.ext
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change ((eC x : ↥(C.map e.toMonoidHom)) : Y) ∈ E.map e.toMonoidHom ↔ (x : X) ∈ E
    rw [hcoe x, Subgroup.mem_map_equiv]
    simp
  · rintro ⟨hCE, f, hf, hker⟩
    refine ⟨Subgroup.map_mono hCE,
      f.comp eC.symm.toMonoidHom, hf.comp eC.symm.surjective, ?_⟩
    apply Subgroup.ext
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change ((eC.symm x : ↥C) : X) ∈ E ↔ ((x : ↥(C.map e.toMonoidHom)) : Y) ∈ E.map e.toMonoidHom
    have hx : e ((eC.symm x : ↥C) : X) = ((x : ↥(C.map e.toMonoidHom)) : Y) := by
      rw [← hcoe (eC.symm x), MulEquiv.apply_symm_apply]
    rw [Subgroup.mem_map_equiv]
    rw [← hx]
    simp

theorem isExtOf_conjAut_iff (g : MulAut V) (C E : Subgroup (MulAut V)) (Q : Type*) [Group Q] :
    IsExtOf (conjAut g C) (conjAut g E) Q ↔ IsExtOf C E Q := by
  have h := isExtOf_map_mulEquiv (MulAut.conj g) C E Q
  simpa only [conjAut] using h

theorem inducesOn_conjAut_iff (g : MulAut V) (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    (A : Type*) [CommGroup A] (Γ : Subgroup (MulAut A)) :
    InducesOn (conjAut g G) (U.map (g : MulAut V).toMonoidHom) (Z.map (g : MulAut V).toMonoidHom) A Γ ↔
      InducesOn G U Z A Γ := by
  let φU : ↥U ≃* ↥(U.map (g : MulAut V).toMonoidHom) :=
    Subgroup.equivMapOfInjective U (g : MulAut V).toMonoidHom (g : MulAut V).injective
  have hcoe : ∀ u : ↥U, ((φU u : ↥(U.map (g : MulAut V).toMonoidHom)) : V) = g (u : V) :=
    fun u => Subgroup.coe_equivMapOfInjective_apply U _ _ u
  have key : ∀ (x x' : ↥(U.map (g : MulAut V).toMonoidHom)) (a : MulAut V),
      (x' : V) = (MulAut.conj g a) x →
      ((φU.symm x' : ↥U) : V) = a ((φU.symm x : ↥U) : V) := by
    intro x x' a h
    have hx1 : (x' : V) = g ((φU.symm x' : ↥U) : V) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply φU x']
      exact hcoe (φU.symm x')
    have hx0 : (x : V) = g ((φU.symm x : ↥U) : V) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply φU x]
      exact hcoe (φU.symm x)
    apply g.injective
    rw [hx1, hx0] at h
    simpa [MulAut.conj_apply, MulAut.mul_apply] using h
  constructor
  · rintro ⟨hZU, hUinv, hZinv, β', hβ'surj, hβ'ker, hβ'G, hβ'Γ⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Subgroup.map_le_map_iff_of_injective (f := (g : MulAut V).toMonoidHom)
        (g : MulAut V).injective).mp hZU
    · intro a ha u hu
      have hh : g * a * g⁻¹ ∈ conjAut g G := conj_mem_conjAut ha
      have hu' : g u ∈ U.map (g : MulAut V).toMonoidHom := Subgroup.mem_map_of_mem _ hu
      have hmem := hUinv (g * a * g⁻¹) hh (g u) hu'
      rw [show (g * a * g⁻¹) (g u) = g (a u) by simp [MulAut.mul_apply],
        Subgroup.mem_map_equiv] at hmem
      simpa using hmem
    · intro a ha z hz
      have hh : g * a * g⁻¹ ∈ conjAut g G := conj_mem_conjAut ha
      have hz' : g z ∈ Z.map (g : MulAut V).toMonoidHom := Subgroup.mem_map_of_mem _ hz
      have hmem := hZinv (g * a * g⁻¹) hh (g z) hz'
      rw [show (g * a * g⁻¹) (g z) = g (a z) by simp [MulAut.mul_apply],
        Subgroup.mem_map_equiv] at hmem
      simpa using hmem
    · refine ⟨β'.comp φU.toMonoidHom, hβ'surj.comp φU.surjective, ?_, ?_, ?_⟩
      · intro u
        rw [MonoidHom.comp_apply, hβ'ker]
        change ((φU u : ↥(U.map (g : MulAut V).toMonoidHom)) : V) ∈
          Z.map (g : MulAut V).toMonoidHom ↔ (u : V) ∈ Z
        rw [hcoe u, Subgroup.mem_map_equiv]
        simp
      · intro a ha
        obtain ⟨γ, hγ, hγa⟩ := hβ'G (g * a * g⁻¹) (conj_mem_conjAut ha)
        refine ⟨γ, hγ, ?_⟩
        intro u u' hu'
        refine hγa (φU u) (φU u') ?_
        rw [hcoe u', hcoe u, hu']
        simp [MulAut.mul_apply]
      · intro γ hγ
        obtain ⟨h', hh', hγh⟩ := hβ'Γ γ hγ
        refine ⟨g⁻¹ * h' * g, mem_conjAut.mp hh', ?_⟩
        intro u u' hu'
        refine hγh (φU u) (φU u') ?_
        rw [hcoe u', hcoe u, hu']
        simp [MulAut.mul_apply]
  · rintro ⟨hZU, hUinv, hZinv, β, hβsurj, hβker, hβG, hβΓ⟩
    refine ⟨Subgroup.map_mono hZU, ?_, ?_, ?_⟩
    · intro h' hh' u' hu'
      obtain ⟨a, ha, rfl⟩ := hh'
      obtain ⟨u, hu, rfl⟩ := hu'
      have h := hUinv a ha u hu
      have h2 := Subgroup.mem_map_of_mem (g : MulAut V).toMonoidHom h
      convert h2 using 1
      simp [MulAut.conj_apply, MulAut.mul_apply]
    · intro h' hh' z' hz'
      obtain ⟨a, ha, rfl⟩ := hh'
      obtain ⟨z, hz, rfl⟩ := hz'
      have h := hZinv a ha z hz
      have h2 := Subgroup.mem_map_of_mem (g : MulAut V).toMonoidHom h
      convert h2 using 1
      simp [MulAut.conj_apply, MulAut.mul_apply]
    · refine ⟨β.comp φU.symm.toMonoidHom, hβsurj.comp φU.symm.surjective, ?_, ?_, ?_⟩
      · intro x
        rw [MonoidHom.comp_apply, hβker]
        change ((φU.symm x : ↥U) : V) ∈ Z ↔
          (x : V) ∈ Z.map (g : MulAut V).toMonoidHom
        have hx' : (x : V) = g ((φU.symm x : ↥U) : V) := by
          conv_lhs => rw [← MulEquiv.apply_symm_apply φU x]
          exact hcoe (φU.symm x)
        constructor
        · intro hx
          rw [Subgroup.mem_map_equiv, hx']
          simpa using hx
        · intro hx
          rw [Subgroup.mem_map_equiv] at hx
          rw [hx'] at hx
          simpa using hx
      · intro h' hh'
        obtain ⟨a, ha, rfl⟩ := hh'
        obtain ⟨γ, hγ, hγa⟩ := hβG a ha
        refine ⟨γ, hγ, ?_⟩
        intro x x' hx'
        exact hγa (φU.symm x) (φU.symm x') (key x x' a hx')
      · intro γ hγ
        obtain ⟨a, ha, hγa⟩ := hβΓ γ hγ
        refine ⟨g * a * g⁻¹, conj_mem_conjAut ha, ?_⟩
        intro x x' hx'
        exact hγa (φU.symm x) (φU.symm x') (key x x' a hx')

theorem nonempty_mulEquiv_conjAut_iff (g : MulAut V) (H : Subgroup (MulAut V)) (X : Type*) [Group X] :
    Nonempty (↥(conjAut g H) ≃* X) ↔ Nonempty (↥H ≃* X) := by
  have e : ↥H ≃* ↥(conjAut g H) :=
    Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  constructor
  · rintro ⟨f⟩
    exact ⟨e.trans f⟩
  · rintro ⟨f⟩
    exact ⟨e.symm.trans f⟩

theorem isTwoCentralVec_iff_of_mem {M : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ M) (v : V) :
    IsTwoCentralVec M (g v) ↔ IsTwoCentralVec M v := by
  constructor
  · rintro ⟨S, hS, hfix⟩
    refine ⟨conjAut g⁻¹ S, ?_, ?_⟩
    · have hM : conjAut g⁻¹ M = M := conjAut_eq_self_of_mem (M.inv_mem hg)
      rw [← hM, isSylowIn_conjAut_iff]
      exact hS
    · intro s' hs'
      have hs : g * s' * g⁻¹ ∈ S := by simpa using mem_conjAut.mp hs'
      have h2 := hfix (g * s' * g⁻¹) hs
      have h3 : g (s' v) = g v := by simpa [MulAut.mul_apply, MulAut.apply_inv_self] using h2
      exact g.injective h3
  · rintro ⟨S, hS, hfix⟩
    refine ⟨conjAut g S, ?_, ?_⟩
    · have hM : conjAut g M = M := conjAut_eq_self_of_mem hg
      rw [← hM, isSylowIn_conjAut_iff]
      exact hS
    · intro s' hs'
      obtain ⟨s, hs, hsg⟩ := hs'
      rw [← hsg]
      simpa [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix s hs]

theorem twoResidual_eq_self_of_isPerfect {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : Group.IsPerfect ↥H) : twoResidual H = H := by
  apply le_antisymm (twoResidual_le H)
  intro x hx
  rw [mem_twoResidual_iff]
  intro N hNH hHN hpow
  haveI hK : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (↥H ⧸ N.subgroupOf H) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) q
    obtain ⟨k, hk⟩ := hpow (y : G) y.2
    refine ⟨k, ?_⟩
    rw [← map_pow (QuotientGroup.mk' (N.subgroupOf H)) y (2 ^ k),
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simpa [Subgroup.mem_subgroupOf] using hk
  haveI : Group.IsPerfect (↥H ⧸ N.subgroupOf H) := inferInstance
  haveI hNil : Group.IsNilpotent (↥H ⧸ N.subgroupOf H) := hP.isNilpotent
  haveI : Subsingleton (↥H ⧸ N.subgroupOf H) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact Group.IsPerfect.not_isNilpotent (↥H ⧸ N.subgroupOf H) hNil
  have hKtop : N.subgroupOf H = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    rw [← QuotientGroup.eq_one_iff (N := N.subgroupOf H) y]
    exact Subsingleton.elim _ _
  have hxK : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H := by rw [hKtop]; trivial
  simpa using (Subgroup.mem_subgroupOf (H := N) (K := H)).mp hxK

end CFSG.ASVolI.ChH
