module

public import CFSG.Certificates.ExtraspecialNormalForm

public section

namespace CFSG.RankThree.PartOne.ThPlane

open CFSG.Certificates.ExtraspecialNF
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] {n : ℕ} {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

@[expose] noncomputable def coord (z : G) (q : Fin n → G) (g : G) : Fin n → ZMod 2 := by
  classical
  exact if hg : ∃ s v, nf z q s v = g then hg.choose_spec.choose else 0

theorem coord_nf (hinj : Function.Injective (Function.uncurry (nf z q))) (s : ZMod 2)
    (v : Fin n → ZMod 2) : coord z q (nf z q s v) = v := by
  classical
  have hg : ∃ s' v', nf z q s' v' = nf z q s v := ⟨s, v, rfl⟩
  have h1 : (hg.choose, hg.choose_spec.choose) = (s, v) := by
    apply hinj
    show nf z q hg.choose hg.choose_spec.choose = nf z q s v
    exact hg.choose_spec.choose_spec
  have h2 : coord z q (nf z q s v) = hg.choose_spec.choose := by
    simp only [coord, hg, ↓reduceDIte]
  rw [h2]
  exact congrArg Prod.snd h1

theorem coord_mul (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    {g g' : G} (hg : g ∈ Subgroup.closure (insert z (Set.range q)))
    (hg' : g' ∈ Subgroup.closure (insert z (Set.range q))) :
    coord z q (g * g') = coord z q g + coord z q g' := by
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hg
  obtain ⟨t, w, rfl⟩ := (mem_closure_iff h).1 hg'
  rw [nf_mul_nf h, coord_nf hinj, coord_nf hinj, coord_nf hinj]

theorem coord_eq_zero_iff (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
    {g : G} (hg : g ∈ Subgroup.closure (insert z (Set.range q))) :
    coord z q g = 0 ↔ g ∈ Subgroup.zpowers z := by
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hg
  rw [coord_nf hinj]
  constructor
  · rintro rfl
    rw [nf_zero_vec]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
  · intro hmem
    obtain ⟨b, hb⟩ := (mem_zpowers_iff_exists h).1 hmem
    have : nf z q b 0 = nf z q s v := by rw [nf_zero_vec]; exact hb
    have := hinj (a₁ := (b, 0)) (a₂ := (s, v)) this
    exact (congrArg Prod.snd this).symm


theorem nf_eq_zpow_mul (s : ZMod 2) (v : Fin n → ZMod 2) :
    nf z q s v = z ^ s.val * nf z q 0 v := by
  simp [nf]

theorem zpow_val_inj (hz1 : z ≠ 1) {a b : ZMod 2}
    (hab : z ^ a.val = z ^ b.val) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · exfalso
    rw [val_one_two] at hab
    simp at hab
    exact hz1 hab.symm
  · exfalso
    rw [val_one_two] at hab
    simp at hab
    exact hz1 hab
  · rfl

@[expose] noncomputable def actv (z : G) (q : Fin n → G) (m : G) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  coord z q (m * nf z q 0 v * m⁻¹)

section Action

variable (h : Rel z q c) (hinj : Function.Injective (Function.uncurry (nf z q)))
include h hinj

theorem coord_conj {m : G}
    (hm : ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
      m * g * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q))) (hz : m * z = z * m) {g : G}
    (hg : g ∈ Subgroup.closure (insert z (Set.range q))) :
    coord z q (m * g * m⁻¹) = actv z q m (coord z q g) := by
  obtain ⟨s, v, rfl⟩ := (mem_closure_iff h).1 hg
  rw [coord_nf hinj]
  have hzc : Commute m z := hz
  have e : m * nf z q s v * m⁻¹ = nf z q s 0 * (m * nf z q 0 v * m⁻¹) := by
    rw [nf_eq_zpow_mul s v, nf_zero_vec]
    have hc : Commute m (z ^ s.val) := hzc.pow_right _
    calc m * (z ^ s.val * nf z q 0 v) * m⁻¹ =
          (m * z ^ s.val * m⁻¹) * (m * nf z q 0 v * m⁻¹) := by group
      _ = z ^ s.val * (m * nf z q 0 v * m⁻¹) := by rw [hc.eq]; group
  have hmem : m * nf z q 0 v * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q)) :=
    hm _ (nf_mem_closure z q 0 v)
  rw [e, coord_mul h hinj (nf_mem_closure z q s 0) hmem, coord_nf hinj, zero_add]
  rfl

theorem actv_add {m : G}
    (hm : ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
      m * g * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q))) (hz : m * z = z * m)
    (v w : Fin n → ZMod 2) :
    actv z q m (v + w) = actv z q m v + actv z q m w := by
  have e : nf z q 0 v * nf z q 0 w = nf z q (collect c v w) (v + w) := by
    rw [nf_mul_nf h]; simp
  have h1 : coord z q (m * (nf z q 0 v * nf z q 0 w) * m⁻¹) =
      actv z q m v + actv z q m w := by
    have : m * (nf z q 0 v * nf z q 0 w) * m⁻¹ =
        (m * nf z q 0 v * m⁻¹) * (m * nf z q 0 w * m⁻¹) := by group
    rw [this, coord_mul h hinj (hm _ (nf_mem_closure z q 0 v)) (hm _ (nf_mem_closure z q 0 w))]
    rfl
  rw [← h1, e, coord_conj h hinj hm hz (nf_mem_closure z q _ _), coord_nf hinj]

theorem actv_mul {m m' : G}
    (hm : ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
      m * g * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q))) (hz : m * z = z * m)
    (hm' : ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
      m' * g * m'⁻¹ ∈ Subgroup.closure (insert z (Set.range q)))
    (v : Fin n → ZMod 2) :
    actv z q (m * m') v = actv z q m (actv z q m' v) := by
  have e : m * m' * nf z q 0 v * (m * m')⁻¹ = m * (m' * nf z q 0 v * m'⁻¹) * m⁻¹ := by group
  unfold actv
  rw [e, coord_conj h hinj hm hz (hm' _ (nf_mem_closure z q 0 v))]
  rfl

omit h in
theorem actv_one (v : Fin n → ZMod 2) : actv z q 1 v = v := by
  unfold actv
  simp only [one_mul, inv_one, mul_one]
  exact coord_nf hinj 0 v

theorem actv_of_mem {m : G} (hm : m ∈ Subgroup.closure (insert z (Set.range q)))
    (v : Fin n → ZMod 2) : actv z q m v = v := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  have hsymm := h.symm_of_ne_one hz1
  have hdiag := h.diag_eq_zero hz1
  obtain ⟨s, w, rfl⟩ := (mem_closure_iff h).1 hm
  unfold actv
  have hc := commutator_eq_zpow h hsymm hdiag s 0 w v
  have e : nf z q s w * nf z q 0 v * (nf z q s w)⁻¹ =
      nf z q (bil c w v) 0 * nf z q 0 v := by
    rw [nf_zero_vec, ← hc, commutatorElement_def]
    group
  rw [e, coord_mul h hinj (nf_mem_closure z q _ 0) (nf_mem_closure z q 0 v), coord_nf hinj,
    coord_nf hinj, zero_add]

theorem bil_actv {m : G}
    (hm : ∀ g ∈ Subgroup.closure (insert z (Set.range q)),
      m * g * m⁻¹ ∈ Subgroup.closure (insert z (Set.range q))) (hz : m * z = z * m)
    (v w : Fin n → ZMod 2) :
    bil c (actv z q m v) (actv z q m w) = bil c v w := by
  have hz1 : z ≠ 1 := ne_one_of_injective hinj
  have hsymm := h.symm_of_ne_one hz1
  have hdiag := h.diag_eq_zero hz1
  have hzc : Commute m z := hz
  obtain ⟨t1, v1, hv1⟩ := (mem_closure_iff h).1 (hm _ (nf_mem_closure z q 0 v))
  obtain ⟨t2, w1, hv2⟩ := (mem_closure_iff h).1 (hm _ (nf_mem_closure z q 0 w))
  have a1 : actv z q m v = v1 := by
    unfold actv
    rw [← hv1, coord_nf hinj]
  have a2 : actv z q m w = w1 := by
    unfold actv
    rw [← hv2, coord_nf hinj]
  have k : ⁅m * nf z q 0 v * m⁻¹, m * nf z q 0 w * m⁻¹⁆ = z ^ (bil c v w).val := by
    have e : ⁅m * nf z q 0 v * m⁻¹, m * nf z q 0 w * m⁻¹⁆ =
        m * ⁅nf z q 0 v, nf z q 0 w⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, commutator_eq_zpow h hsymm hdiag]
    have hc : Commute m (z ^ (bil c v w).val) := hzc.pow_right _
    rw [hc.eq]
    group
  have k' : ⁅m * nf z q 0 v * m⁻¹, m * nf z q 0 w * m⁻¹⁆ = z ^ (bil c v1 w1).val := by
    rw [← hv1, ← hv2, commutator_eq_zpow h hsymm hdiag]
  rw [a1, a2]
  exact zpow_val_inj hz1 (k'.symm.trans k)

end Action

end Generic

end CFSG.RankThree.PartOne.ThPlane
