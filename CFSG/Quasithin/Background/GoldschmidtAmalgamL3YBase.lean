module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UCent
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VNbr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
@[expose] def IsPair (z : D) (V : Subgroup D) (x ρ : CosetGeom (A ⊔ B) A B) (c : D) : Prop :=
  ∃ μ μ' : CosetGeom (A ⊔ B) A B, ∃ a a' : D, (graph (A ⊔ B) A B).Adj x μ ∧
    (graph (A ⊔ B) A B).Adj x μ' ∧ μ ≠ ρ ∧ μ' ≠ ρ ∧ μ ≠ μ' ∧ a ∈ Vv V μ ∧ a ∉ Zv z x ∧
    a' ∈ Vv V μ' ∧ a' ∉ Zv z x ∧ c = a * a'

omit [Finite D] in
theorem IsPair.inv {x ρ : CosetGeom (A ⊔ B) A B} {c : D} (hc : IsPair z V x ρ c) :
    IsPair z V x ρ c⁻¹ := by
  obtain ⟨μ, μ', a, a', hμ, hμ', hμρ, hμ'ρ, hμμ', ha, ha1, ha', ha'1, rfl⟩ := hc
  refine ⟨μ', μ, a'⁻¹, a⁻¹, hμ', hμ, hμ'ρ, hμρ, hμμ'.symm, (Vv V μ').inv_mem ha', ?_,
    (Vv V μ).inv_mem ha, ?_, by simp⟩
  · rwa [(Zv z x).inv_mem_iff]
  · rwa [(Zv z x).inv_mem_iff]

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_two_others {w u : CosetGeom (A ⊔ B) A B} (hu : (graph (A ⊔ B) A B).Adj w u) :
    ∃ x y : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj w x ∧ (graph (A ⊔ B) A B).Adj w y ∧
      u ≠ x ∧ u ≠ y ∧ x ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Set.ncard_eq_three.mp (h.ncard_nbrs w)
  have hm : ∀ y, (graph (A ⊔ B) A B).Adj w y → y = a ∨ y = b ∨ y = c := by
    intro y hy
    have : y ∈ nbrs w := hy
    rw [hset] at this
    simpa using this
  have hmem : ∀ y, y = a ∨ y = b ∨ y = c → (graph (A ⊔ B) A B).Adj w y := by
    intro y hy
    have : y ∈ nbrs w := by
      rw [hset]
      simpa using hy
    exact this
  have ha := hmem a (Or.inl rfl)
  have hb := hmem b (Or.inr (Or.inl rfl))
  have hc := hmem c (Or.inr (Or.inr rfl))
  rcases hm u hu with rfl | rfl | rfl
  · exact ⟨b, c, hb, hc, hab, hac, hbc⟩
  · exact ⟨a, c, ha, hc, hab.symm, hbc, hac⟩
  · exact ⟨a, b, ha, hb, hac.symm, hbc.symm, hab⟩

omit [Finite D] in
theorem elemAbelian_Vv_B {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    IsElemAbelian 2 (Vv V v) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1]
  exact F7.isElemAbelian_conjSub h.abelian

omit [Finite D] in
theorem Vv_smul' (k : ↥(A ⊔ B)) (w : CosetGeom (A ⊔ B) A B) :
    Vv V (k • w) = conjSub (k : D) (Vv V w) :=
  Vv_smul h.natural.reduced.2.1 k w

omit [Finite D] in
theorem Zv_smul' (k : ↥(A ⊔ B)) (w : CosetGeom (A ⊔ B) A B) :
    Zv z (k • w) = conjSub (k : D) (Zv z w) :=
  Zv_smul h.normalizes_zpowers k w

omit [Finite D] in
theorem card_Vv_B_of {n : ℕ} (hU : Nat.card (conjClosure V B) = n)
    {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) : Nat.card (Vv V v) = n := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1, card_conjSub]
  exact hU

theorem Vv_le_Zv_sup_zpowers {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) {a : D} (ha : a ∈ Vv V u) (ha' : a ∉ Zv z v) :
    Vv V u ≤ Zv z v ⊔ Subgroup.zpowers a := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  have hZ : Zv z v ≤ Vv V u := h.Zv_le_Vv huv hu
  have hS : Zv z v ⊔ Subgroup.zpowers a ≤ Vv V u := sup_le hZ (Subgroup.zpowers_le.mpr ha)
  have hd1 : 2 ∣ Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Zv z v ≤ Zv z v ⊔ Subgroup.zpowers a)
    rwa [h.card_Zv hv] at this
  have hd2 : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) ∣ 4 := by
    have := Subgroup.card_dvd_of_le hS
    rwa [h.card_Vv_A hu] at this
  have hne : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) ≠ 2 := fun e => by
    have heq : Zv z v = Zv z v ⊔ Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [e, h.card_Zv hv])
    exact ha' (heq ▸ (le_sup_right : Subgroup.zpowers a ≤ Zv z v ⊔ Subgroup.zpowers a)
      (Subgroup.mem_zpowers a))
  have hle4 := Nat.le_of_dvd (by norm_num) hd2
  have hpos : 0 < Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) := Nat.card_pos
  have h4 : Nat.card ↥(Zv z v ⊔ Subgroup.zpowers a) = 4 := by
    obtain ⟨k, hk⟩ := hd1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [h4, h.card_Vv_A hu])).ge

omit [Finite D] in
theorem mul_inv_mem_Zv_of_Vv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) {a y : D} (ha : a ∈ Vv V u) (ha' : a ∉ Zv z v)
    (hy : y ∈ Vv V u) (hy' : y ∉ Zv z v) : y * a⁻¹ ∈ Zv z v := by
  have hv : vtype v = true := vtype_eq_true_of_adj huv hu
  have e := Subgroup.relIndex_mul_card (Zv z v) (Vv V u)
  rw [inf_eq_left.mpr (h.Zv_le_Vv huv hu), h.card_Zv hv, h.card_Vv_A hu] at e
  have hidx : (Zv z v).relIndex (Vv V u) = 2 := by omega
  exact mul_inv_mem_of_relIndex_eq_two hidx hy ha hy' ha'

theorem exists_Vv_not_mem_Zv {u v : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (huv : (graph (A ⊔ B) A B).Adj u v) : ∃ a ∈ Vv V u, a ∉ Zv z v := by
  by_contra hcon
  push Not at hcon
  have hle : Vv V u ≤ Zv z v := fun a ha => hcon a ha
  have := Subgroup.card_le_of_le hle
  rw [h.card_Vv_A hu, h.card_Zv (vtype_eq_true_of_adj huv hu)] at this
  omega

theorem smul_nbr_ne {w u μ : CosetGeom (A ⊔ B) A B} (hu : (graph (A ⊔ B) A B).Adj w u)
    (hμ : (graph (A ⊔ B) A B).Adj w μ) (huμ : u ≠ μ) {k : ↥(A ⊔ B)} (hkw : k • w = w)
    (hku : k • u = u) (hk : (k : D) ∉ ballStab 1 w) :
    k • μ ≠ μ ∧ (graph (A ⊔ B) A B).Adj w (k • μ) ∧ k • μ ≠ u := by
  refine ⟨fun e => hk (h.mem_ballStab_one_of_fix_two' hu hμ huμ (mem_stab_of_smul_eq hkw)
    (mem_stab_of_smul_eq hku) (mem_stab_of_smul_eq e)), ?_,
    fun e => huμ (smul_left_cancel k (e.trans hku.symm)).symm⟩
  have := (smul_adj k).mpr hμ
  rwa [hkw] at this

omit [Finite D] in
theorem conjSub_Zv_eq {x : CosetGeom (A ⊔ B) A B} {k : ↥(A ⊔ B)} (hkx : k • x = x) :
    conjSub (k : D) (Zv z x) = Zv z x := by
  rw [← h.Zv_smul' k x, hkx]

omit [Finite D] in
theorem conj_mem_Zv_iff {x : CosetGeom (A ⊔ B) A B} {k : ↥(A ⊔ B)} (hkx : k • x = x) {e : D} :
    (k : D) * e * (k : D)⁻¹ ∈ Zv z x ↔ e ∈ Zv z x := by
  have hZ := h.conjSub_Zv_eq hkx
  constructor
  · intro hmem
    rw [← hZ, mem_conjSub] at hmem
    have e1 : (k : D)⁻¹ * ((k : D) * e * (k : D)⁻¹) * k = e := by group
    rwa [e1] at hmem
  · intro hmem
    rw [← hZ]
    exact mul_mem_conjSub hmem

omit [Finite D] in
theorem isPair_conj (k : ↥(A ⊔ B)) {x ρ : CosetGeom (A ⊔ B) A B} {c : D}
    (hc : IsPair z V x ρ c) : IsPair z V (k • x) (k • ρ) ((k : D) * c * (k : D)⁻¹) := by
  obtain ⟨μ, μ', a, a', hμ, hμ', hμρ, hμ'ρ, hμμ', ha, ha1, ha', ha'1, rfl⟩ := hc
  refine ⟨k • μ, k • μ', (k : D) * a * (k : D)⁻¹, (k : D) * a' * (k : D)⁻¹,
    (smul_adj k).mpr hμ, (smul_adj k).mpr hμ', fun e => hμρ (smul_left_cancel k e),
    fun e => hμ'ρ (smul_left_cancel k e), fun e => hμμ' (smul_left_cancel k e), ?_, ?_, ?_, ?_,
    by group⟩
  · rw [h.Vv_smul' k μ]
    exact mul_mem_conjSub ha
  · rw [h.Zv_smul' k x, mem_conjSub]
    have e1 : (k : D)⁻¹ * ((k : D) * a * (k : D)⁻¹) * k = a := by group
    rwa [e1]
  · rw [h.Vv_smul' k μ']
    exact mul_mem_conjSub ha'
  · rw [h.Zv_smul' k x, mem_conjSub]
    have e1 : (k : D)⁻¹ * ((k : D) * a' * (k : D)⁻¹) * k = a' := by group
    rwa [e1]

omit [Finite D] in
theorem isPair_conj_fix {x ρ : CosetGeom (A ⊔ B) A B} {k : ↥(A ⊔ B)} (hkx : k • x = x)
    (hkρ : k • ρ = ρ) {c : D} (hc : IsPair z V x ρ c) :
    IsPair z V x ρ ((k : D) * c * (k : D)⁻¹) := by
  have := h.isPair_conj k hc
  rwa [hkx, hkρ] at this

omit h [Finite D] in
theorem isPair_mem_Vv {x ρ : CosetGeom (A ⊔ B) A B} (hx : vtype x = true) {c : D}
    (hc : IsPair z V x ρ c) : c ∈ Vv V x := by
  obtain ⟨μ, μ', a, a', hμ, hμ', -, -, -, ha, -, ha', -, rfl⟩ := hc
  have h1 : Vv V μ ≤ Vv V x := Vv_le_Vv_of_adj hμ.symm (vtype_eq_false_of_adj hμ hx)
  have h2 : Vv V μ' ≤ Vv V x := Vv_le_Vv_of_adj hμ'.symm (vtype_eq_false_of_adj hμ' hx)
  exact (Vv V x).mul_mem (h1 ha) (h2 ha')

theorem isPair_ne_one {x ρ : CosetGeom (A ⊔ B) A B} (hx : vtype x = true) {c : D}
    (hc : IsPair z V x ρ c) : c ≠ 1 := by
  obtain ⟨μ, μ', a, a', hμ, hμ', -, -, hμμ', ha, ha1, ha', -, rfl⟩ := hc
  intro h1
  apply ha1
  have e : a = a'⁻¹ := eq_inv_of_mul_eq_one_left h1
  refine h.mem_Zv_of_mem_Vv_of_mem_Vv hx hμ hμ' hμμ' ha ?_
  rw [e]
  exact (Vv V μ').inv_mem ha'

theorem isPair_mul_mem_Zv {x ρ : CosetGeom (A ⊔ B) A B} (hx : vtype x = true)
    (hρ : (graph (A ⊔ B) A B).Adj x ρ) {c c' : D} (hc : IsPair z V x ρ c)
    (hc' : IsPair z V x ρ c') : c * c' ∈ Zv z x := by
  obtain ⟨μ, μ', a, a', hμ, hμ', hμρ, hμ'ρ, hμμ', ha, ha1, ha', ha'1, rfl⟩ := hc
  obtain ⟨ν, ν', b, b', hν, hν', hνρ, hν'ρ, hνν', hb, hb1, hb', hb'1, rfl⟩ := hc'
  have hab := h.elemAbelian_Vv_B hx
  have hμ0 := vtype_eq_false_of_adj hμ hx
  have hμ'0 := vtype_eq_false_of_adj hμ' hx
  have hVμ : Vv V μ ≤ Vv V x := Vv_le_Vv_of_adj hμ.symm hμ0
  have hVμ' : Vv V μ' ≤ Vv V x := Vv_le_Vv_of_adj hμ'.symm hμ'0
  have hsq : ∀ y ∈ Vv V x, y⁻¹ = y := fun y hy => by
    have h2 := isElemAbelian_pow_eq_one hab hy
    exact inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  have hcases : ∀ w, (graph (A ⊔ B) A B).Adj x w → w ≠ ρ → w = μ ∨ w = μ' := by
    intro w hw hwρ
    rcases h.eq_or_eq_of_adj hρ hμ hμ' hw hμρ.symm hμ'ρ.symm hμμ' with e | e | e
    · exact absurd e hwρ
    · exact Or.inl e
    · exact Or.inr e
  have hpair : (ν = μ ∧ ν' = μ') ∨ (ν = μ' ∧ ν' = μ) := by
    rcases hcases ν hν hνρ with e | e
    · rcases hcases ν' hν' hν'ρ with e' | e'
      · exact absurd (e.trans e'.symm) hνν'
      · exact Or.inl ⟨e, e'⟩
    · rcases hcases ν' hν' hν'ρ with e' | e'
      · exact Or.inr ⟨e, e'⟩
      · exact absurd (e.trans e'.symm) hνν'
  rcases hpair with ⟨e, e'⟩ | ⟨e, e'⟩
  · subst e e'
    have h1 : a * b⁻¹ ∈ Zv z x := h.mul_inv_mem_Zv_of_Vv hμ0 hμ.symm hb hb1 ha ha1
    have h2 : a' * b'⁻¹ ∈ Zv z x := h.mul_inv_mem_Zv_of_Vv hμ'0 hμ'.symm hb' hb'1 ha' ha'1
    rw [hsq b (hVμ hb)] at h1
    rw [hsq b' (hVμ' hb')] at h2
    have hc : a' * b = b * a' := isElemAbelian_comm hab (hVμ' ha') (hVμ hb)
    have e1 : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc]
        _ = (a * b) * (a' * b') := by group
    rw [e1]
    exact (Zv z x).mul_mem h1 h2
  · subst e e'
    have h1 : a * b'⁻¹ ∈ Zv z x := h.mul_inv_mem_Zv_of_Vv hμ0 hμ.symm hb' hb'1 ha ha1
    have h2 : a' * b⁻¹ ∈ Zv z x := h.mul_inv_mem_Zv_of_Vv hμ'0 hμ'.symm hb hb1 ha' ha'1
    rw [hsq b' (hVμ hb')] at h1
    rw [hsq b (hVμ' hb)] at h2
    have hc1 : b * b' = b' * b := isElemAbelian_comm hab (hVμ' hb) (hVμ hb')
    have hc2 : a' * b' = b' * a' := isElemAbelian_comm hab (hVμ' ha') (hVμ hb')
    have e1 : a * a' * (b * b') = (a * b') * (a' * b) := by
      calc a * a' * (b * b') = a * a' * (b' * b) := by rw [hc1]
        _ = a * (a' * b') * b := by group
        _ = a * (b' * a') * b := by rw [hc2]
        _ = (a * b') * (a' * b) := by group
    rw [e1]
    exact (Zv z x).mul_mem h1 h2

theorem card_Vv_le_eight {x ρ μ μ' : CosetGeom (A ⊔ B) A B} (hx : vtype x = true)
    (hρ : (graph (A ⊔ B) A B).Adj x ρ) (hμ : (graph (A ⊔ B) A B).Adj x μ)
    (hμ' : (graph (A ⊔ B) A B).Adj x μ') (hρμ : ρ ≠ μ) (hρμ' : ρ ≠ μ') (hμμ' : μ ≠ μ')
    {b a' : D} (hb : b ∈ Vv V μ) (hb1 : b ∉ Zv z x) (ha' : a' ∈ Vv V μ') (ha1 : a' ∉ Zv z x)
    (hja : a' ∈ Vv V ρ ⊔ Subgroup.zpowers b) : Nat.card (Vv V x) ≤ 8 := by
  have hρ0 : vtype ρ = false := vtype_eq_false_of_adj hρ hx
  have hμ0 : vtype μ = false := vtype_eq_false_of_adj hμ hx
  have hμ'0 : vtype μ' = false := vtype_eq_false_of_adj hμ' hx
  have hZρ : Zv z x ≤ Vv V ρ := h.Zv_le_Vv hρ.symm hρ0
  have hμJ : Vv V μ ≤ Vv V ρ ⊔ Subgroup.zpowers b :=
    (h.Vv_le_Zv_sup_zpowers hμ0 hμ.symm hb hb1).trans
      (sup_le (hZρ.trans le_sup_left) le_sup_right)
  have hμ'J : Vv V μ' ≤ Vv V ρ ⊔ Subgroup.zpowers b :=
    (h.Vv_le_Zv_sup_zpowers hμ'0 hμ'.symm ha' ha1).trans
      (sup_le (hZρ.trans le_sup_left) (Subgroup.zpowers_le.mpr hja))
  have hxJ : Vv V x ≤ Vv V ρ ⊔ Subgroup.zpowers b := by
    refine (Vv_B_le_iff hx).mpr fun w hw => ?_
    rcases h.eq_or_eq_of_adj hρ hμ hμ' hw hρμ hρμ' hμμ' with rfl | rfl | rfl
    · exact le_sup_left
    · exact hμJ
    · exact hμ'J
  have hb3 := h.three_le_critDist
  have hdist : CosetGeom.dist ρ μ < critDist (A ⊔ B) A B V := by
    have h1 := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) ρ x μ
    have h2 : CosetGeom.dist ρ x = 1 := dist_eq_one_iff_adj.mpr hρ.symm
    have h3 : CosetGeom.dist x μ = 1 := dist_eq_one_iff_adj.mpr hμ
    omega
  have hcomm : Vv V ρ ≤ Subgroup.normalizer (Subgroup.zpowers b : Set D) := by
    intro y hy
    have hc := h.Vv_le_centralizer_of_dist rfl hρ0 hμ0 hdist
    exact mem_normalizer_zpowers_of_mul_comm
      (Subgroup.mem_centralizer_iff.mp (hc hy) b hb).symm
  have hb2 : b ^ 2 = 1 := by
    have hVμ : Vv V μ ≤ Vv V x := Vv_le_Vv_of_adj hμ.symm hμ0
    exact isElemAbelian_pow_eq_one (h.elemAbelian_Vv_B hx) (hVμ hb)
  have hc1 : Nat.card ↥(Vv V ρ ⊔ Subgroup.zpowers b) ≤
      Nat.card (Vv V ρ) * Nat.card (Subgroup.zpowers b) :=
    GoldAmN.card_sup_le_of_le_normalizer _ _ hcomm
  have hc2 := card_zpowers_le_two hb2
  have h3 := Subgroup.card_le_of_le hxJ
  rw [h.card_Vv_A hρ0] at hc1
  calc Nat.card (Vv V x) ≤ Nat.card ↥(Vv V ρ ⊔ Subgroup.zpowers b) := h3
    _ ≤ 4 * Nat.card (Subgroup.zpowers b) := hc1
    _ ≤ 4 * 2 := Nat.mul_le_mul_left 4 hc2

theorem isPair_not_mem_Vv (h16 : Nat.card (conjClosure V B) = 16)
    {x ρ : CosetGeom (A ⊔ B) A B} (hx : vtype x = true)
    (hρ : (graph (A ⊔ B) A B).Adj x ρ) {c : D} (hc : IsPair z V x ρ c) : c ∉ Vv V ρ := by
  intro hcV
  obtain ⟨μ, μ', a, a', hμ, hμ', hμρ, hμ'ρ, hμμ', ha, ha1, ha', ha'1, rfl⟩ := hc
  have hja : a' ∈ Vv V ρ ⊔ Subgroup.zpowers a := by
    have e : a' = a⁻¹ * (a * a') := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((Subgroup.zpowers a).inv_mem
      (Subgroup.mem_zpowers a))) (Subgroup.mem_sup_left hcV)
  have := h.card_Vv_le_eight hx hρ hμ hμ' hμρ.symm hμ'ρ.symm hμμ' ha ha1 ha' ha'1 hja
  rw [h.card_Vv_B_of h16 hx] at this
  omega

theorem isPair_comm {x ρ μ : CosetGeom (A ⊔ B) A B} (hρ : (graph (A ⊔ B) A B).Adj x ρ)
    (hμ : (graph (A ⊔ B) A B).Adj x μ) (hμρ : μ ≠ ρ) {k : ↥(A ⊔ B)} (hkx : k • x = x)
    (hkρ : k • ρ = ρ) (hk : (k : D) ∉ ballStab 1 x) {a : D} (ha : a ∈ Vv V μ)
    (ha1 : a ∉ Zv z x) : IsPair z V x ρ ((k : D) * a * (k : D)⁻¹ * a⁻¹) := by
  obtain ⟨hne, hadj, hnρ⟩ := h.smul_nbr_ne hρ hμ hμρ.symm hkx hkρ hk
  refine ⟨k • μ, μ, (k : D) * a * (k : D)⁻¹, a⁻¹, hadj, hμ, hnρ, hμρ, hne, ?_, ?_,
    (Vv V μ).inv_mem ha, ?_, rfl⟩
  · rw [h.Vv_smul' k μ]
    exact mul_mem_conjSub ha
  · rwa [h.conj_mem_Zv_iff hkx]
  · rwa [(Zv z x).inv_mem_iff]

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
