module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Str

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

theorem GoldHyp.not_normal_T_left (h : GoldHyp A B) :
    ¬ A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  intro hAN
  have hTQ : A ⊓ B ≤ pCoreOf 2 A :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hAN h.vertex_left.isPGroup
  have h1 : (pCoreOf 2 A).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hTQ
  have h2 := h.vertex_left.relIndex_pCoreOf_T
  omega

theorem GoldHyp.not_normal_T_right (h : GoldHyp A B) :
    ¬ B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  intro hBN
  have hTP : A ⊓ B ≤ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hBN h.vertex_right.isPGroup
  have h1 : (pCoreOf 2 B).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hTP
  have h2 := h.vertex_right.relIndex_pCoreOf_T
  omega

theorem GoldHyp.sup_conjSub_inf_eq_left (h : GoldHyp A B) {c : D} (hcA : c ∈ A) (hcB : c ∉ B) :
    (A ⊓ B) ⊔ conjSub c (A ⊓ B) = A := by
  have hTA : A ⊓ B ≤ A := inf_le_left
  have hcT : c ∉ A ⊓ B := fun hc => hcB hc.2
  have hconj : conjSub c (A ⊓ B) ≤ A := fun x hx => by
    have hx' := (mem_conjSub.mp hx).1
    have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [e]
    exact A.mul_mem (A.mul_mem hcA hx') (A.inv_mem hcA)
  have hH : (A ⊓ B) ⊔ conjSub c (A ⊓ B) ≤ A := sup_le hTA hconj
  have hmul := Subgroup.relIndex_mul_relIndex (A ⊓ B) ((A ⊓ B) ⊔ conjSub c (A ⊓ B)) A
    le_sup_left hH
  rw [h.relIndex_left] at hmul
  have hdvd : ((A ⊓ B) ⊔ conjSub c (A ⊓ B)).relIndex A ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact le_antisymm hH (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h3] at hmul
    have hle : (A ⊓ B) ⊔ conjSub c (A ⊓ B) ≤ A ⊓ B :=
      Subgroup.relIndex_eq_one.mp (by omega)
    have hcn : conjSub c (A ⊓ B) ≤ A ⊓ B := le_sup_right.trans hle
    have heq : conjSub c (A ⊓ B) = A ⊓ B :=
      Subgroup.eq_of_le_of_card_ge hcn (by rw [card_conjSub])
    have hcN : c ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
      mem_normalizer_of_conjSub_eq heq
    have hTM : A ⊓ B ≤ A ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
      le_inf hTA Subgroup.le_normalizer
    have hmul2 := Subgroup.relIndex_mul_relIndex _ _ _ hTM
      (inf_le_left : A ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) ≤ A)
    rw [h.relIndex_left] at hmul2
    have hdvd2 : (A ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D)).relIndex A ∣ 3 :=
      Dvd.intro_left _ hmul2
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with k1 | k3
    · exact h.not_normal_T_left fun g hg => (Subgroup.relIndex_eq_one.mp k1 hg).2
    · rw [k3] at hmul2
      have hM : A ⊓ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) ≤ A ⊓ B :=
        Subgroup.relIndex_eq_one.mp (by omega)
      exact hcT (hM ⟨hcA, hcN⟩)

end GoldAmL

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem mul_inv_mem_of_relIndex_eq_two {H K : Subgroup D} (h2 : H.relIndex K = 2) {x y : D}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x * y⁻¹ ∈ H := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
  have hxa : x * a ∈ H := by
    rcases ha x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hxH
  have hya : y * a ∈ H := by
    rcases ha y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyH
  have e : x * y⁻¹ = (x * a) * (y * a)⁻¹ := by group
  rw [e]
  exact H.mul_mem hxa (H.inv_mem hya)

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem relIndex_zpowers_V : (Subgroup.zpowers z).relIndex V = 2 := by
  have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers z) V
  rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr h.natural.z_mem_V), h.natural.card_eq,
    Nat.card_zpowers, orderOf_eq_prime h.natural.z_sq h.natural.z_ne] at h1
  omega

omit [Finite D] in
theorem commutator_U_T (hU : Nat.card (conjClosure V B) = 8) {t u : D} (ht : t ∈ A ⊓ B)
    (hu : u ∈ conjClosure V B) : t * u * t⁻¹ * u⁻¹ ∈ V := by
  have hNV := h.natural.reduced.2.1
  have htU : t * u * t⁻¹ ∈ conjClosure V B :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B ht.2) u).mp hu
  by_cases huV : u ∈ V
  · have : t * u * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hNV ht.1) u).mp huV
    exact V.mul_mem this (V.inv_mem huV)
  · have hV' : t * u * t⁻¹ ∉ V := fun hx =>
      huV ((Subgroup.mem_normalizer_iff.mp (hNV ht.1) u).mpr hx)
    have := h.mul_inv_mem_V_of_not_mem hU htU hu hV' huV
    simpa [mul_assoc] using this

omit [Finite D] in
theorem commutator_V_T {t v : D} (ht : t ∈ A ⊓ B) (hv : v ∈ V) :
    t * v * t⁻¹ * v⁻¹ ∈ Subgroup.zpowers z := by
  have hNV := h.natural.reduced.2.1
  have htc : t * z = z * t := Subgroup.mem_centralizer_iff.mp h.natural.z_mem.2 t ht
  have htz : ∀ k : ℤ, t * z ^ k * t⁻¹ = z ^ k := fun k => by
    rw [← conj_zpow, show t * z * t⁻¹ = z by rw [htc]; group]
  have htV : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hNV ht.1) v).mp hv
  by_cases hvz : v ∈ Subgroup.zpowers z
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hvz
    rw [htz k]
    simp
  · have hvz' : t * v * t⁻¹ ∉ Subgroup.zpowers z := fun hx => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      apply hvz
      have e : v = t⁻¹ * (t * v * t⁻¹) * t := by group
      rw [e, ← hk]
      have := htz k
      have e2 : t⁻¹ * z ^ k * t = z ^ k := by
        calc t⁻¹ * z ^ k * t = t⁻¹ * (t * z ^ k * t⁻¹) * t := by rw [this]
          _ = z ^ k := by group
      rw [e2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
    exact mul_inv_mem_of_relIndex_eq_two h.relIndex_zpowers_V htV hv hvz' hvz

theorem exists_conj_of_mem_V {c : D} (hc : c ∈ V) (hc1 : c ≠ 1) :
    ∃ a ∈ A, c = a * z * a⁻¹ := by
  obtain ⟨a₀, ha1, haz, hVset⟩ := h.natural.basis
  have hmem : ∀ u : D, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a₀ ∨ u = z * a₀ := fun u => by
    have := Set.ext_iff.mp hVset u
    simpa using this
  have hNV := h.natural.reduced.2.1
  obtain ⟨a, haA, ha3⟩ := h.gold.vertex_left.exists_order_three
  have haT := h.gold.vertex_left.not_mem_of_orderOf ha3
  have hcube : a * a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha3, pow_three'] at this
  have ha4 : a * a * (a * a) = a := by
    calc a * a * (a * a) = (a * a * a) * a := by group
      _ = a := by rw [hcube, one_mul]
  have hzV := h.natural.z_mem_V
  have hz1 : a * z * a⁻¹ ≠ z := fun hconj => haT
    (inf_normalizer_zpowers_le h.gold h.natural
      ⟨haA, mem_normalizer_zpowers_of_mul_comm (mul_inv_eq_iff_eq_mul.mp hconj)⟩)
  have hz₁V : a * z * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hNV haA) z).mp hzV
  have hz₂V : a * (a * z * a⁻¹) * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hNV haA) _).mp hz₁V
  have hz₁1 : a * z * a⁻¹ ≠ 1 := fun e => h.natural.z_ne (by
    have : z = a⁻¹ * (a * z * a⁻¹) * a := by group
    rw [this, e]; group)
  have hz₂1 : a * (a * z * a⁻¹) * a⁻¹ ≠ 1 := fun e => hz₁1 (by
    have : a * z * a⁻¹ = a⁻¹ * (a * (a * z * a⁻¹) * a⁻¹) * a := by group
    rw [this, e]; group)
  have hz₂z₁ : a * (a * z * a⁻¹) * a⁻¹ ≠ a * z * a⁻¹ := fun e => hz1 (by
    calc a * z * a⁻¹ = a⁻¹ * (a * (a * z * a⁻¹) * a⁻¹) * a := by group
      _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [e]
      _ = z := by group)
  have hz₂z : a * (a * z * a⁻¹) * a⁻¹ ≠ z := fun e => hz1 (by
    have e' : a * a * z * (a * a)⁻¹ = z := by
      calc a * a * z * (a * a)⁻¹ = a * (a * z * a⁻¹) * a⁻¹ := by group
        _ = z := e
    calc a * z * a⁻¹ = (a * a * (a * a)) * z * (a * a * (a * a))⁻¹ := by rw [ha4]
      _ = (a * a) * (a * a * z * (a * a)⁻¹) * (a * a)⁻¹ := by group
      _ = z := by rw [e', e'])
  have hz₁cases : a * z * a⁻¹ = a₀ ∨ a * z * a⁻¹ = z * a₀ := by
    rcases (hmem _).mp hz₁V with e | e | e | e
    · exact absurd e hz₁1
    · exact absurd e hz1
    · exact Or.inl e
    · exact Or.inr e
  have hz₂cases : a * (a * z * a⁻¹) * a⁻¹ = a₀ ∨ a * (a * z * a⁻¹) * a⁻¹ = z * a₀ := by
    rcases (hmem _).mp hz₂V with e | e | e | e
    · exact absurd e hz₂1
    · exact absurd e hz₂z
    · exact Or.inl e
    · exact Or.inr e
  have hA2 : a * a ∈ A := A.mul_mem haA haA
  have e2 : a * (a * z * a⁻¹) * a⁻¹ = a * a * z * (a * a)⁻¹ := by group
  rcases (hmem c).mp hc with rfl | rfl | rfl | rfl
  · exact absurd rfl hc1
  · exact ⟨1, A.one_mem, by group⟩
  · rcases hz₁cases with e1 | e1
    · exact ⟨a, haA, e1.symm⟩
    · rcases hz₂cases with e3 | e3
      · exact ⟨a * a, hA2, by rw [← e2, e3]⟩
      · exact absurd (e3.trans e1.symm) hz₂z₁
  · rcases hz₁cases with e1 | e1
    · rcases hz₂cases with e3 | e3
      · exact absurd (e3.trans e1.symm) hz₂z₁
      · exact ⟨a * a, hA2, by rw [← e2, e3]⟩
    · exact ⟨a, haA, e1.symm⟩

omit [Finite D] in
theorem normalizes_zpowers : B ≤ Subgroup.normalizer (Subgroup.zpowers z : Set D) := fun y hy =>
  Subgroup.centralizer_le_normalizer _
    (mem_centralizer_zpowers_of_mul_comm (GoldAmL.mul_eq_of_conj_eq (h.central y hy)))

theorem not_le_normalizer_conjClosure :
    ¬ A ≤ Subgroup.normalizer (conjClosure V B : Set D) := fun hA =>
  h.natural.natural.ne_bot (le_bot_iff.mp ((le_conjClosure V B).trans
    (h.gold.eq_bot_of_normalizes hA (le_normalizer_conjClosure V B)
      (h.conjClosure_le_pCoreOf_left.trans h.gold.pCoreOf_left_le)).le))

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
