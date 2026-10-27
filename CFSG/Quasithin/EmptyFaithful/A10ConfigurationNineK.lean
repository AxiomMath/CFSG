module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationNine

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

theorem card_dvd_factorial_mul [Finite G] {N J : Subgroup G} {S : Set G}
    (hS : ∀ k ∈ N, ∀ y ∈ S, k * y * k⁻¹ ∈ S)
    (hJ : ∀ k ∈ N, (∀ y ∈ S, k * y * k⁻¹ = y) → k ∈ J) :
    Nat.card N ∣ (Nat.card S).factorial * Nat.card J := by
  let σ : N → Equiv.Perm S := fun k =>
    { toFun := fun y => ⟨(k : G) * y * (k : G)⁻¹, hS k k.2 y y.2⟩
      invFun := fun y => ⟨(k : G)⁻¹ * y * (k : G), by
        have := hS (k⁻¹ : N) (N.inv_mem k.2) y y.2
        simpa using this⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  let φ : N →* Equiv.Perm S :=
    { toFun := σ
      map_one' := Equiv.ext fun y => Subtype.ext (by simp [σ])
      map_mul' := fun k₁ k₂ => Equiv.ext fun y => Subtype.ext (by
        simp only [σ, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hker : φ.ker ≤ J.subgroupOf N := by
    intro k hk
    rw [Subgroup.mem_subgroupOf]
    apply hJ k k.2
    intro y hy
    have h1 : φ k = 1 := hk
    have h2 := congrArg (fun p : Equiv.Perm S => ((p ⟨y, hy⟩ : S) : G)) h1
    simpa [φ, σ] using h2
  have h1 : Nat.card N = Nat.card (N ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (N ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h3 : Nat.card φ.range ∣ (Nat.card S).factorial := by
    rw [← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card φ.ker ∣ Nat.card J := by
    refine (Subgroup.card_dvd_of_le hker).trans ?_
    let f : J.subgroupOf N →* J :=
      ((N.subtype.comp (J.subgroupOf N).subtype)).codRestrict J (fun x => x.2)
    have hf : Function.Injective f := fun x y hxy => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun j : J => (j : G)) hxy
    exact Subgroup.card_dvd_of_injective f hf
  rw [h1, h2]
  exact Nat.mul_dvd_mul h3 h4

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def tK : Set G := {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y}

theorem tK_sub_B : ∀ y ∈ E.tK, y ∈ E.B := by
  rintro y ⟨k, hk, rfl⟩
  exact E.conj_mem_B_of_mem_K hk E.t_mem_B

theorem zK_inter_Lam [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {y : G} (hz : y ∈ E.zK) (hl : y ∈ E.Lam) : False := by
  obtain ⟨k, -, hk⟩ := hz
  obtain ⟨g, -, hg⟩ := hl
  apply E.t_not_conj_z hT hM
  refine ⟨k * g⁻¹, ?_⟩
  calc (k * g⁻¹)⁻¹ * E.z * (k * g⁻¹) = g * (k⁻¹ * E.z * k) * g⁻¹ := by group
    _ = g * (g⁻¹ * E.t * g) * g⁻¹ := by rw [hk, hg]
    _ = E.t := by group

theorem tK_inter_zK [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {y : G} (hz : y ∈ E.zK) (ht : y ∈ E.tK) : False := by
  obtain ⟨k, -, hk⟩ := hz
  obtain ⟨k', -, hk'⟩ := ht
  apply E.t_not_conj_z hT hM
  refine ⟨k * k'⁻¹, ?_⟩
  calc (k * k'⁻¹)⁻¹ * E.z * (k * k'⁻¹) = k' * (k⁻¹ * E.z * k) * k'⁻¹ := by group
    _ = k' * (k'⁻¹ * E.t * k') * k'⁻¹ := by rw [hk, hk']
    _ = E.t := by group

theorem zK_classify [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hLam : E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄)) :
    ∃ a b : Bool, (∀ w, (w ∈ A2 ∧ E.ι w ∈ E.zK) ↔ w ∈ Yset a b) ∧
      (a = true ↔ (u3 ∈ A2 ∧ E.ι u3 ∈ E.zK)) ∧ (b = true ↔ (u5 ∈ A2 ∧ E.ι u5 ∈ E.zK)) := by
  refine zset_classify (fun w => w ∈ A2 ∧ E.ι w ∈ E.zK) ⟨z0_mem_A2, E.z_mem_zK⟩
    (fun w hw => hw.1) ?_ ?_
  · rintro w ⟨hwA, hw⟩
    have hwB : E.ι w ∈ E.B := Subgroup.mem_map_of_mem _ hwA
    refine ⟨?_, ?_, ?_⟩
    · intro h1
      obtain ⟨k, -, hk⟩ := hw
      apply E.z_ne_one
      calc E.z = k * (k⁻¹ * E.z * k) * k⁻¹ := by group
        _ = 1 := by rw [hk, h1, map_one]; group
    · by_contra hD
      have hD' : D2 w = true := by simpa using hD
      refine E.zK_inter_Lam hT hM hw ?_
      rw [hLam]
      exact ⟨hwB, Or.inl (E.mem_Δ₂_iff.2 hD')⟩
    · by_contra hD
      have hD' : D4 w = true := by simpa using hD
      refine E.zK_inter_Lam hT hM hw ?_
      rw [hLam]
      exact ⟨hwB, Or.inr (E.mem_Δ₄_iff.2 hD')⟩
  · rintro w ⟨hwA, hw⟩ v hv
    refine ⟨conj_mem_A2_of_mem_Th hv hwA, ?_⟩
    have hvT : E.ι v ∈ T := E.mem_T_iff.2 ⟨v, hv, rfl⟩
    have := E.zK_inv hw (E.T_le_K hvT)
    simpa [map_mul, map_inv] using this

theorem zK_eq_image {a b : Bool} (hab : ∀ w, (w ∈ A2 ∧ E.ι w ∈ E.zK) ↔ w ∈ Yset a b) :
    E.zK = E.ι '' {w | w ∈ Yset a b} := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := E.zK_sub_B y hy
    exact ⟨w, (hab w).1 ⟨hw, hy⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ((hab w).2 hw).2

theorem zK_ncard {a b : Bool} (hab : ∀ w, (w ∈ A2 ∧ E.ι w ∈ E.zK) ↔ w ∈ Yset a b) :
    E.zK.ncard = 1 + 4 * a.toNat + 4 * b.toNat := by
  rw [E.zK_eq_image hab, Set.ncard_image_of_injective _ E.injective]
  have : {w | w ∈ Yset a b} = ↑(Yset a b) := by
    ext w
    simp
  rw [this, Set.ncard_coe_finset, card_Yset]

theorem card_K_zK (hBn : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) [Finite G]
    (hGz : Nat.card E.Gz = 384) : E.zK.ncard * 384 = Nat.card E.K := by
  have h := ncard_conjClass_mul_card E.K E.z
  have hinf : E.K ⊓ Subgroup.centralizer ({E.z} : Set G) = E.Gz :=
    inf_eq_right.2 (E.Gz_le_K hBn)
  rw [hinf, hGz] at h
  exact h

theorem false_of_zK_trivial [Finite G] (hOT : oTwoUpper (⊤ : Subgroup G) = ⊤)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hLam : E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄))
    (hab : ∀ w, (w ∈ A2 ∧ E.ι w ∈ E.zK) ↔ w ∈ Yset false false) : False := by
  have hKz : ∀ k ∈ E.K, k ∈ E.Gz := by
    intro k hk
    have hy : k⁻¹ * E.z * k ∈ E.zK := ⟨k, hk, rfl⟩
    obtain ⟨w, hw, hwy⟩ := E.zK_sub_B _ hy
    have hw' := (hab w).1 ⟨hw, hwy ▸ hy⟩
    rw [mem_Yset] at hw'
    have hwz : w = z0 := by simpa using hw'
    have h : k⁻¹ * E.z * k = E.z := by rw [← hwy, hwz]; rfl
    rw [E.mem_Gz]
    calc E.z * k = k * (k⁻¹ * E.z * k) := by group
      _ = k * E.z := by rw [h]
  have hx2 : E.ι u3 * E.ι u3 = 1 := E.ι_sq_eq_one.2 u3_sq
  have hx1 : E.ι u3 ≠ 1 := fun h => u3_ne_one (E.ι_eq_one.1 h)
  have hxB : E.ι u3 ∈ E.B := Subgroup.mem_map_of_mem _ u3_mem_A2
  rcases E.involution_fusion hOT hT hLam hx2 hx1 with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨k, hk, hkz⟩ := E.fusion_B hT hM E.z_mem_B (g := g) (by rw [hg]; exact hxB)
    have hP : u3 ∈ A2 ∧ E.ι u3 ∈ E.zK := ⟨u3_mem_A2, ⟨k, hk, by rw [hkz, hg]⟩⟩
    have := (hab u3).1 hP
    rw [mem_Yset] at this
    exact u3_ne_z0 (by simpa using this)
  · obtain ⟨k, hk, hkt⟩ := E.fusion_B hT hM E.t_mem_B (g := g) (by rw [hg]; exact hxB)
    have hxL : E.ι u3 ∈ E.Lam := ⟨k, hKz k hk, by rw [hkt, hg]⟩
    rw [hLam] at hxL
    rcases hxL.2 with h | h
    · have := E.mem_Δ₂_iff.1 h
      rw [D2_u3] at this
      exact absurd this (by decide)
    · have := E.mem_Δ₄_iff.1 h
      rw [D4_u3] at this
      exact absurd this (by decide)

theorem false_of_zK_nine [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hBn : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) (hGz : Nat.card E.Gz = 384)
    (hLam : E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄))
    (hab : ∀ w, (w ∈ A2 ∧ E.ι w ∈ E.zK) ↔ w ∈ Yset true true) : False := by
  have hLamcard : E.Lam.ncard = 6 := by
    have := E.Lam_card hEven hT hM
    omega
  have hS : ∀ k ∈ E.K, ∀ y ∈ E.Lam, k * y * k⁻¹ ∈ E.Lam := by
    intro k hk y hy
    have hyB : y ∈ E.B := by
      rw [hLam] at hy
      exact hy.1
    have hy'B : k * y * k⁻¹ ∈ E.B := by
      have := E.conj_mem_B_of_mem_K (E.K.inv_mem hk) hyB
      simpa using this
    obtain ⟨w, hwA, hw⟩ := hy'B
    have hyz : ∀ h : k * y * k⁻¹ ∈ E.zK, False := fun h => by
      have := E.zK_inv h hk
      have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rw [e] at this
      exact E.zK_inter_Lam hT hM this hy
    have hmemB : E.ι w ∈ E.B := Subgroup.mem_map_of_mem _ hwA
    rcases B_decomp w hwA with h | h | h | h | h | h
    · exfalso
      apply E.Lam_ne_one hy
      calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
        _ = 1 := by rw [← hw, h, map_one]; group
    · exfalso
      apply hyz
      rw [← hw, h]
      exact E.z_mem_zK
    · rw [← hw, hLam]
      exact ⟨hmemB, Or.inl (E.mem_Δ₂_iff.2 h)⟩
    · rw [← hw, hLam]
      exact ⟨hmemB, Or.inr (E.mem_Δ₄_iff.2 h)⟩
    · exfalso
      apply hyz
      rw [← hw]
      exact ((hab w).2 (mem_Yset.2 (Or.inr (Or.inl ⟨rfl, hwA, h⟩)))).2
    · exfalso
      apply hyz
      rw [← hw]
      exact ((hab w).2 (mem_Yset.2 (Or.inr (Or.inr ⟨rfl, hwA, h⟩)))).2
  have hJ : ∀ k ∈ E.K, (∀ y ∈ E.Lam, k * y * k⁻¹ = y) → k ∈ E.J := by
    intro k hk hc
    rw [← E.lemma_13_9_7 hEven hT hM, Subgroup.mem_centralizer_iff]
    have ht := hc E.t E.t_mem_Lam
    have htz := hc (E.t * E.z) (E.Lam_mul_z E.t_mem_Lam)
    have e : E.t * (E.t * E.z) = E.z := by rw [← mul_assoc, E.t_sq, one_mul]
    have hz : k * E.z * k⁻¹ = E.z := by
      calc k * E.z * k⁻¹ = k * (E.t * (E.t * E.z)) * k⁻¹ := by rw [e]
        _ = (k * E.t * k⁻¹) * (k * (E.t * E.z) * k⁻¹) := by group
        _ = E.t * (E.t * E.z) := by rw [ht, htz]
        _ = E.z := e
    rintro h (rfl | rfl)
    · exact (mul_inv_eq_iff_eq_mul.1 hz).symm
    · exact (mul_inv_eq_iff_eq_mul.1 ht).symm
  have hdvd := card_dvd_factorial_mul (N := E.K) (J := E.J) (S := E.Lam) hS hJ
  rw [Nat.card_coe_set_eq, hLamcard, E.card_J] at hdvd
  have hzK : E.zK.ncard = 9 := by
    have := E.zK_ncard hab
    simpa using this
  have hK := E.card_K_zK hBn hGz
  rw [hzK] at hK
  rw [← hK] at hdvd
  exact absurd hdvd (by decide)

theorem one_not_mem_zK : (1 : G) ∉ E.zK := by
  rintro ⟨k, -, hk⟩
  apply E.z_ne_one
  calc E.z = k * (k⁻¹ * E.z * k) * k⁻¹ := by group
    _ = 1 := by rw [hk]; group

theorem lemma_13_9_9 [Finite G] (hG : IsSimpleGroup G) (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.centralizer (E.B : Set G) = E.B ∧ Nat.card E.K = 1920 ∧
      (E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₃) ∨ E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₅)) ∧
      E.zK.ncard = 5 ∧ E.tK = (E.B : Set G) \ ({1} ∪ E.zK) ∧ E.tK.ncard = 10 ∧
      ∀ x : G, x * x = 1 → x ≠ 1 → (∃ g : G, g⁻¹ * E.z * g = x) ∨ ∃ g : G, g⁻¹ * E.t * g = x := by
  obtain ⟨hGz, hB, hQ, hQn, hBn, hLam⟩ := E.lemma_13_9_8 hG hEven hT hM
  obtain ⟨c, hc3, hc1⟩ := E.exists_order_three
  have hOT := oTwoUpper_top_eq_top hG hc3 hc1
  have hfus : ∀ x : G, x * x = 1 → x ≠ 1 →
      (∃ g : G, g⁻¹ * E.z * g = x) ∨ ∃ g : G, g⁻¹ * E.t * g = x :=
    fun x hx2 hx1 => E.involution_fusion hOT hT hLam hx2 hx1
  obtain ⟨a, b, hab, -, -⟩ := E.zK_classify hT hM hLam
  have hncard := E.zK_ncard hab
  have hK := E.card_K_zK hBn hGz
  have main : (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by
    cases a <;> cases b
    · exact (E.false_of_zK_trivial hOT hT hM hLam hab).elim
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact (E.false_of_zK_nine hEven hT hM hBn hGz hLam hab).elim
  have h5 : E.zK.ncard = 5 := by
    rcases main with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa using hncard
  have hshape : E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₃) ∨
      E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₅) := by
    rw [E.zK_eq_image hab]
    rcases main with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : w ∈ Yset true false := hw
        rcases mem_Yset.1 hw' with rfl | ⟨-, hwA, hD⟩ | ⟨h, -, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Subgroup.mem_map_of_mem _ hwA, E.mem_Δ₃_iff.2 hD⟩
        · exact absurd h (by decide)
      · rintro (rfl | ⟨⟨w, hwA, rfl⟩, hy⟩)
        · exact ⟨z0, mem_Yset.2 (Or.inl rfl), rfl⟩
        · exact ⟨w, mem_Yset.2 (Or.inr (Or.inl ⟨rfl, hwA, E.mem_Δ₃_iff.1 hy⟩)), rfl⟩
    · right
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : w ∈ Yset false true := hw
        rcases mem_Yset.1 hw' with rfl | ⟨h, -, -⟩ | ⟨-, hwA, hD⟩
        · exact Or.inl rfl
        · exact absurd h (by decide)
        · exact Or.inr ⟨Subgroup.mem_map_of_mem _ hwA, E.mem_Δ₅_iff.2 hD⟩
      · rintro (rfl | ⟨⟨w, hwA, rfl⟩, hy⟩)
        · exact ⟨z0, mem_Yset.2 (Or.inl rfl), rfl⟩
        · exact ⟨w, mem_Yset.2 (Or.inr (Or.inr ⟨rfl, hwA, E.mem_Δ₅_iff.1 hy⟩)), rfl⟩
  have htK : E.tK = (E.B : Set G) \ ({1} ∪ E.zK) := by
    ext y
    constructor
    · intro hy
      refine ⟨E.tK_sub_B y hy, ?_⟩
      rintro (h1 | hz)
      · obtain ⟨k, -, hk⟩ := hy
        apply E.t_ne_one
        calc E.t = k * (k⁻¹ * E.t * k) * k⁻¹ := by group
          _ = 1 := by rw [hk, h1]; group
      · exact E.tK_inter_zK hT hM hz hy
    · rintro ⟨hyB, hy⟩
      have hy1 : y ≠ 1 := fun h => hy (Or.inl h)
      have hyz : y ∉ E.zK := fun h => hy (Or.inr h)
      obtain ⟨w, hwA, rfl⟩ := hyB
      have hw1 : w ≠ 1 := fun h => hy1 (by rw [h, map_one])
      have hy2 : E.ι w * E.ι w = 1 := E.ι_sq_eq_one.2 (B_ne_one_involution w hwA hw1)
      have hwB : E.ι w ∈ E.B := Subgroup.mem_map_of_mem _ hwA
      rcases hfus _ hy2 hy1 with ⟨g, hg⟩ | ⟨g, hg⟩
      · exfalso
        obtain ⟨k, hk, hkz⟩ := E.fusion_B hT hM E.z_mem_B (g := g) (by rw [hg]; exact hwB)
        exact hyz ⟨k, hk, by rw [hkz, hg]⟩
      · obtain ⟨k, hk, hkt⟩ := E.fusion_B hT hM E.t_mem_B (g := g) (by rw [hg]; exact hwB)
        exact ⟨k, hk, by rw [hkt, hg]⟩
  have hU : (({1} : Set G) ∪ E.zK).ncard = 6 := by
    rw [Set.ncard_union_eq (Set.disjoint_singleton_left.2 E.one_not_mem_zK)
      (Set.finite_singleton _) (Set.toFinite _), Set.ncard_singleton, h5]
  have hsub : (({1} : Set G) ∪ E.zK) ⊆ (E.B : Set G) := by
    rintro y (rfl | hy)
    · exact E.B.one_mem
    · exact E.zK_sub_B y hy
  have hBcard : (E.B : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact E.card_B
  refine ⟨E.centralizer_B hEven hT hM, ?_, hshape, h5, htK, ?_, hfus⟩
  · rw [h5] at hK
    omega
  · rw [htK, Set.ncard_sdiff hsub, hBcard, hU]

@[expose] def Through139 : Prop :=
  T < E.Gz ∧ Nat.card E.Gz = 384 ∧ E.B ≤ pCoreOf 2 E.Gz ∧ E.Q ≤ pCoreOf 2 E.Gz ∧
    (∀ g ∈ E.Gz, ∀ q ∈ E.Q, g * q * g⁻¹ ∈ E.Q) ∧
    (∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) ∧
    E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄) ∧
    Subgroup.centralizer (E.B : Set G) = E.B ∧ Nat.card E.K = 1920 ∧
    (E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₃) ∨ E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₅)) ∧
    E.zK.ncard = 5 ∧ E.tK = (E.B : Set G) \ ({1} ∪ E.zK) ∧ E.tK.ncard = 10 ∧
    ∀ x : G, x * x = 1 → x ≠ 1 → (∃ g : G, g⁻¹ * E.z * g = x) ∨ ∃ g : G, g⁻¹ * E.t * g = x

theorem through_13_9_9 [Finite G] (hG : IsSimpleGroup G) (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) : E.Through139 := by
  obtain ⟨hlt, -⟩ := E.lemma_13_9_5 hG hT hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := E.lemma_13_9_8 hG hEven hT hM
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := E.lemma_13_9_9 hG hEven hT hM
  exact ⟨hlt, h1, h2, h3, h4, h5, h6, k1, k2, k3, k4, k5, k6, k7⟩

end Emb

end CFSG.Quasithin.A10
