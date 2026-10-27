module

public import CFSG.Quasithin.EmptyFaithful.S146E6
public import CFSG.Quasithin.EmptyFaithful.S146E10

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Quad

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizerMod_sq_le {Z E : Subgroup G} {a : G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hZE : Z ≤ E) (haE : ∀ x ∈ E, a * x * a⁻¹ ∈ E) (ha2 : a * a = 1)
    (haZ : ∀ z ∈ Z, a * z * a⁻¹ = z) :
    ((centralizerMod Z E (Subgroup.zpowers a)).relIndex E) ^ 2 ≤ Z.relIndex E := by
  classical
  let _ : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun x y => Subtype.ext (hEc x x.2 y y.2) }
  let σ : ↥E →* ↥E :=
    { toFun := fun x => ⟨a * x * a⁻¹, haE x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp [mul_assoc] }
  have hσ : ∀ x : ↥E, ((σ x : ↥E) : G) = a * x * a⁻¹ := fun x => rfl
  let ψ : ↥E →* ↥E :=
    { toFun := fun x => σ x * x⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm y⁻¹ x⁻¹]
        exact mul_mul_mul_comm _ _ _ _ }
  have hψ : ∀ x : ↥E, ((ψ x : ↥E) : G) = a * x * a⁻¹ * (x : G)⁻¹ := fun x => rfl
  have hE2' : ∀ x : ↥E, x * x = 1 := fun x => Subtype.ext (hE2 x x.2)
  have hσσ : ∀ x : ↥E, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    rw [hσ, hσ]
    have ha' : a⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one]; exact ha2
    rw [ha']
    calc a * (a * (x : G) * a) * a = (a * a) * (x : G) * (a * a) := by group
      _ = x := by rw [ha2]; group
  have hψψ : ∀ x : ↥E, ψ (ψ x) = 1 := by
    intro x
    have h2 : x * x = 1 := hE2' x
    have h3 : σ x * σ x = 1 := by rw [← map_mul, h2, map_one]
    have hinvx : x⁻¹ = x := inv_eq_of_mul_eq_one_right h2
    have hinvσ : (σ x)⁻¹ = σ x := inv_eq_of_mul_eq_one_right h3
    show σ (σ x * x⁻¹) * (σ x * x⁻¹)⁻¹ = 1
    simp only [hinvx, hinvσ, map_mul, hσσ, mul_inv_rev]
    calc x * σ x * (x * σ x) = (x * x) * (σ x * σ x) := by rw [mul_mul_mul_comm]
      _ = 1 := by rw [h2, h3, mul_one]
  have hZn : E ≤ Subgroup.normalizer (Z : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have key : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
      have := hEc x hx z (hZE hz)
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [this]
        _ = z := by group
    constructor
    · intro hn; rw [key n hn]; exact hn
    · intro hn
      have h2 := hEc x hx _ (hZE hn)
      have e : n = x⁻¹ * (x * n * x⁻¹) * x := by group
      rw [e, show x⁻¹ * (x * n * x⁻¹) * x = x * n * x⁻¹ by
        calc x⁻¹ * (x * n * x⁻¹) * x = x⁻¹ * ((x * n * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * n * x⁻¹)) := by rw [← h2]
          _ = x * n * x⁻¹ := by group]
      exact hn
  have hNn : (Z.subgroupOf E).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZE).mpr hZn
  set N : Subgroup ↥E := Z.subgroupOf E with hNdef
  have hψN : N ≤ N.comap ψ := by
    intro z hz
    have hz' : (z : G) ∈ Z := hz
    have h1 : ψ z = 1 := by
      apply Subtype.ext
      rw [hψ, haZ z hz']
      simp
    show ψ z ∈ N
    rw [h1]
    exact N.one_mem
  let χ : ↥E ⧸ N →* ↥E ⧸ N := QuotientGroup.map N N ψ hψN
  have hχ : ∀ x : ↥E, χ (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := fun x => rfl
  have hzp : ∀ u ∈ Subgroup.zpowers a, u = 1 ∨ u = a := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have ha2' : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha2
    rw [zpow_eq_zpow_emod k ha2']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  have hker : ∀ x : ↥E, χ (QuotientGroup.mk x) = 1 ↔
      x ∈ (centralizerMod Z E (Subgroup.zpowers a)).subgroupOf E := by
    intro x
    rw [hχ, QuotientGroup.eq_one_iff]
    show ψ x ∈ Z.subgroupOf E ↔ x ∈ (centralizerMod Z E (Subgroup.zpowers a)).subgroupOf E
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_centralizerMod, hψ]
    constructor
    · intro hx
      refine ⟨x.2, hZn x.2, fun u hu => ?_⟩
      rcases hzp u hu with h | h
      · rw [h]; simp
      · rw [h]
        have e : (x : G) * a * (x : G)⁻¹ * a⁻¹ = (a * x * a⁻¹ * (x : G)⁻¹)⁻¹ := by group
        rw [e]; exact Z.inv_mem hx
    · rintro ⟨-, -, h⟩
      have h1 := h a (Subgroup.mem_zpowers a)
      have e : a * (x : G) * a⁻¹ * (x : G)⁻¹ = ((x : G) * a * (x : G)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]; exact Z.inv_mem h1
  have hrange_le : χ.range ≤ χ.ker := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    show χ (χ (QuotientGroup.mk x)) = 1
    rw [hχ, hχ, hψψ]
    rfl
  have hcomap : (centralizerMod Z E (Subgroup.zpowers a)).subgroupOf E =
      χ.ker.comap (QuotientGroup.mk' N) := by
    ext x
    rw [← hker]
    rfl
  have hidx1 : (centralizerMod Z E (Subgroup.zpowers a)).relIndex E = χ.ker.index := by
    unfold Subgroup.relIndex
    rw [hcomap]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hidx2 : Z.relIndex E = Nat.card (↥E ⧸ N) := rfl
  have hi := Subgroup.index_ker χ
  have hm := Subgroup.card_mul_index χ.ker
  have hle : Nat.card χ.range ≤ Nat.card χ.ker := Subgroup.card_le_of_le hrange_le
  rw [hidx1, hidx2, ← hm, sq, hi]
  exact Nat.mul_le_mul_right _ hle

end Quad

section General1

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_le_relIndex {A B Ω : Subgroup G} (hB : B ≤ Ω) (hA : A ≤ Ω)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : (A ⊓ B).relIndex B ≤ A.relIndex Ω := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm
  have hAP : A ≤ A ⊔ B := le_sup_left
  have hPΩ : A ⊔ B ≤ Ω := sup_le hA hB
  have e1 := Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr hAP] at e1
  have e2 := Subgroup.relIndex_mul_card (A ⊓ B) B
  rw [inf_eq_left.mpr inf_le_right] at e2
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hIpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  have key : A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hApos hIpos) ?_
    calc A.relIndex (A ⊔ B) * (Nat.card A * Nat.card ↥(A ⊓ B))
        = (A.relIndex (A ⊔ B) * Nat.card A) * Nat.card ↥(A ⊓ B) := by ring
      _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [e1]
      _ = Nat.card A * Nat.card B := hc
      _ = Nat.card A * ((A ⊓ B).relIndex B * Nat.card ↥(A ⊓ B)) := by rw [e2]
      _ = (A ⊓ B).relIndex B * (Nat.card A * Nat.card ↥(A ⊓ B)) := by ring
  rw [← key]
  have := Subgroup.relIndex_mul_relIndex A (A ⊔ B) Ω hAP hPΩ
  rw [← this]
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _))

end General1

section General2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizerMod_zpowers_iff {Z E : Subgroup G} {a x : G} (ha2 : a * a = 1) :
    x ∈ centralizerMod Z E (Subgroup.zpowers a) ↔
      x ∈ E ∧ x ∈ Subgroup.normalizer (Z : Set G) ∧ a * x * a⁻¹ * x⁻¹ ∈ Z := by
  have hzp : ∀ u ∈ Subgroup.zpowers a, u = 1 ∨ u = a := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have ha2' : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha2
    rw [zpow_eq_zpow_emod k ha2']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  rw [mem_centralizerMod]
  constructor
  · rintro ⟨hE, hN, h⟩
    refine ⟨hE, hN, ?_⟩
    have h1 := h a (Subgroup.mem_zpowers a)
    have e : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]; exact Z.inv_mem h1
  · rintro ⟨hE, hN, h⟩
    refine ⟨hE, hN, fun u hu => ?_⟩
    rcases hzp u hu with h' | h'
    · rw [h']; simp
    · rw [h']
      have e : x * a * x⁻¹ * a⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]; exact Z.inv_mem h

omit [Finite G] in
theorem comm_mul_of_abelian {E : Subgroup G} {a x y : G} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (haE : ∀ x ∈ E, a * x * a⁻¹ ∈ E) (hx : x ∈ E) (hy : y ∈ E) :
    a * (x * y) * a⁻¹ * (x * y)⁻¹ = (a * x * a⁻¹ * x⁻¹) * (a * y * a⁻¹ * y⁻¹) := by
  have hq : a * y * a⁻¹ ∈ E := haE y hy
  have hc : x⁻¹ * ((a * y * a⁻¹) * y⁻¹) = ((a * y * a⁻¹) * y⁻¹) * x⁻¹ :=
    hEc _ (E.inv_mem hx) _ (E.mul_mem hq (E.inv_mem hy))
  calc a * (x * y) * a⁻¹ * (x * y)⁻¹
      = (a * x * a⁻¹) * (((a * y * a⁻¹) * y⁻¹) * x⁻¹) := by group
    _ = (a * x * a⁻¹) * (x⁻¹ * ((a * y * a⁻¹) * y⁻¹)) := by rw [← hc]
    _ = (a * x * a⁻¹ * x⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group

theorem exists_u_of_relIndex_eight {Z E : Subgroup G} {a : G}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hZE : Z ≤ E) (haE : ∀ x ∈ E, a * x * a⁻¹ ∈ E) (ha2 : a * a = 1)
    (haZ : ∀ z ∈ Z, a * z * a⁻¹ = z) (h8 : Z.relIndex E = 8) :
    ∃ u₁ ∈ E, ∀ y ∈ E, a * y * a⁻¹ * y⁻¹ ∈ Z ∨ (a * y * a⁻¹ * y⁻¹) * u₁⁻¹ ∈ Z := by
  classical
  have hq := relIndex_centralizerMod_sq_le hEc hE2 hZE haE ha2 haZ
  rw [h8] at hq
  set C := centralizerMod Z E (Subgroup.zpowers a) with hC
  have hpos : 0 < C.relIndex E := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have hle2 : C.relIndex E ≤ 2 := by
    by_contra h
    push Not at h
    have : 9 ≤ C.relIndex E ^ 2 := by nlinarith
    omega
  have hdvd : C.relIndex E ∣ 2 := by
    interval_cases hn : C.relIndex E
    · exact one_dvd _
    · exact dvd_refl _
  obtain ⟨b, hbE, hb⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd
  have hmemC : ∀ x, x ∈ C ↔ x ∈ E ∧ x ∈ Subgroup.normalizer (Z : Set G) ∧ a * x * a⁻¹ * x⁻¹ ∈ Z :=
    fun x => mem_centralizerMod_zpowers_iff ha2
  have hu1E : a * b * a⁻¹ * b⁻¹ ∈ E := E.mul_mem (haE b hbE) (E.inv_mem hbE)
  refine ⟨a * b * a⁻¹ * b⁻¹, hu1E, fun y hy => ?_⟩
  rcases hb y hy with hyb | hyC
  · right
    have h1 := ((hmemC _).mp hyb).2.2
    rw [comm_mul_of_abelian hEc haE hy hbE] at h1
    have hu2 : (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
      have := hE2 _ hu1E
      exact this
    have hinv : (a * b * a⁻¹ * b⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ := inv_eq_of_mul_eq_one_right hu2
    rw [hinv]
    exact h1
  · left
    exact ((hmemC _).mp hyC).2.2

end General2

section NMem

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_two_iff {Zz : Subgroup G} {u₁ u₂ x : G} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hZ1 : ∀ y ∈ Zz, y * u₁ = u₁ * y)
    (hA2 : ∀ y ∈ Zz ⊔ Subgroup.zpowers u₁, y * u₂ = u₂ * y) :
    x ∈ (Zz ⊔ Subgroup.zpowers u₁) ⊔ Subgroup.zpowers u₂ ↔
      (x ∈ Zz ∨ x * u₁⁻¹ ∈ Zz) ∨ (x * u₂⁻¹ ∈ Zz ∨ x * u₂⁻¹ * u₁⁻¹ ∈ Zz) := by
  rw [mem_sup_zpowers_iff hu₂ hA2, mem_sup_zpowers_iff hu₁ hZ1, mem_sup_zpowers_iff hu₁ hZ1]

end NMem

end CFSG.Quasithin
