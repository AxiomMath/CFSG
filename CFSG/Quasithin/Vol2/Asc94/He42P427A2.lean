module

public import CFSG.Quasithin.Vol2.Asc94.He42P427A

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem p427_vecMulVec_zero : ∀ v w : HeJ.V2, Matrix.vecMulVec v w = 0 → v = 0 ∨ w = 0 := by
  decide

theorem p427_isPGroup_zpowers {H : Type} [Group H] [Finite H] {x : H} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hord : orderOf x ∣ 2 ^ 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hx)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem p427_invol_J (T : HeSetup G) (hB : T.BaseFacts) {j : G} (hj : j ∈ T.J) (hj2 : j * j = 1) :
    j ∈ T.A ∨ j ∈ T.A' := by
  obtain ⟨x, hx, y, hy, rfl⟩ := T.hD.exists_mul_of_mem_sup hj
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hB.A_sq x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hB.A'_sq y hy)
  obtain ⟨-, hm⟩ := T.hD.hT.comm x hx y hy
  have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [hxi, hyi]
    simpa only [mul_assoc] using hj2
  rw [hc1, T.hD.hT.m_one] at hm
  rcases p427_vecMulVec_zero _ _ hm.symm with h | h
  · have hxA' : x ∈ T.A' := (T.hD.hT.cu.zero x hx).1 h
    exact Or.inr (T.A'.mul_mem hxA' hy)
  · have hyA : y ∈ T.A := (T.hD.hT.cw.zero y hy).1 h
    exact Or.inl (T.A.mul_mem hx hyA)

theorem p427_A_le_L1 (T : HeSetup G) (hB : T.BaseFacts) : T.A ≤ T.L1 := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hB.A_comm b (hB.Z_le_A (hB.B_le_Z hb)) x hx

theorem p427_A'_le_L2 (T : HeSetup G) (hB : T.BaseFacts) : T.A' ≤ T.L2 := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hB.A'_comm b (hB.Z_le_A' (hB.B_le_Z hb)) x hx

theorem p427_J_le_L (T : HeSetup G) (hB : T.BaseFacts) : T.J ≤ T.L :=
  sup_le (le_trans (p427_A_le_L1 T hB) le_sup_left) (le_trans (p427_A'_le_L2 T hB) le_sup_right)

theorem p427_L_le_centB (T : HeSetup G) (hB : T.BaseFacts) :
    T.L ≤ centralizer (T.B : Set G) :=
  sup_le hB.L1_le_centralizer hB.L2_le_centralizer

theorem p427_J_relIndex_L (T : HeSetup G) (hB : T.BaseFacts) (hLcard : Nat.card T.L = 80640) :
    T.J.relIndex T.L = 315 := by
  have h := Subgroup.relIndex_mul_card T.J T.L
  rw [inf_eq_left.2 (p427_J_le_L T hB), hB.card_J, hLcard] at h
  omega

theorem p427_conj_L_J (T : HeSetup G) (hB : T.BaseFacts) (hLcard : Nat.card T.L = 80640)
    {w : G} (hwL : w ∈ T.L) (hw2 : w * w = 1) : ∃ l ∈ T.L, l⁻¹ * w * l ∈ T.J := by
  have hJL := p427_J_le_L T hB
  have hP : IsPGroup 2 (T.J.subgroupOf T.L) := by
    apply IsPGroup.of_card (n := 8)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv, hB.card_J]
    norm_num
  have hodd : Odd (T.J.subgroupOf T.L).index := by
    have h : (T.J.subgroupOf T.L).index = T.J.relIndex T.L := rfl
    rw [h, p427_J_relIndex_L T hB hLcard]
    decide
  have hQ : IsPGroup 2 (Subgroup.zpowers (⟨w, hwL⟩ : T.L)) :=
    p427_isPGroup_zpowers (x := (⟨w, hwL⟩ : T.L)) (Subtype.ext (by simpa using hw2))
  obtain ⟨g, hg⟩ := p427_conj_into hP hQ hodd
  refine ⟨(g : G), g.2, ?_⟩
  have h1 := hg ⟨w, hwL⟩ (Subgroup.mem_zpowers _)
  have h2 := Subgroup.mem_subgroupOf.1 h1
  simpa using h2

private theorem p427_mem_cent_conj (T : HeSetup G) {X : Subgroup G} (hXL : X ≤ T.L)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {l w : G} (hl : l ∈ T.L)
    (hj : l⁻¹ * w * l ∈ X) {x : G} (hx : x ∈ X) :
    l * x * l⁻¹ ∈ centralizer ({w} : Set G) ⊓ T.L := by
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
    T.L.mul_mem (T.L.mul_mem hl (hXL hx)) (T.L.inv_mem hl)⟩
  have hw : w = l * (l⁻¹ * w * l) * l⁻¹ := by group
  have hc := hXc x hx _ hj
  calc l * x * l⁻¹ * w = l * x * l⁻¹ * (l * (l⁻¹ * w * l) * l⁻¹) := by rw [← hw]
    _ = l * (x * (l⁻¹ * w * l)) * l⁻¹ := by group
    _ = l * ((l⁻¹ * w * l) * x) * l⁻¹ := by rw [hc]
    _ = (l * (l⁻¹ * w * l) * l⁻¹) * (l * x * l⁻¹) := by group
    _ = w * (l * x * l⁻¹) := by rw [← hw]

private theorem p427_card_cent_aux (T : HeSetup G) {X : Subgroup G} (hXL : X ≤ T.L)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX : Nat.card ↥X = 64) {l w : G} (hl : l ∈ T.L)
    (hj : l⁻¹ * w * l ∈ X) :
    64 ≤ Nat.card ↥(centralizer ({w} : Set G) ⊓ T.L) := by
  rw [← hX]
  have hinj : Function.Injective (fun x : ↥X =>
      (⟨l * (x : G) * l⁻¹, p427_mem_cent_conj T hXL hXc hl hj x.2⟩ :
        ↥(centralizer ({w} : Set G) ⊓ T.L))) := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    have h2 : (x : G) = (y : G) := by simpa using h1
    exact Subtype.ext h2
  exact Nat.card_le_card_of_injective _ hinj

theorem p427_card_cent_L (T : HeSetup G) (hB : T.BaseFacts) (hLcard : Nat.card T.L = 80640)
    {w : G} (hwL : w ∈ T.L) (hw2 : w * w = 1) :
    64 ≤ Nat.card ↥(centralizer ({w} : Set G) ⊓ T.L) := by
  obtain ⟨l, hl, hlJ⟩ := p427_conj_L_J T hB hLcard hwL hw2
  have hj2 : (l⁻¹ * w * l) * (l⁻¹ * w * l) = 1 := by
    rw [show (l⁻¹ * w * l) * (l⁻¹ * w * l) = l⁻¹ * (w * w) * l by group, hw2]
    group
  rcases p427_invol_J T hB hlJ hj2 with h | h
  · exact p427_card_cent_aux T ((p427_A_le_L1 T hB).trans le_sup_left) hB.A_comm hB.card_A hl h
  · exact p427_card_cent_aux T ((p427_A'_le_L2 T hB).trans le_sup_right) hB.A'_comm hB.card_A' hl h

end CFSG.Quasithin.A94.He42
