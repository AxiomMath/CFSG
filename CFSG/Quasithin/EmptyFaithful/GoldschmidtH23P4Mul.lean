module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H23P4

open scoped Pointwise

variable {G : Type*} [Group G]

theorem coe_sup_eq_mul_of_mul_comm {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * K := by
  let D : Subgroup G :=
    { carrier := (H : Set G) * K
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (K : Set G) * H := Set.mul_mem_mul hb hc
        rw [← h] at hbc
        obtain ⟨e, he, f, hf, hef⟩ := hbc
        have hef' : e * f = b * c := hef
        refine ⟨a * e, H.mul_mem ha he, f * d, K.mul_mem hf hd, ?_⟩
        calc a * e * (f * d) = a * (e * f) * d := by group
          _ = a * (b * c) * d := by rw [hef']
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := Set.mul_mem_mul (K.inv_mem hb) (H.inv_mem ha)
        rw [← h] at this
        obtain ⟨e, he, f, hf, hef⟩ := this
        have hef' : e * f = b⁻¹ * a⁻¹ := hef
        exact ⟨e, he, f, hf, by show e * f = (a * b)⁻¹; rw [hef']; group⟩ }
  have hD : (D : Set G) = (H : Set G) * K := rfl
  have : H ⊔ K = D := by
    apply le_antisymm
    · exact sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, by simp⟩)
        (fun x hx => ⟨1, H.one_mem, x, hx, by simp⟩)
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact (H ⊔ K).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  rw [this, hD]

theorem inf_mul_eq_mul_inf {H K I : Subgroup G} (hK : K ≤ I) :
    ((H : Set G) * K) ∩ (I : Set G) = ((H ⊓ I : Subgroup G) : Set G) * K := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hI⟩
    refine ⟨a, ⟨ha, ?_⟩, b, hb, rfl⟩
    have : a * b * b⁻¹ ∈ I := I.mul_mem hI (I.inv_mem (hK hb))
    simpa using this
  · rintro ⟨a, ⟨ha, haI⟩, b, hb, rfl⟩
    exact ⟨⟨a, ha, b, hb, rfl⟩, I.mul_mem haI (hK hb)⟩

theorem inf_mul_eq_mul_inf' {H K I : Subgroup G} (hK : K ≤ I) :
    ((K : Set G) * H) ∩ (I : Set G) = (K : Set G) * ((H ⊓ I : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hI⟩
    refine ⟨a, ha, b, ⟨hb, ?_⟩, rfl⟩
    have : a⁻¹ * (a * b) ∈ I := I.mul_mem (I.inv_mem (hK ha)) hI
    simpa using this
  · rintro ⟨a, ha, b, ⟨hb, hbI⟩, rfl⟩
    exact ⟨⟨a, ha, b, hb, rfl⟩, I.mul_mem (hK ha) hbI⟩

theorem mul_comm_inf_of_le {S Y N : Subgroup G} (h : (S : Set G) * Y = Y * S) (hY : Y ≤ N) :
    ((S ⊓ N : Subgroup G) : Set G) * Y = Y * ((S ⊓ N : Subgroup G) : Set G) := by
  have h1 := inf_mul_eq_mul_inf (H := S) hY
  have h2 := inf_mul_eq_mul_inf' (H := S) hY
  rw [← h1, ← h2, h]

theorem mul_comm_subgroupOf {A B N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (h : (A : Set G) * B = B * A) :
    ((A.subgroupOf N : Subgroup N) : Set N) * (B.subgroupOf N : Subgroup N) =
      (B.subgroupOf N : Subgroup N) * (A.subgroupOf N : Subgroup N) := by
  ext n
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hab : (a : G) * b ∈ (B : Set G) * A := by
      rw [← h]
      exact ⟨a, ha, b, hb, rfl⟩
    obtain ⟨b', hb', a', ha', hba⟩ := hab
    have hb'N : b' ∈ N := hB hb'
    have ha'N : a' ∈ N := hA ha'
    refine ⟨⟨b', hb'N⟩, hb', ⟨a', ha'N⟩, ha', ?_⟩
    apply Subtype.ext
    exact hba
  · rintro ⟨b, hb, a, ha, rfl⟩
    have hba : (b : G) * a ∈ (A : Set G) * B := by
      rw [h]
      exact ⟨b, hb, a, ha, rfl⟩
    obtain ⟨a', ha', b', hb', hab⟩ := hba
    have hb'N : b' ∈ N := hB hb'
    have ha'N : a' ∈ N := hA ha'
    refine ⟨⟨a', ha'N⟩, ha', ⟨b', hb'N⟩, hb', ?_⟩
    apply Subtype.ext
    exact hab

theorem card_eq_mul_of_coe_eq_mul {H K U : Subgroup G} (hU : (U : Set G) = (H : Set G) * K)
    (hd : H ⊓ K = ⊥) : Nat.card U = Nat.card H * Nat.card K := by
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ((H : Set G) ×ˢ (K : Set G)) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd'⟩ h
    simp only at h
    have h1 : c⁻¹ * a = d * b⁻¹ := by
      have : a * b = c * d := h
      calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
        _ = c⁻¹ * (c * d) * b⁻¹ := by rw [this]
        _ = d * b⁻¹ := by group
    have h2 : c⁻¹ * a ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem hc) ha, h1 ▸ K.mul_mem hd' (K.inv_mem hb)⟩
    rw [hd, Subgroup.mem_bot] at h2
    have h3 : c = a := by
      have := congrArg (c * ·) h2
      simpa using this.symm
    subst h3
    have h4 : d * b⁻¹ = 1 := by rw [← h1, inv_mul_cancel]
    have h5 : d = b := by
      have := congrArg (· * b) h4
      simpa using this
    subst h5
    rfl
  have himg : (fun p : G × G => p.1 * p.2) '' ((H : Set G) ×ˢ (K : Set G)) = (H : Set G) * K := by
    ext x
    simp only [Set.mem_image, Set.mem_prod, Set.mem_mul, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
  have h1 : Nat.card U = ((U : Set G)).ncard := (Nat.card_coe_set_eq _).symm
  rw [h1, hU, ← himg, hinj.ncard_image, Set.ncard_prod]
  rfl

theorem relIndex_eq_card_of_coe_eq_mul {H K U : Subgroup G} (hHU : H ≤ U)
    (hU : (U : Set G) = (H : Set G) * K) (hd : H ⊓ K = ⊥) [Finite G] :
    H.relIndex U = Nat.card K := by
  have h1 := card_eq_mul_of_coe_eq_mul hU hd
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := U)
  rw [inf_eq_left.mpr hHU] at h2
  have hpos : 0 < Nat.card H := Nat.card_pos
  have : H.relIndex U * Nat.card H = Nat.card K * Nat.card H := by
    rw [h2, h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem eq_of_isPGroup_two_of_le [Finite G] {S₀ T : Subgroup G} (hle : S₀ ≤ T)
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ S₀.index) : S₀ = T := by
  have h1 : S₀.relIndex T ∣ S₀.index := by
    rw [← Subgroup.relIndex_mul_index hle]
    exact dvd_mul_right _ _
  have h2 : S₀.relIndex T ∣ Nat.card T := by
    rw [← Subgroup.relIndex_mul_card (H := S₀) (K := T)]
    exact dvd_mul_right _ _
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn] at h2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k = 0 := by
    by_contra hk0
    apply hodd
    rw [hk] at h1
    exact (dvd_pow_self 2 hk0).trans h1
  rw [hk0, pow_zero] at hk
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hk)

end CFSG.Quasithin.H23P4
