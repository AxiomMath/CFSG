module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixAbsCent

public section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.QuasithinUnique CFSG.Quasithin

section Main

variable {X H : Type} [Group X] [Group H] [Finite X] [Finite H] {Φ : X →* H} {ψ : H}
  {α : MulAut X}

theorem OutProps.isSylowTwoOf_inf_centralizer_invol (P : OutProps Φ ψ α) (ha : 1 ≤ twoExp ψ)
    {U : Subgroup X} (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) (hUS : IsSylowTwoOf U ⊤)
    {N : Subgroup H} (hTN : spT Φ ψ U ≤ N) {m : ℕ}
    (hge : m ≤ Nat.card ↥(fixSub (involAut ψ α) U))
    (hle : ∀ u ∈ U, (twistFix (involAut ψ α) U u).ncard ≤ m) :
    IsSylowTwoOf (spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H))
      (Subgroup.centralizer ({invol ψ} : Set H) ⊓ N) := by
  refine isSylowTwoOf_centralizer_inf P.range_normal (P.isSylowTwoOf_spT hU hUS) hTN
    (invol_mem_spT U) (invol_sq ha) (P.invol_not_mem_range ha) ?_
  intro f' hf'T hf'R hf'2
  obtain ⟨u, hu, rfl⟩ := P.exists_eq_mul_invol ha hU hf'T hf'R hf'2
  rw [P.card_inf_centralizer_invol hU]
  calc _ ≤ 2 ^ twoExp ψ * (twistFix (involAut ψ α) U u).ncard := P.card_inf_centralizer_le hU u
    _ ≤ 2 ^ twoExp ψ * m := Nat.mul_le_mul_left _ (hle u hu)
    _ ≤ 2 ^ twoExp ψ * Nat.card ↥(fixSub (involAut ψ α) U) := Nat.mul_le_mul_left _ hge
    _ = _ := mul_comm _ _

omit [Finite X] [Finite H] in
theorem OutProps.psi2_pow_comm_of_fixed (P : OutProps Φ ψ α) {y : X} (hy : α y = y) (s : ℕ) :
    psi2 ψ ^ s * Φ y = Φ y * psi2 ψ ^ s := by
  have h := P.act_pow (oddPart ψ * s) y
  rw [pow_apply_of_fixed hy, ← psi2_pow_eq] at h
  calc psi2 ψ ^ s * Φ y = psi2 ψ ^ s * Φ y * (psi2 ψ ^ s)⁻¹ * psi2 ψ ^ s := by group
    _ = Φ y * psi2 ψ ^ s := by rw [h]

omit [Finite X] in
theorem OutProps.card_inf_centralizer_invol_lt (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) {m : ℕ}
    (hle : Nat.card ↥(fixSub (involAut ψ α) U) ≤ m) {y : X} (hy : α y = y)
    (hlt : m < Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set X))) :
    Nat.card ↥(spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)) <
      Nat.card ↥(spT Φ ψ U ⊓ Subgroup.centralizer ({Φ y} : Set H)) := by
  have hmemC : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ Subgroup.centralizer ({y} : Set X) ↔
      x ∈ Subgroup.centralizer ({y} : Set X) := by
    intro k x
    have hk := pow_apply_of_fixed hy k
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : (α ^ k) (y * x) = (α ^ k) (x * y) := by rw [map_mul, map_mul, hk]; exact h
      exact (α ^ k).injective h'
    · intro h
      have h' := congrArg (α ^ k) h
      rwa [map_mul, map_mul, hk] at h'
  have hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ⊓ Subgroup.centralizer ({y} : Set X) ↔
      x ∈ U ⊓ Subgroup.centralizer ({y} : Set X) := fun k x =>
    and_congr (hU k x) (hmemC k x)
  have hle' : spT Φ ψ (U ⊓ Subgroup.centralizer ({y} : Set X)) ≤
      spT Φ ψ U ⊓ Subgroup.centralizer ({Φ y} : Set H) := by
    intro z hz
    obtain ⟨w, hw, s, rfl⟩ := (P.mem_spT_iff hV).1 hz
    refine ⟨(P.mem_spT_iff hU).2 ⟨w, hw.1, s, rfl⟩,
      Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.1 hg]
    have hwy : y * w = w * y := Subgroup.mem_centralizer_iff.1 hw.2 y rfl
    calc Φ y * (Φ w * psi2 ψ ^ s) = Φ (y * w) * psi2 ψ ^ s := by rw [map_mul, mul_assoc]
      _ = Φ (w * y) * psi2 ψ ^ s := by rw [hwy]
      _ = Φ w * (Φ y * psi2 ψ ^ s) := by rw [map_mul, mul_assoc]
      _ = Φ w * (psi2 ψ ^ s * Φ y) := by rw [P.psi2_pow_comm_of_fixed hy]
      _ = Φ w * psi2 ψ ^ s * Φ y := by rw [mul_assoc]
  calc Nat.card ↥(spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H))
      = Nat.card ↥(fixSub (involAut ψ α) U) * 2 ^ twoExp ψ := P.card_inf_centralizer_invol hU
    _ ≤ m * 2 ^ twoExp ψ := Nat.mul_le_mul_right _ hle
    _ < Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set X)) * 2 ^ twoExp ψ :=
        (Nat.mul_lt_mul_right (by positivity)).2 hlt
    _ = Nat.card ↥(spT Φ ψ (U ⊓ Subgroup.centralizer ({y} : Set X))) := (P.card_spT hV).symm
    _ ≤ _ := Subgroup.card_le_of_le hle'

omit [Finite X] [Finite H] in
theorem OutProps.map_mem_inf_centralizer_invol (P : OutProps Φ ψ α) {U : Subgroup X} {x : X}
    (hx : x ∈ U) (hα : α x = x) :
    Φ x ∈ spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H) := by
  refine ⟨Subgroup.mem_sup_left ⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  rw [Set.mem_singleton_iff.1 hg]
  exact P.invol_mul_comm x (pow_apply_of_fixed hα _)

omit [Finite X] in
theorem OutProps.spW_le_centerOf (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) {x₁ x₂ : X} (h₁ : x₁ ∈ U) (h₂ : x₂ ∈ U)
    (hα₁ : α x₁ = x₁) (hα₂ : α x₂ = x₂)
    (hcen : ∀ x ∈ U, x * x₁ = x₁ * x → x * x₂ = x₂ * x → ∀ w ∈ U, x * w = w * x) :
    centerOf (spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)) ⊓
        ⁅spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H),
          spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)⁆ ≤ centerOf (U.map Φ) := by
  rintro w ⟨⟨hwT, hwC⟩, hwComm⟩
  have hcomm : ⁅spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H),
      spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)⁆ ≤ Φ.range :=
    Subgroup.commutator_le.2 fun a _ b _ => by
      rw [commutatorElement_def]
      exact P.commutator_mem_range a b
  have hwS : w ∈ U.map Φ := by
    rw [← P.spT_inf_range hU]
    exact ⟨hwT.1, hcomm hwComm⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hwS
  have hc : ∀ (xi : X) (hi : xi ∈ U), α xi = xi → xi * x = x * xi := by
    intro xi hi hαi
    have h := Subgroup.mem_centralizer_iff.1 hwC (Φ xi) (P.map_mem_inf_centralizer_invol hi hαi)
    exact P.inj (by rw [map_mul, map_mul]; exact h)
  have hfull := hcen x hx (hc x₁ h₁ hα₁).symm (hc x₂ h₂ hα₂).symm
  refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hs
  rw [← map_mul, ← map_mul, hfull w' hw']

omit [Finite X] in
theorem OutProps.map_mem_spW (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) {x₁ x₃ z : X} (h₁ : x₁ ∈ U) (h₃ : x₃ ∈ U)
    (hα₁ : α x₁ = x₁) (hα₃ : α x₃ = x₃) (hαz : α z = z)
    (hz : x₁ * x₃ * x₁⁻¹ * x₃⁻¹ = z) (hzc : ∀ w ∈ U, z * w = w * z) :
    Φ z ∈ centerOf (spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)) ⊓
        ⁅spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H),
          spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)⁆ := by
  have hzU : z ∈ U := hz ▸ U.mul_mem (U.mul_mem (U.mul_mem h₁ h₃) (U.inv_mem h₁)) (U.inv_mem h₃)
  have hzTf := P.map_mem_inf_centralizer_invol hzU hαz
  refine ⟨⟨hzTf, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩, ?_⟩
  · obtain ⟨w, hw, s, rfl⟩ := (P.mem_spT_iff hU).1 ht.1
    calc Φ w * psi2 ψ ^ s * Φ z = Φ w * (psi2 ψ ^ s * Φ z) := by rw [mul_assoc]
      _ = Φ w * (Φ z * psi2 ψ ^ s) := by rw [P.psi2_pow_comm_of_fixed hαz]
      _ = Φ (w * z) * psi2 ψ ^ s := by rw [map_mul, mul_assoc]
      _ = Φ (z * w) * psi2 ψ ^ s := by rw [(hzc w hw).symm]
      _ = Φ z * (Φ w * psi2 ψ ^ s) := by rw [map_mul, mul_assoc]
  · have h := Subgroup.commutator_mem_commutator (P.map_mem_inf_centralizer_invol h₁ hα₁)
      (P.map_mem_inf_centralizer_invol h₃ hα₃)
    rw [commutatorElement_def] at h
    have e : Φ x₁ * Φ x₃ * (Φ x₁)⁻¹ * (Φ x₃)⁻¹ = Φ z := by
      rw [← hz, map_mul, map_mul, map_mul, map_inv, map_inv]
    rwa [e] at h

end Main

end CFSG.Quasithin.H13.F431.G2.OutK
