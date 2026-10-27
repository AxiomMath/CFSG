module

public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS

variable {G : Type} [Group G]

def prodMulHom {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    (↥Y × ↥C) →* G where
  toFun p := (p.1 : G) * (p.2 : G)
  map_one' := by simp
  map_mul' p q := by
    show ((p.1 * q.1 : ↥Y) : G) * ((p.2 * q.2 : ↥C) : G) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    simp only [Subgroup.coe_mul]
    calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
        = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by simp only [mul_assoc]
      _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
          rw [hC (p.2 : G) p.2.2 (q.1 : G) q.1.2]
      _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by simp only [mul_assoc]

theorem prodMulHom_apply {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y)
    (p : ↥Y × ↥C) : prodMulHom hC p = (p.1 : G) * (p.2 : G) := by
  simp [prodMulHom]

theorem comm_of_mem_isMulCommutative {E : Subgroup G} (hE : IsMulCommutative ↥E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)

theorem range_prodMulHom {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    (prodMulHom hC).range = Y ⊔ C := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact Subgroup.mul_mem_sup p.1.2 p.2.2
  · refine sup_le (fun y hy => ⟨(⟨y, hy⟩, 1), ?_⟩) (fun c hc => ⟨(1, ⟨c, hc⟩), ?_⟩)
    · simp [prodMulHom_apply]
    · simp [prodMulHom_apply]

theorem card_sup_mul_card_inf_of_centralizes [Finite G] {Y C : Subgroup G}
    (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    Nat.card ↥(Y ⊔ C) * Nat.card ↥(Y ⊓ C) = Nat.card ↥Y * Nat.card ↥C := by
  have hquot : Nat.card (↥Y × ↥C) = Nat.card (prodMulHom hC).ker *
      Nat.card (prodMulHom hC).range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (prodMulHom hC).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (prodMulHom hC)).toEquiv] at h
    rw [h, mul_comm]
  have hker : Nat.card (prodMulHom hC).ker = Nat.card ↥(Y ⊓ C) := by
    let g : ↥(Y ⊓ C) →* (↥Y × ↥C) :=
      { toFun z := (⟨z.1, (Subgroup.mem_inf.mp z.2).1⟩,
          ⟨(z.1 : G)⁻¹, inv_mem (Subgroup.mem_inf.mp z.2).2⟩)
        map_one' := by simp
        map_mul' z w := by
          have hcom : Commute (z.1 : G) (w.1 : G) :=
            (hC (z.1 : G) (Subgroup.mem_inf.mp z.2).2 (w.1 : G) (Subgroup.mem_inf.mp w.2).1).symm
          ext
          · simp
          · show ((z.1 * w.1 : G))⁻¹ = (z.1 : G)⁻¹ * (w.1 : G)⁻¹
            rw [mul_inv_rev]
            exact (Commute.inv_inv hcom).eq.symm }
    have hinj : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      have := congrArg (fun p : ↥Y × ↥C => ((p.1 : ↥Y) : G)) h
      simpa [g] using this
    have hr : g.range = (prodMulHom hC).ker := by
      ext p
      constructor
      · rintro ⟨z, rfl⟩
        rw [MonoidHom.mem_ker, prodMulHom_apply]
        simp [g]
      · intro hp
        rw [MonoidHom.mem_ker, prodMulHom_apply] at hp
        have h2 : (p.2 : G) = (p.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right hp
        have hz : (p.1 : G) ∈ Y ⊓ C := by
          refine Subgroup.mem_inf.mpr ⟨p.1.2, ?_⟩
          have : (p.1 : G) = (p.2 : G)⁻¹ := by rw [h2, inv_inv]
          rw [this]
          exact inv_mem p.2.2
        refine ⟨⟨p.1, hz⟩, ?_⟩
        apply Prod.ext
        · apply Subtype.ext; rfl
        · apply Subtype.ext; simp [g, h2]
    rw [← hr]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hprod : Nat.card (↥Y × ↥C) = Nat.card ↥Y * Nat.card ↥C := Nat.card_prod _ _
  rw [← range_prodMulHom hC, ← hker, ← hprod, hquot, mul_comm]

theorem offender_index_le_of_isMaxElemAbelian [Finite G] {P Y A : Subgroup G}
    (hA : IsMaxElemAbelian P A) (hYP : Y ≤ P) (hY : IsElemAbelian 2 Y) :
    (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y ≤
      (A ⊓ Subgroup.centralizer (Y : Set G)).relIndex A := by
  have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    comm_of_mem_isMulCommutative hY.1 ha hb
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    comm_of_mem_isMulCommutative hA.2.1.1 ha hb
  set C : Subgroup G := A ⊓ Subgroup.centralizer (Y : Set G) with hCdef
  set K : Subgroup G := Y ⊓ Subgroup.centralizer (A : Set G) with hKdef
  have hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y := fun c hc y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y hy
  have hCA : C ≤ A := inf_le_left
  have hSP : Y ⊔ C ≤ P := sup_le hYP (hCA.trans hA.1)
  have hmem : ∀ x ∈ Y ⊔ C, ∃ p : ↥Y × ↥C, (p.1 : G) * (p.2 : G) = x := by
    intro x hx
    rw [← range_prodMulHom hC] at hx
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, by rw [← prodMulHom_apply]; exact hp⟩
  have hSel : IsElemAbelian 2 (Y ⊔ C) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · show a * b = b * a
      obtain ⟨p, hp⟩ := hmem a a.2
      obtain ⟨q, hq⟩ := hmem b b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq]
      have h11 := hYc (p.1 : G) p.1.2 (q.1 : G) q.1.2
      have h12 := (hC (q.2 : G) q.2.2 (p.1 : G) p.1.2).symm
      have h21 := (hC (p.2 : G) p.2.2 (q.1 : G) q.1.2).symm
      have h22 := hAc (p.2 : G) (hCA p.2.2) (q.2 : G) (hCA q.2.2)
      calc (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G))
          = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by simp only [mul_assoc]
        _ = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by rw [h21]
        _ = ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) := by simp only [mul_assoc]
        _ = ((q.1 : G) * (p.1 : G)) * ((q.2 : G) * (p.2 : G)) := by rw [h11, h22]
        _ = (q.1 : G) * ((p.1 : G) * (q.2 : G)) * (p.2 : G) := by simp only [mul_assoc]
        _ = (q.1 : G) * ((q.2 : G) * (p.1 : G)) * (p.2 : G) := by rw [h12]
        _ = (q.1 : G) * (q.2 : G) * ((p.1 : G) * (p.2 : G)) := by simp only [mul_assoc]
    · intro x hx
      obtain ⟨p, rfl⟩ := hmem x hx
      have hcom : Commute (p.1 : G) (p.2 : G) := hC (p.2 : G) p.2.2 (p.1 : G) p.1.2
      have h1 : (p.1 : G) ^ 2 = 1 := hY.2 _ p.1.2
      have h2 : (p.2 : G) ^ 2 = 1 := hA.2.1.2 _ (hCA p.2.2)
      show ((p.1 : G) * (p.2 : G)) ^ 2 = 1
      rw [hcom.mul_pow, h1, h2, one_mul]
  have hSmax : Nat.card ↥(Y ⊔ C) ≤ Nat.card ↥A := hA.2.2 (Y ⊔ C) hSP hSel
  have hK : K.relIndex Y * Nat.card ↥K = Nat.card ↥Y := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := Y)
    rw [inf_eq_left.mpr inf_le_left] at h
    exact h
  have hB : C.relIndex A * Nat.card ↥C = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := A)
    rw [inf_eq_left.mpr hCA] at h
    exact h
  have hYCK : Y ⊓ C ≤ K := by
    intro y hy
    obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨hyY, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact hAc a ha y (hCA hyC)
  have hcardYK : Nat.card ↥(Y ⊓ C) ≤ Nat.card ↥K := Subgroup.card_le_of_le hYCK
  have hprod := card_sup_mul_card_inf_of_centralizes hC
  have hKpos : 0 < Nat.card ↥K := Nat.card_pos
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have key : K.relIndex Y * (Nat.card ↥K * Nat.card ↥C) ≤
      C.relIndex A * (Nat.card ↥K * Nat.card ↥C) := by
    calc K.relIndex Y * (Nat.card ↥K * Nat.card ↥C)
        = (K.relIndex Y * Nat.card ↥K) * Nat.card ↥C := by ring
      _ = Nat.card ↥Y * Nat.card ↥C := by rw [hK]
      _ = Nat.card ↥(Y ⊔ C) * Nat.card ↥(Y ⊓ C) := hprod.symm
      _ ≤ Nat.card ↥A * Nat.card ↥K := Nat.mul_le_mul hSmax hcardYK
      _ = (C.relIndex A * Nat.card ↥C) * Nat.card ↥K := by rw [hB]
      _ = C.relIndex A * (Nat.card ↥K * Nat.card ↥C) := by ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hKpos hCpos)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
