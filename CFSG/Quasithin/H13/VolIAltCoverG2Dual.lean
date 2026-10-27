module

public import CFSG.Quasithin.H13.VolII16Forms
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import CFSG.Quasithin.Background.JonesParshallSLn

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open Matrix

section Conj

variable {G M : Type*} [Group G] [AddCommGroup M]

theorem card_Z1A_conj (μ ν : G →* AddMonoid.End M) (L : M ≃+ M)
    (h : ∀ g x, ν g (L x) = L (μ g x)) :
    Nat.card (Z1A ν) = Nat.card (Z1A μ) ∧ Nat.card (B1A ν) = Nat.card (B1A μ) := by
  let e : (G → M) ≃ (G → M) := Equiv.piCongrRight fun _ => L.toEquiv
  have he : ∀ f g, e f g = L (f g) := fun _ _ => rfl
  refine ⟨(Nat.card_congr (e.subtypeEquiv fun f => ?_)).symm,
    (Nat.card_congr (e.subtypeEquiv fun f => ?_)).symm⟩
  · constructor
    · intro hf g k
      rw [he, he, he, hf g k, map_add, h]
    · intro hf g k
      have h1 := hf g k
      rw [he, he, he, h, ← map_add] at h1
      exact L.injective h1
  · constructor
    · rintro ⟨m, rfl⟩
      refine ⟨L m, funext fun g => ?_⟩
      rw [he, coboundaryA_apply, coboundaryA_apply, map_sub, h]
    · rintro ⟨m', hm'⟩
      refine ⟨L.symm m', funext fun g => L.injective ?_⟩
      have h1 := congrFun hm' g
      rw [coboundaryA_apply, he] at h1
      rw [coboundaryA_apply, map_sub, ← h, AddEquiv.apply_symm_apply, h1]

end Conj

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

@[expose] def muQ (g : ↥subG2) : Matrix Ix3 Ix3 (ZMod 2) :=
  (cmat (Subgroup.inclusion subG2_le g)).submatrix embQ embQ

theorem muK_eq_mulVec (g : ↥subG2) (w : Ix3 → ZMod 2) : muK g w = muQ g *ᵥ w :=
  g2Act_eq_mulVec _ w

theorem muQ_one : muQ 1 = 1 := by
  rw [ext_iff_mulVec]
  intro w
  rw [← muK_eq_mulVec, map_one, one_mulVec]
  rfl

theorem muQ_mul (g h : ↥subG2) : muQ (g * h) = muQ g * muQ h := by
  rw [ext_iff_mulVec]
  intro w
  rw [← muK_eq_mulVec, ← mulVec_mulVec, ← muK_eq_mulVec, ← muK_eq_mulVec, map_mul]
  rfl

@[expose] def gramQ : Matrix Ix3 Ix3 (ZMod 2) := fromBlocks 0 1 1 0

theorem gramQ_mul_self : gramQ * gramQ = 1 := by
  rw [gramQ, fromBlocks_multiply]
  simp

theorem muQ_gensK0 :
    muQ (gensK 0) = matA6 := by
  rw [muQ, show Subgroup.inclusion subG2_le (gensK 0) = g2a from rfl, cmat_g2a]
  rfl

theorem muQ_gensK1 :
    muQ (gensK 1) = matB6 := by
  rw [muQ, show Subgroup.inclusion subG2_le (gensK 1) = g2b from rfl, cmat_g2b]
  rfl

theorem gram_matA6 : matA6ᵀ * gramQ * matA6 = gramQ := by decide

theorem gram_matB6 : matB6ᵀ * gramQ * matB6 = gramQ := by decide

theorem muQ_gram
    (g : ↥subG2) : (muQ g)ᵀ * gramQ * muQ g = gramQ := by
  let S : Subgroup ↥subG2 :=
    { carrier := {g | (muQ g)ᵀ * gramQ * muQ g = gramQ}
      one_mem' := by
        show (muQ 1)ᵀ * gramQ * muQ 1 = gramQ
        rw [muQ_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
      mul_mem' := fun {x y} hx hy => by
        show (muQ (x * y))ᵀ * gramQ * muQ (x * y) = gramQ
        have hx' : (muQ x)ᵀ * gramQ * muQ x = gramQ := hx
        have hy' : (muQ y)ᵀ * gramQ * muQ y = gramQ := hy
        rw [muQ_mul, transpose_mul]
        calc (muQ y)ᵀ * (muQ x)ᵀ * gramQ * (muQ x * muQ y) =
            (muQ y)ᵀ * ((muQ x)ᵀ * gramQ * muQ x) * muQ y := by
              simp only [Matrix.mul_assoc]
          _ = gramQ := by rw [hx', hy']
      inv_mem' := fun {x} hx => by
        show (muQ x⁻¹)ᵀ * gramQ * muQ x⁻¹ = gramQ
        have hx' : (muQ x)ᵀ * gramQ * muQ x = gramQ := hx
        have h2 : muQ x * muQ x⁻¹ = 1 := by rw [← muQ_mul, mul_inv_cancel, muQ_one]
        calc (muQ x⁻¹)ᵀ * gramQ * muQ x⁻¹ =
            (muQ x⁻¹)ᵀ * ((muQ x)ᵀ * gramQ * muQ x) * muQ x⁻¹ := by rw [hx']
          _ = (muQ x * muQ x⁻¹)ᵀ * gramQ * (muQ x * muQ x⁻¹) := by
              rw [transpose_mul]
              simp only [Matrix.mul_assoc]
          _ = gramQ := by rw [h2, transpose_one, Matrix.one_mul, Matrix.mul_one] }
  have htop : Subgroup.closure ((Subtype.val : ↥subG2 → Amb) ⁻¹'
      {(g2a : Amb), (g2b : Amb)}) = ⊤ := Subgroup.closure_closure_coe_preimage
  have hle : Subgroup.closure ((Subtype.val : ↥subG2 → Amb) ⁻¹'
      {(g2a : Amb), (g2b : Amb)}) ≤ S := by
    rw [Subgroup.closure_le]
    rintro s (hs | hs)
    · have e : s = gensK 0 := Subtype.ext hs
      show (muQ s)ᵀ * gramQ * muQ s = gramQ
      rw [e, muQ_gensK0]
      exact gram_matA6
    · have e : s = gensK 1 := Subtype.ext hs
      show (muQ s)ᵀ * gramQ * muQ s = gramQ
      rw [e, muQ_gensK1]
      exact gram_matB6
  rw [htop] at hle
  exact hle (Subgroup.mem_top g)

theorem muQ_inv_transpose
    (g : ↥subG2) : (muQ g⁻¹)ᵀ = gramQ * muQ g * gramQ := by
  have h1 : (muQ g⁻¹)ᵀ * (muQ g)ᵀ = 1 := by
    rw [← transpose_mul, ← muQ_mul, mul_inv_cancel, muQ_one, transpose_one]
  have h2 : (muQ g)ᵀ * (gramQ * muQ g * gramQ) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, muQ_gram, gramQ_mul_self]
  calc (muQ g⁻¹)ᵀ = (muQ g⁻¹)ᵀ * ((muQ g)ᵀ * (gramQ * muQ g * gramQ)) := by
        rw [h2, Matrix.mul_one]
    _ = gramQ * muQ g * gramQ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

@[expose] def dualQ (g : ↥subG2) : Matrix Ix3 Ix3 (ZMod 2) := gramQ * muQ g * gramQ

theorem dualQ_one : dualQ 1 = 1 := by
  rw [dualQ, muQ_one, Matrix.mul_one, gramQ_mul_self]

theorem dualQ_mul (g h : ↥subG2) : dualQ (g * h) = dualQ g * dualQ h := by
  rw [dualQ, dualQ, dualQ, muQ_mul]
  calc gramQ * (muQ g * muQ h) * gramQ = gramQ * muQ g * (gramQ * gramQ) * muQ h * gramQ := by
        rw [gramQ_mul_self, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = gramQ * muQ g * gramQ * (gramQ * muQ h * gramQ) := by simp only [Matrix.mul_assoc]

@[expose] def muKdual : ↥subG2 →* AddMonoid.End (Ix3 → ZMod 2) where
  toFun g := (mulVecLin (dualQ g)).toAddMonoidHom
  map_one' := AddMonoidHom.ext fun w => by
    change dualQ 1 *ᵥ w = w
    rw [dualQ_one, one_mulVec]
  map_mul' g h := AddMonoidHom.ext fun w => by
    change dualQ (g * h) *ᵥ w = dualQ g *ᵥ (dualQ h *ᵥ w)
    rw [dualQ_mul, mulVec_mulVec]

theorem muKdual_apply (g : ↥subG2) (w : Ix3 → ZMod 2) :
    muKdual g w = (gramQ * muQ g * gramQ) *ᵥ w := rfl

theorem muKdual_eq
    (g : ↥subG2) (w : Ix3 → ZMod 2) : muKdual g w = (muQ g⁻¹)ᵀ *ᵥ w := by
  rw [muKdual_apply, muQ_inv_transpose]

theorem card_Z1A_muKdual
    : Nat.card (Z1A muKdual) = 2 * Nat.card (B1A muKdual) := by
  let L : (Ix3 → ZMod 2) ≃+ (Ix3 → ZMod 2) :=
    { toFun := fun x => gramQ *ᵥ x
      invFun := fun x => gramQ *ᵥ x
      left_inv := fun x => by
        show gramQ *ᵥ (gramQ *ᵥ x) = x
        rw [mulVec_mulVec, gramQ_mul_self, one_mulVec]
      right_inv := fun x => by
        show gramQ *ᵥ (gramQ *ᵥ x) = x
        rw [mulVec_mulVec, gramQ_mul_self, one_mulVec]
      map_add' := fun x y => mulVec_add _ _ _ }
  have hL : ∀ g x, muKdual g (L x) = L (muK g x) := fun g x => by
    show (gramQ * muQ g * gramQ) *ᵥ (gramQ *ᵥ x) = gramQ *ᵥ muK g x
    rw [muK_eq_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, gramQ_mul_self,
      Matrix.mul_one]
  obtain ⟨h1, h2⟩ := card_Z1A_conj muK muKdual L hL
  rw [h1, h2]
  exact card_Z1A_K

end CFSG.Quasithin.H13.VolI
