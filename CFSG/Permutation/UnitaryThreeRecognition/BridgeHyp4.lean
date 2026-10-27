module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp2

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))
include C S hconj hcop

omit C hconj hcop [Finite G] [Finite Ω] in
theorem sMapCoord_inv_inv (u : Q) (hu : (u : G) ≠ 1) :
    (S.sMapCoord φ (φ u)⁻¹)⁻¹ =
      φ ⟨sRight Q a b s u, S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu⟩ := by
  have hui : ((u⁻¹ : Q) : G) ≠ 1 := by
    intro e; apply hu
    have : u⁻¹ = 1 := Subtype.ext e
    rw [show u = 1 by simpa using this]; rfl
  rw [← map_inv, S.sMapCoord_apply φ u⁻¹ hui, ← map_inv]
  congr 1
  apply Subtype.ext
  have := (S.root.sFactors_inv S.hb S.hsa S.hs2 (Q.inv_mem u.2) hui).2.2
  simp only [inv_inv] at this
  change (sLeft Q a b s (u : G)⁻¹)⁻¹ = sRight Q a b s u
  rw [this]

omit S [Finite G] [Finite Ω] hconj hcop in
theorem kOf_conj (t : pairStab G a b) (x : Q) (hx : (t : G) * x * (t : G)⁻¹ ∈ Q) :
    hermitianTorusAction J (C.kOf t) (φ x) = φ ⟨_, hx⟩ :=
  (C.kOf_spec' t x ⟨_, hx⟩ rfl).symm

theorem sMapCoord_moufang {z w : Coord J} (hz : z ≠ 1) (hza : z.1.1 = 0) (hw : w.1.1 ≠ 0) :
    S.sMapCoord φ (z * w) = S.sMapCoord φ z *
      hermitianTorusAction J (C.hmap S hconj hcop z)
        (S.sMapCoord φ ((S.sMapCoord φ z⁻¹)⁻¹ * S.sMapCoord φ w)) := by
  obtain ⟨u, rfl⟩ := φ.surjective z
  obtain ⟨v', rfl⟩ := φ.surjective w
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hz
  have huZ : (u : G) ∈ centQ Q j := (C.center u).mpr hza
  have hv'Z : (v' : G) ∉ centQ Q j := fun h => hw ((C.center v').mp h)
  have hv'1 : (v' : G) ≠ 1 := fun e => hv'Z (by rw [e]; exact (centQ Q j).one_mem)
  have hyQ := S.root.sLeft_mem S.hb S.hsa S.hs2 v'.2 hv'1
  set y : Q := ⟨sLeft Q a b s v', hyQ⟩ with hydef
  have hy1 : (y : G) ≠ 1 := S.root.sLeft_ne_one S.hb S.hsa S.hs2 v'.2 hv'1
  have hyy : sLeft Q a b s y = v' := S.root.sLeft_sLeft S.hb S.hsa S.hs2 v'.2 hv'1
  have hyZ : (y : G) ∉ centQ Q j := by
    intro h
    apply hv'Z
    have := S.root.sLeft_mem_centQ S.hb S.hsa S.hs2 S.hj S.hsj h hy1
    rwa [hyy] at this
  have hrQ := S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu1
  have hrZ := S.root.sRight_mem_centQ S.hb S.hsa S.hs2 S.hj S.hsj huZ hu1
  set r : Q := ⟨sRight Q a b s u, hrQ⟩ with hrdef
  have huv : (u : G) * sLeft Q a b s y ≠ 1 := by
    rw [hyy]; intro e; apply hv'Z
    have : (v' : G) = (u : G)⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this]; exact (centQ Q j).inv_mem huZ
  have hry : (r : G) * y ≠ 1 := by
    intro e; apply hyZ
    have : (y : G) = (r : G)⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this]; exact (centQ Q j).inv_mem hrZ
  have hM := S.root.sLeft_mul_sLeft S.hb S.hsa S.hs2 u.2 hu1 y.2 hy1 huv hry
  rw [hyy] at hM
  have huv' : ((u * v' : Q) : G) ≠ 1 := by
    change (u : G) * v' ≠ 1; rw [← hyy]; exact huv
  have hry' : ((r * y : Q) : G) ≠ 1 := hry
  rw [← map_mul, S.sMapCoord_apply φ _ huv', sMapCoord_inv_inv S u hu1, ← hrdef,
    S.sMapCoord_apply φ v' hv'1, ← hydef, ← map_mul, S.sMapCoord_apply φ _ hry',
    C.hmap_apply S hconj hcop u hu1, S.sMapCoord_apply φ u hu1]
  set τ : pairStab G a b := ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩
  rw [C.kOf_conj τ _ (S.root.normal τ τ.2.1 _
    (S.root.sLeft_mem S.hb S.hsa S.hs2 (r * y).2 hry')), ← map_mul]
  congr 1
  apply Subtype.ext
  exact hM

theorem hmap_rel {z : Coord J} (hz : z ≠ 1) :
    hermitianTorusAction J (C.hmap S hconj hcop z) (S.sMapCoord φ (S.sMapCoord φ z⁻¹)⁻¹) =
      (S.sMapCoord φ z)⁻¹ := by
  obtain ⟨u, rfl⟩ := φ.surjective z
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hz
  have hr1 := S.root.sRight_ne_one S.hb S.hsa S.hs2 u.2 hu1
  rw [sMapCoord_inv_inv S u hu1, S.sMapCoord_apply φ _ hr1, C.hmap_apply S hconj hcop u hu1,
    S.sMapCoord_apply φ u hu1]
  set τ : pairStab G a b := ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩
  rw [C.kOf_conj τ _ (S.root.normal τ τ.2.1 _
    (S.root.sLeft_mem S.hb S.hsa S.hs2 (S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu1) hr1)),
    ← map_inv]
  congr 1
  apply Subtype.ext
  exact S.root.sTor_conj_sLeft_sRight S.hb S.hsa S.hs2 u.2 hu1

theorem hmap_torus (k : Kˣ) {z : Coord J} (hz : z ≠ 1) :
    C.hmap S hconj hcop (hermitianTorusAction J k z) =
      C.sigmaK S hconj hcop k * C.hmap S hconj hcop z * k⁻¹ := by
  obtain ⟨u, rfl⟩ := φ.surjective z
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hz
  set t := (C.torusEquiv S hconj hcop).symm k with htdef
  set v : Q := ⟨(t : G) * u * (t : G)⁻¹, S.root.normal _ t.2.1 u u.2⟩ with hvdef
  have hv : (v : G) ≠ 1 := by
    intro e
    apply hu1
    have e' : (t : G) * u * (t : G)⁻¹ = 1 := e
    calc (u : G) = (t : G)⁻¹ * ((t : G) * u * (t : G)⁻¹) * t := by group
      _ = 1 := by rw [e']; group
  rw [← C.phi_conj_symm S hconj hcop k u, ← htdef, ← hvdef, C.hmap_apply S hconj hcop v hv,
    C.hmap_apply S hconj hcop u hu1]
  obtain ⟨-, hT, -⟩ := S.root.sFactors_conj S.hb S.hsa S.hs2 u.2 hu1 t.2
  have he : (⟨sTor Q a b s v, S.root.sTor_mem S.hb S.hsa S.hs2 v.2 hv⟩ : pairStab G a b) =
      S.conjS t * ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩ * t⁻¹ := by
    apply Subtype.ext
    change sTor Q a b s ((t : G) * u * (t : G)⁻¹) = _
    rw [hT]
    rfl
  rw [he]
  calc C.kOf (S.conjS t * ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩ * t⁻¹)
      = C.torusEquiv S hconj hcop
          (S.conjS t * ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩ * t⁻¹) := rfl
    _ = C.torusEquiv S hconj hcop (S.conjS t) *
          C.torusEquiv S hconj hcop ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu1⟩ *
          (C.torusEquiv S hconj hcop t)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = _ := by
        rw [htdef, MulEquiv.apply_symm_apply, torusEquiv_apply, torusEquiv_apply,
          ← sigmaK_apply]

end CoordHyp

end CFSG.UnitaryThreeRecognition
