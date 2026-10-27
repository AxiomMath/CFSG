module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem comm_of_cinv {v : V} {w g : G} (hw : w ∈ Cinv G v) (hg : g • v = v) :
    g * w = w * g :=
  hw.2.2.2 g (MulAction.mem_stabilizer_iff.2 hg)

theorem comm_of_ball {v q : V} {w g : G} (hw : w ∈ Cinv G q) (hg : g ∈ ballStab Γ G 2 v)
    (hd : Γ.dist v q ≤ 2) : g * w = w * g :=
  comm_of_cinv hw (mem_ballStab.1 hg q hd)

theorem not_cross (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) {α β : V} (hαβ : Γ.Adj α β) {u g y : G} (hu1 : u ≠ 1)
    (huα : u • α = α) (huβ : u • β = β) (hg : g • α = α) (hgβ : g • β ≠ β) (hy : y • β = β)
    (hyα : y • α ≠ α) (hgu : g * u = u * g) (hyu : y * u = u * y) : False :=
  no_fixed_cross F h40 h28 hΞ hαβ ⟨hg, hgβ, hy, hyα⟩ hu1 huα huβ hgu hyu

theorem dist_up (F : FanTree Γ G) (ℓ : Line Γ) {g : G} {i : ℤ} (hg : g • ℓ.vert i = ℓ.vert i) :
    Γ.dist (ℓ.vert i) (g • ℓ.vert (i + 2)) ≤ 2 := by
  have h1 : Γ.Adj (ℓ.vert i) (g • ℓ.vert (i + 1)) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj i)
    rwa [hg] at this
  have h2 : Γ.Adj (g • ℓ.vert (i + 1)) (g • ℓ.vert (i + 2)) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj (i + 1))
    rwa [show i + 1 + 1 = i + 2 by ring] at this
  simpa using SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))

theorem dist_down (F : FanTree Γ G) (ℓ : Line Γ) {g : G} {i : ℤ} (hg : g • ℓ.vert i = ℓ.vert i) :
    Γ.dist (ℓ.vert i) (g • ℓ.vert (i - 2)) ≤ 2 := by
  have h1 : Γ.Adj (ℓ.vert i) (g • ℓ.vert (i - 1)) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj_pred i)
    rwa [hg] at this
  have h2 : Γ.Adj (g • ℓ.vert (i - 1)) (g • ℓ.vert (i - 2)) := by
    have := (F.adj_smul g _ _).2 (ℓ.adj_pred (i - 1))
    rwa [show i - 1 - 1 = i - 2 by ring] at this
  simpa using SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))

theorem fcomm_eq {z t : G} (hz : z * z = 1) (ht : t * t = 1) :
    fcomm z t = z * (t * z * t⁻¹) ∧ fcomm z t = (z * t * z⁻¹) * t := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  constructor <;> simp only [fcomm, hz', ht', mul_assoc]

theorem fcomm_inv (z t : G) : (fcomm z t)⁻¹ = fcomm t z := by
  simp [fcomm, mul_assoc]

theorem comm_inv {g u : G} (h : g * u = u * g) : g * u⁻¹ = u⁻¹ * g :=
  (Commute.inv_right (show Commute g u from h)).eq

theorem inXi_rev (hXi1 : ∀ T' : Track Γ G, ¬ Xi 1 T') {T : Track Γ G} (hXi : InXi T) :
    InXi T.rev := by
  obtain ⟨i, hi, hmin⟩ := hXi
  have hi1 : i ≠ 1 := fun h => hXi1 T (h ▸ hi)
  rcases i with _ | _ | _ | _ | n
  · exact hi.elim
  · exact absurd rfl hi1
  · refine ⟨2, ?_, hmin⟩
    show T.rev.HasReflections
    intro k
    obtain ⟨f, hf2, hf⟩ := hi (-k)
    refine ⟨f, hf2, fun i => ?_⟩
    show f • T.line.vert (-(k + i)) = T.line.vert (-(k - i))
    rw [show -(k + i) = -k + -i by ring, show -(k - i) = -k - -i by ring]
    exact hf (-i)
  · refine ⟨3, ?_, hmin⟩
    show HasLenTwoReflection Γ G T.rev
    obtain ⟨k, f, hff, h0, h1, h2⟩ := (hi : HasLenTwoReflection Γ G T)
    have back : ∀ u v : V, f • u = v → f • v = u := fun u v h => by
      rw [← h, smul_smul, hff, one_smul]
    refine ⟨-k, f, hff, ?_, ?_, ?_⟩
    · show f • T.line.vert (-(-k)) = T.line.vert (-(-k))
      rw [neg_neg]
      exact h0
    · show f • T.line.vert (-(-k + 1)) = T.line.vert (-(-k - 1))
      rw [show -(-k + 1) = k - 1 by ring, show -(-k - 1) = k + 1 by ring]
      exact back _ _ h1
    · show f • T.line.vert (-(-k + 2)) = T.line.vert (-(-k - 2))
      rw [show -(-k + 2) = k - 2 by ring, show -(-k - 2) = k + 2 by ring]
      exact back _ _ h2
  · exact hi.elim

end P516

end CFSG.Quasithin.Fan86
