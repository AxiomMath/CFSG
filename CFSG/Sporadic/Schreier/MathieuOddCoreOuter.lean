module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem conj_mem_of_closure {M : Type*} [Group M] {H : Subgroup M} {S : Set M}
    (hH : H = Subgroup.closure S) {u : M} (hu : ∀ s ∈ S, u * s * u⁻¹ ∈ H) :
    ∀ h ∈ H, u * h * u⁻¹ ∈ H := by
  have hle : H.map (MulAut.conj u).toMonoidHom ≤ H := by
    rw [hH, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [← hH]
    exact hu s hs
  intro h hh
  exact hle ⟨h, hh, rfl⟩

variable {n : ℕ}

theorem commT_iff {x y : Table} {xg yg : Equiv.Perm (Fin n)} (hx : Rep n x xg)
    (hy : Rep n y yg) : commT n x y = true ↔ xg * yg = yg * xg := by
  refine ⟨eq_of_commT hx hy, fun h => ?_⟩
  have h1 := Rep.compT hx hy
  have h2 := Rep.compT hy hx
  rw [h] at h1
  change tblEq n (compT n x y) (compT n y x) = true
  rw [tblEq_iff]
  intro i hi
  rw [h1 i hi, h2 i hi]

theorem not_centralizes_of_count (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {a b δ : Equiv.Perm (Fin n)} (ha : a ∈ Q.originalSubgroup)
    (hb : b ∈ Q.originalSubgroup)
    (h : countProducts n (commAll n [toTable a, toTable b]) (levelTables Q) (toTable δ) = 0) :
    ∀ g ∈ Q.originalSubgroup, ¬∀ x ∈ Q.originalSubgroup, δ * g * x = x * (δ * g) := by
  intro g hg hall
  have hspec := countProducts_spec
    (P := fun y : Equiv.Perm (Fin n) => y * a = a * y ∧ y * b = b * y)
    (f := commAll n [toTable a, toTable b]) (fun T y hT => by
      simp only [commAll, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      rw [commT_iff hT (rep_toTable hn a), commT_iff hT (rep_toTable hn b)])
    (forall₂_levelTables hn Q) (rep_toTable hn δ)
  rw [h, eq_comm, List.countP_eq_zero] at hspec
  have hgL : g ∈ enumeration Q := (mem_enumeration_iff Q hQ g).2 hg
  have := hspec (δ * g) (List.mem_map.2 ⟨g, hgL, rfl⟩)
  apply this
  simp only [decide_eq_true_eq]
  exact ⟨(hall a ha), (hall b hb)⟩

end CFSG.Sporadic.Schreier
