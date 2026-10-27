module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Monster.B.Recog.GenericWalkHomotopy
import CFSG.LocalAnalysis.StandardType.GGQTwoBSVec
import CFSG.Monster.B.GSide.HomotopyRonan

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[ext] structure NormOneVec (m : ℕ) where
  val : Fin m → K
  herm_self : herm (unitaryInvolution K 2 1) val val = 1

variable {K}

namespace NormOneVec

variable {m : ℕ}

noncomputable instance : MulAction (Su K 2 1 m) (NormOneVec K m) where
  smul g x := ⟨g • x.val, by rw [herm_smul_smul]; exact x.herm_self⟩
  one_smul x := NormOneVec.ext (one_smul _ x.val)
  mul_smul g h x := NormOneVec.ext (mul_smul g h x.val)

@[simp] theorem val_smul (g : Su K 2 1 m) (x : NormOneVec K m) : (g • x).val = g • x.val := rfl

@[expose] def single (i : Fin m) : NormOneVec K m :=
  ⟨Pi.single i 1, by simp [herm_single_left]⟩

@[simp] theorem val_single (i : Fin m) : (single i : NormOneVec K m).val = Pi.single i 1 := rfl

end NormOneVec

variable (K)

@[expose] def orthGraph (m : ℕ) : SimpleGraph (NormOneVec K m) where
  Adj x y := herm (unitaryInvolution K 2 1) x.val y.val = 0 ∧
    herm (unitaryInvolution K 2 1) y.val x.val = 0
  symm := ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
  loopless := ⟨fun x h => by
    rw [x.herm_self] at h
    exact one_ne_zero h.1⟩

variable {K}

private theorem bsg_unitaryInvolution_invol (hK : Nat.card K = 4) :
    ∀ c : K, unitaryInvolution K 2 1 (unitaryInvolution K 2 1 c) = c := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  exact unitaryInvolution_involutive hK'

theorem orthGraph_adj (hK : Nat.card K = 4) {m : ℕ} {x y : NormOneVec K m} :
    (orthGraph K m).Adj x y ↔ herm (unitaryInvolution K 2 1) x.val y.val = 0 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact herm_eq_zero_comm _ (bsg_unitaryInvolution_invol hK) h

theorem orthGraph_adj_smul {m : ℕ} (g : Su K 2 1 m) {x y : NormOneVec K m}
    (h : (orthGraph K m).Adj x y) : (orthGraph K m).Adj (g • x) (g • y) := by
  refine ⟨?_, ?_⟩
  · simp only [NormOneVec.val_smul]
    rw [herm_smul_smul]
    exact h.1
  · simp only [NormOneVec.val_smul]
    rw [herm_smul_smul]
    exact h.2

theorem orthGraph_adj_single {m : ℕ} {i j : Fin m} (h : i ≠ j) :
    (orthGraph K m).Adj (NormOneVec.single i) (NormOneVec.single j) := by
  have hij : j ≠ i := Ne.symm h
  refine ⟨?_, ?_⟩
  · rw [NormOneVec.val_single, NormOneVec.val_single, herm_single_left,
      Pi.single_eq_of_ne h, mul_zero]
  · rw [NormOneVec.val_single, NormOneVec.val_single, herm_single_left,
      Pi.single_eq_of_ne hij, mul_zero]

private theorem bsg_herm_comm (hK : Nat.card K = 4) {m : ℕ} {x y : Fin m → K}
    (h : herm (unitaryInvolution K 2 1) x y = 0) :
    herm (unitaryInvolution K 2 1) y x = 0 :=
  herm_eq_zero_comm _ (bsg_unitaryInvolution_invol hK) h

private theorem bsg_exists_common (hK : Nat.card K = 4) {m : ℕ} (hm : 5 ≤ m)
    (x y : NormOneVec K m) :
    ∃ z : NormOneVec K m, (orthGraph K m).Adj x z ∧ (orthGraph K m).Adj y z := by
  have hσ := bsg_unitaryInvolution_invol hK
  obtain ⟨z, hz, hxz⟩ :=
    exists_herm_self_eq_one_of_orthonormal hK (k := 2) (d := 0) (by omega) (by omega)
      ![x.val, y.val] (by intro i j hi hj; omega)
  have hx : herm (unitaryInvolution K 2 1) x.val z = 0 := by simpa using hxz 0
  have hy : herm (unitaryInvolution K 2 1) y.val z = 0 := by simpa using hxz 1
  exact ⟨⟨z, hz⟩, ⟨hx, herm_eq_zero_comm _ hσ hx⟩,
    ⟨hy, herm_eq_zero_comm _ hσ hy⟩⟩

theorem orthGraph_preconnected (hK : Nat.card K = 4) {m : ℕ} (hm : 5 ≤ m) :
    (orthGraph K m).Preconnected := by
  intro x y
  obtain ⟨z, hxz, hyz⟩ := bsg_exists_common hK hm x y
  exact ⟨SimpleGraph.Walk.cons hxz (SimpleGraph.Walk.cons hyz.symm SimpleGraph.Walk.nil)⟩

private theorem bsg_commonNeighbors_preconnected (hK : Nat.card K = 4) {m : ℕ} (hm : 7 ≤ m)
    (v w : NormOneVec K m) :
    (SimpleGraph.induce ((orthGraph K m).commonNeighbors v w) (orthGraph K m)).Preconnected := by
  intro a b
  have ha := (SimpleGraph.mem_commonNeighbors (orthGraph K m)).mp a.2
  have hb := (SimpleGraph.mem_commonNeighbors (orthGraph K m)).mp b.2
  obtain ⟨z, hz, horth⟩ :=
    exists_herm_self_eq_one_of_orthonormal hK (k := 4) (d := 2) (by omega) (by omega)
      ![a.val.val, v.val, w.val, b.val.val] (by
        intro i j hi hj
        fin_cases i <;> fin_cases j <;>
          first
            | exact a.val.herm_self
            | exact ha.1.2
            | exact ha.1.1
            | exact v.herm_self
            | simp_all)
  have h0 : herm (unitaryInvolution K 2 1) a.val.val z = 0 := by simpa using horth 0
  have h1 : herm (unitaryInvolution K 2 1) v.val z = 0 := by simpa using horth 1
  have h2 : herm (unitaryInvolution K 2 1) w.val z = 0 := by simpa using horth 2
  have h3 : herm (unitaryInvolution K 2 1) b.val.val z = 0 := by simpa using horth 3
  set z' : NormOneVec K m := ⟨z, hz⟩ with hz'def
  have hvz : (orthGraph K m).Adj v z' := ⟨h1, bsg_herm_comm hK h1⟩
  have hwz : (orthGraph K m).Adj w z' := ⟨h2, bsg_herm_comm hK h2⟩
  have hzmem : z' ∈ (orthGraph K m).commonNeighbors v w :=
    (SimpleGraph.mem_commonNeighbors (orthGraph K m)).mpr ⟨hvz, hwz⟩
  have haz : (orthGraph K m).Adj a.val z' := ⟨h0, bsg_herm_comm hK h0⟩
  have hzb : (orthGraph K m).Adj z' b.val := ⟨bsg_herm_comm hK h3, h3⟩
  have h1' : (SimpleGraph.induce ((orthGraph K m).commonNeighbors v w)
      (orthGraph K m)).Adj a ⟨z', hzmem⟩ := haz
  have h2' : (SimpleGraph.induce ((orthGraph K m).commonNeighbors v w)
      (orthGraph K m)).Adj ⟨z', hzmem⟩ b := hzb
  exact ⟨SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2' SimpleGraph.Walk.nil)⟩

private theorem bsg_exists_common_adj (hK : Nat.card K = 4) {m : ℕ} (hm : 5 ≤ m)
    {v x y : NormOneVec K m} (hxy : (orthGraph K m).Adj x y) :
    ∃ c, (orthGraph K m).Adj v c ∧ (orthGraph K m).Adj c x ∧ (orthGraph K m).Adj c y := by
  obtain ⟨z, hz, horth⟩ :=
    exists_herm_self_eq_one_of_orthonormal hK (k := 3) (d := 2) (by omega) (by omega)
      ![x.val, y.val, v.val] (by
        intro i j hi hj
        fin_cases i <;> fin_cases j <;>
          first
            | exact x.herm_self
            | exact hxy.1
            | exact hxy.2
            | exact y.herm_self
            | simp_all)
  have h0 : herm (unitaryInvolution K 2 1) x.val z = 0 := by simpa using horth 0
  have h1 : herm (unitaryInvolution K 2 1) y.val z = 0 := by simpa using horth 1
  have h2 : herm (unitaryInvolution K 2 1) v.val z = 0 := by simpa using horth 2
  exact ⟨⟨z, hz⟩, ⟨h2, bsg_herm_comm hK h2⟩, ⟨bsg_herm_comm hK h0, h0⟩,
    ⟨bsg_herm_comm hK h1, h1⟩⟩

private theorem bsg_dist_le_two (hK : Nat.card K = 4) {m : ℕ} (hm : 5 ≤ m)
    (x y : NormOneVec K m) : (orthGraph K m).dist x y ≤ 2 := by
  obtain ⟨z, hxz, hzy⟩ := bsg_exists_common hK hm x y
  have hwalk := SimpleGraph.dist_le (SimpleGraph.Walk.cons hxz
    (SimpleGraph.Walk.cons hzy.symm SimpleGraph.Walk.nil))
  simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hwalk
  omega

theorem orthGraph_triangulable (hK : Nat.card K = 4) {m : ℕ} (hm : 7 ≤ m) :
    CFSG.Monster.B.Recog.Triangulable (orthGraph K m) := by
  have hD2 : ∀ x y : NormOneVec K m, (orthGraph K m).dist x y ≤ 2 :=
    bsg_dist_le_two hK (by omega)
  have hD : ∀ x y : NormOneVec K m, (orthGraph K m).dist x y ≤ 3 := by
    intro x y
    have := hD2 x y
    omega
  refine CFSG.Monster.B.GSide.triangulable_of_dist_le_three hD
    (fun v w _ => bsg_commonNeighbors_preconnected hK hm v w)
    (fun v x y _ _ hxy => bsg_exists_common_adj hK (by omega) hxy) ?_ ?_
  · intro v u hvu
    have := hD2 v u
    omega
  · intro v x y hvx _
    have := hD2 v x
    omega

private theorem bsg_smul_eq {m : ℕ} (g : Su K 2 1 m) {x y : NormOneVec K m}
    (h : g • x.val = y.val) : g • x = y :=
  NormOneVec.ext (by rwa [NormOneVec.val_smul])

theorem orthGraph_arc (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m) {a b c d : NormOneVec K m}
    (hab : (orthGraph K m).Adj a b) (hcd : (orthGraph K m).Adj c d) :
    ∃ g : Su K 2 1 m, g • a = c ∧ g • b = d := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_orthonormal hK (k := 2) (by omega)
    (u := ![a.val, b.val]) (v := ![c.val, d.val])
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        first
          | simpa using a.herm_self
          | exact hab.1
          | exact hab.2
          | simpa using b.herm_self)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        first
          | simpa using c.herm_self
          | exact hcd.1
          | exact hcd.2
          | simpa using d.herm_self)
  exact ⟨g, bsg_smul_eq g (by simpa using hg 0), bsg_smul_eq g (by simpa using hg 1)⟩

theorem orthGraph_triangle (hK : Nat.card K = 4) {m : ℕ} (hm : 4 ≤ m)
    {a b c a' b' c' : NormOneVec K m} (hab : (orthGraph K m).Adj a b)
    (hbc : (orthGraph K m).Adj b c) (hca : (orthGraph K m).Adj c a)
    (hab' : (orthGraph K m).Adj a' b') (hbc' : (orthGraph K m).Adj b' c')
    (hca' : (orthGraph K m).Adj c' a') :
    ∃ g : Su K 2 1 m, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_orthonormal hK (k := 3) (by omega)
    (u := ![a.val, b.val, c.val]) (v := ![a'.val, b'.val, c'.val])
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        first
          | simpa using a.herm_self
          | simpa using b.herm_self
          | simpa using c.herm_self
          | exact hab.1
          | exact hab.2
          | exact hbc.1
          | exact hbc.2
          | exact hca.1
          | exact hca.2)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        first
          | simpa using a'.herm_self
          | simpa using b'.herm_self
          | simpa using c'.herm_self
          | exact hab'.1
          | exact hab'.2
          | exact hbc'.1
          | exact hbc'.2
          | exact hca'.1
          | exact hca'.2)
  exact ⟨g, bsg_smul_eq g (by simpa using hg 0), bsg_smul_eq g (by simpa using hg 1),
    bsg_smul_eq g (by simpa using hg 2)⟩

end CFSG.StandardType.QTwo

end
