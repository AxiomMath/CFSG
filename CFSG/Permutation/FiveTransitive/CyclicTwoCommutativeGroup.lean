module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.KernelImageGeneration
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution
public import CFSG.Permutation.FiveTransitive.ThreeSwapCardLower
public import CFSG.Permutation.FiveTransitive.PairSwapEightSubgroup

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoCommutativeGroup

open FixedNormalizerAction

theorem local_card {F : Type*} [Finite F] [DecidableEq F] (e : Fin 6 ↪ F) :
    Nat.card (ThreeSwapTwoGroup.subgroup e) = 8 := by
  let V := ThreeSwapTwoGroup.subgroup e
  have hc (i j k l : Fin 6) (h : [i, j, k, l].Nodup) :
      Commute (Equiv.swap (e i) (e j)) (Equiv.swap (e k) (e l)) :=
    (Equiv.Perm.disjoint_swap_swap (by
      simpa only [List.map_cons, List.map_nil] using h.map e.injective)).commute
  have hc01 := hc 0 1 2 3 (by decide)
  have hc02 := hc 0 1 4 5 (by decide)
  have hc12 := hc 2 3 4 5 (by decide)
  have habel : IsMulCommutative V := by
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    change a * b = b * a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | rfl | exact hc01.eq | exact hc01.eq.symm | exact hc02.eq | exact hc02.eq.symm | exact hc12.eq | exact hc12.eq.symm
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := isMulCommutative_iff.mp habel }
  let u : V := ⟨Equiv.swap (e 0) (e 1), Subgroup.subset_closure (by simp)⟩
  let v : V := ⟨Equiv.swap (e 2) (e 3), Subgroup.subset_closure (by simp)⟩
  let w : V := ⟨Equiv.swap (e 4) (e 5), Subgroup.subset_closure (by simp)⟩
  let K := Subgroup.closure ({u, v, w} : Set V)
  have htop : K = ⊤ := by
    apply top_unique
    intro g hg
    clear hg
    rcases g with ⟨g, hg⟩
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> apply Subgroup.subset_closure <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, u, v, w] <;> tauto
    | one => exact K.one_mem
    | mul g h hg hh ihg ihh => exact K.mul_mem ihg ihh
    | inv g hg ihg => exact K.inv_mem ihg
  have hsq := (ThreeSwapTwoGroup.isTwoGroup e).2
  have hupper := PairSwapEightSubgroup.card_closure_le_eight u v w (hsq u) (hsq v) (hsq w)
  change Nat.card K ≤ 8 at hupper
  rw [htop, Subgroup.card_top] at hupper
  exact le_antisymm hupper (ThreeSwapCardLower.eight_le e)

theorem card_sixteen
    {G F : Type*} [Group G] [Finite G] [Finite F] [DecidableEq F]
    (f : G →* Equiv.Perm F) (B I : Subgroup G) (hI : Nat.card I = 2)
    (hk : B ⊓ f.ker = I) (e : Fin 6 ↪ F)
    (hm : B.map f = ThreeSwapTwoGroup.subgroup e) : Nat.card B = 16 := by
  let V := ThreeSwapTwoGroup.subgroup e
  let phi : B →* V :=
    { toFun := fun b => ⟨f b.val, hm.le ⟨b.val, b.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun b c => Subtype.ext (map_mul f b.val c.val) }
  have hsur : Function.Surjective phi := by
    intro v
    obtain ⟨b, hb, he⟩ := hm.ge v.property
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩
  let ek : phi.ker ≃ I :=
    { toFun := fun b => ⟨b.val.val, hk.le ⟨b.val.property,
        congrArg (fun v : V => v.val) b.property⟩⟩
      invFun := fun a => ⟨⟨a.val, (hk.ge a.property).1⟩,
        Subtype.ext (show f a.val = 1 from (hk.ge a.property).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hkc : Nat.card phi.ker = 2 := (Nat.card_congr ek).trans hI
  have hi : phi.ker.index = 8 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsur, Subgroup.card_top]
    exact local_card e
  have he := phi.ker.card_mul_index
  rw [hkc, hi] at he
  exact he.symm

theorem generated_commutative
    {G H : Type*} [Group G] [Group H] (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (f : Normalizer Q →* H) (B : Subgroup (Normalizer Q))
    (hk : B ⊓ f.ker = Inside Q)
    (a : Normalizer Q) (ha : a ∈ Inside Q) (hgen : Inside Q = Subgroup.zpowers a)
    (x y z : Normalizer Q) (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hm : B.map f = Subgroup.closure (f '' ({x, y, z} : Set (Normalizer Q)))) :
    B = Subgroup.closure ({a, x, y, z} : Set (Normalizer Q)) ∧ IsMulCommutative B := by
  have hB : B = Subgroup.closure ({a, x, y, z} : Set (Normalizer Q)) := by
    apply KernelImageGeneration.eq_closure_insert f B (Inside Q) hk a hgen
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> assumption
    · exact hm
  have hac (g : Normalizer Q) : Commute a g := by
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hQ g ⟨a.val, ha⟩
  refine ⟨hB, ?_⟩
  rw [hB]
  apply Subgroup.isMulCommutative_closure
  intro b hb c hc _
  change b * c = c * b
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
  rcases hb with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl
  all_goals first | rfl | exact (hac _).eq | exact (hac _).eq.symm | exact hxy.eq | exact hxy.eq.symm | exact hxz.eq | exact hxz.eq.symm | exact hyz.eq | exact hyz.eq.symm

end FiveTransitive.CyclicTwoCommutativeGroup

end CFSG
