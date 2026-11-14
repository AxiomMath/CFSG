module

public import CFSG.Permutation.FiveTransitive.EvenSixTupleLocal

public section

namespace CFSG

namespace FiveTransitive.EvenLocalNoSwap

open MulAction FixedSetNormalizerPerm

theorem no_swap
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    [DecidableEq X] (hcard:4≤Nat.card X) (hlocal:EvenSixTupleLocal.Property G X)
    (g:G) (u v:X) (huv:u≠v) : toPermHom G X g≠Equiv.swap u v := by
  classical
  intro hg
  have hcard2 : 2 ≤ (Finset.univ \ ({u,v} : Finset X)).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_pair huv, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  have hone : 1 < (Finset.univ \ ({u,v} : Finset X)).card := by omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hone
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hx hy
  let b:Fin 4 ↪ X := ⟨![u,v,x,y],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hb0:b 0=u := rfl
  have hb1:b 1=v := rfl
  let S:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (S:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  have hfix (i:Fin 4):b i∈fixedPoints A X := by
    rw [mem_fixedPoints]
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    change r.val • b i=b i
    rw [←he]
    exact DFunLike.congr_fun s.property i
  have hu:u∈fixedPoints A X := hb0 ▸ hfix 0
  have hv:v∈fixedPoints A X := hb1 ▸ hfix 1
  have hnorm:g∈Subgroup.normalizer (A:Set G) := by
    apply Subgroup.centralizer_le_normalizer (A:Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hru:toPermHom G X r u=u := mem_fixedPoints.mp hu ⟨r,hr⟩
    have hrv:toPermHom G X r v=v := mem_fixedPoints.mp hv ⟨r,hr⟩
    apply toPerm_injective (β:=X)
    change toPermHom G X (r*g)=toPermHom G X (g*r)
    rw [map_mul,map_mul,hg,Equiv.mul_swap_eq_swap_mul,hru,hrv]
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  have he:fixedPerm G X A g hnorm=Equiv.swap (⟨u,hu⟩:fixedPoints A X) ⟨v,hv⟩ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (toPermHom G X g) x.val=_
    rw [hg]
    simp only [Equiv.swap_apply_def,Subtype.ext_iff]
    split_ifs <;> rfl
  have hs := (hlocal b S).2 g hnorm
  change (fixedPerm G X A g hnorm).sign=1 at hs
  rw [he,Equiv.Perm.sign_swap (fun h => huv (congrArg Subtype.val h))] at hs
  norm_num at hs

end FiveTransitive.EvenLocalNoSwap

end CFSG
