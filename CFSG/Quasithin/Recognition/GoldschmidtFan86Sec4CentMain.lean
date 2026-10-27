module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Cent
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4CentAbs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Three

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem fan46_central (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m : ℤ} (hm : b - a = 2 * m)
    (hm6 : 6 ≤ b - a) (h28 : Fan28) (h3 : valence Γ (T.line.vert a) = 3) :
    ∀ p ∈ H ⊓ MulAction.stabilizer G (T.line.vert a), orderOf p = 3 →
      ∀ z ∈ fixSet G (MulAction.orbit ↥H (T.line.vert a)), p * z = z * p := by
  obtain ⟨L, hL, hHL⟩ := hS.lam
  obtain ⟨n, hn, C, hCg, hCf, hC2, ⟨e⟩⟩ :=
    fan41_3 F _ _ _ L (T.line.adj a) (T.line.nb a) hL h3 h28
  intro p hp hp3 z hz
  have hpα := MulAction.mem_stabilizer_iff.1 hp.2
  have hpL : p ∈ L ⊓ MulAction.stabilizer G (T.line.vert a) := ⟨hHL hp.1, hp.2⟩
  have hαA : T.line.vert a ∈ MulAction.orbit ↥H (T.line.vert a) := MulAction.mem_orbit_self _
  have hNK : ∀ g ∈ fixSet G (MulAction.orbit ↥H (T.line.vert a)),
      g ∈ L ⊓ nbrStab Γ G (T.line.vert a) := fun g hg =>
    ⟨hHL (hS.fixSet_le_H F hg), hS.fixSet_le_nbrStab F hm hαA hg⟩
  have hKL : L ⊓ nbrStab Γ G (T.line.vert a) ≤ L ⊓ MulAction.stabilizer G (T.line.vert a) :=
    fun g hg => ⟨hg.1, F.nbrStab_le_stabilizer _ hg.2⟩
  let O : Subgroup ↥(L ⊓ MulAction.stabilizer G (T.line.vert a)) :=
    (L ⊓ nbrStab Γ G (T.line.vert a)).subgroupOf (L ⊓ MulAction.stabilizer G (T.line.vert a))
  let N : Subgroup ↥(L ⊓ MulAction.stabilizer G (T.line.vert a)) :=
    (fixSet G (MulAction.orbit ↥H (T.line.vert a))).subgroupOf
      (L ⊓ MulAction.stabilizer G (T.line.vert a))
  have hOn : O.Normal := by
    refine ⟨fun k hk g => ?_⟩
    exact ⟨(L).mul_mem ((L).mul_mem g.2.1 hk.1) ((L).inv_mem g.2.1),
      nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 g.2.2) hk.2⟩
  have hO2 : IsPGroup 2 ↥O :=
    ((F.nbrStab_isPGroup (T.line.vert a)).to_le (inf_le_right :
      L ⊓ nbrStab Γ G (T.line.vert a) ≤ _)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hKL).symm
  have hNO : N ≤ O := fun g hg => hNK g.1 hg
  have hp3' : (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a))) ^ 3 = 1 := by
    refine Subtype.ext ?_
    simpa using (hp3 ▸ pow_orderOf_eq_one p)
  have hp1 : (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a))) ≠ 1 := by
    intro h
    have : p = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hp3
    omega
  have hpN : ∀ g ∈ N, (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a))) * g *
      (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a)))⁻¹ ∈ N := fun g hg =>
    fixSet_orbit_conj hp.1 hg
  have h5 : ∃ k ∈ O, (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a))) * k *
      (⟨p, hpL⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a)))⁻¹ * k⁻¹ ∉ N := by
    obtain ⟨k, hk, hkN⟩ := claim_five_a hS F hm (by omega) hp.1 hpα hp3
    exact ⟨⟨k, hKL ⟨hHL hk.1, hk.2⟩⟩, ⟨hHL hk.1, hk.2⟩, hkN⟩
  have hzN : (⟨z, (hKL (hNK z hz))⟩ : ↥(L ⊓ MulAction.stabilizer G (T.line.vert a))) ∈ N := hz
  have := central_perm hn hC2 e hp3' hp1 hO2 hNO hpN h5 _ hzN
  exact congrArg Subtype.val this

end CFSG.Quasithin.Fan86
