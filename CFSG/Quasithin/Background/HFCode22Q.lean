module

public import CFSG.Quasithin.Background.SmithB45MatQ
public import CFSG.Quasithin.Background.HFCode22U
public import Certificates.Certificate7240

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.Code

variable {V : Type*} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}

theorem two_lt_qOf_code22_self
    (h : MathieuCode22 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf L := by
  have hLL : IsOver L L := ⟨le_rfl, Subgroup.le_normalizer⟩
  obtain ⟨e, he⟩ := code22_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := code22_card_le hLL h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective
    phi22 (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos22s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 5 [] Certificates.certificate7240 _ hk)) e
    (map_le_of_normalizer hLL he normalizer_rhoC10_mog22 hA.1) hA.isElemAbelian2 hc
  have hall : l.all inM22s2 = true := by
    rw [List.all_eq_true]
    intro s hs
    have hsA : chainAut e psiC22 phi22 g s ∈ A := (hchain _).2 ⟨s, mem_subprods_of_mem hs, rfl⟩
    have h1 : congrHom e (chainAut e psiC22 phi22 g s) ∈
        (rhoC10 mog22 mog22_le_mog22plus).range := by
      rw [← he]
      exact ⟨_, hA.1 hsA, rfl⟩
    obtain ⟨m, hm⟩ := h1
    set m' : ↥mog22plus := ⟨m, mog22_le_mog22plus m.2⟩ with hm'
    have h2 : psiC22 (phi22 s) = psiC22 (g * m' * g⁻¹) := by
      have k1 : psiC22 (phi22 s) =
          congrHom (twistEquiv e psiC22 g) (chainAut e psiC22 phi22 g s) :=
        (congrHom_chainAut e psiC22 phi22 g s).symm
      have k3 := congrHom_trans_eq_conj e (psiC22 g) (chainAut e psiC22 phi22 g s)
      have k4 : psiC22 (phi22 s) =
          psiC22 g * rhoC10 mog22 mog22_le_mog22plus m * (psiC22 g)⁻¹ := by
        rw [hm]
        exact k1.trans k3
      rw [k4, map_mul, map_mul, map_inv]
      rfl
    have h3 := rhoC10_mog22plus_injective h2
    have h4 : ((phi22 s : ↥mog22plus) : Equiv.Perm (Fin 24)) ∈ mog22 := by
      rw [h3]
      exact mog22_normal_in_plus g.2 m.2
    obtain ⟨⟨-, h0⟩, -⟩ := h4
    have h5 : (T22s2.perm s 0 : ℕ) = 0 := by
      have := (mem_stab_iff 0 _).1 h0
      exact congrArg Fin.val this
    rw [T22s2.perm_val] at h5
    simp only [inM22s2, beq_iff_eq]
    exact h5
  have hpred' : predQ 10 actC22s2 true l = true := by
    simpa [predQ22in, hall] using hpred
  have hact : ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC22 g)) (chainAut e psiC22 phi22 g)
      actC22s2 :=
    chainAct_twist e psiC22 phi22 g (fun s _ hm => psiC22_phi22 s hm)
      (fun s _ hm => by
        rw [actC22s2, actM_matsC10 T22s2 (mats := matsC22) rfl s hm]
        exact actC10_lt _ _)
  exact lt_of_predQ hpred' hact hchain
    (chainAut_injective rhoC10_mog22plus_injective (T22s2.toSub_injective _ _) g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

end CFSG.Quasithin.B45Mat
