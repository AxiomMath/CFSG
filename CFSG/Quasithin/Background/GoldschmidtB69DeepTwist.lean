module

public import CFSG.Quasithin.Background.B69SL3Aux
public import CFSG.Quasithin.Background.Sp4InfTwist

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open B6

namespace B69

theorem exists_twist_member_sp4 {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {K : Type} [Field K] [Finite K] [CharP K 2] (r : ↥L →* ↥(StatedSp 2 K))
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (e₁ : Sec W₁ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K)
    (he₁ : ∀ (hLW : L ≤ stabSub W₁) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₁ (fixV L)),
      e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₁ s))
    (t : MulAut V) (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L)
    (htw : ∃ (A' : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K), ∀ l l' : ↥L,
      (l' : MulAut V) = t * l * t⁻¹ →
        (((r l' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ *
            (((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) K ≃* StdMod (Fin 2 ⊕ Fin 2) K,
      (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) K),
        Φ (matAut ((r l : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) x) =
          matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (Φ x)) → False) :
    ∃ W₂ : Subgroup V, W₂ ∈ IrrPlus L (⊤ : Subgroup V) ∧ W₁ ≠ W₂ ∧
      ∃ e₂ : Sec W₂ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K,
        ∀ (hLW : L ≤ stabSub W₂) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₂ (fixV L)),
          e₂ (B5.secHom L hLW hLU l s) =
            matAut ((tauSp (r l) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) (e₂ s) := by
  classical
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := mem_normalizer_of_forall_mem ht ht'
  set W₂ : Subgroup V := W₁.map (t⁻¹ : MulAut V).toMonoidHom with hW₂
  have hW₂irr : W₂ ∈ IrrPlus L (⊤ : Subgroup V) :=
    irrPlus_map (g := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht' x hx)
      (fun x hx => by rw [inv_inv]; exact ht x hx) hW₁
  have hmemW₂ : ∀ w, w ∈ W₂ ↔ t w ∈ W₁ := fun w => by
    rw [hW₂, mem_map_aut_iff, inv_inv]
  have hLW₁ : L ≤ stabSub W₁ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₁).1
  have hLW₂ : L ≤ stabSub W₂ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₂irr).1
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  let eT : ↥W₂ ≃* ↥W₁ :=
    { toFun := fun w => ⟨t (w : V), (hmemW₂ w).1 w.2⟩
      invFun := fun w => ⟨t⁻¹ (w : V), (hmemW₂ _).2 (by simp)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hfixt : ∀ w ∈ fixV L, t w ∈ fixV L := fun w hw => mem_fixV_of_conj ht' hw
  have hfixt' : ∀ w ∈ fixV L, t⁻¹ w ∈ fixV L := fun w hw =>
    mem_fixV_of_conj (t := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht x hx) hw
  have hmapC : ((fixV L).subgroupOf W₂).map eT.toMonoidHom = (fixV L).subgroupOf W₁ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfixt _ hx
    · intro hy
      exact ⟨eT.symm y, hfixt' _ hy, eT.apply_symm_apply y⟩
  let τ : Sec W₂ (fixV L) ≃* Sec W₁ (fixV L) := QuotientGroup.congr _ _ eT hmapC
  let c : MulAut ↥L := indAut L t
  have hc : ∀ l : ↥L, ((c l : ↥L) : MulAut V) = t * l * t⁻¹ := fun l => coe_indAut_apply htN l
  have hτ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      τ (B5.secHom L hLW₂ hLU l s) = B5.secHom L hLW₁ hLU (c l) (τ s) := by
    intro l s
    induction s using QuotientGroup.induction_on with
    | H w =>
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show t ((l : MulAut V) (w : V)) = ((c l : ↥L) : MulAut V) (t (w : V))
      rw [hc]
      simp [MulAut.mul_apply]
  let e₂₀ : Sec W₂ (fixV L) ≃* StdMod (Fin 2 ⊕ Fin 2) K := τ.trans e₁
  have he₂₀ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      e₂₀ (B5.secHom L hLW₂ hLU l s) =
        matAut ((r (c l) : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) (e₂₀ s) := by
    intro l s
    show e₁ (τ (B5.secHom L hLW₂ hLU l s)) = matAut _ (e₁ (τ s))
    rw [hτ]
    exact he₁ hLW₁ hLU (c l) (τ s)
  obtain ⟨A', σ, hmat⟩ := htw
  obtain ⟨e₂', he₂'⟩ := exists_tau_coord_of_mat (K := K) (B5.secHom L hLW₂ hLU) r
    (r.comp c.toMonoidHom) A' σ (fun l => hmat l (c l) (hc l)) e₂₀ he₂₀
  have hne : W₁ ≠ W₂ := ne_of_tau' r hLW₁ hLW₂ hLU e₁ e₂' (he₁ hLW₁ hLU) he₂' hniso
  refine ⟨W₂, hW₂irr, hne, e₂', fun hLW hLU' l s => ?_⟩
  exact he₂' l s

end B69

end CFSG.Quasithin
