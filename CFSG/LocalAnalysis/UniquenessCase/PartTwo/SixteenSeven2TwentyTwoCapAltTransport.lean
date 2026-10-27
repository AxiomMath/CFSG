module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)

theorem s16c167_exists_hyperplane {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {E H : Subgroup W} (hH : E3.mQuot E H = 1) {A : Type} [AddGroup A]
    (ψ : ↥E ≃* Multiplicative A) :
    ∃ K : AddSubgroup A, K.index = 2 ∧
      ∀ (e : W) (he : e ∈ E), e ∈ H ↔ Multiplicative.toAdd (ψ ⟨e, he⟩) ∈ K := by
  have hsq : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW (v : W))
  have hP : IsPGroup 2 ↥E := CFSG.Quasithin.isPGroup_two_of_sq_eq_one hsq
  have hrel : H.relIndex E = 2 := by
    have h := E3.relIndex_eq_two_pow hP H
    rw [hH, pow_one] at h
    exact h
  have hidx : (H.subgroupOf E).index = 2 := hrel
  have hK0 : ((H.subgroupOf E).map ψ.toMonoidHom).index = 2 :=
    (Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective
      (H.subgroupOf E)).trans hidx
  refine ⟨Subgroup.toAddSubgroup' ((H.subgroupOf E).map ψ.toMonoidHom), ?_, ?_⟩
  · rw [show (Subgroup.toAddSubgroup' ((H.subgroupOf E).map ψ.toMonoidHom)).index =
        ((H.subgroupOf E).map ψ.toMonoidHom).index from rfl, hK0]
  · intro e he
    constructor
    · intro heH
      show Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨e, he⟩)) ∈
        (H.subgroupOf E).map ψ.toMonoidHom
      rw [ofAdd_toAdd]
      exact (Subgroup.mem_map_iff_mem ψ.injective).2 (Subgroup.mem_subgroupOf.2 heH)
    · intro hK
      have h1 : Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨e, he⟩)) ∈
          (H.subgroupOf E).map ψ.toMonoidHom := hK
      rw [ofAdd_toAdd] at h1
      exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_map_iff_mem ψ.injective).1 h1)

theorem s16c167_altNatural_transvection {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {E : Subgroup W} {n : ℕ} {π : alternatingGroup (Fin n) →* ↥L}
    (hπ : Function.Surjective π) {ψ : ↥E ≃* Multiplicative (altHeart n)}
    (hψ : ∀ (γ : alternatingGroup (Fin n)) (u : ↥E)
        (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ E),
        ψ ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (ψ u))))
    (hLE : ∀ g : ↥L, ∀ e ∈ E, (g : MulAut W) e ∈ E)
    {x : MulAut W} (hxL : L.map (MulAut.conj x).toMonoidHom = L)
    (hxE : E.map x.toMonoidHom = E) {H : Subgroup W} {K : AddSubgroup (altHeart n)}
    (hK : ∀ (e : W) (he : e ∈ E), e ∈ H ↔ Multiplicative.toAdd (ψ ⟨e, he⟩) ∈ K)
    (hxH : ∀ e ∈ H, x e = e) (hxT : ∀ e ∈ E, x e * e⁻¹ ∈ H) :
    ∃ t : altHeart n ≃+ altHeart n,
      (∀ (e : W) (he : e ∈ E) (hxe : x e ∈ E),
        Multiplicative.toAdd (ψ ⟨x e, hxe⟩) = t (Multiplicative.toAdd (ψ ⟨e, he⟩))) ∧
      (∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
        ∀ v, t (altAct σ v) = altAct σ' (t v)) ∧
      (∀ v ∈ K, t v = v) ∧ ∀ v, t v - v ∈ K := by
  have hxmem : ∀ e : ↥E, x (e : W) ∈ E := fun e => by
    have h : x (e : W) ∈ E.map x.toMonoidHom := Subgroup.mem_map.mpr ⟨e, e.2, rfl⟩
    rwa [hxE] at h
  have hxinvmem : ∀ e : ↥E, x⁻¹ (e : W) ∈ E := fun e => by
    have h : (e : W) ∈ E.map x.toMonoidHom := by rw [hxE]; exact e.2
    obtain ⟨e', he', hxe'⟩ := Subgroup.mem_map.mp h
    have hxee' : (e : W) = x e' := hxe'.symm
    rw [hxee', MulAut.inv_apply_self W x e']
    exact he'
  let xE : ↥E ≃* ↥E :=
    { toFun := fun e => ⟨x (e : W), hxmem e⟩
      invFun := fun e => ⟨x⁻¹ (e : W), hxinvmem e⟩
      left_inv := fun e => Subtype.ext (MulAut.inv_apply_self W x (e : W))
      right_inv := fun e => Subtype.ext (MulAut.apply_inv_self W x (e : W))
      map_mul' := fun e f => Subtype.ext (map_mul x (e : W) (f : W)) }
  let T : Multiplicative (altHeart n) ≃* Multiplicative (altHeart n) := ψ.symm.trans (xE.trans ψ)
  let t : altHeart n ≃+ altHeart n := AddEquiv.toMultiplicative.symm T
  have ht_apply : ∀ e : ↥E, t (Multiplicative.toAdd (ψ e)) =
      Multiplicative.toAdd (ψ (xE e)) := by
    intro e
    show Multiplicative.toAdd (T (Multiplicative.ofAdd (Multiplicative.toAdd (ψ e)))) =
      Multiplicative.toAdd (ψ (xE e))
    rw [ofAdd_toAdd]
    simp only [T, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro e he hxe
    rw [ht_apply ⟨e, he⟩]
    exact congrArg Multiplicative.toAdd (congrArg ψ (Subtype.ext rfl))
  · intro σ hσ
    let γ : alternatingGroup (Fin n) := ⟨σ, hσ⟩
    let g : MulAut W := ((π γ : ↥L) : MulAut W)
    have hgL : g ∈ L := (π γ).2
    have hconj : MulAut.conj x g ∈ L := by
      have h : MulAut.conj x g ∈ L.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨g, hgL, rfl⟩
      rwa [hxL] at h
    obtain ⟨γ', hγ'⟩ := hπ ⟨MulAut.conj x g, hconj⟩
    have hγ'val : ((π γ' : ↥L) : MulAut W) = MulAut.conj x g := congrArg Subtype.val hγ'
    have hxg : ∀ e : W, ((π γ' : ↥L) : MulAut W) (x e) = x (g e) := by
      intro e
      rw [hγ'val, MulAut.conj_apply]
      simp [MulAut.mul_apply, MulAut.inv_apply_self]
    refine ⟨(γ' : Equiv.Perm (Fin n)), γ'.2, ?_⟩
    intro v
    obtain ⟨e, he⟩ : ∃ e : ↥E, Multiplicative.toAdd (ψ e) = v := by
      obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
      exact ⟨u, by rw [hu, toAdd_ofAdd]⟩
    have hgmem : g (e : W) ∈ E := hLE ⟨g, hgL⟩ (e : W) e.2
    have hxemem : x (e : W) ∈ E := hxmem e
    have hg'mem : ((π γ' : ↥L) : MulAut W) (x (e : W)) ∈ E :=
      hLE ⟨_, (π γ').2⟩ _ hxemem
    have hh : ψ ⟨g (e : W), hgmem⟩ = Multiplicative.ofAdd (altAct σ v) := by
      rw [hψ γ e hgmem, he]
    have halt : altAct σ v = Multiplicative.toAdd (ψ ⟨g (e : W), hgmem⟩) := by
      rw [hh, toAdd_ofAdd]
    have hh' : ψ ⟨((π γ' : ↥L) : MulAut W) (x (e : W)), hg'mem⟩ =
        Multiplicative.ofAdd (altAct (γ' : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (ψ ⟨x (e : W), hxemem⟩))) :=
      hψ γ' ⟨x (e : W), hxemem⟩ hg'mem
    have hsub : (⟨x (g (e : W)), hxmem ⟨g (e : W), hgmem⟩⟩ : ↥E) =
        ⟨((π γ' : ↥L) : MulAut W) (x (e : W)), hg'mem⟩ :=
      Subtype.ext (hxg (e : W)).symm
    calc t (altAct σ v)
        = t (Multiplicative.toAdd (ψ ⟨g (e : W), hgmem⟩)) := by rw [halt]
      _ = Multiplicative.toAdd (ψ ⟨x (g (e : W)), hxmem ⟨g (e : W), hgmem⟩⟩) :=
            ht_apply ⟨g (e : W), hgmem⟩
      _ = Multiplicative.toAdd (ψ ⟨((π γ' : ↥L) : MulAut W) (x (e : W)), hg'mem⟩) := by
            rw [hsub]
      _ = altAct (γ' : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (ψ ⟨x (e : W), hxemem⟩)) := by
            rw [hh', toAdd_ofAdd]
      _ = altAct (γ' : Equiv.Perm (Fin n)) (t (Multiplicative.toAdd (ψ e))) := by
            rw [ht_apply]
            exact congrArg (fun w => altAct (γ' : Equiv.Perm (Fin n))
              (Multiplicative.toAdd (ψ w))) (Subtype.ext rfl)
      _ = altAct (γ' : Equiv.Perm (Fin n)) (t v) := by rw [he]
  · intro v hv
    obtain ⟨e, he⟩ : ∃ e : ↥E, Multiplicative.toAdd (ψ e) = v := by
      obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
      exact ⟨u, by rw [hu, toAdd_ofAdd]⟩
    have heH : (e : W) ∈ H := (hK (e : W) e.2).2 (by rwa [he])
    have hxfix : x (e : W) = (e : W) := hxH (e : W) heH
    have h1 : t (Multiplicative.toAdd (ψ e)) =
        Multiplicative.toAdd (ψ ⟨x (e : W), hxmem e⟩) := ht_apply e
    rw [← he, h1]
    exact congrArg Multiplicative.toAdd (congrArg ψ (Subtype.ext hxfix))
  · intro v
    obtain ⟨e, he⟩ : ∃ e : ↥E, Multiplicative.toAdd (ψ e) = v := by
      obtain ⟨u, hu⟩ := ψ.surjective (Multiplicative.ofAdd v)
      exact ⟨u, by rw [hu, toAdd_ofAdd]⟩
    have hxemem : x (e : W) ∈ E := hxmem e
    have hprod : x (e : W) * (e : W)⁻¹ ∈ E := E.mul_mem hxemem (E.inv_mem e.2)
    have h1 : t (Multiplicative.toAdd (ψ e)) =
        Multiplicative.toAdd (ψ ⟨x (e : W), hxemem⟩) := ht_apply e
    have hsub : Multiplicative.toAdd (ψ ⟨x (e : W), hxemem⟩) -
        Multiplicative.toAdd (ψ e) =
        Multiplicative.toAdd (ψ ⟨x (e : W) * (e : W)⁻¹, hprod⟩) := by
      rw [sub_eq_add_neg, ← toAdd_inv, ← map_inv, ← toAdd_mul, ← map_mul]
      exact congrArg Multiplicative.toAdd (congrArg ψ (Subtype.ext rfl))
    rw [← he, h1, hsub]
    exact (hK _ hprod).1 (hxT (e : W) e.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
