module

public import CFSG.Quasithin.Vol2.Ch3Sec3Sp4ZData
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316Q

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.QuasithinUnique
open CFSG.Open (pCoreOf)

namespace Sp4Z

theorem map_mem_statedSp {K K' : Type} [Field K] [Field K'] (f : K →+* K')
    {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ StatedSp 2 K) :
    Matrix.GeneralLinearGroup.map f g ∈ StatedSp 2 K' := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff] at hg ⊢
  have h1 := congrArg (fun M => M.map f) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map, Matrix.map_zero _
    (map_zero f), Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_neg _ (map_neg f)] at h1
  exact h1

theorem map_injective {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2 ⊕ Fin 2) e.toRingHom) := by
  intro g h hgh
  have h1 := congrArg (Matrix.GeneralLinearGroup.map e.symm.toRingHom) hgh
  rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp_apply,
    ← Matrix.GeneralLinearGroup.map_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
    Matrix.GeneralLinearGroup.map_id] at h1
  exact h1

theorem map_map_symm {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (g : GL (Fin 2 ⊕ Fin 2) K') :
    Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.map e.symm.toRingHom g) =
      g := by
  rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
    RingEquiv.toRingHom_comp_symm_toRingHom, Matrix.GeneralLinearGroup.map_id]
  rfl

end Sp4Z

namespace L3316

open Sp4Z

theorem card_blockZ_le_four {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsSp4Block L) : Nat.card ↥(blockZ L) ≤ 4 := by
  classical
  have hcardU := card_blockU hL
  obtain ⟨hS, F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hL
  let e : F ≃+* F4 := FiniteField.ringEquivOfCardEq (by rw [hF, F4.card])
  have hUQ : (blockU L) ≤ (blockQ L) := C1.blockU_le_blockQ hS
  have hU : ∀ x ∈ (blockU L), ∀ y ∈ (blockU L), x * y = y * x := fun x hx y hy =>
    C1.blockU_comm hS x hx y (hUQ hy)
  have hLU : L ≤ Subgroup.normalizer ((blockU L) : Set G) := C1.le_normalizer_blockU L
  have hQc : ∀ q ∈ (blockQ L), ∀ x ∈ (blockU L), q * x = x * q := fun q hq x hx =>
    (C1.blockU_comm hS x hx q hq).symm
  have hpQ : ∀ q ∈ CFSG.pCore 2 ↥L, (q : G) ∈ (blockQ L) := fun q hq => by
    rw [blockQ, pCoreOf]
    exact ⟨q, hq, rfl⟩
  let α' : ↥L →* GL Idx F4 :=
    (Matrix.GeneralLinearGroup.map e.toRingHom).comp ((StatedSp 2 F).subtype.comp α)
  have hα'mem : ∀ l, α' l ∈ StatedSp 2 F4 := fun l =>
    map_mem_statedSp e.toRingHom (α l).2
  have hα'k : ∀ l, α' l = 1 → l ∈ CFSG.pCore 2 ↥L := by
    intro l h1
    rw [← hαk, MonoidHom.mem_ker]
    apply Subtype.ext
    apply map_injective e
    rw [Subgroup.coe_one, map_one]
    exact h1
  have hα'surj : ∀ g ∈ StatedSp 2 F4, ∃ l, α' l = g := by
    intro g hg
    obtain ⟨l, hl⟩ := hαs ⟨_, map_mem_statedSp e.symm.toRingHom hg⟩
    refine ⟨l, ?_⟩
    show Matrix.GeneralLinearGroup.map e.toRingHom ((α l : GL (Fin 2 ⊕ Fin 2) F)) = g
    rw [hl]
    exact map_map_symm e g
  obtain ⟨a', ha'⟩ := hα'surj genA genA_mem
  obtain ⟨b', hb'⟩ := hα'surj genB genB_mem
  set a : G := (a' : G) with hadef
  set b : G := (b' : G) with hbdef
  have ha : a ∈ Subgroup.normalizer ((blockU L) : Set G) := hLU a'.2
  have hb : b ∈ Subgroup.normalizer ((blockU L) : Set G) := hLU b'.2
  have hmem : ∀ l ∈ L, l ∈ Subgroup.closure ({a, b} ∪ ((blockQ L) : Set G)) := by
    intro l hl
    have h1 : α' ⟨l, hl⟩ ∈ (Subgroup.closure ({a', b'} : Set ↥L)).map α' := by
      rw [MonoidHom.map_closure, Set.image_pair, ha', hb', ← statedSp_eq_closure]
      exact hα'mem _
    obtain ⟨h, hh, hhl⟩ := h1
    have h2 : h⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := hα'k _ (by rw [map_mul, map_inv, hhl,
      inv_mul_cancel])
    have h3 : (h : G) ∈ Subgroup.closure ({a, b} : Set G) := by
      have := Subgroup.mem_map_of_mem L.subtype hh
      rwa [MonoidHom.map_closure, Set.image_pair] at this
    have h4 : l = (h : G) * ((h⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [h4]
    exact Subgroup.mul_mem _ (Subgroup.closure_mono Set.subset_union_left h3)
      (Subgroup.subset_closure (Or.inr (hpQ _ h2)))
  let β' : ↥(blockU L) →* Multiplicative (Idx → F4) :=
    (AddMonoidHom.toMultiplicative (e.toRingHom.toAddMonoidHom.compLeft Idx)).comp β
  have hβ'v : ∀ u, Multiplicative.toAdd (β' u) = fun i => e (Multiplicative.toAdd (β u) i) :=
    fun u => rfl
  have hβ'k : ∀ z : ↥(blockU L), β' z = 1 → (z : G) ∈ (blockZ L) := by
    intro z hz
    have h1 : β z = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      have h2 := congrFun (congrArg Multiplicative.toAdd hz) i
      rw [hβ'v] at h2
      exact e.injective (h2.trans (map_zero e).symm)
    have h3 : z ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h3
    exact h3
  have hβ's : Function.Surjective β' := by
    intro v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd fun i => e.symm (Multiplicative.toAdd v i))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [hβ'v, hu]
    exact e.apply_symm_apply _
  have hβ'e : ∀ (l : ↥L) (u v : ↥(blockU L)), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β' v) = (α' l : Matrix Idx Idx F4) *ᵥ Multiplicative.toAdd (β' u) := by
    intro l u v huv
    funext i
    rw [hβ'v, hβe l u v huv]
    exact RingHom.map_mulVec e.toRingHom _ _ i
  have hker : ∀ z : ↥(blockU L), β' z = 1 → a * z = z * a ∧ b * z = z * b := by
    intro z hz
    have h1 := hβ'k z hz
    exact ⟨Subgroup.mem_centralizer_iff.1 h1.2 a a'.2,
      Subgroup.mem_centralizer_iff.1 h1.2 b b'.2⟩
  have hβa : ∀ u v : ↥(blockU L), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β' v) = rhoA (Multiplicative.toAdd (β' u)) := by
    intro u v huv
    rw [hβ'e a' u v huv, ha', coe_genA]
    rfl
  have hβb : ∀ u v : ↥(blockU L), (v : G) = b * u * b⁻¹ →
      Multiplicative.toAdd (β' v) = rhoB (Multiplicative.toAdd (β' u)) := by
    intro u v huv
    rw [hβ'e b' u v huv, hb', coe_genB]
    rfl
  have hrel : ∀ i : Fin 3, ∀ x ∈ (blockU L), evalW a b (relW i) * x = x * evalW a b (relW i) := by
    intro i x hx
    have h1 : α' (evalW a' b' (relW i)) = 1 := by
      rw [map_evalW, ha', hb']
      apply Units.ext
      rw [coe_evalW, matW_relW, Units.val_one]
    have h2 := hpQ _ (hα'k _ h1)
    rw [show ((evalW a' b' (relW i) : ↥L) : G) = evalW a b (relW i) from
      map_evalW L.subtype a' b' (relW i)] at h2
    exact hQc _ h2 x hx
  have hUab : (blockU L) ≤ imC (blockU L) a ⊔ imC (blockU L) b :=
    le_of_commutator_eq (C1.commutator_blockU hS) fun l hl =>
      imC_le_of_mem_closure hU ha hb hQc (hmem l hl)
  have hcardV : Nat.card (Idx → F4) = 2 ^ 8 := by
    simp [Nat.card_eq_fintype_card, F4.card]
  have hb8 : Nat.card ↥(imC (blockU L) b) ≤ 2 ^ 8 := by
    rw [← hcardV]
    refine card_imC_le hU hb (fun u => Multiplicative.toAdd (β' u)) ?_ fun x y hxy => ?_
    · intro v
      obtain ⟨u, hu⟩ := hβ's (Multiplicative.ofAdd v)
      exact ⟨u, by simp only [hu, toAdd_ofAdd]⟩
    · exact cmap_eq_of_eq hU hb β' (fun z hz => (hker z hz).2)
        (Multiplicative.toAdd.injective hxy)
  have hS0 : ∀ v : Idx → F4, (∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) = v → cmap a u = 1) →
      ∀ v' : Idx → F4, (∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) = v' → cmap a u = 1) →
      ∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) = v + v' → cmap a u = 1 := by
    intro v hv v' hv' u hu
    obtain ⟨u₁, hu₁⟩ := hβ's (Multiplicative.ofAdd v)
    have h1 : Multiplicative.toAdd (β' (u₁⁻¹ * u)) = v' := by
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hu, hu₁, toAdd_ofAdd, neg_add_cancel_left]
    have h2 := cmap_mul hU ha u₁.2 (u₁⁻¹ * u).2
    rw [show (u₁ : G) * ((u₁⁻¹ * u : ↥(blockU L)) : G) = u by simp,
      hv u₁ (by rw [hu₁]; rfl), hv' _ h1, one_mul] at h2
    exact h2
  have hP : ∀ j : Fin 6, ∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) = relP j →
      cmap a u = 1 := by
    intro j u hu
    obtain ⟨u₀, hu₀⟩ := hβ's (Multiplicative.ofAdd (relV j))
    have hu₀' : Multiplicative.toAdd (β' u₀) = relV j := by rw [hu₀]; rfl
    have hfox := foxV_rel j
    rw [← hu₀'] at hfox
    exact cmap_eq_one_of_relation hU ha hb β' hβa hβb hker (relW (relIdx j))
      (hrel (relIdx j)) u₀ u (by rw [hfox]) (by rw [hfox, hu])
  have h0 : ∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) = 0 → cmap a u = 1 := by
    intro u hu
    have h1 : β' u = 1 := Multiplicative.toAdd.injective hu
    rw [cmap, (hker u h1).1, mul_inv_cancel_right, mul_inv_cancel]
  have hperp : ∀ u : ↥(blockU L), Multiplicative.toAdd (β' u) (Sum.inr 0) = 0 → cmap a u = 1 := by
    intro u hu
    obtain ⟨c, hc⟩ := exists_sum_relP (Multiplicative.toAdd (β' u) (Sum.inl 0))
      (Multiplicative.toAdd (β' u) (Sum.inl 1)) (Multiplicative.toAdd (β' u) (Sum.inr 1))
    have hv : Multiplicative.toAdd (β' u) = ∑ j, if c j then relP j else 0 := by
      rw [← hc]
      conv_lhs => rw [eq_vec4 (Multiplicative.toAdd (β' u)), hu]
    have hsum : ∀ u' : ↥(blockU L), Multiplicative.toAdd (β' u') =
        (∑ j, if c j then relP j else 0) → cmap a u' = 1 := by
      refine Finset.sum_induction _
        (fun v => ∀ u' : ↥(blockU L), Multiplicative.toAdd (β' u') = v → cmap a u' = 1)
        (fun v v' hv hv' => hS0 v hv v' hv') h0 fun j _ => ?_
      by_cases hj : c j
      · simp only [hj, ite_true]
        exact hP j
      · simp only [hj]
        exact h0
    exact hsum u hv
  have ha4 : Nat.card ↥(imC (blockU L) a) ≤ 4 := by
    rw [show (4 : ℕ) = Nat.card F4 by rw [Nat.card_eq_fintype_card, F4.card]]
    refine card_imC_le hU ha (fun u => Multiplicative.toAdd (β' u) (Sum.inr 0)) ?_ ?_
    · intro s
      obtain ⟨u, hu⟩ := hβ's (Multiplicative.ofAdd (vec4 0 0 s 0))
      exact ⟨u, by simp only [hu, toAdd_ofAdd]; rfl⟩
    · intro x y hxy
      have hd : Multiplicative.toAdd (β' (x * y⁻¹)) (Sum.inr 0) = 0 := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
        exact hxy ▸ add_neg_cancel _
      have h1 := hperp _ hd
      have h2 := cmap_mul hU ha (x * y⁻¹).2 y.2
      rw [show ((x * y⁻¹ : ↥(blockU L)) : G) * y = x by simp, h1, one_mul] at h2
      exact h2
  have hcomm : ∀ x ∈ imC (blockU L) a, ∀ y ∈ imC (blockU L) b, x * y = y * x :=
    fun x hx y hy => hU x (imC_le ha hx) y (imC_le hb hy)
  have h1 : Nat.card ↥(blockU L) ≤ 4 * 2 ^ 8 :=
    calc Nat.card ↥(blockU L) ≤ Nat.card ↥(imC (blockU L) a ⊔ imC (blockU L) b) :=
          Subgroup.card_le_of_le hUab
      _ ≤ Nat.card ↥(imC (blockU L) a) * Nat.card ↥(imC (blockU L) b) :=
          card_sup_le_of_comm hcomm
      _ ≤ 4 * 2 ^ 8 := Nat.mul_le_mul ha4 hb8
  rw [hcardU] at h1
  omega

theorem factSp4BlockZ_holds : FactSp4BlockZ := fun _ _ _ _ hL => card_blockZ_le_four hL

end L3316

end CFSG.Quasithin.H13
