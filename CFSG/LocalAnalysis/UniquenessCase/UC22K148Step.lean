module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22K148LemFP
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.RankThree.FFModules.FixSubConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

@[expose] def HasFactors148Below (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V']
    [Finite V'] (ρ' : Representation (ZMod 2) G' V'), Nat.card G' < n →
    CFSG.pCore 2 G' = ⊥ → Function.Injective ρ' →
    (∀ L : Subgroup G', IsComponentOf L ⊤ →
      (∃ k : ℕ, 2 ≤ k ∧ IsL2 ↥L k) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2)))) →
    hP ρ' = ⊤ → HasFactors148 G'

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem isInternalDirect_cons {M K : Subgroup G} (hM : M.Normal) (hMK : M ⊓ K = ⊥)
    (hsup : M ⊔ K = ⊤) (hc : ∀ m ∈ M, ∀ k ∈ K, m * k = k * m) {s : ℕ}
    {Ks : Fin s → Subgroup G} (hD : IsInternalDirect K Ks) :
    IsInternalDirect ⊤ (Fin.cons M Ks : Fin (s + 1) → Subgroup G) := by
  obtain ⟨hDs, hDc, hDi⟩ := hD
  have hKs : ∀ i, Ks i ≤ K := fun i => hDs ▸ le_iSup Ks i
  have h0 : (Fin.cons M Ks : Fin (s + 1) → Subgroup G) 0 = M := Fin.cons_zero _ _
  have hS : ∀ i, (Fin.cons M Ks : Fin (s + 1) → Subgroup G) i.succ = Ks i := fun i =>
    Fin.cons_succ _ _ _
  refine ⟨eq_top_iff.2 (hsup ▸ sup_le (le_iSup_of_le 0 h0.ge) ?_), ?_, ?_⟩
  · rw [← hDs]
    exact iSup_le fun i => le_iSup_of_le i.succ (hS i).ge
  · intro i j hij x hx y hy
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        rw [h0] at hx
        rw [hS] at hy
        exact hc x hx y (hKs j hy)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        rw [hS] at hx
        rw [h0] at hy
        exact (hc y hy x (hKs i hx)).symm
      | succ j =>
        rw [hS] at hx hy
        exact hDc i j (fun h => hij (by rw [h])) x hx y hy
  · intro i
    induction i using Fin.cases with
    | zero =>
      rw [h0, eq_bot_iff, ← hMK]
      refine inf_le_inf_left M (iSup₂_le fun j hj => ?_)
      induction j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j => exact (hS j).le.trans (hKs j)
    | succ i =>
      rw [hS, eq_bot_iff]
      have hle : (⨆ j ∈ {j : Fin (s + 1) | j ≠ i.succ},
          (Fin.cons M Ks : Fin (s + 1) → Subgroup G) j) ≤ M ⊔ ⨆ j ∈ {j | j ≠ i}, Ks j :=
        iSup₂_le fun j hj => by
          induction j using Fin.cases with
          | zero => exact h0.le.trans le_sup_left
          | succ j =>
            refine (hS j).le.trans (le_sup_of_le_right ?_)
            exact le_iSup₂_of_le (f := fun j (_ : j ∈ {j | j ≠ i}) => Ks j) j
              (show j ≠ i from fun h => hj (by rw [h])) le_rfl
      have hRK : (⨆ j ∈ {j | j ≠ i}, Ks j) ≤ K := iSup₂_le fun j _ => hKs j
      intro x hx
      obtain ⟨hxi, hxR⟩ := Subgroup.mem_inf.1 hx
      haveI := hM
      obtain ⟨m, hm, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (hle hxR)
      have hmK : m ∈ M ⊓ K := ⟨hm, by
        have h := K.mul_mem (hKs i hxi) (K.inv_mem (hRK hr))
        rwa [mul_inv_cancel_right] at h⟩
      rw [hMK, Subgroup.mem_bot] at hmK
      subst hmK
      rw [one_mul] at hxi ⊢
      have h : r ∈ Ks i ⊓ ⨆ j ∈ {j | j ≠ i}, Ks j := ⟨hxi, hr⟩
      rwa [hDi i] at h

theorem isFactor148_map_subtype {K : Subgroup G} (hK : K.Normal) {H : Subgroup ↥K}
    (h : IsFactor148 H) : IsFactor148 (H.map K.subtype) := by
  have e := H.equivMapOfInjective K.subtype K.subtype_injective
  rcases h with h | h | h
  · exact Or.inl (isComponentOf_map_subtype hK h)
  · exact Or.inr (Or.inl (h.map fun f => e.symm.trans f))
  · exact Or.inr (Or.inr (h.map fun f => e.symm.trans f))

theorem hasFactors148_of_prod [Finite G] [Finite V] (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G)) {M K : Subgroup G} (hM : M.Normal)
    (hK : K.Normal) (hMK : M ⊓ K = ⊥) (hsup : M ⊔ K = ⊤) (hc : ∀ m ∈ M, ∀ k ∈ K, m * k = k * m)
    (hM1 : M ≠ ⊥) (hfM : IsFactor148 M) {X : Submodule (ZMod 2) V}
    (hX : commOn ρ M ⊤ ≤ X ⊔ fixSub ρ M) (hKX : ∀ k ∈ K, ∀ x ∈ X, ρ k x = x) :
    HasFactors148 G := by
  have hW : ∀ g : G, ∀ w ∈ fixSub ρ M, ρ g w ∈ fixSub ρ M := fun g w hw =>
    rep_apply_mem_fixSub_of_normal ρ hM g hw
  have hle : commOn ρ M ⊤ ⊔ fixSub ρ M ≤ X ⊔ fixSub ρ M := sup_le hX le_sup_right
  have hfaith : ∀ k ∈ K, (∀ w ∈ fixSub ρ M, ρ k w = w) → k = 1 := fun k hk hkW => by
    have hmem : k ∈ cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M) := ⟨hk, fun v hv => by
      obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 (hle hv)
      rw [map_add, hKX k hk x hx, hkW w hw]⟩
    rw [cenOn_commOn_sup_fixSub_eq_bot hρ hO hM hK hc] at hmem
    exact hmem
  have hinj : Function.Injective
      (subRep (ρ.comp K.subtype) (fixSub ρ M) fun g w hw => hW g w hw) :=
    (injective_subRep_iff _).2 fun g hg => Subtype.ext (hfaith g g.2 hg)
  have hHK := hP_subRep_comp_subtype_eq_top hρ hH hM hMK hsup hW fun m hm w hw =>
    mem_fixSub.1 hw m hm
  have hKlt : K < ⊤ := lt_top_iff_ne_top.2 fun h => hM1 (by rw [← inf_top_eq M, ← h, hMK])
  have hcard : Nat.card ↥K < Nat.card G := by
    have h := Subgroup.card_lt_of_lt hKlt
    rwa [Subgroup.card_top] at h
  obtain ⟨s, Ks, hDK, hFK⟩ := IH ↥K ↥(fixSub ρ M) _ hcard (pCore_subgroup_eq_bot hO hK) hinj
    (fun L hL => allowed_shape_of_normal hK hshape hL) hHK
  have hD := (isInternalDirect_map_subtype_iff K ⊤ Ks).1 hDK
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hD
  refine ⟨s + 1, Fin.cons M fun i => (Ks i).map K.subtype, isInternalDirect_cons hM hMK hsup hc hD,
    fun i => ?_⟩
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact hfM
  | succ i => rw [Fin.cons_succ]; exact isFactor148_map_subtype hK (hFK i)

theorem inf_cenOn_commOn_eq_bot_of_pCore_eq_bot (hρ : Function.Injective ρ)
    (hO : CFSG.pCore 2 G = ⊥) {N : Subgroup G} (hN : N.Normal) :
    N ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊥ := by
  have hnorm : (N ⊓ cenOn ρ ⊤ (commOn ρ N ⊤)).Normal := by
    haveI := hN
    haveI := cenOn_commOn_normal (ρ := ρ) hN
    infer_instance
  have hp : IsPGroup 2 ↥(N ⊓ cenOn ρ ⊤ (commOn ρ N ⊤)) := fun k => by
    refine ⟨1, Subtype.ext (hρ (LinearMap.ext fun v => ?_))⟩
    have h1 : ρ k (ρ k v - v) = ρ k v - v := k.2.2.2 _ (sub_mem_commOn k.2.1 Submodule.mem_top)
    rw [map_sub, sub_eq_iff_eq_add] at h1
    rw [pow_one, Subgroup.coe_pow, pow_two, glRep_mul_apply, h1, Subgroup.coe_one, map_one,
      Module.End.one_apply, ZModModule.sub_eq_add, add_right_comm, ZModModule.add_self, zero_add]
  have hle : N ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) ≤ CFSG.pCore 2 G :=
    le_sSup (s := {M : Subgroup G | M.Normal ∧ IsPGroup 2 M}) ⟨hnorm, hp⟩
  rw [hO] at hle
  exact le_bot_iff.1 hle

theorem hasFactors148_of_inner [Finite G] [Finite V] (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G)) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) (hin : ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u) :
    HasFactors148 G := by
  have hLn : L.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hH]
    exact hP_le_normalizer hρ hL
  have hK := cenOn_commOn_normal (ρ := ρ) hLn
  have hLK := inf_cenOn_commOn_eq_bot_of_pCore_eq_bot hρ hO hLn
  have hsup : L ⊔ cenOn ρ ⊤ (commOn ρ L ⊤) = ⊤ := eq_top_iff.2 fun g _ => by
    obtain ⟨l, hl, hgl⟩ := hin g
    have hk : l⁻¹ * g ∈ cenOn ρ ⊤ (commOn ρ L ⊤) :=
      ⟨Subgroup.mem_top _, fun x hx => by rw [glRep_mul_apply, hgl x hx, glRep_inv_apply]⟩
    have e : g = l * (l⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hk)
  have hL1 : L ≠ ⊥ := by
    haveI := hL.2.2.2
    haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  exact hasFactors148_of_prod hO hρ hshape hH IH hLn hK hLK hsup
    (fun m hm k hk => Subgroup.commute_of_normal_of_disjoint L _ hLn hK (disjoint_iff.2 hLK) m k
      hm hk) hL1 (Or.inl hL) le_sup_left fun k hk x hx => hk.2 x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
