module

public import CFSG.Quasithin.Vol2.Ch4Sec3Core

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_commutator_commutator_of_perfect' {A L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : ⁅A, L⁆ = ⁅⁅A, L⁆, L⁆ := by
  set W := ⁅⁅A, L⁆, L⁆ with hW
  refine le_antisymm ?_
    (commutator_le_left_of_le_normalizer (Subgroup.normalizer_commutator_ge_right A L))
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    mem_normalizer_commutator
      (mem_normalizer_commutator (Subgroup.le_normalizer ha) (hAL ha)) (hAL ha)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    mem_normalizer_commutator (Subgroup.normalizer_commutator_ge_right A L hl)
      (Subgroup.le_normalizer hl)
  have h1 : ⁅⁅L, A⁆, L⁆ ≤ W := by rw [Subgroup.commutator_comm L A]
  have h3 := three_subgroups_le (X := L) (Y := A) (Z := L) (N := W) hLW hAW hLW h1 le_rfl
  rw [hL, Subgroup.commutator_comm] at h3
  exact h3

omit [Finite G] in
theorem map_conj_mul (A : Subgroup G) (g h : G) :
    A.map (MulAut.conj (g * h)).toMonoidHom =
      (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_normalizer_of_map_conj_le {W : Subgroup G} {g : G}
    (h : W.map (MulAut.conj g).toMonoidHom ≤ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  have hcard : Nat.card W ≤ Nat.card ↥(W.map (MulAut.conj g).toMonoidHom) :=
    (Nat.card_congr (W.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).le
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h hcard)

omit [Finite G] in
theorem eq_bot_of_perfect_of_isPGroup_two [Finite G] {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (h2 : IsPGroup 2 ↥K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have : Group.IsNilpotent ↥K := h2.isNilpotent
  have h1 : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hK)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K).ne h1

theorem blockU_ne_bot {K : Subgroup G} (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) (hchar : CharTwo K) :
    blockU K ≠ ⊥ := by
  intro h
  have hc : K ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    have h' : ⁅pCoreOf 2 K, K⁆ = ⊥ := h
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h'
    exact fun k hk => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (h' hx)) k hk).symm
  have hKO : K ≤ pCoreOf 2 K := (le_inf le_rfl hc).trans hchar
  exact hK1 (eq_bot_of_perfect_of_isPGroup_two hK ((pCoreOf_isPGroup 2 K).to_le hKO))

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem false_of_commutator_conj_le {U : Subgroup G} (hU1 : U ≠ ⊥) (hUS : U ≤ T ⊓ H)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hSU : T ⊓ H ≤ Subgroup.normalizer (U : Set G))
    (hc : ⁅U.map (MulAut.conj t).toMonoidHom, K⁆ ≤ U) : False := by
  set S := T ⊓ H with hS
  set Ut := U.map (MulAut.conj t).toMonoidHom with hUt
  set W := U ⊔ Ut with hW
  have htS : S.map (MulAut.conj t).toMonoidHom = S :=
    map_conj_eq_of_mem_normalizer sk.t_normalizer
  have hUtS : Ut ≤ S := htS ▸ map_conj_mono hUS t
  have hW2 : IsPGroup 2 W :=
    sk.base.hyp.sylow.1.to_le ((_root_.sup_le hUS hUtS).trans inf_le_left)
  have hW1 : W ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ le_sup_left))
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup]
    refine _root_.sup_le ?_ ?_
    · rw [map_conj_eq_of_mem_normalizer (hKU hk)]
      exact le_sup_left
    · rintro _ ⟨y, hy, rfl⟩
      have hyk : ⁅y, k⁆ ∈ U := hc (Subgroup.commutator_mem_commutator hy hk)
      have e : (MulAut.conj k).toMonoidHom y = ⁅y, k⁆⁻¹ * y := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact W.mul_mem (Subgroup.mem_sup_left (U.inv_mem hyk)) (Subgroup.mem_sup_right hy)
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    intro s hs
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hSU hs)]
    refine sup_le_sup_left ?_ U
    have hs' : t⁻¹ * s * t ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ sk.t_normalizer) s).mp hs
      rwa [inv_inv] at this
    have e : s * t = t * (t⁻¹ * s * t) := by group
    rw [hUt, ← map_conj_mul, e, map_conj_mul, map_conj_eq_of_mem_normalizer (hSU hs')]
  have htW : t ∈ Subgroup.normalizer (W : Set G) := by
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup, hUt, ← map_conj_mul, ← pow_two,
      map_conj_eq_of_mem_normalizer (hSU sk.t_sq), sup_comm]
  have hX : L ⊔ (S ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (W : Set G) :=
    _root_.sup_le (sk.L_le_K.trans hKW) (_root_.sup_le hSW (Subgroup.zpowers_le.mpr htW))
  have hN := isUniqueM_normalizer_le sk.lemma_4_3_5 hW1 hW2 hX
  exact sk.not_le (le_inf (le_of_mem_cComp sk.cComp) (hKW.trans hN))

theorem S_le_normalizer : T ⊓ H ≤ Subgroup.normalizer (K : Set G) :=
  (le_inf inf_le_right (inf_le_left.trans sk.base.hyp.T_le)).trans sk.le_normalizer

theorem pCoreOf_K_le_S (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : pCoreOf 2 K ≤ T ⊓ H := by
  have hHK := sk.base.le_normalizer_of_cComp hR hC h37 h38 h39 sk.cComp sk.S_le_normalizer
  have hKH : K ≤ H := le_of_mem_cComp sk.cComp
  refine le_of_normal_of_isSylowTwoOf (sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39)
    ((pCoreOf_le 2 K).trans hKH) ?_ (pCoreOf_isPGroup 2 K)
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K))

theorem not_commutator_conj_blockU_le (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hchar : CharTwo K) :
    ¬ ⁅(blockU K).map (MulAut.conj t).toMonoidHom, K⁆ ≤ pCoreOf 2 K := by
  intro hle
  set S := T ⊓ H with hS
  have hSK := sk.S_le_normalizer
  have hOS := sk.pCoreOf_K_le_S hR hC h37 h38 h39
  have hperf := perfect_of_mem_cComp sk.cComp
  have hU1 : blockU K ≠ ⊥ := blockU_ne_bot hperf (ne_bot_of_mem_cComp sk.cComp) hchar
  have hUO : blockU K ≤ pCoreOf 2 K :=
    commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K)
  have hUS : blockU K ≤ S := hUO.trans hOS
  have hKU : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 K) K
  have hSU : S ≤ Subgroup.normalizer (blockU K : Set G) := fun s hs =>
    mem_normalizer_commutator ((normalizer_le_normalizer_pCoreOf 2 K) (hSK hs)) (hSK hs)
  have htS : S.map (MulAut.conj t).toMonoidHom = S :=
    map_conj_eq_of_mem_normalizer sk.t_normalizer
  have hUtK : (blockU K).map (MulAut.conj t).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    (htS ▸ map_conj_mono hUS t).trans hSK
  refine sk.false_of_commutator_conj_le hU1 hUS hKU hSU ?_
  rw [commutator_eq_commutator_commutator_of_perfect' hperf hUtK]
  exact Subgroup.commutator_mono hle le_rfl

end Setting432K

end CFSG.Quasithin.H13.Ch4
