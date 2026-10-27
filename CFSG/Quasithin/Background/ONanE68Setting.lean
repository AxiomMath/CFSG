module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.Background.E6Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique

section Helpers

variable {G : Type} [Group G]

theorem two_dvd_card_of_quasisimple [Finite G] {L : Subgroup G} (hL : CFSG.IsQuasisimple ↥L) :
    2 ∣ Nat.card L := by
  by_contra h
  have hodd : Odd (Nat.card L) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have hsol : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL
  have : Group.IsPerfect ↥L := hL.1
  exact Group.IsPerfect.not_isSolvable ↥L hsol

theorem isComponentIn_conjugate_of_mem {K H : Subgroup G} (hK : IsComponentIn K H) {g : G}
    (hg : g ∈ H) : IsComponentIn (CFSG.conjugate K g) H := by
  have h := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hK
  have hH : H.map (MulAut.conj g⁻¹).toMonoidHom = H := by
    ext x
    rw [mem_map_conj_inv_iff]
    exact ⟨fun hx => by simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg,
      fun hx => H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)⟩
  rw [hH] at h
  exact h

theorem mem_normalizer_of_centralizes_sylow [Finite G] {H Q L : Subgroup G}
    (hQ : IsSylowTwoOf Q H) (hL : IsComponentIn L H) {v : G} (hvH : v ∈ H)
    (hv : ∀ q ∈ Q, v * q = q * v) : v ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnorm
  have hL' : IsComponentIn (CFSG.conjugate L v) H := isComponentIn_conjugate_of_mem hL hvH
  have hne : L ≠ CFSG.conjugate L v := fun h =>
    hnorm (BenderBranch.conjugate_eq_iff_mem_normalizer.1 h.symm)
  have hcomm : ⁅L, CFSG.conjugate L v⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left hne
  have hP : IsSylowTwoOf (Q ⊓ L) L := RankOneRecog.isSylowTwoOf_inf_of_subnormal hQ hL.1 hL.2.2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hP2 : IsPGroup 2 ((Q ⊓ L).subgroupOf L) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  let T : Sylow 2 ↥L := hP2.toSylow hP.2.2
  have hTZ : (T : Subgroup ↥L) ≤ Subgroup.center ↥L := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    have htP : (t : G) ∈ Q ⊓ L := ht
    have htc : (t : G) ∈ CFSG.conjugate L v := by
      have hvt : v * (t : G) * v⁻¹ = t := by rw [hv _ htP.1, mul_inv_cancel_right]
      rw [BenderBranch.mem_conjugate_iff, hvt]
      exact htP.2
    have hLc : L ≤ Subgroup.centralizer ((CFSG.conjugate L v : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLc g.2) t htc).symm
  have : Group.IsPerfect ↥L := hq.1
  have hT1 := sylow_eq_bot_of_le_center T hTZ
  have hidx : (T : Subgroup ↥L).index = Nat.card L := by rw [hT1, Subgroup.index_bot]
  exact T.not_dvd_index (by rw [hidx]; exact two_dvd_card_of_quasisimple hq)

theorem twoPrimeResidual_mono [Finite G] {A B : Subgroup G} (hAB : A ≤ B) :
    twoPrimeResidual A ≤ twoPrimeResidual B := by
  obtain ⟨TA, hTA⟩ := exists_isSylowTwoOf A
  obtain ⟨TB, hTATB, hTB⟩ := exists_isSylowTwoOf_of_le (hTA.1.trans hAB) hTA.2.1
  rw [← conjClosure_eq_twoPrimeResidual hTA, ← conjClosure_eq_twoPrimeResidual hTB]
  exact conjClosure_le fun h hh z hz => mem_conjClosure (hAB hh) (hTATB hz)

end Helpers

section Setting

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem not_le_of_component (h : HypE61 T M V) (hUV : U ≤ V)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) : ¬ L ≤ M := fun hLM =>
  DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) L
    (BenderBranch.isComponentIn_of_le hL (le_inf hLM hL.1) inf_le_right)

theorem le_normalizer_of_component (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    V ≤ Subgroup.normalizer (L : Set G) := by
  intro v hv
  have hVQ : V ≤ T ⊓ Subgroup.centralizer (V : Set G) := h.le_inf_centralizer
  have hQH := e6_5_one h hU
  exact mem_normalizer_of_centralizes_sylow hQH hL (hQH.1 (hVQ hv)) fun q hq =>
    Subgroup.mem_centralizer_iff.1 hq.2 v hv

theorem exists_mem_V_inf_center (h : HypE61 T M V) :
    ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
  have hT2 : IsPGroup 2 T := h.sylow.1
  have : Group.IsNilpotent T := hT2.isNilpotent
  have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h.normal
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h0
    apply h.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, ⟨y.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)⟩, fun h1 => hy1 ?_⟩
  exact Subtype.ext (Subtype.ext h1)

theorem lemma115Hyp_of_gamma (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) {z : G} (hzV : z ∈ V)
    (hzT : z ∈ T ⊓ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    Lemma115Hyp (Subgroup.centralizer (U : Set G)) (T ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer ({z} : Set G)) z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hUV : U ≤ V := hU.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz : Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    ext g
    constructor
    · intro hg
      have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      have hgZ : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, rfl⟩
        exact ((Commute.zpow_left hgz.symm k).symm).eq.symm
      exact ⟨Subgroup.centralizer_le_normalizer _ hgZ, hgZ⟩
    · rintro ⟨-, hg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg z (Subgroup.mem_zpowers z)).symm
  have hTsyl : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZT : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_zpowers z, hzT⟩
    rw [h0] at this
    exact this
  have hNz := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hTsyl hZ2 hZT
  have hCz2 : CharTwo (Subgroup.centralizer ({z} : Set G)) := by
    rw [hCz]
    exact CT.CharTwo.inf_centralizer hNz Subgroup.le_normalizer hZ2
  have hzQ : z ∈ Q := hVQ hzV
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hUz : U ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine C1.le_pCoreOf_of_normalized (le_inf (fun u hu => ?_) (fun u hu => ?_)) (fun g hg => ?_)
      (h.isPGroup_V.to_le hUV)
    · exact Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hVc _ (hUV hu) _ hzV)
    · exact Subgroup.centralizer_le_normalizer _ hg.1
  exact
    { pCore_ne_bot := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸ (C1.le_pCoreOf_of_normalized
        (fun u hu => Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu))
        (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hUV))))
      sylow := hQH
      charTwo := hCz2
      pCore_M_ne_bot := fun h0 => hz1 (by
        have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
          C1.le_pCoreOf_of_normalized (Subgroup.zpowers_le.2 hzC) (by
            rw [hCz]; exact inf_le_left) hZ2
        have := hle (Subgroup.mem_zpowers z)
        rw [h0] at this
        exact this)
      le := fun q hq => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      centralizer_le := fun g hg => Subgroup.centralizer_le hUz hg.2
      centralizer_z_le := le_rfl
      z_ne_one := hz1
      z_mem := hzQ
      z_central := Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      z_sq := hz2 }

theorem setting (hlist : Lemma115_3_List) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    ¬ L ≤ M ∧ V ≤ Subgroup.normalizer (L : Set G) ∧
      IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L ∧
      ∃ z : G, z ∈ V ∧ z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 ∧
        Lemma115Cases L z := by
  have := h.simple
  obtain ⟨z, hzV, hzT, hz1⟩ := exists_mem_V_inf_center h
  have h115 := lemma115Hyp_of_gamma h hU hzV hzT hz1
  obtain ⟨-, -, -, hcases⟩ := Lemma115_3_List.component_cases hlist h.simple h.nonabelian
    (qtkeCore_of_cat h.nonabelian h.qtke) h115 hL
  exact ⟨not_le_of_component h hU.1 hL, le_normalizer_of_component h hU hL,
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2, z, hzV, hzT, hz1,
    hcases⟩

omit [Finite G] in
theorem le_inf_centralizer_component (hUV : U ≤ V)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    U ≤ V ⊓ Subgroup.centralizer (L : Set G) :=
  le_inf hUV fun u hu => Subgroup.mem_centralizer_iff.2 fun _ hl =>
    (Subgroup.mem_centralizer_iff.1 (hL.1 hl) u hu).symm

omit [Finite G] in
theorem le_centralizer_inf_centralizer (V L : Subgroup G) :
    L ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun l hl => Subgroup.mem_centralizer_iff.2 fun _ hu =>
    (Subgroup.mem_centralizer_iff.1 hu.2 l hl).symm

theorem eq_inf_centralizer_of_hypOrMax (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (hHM : E68HypOrMax M V U) :
    U = V ⊓ Subgroup.centralizer (L : Set G) := by
  have hUU := le_inf_centralizer_component hU.1 hL
  have hLle := le_centralizer_inf_centralizer V L
  have hLM := not_le_of_component h hU.1 hL
  by_contra hne
  rcases hHM with hm1 | hmax
  · have hV2 : IsPGroup 2 V := h.isPGroup_V
    have hU₁2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer (L : Set G)) := hV2.to_le inf_le_left
    have hpos : E3.mQuot (V ⊓ Subgroup.centralizer (L : Set G)) U ≠ 0 := fun h0 =>
      hne ((E3.mQuot_eq_zero_iff hU₁2 hUU).1 h0)
    have hadd := E3.mQuot_add hUU (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V)
    have h0 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 0 := by omega
    have hVeq := (E3.mQuot_eq_zero_iff hV2 inf_le_left).1 h0
    apply hLM
    refine hLle.trans ?_
    rw [hVeq]
    exact h.centralizer_le
  · exact hLM (hLle.trans (hmax _ (lt_of_le_of_ne hUU hne) inf_le_left))

end Setting

end E68Proof

end E6

end CFSG.Quasithin
