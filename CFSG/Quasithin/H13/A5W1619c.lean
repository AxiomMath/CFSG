module

public import CFSG.Quasithin.H13.A5W1619b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

local notation "StSL" => Assembly.LowTwoRank.StatedSL

local notation "StSp" => Assembly.LowTwoRank.StatedSp

theorem map_subtype_maximal {Γ : Type*} [Group Γ] {X : Subgroup Γ} {P : Subgroup ↥X}
    (hP : P ⋖ ⊤) : P.map X.subtype < X ∧
      ∀ M' : Subgroup Γ, P.map X.subtype ≤ M' → M' < X → M' = P.map X.subtype := by
  refine ⟨lt_of_le_of_ne (Subgroup.map_subtype_le P) fun h => hP.lt.ne ?_,
    fun M' hPM hMX => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : (x : Γ) ∈ P.map X.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have e : y = x := Subtype.ext hyx
    exact e ▸ hy
  · have hle : P ≤ M'.subgroupOf X := fun x hx => by
      rw [Subgroup.mem_subgroupOf]
      exact hPM ⟨x, hx, rfl⟩
    have hne : M'.subgroupOf X ≠ ⊤ := by
      intro h
      refine hMX.ne (le_antisymm hMX.le fun x hx => ?_)
      have : (⟨x, hx⟩ : ↥X) ∈ M'.subgroupOf X := h ▸ Subgroup.mem_top _
      exact this
    have heq : P = M'.subgroupOf X := by
      by_contra hne'
      exact hP.2 (lt_of_le_of_ne hle hne') (lt_top_iff_ne_top.mpr hne)
    rw [heq, Subgroup.map_subgroupOf_eq_of_le hMX.le]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_levi_of_rank2
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h56 : AsB56)
    (hng : FactNoGraphTwist) (hH : S.Hyp1367) {K : Subgroup G} [IsMulCommutative ↥(S.WK K)]
    (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hn : 2 ≤ n) (hFn : Nat.card F = 2 ^ n)
    (hY : Nonempty (↥(S.plus K) ≃* ↥(StSL 3 F)) ∨ Nonempty (↥(S.plus K) ≃* ↥(StSp 2 F)) ∨
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Open.quasithinG2 F))) :
    ∃ L' : Subgroup (MulAut ↥(S.WK K)), L' ≤ S.plus K ∧ ⁅L', L'⁆ = L' ∧
      (∃ (K' : Type) (_ : Field K') (_ : Finite K') (m : ℕ), Nat.card K' = 2 ^ m ∧ 2 ≤ m ∧
        ∃ g : ↥L' →* Matrix.SpecialLinearGroup (Fin 2) K', Function.Surjective g ∧
          IsPGroup 2 g.ker) ∧
      CharTwo L' ∧ ¬ Group.IsSolvable ↥L' ∧
      autOn S.Tv (S.WK K) ≤ Subgroup.normalizer (L' : Set (MulAut ↥(S.WK K))) ∧
      ∃ a ∈ L', ∃ w : ↥(S.WK K), (w : G) = S.z ∧ a w ≠ w := by
  classical
  have hF' := hH.hF
  have hq := S.isQuasisimple_plus h1222 h517 hF' hK hT
  have hR := S.isTwoReducedIn_WK h1222 h517 hF' hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hKHK.trans hHKW
  have hNH := S.HK_le_normalizer_plus h1222 h517 hF' hK hT
  have hTvHK : IsSylowTwoOf (autOn S.Tv (S.WK K)) (autOn (S.HK K) (S.WK K)) :=
    Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_HK h1222 h517 hK.1) hHKW
  have hQsyl : IsSylowTwoOf (autOn S.Tv (S.WK K) ⊓ S.plus K) (S.plus K) :=
    A4.isSylowTwoOf_inf_normal hTvHK (A4.autOn_mono hKHK) hNH
  have hWT := (S.WK_le_Tv h1222 h517 hF' hK.1 hT).1
  have hSQ := S.sqtkGroup_HK h1222 h517 hF' hK.1 hT
  have hKJ := S.plus_le_jStar h1222 h517 hF' hK hT
  have hJne : autOn (thompsonJ S.Tv) (S.WK K) ≠ ⊥ := by
    intro h
    have h1 := S.plus_eq_commutator h1222 h517 hF' hK hT
    rw [h, Subgroup.commutator_bot_right] at h1
    exact (qs_perfect_ne_bot hq).2 h1.symm
  have hcases := b56Cases_jStar h56 hWT (S.Tv_le_HK K) hR hSQ hJne
  have hb := b53Hyp_jStar hWT (S.Tv_le_HK K) hR hSQ
  have hNn : ∀ x ∈ jStar (S.HK K) S.Tv (S.WK K), ∀ m ∈ S.plus K, x * m * x⁻¹ ∈ S.plus K :=
    fun x hx m hm => (Subgroup.mem_normalizer_iff.mp (hNH (jStar_le (S.Tv_le_HK K) hx)) m).mp hm
  have hV2 : ∀ v : ↥(S.WK K), v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hR.2.2.1.2 _ v.2, Subgroup.coe_one])
  have hTJ : autOn S.Tv (S.WK K) ≤ Subgroup.normalizer
      ((jStar (S.HK K) S.Tv (S.WK K) : Subgroup (MulAut ↥(S.WK K))) : Set (MulAut ↥(S.WK K))) :=
    (A4.autOn_mono (S.Tv_le_HK K)).trans le_normalizer_jStar
  have hTX : autOn S.Tv (S.WK K) ≤ Subgroup.normalizer
      ((S.plus K : Subgroup (MulAut ↥(S.WK K))) : Set (MulAut ↥(S.WK K))) :=
    (A4.autOn_mono (S.Tv_le_HK K)).trans hNH
  have hTQ : autOn S.Tv (S.WK K) ≤ Subgroup.normalizer
      ((autOn S.Tv (S.WK K) ⊓ S.plus K : Subgroup (MulAut ↥(S.WK K))) :
        Set (MulAut ↥(S.WK K))) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTX ht⟩
  set X := S.plus K with hXdef
  set Q := autOn S.Tv (S.WK K) ⊓ X with hQdef
  obtain ⟨P, hP⟩ := exists_rank2Pkg hn hFn hY (Setup.Layer.isSylowTwoOf_subgroupOf_top' hQsyl)
  have hQP : ∀ j, Q ≤ (P j).map X.subtype := fun j q hq =>
    ⟨⟨q, hq.2⟩, hP.le j (by rw [Subgroup.mem_subgroupOf]; exact hq), rfl⟩
  have hTP : ∀ j, autOn S.Tv (S.WK K) ≤ Subgroup.normalizer
      (((perfectCore (P j)).map X.subtype : Subgroup (MulAut ↥(S.WK K))) :
        Set (MulAut ↥(S.WK K))) := by
    intro j t ht
    obtain ⟨hMX, hmax⟩ := map_subtype_maximal (hP.covBy j)
    have h1 := hng (↥(S.WK K)) hV2 _ X hb hcases hKJ hNn hq F n hn hFn hY Q _ hQsyl (hQP j) hMX
      hmax t (hTJ ht) (hTX ht) (hTQ ht)
    have h2 : ((perfectCore (P j)).map X.subtype).map (MulAut.conj t).toMonoidHom =
        (perfectCore (P j)).map X.subtype := by
      rw [map_perfectCore X.subtype (P j),
        map_perfectCore (MulAut.conj t).toMonoidHom ((P j).map X.subtype), h1]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  set zW : ↥(S.WK K) := ⟨S.z, hzW⟩ with hzWdef
  obtain ⟨j, a, ha, haz⟩ : ∃ j, ∃ a ∈ (perfectCore (P j)).map X.subtype, a zW ≠ zW := by
    by_contra hcon
    push Not at hcon
    set St : Subgroup ↥X := (MulAction.stabilizer (MulAut ↥(S.WK K)) zW).subgroupOf X with hSt
    have hle : perfectCore (P 0) ⊔ perfectCore (P 1) ⊔ Q.subgroupOf X ≤ St := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        rw [hSt, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hcon 0 x ⟨x, hx, rfl⟩
      · intro x hx
        rw [hSt, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hcon 1 x ⟨x, hx, rfl⟩
      · intro x hx
        rw [hSt, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        rw [Subgroup.mem_subgroupOf] at hx
        obtain ⟨⟨t, htN⟩, ht, hte⟩ := Setup.mem_autOn_iff.1 hx.1
        rw [← hte]
        apply Subtype.ext
        rw [InternalSec.coe_conjAct_apply]
        exact S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    rw [hP.sup_perfectCore_eq_top] at hle
    apply S.not_le_centralizer_z_of_inYz hK hT
    intro k hk
    have hkX : conjAct (S.WK K) ⟨k, hKW hk⟩ ∈ X := Setup.mem_autOn_iff.2 ⟨⟨k, hKW hk⟩, hk, rfl⟩
    have h1 := hle (Subgroup.mem_top ⟨_, hkX⟩)
    rw [hSt, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1
    have h2 := congrArg Subtype.val h1
    rw [InternalSec.coe_conjAct_apply] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * S.z = k * S.z * k⁻¹ * k := by group
      _ = S.z * k := by rw [h2]
  obtain ⟨K', hKf, hKfin, hKch, m, hK'm, hm, g, hg, hgk⟩ := hP.levi j
  let eL : ↥(perfectCore (P j)) ≃* ↥((perfectCore (P j)).map X.subtype) :=
    (perfectCore (P j)).equivMapOfInjective X.subtype X.subtype_injective
  refine ⟨(perfectCore (P j)).map X.subtype, Subgroup.map_subtype_le _, ?_,
    ⟨K', hKf, hKfin, m, hK'm, hm, g.comp eL.symm.toMonoidHom, hg.comp eL.symm.surjective, ?_⟩,
    Rk2.charTwo_of_equiv eL (hP.charTwo j), ?_, hTP j, a, ha, zW, rfl, haz⟩
  · rw [← Subgroup.map_commutator, perfectCore_perfect]
  · intro x
    have hx : (eL.symm x.1 : ↥(perfectCore (P j))) ∈ g.ker := x.2
    obtain ⟨k, hk⟩ := hgk ⟨eL.symm x.1, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (eL.symm x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : eL.symm (x.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact eL.symm.injective (h2.trans (map_one eL.symm).symm)
  · intro hs
    exact hP.not_isSolvable_perfectCore j (Group.isSolvable_of_isSolvable_injective
      (f := eL.toMonoidHom) eL.injective)

end Setting

end CFSG.Quasithin.H13.A5
