module

public import CFSG.Quasithin.Vol2.Ch10SecKRTj
public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.Quasithin.Vol2.Ch10SecKIK2f
public import CFSG.Quasithin.Vol2.Ch10SecKRTc

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem oddCore_map_mulEquiv' {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact A312.odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact A312.odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem isSL2_top {Y : Type} [Group Y] [Finite Y] {p : ℕ} (h : IsSL2 p (Y ⧸ CFSG.oddCore Y)) :
    IsSL2 p (↥(⊤ : Subgroup Y) ⧸ CFSG.oddCore ↥(⊤ : Subgroup Y)) := by
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.congr _ _ Subgroup.topEquiv (oddCore_map_mulEquiv' _)).trans e⟩

theorem five_le {p : ℕ} (hp : p.Prime) (hp5 : p ^ 2 % 5 = 1) (hp8 : p % 8 = 3 ∨ p % 8 = 5) :
    5 ≤ p := by
  by_contra h
  push Not at h
  interval_cases p <;> simp_all (config := { decide := true })

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

theorem false_of_22 (h56 : AsB56) (h1022 : Stmt10_2_2) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) {p : ℕ} (hp : p.Prime) (hp5 : p ^ 2 % 5 = 1)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hpSL : IsSL2 p (↥(modO2Image M₁ J) ⧸ CFSG.oddCore ↥(modO2Image M₁ J))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp5' := five_le hp hp5 hp8
  set H₀ := J ⊔ T with hH₀def
  have hH₀ : H₀ ≤ M₁ := sup_le (J_le cfg) (T_le cfg)
  have hJH₀ : H₀ ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTJ
  have hKT : conjClosure K T ≤ J := conjClosure_le fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTJ ht) k).mp (cfg.hKJ hk)
  have ff := ffSet h1022 cfg le_sup_right hH₀ (H_le_of cfg le_sup_right (hKT.trans le_sup_left))
  set V := conjClosure (quasithinOmegaOneCenter T) H₀ with hVdef
  have hel : IsElemAbelian 2 V := ff.elem
  have : IsMulCommutative ↥V := hel.1
  have hH₀V : H₀ ≤ Subgroup.normalizer (V : Set G) := ff.red.2.1
  have hJV : J ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hH₀V
  have hO := SecC.C10KH.pCoreOf_le_centralizer ff.red le_sup_left hJH₀
  have hnt : ¬ J ≤ Subgroup.centralizer (V : Set G) := fun h => ff.K_not (cfg.hKJ.trans h)
  obtain ⟨π₀, hπ⟩ := exists_pi cfg hel hJV hO
  set Js := autOn J V with hJs
  let π : ↥(modO2Image M₁ J) →* ↥Js := π₀
  set X := autOn H₀ V with hX
  have hJJ : Js ≤ ffJ X :=
    (InternalSec.autOn_le_autOn_of_le (le_thompsonJ h1022 cfg hTJ hp hp5' hpSL)).trans
      (SBc3.autOn_thompsonJ_le_ffJ hel ff.red.1 hH₀V)
  have hJn' : ∀ x ∈ X, ∀ k ∈ Js, x * k * x⁻¹ ∈ Js := InternalSec.autOn_normal_of (U := V) hJH₀
  have hJn : (Js.subgroupOf (ffJ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff hJJ).mpr fun k y hk hy => hJn' y (B6.ffJ_le X hy) k hk
  have hperf : ⁅Js, Js⁆ = Js := by
    rw [hJs, ← S153D.autOn_commutator hJV hJV, perfect_of_mem_cComp cfg.hJ]
  obtain ⟨x, hx⟩ := exists_ne_one_autI hel hJV hnt
  have hJns : ¬ Group.IsSolvable ↥Js := by
    intro hs
    have hb : perfectCore Js = ⊥ := (isSolvable_iff_perfectCore_eq_bot Js).mp hs
    rw [perfectCore_eq_self_of_perfect hperf] at hb
    exact hx (Subtype.ext (Subgroup.mem_bot.mp (hb ▸ x.2)))
  obtain ⟨K₀, hK₀, hK₀J⟩ := exists_cComp_le_of_not_solvable hJJ hJn hJns
  have hK₀ne : K₀ ≠ ⊥ := ne_bot_of_mem_cComp hK₀
  have hK₀s := not_isSolvable_of_mem_cComp hK₀
  have hO2 : pCoreOf 2 X = ⊥ := CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot ff.red
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hel.2 v v.2)
  have hJne : ffJ X ≠ ⊥ := fun h => hK₀ne (le_bot_iff.mp ((le_of_mem_cComp hK₀).trans h.le))
  have hcases := h56 ↥V hV2 (ffJ X) hJne (InternalSec.b53Hyp_ffJ_autOn hH₀V ff.sqtk hO2)
  obtain ⟨hK₀q, hK₀l, hK₀n⟩ : CFSG.IsQuasisimple ↥K₀ ∧ B56QuasisimpleList ↥K₀ ∧
      ∀ y ∈ ffJ X, ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀ := by
    rcases S153L.b56_components hcases with ⟨h6, -⟩ | ⟨G₁, G₂, hsup, -, hc, ⟨h6₁, -⟩, ⟨h6₂, -⟩⟩ |
        ⟨N₁, N₂, -, -, -, hn₁, hn₂, hq₁, hq₂, hK⟩
    · exfalso
      have : Group.IsSolvable ↥(ffJ X) := S153L.comp_solvable_of_card_six h6
      exact hK₀s (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hK₀)) (Subgroup.inclusion_injective _))
    · exfalso
      have h1 := (S153L.factorN_of_solvable (S153L.comp_solvable_of_card_six h6₁)).2.2.2
      have h2 := (S153L.factorN_of_solvable (S153L.comp_solvable_of_card_six h6₂)).2.2.2
      have hle := S153L.perfect_le_sup_of_commute hc h1 h2
        (hsup ▸ le_of_mem_cComp hK₀) (perfect_of_mem_cComp hK₀)
      rw [sup_bot_eq] at hle
      exact hK₀ne (le_bot_iff.mp hle)
    · rcases hK K₀ hK₀ with rfl | rfl
      · rcases hq₁ with h | h
        · exact absurd h hK₀ne
        · exact ⟨h.1, h.2, hn₁⟩
      · rcases hq₂ with h | h
        · exact absurd h hK₀ne
        · exact ⟨h.1, h.2, hn₂⟩
  have hKn : (K₀.subgroupOf Js).Normal :=
    (Subgroup.normal_subgroupOf_iff hK₀J).mpr fun k y hk hy => hK₀n y (hJJ hy) k hk
  set Np := (K₀.subgroupOf Js).comap π with hNp
  have hNpn : Np.Normal := hKn.comap π
  have hNps : ¬ Group.IsSolvable ↥Np := by
    intro hs
    have hmap : Np.map π = K₀.subgroupOf Js := Subgroup.map_comap_eq_self_of_surjective hπ _
    have h1 : Group.IsSolvable ↥(Np.map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective Np)
    rw [hmap] at h1
    exact hK₀s (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hK₀J).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK₀J).symm.injective)
  have htop := eq_top_of_not_isSolvable
    (isPerfect_of_commutator_eq (perfect_of_mem_cComp (Jbar_mem_cComp cfg))) hp hp5' hpSL hNpn
    hNps
  have heq : Js = K₀ := by
    refine le_antisymm (fun y hy => ?_) hK₀J
    obtain ⟨z, hz⟩ : ∃ z, π z = ⟨y, hy⟩ := hπ ⟨y, hy⟩
    have hzN : z ∈ Np := htop ▸ Subgroup.mem_top z
    have := Subgroup.mem_comap.mp hzN
    rw [hz] at this
    exact this
  have hJq : CFSG.IsQuasisimple ↥Js := heq ▸ hK₀q
  have hJl : B56QuasisimpleList ↥Js := heq ▸ hK₀l
  exact SecC.C10KH.false_of_sl2_quot π hπ hJq hJl hp hp8 hp5 (isSL2_top hpSL)

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
