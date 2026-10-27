module

public import CFSG.Quasithin.Vol2.Ch11SecE42S1e
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple
public import CFSG.Quasithin.Vol2.Ch11SecA15Q
public import CFSG.Quasithin.Vol2.Ch11SecE42S1d

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem nonempty_autOn_fsuV_equiv {T Kp I : Subgroup G} (hfsu : FSU G T Kp I)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G)) (hs : IsSimpleGroup (↥Kp ⧸ CFSG.pCore 2 ↥Kp))
    (hKV : Kp ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    Nonempty (↥(autOn Kp (fsuV T I)) ≃* ↥Kp ⧸ CFSG.pCore 2 ↥Kp) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL0 : conjClosure Kp T = Kp := conjClosure_eq_self hTKp
  have hVR : fsuV T I ≤ reducedAggregate (Kp ⊔ T) := by
    have hN := (SecA.reducedAggregate_props (Kp ⊔ T)).2.2.2
    refine conjClosure_le fun t ht x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) x).mp
      (hfsu.irrPlus.1 hx)
  have hOKM : pCoreOf 2 Kp ≤ pCoreOf 2 (Kp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Kp).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hTKp).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Kp))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kp)
  have hVC : fsuV T I ≤ Subgroup.centralizer (pCoreOf 2 Kp : Set G) :=
    (hVR.trans (SecA.reducedAggregate_le_centralizer _)).trans (Subgroup.centralizer_le hOKM)
  have hO : pCoreOf 2 Kp ≤ Subgroup.centralizer (fsuV T I : Set G) :=
    Subgroup.le_centralizer_iff.mp hVC
  have hne : ¬ Kp ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    intro hle
    have h1 := hfsu.irrPlus.2.2.2.1
    rw [hL0] at h1
    have h2 : ⁅I, Kp⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (hle.trans (Subgroup.centralizer_le (le_conjClosure I T))))
    exact hfsu.irrPlus.2.1 (h1.symm.trans h2)
  exact nonempty_autOn_equiv hs hKV hO hne

theorem list701Excl_of_ff (h328 : Stmt3_2_8) {T Kp I : Subgroup G} (hfsu : FSU G T Kp I)
    (hTKp : T ≤ Subgroup.normalizer (Kp : Set G)) [hcomm : IsMulCommutative ↥(fsuV T I)]
    (hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G)) (hI : I = conjClosure I T)
    {A : Subgroup (MulAut ↥(fsuV T I))}
    (hA : IsFFStarOffender (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn Kp (fsuV T I) : Set (MulAut ↥(fsuV T I)))) A)
    (hne1 : autOn Kp (fsuV T I) ≠ ⊥) : List701Excl ↥(autOn Kp (fsuV T I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL0 : conjClosure Kp T = Kp := conjClosure_eq_self hTKp
  have hfsu' : FSU G T Kp (conjClosure I T) := by
    rw [← hI]
    exact hfsu
  have hVc : conjClosure I T = conjClosure (conjClosure I T) T := (conjClosure_eq_self hTV).symm
  have hKpT : Kp ⊔ T ≤ Subgroup.normalizer (Kp : Set G) := sup_le Subgroup.le_normalizer hTKp
  obtain ⟨_, h8⟩ := h328 G T Kp (conjClosure I T) hfsu' hL0.symm hVc
    ⟨hcomm, isFFModule_of_offender hA⟩
  rcases h8 with ⟨m, hm, -⟩ | (⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩) |
      ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | (⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩) | ⟨⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨hp, hc, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
  · exact List701Excl.psl2 hm
  · exact List701Excl.sl3 hK e
  · exact List701Excl.sl3two e
  · exact List701Excl.sp4 hK e
  · exact List701Excl.g2 hK e
  · exact List701Excl.a5 e
  · exact List701Excl.a7 e
  · exact List701Excl.a6 e
  · have := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
    obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup le_sup_left hKpT e hne1
    exact List701Excl.a7 e'
  · exact List701Excl.threeA6 hp hc e
  · rcases hm with rfl | rfl
    · have := SecA.isSimpleGroup_SL_zmod_two (n := 4) (by norm_num)
      obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup le_sup_left hKpT e hne1
      exact List701Excl.sl4 e'
    · have := SecA.isSimpleGroup_SL_zmod_two (n := 5) (by norm_num)
      obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup le_sup_left hKpT e hne1
      exact List701Excl.sl5 e'
  · exact List701Excl.sl4 e
  · have := SecA.isSimpleGroup_SL_zmod_two (n := 5) (by norm_num)
    obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup le_sup_left hKpT e hne1
    exact List701Excl.sl5 e'

theorem false_of_fsu_sporadic (hF : Facts42S1) (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (h701 : Stmt7_0_1) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) {T Kp I : Subgroup G}
    (hfsu : FSU G T Kp I) (hTKp : T ≤ Subgroup.normalizer (Kp : Set G))
    (hX : IsSporadic .M23 (↥Kp ⧸ CFSG.pCore 2 ↥Kp) ∨ IsSporadic .J4 (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) :
    False := by
  have hL0 : fsuL0 T Kp = Kp := conjClosure_eq_self hTKp
  have hL0' : conjClosure Kp T = Kp := hL0
  have hs := (hF.m23j4 _ hX).1
  obtain ⟨hcomm, -, hNV, hcases⟩ := h701 G T Kp I hfsu
  rw [hL0] at hNV
  have hKV : Kp ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hNV
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hNV
  obtain ⟨e⟩ := nonempty_autOn_fsuV_equiv hfsu hTKp hs hKV
  have hY : IsSporadic .M23 ↥(autOn Kp (fsuV T I)) ∨ IsSporadic .J4 ↥(autOn Kp (fsuV T I)) := by
    rcases hX with hX | hX
    · exact Or.inl (Nonempty.intro (e.trans (Nonempty.some hX)))
    · exact Or.inr (Nonempty.intro (e.trans (Nonempty.some hX)))
  obtain ⟨hsY, hnot⟩ := hF.m23j4 _ hY
  have hne1 : autOn Kp (fsuV T I) ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  apply hnot
  rcases hcases with hFF | hJ | hO | h4
  · obtain ⟨A, hA⟩ := hFF
    rw [hL0] at hA
    obtain ⟨-, -, h3⟩ := h325 G T Kp I hfsu hL0'.symm
    rcases h3 with ⟨hI, -⟩ | ⟨hI, -⟩ | ⟨-, hlist, -⟩
    · exact list701Excl_of_ff h328 hfsu hTKp hTV hI hA hne1
    · exact list701Excl_of_ff h328 hfsu hTKp hTV hI hA hne1
    · rcases hlist with ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨m, K, _, _, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact List701Excl.sl3 hK e
      · exact List701Excl.sp4 hK e
      · exact List701Excl.a6 e
      · exact List701Excl.sl4 e
      · exact List701Excl.sl5 e
      · exact List701Excl.a7 e
  · obtain ⟨-, -, -, -, ⟨π, hπs, -⟩, -⟩ := hJ
    have hKH : Kp ≤ fsuM T Kp := by
      show Kp ≤ Subgroup.normalizer (fsuL0 T Kp : Set G)
      rw [hL0]
      exact Subgroup.le_normalizer
    have hHK : fsuM T Kp ≤ Subgroup.normalizer (Kp : Set G) := by
      show Subgroup.normalizer (fsuL0 T Kp : Set G) ≤ _
      rw [hL0]
    let π' : ↥NativeSporadic.M24 →* ↥(autOn (fsuM T Kp) (fsuV T I)) := π
    have hπi : Function.Injective π' := by
      rcases hM24.eq_bot_or_eq_top_of_normal π'.ker with h0 | h0
      · exact (MonoidHom.ker_eq_bot_iff π').mp h0
      · exfalso
        apply hne1
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨y, hy⟩ := hπs ⟨x, InternalSec.autOn_le_autOn_of_le hKH hx⟩
        have h1 : π' y = 1 := (MonoidHom.mem_ker).mp (h0 ▸ Subgroup.mem_top y)
        have h2 : π y = 1 := h1
        rw [h2] at hy
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy).symm
    let f : ↥NativeSporadic.M24 ≃* ↥(autOn (fsuM T Kp) (fsuV T I)) :=
      MulEquiv.ofBijective π' ⟨hπi, hπs⟩
    obtain ⟨e'⟩ := nonempty_autOn_equiv_of_sup hKH hHK f.symm hne1
    exact List701Excl.m24 e'
  · obtain ⟨n, -, K, _, _, _, hK, π, hπs, -⟩ := hO
    have heq : autOn (fsuL0 T Kp) (fsuV T I) = autOn Kp (fsuV T I) := by rw [hL0]
    exact List701Excl.sl2 hK ((MulEquiv.subgroupCongr heq).toMonoidHom.comp π)
      ((MulEquiv.subgroupCongr heq).surjective.comp hπs)
  · have h41 := h4.1
    rw [hL0] at h41
    exact absurd h41 (lt_irrefl _)

end CFSG.Quasithin.Vol2.Ch11.SecE
