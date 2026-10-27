module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU
public import CFSG.Quasithin.Background.E3MParamTI
public import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpEqMul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Quasithin (conjSubgroup card_eq_two_pow_of_isPGroup rk)
open CFSG.Quasithin.E3 (pRank_le_rk le_wClos_of_mQuot_le le_wClos_of_mQuot_le_self
  le_mParam_of_tiFamily lt_sParam_of_lt normalizer_le_normalizer_wClos wClos cClos wClos_le
  wClos_mono wClos_le_of_forall le_wClos mQuot rParam sParam mParam)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_ne_bot_of_mQuot_le_one {U Y V : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V)
    (hYV : Y ≤ V) (hU : mQuot V U ≤ 1) (hY : 2 < Nat.card Y) : U ⊓ Y ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card Y = U.relIndex Y := by
    rw [← Subgroup.inf_relIndex_right (H := U) (K := Y), hbot, Subgroup.relIndex_bot_left]
  have hle : U.relIndex Y ≤ U.relIndex V :=
    Subgroup.relIndex_le_of_le_right hYV (CFSG.Quasithin.E3.relIndex_ne_zero' V U)
  have hidx : U.relIndex V = 2 ^ mQuot V U := CFSG.Quasithin.E3.relIndex_eq_two_pow hV U
  have hpow : 2 ^ mQuot V U ≤ 2 := by
    calc 2 ^ mQuot V U ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hU
      _ = 2 := by norm_num
  omega

theorem normalizer_wClos_one_le_zero {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hrk : 1 < rk ↥V) (T : Subgroup G) :
    Subgroup.normalizer (wClos V 1 T : Set G) ≤
      Subgroup.normalizer (wClos V 0 T : Set G) := by
  have heq : wClos V 0 T = wClos V 0 (wClos V 1 T) := by
    refine le_antisymm ?_ (wClos_mono (wClos_le 1 T))
    refine wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hAm⟩ := hA
    have hAW : A ≤ wClos V 1 T :=
      le_wClos_of_mQuot_le hV g hAT hAg (by rw [hAm]; exact Nat.zero_le 1) hrk
    exact le_wClos ⟨hAW, g, hAg, hAm⟩
  rw [heq]
  exact normalizer_le_normalizer_wClos (V := V) (i := 0) (wClos V 1 T)

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem card_Z_ge_four (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) : 4 ≤ Nat.card D.Z := by
  have hZel : IsElemAbelian 2 (D.Z : Subgroup G) := c.isElemAbelian_Z h4 h1930
  have hZrk : 2 ≤ rk ↥D.Z := hn.trans (pRank_le_rk hZel)
  have hZcard : Nat.card D.Z = 2 ^ rk ↥D.Z := card_eq_two_pow_of_isPGroup hZel.isPGroup
  rw [hZcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ rk ↥D.Z := Nat.pow_le_pow_right (by norm_num) hZrk

private theorem conjSubgroup_Z_le_V (c : Ctx23L D Ch) (k : G) (hk : k ∈ c.N) :
    conjSubgroup D.Z k ≤ c.V := by
  have hVdecomp : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  rw [hVdecomp]
  have hY : conjSubgroup D.Z k = D.Z.map (MulAut.conj (k⁻¹)).toMonoidHom := rfl
  rw [hY]
  exact le_iSup (fun n : ↥c.N => D.Z.map (MulAut.conj (n : G)).toMonoidHom)
    ⟨k⁻¹, c.N.inv_mem hk⟩

private theorem conjSubgroup_Z_invariant (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) {U : Subgroup G} (hUV : U ≤ c.V)
    (hU : mQuot c.V U ≤ 1) {x : G} (hx : x ∈ Subgroup.centralizer (U : Set G))
    {k : G} (hk : k ∈ c.N) :
    conjSubgroup (conjSubgroup D.Z k) x = conjSubgroup D.Z k := by
  have hVelem : IsElemAbelian 2 c.V := c.isElemAbelian_V h4 h1930
  have hYV : conjSubgroup D.Z k ≤ c.V := c.conjSubgroup_Z_le_V k hk
  have hYcard : 2 < Nat.card (conjSubgroup D.Z k) := by
    rw [CFSG.Quasithin.E3.card_conjSubgroup]
    exact lt_of_lt_of_le (by norm_num) (c.card_Z_ge_four h4 h1930 hn)
  have hne' : U ⊓ conjSubgroup D.Z k ≠ ⊥ :=
    inf_ne_bot_of_mQuot_le_one hVelem.isPGroup hUV hYV hU hYcard
  haveI : Nontrivial ↥(U ⊓ conjSubgroup D.Z k) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hne'
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_ne_one_of_nontrivial (U ⊓ conjSubgroup D.Z k)
  have hux : x * u * x⁻¹ = u := by
    have hcomm : u * x = x * u := (Subgroup.mem_centralizer_iff.mp hx) u hu.1
    rw [← hcomm]
    group
  have hne : conjSubgroup D.Z k ⊓ conjSubgroup (conjSubgroup D.Z k) x ≠ ⊥ := by
    intro hbot
    have hug : u ∈ conjSubgroup (conjSubgroup D.Z k) x := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff, hux]
      exact hu.2
    have hbot' : u ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hu.2, hug⟩
    exact hu1 (Subgroup.mem_bot.mp hbot')
  exact c.conjSubgroup_TI h4 h1930 k x hne

theorem centralizer_le_normalizer_V (c : Ctx23L D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G))
    {U : Subgroup G} (hUV : U ≤ c.V) (hU : mQuot c.V U ≤ 1) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (c.V : Set G) := by
  intro x hx
  have hVdecomp : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  have hgen : ∀ n : ↥c.N, conjSubgroup (D.Z.map (MulAut.conj (n : G)).toMonoidHom) x =
      D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    intro n
    have h := c.conjSubgroup_Z_invariant h4 h1930 hn hUV hU hx (k := (n : G)⁻¹)
      (c.N.inv_mem n.2)
    simpa [CFSG.Quasithin.conjSubgroup, inv_inv] using h
  have hVeq : conjSubgroup c.V x = c.V := by
    rw [hVdecomp]
    unfold CFSG.Quasithin.conjSubgroup
    rw [Subgroup.map_iSup]
    exact iSup_congr hgen
  exact (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mp hVeq

theorem two_le_rParam_V (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) : (2 : ℕ∞) ≤ rParam c.V := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hcent⟩ := hU
  have h2 : 2 ≤ mQuot c.V U := by
    by_contra h
    exact hcent (c.centralizer_le_normalizer_V h4 h1930 hn hUV (by omega))
  exact_mod_cast h2

theorem pRank_le_mParam_V (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    CFSG.Open.pRank 2 (D.Z : Subgroup G) ≤
      mParam (CFSG.Quasithin.autI (c.isElemAbelian_V h4 h1930) ⊤) := by
  have hVelem := c.isElemAbelian_V h4 h1930
  have hVdecomp : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  let Y : ↥c.N → Subgroup G := fun n => conjSubgroup D.Z ((n : G)⁻¹)
  have hYleV : ∀ n, Y n ≤ c.V := by
    intro n
    rw [hVdecomp]
    have hYn : Y n = D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
      simp [Y, CFSG.Quasithin.conjSubgroup, inv_inv]
    rw [hYn]
    exact le_iSup (fun n : ↥c.N => D.Z.map (MulAut.conj (n : G)).toMonoidHom) n
  have hspanV : c.V = ⨆ n, Y n := by
    rw [hVdecomp]
    exact iSup_congr fun n => by simp [Y, CFSG.Quasithin.conjSubgroup, inv_inv]
  have hTI : ∀ (n : ↥c.N) (g : G), Y n ⊓ conjSubgroup (Y n) g ≠ ⊥ →
      conjSubgroup (Y n) g = Y n := by
    intro n g hne
    exact c.conjSubgroup_TI h4 h1930 ((n : G)⁻¹) g hne
  have hCN : ∀ (n : ↥c.N) (x : G), x ∈ Subgroup.normalizer (Y n : Set G) →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ Y n, x * y * x⁻¹ = y := by
    intro n x hxN hx2
    exact c.conjSubgroup_twoElement_centralizes h4 h1930 ((n : G)⁻¹) hxN hx2
  have hk : ∀ n : ↥c.N, CFSG.Open.pRank 2 (D.Z : Subgroup G) ≤
      CFSG.Open.pRank 2 (Y n : Subgroup G) := by
    intro n
    have hYn : Y n = D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
      simp [Y, CFSG.Quasithin.conjSubgroup, inv_inv]
    rw [hYn]
    exact le_of_eq (CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
      (by norm_num) (MulAut.conj (n : G)) (D.Z : Subgroup G)).symm
  exact le_mParam_of_tiFamily hVelem Y hYleV hspanV hTI hCN
    (CFSG.Open.pRank 2 (D.Z : Subgroup G)) hk

theorem one_lt_sParam_V (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) :
    1 < sParam (c.isElemAbelian_V h4 h1930) := by
  have hV := c.isElemAbelian_V h4 h1930
  have hr : (1 : ℕ∞) < rParam c.V :=
    lt_of_lt_of_le (by norm_num) (c.two_le_rParam_V h4 h1930 hn)
  have hm : 1 < mParam (CFSG.Quasithin.autI hV ⊤) :=
    lt_of_lt_of_le (by omega : 1 < CFSG.Open.pRank 2 (D.Z : Subgroup G))
      (c.pRank_le_mParam_V h4 h1930)
  exact lt_sParam_of_lt hV (k := 1) hr hm

end Ctx23L

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G}

private theorem V_le_wClos (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) {i : ℕ} (hi : i ≤ 1) :
    c.V ≤ wClos c.V i D.T := by
  have hVelem := c.isElemAbelian_V h4 h1930
  have hVrk : 2 ≤ rk ↥c.V := by
    have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    exact hn.trans ((CFSG.SectionRank.pRank_mono (by norm_num) hZV).trans (pRank_le_rk hVelem))
  exact le_wClos_of_mQuot_le_self hVelem (c.V_le_T h4 h1930) le_rfl
    (by rw [CFSG.Quasithin.E3.mQuot_self]; exact Nat.zero_le _) (by omega)

private theorem wClos_ne_bot (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) {i : ℕ} (hi : i ≤ 1) :
    wClos c.V i D.T ≠ ⊥ := by
  intro hbot
  exact c.V_ne_bot h4 h1930 (le_bot_iff.mp (hbot ▸ c.V_le_wClos h4 h1930 hn hi))

private theorem isPGroup_wClos (c : Ctx2311 D Ch) (i : ℕ) :
    IsPGroup 2 (wClos c.V i D.T) :=
  D.sylowM.isPGroup.to_le (uc22p22ta_wClos_le c.V i D.T)

private theorem center_wClos_one_ne_bot (c : Ctx2311 D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) :
    wClos c.V 1 D.T ⊓ Subgroup.centralizer (wClos c.V 1 D.T : Set G) ≠ ⊥ := by
  have hW2 := c.isPGroup_wClos 1
  have hWne := c.wClos_ne_bot h4 h1930 hn (i := 1) le_rfl
  haveI : Nontrivial ↥(wClos c.V 1 D.T) := (Subgroup.nontrivial_iff_ne_bot _).2 hWne
  haveI := hW2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥(wClos c.V 1 D.T)))
  intro hbot
  have hzmem : ((z : ↥(wClos c.V 1 D.T)) : G) ∈
      wClos c.V 1 D.T ⊓ Subgroup.centralizer (wClos c.V 1 D.T : Set G) := by
    refine ⟨(z : ↥(wClos c.V 1 D.T)).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)
  rw [hbot, Subgroup.mem_bot] at hzmem
  exact hz (Subtype.ext (Subtype.ext hzmem))

private theorem mem_hSet_normalizer_center_wClos_one (c : Ctx2311 D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G))
    (hXN : c.X ≤ Subgroup.normalizer (wClos c.V 1 D.T : Set G)) :
    Subgroup.normalizer (wClos c.V 1 D.T ⊓
      Subgroup.centralizer (wClos c.V 1 D.T : Set G) : Subgroup G) ∈ hSet D.T D.M := by
  let ZW₁ : Subgroup G := wClos c.V 1 D.T ⊓ Subgroup.centralizer (wClos c.V 1 D.T : Set G)
  change Subgroup.normalizer ZW₁ ∈ hSet D.T D.M
  refine ⟨fun t ht => ?_, fun h => c.hXM ?_, ?_⟩
  · exact uc22p22ta_mem_normalizer_center
      (normalizer_le_normalizer_wClos (V := c.V) (i := 1) D.T (Subgroup.le_normalizer ht))
  · exact (hXN.trans fun x hx => uc22p22ta_mem_normalizer_center hx).trans h
  · exact D.standing.charTwo _ ⟨ZW₁, c.center_wClos_one_ne_bot h4 h1930 hn,
      (c.isPGroup_wClos 1).to_le inf_le_left, rfl⟩

private theorem mem_hSet_normalizer_wClos_zero (c : Ctx2311 D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G))
    (hXN : c.X ≤ Subgroup.normalizer (wClos c.V 1 D.T : Set G)) :
    Subgroup.normalizer (wClos c.V 0 D.T : Set G) ∈ hSet D.T D.M := by
  have hVelem := c.isElemAbelian_V h4 h1930
  have hVrk : 1 < rk ↥c.V := by
    have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    have h2 : 2 ≤ rk ↥c.V :=
      hn.trans ((CFSG.SectionRank.pRank_mono (by norm_num) hZV).trans (pRank_le_rk hVelem))
    omega
  refine ⟨fun t ht => normalizer_le_normalizer_wClos (V := c.V) (i := 0) D.T
      (Subgroup.le_normalizer ht), fun h => c.hXM ?_, ?_⟩
  · exact (hXN.trans (normalizer_wClos_one_le_zero hVelem hVrk D.T)).trans h
  · exact D.standing.charTwo _ ⟨wClos c.V 0 D.T,
      c.wClos_ne_bot h4 h1930 hn (i := 0) (by omega), c.isPGroup_wClos 0, rfl⟩

private theorem eq_mul_normalizers_wClos (c : Ctx2311 D Ch) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G)) {X : Subgroup G}
    (hTX : D.T ≤ X)
    (hF : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 X ∨ Group.IsSolvable ↥X) :
    (X : Set G) = ((Subgroup.normalizer (wClos c.V 1 D.T ⊓
        Subgroup.centralizer (wClos c.V 1 D.T : Set G) : Subgroup G) ⊓ X : Subgroup G) : Set G) *
      ((Subgroup.normalizer (wClos c.V 0 D.T : Set G) ⊓ X : Subgroup G) : Set G) := by
  have hVelem := c.isElemAbelian_V h4 h1930
  have hlt : 0 + 1 < sParam hVelem := by
    simpa using c.one_lt_sParam_V h4 h1930 hn
  have h := uc22s21rhp_eq_mul_of_or hVelem (uc22p22ta_isSylowIn D hTX) (i := 0) (j := 1) le_rfl
    hF hlt
  have hZW : wClos c.V 1 D.T ⊓ Subgroup.centralizer (wClos c.V 1 D.T : Set G) ≤
      cClos c.V (0 + 1) D.T := by
    rw [CFSG.Quasithin.E3.cClos]
    exact le_inf (inf_le_left.trans (uc22p22ta_wClos_le c.V 1 D.T)) inf_le_right
  apply Set.Subset.antisymm
  · intro x hx
    rw [h] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a, ⟨?_, ha.1⟩, b, ⟨hb.2, hb.1⟩, rfl⟩
    exact Subgroup.centralizer_le_normalizer _
      ((Subgroup.centralizer_le hZW) ha.2)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact X.mul_mem ha.2 hb.2

theorem not_le_normalizer_wClos_one (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h2122 : S21_22Use D Ch) (hn : 2 ≤ CFSG.Open.pRank 2 (D.Z : Subgroup G))
    (hL0X : c.L0 ≤ c.X) :
    ¬ c.X ⊔ D.T ≤ Subgroup.normalizer (wClos c.V 1 D.T : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hXT
  have hXN : c.X ≤ Subgroup.normalizer (wClos c.V 1 D.T : Set G) := le_sup_left.trans hXT
  have hVelem := c.isElemAbelian_V h4 h1930
  have hVrk : 1 < rk ↥c.V := by
    have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    have h2 : 2 ≤ rk ↥c.V :=
      hn.trans ((CFSG.SectionRank.pRank_mono (by norm_num) hZV).trans (pRank_le_rk hVelem))
    omega
  have hX₁ : c.X ≤ Subgroup.normalizer (wClos c.V 1 D.T ⊓
      Subgroup.centralizer (wClos c.V 1 D.T : Set G) : Subgroup G) :=
    hXN.trans fun x hx => uc22p22ta_mem_normalizer_center hx
  have hX₂ : c.X ≤ Subgroup.normalizer (wClos c.V 0 D.T : Set G) :=
    hXN.trans (normalizer_wClos_one_le_zero hVelem hVrk D.T)
  have hH₁ := c.mem_hSet_normalizer_center_wClos_one h4 h1930 hn hXN
  have hH₂ := c.mem_hSet_normalizer_wClos_zero h4 h1930 hn hXN
  have hL0 : c.L0 ≤ Subgroup.normalizer (wClos c.V 1 D.T ⊓
      Subgroup.centralizer (wClos c.V 1 D.T : Set G) : Subgroup G) ⊓
        Subgroup.normalizer (wClos c.V 0 D.T : Set G) := by
    refine le_inf ?_ ?_
    · exact (hL0X.trans hXN).trans fun x hx => uc22p22ta_mem_normalizer_center hx
    · exact (hL0X.trans hXN).trans (normalizer_wClos_one_le_zero hVelem hVrk D.T)
  have hle : Subgroup.normalizer (wClos c.V 1 D.T ⊓
      Subgroup.centralizer (wClos c.V 1 D.T : Set G) : Subgroup G) ⊓
        Subgroup.normalizer (wClos c.V 0 D.T : Set G) ≤ D.M :=
    h2122 h1930 c.toCtx21 _ hH₁ _ hH₂ hL0 fun X _ hTX hInF =>
      c.eq_mul_normalizers_wClos h4 h1930 hn hTX hInF
  exact c.hXM ((le_inf hX₁ hX₂).trans hle)

end Ctx2311

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
