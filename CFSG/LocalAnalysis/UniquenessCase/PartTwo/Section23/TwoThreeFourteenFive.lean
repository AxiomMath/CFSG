module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransportModule
public import CFSG.GroupTheory.RegularRepGF2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeMinimal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem dMinDeg_le_of_surjective {K H : Type} [Group K] [Group H] [Finite H] [Nontrivial H]
    (q : K →* H) (hq : Function.Surjective q) : dMinDeg K ≤ dMinDeg H := by
  classical
  obtain ⟨n, f, hf⟩ := CFSG.GroupTheory.exists_nontrivial_repr_card H
  have hne : {m : ℕ | ∃ g : H →* Matrix.GeneralLinearGroup (Fin m) (ZMod 2), g ≠ 1}.Nonempty :=
    ⟨n, f, hf⟩
  obtain ⟨g, hg⟩ := Nat.sInf_mem hne
  have hcomp : g.comp q ≠ 1 := by
    intro h1
    apply hg
    refine MonoidHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hq y
    exact congrArg (fun φ => φ x) h1
  exact Nat.sInf_le ⟨g.comp q, hcomp⟩

private theorem N_le_stabTil {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.N ≤ stabTil ⊥ A :=
  le_inf hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)

theorem fixV_barSub_eq_imgTil_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {X : Subgroup G} (hX : X ≤ stabTil ⊥ A) :
    fixV (barSub ⊥ A hA X) = imgTil ⊥ A hA (A ⊓ Subgroup.centralizer (X : Set G)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ A hA q
    have hxcent : x.val ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hmem : actTil ⊥ A hA ⟨y, hX hy⟩ ∈ barSub ⊥ A hA X :=
        actTil_mem_barSub ⊥ A hA hy (hX hy)
      have hfix := (mem_fixV.mp hq) _ hmem
      rw [actTil_mk, mkTil_eq_iff] at hfix
      rw [Subgroup.mem_bot] at hfix
      have hval : y * x.val * y⁻¹ = x.val := mul_inv_eq_one.1 hfix
      calc y * x.val = (y * x.val * y⁻¹) * y := by group
        _ = x.val * y := by rw [hval]
    refine (mem_imgTil ⊥ A hA (A ⊓ Subgroup.centralizer (X : Set G))
      (mkTil ⊥ A hA x)).2 ?_
    exact ⟨x, Subgroup.mem_inf.mpr ⟨x.val_mem, hxcent⟩, rfl⟩
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_imgTil ⊥ A hA (A ⊓ Subgroup.centralizer (X : Set G)) q).1 hq
    rw [← hxq]
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨g, hgX, hgφ⟩ := (mem_barSub ⊥ A hA X φ).1 hφ
    have hxC : x.val ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hx).2
    rw [← hgφ, actTil_mk, mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val]
    have hcomm : (g : G) * x.val = x.val * (g : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (g : G) hgX
    rw [hcomm]
    group

private theorem T_le_normalizer_of_le_N {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    D.T ≤ Subgroup.normalizer (A : Set G) :=
  (Ctx23L.T_le_N c).trans hAN

private theorem T_le_stabTil {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    D.T ≤ stabTil ⊥ A :=
  le_inf (T_le_normalizer_of_le_N c hAN)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)

private theorem L0_le_stabTil {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.L0 ≤ stabTil ⊥ A :=
  (Ctx23L.L0_le_N c).trans (N_le_stabTil c hAN)

theorem fixV_T_barSub_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    fixV (barSub ⊥ A hA D.T) = imgTil ⊥ A hA (A ⊓ D.Z) := by
  rw [fixV_barSub_eq_imgTil_centralizer hA (T_le_stabTil c hAN)]
  have hTZ : A ⊓ D.Z = A ⊓ Subgroup.centralizer (D.T : Set G) := by
    refine le_antisymm (le_inf inf_le_left ?_) (le_inf inf_le_left ?_)
    · intro x hx
      exact ((omegaOneCenterIn_le_inf_centralizer D.T).trans inf_le_right) hx.2
    · intro x hx
      have hxA : x ∈ A := hx.1
      have hxC : x ∈ Subgroup.centralizer (D.T : Set G) := hx.2
      have hxT : x ∈ D.T := Ctx23L.V_le_T_basic c (hAV hxA)
      change x ∈ CFSG.RankThree.PartOne.omegaOneCenterIn D.T
      rw [CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff]
      exact ⟨hxT, fun k hk => Subgroup.mem_centralizer_iff.mp hxC k hk,
        by simpa using hA.2 x hxA⟩
  rw [hTZ]

private theorem inf_Z_ne_bot_of_min {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    A ⊓ D.Z ≠ ⊥ :=
  Ctx23L.inf_Z_ne_bot c hAV hAne (T_le_normalizer_of_le_N c hAN)

private theorem L0_le_centralizer_of_mem_fixV {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hL0stab : c.L0 ≤ stabTil ⊥ A) {z : G} (hzA : z ∈ A)
    (hq' : mkTil ⊥ A hA (IntMod.mk hA ⟨z, hzA⟩) ∈ fixV (barSub ⊥ A hA c.L0)) :
    c.L0 ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [mem_fixV] at hq'
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hφmem : actTil ⊥ A hA ⟨l, hL0stab hl⟩ ∈ barSub ⊥ A hA c.L0 :=
    actTil_mem_barSub ⊥ A hA hl (hL0stab hl)
  have hfixz := hq' _ hφmem
  rw [actTil_mk, mkTil_eq_iff, Subgroup.mem_bot] at hfixz
  have hval : l * z * l⁻¹ = z := mul_inv_eq_one.1 hfixz
  calc z * l = (l * z * l⁻¹) * l := by rw [hval]
    _ = l * z := by group

theorem commSub_fixV_T_hinf_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hPL : P ≤ c.L)
    (hL0P : c.L0 = Hinf P) :
    commSub (fixV (barSub ⊥ A hA D.T)) (Hinf (barSub ⊥ A hA P)) ≠ ⊥ := by
  intro hbot
  have hL0stab : c.L0 ≤ stabTil ⊥ A := L0_le_stabTil c hAN
  have hHinf : Hinf (barSub ⊥ A hA P) = barSub ⊥ A hA c.L0 := by
    rw [Ctx23L.Hinf_barSub c hA hAN hPL, hL0P]
  rw [hHinf] at hbot
  have hfix : fixV (barSub ⊥ A hA D.T) ≤ fixV (barSub ⊥ A hA c.L0) :=
    (commSub_eq_bot_iff.mp hbot)
  rw [fixV_T_barSub_eq c hA hAV hAN,
    fixV_barSub_eq_imgTil_centralizer hA hL0stab] at hfix
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_Z_ne_bot_of_min c hAV hAne hAN)
  have hzA : (z : G) ∈ A := z.2.1
  have hzZ : (z : G) ∈ D.Z := z.2.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hq : mkTil ⊥ A hA (IntMod.mk hA ⟨(z : G), hzA⟩) ∈ imgTil ⊥ A hA (A ⊓ D.Z) :=
    (mem_imgTil ⊥ A hA _ _).2
      ⟨IntMod.mk hA ⟨(z : G), hzA⟩, ⟨hzA, hzZ⟩, rfl⟩
  have hq' : mkTil ⊥ A hA (IntMod.mk hA ⟨(z : G), hzA⟩) ∈
      fixV (barSub ⊥ A hA c.L0) := by
    rw [fixV_barSub_eq_imgTil_centralizer hA hL0stab]
    exact hfix hq
  exact Ctx23L.L0_not_le_M c
    ((L0_le_centralizer_of_mem_fixV c hA hL0stab hzA hq').trans
      (Ctx23.centralizer_le_M c.toCtx23 (Data.Z_le_U D hzZ) hz1'))

private theorem le_sup_centralizer_of_actTil_mem {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hPL : P ≤ c.L)
    {x : G} (hxL : x ∈ c.L) (hxP : ∀ h : x ∈ stabTil ⊥ A,
      actTil ⊥ A hA ⟨x, h⟩ ∈ barSub ⊥ A hA P) :
    x ∈ P ⊔ (c.L ⊓ Subgroup.centralizer (A : Set G)) := by
  have hLstab : c.L ≤ stabTil ⊥ A := (Ctx23L.L_le_N c).trans (N_le_stabTil c hAN)
  have hxPA : actTil ⊥ A hA ⟨x, hLstab hxL⟩ ∈ barSub ⊥ A hA P := hxP (hLstab hxL)
  obtain ⟨p, hpP, hpact⟩ := (mem_barSub ⊥ A hA P _).1 hxPA
  have hact : actTil ⊥ A hA (p⁻¹ * ⟨x, hLstab hxL⟩) = 1 := by
    rw [map_mul, map_inv, hpact, inv_mul_cancel]
  have hcomm : ∀ a ∈ A, ((p : G)⁻¹ * x) * a * ((p : G)⁻¹ * x)⁻¹ * a⁻¹ = 1 := by
    intro a ha
    have h := (actTil_eq_one_iff ⊥ A hA _).1 hact a ha
    simpa using h
  have hcent : (p : G)⁻¹ * x ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hcomm a ha
    calc a * ((p : G)⁻¹ * x) =
        (((p : G)⁻¹ * x) * a * ((p : G)⁻¹ * x)⁻¹) * ((p : G)⁻¹ * x) := by
          rw [mul_inv_eq_one.1 h]
      _ = ((p : G)⁻¹ * x) * a := by group
  have hy : (p : G)⁻¹ * x ∈ c.L ⊓ Subgroup.centralizer (A : Set G) :=
    ⟨c.L.mul_mem (c.L.inv_mem (hPL hpP)) hxL, hcent⟩
  have hxmul : (p : G) * ((p : G)⁻¹ * x) ∈ P ⊔ (c.L ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.mul_mem_sup hpP hy
  rwa [show (p : G) * ((p : G)⁻¹ * x) = x from by group] at hxmul

theorem minimal_parabolic_barSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (hRB : KRankOneBorel) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P)
    (hC : c.L ⊓ Subgroup.centralizer (A : Set G) ≤ P) :
    ∀ Q : Subgroup (MulAut (Vtil ⊥ A hA)),
      Q < barSub ⊥ A hA P →
      IsParabolicTwo ↥(barSub ⊥ A hA c.L) (Q.subgroupOf (barSub ⊥ A hA c.L)) →
      normIn (barSub ⊥ A hA D.T) (barSub ⊥ A hA c.L) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil ⊥ A hA))) →
      (D.T ≤ Subgroup.normalizer (preBarSub c.L ⊥ A hA Q : Set G)) →
      Hinf Q = ⊥ := by
  intro Q hQlt hQpar _ hTR
  classical
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hQL : Q ≤ barSub ⊥ A hA c.L := hQlt.le.trans (barSub_mono ⊥ A hA hPL)
  let R : Subgroup G := preBarSub c.L ⊥ A hA Q
  have hRbar : barSub ⊥ A hA R = Q := Ctx23L.barSub_preBarSub_eq c hA hQL
  have hRpar : ParabolicOf c.L R :=
    parabolicOf_iff.mpr ⟨inf_le_left, Ctx23L.isParabolicTwo_preBarSub c hA hAN hQpar⟩
  have hRleL : R ≤ c.L := inf_le_left
  have hRP : R ≤ P := by
    intro x hx
    obtain ⟨hxL, ⟨hst, hxQ⟩⟩ := (mem_preBarSub c.L ⊥ A hA Q).1 hx
    have hsup : x ∈ P ⊔ (c.L ⊓ Subgroup.centralizer (A : Set G)) :=
      le_sup_centralizer_of_actTil_mem c hA hAN hPL hxL fun h => by
        rw [show (⟨x, h⟩ : ↥(stabTil ⊥ A)) = ⟨x, hst⟩ from Subtype.ext rfl]
        exact hQlt.le hxQ
    exact (sup_le le_rfl hC) hsup
  have hRne : R ≠ P := by
    intro h
    exact hQlt.ne (by rw [← hRbar, h])
  have hRlt : R < P := lt_of_le_of_ne hRP hRne
  have hHinfR : Hinf R = ⊥ :=
    Ctx23L.hinf_eq_bot_of_lt c h2010 h207 hRB hBS h1930 hP hL0P hRpar hTR hRlt
  rw [← hRbar, Ctx23L.Hinf_barSub c hA hAN hRleL, hHinfR, barSub_bot]

theorem aBar_bound_of_S23_1A {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1A : S23_1A D Ch) (h1930 : H1930 D) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    ∃ hW : IsElemAbelian 2 (conjClosure c.L0 (A ⊓ D.Z)),
      mBar c.N ⊥ A hA ≤ aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (A ⊓ D.Z)) hW + 1 ∧
        aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (A ⊓ D.Z)) hW ≤ c.n :=
  h1A h1930 c A hA hAV (Ctx23L.A_eq_conjClosure c hAV hAne hAN hmin) hAne

theorem odd_relIndex_normalizer_of_isSylowIn {W : Type} [CommGroup W] [Finite W]
    {Y T K : Subgroup (MulAut W)} (hT : IsSylowIn 2 T Y)
    (hTY : T ≤ Y) (hTK : T ≤ Subgroup.normalizer (K : Set (MulAut W))) :
    Odd ((Y ⊓ Subgroup.normalizer (K : Set (MulAut W))).relIndex Y) := by
  classical
  have hoddT : Odd (T.relIndex Y) := by
    rw [← Nat.not_even_iff_odd]
    simpa [Nat.even_iff] using hT.2.2
  set N : Subgroup (MulAut W) := Y ⊓ Subgroup.normalizer (K : Set (MulAut W)) with hN
  change Odd (N.relIndex Y)
  have hTN : T ≤ N := le_inf hTY hTK
  have hmul := Subgroup.relIndex_mul_relIndex T N Y hTN inf_le_left
  have hdvd : N.relIndex Y ∣ T.relIndex Y :=
    ⟨T.relIndex N, by rw [mul_comm]; exact hmul.symm⟩
  exact Odd.of_dvd_nat hoddT hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
