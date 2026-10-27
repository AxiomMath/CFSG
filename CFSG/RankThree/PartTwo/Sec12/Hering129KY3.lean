module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KLie
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem exists_sl2_image_Y (hTL : KS129ThreeLocalFix) (h1134N : Sec11.Item1134E27N)
    (h1134ST : Sec21.Item1134E27ST) (hKK : Gap129KFKStrong)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {b a : G}
    {K S : Subgroup G} (cfg : Cfg129 G A c L b a K S) (hty : GTwoType129 L K) {x : G}
    (hxD : x ∈ D129 a b) (hxb : x ∉ Subgroup.zpowers b) {Y : Subgroup G}
    (hY : Core129 A c x Y) (hXY : resCent K x ≤ Y) {r₀ : TauCeti.PrimePower} {δ₀ : ℕ}
    (hG₀ : IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r₀ δ₀) (hr₄ : 4 ≤ r₀.card) (hr₀p3 : r₀.p ≠ 3)
    (hr₀δ : δ₀ = 3 → r₀.p = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = r₀.card ^ δ₀ ∧
      ∃ φ : ↥(resCent K x) →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective φ ∧ φ.ker ≤ aschbacherSolvableCore 3 ↥(resCent K x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAF : A ∈ partTwoF G := hstd.partTwoF_eq ▸ cfg.mem_E
  have hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A := hAF.2.1
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcA := hstd.mem_A
  have hc1 := hstd.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hxB := cfg.not_mem_B_of_mem_D hxD hxb
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hstd.mem_thetaComponentsAt
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hstd.mem_L hLc
  have hbB : b ∈ Sec4.thetaQuotCentralizer L := cfg.hb.2
  obtain ⟨hcX, hSX, hXq, hZ2⟩ := hKK G A c L b a K S cfg hty x hxD hxb
  have hcY : c ∈ Y := hXY hcX
  obtain ⟨-, -, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  set N := aschbacherSolvableCore 3 ↥Y with hN
  haveI hNn : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  have hθ : N = CFSG.pCore 2 ↥Y := Hering129KOut.aschbacherSolvableCore_eq_pCore_two hG₀
  have hGθ₀ : IsG2D4 (↥Y ⧸ N) r₀ δ₀ :=
    Hering129KOut.isG2D4_congr (QuotientGroup.quotientMulEquivOfEq hθ).symm hG₀
  have hZ : Subgroup.center (↥Y ⧸ N) = ⊥ := Hering129KModels.center_eq_bot_of_isG2D4 hGθ₀
  have hinner : ∀ e ∈ A, ¬ Sec4.InducesOuterTheta e Y := fun e he =>
    Hering129KOut.not_inducesOuterTheta_of_core h1134N h1134ST hstd.toPartTwoStanding hAF
      cfg.mem_S hstd.partTwoF_eq hA27 hxA hx1 hY.1 hY.2.1 hY.2.2.1 hGθ₀ hr₄ hr₀p3 hr₀δ he
  obtain ⟨b', hb'AY, hb'⟩ := Hering129KInner.exists_mem_inf_of_not_inducesOuterTheta hAe hAmax
    hY.2.1 hZ hbA (hinner b hbA)
  have hb'A : b' ∈ A := hb'AY.1
  have hb'Y : b' ∈ Y := hb'AY.2
  have hb'3 : b' ^ 3 = 1 := hAe.2 b' hb'A
  obtain ⟨m, hm⟩ : ∃ m : ℤ, x ^ m = b * b'⁻¹ := by
    have hmem : b * b'⁻¹ ∈ A ⊓ Sec4.thetaQuotCentralizer Y :=
      ⟨A.mul_mem hbA (A.inv_mem hb'A), hb'⟩
    rw [hY.2.2.1] at hmem
    exact Subgroup.mem_zpowers_iff.mp hmem
  have hbxb' : b = x ^ m * b' := by rw [hm]; group
  set c₀ : ↥Y := ⟨c, hcY⟩ with hc₀
  set b₀ : ↥Y := ⟨b', hb'Y⟩ with hb₀
  have hc₀3 : c₀ ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hb₀3 : b₀ ^ 3 = 1 := Subtype.ext (by simpa using hb'3)
  have hcb : c₀ * b₀ = b₀ * c₀ := Subtype.ext (hAc c hcA b' hb'A)
  have hbU : b' ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c := by
    intro h
    have hxc : x * c = c * x := hAc x hxA c hcA
    have hb : b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers c := by
      rw [hbxb']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x m)) h
    obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup hxc hb
    rw [Sec4.zpow_emod_three hx3 i] at hik
    have hck : c ^ k ∈ Sec4.thetaQuotCentralizer L :=
      Subgroup.zpow_mem _ hcB k
    have hx2 : x ^ (2 : ℤ) = x⁻¹ := by
      have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
      calc x ^ (2 : ℤ) = x ^ (3 : ℤ) * x⁻¹ := by
            rw [← zpow_neg_one, ← zpow_add]; norm_num
        _ = x⁻¹ := by rw [h3, one_mul]
    have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hi with h0 | h1 | h2
    · apply cfg.hb_not
      rw [hik, h0, zpow_zero, one_mul]
      exact Subgroup.zpow_mem_zpowers c k
    · apply hxB
      rw [h1, zpow_one] at hik
      have : x = b * (c ^ k)⁻¹ := by rw [hik]; group
      rw [this]
      exact Subgroup.mul_mem _ hbB (Subgroup.inv_mem _ hck)
    · apply hxB
      rw [h2, hx2] at hik
      have : x = (b * (c ^ k)⁻¹)⁻¹ := by rw [hik]; group
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hbB (Subgroup.inv_mem _ hck))
  have hb'1 : b' ≠ 1 := fun h => hbU (h ▸ Subgroup.one_mem _)
  have hb₀1 : b₀ ≠ 1 := fun h => hb'1 (congrArg Subtype.val h)
  have hc₀1 : c₀ ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hĉ3' : π c₀ ^ 3 = 1 := by rw [← map_pow, hc₀3, map_one]
  have hĉ1 : π c₀ ≠ 1 := fun h =>
    hc₀1 (eq_one_of_mem_theta_of_pow_three ((QuotientGroup.eq_one_iff _).mp h) hc₀3)
  have hĉ3 : orderOf (π c₀) = 3 := orderOf_eq_prime hĉ3' hĉ1
  have hbh3' : π b₀ ^ 3 = 1 := by rw [← map_pow, hb₀3, map_one]
  have hbh1 : π b₀ ≠ 1 := fun h =>
    hb₀1 (eq_one_of_mem_theta_of_pow_three ((QuotientGroup.eq_one_iff _).mp h) hb₀3)
  have hbh3 : orderOf (π b₀) = 3 := orderOf_eq_prime hbh3' hbh1
  set X := resCent K x with hX
  have hXperf : Group.IsPerfect X := isPerfect_resCent K x
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXK : X ≤ K := (resCent_le K x).trans inf_le_left
  have hXx : X ≤ Subgroup.centralizer ({x} : Set G) := (resCent_le K x).trans inf_le_right
  have hYx : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY.1
  have hXb' : X ≤ Subgroup.centralizer ({b'} : Set G) := by
    intro k hk
    have hkb : Commute k b := Subgroup.mem_centralizer_singleton_iff.mp (hKb (hXK hk))
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.mp (hXx hk)
    have hb'eq : b' = (x ^ m)⁻¹ * b := by rw [hbxb']; group
    rw [hb'eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((hkx.zpow_right m).inv_right).mul_right hkb)
  have hXM : X ≤ Y ⊓ Subgroup.centralizer ({b'} : Set G) := le_inf hXY hXb'
  have hXR : X ≤ resCent Y b' := le_inSubgroup_perfectResidual_of_isPerfect hXM hXperf
  have hMb : Y ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro g hg
    have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp (hYx hg.1)
    have hgb' : Commute g b' := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    rw [hbxb']
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hgx.zpow_right m).mul_right hgb')
  have hMx : Y ⊓ Subgroup.centralizer ({b'} : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    inf_le_left.trans hYx
  have hsubG := resCent_isSubnormal cfg.hK hMb hMx hXM
  set XY : Subgroup ↥Y := X.subgroupOf Y with hXYdef
  have hXYmap : XY.map Y.subtype = X := by
    rw [hXYdef, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left hXY
  set C₀ : Subgroup ↥Y := Subgroup.centralizer ({b₀} : Set ↥Y) with hC₀
  have hC₀map : C₀.map Y.subtype = Y ⊓ Subgroup.centralizer ({b'} : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton Y b₀
  have hsubY : (XY.subgroupOf C₀).IsSubnormal := by
    apply Hering129KSub.isSubnormal_subgroupOf_of_map
    rw [hXYmap, hC₀map]
    exact hsubG
  have hRb : resCent Y b' = (inSubgroup perfectResidual C₀).map Y.subtype :=
    resCent_eq_map Y hb'Y
  have hXRY : XY ≤ inSubgroup perfectResidual C₀ := by
    intro y hy
    have hyX : (y : G) ∈ X := hy
    have hy2 : (y : G) ∈ (inSubgroup perfectResidual C₀).map Y.subtype := hRb ▸ hXR hyX
    obtain ⟨r, hr, hry⟩ := hy2
    have : r = y := Subtype.ext hry
    exact this ▸ hr
  obtain ⟨hXhat_le, hXhat_sub⟩ := image_subnormal_in_resCent N hθ3 hb₀3 hXRY hsubY
  let φ : ↥X →* ↥Y ⧸ N := π.comp (Subgroup.inclusion hXY)
  have hrange : φ.range = XY.map π := by
    ext w
    constructor
    · rintro ⟨ξ, rfl⟩
      exact ⟨Subgroup.inclusion hXY ξ, ξ.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  have hPz : φ.range ≤ resCent (⊤ : Subgroup (↥Y ⧸ N)) (π b₀) := hrange ▸ hXhat_le
  have hsub' : (φ.range.subgroupOf (resCent (⊤ : Subgroup (↥Y ⧸ N)) (π b₀))).IsSubnormal :=
    hrange ▸ hXhat_sub
  have hĉφ : π c₀ ∈ φ.range := ⟨⟨c, hcX⟩, rfl⟩
  have hne : φ.range ≠ ⊥ := fun h => hĉ1 (by
    have := hĉφ
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hker : φ.ker ≤ aschbacherSolvableCore 3 ↥X := by
    intro ξ hξ
    have h1 : π (Subgroup.inclusion hXY ξ) = 1 := hξ
    have h2 : Subgroup.inclusion hXY ξ ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (ξ : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := ⟨_, h2, rfl⟩
    exact mem_theta_of_mem_theta_of_le hXY ξ.2 h3
  have hN2 : ∀ n ∈ N, ∃ k : ℕ, n ^ (2 ^ k) = 1 := fun n hn =>
    exists_pow_two_pow_eq_one (Y := ↥Y) (hθ ▸ hn)
  obtain ⟨h0, -, -, -⟩ := hTL _ r₀ δ₀ hGθ₀ hr₄ hr₀p3 hr₀δ
  have hBb : IsThreeB (π b₀) (r₀.card ^ δ₀) := by
    rcases h0 (π b₀) hbh3 with hA | hB
    · exfalso
      exact Hering129KRes.false_of_threeA_image hXperf φ hker (m := r₀.card) (by omega)
        hA.2.2 hPz hsub' hne hZ2
    · exact hB
  obtain ⟨-, F, hFf, hFfin, hFcard, ⟨e⟩⟩ := hBb
  set Q := resCent (⊤ : Subgroup (↥Y ⧸ N)) (π b₀) with hQ
  haveI : Finite F := Finite.of_fintype F
  have h4F : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    exact hr₄.trans (Nat.le_self_pow (by rcases hG₀ with ⟨h1, -⟩ | ⟨h3, -⟩ <;> omega) _)
  have hQq : CFSG.IsQuasisimple ↥Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour.isQuasisimple_sl2 h4F)
  have hφp : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hφp' : Group.IsPerfect (φ.range.subgroupOf Q) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPz).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPz).symm.surjective
  have hne' : φ.range.subgroupOf Q ≠ ⊥ := by
    intro h
    apply hne
    have hle : φ.range ≤ ⊥ := by
      intro w hw
      have : (⟨w, hPz hw⟩ : ↥Q) ∈ φ.range.subgroupOf Q := hw
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    exact le_bot_iff.mp hle
  have htop : φ.range.subgroupOf Q = ⊤ :=
    Sec11.FieldCentRigid82.eq_top_of_isSubnormal_of_isQuasisimple hQq hsub' hφp' hne'
  let φ1 : ↥(resCent K x) →* ↥Q := φ.codRestrict Q (fun ξ => hPz ⟨ξ, rfl⟩)
  have hφ1 : Function.Surjective φ1 := by
    intro w
    have hw : (w : ↥Y ⧸ N) ∈ φ.range := by
      have : w ∈ φ.range.subgroupOf Q := by rw [htop]; trivial
      exact this
    obtain ⟨ξ, hξ⟩ := hw
    exact ⟨ξ, Subtype.ext hξ⟩
  refine ⟨F, hFf, hFfin, hFcard, e.toMonoidHom.comp φ1, e.surjective.comp hφ1, ?_⟩
  intro ξ hξ
  have h1 : φ1 ξ = 1 := by
    have : e (φ1 ξ) = 1 := hξ
    exact (MulEquiv.map_eq_one_iff e).mp this
  apply hker
  have := congrArg Subtype.val h1
  exact this

end CFSG.RankThree.PartTwo.Sec12
