module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KFix
public import CFSG.RankThree.PartTwo.Sec12.Hering129KOut
public import CFSG.RankThree.PartTwo.Sec12.Hering129KRes
public import CFSG.RankThree.PartTwo.Sec12.Hering129KImg
public import CFSG.RankThree.PartTwo.Sec12.Hering129KInner
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Gap129KFLieP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y →
        ∀ (r : TauCeti.PrimePower) (δ : ℕ), IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r δ →
          4 ≤ r.card → r.p ≠ 3 → (δ = 3 → r.p = 2) →
          SymData129 A c x Y ∧
            ¬ (resCent Y c ⊔ inSubgroup (aschbacherSolvableCore 3) Y = Y) ∧
            Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c))
              r.card

theorem eq_one_of_mem_theta_of_pow_three {Y : Type} [Group Y] [Finite Y] {n : Y}
    (hn : n ∈ aschbacherSolvableCore 3 Y) (hn3 : n ^ 3 = 1) : n = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  by_contra hne
  have hord : orderOf (⟨n, hn⟩ : aschbacherSolvableCore 3 Y) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hn3 hne
  have := orderOf_dvd_natCard (⟨n, hn⟩ : aschbacherSolvableCore 3 Y)
  rw [hord] at this
  exact hθ3 this



theorem gap129KFLieP_of (hTL : KS129ThreeLocalFix) (h1134N : Sec11.Item1134E27N)
    (h1134ST : Sec21.Item1134E27ST) (hKK : Gap129KFKStrong) : Gap129KFLieP := by
  intro G _ _ A c L b a K S cfg hty x hxD hxb Y hY hXY r₀ δ₀ hG₀ hr₄ hr₀p3 hr₀δ
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
  have core : ∀ (r : TauCeti.PrimePower) (δ : ℕ), IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r δ →
      4 ≤ r.card → r.p ≠ 3 → (δ = 3 → r.p = 2) →
      SymData129 A c x Y ∧
        ¬ (resCent Y c ⊔ inSubgroup (aschbacherSolvableCore 3) Y = Y) ∧
        Nonempty (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c) ≃*
          ↥(resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀))) ∧ IsThreeA (π c₀) r.card := by
    intro r δ hG hr4 hrp3 hrδ
    have hGθ : IsG2D4 (↥Y ⧸ N) r δ :=
      Hering129KOut.isG2D4_congr (QuotientGroup.quotientMulEquivOfEq hθ).symm hG
    obtain ⟨h0, ha', hcl, hd⟩ := hTL _ r δ hGθ hr4 hrp3 hrδ
    have hBb : IsThreeB (π b₀) (r.card ^ δ) := by
      rcases h0 (π b₀) hbh3 with hA | hB
      · exfalso
        exact Hering129KRes.false_of_threeA_image hXperf φ hker (m := r.card) (by omega)
          hA.2.2 hPz hsub' hne hZ2
      · exact hB
    have hĉmem : π c₀ ∈ resCent (⊤ : Subgroup (↥Y ⧸ N)) (π b₀) := hPz hĉφ
    have hĉA : IsThreeA (π c₀) r.card := (hd (π b₀) hBb).1 (π c₀) hĉmem hĉ3
    have hbmem : π b₀ ∈ resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀) :=
      ha' (π c₀) hĉA (π b₀) hBb hĉmem
    have hcI : c₀ ∈ inSubgroup perfectResidual (Subgroup.centralizer ({c₀} : Set ↥Y)) :=
      Hering129KRes.mem_resCent_of_image N hθ3 hN2 hc₀3 hc₀3 rfl hĉA.2.1
    have hbI : b₀ ∈ inSubgroup perfectResidual (Subgroup.centralizer ({c₀} : Set ↥Y)) :=
      Hering129KRes.mem_resCent_of_image N hθ3 hN2 hc₀3 hb₀3 hcb.symm hbmem
    have hIeq : resCent Y c =
        (inSubgroup perfectResidual (Subgroup.centralizer ({c₀} : Set ↥Y))).map Y.subtype :=
      resCent_eq_map Y hcY
    have hcI' : c ∈ resCent Y c := hIeq ▸ ⟨c₀, hcI, rfl⟩
    have hbI' : b' ∈ resCent Y c := hIeq ▸ ⟨b₀, hbI, rfl⟩
    obtain ⟨eI⟩ := Hering129KRes.exists_quotTheta_resCent_equiv hcY hc3 (m := r.card)
      (by omega) hĉA.2.2
    have hsl : Sec4.IsSLThreePiAt
        (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c)) r.card :=
      isSLThreePiAt_congr eI.symm hĉA.2.2
    refine ⟨⟨?_, hcI', ⟨b', ⟨hb'A, hbI'⟩, hbU⟩, ?_⟩, ?_, ⟨eI⟩, hĉA⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eI.symm
        (Hering129KRes.isQuasisimple_of_isSLThreePiAt hĉA.2.2 (by omega))
    · exact card_center_eq_three_of_isSLThreePi ⟨r.card, hsl⟩
    · intro hIY
      set Rc := inSubgroup perfectResidual (Subgroup.centralizer ({c₀} : Set ↥Y)) with hRc
      have hsup : Rc ⊔ N = ⊤ := by
        apply Subgroup.map_injective Y.subtype_injective
        rw [Subgroup.map_sup, ← hIeq, Subgroup.map_top, Subgroup.range_subtype]
        exact hIY
      have hRcmap : Rc.map π = resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀) :=
        map_resCent_quot N hθ3 hc₀3
      have htop : resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀) = ⊤ := by
        have h1 : (Rc ⊔ N).map π = ⊤ := by
          rw [hsup, Subgroup.map_top]
          exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
        rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
        rw [← hRcmap]
        exact h1
      have e : ↥(resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀)) ≃* (↥Y ⧸ N) :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      exact Hering129KOut.not_isSLThreePiAt_of_isG2D4 hGθ r.card
        (isSLThreePiAt_congr e hĉA.2.2)
  obtain ⟨S1, S2, ⟨eI₀⟩, hĉA₀⟩ := core r₀ δ₀ hG₀ hr₄ hr₀p3 hr₀δ
  exact ⟨S1, S2, isSLThreePiAt_congr eI₀.symm hĉA₀.2.2⟩

end CFSG.RankThree.PartTwo.Sec12
