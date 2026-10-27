module

public import CFSG.Quasithin.EmptyFaithful.S151S9ULift
public import CFSG.Quasithin.EmptyFaithful.S151S9UCQ
public import CFSG.Quasithin.EmptyFaithful.S151S9UNorm
public import CFSG.Quasithin.EmptyFaithful.S151S9UFaith
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Quasithin.EmptyFaithful.FLcL45
public import CFSG.Quasithin.EmptyFaithful.S151S6B

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem exists_z_data {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hfix : AutFixOn L (s1516 T Z₁ ⊓ L)) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ (∀ x ∈ s1516 T Z₁, z * x = x * z) ∧
      ∃ b ∈ centerOf (s1516 T Z₁ ⊓ L), (∀ l ∈ L, z * l * z⁻¹ = b * l * b⁻¹) ∧
        ¬ ∀ l ∈ L, b * l = l * b := by
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ctx.qtfe.omegaOneCenter_ne_bot
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hyp := hc.h18.six z hzZ hz1
  have hzC : z ∈ Subgroup.centralizer (s1516 T Z₁ : Set G) := hyp.z_central
  have hzG : z ∈ g1_1516 Z₁ := hyp.z_mem_H
  have hzcz : Subgroup.centralizer ({z} : Set G) ≤ Mc := hyp.centralizer_z_le
  have hzB : ∀ x ∈ s1516 T Z₁, z * x * z⁻¹ = x := fun x hx => by
    have h := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [← h]
    group
  have hzN := s151s_z_normalizes hcomp hzG hSyl hzB
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hzZ
  have hzfix : ∀ x ∈ s1516 T Z₁ ⊓ L, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hzC x hx.1).symm
  obtain ⟨b, hb, hbe⟩ := hfix z hzN hz2 hzfix
  refine ⟨z, hzZ, fun x hx => (Subgroup.mem_centralizer_iff.1 hzC x hx).symm, b, hb, hbe, ?_⟩
  intro hbc
  apply hc.hL.not_le
  have hLz : L ≤ Subgroup.centralizer ({z} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hbe l hl
    have h2 : b * l * b⁻¹ = l := by
      rw [hbc l hl]
      group
    rw [h2] at h1
    calc l * z = (z * l * z⁻¹) * z := by rw [h1]
      _ = z * l := by group
  intro l hl
  exact ⟨hc.hL.mem.1 hl, hzcz (hLz hl)⟩

theorem input15120MLDHardB_of_simple (h38 : A38ForSQTK) (kN : SporadicSixNotA38)
    (hloc : Input15120CentLocB) (h22 : MLDAt .M22) (h23 : MLDAt .M23) (h24 : MLDAt .M24) :
    Input15120MLDHardB := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD hH hx
  by_contra hcon
  set S₀ : Subgroup G := s1516 T Z₁ ⊓ L with hS₀
  set ML : Subgroup G := mZ1516 Mc Z₁ ⊓ L with hML
  have hSyl : IsSylowTwoOf S₀ L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  have hfix : AutFixOn L S₀ := (hloc G L S₀ hcomp.2.2 hZ2 hSyl (Or.inr hD)).1
  have hcle := s151s_cent_le_mZ hc hcomp hfix
  have hnotle := s151s_not_le_centralizer hc hcomp hfix
  have hlt : L ⊓ Subgroup.centralizer (centerOf S₀ : Set G) < ML :=
    lt_of_le_of_ne hcle (fun h => hcon (h ▸ le_rfl))
  have hspor : SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hH with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hnormL := g1_le_normalizer_of_sporadic h38 kN hc hcomp hspor
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥L := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact pCore_le_center_of_quasisimple hcomp.2.2
  have hker2 : IsPGroup 2 ↥π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hmld : MLDOver (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hH with h | h | h
    · exact h22 _ h
    · exact h23 _ h
    · exact h24 _ h
  set B' : Subgroup ↥L := S₀.subgroupOf L with hB'
  set P : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := B'.map π with hP
  have hPsyl : IsSylowTwoOf P ⊤ := K1.isSylowTwoOf_top_iff.mpr (sylow_map hSyl π hπ)
  set W : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (centerOf B').map π with hWdef
  obtain ⟨hWle, hWne, hpre⟩ := central_quotient_centralizer hSyl π hπ hker hker2 hnotle hWdef
  obtain ⟨hZP2, hmldP⟩ := hmld P hPsyl
  set M' : Subgroup ↥L := ML.subgroupOf L with hM'
  set Y : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := M'.map π with hY
  have hSM : S₀ ≤ ML := inf_le_inf_right L (s1516_le_mZ1516 hc.h18)
  have hMLL : ML ≤ L := inf_le_right
  have hpc : pCoreOf 2 L ≤ S₀ := pCoreOf_two_le_of_sylowIn hSyl.1 hSyl.2.1 hSyl.2.2
  have hkB : π.ker ≤ B' := by
    rw [hπdef, QuotientGroup.ker_mk', ← pCoreOf_subgroupOf]
    intro x hx
    exact hpc hx
  have hkM : π.ker ≤ M' := fun x hx => hSM (hkB hx)
  have hBM : B' ≤ M' := fun x hx => hSM hx
  have hPY : P ≤ Y := Subgroup.map_mono hBM
  have hMpre : Y.comap π = M' := by
    ext x
    simp only [hY, Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      have h2 := M'.mul_mem hy (hkM this)
      simpa using h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply hc.hL.not_le
    intro l hl
    have h1 : (⟨l, hl⟩ : ↥L) ∈ Y.comap π := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [hMpre] at h1
    exact h1.1
  have hCle : Subgroup.centralizer (W : Set (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ Y := by
    intro q hq
    obtain ⟨l, rfl⟩ := hπ q
    have h1 : l ∈ (Subgroup.centralizer (W : Set (↥L ⧸ CFSG.pCore 2 ↥L))).comap π := hq
    rw [← hpre] at h1
    have h2 : (l : G) ∈ ML := hcle h1
    exact ⟨l, h2, rfl⟩
  have hCne : Subgroup.centralizer (W : Set (↥L ⧸ CFSG.pCore 2 ↥L)) ≠ Y := by
    intro heq
    apply hcon
    intro m hm
    have hmL : m ∈ L := hm.2
    have h1 : (⟨m, hmL⟩ : ↥L) ∈ Y.comap π := by
      rw [hMpre]
      exact hm
    rw [← heq, ← hpre] at h1
    exact h1
  have hCY : Subgroup.centralizer (W : Set (↥L ⧸ CFSG.pCore 2 ↥L)) < Y := lt_of_le_of_ne hCle hCne
  have hPYs : IsSylowTwoOf P Y := A4.isSylowTwoOf_mono hPsyl hPY le_top
  have hact := hmldP W hWle hWne Y hPY hYtop hCY
  have hperf := perfCore_of_actionData hPYs hact
  obtain ⟨hKne, hKc, hKsup⟩ := perfCore_lift π hker hker2 hMLL hSM hSyl hperf
  set K : Subgroup G := perfectCore ML with hKdef
  have hKM : K ≤ mZ1516 Mc Z₁ := (perfectCore_le ML).trans inf_le_left
  have hMZN : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) := by
    have h1 : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
      (mZ1516_le_g1 Mc Z₁).trans hnormL
    have h2 : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (ML : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, h1 hx⟩
    exact h2.trans (normalizer_le_normalizer_perfectCore ML)
  have hKn : (K.subgroupOf (mZ1516 Mc Z₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMZN
  obtain ⟨z, hzZ, hzS, b, hb, hbe, hbnc⟩ := exists_z_data hc hcomp hfix
  have hKz : ¬ K ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hKz
    have hSz : S₀ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzS x hx.1).symm
    have hMLz : ML ≤ Subgroup.centralizer ({z} : Set G) := hKsup ▸ sup_le hKz hSz
    have hbL : b ∈ L := hb.1.2
    have hb' : (⟨b, hbL⟩ : ↥L) ∈ centerOf B' :=
      (mem_centerOf_subgroupOf (inf_le_right : S₀ ≤ L) ⟨b, hbL⟩).mpr hb
    have hbW : π ⟨b, hbL⟩ ∈ W := Subgroup.mem_map_of_mem π hb'
    have hbP : π ⟨b, hbL⟩ ∈ centerOf P := hWle hbW
    have hb1 : π ⟨b, hbL⟩ ≠ 1 := by
      intro h1
      have h3 : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.center ↥L := hker h1
      apply hbnc
      intro l hl
      have h4 := Subgroup.mem_center_iff.mp h3 ⟨l, hl⟩
      exact congrArg Subtype.val h4.symm
    have hzp : Subgroup.zpowers (π ⟨b, hbL⟩) = centerOf P := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbP) ?_
      rw [hZP2, Nat.card_zpowers]
      have h1 : orderOf (π ⟨b, hbL⟩) ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
      have h2 := orderOf_pos (π ⟨b, hbL⟩)
      omega
    apply hCY.not_ge
    intro y hy
    obtain ⟨m, hm, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ Subgroup.zpowers (π ⟨b, hbL⟩) := hzp ▸ hWle hw
    have hmz : (m : G) * z = z * (m : G) := Subgroup.mem_centralizer_singleton_iff.mp (hMLz hm)
    have hbm : b * (m : G) * b⁻¹ = (m : G) := by
      rw [← hbe (m : G) m.2]
      calc z * (m : G) * z⁻¹ = (m : G) * z * z⁻¹ := by rw [hmz]
        _ = (m : G) := by group
    have hbm' : (⟨b, hbL⟩ : ↥L) * m = m * ⟨b, hbL⟩ := by
      apply Subtype.ext
      show b * (m : G) = (m : G) * b
      calc b * (m : G) = (b * (m : G) * b⁻¹) * b := by group
        _ = (m : G) * b := by rw [hbm]
    have hcomm : Commute (π ⟨b, hbL⟩) (π m) := by
      show π ⟨b, hbL⟩ * π m = π m * π ⟨b, hbL⟩
      rw [← map_mul, ← map_mul, hbm']
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (hcomm.zpow_left k).eq
  exact false_of_block_not_centralizing hc hx.mz_normal hKc hKM hKn hzZ hKz

end CFSG.Quasithin.S151S9U
