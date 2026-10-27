module

public import CFSG.Quasithin.EmptyFaithful.S151YC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem star_general (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    {H : Subgroup G} (hSH' : s1516 T Z₁ ≤ H) (hHG : H ≤ g1_1516 Z₁)
    (hchar : CharTwo H) (hmin : IsMinParabolicOf H H) (hno3 : ¬ C126Third H (s1516 T Z₁)) :
    H ≤ M ∨ H ≤ mZ1516 Mc Z₁ := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hSH : IsSylowTwoOf S H := ya7_isSylowTwoOf_restrict hc.h18.four hSH' hHG
  have hpc : pCoreOf 2 H ≠ ⊥ := by
    have h1 : pCoreOf 2 (g1_1516 Z₁) ≤ S := hc.h18.four.pCoreOf_le
    have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans hSH')
        (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (g1_1516 Z₁)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (g1_1516 Z₁))
    exact ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) h2
  have hSQ : IsSQTKTC H :=
    ⟨kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc,
      stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hS2 : IsPGroup 2 S := hSH.2.1
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hT0 : T ≠ ⊥ := ne_bot_of_le_ne_bot hSet.z1_ne hZ₁T
  have hST : S ≤ T := s1516_le T Z₁
  obtain ⟨h1ne, h1Z, -⟩ := hC.pair T hT2 hT0
  have hC1T : C₁ T ≤ centerOf T := h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)
  have hcTS : centerOf T ≤ S := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.2 y (hZ₁T hy)⟩
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot h1ne (hC1T.trans hcTS)
  have hcTcS : centerOf T ≤ centerOf S := fun z hz =>
    ⟨hcTS hz, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hz.2⟩
  have hc1S : C₁ T ≤ C₁ S := by
    rw [hC.c1_eq T hT2 hT0, hC.c1_eq S hS2 hS0, hc.h17.baumS]
    exact inf_le_inf hcTcS le_rfl
  rcases h126 G C₁ C₂ hC H S hSQ hSH hchar hmin with h1 | h2 | h3
  ·
    right
    have hHc : ∀ y ∈ C₁ S, ∀ h ∈ H, y * h = h * y := fun y hy h hh =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy).2 h hh).symm
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1ne
    have hzZ : (z : G) ∈ quasithinOmegaOneCenter T := h1Z z.2
    have hzC : (z : G) ∈ C₁ S := hc1S z.2
    intro h hh
    have hhC : h ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hHc (z : G) hzC h hh
    exact ⟨hHG hh, ya7_centralizer_le_mc hq hzZ (fun h => hz1 (Subtype.ext h)) hhC⟩
  ·
    left
    obtain ⟨-, -, -, h2ne, h2B, h2char, -⟩ := hC.pair S hS2 hS0
    have hNle : Subgroup.normalizer (C₂ S : Set G) ≤ M := by
      refine le_trans ?_ hc.h17.cgs
      exact le_iSup_of_le (C₂ S) (le_iSup_of_le h2B (le_iSup_of_le h2ne
        (le_iSup_of_le h2char le_rfl)))
    exact fun h hh => hNle (h2 hh)
  · exact (hno3 h3).elim

@[expose] def ZL2 (S L : Subgroup G) : Prop :=
  ∀ a b : G, a ∈ S → b ∈ S →
    a ∉ Subgroup.centralizer (L : Set G) → a ^ 2 ∈ Subgroup.centralizer (L : Set G) →
    (∀ c ∈ S, ⁅a, c⁆ ∈ Subgroup.centralizer (L : Set G)) →
    b ∉ Subgroup.centralizer (L : Set G) → b ^ 2 ∈ Subgroup.centralizer (L : Set G) →
    (∀ c ∈ S, ⁅b, c⁆ ∈ Subgroup.centralizer (L : Set G)) →
    a⁻¹ * b ∈ Subgroup.centralizer (L : Set G)

omit [Finite G] in
theorem centralizer_inf_normal {S L : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    ((S ⊓ Subgroup.centralizer (L : Set G)).subgroupOf S).Normal := by
  refine ⟨fun n hn s => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨S.mul_mem (S.mul_mem s.2 hn.1) (S.inv_mem s.2), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro l hl
  have hl' : (s : G)⁻¹ * l * (s : G) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hSN s.2)) l).mp hl
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hn.2 _ hl'
  calc l * ((s : G) * n * (s : G)⁻¹) = (s : G) * (((s : G)⁻¹ * l * (s : G)) * n) * (s : G)⁻¹ := by
        group
    _ = (s : G) * (n * ((s : G)⁻¹ * l * (s : G))) * (s : G)⁻¹ := by rw [hc]
    _ = ((s : G) * n * (s : G)⁻¹) * l := by group

theorem centS_of_zl2 {S Z X L : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hS2 : IsPGroup 2 ↥S) (hXL : X ≤ L) (hSX : S ≤ Subgroup.normalizer (X : Set G))
    (hZS : Z ≤ S) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (hZc : ∀ z ∈ Z, ∀ c ∈ S, z * c = c * z)
    (hzl : ZL2 S L) (hX : ¬ ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x) :
    S ⊓ Subgroup.centralizer (X : Set G) = S ⊓ Subgroup.centralizer (L : Set G) := by
  classical
  apply le_antisymm _ (inf_le_inf_left S (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXL)))
  intro d hd
  by_contra hdL
  have hdL' : d ∉ Subgroup.centralizer (L : Set G) := fun h => hdL ⟨hd.1, h⟩
  set N : Subgroup ↥S := (S ⊓ Subgroup.centralizer (L : Set G)).subgroupOf S with hN
  have hNn : N.Normal := centralizer_inf_normal hSN
  set D' : Subgroup ↥S := (S ⊓ Subgroup.centralizer (X : Set G)).subgroupOf S with hD'
  have hD'n : D'.Normal := by
    refine ⟨fun n hn s => ?_⟩
    rw [hD', Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨S.mul_mem (S.mul_mem s.2 hn.1) (S.inv_mem s.2), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hx' : (s : G)⁻¹ * x * (s : G) ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hSX s.2)) x).mp hx
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hn.2 _ hx'
    calc x * ((s : G) * n * (s : G)⁻¹) = (s : G) * (((s : G)⁻¹ * x * (s : G)) * n) * (s : G)⁻¹ := by
          group
      _ = (s : G) * (n * ((s : G)⁻¹ * x * (s : G))) * (s : G)⁻¹ := by rw [hc]
      _ = ((s : G) * n * (s : G)⁻¹) * x := by group
  let π : ↥S →* ↥S ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hp : IsPGroup 2 (↥S ⧸ N) := hS2.of_surjective π hπ
  have hnil : Group.IsNilpotent (↥S ⧸ N) := hp.isNilpotent
  set Db : Subgroup (↥S ⧸ N) := D'.map π with hDb
  have hDbn : Db.Normal := Subgroup.Normal.map hD'n π hπ
  have hdD' : (⟨d, hd.1⟩ : ↥S) ∈ D' := Subgroup.mem_subgroupOf.mpr hd
  have hdN : (⟨d, hd.1⟩ : ↥S) ∉ N := fun h => hdL' (Subgroup.mem_subgroupOf.mp h).2
  have hDb_ne : Db ≠ ⊥ := by
    intro h
    have : π ⟨d, hd.1⟩ ∈ Db := Subgroup.mem_map_of_mem _ hdD'
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hdN this
  obtain ⟨ā, hāDb, hācenter⟩ : ∃ ā, ā ∈ Db ∧ ā ∈ Subgroup.center (↥S ⧸ N) ∧ ā ≠ 1 := by
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hDb_ne
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    exact ⟨(a : ↥S ⧸ N), a.2.1, a.2.2, fun h' => ha1 (Subtype.ext h')⟩
  obtain ⟨hāc, hā1⟩ := hācenter
  obtain ⟨k, hk⟩ := hp ā
  have hex : ∃ m : ℕ, ā ^ 2 ^ m = 1 := ⟨k, hk⟩
  classical
  set m := Nat.find hex with hm
  have hm1 : ā ^ 2 ^ m = 1 := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hm1
    exact hā1 hm1
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hm'min : ā ^ 2 ^ m' ≠ 1 := Nat.find_min hex (by omega)
  set bq := ā ^ 2 ^ m' with hbq
  have hbqsq : bq ^ 2 = 1 := by
    rw [hbq, ← pow_mul, ← pow_succ]
    rw [hm', ] at hm1
    exact hm1
  have hbqD : bq ∈ Db := Subgroup.pow_mem _ hāDb _
  have hbqc : bq ∈ Subgroup.center (↥S ⧸ N) := Subgroup.pow_mem _ hāc _
  obtain ⟨b₀, hb₀D, hb₀⟩ := Subgroup.mem_map.mp hbqD
  have hbS : (b₀ : G) ∈ S := b₀.2
  have hbX : (b₀ : G) ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_subgroupOf.mp hb₀D).2
  have hb₀eq : (QuotientGroup.mk b₀ : ↥S ⧸ N) = bq := hb₀
  have hbL : (b₀ : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro hcl
    apply hm'min
    rw [← hb₀eq, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr ⟨hbS, hcl⟩
  have hbsq : (b₀ : G) ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : (QuotientGroup.mk (b₀ ^ 2) : ↥S ⧸ N) = 1 := by
      rw [QuotientGroup.mk_pow, hb₀eq]
      exact hbqsq
    rw [QuotientGroup.eq_one_iff] at h1
    exact (Subgroup.mem_subgroupOf.mp h1).2
  have hbcomm : ∀ c ∈ S, ⁅(b₀ : G), c⁆ ∈ Subgroup.centralizer (L : Set G) := by
    intro c hc
    have hcen := Subgroup.mem_center_iff.mp hbqc (QuotientGroup.mk (⟨c, hc⟩ : ↥S))
    have h1 : (QuotientGroup.mk (b₀ * ⟨c, hc⟩ * b₀⁻¹ * ⟨c, hc⟩⁻¹) : ↥S ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hb₀eq]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcen.symm
    rw [QuotientGroup.eq_one_iff] at h1
    exact (Subgroup.mem_subgroupOf.mp h1).2
  apply hX
  intro x hx z hz
  by_cases hzc : z ∈ Subgroup.centralizer (L : Set G)
  · exact Subgroup.mem_centralizer_iff.mp hzc x (hXL hx)
  · have hz2 : z ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
      rw [hZ2 z hz]
      exact one_mem _
    have hzcomm : ∀ c ∈ S, ⁅z, c⁆ ∈ Subgroup.centralizer (L : Set G) := by
      intro c hc
      rw [commutatorElement_def, hZc z hz c hc]
      simp
    have hw := hzl (b₀ : G) z hbS (hZS hz) hbL hbsq hbcomm hzc hz2 hzcomm
    obtain ⟨w, hw_def⟩ : ∃ w : G, w = (b₀ : G)⁻¹ * z := ⟨_, rfl⟩
    have hw' : w ∈ Subgroup.centralizer (L : Set G) := hw_def ▸ hw
    have hzw : z = (b₀ : G) * w := by rw [hw_def]; group
    have hwx : x * w = w * x := Subgroup.mem_centralizer_iff.mp hw' x (hXL hx)
    have hbx : x * (b₀ : G) = (b₀ : G) * x := Subgroup.mem_centralizer_iff.mp hbX x hx
    rw [hzw]
    calc x * ((b₀ : G) * w) = ((b₀ : G) * x) * w := by rw [← mul_assoc, hbx]
      _ = (b₀ : G) * (x * w) := by rw [mul_assoc]
      _ = (b₀ : G) * (w * x) := by rw [hwx]
      _ = (b₀ : G) * w * x := by rw [mul_assoc]

end CFSG.Quasithin
