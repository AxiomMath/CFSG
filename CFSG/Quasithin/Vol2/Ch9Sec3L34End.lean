module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Stab
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Out
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Facts
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Res
public import CFSG.Quasithin.Vol2.Ch9Lem935
public import CFSG.Quasithin.Vol2.Ch9Lem934
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Branch

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace L34

theorem m23_of_embLoc (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (h312 : A312ForSQTK) {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
    (hSL : IsSL3Ch5 2 (O2Q K)) : IsSporadic .M23 ↥(modO2Image X Kh) := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  obtain ⟨Y, _, _, _, ψ, hψ, hY, hQ⟩ := exists_psl3_quotient le_rfl hSL
  have hYab := Vol2.Ch11.SecB.nonabelian_of_perfect_surjective ψ hψ
  rcases l.cases h312 with hc | hnq
  · exact Vol2.Ch11.SecB.m23_of_case_of_l34 hYab (isPGroup_openPCore K) hQ ψ hψ hY hM
      (barMap l.le_X) (barMap_surjective _) hc
  · exact (Vol2.Ch11.SecB.false_of_a312Nonquasi (k := 2) le_rfl (Or.inr (Or.inr (Or.inl hY))) hQ
      ψ hψ l.bar_lt.le (barMap l.le_X) (barMap_surjective _) hnq).elim

theorem mem_normalizer_map_subtype {X : Subgroup G} {N : Subgroup ↥X} (hN : N.Normal)
    {x : G} (hx : x ∈ X) : x ∈ Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall fun v hv => ?_
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  exact ⟨⟨x, hx⟩ * w * ⟨x, hx⟩⁻¹, hN.conj_mem w hw ⟨x, hx⟩, rfl⟩

end L34

variable {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem false_of_l34_push
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (hM23i : FactM23L34Inner)
    (h312 : A312ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementC)
    (h331 : Stmt3_3_1) (h3108 : Stmt3_2_10_eight) (h2 : n = 2) {H K B D : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn2 : E1.nParam H = 2) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K))
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hPush : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfsu := S.hyp.fsu
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hDM₀ : D ≤ M₀ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  have hKM₀ : K ≤ M₀ := le_sup_right
  have hKM : ¬ K ≤ fsuM T L := fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM)
  have hM₀M : ¬ M₀ ≤ fsuM T L := fun h => hKM (hKM₀.trans h)
  have hsyl := S.lem934 h37 h38 h37c h38c h3108 hLM₀ hT₁M₀ hPush hM₀M
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  have hBK' : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K := by
    rw [← hBD]
    exact hBK
  obtain ⟨K₀, hK₀c, hLK₀, hKK₀, hM₀K₀⟩ :=
    S.exists_K0 h37 h38 h39 h37c h38c h2 hKl hD hBK' hPush hsyl
  have hmax := S.isMaximalLocal_of_l34 hM hM23 h312 h37c hE22 h331 hH hn1 hHK hKc hTK hJ hKL
  have hlt : K < K₀ := by
    refine lt_of_le_of_ne hKK₀ fun heq => ?_
    have hLK : L ≤ K := heq ▸ hLK₀
    have hKL' : K = L := hfsu.maximal.2 K hmax.1 hLK
    exact hKM (hKL' ▸ S.L_le_fsuM)
  have hKl₁ : K ∈ lFamily T₁ :=
    cComp_mem_of_le (X := K ⊔ T) hKl le_sup_left (sup_le_sup_left inf_le_left K)
  have : IsSimpleGroup G := hfsu.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1
  have l : EmbLoc G T₁ M₀ K K₀ :=
    { simple := hfsu.simple
      nonabelian := hfsu.nonabelian
      qtke := hfsu.qtke
      pCoreX := hPush
      sylowX := hsyl
      le_X := hKM₀
      mem_lFamily := hKl₁
      normalizes := inf_le_left.trans hTK
      hat := ⟨hK₀c, hKK₀, fun Y hY hKY =>
        Vol2Native.lemma_1_2_4_unique hloc h37c hPush hKl₁ hY hK₀c hKY hKK₀⟩
      lt := hlt }
  have hPSL := L34.isPSL_of_star hKH hJ hKL
  have hSL := L34.isSL3Ch5_of_star hKH hJ hKL
  have hM23L := L34.m23_of_embLoc hM h312 l hSL
  obtain ⟨eB⟩ := l.bar_equiv
  have hSLb : IsSL3Ch5 2 (ModO2 (modO2Image M₀ K)) := IsSL3Ch5.of_mulEquiv eB hSL
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M₀) with hπ
  have hRL : o2Img M₀ D ≤ Subgroup.normalizer ((modO2Image M₀ K₀ : Subgroup (O2Q M₀)) :
      Set (O2Q M₀)) := A7.map_le_normalizer_modO2Image (hDM₀.trans hM₀K₀)
  have hRA : o2Img M₀ D ≤ Subgroup.normalizer ((modO2Image M₀ K : Subgroup (O2Q M₀)) :
      Set (O2Q M₀)) := A7.map_le_normalizer_modO2Image hDK
  have hRodd : Odd (Nat.card (o2Img M₀ D)) := by
    refine hD.2.1.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM₀).toEquiv]
  have hinner := hM23i (O2Q M₀) (modO2Image M₀ K₀) (modO2Image M₀ K) (o2Img M₀ D) hM23L
    (Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr
      (hKK₀ (Subgroup.mem_subgroupOf.mp hx))) hSLb hRL hRA hRodd
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  have hDK' : ¬ D ≤ K := by
    intro hle
    have h9 : 9 ∣ Nat.card D := by
      have h1 := Subgroup.card_map_dvd (D.subgroupOf (fsuL0 T L)) ψ
      rw [hdiag, Nat.card_congr ((diagT F).prodEquiv (diagT F)).toEquiv, Nat.card_prod,
        card_diagT, hc.natCard, h2,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv] at h1
      norm_num at h1
      exact h1
    have hDHM : D ≤ H ⊓ fsuM T L := le_inf (hle.trans hKH) (hDL.trans Setup.L0_le_fsuM)
    have h1 : Nat.card D ∣ Nat.card ↥(H ⊓ fsuM T L) := Subgroup.card_dvd_of_le hDHM
    obtain ⟨k, hk⟩ := hB.2.2
    have h3 := Subgroup.relIndex_mul_card (H := B) (K := H ⊓ fsuM T L)
    rw [inf_eq_left.mpr hB.1, hk, hB3] at h3
    have h4 : 3 * 3 ∣ 2 ^ k * 3 := h3 ▸ h9.trans h1
    have h5 : 3 ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h4
    have h6 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    norm_num at h6
  obtain ⟨d, hdD, hdK⟩ := Set.not_subset.mp hDK'
  have hdM₀ : d ∈ M₀ := hDM₀ hdD
  have hd3 : d ^ 3 = 1 := hc.pow_three_eq_one h37c h38c h2 hD hdiag hdD
  obtain ⟨ab, hab, habx⟩ := hinner (π ⟨d, hdM₀⟩) ⟨⟨d, hdM₀⟩, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
  obtain ⟨a', ha'K, rfl⟩ := Subgroup.mem_map.mp hab
  rw [← hπ] at habx
  have haK : (a' : G) ∈ K := Subgroup.mem_subgroupOf.mp ha'K
  set a : G := (a' : G) with ha
  set c : G := a⁻¹ * d with hcdef
  have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer haK))
      (hDK hdD)
  have hcK : c ∉ K := fun h => hdK (by simpa [hcdef] using K.mul_mem haK h)
  set O₀ : Subgroup G := (CFSG.pCore 2 ↥M₀).map M₀.subtype with hO₀
  have hO₀2 : IsPGroup 2 O₀ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M₀)).map _
  have hP₀ : O₀ ⊓ K ≤ pCoreOf 2 K := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right (fun k hk => ?_)
      (hO₀2.to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨L34.mem_normalizer_map_subtype CFSG.pCore_normal (hKM₀ hk), Subgroup.le_normalizer hk⟩
  have hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro k hk
    have hkM : k ∈ M₀ := hKM₀ hk
    have h1 := habx (π ⟨k, hkM⟩) ⟨⟨k, hkM⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h2 : π (a'⁻¹ * ⟨d, hdM₀⟩ * ⟨k, hkM⟩ * (a'⁻¹ * ⟨d, hdM₀⟩)⁻¹ * (⟨k, hkM⟩ : ↥M₀)⁻¹) = 1 := by
      have e2 : π (a'⁻¹ * ⟨d, hdM₀⟩ * ⟨k, hkM⟩ * (a'⁻¹ * ⟨d, hdM₀⟩)⁻¹ * (⟨k, hkM⟩ : ↥M₀)⁻¹) =
          (π a')⁻¹ * (π ⟨d, hdM₀⟩ * π ⟨k, hkM⟩ * (π ⟨d, hdM₀⟩)⁻¹) * π a' * (π ⟨k, hkM⟩)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [e2, h1]
      group
    have h3 : (a'⁻¹ * ⟨d, hdM₀⟩ * ⟨k, hkM⟩ * (a'⁻¹ * ⟨d, hdM₀⟩)⁻¹ * (⟨k, hkM⟩ : ↥M₀)⁻¹ : ↥M₀) ∈
        CFSG.pCore 2 ↥M₀ := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : c * k * c⁻¹ * k⁻¹ ∈ O₀ := ⟨_, h3, rfl⟩
    have h5 : c * k * c⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN k).mp hk) (K.inv_mem hk)
    exact hP₀ ⟨h4, h5⟩
  have hcO : c ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcN
  have hOK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hc3K : c ^ 3 ∈ K := by
    have h1 := hOK (hcc a haK)
    have h2 := hOK (L34.pow_comm_mem hcO hcc 2 a haK)
    have e3 : c ^ 3 = (a * (c * a * c⁻¹ * a⁻¹) * a * (c ^ 2 * a * (c ^ 2)⁻¹ * a⁻¹) * a)⁻¹ *
        ((a * c) * (a * c) * (a * c)) := by group
    have had : a * c = d := by rw [hcdef, mul_inv_cancel_left]
    rw [e3, had, (pow_three' d).symm.trans hd3, mul_one]
    exact K.inv_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem haK h1) haK) h2) haK)
  have hc3 : c ^ 3 ∈ pCoreOf 2 K :=
    L34.mem_pCoreOf_of_centralizes hPSL hc3K (L34.pow_comm_mem hcO hcc 3)
  have hr := L34.three_le_pRank_of_centralizes hPSL hcN hc3 hcK hcc
  have hcM₀ : c ∈ M₀ := M₀.mul_mem (M₀.inv_mem (hKM₀ haK)) hdM₀
  have hle : K ⊔ Subgroup.zpowers c ≤ M₀ := sup_le hKM₀ (Subgroup.zpowers_le.mpr hcM₀)
  have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
  have h2 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hfsu.qtke hPush Nat.prime_three
    (by norm_num)
  omega

end Setup

theorem ch9L34Branch_of
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (hM23i : FactM23L34Inner)
    (h312 : A312ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementC)
    (h331 : Stmt3_3_1) (hC58 : TheoremC58) (h317 : AS317Sylow) (h3108 : Stmt3_2_10_eight)
    (hStab : Ch9L34Stab) (hPush : Ch9L34Push) : Ch9L34Branch := by
  intro G _ _ T L I S h1 H K B D hH hn2 hHK hKc hTK hJ hKL hB hBK hB3 hBTK hD hBD
  have hSt := hStab G T L I S h1 H K B D hH hn2 hHK hKc hTK hJ hKL hB hBK hB3 hBTK hD hBD
  obtain ⟨hDK, hKV⟩ := S.normalizer_of_l34 hM hM23 h312 h37c h38c h37 h38 h39 hE22 h331 hC58
    h317 rfl h1 hH hn2 hHK hKc hTK hJ hKL hBK hB3 hBTK hD hBD hSt
  have hP := hPush G T L I S h1 H K B D hH hn2 hHK hKc hTK hJ hKL hB hBK hB3 hBTK hD hBD hSt hDK
    hKV
  exact S.false_of_l34_push hM hM23 hM23i h312 h37c h38c h37 h38 h39 hE22 h331 h3108 rfl hH hn2
    hHK hKc hTK hJ hKL hB hBK hB3 hD hBD hDK hP

end CFSG.Quasithin.H13.Ch9
