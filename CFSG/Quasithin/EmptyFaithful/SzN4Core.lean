module

public import CFSG.Quasithin.EmptyFaithful.SzN3R
public import CFSG.Quasithin.EmptyFaithful.SzN4Aux
public import CFSG.Quasithin.EmptyFaithful.SzN3Lin2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Carrier

variable {G : Type} [Group G]

theorem szN4_conj_mem_carrier {Y L : Subgroup G} {g m : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hm : m ∈ centralizerSection Y L (pCoreOf 2 L)) :
    g * m * g⁻¹ ∈ centralizerSection Y L (pCoreOf 2 L) := by
  obtain ⟨hmY, hmL, hmQ, hmc⟩ := mem_centralizerSection.mp hm
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L hgL
  refine mem_centralizerSection.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgY m).mp hmY,
    mul_mem (mul_mem hgL hmL) (inv_mem hgL), mul_mem (mul_mem hgQ hmQ) (inv_mem hgQ), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgL) x).mp hx
    simpa using this
  have h := hmc _ hx'
  have e : x * (g * m * g⁻¹) * x⁻¹ * (g * m * g⁻¹)⁻¹ =
      g * ((g⁻¹ * x * g) * m * (g⁻¹ * x * g)⁻¹ * m⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hgQ _).mp h

end Carrier

section YLStructure

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem szN4_YL_structure (h113 : StageLemma14113) (hyp : Hyp153 G T Mc M) {hV : IsElemAbelian 2 (VZ T M)}
    {La Lb : Subgroup (MulAut (IntMod (VZ T M) hV))} {tb : MulAut (IntMod (VZ T M) hV)}
    (hS : OfourStruct (autI hV M) La Lb tb) {Va : Subgroup G}
    (hVa : Va = (commV La).map (inclMod hV)) {L : Subgroup G}
    (hcore : pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))
    (hYNL : Y153 Mc M ≤ Subgroup.normalizer (L : Set G))
    (hYLne : YL153 (Y153 Mc M) L ≠ ⊥)
    (hYLa : YL153 (Y153 Mc M) L ≤ Subgroup.centralizer (Va : Set G)) :
    autI hV (YL153 (Y153 Mc M) L) = Lb ⊓ oTwoUpper (autI hV M) ∧
      YL153 (Y153 Mc M) L = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (Va : Set G)) := by
  classical
  subst hVa
  have hMN := hyp.le_normalizer
  set Y := Y153 Mc M with hY
  set YL := YL153 Y L with hYL
  set X := autI hV M with hX
  have hYM : Y ≤ M := Y153_le Mc M
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hYe : autI hV Y = oTwoUpper X := hyp.autOn_Y153 h113
  have hYLle : YL ≤ Y ⊓ L := oTwoUpper_le _
  have hYLY : YL ≤ Y := hYLle.trans inf_le_left
  have hYLL : YL ≤ L := hYLle.trans inf_le_right
  have hYNYL : Y ≤ Subgroup.normalizer (YL : Set G) := fun g hg =>
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hYNL hg⟩)
  obtain ⟨y, hyY, hyo, hy1⟩ : ∃ y ∈ Y ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hYLne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  have hyYL : y ∈ YL := mem_oTwoUpper_of_odd hyY hyo
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hyY.1
  have hconv1 : convI hV ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 h1
    have hyP : y ∈ pCoreOf 2 Y := by rw [hcore]; exact ⟨hyY.1, hyC⟩
    exact hy1 (S153F.eq_one_of_mem_pCoreOf_of_odd hyP hyo)
  have hautL_le : autI hV YL ≤ Lb ⊓ oTwoUpper X := by
    intro φ hφ
    obtain ⟨g, hgYL, rfl⟩ := (mem_autI hV).1 hφ
    have hφY : convI hV g ∈ autI hV Y := convI_mem_autI hV (hYLY hgYL) g.2
    rw [hYe] at hφY
    have hφX : convI hV g ∈ X := oTwoUpper_le _ hφY
    refine ⟨(hS.mem_L₂_iff hφX).2 fun u hu => ?_, hφY⟩
    exact (mem_centralizer_map_inclMod_iff hV g.2 (commV La)).1 (hYLa hgYL) u hu
  have hbotL : autI hV YL ≠ ⊥ := by
    intro hb
    have : convI hV ⟨y, hyN⟩ ∈ autI hV YL := convI_mem_autI hV hyYL hyN
    rw [hb, Subgroup.mem_bot] at this
    exact hconv1 this
  have hautL : autI hV YL = Lb ⊓ oTwoUpper X :=
    szN3_eq_of_le_of_ne_bot hautL_le hbotL (szN3_card_inf_oTwoUpper_dvd hS)
  refine ⟨hautL, ?_⟩
  have hKle : pCoreOf 2 Y ≤ Y ⊓ Subgroup.centralizer (((commV La).map (inclMod hV) : Subgroup G) : Set G) := by
    rw [hcore]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (map_inclMod_le hV _))
  refine le_antisymm (szN3_oTwoUpper_le_oTwoUpper (le_inf hYLY hYLa)) ?_
  refine szN3_oTwoUpper_le_of_decomp (inf_le_left.trans hYNYL) (pCoreOf_isPGroup 2 Y) hKle
    (szN3_decomp (hV := hV) hYN hcore hYLY inf_le_left ?_)
  intro z hz
  have hzN : z ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hz.1
  have hzy : convI hV ⟨z, hzN⟩ ∈ autI hV Y := convI_mem_autI hV hz.1 hzN
  rw [hYe] at hzy
  have hzX : convI hV ⟨z, hzN⟩ ∈ X := oTwoUpper_le _ hzy
  rw [hautL]
  exact ⟨(hS.mem_L₂_iff hzX).2 fun u hu =>
    (mem_centralizer_map_inclMod_iff hV hzN (commV La)).1 hz.2 u hu, hzy⟩

end YLStructure


section Core

variable {G : Type} [Group G] [Finite G]

theorem szN4_core (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (kS : Lin2Setup) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) (hsh : IsShort2 L)
    (hYY : Yp = Y153 Mc M)
    {hV : IsElemAbelian 2 (VZ T M)} {La Lb : Subgroup (MulAut (IntMod (VZ T M) hV))}
    {tb : MulAut (IntMod (VZ T M) hV)} (hS : OfourStruct (autI hV M) La Lb tb) {Va Vb : Subgroup G}
    (hVa : Va = (commV La).map (inclMod hV)) (hVb : Vb = (commV Lb).map (inclMod hV))
    (hSVa : Sgp153 T V₁ ≤ Subgroup.normalizer (Va : Set G))
    (hSlift : ∀ g : G, g ∈ T → ∀ hgN : g ∈ Subgroup.normalizer (VZ T M : Set G),
      convI hV ⟨g, hgN⟩ ∈ La ⊔ Lb → g ∈ Sgp153 T V₁)
    (hYLa : YL153 Yp L ≤ Subgroup.centralizer (Va : Set G)) :
    YC153 Yp L ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  obtain ⟨-, hE9, hVdec⟩ := kS G T Mc M V₁ V₂ Yp I L t ctx hn
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hYNL : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 hh ctx.ctx.inH hLI
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  subst hYY
  have hcore := szN3_core_eq h113 hh.hyp hE9
  have hMN := hh.hyp.le_normalizer
  obtain ⟨hautL, hYLeq⟩ := szN4_YL_structure h113 hh.hyp hS hVa hcore hYNL ctx.c16.YL_ne hYLa
  set Y := Y153 Mc M with hY
  have hYM : Y ≤ M := Y153_le Mc M
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hYe : autI hV Y = oTwoUpper (autI hV M) := hh.hyp.autOn_Y153 h113
  have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Y L : Set G) := by
    rw [hYLeq]
    exact szN3_S_le_normalizer_oTwoUpper hh.hyp inf_le_left hSVa
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    szN3_S_le_normalizer_L h37 h38 ctx hSYL
  have hST : Sgp153 T V₁ ≤ T := inf_le_left
  have hSY : Sgp153 T V₁ ≤ Subgroup.normalizer (Y : Set G) := fun s hs =>
    le_normalizer_Y153 Mc M (hh.hyp.T_le (hST hs))
  obtain ⟨n, -, hnL⟩ := hn
  have hVbV : Vb ≤ VZ T M := by rw [hVb]; exact map_inclMod_le hV _
  have hVL : VZ T M ≤ Subgroup.normalizer (L : Set G) := szN3_VZ_le_normalizer_L ctx
  obtain ⟨y₀, hy₀Y, hy₀o, hy₀1⟩ : ∃ y ∈ Y ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    apply ctx.c16.YL_ne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  have hy₀YL : y₀ ∈ YL153 Y L := mem_oTwoUpper_of_odd hy₀Y hy₀o
  have hy₀N : y₀ ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hy₀Y.1
  have hy₀1' : convI hV ⟨y₀, hy₀N⟩ ≠ 1 := by
    intro h1
    have hyC : y₀ ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 h1
    have hyP : y₀ ∈ pCoreOf 2 Y := by rw [hcore]; exact ⟨hy₀Y.1, hyC⟩
    exact hy₀1 (S153F.eq_one_of_mem_pCoreOf_of_odd hyP hy₀o)
  have hy₀Lb : convI hV ⟨y₀, hy₀N⟩ ∈ Lb ⊓ oTwoUpper (autI hV M) := by
    rw [← hautL]; exact convI_mem_autI hV hy₀YL hy₀N
  have hy₀odd : Odd (orderOf (convI hV ⟨y₀, hy₀N⟩)) :=
    Odd.of_dvd_nat (by decide : Odd 3)
      (orderOf_dvd_of_pow_eq_one (hS.pow_three_of_mem_oTwoUpper hy₀Lb.2))
  have hVbL : ∃ v ∈ Vb, v ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hno
    push Not at hno
    have hyC : y₀ ∈ Subgroup.centralizer (Vb : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hno v hv) y₀ hy₀Y.2).symm
    rw [hVb] at hyC
    have hfix := (mem_centralizer_map_inclMod_iff hV hy₀N (commV Lb)).1 hyC
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ commV Lb, u ≠ 1 := by
      by_contra hu
      push Not at hu
      have hbot : commV Lb = ⊥ := by
        rw [eq_bot_iff]; exact fun u hu' => Subgroup.mem_bot.mpr (hu u hu')
      have h4 := (card_of_actsAsNaturalL2 hS.nat₂).2
      rw [hbot] at h4
      simp at h4
    exact hy₀1' (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable Lb hl hu) hy₀Lb.1
      hy₀odd hu hu1 (hfix u hu))
  have hodd : ∀ c ∈ centralizerSection Y L (pCoreOf 2 L), Odd (orderOf c) →
      c ∈ Subgroup.centralizer (L : Set G) := by
    intro c hc hco
    obtain ⟨hcY, hcN, hcQN, hcc⟩ := mem_centralizerSection.mp hc
    have hcNV : c ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hcY
    have hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
      intro x hx
      have := inv_mem (hcc x hx)
      have e : (x * c * x⁻¹ * c⁻¹)⁻¹ = c * x * c⁻¹ * x⁻¹ := by group
      rwa [e] at this
    have hcbar : convI hV ⟨c, hcNV⟩ ∈ oTwoUpper (autI hV M) := by
      have := convI_mem_autI hV hcY hcNV
      rwa [hYe] at this
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_mul_of_mem_sup_of_commute hS.comm (hS.oTwoUpper_le_sup hcbar)
    have hcomm : Commute a b := hS.comm a ha b hb
    have hcube : a ^ 3 * b ^ 3 = 1 := by
      rw [← hcomm.mul_pow, hab]; exact hS.pow_three_of_mem_oTwoUpper hcbar
    have ha3 : a ^ 3 = 1 := by
      have : a ^ 3 ∈ La ⊓ Lb := ⟨La.pow_mem ha 3, by
        rw [eq_inv_of_mul_eq_one_left hcube]
        exact Lb.inv_mem (Lb.pow_mem hb 3)⟩
      rw [hS.Linf, Subgroup.mem_bot] at this
      exact this
    have hb3 : b ^ 3 = 1 := by
      rw [ha3, one_mul] at hcube
      exact hcube
    have hE1 : ∀ z ∈ centralizerSection Y L (pCoreOf 2 L),
        ∀ hzN : z ∈ Subgroup.normalizer (VZ T M : Set G),
          convI hV ⟨z, hzN⟩ ∈ Lb → convI hV ⟨z, hzN⟩ = 1 := by
      intro z hz hzN hzLb
      obtain ⟨hzY, hzL, -, hzc⟩ := mem_centralizerSection.mp hz
      have hzQ : ∀ x ∈ L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
        intro x hx
        have := inv_mem (hzc x hx)
        have e : (x * z * x⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * x⁻¹ := by group
        rwa [e] at this
      have hzbar : convI hV ⟨z, hzN⟩ ∈ oTwoUpper (autI hV M) := by
        have := convI_mem_autI hV hzY hzN
        rwa [hYe] at this
      have hzYL : convI hV ⟨z, hzN⟩ ∈ autI hV (YL153 Y L) := by
        rw [hautL]; exact ⟨hzLb, hzbar⟩
      obtain ⟨y₁, hy₁YL, hy₁eq⟩ := (mem_autI hV).1 hzYL
      have hy₁L : (y₁ : G) ∈ L := ((oTwoUpper_le _).trans inf_le_right) hy₁YL
      have hy₁Y : (y₁ : G) ∈ Y := ((oTwoUpper_le _).trans inf_le_left) hy₁YL
      have hwC : (y₁ : G) * z⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
        have h1 : convI hV (y₁ * ⟨z, hzN⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, hy₁eq, mul_inv_cancel]
        exact (convI_eq_one_iff hV _).1 h1
      have hwP : (y₁ : G) * z⁻¹ ∈ pCoreOf 2 Y := by
        rw [hcore]; exact ⟨Y.mul_mem hy₁Y (Y.inv_mem hzY), hwC⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hwP⟩
      have hwk : ((y₁ : G) * z⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨j, hj⟩ := szN4_two_element_of_trivial_action hnL hy₁L hzL hzQ hwk
      have h2 : (convI hV ⟨z, hzN⟩) ^ 2 ^ j = 1 := by
        rw [← hy₁eq, ← map_pow]
        have : (y₁ ^ 2 ^ j : ↥(Subgroup.normalizer (VZ T M : Set G))) = 1 := Subtype.ext hj
        rw [this, map_one]
      have h3 : (convI hV ⟨z, hzN⟩) ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hzbar
      have hd1 : orderOf (convI hV ⟨z, hzN⟩) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
      have hd2 : orderOf (convI hV ⟨z, hzN⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
      have : orderOf (convI hV ⟨z, hzN⟩) ∣ Nat.gcd 3 (2 ^ j) := Nat.dvd_gcd hd2 hd1
      rw [hcop] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
    have hb1 : b = 1 := by
      by_contra hb1
      obtain ⟨z, hz, hzN, hzLb, hz1⟩ : ∃ z ∈ centralizerSection Y L (pCoreOf 2 L),
          ∃ hzN : z ∈ Subgroup.normalizer (VZ T M : Set G),
            convI hV ⟨z, hzN⟩ ∈ Lb ∧ convI hV ⟨z, hzN⟩ ≠ 1 := by
        by_cases ha1 : a = 1
        · refine ⟨c, hc, hcNV, ?_, ?_⟩
          · rw [← hab, ha1, one_mul]; exact hb
          · rw [← hab, ha1, one_mul]; exact hb1
        · obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hh.hyp.isSylowTwoOf_autI
          have hs₁L : s₁ ∈ La := hF.sylow.s₁_mem_L
          have hs₁T : s₁ ∈ autI hV T ⊓ (La ⊔ Lb) := hF.sylow.s₁_mem_S
          obtain ⟨g, hgT, hg⟩ := (mem_autI hV).1 hs₁T.1
          have hgS : (g : G) ∈ Sgp153 T V₁ := by
            refine hSlift g hgT g.2 ?_
            have h' : convI hV ⟨(g : G), g.2⟩ = s₁ := hg
            rw [h']; exact hs₁T.2
          have hscs : (g : G) * c * (g : G)⁻¹ ∈ centralizerSection Y L (pCoreOf 2 L) :=
            szN4_conj_mem_carrier (hSY hgS) (hSL hgS) hc
          have hz : c * ((g : G) * c * (g : G)⁻¹) ∈ centralizerSection Y L (pCoreOf 2 L) :=
            mul_mem hc hscs
          have hzN : c * ((g : G) * c * (g : G)⁻¹) ∈ Subgroup.normalizer (VZ T M : Set G) :=
            mul_mem hcNV (mul_mem (mul_mem g.2 hcNV) (inv_mem g.2))
          have himg : convI hV ⟨c * ((g : G) * c * (g : G)⁻¹), hzN⟩ = b * b := by
            have e : (⟨c * ((g : G) * c * (g : G)⁻¹), hzN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) =
                ⟨c, hcNV⟩ * (g * ⟨c, hcNV⟩ * g⁻¹) := rfl
            rw [e, map_mul, map_mul, map_mul, map_inv, hg, ← hab]
            have hinv : s₁ * a * s₁⁻¹ = a⁻¹ :=
              OfourStruct.conj_inv_cube hS.nat₁ hs₁L (by rw [pow_two]; exact hF.s₁_sq)
                hF.sylow.s₁_ne ha ha3
            have hcb : s₁ * b * s₁⁻¹ = b := by
              rw [hS.comm s₁ hs₁L b hb]; group
            have h1 : s₁ * (a * b) * s₁⁻¹ = a⁻¹ * b := by
              calc s₁ * (a * b) * s₁⁻¹ = (s₁ * a * s₁⁻¹) * (s₁ * b * s₁⁻¹) := by group
                _ = a⁻¹ * b := by rw [hinv, hcb]
            rw [h1]
            have hc' : b * a⁻¹ = a⁻¹ * b := hcomm.inv_left.eq.symm
            calc a * b * (a⁻¹ * b) = a * (b * a⁻¹) * b := by group
              _ = a * (a⁻¹ * b) * b := by rw [hc']
              _ = b * b := by group
          refine ⟨_, hz, hzN, ?_, ?_⟩
          · rw [himg]; exact Lb.mul_mem hb hb
          · rw [himg]
            intro h
            apply hb1
            calc b = b ^ 3 := by
                  have : b ^ 3 = (b * b) * b := pow_three' b
                  rw [this, h, one_mul]
              _ = 1 := hb3
      exact hz1 (hE1 z hz hzN hzLb)
    have hcbar_a : convI hV ⟨c, hcNV⟩ = a := by rw [← hab, hb1, mul_one]
    have hcVb : c ∈ Subgroup.centralizer (Vb : Set G) := by
      rw [hVb]
      exact (mem_centralizer_map_inclMod_iff hV hcNV (commV Lb)).2 fun u hu => by
        rw [hcbar_a]; exact hS.L₁_fix₂ ha hu
    obtain ⟨v, hvVb, hvL⟩ := hVbL
    obtain ⟨a', ha', b', hb', hvab⟩ := hVdec v (hVbV hvVb)
    have hcv : c * v = v * c := Subgroup.mem_centralizer_iff.mp hcVb v hvVb |>.symm
    have hcL : c ∈ Subgroup.normalizer (L : Set G) := hcN
    refine szN4_lin2_central_of_fixed hsh hnL hperf hcL hco hcQ ⟨a', ha'.1, ?_, ?_⟩
    · intro hCa
      apply hvL
      rw [hvab]
      exact mul_mem hCa hb'
    · have hcb' : c * b' * c⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
        szN4_conj_mem_centralizer hcL hb'
      have hcv' : c * (a' * b') * c⁻¹ = a' * b' := by
        rw [hvab] at hcv
        calc c * (a' * b') * c⁻¹ = (a' * b') * c * c⁻¹ := by rw [hcv]
          _ = a' * b' := by group
      have hz : a'⁻¹ * (c * a' * c⁻¹) = b' * (c * b' * c⁻¹)⁻¹ := by
        calc a'⁻¹ * (c * a' * c⁻¹)
            = a'⁻¹ * (c * (a' * b') * c⁻¹) * (c * b' * c⁻¹)⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * (c * b' * c⁻¹)⁻¹ := by rw [hcv']
          _ = b' * (c * b' * c⁻¹)⁻¹ := by group
      have hzC : a'⁻¹ * (c * a' * c⁻¹) ∈ Subgroup.centralizer (L : Set G) := by
        rw [hz]; exact (Subgroup.centralizer (L : Set G)).mul_mem hb' ((Subgroup.centralizer (L : Set G)).inv_mem hcb')
      have ha'L : a' ∈ L := szN4_blockU_le ha'.1
      have hcomm' := Subgroup.mem_centralizer_iff.mp hzC a' ha'L
      have e : c * a' * c⁻¹ * a'⁻¹ = a'⁻¹ * (c * a' * c⁻¹) := by
        calc c * a' * c⁻¹ * a'⁻¹ = (a' * (a'⁻¹ * (c * a' * c⁻¹))) * a'⁻¹ := by group
          _ = ((a'⁻¹ * (c * a' * c⁻¹)) * a') * a'⁻¹ := by rw [hcomm']
          _ = a'⁻¹ * (c * a' * c⁻¹) := by group
      rw [e]; exact hzC
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, hxo⟩
  exact hodd x hx hxo

end Core

end CFSG.Quasithin
