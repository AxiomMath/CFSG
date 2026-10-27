module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DM

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commutator_le_UH_ch615 (T H : Subgroup G) :
    ⁅Cx615.UH T H, oTwoUpper H⁆ ≤ Cx615.UH T H := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have hkN := le_normalizer_conjClosure (quasithinOmegaOneCenter T) H (oTwoUpper_le H hk)
  rw [commutatorElement_def]
  have h1 : k * u⁻¹ * k⁻¹ ∈ Cx615.UH T H :=
    (Subgroup.mem_normalizer_iff.mp hkN _).mp (Subgroup.inv_mem _ hu)
  have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hu h1

namespace Cx615B

theorem existsUnique_ch615 (c : Cx615B G T M L V H n) :
    ∃! z : G, z ∈ ⁅Cx615.UH T H, oTwoUpper H⁆ ∧
      z ∈ Subgroup.centralizer (thompsonJ T : Set G) ∧ z ≠ 1 ∧
      ∀ g ∈ kStar615 T L H, g * z * g⁻¹ = z →
        g ∈ Subgroup.centralizer ((⁅Cx615.UH T H, oTwoUpper H⁆ : Subgroup G) : Set G) := by
  classical
  obtain ⟨w₀, ⟨hw₀Y, hw₀B, hw₀1, hw₀s⟩, huniq⟩ := c.existsUnique_mod_ch615
  have hYUH := commutator_le_UH_ch615 T H
  set UH := Cx615.UH T H with hUHdef
  set K := oTwoUpper H with hKdef
  set Y := ⁅UH, K⁆ with hYdef
  set C := cXU615 T L H with hCdef
  have hHN : H ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure _ _
  have hKH : K ≤ H := oTwoUpper_le H
  have hJH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans c.hH.1.1
  have hUHU : UH ≤ conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) :=
    conjClosure_mono le_rfl le_sup_right
  have hCY : C ≤ Subgroup.centralizer (Y : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hYUH.trans hUHU)))
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    (hKH.trans le_sup_right).trans le_normalizer_cXU615
  have hKCeq := Subgroup.coe_mul_of_left_le_normalizer_right K C hKC
  let ι : IntMod UH c.hU →* G :=
    { toFun := IntMod.val, map_one' := IntMod.val_one, map_mul' := IntMod.val_mul }
  have hι : ∀ w : IntMod UH c.hU, ι w = w.val := fun w => rfl
  have hT1 : Y = (commV (autI c.hU K)).map ι := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu k hk
      refine ⟨(convI c.hU ⟨k, hHN (hKH hk)⟩)⁻¹ (convI c.hU ⟨k, hHN (hKH hk)⟩
          (IntMod.mk c.hU ⟨u, hu⟩)) * (convI c.hU ⟨k, hHN (hKH hk)⟩ (IntMod.mk c.hU ⟨u, hu⟩))⁻¹,
        Subgroup.subset_closure ⟨_, Subgroup.inv_mem _ (convI_mem_autI c.hU hk (hHN (hKH hk))),
          _, rfl⟩, ?_⟩
      rw [MulAut.inv_apply_self, map_mul, map_inv, hι, hι, convI_apply_val,
        commutatorElement_def]
      show u * (k * u * k⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹
      group
    · rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, hx, v, rfl⟩
      obtain ⟨g, hgK, rfl⟩ := (mem_autI c.hU).mp hx
      show ι (convI c.hU g v * v⁻¹) ∈ Y
      rw [map_mul, map_inv, hι, hι, convI_apply_val, hYdef, Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator hgK v.val_mem
      rwa [commutatorElement_def] at this
  have hT2 : ∀ w : IntMod UH c.hU, w.val ∈ Subgroup.centralizer (thompsonJ T : Set G) ↔
      w ∈ fixV (autI c.hU (thompsonJ T)) := by
    intro w
    constructor
    · intro hw β hβ
      obtain ⟨g, hgJ, rfl⟩ := (mem_autI c.hU).mp hβ
      apply IntMod.val_injective
      rw [convI_apply_val, Subgroup.mem_centralizer_iff.mp hw g hgJ, mul_inv_cancel_right]
    · intro hw
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h2 := congrArg IntMod.val (hw _ (convI_mem_autI c.hU hj (hHN (hJH hj))))
      rw [convI_apply_val] at h2
      calc j * w.val = j * w.val * j⁻¹ * j := by group
        _ = w.val * j := by rw [h2]
  have hKY : ∀ k (hk : k ∈ K), (∀ w' ∈ commV (autI c.hU K),
      convI c.hU ⟨k, hHN (hKH hk)⟩ w' = w') → k ∈ Subgroup.centralizer (Y : Set G) := by
    intro k hk h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hT1] at hy
    obtain ⟨w', hw', rfl⟩ := hy
    have h1 := congrArg IntMod.val (h w' hw')
    rw [convI_apply_val] at h1
    rw [hι]
    calc w'.val * k = (k * w'.val * k⁻¹) * k := by rw [h1]
      _ = k * w'.val := by group
  have hstab : ∀ y : IntMod UH c.hU, (∀ g ∈ kStar615 T L H, g * y.val * g⁻¹ = y.val →
      g ∈ Subgroup.centralizer (Y : Set G)) → ∀ τ ∈ autI c.hU K, τ y = y →
        ∀ w' ∈ commV (autI c.hU K), τ w' = w' := by
    intro y hys τ hτ hτw w' hw'
    obtain ⟨g, hgK, rfl⟩ := (mem_autI c.hU).mp hτ
    have hgz : (g : G) * y.val * (g : G)⁻¹ = y.val := by
      have := congrArg IntMod.val hτw
      rwa [convI_apply_val] at this
    have hgY := hys g (Subgroup.mem_sup_left hgK) hgz
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hw'Y : w'.val ∈ Y := by rw [hT1]; exact ⟨w', hw', rfl⟩
    rw [← Subgroup.mem_centralizer_iff.mp hgY _ hw'Y, mul_inv_cancel_right]
  refine ⟨w₀.val, ⟨?_, (hT2 w₀).mpr hw₀B, fun h => hw₀1 (IntMod.val_injective
    (h.trans IntMod.val_one.symm)), fun g hg hgz => ?_⟩, ?_⟩
  · rw [hT1]
    exact ⟨w₀, hw₀Y, rfl⟩
  · have hg' : g ∈ ((K ⊔ C : Subgroup G) : Set G) := hg
    rw [hKCeq] at hg'
    obtain ⟨k, hk, c', hc', rfl⟩ := hg'
    have hc'z : c' * w₀.val * c'⁻¹ = w₀.val := by
      rw [← Subgroup.mem_centralizer_iff.mp hc'.2 _ (hUHU w₀.val_mem), mul_inv_cancel_right]
    have hkz : k * w₀.val * k⁻¹ = w₀.val := by
      have e : k * c' * w₀.val * (k * c')⁻¹ = k * (c' * w₀.val * c'⁻¹) * k⁻¹ := by group
      rw [e, hc'z] at hgz
      exact hgz
    have hσ : convI c.hU ⟨k, hHN (hKH hk)⟩ w₀ = w₀ :=
      IntMod.val_injective (by rw [convI_apply_val]; exact hkz)
    exact Subgroup.mul_mem _
      (hKY k hk (hw₀s _ (convI_mem_autI c.hU hk (hHN (hKH hk))) hσ)) (hCY hc')
  · rintro y ⟨hyY, hyJ, hy1, hys⟩
    rw [hT1] at hyY
    obtain ⟨ŵ, hŵ, rfl⟩ := hyY
    have hŵ1 : ŵ ≠ 1 := fun h => hy1 (by rw [h, map_one])
    rw [huniq ŵ ⟨hŵ, (hT2 ŵ).mp hyJ, hŵ1, hstab ŵ hys⟩]
    rfl

end Cx615B

namespace Cx615C

theorem borelL_le_normalizer_commutator_ch615 (c : Cx615C G T M L V H n)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    borelL T L ≤ Subgroup.normalizer ((⁅Cx615.UH T H, oTwoUpper H⁆ : Subgroup G) : Set G) := by
  classical
  obtain ⟨-, I, hcard, hJeq, -, -, -, htype, -, -, h2, -⟩ := c.e23
  have hnat := c.s3 I hcard hJeq htype
  obtain ⟨-, -, -, hEK⟩ := h2 fun L hL => ⟨1, hnat L hL⟩
  rw [twoResidual_eq_oTwoUpper'] at hEK
  have hYUH := commutator_le_UH_ch615 T H
  have hBJ := c.borelL_le_normalizer_thompsonJ_ch615
  have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
  rw [twoResidual_eq_oTwoUpper'] at hsup
  have hZE : quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) :=
    S1417.omegaOneCenter_le_omegaOneCenterOf T
  set Z := quasithinOmegaOneCenter T with hZdef
  set X := borelL T L ⊔ H with hXdef
  set U := conjClosure Z X with hUdef
  set UH := Cx615.UH T H with hUHdef
  set K := oTwoUpper H with hKdef
  set C := cXU615 T L H with hCdef
  set E := omegaOneCenterOf (thompsonJ T) with hEdef
  set Y := ⁅UH, K⁆ with hYdef
  have hTH : T ≤ H := c.hH.1.1
  have hKH : K ≤ H := oTwoUpper_le H
  have hKX : K ≤ X := hKH.trans le_sup_right
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Z X
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := hKX.trans le_normalizer_cXU615
  have hKCeq := Subgroup.coe_mul_of_left_le_normalizer_right K C hKC
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_commutator_ch6 (le_normalizer_conjClosure _ _) (le_normalizer_oTwoUpper H)
  have hEH : E ≤ H := (omegaOneCenterOf_le (thompsonJ T)).trans ((thompsonJ_le_self T).trans hTH)
  have hEYeq := Subgroup.coe_mul_of_right_le_normalizer_left Y
    (E ⊓ Subgroup.centralizer (K : Set G)) ((inf_le_left.trans hEH).trans hHY)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hKTeq := Subgroup.coe_mul_of_right_le_normalizer_left K T hTK
  set Wc := conjClosure (E ⊓ U) (K ⊔ C) with hWcdef
  have hWU : Wc ≤ U := conjClosure_le fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp (hXU (sup_le hKX inf_le_left hg)) a).mp ha.2
  have hWE : Wc ≤ conjClosure E K := conjClosure_le fun g hg a ha => by
    have hg' : g ∈ ((K ⊔ C : Subgroup G) : Set G) := hg
    rw [hKCeq] at hg'
    obtain ⟨k, hk, c', hc', rfl⟩ := hg'
    have hc'a : c' * a * c'⁻¹ = a := by
      rw [← Subgroup.mem_centralizer_iff.mp hc'.2 a ha.2, mul_inv_cancel_right]
    have e : k * c' * a * (k * c')⁻¹ = k * (c' * a * c'⁻¹) * k⁻¹ := by group
    rw [e, hc'a]
    exact mem_conjClosure hk ha.1
  have hUHW : UH ≤ Wc := conjClosure_le fun h hh z hz => by
    have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := by
      rw [sup_comm, hsup]; exact hh
    rw [hKTeq] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    have htz : t * z * t⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1 t ht,
        mul_inv_cancel_right]
    have e : k * t * z * (k * t)⁻¹ = k * (t * z * t⁻¹) * k⁻¹ := by group
    rw [e, htz]
    exact mem_conjClosure (Subgroup.mem_sup_left hk) ⟨hZE hz, le_conjClosure Z X hz⟩
  have hWY : ⁅Wc, K ⊔ C⁆ = Y := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro w hw g hg
      have hwU := hWU hw
      have hwE : w ∈ ((Y ⊔ E ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
        rw [SetLike.mem_coe, hYdef, ← hEK]; exact hWE hw
      rw [hEYeq] at hwE
      obtain ⟨y, hy, e, he, rfl⟩ := hwE
      have hg' : g ∈ ((K ⊔ C : Subgroup G) : Set G) := hg
      rw [hKCeq] at hg'
      obtain ⟨k, hk, c', hc', rfl⟩ := hg'
      have hca : c' * (y * e)⁻¹ = (y * e)⁻¹ * c' :=
        (Commute.inv_right (Subgroup.mem_centralizer_iff.mp hc'.2 _ hwU).symm).eq
      have hek : e * k = k * e := (Subgroup.mem_centralizer_iff.mp he.2 k hk).symm
      have key : ⁅y * e, k * c'⁆ = ⁅y, k⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc y * e * (k * c') * (y * e)⁻¹ * (k * c')⁻¹
            = y * e * k * (c' * (y * e)⁻¹) * c'⁻¹ * k⁻¹ := by group
          _ = y * e * k * ((y * e)⁻¹ * c') * c'⁻¹ * k⁻¹ := by rw [hca]
          _ = y * (e * k) * e⁻¹ * y⁻¹ * k⁻¹ := by group
          _ = y * (k * e) * e⁻¹ * y⁻¹ * k⁻¹ := by rw [hek]
          _ = y * k * y⁻¹ * k⁻¹ := by group
      rw [key]
      exact Subgroup.commutator_mem_commutator (hYUH hy) hk
    · exact Subgroup.commutator_mono hUHW le_sup_left
  have hBW : borelL T L ≤ Subgroup.normalizer (Wc : Set G) := fun b hb =>
    mem_normalizer_conjClosure_ch615
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T) (hBJ hb),
          hXU (Subgroup.mem_sup_left hb)⟩) (hN hb)
  have := le_normalizer_commutator_ch6 hBW hN
  rwa [hWY] at this

end Cx615C

namespace Cx615C

omit [Finite G] in
theorem mem_normalizer_zpowers_ch615 {z g : G} (h : g * z = z * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_right h k).eq.symm

theorem cXU615_le_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    cXU615 T L H ≤ M := by
  classical
  have h := c.hyp
  obtain ⟨z, ⟨hzY, hzJ, hz1, hzs⟩, huniq⟩ := c.toCx615B.existsUnique_ch615
  have hBY := c.borelL_le_normalizer_commutator_ch615 hN
  have hBJ := c.borelL_le_normalizer_thompsonJ_ch615
  have hYUH := commutator_le_UH_ch615 T H
  have hred := conjClosure_isTwoReducedIn_of_charTwo c.toCx615.isSylowTwoOf c.toCx615.charTwo
    (le_rfl : quasithinOmegaOneCenter T ≤ _)
  set Z := quasithinOmegaOneCenter T with hZdef
  set UH := Cx615.UH T H with hUHdef
  set K := oTwoUpper H with hKdef
  set Y := ⁅UH, K⁆ with hYdef
  set X := borelL T L ⊔ H with hXdef
  set C := cXU615 T L H with hCdef
  have hTH : T ≤ H := c.hH.1.1
  have hinv : ∀ g : G, g ∈ Subgroup.normalizer (Y : Set G) →
      g ∈ Subgroup.normalizer (thompsonJ T : Set G) →
      g ∈ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) → g * z * g⁻¹ = z := by
    intro g hgY hgJ hgK
    refine huniq (g * z * g⁻¹) ⟨(Subgroup.mem_normalizer_iff.mp hgY z).mp hzY, ?_,
      fun h1 => hz1 (conj_eq_one_iff.mp h1), fun g' hg' hg'z => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : g⁻¹ * j * g ∈ thompsonJ T := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgJ) j).mp hj
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hzJ _ hj'
      calc j * (g * z * g⁻¹) = g * ((g⁻¹ * j * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * j * g)) * g⁻¹ := by rw [hc]
        _ = g * z * g⁻¹ * j := by group
    · have hg'' : g⁻¹ * g' * g ∈ kStar615 T L H := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) g').mp hg'
        rwa [inv_inv] at this
      have hz' : (g⁻¹ * g' * g) * z * (g⁻¹ * g' * g)⁻¹ = z := by
        have e : (g⁻¹ * g' * g) * z * (g⁻¹ * g' * g)⁻¹ =
            g⁻¹ * (g' * (g * z * g⁻¹) * g'⁻¹) * g := by group
        rw [e, hg'z]
        group
      have hcY := hzs _ hg'' hz'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgY) y).mp hy
        rwa [inv_inv] at this
      have hc := Subgroup.mem_centralizer_iff.mp hcY _ hy'
      calc y * g' = g * ((g⁻¹ * y * g) * (g⁻¹ * g' * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * g' * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
        _ = g' * y := by group
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTH.trans
    (le_normalizer_commutator_ch6 (le_normalizer_conjClosure _ _) (le_normalizer_oTwoUpper H))
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hTK : T ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) := by
    intro t ht
    have h1 : t ∈ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H (hTH ht)
    have h2 : t ∈ Subgroup.normalizer (C : Set G) :=
      le_normalizer_cXU615 (Subgroup.mem_sup_right (hTH ht))
    show t ∈ Subgroup.normalizer ((K ⊔ C : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hzUH : z ∈ UH := hYUH hzY
  have hUHT : UH ≤ T :=
    hred.1.trans (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le c.toCx615.isSylowTwoOf))
  have hz2 : z ^ 2 = 1 := c.hU.2 z hzUH
  have hzT : ∀ t ∈ T, t * z = z * t := fun t ht => by
    have := hinv t (hTY ht) (hTJ ht) (hTK ht)
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [this]
  have hzZ : z ∈ Z :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUHT hzUH, Subgroup.mem_centralizer_iff.mpr hzT, hz2⟩
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨F, _, _, _, hF, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [c.V_eq]; exact hS.centralizer_le
  have hn2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hodd2 : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by have := h.two_le; omega⟩)
      odd_one
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := Odd.of_dvd_nat hodd2 hpd
  obtain ⟨d, hdD, hdp⟩ := hc.exists_orderOf_eq_ch615 (p := p) hCV c.toCx615.isSylowTwoOf_inf hD
    (by rw [hF]; exact hpd)
  have hdB : d ∈ borelL T L := hD.1 hdD
  have hdodd : Odd (orderOf d) := hdp ▸ hpodd
  have hd1 : d ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hdp
    exact hp.one_lt.ne hdp
  have hdz : d * z * d⁻¹ = z := hinv d (hBY hdB) (hBJ hdB) (hN hdB)
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hzZ, hzd⟩
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hzL l hl))
      (fun t ht => mem_normalizer_zpowers_ch615 (hzT t ht))
  have hzU : z ∈ conjClosure Z X := conjClosure_mono le_rfl le_sup_right hzUH
  have hCz : C ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun x hx =>
    mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hx.2 z hzU).symm
  exact hCz.trans (le_of_isUniqueM_of_le_twoLocal (h.isUniqueM h432) hLT hloc)

end Cx615C

end CFSG.Quasithin.H13
