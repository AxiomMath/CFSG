module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420B56Group
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420B56Fix
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L15420

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_commV_autI {K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {w : G} (hw : w ∈ ⁅V, K⁆) (hwV : w ∈ V) :
    IntMod.mk hV ⟨w, hwV⟩ ∈ commV (autI hV K) := by
  let ι : IntMod V hV →* G := ⟨⟨IntMod.val, rfl⟩, fun _ _ => rfl⟩
  have hle : ⁅V, K⁆ ≤ (commV (autI hV K)).map ι := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    set u : IntMod V hV := IntMod.mk hV ⟨v⁻¹, V.inv_mem hv⟩
    refine ⟨convI hV ⟨k, hKV hk⟩ u * u⁻¹,
      Subgroup.subset_closure ⟨_, convI_mem_autI hV hk (hKV hk), u, rfl⟩, ?_⟩
    change (convI hV ⟨k, hKV hk⟩ u).val * (u.val)⁻¹ = v * k * v⁻¹ * k⁻¹
    rw [convI_apply_val]
    change k * v⁻¹ * k⁻¹ * v⁻¹⁻¹ = v * k * v⁻¹ * k⁻¹
    have hkv : k * v⁻¹ * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hKV hk) _).mp (V.inv_mem hv)
    have hc : (k * v⁻¹ * k⁻¹) * v = v * (k * v⁻¹ * k⁻¹) := by
      have := hV.1
      exact setLike_mul_comm hkv hv
    rw [inv_inv, hc]
    group
  obtain ⟨u, hu, hue⟩ := hle hw
  have h1 : u = IntMod.mk hV ⟨w, hwV⟩ := IntMod.val_injective hue
  rw [← h1]
  exact hu

omit [Finite G] in
theorem exists_fix_of_autI {K V TK : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (h : ∃ g ∈ autI hV K, orderOf g = 3 ∧
      ∀ v ∈ fixV (autI hV TK) ⊓ commV (autI hV K), g v = v) :
    ∃ k₀ ∈ K, (∀ n : ℕ, k₀ ^ 2 ^ n ≠ 1) ∧ ∀ w ∈ ⁅V, K⁆, (∀ t ∈ TK, t * w = w * t) →
      k₀ * w * k₀⁻¹ * w⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨g, hgL, hg3, hgfix⟩ := h
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hgL
  refine ⟨(x : G), hx, fun n hn => ?_, fun w hw hwT => ?_⟩
  · have h1 : x ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
    have h2 : convI hV x ^ 2 ^ n = 1 := by rw [← map_pow, h1, map_one]
    have h3 : 3 ∣ 2 ^ n := hg3 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · have hwV : w ∈ V := commutator_le_of_le_normalizer hKV hw
    have hfixS : IntMod.mk hV ⟨w, hwV⟩ ∈ fixV (autI hV TK) := by
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨t, ht, rfl⟩ := (mem_autI hV).1 hφ
      apply IntMod.val_injective
      rw [convI_apply_val]
      change (t : G) * w * (t : G)⁻¹ = w
      rw [hwT t ht]
      group
    have hgw := hgfix _ ⟨hfixS, mem_commV_autI hV hKV hw hwV⟩
    have h1 : (x : G) * w * (x : G)⁻¹ = w := by
      have := congrArg IntMod.val hgw
      rwa [convI_apply_val] at this
    rw [h1, mul_inv_cancel]
    exact Subgroup.one_mem _

end L15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Comp15420

variable {s : Setting15419 G T} {I₀ K : Subgroup G} {y : G}

theorem false_of_lin2_b56 (hnot : ¬ IsLThreeTwoOrASix G) (h2 : Stmt1542Two G T)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (c : Config15420 s I₀)
    (hC : Comp15420 s I₀ K y) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : quasithinOmegaOneCenter T ≤ V)
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K)
    (hlin : ∃ n, BinaryNaturalSL (autI hV K) (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) 2 n) : False := by
  obtain ⟨n, F, _, _, hF, π, hπ⟩ := hlin
  have := FFL.charP_two_of_card hF
  obtain ⟨zX, hzX, -, hzXC, hCzX⟩ := exists_zX hnot h12 h14 s
  have hTK : IsSylowTwoOf (T ⊓ I₀ ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hC.mem) c.sylow
  set U := ⁅V, K⁆ with hUdef
  have hUV : U ≤ V := commutator_le_of_le_normalizer hKV
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v hv
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := fun k hk =>
    A4.mem_normalizer_commutator (hKV hk) (Subgroup.le_normalizer hk)
  have hzT := L15420.omegaOneCenter_le_center T hzX
  have hzTK : ∀ t ∈ T ⊓ I₀ ⊓ K, t * zX = zX * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hzT.2 t ht.1.1
  have hδ : ∀ k' ∈ K, k' * zX * k'⁻¹ * zX⁻¹ ∈ U := by
    intro k' hk'
    have h := Subgroup.commutator_mem_commutator hk' (hZV hzX)
    rw [Subgroup.commutator_comm] at h
    simpa [commutatorElement_def] using h
  obtain ⟨w, hwU, hw⟩ := L15420.exists_mul_mem_centralizer hTK.2.2
    (fun a ha b hb => hVc a (hUV ha) b (hUV hb)) (fun u hu => hV2 u (hUV hu)) hKU hzTK hδ
  have hyK : y ∈ K := hC.y_mem.2
  have hyz : y * zX = zX * y := Subgroup.mem_centralizer_iff.mp hzXC y hC.y_mem.1
  have hyw : y * w = w * y := by
    have h1 := hw y hyK
    have e : w = zX * (w⁻¹ * zX)⁻¹ := by group
    rw [e]
    calc y * (zX * (w⁻¹ * zX)⁻¹) = (y * zX) * (w⁻¹ * zX)⁻¹ := by group
      _ = zX * (y * (w⁻¹ * zX)⁻¹) := by rw [hyz]; group
      _ = zX * ((w⁻¹ * zX)⁻¹ * y) := by
        congr 1
        calc y * (w⁻¹ * zX)⁻¹ = (w⁻¹ * zX)⁻¹ * ((w⁻¹ * zX) * y) * (w⁻¹ * zX)⁻¹ := by group
          _ = (w⁻¹ * zX)⁻¹ * (y * (w⁻¹ * zX)) * (w⁻¹ * zX)⁻¹ := by rw [h1]
          _ = (w⁻¹ * zX)⁻¹ * y := by group
      _ = zX * (w⁻¹ * zX)⁻¹ * y := by group
  have hwV : w ∈ V := hUV hwU
  set ℓ : ↥(autI hV K) := ⟨convI hV ⟨y, hKV hyK⟩, convI_mem_autI hV hyK (hKV hyK)⟩
  have hy3 : y ^ 3 = 1 := by rw [← hC.y_order, pow_orderOf_eq_one]
  have hℓ3 : ℓ ^ 3 = 1 := by
    apply Subtype.ext
    have h1 : (⟨y, hKV hyK⟩ : Subgroup.normalizer (V : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy3)
    change convI hV ⟨y, hKV hyK⟩ ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hℓ1 : ℓ ≠ 1 := by
    intro h
    have h1 : convI hV ⟨y, hKV hyK⟩ = 1 := congrArg Subtype.val h
    exact hC.not_mem_pCoreOf (hCK ⟨hyK, (convI_eq_one_iff hV _).mp h1⟩)
  have hfix : (ℓ : MulAut (IntMod V hV)) (IntMod.mk hV ⟨w, hwV⟩) = IntMod.mk hV ⟨w, hwV⟩ := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    change y * w * y⁻¹ = w
    rw [hyw]
    group
  have hmem := FFL.mem_of_fix_nat_two hπ hℓ3 hℓ1 (L15420.mem_commV_autI hV hKV hwU hwV) hfix
  have hwC : w ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk1 := (mem_fixV.mp hmem.1) _ (convI_mem_autI hV hk (hKV hk))
    have hk2 := congrArg IntMod.val hk1
    rw [convI_apply_val] at hk2
    have hk3 : k * w * k⁻¹ = w := hk2
    calc k * w = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [hk3]
  apply hC.not_le_M₁ h2
  intro k hk
  apply hCzX
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hw k hk
  have h3 := Subgroup.mem_centralizer_iff.mp hwC k hk
  calc k * zX = k * (w * (w⁻¹ * zX)) := by group
    _ = (k * w) * (w⁻¹ * zX) := by group
    _ = (w * k) * (w⁻¹ * zX) := by rw [h3]
    _ = w * (k * (w⁻¹ * zX)) := by group
    _ = w * ((w⁻¹ * zX) * k) := by rw [h1]
    _ = zX * k := by group

end Comp15420

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem false_of_charTwo_b56
    (facts : Facts15420) (h56 : AsB56)
    (hyp : MultipleCentralizerHypothesis G T) (hnot : ¬ IsLThreeTwoOrASix G)
    (h2 : Stmt1542Two G T) (h8 : Stmt1548 G T) (h12 : Stmt15412 G T) (h14 : Stmt15414 G T)
    (c : Config15420 s I₀) {K : Subgroup G} {y : G} (hC : Comp15420 s I₀ K y)
    (hK : CharTwo K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (s.X ⊔ T ⊓ I₀) with hRdef
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hZ := hC.center_eq_bot facts
  have hRK := hC.R_le_normalizer facts hyp h12 c
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hKRK : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hKRV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hKRV
  have hV : IsElemAbelian 2 V := B2F.isElemAbelian_omegaOneCenterOf _
  have hZV := hC.omegaOneCenter_le_of_charTwo hyp h12 c hK hRK
  have hCK := hC.inf_centralizer_V_le facts h8 hyp h12 c hK hRK
  have hQV : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G) :=
    L15420.le_centralizer_omegaOneCenterOf _
  have hOK : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    (Comp15420.pCoreOf_le_pCoreOf_sup hRK).trans hQV
  have hTK : IsSylowTwoOf (T ⊓ I₀ ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hC.mem) c.sylow
  obtain ⟨e⟩ := L15420.nonempty_mulEquiv_autOn hKV hCK hOK
  have hq : CFSG.IsQuasisimple ↥(autI hV K) := FFL.isQuasisimple_of_mulEquiv e hC.quasisimple
  have hcard : Nat.card ↥(autI hV K) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (Nat.card_congr e.toEquiv).symm
  obtain ⟨h6, hN⟩ := hC.card_quot facts
  rw [← hcard] at h6 hN
  have hΓ : autI hV (K ⊔ R) ⊓ Subgroup.centralizer (autI hV K : Set (MulAut (IntMod V hV))) =
      ⊥ :=
    L15420.autOn_inf_centralizer_eq_bot hZ hR2 hRK hKRV hCK hQV
  have hQ : G64.IsQuotientOfSQTKCat ↥(autI hV (K ⊔ R)) :=
    L15420.isQuotientOfSQTKCat_autOn (c.hypC23 hyp h12).sqtk
      (sup_le (le_of_mem_cComp hC.mem) (c.hypC23 hyp h12).radical.1) hKRV
  have hLΓ : autI hV K ≤ autI hV (K ⊔ R) := autI_mono hV le_sup_left
  have hnormal : ((autI hV K).subgroupOf (autI hV (K ⊔ R))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLΓ]
    rintro _ _ ⟨k, hk, rfl⟩ ⟨x, hx, rfl⟩
    refine ⟨x * k * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKRK hx) k).mp hk
  have hoff := hC.exists_ffStarOffender facts h2 h8 hyp h12 c hK hRK hV
  have hS : IsSylowTwoOf (autI hV (T ⊓ I₀ ⊓ K)) (autI hV K) := L15420.isSylowTwoOf_autOn hTK hKV
  have hV2 : ∀ v : IntMod V hV, v * v = 1 := fun v => by
    rw [← sq]
    exact IntMod.sq_eq_one v
  rcases FFL.fix_or_lin2_of_b56 h56 hV2 hQ hLΓ hnormal hΓ hq h6 hN hoff hS with
    hfix | hlin
  · obtain ⟨k₀, hk₀, hk₀2, hfix'⟩ := L15420.exists_fix_of_autI hV hKV hfix
    exact hC.false_of_fix h8 hyp c hV hKV hZV hk₀ hk₀2 hfix'
  · exact hC.false_of_lin2_b56 hnot h2 h12 h14 c hV hKV hZV hCK hlin

end Config15420

theorem stmt15420_of_b56
    (facts : Facts15420) (h56 : AsB56) (h134 : Prop134E9He)
    {G : Type} [Group G] [Finite G] {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T)
    (hnot : ¬ IsLThreeTwoOrASix G) (h2 : Stmt1542Two G T) (h8 : Stmt1548 G T)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (h16 : Stmt15416 G T) (h17 : Stmt15417 G T)
    (h19 : Stmt15419 G T) : Stmt15420 G T := by
  intro s I₀ hI₀
  by_contra hns
  obtain ⟨s', J, c⟩ := exists_config15420 hyp h12 h16 s hI₀ hns
  obtain ⟨K, y, hC⟩ := c.exists_comp h134 hyp h12 h19
  rcases L15420.charTwo_or_isComponentIn hC.mem hC.quasisimple (hC.center_eq_bot facts) with
    hK | hK
  · exact c.false_of_charTwo_b56 facts h56 hyp hnot h2 h8 h12 h14 hC hK
  · exact c.false_of_isComponentIn facts hyp hnot h12 h14 h17 hC hK

end CFSG.Quasithin.EmptyFaithfulMultiple
