module

public import CFSG.Quasithin.Background.SmithB51G2DOff
public import CFSG.Quasithin.Background.SmithB51G2DKey
public import CFSG.Quasithin.Background.SmithB51G2DCoh
public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem cayleyTr_add {K : Type} [Field K] (x y : quasithinZorn K) :
    cayleyTr (x + y) = cayleyTr x + cayleyTr y := by
  simp only [cayleyTr, Prod.fst_add, Prod.snd_add]
  ring

omit [Finite V] in
theorem cayleyTr_sub {K : Type} [Field K] (x y : quasithinZorn K) :
    cayleyTr (x - y) = cayleyTr x - cayleyTr y := by
  simp only [cayleyTr, Prod.fst_sub, Prod.snd_sub]
  ring

omit [Finite V] in
theorem cayleyTr_smul {K : Type} [Field K] (c : K) (x : quasithinZorn K) :
    cayleyTr (c • x) = c * cayleyTr x := by
  simp only [cayleyTr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

omit [Finite V] in
theorem zP_sub {K : Type} [Field K] (x y : quasithinZorn K) : zP (x - y) = zP x - zP y := by
  rw [sub_eq_add_neg, zP_add, ← neg_one_smul K y, zP_smul, neg_one_smul, ← sub_eq_add_neg]

theorem g2Data (h : B51Hyp G L)
    (hG2 : (∃ n, G2Natural L (commV L) (fixV L ⊓ commV L) n) ∨
      G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1) :
    ∃ n, 1 ≤ n ∧ G2NaturalDerived L (commV L) (fixV L ⊓ commV L) n := by
  rcases hG2 with ⟨n, hn⟩ | hd
  · refine ⟨n, one_le_of_g2Natural hn, ?_⟩
    have hperf : ⁅L, L⁆ = L := by
      have : Group.IsPerfect ↥L := (quasi_L h).1
      exact Subgroup.commutator_eq_self
    have := g2NaturalDerived_of_g2Natural hn
    rwa [hperf] at this
  · exact ⟨1, le_rfl, hd⟩

theorem g2_cover (hIdent : AsB42Ident) (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6) (hL : G2Orders L n)
    {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G) :
    ∃ X : Subgroup (MulAut V), X ≤ G ∧ L ≤ X ∧
      (∀ A, IsFFStarOffender G A → A ≤ T → A ≤ X) ∧
      G2Natural X (commV L) (fixV L ⊓ commV L) n := by
  set C := fixV L ⊓ commV L with hC
  obtain ⟨hUC, -, hGU, hGC, -, hfM⟩ := secConfig hV h hU hT hC
  obtain ⟨hq, -, hJ⟩ := sylow_facts hIdent h42 hV h hU hn hcardS hL hT
  have hLG := le_G h
  have hMG : L ⊔ T ≤ G := sup_le hLG hT.1
  have hMU : L ⊔ T ≤ stabSub (commV L) := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub C := hMG.trans hGC
  have hLM : L ≤ L ⊔ T := le_sup_left
  have hTM : T ≤ L ⊔ T := le_sup_right
  set J := ffJ (autSec (L ⊔ T) (commV L) C) with hJdef
  set φ := secHom (L ⊔ T) hMU hMC with hφ
  set X : Subgroup (MulAut V) := (J.comap φ).map (L ⊔ T).subtype with hX
  have hXM : X ≤ L ⊔ T := Subgroup.map_subtype_le _
  have hXsub : X.subgroupOf (L ⊔ T) = J.comap φ :=
    Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective _
  have hmemX : ∀ g : ↥(L ⊔ T), φ g ∈ J → (g : MulAut V) ∈ X := fun g hg => ⟨g, hg, rfl⟩
  have hautX : autSec X (commV L) C = J := by
    rw [← map_secHom_eq_autSec (L ⊔ T) hMU hMC hXM, hXsub, Subgroup.map_comap_eq,
      ← hφ, range_secHom]
    exact inf_eq_right.2 (ffJ_le (autSec (L ⊔ T) (commV L) C))
  have hfX : X ⊓ centSec (commV L) C = ⊥ := by
    rw [eq_bot_iff, ← hfM]
    exact inf_le_inf_right _ hXM
  have hXG2 : G2Natural X (commV L) C n :=
    g2Natural_of_autSec hUC (hXM.trans hMU) (hXM.trans hMC) hfX (hautX ▸ hJ)
  have hHyp := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
  obtain ⟨-, -, -, B₀, -, hB₀⟩ := exists_section_offender' hV h hU hT hC
  have hΛJ : autSec L (commV L) C ≤ J :=
    Bridge.TypeList.le_ffJ_of_b4Hyp (KP := CFSG.SectionRank.IsKGroupCat)
      (sq_eq_one_sec hV _ _) hHyp hB₀
  have hLX : L ≤ X := by
    intro l hl
    refine hmemX ⟨l, hLM hl⟩ (hΛJ ?_)
    rw [← map_secHom_eq_autSec (L ⊔ T) hMU hMC hLM]
    exact ⟨⟨l, hLM hl⟩, hl, rfl⟩
  have hAX : ∀ A, IsFFStarOffender G A → A ≤ T → A ≤ X := by
    intro A hA hAT a ha
    have hoff := offender_sec hV h hU hT hq hA hAT
    have hAJ : autSec A (commV L) C ≤ J := le_iSup₂_of_le _ hoff le_rfl
    refine hmemX ⟨a, hTM (hAT ha)⟩ (hAJ ?_)
    rw [← map_secHom_eq_autSec (L ⊔ T) hMU hMC (hAT.trans hTM)]
    exact ⟨⟨a, hTM (hAT ha)⟩, ha, rfl⟩
  exact ⟨X, hXM.trans hMG, hLX, hAX, hXG2⟩



theorem g2Orders_of_derived {n : ℕ} (hn : 1 ≤ n)
    (hd : G2NaturalDerived L (commV L) (fixV L ⊓ commV L) n) :
    G2Orders L n ∧ Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hd
  have hK2 : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hΓ : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := commutator_le_self _
  have hLc := card_eq_gam (FFC.zornQ_faithful _ hΓ) hπ
  have hU := G64.RealizesVia.card_eq hπ
  have hCU : fixV L ⊓ commV L ≤ commV L := inf_le_right
  have hUc : Nat.card (commV L) = Nat.card (Sec (commV L) (fixV L ⊓ commV L)) *
      Nat.card ↥(fixV L ⊓ commV L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((fixV L ⊓ commV L).subgroupOf (commV L))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  have hS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6 := by
    rw [card_zornQMod, hK, hUc] at hU
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hU
  refine ⟨?_, hS⟩
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · right
    refine ⟨h2, ?_⟩
    have : Fintype K := Fintype.ofFinite K
    have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hKf h2
    have heq : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K := by
      rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
      exact cayley_commutator_eq hc0 hc1
    have hLc' : Nat.card L = Nat.card (quasithinG2 K) := by
      rw [hLc]
      change Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = _
      rw [heq]
    rw [hLc', card_quasithinG2_1527d hK, hK]
  · left
    have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    refine ⟨rfl, ?_⟩
    rw [hLc]
    exact S1549D.card_commutator_quasithinG2_two (by rw [hK, pow_one])


theorem fixV_L_le_fixV_G (hIdent : AsB42Ident) (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6) (hL : G2Orders L n) :
    fixV L ≤ fixV G := by
  have hnL := normal_L h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hnL (fun g hg => G.inv_mem hg)
  intro v hv
  have hall : ∀ A, IsFFStarOffender G A → ∀ a ∈ A, a v = v := by
    intro A hA a ha
    obtain ⟨hsup, -, hfix, -⟩ := offender_facts hIdent h42 hV h hU hn hcardS hL hA
    have hvt : v ∈ commV L ⊔ fixV A := by rw [hsup]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hvt
    have huY : u ∈ fixMod A (commV L) (fixV L ⊓ commV L) := by
      refine ⟨hu, fun a' ha' => ⟨?_, ?_⟩⟩
      · have ha'G : a' ∈ G := hA.1 ha'
        have hav : a' (u * c) ∈ fixV L := B1Red.fixV_inv_of_normalizes hnL a' ha'G _ hv
        have e : a' u * u⁻¹ = a' (u * c) * (u * c)⁻¹ := by
          rw [map_mul, hc a' ha', mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
        rw [e]
        exact (fixV L).mul_mem hav ((fixV L).inv_mem hv)
      · exact (commV L).mul_mem ((hGU (hA.1 ha') u).2 hu) ((commV L).inv_mem hu)
    rw [hfix] at huY
    rw [map_mul, huY.2 a ha, hc a ha]
  have hJ : ffJ G ≤ MulAction.stabilizer (MulAut V) v :=
    iSup₂_le fun A hA => fun a ha => hall A hA a ha
  intro g hg
  exact hJ (h.2.2.2.2.2 ▸ hg)

theorem exists_mem_fixV_L (hIdent : AsB42Ident) (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card (Sec (commV L) (fixV L ⊓ commV L)) = (2 ^ n) ^ 6) (hL : G2Orders L n)
    (v : V) : ∃ u ∈ commV L, v * u⁻¹ ∈ fixV L := by
  classical
  set C := fixV L ⊓ commV L with hC
  have hnL := normal_L h
  have hGU : G ≤ stabSub (commV L) := le_stabSub_commV hnL (fun g hg => G.inv_mem hg)
  have hVGU : ∀ g ∈ G, ∀ w : V, g w * w⁻¹ ∈ commV L := by
    have hoffQ : ∀ A, IsFFStarOffender G A → A ≤ centQuot (commV L) := by
      intro A hA a ha w
      obtain ⟨hsup, -⟩ := offender_facts hIdent h42 hV h hU hn hcardS hL hA
      have hw : w ∈ commV L ⊔ fixV A := by rw [hsup]; trivial
      obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
      have e : a (u * c) * (u * c)⁻¹ = a u * u⁻¹ := by
        rw [map_mul, hc a ha, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
      rw [e]
      exact (commV L).mul_mem ((hGU (hA.1 ha) u).2 hu) ((commV L).inv_mem hu)
    have hJQ : ffJ G ≤ centQuot (commV L) := iSup₂_le fun A hA => hoffQ A hA
    intro g hg w
    exact hJQ (h.2.2.2.2.2 ▸ hg) w
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  obtain ⟨A₀, hA₀, hA₀T, -⟩ := exists_section_offender' hV h hU hT hC
  obtain ⟨X, hXG, hLX, hAX, hXG2⟩ := g2_cover hIdent h42 hV h hU hn hcardS hL hT
  have hA₀X := hAX A₀ hA₀ hA₀T
  obtain ⟨hsup₀, hcardA₀, -, hY₀⟩ := offender_facts hIdent h42 hV h hU hn hcardS hL hA₀
  obtain ⟨K, _, _, hK, π, hπ⟩ := hXG2
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hq2 : quasithinG2 K = cayleyGroup K := G11.P3G2.quasithinG2_eq_cayleyGroup
  obtain ⟨f, hfadd, hfker, hfonto, hfeq⟩ :=
    Vol2.KGNat.exists_coord (Vol2.KGNat.linModelZorn (quasithinG2 K) hq2.le) hπ
  let Θ : ↥(quasithinG2 K) ≃* ↥(cayleyGroup K) := MulEquiv.subgroupCongr hq2
  have hπinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
  let ψ : ↥(cayleyGroup K) →* ↥X := π.comp Θ.symm.toMonoidHom
  have hψinj : Function.Injective ψ := hπinj.comp Θ.symm.injective
  have hψsurj : Function.Surjective ψ := hπ.1.comp Θ.symm.surjective
  have hψeq : ∀ g u, u ∈ commV L → f (((ψ g : ↥X) : MulAut V) u) = g2Act g (f u) := by
    intro g u hu
    have h1 := hfeq (Θ.symm g) u hu
    have h2 : g2Act (Θ (Θ.symm g)) (f u) = g2Act g (f u) := by rw [MulEquiv.apply_symm_apply]
    exact h1.trans h2
  have hXU : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu => (hGU (hXG hx) u).2 hu
  have hUmi : ∀ {u u' : V}, u ∈ commV L → u' ∈ commV L → u * u'⁻¹ ∈ commV L :=
    fun hu hu' => (commV L).mul_mem hu ((commV L).inv_mem hu')
  have hfsub : ∀ u ∈ commV L, ∀ u' ∈ commV L, f (u * u'⁻¹) = f u - f u' := by
    intro u hu u' hu'
    have h1 := hfadd (u * u'⁻¹) (hUmi hu hu') u' hu'
    rw [inv_mul_cancel_right] at h1
    rw [h1]
    abel
  set φ : ↥(cayleyGroup K) → (Ix3 → K) := fun g => f (((ψ g : ↥X) : MulAut V) v * v⁻¹) with hφ
  have hφZ : φ ∈ Z1A (g2Act (F := K)) := by
    intro g g'
    show f (((ψ (g * g') : ↥X) : MulAut V) v * v⁻¹) = f (((ψ g : ↥X) : MulAut V) v * v⁻¹) +
      g2Act g (f (((ψ g' : ↥X) : MulAut V) v * v⁻¹))
    have hxy : ((ψ (g * g') : ↥X) : MulAut V) =
        ((ψ g : ↥X) : MulAut V) * ((ψ g' : ↥X) : MulAut V) := by
      rw [map_mul]
      rfl
    have hy : ((ψ g' : ↥X) : MulAut V) v * v⁻¹ ∈ commV L := hVGU _ (hXG (ψ g').2) v
    have hx : ((ψ g : ↥X) : MulAut V) v * v⁻¹ ∈ commV L := hVGU _ (hXG (ψ g).2) v
    have hsplit : (((ψ g : ↥X) : MulAut V) * ((ψ g' : ↥X) : MulAut V)) v * v⁻¹ =
        ((ψ g : ↥X) : MulAut V) (((ψ g' : ↥X) : MulAut V) v * v⁻¹) *
          (((ψ g : ↥X) : MulAut V) v * v⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    rw [hxy, hsplit, hfadd _ (hXU _ (ψ g).2 _ hy) _ hx, hψeq g _ hy, add_comm]
  obtain ⟨α, w, hw⟩ := exists_sub_fG_mem_B1A_all hKf hn hφZ
  have hw' : ∀ g, g2Act g w - w = φ g - α • fG g := fun g => congrFun hw g
  set Ā : Subgroup ↥(cayleyGroup K) := (A₀.subgroupOf X).comap ψ with hĀ
  have hmemĀ : ∀ γ, γ ∈ Ā ↔ ((ψ γ : ↥X) : MulAut V) ∈ A₀ := fun γ => Iff.rfl
  have hvA : v ∈ commV L ⊔ fixV A₀ := by rw [hsup₀]; trivial
  obtain ⟨u₁, hu₁, c₁, hc₁, hv⟩ := Subgroup.mem_sup.1 hvA
  have hcob : ∀ γ ∈ Ā, φ γ = g2Act γ (f u₁) - f u₁ := by
    intro γ hγ
    have ha := (hmemĀ γ).1 hγ
    have e : ((ψ γ : ↥X) : MulAut V) v * v⁻¹ = ((ψ γ : ↥X) : MulAut V) u₁ * u₁⁻¹ := by
      rw [← hv, map_mul, hc₁ _ ha, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    show f (((ψ γ : ↥X) : MulAut V) v * v⁻¹) = _
    rw [e, hfsub _ (hXU _ (ψ γ).2 _ hu₁) _ hu₁, hψeq γ _ hu₁]
  have hα : α = 0 := by
    by_contra hα0
    set w' := f u₁ - w with hw'def
    set x₀ : quasithinZorn K := α • zE' K + zI w' with hx₀
    have htr : cayleyTr x₀ = α := by
      rw [hx₀, cayleyTr_add, cayleyTr_smul, cayleyTr_zI, zE', cayleyTr_zmk]
      ring
    have hxA : ∀ γ ∈ Ā, ∃ c : K, cgE γ x₀ = x₀ + c • cayleyOne K := by
      intro γ hγ
      have hd : cayleyTr (cgE γ x₀ - x₀) = 0 := by
        rw [cayleyTr_sub, cg_tr, sub_self]
      have hP : zP (cgE γ x₀ - x₀) = 0 := by
        have h1 : zP (cgE γ x₀ - x₀) = α • fG γ + (g2Act γ w' - w') := by
          have e : cgE γ x₀ - x₀ = α • (cgE γ (zE' K) - zE' K) + (cgE γ (zI w') - zI w') := by
            rw [hx₀, map_add, map_smul, smul_sub]
            abel
          rw [e, zP_add, zP_smul, zP_sub (cgE γ (zI w')), zP_zI, fG_eq_zP, g2Act_apply]
        have h2 : α • fG γ = g2Act γ w' - w' := by
          have e1 := hw' γ
          rw [hcob γ hγ] at e1
          rw [hw'def, g2Act_sub]
          linear_combination (norm := abel_nf) e1
        rw [h1, h2]
        exact (CharTwo.add_self_eq_zero (g2Act γ w' - w'))
      refine ⟨(cgE γ x₀ - x₀).1, ?_⟩
      have := eq_smul_one_of_zP hd hP
      rw [← this]
      abel
    have hcommĀ : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a := by
      intro a ha b hb
      apply hψinj
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hA₀.2.2.1.1 _ ha _ hb
    have hinvĀ : ∀ a ∈ Ā, a * a = 1 := by
      intro a ha
      apply hψinj
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact hA₀.2.2.1.2 _ ha
    have hcardĀ : Nat.card Ā = Nat.card K ^ 3 := by
      have h1 : Nat.card Ā = Nat.card (A₀.subgroupOf X) := by
        rw [hĀ, ← Subgroup.card_map_of_injective hψinj,
          Subgroup.map_comap_eq_self_of_surjective hψsurj]
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀X).toEquiv, hcardA₀, hK,
        ← pow_mul, mul_comm]
    have hfixĀ : Nat.card (fixQ Ā) = Nat.card K ^ 3 := by
      let fU : ↥(commV L) →* Multiplicative (Ix3 → K) :=
        { toFun := fun u => Multiplicative.ofAdd (f u)
          map_one' := by
            have := (hfker 1 (commV L).one_mem).2 C.one_mem
            show Multiplicative.ofAdd (f 1) = 1
            rw [this]
            rfl
          map_mul' := fun u u' => by
            rw [show ((u * u' : ↥(commV L)) : V) = (u : V) * u' from rfl,
              hfadd _ u.2 _ u'.2]
            rfl }
      have hfUs : Function.Surjective fU := by
        intro m
        obtain ⟨u, hu, hfu⟩ := hfonto (Multiplicative.toAdd m)
        exact ⟨⟨u, hu⟩, by rw [← ofAdd_toAdd m, ← hfu]; rfl⟩
      have hfUk : Nat.card fU.ker = Nat.card C := by
        refine Nat.card_congr
          { toFun := fun u => ⟨((u : ↥(commV L)) : V), (hfker _ (u : ↥(commV L)).2).1
              (congrArg Multiplicative.toAdd u.2)⟩
            invFun := fun c => ⟨⟨c, c.2.2⟩, by
              show Multiplicative.ofAdd (f c) = 1
              rw [(hfker _ c.2.2).2 c.2]
              rfl⟩
            left_inv := fun u => rfl
            right_inv := fun c => rfl }
      set F' : Subgroup (Multiplicative (Ix3 → K)) := (fixQ Ā).toAddSubgroup.toSubgroup with hF'
      have hF'card : Nat.card F' = Nat.card (fixQ Ā) := rfl
      have hmem : ∀ u : ↥(commV L), fU u ∈ F' ↔ ∀ a ∈ A₀, a (u : V) * (u : V)⁻¹ ∈ C := by
        intro u
        show f u ∈ fixQ Ā ↔ _
        constructor
        · intro hu a ha
          obtain ⟨γ, hγ⟩ := hψsurj ⟨a, hA₀X ha⟩
          have hγĀ : γ ∈ Ā := by
            rw [hmemĀ, hγ]
            exact ha
          have h1 := hu γ hγĀ
          rw [← hψeq γ u u.2, hγ] at h1
          refine (hfker _ (hUmi (hXU _ (hA₀X ha) _ u.2) u.2)).1 ?_
          rw [hfsub _ (hXU _ (hA₀X ha) _ u.2) _ u.2]
          exact sub_eq_zero.2 h1
        · intro hu γ hγ
          have ha := (hmemĀ γ).1 hγ
          rw [← hψeq γ u u.2]
          have h1 := (hfker _ (hUmi (hXU _ (ψ γ).2 _ u.2) u.2)).2 (hu _ ha)
          rw [hfsub _ (hXU _ (ψ γ).2 _ u.2) _ u.2] at h1
          exact sub_eq_zero.1 h1
      have heq : fixMod A₀ (commV L) C = (F'.comap fU).map (commV L).subtype := by
        ext u
        constructor
        · rintro ⟨huU, hu⟩
          exact ⟨⟨u, huU⟩, (hmem ⟨u, huU⟩).2 hu, rfl⟩
        · rintro ⟨u', hu', rfl⟩
          exact ⟨u'.2, (hmem u').1 hu'⟩
      have h1 := hY₀
      rw [heq, Subgroup.card_map_of_injective (commV L).subtype_injective,
        card_comap_of_surjective hfUs, hfUk, hF'card] at h1
      have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
      rw [h2, hK, ← pow_mul, mul_comm]
    exact false_of_offender hcommĀ hinvĀ hcardĀ hfixĀ (htr ▸ hα0) hxA
  obtain ⟨u₀, hu₀, hfu₀⟩ := hfonto w
  refine ⟨u₀, hu₀, ?_⟩
  set v' := v * u₀⁻¹ with hv'
  have hcomm : ∀ l ∈ L, l v' * v'⁻¹ ∈ fixV L := by
    intro l hl
    obtain ⟨g, hg⟩ := hψsurj ⟨l, hLX hl⟩
    have hlv : l v * v⁻¹ ∈ commV L := hVGU l (le_G h hl) v
    have hlu : l u₀ * u₀⁻¹ ∈ commV L := hVGU l (le_G h hl) u₀
    have e : l v' * v'⁻¹ = (l v * v⁻¹) * (l u₀ * u₀⁻¹)⁻¹ := by
      rw [hv', map_mul, map_inv, mul_inv, mul_inv, inv_inv]
      exact mul_mul_mul_comm _ _ _ _
    have hzero : f (l v' * v'⁻¹) = 0 := by
      rw [e, hfsub _ hlv _ hlu]
      have h1 := hw' g
      rw [hα, zero_smul, sub_zero] at h1
      have h2 : φ g = f (l v * v⁻¹) := by
        show f (((ψ g : ↥X) : MulAut V) v * v⁻¹) = _
        rw [hg]
      have h3 : f (l u₀ * u₀⁻¹) = g2Act g w - w := by
        rw [hfsub _ (hXU _ (hLX hl) _ hu₀) _ hu₀, ← hfu₀, ← hψeq g u₀ hu₀, hg]
      rw [← h2, h3, h1, sub_self]
    have hmemU : l v' * v'⁻¹ ∈ commV L := by
      rw [e]
      exact (commV L).mul_mem hlv ((commV L).inv_mem hlu)
    exact ((hfker _ hmemU).1 hzero).1
  let χ : ↥L →* V :=
    { toFun := fun l => (l : MulAut V) v' * v'⁻¹
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        show ((l₁ : MulAut V) * l₂) v' * v'⁻¹ =
          ((l₁ : MulAut V) v' * v'⁻¹) * ((l₂ : MulAut V) v' * v'⁻¹)
        set d := (l₂ : MulAut V) v' * v'⁻¹ with hd
        have h1 : (l₁ : MulAut V) d = d := hcomm l₂ l₂.2 _ l₁.2
        have h2 : (l₂ : MulAut V) v' = d * v' := by rw [hd, inv_mul_cancel_right]
        rw [MulAut.mul_apply, h2, map_mul, h1, mul_assoc, mul_comm] }
  have hperf : commutator ↥L = ⊤ := (quasi_L h).1.commutator_eq_top
  have hker : χ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker χ
  intro l hl
  have h1 : χ ⟨l, hl⟩ = 1 := by
    have : (⟨l, hl⟩ : ↥L) ∈ χ.ker := by rw [hker]; trivial
    exact this
  exact mul_inv_eq_one.1 h1

end CFSG.Quasithin.B5.G2D

theorem CFSG.Quasithin.asB51G2Dual_holds
    (h42 : CFSG.Quasithin.AsB42) : CFSG.Quasithin.AsB51G2Dual := by
  intro V _ _ hV G L h hU hG2
  have hIdent := CFSG.Quasithin.FFC.asB42Ident_of_b42 h42
  obtain ⟨n, hn, hd⟩ := CFSG.Quasithin.B5.G2D.g2Data h hG2
  obtain ⟨hL, hcardS⟩ := CFSG.Quasithin.B5.G2D.g2Orders_of_derived hn hd
  rw [eq_top_iff]
  intro v _
  obtain ⟨u₀, hu₀, hv'⟩ :=
    CFSG.Quasithin.B5.G2D.exists_mem_fixV_L hIdent h42 hV h hU hn hcardS hL v
  have hvG := CFSG.Quasithin.B5.G2D.fixV_L_le_fixV_G hIdent h42 hV h hU hn hcardS hL hv'
  have e : v = u₀ * (v * u₀⁻¹) := by rw [mul_comm v, mul_inv_cancel_left]
  rw [e]
  exact Subgroup.mul_mem_sup hu₀ hvG
