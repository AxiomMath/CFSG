module

public import CFSG.Quasithin.EmptyFaithful.R3c10Cl
public import CFSG.Quasithin.EmptyFaithful.R3c11L3b
public import CFSG.Quasithin.EmptyFaithful.R3c11Pl
public import CFSG.Quasithin.EmptyFaithful.R3c9Lie
public import CFSG.Quasithin.EmptyFaithful.S153D57

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Ctx2

variable {G : Type} [Group G] [Finite G]

theorem ctx2_facts {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    Yp ≤ Subgroup.normalizer (V₂ : Set G) ∧
      (∀ x ∈ V₂, (∀ a ∈ Yp, a * x = x * a) → x = 1) ∧ V₂ ≤ Yp ∧
        M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV14 : Nat.card V₁ = 4 := hh.decomp.card₁
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  obtain ⟨hY₁, hY₂⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
  have hYN₁ : Yp ≤ Subgroup.normalizer (V₁ : Set G) := hh.Yp_le_Y153.trans hY₁
  have hYN₂ : Yp ≤ Subgroup.normalizer (V₂ : Set G) := hh.Yp_le_Y153.trans hY₂
  obtain ⟨y, hyO, -, hyfpf⟩ := hh.hyp.exists_Yplus_fpf h113 hh.decomp
  have hyY153 : y ∈ Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) := oTwoUpper_le _ hyO
  have hyYp : y ∈ Yp := by
    rcases hh.cases with hYeq | ⟨-, hYeq⟩
    · rw [hYeq]
      exact hyY153.1
    · rw [hYeq]
      exact hyO
  have hy1 : ∀ a ∈ V₁, y * a = a * y := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hyY153.2 a ha).symm
  have hyV₂ : ∀ u ∈ V₂, y * u * y⁻¹ ∈ V₂ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hYN₂ hyYp) u).mp hu
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [c.facts.theta]
      rw [thetaOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [c.facts.theta]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, 1, by simpa using hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : V₂ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      rw [this, Subgroup.card_bot] at hV4
      omega
    apply hyfpf u hu hu1
    have := Subgroup.mem_centralizer_iff.mp (hle hyYp) u hu
    calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [this]
      _ = u := by group
  have hfix : ∀ x ∈ V₂, (∀ a ∈ Yp, a * x = x * a) → x = 1 :=
    fixed_eq_one_of_gen hV4 hgen hYN₂ hact
  have hV2N : V₂ ≤ Subgroup.normalizer (Yp : Set G) := fun v hv =>
    hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
  have hV2Y : V₂ ≤ Yp := by
    rcases R3c9.centralizes_or_le_of_generated_by_threePow hgen.le hV2N hYN₂ hV4 with hc | ⟨hle, -⟩
    · exfalso
      apply hact
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hc x hx v hv).symm
    · exact hle
  refine ⟨hYN₂, hfix, hV2Y, ?_⟩
  have hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb => by
    have := hh.hyp.elemAbelian.1.is_comm.comm ⟨a, hh.decomp.le₁ ha⟩ ⟨b, hh.decomp.le₂ hb⟩
    exact congrArg Subtype.val this
  have hSyl' : IsSylowTwoOf (Sgp153 T V₁) (M ⊓ I) :=
    A4.isSylowTwoOf_mono c.facts.sylow (le_inf hSM hSI) inf_le_right
  refine R3c11.le_normalizer_of_swap (V₁ := V₁) hSyl' (hh.hyp.Sgp153_le_normalizer_V₂ hh.decomp)
    fun m hm => ?_
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer hm.1
  have hconj : ∀ w ∈ Yp, m⁻¹ * w * m ∈ Yp := fun w hw => by
    have := (Subgroup.mem_normalizer_iff.mp (hMIY ((M ⊓ I).inv_mem hm)) w).mp hw
    simpa using this
  have key : ∀ W : Subgroup G, W ≤ VZ T M → Nat.card W = 4 →
      Yp ≤ Subgroup.normalizer (W : Set G) →
        W.map (MulAut.conj m).toMonoidHom = V₁ ∨ W.map (MulAut.conj m).toMonoidHom = V₂ := by
    intro W hWV hW4 hYW
    have hE4 : Nat.card (W.map (MulAut.conj m).toMonoidHom) = 4 := by
      rw [← hW4]
      exact (Nat.card_congr (W.equivMapOfInjective _ (MulAut.conj m).injective).toEquiv).symm
    have hEle : W.map (MulAut.conj m).toMonoidHom ≤ V₁ ⊔ V₂ := by
      rw [hh.decomp.sup]
      rintro x ⟨v, hv, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hmN v).mp (hWV hv)
      simpa using this
    have hyE : ∀ e ∈ W.map (MulAut.conj m).toMonoidHom,
        y * e * y⁻¹ ∈ W.map (MulAut.conj m).toMonoidHom := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨(m⁻¹ * y * m) * v * (m⁻¹ * y * m)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYW (hconj y hyYp)) v).mp hv, ?_⟩
      show m * ((m⁻¹ * y * m) * v * (m⁻¹ * y * m)⁻¹) * m⁻¹ = y * (m * v * m⁻¹) * y⁻¹
      group
    exact R3c11.plane_eq hcomm hV14 hV4 hE4 hEle hyE hyV₂ hy1 hyfpf
  have k2 := key V₂ hh.decomp.le₂ hV4 hYN₂
  have k1 := key V₁ hh.decomp.le₁ hV14 hYN₁
  have hmap : ∀ (W : Subgroup G) (v : G), v ∈ W → m * v * m⁻¹ ∈ W.map (MulAut.conj m).toMonoidHom :=
    fun W v hv => ⟨v, hv, rfl⟩
  rcases k2 with h2 | h2
  · rcases k1 with h1 | h1
    · exfalso
      have heq : V₂ = V₁ :=
        Subgroup.map_injective (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
          (h2.trans h1.symm)
      have hle : V₂ ≤ V₁ ⊓ V₂ := le_inf heq.le le_rfl
      rw [hh.decomp.inf, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hV4
      omega
    · refine Or.inr ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [← h2]
        exact hmap V₂ v hv
      · rw [← h1]
        exact hmap V₁ v hv
  · exact Or.inl fun v hv => by
      rw [← h2]
      exact hmap V₂ v hv

omit [Finite G] in
theorem exists_ne_one_centralizes {E W : Subgroup G} (hEW : E ≤ Subgroup.normalizer (W : Set G))
    (hE : Nat.card E = 9) (hW : Nat.card W = 4) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ w ∈ W, e * w = w * e := by
  classical
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  let ψ : ↥E →* Equiv.Perm ↥W :=
    (MulAut.toPerm ↥W).comp ((Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hEW))
  have hψ : ∀ (b : ↥E) (w : ↥W), ((ψ b w : ↥W) : G) = (b : G) * (w : G) * (b : G)⁻¹ :=
    fun b w => rfl
  have h24 : Nat.card (Equiv.Perm ↥W) = 24 := by
    have : Fintype ↥W := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hW]
    rfl
  have hr : Nat.card ψ.range ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [h24] at this
  have hk : Nat.card ψ.ker * Nat.card ψ.range = 9 := by
    have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card E := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hE] at h1
    exact h1
  have hr9 : Nat.card ψ.range ∣ 9 := Dvd.intro_left _ hk
  have hr3 : Nat.card ψ.range ∣ 3 := by
    have := Nat.dvd_gcd hr hr9
    simpa using this
  have hker1 : ψ.ker ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hk
    have := Nat.le_of_dvd (by norm_num) hr3
    omega
  obtain ⟨e₀, he₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker1
  have he₀ψ : ψ (e₀ : ↥E) = 1 := e₀.2
  refine ⟨((e₀ : ↥E) : G), (e₀ : ↥E).2, fun h1 => he₀ ?_, fun w hw => ?_⟩
  · exact Subtype.ext (Subtype.ext h1)
  · have h2 := congrArg (fun p : Equiv.Perm ↥W => ((p ⟨w, hw⟩ : ↥W) : G)) he₀ψ
    simp only [hψ] at h2
    have e : ((e₀ : ↥E) : G) * w * ((e₀ : ↥E) : G)⁻¹ = w := h2
    calc ((e₀ : ↥E) : G) * w = (((e₀ : ↥E) : G) * w * ((e₀ : ↥E) : G)⁻¹) * ((e₀ : ↥E) : G) := by group
      _ = w * ((e₀ : ↥E) : G) := by rw [e]

theorem cl_core {L Q V : Subgroup G} (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hSG : ∀ T : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ → R3c11.SylowGoodCl T)
    (hV4 : Nat.card V = 4) (hVQ : V ≤ Q)
    (hBV : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVz : ∀ x ∈ V, x ∈ centerOf L → x = 1)
    {e : G} (heL : e ∈ L) (heQ : e ∈ Subgroup.normalizer (Q : Set G))
    (hec : ∀ v ∈ V, e * v = v * e) : e ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : Q ≤ L := hQ.1
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set T : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hTsyl : IsSylowTwoOf T ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hG : R3c11.SylowGoodCl T := hSG T hTsyl
  set Vbar : Subgroup (↥L ⧸ Z) := (V.subgroupOf L).map π with hVbar
  have hVL : V ≤ L := hVQ.trans hPL
  have hNT : ∀ x ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)),
      ∃ l : ↥L, π l = x ∧ (l : G) ∈ L ⊓ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨l, rfl⟩ := hsurj x
    have hl : l ∈ Subgroup.normalizer ((Q.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [← hNcomap]
      exact hx
    have hlN : (l : G) ∈ Subgroup.normalizer (Q : Set G) :=
      (SBc2.mem_normalizer_subgroupOf_iff hPL l).mp hl
    exact ⟨l, rfl, l.2, hlN⟩
  have hNV : Subgroup.normalizer (T : Set (↥L ⧸ Z)) ≤
      Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := by
    intro x hx
    obtain ⟨l, rfl, hlB⟩ := hNT x hx
    have hlV : (l : G) ∈ Subgroup.normalizer (V : Set G) := hBV hlB
    have hlV' : l ∈ Subgroup.normalizer ((V.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hVL l).mpr hlV
    refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
    obtain ⟨a, ha, rfl⟩ := hvbar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlV' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  have hVT : Vbar ≤ T := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hVQ (Subgroup.mem_subgroupOf.mp hx))
  have hKcard : Nat.card (V.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  have hinj : Function.Injective (π.comp (V.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card Vbar = 4 := by
    have h1 : (π.comp (V.subgroupOf L).subtype).range = Vbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  have hV1 : Vbar ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hVbar4
    omega
  have hTV : T ≤ Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := Subgroup.le_normalizer.trans hNV
  have hvc : Vbar ≤ centerOf T := hG.vcen Vbar hVT hVbar4 hTV
  have hcl : centerOf T ≤ Vbar := hG.cenle Vbar hVT hV1 hNV
  have hcard : Nat.card (centerOf T) = 4 := by
    rw [le_antisymm hcl hvc]
    exact hVbar4
  have hmemN : π ⟨e, heL⟩ ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)) := by
    have h1 : (⟨e, heL⟩ : ↥L) ∈ Subgroup.normalizer ((Q.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hPL _).mpr heQ
    rw [← hNcomap] at h1
    exact h1
  have hcomm : ∀ z ∈ centerOf T, π ⟨e, heL⟩ * z = z * π ⟨e, heL⟩ := by
    intro z hz
    obtain ⟨x₀, hx₀, rfl⟩ := hcl hz
    have hxV : (x₀ : G) ∈ V := Subgroup.mem_subgroupOf.mp hx₀
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hec _ hxV)
  have hmemT : π ⟨e, heL⟩ ∈ T := hG.cent hcard _ hmemN hcomm
  have h2 : (⟨e, heL⟩ : ↥L) ∈ T.comap π := hmemT
  rw [hTcomap] at h2
  exact Subgroup.mem_subgroupOf.mp h2

end Ctx2

section Main

variable {G : Type} [Group G] [Finite G]

theorem l3_cl {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : IsPSL 3 2 f (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  obtain ⟨hYN, hfix, hV2Y, hMIV⟩ := ctx2_facts h113 c
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Q ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun a ha => Subgroup.mem_centralizer_iff.mp hxc.2 a (hYL ha)
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  have hD : BorelData (↥L ⧸ Subgroup.center ↥L) := borelData_psl3 hf h
  have hYQ : Yp ≤ Subgroup.normalizer (Q : Set G) := by
    rcases l3_par hf hZ hQsyl h hV4 hVz hVQ hQV (Yp ⊔ Q) le_sup_right
        (sup_le hYL (inf_le_right : Q ≤ L)) (sup_le hYN hQV) with h' | h'
    · exact le_sup_left.trans h'
    · exact (c.c33.not_le (h'.trans (sup_le hYpM (inf_le_left.trans hSM)))).elim
  have hXL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hYL.trans Subgroup.le_normalizer) hSL
  have hXQ : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := sup_le hYQ hSQ
  have hBX : Yp ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
    SBc2.le_normalizer_borel hXL hXQ
  have hcent := (R3c8.borelLift_of_pkg hq hZ hQsyl hD.pkg).1
  have hChar : CharTwo (L ⊓ Subgroup.normalizer (Q : Set G)) :=
    R3c8.charTwo_borel_of_cent hQsyl hcent
  have hBMI : L ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ I :=
    c.c33.inv_le _ (inf_le_left.trans (le_conjClosure L (Sgp153 T V₁))) hBX hChar
  have hBV : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (V₂ : Set G) :=
    hBMI.trans hMIV
  obtain ⟨E, hEY, hE, hE9⟩ := exists_nine_of_pRank_two c.rank
  obtain ⟨e, heE, he1, hec⟩ := exists_ne_one_centralizes (hEY.trans hYN) hE9 hV4
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have heQ : e ∈ Q := cl_core hZ hQsyl (R3c11.sylowGoodCl_psl3 hf h) hV4 hVQ hBV hVz
    (hYL (hEY heE)) (hYQ (hEY heE)) hec
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQsyl.2.1) (⟨e, heQ⟩ : ↥Q)
  have hj' : orderOf e = 2 ^ j := by
    rw [← hj]
    exact Subgroup.orderOf_coe (⟨e, heQ⟩ : ↥Q)
  have hdvd : 2 ^ j ∣ 3 := by
    rw [← hj']
    exact orderOf_dvd_of_pow_eq_one he3
  have hj0 : 2 ^ j = 1 :=
    (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
  rw [hj0, orderOf_eq_one_iff] at hj'
  exact he1 hj'

end Main

section Cases

@[expose] def Lemma115LieHighRest (X : Type) [Group X] : Prop :=
  (((∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1)) ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1

theorem lemma115LieHighTwo_cases_rest {X : Type} [Group X] (h : Lemma115LieHighTwo X) :
    Lemma115LieHighRest X ∨
      ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f := by
  rcases h with (((⟨f, hfam⟩ | hTits) | hL45) | ⟨⟨e⟩⟩ | hU33)
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩
    · exact Or.inr ⟨f, hf, hm⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inl ⟨hf, hm⟩⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩))⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hTits)))
  · exact Or.inl (Or.inl (Or.inr hL45))
  · exact Or.inl (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inl (Or.inr (Or.inr hU33))

end Cases

section Residue

@[expose] def Input15335CloseLieRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieHigh_of_rest (h113 : StageLemma14113) (kR : Input15335CloseLieRest) :
    Input15335CloseLieHigh := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hHigh
  rcases lemma115LieHighTwo_cases_rest hHigh with hRest | ⟨f, hf, h⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  · exact (l3_cl h113 c hN hYL hf h).elim

end Residue

end CFSG.Quasithin.R3c10
