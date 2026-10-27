module

public import CFSG.Quasithin.EmptyFaithful.SBd18Cl
public import CFSG.Quasithin.EmptyFaithful.SBd17Quot
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.Quasithin.SBd18

theorem no_twoComponent_of_charTwo {H : Type} [Group H] [Finite H]
    (hchar : Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H)
    {t : H} (ht2 : t * t = 1) {K : Subgroup H} (hKC : K ≤ Subgroup.centralizer ({t} : Set H))
    (hKn : ∀ c ∈ Subgroup.centralizer ({t} : Set H), c ∈ Subgroup.normalizer (K : Set H))
    (hq : CFSG.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hK2 : 2 ∣ Nat.card ↥K) : False := by
  classical
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  have hnormal : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr fun c hc => hKn c hc
  let e : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hq' : CFSG.IsQuasisimple ↥(K.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hZ' : IsPGroup 2 ↥(Subgroup.center ↥(K.subgroupOf C)) := by
    intro z
    have hzc : e z.1 ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨k', rfl⟩ := e.surjective k
      have := Subgroup.mem_center_iff.mp z.2 k'
      rw [← map_mul, ← map_mul, this]
    obtain ⟨n, hn⟩ := hZ ⟨e z.1, hzc⟩
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    have := congrArg Subtype.val hn
    simpa [map_pow] using this
  have hK2' : 2 ∣ Nat.card ↥(K.subgroupOf C) := by
    rw [Nat.card_congr e.toEquiv]
    exact hK2
  have hTC : CFSG.ComponentClassification.TwoComponents.IsTwoComponent (K.subgroupOf C) :=
    SBd17.isTwoComponent_of_normal_quasisimple hq' hZ' hK2'
  have hcore := SBd17.oddCore_eq_bot_of_centralizer_pCore_le hchar
  have hlayer := SBd17.layer_eq_bot_of_centralizer_pCore_le hchar
  have h1 := CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    CFSG.ClassicalInvolution.l2PrimeBalance hcore ht2 rfl hTC
  rw [hlayer, le_bot_iff, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKC] at h1
  have hbot : K.subgroupOf C = ⊥ := by
    rw [h1]
    exact Subgroup.bot_subgroupOf _
  have hnt := CFSG.ComponentClassification.TwoComponents.nontrivial hTC
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hbot

theorem charTwo_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.centralizer (CFSG.pCore 2 A : Set A) ≤ CFSG.pCore 2 A) :
    Subgroup.centralizer (CFSG.pCore 2 B : Set B) ≤ CFSG.pCore 2 B := by
  intro y hy
  have hcore : (CFSG.pCore 2 A).map e.toMonoidHom = CFSG.pCore 2 B :=
    CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e
  have hy' : e.symm y ∈ CFSG.pCore 2 A := by
    refine h (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    have hea : e a ∈ CFSG.pCore 2 B := by
      rw [← hcore]
      exact ⟨a, ha, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hy (e a) hea
    apply e.injective
    simpa [map_mul] using this
  rw [← hcore]
  exact ⟨e.symm y, hy', by simp⟩

theorem isPGroup_two_center_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hZ : ∀ z ∈ Subgroup.center B, z * z = 1) : IsPGroup 2 ↥(Subgroup.center A) := by
  intro z
  refine ⟨1, Subtype.ext ?_⟩
  have hzc : e z.1 ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    have := Subgroup.mem_center_iff.mp z.2 a
    rw [← map_mul, ← map_mul, this]
  have h1 := hZ _ hzc
  apply e.injective
  simpa [pow_two, ← map_mul] using h1

end CFSG.Quasithin.SBd18

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.not_conj_z (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I)
    {τ f : G} (hτS : τ ∈ Sgp153 T V₁) (hfS : f ∈ Sgp153 T V₁) (hττ : τ * τ = 1) (hff : f * f = 1)
    (hτf : τ * f = f * τ) (hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f))
    (hmove : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσL : τ * f ∉ L)
    {z : G} (hzT : ∀ g ∈ T, g * z = z * g) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∀ g : G, g⁻¹ * τ * g ≠ z := by
  classical
  intro g hg
  obtain ⟨Lτ, Lf, ⟨hLτL, hLτq, hLτZ, hLτc, hLτn⟩, -, hord⟩ :=
    r.exists_core_pair h113 hOut hτS hfS hττ hff hτf hcent hmove hσL
  have D0 := r.ctx.hyp.decomp
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hτI : τ ∈ I := r.S_le_I hτS
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  obtain ⟨v₀, hv₀V, hv₀1, hv₀τ⟩ : ∃ v₀ ∈ V₁, v₀ ≠ 1 ∧ τ * v₀ = v₀ * τ := by
    obtain ⟨v, hv, hne⟩ := hmove
    have hτN : τ ∈ Subgroup.normalizer (V₁ : Set G) :=
      (le_normalizer_of_eq_center r.hNL hV₁) hτI
    obtain ⟨w, hw⟩ : ∃ w : G, w = τ * v * τ⁻¹ := ⟨_, rfl⟩
    have hwV : w ∈ V₁ := by rw [hw]; exact (Subgroup.mem_normalizer_iff.mp hτN v).mp hv
    have hcomm : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := by
      intro a ha b hb
      have h1 := r.V_sq (a * b) (D0.le₁ (V₁.mul_mem ha hb))
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (r.V_sq a (D0.le₁ ha))
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (r.V_sq b (D0.le₁ hb))
      calc a * b = (a * b) * (a * b) * (a * b)⁻¹ := by group
        _ = (a * b)⁻¹ := by rw [h1, one_mul]
        _ = b * a := by rw [mul_inv_rev, ha', hb']
    have hτv : τ * v = w * τ := by rw [hw]; group
    have hτw : τ * w = v * τ := by
      rw [hw]
      calc τ * (τ * v * τ⁻¹) = (τ * τ) * v * τ⁻¹ := by group
        _ = v * τ := by rw [hττ, one_mul, hτinv]
    refine ⟨v * w, V₁.mul_mem hv hwV, ?_, ?_⟩
    · intro h1
      apply hne
      have hwv : w = v⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (r.V_sq v (D0.le₁ hv))
      have : w = v := hwv.trans hvinv
      rw [hτv, this]
    · calc τ * (v * w) = (τ * v) * w := by rw [mul_assoc]
        _ = (w * τ) * w := by rw [hτv]
        _ = w * (τ * w) := by rw [mul_assoc]
        _ = w * (v * τ) := by rw [hτw]
        _ = (w * v) * τ := by rw [mul_assoc]
        _ = (v * w) * τ := by rw [hcomm w hwV v hv]
  have hq := r.ctx.hyp.hyp.qtfe
  let P : Sylow 2 G := hq.sylow.1.toSylow hq.sylow.2
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzT x hx)
  have hcharz := hq.qtke.2.1 (Subgroup.centralizer ({z} : Set G))
    (isTwoLocal_centralizer_involution hz1 hz2) ⟨P, hTz⟩
  have hXz := centralizer_pCore_le_of_inf_le hcharz
  have hτ' : τ = g * z * g⁻¹ := by rw [← hg]; group
  have hmapeq : (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({τ} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hτ']
      calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
        _ = g * (z * y) * g⁻¹ := by rw [hy]
        _ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      rw [← hg]
      have h1 : x * τ = τ * x := hx
      calc g⁻¹ * x * g * (g⁻¹ * τ * g) = g⁻¹ * (x * τ) * g := by group
        _ = g⁻¹ * (τ * x) * g := by rw [h1]
        _ = (g⁻¹ * τ * g) * (g⁻¹ * x * g) := by group
  let e : ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({τ} : Set G)) :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hmapeq)
  have hcharτ := SBd18.charTwo_of_mulEquiv e hXz
  have hLτH : Lτ ≤ Subgroup.centralizer ({τ} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hLτc y hy).symm
  have hv₀H : v₀ ∈ Subgroup.centralizer ({τ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hv₀τ.symm
  have ht₀2 : (⟨v₀, hv₀H⟩ : ↥(Subgroup.centralizer ({τ} : Set G))) * ⟨v₀, hv₀H⟩ = 1 :=
    Subtype.ext (r.V_sq v₀ (D0.le₁ hv₀V))
  refine SBd18.no_twoComponent_of_charTwo hcharτ ht₀2 (K := Lτ.subgroupOf _) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    exact Subgroup.mem_centralizer_iff.mp (r.h1 hv₀V) (y : G) (hLτL (Subgroup.mem_subgroupOf.mp hy))
  · intro c hc
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcv : (c : G) * v₀ = v₀ * (c : G) := congrArg Subtype.val hc'
    have hcI : (c : G) ∈ I := hK1 v₀ hv₀V hv₀1 (Subgroup.mem_centralizer_singleton_iff.mpr hcv)
    have hcτ : (c : G) * τ = τ * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hcn := hLτn (c : G) hcI hcτ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.mp hcn (y : G)
    simpa [Subgroup.mem_subgroupOf] using this
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLτH).symm hLτq
  · refine SBd18.isPGroup_two_center_of_equiv (Subgroup.subgroupOfEquivOfLe hLτH) ?_
    intro z' hz'
    exact Subtype.ext (r.V_sq _ (D0.le₁ (hLτZ z' hz')))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLτH).toEquiv]
    have hdvd : Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) ∣ Nat.card ↥Lτ :=
      ⟨Nat.card ↥(Subgroup.center ↥Lτ),
        Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Lτ)⟩
    refine Nat.dvd_trans ?_ hdvd
    rcases hord with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> norm_num

end CFSG.Quasithin.SBd14
