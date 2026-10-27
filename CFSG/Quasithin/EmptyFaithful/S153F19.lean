module

public import CFSG.Quasithin.EmptyFaithful.S153YCases
public import CFSG.Quasithin.EmptyFaithful.S153D15
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Lin2QuotIsLin2OrA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V : Subgroup G),
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
      C27Concl H R M K V → IsLin2Quot K → IsLin2Block H K ∨ IsAltType K 5

@[expose] def A5Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsAltType L 5 →
      IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L ∧ Yp = YL153 Yp L ⊔ YC153 Yp L ∧
        IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∧ blockZ L = ⊥ ∧
        ∀ v ∈ VZ T M, ∃ a ∈ blockU L ⊓ Subgroup.centralizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G),
          ∃ b ∈ Subgroup.centralizer (L : Set G), v = a * b

@[expose] def A5FixedPoints : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsAltType L 5 → IsSylowTwoOf P L →
    ∀ y ∈ L, y ∈ Subgroup.normalizer (P : Set G) → Odd (orderOf y) →
      y ∈ Subgroup.centralizer ((blockU L ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G)

@[expose] def A5OddCommuting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsAltType L 5 → blockZ L = ⊥ →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → Odd (orderOf y) →
      (∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L) → y ∈ Subgroup.centralizer (blockU L : Set G)

@[expose] def V2CommutatorYp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ⁅V₂, Yp⁆ = V₂

namespace S153F

open CFSG.Quasithin.S153D

section Helpers

variable {G : Type} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer {L : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.centralizer (L : Set G)) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.mp hz _ h1
  calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [h2]
    _ = g * z * g⁻¹ * l := by group

theorem commutator_sup_le {K X A B : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hA : ∀ x ∈ X, ∀ y ∈ A, ⁅x, y⁆ ∈ K)
    (hB : ∀ x ∈ X, ∀ y ∈ B, ⁅x, y⁆ ∈ K) : ⁅X, A ⊔ B⁆ ≤ K := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (K : Set G) ∧ ∀ x ∈ X, ⁅x, y⁆ ∈ K}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y z ⟨hyN, hy⟩ ⟨hzN, hz⟩
        refine ⟨mul_mem hyN hzN, fun x hx => ?_⟩
        have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (hy x hx) ((Subgroup.mem_normalizer_iff.mp hyN _).mp (hz x hx))
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        refine ⟨inv_mem hyN, fun x hx => ?_⟩
        have e : ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆)⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 : (⁅x, y⁆)⁻¹ ∈ K := inv_mem (hy x hx)
        have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) _).mp h1
        simpa using h2 }
  have hAS : A ≤ S := fun y hy => ⟨hAN hy, fun x hx => hA x hx y hy⟩
  have hBS : B ≤ S := fun y hy => ⟨hBN hy, fun x hx => hB x hx y hy⟩
  have hsup : A ⊔ B ≤ S := sup_le hAS hBS
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (hsup hy).2 x hx

omit [Group G] in
theorem card_eq_nine_of_isElemAbelianOfRank {X : Type} [Group X] (h : IsElemAbelianOfRank 3 2 X) :
    Nat.card X = 9 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem eq_one_of_mem_pCoreOf_of_odd [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 X)
    (ho : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨x, hx⟩
  have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx2
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)

theorem mem_normalizer_centralizer_of_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_centralizer_of_mem_normalizer hg hz, fun hz => ?_⟩
  have h1 := conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at h1

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input15319_of_named_inputs (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kC : Lin2QuotIsLin2OrA5) (kS : A5Setup) (kF : A5FixedPoints) (kO : A5OddCommuting) (kV : V2CommutatorYp) :
    Input15319 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ n18 hQ
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hA5 : IsAltType L 5 := by
    rcases kC G I (R153 T V₁ Yp) (M ⊓ I) L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))
      c.c16.R_norm rfl c.c16.desc hQ with h | h
    · exact absurd h n18
    · exact h
  obtain ⟨hRL, hYpeq, hE9, hZ, hVdec⟩ := kS G T Mc M V₁ V₂ Yp I L t c hA5
  have hYpN : Yp ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYLV : YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hxo⟩
    have hxP : x ∈ Subgroup.normalizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G) :=
      F7.le_normalizer_inf (X := Yp ⊓ L) (inf_le_left.trans hYpN)
        (inf_le_right.trans Subgroup.le_normalizer) hx
    have hxA := kF G L (R153 T V₁ Yp ⊓ L) hA5 hRL x hx.2 hxP hxo
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hVdec v hv
    have hxa := Subgroup.mem_centralizer_iff.mp hxA a ha
    have hxb := Subgroup.mem_centralizer_iff.mp hb x hx.2
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [hxb]
      _ = (a * x) * b := by group
      _ = (x * a) * b := by rw [← hxa]
      _ = x * (a * b) := by group
  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M := by
    rcases hh.cases with hY | ⟨hU, -⟩
    · exfalso
      have hY' := hY
      rcases Hyp153.lemma_15_3_7_cases h113 hh.hyp with ⟨hcore, -⟩ | ⟨hP, -⟩
      ·
        apply c.c16.YL_ne
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨hx, hxo⟩
        have hxY : x ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
          ⟨hY ▸ hx.1, hYLV (Subgroup.subset_closure ⟨hx, hxo⟩)⟩
        exact Subgroup.mem_bot.mpr (eq_one_of_mem_pCoreOf_of_odd (hcore ▸ hxY) hxo)
      ·
        have h9 := card_eq_nine_of_isElemAbelianOfRank hE9
        rw [hY] at h9
        have h27 := hP.2.1
        rw [h9] at h27
        norm_num at h27
    · exact hU
  have hN2 : Subgroup.normalizer (V₂ : Set G) ≤ M :=
    (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU).2
  have hYCU : YC153 Yp L ≤ Subgroup.centralizer (blockU L : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, hyo⟩
    obtain ⟨-, hyL, -, hycomm⟩ := hy
    exact kO G L hA5 hZ y hyL hyo (fun l hl => hycomm l hl)
  have hUL : blockU L ≤ L := by
    rw [blockU, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁L : g₁ ∈ L := pCoreOf_le 2 L hg₁
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hg₁L hg₂) (inv_mem hg₁L)) (inv_mem hg₂)
  have hV₂ : V₂ ≤ Subgroup.centralizer (L : Set G) := by
    have e : ⁅V₂, Yp⁆ = ⁅V₂, YL153 Yp L ⊔ YC153 Yp L⁆ := congrArg (fun Z => ⁅V₂, Z⁆) hYpeq
    have hYCle : YC153 Yp L ≤ Yp := fun y hy => by
      obtain ⟨hyYp, -⟩ := (Subgroup.closure_le _).mpr (fun z hz => hz.1) hy
      exact hyYp
    have hcomm : ⁅V₂, YL153 Yp L ⊔ YC153 Yp L⁆ ≤ Subgroup.centralizer (L : Set G) := by
      refine commutator_sup_le (K := Subgroup.centralizer (L : Set G)) ?_ ?_ ?_ ?_
      · intro g hg
        exact mem_normalizer_centralizer_of_mem_normalizer
          (Subgroup.le_normalizer ((hYLle hg).2))
      · intro g hg
        exact mem_normalizer_centralizer_of_mem_normalizer (hYpL (hYCle hg))
      · intro x hx y hy
        have hxy := Subgroup.mem_centralizer_iff.mp (hYLV hy) x (hh.decomp.le₂ hx)
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy]
        exact one_mem _
      · intro x hx y hy
        obtain ⟨a, ha, b, hb, rfl⟩ := hVdec x (hh.decomp.le₂ hx)
        have hya := Subgroup.mem_centralizer_iff.mp (hYCU hy) a ha.1
        have hyN : y ∈ Subgroup.normalizer (L : Set G) := hYpL (hYCle hy)
        have hbyc : ⁅b, y⁆ ∈ Subgroup.centralizer (L : Set G) := by
          have h1 : y * b⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
            conj_mem_centralizer_of_mem_normalizer hyN (inv_mem hb)
          have e1 : ⁅b, y⁆ = b * (y * b⁻¹ * y⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e1]
          exact mul_mem hb h1
        have hay : a⁻¹ * y⁻¹ = y⁻¹ * a⁻¹ := by
          have : y * a = a * y := hya.symm
          calc a⁻¹ * y⁻¹ = (y * a)⁻¹ := by group
            _ = (a * y)⁻¹ := by rw [this]
            _ = y⁻¹ * a⁻¹ := by group
        have e2 : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ := by
          simp only [commutatorElement_def]
          calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * b * y * b⁻¹ * (a⁻¹ * y⁻¹) := by group
            _ = a * b * y * b⁻¹ * (y⁻¹ * a⁻¹) := by rw [hay]
            _ = a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ := by group
        rw [e2]
        exact conj_mem_centralizer_of_mem_normalizer
          (Subgroup.le_normalizer (hUL ha.1)) hbyc |> fun h => by simpa using h
    have := kV G T Mc M V₁ V₂ Yp t hh
    rw [e] at this
    exact this ▸ hcomm
  have hLN : L ≤ Subgroup.normalizer (V₂ : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      ((Subgroup.mem_centralizer_iff.mp (hV₂ hv)) l hl).symm)
  exact hLn (le_inf (hLN.trans hN2) hLle)

end Main

end S153F

end CFSG.Quasithin
