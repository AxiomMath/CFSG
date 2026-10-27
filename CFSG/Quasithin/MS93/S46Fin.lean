module

public import CFSG.Quasithin.MS93.S46Qj
public import CFSG.Quasithin.MS93.S4AM

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Sums

variable {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

theorem isSumOfNaturalModulesVia_restrict {K K' V Z : Subgroup G} {φ : ↥K →* ↥Γ} {dual : Bool}
    {k : ℕ} (h : IsSumOfNaturalModulesVia K V Z φ dual k) (hK' : K' ≤ K) :
    IsSumOfNaturalModulesVia K' V Z (φ.comp (Subgroup.inclusion hK')) dual k := by
  obtain ⟨hKV, hZV, β, hβs, hβk, hβe⟩ := h
  exact ⟨hK'.trans hKV, hZV, β, hβs, hβk,
    fun a u v huv i => hβe (Subgroup.inclusion hK' a) u v huv i⟩

theorem isSumOfNaturalModulesVia_two {A V V₁ V₂ Z : Subgroup G} {φ : ↥A →* ↥Γ} {dual : Bool}
    (h₁ : IsSumOfNaturalModulesVia A V₁ Z φ dual 1) (h₂ : IsSumOfNaturalModulesVia A V₂ Z φ dual 1)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hn₁ : V ≤ Subgroup.normalizer (V₁ : Set G))
    (hn₂ : V ≤ Subgroup.normalizer (V₂ : Set G)) (hinf : V₁ ⊓ V₂ = Z) (hsup : V₁ ⊔ V₂ = V) :
    IsSumOfNaturalModulesVia A V Z φ dual 2 := by
  classical
  obtain ⟨hAV₁, hZV₁, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := h₁
  obtain ⟨hAV₂, -, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := h₂
  have hV₁V : V₁ ≤ V := hsup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hsup ▸ le_sup_right
  have hZV : Z ≤ V := hZV₁.trans hV₁V
  have hZV₂ : Z ≤ V₂ := hinf ▸ inf_le_right
  have hdec : ∀ v : ↥V, ∃ x : ↥V₁, ∃ y : ↥V₂, (x : G) * y = v := by
    intro v
    have hv : (v : G) ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by rw [hsup]; exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ (hV₁V.trans hn₂)] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hv
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩
  choose a b hab using hdec
  let c₁ : ↥V₁ → (ι → F) := fun x => Multiplicative.toAdd (β₁ x) 0
  let c₂ : ↥V₂ → (ι → F) := fun x => Multiplicative.toAdd (β₂ x) 0
  have hc₁mul : ∀ x y, c₁ (x * y) = c₁ x + c₁ y := fun x y => by simp [c₁]
  have hc₂mul : ∀ x y, c₂ (x * y) = c₂ x + c₂ y := fun x y => by simp [c₂]
  have hc₁inv : ∀ x, c₁ x⁻¹ = - c₁ x := fun x => by simp [c₁]
  have hc₂inv : ∀ x, c₂ x⁻¹ = - c₂ x := fun x => by simp [c₂]
  have hc₁Z : ∀ x : ↥V₁, (x : G) ∈ Z ↔ c₁ x = 0 := by
    intro x
    rw [← Subgroup.mem_subgroupOf, ← hβ₁k, MonoidHom.mem_ker]
    constructor
    · intro h
      simp [c₁, h]
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact h
  have hc₂Z : ∀ x : ↥V₂, (x : G) ∈ Z ↔ c₂ x = 0 := by
    intro x
    rw [← Subgroup.mem_subgroupOf, ← hβ₂k, MonoidHom.mem_ker]
    constructor
    · intro h
      simp [c₂, h]
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact h
  have hwd : ∀ (x x' : ↥V₁) (y y' : ↥V₂), (x : G) * y = x' * y' →
      c₁ x = c₁ x' ∧ c₂ y = c₂ y' := by
    intro x x' y y' h
    have hz : (x'⁻¹ * x : ↥V₁) = (((y' * y⁻¹ : ↥V₂) : G) : G) := by
      show (x' : G)⁻¹ * x = y' * (y : G)⁻¹
      calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
        _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h]
        _ = y' * (y : G)⁻¹ := by group
    have hzZ : ((x'⁻¹ * x : ↥V₁) : G) ∈ Z := by
      rw [← hinf]
      exact ⟨(x'⁻¹ * x).2, hz ▸ (y' * y⁻¹).2⟩
    have hzZ' : ((y' * y⁻¹ : ↥V₂) : G) ∈ Z := hz ▸ hzZ
    rw [hc₁Z, hc₁mul, hc₁inv, neg_add_eq_zero] at hzZ
    rw [hc₂Z, hc₂mul, hc₂inv, add_neg_eq_zero] at hzZ'
    exact ⟨hzZ.symm, hzZ'.symm⟩
  have hconj₂ : ∀ (x : ↥V₁) (y : ↥V₂), (x : G)⁻¹ * y * x ∈ V₂ := fun x y => by
    have := (Subgroup.mem_normalizer_iff.mp (hn₂ (hV₁V (V₁.inv_mem x.2))) y).mp y.2
    simpa using this
  let β : ↥V →* Multiplicative (Fin 2 → ι → F) :=
    { toFun := fun v => Multiplicative.ofAdd ![c₁ (a v), c₂ (b v)]
      map_one' := by
        have h1 := hwd (a 1) 1 (b 1) 1 (by rw [hab]; simp)
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · simpa [c₁] using h1.1
        · simpa [c₂] using h1.2
      map_mul' := fun v w => by
        set y' : ↥V₂ := ⟨(a w : G)⁻¹ * b v * a w, hconj₂ (a w) (b v)⟩ with hy'
        have hdec' : ((a v * a w : ↥V₁) : G) * (y' * b w : ↥V₂) = ((v * w : ↥V) : G) := by
          show (a v : G) * a w * ((a w : G)⁻¹ * b v * a w * b w) = v * w
          rw [← hab v, ← hab w]
          group
        obtain ⟨e1, e2⟩ := hwd (a (v * w)) (a v * a w) (b (v * w)) (y' * b w)
          (by rw [hab, hdec'])
        have hz : c₂ y' = c₂ (b v) := by
          have hmem : ((b v)⁻¹ * y' : ↥V₂) ∈ Z.subgroupOf V₂ := by
            rw [Subgroup.mem_subgroupOf, ← hinf]
            refine ⟨?_, ((b v)⁻¹ * y').2⟩
            show (b v : G)⁻¹ * ((a w : G)⁻¹ * b v * a w) ∈ V₁
            have h2 := (Subgroup.mem_normalizer_iff.mp (hn₁ (hV₂V (V₂.inv_mem (b v).2)))
              (a w)⁻¹).mp (V₁.inv_mem (a w).2)
            rw [show (b v : G)⁻¹ * ((a w : G)⁻¹ * b v * a w) =
              ((b v : G)⁻¹ * (a w : G)⁻¹ * ((b v : G)⁻¹)⁻¹) * a w by group]
            exact V₁.mul_mem h2 (a w).2
          have := (hc₂Z _).mp (Subgroup.mem_subgroupOf.mp hmem)
          rw [hc₂mul, hc₂inv, neg_add_eq_zero] at this
          exact this.symm
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
          simp [e1, hc₁mul]
        · simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
          simp [e2, hc₂mul, hz] }
  have hβ : ∀ v, β v = Multiplicative.ofAdd ![c₁ (a v), c₂ (b v)] := fun _ => rfl
  refine ⟨hAV, hZV, β, ?_, ?_, ?_⟩
  ·
    intro t
    obtain ⟨x, hx⟩ := hβ₁s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd t 0)
    obtain ⟨y, hy⟩ := hβ₂s (Multiplicative.ofAdd fun _ => Multiplicative.toAdd t 1)
    let v₀ : ↥V := ⟨x * y, V.mul_mem (hV₁V x.2) (hV₂V y.2)⟩
    refine ⟨v₀, ?_⟩
    obtain ⟨e1, e2⟩ := hwd (a v₀) x (b v₀) y (hab v₀)
    rw [hβ]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · simp [e1, c₁, hx]
    · simp [e2, c₂, hy]
  ·
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβ]
    constructor
    · intro h
      have h0 := congrFun (congrArg Multiplicative.toAdd h) 0
      have h1 := congrFun (congrArg Multiplicative.toAdd h) 1
      simp only [toAdd_ofAdd, toAdd_one] at h0 h1
      rw [← hab v]
      exact Z.mul_mem ((hc₁Z _).mpr (by simpa using h0)) ((hc₂Z _).mpr (by simpa using h1))
    · intro hv
      obtain ⟨e1, e2⟩ := hwd (a v) ⟨v, hZV₁ hv⟩ (b v) 1 (by rw [hab]; simp)
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · simp [e1, (hc₁Z ⟨v, hZV₁ hv⟩).mp hv]
      · simp [e2, c₂]
  ·
    intro g u v huv i
    set x' : ↥V₁ := ⟨(g : G) * a u * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAV₁ g.2) _).mp (a u).2⟩ with hx'
    set y' : ↥V₂ := ⟨(g : G) * b u * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAV₂ g.2) _).mp (b u).2⟩ with hy'
    obtain ⟨e1, e2⟩ := hwd (a v) x' (b v) y' (by
      rw [hab, huv, hx', hy']
      show (g : G) * u * (g : G)⁻¹ = (g : G) * a u * (g : G)⁻¹ * ((g : G) * b u * (g : G)⁻¹)
      rw [← hab u]
      group)
    have f1 := hβ₁e g (a u) x' rfl 0
    have f2 := hβ₂e g (b u) y' rfl 0
    fin_cases i
    · simp only [hβ, toAdd_ofAdd, Fin.zero_eta, Matrix.cons_val_zero]
      rw [e1]
      exact f1
    · simp only [hβ, toAdd_ofAdd, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [e2]
      exact f2

end Sums

section Layers

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem case11_of_layers (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2)
    (hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) = Fintype.card F)
    {ψ : ↥M →* ↥(StatedSL 3 F)} (hψ : Function.Surjective ψ)
    (hUψ : IsSumOfNaturalModulesVia M (Uq M T L) ⊥ ψ false 1)
    (hZ : centerOf (Vq M L) = Uq M T L) {V₁ V₂ : Subgroup G} (_hV₁ : V₁ ≤ Vq M L)
    (_hV₂ : V₂ ≤ Vq M L) (hinf : V₁ ⊓ V₂ = Uq M T L) (hsup : V₁ ⊔ V₂ = Vq M L)
    (h₁ : IsSumOfNaturalModulesVia M V₁ (Uq M T L) ψ true 1)
    (h₂ : IsSumOfNaturalModulesVia M V₂ (Uq M T L) ψ true 1) : MS93Case11 (Vq M L) T L := by
  obtain ⟨n, hn⟩ := hφ.1
  refine ⟨n, F, inferInstance, inferInstance, ψ.comp (Subgroup.inclusion h.L_le), hn, ?_, ?_, ?_,
    ?_⟩
  · intro y
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hψ y
    exact ⟨⟨ℓ, hℓL⟩, hℓ⟩
  · rw [hZ]
    exact isSumOfNaturalModulesVia_restrict hUψ h.L_le
  · rw [hZ]
    exact isSumOfNaturalModulesVia_restrict (isSumOfNaturalModulesVia_two h₁ h₂
      (le_normalizer_Vq h.le_normalizer) ((Vq_le h.L_le).trans h₁.1) ((Vq_le h.L_le).trans h₂.1)
      hinf hsup) h.L_le
  · rw [hZ, ← hn]
    exact qjInfo_of_card h hφ hT hU

end Layers

section Transport

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

@[expose] noncomputable def imMEquiv {N : Subgroup G} (hN : N ≤ M) : ↥N ≃* ↥(imM hTM N) :=
  (Subgroup.subgroupOfEquivOfLe hN).symm.trans
    (Subgroup.equivMapOfInjective (N.subgroupOf M) _ (puAmalgam hTM).ofA_injective)

theorem coe_imMEquiv {N : Subgroup G} (hN : N ≤ M) (x : ↥N) :
    ((imMEquiv hTM hN x : ↥(imM hTM N)) : (puAmalgam hTM).Universal) =
      (puAmalgam hTM).ofA ⟨x, hN x.2⟩ :=
  rfl

theorem ofA_mem_imM {K : Subgroup G} (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ imM hTM K ↔ (m : G) ∈ K := by
  rw [imM, Subgroup.mem_map_iff_mem (puAmalgam hTM).ofA_injective, Subgroup.mem_subgroupOf]

@[expose] noncomputable def imMPull (W : Subgroup (puAmalgam hTM).Universal) : Subgroup G :=
  (W.comap (puAmalgam hTM).ofA).map M.subtype

theorem imMPull_le (W : Subgroup (puAmalgam hTM).Universal) : imMPull hTM W ≤ M :=
  Subgroup.map_subtype_le _

theorem imM_imMPull {W : Subgroup (puAmalgam hTM).Universal} (hW : W ≤ imM hTM M) :
    imM hTM (imMPull hTM W) = W := by
  rw [imMPull, imM_map_subtype, Subgroup.map_comap_eq, inf_eq_right]
  exact hW.trans (Subgroup.map_le_range _ _)

theorem imM_eq_imM_iff {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM K = imM hTM K' ↔ K = K' :=
  ⟨fun h => le_antisymm ((imM_le_imM_iff hTM hK).mp h.le) ((imM_le_imM_iff hTM hK').mp h.ge),
    fun h => h ▸ rfl⟩

theorem imM_centerOf {V : Subgroup G} (hV : V ≤ M) :
    imM hTM (centerOf V) = centerOf (imM hTM V) :=
  imM_inf_centralizer hTM V hV

theorem isSumOfNaturalModulesVia_of_imM {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {dual : Bool} {k : ℕ}
    {K V Z : Subgroup G} {K₀ V₀ Z₀ : Subgroup (puAmalgam hTM).Universal} (hK : K ≤ M)
    (hV : V ≤ M) (hZ : Z ≤ M) (hK₀ : imM hTM K = K₀) (hV₀ : imM hTM V = V₀)
    (hZ₀ : imM hTM Z = Z₀) {φ : ↥K₀ →* ↥Γ} (h : IsSumOfNaturalModulesVia K₀ V₀ Z₀ φ dual k) :
    IsSumOfNaturalModulesVia K V Z
      (φ.comp ((imMEquiv hTM hK).trans (MulEquiv.subgroupCongr hK₀)).toMonoidHom) dual k := by
  subst hK₀ hV₀ hZ₀
  have hKV₀ := h.1
  have hZV₀ := h.2.1
  have hc : ∀ a ∈ K, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    have h1 : (puAmalgam hTM).ofA ⟨a, hK ha⟩ ∈ imM hTM K := (ofA_mem_imM hTM _).mpr ha
    have h2 : (puAmalgam hTM).ofA ⟨v, hV hv⟩ ∈ imM hTM V := (ofA_mem_imM hTM _).mpr hv
    have h3 := (Subgroup.mem_normalizer_iff.mp (hKV₀ h1) _).mp h2
    rw [← map_inv, ← map_mul, ← map_mul] at h3
    exact (ofA_mem_imM hTM _).mp h3
  refine isSumOfNaturalModulesVia_of_equiv h _ (imMEquiv hTM hV) ?_
    ((imM_le_imM_iff hTM hZ).mp hZV₀) ?_ ?_
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hc a ha v, fun hv => ?_⟩
    have := hc a⁻¹ (K.inv_mem ha) _ hv
    rwa [show a⁻¹ * (a * v * a⁻¹) * a⁻¹⁻¹ = v by group] at this
  · intro v
    exact (ofA_mem_imM hTM ⟨v, hV v.2⟩).symm
  · intro a u v huv
    show (puAmalgam hTM).ofA ⟨v, hV v.2⟩ = (puAmalgam hTM).ofA ⟨a, hK a.2⟩ *
      (puAmalgam hTM).ofA ⟨u, hV u.2⟩ * ((puAmalgam hTM).ofA ⟨a, hK a.2⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext huv)

end Transport

section BaseA

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem case11_of_baseA (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2)
    (hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) = Fintype.card F)
    {ψ₀ : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSL 3 F)} (hψ₀ : Function.Surjective ψ₀)
    (hU₀ : IsSumOfNaturalModulesVia (stab _ (baseA _)) (Uloc h.le L (baseA _)) ⊥ ψ₀ false 1)
    (hZ₀ : centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ =
      Uloc h.le L (baseA _))
    {W₁ W₂ : Subgroup (puAmalgam h.le).Universal}
    (hW₁ : W₁ ≤ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆)
    (hW₂ : W₂ ≤ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆)
    (hinf : W₁ ⊓ W₂ = Uloc h.le L (baseA _))
    (hsup : W₁ ⊔ W₂ = ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆)
    (h₁ : IsSumOfNaturalModulesVia (stab _ (baseA _)) W₁ (Uloc h.le L (baseA _)) ψ₀ true 1)
    (h₂ : IsSumOfNaturalModulesVia (stab _ (baseA _)) W₂ (Uloc h.le L (baseA _)) ψ₀ true 1) :
    MS93Case11 (Vq M L) T L := by
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hVM : Vq M L ≤ M := Vq_le h.L_le
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hLt : Ltil h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hUl : Uloc h.le L (baseA _) = imM h.le (Uq M T L) :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hUM).2
      (le_normalizer_Uq h.le_normalizer))
  have hV : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ = imM h.le (Vq M L) := by
    rw [hQ, hLt, imM_commutator h.le hOM h.L_le]
  have hstab : imM h.le M = stab (puAmalgam h.le) (baseA _) := (puAmalgam.stab_baseA h.le).symm
  have hVα : imM h.le (Vq M L) ≤ imM h.le M := imM_mono h.le hVM
  have hi₁ : imM h.le (imMPull h.le W₁) = W₁ := imM_imMPull h.le ((hV ▸ hW₁).trans hVα)
  have hi₂ : imM h.le (imMPull h.le W₂) = W₂ := imM_imMPull h.le ((hV ▸ hW₂).trans hVα)
  have hP₁ := imMPull_le h.le W₁
  have hP₂ := imMPull_le h.le W₂
  have hbot : imM h.le (⊥ : Subgroup G) = ⊥ := by
    rw [imM, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  refine case11_of_layers h hφ hT hU (V₁ := imMPull h.le W₁) (V₂ := imMPull h.le W₂)
    (ψ := ψ₀.comp ((imMEquiv h.le le_rfl).trans (MulEquiv.subgroupCongr hstab)).toMonoidHom)
    (hψ₀.comp (MulEquiv.surjective _))
    (isSumOfNaturalModulesVia_of_imM h.le le_rfl hUM bot_le hstab hUl.symm hbot hU₀) ?_ ?_ ?_ ?_ ?_
    (isSumOfNaturalModulesVia_of_imM h.le le_rfl hP₁ hUM hstab hi₁ hUl.symm h₁)
    (isSumOfNaturalModulesVia_of_imM h.le le_rfl hP₂ hUM hstab hi₂ hUl.symm h₂)
  · rw [← imM_eq_imM_iff h.le (show centerOf (Vq M L) ≤ M from inf_le_left.trans hVM) hUM,
      imM_centerOf h.le hVM, ← hV, hZ₀, hUl]
  · rw [← imM_le_imM_iff h.le hP₁, hi₁, ← hV]
    exact hW₁
  · rw [← imM_le_imM_iff h.le hP₂, hi₂, ← hV]
    exact hW₂
  · rw [← imM_eq_imM_iff h.le (inf_le_left.trans hP₁) hUM, imM_inf, hi₁, hi₂, hinf, hUl]
  · have hs : imM h.le (imMPull h.le W₁ ⊔ imMPull h.le W₂) =
        imM h.le (imMPull h.le W₁) ⊔ imM h.le (imMPull h.le W₂) := by
      simp only [imM]
      rw [Subgroup.subgroupOf_sup hP₁ hP₂, Subgroup.map_sup]
    rw [← imM_eq_imM_iff h.le (sup_le hP₁ hP₂) hVM, hs, hi₁, hi₂, hsup, hV]

end BaseA

end CFSG.Quasithin.MS93.S46
