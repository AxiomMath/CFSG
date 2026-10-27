module

public import CFSG.Quasithin.Background.SmithC27B210
public import CFSG.Quasithin.Background.SmithC27Frattini
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.C124AsmOrder
public import CFSG.Quasithin.Background.C124YZBase
public import CFSG.Quasithin.Background.C124B51Hyp

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Raw

variable {H R M K V : Subgroup G}

theorem b51Hyp_jP (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hA21 : AsA21SQTKSection) :
    B51Hyp (ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R))) (autI hV K) := by
  obtain ⟨hstab, -, hF⟩ := stable_branch h hs hV
  exact C124.b51Hyp_ffJP hV hA21 (h.hyp.sqtk.mono h.sup_le) hs.le_normalizer_V le_sup_left
    hstab hF hs.quasisimple hs.pCore_K_eq_bot

theorem moduleType_of (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hA21 : AsA21SQTKSection) (hB51 : AsB51) :
    IsStableFF (autI hV (K ⊔ R)) (C124.offenderImagesConjIn hV (K ⊔ R) R) ∧
      ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R)) ≤ ffJ (autI hV (K ⊔ R)) ∧
      quasithinGenFitting (ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R))) =
        autI hV K ∧
      B51Hyp (ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R))) (autI hV K) ∧
      B51Conclusion (ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R)))
        (autI hV K) ∧
      B56QuasisimpleList ↥(autI hV K) := by
  obtain ⟨hstab, hle, hF⟩ := stable_branch h hs hV
  have hHyp := b51Hyp_jP h hs hV hA21
  have hC := hB51 (IntMod V hV) IntMod.sq_eq_one _ _ hHyp
  exact ⟨hstab, hle, hF, hHyp, hC, FFC.b56List_of_b51 hC⟩

end Raw

section Gen

omit [Finite G] in
theorem le_normalizer_commutator' {Y A B : Subgroup G} (hA : Y ≤ Subgroup.normalizer (A : Set G))
    (hB : Y ≤ Subgroup.normalizer (B : Set G)) :
    Y ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hy),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hy)]

omit [Finite G] in
theorem le_normalizer_sup' {Y A B : Subgroup G} (hA : Y ≤ Subgroup.normalizer (A : Set G))
    (hB : Y ≤ Subgroup.normalizer (B : Set G)) :
    Y ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hy),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hy)]

omit [Finite G] in
theorem commutator_le_commutator_commutator {X V K : Subgroup G} (hVX : V ≤ X) (hKX : K ≤ X)
    (hperf : ⁅K, K⁆ = K)
    (hW : X ≤ Subgroup.normalizer ((⁅⁅V, K⁆, K⁆ : Subgroup G) : Set G)) :
    ⁅V, K⁆ ≤ ⁅⁅V, K⁆, K⁆ := by
  have hconj : ∀ g ∈ X, ∀ w ∈ ⁅⁅V, K⁆, K⁆, g * w * g⁻¹ ∈ ⁅⁅V, K⁆, K⁆ := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hW hg) w).mp hw
  have hconj' : ∀ g ∈ X, ∀ w ∈ ⁅⁅V, K⁆, K⁆, g⁻¹ * w * g ∈ ⁅⁅V, K⁆, K⁆ := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff''.mp (hW hg) w).mp hw
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_self K
  have key : ∀ c ∈ ⁅K, K⁆, ∀ v ∈ V, ⁅c, v⁆ ∈ ⁅⁅V, K⁆, K⁆ := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hc
      intro v hv
      have e : ⁅v, ⁅x, y⁆⁆ = (x * v) * ⁅⁅v⁻¹, x⁻¹⁆, y⁆ * (x * v)⁻¹ *
          ((x * y) * ⁅⁅y⁻¹, v⁆, x⁻¹⁆ * (x * y)⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      have h₁ : ⁅v⁻¹, x⁻¹⁆ ∈ ⁅V, K⁆ :=
        Subgroup.commutator_mem_commutator (V.inv_mem hv) (K.inv_mem hx)
      have h₂ : ⁅y⁻¹, v⁆ ∈ ⁅V, K⁆ :=
        Subgroup.commutator_comm_le K V (Subgroup.commutator_mem_commutator (K.inv_mem hy) hv)
      rw [← commutatorElement_inv v, e]
      exact Subgroup.inv_mem _ <| Subgroup.mul_mem _
        (hconj _ (X.mul_mem (hKX hx) (hVX hv)) _ (Subgroup.commutator_mem_commutator h₁ hy))
        (hconj _ (X.mul_mem (hKX hx) (hKX hy)) _
          (Subgroup.commutator_mem_commutator h₂ (K.inv_mem hx)))
    | one =>
      intro v _
      simp
    | mul c₁ c₂ hc₁ _ ih₁ ih₂ =>
      intro v hv
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Subgroup.mul_mem _ (hconj _ (hKX (hKK hc₁)) _ (ih₂ v hv)) (ih₁ v hv)
    | inv c hc ih =>
      intro v hv
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      exact hconj' _ (hKX (hKK hc)) _ (Subgroup.inv_mem _ (ih v hv))
  calc ⁅V, K⁆ = ⁅⁅K, K⁆, V⁆ := by rw [hperf, Subgroup.commutator_comm]
    _ ≤ ⁅⁅V, K⁆, K⁆ := Subgroup.commutator_le.mpr key

theorem card_comap_of_surjective' {A B : Type*} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) (S : Subgroup B) :
    Nat.card (S.comap f) = Nat.card S * Nat.card f.ker := by
  let f' : ↥(S.comap f) →* ↥S := (f.comp (S.comap f).subtype).codRestrict S fun x => x.2
  have hf' : Function.Surjective f' := by
    rintro ⟨s, hs⟩
    obtain ⟨a, rfl⟩ := hf s
    exact ⟨⟨a, hs⟩, rfl⟩
  have hker : Nat.card f'.ker = Nat.card f.ker := by
    have hle : f.ker ≤ S.comap f := fun x hx => by
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_comap, hx]
      exact S.one_mem
    have e : f'.ker = f.ker.subgroupOf (S.comap f) := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hf').toEquiv, hker]

end Gen

section Block

variable {H R M K V : Subgroup G}

omit [Finite G] in
theorem commutator_V_K_le_V (hs : StarHyp R K V) : ⁅V, K⁆ ≤ V := by
  refine Subgroup.commutator_le.2 fun v hv k hk => ?_
  have hk' : k * v⁻¹ * k⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hs.K_le_normalizer_V hk) _).1 (V.inv_mem hv)
  have e : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv hk'

omit [Finite G] in
theorem commutator_V_K_le_K (hs : StarHyp R K V) : ⁅V, K⁆ ≤ K := by
  refine Subgroup.commutator_le.2 fun v hv k hk => ?_
  have hvK : v * k * v⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.1 (hs.le_normalizer (hs.red.1 hv)) k).1 hk
  rw [commutatorElement_def]
  exact K.mul_mem hvK (K.inv_mem hk)

theorem commutator_V_K_le_pCore (hs : StarHyp R K V) : ⁅V, K⁆ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : K ≤ Subgroup.normalizer ((pCoreOf 2 (K ⊔ R) ⊓ K : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk), Subgroup.le_normalizer hk⟩
  have h3 : pCoreOf 2 (K ⊔ R) ⊓ K ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hn ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact fun x hx => h3 ⟨C124.le_pCoreOf_of_reduced hs.red (commutator_V_K_le_V hs hx),
    commutator_V_K_le_K hs hx⟩

theorem commutator_V_K_le_comm (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    ⁅V, K⁆ ≤ ⁅⁅V, K⁆, K⁆ :=
  commutator_le_commutator_commutator hs.red.1 le_sup_left h.perfect
    (le_normalizer_commutator' (le_normalizer_commutator' hs.red.2.1 hs.le_normalizer)
      hs.le_normalizer)

theorem commutator_V_K_le_blockU (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    ⁅V, K⁆ ≤ blockU K :=
  (commutator_V_K_le_comm h hs).trans (Subgroup.commutator_mono (commutator_V_K_le_pCore hs) le_rfl)

omit [Finite G] in
theorem le_normalizer_blockZ (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((blockZ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_commutator' (le_normalizer_pCoreOf 2 K) (fun x hx => Subgroup.le_normalizer hx)
      hk, A4.mem_normalizer_centralizer (Subgroup.le_normalizer hk)⟩

theorem blockU_eq_sup (h : Hyp27 H R M K) (hs : StarHyp R K V) (hK : IsShort2 K) :
    blockU K = ⁅V, K⁆ ⊔ blockZ K := by
  have hKN : K ≤ Subgroup.normalizer ((⁅V, K⁆ ⊔ blockZ K : Subgroup G) : Set G) :=
    le_normalizer_sup' (le_normalizer_commutator' hs.K_le_normalizer_V
      (fun x hx => Subgroup.le_normalizer hx)) (le_normalizer_blockZ K)
  rcases hK.2.2.2.2.2 _ le_sup_right (sup_le (commutator_V_K_le_blockU h hs) inf_le_left)
      hKN with h1 | h1
  · exfalso
    apply hs.commutator_ne_bot
    have hle : ⁅V, K⁆ ≤ Subgroup.centralizer (K : Set G) :=
      (le_sup_left.trans h1.le).trans inf_le_right
    have hbot : ⁅⁅V, K⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    exact le_bot_iff.1 (hbot ▸ commutator_V_K_le_comm h hs)
  · exact h1.symm

theorem blockData_of_short (h : Hyp27 H R M K) (hs : StarHyp R K V) (hK : IsShort2 K)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) : C124.BlockData V K :=
  ⟨hK, (hs.inf_centralizer_eq hZ).symm, commutator_V_K_le_blockU h hs, blockU_eq_sup h hs hK⟩

end Block

section Coord

variable {K V : Subgroup G}

omit [Finite G] in
theorem val_mem_commutator_of_mem_commV (hV : IsElemAbelian 2 V) {u : IntMod V hV}
    (hu : u ∈ commV (autI hV K)) : u.val ∈ ⁅V, K⁆ := by
  unfold commV at hu
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hx
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hgK v.val_mem
  | one => exact (⁅V, K⁆).one_mem
  | mul a b _ _ ha hb =>
    rw [IntMod.val_mul]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [IntMod.val_inv]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem exists_mem_commV_of_mem_commutator (hV : IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {g : G} (hg : g ∈ ⁅V, K⁆) :
    ∃ u ∈ commV (autI hV K), u.val = g := by
  let φ : IntMod V hV →* G :=
    { toFun := IntMod.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hle : ⁅V, K⁆ ≤ (commV (autI hV K)).map φ := by
    refine Subgroup.commutator_le.2 fun v hv k hk => ?_
    set w : IntMod V hV := IntMod.mk hV ⟨v⁻¹, V.inv_mem hv⟩ with hw
    set x : MulAut (IntMod V hV) := convI hV ⟨k, hKV hk⟩ with hx
    refine ⟨x w * w⁻¹, Subgroup.subset_closure ⟨x, convI_mem_autI hV hk (hKV hk), w, rfl⟩, ?_⟩
    show (x w * w⁻¹).val = ⁅v, k⁆
    rw [IntMod.val_mul, IntMod.val_inv, hx, convI_apply_val]
    have hcomm := IntMod.val_comm (x w) (IntMod.mk hV ⟨v, hv⟩)
    rw [hx, convI_apply_val] at hcomm
    have e1 : (w.val)⁻¹ = v := by simp [hw, IntMod.mk, IntMod.val]
    have e2 : w.val = v⁻¹ := rfl
    rw [e1, e2, commutatorElement_def]
    have e3 : (IntMod.mk hV ⟨v, hv⟩ : IntMod V hV).val = v := rfl
    rw [e2, e3] at hcomm
    rw [hcomm]
    group
  obtain ⟨u, hu, rfl⟩ := hle hg
  exact ⟨u, hu, rfl⟩

omit [Finite G] in
theorem mem_fixV_autI_iff (hV : IsElemAbelian 2 V) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    {u : IntMod V hV} : u ∈ fixV (autI hV K) ↔ u.val ∈ Subgroup.centralizer (K : Set G) := by
  rw [mem_fixV, Subgroup.mem_centralizer_iff]
  constructor
  · intro hu k hk
    have h1 := congrArg IntMod.val (hu _ (convI_mem_autI hV hk (hKV hk)))
    rw [convI_apply_val] at h1
    have h2 : (k : G) * u.val * k⁻¹ = u.val := h1
    calc k * u.val = (k * u.val * k⁻¹) * k := by group
      _ = u.val * k := by rw [h2]
  · intro hu x hx
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 hx
    apply IntMod.val_injective
    rw [convI_apply_val, hu _ hgK]
    group

end Coord

section Model

open Matrix

variable {F : Type} [Field F] [Fintype F]

theorem card_fix_le_of_ne_one {g : Matrix (Fin 2) (Fin 2) F} (hg : g ≠ 1) :
    Nat.card {v : Fin 2 → F // g *ᵥ v = v} ≤ Nat.card F := by
  set W := LinearMap.ker (Matrix.toLin' g - LinearMap.id)
  have hW : Nat.card {v : Fin 2 → F // g *ᵥ v = v} = Nat.card W :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      simp only [W, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
        LinearMap.id_apply, sub_eq_zero])
  have hfr : Module.finrank F W ≤ 1 := by
    by_contra h
    have h2 : Module.finrank F W = Module.finrank F (Fin 2 → F) := by
      have := Submodule.finrank_le W
      rw [Module.finrank_fin_fun] at this ⊢
      omega
    have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq h2
    rw [LinearMap.ker_eq_top, sub_eq_zero, ← Matrix.toLin'_one] at htop
    exact hg (Matrix.toLin'.injective htop)
  rw [hW, Module.natCard_eq_pow_finrank (K := F)]
  calc Nat.card F ^ Module.finrank F W ≤ Nat.card F ^ 1 :=
        Nat.pow_le_pow_right Nat.card_pos hfr
    _ = Nat.card F := pow_one _

omit [Fintype F] in
theorem mul_self_eq_one_of_mulVec_eq_self [CharP F 2] {M : Matrix (Fin 2) (Fin 2) F}
    (hM : M.det = 1) {v : Fin 2 → F} (hv : M *ᵥ v = v) (hv0 : v ≠ 0) : M * M = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hM
  have e0 : M 0 0 * v 0 + M 0 1 * v 1 = v 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have e1 : M 1 0 * v 0 + M 1 1 * v 1 = v 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  have htr : M 0 0 + M 1 1 = 0 := by
    by_contra hne
    apply hv0
    funext i
    fin_cases i
    · have : (M 0 0 + M 1 1) * v 0 = 0 := by
        linear_combination v 0 * h2 - (M 1 1 - 1) * e0 + M 0 1 * e1 + v 0 * hM
      simpa [hne] using this
    · have : (M 0 0 + M 1 1) * v 1 = 0 := by
        linear_combination v 1 * h2 - (M 0 0 - 1) * e1 + M 1 0 * e0 + v 1 * hM
      simpa [hne] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * htr - hM - h2
  · linear_combination M 0 1 * htr
  · linear_combination M 1 0 * htr
  · linear_combination M 1 1 * htr - hM - h2

omit [Fintype F] in
theorem eq_zero_of_mulVec_eq_self [CharP F 2] {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h3 : g ^ 3 = 1) (h1 : g ≠ 1) {v : Fin 2 → F}
    (hv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : v = 0 := by
  by_contra hv0
  have hsq : g * g = 1 :=
    Subtype.ext (mul_self_eq_one_of_mulVec_eq_self g.2 hv hv0)
  exact h1 (by rw [← h3, pow_three, hsq, mul_one])

omit [Fintype F] in
theorem exists_SL2_pow_three [CharP F 2] :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g ^ 3 = 1 ∧ g ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ⟨⟨!![0, 1; 1, 1], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination -h2
  · apply Subtype.ext
    show !![(0 : F), 1; 1, 1] ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_three, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro h
    have := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp at this

omit [Fintype F] in
theorem center_SL2_eq_bot [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := CharTwo.sq_injective (by simpa using hr)
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

omit [Field F] [Fintype F] in
theorem exists_fixed_D5_of_pow_three (σ : Equiv.Perm (Fin 5)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ∃ x ∈ G6.coreMod 5, x ∉ Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 ∧
      G6.permAct 5 σ x = x := by
  have hsupp : σ.support.card = 3 := by
    have hc : ∀ c ∈ σ.cycleType, c = 3 := Equiv.Perm.pow_prime_eq_one_iff.mp h3
    have hsum := σ.sum_cycleType
    rw [Multiset.eq_replicate_card.mpr hc, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hle : σ.support.card ≤ 5 := by
      simpa using Finset.card_le_univ σ.support
    have hge := Equiv.Perm.two_le_card_support_of_ne_one h1
    omega
  have hfix : (Finset.univ.filter fun i => σ i = i).card = 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => σ i = i)
    have hs : (Finset.univ.filter fun i => ¬ σ i = i) = σ.support := rfl
    rw [hs, hsupp, Finset.card_univ, Fintype.card_fin] at h
    omega
  refine ⟨Multiplicative.ofAdd (fun i => if σ i = i then (1 : ZMod 2) else 0), ?_, ?_, ?_⟩
  · rw [G6.mem_coreMod]
    simp only [toAdd_ofAdd]
    rw [Finset.sum_boole, hfix]
    decide
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.mp h).1
    obtain ⟨i, hi⟩ : ∃ i, σ i = i := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp
        (by omega : 0 < (Finset.univ.filter fun i => σ i = i).card)
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
      exact ⟨j, Equiv.Perm.mem_support.mp hj⟩
    have key : ∀ a b : Fin 5, Multiplicative.toAdd (G6.allOnes 5 ^ k) a =
        Multiplicative.toAdd (G6.allOnes 5 ^ k) b := fun _ _ => rfl
    have hij := key i j
    rw [hk] at hij
    simp only [toAdd_ofAdd, hi, hj, ite_true, ite_false] at hij
    exact absurd hij (by decide)
  · apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    simp only [toAdd_ofAdd, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Equiv.eq_symm_apply]

end Model

section Lin2

variable {H R M K V : Subgroup G}

theorem exists_coord_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hK : IsShort2 K) {n : ℕ} (hL : IsLin2Type K n) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      ∃ α : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
        α.ker = CFSG.pCore 2 ↥K ∧
      ∃ c : ↥(commV (autI hV K)) →* Multiplicative (Fin 2 → F), Function.Surjective c ∧
        (∀ u, c u = 1 ↔ (u : IntMod V hV) ∈ fixV (autI hV K)) ∧
        ∀ (g : ↥(Subgroup.normalizer (V : Set G))) (hg : (g : G) ∈ K)
          (u : ↥(commV (autI hV K))) (hu' : convI hV g (u : IntMod V hV) ∈ commV (autI hV K)),
          Multiplicative.toAdd (c ⟨_, hu'⟩) =
            (α ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c u)) := by
  classical
  obtain ⟨F, iF, fF, hF, α, hα, hαk, β, hβ, hβk, hequiv⟩ := hL
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hs.K_le_normalizer_V
  set L := autI hV K with hLdef
  set U := commV L with hUdef
  have hval : ∀ u : ↥U, (u : IntMod V hV).val ∈ blockU K := fun u =>
    commutator_V_K_le_blockU h hs (val_mem_commutator_of_mem_commV hV u.2)
  let ι : ↥U →* ↥(blockU K) :=
    { toFun := fun u => ⟨(u : IntMod V hV).val, hval u⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨F, iF, fF, hF, α, hα, hαk, β.comp ι, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨w, rfl⟩ := hβ y
    have hw : (w : G) ∈ ⁅V, K⁆ ⊔ blockZ K := by
      rw [← blockU_eq_sup h hs hK]
      exact w.2
    have hUK : blockU K ≤ K := hK.2.2.1.1.trans (inf_le_left.trans (pCoreOf_le 2 K))
    have hZn : blockZ K ≤ Subgroup.normalizer ((⁅V, K⁆ : Subgroup G) : Set G) :=
      (inf_le_left.trans hUK).trans
        (le_normalizer_commutator' hKN (fun x hx => Subgroup.le_normalizer hx))
    obtain ⟨a, ha, z, hz, haz⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZn).1 hw
    obtain ⟨u, hu, hua⟩ := exists_mem_commV_of_mem_commutator hV hKN ha
    refine ⟨⟨u, hu⟩, ?_⟩
    have hzU : z ∈ blockU K := hz.1
    have haU : a ∈ blockU K := commutator_V_K_le_blockU h hs ha
    have hβz : β ⟨z, hzU⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
      exact hz
    have hw' : w = ⟨a, haU⟩ * ⟨z, hzU⟩ := Subtype.ext haz
    show β (ι ⟨u, hu⟩) = β w
    rw [hw', map_mul, hβz, mul_one]
    congr 1
    exact Subtype.ext hua
  ·
    intro u
    show β (ι u) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, mem_fixV_autI_iff hV hKN]
    exact ⟨fun hz => hz.2, fun hz => ⟨hval u, hz⟩⟩
  ·
    intro g hg u hu'
    exact hequiv ⟨g, hg⟩ (ι u) (ι ⟨_, hu'⟩) (convI_apply_val hV _ _)

theorem two_pow_le_card_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hK : IsShort2 K) {n : ℕ} (hL : IsLin2Type K n) {B : Subgroup (MulAut (IntMod V hV))}
    (hBK : B ≤ autI hV K) (hB1 : B ≠ ⊥)
    (hW : Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B)) : 2 ^ n ≤ Nat.card B := by
  classical
  set L := autI hV K with hLdef
  set U := commV L with hUdef
  set Z := fixV L ⊓ U with hZdef
  obtain ⟨F, iF, fF, hF, α, -, hαk, c, hcs, hc1, hceq⟩ := exists_coord_of_lin2 h hs hV hK hL
  have hkerc : Nat.card c.ker = Nat.card Z := by
    have e : c.ker = Z.subgroupOf U := by
      ext u
      rw [MonoidHom.mem_ker, hc1, Subgroup.mem_subgroupOf]
      exact ⟨fun hu => ⟨hu, u.2⟩, fun hu => hu.1⟩
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcard2 : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  have hU : Nat.card U = Nat.card F ^ 2 * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup c.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective c hcs).toEquiv, hcard2, hkerc]
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
  have hb1' : b ≠ 1 := fun hb => hb1 (Subtype.ext hb)
  obtain ⟨g₀, hg₀K, hb⟩ := (mem_autI hV).1 (hBK hbB)
  set M₀ : Matrix (Fin 2) (Fin 2) F := (α ⟨g₀, hg₀K⟩ : Matrix (Fin 2) (Fin 2) F) with hM₀
  have hM1 : M₀ ≠ 1 := by
    intro hM
    apply hb1'
    have h1 : α ⟨g₀, hg₀K⟩ = 1 := Subtype.ext hM
    have h2 : (⟨g₀, hg₀K⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← hαk]
      exact h1
    have h3 : (g₀ : G) ∈ pCoreOf 2 K := by
      rw [C124.pCoreOf_eq_map_pCore]
      exact ⟨_, h2, rfl⟩
    rw [← hb]
    exact (convI_eq_one_iff hV g₀).2 (hs.pCore_K_le_centralizer h3)
  let FixSub : Subgroup (Multiplicative (Fin 2 → F)) :=
    { carrier := {y | M₀.mulVec (Multiplicative.toAdd y) = Multiplicative.toAdd y}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, toAdd_mul, Matrix.mulVec_add] at hx hy ⊢
        rw [hx, hy]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, toAdd_inv, Matrix.mulVec_neg] at hx ⊢
        rw [hx] }
  have hFix : Nat.card FixSub ≤ Nat.card F := by
    refine le_trans (le_of_eq (Nat.card_congr ?_)) (card_fix_le_of_ne_one hM1)
    exact { toFun := fun y => ⟨Multiplicative.toAdd y.1, y.2⟩
            invFun := fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  have hsub : fixV B ⊓ U ≤ (FixSub.comap c).map U.subtype := by
    rintro u ⟨hub, huU⟩
    refine ⟨⟨u, huU⟩, ?_, rfl⟩
    have hbu : b u = u := hub b hbB
    have hu' : convI hV g₀ u ∈ U := by
      rw [hb, hbu]
      exact huU
    have h1 := hceq g₀ hg₀K ⟨u, huU⟩ hu'
    have h2 : (⟨convI hV g₀ u, hu'⟩ : ↥U) = ⟨u, huU⟩ := by
      apply Subtype.ext
      show (convI hV g₀) u = u
      rw [hb]
      exact hbu
    rw [h2] at h1
    exact h1.symm
  have hcomap : Nat.card (FixSub.comap c) = Nat.card FixSub * Nat.card Z := by
    rw [card_comap_of_surjective' hcs, hkerc]
  have hfixU : Nat.card ↥(fixV B ⊓ U) ≤ Nat.card F * Nat.card Z := by
    calc Nat.card ↥(fixV B ⊓ U) ≤ Nat.card ((FixSub.comap c).map U.subtype) :=
          Subgroup.card_le_of_le hsub
      _ = Nat.card (FixSub.comap c) := Subgroup.card_map_of_injective U.subtype_injective
      _ = Nat.card FixSub * Nat.card Z := hcomap
      _ ≤ Nat.card F * Nat.card Z := Nat.mul_le_mul_right _ hFix
  have hoff := C124.YZ.card_le_card_mul_inf U B hW
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have key : Nat.card F * (Nat.card F * Nat.card Z) ≤ Nat.card B * (Nat.card F * Nat.card Z) := by
    calc Nat.card F * (Nat.card F * Nat.card Z) = Nat.card U := by rw [hU]; ring
      _ ≤ Nat.card B * Nat.card ↥(fixV B ⊓ U) := hoff
      _ ≤ Nat.card B * (Nat.card F * Nat.card Z) := Nat.mul_le_mul_left _ hfixU
  have hFB : Nat.card F ≤ Nat.card B := Nat.le_of_mul_le_mul_right key (Nat.mul_pos hFpos hZpos)
  rw [Nat.card_eq_fintype_card (α := F), hF] at hFB
  exact hFB

omit [Finite G] in
theorem center_eq_bot_of_lin2 {n : ℕ} (hL : IsLin2Type K n) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  obtain ⟨F, iF, fF, hF, α, hα, hαk, -⟩ := hL
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card]; exact hF)
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hez : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [center_SL2_eq_bot, Subgroup.mem_bot] at hez
  exact e.injective (hez.trans (map_one e).symm)

theorem card_autI_K_of_lin2 (hs : StarHyp R K V) (hV : IsElemAbelian 2 V) {n : ℕ}
    (hL : IsLin2Type K n) : Nat.card ↥(autI hV K) = 2 ^ n * (2 ^ (2 * n) - 1) := by
  obtain ⟨e₁⟩ := hs.quotEquiv (center_eq_bot_of_lin2 hL)
  obtain ⟨F, iF, fF, hF, α, hα, hαk, -⟩ := hL
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  rw [show Nat.card ↥(autI hV K) = Nat.card ↥(autOn K V) from rfl, ← Nat.card_congr e₁.toEquiv,
    Nat.card_congr e.toEquiv, ← Vol2.Ch10.SecA.card_statedSL 2 F,
    C124.card_statedSL_two_pow hF']

omit [Finite G] in
theorem isSylowTwoOf_of_two_pow_le {Γ : Type*} [Group Γ] [Finite Γ] {B L : Subgroup Γ}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) {n q : ℕ} (hq : Odd q) (hL : Nat.card L = 2 ^ n * q)
    (hcard : 2 ^ n ≤ Nat.card B) : IsSylowTwoOf B L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hBL, hB, fun hdvd => ?_⟩
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  obtain ⟨m, hm⟩ := hdvd
  have hidx : (B.subgroupOf L).index * Nat.card B = Nat.card L := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, Subgroup.index_mul_card]
  rw [hm, hb, hL] at hidx
  have h1 : 2 ^ (b + 1) ∣ 2 ^ n * q := ⟨m, by rw [← hidx]; ring⟩
  have h2 : 2 ^ (b + 1) ∣ 2 ^ n :=
    (Nat.Coprime.pow_left (b + 1) (Nat.coprime_two_left.2 hq)).dvd_of_dvd_mul_right h1
  have h3 : b + 1 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  rw [hb] at hcard
  have h4 : 2 ^ n ≤ 2 ^ b := hcard
  have h5 : n ≤ b := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  omega

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have he : Even (2 ^ k) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨r, hr⟩ := he
  exact ⟨r - 1, by omega⟩

theorem odd_eq_of_mul_two_pow_eq {a b i j : ℕ} (ha : Odd a) (hb : Odd b)
    (h : a * 2 ^ i = b * 2 ^ j) : a = b := by
  rcases le_total i j with hij | hji
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have h' : a = b * 2 ^ d :=
      Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) i) (by rw [h]; ring)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      have : Even a := by
        rw [h']
        exact (Nat.even_pow.2 ⟨even_two, hd.ne'⟩).mul_left b
      exact (Nat.not_even_iff_odd.2 ha) this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    have h' : a * 2 ^ d = b :=
      Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) j) (by rw [← h]; ring)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      have : Even b := by
        rw [← h']
        exact (Nat.even_pow.2 ⟨even_two, hd.ne'⟩).mul_left a
      exact (Nat.not_even_iff_odd.2 hb) this

theorem not_symDn5_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hK : IsShort2 K) {n : ℕ} (hL : IsLin2Type K n) {G₀ : Subgroup (MulAut (IntMod V hV))}
    (hLG : autI hV K ≤ G₀) {π : Equiv.Perm (Fin 5) →* ↥G₀}
    (hπ : (FFModel.symDn 5).RealizesVia G₀ (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) π) : False := by
  classical
  have hZ := center_eq_bot_of_lin2 hL
  obtain ⟨F, iF, fF, hF, α, hα, hαk, c, -, hc1, hceq⟩ := exists_coord_of_lin2 h hs hV hK hL
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have : CharP F 2 := FFC.charP_two_of_card_pow hF'
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hs.K_le_normalizer_V
  obtain ⟨s₀, hs3, hs1⟩ := exists_SL2_pow_three (F := F)
  obtain ⟨k₀, hk₀⟩ := hα s₀
  set g₀ : ↥(Subgroup.normalizer (V : Set G)) := ⟨k₀, hKN k₀.2⟩ with hg₀
  set b : MulAut (IntMod V hV) := convI hV g₀ with hbdef
  have hbL : b ∈ autI hV K := convI_mem_autI hV k₀.2 (hKN k₀.2)
  have hmemK : ∀ y : ↥K, (y : G) ∈ Subgroup.centralizer (V : Set G) → α y = 1 := by
    intro y hy
    have h2 : (y : G) ∈ pCoreOf 2 K := by
      rw [← hs.inf_centralizer_eq hZ]
      exact ⟨y.2, hy⟩
    rw [C124.pCoreOf_eq_map_pCore] at h2
    obtain ⟨y', hy', hyy⟩ := h2
    have e : y' = y := Subtype.ext hyy
    rw [e, ← hαk] at hy'
    exact hy'
  have hb1 : b ≠ 1 := by
    intro hb
    apply hs1
    rw [← hk₀]
    exact hmemK k₀ ((convI_eq_one_iff hV g₀).1 hb)
  have hb3 : b ^ 3 = 1 := by
    have h1 : α (k₀ ^ 3) = 1 := by rw [map_pow, hk₀, hs3]
    have h2 : k₀ ^ 3 ∈ CFSG.pCore 2 ↥K := by
      rw [← hαk]
      exact h1
    have h3 : ((k₀ ^ 3 : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [C124.pCoreOf_eq_map_pCore]
      exact ⟨_, h2, rfl⟩
    have h4 := hs.pCore_K_le_centralizer h3
    have e : b ^ 3 = convI hV (g₀ ^ 3) := by rw [hbdef, map_pow]
    rw [e]
    exact (convI_eq_one_iff hV _).2 (by simpa [hg₀] using h4)
  have hinj : Function.Injective (π : Equiv.Perm (Fin 5) → ↥G₀) :=
    FFC.injective_of_faithful_sec (FFC.symDn_faithful (by norm_num)) hπ
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), π σ = ⟨b, hLG hbL⟩ := hπ.1 _
  have hσ3 : σ ^ 3 = 1 := hinj (by rw [map_pow, hσ, map_one]; exact Subtype.ext hb3)
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hb1
    have := congrArg Subtype.val hσ
    rw [h1, map_one] at this
    exact this.symm
  obtain ⟨x, hx, hxk, hσx⟩ := exists_fixed_D5_of_pow_three σ hσ3 hσ1
  obtain ⟨-, -, -, hHU, -, hsec, -, βS, hβs, hβk, hβe⟩ := hπ
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨x, hx⟩)
  have hu1 : ((π σ : ↥G₀) : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV K) :=
    hHU (π σ) u u.2
  have hm : (FFModel.symDn 5).act σ x ∈ (FFModel.symDn 5).sec := hsec σ x hx
  have hβbu := hβe σ u ⟨x, hx⟩ hu1 hm hu
  have hσx' : (⟨(FFModel.symDn 5).act σ x, hm⟩ : ↥(FFModel.symDn 5).sec) = ⟨x, hx⟩ :=
    Subtype.ext hσx
  rw [hσx', ← hu] at hβbu
  have hbu' : ((⟨_, hu1⟩ : ↥(commV (autI hV K))) * u⁻¹ : IntMod V hV) ∈ fixV (autI hV K) := by
    refine ((hβk (⟨_, hu1⟩ * u⁻¹)).1 ?_).1
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact hβbu
  have hπσ : ((π σ : ↥G₀) : MulAut (IntMod V hV)) = convI hV g₀ := by rw [hσ]
  have hu2 : convI hV g₀ (u : IntMod V hV) ∈ commV (autI hV K) := by rw [← hπσ]; exact hu1
  have hc2 := hceq g₀ k₀.2 u hu2
  have hcbu : c (⟨_, hu2⟩ * u⁻¹) = 1 := by
    rw [hc1]
    have e : (((⟨_, hu2⟩ : ↥(commV (autI hV K))) * u⁻¹ : ↥(commV (autI hV K))) : IntMod V hV) =
        (((⟨_, hu1⟩ : ↥(commV (autI hV K))) * u⁻¹ : ↥(commV (autI hV K))) : IntMod V hV) := by
      show convI hV g₀ (u : IntMod V hV) * (u : IntMod V hV)⁻¹ =
        ((π σ : ↥G₀) : MulAut (IntMod V hV)) (u : IntMod V hV) * (u : IntMod V hV)⁻¹
      rw [hπσ]
    rw [e]
    exact hbu'
  rw [map_mul, map_inv, mul_inv_eq_one] at hcbu
  rw [hcbu] at hc2
  have hk₀' : (⟨(g₀ : G), k₀.2⟩ : ↥K) = k₀ := rfl
  rw [hk₀', hk₀] at hc2
  have hzero := eq_zero_of_mulVec_eq_self hs3 hs1 hc2.symm
  have hcu : c u = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hzero]
    rfl
  have huZ : (u : IntMod V hV) ∈ fixV (autI hV K) ⊓ commV (autI hV K) := ⟨(hc1 u).1 hcu, u.2⟩
  have hβu : βS u = 1 := (hβk u).2 huZ
  rw [hu, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hβu
  exact hxk hβu

theorem jP_eq_K_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hA21 : AsA21SQTKSection) (hB51 : AsB51) (hK : IsShort2 K) {n : ℕ} (hn : 1 < n)
    (hL : IsLin2Type K n) :
    ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R)) = autI hV K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hHyp, hC, -⟩ := moduleType_of h hs hV hA21 hB51
  obtain ⟨⟨-, hcases⟩, -⟩ := hC
  rcases hcases with ⟨-, -, halt⟩ | ⟨hGL, -⟩ | ⟨m, hGL, -⟩ | ⟨hGL, -⟩
  rotate_left
  · exact hGL
  · exact hGL
  · exact hGL
  set G₀ := ffJP (C124.offenderImagesConjIn hV (K ⊔ R) R) (autI hV (K ⊔ R)) with hG₀
  obtain ⟨T, hT⟩ := B5.exists_isSylowTwoOf G₀
  rcases halt T hT with hGL | ⟨hGT, hmod⟩
  · exact hGL
  exfalso
  have hTL : T ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun l hl => B5.normal_L hHyp t (hT.1 ht) l hl
  have hprod := card_sup_mul_card_inf_of_le_normalizer' hTL
  rw [← hGT] at hprod
  obtain ⟨t, ht⟩ := hT.2.1.exists_card_eq
  obtain ⟨s', hs'⟩ := (hT.2.1.to_le inf_le_right : IsPGroup 2 ↥(autI hV K ⊓ T)).exists_card_eq
  rw [ht, hs', card_autI_K_of_lin2 hs hV hL] at hprod
  have hodd : Odd (2 ^ (2 * n) - 1) := odd_two_pow_sub_one (by omega)
  have key : ∀ e o : ℕ, Odd o → Nat.card G₀ = o * 2 ^ e → o = 2 ^ (2 * n) - 1 := by
    intro e o ho hG
    rw [hG] at hprod
    refine odd_eq_of_mul_two_pow_eq ho hodd (i := e + s') (j := n + t) ?_
    rw [pow_add, pow_add]
    linarith [hprod]
  have h16 : 16 ∣ 2 ^ (2 * n) := by
    have := pow_dvd_pow 2 (show 4 ≤ 2 * n by omega)
    simpa using this
  have hpos : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  rcases hmod with ⟨m, hm5, hm8, hS⟩ | hG2
  · obtain ⟨π, hπ⟩ := hS
    have hcard : Nat.card G₀ = Nat.factorial m := by
      rw [← Nat.card_congr (FFC.equivOfRealizes (FFC.symDn_faithful hm5) hπ).toEquiv]
      show Nat.card (Equiv.Perm (Fin m)) = _
      rw [Nat.card_perm, Nat.card_fin]
    interval_cases m
    · have h15 := key 3 15 (by decide) (by rw [hcard]; decide)
      rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
      · exact not_symDn5_of_lin2 h hs hV hK hL (le_sup_left.trans hGT.ge) hπ
      · have h64 : 64 ∣ 2 ^ (2 * n) := by
          have := pow_dvd_pow 2 (show 6 ≤ 2 * n by omega)
          simpa using this
        omega
    · have := key 4 45 (by decide) (by rw [hcard]; decide)
      omega
    · have := key 4 315 (by decide) (by rw [hcard]; decide)
      omega
    · have := key 7 315 (by decide) (by rw [hcard]; decide)
      omega
  · obtain ⟨K₂, iK, fK, hK₂, π, hπ⟩ := hG2
    have : CharP K₂ 2 := FFC.charP_two_of_card_pow hK₂
    have hcard : Nat.card G₀ = 12096 := by
      rw [← Nat.card_congr (FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ).toEquiv]
      exact C124.card_G2_two (by simpa using hK₂)
    have := key 6 189 (by decide) (by rw [hcard]; decide)
    omega

omit [Finite G] in
theorem autI_mem_offenders {X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hRN : R ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hA : IsMaxElemAbelian R A)
    (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    autI hV A ∈ C124.offenderImagesConjIn hV X R := by
  refine ⟨fun hb => hAV ((autI_eq_bot_iff hV (hA.1.trans hRN)).1 hb), A, rfl, 1, X.one_mem, ?_⟩
  have e : cjSub (1 : G)⁻¹ A = A := by
    ext x
    rw [mem_cjSub]
    simp
  rw [e]
  exact hA

theorem isSylowTwoOf_of_mem_offenders_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hV : IsElemAbelian 2 V) (hA21 : AsA21SQTKSection) (hB51 : AsB51) (hK : IsShort2 K)
    {n : ℕ} (hn : 1 < n) (hL : IsLin2Type K n) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ C124.offenderImagesConjIn hV (K ⊔ R) R) : IsSylowTwoOf B (autI hV K) := by
  obtain ⟨hstab, -, -⟩ := stable_branch h hs hV
  have hoff : IsFFStarOffender (autI hV (K ⊔ R)) B := hstab.2.1 B hB
  have hBK : B ≤ autI hV K := by
    rw [← jP_eq_K_of_lin2 h hs hV hA21 hB51 hK hn hL]
    exact le_iSup₂_of_le B hB (le_iSup_of_le hoff.1 le_rfl)
  have hW : Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B) := by
    have := hoff.card_le (bot_le : (⊥ : Subgroup (MulAut (IntMod V hV))) ≤ B)
    rwa [B1.card_bot_mul_card_fixV] at this
  exact isSylowTwoOf_of_two_pow_le hBK hoff.2.2.1.isPGroup (odd_two_pow_sub_one (by omega))
    (card_autI_K_of_lin2 hs hV hL) (two_pow_le_card_of_lin2 h hs hV hK hL hBK hoff.2.1 hW)

theorem sylow_thompsonJ_of_lin2 (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hA21 : AsA21SQTKSection) (hB51 : AsB51) (hK : IsShort2 K) {n : ℕ} (hn : 1 < n)
    (hL : IsLin2Type K n) : IsSylowTwoOf (autOn (thompsonJ R) V) (autOn K V) := by
  have hV := hs.elemAbelian
  have hRN := hs.R_le_normalizer_V
  have hsyl : ∀ A : Subgroup G, IsMaxElemAbelian R A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      IsSylowTwoOf (autI hV A) (autI hV K) := fun A hA hAV =>
    isSylowTwoOf_of_mem_offenders_of_lin2 h hs hV hA21 hB51 hK hn hL
      (autI_mem_offenders hV hRN hA hAV)
  have hJ : autI hV (thompsonJ R) = ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian R A), autI hV A :=
    autI_iSup₂ hV fun A hA => hA.1.trans hRN
  have hJK : autI hV (thompsonJ R) ≤ autI hV K := by
    rw [hJ]
    refine iSup₂_le fun A hA => ?_
    by_cases hAV : A ≤ Subgroup.centralizer (V : Set G)
    · rw [autI_eq_bot_of_le_centralizer hV hAV]
      exact bot_le
    · exact (hsyl A hA hAV).1
  obtain ⟨A, hA, hAV⟩ : ∃ A : Subgroup G, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hne
    push Not at hne
    exact not_thompsonJ_le_centralizer h hs (iSup₂_le fun A hA => hne A hA)
  have hAJ : autI hV A ≤ autI hV (thompsonJ R) := autI_mono hV (le_iSup₂_of_le A hA le_rfl)
  refine ⟨hJK, isPGroup_autOn (hs.pgroup.to_le (thompsonJ_le_self R)), fun h2 => ?_⟩
  exact (hsyl A hA hAV).2.2 (h2.trans (Subgroup.index_dvd_of_le
    (Subgroup.subgroupOf_mono _ hAJ)))

end Lin2

end CFSG.Quasithin.SmithC27
