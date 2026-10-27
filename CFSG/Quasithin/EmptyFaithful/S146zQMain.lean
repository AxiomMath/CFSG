module

public import CFSG.Quasithin.EmptyFaithful.S146zQRefl
public import CFSG.Quasithin.EmptyFaithful.S146zIB1b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Central

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.false_of_swap_of_central (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h4 : mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (hpos : 0 < mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hle : mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
      mIdx (F8.Uγ (VZ T M) H (k : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G))
    {y : G} (hy : y ∈ F8.Uγ (VZ T M) H (k : G))
    (hsw : conjSub y (uHi T M H H₁) = uHi T M H H₂) : False := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨hF81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hr₁ : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 := by
    have := h.mIdx_uK_sup_eq S hred
    omega
  obtain ⟨hp3, hcard⟩ := h.p_eq_three_of_mIdx_four S hred h91 h4
  subst hp3
  obtain ⟨hUkH, hUle⟩ := S.setup_le hH sk
  have hq : QCrit (quasithinOmegaOneCenter T) (VZ T M) H (F8.Uγ (VZ T M) H (k : G)) :=
    (h98.F916_2_aux sk hpos hle).1
  have hUab : IsElemAbelian 2 (F8.Uγ (VZ T M) H (k : G)) := h98.isElemAbelian_Uγ
  have hyH : y ∈ H := hUkH hy
  have hyy : y * y = 1 := by
    have := isElemAbelian_pow_eq_one hUab hy
    rwa [pow_two] at this
  have hsw' : conjSub y (uHi T M H H₂) = uHi T M H H₁ := by
    rcases h.normalizer_or_swap S hred hyH with ⟨-, h1, -⟩ | ⟨-, h2⟩
    · exfalso
      rw [h1] at hsw
      have hZeq : uHi T M H H₁ = quasithinOmegaOneCenter T := by
        have h3 : uHi T M H H₁ ⊓ uHi T M H H₂ = quasithinOmegaOneCenter T := h.dir_inf
        rw [← hsw, inf_idem] at h3
        exact h3
      rw [hZeq] at hr₁
      unfold mIdx at hr₁
      simp at hr₁
    · exact h2
  have hρ : ∀ z (hz : z ∈ F8.Uγ (VZ T M) H (k : G)), rhoH h91 ⟨z, hUkH hz⟩ = 1 ∨
      rhoH h91 ⟨z, hUkH hz⟩ = rhoH h91 ⟨y, hyH⟩ :=
    fun z hz => h.rho_eq_of_swap_quad S hred h91 hq hy hz hyy hsw hsw'
  have hDγ := h98.Dγ_eq_inf_pCoreOf sk
  have hidxD : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)).relIndex
      (F8.Uγ (VZ T M) H (k : G)) ≤ 2 := by
    unfold Subgroup.relIndex
    refine index_le_two_of_forall _ (⟨y, hy⟩ : ↥(F8.Uγ (VZ T M) H (k : G))) fun z => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hzH : (z : G) ∈ H := hUkH z.2
    rcases hρ z.1 z.2 with h1 | h1
    · left
      rw [hDγ]
      exact ⟨z.2, (rhoH_eq_one_iff h91 ⟨z.1, hzH⟩).mp h1⟩
    · right
      rw [hDγ]
      have hyz : y⁻¹ * (z : G) ∈ F8.Uγ (VZ T M) H (k : G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) z.2
      refine ⟨by simpa using hyz, ?_⟩
      have h2 : rhoH h91 ((⟨y, hyH⟩ : ↥H)⁻¹ * ⟨z.1, hzH⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      simpa using (rhoH_eq_one_iff h91 _).mp h2
  have hmI : mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤ 1 :=
    padicValNat_two_le_one (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hidxD
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hDHidx : (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)).relIndex
      (conjClosure (VZ T M) H) ≤ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp]
    calc 2 ^ mIdx (conjClosure (VZ T M) H)
          (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤ 2 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) (hle.trans hmI)
      _ = 2 := by norm_num
  have hZDH : quasithinOmegaOneCenter T ≤
      F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G) := by
    intro z hz
    have hzU : z ∈ conjClosure (VZ T M) H := le_conjClosure (VZ T M) H (h91.V₁_le_V hz)
    have hzC : ∀ x ∈ H, z * x = x * z := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (h91.H_le_centralizer hx)) z hz
    refine ⟨hzU, ?_, fun y' hy' => ?_⟩
    · apply Subgroup.centralizer_le_normalizer
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      exact (hzC x (hUkH (h98.A₁_le_Uγ hx))).symm
    · have h1 := hzC y' (hUkH hy')
      have e : z * y' * z⁻¹ * y'⁻¹ = 1 := by rw [h1]; group
      rw [e]
      exact (F8.A₁ (quasithinOmegaOneCenter T) (k : G)).one_mem
  obtain ⟨d, hdD, hd1⟩ := h.exists_DH_comm h91 hcard hyH hsw (centralizerMod_le_left _ _ _)
    hZDH hDHidx
  have hdU : d ∈ conjClosure (VZ T M) H := centralizerMod_le_left _ _ _ hdD
  obtain ⟨z', hz'⟩ : ∃ z', z' = d * y * d⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hz'A : z' ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G) := hz' ▸ hdD.2.2 y hy
  have hz'K : z' ∈ ⁅conjClosure (VZ T M) H, H⁆ := by
    have := Subgroup.commutator_mem_commutator hdU hyH
    rw [commutatorElement_def] at this
    rwa [hz']
  have hz'U : z' ∈ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure (VZ T M) H) hz'K
  have hz'1 : z' ≠ 1 := hz' ▸ hd1
  have hz'Z : z' ∉ quasithinOmegaOneCenter T := by
    intro hZ
    have h1 : z' ∈ quasithinOmegaOneCenter T ⊓ F8.A₁ (quasithinOmegaOneCenter T) (k : G) :=
      ⟨hZ, hz'A⟩
    rw [h98.F913_5b sk, Subgroup.mem_bot] at h1
    exact hz'1 h1
  have hA₁two : ∀ x ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G), x = 1 ∨ x = z' := fun x hx =>
    eq_one_or_eq_of_card_subgroup_two _ h98.card_A₁ hz'A hz'1 hx
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hW : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ :=
    Wsub_inf_eq_bot h91 hi₁ hi₂ (Z_le_uHi T M H H₁) h.dir_inf.le
  have hσσ : ∀ v : UMod h91, rhoH h91 ⟨y, hyH⟩ (rhoH h91 ⟨y, hyH⟩ v) = v := by
    intro v
    have h1 : rhoH h91 ⟨y, hyH⟩ * rhoH h91 ⟨y, hyH⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
      rw [this, map_one]
    have := congrArg (fun f : MulAut (UMod h91) => f v) h1
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hinv : ∀ v : UMod h91, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using IntMod.sq_eq_one v)
  have hζy : rhoH h91 ⟨y, hyH⟩ (clsU h91 hz'U) = clsU h91 hz'U := by
    have hc : clsU h91 hz'U = clsU h91 hdU * rhoH h91 ⟨y, hyH⟩ (clsU h91 hdU) := by
      have hcU : d * y * d⁻¹ * y⁻¹ ∈ conjClosure (VZ T M) H := hz' ▸ hz'U
      have := clsU_commutator h91 hdU hyH hcU
      rw [← this]
      exact clsU_congr h91 _ _ hz'
    rw [hc, map_mul, hσσ, mul_comm]
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_decomp S hred hz'K
  have haU := hi₁ ha
  have hbU := hi₂ hb
  have hζab : clsU h91 hz'U = clsU h91 haU * clsU h91 hbU := by
    rw [clsU_mul]
    exact clsU_congr h91 _ _ hab
  have hζ₁W : clsU h91 haU ∈ Wsub h91 (uHi T M H H₁) := clsU_mem_Wsub h91 haU ha
  have hζ₂W : clsU h91 hbU ∈ Wsub h91 (uHi T M H H₂) := clsU_mem_Wsub h91 hbU hb
  have hyζ₁ : rhoH h91 ⟨y, hyH⟩ (clsU h91 haU) = clsU h91 hbU := by
    have h1 := hζy
    rw [hζab, map_mul] at h1
    have hP : rhoH h91 ⟨y, hyH⟩ (clsU h91 haU) ∈ Wsub h91 (uHi T M H H₂) :=
      rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₁ hsw hζ₁W
    have hR : rhoH h91 ⟨y, hyH⟩ (clsU h91 hbU) ∈ Wsub h91 (uHi T M H H₁) :=
      rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₂ hsw' hζ₂W
    have hAB : rhoH h91 ⟨y, hyH⟩ (clsU h91 haU) * (clsU h91 hbU)⁻¹ =
        clsU h91 haU * (rhoH h91 ⟨y, hyH⟩ (clsU h91 hbU))⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h1, mul_comm]
    have hm₂ : rhoH h91 ⟨y, hyH⟩ (clsU h91 haU) * (clsU h91 hbU)⁻¹ ∈ Wsub h91 (uHi T M H H₂) :=
      (Wsub h91 (uHi T M H H₂)).mul_mem hP ((Wsub h91 (uHi T M H H₂)).inv_mem hζ₂W)
    have hm₁ : clsU h91 haU * (rhoH h91 ⟨y, hyH⟩ (clsU h91 hbU))⁻¹ ∈ Wsub h91 (uHi T M H H₁) :=
      (Wsub h91 (uHi T M H H₁)).mul_mem hζ₁W ((Wsub h91 (uHi T M H H₁)).inv_mem hR)
    have hmem : rhoH h91 ⟨y, hyH⟩ (clsU h91 haU) * (clsU h91 hbU)⁻¹ ∈
        Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) := ⟨hAB ▸ hm₁, hm₂⟩
    rw [hW, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hζ₁ne : clsU h91 haU ≠ 1 := by
    intro e
    have h1 : clsU h91 hbU = 1 := by rw [← hyζ₁, e, map_one]
    have h2 : clsU h91 hz'U = 1 := by rw [hζab, e, h1, one_mul]
    exact hz'Z ((clsU_eq_one_iff h91 hz'U).mp h2)
  obtain ⟨a₁, ha₁H₁, ha₁sq, ha₁fix, u₀, hu₀W, hu₀mv⟩ :=
    h.exists_refl_fixing_sq S hred h91 hcard hζ₁W hζ₁ne
  have ha₁ζ : rhoH h91 a₁ (clsU h91 hz'U) = clsU h91 hz'U := by
    rw [hζab, map_mul, ha₁fix, h.rho_fix_W₂ h91 a₁ ha₁H₁ hζ₂W]
  have hε' : (a₁ : G) * z' * (a₁ : G)⁻¹ * z'⁻¹ ∈ quasithinOmegaOneCenter T :=
    (rhoH_clsU_eq_iff h91 a₁ hz'U).mp ha₁ζ
  have ha₁a : (a₁ : G) * a * (a₁ : G)⁻¹ = a :=
    h.refl_lift_fixed S hred h91 hcard hQC ha₁H₁ ha₁sq hζ₁ne hζ₁W ha₁fix hu₀W hu₀mv haU rfl
  have ha₁b : (a₁ : G) * b * (a₁ : G)⁻¹ = b :=
    h.cent_H₁_U₂ S hred h91 hcard hQC (a₁ : G) ha₁H₁ b hb
  obtain ⟨r, hrH₁, hrfix, hρr⟩ : ∃ r : ↥H, (r : G) ∈ H₁ ∧ (r : G) * z' * (r : G)⁻¹ = z' ∧
      rhoH h91 r = rhoH h91 a₁ := by
    refine ⟨a₁, ha₁H₁, ?_, rfl⟩
    calc (a₁ : G) * z' * (a₁ : G)⁻¹
        = ((a₁ : G) * a * (a₁ : G)⁻¹) * ((a₁ : G) * b * (a₁ : G)⁻¹) := by rw [hab]; group
      _ = z' := by rw [ha₁a, ha₁b, hab]
  have hrH : (r : G) ∈ H := r.2
  have hrcen : ∀ x' ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G),
      (r : G) * x' * (r : G)⁻¹ = x' := by
    intro x' hx'
    rcases hA₁two x' hx' with rfl | rfl
    · group
    · exact hrfix
  have hrmem : (r : G) ∈ conjSub (k : G) (mcOf T) := by
    rw [mem_conjSub, ← S.normalizer_Z, Subgroup.mem_normalizer_iff]
    intro x
    have hxA : x ∈ quasithinOmegaOneCenter T ↔
        (k : G) * x * (k : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G) := by
      show _ ↔ (k : G) * x * (k : G)⁻¹ ∈ conjSub (k : G) (quasithinOmegaOneCenter T)
      rw [mem_conjSub]
      have e : (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) = x := by group
      rw [e]
    have hyA : (k : G)⁻¹ * (r : G) * (k : G) * x * ((k : G)⁻¹ * (r : G) * (k : G))⁻¹ ∈
        quasithinOmegaOneCenter T ↔
        (r : G) * ((k : G) * x * (k : G)⁻¹) * (r : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G) := by
      show _ ↔ _ ∈ conjSub (k : G) (quasithinOmegaOneCenter T)
      rw [mem_conjSub]
      have e : (k : G)⁻¹ * ((r : G) * ((k : G) * x * (k : G)⁻¹) * (r : G)⁻¹) * (k : G) =
          (k : G)⁻¹ * (r : G) * (k : G) * x * ((k : G)⁻¹ * (r : G) * (k : G))⁻¹ := by group
      rw [e]
    rw [hxA, hyA]
    constructor
    · intro hx'
      rw [hrcen _ hx']
      exact hx'
    · intro hx'
      rcases hA₁two _ hx' with e | e
      · have h2 : (k : G) * x * (k : G)⁻¹ =
            (r : G)⁻¹ * ((r : G) * ((k : G) * x * (k : G)⁻¹) * (r : G)⁻¹) * (r : G) := by group
        have : (k : G) * x * (k : G)⁻¹ = 1 := by rw [h2, e]; group
        rw [this]
        exact (F8.A₁ (quasithinOmegaOneCenter T) (k : G)).one_mem
      · have h1 : (k : G) * x * (k : G)⁻¹ = z' := by
          have h2 : (k : G) * x * (k : G)⁻¹ =
              (r : G)⁻¹ * ((r : G) * ((k : G) * x * (k : G)⁻¹) * (r : G)⁻¹) * (r : G) := by group
          have h3 : (r : G)⁻¹ * z' * (r : G) = z' := by
            have h4 : z' = (r : G)⁻¹ * ((r : G) * z' * (r : G)⁻¹) * (r : G) := by group
            rw [hrfix] at h4
            exact h4.symm
          rw [h2, e, h3]
        rw [h1]
        exact hz'A
  have hUsub : F8.Uγ (VZ T M) H (k : G) ≤ conjSub (k : G) (conjClosure (VZ T M) (mcOf T)) :=
    conjSub_mono (k : G) (conjClosure_mono le_rfl (S.le_mcOf hH))
  have hγ : ∀ u ∈ conjClosure (VZ T M) H,
      ⁅u, y⁆ ∈ conjSub (k : G) (conjClosure (VZ T M) (mcOf T)) := by
    intro u hu
    have h3 := h98.F913_3 sk (X := VZ T M) (Y := VZ T M) (Or.inl rfl) (Or.inl rfl)
    exact hUsub (h3 (Subgroup.commutator_mem_commutator hu hy)).2
  exact h.false_of_normalizes_U S hred h91 hyH hrH hyy hsw (hUsub hy) hrmem hγ
    (conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ hrH₁)))
    (fun w hw => h.rho_fix_W₂ h91 r hrH₁ hw)
    ⟨u₀, hu₀W, by rw [hρr]; exact hu₀mv⟩

end Central

theorem input14613B1ActC_proved : Input14613B1ActC := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h h4 δ δ' k sk hpos hle hQC y hy
  by_contra hnot
  have hH : IsHTM T M H := hred.isHTM
  have hyH : y ∈ H := (S.setup_le hH sk).1 hy
  rcases h.normalizer_or_swap S hred hyH with ⟨-, h1, -⟩ | ⟨h1, -⟩
  · exact hnot (mem_normalizer_of_conjSub_eq h1)
  · exact h.false_of_swap_of_central S hred h4 sk hpos hle hQC hy h1

end CFSG.Quasithin
