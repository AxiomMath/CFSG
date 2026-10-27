module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
open scoped MatrixGroups

theorem exists_mulEquiv_Wm_of_card_four {A : Type*} [CommGroup A] (hA : Nat.card A = 4)
    (hsq : ∀ a : A, a * a = 1) : Nonempty (A ≃* Wm (GaloisField 2 1)) := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let inst : Module (ZMod 2) (Additive A) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show (2 : ℕ) • x = 0
      rw [two_nsmul]
      exact Additive.toMul.injective (by simpa using hsq (Additive.toMul x)))
  have : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive A) = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    have h2 : Nat.card (Additive A) = 4 := hA
    rw [h2, Nat.card_zmod] at h1
    have : (2:ℕ) ^ 2 = 4 := by norm_num
    exact (Nat.pow_right_injective (le_refl 2) (h1.symm.trans this.symm))
  let e1 : Additive A ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hfr])
  let e2 : ZMod 2 ≃+ GaloisField 2 1 :=
    (GaloisField.equivZmodP 2).symm.toRingEquiv.toAddEquiv
  let e3 : (Fin 2 → ZMod 2) ≃+ (Fin 2 → GaloisField 2 1) := AddEquiv.piCongrRight (fun _ => e2)
  exact ⟨AddEquiv.toMultiplicativeRight (e1.toAddEquiv.trans e3)⟩

theorem natAct_surjective_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Function.Surjective (natAct : SL(2, F) →* MulAut (Wm F)) := by
  intro ρ
  have h01 := eq_zero_or_one_of_card_two hF
  set e0' : Wm F := Multiplicative.ofAdd (Pi.single 0 1) with he0'
  have hxform : ∀ x : Wm F, x = Multiplicative.ofAdd ![Multiplicative.toAdd x 0,
      Multiplicative.toAdd x 1] := fun x => by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  have he0'_ne : e0' ≠ 1 := by
    intro h
    have := congrArg (fun x : Wm F => Multiplicative.toAdd x 0) h
    simp [he0'] at this
  have hρe0 : ρ e0' ≠ 1 := fun h => he0'_ne (ρ.injective (by rw [h, map_one]))
  have hw : Multiplicative.toAdd (ρ e0') ≠ 0 := fun h => hρe0 (Multiplicative.toAdd.injective h)
  obtain ⟨g, hg⟩ := exists_smul_eq_e0 _ hw
  set ρ' : MulAut (Wm F) := natAct g * ρ with hρ'
  have hρ'e0 : ρ' e0' = e0' := by
    rw [hρ', MulAut.mul_apply, natAct_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hg]
    rfl
  have hρ'inj : ∀ x y : Wm F, ρ' x = ρ' y → x = y := fun x y h => ρ'.injective h
  have ha : ∀ x : Wm F, Multiplicative.toAdd (ρ' x) 1 = Multiplicative.toAdd x 1 := by
    intro x
    rcases h01 (Multiplicative.toAdd x 1) with hb | hb
    ·
      rw [hb]
      rcases h01 (Multiplicative.toAdd x 0) with ha0 | ha0
      · have : x = 1 := by
          rw [hxform x, ha0, hb]
          apply Multiplicative.toAdd.injective
          ext i
          fin_cases i <;> simp
        rw [this, map_one]; simp
      · have : x = e0' := by
          rw [hxform x, ha0, hb]
          apply Multiplicative.toAdd.injective
          ext i
          fin_cases i <;> simp [he0']
        rw [this, hρ'e0]; simp [he0']
    ·
      rw [hb]
      have hx1 : x ≠ 1 := by
        intro h
        have := congrArg (fun x : Wm F => Multiplicative.toAdd x 1) h
        simp [hb] at this
      have hxe0 : x ≠ e0' := by
        intro h
        have := congrArg (fun x : Wm F => Multiplicative.toAdd x 1) h
        simp [hb, he0'] at this
      rcases h01 (Multiplicative.toAdd (ρ' x) 1) with hc | hc
      · exfalso
        rcases h01 (Multiplicative.toAdd (ρ' x) 0) with hd | hd
        · apply hx1
          apply hρ'inj
          rw [map_one, hxform (ρ' x), hc, hd]
          apply Multiplicative.toAdd.injective
          ext i
          fin_cases i <;> simp
        · apply hxe0
          apply hρ'inj
          rw [hρ'e0, hxform (ρ' x), hc, hd]
          apply Multiplicative.toAdd.injective
          ext i
          fin_cases i <;> simp [he0']
      · exact hc
  obtain ⟨b, hb⟩ := normalizing_lemma_two hF ρ' ha
  have hρ'eq : ρ' = natAct (e12 b) := MulEquiv.ext hb
  refine ⟨g⁻¹ * e12 b, ?_⟩
  rw [map_mul, map_inv, ← hρ'eq, hρ']
  group


theorem card_galoisField_two_one : Nat.card (GaloisField 2 1) = 2 := by
  have := GaloisField.card 2 1 one_ne_zero
  simpa using this



variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
theorem conjAct_eq_one_iff_mem_centralizer {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g


namespace Hyp1281Two

theorem isNaturalSL2Module (h : Hyp1281Two G T M L) :
    IsNaturalSL2Module 1 L (pCoreOf 2 (L ⊔ T)) (VZ T M) (quasithinOmegaOneCenter T) := by
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  set V := VZ T M with hVdef
  set Z := quasithinOmegaOneCenter T with hZdef
  set F := GaloisField 2 1 with hFdef
  have hF : Nat.card F = 2 := card_galoisField_two_one
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := eq_zero_or_one_of_card_two hF
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := h.le.trans hVred.2.1
  have hVelem : IsElemAbelian 2 V := hVred.2.2.1
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVelem
  have hsq : ∀ v : ↥V, v * v = 1 := fun v =>
    Subtype.ext (by simpa [sq] using hVelem.2 v v.2)
  obtain ⟨ψ⟩ := exists_mulEquiv_Wm_of_card_four (A := ↥V) h.rank_two hsq
  let α : ↥L →* MulAut (Wm F) :=
    (MulAut.congr ψ).toMonoidHom.comp ((conjAct V).comp (Subgroup.inclusion hLN))
  let e : SL(2, F) ≃* MulAut (Wm F) :=
    MulEquiv.ofBijective (natAct : SL(2, F) →* MulAut (Wm F))
      ⟨natAct_injective, natAct_surjective_of_card_two hF⟩
  let θ : ↥L →* SL(2, F) := e.symm.toMonoidHom.comp α
  have hθ : ∀ a : ↥L, natAct (θ a) = α a := fun a => by
    show e (e.symm (α a)) = α a
    exact e.apply_symm_apply _
  have hαa : ∀ (a : ↥L) (v : ↥V), α a (ψ v) = ψ (conjAct V ⟨a, hLN a.2⟩ v) := fun a v => by
    simp [α, MulAut.congr_apply]
    rfl
  have hα1 : ∀ a : ↥L, α a = 1 ↔ conjAct V ⟨a, hLN a.2⟩ = 1 := fun a => by
    constructor
    · intro h1
      refine MulEquiv.ext fun v => ?_
      have := hαa a v
      rw [h1, MulAut.one_apply] at this
      rw [MulAut.one_apply]
      exact (ψ.injective this).symm
    · intro h1
      refine MulEquiv.ext fun w => ?_
      obtain ⟨v, rfl⟩ := ψ.surjective w
      rw [hαa, h1, MulAut.one_apply, MulAut.one_apply]
  have hθ1 : ∀ a : ↥L, θ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) := fun a => by
    have hc : conjAct V ⟨a, hLN a.2⟩ = 1 ↔ (a : G) ∈ Subgroup.centralizer (V : Set G) :=
      conjAct_eq_one_iff_mem_centralizer (V := V) (g := ⟨a, hLN a.2⟩)
    rw [← hc, ← hα1]
    constructor
    · intro h1
      rw [← hθ a, h1, map_one]
    · intro h1
      exact natAct_injective (by rw [hθ a, h1, map_one])
  have hCV : ∀ x : G, x ∈ L → (x ∈ Subgroup.centralizer (V : Set G) ↔ x ∈ pCoreOf 2 (L ⊔ T)) :=
    fun x hx => by
      rw [← h.centralizer]
      exact ⟨fun hc => ⟨Subgroup.mem_sup_left hx, hc⟩, fun hc => hc.2⟩
  have hker : θ.ker = (pCoreOf 2 (L ⊔ T)).subgroupOf L := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hθ1, hCV _ a.2]
  have hcomm := commutator_eq_zpowers_c3 (F := F) hF
  have hNn : (Subgroup.zpowers (c3 F)).Normal :=
    Subgroup.normal_of_index_eq_two (index_zpowers_c3 hF)
  have hrange_le : θ.range ≤ Subgroup.zpowers (c3 F) := by
    have htop : (Subgroup.zpowers (c3 F)).comap θ = ⊤ := by
      refine eq_top_of_oTwoUpper_eq h.residual.symm _ fun x => ⟨1, ?_⟩
      rw [Subgroup.mem_comap, map_pow, pow_one]
      have := Subgroup.pow_index_mem (Subgroup.zpowers (c3 F)) (θ x)
      rwa [index_zpowers_c3 hF] at this
    rintro _ ⟨x, rfl⟩
    have : x ∈ (Subgroup.zpowers (c3 F)).comap θ := by rw [htop]; exact Subgroup.mem_top x
    exact this
  have hrange_ne : θ.range ≠ ⊥ := by
    intro hbot
    apply h.not_le_centralizer_L
    intro x hx
    have : θ ⟨x, hx⟩ = 1 := by
      have hmem : θ ⟨x, hx⟩ ∈ θ.range := ⟨_, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact (hθ1 ⟨x, hx⟩).mp this
  have hrange : θ.range = commutator SL(2, F) := by
    rw [hcomm]
    have hcard : Nat.card (Subgroup.zpowers (c3 F)) = 3 := by rw [Nat.card_zpowers, orderOf_c3]
    have hdvd : Nat.card θ.range ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hrange_le
    have h1 : Nat.card θ.range ≠ 1 := fun h1 => hrange_ne (Subgroup.card_eq_one.mp h1)
    have h3 : Nat.card θ.range = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h h1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hcard, h3])
  obtain ⟨z, hzZ, hz1, hzall⟩ : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ∀ w ∈ Z, w = 1 ∨ w = z := by
    have hZ2 := h.card_omegaOneCenter
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ2
    obtain ⟨z, hzZ⟩ : ∃ z : Z, z ≠ 1 := by
      by_contra hall
      push Not at hall
      exact h.omegaOneCenter_ne_bot (by
        rw [eq_bot_iff]
        intro w hw
        have := hall ⟨w, hw⟩
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this)
    refine ⟨z, z.2, fun he => hzZ (Subtype.ext he), fun w hw => ?_⟩
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      have h1 := hy ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))
      have h2 := hy z hzZ
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hzV : z ∈ V := (omegaOneCenter_le_VZ T M) hzZ
  refine ⟨hLN, θ, ψ, hker, hrange, fun a v => ?_, Multiplicative.toAdd (ψ ⟨z, hzV⟩), ?_, fun v => ?_⟩
  · rw [hθ, hαa]
  · intro h0
    have : ψ ⟨z, hzV⟩ = 1 := Multiplicative.toAdd.injective h0
    have := ψ.injective (this.trans (map_one ψ).symm)
    exact hz1 (congrArg Subtype.val this)
  · constructor
    · intro hv
      rcases hzall _ hv with h1 | h1
      · refine ⟨0, ?_⟩
        have : v = 1 := Subtype.ext h1
        rw [this, map_one]
        simp
      · refine ⟨1, ?_⟩
        have : v = ⟨z, hzV⟩ := Subtype.ext h1
        rw [this, one_smul]
    · rintro ⟨c, hc⟩
      rcases h01 c with rfl | rfl
      · rw [zero_smul] at hc
        have : ψ v = 1 := Multiplicative.toAdd.injective hc
        have hv1 : v = 1 := ψ.injective (this.trans (map_one ψ).symm)
        have : (v : G) = 1 := congrArg Subtype.val hv1
        rw [this]
        exact Subgroup.one_mem _
      · rw [one_smul] at hc
        have : ψ v = ψ ⟨z, hzV⟩ := Multiplicative.toAdd.injective hc
        have hv1 : v = ⟨z, hzV⟩ := ψ.injective this
        have : (v : G) = z := congrArg Subtype.val hv1
        rw [this]
        exact hzZ

theorem VZ_eq_conjClosure_L (h : Hyp1281Two G T M L) :
    VZ T M = conjClosure (quasithinOmegaOneCenter T) L := by
  apply le_antisymm
  · obtain ⟨z, hzZ, hz1, -⟩ := h.exists_zgen
    have hzV := omegaOneCenter_le_VZ T M hzZ
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Subgroup.one_mem _
    · obtain ⟨l, hl, hlz⟩ := h.exists_conj_eq hzV hv hz1 hv1
      rw [← hlz]
      exact mem_conjClosure hl hzZ
  · exact conjClosure_mono le_rfl h.le

theorem almostSpecialL2Hyp (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    AlmostSpecialL2Hyp 1 (VZ T M) (quasithinOmegaOneCenter T) L T
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) where
  base := h.almostSpecialHyp_g1
  n_pos := Nat.one_pos
  V_eq := h.VZ_eq_conjClosure_L
  natural := h.isNaturalSL2Module
  U_ne := h.not_le_pCoreOf_LT_of_nonabelian hU

end Hyp1281Two

end CFSG.Quasithin
