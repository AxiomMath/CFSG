module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aNe
public import CFSG.RankThree.GF2n.Stroth80.Sec53HcentC
public import CFSG.Quasithin.H13.GoldschmidtM22EndMul
public import CFSG.RankThree.GF2n.Stroth80.Sec53bProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_mul_of_card_eq_pow {A B D : Subgroup G} {q n k : ℕ}
    (hA : A ≤ D) (hB : B ≤ D) (hAc : Nat.card A = q ^ n) (hBc : Nat.card B = q ^ n)
    (hI : Nat.card ↥(A ⊓ B) ≤ q ^ k) (hD : Nat.card D * q ^ k = q ^ (2 * n)) :
    ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, d = a * b := by
  have h1 := CFSG.Quasithin.H13.GM22.card_mul_set_mul_card_inf A B
  have hsub : (A : Set G) * (B : Set G) ⊆ (D : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact D.mul_mem (hA ha) (hB hb)
  have hle : Nat.card ((A : Set G) * (B : Set G)) ≤ Nat.card D :=
    Nat.card_mono (Set.toFinite _) hsub
  have hAB : Nat.card A * Nat.card B = q ^ (2 * n) := by
    rw [hAc, hBc, ← pow_add, two_mul]
  have hup : Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card D := by
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul_left _ hle
  have hlow : Nat.card ↥(A ⊓ B) * Nat.card D ≤ Nat.card A * Nat.card B := by
    rw [hAB, ← hD, mul_comm (Nat.card D)]
    exact Nat.mul_le_mul_right _ hI
  exact CFSG.Quasithin.H13.GM22.exists_mul_eq_of_card_mul hA hB (le_antisymm hup hlow)

omit [Finite G] in
theorem mem_Wt_of_le_sup {Q V S X : Subgroup G} {a : G} (ha : a ∈ Wt Q V)
    (hS : ∀ s ∈ S, s * a = a * s) (hX : X ≤ S ⊔ V) : a ∈ Wt Q X := by
  refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hle : S ⊔ V ≤ Subgroup.centralizer {a} := by
    refine sup_le (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs)) ?_
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ha.2 v hv)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hX hx))

section ModelCount

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.card_le_of_le_inf_QB_inf_QB (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) {Y : Subgroup G}
    (hZY : Z ≤ Y) (hYQ : Y ≤ Q) (hYB : Y ≤ QB B) (hYC : Y ≤ QB C) {k : ℕ}
    (hk : Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ C) + 1 = k) :
    Nat.card ↥Y ≤ Nat.card Z ^ k := by
  haveI : FiniteDimensional K M₀.E := M₀.fin
  have hcard : Nat.card ↥Y = Nat.card Z * Nat.card ↥(M₀.img Y) := M₀.card_eq hYQ hZY
  set S : Submodule K M₀.E := imgQInfQB M₀ B ⊓ imgQInfQB M₀ C with hS
  haveI : FiniteDimensional K ↥S := FiniteDimensional.finiteDimensional_submodule S
  haveI : Finite ↥S := Module.finite_of_finite K
  have hsub : ((M₀.img Y : AddSubgroup M₀.E) : Set M₀.E) ⊆ (S : Set M₀.E) := by
    intro e he
    refine ⟨?_, ?_⟩
    · exact (hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD e).mpr
        (M₀.img_mono (le_inf hYQ hYB) he)
    · exact (hcC.mem_imgQInfQB_iff (X := C) hs.width hs.n_gt hnoC hD e).mpr
        (M₀.img_mono (le_inf hYQ hYC) he)
  have himg : Nat.card ↥(M₀.img Y) ≤ Nat.card ↥S := Nat.card_mono (Set.toFinite _) hsub
  have hSc : Nat.card ↥S = Nat.card K ^ Module.finrank K ↥S := Module.natCard_eq_pow_finrank
  have hKZ : Nat.card K = Nat.card Z := hD.card
  calc Nat.card ↥Y = Nat.card Z * Nat.card ↥(M₀.img Y) := hcard
    _ ≤ Nat.card Z * Nat.card Z ^ Module.finrank K ↥S := by
        apply Nat.mul_le_mul_left
        rw [← hKZ, ← hSc]
        exact himg
    _ = Nat.card Z ^ k := by rw [← hk, pow_succ']

end ModelCount


theorem sec53b_prod_of_model_count (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) (hr : r ∈ Rt M (LB M Q B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {D : Subgroup G} {k : ℕ}
    (hk : Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ (conjSubgroup r B)) + 1 = k)
    (hAD : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤ D)
    (hCD : QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤ D)
    (hDc : Nat.card ↥D * Nat.card Z ^ k = Nat.card Z ^ (2 * n)) :
    ∀ x ∈ D, ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), x = a * b := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm
  have hAc : Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n :=
    sec53b_card_QB_inf_Wt_sp h34 hRoot hc hs hm hV
  have hWr : conjSubgroup r (Wt Q (Vt M (LB M Q B) B Z t)) = Wt Q (Vt M (LB M Q B) B Z t) :=
    sec8_conjSubgroup_eq_of_mem_normalizer
      (sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 hrM) (hc.Rt_normalizes_Vt hs.mem hr))
  have hCc : Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ n := by
    have h : conjSubgroup r (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
        QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
      rw [QB_conj, conjSubgroup_inf, hWr]
    rw [← h, card_conjSubgroup]
    exact hAc
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hI := hc.card_le_of_le_inf_QB_inf_QB hs hcC hnoC hD
    (Y := (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)))
    (le_inf (le_inf hc.Z_le_QB.1 hZW) (le_inf hcC.Z_le_QB.1 hZW))
    (inf_le_left.trans (inf_le_right.trans hWQ)) (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) hk
  exact exists_mul_of_card_eq_pow hAD hCD hAc hCc hI hDc


theorem sec53_hBC_of_vone_ne (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hne : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane m hV K _ _ _ γ M₀ hD
  let T : Submodule K M₀.E :=
    imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  have hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun e => mem_imgSub
  have hm : 2 ≤ m := by
    obtain ⟨K₀, iF₀, iFin₀, hK₀, m₀, hm₀, hrep₀⟩ := hsp
    have hEq : m = m₀ := SpMNat.m_unique hV ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩
    omega
  exact ⟨T, hTmem, (Ctx.hBC_iff_vone_ne h34 hRoot h51 hc hs hm hV hr hplane hD T hTmem).mpr
    (hne G M Q Z B hc n t hs hsp r hr hplane)⟩

theorem stroth53bProd_of_vone_ne (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hne : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
          ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  obtain ⟨K₀, iF₀, iFin₀, hK₀, m, hm, hrep₀⟩ := hsp
  have hV : SpMNat hc t m := ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩
  have hsp' : SpNat hc t := ⟨K₀, iF₀, iFin₀, hK₀, m, hm, hrep₀⟩
  obtain ⟨K, iF, iFin, iCh, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF
  letI := iFin
  letI := iCh
  obtain ⟨T, hTmem, hBC⟩ :=
    sec53_hBC_of_vone_ne h34 hRoot h51 hne G M Q Z B hc n t hs hsp' r hr hplane m hV K γ M₀ hD
  have hspan := Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem
  have hcard := Ctx.card_vone_sp_of_hBC h34 hRoot hc hs hm hV hr hD T hTmem hBC hspan
  have hcommB : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommC : ∀ x ∈ Q ⊓ QB (conjSubgroup r B), ∀ y ∈ Q ⊓ QB (conjSubgroup r B),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hcC).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAD : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := fun a ha =>
    mem_Wt_of_le_sup ha.2
      (fun s hs' => hcommB s hs' a ⟨(inf_le_left : Wt Q _ ≤ Q) ha.2, ha.1⟩) inf_le_left
  have hCD : QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := fun a ha =>
    mem_Wt_of_le_sup ha.2
      (fun s hs' => hcommC s hs' a ⟨(inf_le_left : Wt Q _ ≤ Q) ha.2, ha.1⟩) inf_le_right
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have hDc : Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
      Nat.card Z ^ (2 * m) = Nat.card Z ^ (2 * n) := by
    have h := hc.card_Wt_mul_card_vone hs hcC hnoC
    rw [hcard, SpMNat.card_V hV, hQ] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hq 2) ?_
    calc Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          Nat.card Z ^ (2 * m) * Nat.card Z ^ 2
        = Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          (Nat.card Z ^ (2 * m + 1) * Nat.card Z) := by ring
      _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := h
      _ = Nat.card Z ^ (2 * n) * Nat.card Z ^ 2 := by ring
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := sec53b_prod_of_model_count h34 hRoot hc hs hm hV hr hD hBC
    hAD hCD hDc x hx
  exact ⟨a, ⟨ha.1, hAD ha⟩, b, ⟨hb.1, hCD hb⟩, hab⟩

theorem sec53CentralizerW1_of_vone_ne (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hne : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    Sec53CentralizerW1Statement :=
  sec53CentralizerW1Statement_holds_of_prod_hBC' h34 hRoot h51
    (stroth53bProd_of_vone_ne h34 hRoot h51 hne) (sec53_hBC_of_vone_ne h34 hRoot h51 hne)

end CFSG.RankThree.GF2n.Stroth80
