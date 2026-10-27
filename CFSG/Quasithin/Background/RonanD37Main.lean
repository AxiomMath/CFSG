module

public import CFSG.Quasithin.Background.RonanD37Bound
public import CFSG.Quasithin.Background.RonanD37Opt2
public import CFSG.Quasithin.Background.RonanD37Opt3
public import CFSG.Quasithin.Background.SmithD37Main
public import CFSG.Quasithin.Background.F918Z6Bridge

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SmithD37 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem qhatOf_eq_of_isSylowTwoOf {V : Type*} [CommGroup V] [Finite V]
    {X Y : Subgroup (MulAut V)} (hY : IsSylowTwoOf Y X) : qhatOf Y = qhatOf X := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  apply le_antisymm
  · rcases h : qhatOf X with _ | r
    · exact le_top
    · have hr : kq X 3 ≤ (r : WithTop ℚ) := le_of_eq h
      obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp hr
      obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hY hA.le hA.isElemAbelian2.isPGroup
      have hA' : IsA2 X (conjBy x⁻¹ A) := hA.conjBy (X.inv_mem hx)
      have hAY : conjBy x⁻¹ A ≤ Y := by
        intro y hy
        rw [mem_conjBy_iff] at hy
        have := hle hy
        rw [mem_conjSub] at this
        simpa [mul_assoc] using this
      exact kq_le_iff.mpr ⟨conjBy x⁻¹ A, ⟨hAY, hA'.ne_bot, hA'.isElemAbelian2⟩,
        (commSeries_conjBy_eq_bot_iff _ A 3).mpr hAk, by rw [rAV_conjBy]; exact hAr⟩
  · rcases h : qhatOf Y with _ | r
    · exact le_top
    · have hr : kq Y 3 ≤ (r : WithTop ℚ) := le_of_eq h
      obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp hr
      exact kq_le_iff.mpr ⟨A, ⟨hA.le.trans hY.1, hA.ne_bot, hA.isElemAbelian2⟩, hAk, hAr⟩

section Qhat

variable {U : Type} [CommGroup U] [Finite U] {X L₁ L₂ : Subgroup (MulAut U)} {s : MulAut U}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem of_mem_qhatStar {T' A : Subgroup (MulAut U)} (hT' : T' ≤ X)
    (hq : qhatOf T' = qhatOf X) (hA : A ∈ QhatStar T') :
    ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ IsA2 X A ∧ commSeries A 3 = ⊥ ∧ rAV A = r := by
  obtain ⟨r, hr, -, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := hA
  have hrA : r ≤ rAV A := le_kq_iff.mp (le_of_eq hr.symm) A hA2 hA3
  exact ⟨r, hq ▸ hr, ⟨hA2.le.trans hT', hA2.ne_bot, hA2.isElemAbelian2⟩, hA3,
    le_antisymm hAr hrA⟩

theorem le_of_cubic {B : Subgroup (MulAut U)} (hB : IsA2 X B) (hB3 : commSeries B 3 = ⊥)
    {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) : r ≤ rAV B := by
  have h := kq_le_iff.mpr ⟨B, hB, hB3, le_refl (rAV B)⟩
  rw [show kq X 3 = qhatOf X from rfl, hr] at h
  exact WithTop.coe_le_coe.mp h

theorem rAV_eq_iff {B : Subgroup (MulAut U)} (hB : IsA2 X B) {p q : ℕ} (hq : 0 < q) :
    rAV B = (p : ℚ) / q ↔ q * rkIdx (fixV B) = p * rk B := by
  have h0 : (0 : ℚ) < rk B := by exact_mod_cast hB.rk_pos
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  unfold rAV
  rw [div_eq_div_iff h0.ne' hq'.ne']
  constructor
  · intro h
    exact_mod_cast (by linarith : (q : ℚ) * rkIdx (fixV B) = p * rk B)
  · intro h
    have h' : (q : ℚ) * rkIdx (fixV B) = p * rk B := by exact_mod_cast h
    linarith

theorem le_rAV_iff {B : Subgroup (MulAut U)} (hB : IsA2 X B) {p q : ℕ} (hq : 0 < q) :
    (p : ℚ) / q ≤ rAV B ↔ p * rk B ≤ q * rkIdx (fixV B) := by
  have h0 : (0 : ℚ) < rk B := by exact_mod_cast hB.rk_pos
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  unfold rAV
  rw [div_le_div_iff₀ hq' h0]
  constructor
  · intro h
    exact_mod_cast (by linarith : (p : ℚ) * rk B ≤ q * rkIdx (fixV B))
  · intro h
    have h' : (p : ℚ) * rk B ≤ q * rkIdx (fixV B) := by exact_mod_cast h
    linarith

theorem qhat_two
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 2)
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ k, Mm.R₂ k = g)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (hL : IsPSL 2 2 n ↥L₁)
    {T' : Subgroup (MulAut U)} (hT' : T' ≤ X) (hq : qhatOf T' = qhatOf X)
    {A : Subgroup (MulAut U)} (hA : A ∈ QhatStar T') :
    (qhatOf X = ((3 / 2 : ℚ) : WithTop ℚ) ∧ (rk A = 2 * n ∨ (n = 3 ∧ rk A = 4))) ∨
      (n = 2 ∧ rk A = 3 ∧ qhatOf X = ((4 / 3 : ℚ) : WithTop ℚ)) := by
  obtain ⟨r, hqX, hAX, -, hrA⟩ := of_mem_qhatStar hT' hq hA
  obtain ⟨B, hBle, hB0, hBE, hB3, hrkB, hidxB⟩ := exists_opt_two Mm hR₁ hR₂ hF
  have hBX : IsA2 X B := ⟨hBle.trans (sup_le hC.le₁ hC.le₂), hB0, hBE⟩
  have hrB : rAV B = ((3 : ℕ) : ℚ) / ((2 : ℕ) : ℚ) := by
    rw [rAV_eq_iff hBX (by norm_num), hrkB, hidxB]
    ring
  have hle : r ≤ 3 / 2 := by
    have := le_of_cubic hBX hB3 hqX
    rw [hrB] at this
    norm_num at this
    exact this
  rcases bound_two hC Mm hF hn hL hAX with ⟨h1, h2⟩ | ⟨hn2, h3, h4⟩
  · left
    have h1' : ((3 : ℕ) : ℚ) / ((2 : ℕ) : ℚ) ≤ rAV A := (le_rAV_iff hAX (by norm_num)).mpr h1
    have hr32 : r = 3 / 2 := by
      refine le_antisymm hle ?_
      rw [← hrA]
      norm_num at h1'
      exact h1'
    refine ⟨by rw [hqX, hr32], h2 ?_⟩
    have h5 : rAV A = ((3 : ℕ) : ℚ) / ((2 : ℕ) : ℚ) := by
      rw [hrA, hr32]
      norm_num
    have := (rAV_eq_iff hAX (by norm_num)).mp h5
    omega
  · right
    refine ⟨hn2, h4, ?_⟩
    have h5 : rAV A = ((4 : ℕ) : ℚ) / ((3 : ℕ) : ℚ) := by
      rw [rAV_eq_iff hAX (by norm_num)]
      omega
    rw [hqX, ← hrA, h5]
    norm_num

theorem qhat_three (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 3)
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ k, Mm.R₂ k = g)
    (hF : Nat.card F = 2) {T' : Subgroup (MulAut U)} (hT' : T' ≤ X) (hq : qhatOf T' = qhatOf X)
    {A : Subgroup (MulAut U)} (hA : A ∈ QhatStar T') :
    qhatOf X = ((5 / 4 : ℚ) : WithTop ℚ) ∧ rk A = 4 := by
  obtain ⟨r, hqX, hAX, -, hrA⟩ := of_mem_qhatStar hT' hq hA
  obtain ⟨B, hBle, hB0, hBE, hB3, hrkB, hidxB⟩ := exists_opt_three Mm hR₁ hR₂ hF
  have hBX : IsA2 X B := ⟨hBle.trans (sup_le hC.le₁ hC.le₂), hB0, hBE⟩
  have hrB : rAV B = ((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ) := by
    rw [rAV_eq_iff hBX (by norm_num), hrkB, hidxB]
  have hle : r ≤ 5 / 4 := by
    have := le_of_cubic hBX hB3 hqX
    rw [hrB] at this
    norm_num at this
    exact this
  obtain ⟨h1, h2⟩ := bound_three hC Mm hF hAX
  have h1' : ((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ) ≤ rAV A := (le_rAV_iff hAX (by norm_num)).mpr h1
  have hr54 : r = 5 / 4 := by
    refine le_antisymm hle ?_
    rw [← hrA]
    norm_num at h1'
    exact h1'
  refine ⟨by rw [hqX, hr54], h2 ?_⟩
  have h5 : rAV A = ((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ) := by
    rw [hrA, hr54]
    norm_num
  have := (rAV_eq_iff hAX (by norm_num)).mp h5
  omega

end Qhat

section Shape

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem dim_two_data (Mm : MatModel L₁ L₂ F 2)
    (hA₁ : A38Types ↥L₁) (hA₂ : A38Types ↥L₂) :
    ∃ n, 2 ≤ n ∧ Nat.card F = 2 ^ n ∧ IsPSL 2 2 n ↥L₁ ∧ Omega4PlusModule (L₁ ⊔ L₂) n ∧
      (∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
        ∃ l, Mm.R₁ l = g) ∧
      (∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
        ∃ k, Mm.R₂ k = g) := by
  obtain ⟨h₁, n, hn, hF⟩ := range_eq_statedSL Mm.R₁ Mm.inj₁ hA₁ Mm.irr₁ Mm.end₁
  obtain ⟨h₂, -⟩ := range_eq_statedSL Mm.R₂ Mm.inj₂ hA₂ Mm.irr₂ Mm.end₂
  set e₁ := (MonoidHom.ofInjective Mm.inj₁).trans (MulEquiv.subgroupCongr h₁)
  set e₂ := (MonoidHom.ofInjective Mm.inj₂).trans (MulEquiv.subgroupCongr h₂)
  have hrange : ∀ (L : Subgroup (MulAut U)) (e : ↥L ≃* ↥(StatedSL 2 F)),
      (L.subtype.comp e.symm.toMonoidHom).range = L := by
    intro L e
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  refine ⟨n, hn, hF, isPSL_of_mulEquiv hn hF e₁, ⟨F, inferInstance, inferInstance, hF, ?_⟩,
    ?_, ?_⟩
  · refine tensorNat_realizes_of_pair L₁ L₂ Mm.β (L₁.subtype.comp e₁.symm.toMonoidHom)
      (L₂.subtype.comp e₂.symm.toMonoidHom) (hrange L₁ e₁) (hrange L₂ e₂) ?_ ?_
    · intro g u
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype]
      rw [Mm.act₁, coe_symm_ofInjective]
    · intro g u
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype]
      rw [Mm.act₂, coe_symm_ofInjective]
  · intro g hg
    have hmem : g ∈ Mm.R₁.range := h₁ ▸ CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    exact hmem
  · intro g hg
    have hmem : g ∈ Mm.R₂.range := h₂ ▸ CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    exact hmem

theorem dim_three_data [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U}
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 3) (hF : Nat.card F = 2)
    (hL : IsPSL 2 7 1 ↥L₁) :
    IsPSL 3 2 1 ↥L₁ ∧ TensorNatL32 (L₁ ⊔ L₂) ∧
      (∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
        ∃ l, Mm.R₁ l = g) ∧
      (∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
        ∃ k, Mm.R₂ k = g) := by
  have h₁ := natCard_of_isPSL_two_seven hL
  have h₂ : Nat.card ↥L₂ = 168 := by
    rw [← h₁]
    exact (Nat.card_congr hC.equiv.toEquiv).symm
  obtain ⟨hL3, hT⟩ := l32_of_dim_three Mm hF h₁ h₂
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 168 := by
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
    norm_num
  have hb₁ := Mm.inj₁.bijective_of_nat_card_le (by rw [hGL, h₁])
  have hb₂ := Mm.inj₂.bijective_of_nat_card_le (by rw [hGL, h₂])
  exact ⟨hL3, hT, fun g _ => hb₁.2 g, fun g _ => hb₂.2 g⟩

end Shape

theorem d37_full :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → V = orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L →
        ∀ A : Subgroup (MulAut ↥V), A ∈ QhatStar (autSub T V) →
          (∃ n : ℕ, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n ∧
            ((qhatOf (autSub (Mp ⊔ T) V) = ((3 / 2 : ℚ) : WithTop ℚ) ∧
                (rk A = 2 * n ∨ (n = 3 ∧ rk A = 4))) ∨
              (n = 2 ∧ rk A = 3 ∧ qhatOf (autSub (Mp ⊔ T) V) = ((4 / 3 : ℚ) : WithTop ℚ)))) ∨
          (IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V) ∧
            qhatOf (autSub (Mp ⊔ T) V) = ((5 / 4 : ℚ) : WithTop ℚ) ∧ rk A = 4) := by
  intro W _ _ M Mp T L V std hVT t htT htn hMp A hA
  have hL38 : D3L38 := d3L38_of_a38 d3A38_holds
  obtain ⟨htV, hC, hsup⟩ := core_of_d3Std hL38 asA21SQTKSection std hVT htT htn hMp
  have hSyl := (D37Cfg.of_d3L38 hL38 std hVT htT htn hMp).T_sylow
  have hq := qhatOf_eq_of_isSylowTwoOf hSyl
  have hT' : autSub T V ≤ autSub (Mp ⊔ T) V := autSub_mono le_sup_right V
  have := hC.nt
  obtain ⟨F, _, _, _, d, hd0, ⟨Mm⟩⟩ := exists_matModel hC.exp hC.comm hC.irr _ hC.swap₁ hC.swap₂
  rw [hsup]
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · exfalso
      obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V std t htT htn hMp
      have hLq := insp5a_sec_isQuasisimple std.hyp hA38
      have hLV : L ≤ stabSub V := insp5a_le_stabSub std.hyp
      have : IsSimpleGroup ↥(autSub L V) := hC.simple
      have hnt : autSub L V ≠ ⊥ := by
        have : Nontrivial ↥(autSub L V) := IsSimpleGroup.toNontrivial
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this
      obtain ⟨a, b, hab⟩ := exists_ne_comm_autSub hLV hLq hnt
      exact hab (comm_of_dim_one Mm a b)
    · obtain ⟨n, hn, hF, hL, hΩ, hR₁, hR₂⟩ := dim_two_data Mm hC.a38 hC.swap.a38
      exact Or.inl ⟨n, hL, hΩ, qhat_two hC Mm hR₁ hR₂ hF hn hL hT' hq hA⟩
  · obtain ⟨hd3, hF2, hL7⟩ := big_case hC Mm hd
    subst hd3
    obtain ⟨hL3, hT, hR₁, hR₂⟩ := dim_three_data hC Mm hF2 hL7
    exact Or.inr ⟨hL3, hT, qhat_three hC Mm hR₁ hR₂ hF2 hT' hq hA⟩

end CFSG.Quasithin.RonanD37
