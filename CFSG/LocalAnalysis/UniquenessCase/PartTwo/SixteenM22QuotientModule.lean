module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22TenPointThreeHolds
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.H132Irr
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Sec
public import CFSG.Quasithin.Vol2.KGFactC31KG443Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}

theorem isQuasisimple_of_isSpor_m22 {X : Type} [Group X]
    (h : IsSpor X .M22) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  have hq : CFSG.IsQuasisimple (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      CFSG.Quasithin.KGC31.KG443.not_comm_m22).1
  have hq' : CFSG.IsQuasisimple X := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  exact ⟨Group.isPerfect_def.mp hq'.1, hq'.2.1⟩

section

omit [Finite W]

private theorem s16m_centralizer_of_quot_data
    {Q : Type} [CommGroup Q] [Finite Q]
    {q : W →* Q} {ρ : ↥H →* MulAut Q}
    (hH : IsSpor ↥H .M22)
    (hqsurj : Function.Surjective q)
    (hqker : ∀ x : W, q x = 1 ↔ x ∈ fixV H)
    (hρinj : Function.Injective ρ)
    (heq : ∀ (l : ↥H) (x : W), q ((l : MulAut W) x) = ρ l (q x))
    (hexp : ∀ x : Q, x ^ 2 = 1)
    (hcard : Nat.card Q = 2 ^ 10)
    (hirrQ : ∀ B : Subgroup Q, (∀ l : ↥H, ∀ b ∈ B, ρ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤) :
    Subgroup.centralizer (H : Set (MulAut W)) = ⊥ := by
  classical
  have hcent : Subgroup.centralizer (ρ.range : Set (MulAut Q)) = ⊥ := by
    have hcard30 : Nat.card Q ≤ 2 ^ 30 := by rw [hcard]; norm_num
    have hQ2 : ∀ x : Q, x * x = 1 := by
      intro x
      rw [← sq]
      exact hexp x
    have hspor : IsSpor ↥ρ.range .M22 := by
      obtain ⟨e⟩ := hH
      exact ⟨(MonoidHom.ofInjective hρinj).symm.trans e⟩
    have hirrRange : ∀ B : Subgroup Q, (∀ x ∈ ρ.range, ∀ b ∈ B, x b ∈ B) → B = ⊥ ∨ B = ⊤ :=
      fun B hB => hirrQ B fun l b hb => hB (ρ l) (MonoidHom.mem_range.mpr ⟨l, rfl⟩) b hb
    rcases mathieuSmallIrr22_holds (W := Q) hQ2 ρ.range hspor hirrRange hcard30 with
      hcode | hcocode
    · exact CFSG.Quasithin.H.ModelType.centralizer_eq_bot_of_code22 hcode
    · exact CFSG.Quasithin.H.ModelIrr.centralizer_eq_bot_of_cocode22 hcocode
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have hac : ∀ h ∈ H, a * h = h * a := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp ha h hh).symm
  have hZa : ∀ z ∈ fixV H, a z ∈ fixV H := by
    intro z hz
    rw [mem_fixV] at hz ⊢
    intro h hh
    have h1 : a (h z) = h (a z) := by
      have h2 := congrFun (congrArg DFunLike.coe (hac h hh)) z
      simpa only [MulAut.mul_apply] using h2
    calc h (a z) = a (h z) := h1.symm
      _ = a z := by rw [hz h hh]
  have hZa_inv : ∀ z ∈ fixV H, a⁻¹ z ∈ fixV H := by
    intro z hz
    rw [mem_fixV] at hz ⊢
    intro h hh
    have hainv : a⁻¹ * h = h * a⁻¹ := by
      have h1 : h * a⁻¹ = a⁻¹ * (a * h) * a⁻¹ := by group
      rw [hac h hh] at h1
      have h2 : a⁻¹ * (h * a) * a⁻¹ = a⁻¹ * h := by group
      exact (h1.trans h2).symm
    have h1 : a⁻¹ (h z) = h (a⁻¹ z) := by
      have h2 := congrFun (congrArg DFunLike.coe hainv) z
      simpa only [MulAut.mul_apply] using h2
    calc h (a⁻¹ z) = a⁻¹ (h z) := h1.symm
      _ = a⁻¹ z := by rw [hz h hh]
  have hZiff : ∀ z : W, z ∈ fixV H ↔ a z ∈ fixV H := by
    intro z
    refine ⟨hZa z, fun hz => ?_⟩
    have h1 := hZa_inv (a z) hz
    simpa using h1
  obtain ⟨ψ, hψ⟩ := s16g_exists_induced_aut (W := W) (Q := Q)
    (β := q) hqsurj (φ := a) (fun w => by
      rw [hqker w, hqker (a w)]
      exact hZiff w)
  have hψcent : ∀ x ∈ ρ.range, x * ψ = ψ * x := by
    intro x hx
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hx
    ext qv
    obtain ⟨w, rfl⟩ := hqsurj qv
    have haw : (l : MulAut W) (a w) = a ((l : MulAut W) w) := by
      have h1 := congrFun (congrArg DFunLike.coe (hac l l.2)) w
      simpa only [MulAut.mul_apply] using h1.symm
    calc (ρ l * ψ) (q w) = ρ l (ψ (q w)) := rfl
      _ = ρ l (q (a w)) := by rw [hψ w]
      _ = q ((l : MulAut W) (a w)) := (heq l (a w)).symm
      _ = q (a ((l : MulAut W) w)) := by rw [haw]
      _ = ψ (q ((l : MulAut W) w)) := (hψ _).symm
      _ = ψ (ρ l (q w)) := by rw [heq l w]
      _ = (ψ * ρ l) (q w) := rfl
  have hψ1 : ψ = 1 := by
    have hmem : ψ ∈ Subgroup.centralizer (ρ.range : Set (MulAut Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      exact hψcent
    rw [hcent] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfix : ∀ w : W, a w * w⁻¹ ∈ fixV H := by
    intro w
    have h2 : q (a w) = q w := by
      rw [← hψ w, hψ1]
      rfl
    have h3 : q (a w * w⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (hqker _).1 h3
  exact s16g_eq_one_of_commSub hcomm hac hfix

private theorem s16m_exists_order_three_of_nonidentity
    {Q : Type} [CommGroup Q] [Finite Q] {ρ : ↥H →* MulAut Q}
    (hspor : IsSpor ↥ρ.range .M22)
    (hirrQ : ∀ B : Subgroup Q, (∀ l : ↥H, ∀ b ∈ B, ρ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hexp : ∀ x : Q, x ^ 2 = 1)
    (hcard : Nat.card Q = 2 ^ 10)
    (hρinj : Function.Injective ρ) {v : Q} (hv : v ≠ 1) :
    ∃ h : ↥H, orderOf h = 3 ∧ ρ h v = v := by
  have hQ2 : ∀ x : Q, x * x = 1 := by
    intro x
    rw [← sq]
    exact hexp x
  obtain ⟨g, hg, hgord, hgv⟩ := k_M22TenPointThree_holds (W := Q) hQ2 hcard ρ.range hspor
    (fun B hB => hirrQ B fun l b hb => hB (ρ l) (MonoidHom.mem_range.mpr ⟨l, rfl⟩) b hb) v hv
  obtain ⟨h, hgh⟩ := MonoidHom.mem_range.mp hg
  exact ⟨h, by rw [← orderOf_injective ρ hρinj h, hgh, hgord], by rw [hgh]; exact hgv⟩

private theorem s16m_exists_order_three_fixing_of_quot_data
    {Q : Type} [CommGroup Q] [Finite Q] {q : W →* Q} {ρ : ↥H →* MulAut Q}
    (hqker : ∀ x : W, q x = 1 ↔ x ∈ fixV H)
    (hρinj : Function.Injective ρ)
    (heq : ∀ (l : ↥H) (x : W), q ((l : MulAut W) x) = ρ l (q x))
    (hspor : IsSpor ↥ρ.range .M22)
    (hirrQ : ∀ B : Subgroup Q, (∀ l : ↥H, ∀ b ∈ B, ρ l b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hexp : ∀ x : Q, x ^ 2 = 1)
    (hcard : Nat.card Q = 2 ^ 10)
    (hW : ∀ w : W, w ^ 2 = 1)
    (w : W) :
    ∃ b ∈ H, orderOf b = 3 ∧ b w = w := by
  classical
  have : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  by_cases hw : q w = 1
  · obtain ⟨v, hv⟩ := exists_ne (1 : Q)
    obtain ⟨h, hord, -⟩ :=
      s16m_exists_order_three_of_nonidentity hspor hirrQ hexp hcard hρinj hv
    have hordW : orderOf (h : MulAut W) = 3 := by
      have h1 := orderOf_injective H.subtype H.subtype_injective h
      exact h1.trans hord
    refine ⟨(h : MulAut W), h.2, hordW, ?_⟩
    exact mem_fixV.mp ((hqker w).1 hw) h h.2
  · obtain ⟨h, hord, hfix⟩ :=
      s16m_exists_order_three_of_nonidentity hspor hirrQ hexp hcard hρinj hw
    have hordW : orderOf (h : MulAut W) = 3 := by
      have h1 := orderOf_injective H.subtype H.subtype_injective h
      exact h1.trans hord
    refine ⟨(h : MulAut W), h.2, hordW, ?_⟩
    have hcZ : (h : MulAut W) w * w⁻¹ ∈ fixV H :=
      (hqker _).1 (by
        rw [map_mul, map_inv, heq h w, hfix, mul_inv_cancel])
    have hodd : Odd (orderOf h) := by rw [hord]; norm_num
    have hc : H.subtype h ((h : MulAut W) w * w⁻¹) = (h : MulAut W) w * w⁻¹ :=
      mem_fixV.mp hcZ h h.2
    have hm : H.subtype h w = ((h : MulAut W) w * w⁻¹) * w := by
      simp only [Subgroup.coe_subtype]
      group
    exact CFSG.Quasithin.Kleidman.F204.Sec.coprime_fix (A := W) (Γ := ↥H) (ρ := H.subtype)
      (fun x => by rw [← sq]; exact hW x) hodd hc hm

end

theorem centralizer_eq_bot_of_m22_quotient_rank_ten
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsSpor ↥H .M22)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10) :
    Subgroup.centralizer (H : Set (MulAut W)) = ⊥ := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥H := isQuasisimple_of_isSpor_m22 hH
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, hexp, hcardQ, hirrQ⟩ :=
    s16k_qm_quotMap (W := W) (H := H) hq hcomm hW
  have hcard : Nat.card Q = 2 ^ 10 := by rw [hcardQ, hdim]
  exact s16m_centralizer_of_quot_data hH hqsurj hqker hρinj heq hexp hcard
    (fun B hB => hirrQ hirr B hB) hcomm

theorem exists_order_three_fixing_of_m22_quotient_rank_ten
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsSpor ↥H .M22)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10)
    (w : W) :
    ∃ b ∈ H, orderOf b = 3 ∧ b w = w := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥H := isQuasisimple_of_isSpor_m22 hH
  obtain ⟨Q, hQc, hQf, q, ρ, _hqsurj, hqker, hρinj, heq, hexp, hcardQ, hirrQ⟩ :=
    s16k_qm_quotMap (W := W) (H := H) hq hcomm hW
  have hcard : Nat.card Q = 2 ^ 10 := by rw [hcardQ, hdim]
  have hspor : IsSpor ↥ρ.range .M22 := by
    obtain ⟨e⟩ := hH
    exact ⟨(MonoidHom.ofInjective hρinj).symm.trans e⟩
  exact s16m_exists_order_three_fixing_of_quot_data hqker hρinj heq hspor
    (fun B hB => hirrQ hirr B hB) hexp hcard hW w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
