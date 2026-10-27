module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveAdjoin
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveDiameter
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLiftModel
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocal
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModelStd
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModelIso

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

private theorem fiveReflOf_mul_self' (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) :
    fiveReflOf n ε x * fiveReflOf n ε x = 1 := by
  apply Units.ext
  change fiveReflMatrix n ε x * fiveReflMatrix n ε x = 1
  exact fiveReflMatrix_mul_self n ε x

private theorem exists_ne_zero_fiveOrth_singleton {n : ℕ} (hn : 2 ≤ n) {ε : Bool}
    {v : Fin (n + 1) → ZMod 5} (hv : fiveForm n ε v v ≠ 0) :
    ∃ x : Fin (n + 1) → ZMod 5, x ≠ 0 ∧ fiveForm n ε x v = 0 := by
  have h1 : IsFiveNondeg n ε (fiveOrth n ε (Submodule.span (ZMod 5) {v})) := by
    simpa only [top_inf_eq] using
      isFiveNondeg_inf_fiveOrth (isFiveNondeg_top n ε) (isFiveNondeg_span_singleton hv) le_top
  have h2 : 2 ≤ Module.finrank (ZMod 5) (fiveOrth n ε (Submodule.span (ZMod 5) {v})) := by
    have h := finrank_inf_fiveOrth_add (k := n) (ε := ε) (W := ⊤)
      (U := Submodule.span (ZMod 5) {v}) (isFiveNondeg_top n ε) le_top
    rw [top_inf_eq] at h
    have hspan : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {v}) ≤ 1 := by
      have h := finrank_span_le_card (R := ZMod 5) (s := ({v} : Set (Fin (n + 1) → ZMod 5)))
      simpa using h
    have htop :
        Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) = n + 1 := by
      rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
    rw [htop] at h
    omega
  obtain ⟨x, hx, hxQ⟩ := exists_fiveForm_eq_of_nondeg h1 h2 (c := 1)
  refine ⟨x, ?_, (mem_fiveOrth.mp hx) v (Submodule.subset_span (Set.mem_singleton v))⟩
  rintro rfl
  simp [fiveForm] at hxQ

private theorem fiveReflection_ne_one {n : ℕ} {ε π : Bool}
    {d : GL (Fin (n + 1)) (ZMod 5)} (hd : d ∈ fiveReflections n ε π) : d ≠ 1 := by
  obtain ⟨v, hv, -, hvd⟩ := exists_eq_fiveReflOf hd
  rw [hvd]
  intro h1
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp [fiveForm])
  have h := congrArg (fun g : GL (Fin (n + 1)) (ZMod 5) =>
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) h1
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
  rw [fiveReflOf_mulVec] at h
  have hcoef : 2 * fiveForm n ε v v * (fiveForm n ε v v)⁻¹ = 2 := by
    rw [mul_assoc, mul_inv_cancel₀ hv, mul_one]
  rw [hcoef] at h
  exact hv0 ((smul_eq_zero.mp (sub_eq_self.mp h)).resolve_left (by decide))

private theorem fiveReflection_ne_neg_one {n : ℕ} (hn : 2 ≤ n) {ε π : Bool}
    {d : GL (Fin (n + 1)) (ZMod 5)} (hd : d ∈ fiveReflections n ε π) : d ≠ -1 := by
  obtain ⟨v, hv, -, hvd⟩ := exists_eq_fiveReflOf hd
  intro hd1
  obtain ⟨x, hx0, hxv⟩ := exists_ne_zero_fiveOrth_singleton hn hv
  have hdx : (d : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x = x := by
    rw [hvd, fiveReflOf_mulVec, hxv]
    simp
  have hneg : (d : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x = -x := by
    rw [hd1]
    simp [Matrix.neg_mulVec]
  rw [hdx] at hneg
  have h2x : (2 : ZMod 5) • x = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact hx0 ((smul_eq_zero.mp h2x).resolve_left (by decide))

private theorem isOddTransp_fiveReflections (n : ℕ) (ε π : Bool) :
    IsOddTransp (fiveReflections n ε π) := by
  constructor
  · intro d hd
    obtain ⟨v, hv, hvπ, hvd⟩ := exists_eq_fiveReflOf hd
    rw [hvd]
    refine orderOf_eq_prime (p := 2) ?_ ?_
    · rw [pow_two, fiveReflOf_mul_self']
    · exact fiveReflection_ne_one (fiveReflOf_mem hv hvπ)
  · intro d hd e he
    obtain ⟨v, hv, hvπ, hvd⟩ := exists_eq_fiveReflOf hd
    obtain ⟨w, hw, hwπ, hwe⟩ := exists_eq_fiveReflOf he
    rw [hvd, hwe]
    by_cases h : ∃ μ : ZMod 5, w = μ • v
    · obtain ⟨μ, rfl⟩ := h
      have hμ : μ ≠ 0 := by
        rintro rfl
        exact hw (by simp [fiveForm])
      rw [fiveReflOf_smul n ε v hμ, fiveReflOf_mul_self']
      exact Or.inl (by norm_num)
    · push Not at h
      rw [orderOf_fiveReflOf_mul n ε π hv hvπ hw hwπ h]
      split_ifs
      · exact Or.inl dvd_rfl
      · exact Or.inr (by decide : Odd 5)
      · exact Or.inr (by decide : Odd 3)

theorem setup_fiveProjClass {n : ℕ} (hn : 4 ≤ n) (ε π : Bool) :
    Setup (fiveProjective n ε π) (fiveProjClass n ε π) := by
  have hn2 : 2 ≤ n := by omega
  let R := fiveReflectionGroup n ε π
  let φ : R →* fiveProjective n ε π := QuotientGroup.mk' (Subgroup.center R)
  have hφ_apply : ∀ r : R, φ r = (QuotientGroup.mk r : fiveProjective n ε π) := fun r => rfl
  have hne_one : ∀ d : R, (d : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π →
      φ d ≠ 1 := by
    intro d hd h1
    have hdmem : d ∈ Subgroup.center R := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    rcases (mem_center_fiveReflectionGroup_iff hn ε π d).mp hdmem with h | h
    · exact fiveReflection_ne_one hd h
    · exact fiveReflection_ne_neg_one hn2 hd h
  have hodd : IsOddTransp (fiveProjClass n ε π) := by
    have hD : IsOddTransp ((↑) ⁻¹' fiveReflections n ε π : Set R) :=
      IsOddTransp.preimage (isOddTransp_fiveReflections n ε π) R
    have himg : IsOddTransp (φ '' ((↑) ⁻¹' fiveReflections n ε π : Set R)) :=
      IsOddTransp.image hD φ (fun d hd => hne_one d hd)
    have hset : (φ '' ((↑) ⁻¹' fiveReflections n ε π : Set R)) = fiveProjClass n ε π := by
      ext x
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, rfl⟩
    rwa [hset] at himg
  have hgen : Subgroup.closure (fiveProjClass n ε π) = ⊤ := by
    have hD : Subgroup.closure ((↑) ⁻¹' fiveReflections n ε π : Set R) = ⊤ :=
      Subgroup.closure_closure_coe_preimage (k := fiveReflections n ε π)
    have hset : (φ '' ((↑) ⁻¹' fiveReflections n ε π : Set R)) = fiveProjClass n ε π := by
      ext x
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, rfl⟩
    rw [← hset]
    calc Subgroup.closure (φ '' ((↑) ⁻¹' fiveReflections n ε π : Set R))
        = (Subgroup.closure ((↑) ⁻¹' fiveReflections n ε π : Set R)).map φ :=
          (MonoidHom.map_closure φ _).symm
      _ = Subgroup.map φ ⊤ := by rw [hD]
      _ = ⊤ := Subgroup.map_top_of_surjective φ
        (QuotientGroup.mk'_surjective (N := Subgroup.center R))
  have hisClass : ∃ d₀ : fiveProjective n ε π, fiveProjClass n ε π = {g | IsConj d₀ g} := by
    have htop : 2 ≤ Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) := by
      rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
      omega
    obtain ⟨v₀, -, hv₀Q⟩ := exists_fiveForm_eq_of_nondeg (isFiveNondeg_top n ε) htop
      (c := fiveSignRep π)
    have hr₀ : fiveReflOf n ε v₀ ∈ fiveReflections n ε π :=
      fiveReflOf_mem (by rw [hv₀Q]; exact fiveSignRep_ne_zero π)
        (by rw [hv₀Q]; exact isSquare_fiveSignRep_iff π)
    let r₀R : R := ⟨fiveReflOf n ε v₀, Subgroup.subset_closure hr₀⟩
    refine ⟨φ r₀R, ?_⟩
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨g, hg, hconj⟩ := isConj_of_mem_fiveReflections hn ε π hr₀ hr
      let gR : R := ⟨g, hg⟩
      have hR : gR * r₀R * gR⁻¹ = r := by
        apply Subtype.ext
        simpa [gR, r₀R] using hconj
      refine isConj_iff.mpr ⟨φ gR, ?_⟩
      have hthis : φ (gR * r₀R * gR⁻¹) = φ r := by rw [hR]
      calc φ gR * φ r₀R * (φ gR)⁻¹
          = φ (gR * r₀R * gR⁻¹) := by simp only [map_mul, map_inv]
        _ = φ r := hthis
        _ = (QuotientGroup.mk r : fiveProjective n ε π) := hφ_apply r
    · intro hxconj
      obtain ⟨h, hh⟩ := isConj_iff.mp hxconj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
      let gR : R := g
      refine ⟨gR * r₀R * gR⁻¹, ?_, ?_⟩
      · have hcoe : ((gR * r₀R * gR⁻¹ : R) : GL (Fin (n + 1)) (ZMod 5)) =
            (g : GL (Fin (n + 1)) (ZMod 5)) * fiveReflOf n ε v₀ *
              (g : GL (Fin (n + 1)) (ZMod 5))⁻¹ := rfl
        rw [hcoe]
        exact conj_mem_fiveReflections (fiveForm_mulVec_of_mem g.2) hr₀
      · have hx : (QuotientGroup.mk (gR * r₀R * gR⁻¹) : fiveProjective n ε π) =
            (QuotientGroup.mk gR : fiveProjective n ε π) * QuotientGroup.mk r₀R *
              (QuotientGroup.mk gR : fiveProjective n ε π)⁻¹ := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [hx]
        exact hh
  exact ⟨hisClass, hodd, hgen⟩

theorem center_fiveProjective_eq_bot {n : ℕ} (hn : 4 ≤ n) (ε π : Bool) :
    Subgroup.center (fiveProjective n ε π) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  have hn2 : 2 ≤ n := by omega
  let R := fiveReflectionGroup n ε π
  have hcomm : ∀ r : R, (r : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π →
      Commute g r := by
    intro r hr
    have hzr : QuotientGroup.mk r * QuotientGroup.mk g = QuotientGroup.mk g * QuotientGroup.mk r :=
      Subgroup.mem_center_iff.mp hz (QuotientGroup.mk r)
    have hc_mem : g * r * g⁻¹ * r⁻¹ ∈ Subgroup.center R := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hzr]
      rw [mul_assoc, ← _root_.mul_inv_rev, mul_inv_cancel]
    have hgr : (g : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) *
        (g : GL (Fin (n + 1)) (ZMod 5))⁻¹ = (r : GL (Fin (n + 1)) (ZMod 5)) := by
      rcases (mem_center_fiveReflectionGroup_iff hn ε π (g * r * g⁻¹ * r⁻¹)).mp hc_mem with h | h
      · have h' : (g : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) *
            (g : GL (Fin (n + 1)) (ZMod 5))⁻¹ * (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ = 1 := h
        rw [mul_inv_eq_one] at h'
        exact h'
      · exfalso
        have h' : (g : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) *
            (g : GL (Fin (n + 1)) (ZMod 5))⁻¹ = -(r : GL (Fin (n + 1)) (ZMod 5)) := by
          have hcongr := congrArg (fun t => t * (r : GL (Fin (n + 1)) (ZMod 5))) h
          simpa [mul_assoc] using hcongr
        have hmem : (g : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) *
            (g : GL (Fin (n + 1)) (ZMod 5))⁻¹ ∈ fiveReflections n ε π :=
          conj_mem_fiveReflections (fiveForm_mulVec_of_mem g.2) hr
        rw [h'] at hmem
        exact neg_notMem_fiveReflections hn2 ε π hr hmem
    have : (g : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) =
        (r : GL (Fin (n + 1)) (ZMod 5)) * (g : GL (Fin (n + 1)) (ZMod 5)) := by
      have hcongr := congrArg (fun t => t * (g : GL (Fin (n + 1)) (ZMod 5))) hgr
      simpa [mul_assoc] using hcongr
    exact Subtype.ext this
  have hg_center : g ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro h
    have hh : (g : GL (Fin (n + 1)) (ZMod 5)) * (h : GL (Fin (n + 1)) (ZMod 5)) =
        (h : GL (Fin (n + 1)) (ZMod 5)) * (g : GL (Fin (n + 1)) (ZMod 5)) := by
      refine Subgroup.closure_induction (k := fiveReflections n ε π)
        (p := fun (r : GL (Fin (n + 1)) (ZMod 5))
          (_ : r ∈ Subgroup.closure (fiveReflections n ε π)) =>
          (g : GL (Fin (n + 1)) (ZMod 5)) * r = r * (g : GL (Fin (n + 1)) (ZMod 5)))
        ?_ ?_ ?_ ?_ h.2
      · intro r hr
        have h := (hcomm ⟨r, Subgroup.subset_closure hr⟩ hr).eq
        simpa using congrArg (fun x : R => (x : GL (Fin (n + 1)) (ZMod 5))) h
      · simp
      · intro x y hx hy ihx ihy
        rw [← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]
      · intro x hx ihx
        have hcongr := congrArg (fun t => x⁻¹ * t * x⁻¹) ihx
        have hx' : (g : GL (Fin (n + 1)) (ZMod 5)) * x⁻¹ =
            x⁻¹ * (g : GL (Fin (n + 1)) (ZMod 5)) := by
          simpa [mul_assoc] using hcongr.symm
        exact hx'
    exact Subtype.ext hh.symm
  rw [QuotientGroup.eq_one_iff]
  exact hg_center

theorem diameter_two_fiveProjClass {n : ℕ} (hn : 4 ≤ n) (ε π : Bool) :
    ∀ a ∈ fiveProjClass n ε π, ∀ b ∈ fiveProjClass n ε π, ¬ Commute a b →
      (commSet (fiveProjClass n ε π) a ∩ commSet (fiveProjClass n ε π) b).Nonempty := by
  intro a ha b hb hab
  obtain ⟨ra, hra, rfl⟩ := ha
  obtain ⟨rb, hrb, rfl⟩ := hb
  obtain ⟨v, hv, _, hveq⟩ := exists_eq_fiveReflOf hra
  obtain ⟨w, hw, _, hweq⟩ := exists_eq_fiveReflOf hrb
  have hcomm : ¬ Commute (fiveReflOf n ε v) (fiveReflOf n ε w) := by
    intro hc
    apply hab
    rw [commute_mk_iff_commute hn ε π hrb]
    exact Subtype.ext (by
      show (ra : GL (Fin (n + 1)) (ZMod 5)) * (rb : GL (Fin (n + 1)) (ZMod 5)) =
        (rb : GL (Fin (n + 1)) (ZMod 5)) * (ra : GL (Fin (n + 1)) (ZMod 5))
      rw [hveq, hweq]
      exact hc.eq)
  have hlin : ∀ μ : ZMod 5, w ≠ μ • v := by
    intro μ hμ
    exact hcomm ((commute_fiveReflOf_iff n ε hv hw).mpr (Or.inr ⟨μ, hμ⟩))
  obtain ⟨x, hx0, hxQ, hxπ, hxv, hxw⟩ :=
    exists_common_perp_fiveForm hn ε π hv hlin
  let rx : fiveReflectionGroup n ε π :=
    ⟨fiveReflOf n ε x, Subgroup.subset_closure (fiveReflOf_mem hxQ hxπ)⟩
  have hrx : (rx : GL (Fin (n + 1)) (ZMod 5)) = fiveReflOf n ε x := rfl
  have hne_a : (QuotientGroup.mk rx : fiveProjective n ε π) ≠ QuotientGroup.mk ra := by
    intro heq
    have hmem : rx * ra⁻¹ ∈ Subgroup.center (fiveReflectionGroup n ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
    rcases (mem_center_fiveReflectionGroup_iff hn ε π (rx * ra⁻¹)).mp hmem with h1 | hneg
    · have hGL : (rx : GL (Fin (n + 1)) (ZMod 5)) = (ra : GL (Fin (n + 1)) (ZMod 5)) := by
        have hthis : (rx : GL (Fin (n + 1)) (ZMod 5)) * (ra : GL (Fin (n + 1)) (ZMod 5))⁻¹
            = 1 := by
          have := h1
          rwa [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rwa [mul_inv_eq_one] at hthis
      have h1' : (rx : GL (Fin (n + 1)) (ZMod 5)) *ᵥ v = v := by
        rw [hrx, fiveReflOf_mulVec, fiveForm_comm n ε v x, hxv]
        simp
      have h2' : (ra : GL (Fin (n + 1)) (ZMod 5)) *ᵥ v = -v := by
        rw [hveq, fiveReflOf_mulVec]
        have hcoef : 2 * fiveForm n ε v v * (fiveForm n ε v v)⁻¹ = 2 := by
          rw [mul_assoc, mul_inv_cancel₀ hv, mul_one]
        rw [hcoef]
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact zmod5_sub_two_mul_self _
      have := congrArg (fun g : GL (Fin (n + 1)) (ZMod 5) =>
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ v) hGL
      rw [h1', h2'] at this
      have hv0 : v = 0 := by
        have h2v : (2 : ZMod 5) • v = 0 := by
          rw [two_smul]
          exact eq_neg_iff_add_eq_zero.mp this
        exact (smul_eq_zero.mp h2v).resolve_left (by decide)
      exact hv (by rw [hv0]; simp [fiveForm])
    · exfalso
      have hGL : (rx : GL (Fin (n + 1)) (ZMod 5)) = -(ra : GL (Fin (n + 1)) (ZMod 5)) := by
        have hthis : (rx : GL (Fin (n + 1)) (ZMod 5)) * (ra : GL (Fin (n + 1)) (ZMod 5))⁻¹
            = -1 := by
          have := hneg
          rwa [Subgroup.coe_mul, Subgroup.coe_inv] at this
        have hcongr := congrArg (fun z => z * (ra : GL (Fin (n + 1)) (ZMod 5))) hthis
        simpa [mul_assoc] using hcongr
      have hmem' : (rx : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π :=
        fiveReflOf_mem hxQ hxπ
      rw [hGL] at hmem'
      exact neg_notMem_fiveReflections (by omega : 2 ≤ n) ε π hra hmem'
  have hne_b : (QuotientGroup.mk rx : fiveProjective n ε π) ≠ QuotientGroup.mk rb := by
    intro heq
    have hmem : rx * rb⁻¹ ∈ Subgroup.center (fiveReflectionGroup n ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
    rcases (mem_center_fiveReflectionGroup_iff hn ε π (rx * rb⁻¹)).mp hmem with h1 | hneg
    · have hGL : (rx : GL (Fin (n + 1)) (ZMod 5)) = (rb : GL (Fin (n + 1)) (ZMod 5)) := by
        have hthis : (rx : GL (Fin (n + 1)) (ZMod 5)) * (rb : GL (Fin (n + 1)) (ZMod 5))⁻¹
            = 1 := by
          have := h1
          rwa [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rwa [mul_inv_eq_one] at hthis
      have h1' : (rx : GL (Fin (n + 1)) (ZMod 5)) *ᵥ w = w := by
        rw [hrx, fiveReflOf_mulVec, fiveForm_comm n ε w x, hxw]
        simp
      have h2' : (rb : GL (Fin (n + 1)) (ZMod 5)) *ᵥ w = -w := by
        rw [hweq, fiveReflOf_mulVec]
        have hcoef : 2 * fiveForm n ε w w * (fiveForm n ε w w)⁻¹ = 2 := by
          rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]
        rw [hcoef]
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact zmod5_sub_two_mul_self _
      have := congrArg (fun g : GL (Fin (n + 1)) (ZMod 5) =>
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ w) hGL
      rw [h1', h2'] at this
      have hw0 : w = 0 := by
        have h2v : (2 : ZMod 5) • w = 0 := by
          rw [two_smul]
          exact eq_neg_iff_add_eq_zero.mp this
        exact (smul_eq_zero.mp h2v).resolve_left (by decide)
      exact hw (by rw [hw0]; simp [fiveForm])
    · exfalso
      have hGL : (rx : GL (Fin (n + 1)) (ZMod 5)) = -(rb : GL (Fin (n + 1)) (ZMod 5)) := by
        have hthis : (rx : GL (Fin (n + 1)) (ZMod 5)) * (rb : GL (Fin (n + 1)) (ZMod 5))⁻¹
            = -1 := by
          have := hneg
          rwa [Subgroup.coe_mul, Subgroup.coe_inv] at this
        have hcongr := congrArg (fun z => z * (rb : GL (Fin (n + 1)) (ZMod 5))) hthis
        simpa [mul_assoc] using hcongr
      have hmem' : (rx : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π :=
        fiveReflOf_mem hxQ hxπ
      rw [hGL] at hmem'
      exact neg_notMem_fiveReflections (by omega : 2 ≤ n) ε π hrb hmem'
  refine ⟨QuotientGroup.mk rx, ?_⟩
  constructor
  · refine ⟨⟨rx, fiveReflOf_mem hxQ hxπ, rfl⟩, ?_, hne_a⟩
    show QuotientGroup.mk rx * QuotientGroup.mk ra =
      QuotientGroup.mk ra * QuotientGroup.mk rx
    have hcx : Commute rx ra := by
      apply Subtype.ext
      show (rx : GL (Fin (n + 1)) (ZMod 5)) * (ra : GL (Fin (n + 1)) (ZMod 5)) =
        (ra : GL (Fin (n + 1)) (ZMod 5)) * (rx : GL (Fin (n + 1)) (ZMod 5))
      rw [hrx, hveq]
      exact (fiveReflOf_commute_of_orthogonal hxQ hxπ hxv).eq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk hcx.eq
  · refine ⟨⟨rx, fiveReflOf_mem hxQ hxπ, rfl⟩, ?_, hne_b⟩
    show QuotientGroup.mk rx * QuotientGroup.mk rb =
      QuotientGroup.mk rb * QuotientGroup.mk rx
    have hcx : Commute rx rb := by
      apply Subtype.ext
      show (rx : GL (Fin (n + 1)) (ZMod 5)) * (rb : GL (Fin (n + 1)) (ZMod 5)) =
        (rb : GL (Fin (n + 1)) (ZMod 5)) * (rx : GL (Fin (n + 1)) (ZMod 5))
      rw [hrx, hweq]
      exact (fiveReflOf_commute_of_orthogonal hxQ hxπ hxw).eq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk hcx.eq


theorem exists_fiveLocalModel_proj {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} (A : FiveAdjoin k ε π) :
    ∃ r : fiveReflectionGroup (k + 1) (ε == π) π,
      (∀ x, ((r : GL (Fin (k + 2)) (ZMod 5)) :
          Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ x =
        x - (2 * fiveForm (k + 1) (ε == π) x A.a *
          (fiveForm (k + 1) (ε == π) A.a A.a)⁻¹) • A.a) ∧
      Nonempty (FiveLocalModel (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk r : fiveProjective (k + 1) (ε == π) π) k ε π) :=
  ⟨adjoinRa A, fun x => by rw [coe_adjoinRa, fiveReflOf_mulVec], ⟨adjoinLocalModel A hk⟩⟩

theorem fiveHyperplaneData_proj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {x : fiveProjective (k + 1) (ε == π) π} (hx : x ∈ fiveProjClass (k + 1) (ε == π) π)
    (c : FiveLocalModel (fiveProjClass (k + 1) (ε == π) π) x k ε π) : FiveHyperplaneData c := by
  obtain ⟨A⟩ := nonempty_fiveAdjoin k ε π
  have hra : ∀ x, ((adjoinRa A : GL (Fin (k + 2)) (ZMod 5)) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ x =
      x - (2 * fiveForm (k + 1) (ε == π) x A.a *
        (fiveForm (k + 1) (ε == π) A.a A.a)⁻¹) • A.a :=
    fun x => by rw [coe_adjoinRa, fiveReflOf_mulVec]
  let c₀ := adjoinLocalModel A hk
  refine FiveHyperplaneData.of_pivot (D := fiveProjClass (k + 1) (ε == π) π)
    (setup_fiveProjClass (by omega : 4 ≤ k + 1) (ε == π) π) (by omega : 3 ≤ k)
    (x₀ := (QuotientGroup.mk (adjoinRa A) : fiveProjective (k + 1) (ε == π) π)) (c₀ := c₀)
    ⟨adjoinRa A, ?_, rfl⟩ ?_ hx c
  · rw [coe_adjoinRa]
    exact fiveReflOf_mem A.sign_a.1 A.sign_a.2
  · refine FiveHyperplaneData.of_fiveAdjoin hk A hra c₀ ?_
    intro y _
    refine ⟨adjoinIotaSub A (c₀.toMulEquiv y), ?_, ?_, ?_⟩
    · have hmk := (adjoinLocalModel_eq_iff A hk y (c₀.toMulEquiv y)).mp rfl
      rw [adjoinPhi_apply] at hmk
      exact hmk.symm
    · rw [coe_adjoinIotaSub, ← fiveGLIso_apply]
      exact adjoinIota_apply_a A (c₀.toMulEquiv y)
    · intro z
      rw [coe_adjoinIotaSub]
      simpa using adjoinIota_apply_adjoin A (c₀.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) z 0

end CFSG.OddTranspositions.PartThree

end
