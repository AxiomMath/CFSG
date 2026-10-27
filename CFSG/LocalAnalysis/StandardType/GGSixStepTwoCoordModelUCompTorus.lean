module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompClass

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

open Classical in
theorem card_not_pieceIn_le_one [Finite G] (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (hinj : Function.Injective (φ.comp F.ι)) {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)}
    (hxβ : F.ι (ofAdd β) = x) {a : K[X]} (ha : a ∈ primaryFactors (Xe x)) (ha1 : a ≠ X - C 1)
    {L₁ : Subgroup G} (hL₁ : L₁ = (sb h x a).map φ)
    (hcard : Nat.card ((φ.comp F.ι).range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤
      p ^ 2) : (Finset.univ.filter fun i => ¬ PieceIn F x a i).card ≤ 1 := by
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  set S' := Finset.univ.filter fun i => ¬ PieceIn F x a i with hS'
  obtain ⟨i₀, hi₀⟩ := exists_pieceIn hA F hxβ ha ha1
  have hβ₀ := ne_zero_of_pieceIn hA F hxβ ha ha1 hi₀
  have hi₀S : i₀ ∉ S' := by simp [hS', hi₀]
  set e : ZMod p × (S' → ZMod p) → (Fin F.r → ZMod p) :=
    fun κt i => if hi : i ∈ S' then κt.2 ⟨i, hi⟩ else κt.1 * β i with he
  have he_inj : Function.Injective e := by
    rintro ⟨κ, t⟩ ⟨κ', t'⟩ hkt
    have h1 := congrFun hkt i₀
    simp only [he, hi₀S, dite_false] at h1
    have hκ : κ = κ' := mul_right_cancel₀ hβ₀ h1
    refine Prod.ext hκ (funext fun ⟨i, hi⟩ => ?_)
    have h2 := congrFun hkt i
    simpa [he, hi] using h2
  have hs : ∀ κt i, PieceIn F x a i → e κt i = κt.1 * β i := by
    intro κt i hi
    have hiS : i ∉ S' := by simp [hS', hi]
    simp [he, hiS]
  have hle := card_le_card_inf_centralizer (L₁ := L₁) hinj e he_inj fun κt => by
    rw [hL₁]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, ι_comm_sb_class hA F hxβ ha (hs κt) hg]
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_finsetCard, ← pow_succ'] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hle.trans hcard)
  omega

theorem mem_orth_orbW (hA : MaxElemAb p A) {x : ↥(unitarySU 2 f K n)} (hxA : x ∈ A) {a b : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) (hb : b ∈ primaryFactors (Xe x))
    (hbS : b ∉ ({a, dualPoly h.bar a} : Set K[X])) {w : Fin n → K}
    (hw : w ∈ primaryComponent (Xe x) b) :
    w ∈ (orbW h x a).orthogonalBilin (stdHermForm h n) := by
  have H := primaryData h hA.prime hA.ne_two (hA.pow x hxA)
  refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hm
  have had := dualPoly_mem_primaryFactors H ha
  have h1 : stdHermForm h n m₁ w = 0 :=
    orthogonal_of_ne_dualPoly H ha hb (fun e => hbS (Or.inr e)) hm₁ hw
  have h2 : stdHermForm h n m₂ w = 0 :=
    orthogonal_of_ne_dualPoly H had hb
      (fun e => hbS (Or.inl (e.trans (dualPoly_dualPoly_of_mem H ha)))) hm₂ hw
  change stdHermForm h n (m₁ + m₂) w = 0
  rw [map_add, LinearMap.add_apply, h1, h2, add_zero]

theorem ι_mem_sb_torus (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hFm : FrameMoves F)
    {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) {i₀ : Fin F.r} {ε : Fin F.r → (ZMod p)ˣ}
    (hεO : ∀ i, ε i ∈ negQ p (2 ^ f)) (hε₀ : ε i₀ = 1)
    (hβε : ∀ i, PieceIn F x a i → β i = (ε i : ZMod p) * β i₀) {s : Fin F.r → ZMod p}
    (hsS : ∀ i, ¬ PieceIn F x a i → s i = 0) (hsum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0) :
    F.ι (ofAdd s) ∈ sb h x a := by
  classical
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have hsC := mem_centralizer_of_mem hA hxA (ι_mem F (ofAdd s))
  have hU := toUnitHom_mem_unitaryCentralizer (h := h) hsC
  have hgl : ∀ t, toUnitHom (F.ι t) ∈ gl_centralizer (toUnitHom x) := fun t =>
    (toUnitHom_mem_unitaryCentralizer (h := h) (mem_centralizer_of_mem hA hxA (ι_mem F t))).2
  refine mem_specialBlock.mpr ⟨⟨hU, fun b hb hbS v hv => ?_⟩, hU.2, ?_⟩
  ·
    change lin (F.ι (ofAdd s)) v = v
    refine (F.ι_fix _ v).mpr fun k hk => ?_
    have hkS : PieceIn F x a k := by
      by_contra hk'
      exact hk (by rw [toAdd_ofAdd]; exact hsS k hk')
    exact mem_orth_of_pieceIn hA F hkS (mem_orth_orbW hA hxA ha hb hbS hv)
  set D := blockDetHom (toUnitHom x) a with hD
  set Φ : Multiplicative (Fin F.r → ZMod p) →* (AdjoinRoot a)ˣ :=
    D.comp ((toUnitHom.comp F.ι).codRestrict (gl_centralizer (toUnitHom x)) hgl) with hΦ
  have hΦapp : ∀ t, Φ t = D ⟨toUnitHom (F.ι t), hgl t⟩ := fun t => rfl
  change Φ (ofAdd s) = 1
  set e₀ : Multiplicative (Fin F.r → ZMod p) := ofAdd (Pi.single i₀ 1) with he₀
  have hkey : ∀ i, PieceIn F x a i → Φ (ofAdd (Pi.single i (ε i : ZMod p))) = Φ e₀ := by
    intro i hi
    by_cases hii : i = i₀
    · rw [hii, hε₀, Units.val_one]
    set π : Equiv.Perm (Fin F.r) := Equiv.swap i₀ i with hπ
    set η : Fin F.r → (ZMod p)ˣ :=
      fun j => if j = i₀ then (ε i)⁻¹ else if j = i then ε i else 1 with hη
    have hηO : ∀ j, η j ∈ negQ p (2 ^ f) := by
      intro j
      simp only [hη]
      split_ifs
      · exact (negQ p (2 ^ f)).inv_mem (hεO i)
      · exact hεO i
      · exact (negQ p (2 ^ f)).one_mem
    have hprod : ∏ j, η j = 1 := by
      rw [Finset.prod_eq_mul i₀ i (Ne.symm hii) (fun c _ hc => by simp [hη, hc.1, hc.2])
        (fun h' => absurd (Finset.mem_univ _) h') (fun h' => absurd (Finset.mem_univ _) h')]
      simp only [hη, ite_true, hii, ite_false]
      exact inv_mul_cancel _
    obtain ⟨w, hw⟩ := hFm π η hηO hprod
    have hwβ : (fun j => (η j : ZMod p) * β (π j)) = β := by
      funext j
      by_cases hj₀ : j = i₀
      · rw [hj₀]
        simp only [hη, ite_true, hπ, Equiv.swap_apply_left]
        rw [hβε i hi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      · by_cases hji : j = i
        · rw [hji]
          simp only [hη, hii, ite_false, ite_true, hπ, Equiv.swap_apply_right]
          rw [hβε i hi]
        · simp only [hη, hj₀, hji, ite_false, hπ, Equiv.swap_apply_of_ne_of_ne hj₀ hji,
            Units.val_one, one_mul]
    have hwx : w⁻¹ * x * w = x := by rw [← hxβ, hw β, hwβ]
    have hwC : w ∈ Subgroup.centralizer {x} := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc w * x = w * (w⁻¹ * x * w) := by rw [hwx]
        _ = x * w := by group
    have hwe : (fun j => (η j : ZMod p) * (Pi.single i₀ (1 : ZMod p) : Fin F.r → ZMod p) (π j)) =
        Pi.single i (ε i : ZMod p) := by
      funext j
      by_cases hj₀ : j = i₀
      · rw [hj₀]
        simp only [hη, ite_true, hπ, Equiv.swap_apply_left]
        rw [Pi.single_eq_of_ne hii, Pi.single_eq_of_ne (Ne.symm hii), mul_zero]
      · by_cases hji : j = i
        · rw [hji]
          simp only [hη, hii, ite_false, ite_true, hπ, Equiv.swap_apply_right]
          rw [Pi.single_eq_same, Pi.single_eq_same, mul_one]
        · simp only [hη, hj₀, hji, ite_false, hπ, Equiv.swap_apply_of_ne_of_ne hj₀ hji,
            Units.val_one, one_mul]
          rw [Pi.single_eq_of_ne hj₀, Pi.single_eq_of_ne hji]
    have hwb : w⁻¹ * F.ι e₀ * w = F.ι (ofAdd (Pi.single i (ε i : ZMod p))) := by
      rw [he₀, hw, hwe]
    have hwgl : toUnitHom w ∈ gl_centralizer (toUnitHom x) :=
      (toUnitHom_mem_unitaryCentralizer (h := h) hwC).2
    have hconj : (⟨toUnitHom (F.ι (ofAdd (Pi.single i (ε i : ZMod p)))), hgl _⟩ :
        gl_centralizer (toUnitHom x)) = (⟨toUnitHom w, hwgl⟩ : gl_centralizer (toUnitHom x))⁻¹ *
          ⟨toUnitHom (F.ι e₀), hgl e₀⟩ * ⟨toUnitHom w, hwgl⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hwb, map_mul, map_mul, map_inv]
    rw [hΦapp, hΦapp, hconj, map_mul, map_mul, map_inv, mul_assoc, mul_comm (D _) (D _),
      inv_mul_cancel_left]
  have hpow : ∀ (c : ZMod p) (t : Fin F.r → ZMod p), Φ (ofAdd (c • t)) = Φ (ofAdd t) ^ c.val := by
    intro c t
    have hct : c • t = c.val • t := by
      funext j
      rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
    rw [hct, ofAdd_nsmul, map_pow]
  have hsingle : ∀ i, Φ (ofAdd (Pi.single i (s i))) =
      Φ e₀ ^ ((↑(ε i)⁻¹ : ZMod p) * s i).val := by
    intro i
    by_cases hi : PieceIn F x a i
    · have h1 : Pi.single i (s i) = ((↑(ε i)⁻¹ : ZMod p) * s i) • Pi.single i (ε i : ZMod p) := by
        funext j
        by_cases hji : j = i
        · rw [hji]
          simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
          rw [mul_comm (↑(ε i)⁻¹ : ZMod p), mul_assoc, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, mul_one]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji, smul_zero]
      rw [h1, hpow, hkey i hi]
    · rw [hsS i hi, mul_zero, Pi.single_zero, ofAdd_zero, map_one, ZMod.val_zero, pow_zero]
  have hdecomp : ofAdd s = ∏ i, ofAdd (Pi.single i (s i)) := by
    rw [← ofAdd_sum, Finset.univ_sum_single]
  rw [hdecomp, map_prod, Finset.prod_congr rfl fun i _ => hsingle i,
    Finset.prod_pow_eq_pow_sum]
  have hdvd : p ∣ ∑ i, ((↑(ε i)⁻¹ : ZMod p) * s i).val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact hsum
  have he₀p : Φ e₀ ^ p = 1 := by
    rw [← map_pow]
    have h1 : e₀ ^ p = 1 := by
      apply toAdd.injective
      funext j
      rw [toAdd_pow, he₀, toAdd_ofAdd, toAdd_one, Pi.smul_apply, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul]
      rfl
    rw [h1, map_one]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, he₀p, one_pow]

end CoordSU

end CFSG.StandardType
