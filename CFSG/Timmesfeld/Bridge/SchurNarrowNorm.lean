module

public import CFSG.Timmesfeld.Bridge.SchurNarrowBasic

public section

namespace CFSG.Timmesfeld.Bridge

open scoped commutatorElement

variable {K : Type*} [Group K]

theorem centralIn_one (S : Subgroup K) : CentralIn S 1 :=
  ⟨S.one_mem, fun q _ => Commute.one_right q⟩

theorem centralIn_conj {S : Subgroup K} {d w : K} (hd : d ∈ Subgroup.normalizer (S : Set K))
    (hw : CentralIn S w) : CentralIn S (d * w * d⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hd w).mp hw.1, fun q hq => ?_⟩
  have hq' : d⁻¹ * q * d ∈ S := by
    rw [Subgroup.mem_normalizer_iff.mp hd]
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hq
  have h := (hw.2 _ hq').eq
  show q * (d * w * d⁻¹) = d * w * d⁻¹ * q
  calc q * (d * w * d⁻¹) = d * ((d⁻¹ * q * d) * w) * d⁻¹ := by group
    _ = d * (w * (d⁻¹ * q * d)) * d⁻¹ := by rw [h]
    _ = d * w * d⁻¹ * q := by group

variable {Z : Subgroup K} [Z.Normal]

variable (Z) in
abbrev quotImage (S : Subgroup K) : Subgroup (K ⧸ Z) :=
  S.map (QuotientGroup.mk' Z)

variable (Z) in
@[expose] def centralPreimage (S : Subgroup K) : Subgroup K :=
  (quotImage Z S ⊓ Subgroup.centralizer (quotImage Z S : Set (K ⧸ Z))).comap
    (QuotientGroup.mk' Z)

variable {S : Subgroup K}

theorem mem_centralPreimage_iff {x : K} :
    x ∈ centralPreimage Z S ↔ CentralIn (quotImage Z S) (x : K ⧸ Z) := by
  simp only [centralPreimage, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    CentralIn, QuotientGroup.mk'_apply]
  rfl

theorem mk_mem_quotImage_iff (hZS : Z ≤ S) {x : K} :
    (x : K ⧸ Z) ∈ quotImage Z S ↔ x ∈ S := by
  change x ∈ (quotImage Z S).comap (QuotientGroup.mk' Z) ↔ x ∈ S
  rw [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])]

theorem mem_normalizer_of_mk_mem_quotImage (hZS : Z ≤ S) {g : K}
    (hg : (g : K ⧸ Z) ∈ Subgroup.normalizer (quotImage Z S : Set (K ⧸ Z))) :
    g ∈ Subgroup.normalizer (S : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  rw [← mk_mem_quotImage_iff hZS, ← mk_mem_quotImage_iff hZS, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact Subgroup.mem_normalizer_iff.mp hg _

theorem centralIn_mk {x : K} (hx : x ∈ S) (hc : ∀ q ∈ S, Commute q x) :
    CentralIn (quotImage Z S) (x : K ⧸ Z) := by
  refine ⟨Subgroup.mem_map_of_mem _ hx, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (hc q hq).map (QuotientGroup.mk' Z)

section Torus

variable {D : Subgroup (K ⧸ Z)}

theorem centralPreimage_le (hZc : Z ≤ Subgroup.center K) (hZS : Z ≤ S)
    (hDN : D ≤ Subgroup.normalizer (quotImage Z S : Set (K ⧸ Z)))
    (htrans : ∀ w w' : K ⧸ Z, CentralIn (quotImage Z S) w → w ≠ 1 →
      CentralIn (quotImage Z S) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    {w₀ : K} (hw₀S : w₀ ∈ S) (hw₀c : ∀ q ∈ S, Commute q w₀) (hw₀Z : w₀ ∉ Z) {x : K}
    (hx : x ∈ centralPreimage Z S) : x ∈ S ∧ ∀ q ∈ S, Commute q x := by
  by_cases hx1 : (x : K ⧸ Z) = 1
  · have hxZ := (QuotientGroup.eq_one_iff x).mp hx1
    exact ⟨hZS hxZ, fun q _ => Subgroup.mem_center_iff.mp (hZc hxZ) q⟩
  have hw₀1 : (w₀ : K ⧸ Z) ≠ 1 := fun h => hw₀Z ((QuotientGroup.eq_one_iff w₀).mp h)
  obtain ⟨d, hdD, hd⟩ := htrans _ _ (centralIn_mk hw₀S hw₀c) hw₀1
    (mem_centralPreimage_iff.mp hx) hx1
  obtain ⟨g, hgd⟩ : ∃ g : K, (g : K ⧸ Z) = d⁻¹ :=
    ⟨(Quotient.out d)⁻¹, by rw [QuotientGroup.mk_inv, QuotientGroup.out_eq']⟩
  have hgN : g ∈ Subgroup.normalizer (S : Set K) :=
    mem_normalizer_of_mk_mem_quotImage hZS (hgd ▸ hDN (D.inv_mem hdD))
  have hy : CentralIn S (g * w₀ * g⁻¹) := centralIn_conj hgN ⟨hw₀S, hw₀c⟩
  have hyx : ((g * w₀ * g⁻¹ : K) : K ⧸ Z) = x := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgd, inv_inv, hd]
  have hc := QuotientGroup.eq.mp hyx
  have hxe : x = g * w₀ * g⁻¹ * ((g * w₀ * g⁻¹)⁻¹ * x) := by group
  refine ⟨hxe ▸ S.mul_mem hy.1 (hZS hc), fun q hq => ?_⟩
  rw [hxe]
  exact (hy.2 q hq).mul_right (Subgroup.mem_center_iff.mp (hZc hc) q)

theorem mem_of_forall_conj_eq
    (htrans : ∀ w w' : K ⧸ Z, CentralIn (quotImage Z S) w → w ≠ 1 →
      CentralIn (quotImage Z S) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    (hcard : 4 ≤ Nat.card {w : K ⧸ Z // CentralIn (quotImage Z S) w})
    {x : K} (hx : x ∈ centralPreimage Z S)
    (hfix : ∀ d ∈ D, d * (x : K ⧸ Z) * d⁻¹ = x) : x ∈ Z := by
  classical
  by_contra hxZ
  have hx1 : (x : K ⧸ Z) ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
  have hall : ∀ w : {w : K ⧸ Z // CentralIn (quotImage Z S) w},
      (w : K ⧸ Z) ≠ 1 → (w : K ⧸ Z) = x := by
    intro w hw
    obtain ⟨d, hdD, hd⟩ := htrans _ _ (mem_centralPreimage_iff.mp hx) hx1 w.2 hw
    rw [← hd]
    simpa only [inv_inv] using hfix d⁻¹ (D.inv_mem hdD)
  let f : {w : K ⧸ Z // CentralIn (quotImage Z S) w} → Bool :=
    fun w => decide ((w : K ⧸ Z) = 1)
  have hf : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    by_cases hw : (w : K ⧸ Z) = 1
    · have hw' : (w' : K ⧸ Z) = 1 := by
        simpa [f, hw] using h
      rw [hw, hw']
    · have hw' : (w' : K ⧸ Z) ≠ 1 := by
        simpa [f, hw] using h
      rw [hall w hw, hall w' hw']
  have h2 := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by simp
  omega

end Torus

theorem inf_commutator_eq_bot_of_borelData [Finite K] (hZc : Z ≤ Subgroup.center K) {u : K}
    (hu : u * u = 1) (hZu : ∀ s ∈ Z, s = 1 ∨ s = u) (hZS : Z ≤ S)
    (hBD : SylowBorelData (K ⧸ Z) (quotImage Z S)) {w₀ : K} (hw₀S : w₀ ∈ S)
    (hw₀c : ∀ q ∈ S, Commute q w₀) (hw₀Z : w₀ ∉ Z) : Z ⊓ ⁅S, S⁆ = ⊥ := by
  classical
  obtain ⟨D, hDodd, hDN, htrans, hforms⟩ := hBD.torus
  have hWQ : ∀ x ∈ centralPreimage Z S, x ∈ S ∧ ∀ q ∈ S, Commute q x :=
    fun x hx => centralPreimage_le hZc hZS hDN htrans hw₀S hw₀c hw₀Z hx
  set W := centralPreimage Z S with hW
  have hWcomm : ∀ a b : W, a * b = b * a := fun a b =>
    Subtype.ext ((hWQ b b.2).2 a (hWQ a a.2).1).eq
  have hDW : ∀ d ∈ D, ∀ w ∈ W, quotConj Z d w ∈ W := fun d hd w hw =>
    mem_centralPreimage_iff.mpr (by
      rw [mk_quotConj]
      exact centralIn_conj (hDN hd) (mem_centralPreimage_iff.mp hw))
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hWcomm }
  let _ : MulDistribMulAction D W := quotConjAction hZc D W hDW
  let _ : Fintype D := Fintype.ofFinite D
  have hsmul : ∀ (d : D) (w : W), ((d • w : W) : K) = quotConj Z (d : K ⧸ Z) w :=
    fun _ _ => rfl
  have hNZ : ∀ w : W, (orbitNorm D W w : K) ∈ Z := fun w =>
    mem_of_forall_conj_eq htrans hBD.center_card (orbitNorm D W w).2 fun d hd => by
      rw [← mk_quotConj, ← hsmul ⟨d, hd⟩, smul_orbitNorm]
  have hNpow : ∀ w : W, (w : K) ∈ Z → orbitNorm D W w = w ^ Fintype.card D :=
    fun w hw => orbitNorm_of_forall_smul_eq fun d => Subtype.ext (by
      rw [hsmul, quotConj_of_mem_center _ (hZc hw)])
  let nm : K → K := fun x => if h : x ∈ W then (orbitNorm D W ⟨x, h⟩ : K) else 1
  have hnm : ∀ x (h : x ∈ W), nm x = orbitNorm D W ⟨x, h⟩ := fun x h => by simp [nm, h]
  have hnm_mul : ∀ x ∈ W, ∀ y ∈ W, nm (x * y) = nm x * nm y := by
    intro x hx y hy
    rw [hnm _ (W.mul_mem hx hy), hnm x hx, hnm y hy]
    exact congrArg Subtype.val (map_mul (orbitNorm D W) ⟨x, hx⟩ ⟨y, hy⟩)
  have hnm_one : nm 1 = 1 := by
    rw [hnm 1 W.one_mem]
    exact congrArg Subtype.val (map_one (orbitNorm D W))
  have hnm_conj : ∀ d ∈ D, ∀ x ∈ W, nm (quotConj Z d x) = nm x := by
    intro d hd x hx
    rw [hnm _ (hDW d hd x hx), hnm x hx]
    exact congrArg Subtype.val (orbitNorm_smul (⟨d, hd⟩ : D) (⟨x, hx⟩ : W))
  have hout : ∀ a ∈ quotImage Z S, Quotient.out a ∈ S :=
    fun a ha => (mk_mem_quotImage_iff hZS).mp (by rwa [QuotientGroup.out_eq'])
  have hcomW : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ W := fun a ha b hb =>
    mem_centralPreimage_iff.mpr (by
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      exact hBD.commutator_central _ (Subgroup.mem_map_of_mem _ ha) _
        (Subgroup.mem_map_of_mem _ hb))
  have hconj : ∀ a ∈ S, ∀ w ∈ W, a * w * a⁻¹ = w := fun a ha w hw => by
    rw [((hWQ w hw).2 a ha).eq, mul_inv_cancel_right]
  have hmul_left : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
    intro a ha b hb c hc
    have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hconj a ha _ (hcomW b hb c hc)]
  have hmul_right : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
    intro a ha b hb c hc
    have h1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1, hconj b hb _ (hcomW a ha c hc)]
  have hsq : ∀ a ∈ S, ∀ b ∈ S, nm ⁅a, b⁆ * nm ⁅a, b⁆ = 1 := by
    intro a ha b hb
    have haa : a * a ∈ W := mem_centralPreimage_iff.mpr (by
      rw [QuotientGroup.mk_mul]
      exact hBD.sq_central _ (Subgroup.mem_map_of_mem _ ha))
    rw [← hnm_mul _ (hcomW a ha b hb) _ (hcomW a ha b hb), ← hmul_left a ha a ha b hb,
      commutatorElement_eq_one_iff_mul_comm.mpr ((hWQ _ haa).2 b hb).symm.eq, hnm_one]
  have hval : ∀ a ∈ S, ∀ b ∈ S, nm ⁅a, b⁆ = 1 ∨ nm ⁅a, b⁆ = u :=
    fun a ha b hb => hZu _ (by rw [hnm _ (hcomW a ha b hb)]; exact hNZ _)
  have hor : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ e ∈ S,
      nm ⁅a, b⁆ = 1 ∨ nm ⁅c, e⁆ = 1 ∨ nm ⁅a, b⁆ = nm ⁅c, e⁆ := by
    intro a ha b hb c hc e he
    rcases hval a ha b hb with h | h
    · exact Or.inl h
    rcases hval c hc e he with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))
  let β : K ⧸ Z → K ⧸ Z → ZMod 2 :=
    fun a b => neOneInd (nm ⁅Quotient.out a, Quotient.out b⁆)
  have hβ : ∀ (a b : K ⧸ Z) (x y : K), (x : K ⧸ Z) = a → (y : K ⧸ Z) = b →
      β a b = neOneInd (nm ⁅x, y⁆) := by
    intro a b x y hx hy
    change neOneInd (nm ⁅Quotient.out a, Quotient.out b⁆) = _
    rw [commutatorElement_eq_of_mk_eq_central hZc (a := x) (b := y)
      (by rw [hx, QuotientGroup.out_eq']) (by rw [hy, QuotientGroup.out_eq'])]
  have hβ0 := hforms β
    (by
      intro a ha b hb c hc
      have hA := hout a ha
      have hB := hout b hb
      have hC := hout c hc
      rw [hβ (a * b) c (Quotient.out a * Quotient.out b) (Quotient.out c)
          (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq'])
          (QuotientGroup.out_eq' c),
        hmul_left _ hA _ hB _ hC, hnm_mul _ (hcomW _ hB _ hC) _ (hcomW _ hA _ hC),
        neOneInd_mul (hor _ hB _ hC _ hA _ hC) (hsq _ hB _ hC)]
      exact add_comm _ _)
    (by
      intro a ha b hb c hc
      have hA := hout a ha
      have hB := hout b hb
      have hC := hout c hc
      rw [hβ a (b * c) (Quotient.out a) (Quotient.out b * Quotient.out c)
          (QuotientGroup.out_eq' a)
          (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']),
        hmul_right _ hA _ hB _ hC, hnm_mul _ (hcomW _ hA _ hB) _ (hcomW _ hA _ hC),
        neOneInd_mul (hor _ hA _ hB _ hA _ hC) (hsq _ hA _ hB)])
    (by
      intro a _
      change neOneInd (nm ⁅Quotient.out a, Quotient.out a⁆) = 0
      rw [commutatorElement_self, hnm_one, neOneInd_one])
    (by
      intro a ha b hb
      have hbW : Quotient.out b ∈ W := mem_centralPreimage_iff.mpr (by
        rwa [QuotientGroup.out_eq'])
      change neOneInd (nm ⁅Quotient.out a, Quotient.out b⁆) = 0
      rw [commutatorElement_eq_one_iff_mul_comm.mpr ((hWQ _ hbW).2 _ (hout a ha)).eq, hnm_one,
        neOneInd_one])
    (by
      intro d hd a ha b hb
      rw [hβ _ _ (quotConj Z d⁻¹ (Quotient.out a)) (quotConj Z d⁻¹ (Quotient.out b))
          (by rw [mk_quotConj, QuotientGroup.out_eq', inv_inv])
          (by rw [mk_quotConj, QuotientGroup.out_eq', inv_inv]),
        ← quotConj_commutatorElement,
        hnm_conj _ (D.inv_mem hd) _ (hcomW _ (hout a ha) _ (hout b hb))])
  have hcom1 : ∀ x ∈ S, ∀ y ∈ S, nm ⁅x, y⁆ = 1 := by
    intro x hx y hy
    have h := hβ0 _ (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
    rw [hβ (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) x y rfl rfl] at h
    exact eq_one_of_neOneInd_eq_zero h
  have hle : ⁅S, S⁆ ≤ (orbitNorm D W).ker.map W.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⟨⁅x, y⁆, hcomW x hx y hy⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply Subtype.ext
    rw [← hnm _ (hcomW x hx y hy)]
    exact hcom1 x hx y hy
  rw [eq_bot_iff]
  rintro x ⟨hxZ, hxC⟩
  obtain ⟨w, hw, rfl⟩ := hle hxC
  have hw1 : orbitNorm D W w = 1 := MonoidHom.mem_ker.mp hw
  rw [hNpow w hxZ] at hw1
  have hw1' : (w : K) ^ Fintype.card D = 1 := by
    have := congrArg Subtype.val hw1
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
  rw [Subgroup.mem_bot]
  change (w : K) = 1
  rcases hZu _ hxZ with h1 | h1
  · exact h1
  · have h1' : (w : K) = u := h1
    have hDodd' : Odd (Fintype.card D) := by rwa [Fintype.card_eq_nat_card]
    obtain ⟨m, hm⟩ := hDodd'
    rw [h1'] at hw1' ⊢
    rw [hm, pow_succ, pow_mul, pow_two, hu, one_pow, one_mul] at hw1'
    exact hw1'

end CFSG.Timmesfeld.Bridge
