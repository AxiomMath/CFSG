module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecCL3A4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conj_mul_of_mem_centralizer {u h : G} (hu : u ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    (hh : h ∈ Subgroup.normalizer (fsuVM T L I : Set G)) {v : G} (hv : v ∈ fsuVM T L I) :
    (u * h) * v * (u * h)⁻¹ = h * v * h⁻¹ := by
  have hv' : h * v * h⁻¹ ∈ fsuVM T L I := (Subgroup.mem_normalizer_iff.mp hh v).mp hv
  calc (u * h) * v * (u * h)⁻¹ = u * (h * v * h⁻¹) * u⁻¹ := by group
    _ = h * v * h⁻¹ := by
        rw [← Subgroup.mem_centralizer_iff.mp hu _ hv', mul_inv_cancel_right]

theorem conj_comm_conjugate (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {l m : G} (hl : l ∈ L)
    (hm : m ∈ CFSG.conjugate L t) {v : G} (hv : v ∈ fsuVM T L I) :
    (l * m) * v * (l * m)⁻¹ = (m * l) * v * (m * l)⁻¹ := by
  have hc : ⁅l, m⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    pCoreOf_L_le_centralizer hyp h1011
      (SecA.commutator_conjugate_le h37 hyp ht htn (Subgroup.commutator_mem_commutator hl hm)).1
  have hN : m * l ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    Subgroup.mul_mem _ (SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.conjugate_le_fsuL0 ht hm))
      (SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.le_fsuL0 T L hl))
  have e : l * m = ⁅l, m⁆ * (m * l) := by rw [commutatorElement_def]; group
  rw [e, conj_mul_of_mem_centralizer hc hN hv]

theorem mem_T1_of_conj_mem (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {s : G} (hs : s ∈ T)
    (hsv : s * v * s⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) : s ∈ T1 T L := by
  refine ⟨hs, ?_⟩
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hs) with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    apply hvC
    have hV2s : ⁅fsuVM T L I, CFSG.conjugate L t⁆ = CFSG.conjugate (fsuUL T L I) s := by
      rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L hs), h]
    have h1 : s * v * s⁻¹ ∈ fsuUL T L I := by
      have hv' := hv
      rw [hV2s] at hv'
      exact SecA.mem_conjugate_iff.mp hv'
    have h2 := (inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h1, hsv⟩).2
    have hN := SecA.le_normalizer_centralizer (V := fsuL0 T L) (SecA.le_fsuM T L)
    have h3 := (Subgroup.mem_normalizer_iff.mp (hN (T.inv_mem hs)) _).mp h2
    have e : s⁻¹ * (s * v * s⁻¹) * s⁻¹⁻¹ = v := by group
    rwa [e] at h3

theorem exists_decomp_stabilizer (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hD : ∀ γ, ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {g : G} (hg : g ∈ fsuL0 T L ⊔ T)
    (hgv : g * v * g⁻¹ = v) :
    ∃ l ∈ L, ∃ m ∈ CFSG.conjugate L t,
      (∀ w ∈ fsuVM T L I, g * w * g⁻¹ = (l * m) * w * (l * m)⁻¹) ∧ m * v * m⁻¹ = v := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, hV2, -⟩ := hdec t ht htn
  have hLtN := conjugate_le_normalizer hyp ht
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuL0_le_normalizer_fsuVM T L I
  have hg' : g ∈ (↑(fsuL0 T L ⊔ T) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (SecA.le_fsuM T L)] at hg'
  obtain ⟨y, hy, s, hs, hys⟩ := hg'
  have hys' : y * s = g := hys
  have hy' : y ∈ (↑(L ⊔ CFSG.conjugate L t) : Set G) := by
    rw [← SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLtN] at hy'
  obtain ⟨l', hl', m', hm', hlm⟩ := hy'
  have hlm' : l' * m' = y := hlm
  have hL0V2 : fsuL0 T L ≤ Subgroup.normalizer
      ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator hL0N
      (SecA.fsuL0_le_normalizer_conjugate hyp.fsu.maximal.1 (SecA.le_fsuM T L ht))
  have hsv : s * v * s⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    have e : s * v * s⁻¹ = y⁻¹ * (g * v * g⁻¹) * y := by rw [← hys']; group
    rw [e, hgv]
    have := (Subgroup.mem_normalizer_iff.mp (hL0V2 (Subgroup.inv_mem _ hy)) v).mp hv
    rwa [inv_inv] at this
  have hsT1 := mem_T1_of_conj_mem h37 h38 hyp h1011 ht htn hv hvC hs hsv
  obtain ⟨d₁, hd₁, d₂, hd₂, hsd⟩ := exists_decomp_T1 h37 h38 hyp h1011 h3 D hD ht htn hsT1
  refine ⟨l' * d₁, L.mul_mem hl' hd₁.2, m' * d₂, Subgroup.mul_mem _ hm' hd₂.2, ?_, ?_⟩
  · intro w hw
    have hd2w : d₂ * w * d₂⁻¹ ∈ fsuVM T L I :=
      (Subgroup.mem_normalizer_iff.mp (hL0N (SecA.conjugate_le_fsuL0 ht hd₂.2)) w).mp hw
    have hcomm := conj_comm_conjugate h37 hyp h1011 ht htn hd₁.2 hm' hd2w
    rw [← hys', ← hlm']
    calc l' * m' * s * w * (l' * m' * s)⁻¹ = l' * m' * (s * w * s⁻¹) * (l' * m')⁻¹ := by group
      _ = l' * m' * ((d₁ * d₂) * w * (d₁ * d₂)⁻¹) * (l' * m')⁻¹ := by rw [hsd w hw]
      _ = l' * ((m' * d₁) * (d₂ * w * d₂⁻¹) * (m' * d₁)⁻¹) * l'⁻¹ := by group
      _ = l' * ((d₁ * m') * (d₂ * w * d₂⁻¹) * (d₁ * m')⁻¹) * l'⁻¹ := by rw [← hcomm]
      _ = (l' * d₁ * (m' * d₂)) * w * (l' * d₁ * (m' * d₂))⁻¹ := by group
  ·
    have hvV : v ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans hL0N) hv
    have hcomm := conj_comm_conjugate h37 hyp h1011 ht htn hd₁.2 hm'
      ((Subgroup.mem_normalizer_iff.mp (hL0N (SecA.conjugate_le_fsuL0 ht hd₂.2)) v).mp hvV)
    have h1 : (l' * d₁ * (m' * d₂)) * v * (l' * d₁ * (m' * d₂))⁻¹ = v := by
      calc (l' * d₁ * (m' * d₂)) * v * (l' * d₁ * (m' * d₂))⁻¹ =
          l' * ((d₁ * m') * (d₂ * v * d₂⁻¹) * (d₁ * m')⁻¹) * l'⁻¹ := by group
        _ = l' * ((m' * d₁) * (d₂ * v * d₂⁻¹) * (m' * d₁)⁻¹) * l'⁻¹ := by rw [hcomm]
        _ = l' * m' * ((d₁ * d₂) * v * (d₁ * d₂)⁻¹) * (l' * m')⁻¹ := by group
        _ = l' * m' * (s * v * s⁻¹) * (l' * m')⁻¹ := by rw [hsd v hvV]
        _ = g * v * g⁻¹ := by rw [← hys', ← hlm']; group
        _ = v := hgv
    have hmv : (m' * d₂) * v * (m' * d₂)⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hL0V2 (SecA.conjugate_le_fsuL0 ht
        (Subgroup.mul_mem _ hm' hd₂.2))) v).mp hv
    have hc : (l' * d₁) * ((m' * d₂) * v * (m' * d₂)⁻¹) * (l' * d₁)⁻¹ =
        (m' * d₂) * v * (m' * d₂)⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hmv) _ (L.mul_mem hl' hd₁.2),
        mul_inv_cancel_right]
    rw [← hc]
    calc (l' * d₁) * ((m' * d₂) * v * (m' * d₂)⁻¹) * (l' * d₁)⁻¹ =
        (l' * d₁ * (m' * d₂)) * v * (l' * d₁ * (m' * d₂))⁻¹ := by group
      _ = v := h1

theorem nonempty_stabilizer_equiv (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) (v : ↥(fsuVM T L I)) (hvU : (v : G) ∈ U₂)
    (hvC : (v : G) ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    Nonempty (↥(autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓
        MulAction.stabilizer (MulAut ↥(fsuVM T L I)) v) ≃*
      (↥(alternatingGroup (Fin 4)) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  have hcv := coord_eq_e0 hF2 hU₂ hvU hvC
  obtain ⟨-, hKN2, -, hD₂, -, hsq2, hfix2, hZc2, hFF2, -⟩ := hF2
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  have hvW : (v : G) ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hU₂.1 hvU
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuL0_le_normalizer_fsuVM T L I
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) := (SecA.le_fsuL0 T L).trans hL0N
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.conjugate_le_fsuL0 ht).trans hL0N
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer hLtN
  have hstab : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (fsuVM T L I : Set G)),
      conjAct (fsuVM T L I) ⟨x, hx⟩ ∈ MulAction.stabilizer (MulAut ↥(fsuVM T L I)) v ↔
        x * v * x⁻¹ = v := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  set Aa : Subgroup (MulAut ↥(fsuVM T L I)) := autOn L (fsuVM T L I) with hAa
  set Bb : Subgroup (MulAut ↥(fsuVM T L I)) := autOn (CFSG.conjugate L t) (fsuVM T L I) ⊓
    MulAction.stabilizer (MulAut ↥(fsuVM T L I)) v with hBb
  set X : Subgroup (MulAut ↥(fsuVM T L I)) := autOn (fsuL0 T L ⊔ T) (fsuVM T L I) ⊓
    MulAction.stabilizer (MulAut ↥(fsuVM T L I)) v with hX
  have hAX : Aa ≤ X := by
    intro a ha
    obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := SecB.mem_autOn_iff.mp ha
    refine ⟨SecB.mem_autOn_iff.mpr ⟨⟨l, hlN⟩, Subgroup.mem_sup_left (SecA.le_fsuL0 T L hl), rfl⟩,
      (hstab l hlN).mpr ?_⟩
    rw [Subgroup.mem_centralizer_iff.mp (hV2 hvW) l hl, mul_inv_cancel_right]
  have hBX : Bb ≤ X := by
    rintro b ⟨hb, hbs⟩
    obtain ⟨⟨m, hmN⟩, hm, rfl⟩ := SecB.mem_autOn_iff.mp hb
    exact ⟨SecB.mem_autOn_iff.mpr ⟨⟨m, hmN⟩,
      Subgroup.mem_sup_left (SecA.conjugate_le_fsuL0 ht hm), rfl⟩, hbs⟩
  have hcomm : ∀ a ∈ Aa, ∀ b ∈ Bb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := SecB.mem_autOn_iff.mp ha
    obtain ⟨⟨m, hmN⟩, hm, rfl⟩ := SecB.mem_autOn_iff.mp hb.1
    rw [← map_mul, ← map_mul]
    ext w
    exact conj_comm_conjugate h37 hyp h1011 ht htn hl hm w.2
  have hdisj : ∀ a ∈ Aa, a ∈ Bb → a = 1 := by
    intro a ha hb
    obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := SecB.mem_autOn_iff.mp ha
    obtain ⟨⟨m, hmN⟩, hm, hml⟩ := SecB.mem_autOn_iff.mp hb.1
    ext w
    change l * w * l⁻¹ = w
    have hw : (w : G) ∈ fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
      rw [← hVeq]
      exact w.2
    have h1 := mem_of_le_eqSet (a := l) (b := 1) (fun x hx => ?_) (fun y hy => ?_) hw
    · simpa using h1
    · have := congrArg (fun f : MulAut ↥(fsuVM T L I) =>
        ((f ⟨x, hV1V hx⟩ : ↥(fsuVM T L I)) : G)) hml
      change m * x * m⁻¹ = l * x * l⁻¹ at this
      rw [← this, Subgroup.mem_centralizer_iff.mp (hV1 hx) m hm, mul_inv_cancel_right]
      group
    · rw [Subgroup.mem_centralizer_iff.mp (hV2 hy) l hl, mul_inv_cancel_right]
      group
  have hgen : ∀ x ∈ X, ∃ a ∈ Aa, ∃ b ∈ Bb, a * b = x := by
    rintro x ⟨hx, hxs⟩
    obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := SecB.mem_autOn_iff.mp hx
    have hgv := (hstab g hgN).mp hxs
    obtain ⟨l, hl, m, hm, hlm, hmv⟩ :=
      exists_decomp_stabilizer h37 h38 hyp h1011 h3 D hF1.2.2.2.1 ht htn hvW hvC hg hgv
    refine ⟨conjAct (fsuVM T L I) ⟨l, hLN hl⟩, SecB.mem_autOn_iff.mpr ⟨⟨l, hLN hl⟩, hl, rfl⟩,
      conjAct (fsuVM T L I) ⟨m, hLtN hm⟩,
      ⟨SecB.mem_autOn_iff.mpr ⟨⟨m, hLtN hm⟩, hm, rfl⟩, (hstab m (hLtN hm)).mpr hmv⟩, ?_⟩
    rw [← map_mul]
    ext w
    exact (hlm w w.2).symm
  let φ : ↥Aa × ↥Bb →* ↥X :=
    { toFun := fun p => ⟨(p.1 : MulAut ↥(fsuVM T L I)) * p.2, X.mul_mem (hAX p.1.2) (hBX p.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun p q => by
        apply Subtype.ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        rw [mul_assoc, ← mul_assoc (q.1 : MulAut ↥(fsuVM T L I)),
          hcomm _ q.1.2 _ p.2.2]
        group }
  have hφ : Function.Bijective φ := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h1 : (p.1 : MulAut ↥(fsuVM T L I)) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have h2 : (q.1 : MulAut ↥(fsuVM T L I))⁻¹ * p.1 = q.2 * (p.2 : MulAut ↥(fsuVM T L I))⁻¹ := by
        calc (q.1 : MulAut ↥(fsuVM T L I))⁻¹ * p.1 =
            (q.1 : MulAut ↥(fsuVM T L I))⁻¹ * (p.1 * p.2) * (p.2 : MulAut ↥(fsuVM T L I))⁻¹ := by
              group
          _ = (q.1 : MulAut ↥(fsuVM T L I))⁻¹ * (q.1 * q.2) * (p.2 : MulAut ↥(fsuVM T L I))⁻¹ := by
              rw [h1]
          _ = q.2 * (p.2 : MulAut ↥(fsuVM T L I))⁻¹ := by group
      have h3 := hdisj _ (Aa.mul_mem (Aa.inv_mem q.1.2) p.1.2)
        (h2 ▸ Bb.mul_mem q.2.2 (Bb.inv_mem p.2.2))
      have h4 : (p.1 : MulAut ↥(fsuVM T L I)) = q.1 := by
        rw [← mul_left_cancel_iff (a := (q.1 : MulAut ↥(fsuVM T L I))⁻¹), h3, inv_mul_cancel]
      have h5 : (p.2 : MulAut ↥(fsuVM T L I)) = q.2 := by
        rw [h4] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    · obtain ⟨a, ha, b, hb, hab⟩ := hgen x x.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  let eX : ↥Aa × ↥Bb ≃* ↥X := MulEquiv.ofBijective φ hφ
  have hCL : ∀ l ∈ L, l ∈ Subgroup.centralizer (fsuVM T L I : Set G) ↔
      l ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    intro l hl
    refine ⟨fun h => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V) h, fun h => ?_⟩
    rw [hVeq]
    exact mem_centralizer_sup h (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hV2 hy) l hl).symm)
  obtain ⟨ψ₁, -⟩ := exists_autOnEquiv hLN (le_normalizer_fsuUL T L I) hCL
  let eA : ↥Aa ≃* L3.Γ :=
    ψ₁.trans (MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm
  have hCLt : ∀ m ∈ CFSG.conjugate L t, m ∈ Subgroup.centralizer (fsuVM T L I : Set G) ↔
      m ∈ Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    intro m hm
    refine ⟨fun h => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV2V) h, fun h => ?_⟩
    rw [hVeq]
    exact mem_centralizer_sup (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hV1 hy) m hm).symm) h
  have hLtW : CFSG.conjugate L t ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
    fun m hm =>
    SecA.le_normalizer_commutator hLtN Subgroup.le_normalizer hm
  obtain ⟨ψ₂, hψ₂⟩ := exists_autOnEquiv hLtN hLtW hCLt
  let e₂ : ↥(autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆)) ≃* L3.Γ :=
    (MulEquiv.ofBijective D₂.π ⟨D₂.π_injective, D₂.π_surj⟩).symm
  let ρ : ↥Bb →* L3.Γ :=
    e₂.toMonoidHom.comp (ψ₂.toMonoidHom.comp (Subgroup.inclusion inf_le_left))
  have hρinj : Function.Injective ρ :=
    e₂.injective.comp (ψ₂.injective.comp (Subgroup.inclusion_injective inf_le_left))
  have hρ : ∀ (m : G) (hm : m ∈ CFSG.conjugate L t) (hmv : m * (v : G) * m⁻¹ = v) (γ : L3.Γ),
      (D₂.π γ : MulAut ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆)) =
        conjAct (⁅fsuVM T L I, CFSG.conjugate L t⁆) ⟨m, hLtW hm⟩ →
      ρ ⟨conjAct (fsuVM T L I) ⟨m, hLtN hm⟩, SecB.mem_autOn_iff.mpr ⟨⟨m, hLtN hm⟩, hm, rfl⟩,
        (hstab m (hLtN hm)).mpr hmv⟩ = γ := by
    intro m hm hmv γ hγ
    change e₂ (ψ₂ ⟨conjAct (fsuVM T L I) ⟨m, hLtN hm⟩, _⟩) = γ
    rw [hψ₂ m hm, MulEquiv.symm_apply_eq]
    exact Subtype.ext hγ.symm
  have hrange : ρ.range = Ka := by
    ext γ
    constructor
    · rintro ⟨⟨b, hb, hbs⟩, rfl⟩
      obtain ⟨⟨m, hmN⟩, hm, rfl⟩ := SecB.mem_autOn_iff.mp hb
      have hmv := (hstab m hmN).mp hbs
      obtain ⟨γ, hγ⟩ := D₂.π_surj ⟨conjAct (⁅fsuVM T L I, CFSG.conjugate L t⁆) ⟨m, hLtW hm⟩,
        SecB.mem_autOn_iff.mpr ⟨⟨m, hLtW hm⟩, hm, rfl⟩⟩
      have h1 : ρ ⟨conjAct (fsuVM T L I) ⟨m, hmN⟩, hb, hbs⟩ = γ :=
        hρ m hm hmv γ (congrArg Subtype.val hγ)
      rw [h1, mem_Ka, ← fixes_iff_ka D₂ hsq2 hfix2 hFF2 hZc2 hcv γ]
      rw [show ((D₂.π γ : ↥(autOn (CFSG.conjugate L t) (⁅fsuVM T L I, CFSG.conjugate L t⁆))) :
        MulAut ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆)) = _ from congrArg Subtype.val hγ]
      exact Subtype.ext hmv
    · intro hγ
      obtain ⟨⟨m, hmN⟩, hm, hmγ⟩ := SecB.mem_autOn_iff.mp (D₂.π γ).2
      have hfixγ := (fixes_iff_ka D₂ hsq2 hfix2 hFF2 hZc2 hcv γ).mpr hγ
      rw [← hmγ] at hfixγ
      have hmv : m * (v : G) * m⁻¹ = v := congrArg Subtype.val hfixγ
      exact ⟨_, hρ m hm hmv γ hmγ.symm⟩
  let eB : ↥Bb ≃* ↥Ka := (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨eX.symm.trans ((MulEquiv.prodCongr eA (eB.trans kaEquiv)).trans
    (MulEquiv.prodComm))⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
