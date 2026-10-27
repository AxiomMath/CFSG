module

public import CFSG.Quasithin.Vol2.Ch12Sec7Lemmas
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem exists_mulVec_eq {F : Type} [Field F] {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F),
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Pi.single 0 1) = w := by
  by_cases ha : w 0 = 0
  · have hb : w 1 ≠ 0 := by
      intro hb
      apply hw
      funext i
      fin_cases i
      · exact ha
      · exact hb
    have hdet : (!![0, -(w 1)⁻¹; w 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      simp [Matrix.det_fin_two_of, hb]
    let M : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _
      (by rw [hdet]; exact one_ne_zero)
    refine ⟨⟨M, Subgroup.subset_closure hdet⟩, ?_⟩
    funext i
    fin_cases i
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · have hdet : (!![w 0, 0; w 1, (w 0)⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      simp [Matrix.det_fin_two_of, ha]
    let M : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _
      (by rw [hdet]; exact one_ne_zero)
    refine ⟨⟨M, Subgroup.subset_closure hdet⟩, ?_⟩
    funext i
    fin_cases i
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_or_eq_of_isNaturalSection {A V Z W : Subgroup G} {N : Subgroup ↥A} {F : Type}
    [Field F] (h : IsNaturalSection A V Z N (CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    (hZW : Z ≤ W) (hWV : W ≤ V)
    (hA : A ≤ Subgroup.normalizer (W : Set G)) : W = Z ∨ W = V := by
  obtain ⟨hAV, α, hαs, -, β, hβs, hβk, hβ⟩ := h
  have hker : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Z := by
    intro v
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  by_cases hW : ∀ w : ↥V, (w : G) ∈ W → β w = 1
  · left
    exact le_antisymm (fun x hx => (hker ⟨x, hWV hx⟩).mp (hW ⟨x, hWV hx⟩ hx)) hZW
  right
  push Not at hW
  obtain ⟨w, hwW, hw1⟩ := hW
  have hu : Multiplicative.toAdd (β w) ≠ 0 := fun h0 => hw1 h0
  have hall : ∀ y : Fin 2 → F, y ≠ 0 → ∃ x : ↥V, (x : G) ∈ W ∧
      Multiplicative.toAdd (β x) = y := by
    intro y hy
    obtain ⟨g1, hg1⟩ := exists_mulVec_eq hy
    obtain ⟨g2, hg2⟩ := exists_mulVec_eq hu
    obtain ⟨a, ha⟩ := hαs (g1 * g2⁻¹)
    have haw : (a : G) * w * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) w).mp w.2
    refine ⟨⟨_, haw⟩, (Subgroup.mem_normalizer_iff.mp (hA a.2) w).mp hwW, ?_⟩
    rw [hβ a w ⟨_, haw⟩ rfl, ha, ← hg2, ← hg1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.mulVec_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mulVec_mulVec]
    have : (((g2 : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  refine le_antisymm hWV fun v hv => ?_
  by_cases hv0 : Multiplicative.toAdd (β ⟨v, hv⟩) = 0
  · exact hZW ((hker ⟨v, hv⟩).mp hv0)
  · obtain ⟨x, hxW, hx⟩ := hall _ hv0
    have hk : β (⟨v, hv⟩ * x⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Multiplicative.toAdd.injective hx.symm
    have h1 := hZW ((hker _).mp hk)
    have h2 : v = (v * (x : G)⁻¹) * x := by group
    rw [h2]
    exact W.mul_mem h1 hxW

theorem le_or_sup_eq_of_isNaturalSection {A V Z U : Subgroup G} {N : Subgroup ↥A} {F : Type}
    [Field F] (h : IsNaturalSection A V Z N (CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    (hZV : Z ≤ V) (hUV : U ≤ V)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ Z ∨ U ⊔ Z = V := by
  have hn : A ≤ Subgroup.normalizer ((U ⊔ Z : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_sup U Z ⟨hAU ha, hAZ ha⟩
  rcases eq_or_eq_of_isNaturalSection h le_sup_right (sup_le hUV hZV) hn with h1 | h1
  · exact Or.inl (h1 ▸ le_sup_left)
  · exact Or.inr h1

theorem false_of_complement {C V U Z : Subgroup G} (hV : IsIndecomposableUnder C V)
    (hUV : U ≤ V) (hZV : Z ≤ V) (hCU : C ≤ Subgroup.normalizer (U : Set G))
    (hCZ : C ≤ Subgroup.normalizer (Z : Set G)) (hUZ : U ⊓ Z = ⊥) (hsup : U ⊔ Z = V)
    (hZ1 : Z ≠ ⊥) (hZV' : Z ≠ V) : False := by
  rcases hV.2 U Z hUV hZV hCU hCZ hUZ hsup with h | h
  · apply hZV'
    rw [← hsup, h, bot_sup_eq]
  · exact hZ1 h

theorem exists_mem_mul_of_isNaturalSection [Finite G] {A V Z L₀ : Subgroup G} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 4)
    (hNS : IsNaturalSection A V Z ((Subgroup.centralizer (V : Set G)).subgroupOf A)
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    (hL₀A : L₀ ≤ A) (hperf : Group.IsPerfect ↥L₀)
    (e : ↥L₀ ⧸ CFSG.pCore 2 ↥L₀ ≃* alternatingGroup (Fin 5))
    (hL₀V : ¬ L₀ ≤ Subgroup.centralizer (V : Set G)) :
    ∀ a ∈ A, ∃ l ∈ L₀, a * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  classical
  obtain ⟨-, α, hαs, hαk, -⟩ := hNS
  set φ : ↥L₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    α.comp (Subgroup.inclusion hL₀A) with hφ
  have hker : ∀ l : ↥L₀, l ∈ φ.ker ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro l
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk,
      Subgroup.mem_subgroupOf]
    rfl
  set q : ↥L₀ →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' _) with hq
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = CFSG.pCore 2 ↥L₀ := by
    ext x
    rw [MonoidHom.mem_ker, hq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkle : φ.ker ≤ CFSG.pCore 2 ↥L₀ := by
    have hn : (φ.ker.map q).Normal := Subgroup.Normal.map inferInstance q hqs
    rcases hn.eq_bot_or_eq_top with h0 | h1
    · rw [← hqk]
      intro k hk
      rw [MonoidHom.mem_ker]
      have : q k ∈ φ.ker.map q := Subgroup.mem_map_of_mem q hk
      rw [h0, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hL₀V
      have hsup : φ.ker ⊔ q.ker = ⊤ := by
        rw [← Subgroup.comap_map_eq, h1, Subgroup.comap_top]
      have h2 : IsPGroup 2 ↥φ.range := by
        rintro ⟨_, l, rfl⟩
        have hl : l ∈ ((φ.ker ⊔ q.ker : Subgroup ↥L₀) : Set ↥L₀) := by
          rw [hsup]; exact Subgroup.mem_top l
        rw [Subgroup.normal_mul] at hl
        obtain ⟨k, hk, o, ho, rfl⟩ := hl
        rw [hqk] at ho
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥L₀) (p := 2)) ⟨o, ho⟩
        refine ⟨n, Subtype.ext ?_⟩
        have hk1 : φ k = 1 := hk
        have ho' : o ^ 2 ^ n = 1 := by
          have := congrArg Subtype.val hn
          simpa using this
        simp [map_mul, hk1, ← map_pow, ho']
      have hperfR : Group.IsPerfect ↥φ.range :=
        Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
      have hsolv : Group.IsSolvable ↥φ.range := by
        have := h2.isNilpotent
        infer_instance
      have hbot : φ.range = ⊥ := by
        by_contra hne
        have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        exact Group.IsPerfect.not_isSolvable ↥φ.range hsolv
      intro l hl
      have h1l : φ ⟨l, hl⟩ = 1 := by
        have : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      exact (hker ⟨l, hl⟩).mp h1l
  have hcardA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hL₀card : Nat.card ↥L₀ = Nat.card ↥(CFSG.pCore 2 ↥L₀) * 60 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L₀),
      Nat.card_congr e.toEquiv, hcardA5, mul_comm]
  have hrange : Nat.card ↥L₀ = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have hdvd : Nat.card ↥φ.ker ∣ Nat.card ↥(CFSG.pCore 2 ↥L₀) := Subgroup.card_dvd_of_le hkle
  have hSL : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) = 60 := by
    rw [card_statedSL_two1527d, hF]
    norm_num
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    rw [hSL]
    obtain ⟨c, hc⟩ := hdvd
    have hpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    have e1 : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥φ.ker * (c * 60) := by
      rw [← hrange, hL₀card, hc]; ring
    have e2 := Nat.eq_of_mul_eq_mul_left hpos e1
    rw [e2]
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (Nat.card_pos (α := ↥(CFSG.pCore 2 ↥L₀))).ne' (by simpa using hc)
    omega
  intro a ha
  obtain ⟨l, hl⟩ : ∃ l : ↥L₀, φ l = α ⟨a, ha⟩ := by
    have : α ⟨a, ha⟩ ∈ φ.range := by rw [htop]; exact Subgroup.mem_top _
    exact this
  refine ⟨l, l.2, ?_⟩
  have hk : (⟨a, ha⟩ * Subgroup.inclusion hL₀A l⁻¹ : ↥A) ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, ← hl]
    simp [hφ]
  rw [hαk, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem XOf_le (L : Subgroup G) : XOf L ≤ L :=
  (oTwoUpper_le _).trans (Subgroup.map_subtype_le _)

variable [Finite G] {T L V : Subgroup G}

theorem le_normalizer_V (h : Hyp1271 G T L V) : L ≤ Subgroup.normalizer (V : Set G) :=
  h.hyp.irrPlus.2.2.1

theorem le_centralizer_Vt (h71 : Setup1271) (h : Hyp1271 G T L V) {t : G} (ht : t ∈ V) :
    L ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer (Vt L t : Set G) := by
  intro l hl
  obtain ⟨hlL, hlt⟩ := Subgroup.mem_inf.mp hl
  obtain ⟨-, -, -, -, hXL, -⟩ := h71 G T L V h
  have hLN := le_normalizer_V h
  have hlz : ∀ z ∈ Subgroup.zpowers t, l * z * l⁻¹ = z := by
    rintro _ ⟨k, rfl⟩
    have hc : Commute l t := Subgroup.mem_centralizer_singleton_iff.mp hlt
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hgen : Vt L t ≤ Subgroup.centralizer ({l} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, z, hz, rfl⟩
    have hzV : z ∈ V := (Subgroup.zpowers_le_of_mem ht) hz
    have hxN := hLN (XOf_le L hx)
    have hlN := hLN hlL
    have hφ : conjAct V ⟨x, hxN⟩ ∈ autOn (XOf L) V :=
      ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hψ : conjAct V ⟨l, hlN⟩ ∈ autOn L V :=
      ⟨⟨l, hlN⟩, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (hXL hφ) _ hψ
    have e := congrArg (fun φ : MulAut ↥V => ((φ ⟨z, hzV⟩ : ↥V) : G)) hcomm
    simp only [MulAut.mul_apply] at e
    change l * (x * z * x⁻¹) * l⁻¹ = x * (l * z * l⁻¹) * x⁻¹ at e
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [hlz z hz] at e
    calc x * z * x⁻¹ * l = l * (x * z * x⁻¹) * l⁻¹ * l := by rw [e]
      _ = l * (x * z * x⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hgen hw)


theorem inf_eq_bot_of_sup_eq_of_card {V U Z : Subgroup G}
    (hc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hUV : U ≤ V) (hZV : Z ≤ V) (hsup : U ⊔ Z = V)
    (hcard : Nat.card ↥U * Nat.card ↥Z = Nat.card ↥V) : U ⊓ Z = ⊥ := by
  let W : Subgroup G :=
    { carrier := {g | ∃ u ∈ U, ∃ z ∈ Z, u * z = g}
      mul_mem' := by
        rintro _ _ ⟨u, hu, z, hz, rfl⟩ ⟨u', hu', z', hz', rfl⟩
        refine ⟨u * u', U.mul_mem hu hu', z * z', Z.mul_mem hz hz', ?_⟩
        have hzu : z * u' = u' * z := hc z (hZV hz) u' (hUV hu')
        calc u * u' * (z * z') = u * (u' * z) * z' := by group
          _ = u * (z * u') * z' := by rw [hzu]
          _ = u * z * (u' * z') := by group
      one_mem' := ⟨1, U.one_mem, 1, Z.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨u, hu, z, hz, rfl⟩
        refine ⟨u⁻¹, U.inv_mem hu, z⁻¹, Z.inv_mem hz, ?_⟩
        rw [mul_inv_rev]
        exact (hc z⁻¹ (hZV (Z.inv_mem hz)) u⁻¹ (hUV (U.inv_mem hu))).symm }
  have hVW : V ≤ W := by
    rw [← hsup]
    exact sup_le (fun u hu => ⟨u, hu, 1, Z.one_mem, mul_one u⟩)
      (fun z hz => ⟨1, U.one_mem, z, hz, one_mul z⟩)
  let ψ : ↥U × ↥Z → ↥V := fun p => ⟨p.1 * p.2, V.mul_mem (hUV p.1.2) (hZV p.2.2)⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨v, hv⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := hVW hv
    exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
  have hψb := hψs.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨hgU, hgZ⟩ := Subgroup.mem_inf.mp hg
  have h1 : ψ (⟨g, hgU⟩, ⟨g⁻¹, Z.inv_mem hgZ⟩) = ψ (1, 1) :=
    Subtype.ext (by simp [ψ])
  have h2 := congrArg (fun p : ↥U × ↥Z => ((p.1 : ↥U) : G)) (hψb.1 h1)
  simp only at h2
  rw [Subgroup.mem_bot]
  exact h2

section Setting


abbrev Lt (L : Subgroup G) (t : G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))

structure D127 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G) : Prop where
  hyp : Hyp1271 G T L V
  mem : t ∈ V
  ne_one : t ≠ 1
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  vt_le : Vt L t ≤ V
  mem_vt : t ∈ Vt L t
  card_V : Nat.card ↥V = 2 ^ 6
  card_Vt : Nat.card ↥(Vt L t) = 4
  lt_le : Lt L t ≤ L ⊓ Subgroup.centralizer (Vt L t : Set G)
  comm_eq : V = ⁅V, Lt L t⁆
  v_le_lt : V ≤ Lt L t
  theta : Lt L t = thetaOf (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
  a5 : Nonempty (↥(Lt L t) ⧸ CFSG.pCore 2 ↥(Lt L t) ≃* alternatingGroup (Fin 5))
  perfect : Group.IsPerfect ↥(Lt L t)
  nat : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    IsNaturalSection (L ⊓ Subgroup.centralizer (Vt L t : Set G)) V (Vt L t)
      ((Subgroup.centralizer (V : Set G)).subgroupOf
        (L ⊓ Subgroup.centralizer (Vt L t : Set G)))
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F)
  indec : IsIndecomposableUnder (L ⊓ Subgroup.centralizer (Vt L t : Set G)) V
  cover : ∀ a ∈ L ⊓ Subgroup.centralizer (Vt L t : Set G), ∃ l ∈ Lt L t,
    a * l⁻¹ ∈ Subgroup.centralizer (V : Set G)


theorem d127_of (h71 : Setup1271) (h74 : Lemma12_7_4) (h : Hyp1271 G T L V) {t : G}
    (ht : t ∈ V) (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    D127 G T L V t := by
  obtain ⟨hVab, hV64, -, -, -, -⟩ := h71 G T L V h
  obtain ⟨⟨F, hFf, hFfin, hF4, -, hNS⟩, hind, ⟨hcomm, hVLt, htheta, ha5, hperf⟩, -, -⟩ :=
    (h74 G T L V h).2 t ht h18
  have hLN := le_normalizer_V h
  have hcV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have ht1 : t ≠ 1 := by
    rintro rfl
    have htop : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop, Subgroup.relIndex_top_left] at h18
    norm_num at h18
  have hVtV : Vt L t ≤ V := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hLN (XOf_le L hx)) z).mp
      ((Subgroup.zpowers_le_of_mem ht) hz)
  have htVt : t ∈ Vt L t :=
    Subgroup.subset_closure ⟨1, (XOf L).one_mem, t, Subgroup.mem_zpowers t, by group⟩
  have hcardVt : Nat.card ↥(Vt L t) = 4 := by
    obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := hNS
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVtV).toEquiv, hV64] at h1
    have h16 : Nat.card (Multiplicative (Fin 2 → F)) = 16 := by
      rw [show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl,
        Nat.card_fun, hF4, Nat.card_fin]
      norm_num
    rw [h16] at h1
    omega
  have hLt : Lt L t ≤ L ⊓ Subgroup.centralizer (Vt L t : Set G) :=
    fun l hl => ⟨(oTwoUpper_le _ hl).1, le_centralizer_Vt h71 h ht (oTwoUpper_le _ hl)⟩
  have hLtV : ¬ Lt L t ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have hb : ⁅V, Lt L t⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle
    exact h.hyp.irrPlus.2.1 (hcomm.trans hb)
  obtain ⟨e⟩ := ha5
  exact
    { hyp := h
      mem := ht
      ne_one := ht1
      comm := hcV
      vt_le := hVtV
      mem_vt := htVt
      card_V := hV64
      card_Vt := hcardVt
      lt_le := hLt
      comm_eq := hcomm
      v_le_lt := hVLt
      theta := htheta
      a5 := ⟨e⟩
      perfect := hperf
      nat := ⟨F, hFf, hFfin, hF4, hNS⟩
      indec := hind
      cover := exists_mem_mul_of_isNaturalSection hF4 hNS hLt hperf e hLtV }

namespace D127

variable {t : G} (d : D127 G T L V t)
include d

theorem le_normalizer_of {U : Subgroup G} (hUV : U ≤ V)
    (hU : Lt L t ≤ Subgroup.normalizer (U : Set G)) :
    L ⊓ Subgroup.centralizer (Vt L t : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  intro a ha
  obtain ⟨l, hl, hc⟩ := d.cover a ha
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  have hlu : l * u * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hU hl) u).mp hu
  have h2 : (a * l⁻¹) * (l * u * l⁻¹) * (a * l⁻¹)⁻¹ = l * u * l⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hc _ (hUV hlu)
    rw [← this, mul_inv_cancel_right]
  have h3 : a * u * a⁻¹ = (a * l⁻¹) * (l * u * l⁻¹) * (a * l⁻¹)⁻¹ := by group
  rw [h3, h2]
  exact hlu

omit d in
theorem le_normalizer_Vt :
    L ⊓ Subgroup.centralizer (Vt L t : Set G) ≤ Subgroup.normalizer (Vt L t : Set G) :=
  fun a ha => Subgroup.mem_normalizer_fintype fun v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm, mul_inv_cancel_right]
    exact hv

theorem le_or_sup_eq {U : Subgroup G} (hUV : U ≤ V)
    (hU : Lt L t ≤ Subgroup.normalizer (U : Set G)) : U ≤ Vt L t ∨ U ⊔ Vt L t = V := by
  obtain ⟨F, _, _, -, hNS⟩ := d.nat
  exact le_or_sup_eq_of_isNaturalSection hNS d.vt_le hUV le_normalizer_Vt
    (d.le_normalizer_of hUV hU)

theorem false_of_complement' {U : Subgroup G} (hUV : U ≤ V)
    (hU : Lt L t ≤ Subgroup.normalizer (U : Set G)) (hUZ : U ⊓ Vt L t = ⊥)
    (hsup : U ⊔ Vt L t = V) : False := by
  refine false_of_complement d.indec hUV d.vt_le (d.le_normalizer_of hUV hU) le_normalizer_Vt
    hUZ hsup ?_ ?_
  · intro h0
    exact d.ne_one ((Subgroup.mem_bot).mp (h0 ▸ d.mem_vt))
  · intro hVt
    have := d.card_Vt
    rw [hVt, d.card_V] at this
    norm_num at this

theorem false_of_card_sixteen {U : Subgroup G} (hUV : U ≤ V)
    (hU : Lt L t ≤ Subgroup.normalizer (U : Set G)) (hcard : Nat.card ↥U = 16) : False := by
  rcases d.le_or_sup_eq hUV hU with hle | hsup
  · have := Subgroup.card_le_of_le hle
    rw [hcard, d.card_Vt] at this
    norm_num at this
  · refine d.false_of_complement' hUV hU ?_ hsup
    refine inf_eq_bot_of_sup_eq_of_card d.comm hUV d.vt_le hsup ?_
    rw [hcard, d.card_Vt, d.card_V]
    norm_num

end D127


end Setting


end CFSG.Quasithin.H13.S127.L5
