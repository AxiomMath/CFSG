module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ElemAb

theorem ncard_fix_le_two {W : Type*} [Group W] [Finite W] {Z Y : Subgroup W}
    (hZ : Nat.card Z ≤ 2) {w₀ : W} (hw₀ : ∀ w, w ∈ Y ∨ w₀⁻¹ * w ∈ Y) {R : Set (MulAut W)}
    (hR : ∀ α ∈ R, α w₀ * w₀⁻¹ ∈ Z) (hRY : ∀ α ∈ R, ∀ y ∈ Y, α y = y) : R.ncard ≤ 2 := by
  rw [← Nat.card_coe_set_eq]
  refine le_trans (Nat.card_le_card_of_injective (fun α : R => (⟨α.1 w₀ * w₀⁻¹, hR α.1 α.2⟩ : Z))
    fun α β hαβ => ?_) hZ
  have h0 : α.1 w₀ = β.1 w₀ := by
    have := congrArg Subtype.val hαβ
    simpa using this
  refine Subtype.ext (MulEquiv.ext fun w => ?_)
  rcases hw₀ w with hw | hw
  · rw [hRY _ α.2 w hw, hRY _ β.2 w hw]
  · calc α.1 w = α.1 (w₀ * (w₀⁻¹ * w)) := by rw [mul_inv_cancel_left]
      _ = α.1 w₀ * α.1 (w₀⁻¹ * w) := map_mul _ _ _
      _ = β.1 w₀ * β.1 (w₀⁻¹ * w) := by rw [h0, hRY _ α.2 _ hw, hRY _ β.2 _ hw]
      _ = β.1 (w₀ * (w₀⁻¹ * w)) := (map_mul _ _ _).symm
      _ = β.1 w := by rw [mul_inv_cancel_left]

end CFSG.Quasithin.ElemAb

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem card_Hs
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V)
    (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) : Nat.card ↥(Hs T L V z) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : ∀ w : ↥(Ut T L V z), w ^ 2 = 1 := fun w =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : ↥(Ut T L V z) => mul_comm a b) hW hd
  rw [(s.Hs_eq_top h1222 h37 h38 h39 hU).1, Subgroup.card_top,
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv, Matrix.card_GL_field,
    ZMod.card]
  simp [Fin.prod_univ_three]

theorem card_V_inf_cTil
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V)
    (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) :
    Nat.card ↥(V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) = 16 := by
  set W := V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hWdef
  have hV64 : Nat.card ↥V = 64 := (S127.card_eq_of_1222 h1222 s.setting.hyp).2.1
  have hker : (s.phiV h1222).ker = W.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, s.mem_ker_phiV h1222, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s.phiV h1222).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (s.phiV h1222)).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ V)).toEquiv] at h1
  have hdvd : Nat.card ↥(s.phiV h1222).range ∣ 168 := by
    rw [← s.card_Hs h1222 h37 h38 h39 hU hd]
    have hle : (s.phiV h1222).range ≤ Hs T L V z := by
      rintro _ ⟨v, rfl⟩
      exact s.phiV_mem_Hs h1222 v
    exact Subgroup.card_dvd_of_le hle
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  rcases s.card_V_cTil h1222 with h2 | h2
  · rw [← hWdef] at h2
    omega
  · exfalso
    rw [← hWdef] at h2
    rw [h2] at h1
    have h16 : Nat.card ↥(s.phiV h1222).range = 16 := Nat.eq_of_mul_eq_mul_right hWpos h1.symm
    rw [h16] at hdvd
    norm_num at hdvd

@[expose] noncomputable def psiH
    (h1222 : Stmt12_2_2) : ↥(H714 T L V z) →* MulAut ↥(U714 T L V z) :=
  (conjAct (U714 T L V z)).comp (Subgroup.inclusion (s.H_le_normalizer_U h1222))

theorem psiH_apply
    (h1222 : Stmt12_2_2) (h : ↥(H714 T L V z)) (u : ↥(U714 T L V z)) :
    ((s.psiH h1222 h u : ↥(U714 T L V z)) : G) = (h : G) * u * (h : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ u

theorem eight_le_card_map_cTil
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V)
    (hd : Nat.card ↥(Ut T L V z) = 2 ^ 3) :
    8 ≤ Nat.card ↥(((cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)).subgroupOf
      (H714 T L V z)).map (s.psiH h1222)) := by
  classical
  have h := s.setting.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨hHs, -⟩ := s.Hs_eq_top h1222 h37 h38 h39 hU
  set cT := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hcT
  set H := H714 T L V z with hH
  set U := U714 T L V z with hUdef
  have hcTH : cT ≤ H := fun x hx => hx.1
  have hVH : V ≤ H := V_le_H714 T L V z
  have hsq := s.sq_eq_one_U h1222 h37 h38 h39 hU
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hsq x hx)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
    have := hinv (a * b) (Subgroup.mul_mem _ ha hb)
    rw [mul_inv_rev, hinv a ha, hinv b hb] at this
    exact this.symm
  have hV1U : V1 T L V ≤ U := le_conjClosure _ _
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hzU : z ∈ U := s.z_mem_U
  have hV14 : Nat.card ↥(V1 T L V) = 4 := (S127.Mod.lemma12_7_2_two h1222 h).1.2
  set R := (cT.subgroupOf H).map (s.psiH h1222) with hR
  have hRz : ∀ α ∈ R, ∀ u : ↥U, ((α u * u⁻¹ : ↥U) : G) ∈ Subgroup.zpowers z := by
    rintro _ ⟨c, hc, rfl⟩ u
    rw [Subgroup.coe_mul, Subgroup.coe_inv, s.psiH_apply]
    exact hc.2 u u.2
  set A := ((V ⊓ cT).subgroupOf H).map (s.psiH h1222) with hA
  have hAR : A ≤ R := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2
  have hAfix : ∀ α ∈ A, ∀ v ∈ V1 T L V, ∀ hv : v ∈ U, α ⟨v, hv⟩ = ⟨v, hv⟩ := by
    rintro _ ⟨c, hc, rfl⟩ v hv1 hv
    apply Subtype.ext
    rw [s.psiH_apply]
    have hcv : (c : G) * v = v * c := congrArg Subtype.val
      (hcomm.is_comm.comm ⟨c, hc.1⟩ ⟨v, hV1V hv1⟩)
    show (c : G) * v * (c : G)⁻¹ = v
    rw [hcv, mul_inv_cancel_right]
  have hA4 : 4 ≤ Nat.card ↥A := by
    have hE := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((s.psiH h1222).comp ((V ⊓ cT).subgroupOf H).subtype).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans hVH : V ⊓ cT ≤ H)).toEquiv,
      s.card_V_inf_cTil h1222 h37 h38 h39 hU hd] at hE
    have hker : Nat.card ↥((s.psiH h1222).comp ((V ⊓ cT).subgroupOf H).subtype).ker ≤ 4 := by
      rw [← hV14]
      refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥((V ⊓ cT).subgroupOf H)) : G),
        ?_⟩ : ↥(V1 T L V))) fun a b hab => Subtype.ext (Subtype.ext (Subtype.ext
          (by simpa using congrArg Subtype.val hab)))
      have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have hkV : ((k : ↥((V ⊓ cT).subgroupOf H)) : G) ∈ V :=
        (Subgroup.mem_subgroupOf.mp (k : ↥((V ⊓ cT).subgroupOf H)).2).1
      obtain ⟨-, -, -, -, -, hV1eq⟩ := S127.Mod.lemma12_7_2_two h1222 h
      rw [← hV1eq]
      refine ⟨hkV, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hRN : R1 T L V ≤ Subgroup.normalizer (V : Set G) :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (s.P1_le_normalizer_V h1222)
      have hmem : conjAct V ⟨r, hRN hr⟩ ∈ autOn U V := by
        rw [hU]
        exact S127.Mod.conjAct_mem_autOn hr (hRN hr)
      obtain ⟨u, huN, huU, hur⟩ := S127.Mod.mem_autOn'.1 hmem
      have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨_, hkV⟩ : ↥V) : G)) hur
      simp only [S127.Mod.conjAct_val] at h1
      have h2 : ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * u *
          ((k : ↥((V ⊓ cT).subgroupOf H)) : G)⁻¹ = u := by
        have h2' := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, huU⟩ : ↥U) : G)) hk
        simp only [MonoidHom.comp_apply, MulAut.one_apply] at h2'
        rw [s.psiH_apply] at h2'
        exact h2'
      have hku : ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * u = u *
          ((k : ↥((V ⊓ cT).subgroupOf H)) : G) := by
        calc ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * u =
            ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * u *
              ((k : ↥((V ⊓ cT).subgroupOf H)) : G)⁻¹ *
              ((k : ↥((V ⊓ cT).subgroupOf H)) : G) := by group
          _ = u * ((k : ↥((V ⊓ cT).subgroupOf H)) : G) := by rw [h2]
      calc r * ((k : ↥((V ⊓ cT).subgroupOf H)) : G) =
          r * ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * r⁻¹ * r := by group
        _ = u * ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * u⁻¹ * r := by rw [h1]
        _ = ((k : ↥((V ⊓ cT).subgroupOf H)) : G) * r := by rw [← hku, mul_inv_cancel_right]
    have hpos : 0 < Nat.card ↥((s.psiH h1222).comp ((V ⊓ cT).subgroupOf H).subtype).ker :=
      Nat.card_pos
    have : 16 ≤ Nat.card ↥A * 4 := by
      rw [hE]
      exact Nat.mul_le_mul_left _ hker
    omega
  obtain ⟨v₁, hv₁V1, hv₁z⟩ : ∃ v₁ ∈ V1 T L V, v₁ ∉ Subgroup.zpowers z := by
    by_contra hno
    push Not at hno
    have hle : V1 T L V ≤ Subgroup.zpowers z := fun v hv => hno v hv
    have := Subgroup.card_le_of_le hle
    rw [hV14, Nat.card_zpowers, s.orderOf_z] at this
    omega
  have hv₁U : v₁ ∈ U := hV1U hv₁V1
  have hv₁N : v₁ ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := s.U_le_N h1222 hv₁U
  set w₁ : ↥(Ut T L V z) := s.piU h1222 ⟨v₁, hv₁U⟩ with hw₁
  have hw₁1 : w₁ ≠ 1 := by
    rw [hw₁, Ne, s.piU_eq_one_iff]
    rintro (h1 | h1)
    · exact hv₁z (by rw [show v₁ = 1 from congrArg Subtype.val h1]; exact Subgroup.one_mem _)
    · exact hv₁z (by rw [show v₁ = z from congrArg Subtype.val h1]; exact Subgroup.mem_zpowers z)
  have hW : ∀ w : ↥(Ut T L V z), w ^ 2 = 1 := fun w =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : ↥(Ut T L V z), w₂ ∉ X1 T L V z := by
    by_contra hno
    push Not at hno
    have hle : (⊤ : Subgroup ↥(Ut T L V z)) ≤ X1 T L V z := fun w _ => hno w
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, hd, s.card_X1 h1222] at this
    norm_num at this
  have hw₂1 : w₂ ≠ 1 := fun h1 => hw₂ (h1 ▸ Subgroup.one_mem _)
  obtain ⟨φ, hφ⟩ := ElemAb.exists_mulAut_apply_eq hW hw₁1 hw₂1
  have hφr : φ ∈ (s.rho h1222).range := by
    rw [s.range_rho h1222, hHs]
    exact Subgroup.mem_top φ
  obtain ⟨h₀, rfl⟩ := hφr
  have hconjU : (h₀ : G) * v₁ * (h₀ : G)⁻¹ ∈ U := (s.psiH h1222 h₀ ⟨v₁, hv₁U⟩).2
  have hmov : (h₀ : G) * v₁ * (h₀ : G)⁻¹ ∉ V1 T L V := by
    intro hmem
    apply hw₂
    rw [← hφ, Subgroup.mem_subgroupOf, s.rho_apply, hw₁, s.piU_coe]
    have e : tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h₀) *
        tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.U_le_N h1222) ⟨v₁, hv₁U⟩) *
        (tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h₀))⁻¹ =
        tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h₀ *
          Subgroup.inclusion (s.U_le_N h1222) ⟨v₁, hv₁U⟩ *
          (Subgroup.inclusion (s.H_le_N h1222) h₀)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact secMk_mem_secImg hmem
  set B := A.map (MulAut.conj (s.psiH h1222 h₀)).toMonoidHom with hB
  have hBR : B ≤ R := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hα
    have hcT' : (c : G) ∈ cT := (Subgroup.mem_subgroupOf.mp hc).2
    refine ⟨h₀ * c * h₀⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ h₀.2) _).mp hcT'
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hB4 : 4 ≤ Nat.card ↥B := by
    rw [hB, Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hA4
  have hBfix : ∀ β ∈ B, ∀ v ∈ V1 T L V, ∀ hv : (h₀ : G) * v * (h₀ : G)⁻¹ ∈ U,
      β ⟨_, hv⟩ = ⟨_, hv⟩ := by
    rintro _ ⟨α, hα, rfl⟩ v hv1 hv
    have hvU : v ∈ U := hV1U hv1
    have e : (⟨(h₀ : G) * v * (h₀ : G)⁻¹, hv⟩ : ↥U) = s.psiH h1222 h₀ ⟨v, hvU⟩ :=
      Subtype.ext (s.psiH_apply h1222 h₀ ⟨v, hvU⟩).symm
    rw [e]
    show (s.psiH h1222 h₀ * α * (s.psiH h1222 h₀)⁻¹) (s.psiH h1222 h₀ ⟨v, hvU⟩) = _
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hAfix α hα v hv1 hvU]
  have hBA : ¬ B ≤ A := by
    intro hle
    set Y : Subgroup ↥U := (V1 T L V).subgroupOf U ⊔ ((V1 T L V).map
      (MulAut.conj (h₀ : G)).toMonoidHom).subgroupOf U with hY
    have hYfix : ∀ β ∈ B, ∀ y ∈ Y, β y = y := by
      intro β hβ
      have hβA := hle hβ
      have hYle : Y ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) := by
        refine sup_le (fun x hx => hAfix β hβA x hx x.2) ?_
        intro x hx
        obtain ⟨v, hv, hvx⟩ := Subgroup.mem_subgroupOf.mp hx
        have hvx' : (h₀ : G) * v * (h₀ : G)⁻¹ = (x : G) := hvx
        have hmemU : (h₀ : G) * v * (h₀ : G)⁻¹ ∈ U := hvx' ▸ x.2
        have e : x = ⟨_, hmemU⟩ := Subtype.ext hvx'.symm
        show β x = x
        rw [e]
        exact hBfix β hβ v hv _
      exact fun y hy => hYle hy
    have hU16 : Nat.card ↥U = 16 := by
      rw [hUdef, s.card_U h1222, hd]
      norm_num
    have hV1Y : (V1 T L V).subgroupOf U ≤ Y := le_sup_left
    have hY8 : 8 ≤ Nat.card ↥Y := by
      have hlt : (V1 T L V).subgroupOf U < Y := by
        refine lt_of_le_of_ne hV1Y fun heq => hmov ?_
        have hmem : (⟨(h₀ : G) * v₁ * (h₀ : G)⁻¹, hconjU⟩ : ↥U) ∈ Y :=
          Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ⟨v₁, hv₁V1, rfl⟩)
        rw [← heq, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      have h1 := Subgroup.card_dvd_of_le hlt.le
      have h2 := Subgroup.card_lt_of_lt hlt
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1U).toEquiv, hV14] at h1 h2
      obtain ⟨k, hk⟩ := h1
      rcases k with _ | _ | k
      · simp at hk; omega
      · omega
      · rw [hk]; nlinarith
    have hYtop : Y ≠ ⊤ := by
      intro htop
      have hB1 : ∀ β ∈ B, β = 1 := fun β hβ =>
        MulEquiv.ext fun y => hYfix β hβ y (htop ▸ Subgroup.mem_top y)
      have : B ≤ ⊥ := fun β hβ => (Subgroup.mem_bot).mpr (hB1 β hβ)
      have := Subgroup.card_le_of_le this
      rw [Subgroup.card_bot] at this
      omega
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥U, w₀ ∉ Y := by
      by_contra hno
      push Not at hno
      exact hYtop (eq_top_iff.mpr fun w _ => hno w)
    have hdich : ∀ w : ↥U, w ∈ Y ∨ w₀⁻¹ * w ∈ Y := by
      intro w
      by_cases hw : w ∈ Y
      · exact Or.inl hw
      · right
        refine mul_mem_of_card_le (G := ↥U) (A := ⊤) (W := Y) ?_ w₀ (Subgroup.mem_top _) w
          (Subgroup.mem_top _) hw₀ hw
        rw [top_inf_eq, Subgroup.card_top, hU16]
        omega
    have hZ : Nat.card ↥((Subgroup.zpowers z).subgroupOf U) ≤ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le_of_mem hzU)).toEquiv,
        Nat.card_zpowers, s.orderOf_z]
    have hcard := ElemAb.ncard_fix_le_two hZ hdich (R := (B : Set (MulAut ↥U)))
      (fun β hβ => by
        rw [Subgroup.mem_subgroupOf]
        exact hRz β (hBR hβ) w₀)
      (fun β hβ y hy => hYfix β hβ y hy)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at hcard
    have : Nat.card ↥B ≤ 2 := hcard
    omega
  have hlt : A < A ⊔ B := lt_of_le_of_ne le_sup_left fun heq => hBA (heq ▸ le_sup_right)
  have h1 := Subgroup.card_dvd_of_le hlt.le
  have h2 := Subgroup.card_lt_of_lt hlt
  have h3 : 2 * Nat.card ↥A ≤ Nat.card ↥(A ⊔ B) := by
    obtain ⟨k, hk⟩ := h1
    rcases k with _ | _ | k
    · simp at hk; omega
    · omega
    · rw [hk]; nlinarith
  have h4 := Subgroup.card_le_of_le (sup_le hAR hBR)
  omega

end CFSG.Quasithin.H13.S127.L715.Set714
