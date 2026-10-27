module

public import CFSG.Quasithin.Vol2.Ch12Sec5L8
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125Ir Matrix
open CFSG.LieType.SteinbergBR.BlockPar
open scoped IsMulCommutative

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125L4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem autOn_l6 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (li L F.V6) V = (S125Gen.pL 4 1 rfl).map (psi F) := by
  have hf := S125Ex.Facts125.of h1222 hH
  show autOn (li L (F.sub {0, 1, 2, 4, 5, 7})) V = _
  rw [lbar_eq F hf.normalizes hf.T_le (S := {0, 1, 2, 4, 5, 7}) (rfl : 4 + 1 = 5)
    (isStab_V6 F hf.normalizes hf.T_le)
    (S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ41), S125Gen.pL,
    Subgroup.map_map]
  rfl

theorem autOn_l3 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (li L F.V3) V = (S125Gen.pL 3 2 rfl).map (psi F) := by
  have hf := S125Ex.Facts125.of h1222 hH
  show autOn (li L (F.sub {0, 1, 4})) V = _
  rw [lbar_eq F hf.normalizes hf.T_le (S := {0, 1, 4}) (rfl : 3 + 2 = 5)
    (isStab_V3 F hf.normalizes hf.T_le)
    (S125L2G.hres_of parJL_le_parQ S125Pb.perfectResidual_parQ32), S125Gen.pL,
    Subgroup.map_map]
  rfl

omit [Finite G] in
theorem map_top_psi (F : Frame125 T L V) : (⊤ : Subgroup SL5).map (psi F) = autOn L V := by
  ext a
  constructor
  · rintro ⟨g, -, rfl⟩
    exact (F.γ.symm g).2
  · intro ha
    exact ⟨F.γ ⟨a, ha⟩, Subgroup.mem_top _, by simp [psi]⟩

theorem autOn_sup_l6 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (li L F.V1) V ⊔ autOn (li L F.V6) V = autOn L V := by
  rw [S125L8.autOn_l1 h1222 F hH, autOn_l6 h1222 F hH, ← Subgroup.map_sup,
    S125Gen.pR_sup_pL41, map_top_psi]

theorem autOn_sup_l3 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    autOn (li L F.V1) V ⊔ autOn (li L F.V3) V = autOn L V := by
  rw [S125L8.autOn_l1 h1222 F hH, autOn_l3 h1222 F hH, ← Subgroup.map_sup,
    S125Gen.pR_sup_pL32, map_top_psi]

@[expose] def conjSpan (A B : Subgroup G) : Subgroup G :=
  ⨆ b ∈ B, A.map (MulAut.conj b).toMonoidHom

omit [Finite G] in
theorem map_conj_map_conj (A : Subgroup G) (b g : G) :
    (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem map_conjSpan_le {A B : Subgroup G} {g : G}
    (h : ∀ b ∈ B, ∃ b' ∈ B, A.map (MulAut.conj (g * b)).toMonoidHom =
      A.map (MulAut.conj b').toMonoidHom) :
    (conjSpan A B).map (MulAut.conj g).toMonoidHom ≤ conjSpan A B := by
  rw [conjSpan, Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  obtain ⟨b', hb', he⟩ := h b hb
  rw [map_conj_map_conj, he]
  exact le_iSup₂_of_le b' hb' le_rfl

theorem mem_normalizer_conjSpan {A B : Subgroup G} {g : G}
    (h : ∀ b ∈ B, ∃ b' ∈ B, A.map (MulAut.conj (g * b)).toMonoidHom =
      A.map (MulAut.conj b').toMonoidHom) :
    g ∈ Subgroup.normalizer (conjSpan A B : Set G) := by
  apply S125St.mem_normalizer_of_conj_le
  intro x hx
  exact map_conjSpan_le h ⟨x, hx, rfl⟩

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this

theorem le_normalizer_L (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {Li : Subgroup G} (hLiL : Li ≤ L) (hTLi : T ≤ Subgroup.normalizer (Li : Set G))
    (hsup : autOn (li L F.V1) V ⊔ autOn Li V = autOn L V) {C : Subgroup G}
    (hC : ∀ c ∈ C, ∀ b ∈ Li, b⁻¹ * c * b ∈ C)
    (hCL₁ : C ≤ Subgroup.normalizer (li L F.V1 : Set G)) :
    C ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  set L₁ := li L F.V1 with hL₁
  set X := conjSpan L₁ Li with hX
  have hL₁L : L₁ ≤ L := S125K6.li_le L _
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := S125K1.T_le_normalizer_l1 h1222 F hH
  have hXL : X ≤ L := by
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem (hLiL hb) (hL₁L hx)) (L.inv_mem (hLiL hb))
  have hL₁X : L₁ ≤ X := by
    refine le_iSup₂_of_le 1 Li.one_mem ?_
    rw [map_conj_eq_of_mem_normalizer (Subgroup.one_mem _)]
  have hLiN : Li ≤ Subgroup.normalizer (X : Set G) := fun b₀ hb₀ =>
    mem_normalizer_conjSpan fun b hb => ⟨b₀ * b, Li.mul_mem hb₀ hb, rfl⟩
  have hTN : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    mem_normalizer_conjSpan fun b hb => by
      refine ⟨t * b * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTLi ht) b).mp hb, ?_⟩
      have e : t * b = t * b * t⁻¹ * t := by group
      conv_lhs => rw [e]
      rw [← map_conj_map_conj, map_conj_eq_of_mem_normalizer (hTL₁ ht)]
  have hCN : C ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    mem_normalizer_conjSpan fun b hb => by
      refine ⟨b, hb, ?_⟩
      have e : c * b = b * (b⁻¹ * c * b) := by group
      conv_lhs => rw [e]
      rw [← map_conj_map_conj, map_conj_eq_of_mem_normalizer (hCL₁ (hC c hc b hb))]
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := hXL.trans hf.normalizes
  have hNa : autOn L V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V)) := by
    rw [← hsup]
    exact sup_le (autOn_le_normalizer_autOn hXV (hL₁L.trans hf.normalizes)
        (hL₁X.trans Subgroup.le_normalizer))
      (autOn_le_normalizer_autOn hXV (hLiL.trans hf.normalizes) hLiN)
  have hXa : autOn X V ≤ autOn L V := A4.autOn_mono hXL
  obtain ⟨eL⟩ := S125Ex.lbar_equiv hH hf
  have hsimp : IsSimpleGroup ↥(autOn L V) := by
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact eL.isSimpleGroup
  have hnorm : ((autOn X V).subgroupOf (autOn L V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXa).mpr hNa
  have hLa : autOn L V ≤ autOn X V := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autOn X V).subgroupOf (autOn L V)) with
      h | h
    · exfalso
      have hne : S125Gen.tv 0 2 (by decide) ≠ 1 := by
        intro h1
        have := congrArg (fun g : SL5 => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2) h1
        simp [S125Gen.tv, Matrix.transvection] at this
      have hmem : psi F (S125Gen.tv 0 2 (by decide)) ∈ autOn X V := by
        refine A4.autOn_mono hL₁X ?_
        rw [S125L8.autOn_l1 h1222 F hH]
        exact ⟨_, S125Gen.tv_mem_pR (by decide) (by decide), rfl⟩
      have h1 : (⟨psi F (S125Gen.tv 0 2 (by decide)), hXa hmem⟩ : ↥(autOn L V)) = 1 := by
        have : (⟨psi F (S125Gen.tv 0 2 (by decide)), hXa hmem⟩ : ↥(autOn L V)) ∈
            (autOn X V).subgroupOf (autOn L V) := hmem
        rw [h] at this
        exact (Subgroup.mem_bot).mp this
      apply hne
      apply (psi_injective F)
      rw [map_one]
      exact congrArg Subtype.val h1
    · intro a ha
      have : (⟨a, ha⟩ : ↥(autOn L V)) ∈ (autOn X V).subgroupOf (autOn L V) := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQT : Q ≤ T := by
    have hS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
    exact pCoreOf_two_le_of_isSylowTwoOf hS
  have hLXQ : L ≤ X ⊔ Q := by
    intro l hl
    obtain ⟨x, hxN, hxX, hx⟩ := mem_autOn_iff_exists.mp
      (hLa (conjAct_mem_autOn (hf.normalizes hl) hl))
    have hc : x⁻¹ * l ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨Subgroup.mem_sup_left (L.mul_mem (L.inv_mem (hXL hxX)) hl),
        Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hx
      simp only [S125ZV.coe_conjAct_apply] at h1
      calc v * (x⁻¹ * l) = x⁻¹ * (x * v * x⁻¹) * l := by group
        _ = x⁻¹ * (l * v * l⁻¹) * l := by rw [h1]
        _ = x⁻¹ * l * v := by group
    have hcQ : x⁻¹ * l ∈ Q := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        (S125Tr2.isPGroup_centralizer hH hf) hc
      intro g hg
      apply S125St.mem_normalizer_of_conj_le
      rintro y ⟨hy, hyC⟩
      have hyC' : y ∈ Subgroup.centralizer (V : Set G) := hyC
      have hgV : g ∈ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le hg
      refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hy) ((L ⊔ T).inv_mem hg),
        Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) v).mp hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hyC' _ hv'
      calc v * (g * y * g⁻¹) = g * ((g⁻¹ * v * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * v := by group
    have e : l = x * (x⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxX) (Subgroup.mem_sup_right hcQ)
  have hLperf : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.mpr hH.hyp.maximal.1.2.1.2.1
  have hO : oTwoUpper (X ⊔ Q) ≤ X :=
    L1295.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer (hQT.trans hTN)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
  have hXeq : X = L :=
    le_antisymm hXL ((CFSG.Quasithin.perfect_le_oTwoUpper hLXQ hLperf).trans hO)
  rw [← hXeq]
  exact hCN

theorem centralizer_le_of_sup (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hN : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G))
    {W : Subgroup G} (hV₁W : F.V1 ≤ W)
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hsup : autOn (li L F.V1) V ⊔ autOn (li L W) V = autOn L V) :
    Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  refine le_normalizer_L h1222 F hH (S125K6.li_le L W)
    (S125K6.le_normalizer_li hH.hyp.normalizes hTW) hsup (fun c hc b hb => ?_) ?_
  · have hbW := S125K6.li_le_normalizer L W hb
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hbW w).mp hw
    have h1 := hc _ hw'
    calc w * (b⁻¹ * c * b) = b⁻¹ * ((b * w * b⁻¹) * c) * b := by group
      _ = b⁻¹ * (c * (b * w * b⁻¹)) * b := by rw [h1]
      _ = b⁻¹ * c * b * w := by group
  · exact ((Subgroup.centralizer_le hV₁W).trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem centralizer_V3_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hN : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G)) :
    Subgroup.centralizer (F.V3 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  centralizer_le_of_sup h1222 F hH hN (S125L5a.sub_mono_le F (by decide))
    (S125L2G.T_le_V F (S125Ex.Facts125.of h1222 hH).T_le).2.1 (autOn_sup_l3 h1222 F hH)

theorem centralizer_V6_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hN : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G)) :
    Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  centralizer_le_of_sup h1222 F hH hN (S125L5a.sub_mono_le F (by decide))
    (S125L2G.T_le_V F (S125Ex.Facts125.of h1222 hH).T_le).2.2.2 (autOn_sup_l6 h1222 F hH)

theorem normalizer_V6_le
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hC : Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨hmi, -, -, hR6, ⟨hcomm, hext⟩, -⟩ := (lemma12_5_2_of h1222 G T L V F hH).2.2.2
  have hTV := S125L2G.T_le_V F hf.T_le
  have hTL₆ := S125K6.T_le_normalizer_l6 h1222 F hH
  have hL₆G₆ : li L F.V6 ≤ Subgroup.normalizer (F.V6 : Set G) := S125K6.li_le_normalizer L _
  have hL₆L : li L F.V6 ≤ L := S125K6.li_le L _
  have hV₆V : F.V6 ≤ V := Subgroup.map_subtype_le _
  have hV₁V₆ : F.V1 ≤ F.V6 := S125L5a.sub_mono_le F (by decide)
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  obtain ⟨-, hG₆N⟩ := S125K6.l6_cComp h1222 h36 h37 h38 h39 h312 F hH
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V6 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTV.2.2.2
  obtain ⟨e₆⟩ := S125K6.l6_quot_equiv h1222 F hH
  have hO₂C : pCoreOf 2 (li L F.V6) ≤ Subgroup.centralizer (F.V6 : Set G) :=
    (E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₆)).trans hR6
  have hTact : ∀ t ∈ T, ∃ l ∈ li L F.V6, ∀ v ∈ V, t * v * t⁻¹ = l * v * l⁻¹ := by
    intro t ht
    have hta : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn (li L F.V6) V := by
      rw [← hmi]
      exact conjAct_mem_autOn (hf.T_le ht) ⟨Subgroup.mem_sup_right ht, hTV.2.2.2 ht⟩
    obtain ⟨l, hlN, hlL, hl⟩ := mem_autOn_iff_exists.mp hta
    refine ⟨l, hlL, fun v hv => ?_⟩
    have := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hl
    simp only [S125ZV.coe_conjAct_apply] at this
    exact this.symm
  have hZV := frame125ZV_of h1222 G T L V F hH
  have hCVT : ∀ v ∈ V, (∀ t ∈ T, t * v * t⁻¹ = v) → v ∈ F.V1 := by
    intro v hv hvT
    rw [← hZV]
    refine ⟨hv, Subgroup.subset_closure ⟨⟨hf.le_T hv, Subgroup.mem_centralizer_iff.mpr
      fun t ht => ?_⟩, hf.sq v hv⟩⟩
    have := hvT t ht
    calc t * v = t * v * t⁻¹ * t := by group
      _ = v * t := by rw [this]
  have hcard₁ := S125L9a.card_V1 F
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ F.V1, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hb : F.V1 = ⊥ := eq_bot_iff.mpr fun v hv => (Subgroup.mem_bot).mpr (hcon v hv)
    rw [hb, Subgroup.card_bot] at hcard₁
    norm_num at hcard₁
  have hV₁eq : ∀ w ∈ F.V1, w = 1 ∨ w = z := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥F.V1)).1 hcard₁
      have h1 := hy ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h))
      have h2 := hy ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hD : ∀ d ∈ centralizerMod (pCoreOf 2 (li L F.V6)) (Subgroup.normalizer (F.V6 : Set G))
      (li L F.V6), d ∈ Subgroup.centralizer (F.V6 : Set G) := by
    rintro d ⟨hdG, -, hdc⟩
    have hdl : ∀ l ∈ li L F.V6, ∀ v ∈ F.V6, d * l * d⁻¹ * v * (d * l * d⁻¹)⁻¹ = l * v * l⁻¹ := by
      intro l hl v hv
      have hc := Subgroup.mem_centralizer_iff.mp (hO₂C (hdc l hl)) (l * v * l⁻¹)
        ((Subgroup.mem_normalizer_iff.mp (hL₆G₆ hl) v).mp hv)
      calc d * l * d⁻¹ * v * (d * l * d⁻¹)⁻¹ =
            (d * l * d⁻¹ * l⁻¹) * (l * v * l⁻¹) * (d * l * d⁻¹ * l⁻¹)⁻¹ := by group
        _ = (l * v * l⁻¹) * (d * l * d⁻¹ * l⁻¹) * (d * l * d⁻¹ * l⁻¹)⁻¹ := by rw [hc]
        _ = l * v * l⁻¹ := by group
    let W : Subgroup G :=
      { carrier := {v | v ∈ F.V6 ∧ d * v * d⁻¹ = v}
        one_mem' := ⟨F.V6.one_mem, by group⟩
        mul_mem' := fun {a b} ha hb => ⟨F.V6.mul_mem ha.1 hb.1, by
          calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
            _ = a * b := by rw [ha.2, hb.2]⟩
        inv_mem' := fun {a} ha => ⟨F.V6.inv_mem ha.1, by
          calc d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
            _ = a⁻¹ := by rw [ha.2]⟩ }
    have hWV : W ≤ F.V6 := fun _ hv => hv.1
    have hLW : li L F.V6 ≤ Subgroup.normalizer (W : Set G) := by
      intro l hl
      apply S125St.mem_normalizer_of_conj_le
      rintro v ⟨hv, hdv⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hL₆G₆ hl) v).mp hv, ?_⟩
      have h1 := hdl l hl v hv
      calc d * (l * v * l⁻¹) * d⁻¹ =
            (d * l * d⁻¹) * (d * v * d⁻¹) * (d * l * d⁻¹)⁻¹ := by group
        _ = (d * l * d⁻¹) * v * (d * l * d⁻¹)⁻¹ := by rw [hdv]
        _ = l * v * l⁻¹ := h1
    have hzW : z ∈ W := by
      refine ⟨hV₁V₆ hz, ?_⟩
      have hdz : d * z * d⁻¹ ∈ F.V6 := (Subgroup.mem_normalizer_iff.mp hdG z).mp (hV₁V₆ hz)
      have hfix : ∀ t ∈ T, t * (d * z * d⁻¹) * t⁻¹ = d * z * d⁻¹ := by
        intro t ht
        obtain ⟨l, hlL, hl⟩ := hTact t ht
        have hzT : l * z * l⁻¹ = z := by
          rw [← hl z (hV₆V (hV₁V₆ hz))]
          exact S125Fin.conj_eq_of_card_two hcard₁ (hTV.1 ht) hz
        rw [hl _ (hV₆V hdz)]
        have h1 := hdl l hlL z (hV₁V₆ hz)
        have h2 := hdl l hlL (d * z * d⁻¹) hdz
        calc l * (d * z * d⁻¹) * l⁻¹ = d * l * d⁻¹ * (d * z * d⁻¹) * (d * l * d⁻¹)⁻¹ :=
              h2.symm
          _ = d * (l * z * l⁻¹) * d⁻¹ := by group
          _ = d * z * d⁻¹ := by rw [hzT]
      rcases hV₁eq _ (hCVT _ (hV₆V hdz) hfix) with h | h
      · exact absurd (by simpa using h) hz1
      · exact h
    rcases Ch4.T4213N.eq_bot_or_eq_of_slExteriorTwo hext hWV hLW with hW | hW
    · exact absurd ((Subgroup.mem_bot).mp (hW ▸ hzW)) hz1
    · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hvW : v ∈ W := hW ▸ hv
      calc v * d = d * v * d⁻¹ * d := by rw [hvW.2]
        _ = d * v := by group
  intro g hg
  obtain ⟨d, hd, hdg⟩ := KGOut.exists_mem_centralizerMod_of_sq_inner
    (Subgroup.normalizer (F.V6 : Set G)) (li L F.V6) T hL₆G₆ hG₆N hS
    (KGOut.sq_inner_sl_two (by norm_num) e₆) g hg
  have hdM := hC (hD d hd)
  have hrest : d⁻¹ * g ∈ Subgroup.normalizer (L : Set G) :=
    sup_le (hL₆L.trans hLM) hTM hdg
  have e : g = d * (d⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ hdM hrest

end S125L4

end CFSG.Quasithin.H13
