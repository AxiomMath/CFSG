module

public import CFSG.Quasithin.Vol2.Ch12Sec5FinD
public import CFSG.Quasithin.Vol2.Ch12Sec5L9a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Fin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_of_card_two {P : Subgroup G} (hP : Nat.card P = 2) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) {v : G} (hv : v ∈ P) : g * v * g⁻¹ = v := by
  by_cases hv1 : v = 1
  · rw [hv1]
    group
  have hgv : g * v * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hgv1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    have e : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [e, h]
    group
  have hP' := S125L9a.eq_zpowers hP hv hv1
  have hv2 : orderOf v = 2 := by
    rw [← Nat.card_zpowers, ← hP', hP]
  rw [hP'] at hgv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgv
  rw [← hk, ← zpow_mod_orderOf, hv2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exfalso
    apply hgv1
    rw [← hk, ← zpow_mod_orderOf, hv2]
    simp [h]
  · simp [h]

theorem index_centralizer_le_two {B V₁ : Subgroup G} {u : G} (hV₁ : Nat.card V₁ = 2)
    (hBV₁ : ∀ b ∈ B, ∀ v ∈ V₁, b * v * b⁻¹ = v)
    (hV₁c : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y = y * x)
    (hBu : ∀ b ∈ B, b * u * b⁻¹ * u⁻¹ ∈ V₁) :
    ((Subgroup.centralizer ({u} : Set G)).subgroupOf B).index ≤ 2 := by
  let ψ : ↥B →* ↥V₁ :=
    { toFun := fun b => ⟨(b : G) * u * (b : G)⁻¹ * u⁻¹, hBu b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b b' => by
        apply Subtype.ext
        have h1 := hBV₁ b b.2 _ (hBu b' b'.2)
        have h2 := hV₁c _ (hBu b' b'.2) _ (hBu b b.2)
        simp only [Subgroup.coe_mul]
        calc (b : G) * b' * u * ((b : G) * b')⁻¹ * u⁻¹ =
            (b * ((b' : G) * u * (b' : G)⁻¹ * u⁻¹) * (b : G)⁻¹) * ((b : G) * u * (b : G)⁻¹ * u⁻¹) :=
              by group
          _ = ((b : G) * u * (b : G)⁻¹ * u⁻¹) * ((b' : G) * u * (b' : G)⁻¹ * u⁻¹) := by
              rw [h1, h2] }
  have hker : ψ.ker = (Subgroup.centralizer ({u} : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (b : G) * u * (b : G)⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · intro h
      apply Subtype.ext
      change (b : G) * u * (b : G)⁻¹ * u⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h
  rw [← hker, Subgroup.index_ker, ← hV₁]
  exact Subgroup.card_le_card_group _

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply S125St.mem_normalizer_of_conj_le
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      exact hB b hb
  intro x hx
  exact hmap ⟨x, hx, rfl⟩

omit [Finite G] in
theorem normalizer_le_normalizer_pCoreOf (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
  have hchar : (CFSG.Open.pCore 2 ↥X).Characteristic := by
    infer_instance
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.Open.pCore 2 ↥X)

end S125Fin

open S125Fin in
theorem final125_of'
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (hE22 : E2.E22StatementC)
    (hTor : E2.E22TorusCover) {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hG₁ : ¬ Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h2 : Concl12_5_2 T L V F)
    (hL₁ : quasithinIsCComponent (li L F.V1) (Subgroup.normalizer (F.V1 : Set G)) ∧
      Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G))
    (hC₃ : Subgroup.centralizer (F.V3 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (h6 : Concl12_5_6 L V) (h7 : Concl12_5_7 T L V) (h8 : Concl12_5_8 T L V F)
    (h9 : Concl12_5_9 T L V F) (h12 : Concl12_5_12 T L V F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨H, hHs, hHG₁, ⟨e⟩, hKL₁, hKM, hM₁⟩ :=
    exists_hStar' h331 h1222 h1228 hE22 hTor hH hG₁ h2 hL₁ h12
  obtain ⟨hL₁c, hG₁N⟩ := hL₁
  have hVe : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hL₁G₁ : li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hL₁L : li L F.V1 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hL₁V : li L F.V1 ≤ Subgroup.normalizer (V : Set G) := hL₁L.trans hf.normalizes
  have hTH : T ≤ H := hHs.1.1
  have hT2 : IsPGroup 2 ↥T := hyp.sylow.1
  have hH₁G₁ : li L F.V1 ⊔ H ≤ Subgroup.normalizer (F.V1 : Set G) := sup_le hL₁G₁ hHG₁
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hTH.trans hHK
  have hTL₁ : T ≤ Subgroup.normalizer (li L F.V1 : Set G) := hTG₁.trans hG₁N
  have hTH₁ : T ≤ li L F.V1 ⊔ H := hTH.trans le_sup_right
  have hTsH₁ : QuasithinUnique.IsSylowTwoOf T (li L F.V1 ⊔ H) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH₁
  have hQT : pCoreOf 2 (li L F.V1 ⊔ H) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsH₁
  have hTsH : QuasithinUnique.IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hHKT : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hTsH
  have hH₁gen : li L F.V1 ⊔ H ≤ oTwoUpper H ⊔ li L F.V1 ⊔ T :=
    sup_le (le_sup_right.trans le_sup_left)
      (hHKT.symm.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hV₁V : F.V1 ≤ V := S125.V1_le F
  have hV₁c2 : Nat.card F.V1 = 2 := S125L9a.card_V1 F
  have hV₁2 : IsPGroup 2 ↥F.V1 := fun x => ⟨1, Subtype.ext (by simpa using hf.sq x (hV₁V x.2))⟩
  have hV₁T : F.V1 ≤ T := hV₁V.trans hf.le_T
  have hV₁sq : ∀ v ∈ F.V1, v * v = 1 := fun v hv => by simpa [sq] using hf.sq v (hV₁V hv)
  have hV₁comm : ∀ x ∈ F.V1, ∀ y ∈ F.V1, x * y = y * x := fun x hx y hy => by
    have := hf.comm
    exact congrArg Subtype.val (mul_comm' (⟨x, hV₁V hx⟩ : V) ⟨y, hV₁V hy⟩)
  have hV₇V : F.V7 ≤ V := Subgroup.map_subtype_le _
  have hV₁V₇ : F.V1 ≤ F.V7 := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, fun k hk => hv k fun h => hk ?_, rfl⟩
    rw [Finset.mem_singleton] at h
    subst h
    decide
  have hV₃V₇ : F.V3 ≤ F.V7 := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, fun k hk => hv k fun h => hk ?_, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h <;> simp [h]
  have hTV₇ : T ≤ Subgroup.normalizer (F.V7 : Set G) :=
    S125Tr2.T_le_normalizer_sub F hf.T_le _ fun u hu =>
      S125W.coordFix_V7_of (S125Tr2.stabGam_of_upperTri hu 2)
  have hV₇e : IsElemAbelian 2 F.V7 := by
    have := hf.comm
    exact ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (Subtype.val : ↥V → G) (mul_comm' (⟨a, hV₇V a.2⟩ : V) ⟨b, hV₇V b.2⟩))⟩⟩,
      fun x hx => hf.sq x (hV₇V hx)⟩
  have hO2L : L = oTwoUpper L := (hyp.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm
  have hTM₁ : T ≤ mi T L F.V1 := le_inf le_sup_right hTG₁
  have hlOne : lOne L F.V1 ≤ mi T L F.V1 :=
    (oTwoUpper_le _).trans (inf_le_inf_right _ le_sup_left)
  have hM₁le : mi T L F.V1 ≤ lOne L F.V1 ⊔ T := by
    have hTs : QuasithinUnique.IsSylowTwoOf T (mi T L F.V1) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTM₁
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hTs]
    refine sup_le_sup_right ((Subgroup.closure_le _).mpr ?_) T
    rintro x ⟨hxM, hxo⟩
    obtain ⟨j, hj⟩ := E1.exists_pow_mem_of_mem_sup hT2 hyp.normalizes hxM.1
    have hxL : x ∈ L :=
      mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxo))
        (pow_orderOf_eq_one x) hj
    exact Subgroup.subset_closure ⟨⟨hxL, hxM.2⟩, hxo⟩
  have hirr := h2.1.2.2.2.2.1
  have hX : lOne L F.V1 ⊔ T ≤ mi T L F.V1 := sup_le hlOne hTM₁
  have hQne : pCoreOf 2 (li L F.V1 ⊔ H) ≠ ⊥ := by
    intro h
    apply S125.V1_ne_bot F
    rw [eq_bot_iff, ← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hV₁T.trans hTH₁) hH₁G₁ hV₁2
  have hASH : AlmostSpecialHyp F.V7 F.V1 L T (li L F.V1 ⊔ H) :=
    { elemAbelian := hV₇e
      ne_bot := S125.V1_ne_bot F
      le_V := hV₁V₇
      oTwo_eq := hO2L
      V_le_T := hV₇V.trans hf.le_T
      T_le_normV₁ := hTG₁
      T_le_normV := hTV₇
      T_le_normL := hyp.normalizes
      sylow_LT := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
      H_le := hH₁G₁
      lOne_sup_le := sup_le (hlOne.trans hM₁) hTH₁
      sylow_H := hTsH₁
      charTwo := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTH₁, hQne⟩
      irred := ⟨hirr.1, hX.trans hirr.2.2.1, hX.trans hirr.2.1,
        fun W h1 h2 h3 => hirr.2.2.2 W h1 h2 (hM₁le.trans h3)⟩ }
  have hQU : ∀ q ∈ pCoreOf 2 (li L F.V1 ⊔ H), ∀ u ∈ conjClosure F.V7 (li L F.V1 ⊔ H),
      q * u * q⁻¹ * u⁻¹ ∈ F.V1 := fun q hq u hu => comm_mem_of_almostSpecial hASH hq hu
  have hUu : conjClosure F.V7 (li L F.V1 ⊔ H) ≤ u128 V F.V1 := conjClosure_mono hV₇V hH₁G₁
  have hU2 : IsPGroup 2 ↥(conjClosure F.V7 (li L F.V1 ⊔ H)) := fun x =>
    ⟨1, Subtype.ext (by simpa using h8.2.2 x (hUu x.2))⟩
  have hV₃U : F.V3 ≤ conjClosure F.V7 (li L F.V1 ⊔ H) := hV₃V₇.trans (le_conjClosure _ _)
  have hH₁U : li L F.V1 ⊔ H ≤ Subgroup.normalizer
      (conjClosure F.V7 (li L F.V1 ⊔ H) : Set G) := le_normalizer_conjClosure _ _
  have hOL₁N : li L F.V1 ⊔ H ≤ Subgroup.normalizer (pCoreOf 2 (li L F.V1) : Set G) :=
    hH₁G₁.trans (hG₁N.trans (normalizer_le_normalizer_pCoreOf _))
  have hOL₁Q : pCoreOf 2 (li L F.V1) ≤ pCoreOf 2 (li L F.V1 ⊔ H) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) hOL₁N
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hOKQ : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (li L F.V1 ⊔ H) := by
    have hOK : pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (oTwoUpper H) ⊔ pCoreOf 2 (li L F.V1)) :=
      IsPGroup.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        (hOK.trans (hKH.trans (le_sup_right.trans hOL₁N)))
    have hPN : li L F.V1 ⊔ H ≤ Subgroup.normalizer
        ((pCoreOf 2 (oTwoUpper H) ⊔ pCoreOf 2 (li L F.V1) : Subgroup G) : Set G) := by
      refine sup_le (fun l hl => mem_normalizer_sup (fun o ho => ?_) (fun o ho => ?_))
        (fun h hh => mem_normalizer_sup (fun o ho => ?_) (fun o ho => ?_))
      · have h1 := hKL₁ o (hOK ho) l hl
        have e1 : l * o * l⁻¹ = (o * l * o⁻¹ * l⁻¹)⁻¹ * o := by group
        rw [e1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right h1))
          (Subgroup.mem_sup_left ho)
      · exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hOL₁N (Subgroup.mem_sup_left hl)) o).mp ho)
      · exact Subgroup.mem_sup_left
          ((Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf _ (hHK hh)) o).mp ho)
      · exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hOL₁N (Subgroup.mem_sup_right hh)) o).mp ho)
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (sup_le (hOK.trans (hKH.trans le_sup_right))
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)) hPN hP2)
  have hD : ∀ x ∈ T, (∀ k ∈ oTwoUpper H, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (li L F.V1 ⊔ H)) →
      (∀ l ∈ li L F.V1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (li L F.V1 ⊔ H)) →
      x ∈ pCoreOf 2 (li L F.V1 ⊔ H) := fun x hx hk hl =>
    mem_pCoreOf_of_comm hH₁gen (hKH.trans le_sup_right) le_sup_left hTH₁ hT2 hTK hTL₁ hQT hx hk hl
  have hQH : pCoreOf 2 (li L F.V1 ⊔ H) ⊓ H ≤ pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((hT2.to_le hQT).to_le inf_le_left)
    intro h hh
    apply S125St.mem_normalizer_of_conj_le
    rintro x ⟨hxQ, hxH⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (Subgroup.mem_sup_right hh)) x).mp hxQ, H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)⟩
  have hW : ¬ E3.wClos V 0 T ≤ pCoreOf 2 H := by
    intro hle
    have hS : IsSylowIn 2 T H := ⟨hTsH.1, hTsH.2.1, hTsH.2.2⟩
    have heq := E3.e3_15 hS (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hle
    apply hHs.2.1
    refine le_trans ?_ h7.2.2
    intro h hh
    apply S125St.mem_normalizer_of_conj_le
    intro w hw
    have hY : conjSubgroup (pCoreOf 2 H) h⁻¹ = pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh))
      rw [conjSubgroup, inv_inv]
      exact this
    have h1 := E3.wClos_conj (V := V) (i := 0) (pCoreOf 2 H) h⁻¹
    rw [hY, ← heq] at h1
    rw [h1, conjSubgroup, inv_inv]
    exact ⟨w, hw, rfl⟩
  obtain ⟨A, hAΓ, hAO⟩ : ∃ A ∈ E3.gammaSet V 0 T, ¬ A ≤ pCoreOf 2 H := by
    by_contra hcon
    push Not at hcon
    exact hW (E3.wClos_le_of_forall hcon)
  have hAW : A ≤ E3.wClos V 0 T := E3.le_wClos hAΓ
  obtain ⟨hAT, g, hAg, hm⟩ := hAΓ
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hVe g
  have hVg2 : IsPGroup 2 ↥(conjSubgroup V g) := fun x =>
    ⟨1, Subtype.ext (by simpa using hVg.2 x x.2)⟩
  have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hVg2 hAg).mp hm
  have hAe : IsElemAbelian 2 A := by rw [hAeq]; exact hVg
  have hA2 : IsPGroup 2 ↥A := by rw [hAeq]; exact hVg2
  have hAC : A ≤ Subgroup.centralizer (V : Set G) := hAW.trans h7.1
  have hCL₁ : IsPGroup 2 ↥(li L F.V1 ⊓ Subgroup.centralizer (V : Set G)) :=
    (S125Tr2.isPGroup_centralizer hH hf).to_le (inf_le_inf_right _ (hL₁L.trans le_sup_left))
  have hAL₁ : ∀ a ∈ A, ∀ l ∈ li L F.V1, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 (li L F.V1) :=
    fun a ha l hl => comm_mem_pCoreOf hL₁V hCL₁ (hTL₁ (hAT ha)) (hAC ha) hl
  have hidx : ((pCoreOf 2 (li L F.V1 ⊔ H)).subgroupOf A).index ≤ 4 :=
    index_subgroupOf_le_four e (fun a ha => hTK (hAT ha)) hAe fun a ha hak =>
      hD a (hAT ha) (fun k hk => hOKQ (hak k hk)) (fun l hl => hOL₁Q (hAL₁ a ha l hl))
  have hrelB : (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)).relIndex A ≤ 4 := by
    rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
    exact hidx
  have hmB : E3.mQuot A (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ≤ 2 := by
    have h1 := E3.relIndex_eq_two_pow hA2 (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H))
    rw [h1] at hrelB
    by_contra hc
    have : 8 ≤ 2 ^ E3.mQuot A (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr3 : 3 < E3.rParam A := by rw [hAeq, E3.rParam_conj]; exact (h6 hVe).1
  have hUA : conjClosure F.V7 (li L F.V1 ⊔ H) ≤ Subgroup.normalizer (A : Set G) := by
    intro u hu
    by_contra hun
    have hCA : (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓ Subgroup.centralizer ({u} : Set G) ≤ A :=
      inf_le_left.trans inf_le_left
    have hnC : ¬ Subgroup.centralizer (((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓
        Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (A : Set G) := by
      intro h
      apply hun
      apply h
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have h1 := E3.rParam_le_mQuot hCA hnC
    have hidx2 := index_centralizer_le_two (B := A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) hV₁c2
      (fun b hb v hv => conj_eq_of_card_two hV₁c2 (hTG₁ (hAT hb.1)) hv) hV₁comm
      (fun b hb => hQU b hb.2 u hu)
    have e1 : ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
        (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) = ((Subgroup.centralizer ({u} : Set G)).subgroupOf
          (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H))).index := by
      rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
    have hrel : ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓ Subgroup.centralizer ({u} : Set G)).relIndex A
        ≤ 8 := by
      rw [← Subgroup.relIndex_mul_relIndex _ (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) A inf_le_left
        inf_le_left, e1]
      calc _ ≤ 2 * 4 := Nat.mul_le_mul hidx2 hrelB
        _ = 8 := by norm_num
    have h2 := E3.relIndex_eq_two_pow hA2
      ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓ Subgroup.centralizer ({u} : Set G))
    rw [h2] at hrel
    have hm3 : E3.mQuot A ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓
        Subgroup.centralizer ({u} : Set G)) ≤ 3 := by
      by_contra hc
      have : 16 ≤ 2 ^ E3.mQuot A ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) ⊓
          Subgroup.centralizer ({u} : Set G)) :=
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : E3.rParam A ≤ 3 := h1.trans (by exact_mod_cast hm3)
    exact absurd hr3 (not_lt.mpr h3)
  have hO₂H : pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ⊓ H ≤ pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro h hh
    apply S125St.mem_normalizer_of_conj_le
    rintro x ⟨hxQ, hxH⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (hHG₁ hh)) x).mp hxQ, H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)⟩
  by_cases hcase : ∃ u ∈ conjClosure F.V7 (li L F.V1 ⊔ H), ∃ b ∈ A ⊓ pCoreOf 2 (li L F.V1 ⊔ H),
      b * u * b⁻¹ * u⁻¹ ≠ 1
  ·
    obtain ⟨u, hu, b, hb, hne⟩ := hcase
    have hcV₁ : b * u * b⁻¹ * u⁻¹ ∈ F.V1 := hQU b hb.2 u hu
    have hcA : b * u * b⁻¹ * u⁻¹ ∈ A := by
      have h1 : u * b⁻¹ * u⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hUA hu) _).mp (A.inv_mem hb.1)
      have e1 : b * u * b⁻¹ * u⁻¹ = b * (u * b⁻¹ * u⁻¹) := by group
      rw [e1]
      exact A.mul_mem hb.1 h1
    have hV₁A : F.V1 ≤ A := by
      rw [S125L9a.eq_zpowers hV₁c2 hcV₁ hne, Subgroup.zpowers_le]
      exact hcA
    have hAO₂ : A ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
      by_cases hgV : g ∈ Subgroup.normalizer (V : Set G)
      · have hAV : A = V := by
          rw [hAeq, conjSubgroup]
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hgV)
        rw [hAV]
        exact h8.1
      · have hV₁g : F.V1 ≤ CFSG.conjugate V g := by
          rw [hAeq] at hV₁A
          exact hV₁A
        obtain ⟨⟨h, hh, hVh⟩, -⟩ := h9.2.2 g hgV hV₁g
        have hAh : A = conjSubgroup V h := hAeq.trans hVh
        intro x hx
        rw [hAh, mem_conjSubgroup_iff] at hx
        have h1 := h8.1 hx
        have h2 := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
          _ (Subgroup.inv_mem _ hh)) _).mp h1
        have e1 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
        rwa [e1] at h2
    exact hAO fun x hx => hO₂H ⟨hAO₂ hx, hTH (hAT hx)⟩
  ·
    push Not at hcase
    have hUB : conjClosure F.V7 (li L F.V1 ⊔ H) ≤
        Subgroup.centralizer ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H) : Subgroup G) : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hcase u hu b hb
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hs : E3.mQuot A (A ⊓ pCoreOf 2 (li L F.V1 ⊔ H)) < E3.sParam hAe := by
      have h1 : E3.sParam hAe = 3 := by
        subst hAeq
        rw [E3.sParam_conj hVe g hAe]
        exact (h6 hVe).2.2
      omega
    obtain ⟨h36, -⟩ := E3.e3_6 hAe inf_le_left le_rfl hs hU2
    have hAU : ∀ a ∈ A, ∀ u ∈ conjClosure F.V7 (li L F.V1 ⊔ H), a * u = u * a := by
      intro a ha u hu
      have h1 : u ∈ conjClosure F.V7 (li L F.V1 ⊔ H) ⊓
          Subgroup.centralizer ((A ⊓ pCoreOf 2 (li L F.V1 ⊔ H) : Subgroup G) : Set G) :=
        ⟨hu, hUB hu⟩
      rw [← h36] at h1
      exact Subgroup.mem_centralizer_iff.mp h1.2 a ha
    have hKU : oTwoUpper H ≤ Subgroup.normalizer (conjClosure F.V7 (li L F.V1 ⊔ H) : Set G) :=
      hKH.trans (le_sup_right.trans hH₁U)
    have hNK : centralizerMod F.V1 (oTwoUpper H) (conjClosure F.V7 (li L F.V1 ⊔ H)) ≤
        pCoreOf 2 (oTwoUpper H) := by
      rcases le_pCoreOf_or_le (centralizerMod_le_left _ _ _) (fun k hk =>
          mem_normalizer_centralizerMod hk (hKU hk) (hHG₁ (hKH hk))) e with h | h
      · exact h
      · exfalso
        apply hKM
        have hKC : oTwoUpper H ≤ Subgroup.centralizer
            (conjClosure F.V7 (li L F.V1 ⊔ H) : Set G) := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro x ⟨hxH, hxo⟩
          have hxK : x ∈ oTwoUpper H := Subgroup.subset_closure ⟨hxH, hxo⟩
          obtain ⟨-, hxN, hxc⟩ := h hxK
          exact mem_centralizer_of_comm_mod hxo (fun v hv => conj_eq_of_card_two hV₁c2 hxN hv)
            hV₁sq hxc
        exact (hKC.trans (Subgroup.centralizer_le hV₃U)).trans hC₃
    apply hAO
    intro a ha
    refine hQH ⟨hD a (hAT ha) (fun k hk => hOKQ (hNK ?_)) (fun l hl => hOL₁Q (hAL₁ a ha l hl)),
      hTH (hAT ha)⟩
    have haN : a ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hTK (hAT ha)
    have hakK : a * k * a⁻¹ * k⁻¹ ∈ oTwoUpper H :=
      (oTwoUpper H).mul_mem ((Subgroup.mem_normalizer_iff.mp haN k).mp hk)
        ((oTwoUpper H).inv_mem hk)
    refine ⟨hakK, (Subgroup.normalizer (F.V1 : Set G)).mul_mem
      ((Subgroup.normalizer (F.V1 : Set G)).mul_mem
        ((Subgroup.normalizer (F.V1 : Set G)).mul_mem (hTG₁ (hAT ha)) (hHG₁ (hKH hk)))
        (Subgroup.inv_mem _ (hTG₁ (hAT ha)))) (Subgroup.inv_mem _ (hHG₁ (hKH hk))),
      fun u hu => ?_⟩
    have hu' : k⁻¹ * u * k ∈ conjClosure F.V7 (li L F.V1 ⊔ H) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hKU hk)) u).mp hu
      simpa using this
    have h1 : a⁻¹ * (k⁻¹ * u * k) * a = k⁻¹ * u * k := by
      rw [mul_assoc, ← hAU a ha _ hu', ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : a * u * a⁻¹ = u := by
      rw [hAU a ha u hu, mul_assoc, mul_inv_cancel, mul_one]
    have e1 : a * k * a⁻¹ * k⁻¹ * u * (a * k * a⁻¹ * k⁻¹)⁻¹ * u⁻¹ =
        a * k * (a⁻¹ * (k⁻¹ * u * k) * a) * k⁻¹ * a⁻¹ * u⁻¹ := by group
    rw [e1, h1]
    have e2 : a * k * (k⁻¹ * u * k) * k⁻¹ * a⁻¹ * u⁻¹ = a * u * a⁻¹ * u⁻¹ := by group
    rw [e2, h2, mul_inv_cancel]
    exact F.V1.one_mem

end CFSG.Quasithin.H13
