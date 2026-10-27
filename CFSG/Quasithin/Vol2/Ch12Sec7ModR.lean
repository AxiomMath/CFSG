module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModQ
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModL

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem r1_sub_l1 : ∀ r ∈ r1, r ∈ l1 := by decide

theorem r1_normal_l1 : ∀ x ∈ l1, ∀ r ∈ r1, ∃ r' ∈ r1, x.comp r = r'.comp x := by decide

theorem two_l1 : ∀ g ∈ l1, two6 g = true → g ∈ r1 := by decide

theorem r2_sub_l2 : ∀ r ∈ r2, r ∈ l2 := by decide

theorem r2_normal_l2 : ∀ x ∈ l2, ∀ r ∈ r2, ∃ r' ∈ r2, x.comp r = r'.comp x := by decide

theorem two_l2 : ∀ g ∈ l2, two6 g = true → g ∈ r2 := by decide

theorem zs6_nodup : zs6.Nodup := by decide

theorem two_zs6 : ∀ g ∈ zs6, two6 g = true → g ∈ [B6.id] := by decide

theorem id_mem_zs6 : B6.id ∈ zs6 := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem relIndex_pCoreOf_mul {J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (V : Set G))
    (hK : IsPGroup 2 (J ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)) {C : Coding ↥V}
    {lJ rl : List B6} (hJc : ∀ a, a ∈ autOn J V ↔ C.cB a ∈ lJ)
    (hsurj : ∀ B ∈ lJ, ∃ a, C.cB a = B) (hJnd : lJ.Nodup) (hrnd : rl.Nodup)
    (hr1 : B6.id ∈ rl) (hrc : ∀ x ∈ rl, ∀ y ∈ rl, x.comp y ∈ rl) (hrsub : ∀ r ∈ rl, r ∈ lJ)
    (hr2 : ∀ r ∈ rl, r.comp r = B6.id)
    (hrn : ∀ x ∈ lJ, ∀ r ∈ rl, ∃ r' ∈ rl, x.comp r = r'.comp x)
    (hmax : ∀ g ∈ lJ, two6 g = true → g ∈ rl) (hgm : ∀ B ∈ lJ, B ∈ gm6) :
    (pCoreOf 2 J).relIndex J * rl.length = lJ.length := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  set H := autOn J V with hH
  set f := autOnSurj hJ with hf
  have e1 : (pCoreOf 2 J).subgroupOf J = CFSG.Open.pCore 2 ↥J := by
    show (Subgroup.map J.subtype (CFSG.Open.pCore 2 ↥J)).comap J.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have hker : f.ker ≤ CFSG.Open.pCore 2 ↥J := by
    apply CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker f)
    rw [ker_autOnSurj hJ]
    have e : (Subgroup.centralizer (V : Set G)).subgroupOf J ≃*
        (J ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
      { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_subgroupOf.1 x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subgroup.mem_subgroupOf.2 x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact hK.of_equiv e.symm
  have hrel : (pCoreOf 2 J).relIndex J = (CFSG.Open.pCore 2 ↥H).index := by
    rw [Subgroup.relIndex, e1, ← Subgroup.index_map_eq _ (autOnSurj_surjective hJ) hker,
      map_pCore_autOnSurj hJ hK]
  have hcardH : Nat.card H = lJ.length := by
    have e : ↥H ≃ {B : B6 // B ∈ lJ} :=
      Equiv.ofBijective (fun a => ⟨C.cB a, (hJc a).1 a.2⟩) ⟨fun a b hab => Subtype.ext
        (C.cB_injective (congrArg Subtype.val hab)), fun B => by
          obtain ⟨a, ha⟩ := hsurj B.1 B.2
          exact ⟨⟨a, (hJc a).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
    rw [Nat.card_congr e]
    have e2 : {B : B6 // B ∈ lJ} ≃ ↥lJ.toFinset := Equiv.subtypeEquivRight fun B => by simp
    rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hJnd]
  set R : Subgroup ↥H :=
    { carrier := {h | C.cB (h : MulAut ↥V) ∈ rl}
      one_mem' := by
        show C.cB 1 ∈ rl
        rw [C.cB_one]
        exact hr1
      mul_mem' := fun {a b} ha hb => by
        show C.cB ((a : MulAut ↥V) * b) ∈ rl
        rw [C.cB_mul]
        exact hrc _ ha _ hb
      inv_mem' := fun {a} ha => by
        show C.cB ((a : MulAut ↥V))⁻¹ ∈ rl
        have hsq : (a : MulAut ↥V) * a = 1 :=
          C.cB_injective (by rw [C.cB_mul, C.cB_one]; exact hr2 _ ha)
        rw [show ((a : MulAut ↥V))⁻¹ = a from (mul_eq_one_iff_inv_eq.1 hsq)]
        exact ha } with hRdef
  have hRn : R.Normal := by
    refine ⟨fun r hr x => ?_⟩
    obtain ⟨r', hr', hxr⟩ := hrn _ ((hJc _).1 x.2) _ hr
    obtain ⟨b, hb⟩ := hsurj r' (hrsub r' hr')
    have hxr' : (x : MulAut ↥V) * r = b * x :=
      C.cB_injective (by rw [C.cB_mul, C.cB_mul, hb]; exact hxr)
    show C.cB ((x : MulAut ↥V) * r * (x : MulAut ↥V)⁻¹) ∈ rl
    rw [hxr', mul_inv_cancel_right, hb]
    exact hr'
  have hRp : IsPGroup 2 R := by
    intro r
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hsq : ((r : ↥H) : MulAut ↥V) * r = 1 :=
      C.cB_injective (by rw [C.cB_mul, C.cB_one]; exact hr2 _ r.2)
    simpa [pow_two] using hsq
  have hRP : CFSG.Open.pCore 2 ↥H = R := by
    apply le_antisymm _ (CFSG.LieType.BorelTits.le_pCore 2 hRn hRp)
    intro x hx
    have h2 := pow_four_of_isPGroup C ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map H.subtype)
      ⟨x, hx, rfl⟩ (hgm _ ((hJc _).1 x.2))
    exact hmax _ ((hJc _).1 x.2) h2
  have hcardR : Nat.card R = rl.length := by
    have e : ↥R ≃ {B : B6 // B ∈ rl} :=
      Equiv.ofBijective (fun a => ⟨C.cB ((a : ↥H) : MulAut ↥V), a.2⟩)
        ⟨fun a b hab => Subtype.ext (Subtype.ext (C.cB_injective (congrArg Subtype.val hab))),
          fun B => by
            obtain ⟨a, ha⟩ := hsurj B.1 (hrsub B.1 B.2)
            exact ⟨⟨⟨a, (hJc a).2 (ha ▸ hrsub B.1 B.2)⟩, show C.cB a ∈ rl by rw [ha]; exact B.2⟩,
              Subtype.ext ha⟩⟩
    rw [Nat.card_congr e]
    have e2 : {B : B6 // B ∈ rl} ≃ ↥rl.toFinset := Equiv.subtypeEquivRight fun B => by simp
    rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hrnd]
  have hmi := (CFSG.Open.pCore 2 ↥H).card_mul_index
  rw [hRP, hcardR, hcardH, ← hRP, ← hrel] at hmi
  rw [mul_comm]
  exact hmi

omit [IsMulCommutative ↥V] in
theorem normalizer_inf_centralizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  apply normalizer_of_maps
  intro w hw
  obtain ⟨hwA, hwB⟩ := Subgroup.mem_inf.1 hw
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hA w).1 hwA, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hwB ⊢
  intro b hb
  have hb' : g⁻¹ * b * g ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hB) b).1 hb
    simpa using this
  have := hwB _ hb'
  calc b * (g * w * g⁻¹) = g * ((g⁻¹ * b * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * b * g)) * g⁻¹ := by rw [this]
    _ = g * w * g⁻¹ * b := by group

omit [IsMulCommutative ↥V] in
theorem normalizer_centralizerMod {W A : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hV : g ∈ Subgroup.normalizer (V : Set G))
    (hW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (centralizerMod W A V : Set G) := by
  apply normalizer_of_maps
  rintro x ⟨hxA, hxW, hxc⟩
  refine ⟨(Subgroup.mem_normalizer_iff.1 hA x).1 hxA,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hW hxW) (Subgroup.inv_mem _ hW), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hV) u).1 hu
    simpa using this
  have hc := (Subgroup.mem_normalizer_iff.1 hW _).1 (hxc _ hu')
  have e : g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ := by group
  rw [← e]
  exact hc

theorem centralizer_le_normalizer' (S : Subgroup G) :
    Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  apply normalizer_of_maps
  intro w hw
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [← hg w hw, mul_inv_cancel_right]
  exact hw

theorem l1_sub_gm6 : ∀ B ∈ l1, B ∈ gm6 := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  exact gm6_of_gmList ⟨(l1m_facts A hA).1, (l1m_facts A hA).2.1⟩

theorem l2_sub_gm6 : ∀ B ∈ l2, B ∈ gm6 := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  exact gm6_of_gmList ⟨(l2m_facts A hA).1, (l2m_facts A hA).2.1⟩

omit [IsMulCommutative ↥V] in
theorem L1_le_P1 : L1 T L V ≤ P1 T L V :=
  (oTwoUpper_le' _).trans (le_inf (inf_le_left.trans le_sup_left)
    (inf_le_right.trans (centralizer_le_normalizer' _)))

omit [Finite G] [IsMulCommutative ↥V] in
theorem L2_le_P2 : L2 T L V ≤ P2 T L V :=
  (oTwoUpper_le' _).trans fun _ hx => Subgroup.mem_inf.2 ⟨le_sup_left (a := L) hx.1, hx.2.1⟩

theorem XOf_le_Pof
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    {l : List ℕ} {h0 : 0 ∈ l} {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l}
    (hz : ∀ z ∈ zs6, ∀ c ∈ l, z.app c ∈ l) : XOf L ≤ Pof T L (C.subG l h0 hx) :=
  le_inf ((XOf_le L).trans le_sup_left) (XOf_le_normalizer_subG h1222 h hC.1 hz)

theorem relIndex_X
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) :
    (pCoreOf 2 (XOf L)).relIndex (XOf L) = 3 := by
  have hXP := XOf_le_Pof h1222 h hC (h0 := p1c_zero) (hx := p1c_xor) zs6_presv_p1c
  have := relIndex_pCoreOf_mul (J := XOf L) (C := C) (lJ := zs6) (rl := [B6.id])
    (fun x hx => L_le_normalizer h (XOf_le L hx))
    ((pof_inf_centralizer_isPGroup h1222 h _).to_le (inf_le_inf_right _ hXP))
    (mem_autOn_XOf h1222 h hC.1) (fun B hB => hC.1.2 B (zs6_sub_gm6 B hB)) zs6_nodup
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) two_zs6 zs6_sub_gm6
  have h3 : zs6.length = 3 := by decide
  simpa [h3] using this

theorem relIndex_L1
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) :
    (pCoreOf 2 (L1 T L V)).relIndex (L1 T L V) = 3 := by
  have hLP := L1_le_P1 (T := T) (L := L) (V := V)
  have := relIndex_pCoreOf_mul (J := L1 T L V) (C := C) (lJ := l1) (rl := r1)
    (fun x hx => pof_le_normalizer h1222 h _ (hLP hx))
    ((pof_inf_centralizer_isPGroup h1222 h _).to_le (inf_le_inf_right _ hLP))
    (mem_autOn_L1 h hC) (fun B hB => hC.1.2 B (l1_sub_gm6 B hB)) l1_nodup r1_nodup id_mem_r1
    r1_closed r1_sub_l1 r1_sq r1_normal_l1 two_l1 l1_sub_gm6
  have h12 : l1.length = 12 := by decide
  have h4 : r1.length = 4 := by decide
  rw [h12, h4] at this
  omega

theorem relIndex_L2
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) :
    (pCoreOf 2 (L2 T L V)).relIndex (L2 T L V) = 3 := by
  have hLP := L2_le_P2 (T := T) (L := L) (V := V)
  have := relIndex_pCoreOf_mul (J := L2 T L V) (C := C) (lJ := l2) (rl := r2)
    (fun x hx => pof_le_normalizer h1222 h _ (hLP hx))
    ((pof_inf_centralizer_isPGroup h1222 h _).to_le (inf_le_inf_right _ hLP))
    (mem_autOn_L2 h hC) (fun B hB => hC.1.2 B (l2_sub_gm6 B hB)) l2_nodup r2_nodup id_mem_r2
    r2_closed r2_sub_l2 r2_sq r2_normal_l2 two_l2 l2_sub_gm6
  have h12 : l2.length = 12 := by decide
  have h4 : r2.length = 4 := by decide
  rw [h12, h4] at this
  omega

theorem lemma12_7_2_five
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    oTwoUpper (P1 T L V) = L1 T L V ⊔ XOf L ∧
      {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
        oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} = {L1 T L V, XOf L} ∧
      oTwoUpper (P2 T L V) = L2 T L V ⊔ XOf L ∧
      {I : Subgroup G | I ≤ P2 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
        oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} = {L2 T L V, XOf L} := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV1 := V1_eq h hC
  have hV2 := V2_eq h hC
  have hTL : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G) := fun t ht => h.hyp.normalizes ht
  have hTV : ∀ t ∈ T, t ∈ Subgroup.normalizer (V : Set G) := fun t ht =>
    T_le_normalizer h1222 h ht
  obtain ⟨h1a, h1b⟩ := five_generic h1222 h hC (W := V1 T L V) (l := p1c) (lc := l1)
    (Li := L1 T L V)
    (fun a => by rw [hV1]; exact mem_autOn_Pof h1222 h hC.1 p1c_lt a) (mem_autOn_L1 h hC)
    l1_sub_gm6 id_mem_l1 l1_closed L1_le_P1
    (fun t ht => normalizer_le_normalizer_oTwoUpper _
      (normalizer_inf_centralizer (hTL t ht) (T_le_normalizer_V1 h1222 h ht)))
    (fun g hg => normalizer_le_normalizer_oTwoUpper _
      (normalizer_inf_centralizer (pof_le_normalizer_L h _ hg) (Subgroup.mem_inf.1 hg).2))
    (oTwoUpper_idem _) (relIndex_L1 h1222 h hC)
    (by rw [hV1]; exact XOf_le_Pof h1222 h hC zs6_presv_p1c) (relIndex_X h1222 h hC)
    cert_ord3a cert_beta1 cert_sq1
  obtain ⟨h2a, h2b⟩ := five_generic h1222 h hC (W := V2 T L V) (l := l2c) (lc := l2)
    (Li := L2 T L V)
    (fun a => by rw [hV2]; exact mem_autOn_Pof h1222 h hC.1 l2c_lt a) (mem_autOn_L2 h hC)
    l2_sub_gm6 id_mem_l2 l2_closed L2_le_P2
    (fun t ht => normalizer_le_normalizer_oTwoUpper _
      (normalizer_centralizerMod (hTL t ht) (hTV t ht) (T_le_normalizer_V2 h1222 h ht)))
    (fun g hg => normalizer_le_normalizer_oTwoUpper _
      (normalizer_centralizerMod (pof_le_normalizer_L h _ hg) (pof_le_normalizer h1222 h _ hg)
        (Subgroup.mem_inf.1 hg).2))
    (oTwoUpper_idem _) (relIndex_L2 h1222 h hC)
    (by rw [hV2]; exact XOf_le_Pof h1222 h hC zs6_presv_l2c) (relIndex_X h1222 h hC)
    cert_ord3b cert_beta2 cert_sq2
  exact ⟨h1a, h1b, h2a, h2b⟩

end CFSG.Quasithin.H13.S127.Mod

end
