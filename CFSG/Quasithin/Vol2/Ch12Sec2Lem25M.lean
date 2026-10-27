module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25L
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3K1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

abbrev RR (T U : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (U : Set G)

abbrev YY (L U V : Subgroup G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G))

abbrev NR (T U : Subgroup G) : Subgroup G := Subgroup.normalizer ((RR T U : Subgroup G) : Set G)

theorem RR_ne_bot [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) : RR T U ≠ ⊥ := by
  have hA := card_inf_V hC
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -, -, -, hUO, -⟩ := hC
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUR : U ≤ RR (S : Subgroup G) U := fun u hu =>
    ⟨hUT hu, Subgroup.mem_centralizer_iff.mpr fun x hx => (hUab u hu x hx).symm⟩
  intro hb
  have h1 : U ⊓ V ≤ ⊥ := hb ▸ (inf_le_left.trans hUR)
  rw [le_bot_iff] at h1
  rw [h1, Subgroup.card_bot] at hA
  have h2 : 2 ≤ n - 1 := by rcases hn with rfl | rfl | rfl <;> omega
  have h3 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem yn_data
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    QuasithinUnique.IsSylowTwoOf T (NR T U) ∧ pCoreOf 2 (NR T U) ≠ ⊥ ∧ YY L U V ≤ NR T U ∧
      YY L U V ∈ lFamily T ∧ T ≤ Subgroup.normalizer ((YY L U V : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13⟩ := hstar
  refine ⟨isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow (le_normalizer_R hC), fun hb => ?_,
    le_sup_left.trans h13, Y_mem_lFamily h1222 h1220 hH hNE hC hn3, le_normalizer_Y h1222 hH hC⟩
  have hR2 : IsPGroup 2 (RR T U) := hH.sylow.1.to_le inf_le_left
  have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 (RR T U) hR2
  rw [hb, le_bot_iff] at h1
  exact RR_ne_bot hH hC h1

theorem exists_K
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p)
    (hn3 : n ≠ 3) :
    ∃ K : Subgroup G, YY L U V ≤ K ∧ K ∈ cComp (NR T U) ∧
      NR T U ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hS, hO, hYN, hB, hTY⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  obtain ⟨K, ⟨hK, hYK⟩, -⟩ := lemma_1_2_4_existsUnique hH.qtke hH.simple hH.nonabelian h37 h39
    hO hS hYN hB
  have hKn := lemma_1_2_4_normal hH.qtke hH.simple hH.nonabelian h37 h38 hO hS hB hYK hK hTY
  exact ⟨K, hYK, hK,
    (Subgroup.normal_subgroupOf_iff_le_normalizer (A3.subnormal_le hK.2.2.1)).1 hKn⟩

theorem data_Ybar
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    Data1293 (modO2Image (NR T U) (YY L U V)) (n - 1)
      (Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2))) := by
  obtain ⟨Q, _, ρ, hsurj, hker, -, ⟨eQ⟩⟩ := exists_Y_rep h1222 h1220 hH hNE hC hn3
  obtain ⟨-, -, hYN, -, -⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  have eY := ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).trans eQ
  obtain ⟨e₁⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hYN
  have hn : n - 1 = 3 ∨ n - 1 = 4 := by
    obtain ⟨-, -, hn, -⟩ := hC
    rcases hn with rfl | rfl | rfl <;> omega
  exact data1293_of hn (e₁.symm.trans eY)

theorem cases_K
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3)
    {K : Subgroup G} (hYK : YY L U V ≤ K) (hK : K ∈ cComp (NR T U)) :
    YY L U V = K ∨ A312Case (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K) ∨
      (n = 4 ∧ IsSL27OverE49 ↥(modO2Image (NR T U) K)) := by
  obtain ⟨hS, hO, hYN, hB, hTY⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  have hKN : K ≤ NR T U := le_of_mem_cComp hK
  rcases lemma_1_2_4_list hH.qtke hH.simple hH.nonabelian h312 hO hS hYN hB hK hYK with
    heq | hcase | hnq
  · left
    refine L1293.eq_of_modO2Image_eq hYK hKN (perfect_of_mem_cComp hK) ?_ heq
    have hP : pCoreOf 2 (NR T U) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hS
    exact L1295.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer (hP.trans hTY)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
  · exact Or.inr (Or.inl hcase)
  · right
    right
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hO
    have hD := data_Ybar h331 h1222 h323 h1216 h1220 hH hNE hC hn3
    obtain ⟨hk3, hSL⟩ := hD.list_of_nonquasi (Subgroup.map_mono (fun x hx => hYK hx))
      (h36 _ hQ _ (modO2Image_mem_cComp hK)) hnq
    exact ⟨by omega, hSL⟩

theorem mem_pCoreOf_of_mem_pCore_subgroupOf [Finite G] {B H : Subgroup G} (hBH : B ≤ H)
    {x : ↥(B.subgroupOf H)} (hx : x ∈ CFSG.pCore 2 ↥(B.subgroupOf H)) :
    ((x : ↥H) : G) ∈ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := Subgroup.subgroupOfEquivOfLe hBH with hφ
  have hn : ((CFSG.pCore 2 ↥(B.subgroupOf H)).map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ φ.surjective
  have hp : IsPGroup 2 ((CFSG.pCore 2 ↥(B.subgroupOf H)).map φ.toMonoidHom) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(B.subgroupOf H))).map _
  have hle : (CFSG.pCore 2 ↥(B.subgroupOf H)).map φ.toMonoidHom ≤ CFSG.pCore 2 ↥B :=
    le_sSup ⟨hn, hp⟩
  have h1 : φ x ∈ CFSG.pCore 2 ↥B := hle ⟨x, hx, rfl⟩
  rw [A7.pCoreOf_eq_map_cfsgPCore]
  exact ⟨φ x, h1, rfl⟩

theorem card_pCore_Ybar_le
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    Nat.card (CFSG.pCore 2 ↥(modO2Image (NR T U) (YY L U V))) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hYN, -, -⟩ := yn_data h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  have hOY := pCoreOf_Y_le h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  have hRV := inf_V_eq h1222 hH hC
  have hidx : ((U ⊓ V).subgroupOf V).index = 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -⟩ := hC
    exact hidx
  have hVN : V ≤ NR T U := (S125.le_of_hyp1223 hH).trans (le_normalizer_R hC)
  have hRN : RR T U ≤ NR T U := Subgroup.le_normalizer
  have hR2 : IsPGroup 2 (RR T U) := hH.sylow.1.to_le inf_le_left
  have hRO : RR T U ≤ pCoreOf 2 (NR T U) := LieType.BorelTits.le_pCoreOf_normalizer 2 _ hR2
  set N := NR T U with hNdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥N) with hπ
  obtain ⟨v₀, hv₀V, hv₀A⟩ : ∃ v₀ ∈ V, v₀ ∉ U ⊓ V := by
    by_contra hno
    push Not at hno
    have htop : (U ⊓ V).subgroupOf V = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      exact Subgroup.mem_subgroupOf.mpr (hno v hv)
    rw [htop, Subgroup.index_top] at hidx
    omega
  set z₀ := π ⟨v₀, hVN hv₀V⟩ with hz₀
  have hπO : ∀ y : ↥N, (y : G) ∈ pCoreOf 2 N → π y = 1 := by
    intro y hy
    rw [A7.pCoreOf_eq_map_cfsgPCore] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    have e : y' = y := Subtype.ext hyy'
    rw [← e]
    exact (QuotientGroup.eq_one_iff _).mpr hy'
  have hRVimg : ∀ x (hx : x ∈ N), x ∈ RR T U ⊔ V → π ⟨x, hx⟩ = 1 ∨ π ⟨x, hx⟩ = z₀ := by
    intro x hx hxRV
    obtain ⟨r, hr, v, hv, rfl⟩ := Lem24.exists_mul_of_mem_sup_normal
      (fun v hv => (le_normalizer_R hC) (S125.le_of_hyp1223 hH hv)) hxRV
    have e1 : (⟨r * v, hx⟩ : ↥N) = ⟨r, hRN hr⟩ * ⟨v, hVN hv⟩ := rfl
    rw [e1, map_mul, hπO ⟨r, hRN hr⟩ (hRO hr), one_mul]
    by_cases hvA : v ∈ U ⊓ V
    · left
      have hvR : v ∈ RR T U := (hRV ▸ hvA : v ∈ RR T U ⊓ V).1
      exact hπO ⟨v, hVN hv⟩ (hRO hvR)
    · right
      have hvv : v * v₀⁻¹ ∈ U ⊓ V := by
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v, hv⟩ : ↥V))
          (b := (⟨v₀, hv₀V⟩ : ↥V)⁻¹)).mpr (by
            rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            exact ⟨fun h' => absurd h' hvA, fun h' => absurd h' hv₀A⟩)
        rw [Subgroup.mem_subgroupOf] at h1
        exact h1
      have hvvR : v * v₀⁻¹ ∈ RR T U := (hRV ▸ hvv : v * v₀⁻¹ ∈ RR T U ⊓ V).1
      have e2 : (⟨v, hVN hv⟩ : ↥N) = ⟨v * v₀⁻¹, hRN hvvR⟩ * ⟨v₀, hVN hv₀V⟩ := by
        apply Subtype.ext
        simp
      rw [e2, map_mul, hπO ⟨v * v₀⁻¹, hRN hvvR⟩ (hRO hvvR), one_mul]
  set ρ := π.subgroupMap ((YY L U V).subgroupOf N) with hρ
  have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  have hker : IsPGroup 2 ↥ρ.ker := by
    intro x
    have hx : ((x : ↥((YY L U V).subgroupOf N)) : ↥N) ∈ CFSG.pCore 2 ↥N := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥N)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  set Pr := (CFSG.pCore 2 ↥(modO2Image N (YY L U V))).comap ρ with hPr
  have hP2 : IsPGroup 2 Pr :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image N (YY L U V)))).comap_of_ker_isPGroup ρ
      hker
  have hPn : Pr.Normal := CFSG.pCore_normal.comap ρ
  have hPle : Pr ≤ CFSG.pCore 2 ↥((YY L U V).subgroupOf N) := le_sSup ⟨hPn, hP2⟩
  have hmem : ∀ w : ↥(CFSG.pCore 2 ↥(modO2Image N (YY L U V))),
      ((w : ↥(modO2Image N (YY L U V))) : ↥N ⧸ CFSG.pCore 2 ↥N) = 1 ∨
        ((w : ↥(modO2Image N (YY L U V))) : ↥N ⧸ CFSG.pCore 2 ↥N) = z₀ := by
    intro w
    obtain ⟨x, hx⟩ := hρs (w : ↥(modO2Image N (YY L U V)))
    have hxP : x ∈ Pr := by
      show ρ x ∈ CFSG.pCore 2 ↥(modO2Image N (YY L U V))
      rw [hx]
      exact w.2
    have hxO := mem_pCoreOf_of_mem_pCore_subgroupOf hYN (hPle hxP)
    have h1 := hRVimg (((x : ↥((YY L U V).subgroupOf N)) : ↥N) : G)
      ((x : ↥((YY L U V).subgroupOf N)) : ↥N).2 (hOY hxO)
    rw [← hx]
    exact h1
  let f : ↥(CFSG.pCore 2 ↥(modO2Image N (YY L U V))) →
      ↥(({1, z₀} : Set (↥N ⧸ CFSG.pCore 2 ↥N))) := fun w =>
    ⟨((w : ↥(modO2Image N (YY L U V))) : ↥N ⧸ CFSG.pCore 2 ↥N), by
      rcases hmem w with h1 | h1 <;> simp [h1]⟩
  have hf : Function.Injective f := by
    intro w₁ w₂ h12
    have h3 := congrArg Subtype.val h12
    exact Subtype.ext (Subtype.ext h3)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_coe_set_eq] at h1
  have h2 : ({1, z₀} : Set (↥N ⧸ CFSG.pCore 2 ↥N)).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : ↥N ⧸ CFSG.pCore 2 ↥N) {z₀}
    rw [Set.ncard_singleton] at this
    exact this
  omega

end Lem25

end CFSG.Quasithin.H13
