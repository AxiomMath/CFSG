module

public import CFSG.Quasithin.H13.A5W1618j
public import CFSG.Quasithin.Background.C126Split2
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model B2F E2
open scoped commutatorElement

section SL2

variable {F : Type} [Field F] [Fintype F]

theorem commutator_sl2_eq_top {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : 2 ≤ n) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ := by
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow (f := n)
    (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbij : Function.Bijective (slOf (K := F)) :=
    ⟨fun a b h => Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h),
      slOf_surjective⟩
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4)
      (MulEquiv.ofBijective _ hbij)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (commutator (Matrix.SpecialLinearGroup (Fin 2) F)) with h | h
  · exfalso
    have hc : ⁅unip (1 : F), lunip (1 : F)⁆ = 1 := by
      have : ⁅unip (1 : F), lunip (1 : F)⁆ ∈
          commutator (Matrix.SpecialLinearGroup (Fin 2) F) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rwa [h, Subgroup.mem_bot] at this
    have hcomm : unip (1 : F) * lunip (1 : F) = lunip (1 : F) * unip (1 : F) :=
      commutatorElement_eq_one_iff_mul_comm.mp hc
    have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 0) hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unip, coe_lunip, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, mul_one,
      mul_zero, add_zero] at h00
    have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [h2] at h00
    exact zero_ne_one h00
  · exact h

end SL2

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem not_le_centralizer_z_of_plus_eq (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ : Subgroup G} (hK₀im : autOn K₀ (S.WK K) = S.plus K) :
    ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro hK₀z
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  apply S.not_le_centralizer_z_of_inYz hK hT
  intro k hk
  have hkW := hKW hk
  have hkp : conjAct (S.WK K) ⟨k, hkW⟩ ∈ autOn K₀ (S.WK K) := by
    rw [hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkW⟩, hk, rfl⟩
  obtain ⟨⟨k₀, hk₀N⟩, hk₀, hk₀e⟩ := Setup.mem_autOn_iff.1 hkp
  have hc : k₀⁻¹ * k ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
    have h1 : conjAct (S.WK K) ((⟨k₀, hk₀N⟩ :
        ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ * ⟨k, hkW⟩) = 1 := by
      rw [map_mul, map_inv, hk₀e, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp h1
  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have h1 : k₀⁻¹ * k ∈ Subgroup.centralizer ({S.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc _ hzW).symm
  have e : k = k₀ * (k₀⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hK₀z hk₀) h1

theorem e23_cases (h23 : E2.E23Statement) (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {K₀ M : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hK₀im : autOn K₀ (S.WK K) = S.plus K) (hmp : MinParabolic (K₀ ⊔ S.Tv) S.Tv M) :
    ∃ hV : IsElemAbelian 2 (conjClosure S.V1 (K₀ ⊔ S.Tv)),
      IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)) ∧
      (C126.NatCase (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV ∨
        C126.A5Case (K₀ ⊔ S.Tv) S.Tv (conjClosure S.V1 (K₀ ⊔ S.Tv)) hV) := by
  set H := K₀ ⊔ S.Tv with hHdef
  set V' := conjClosure S.V1 H with hV'def
  have hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₀K.trans hK.1
  have hsylTv := S.isSylowTwoOf_Tv h1222 h517
  have hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hHchar : CharTwo H := C1GN.charTwo_of_le hF hsylTv le_sup_right hHG
  have hsylH : IsSylowTwoOf S.Tv H := hmp.isSylow
  have hred : IsTwoReducedIn H V' :=
    isTwoReducedIn_conjClosure_of_sylowIn hsylH.1 hsylH.2.1 hsylH.2.2 hHchar S.V1_le_omega_Tv
  have hV : IsElemAbelian 2 V' := hred.2.2.1
  refine ⟨hV, hred, ?_⟩
  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hO : pCoreOf 2 H ≠ ⊥ := by
    have hle : Subgroup.zpowers S.v12 ≤ H := (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    intro h
    have hvO := le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
    rw [h, Subgroup.mem_bot] at hvO
    exact S.v12_ne_one hvO
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO
  have hz := S.not_le_centralizer_z_of_plus_eq h1222 h517 hF hK hT hK₀im
  have hzV : S.z ∈ V' := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hK₀V : ¬ K₀ ≤ Subgroup.centralizer (V' : Set G) := fun h =>
    hz fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h hk) _ hzV).symm
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hK.1 hT
  have hHK : H ≤ S.HK K := sup_le (hK₀K.trans (le_sup_left.trans le_sup_left)) (S.Tv_le_HK K)
  have hVW : V' ≤ S.WK K := by
    rw [S.WK_eq hT]
    exact conjClosure_mono le_rfl hHK
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  have hK₀W := hK₀K.trans hKW
  have hJW : thompsonJ S.Tv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (B6.thompsonJ_le S.Tv).trans ((S.Tv_le_HK K).trans hR.2.1)
  have hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (V' : Set G) := by
    intro hJV
    apply hK₀V
    have hJV' : ⁅thompsonJ S.Tv, V'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJV
    have hVK : ⁅V', K₀⁆ ≤ V' := by
      rw [Subgroup.commutator_le]
      intro w hw k hk
      have hkN : k ∈ Subgroup.normalizer (V' : Set G) :=
        hred.2.1 (Subgroup.mem_sup_left hk)
      have h1 : k * w⁻¹ * k⁻¹ ∈ V' :=
        (Subgroup.mem_normalizer_iff.mp hkN _).mp (V'.inv_mem hw)
      have e2 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e2]
      exact V'.mul_mem hw h1
    have h3 : ⁅⁅K₀, thompsonJ S.Tv⁆, V'⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [hJV', Subgroup.commutator_bot_left]
      · refine le_bot_iff.mp ((Subgroup.commutator_mono hVK le_rfl).trans ?_)
        rw [Subgroup.commutator_comm, hJV']
    have hcV : ⁅K₀, thompsonJ S.Tv⁆ ≤ Subgroup.centralizer (V' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
    have hKJ : autOn ⁅K₀, thompsonJ S.Tv⁆ (S.WK K) = S.plus K := by
      rw [CFSG.Quasithin.H13.A5.autOn_commutator hK₀W hJW, hK₀im]
      exact S.plus_eq_commutator h1222 h517 hF hK hT
    intro k hk
    have hkN := hK₀W hk
    have hkp : conjAct (S.WK K) ⟨k, hkN⟩ ∈ autOn ⁅K₀, thompsonJ S.Tv⁆ (S.WK K) := by
      rw [hKJ, ← hK₀im]; exact Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
    obtain ⟨⟨c, hcN⟩, hc, hce⟩ := Setup.mem_autOn_iff.1 hkp
    have hcW : c⁻¹ * k ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
      have h1 : conjAct (S.WK K) ((⟨c, hcN⟩ :
          ↥(Subgroup.normalizer ((S.WK K : Subgroup G) : Set G)))⁻¹ * ⟨k, hkN⟩) = 1 := by
        rw [map_mul, map_inv, hce, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hcV hc) (Subgroup.centralizer_le hVW hcW)
  have hc := h23 G H S.Tv M V' hV hmp hSQ hHchar hred hJ
  rcases C126.case_split hV S.Tv hred.2.1 hc with hs | hn | ha
  · exfalso
    apply hK₀V
    exact (le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hK₀)).trans hs
  · exact Or.inl hn
  · exact Or.inr ha

end Setting

end CFSG.Quasithin.H13.A5
