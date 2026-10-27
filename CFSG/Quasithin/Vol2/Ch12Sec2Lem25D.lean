module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25B
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G] [Finite G]

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting in
theorem exists_odd_moves {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ v : ↥V, v * v = 1)
    (htop : autOn L V = ⊤) {W : Subgroup ↥V} (hW : 3 ≤ Nat.card ↥W) {d : ↥V} (hd : d ∈ W)
    (hd1 : d ≠ 1) :
    ∃ g, ∃ hg : g ∈ L, Odd (orderOf g) ∧
      (∀ x : ↥V, A4.actionOn V L hLV ⟨g, hg⟩ x * x⁻¹ ∈ W) ∧ g * (d : G) * g⁻¹ ≠ d := by
  classical
  let _ := MulAutTwo.zmod2Module hV2
  obtain ⟨d', hd', hd'1, hd'd⟩ : ∃ d' ∈ W, d' ≠ 1 ∧ d' ≠ d := by
    by_contra hno
    push Not at hno
    have hsub : (W : Set ↥V) ⊆ {1, d} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hno x hx hx1)
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hW3 : 3 ≤ (W : Set ↥V).ncard := by
      calc 3 ≤ Nat.card ↥W := hW
        _ = (W : Set ↥V).ncard := Nat.card_coe_set_eq _
    have h3 := Set.ncard_insert_le (1 : ↥V) ({d} : Set ↥V)
    rw [Set.ncard_singleton] at h3
    omega
  set e := Additive.ofMul d with hedef
  set e' := Additive.ofMul d' with he'def
  have hW' : ∀ x : Additive ↥V, x ∈ (ZMod 2) ∙ e → Additive.toMul x ∈ W := fun x hx => by
    rcases mem_span_singleton_iff_two.mp hx with rfl | rfl
    · exact W.one_mem
    · exact hd
  have hW'' : ∀ x : Additive ↥V, x ∈ (ZMod 2) ∙ e' → Additive.toMul x ∈ W := fun x hx => by
    rcases mem_span_singleton_iff_two.mp hx with rfl | rfl
    · exact W.one_mem
    · exact hd'
  have hne : e' ∉ (ZMod 2) ∙ e := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hd'1 (Additive.ofMul.injective h)
    · exact hd'd (Additive.ofMul.injective h)
  have hne' : e ∉ (ZMod 2) ∙ e' := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hd1 (Additive.ofMul.injective h)
    · exact hd'd (Additive.ofMul.injective h).symm
  obtain ⟨f₁, hf₁S, hf₁e'⟩ := exists_dual_eq_one_of_notMem hne
  obtain ⟨f₂, hf₂S, hf₂e⟩ := exists_dual_eq_one_of_notMem hne'
  have hf₁e : f₁ e = 0 := hf₁S e (mem_span_singleton_self e)
  have hf₂e' : f₂ e' = 0 := hf₂S e' (mem_span_singleton_self e')
  set σL := LinearEquiv.transvection hf₁e * LinearEquiv.transvection hf₂e' with hσL
  have hσx : ∀ x, σL x = x + f₂ x • e' + f₁ (x + f₂ x • e') • e := fun x => by
    rw [hσL, LinearEquiv.mul_apply, transvection_apply, transvection_apply]
  have hσe : σL e = e' := by
    rw [hσx, hf₂e, one_smul, map_add, hf₁e, hf₁e', zero_add, one_smul, add_comm e e',
      add_assoc, two_add_self, add_zero]
  have hσe' : σL e' = e + e' := by
    rw [hσx, hf₂e', zero_smul, add_zero, hf₁e', one_smul, add_comm]
  have hσee : σL (e + e') = e := by
    rw [map_add, hσe, hσe', ← add_assoc, add_comm e' e, add_assoc, two_add_self, add_zero]
  have hz : ∀ a : ZMod 2, a + a = 0 := by decide
  have hσ3 : σL ^ 3 = 1 := by
    refine LinearEquiv.ext fun x => ?_
    set k := x + f₂ x • e + f₁ x • e' with hk
    have hk1 : f₁ k = 0 := by
      rw [hk, map_add, map_add, map_smul, map_smul, hf₁e, hf₁e', smul_zero, smul_eq_mul, mul_one,
        add_zero]
      exact hz _
    have hk2 : f₂ k = 0 := by
      rw [hk, map_add, map_add, map_smul, map_smul, hf₂e, hf₂e', smul_zero, smul_eq_mul, mul_one,
        add_zero]
      exact hz _
    have hσk : σL k = k := by rw [hσx, hk2, zero_smul, add_zero, hk1, zero_smul, add_zero]
    have hx : x = k + f₂ x • e + f₁ x • e' := by
      rw [hk, add_assoc (x + f₂ x • e + f₁ x • e') (f₂ x • e) (f₁ x • e'),
        add_assoc x (f₂ x • e) (f₁ x • e'), add_assoc x, two_add_self, add_zero]
    show σL (σL (σL x)) = x
    rw [hx]
    simp only [map_add, map_smul, hσk, hσe, hσe', hσee]
  set σ : MulAut ↥V := MulAutTwo.linEquiv.symm σL with hσdef
  have hσW : ∀ j : ℕ, ∀ x : ↥V, (σ ^ j) x * x⁻¹ ∈ W := by
    intro j
    induction j with
    | zero => intro x; simp [W.one_mem]
    | succ j ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, show (σ ^ j) (σ x) * x⁻¹ =
        ((σ ^ j) (σ x) * (σ x)⁻¹) * (σ x * x⁻¹) by group]
      refine W.mul_mem (ih _) ?_
      show Additive.toMul (σL (Additive.ofMul x)) * x⁻¹ ∈ W
      rw [hσx, toMul_add, toMul_add, toMul_ofMul, mul_assoc, mul_assoc, mul_comm x, mul_assoc,
        mul_assoc, inv_mul_cancel, mul_one]
      exact W.mul_mem (hW'' _ (smul_mem _ _ (mem_span_singleton_self e')))
        (hW' _ (smul_mem _ _ (mem_span_singleton_self e)))
  obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
  obtain ⟨k, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  refine ⟨((l ^ 2 ^ k : ↥L) : G), (l ^ 2 ^ k).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hlm]; exact dvd_mul_right _ _), hlm, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  · intro x
    have : A4.actionOn V L hLV ⟨((l ^ 2 ^ k : ↥L) : G), (l ^ 2 ^ k).2⟩ = σ ^ 2 ^ k := by
      rw [show (⟨((l ^ 2 ^ k : ↥L) : G), (l ^ 2 ^ k).2⟩ : ↥L) = l ^ 2 ^ k from rfl, map_pow, hl]
    rw [this]
    exact hσW _ x
  · intro hfix
    have hact : A4.actionOn V L hLV (l ^ 2 ^ k) = σ ^ 2 ^ k := by rw [map_pow, hl]
    have h1 : ((σ ^ 2 ^ k) d : G) = d := by
      rw [← hact, A4.actionOn_apply_coe]
      exact hfix
    have h2 : (σL ^ 2 ^ k) e = e := by
      have h3 : MulAutTwo.linEquiv (σ ^ 2 ^ k) = σL ^ 2 ^ k := by
        rw [map_pow, hσdef, MulEquiv.apply_symm_apply]
      rw [← h3, MulAutTwo.linEquiv_apply, toMul_ofMul, Subtype.ext h1]
    have h3 : ¬ 3 ∣ 2 ^ k := fun h => by
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    have h4 : σL ^ 2 ^ k = σL ^ (2 ^ k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, pow_add, pow_mul, hσ3, one_pow, one_mul]
    rw [h4] at h2
    have h5 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by omega
    rcases h5 with h5 | h5
    · rw [h5, pow_one, hσe] at h2
      exact hd'd (Additive.ofMul.injective h2)
    · rw [h5, pow_two, LinearEquiv.mul_apply, hσe, hσe'] at h2
      apply hd'1
      apply Additive.ofMul.injective
      rw [← he'def, ofMul_one]
      calc e' = (e + e') + e := by rw [add_comm e e', add_assoc, two_add_self, add_zero]
        _ = e + e := by rw [h2]
        _ = 0 := two_add_self e

end Lem25

open Lem25

theorem stmt12_2_25_26_of_config_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) (hctl3 : Lem12225CTL3)
    (hn5 : Lem12225N5) (hsplit : Lem12226Split) : Stmt12_2_25_26_of_config := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  have hn34 := hn5 G T L V H P U I h n p hH hNE hC
  refine ⟨?_, hsplit G T L V H P U I h n p hH hNE hC⟩
  have hYN := fun hn3 => hY G T L V H P U I h n p hH hNE hC hn3
  have hctl := fun hn3 => hctl3 G T L V H P U I h n p hH hNE hC hn3
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hc1, -, hc2, -, hc3, hCV, -, hRe, -, -, hZ, hc10, -⟩ := hstar
  obtain ⟨hHs, -, hn, hVn, -, -, hp, hp2, hP, -, hhH, hhM, hI, -, hUd, hUi, hUe, hD, -,
    hidx, ⟨hcommV, htv⟩, hUO, -, -, hHU, hHI, hIP, -, hIM, -⟩ := hC
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Q := pCoreOf 2 (L ⊔ (S : Subgroup G)) with hQdef
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hV2g : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVe
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hNVM : Subgroup.normalizer (V : Set G) ≤ M :=
    Lem20.normalizer_le_of_hyp1223 (stmt12_2_6_of h1222 h323) hH
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hPh : (P : Subgroup G) = Subgroup.zpowers h := hP
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hTI := h1216 G S L V hH hNE
  have hVL : V ≤ L := by
    rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hH.normalizes (hVT hv)) l).mp hl)
      (L.inv_mem hl)
  have hpL : pCoreOf 2 L ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hH.normalizes.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  set A := CFSG.conjugate V h with hAdef
  have hVA : V ⊓ A = ⊥ := by
    rcases hTI h with h1 | h1
    · exfalso
      apply hhM
      refine hNVM (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
      rw [← BlueprintB2.mem_conjugate_iff, h1]
    · exact h1
  have hBase : I62.Base V A := ⟨hVe, isElemAbelian_conjugate' hVe h,
    conjugate_one V ▸ isTISetIn_conjugate hTI 1, isTISetIn_conjugate hTI h, hVA⟩
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  have htiU : ASInputs.tiU V A ≠ V := by
    intro htU
    have hVNA : V ≤ Subgroup.normalizer (A : Set G) := htU ▸ inf_le_right
    have hI2 : IsPGroup 2 I := by
      rw [hI]
      exact IsPGroup.to_sup_of_normal_right' (B2F.isPGroup_of_isElemAbelian hVe)
        (B2F.isPGroup_of_isElemAbelian (isElemAbelian_conjugate' hVe h)) hVNA
    obtain ⟨_, ⟨eD⟩⟩ := hD
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf I)
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hcard
    obtain ⟨k, hk⟩ := hI2.exists_card_eq
    have hpd : p ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd))
  have hCUV : U ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rintro u ⟨hu, huV⟩
    have hUAC : U ⊓ A ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun a ha => hUab a ha.1 b hb.1
    have hu' : u ∈ (U ⊓ V) ⊔ (U ⊓ A) := hUd ▸ hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_centralizer hUAC hu'
    have hbV : b ∈ Subgroup.centralizer (V : Set G) := by
      have ha' : a⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v hv a ha.2)
      have := Subgroup.mul_mem _ ha' huV
      simpa using this
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      exact ha.2
    · exfalso
      have hbB : b ∈ ASInputs.tiB V A := ⟨hb.2, hUN hb.1⟩
      have h1 := hBase.inf_centralizer_eq' hbB hb1
      apply htiU
      rw [← h1]
      refine le_antisymm inf_le_left fun v hv => ⟨hv, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbV v hv)
  have hCLV : Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVL
  have hCTL : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases hn34 with h3 | h4
    · exact hctl h3
    have hY4 := hYN (by omega)
    have hhI : h ∈ I := by rw [hIP]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hPh ▸
      Subgroup.mem_zpowers h))
    have hUI : U ≤ I := by rw [hIP]; exact le_sup_right.trans le_sup_left
    have hCIU : (S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G) ≤
        Subgroup.centralizer (U : Set G) := inf_le_right.trans (Subgroup.centralizer_le hUI)
    have hgR : ∀ g ∈ Subgroup.normalizer (U : Set G), g ∈ I →
        ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
          g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
      intro g hgU hgI x hx
      rw [hc1] at hx ⊢
      obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hCIU hx
      have hcg : g * c * g⁻¹ = c := by
        rw [Subgroup.mem_centralizer_iff.mp hc.2 g hgI, mul_inv_cancel_right]
      rw [show g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) by group, hcg]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp hgU u).mp hu) hc
    have hSR : (S : Subgroup G) ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hHU (hTH ht)⟩
    have hhR : h ∈ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hgR h hhU hhI x, fun hx => ?_⟩
      have := hgR h⁻¹ (Subgroup.inv_mem _ hhU) (I.inv_mem hhI) _ hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
    have hIR : I ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
      rw [hIP]
      exact sup_le (sup_le (hPh ▸ (Subgroup.zpowers_le).mpr hhR) (hUT.trans hSR))
        (hVT.trans hSR)
    have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    have hW3 : 3 ≤ Nat.card ↥((U ⊓ V).subgroupOf V) := by
      have h1 := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
      rw [hA2, hVn, h4, show (2 : ℕ) ^ 4 = 16 by norm_num] at h1
      omega
    have hgY : ∀ g, ∀ hg : g ∈ L, Odd (orderOf g) →
        (∀ x : ↥V, A4.actionOn V L hLV ⟨g, hg⟩ x * x⁻¹ ∈ (U ⊓ V).subgroupOf V) →
          g ∈ oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) := by
      intro g hg hodd hgW
      refine Subgroup.subset_closure ⟨⟨hg, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩, hodd⟩
      have hW : ∀ y (hy : y ∈ V), (g * y * g⁻¹ ∈ U ⊓ V ↔ y ∈ U ⊓ V) := fun y hy => by
        have h1 := (Subgroup.mul_mem_iff_of_index_two hA2).mp (hgW ⟨y, hy⟩)
        rw [inv_mem_iff] at h1
        exact h1
      constructor
      · intro hx
        exact (hW x hx.2).mpr hx
      · intro hx
        have hxV : x ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hg)) _).mp hx.2
          rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
        exact (hW x hxV).mp hx
    have hCUY : ∀ u ∈ U, u ∈ Subgroup.centralizer
        ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
          Set G) → u = 1 := by
      intro u hu huY
      by_contra hu1
      have hfix : ∀ d : ↥V, d ∈ (U ⊓ V).subgroupOf V → d ≠ 1 →
          (∀ g, ∀ hg : g ∈ L, Odd (orderOf g) →
            (∀ x : ↥V, A4.actionOn V L hLV ⟨g, hg⟩ x * x⁻¹ ∈ (U ⊓ V).subgroupOf V) →
              g * (d : G) * g⁻¹ = d) → False := fun d hd hd1 hall => by
        obtain ⟨g, hg, hodd, hgW, hgd⟩ := exists_odd_moves hLV hV2' htop hW3 hd hd1
        exact hgd (hall g hg hodd hgW)
      by_cases huV : u ∈ V
      · refine hfix ⟨u, huV⟩ (Subgroup.mem_subgroupOf.mpr ⟨hu, huV⟩)
          (fun h1 => hu1 (congrArg Subtype.val h1)) fun g hg hodd hgW => ?_
        have := Subgroup.mem_centralizer_iff.mp huY g (hgY g hg hodd hgW)
        show g * u * g⁻¹ = u
        rw [this, mul_inv_cancel_right]
      · have huCV : u ∉ Subgroup.centralizer (V : Set G) := fun h1 => huV (hCUV ⟨hu, h1⟩)
        obtain ⟨v₀, hv₀, hv₀u⟩ : ∃ v₀ ∈ V, u * v₀ * u⁻¹ * v₀⁻¹ ≠ 1 := by
          by_contra hno
          push Not at hno
          exact huCV (Subgroup.mem_centralizer_iff.mpr fun v hv => by
            have := hno v hv
            calc v * u = (u * v * u⁻¹ * v⁻¹)⁻¹ * u * v := by group
              _ = u * v := by rw [this, inv_one, one_mul])
        have hdU : u * v₀ * u⁻¹ * v₀⁻¹ ∈ U := by
          rw [show u * v₀ * u⁻¹ * v₀⁻¹ = u * (v₀ * u⁻¹ * v₀⁻¹) by group]
          exact U.mul_mem hu ((Subgroup.mem_normalizer_iff.mp (hHU (hTH (hVT hv₀))) _).mp
            (U.inv_mem hu))
        have hdV : u * v₀ * u⁻¹ * v₀⁻¹ ∈ V :=
          V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUN hu) v₀).mp hv₀) (V.inv_mem hv₀)
        refine hfix ⟨_, hdV⟩ (Subgroup.mem_subgroupOf.mpr ⟨hdU, hdV⟩)
          (fun h1 => hv₀u (congrArg Subtype.val h1)) fun g hg hodd hgW => ?_
        have hgu := Subgroup.mem_centralizer_iff.mp huY g (hgY g hg hodd hgW)
        have hw := hgW ⟨v₀, hv₀⟩
        set w := (A4.actionOn V L hLV ⟨g, hg⟩ ⟨v₀, hv₀⟩ * (⟨v₀, hv₀⟩ : ↥V)⁻¹ : ↥V) with hwdef
        have hwG : g * v₀ * g⁻¹ = (w : G) * v₀ := by
          rw [hwdef]
          simp [A4.actionOn_apply_coe]
        have hwu : (w : G) * u = u * w := hUab _ (Subgroup.mem_subgroupOf.mp hw).1 u hu
        have hgu' : g * u * g⁻¹ = u := by rw [hgu, mul_inv_cancel_right]
        show g * (u * v₀ * u⁻¹ * v₀⁻¹) * g⁻¹ = u * v₀ * u⁻¹ * v₀⁻¹
        calc g * (u * v₀ * u⁻¹ * v₀⁻¹) * g⁻¹ =
            (g * u * g⁻¹) * (g * v₀ * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * v₀ * g⁻¹)⁻¹ := by group
          _ = u * ((w : G) * v₀) * u⁻¹ * ((w : G) * v₀)⁻¹ := by rw [hgu', hwG]
          _ = (u * w) * v₀ * u⁻¹ * v₀⁻¹ * (w : G)⁻¹ := by group
          _ = (w * u) * v₀ * u⁻¹ * v₀⁻¹ * (w : G)⁻¹ := by rw [hwu]
          _ = w * (u * v₀ * u⁻¹ * v₀⁻¹) * (w : G)⁻¹ := by group
          _ = u * v₀ * u⁻¹ * v₀⁻¹ := by
            rw [hVab _ (Subgroup.mem_subgroupOf.mp hw).2 _ hdV, mul_inv_cancel_right]
    have hCLR : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
        (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := hc2 ▸ le_sup_right
    have hYL : oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ≤ L :=
      (oTwoUpper_le _).trans inf_le_left
    have hCeq : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) =
        ((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer
          ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
            Set G) := by
      apply le_antisymm
      · exact fun c hc => ⟨hCLR hc, Subgroup.centralizer_le hYL hc.2⟩
      · rintro x ⟨hxR, hxY⟩
        rw [hc2] at hxR
        obtain ⟨u, hu, c, hc, rfl⟩ :=
          exists_mul_of_mem_sup_centralizer (hCLR.trans inf_le_right) hxR
        have hcY := Subgroup.centralizer_le hYL hc.2
        have huY : u ∈ Subgroup.centralizer
            ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) :
              Subgroup G) : Set G) := by
          have := Subgroup.mul_mem _ hxY (Subgroup.inv_mem _ hcY)
          simpa using this
        rw [hCUY u hu huY, one_mul]
        exact hc
    by_contra hne
    have hT₀2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      S.isPGroup'.to_le inf_le_left
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨_, hne, hT₀2, rfl⟩ : IsTwoLocal
      (Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)))
    have hLN : L ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
    have hTN : (S : Subgroup G) ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hH.normalizes ht⟩
    have hIN : I ≤ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      fun x hx => by
        rw [hCeq]
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hIR hx, B6.le_normalizer_centralizer le_rfl (hY4 (hIR hx))⟩
    have heq := ((h331 G S hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal
      hH.quasisimple).1.2.2 M' hM' ((sup_le hLN hTN).trans hle)
    rw [hH.conjClosure_eq] at heq
    exact hIM (hIN.trans (hle.trans heq.le))
  have hQV : Q = V := by rw [hc3, hCTL, sup_bot_eq]
  have hVO : V = pCoreOf 2 L := le_antisymm
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV hV2g) (hQV ▸ hpL)
  refine ⟨?_, hVO, hn34, by rw [hZ, hCTL, sup_bot_eq]; exact hc10⟩
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVO]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hOM : pCoreOf 2 M = V := by
    apply le_antisymm
    · have h1 : pCoreOf 2 M ≤ (S : Subgroup G) :=
        A7.pCoreOf_le_of_le_normalizer S (hH.normalizes.trans Subgroup.le_normalizer)
      rw [← hQV]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (sup_le (Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
          (hH.normalizes.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hVL.trans Subgroup.le_normalizer) hMV hV2g
  have hV1 : V ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hVn
    rcases hn with rfl | rfl | rfl <;> norm_num at hVn
  have hev0 := hH.qtke.2.1 M ⟨V, hV1, hV2g, le_antisymm hMV hNVM⟩ ⟨S, hH.normalizes⟩
  have hev : M ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rw [← hOM]
    exact hev0
  refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
  obtain ⟨⟨l, hl⟩, hlσ⟩ := (A4.mem_autOn_iff hLV).mp
    (htop ▸ Subgroup.mem_top (A4.actionOn V M hMV ⟨x, hx⟩))
  have hc : l⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have e := congrArg (fun σ : MulAut ↥V => ((σ ⟨v, hv⟩ : ↥V) : G)) hlσ
    simp only [A4.actionOn_apply_coe] at e
    calc v * (l⁻¹ * x) = l⁻¹ * (l * v * l⁻¹) * x := by group
      _ = l⁻¹ * (x * v * x⁻¹) * x := by rw [e]
      _ = l⁻¹ * x * v := by group
  have hlx := hVL (hev ⟨M.mul_mem (M.inv_mem (Subgroup.le_normalizer hl)) hx, hc⟩)
  rw [show x = l * (l⁻¹ * x) by group]
  exact L.mul_mem hl hlx

end CFSG.Quasithin.H13
