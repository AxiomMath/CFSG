module

public import CFSG.Quasithin.MS93.C134L32CorrMOne
public import CFSG.Quasithin.EmptyFaithful.S152YD
public import CFSG.Quasithin.EmptyFaithful.S152YG
public import CFSG.Quasithin.EmptyFaithful.ModETop
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtStage1469WProved
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4Proved
public import CFSG.Quasithin.EmptyFaithful.Gold14610Holds
public import CFSG.Quasithin.EmptyFaithful.ModA6Perm
public import CFSG.Quasithin.EmptyFaithful.ModA7Block
public import CFSG.Quasithin.EmptyFaithful.ModCPermIn
public import CFSG.Quasithin.EmptyFaithful.ModDTop
public import CFSG.Quasithin.EmptyFaithful.S14610QHat
public import CFSG.Quasithin.EmptyFaithful.S14610QW
public import CFSG.Quasithin.EmptyFaithful.SBd5UL

public section

namespace CFSG.Quasithin.S152Y

section Cases

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_c134_corrM {K R V W S : Subgroup G} {y : G} (d : L32Data K R V W S y) {i : ℕ}
    (hi : IsC134CaseM i (K ⊔ R) R K) :
    Nat.card (Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x}) ≤ 8 := by
  classical
  have hcl := d.closure_le
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => comm_of_sq d.Wsq ha hb
  have hWZ : W ≤ centerOf (c134Q (K ⊔ R) K) := fun a ha =>
    Subgroup.mem_inf.mpr ⟨d.WQ ha,
      Subgroup.mem_centralizer_iff.mpr fun q hq => (d.Wcent a ha q hq).symm⟩
  rcases i with _ | _ | _ | _ | _ | _ | n
  · exact hi.elim
  ·
    obtain ⟨-, n, F, hFfield, hFfin, hFc, hKN, α, hα, hαk, β, hβs, hβk, hβe⟩ := hi
    have hF2 : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj d.hq hFc ⟨hα, hαk⟩
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk]
      simp
    have hcard : Nat.card ↥(c134Q (K ⊔ R) K) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβinj, hβs⟩).toEquiv, card_mult_fin3, hF2]
      norm_num
    exact (Subgroup.card_le_of_le (hcl.trans d.WQ)).trans hcard.le
  ·
    obtain ⟨⟨n, F, hFfield, hFfin, α, hFc, hmod, hsum⟩, -⟩ := hi
    have hF2 : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj d.hq hFc hmod
    obtain ⟨α', β', hα's, hα'k, hβ's, hβ'k, hβ'e⟩ := normalize_via hF2 hmod.1 hsum
    let β'W : ↥W →* Multiplicative (Fin 2 → Vec3) := β'.comp (Subgroup.inclusion d.WQ)
    have hcoord : ∀ i : Fin 2, GCoord K W α' (coordHom β'W i) := by
      intro i
      refine ⟨d.Wnorm, fun a u v huv => ?_⟩
      exact hβ'e a (Subgroup.inclusion d.WQ u) (Subgroup.inclusion d.WQ v) huv i
    have hjoint : ∀ x : ↥W, coordHom β'W 0 x = 1 → coordHom β'W 1 x = 1 → x = 1 := by
      intro x h0 h1
      have e0 : Multiplicative.toAdd (β' (Subgroup.inclusion d.WQ x)) 0 = 0 :=
        congrArg Multiplicative.toAdd h0
      have e1 : Multiplicative.toAdd (β' (Subgroup.inclusion d.WQ x)) 1 = 0 :=
        congrArg Multiplicative.toAdd h1
      have hb : β' (Subgroup.inclusion d.WQ x) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i
        · exact e0
        · exact e1
      have hmem : Subgroup.inclusion d.WQ x ∈ β'.ker := hb
      rw [hβ'k] at hmem
      have h1 : Subgroup.inclusion d.WQ x = 1 := by simpa using hmem
      exact Subgroup.inclusion_injective d.WQ (h1.trans (map_one _).symm)
    exact g_afl2 d.Wsq (hcoord 0) (hcoord 1) hjoint d.vd d.hVW (card_map_sylow d.hS hα's)
  ·
    obtain ⟨⟨n, F, hFfield, hFfin, α, hFc, hmod, hZ, -⟩, -⟩ := hi
    have hF2 : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj d.hq hFc hmod
    obtain ⟨-, -, β, hβs, hβk, -⟩ := hZ
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk]
      simp
    have hcard : Nat.card ↥(centerOf (c134Q (K ⊔ R) K)) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβinj, hβs⟩).toEquiv, card_mult_fun, hF2]
      norm_num
    exact (Subgroup.card_le_of_le (hcl.trans hWZ)).trans hcard.le
  ·
    obtain ⟨⟨n, F, hFfield, hFfin, α, hFc, hmod, -, -, hU, -, -⟩, -⟩ := hi
    have hF2 : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj d.hq hFc hmod
    obtain ⟨hKN, -, β, hβs, hβk, -⟩ := hU
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβk]
      simp
    have hcard : Nat.card ↥(⁅centerOf (c134Q (K ⊔ R) K), K⁆) = 8 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβinj, hβs⟩).toEquiv, card_mult_fun, hF2]
      norm_num
    have hVU : V ≤ ⁅centerOf (c134Q (K ⊔ R) K), K⁆ := by
      intro v hv
      obtain ⟨v', hv', rfl⟩ := exists_commutator d.vd
        (fun a ha b hb => hWcomm a (d.hVW ha) b (d.hVW hb)) v hv
      have h1 : ⁅v', y⁆ ∈ ⁅centerOf (c134Q (K ⊔ R) K), K⁆ :=
        Subgroup.commutator_mem_commutator (hWZ (d.hVW hv')) d.vd.y_mem
      have h2 := Subgroup.inv_mem _ h1
      have e : y * v' * y⁻¹ * v'⁻¹ = ⁅v', y⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact h2
    have hcl' : Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x} ≤
        ⁅centerOf (c134Q (K ⊔ R) K), K⁆ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKN hk) z).mp (hVU hz)
    exact (Subgroup.card_le_of_le hcl').trans hcard.le
  ·
    obtain ⟨⟨α, hmod, hC2, hsum⟩, -⟩ := hi
    obtain ⟨α', β', hα's, hα'k, hβ's, hβ'k, hβ'e⟩ :=
      normalize_via (F := ZMod 2) (by simp) hmod.1 hsum
    let β'W : ↥W →* Multiplicative (Fin 1 → Vec3) := β'.comp (Subgroup.inclusion d.WQ)
    have hcoord : GCoord K W α' (coordHom β'W 0) := by
      refine ⟨d.Wnorm, fun a u v huv => ?_⟩
      exact hβ'e a (Subgroup.inclusion d.WQ u) (Subgroup.inclusion d.WQ v) huv 0
    have hker : ∀ x : ↥W, coordHom β'W 0 x = 1 → (x : G) ∈ c134CQ (K ⊔ R) K := by
      intro x h
      have e0 : Multiplicative.toAdd (β' (Subgroup.inclusion d.WQ x)) 0 = 0 :=
        congrArg Multiplicative.toAdd h
      have hb : β' (Subgroup.inclusion d.WQ x) = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        exact e0
      have hmem : Subgroup.inclusion d.WQ x ∈ β'.ker := hb
      rw [hβ'k] at hmem
      simpa [Subgroup.mem_subgroupOf] using hmem
    have hker3 : ∀ a b c : ↥W, coordHom β'W 0 a = 1 → coordHom β'W 0 b = 1 → coordHom β'W 0 c = 1 →
        a = b ∨ a = c ∨ b = c := by
      intro a b c ha hb hc
      rcases three_of_card_two hC2 (hker a ha) (hker b hb) (hker c hc) with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    have hkerfix : ∀ (k : ↥K) (x : ↥W), coordHom β'W 0 x = 1 → (k : G) * x * (k : G)⁻¹ = x := by
      intro k x hx
      have hxC : (x : G) ∈ c134CQ (K ⊔ R) K := hker x hx
      have hcen := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC).2) k k.2
      rw [mul_inv_eq_iff_eq_mul]
      exact hcen
    have htriv : ∀ k : ↥K, α' k = 1 → ∀ x ∈ W, (k : G) * x * (k : G)⁻¹ = x := by
      intro k hk x hx
      have hk' : k ∈ α'.ker := hk
      rw [hα'k, hmod.2] at hk'
      exact d.Wtriv k ⟨k, hk', rfl⟩ x hx
    exact g_afl1 d.Wsq hcoord hα's hker3 hkerfix htriv d.vd d.hVW (card_map_sylow d.hS hα's)
  · exact hi.elim

theorem card_le_of_c134_corr {K R V W S : Subgroup G} {y : G} (d : L32Data K R V W S y) {i : ℕ}
    (hi : MS93.IsC134CaseCorr i (K ⊔ R) R K) :
    Nat.card (Subgroup.closure {x : G | ∃ k ∈ K, ∃ z ∈ V, k * z * k⁻¹ = x}) ≤ 8 :=
  card_le_of_c134_corrM d hi.toCaseM

end Cases

section C134

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_c134Case_of_c27_corrM (hM : C134L32CorrM) {H R M K V : Subgroup G}
    (hq : IsLnTwoQuot K 3) (hC : C27Concl H R M K V) (hK : K ∈ cComp H)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) :
    ∃ i : ℕ, IsC134CaseM i (K ⊔ R) R K := by
  have hMSp : IsMSPair (K ⊔ R) R := SBd5.c27_caseG hq hC
  have hcomp : K ∈ cComp (K ⊔ R) := SBd5.mem_cComp_sup' hK hRN
  have hset : ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K R hRN
  obtain ⟨e⟩ := hq
  let α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hα : IsModO2Surj K α := by
    refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).ker = CFSG.pCore 2 ↥K
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  exact hM G (K ⊔ R) R K hMSp hcomp hset ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩

section Main

variable {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}

theorem card_conjClosure_K_le_corrM (hC27 : ASC27Statement G) (hM : C134L32CorrM)
    (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) K) ≤ 2 ^ 3 := by
  have S : Setting146 G T M := c.setting
  obtain ⟨hRad, hSyl⟩ := c23_of_facts c hsyl hLT
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  set R₁ : Subgroup G := pCoreOf 2 (i1Of1469 T M I) with hR₁
  have hKI : K ≤ I := hK.le
  have hKN : I ≤ Subgroup.normalizer (K : Set G) := hK.normal
  have hRN : R₁ ≤ Subgroup.normalizer (K : Set G) := hRad.1.trans hKN
  obtain ⟨e⟩ := exists_mulEquiv_of_isPSL hL32
  have hq : IsLnTwoQuot K 3 :=
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩
  have hqs : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (H13.isQuasisimple_sl_zmod_two (by norm_num)).1
  have hKc : K ∈ cComp I := mem_cComp_of_eq_oTwoUpper hK.eq_residual hqs
  have hct : CharTwo K := CharTwo.of_normal c.c4 hKI
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hKN)
  have hnot : ¬ K ≤ M ⊓ I := by
    intro hKM
    apply c.hI.1.2.2
    calc I = K ⊔ (T ⊓ I) := hK.eq_sup
      _ ≤ M := sup_le (hKM.trans inf_le_left) (inf_le_left.trans hTM)
  have hSQ := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.2
  have hyp : HypC23 I R₁ (M ⊓ I) :=
    { sqtk := (show SQTKGroup ↥I from ⟨hSQ.2, hSQ.1⟩)
      radical := hRad
      le := inf_le_right
      cgs := cgsIn_le_of_CGS_le' c.c1
      sylow := hSyl }
  have hC : C27Concl I R₁ (M ⊓ I) K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R₁))) :=
    c27Concl_of_statement hC27 hyp hKc hqs hct hnot hRN rfl
  obtain ⟨i, hi⟩ := exists_c134Case_of_c27_corrM hM hq hC hKc hRN
  obtain ⟨y, hyK, hyN, hyfpf, -⟩ := Setting146.exists_y_fpf c.toHyp14610 hLT
  have hyK' : y ∈ K := by rw [hK.eq_residual]; exact hyK
  have hS : IsSylowTwoOf ((T ⊓ I) ⊓ K) K := A4.isSylowTwoOf_inf_normal hsyl hKI hKN
  have hvd : GVData K (VZ T M) ((T ⊓ I) ⊓ K) y :=
    { card := S.hyp.rank_two
      S_le := inf_le_right
      S_norm := fun s hs => hMV (hTM hs.1.1)
      y_mem := hyK'
      y_norm := hyN
      y_fpf := hyfpf }
  have hAP : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 (K ⊔ R₁) :=
    (A4.omegaOneCenterOf_le _).trans (pCoreOf_le_pCoreOf_sup hRN)
  have d : L32Data K R₁ (VZ T M) (wOf1469 K) ((T ⊓ I) ⊓ K) y :=
    { hq := hq
      vd := hvd
      hS := hS
      hVW := hK.v_le_w
      WQ := Subgroup.commutator_mono hAP le_rfl
      Wsq := fun a ha => wOf1469_sq ha
      Wnorm := le_normalizer_wOf1469 K
      Wtriv := fun k hk x hx => wOf1469_comm_pCore hk hx
      Wcent := fun a ha q hq' => by
        have hqO : q ∈ pCoreOf 2 K := commutator_pCore_le hRN hq'
        have h := wOf1469_comm_pCore hqO ha
        exact (mul_inv_eq_iff_eq_mul.mp h).symm }
  calc Nat.card (conjClosure (VZ T M) K) ≤ 8 := card_le_of_c134_corrM d hi
    _ = 2 ^ 3 := by norm_num

end Main

end C134

end CFSG.Quasithin.S152Y

namespace CFSG.Quasithin

section Setting

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.card_conjClosure_K_le_corrM (hC27 : ASC27Statement G)
    (hM : C134L32CorrM)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) K) ≤ 2 ^ 3 :=
  S152Y.card_conjClosure_K_le_corrM hC27 hM c hsyl hLT hK hL32

theorem Setting146.facts14610_L32_proved_corrM (hC27 : ASC27Statement G)
    (hM : C134L32CorrM)
    {H : Subgroup G} {u : G} {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂)
    (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hL32 : IsPSL 3 2 1 (OTwoQuot K)) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 :=
  le_antisymm
    ((Subgroup.card_le_of_le (Setting146.conjClosure_I₂_le_conjClosure_K c.toHyp14610 hK)).trans
      (Setting146.card_conjClosure_K_le_corrM hC27 hM c hsyl hLT hK hL32))
    (Setting146.eight_le_card_conjClosure_I₂ c.toHyp14610)

end Setting

section Stage

open CFSG.Open CFSG.QuasithinUnique

theorem stage14610FiveW_of_narrow_inputs_H_corrM
    (h9 : Stage1469W) (hF618 : F6.TheoremF618Cat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hM : C134L32CorrM)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three) (h4 : Stage1463Four)
    (i11 : Input14610ListN)
    (i16a : Input14610PermFixedA6)
    (i16b : Input14610PermFixedA7) (i17c : Input14610PermA7Fixed) : Stage14610FiveW := by
  have i13 : Input14610Hat6 := input14610Hat6_proved
  have i16 : Input14610PermFixed := input14610PermFixed_of_narrow i16a i16b
  intro G _ _ T M H u S hH hu I hI hbig hrank I₂ hle hI₂ hs3 hgen hcent
  have c : Hyp14610 T M H u I I₂ :=
    ⟨S, hH, hu, hI, hbig, hrank, hle, hI₂, hs3, hgen, hcent⟩
  have hidx := (h1 G T M S H hH u hu).2.1
  have hN0 := h2 G T M S H hH u hu
  have hNu := (h4 G T M S H hH u hu).1
  obtain ⟨hsyl, hcases⟩ := isIStar_sylow_cases S hu hidx hN0 hNu hI
  have hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) :=
    h9 G T M H u S hH hu I hI hbig hrank
  have hN : tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) := (h1 G T M S H hH u hu).2.2.1
  have hV3 : ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G)) := (h3 G T M S H hH u hu).1
  have hc1 := S.facts14610_c1 hI hsyl hLT
  have hc2 := S.facts14610_c2 hI hsyl hgen hc1
  have hc3 := fun P hPI hPinv => Setting146.facts14610_c3 h9 h3 c hsyl hLT P hPI hPinv
  have hc4 := Setting146.facts14610_c4 hF618 input14610Four_proved c hsyl hLT hc2
  let cF : Facts14610 T M H u I I₂ := { c with c1 := hc1, c2 := hc2, c3 := hc3, c4 := hc4 }
  have hT := S.isGoldschmidtTripleIn_14610 c hsyl hLT
  have hF := S.f618Cat_14610 hF618 c hsyl hLT hc2
  have hK : Concl14610List T M I I₂ (oTwoUpper I) :=
    concl14610List_of_core cF hsyl hLT hT (i11 G T M H u I I₂ (hC27 G) cF hsyl hLT hT hF)
  rcases hK.shape with ⟨hL32, -⟩ | ⟨-, hHat | hG2 | hA6 | hA7⟩
  · exact Setting146.facts14610_L32_proved_corrM (hC27 G) hM cF hsyl hLT hK hL32
  · exact (Setting146.facts14610_hat6 i13 cF hK hHat.1).elim
  · exact Setting146.facts14610_G22_of_sylow cF hsyl hLT hK hG2.1
  · rcases hA6.2.2 with hW | hW
    · exact Setting146.facts14610_rank4_of_sylow cF hK hsyl (Or.inl hA6.1) hW
    · exact Setting146.facts14610_perm_of_sylow' i16 i17c cF hsyl hcases hLT hN hV3 hK
        (Or.inl ⟨hA6.1, hW⟩)
  · rcases hA7.2.2 with hW | hW
    · exact Setting146.facts14610_rank4_of_sylow cF hK hsyl (Or.inr hA7.1) hW
    · exact Setting146.facts14610_perm_of_sylow' i16 i17c cF hsyl hcases hLT hN hV3 hK
        (Or.inr ⟨hA7.1, hW⟩)

end Stage

section Proved

open CFSG.Open CFSG.QuasithinUnique

theorem stage14610FiveW_proved_corrM
    (h9 : Stage1469W) (hF618 : F6.TheoremF618Cat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hM : C134L32CorrM) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) : Stage14610FiveW :=
  stage14610FiveW_of_narrow_inputs_H_corrM h9 hF618 hC27 hM stage1463_one_proof h2 h3 h4
    (input14610ListN_of_listW input14610ListW_holds) input14610PermFixedA6_holds
    input14610PermFixedA7_holds input14610PermA7Fixed_holds

end Proved

section NoE9

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.E9P2L
open CFSG.Quasithin.EmptyFaithfulMultiple

theorem noE9Z4LargeBig_proved_corrM
    (h35 : Lemma1435) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (hD36 : D36)
    (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hcab : GoldschmidtCentralAbelianBound) (hE22 : E2.E22StatementNoN)
    (hF618 : F6.TheoremF618Cat) (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hM : C134L32CorrM) (h2' : Stage1463Two) (h3 : Stage1463Three) (h4 : Stage1463Four) :
    NoE9Z4LargeBig :=
  have h9 : Stage1469W := stage1469W_proved hA37 hA38 hA39 hE22 h2' h3 h4
  noE9Z4LargeBig_of_W h35 hA37 hA38 hD36 hD37 hD321 hI5 hD310 hD391 hI4 hcab h9
    (stage14610FiveW_proved_corrM h9 hF618 hC27 hM h2' h3 h4) h2' h3 h4

end NoE9

end CFSG.Quasithin
