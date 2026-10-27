module

public import CFSG.Quasithin.Background.F918V3S3Aux
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec3L4310Mod

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isMaxElemAbelian_map_conj_of_le {S A : Subgroup G} {g : G}
    (hle : A.map (MulAut.conj g).toMonoidHom ≤ S) (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian S (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨-, ⟨hc, hp⟩, hmax⟩ := hA
  refine ⟨hle, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, fun B hB hBe => ?_⟩
  · rcases x with ⟨_, a, ha, rfl⟩
    rcases y with ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    have hab : a * b = b * a := setLike_mul_comm ha hb
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    show (g * a * g⁻¹) ^ 2 = 1
    rw [conj_pow, hp a ha, mul_one, mul_inv_cancel]
  · have h1 := hmax B hB hBe
    rwa [← Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem not_le_H (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hIH : InM I H) :
    ¬ T ≤ H := by
  intro hTH
  have hO : pCoreOf 2 L ≤ T := c.hyp421.pCoreOf_L_le_T c.normal
  have hLH : L ≤ H :=
    c.L_le.trans (_root_.sup_le ((perfectCore_le _).trans inf_le_right) (hO.trans hTH))
  have hU := (c.hyp421.isUniqueM_sup h37 h38 h39).1
  have hHM : H = M := hU.2 H ⟨hIH.1, _root_.sup_le hLH hTH⟩
  exact c.not_le hHM.le

theorem inf_le_pCoreOf_I {Mm : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : pCoreOf 2 (L ⊔ T) ⊓ H ≤ pCoreOf 2 I := by
  have hsyl := (lemma_4_1_4_four (hy.hyp4_1_1 h37 h38 h39) hy.sigma hy.gammaStar c.inH
    c.not_le).1
  rw [c.conjClosure_eq] at hsyl
  set Hp := oTwoUpper (L ⊓ H) with hHp
  have hRX : pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T) ⊓ H :=
    le_inf c.R_le ((pCoreOf_le 2 I).trans c.inH.1)
  have hX2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T) ⊓ H) :=
    (pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left
  have hXC : pCoreOf 2 (L ⊔ T) ⊓ H ≤ centralizerSection H Hp (pCoreOf 2 Hp) := by
    intro y hy'
    obtain ⟨hyO, hyH⟩ := hy'
    rw [c.hyp421.pCoreOf_sup_eq c.normal] at hyO
    obtain ⟨-, hyM, hyL, hyO2, hyc⟩ := hyO
    have hyLH : y ∈ Subgroup.normalizer ((L ⊓ H : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxL, hxH⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hyL x).mp hxL,
          H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)⟩
      · rintro ⟨hxL, hxH⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hyL x).mpr hxL, ?_⟩
        have := H.mul_mem (H.mul_mem (H.inv_mem hyH) hxH) hyH
        simpa [mul_assoc] using this
    have hyHp : y ∈ Subgroup.normalizer (Hp : Set G) :=
      normalizer_le_normalizer_oTwoUpper _ hyLH
    refine ⟨hyH, hyHp, normalizer_le_normalizer_pCoreOf 2 Hp hyHp, fun x hx => ?_⟩
    have hxL : x ∈ L := (oTwoUpper_le _ hx).1
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := hyc x hxL
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ Hp := by
      have h3 : y * x⁻¹ * y⁻¹ ∈ Hp := (Subgroup.mem_normalizer_iff.mp hyHp x⁻¹).mp (Hp.inv_mem hx)
      have := Hp.mul_mem hx h3
      simpa [mul_assoc] using this
    have hle : pCoreOf 2 L ⊓ Hp ≤ pCoreOf 2 Hp :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun g hg => mem_normalizer_inf
          ((normalizer_le_normalizer_pCoreOf 2 L)
            (Subgroup.le_normalizer ((oTwoUpper_le _ hg).1)))
          (Subgroup.le_normalizer hg))
        ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    exact hle ⟨h1, h2⟩
  exact (hsyl.eq_of_le hRX hXC hX2).le

theorem map_conj_pCoreOf_I {Mm : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {t : G} (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G)) :
    (pCoreOf 2 I).map (MulAut.conj t).toMonoidHom = pCoreOf 2 I := by
  have hle : (pCoreOf 2 I).map (MulAut.conj t).toMonoidHom ≤ pCoreOf 2 I := by
    rintro _ ⟨r, hr, rfl⟩
    refine c.inf_le_pCoreOf_I hy h37 h38 h39 ⟨?_, ?_⟩
    · have htO : t ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
        le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_right ht)
      exact (Subgroup.mem_normalizer_iff.mp htO r).mp (c.R_le hr)
    · have hrTH : r ∈ T ⊓ H := ⟨(hy.R_le hr).1, (pCoreOf_le 2 I).trans c.inH.1 hr⟩
      exact ((Subgroup.mem_normalizer_iff.mp htN r).mp hrTH).2
  exact Subgroup.eq_of_le_of_card_ge hle
    (Nat.card_congr ((pCoreOf 2 I).equivMapOfInjective _ (MulAut.conj t).injective).toEquiv).le

omit c in
theorem normalizer_pCoreOf_K_eq (hIH : InM I H) (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hK2 : pCoreOf 2 K ≠ ⊥) : Subgroup.normalizer (pCoreOf 2 K : Set G) = H :=
  hIH.1.2 _ ⟨pCoreOf 2 K, hK2, pCoreOf_isPGroup 2 K, rfl⟩
    (hKH.trans (normalizer_le_normalizer_pCoreOf 2 K))

theorem perfectCore_le_normalizer_pCoreOf_I :
    perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
  set LH := perfectCore (L ⊓ H) with hLH
  set R := pCoreOf 2 I with hR
  have hcc : conjClosure LH (H ⊓ M) = LH :=
    le_antisymm (conjClosure_le fun _ hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (c.LH_normal hk) z).mp hz) (le_conjClosure LH (H ⊓ M))
  have hsyl := c.hypC28.sylow
  rw [hcc] at hsyl
  set C := centralizerSection (H ⊓ M) LH (pCoreOf 2 LH) with hC
  have hLHM : LH ≤ H ⊓ M := le_of_mem_cComp c.LH_mem
  have hOC : pCoreOf 2 LH ≤ C := by
    intro o ho
    have hoLH : o ∈ LH := pCoreOf_le 2 LH ho
    refine ⟨hLHM hoLH, Subgroup.le_normalizer hoLH,
      normalizer_le_normalizer_pCoreOf 2 LH (Subgroup.le_normalizer hoLH), fun x hx => ?_⟩
    have h1 : x * o * x⁻¹ ∈ pCoreOf 2 LH :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 LH hx) o).mp ho
    exact (pCoreOf 2 LH).mul_mem h1 ((pCoreOf 2 LH).inv_mem ho)
  have hON : ((pCoreOf 2 LH).subgroupOf C).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro y hy
    exact hy.2.2.1
  have hOR : pCoreOf 2 LH ≤ R :=
    le_of_normal_of_isSylowTwoOf hsyl hOC hON (pCoreOf_isPGroup 2 LH)
  have key : ∀ x ∈ LH, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    have hrC : r ∈ C := hsyl.1 hr
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 LH := hrC.2.2.2 x hx
    have h2 : x * r * x⁻¹ = (x * r * x⁻¹ * r⁻¹) * r := by group
    rw [h2]
    exact R.mul_mem (hOR h1) hr
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key x hx r, fun hr => ?_⟩
  have := key x⁻¹ (LH.inv_mem hx) _ hr
  simpa [mul_assoc] using this

theorem not_isC134Case2_core (hKG : SL3ParabolicAutFact) (h136 : LemmaC136) {Mm : Subgroup G}
    (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hIH : InM I H) (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (hMS : IsMSPair (K ⊔ pCoreOf 2 I) (pCoreOf 2 I))
    {m : ℕ} {F : Type} [Field F] [Fintype F] {V₁ : Subgroup G} (hm : 1 < m)
    (hF : Fintype.card F = 2 ^ m) (hstab : IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁)
    (hCRK : (K ⊔ pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    ¬ IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K := by
  classical
  intro h2
  obtain ⟨⟨n₂, F₂, _, _, α, hF₂, hαm, hN⟩, -⟩ := (h2 : IsC134Case2 _ _ _)
  set R := pCoreOf 2 I with hRdef
  set U := pCoreOf 2 K with hU
  set LH := perfectCore (L ⊓ H) with hLHdef
  have hKcc : K ∈ cComp H := c.K_mem
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKcc
  have hKH' : K ≤ H := le_of_mem_cComp hKcc
  have hRH : R ≤ H := (pCoreOf_le 2 I).trans c.inH.1
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hKH
  have hLHK : LH ≤ K := c.LH_le
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK
  obtain ⟨S₀, hS₀, hRS₀⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge
    (le_sup_right : R ≤ K ⊔ R) (pCoreOf_isPGroup 2 I)
  have hQX : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (K : Set G) →
      c134Q (K ⊔ X) K = ⁅U, K⁆ := by
    intro X hX
    have hKXN : K ⊔ X ≤ Subgroup.normalizer (K : Set G) :=
      _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hX
    have hUO : U ≤ pCoreOf 2 (K ⊔ X) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
        (hKXN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
    refine le_antisymm ?_ (Subgroup.commutator_mono hUO le_rfl)
    have h1 := (commutator_le_pCoreOf_of_le hperf hX le_rfl).1
    have hON : pCoreOf 2 (K ⊔ X) ≤ Subgroup.normalizer (K : Set G) :=
      (pCoreOf_le 2 _).trans hKXN
    show ⁅pCoreOf 2 (K ⊔ X), K⁆ ≤ ⁅U, K⁆
    rw [commutator_eq_commutator_commutator_of_perfect' hperf hON]
    exact Subgroup.commutator_mono h1 le_rfl
  have hQU : c134Q (K ⊔ R) K ≤ U := (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1
  obtain ⟨W, hWle, α', β', hnat, hline1, hMK⟩ := hstab
  obtain ⟨hKW, hα', hkerα', hβ', hβker', hequiv'⟩ := hnat
  obtain ⟨hV1W, W', hW', hW'iff⟩ := hline1
  have hLHN : LH ≤ Subgroup.normalizer (V₁ : Set G) := by
    have : LH ≤ H ⊓ M ⊓ K := le_inf (le_of_mem_cComp c.LH_mem) hLHK
    rw [hMK] at this
    exact this.trans inf_le_right
  set A₀ := LH.subgroupOf K with hA₀
  have hA₀map : A₀.map K.subtype = LH := by
    rw [hA₀, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hLHK
  have hLHperf : ⁅LH, LH⁆ = LH := perfectCore_perfect _
  have hA₀perf : ⁅A₀, A₀⁆ = A₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hA₀map, hLHperf]
  set Y₀ := A₀.map α' with hY₀
  have hY₀perf : ⁅Y₀, Y₀⁆ = Y₀ := by rw [hY₀, ← Subgroup.map_commutator, hA₀perf]
  have hstab₀ : ∀ y ∈ Y₀, ∀ w ∈ W',
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W' := by
    rintro _ ⟨l, hl, rfl⟩ w hw
    obtain ⟨u, hu⟩ := hβ' (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V₁ := (hW'iff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    have hlN : (l : G) ∈ Subgroup.normalizer (V₁ : Set G) := hLHN hl
    let v : ↥W := ⟨l * u * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW l.2) u).mp u.2⟩
    have h1 := hequiv' l u v rfl
    rw [hu, toAdd_ofAdd] at h1
    have h2 : (v : G) ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hlN u).mp huV
    have h3 := (hW'iff v).mp h2
    rw [h1] at h3
    exact h3
  have hY₀ne : Y₀ ≠ ⊥ := by
    intro hbot
    apply ne_bot_of_mem_cComp c.LH_mem
    apply eq_bot_of_perfect_of_isPGroup_two hLHperf
    refine (pCoreOf_isPGroup 2 K).to_le ?_
    intro l hl
    have h1 : α' ⟨l, hLHK hl⟩ ∈ Y₀ := ⟨⟨l, hLHK hl⟩, hl, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨l, hLHK hl⟩ : ↥K) ∈ α'.ker := h1
    rw [hkerα'] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hPnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
        g ∈ Subgroup.normalizer ((Y₀ : Subgroup ↥(StatedSL 3 F)) : Set ↥(StatedSL 3 F)) := by
    intro g hg
    obtain ⟨k', rfl⟩ := hα' g
    have hk'V : (k' : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ W := hV1W hv
      let vW : ↥W := ⟨v, hvW⟩
      let v' : ↥W := ⟨k' * v * (k' : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW k'.2) v).mp hvW⟩
      have h1 := hequiv' k' vW v' rfl
      have h2 : Multiplicative.toAdd (β' vW) ∈ W' := (hW'iff vW).mp hv
      exact (hW'iff v').mpr (by rw [h1]; exact hg _ h2)
    have hk'HM : (k' : G) ∈ H ⊓ M := by
      have : (k' : G) ∈ K ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨k'.2, hk'V⟩
      rw [← hMK] at this
      exact this.1
    have hk'L : (k' : G) ∈ Subgroup.normalizer (LH : Set G) := c.LH_normal hk'HM
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨k' * l * k'⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hk'L l).mp hl
    · rintro ⟨l, hl, hle⟩
      refine ⟨k'⁻¹ * l * k', ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk'L) l).mp hl
        rw [inv_inv] at this
        exact this
      · rw [map_mul, map_mul, map_inv, hle]
        group
  have hcard : Fintype.card F = Fintype.card F₂ :=
    card_eq_of_card_statedSL_eq ((card_modO2_of_surjective α' hα' hkerα').symm.trans
      (card_modO2_of_surjective α hαm.1 hαm.2))
  have hn₂ : 2 ≤ n₂ := by
    have h1 : 2 ^ m = 2 ^ n₂ := hF.symm.trans (hcard.trans hF₂)
    rw [← Nat.pow_right_injective (le_refl 2) h1]
    omega
  obtain ⟨cc, hc0, hc1, hcc⟩ := exists_good_scalar (by omega : 2 ≤ m) (hcard.symm.trans hF)
  obtain ⟨hUC, hUmax, A, hAK, hAmax, hAS, hAcard⟩ := h136 G (K ⊔ R) R K S₀ n₂ F₂ α hMS
    (mem_cComp_sup hKcc hRK) (Subgroup.coe_mul_of_right_le_normalizer_left K R hRK) hKRN hn₂
    hF₂ hαm hS₀ hCRK hN
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    have hxC : x ∈ (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) := by rw [hUC]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp hxC.2 y hy).symm
  have hUQ : U ≤ c134Q (K ⊔ R) K := by
    intro x hx
    have hxker : ∀ a : ↥K, α a = 1 → (a : G) * x = x * a := by
      intro a ha
      have h1 : a ∈ α.ker := ha
      rw [hαm.2] at h1
      exact hUab _ ((mem_pCoreOf_iff' a).mpr h1) x hx
    have hxK : ∀ g ∈ K, x⁻¹ * (g * x * g⁻¹) ∈ c134Q (K ⊔ R) K := by
      intro g hg
      rw [hQX R hRK]
      have h1 : ⁅x⁻¹, g⁆ ∈ ⁅U, K⁆ := Subgroup.commutator_mem_commutator (U.inv_mem hx) hg
      have e : ⁅x⁻¹, g⁆ = x⁻¹ * (g * x * g⁻¹) := by
        simp only [commutatorElement_def, inv_inv]; group
      rwa [e] at h1
    obtain ⟨n₁, hn₁Q, hxn⟩ :=
      exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hαm.1 hN hxker hxK
    have h1 : x * n₁ ∈ (K ⊔ R) ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨Subgroup.mem_sup_left (pCoreOf_le 2 K (U.mul_mem hx (hQU hn₁Q))), hxn⟩
    rw [hCRK] at h1
    have h3 : x = n₁⁻¹ := eq_inv_of_mul_eq_one_left (Subgroup.mem_bot.mp h1)
    rw [h3]
    exact (c134Q (K ⊔ R) K).inv_mem hn₁Q
  have hUeq : U = c134Q (K ⊔ R) K := le_antisymm hUQ hQU
  rw [← hUeq] at hN
  obtain ⟨hKU, -, β, hβ, hβker, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hUH : H ≤ Subgroup.normalizer (U : Set G) :=
    hKH.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hUne : U ≠ ⊥ := by
    intro hU0
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ _ => (1 : F₂))
    have key : ∀ x : G, x ∈ U → x = 1 := by
      rw [hU0]
      exact fun x hx => Subgroup.mem_bot.mp hx
    have hu1 : u = 1 := Subtype.ext (key u u.2)
    rw [hu1, map_one] at hu
    have h1 := congrFun (congrFun (congrArg Multiplicative.toAdd hu) 0) 0
    exact one_ne_zero h1.symm
  have hNU : Subgroup.normalizer (U : Set G) = H := normalizer_pCoreOf_K_eq hIH hKH hUne
  have hUR : U ≤ R := by
    have h5 := (lemma_4_1_4_five (hy.hyp4_1_1 h37 h38 h39) hy.sigma hy.gammaStar c.inH
      c.not_le).2.2
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH') hUH
      (pCoreOf_isPGroup 2 K)).trans (h5.1.trans h5.2)
  have hTH : T ⊓ H < T := lt_of_le_of_ne inf_le_left fun heq =>
    c.not_le_H h37 h38 h39 hIH (heq ▸ inf_le_right)
  obtain ⟨t, htT, htN, htS⟩ := exists_mem_normalizer_not_mem c.hyp421.sylow.1 hTH
  have htH : t ∉ H := fun h => htS ⟨htT, h⟩
  have hRt : R.map (MulAut.conj t).toMonoidHom = R := c.map_conj_pCoreOf_I hy h37 h38 h39 htT htN
  have htR : t ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_of_map_conj_le hRt.le
  have htL : t ∈ Subgroup.normalizer (L : Set G) := c.normal (c.hyp421.T_le htT)
  have hmaxR : ∀ {B : Subgroup G} {g : G}, IsMaxElemAbelian S₀ B → B ≤ R →
      g ∈ Subgroup.normalizer (R : Set G) →
        IsMaxElemAbelian S₀ (B.map (MulAut.conj g).toMonoidHom) := by
    intro B g hB hBR hg
    refine isMaxElemAbelian_map_conj_of_le ?_ hB
    rintro _ ⟨b, hb, rfl⟩
    exact hRS₀ ((Subgroup.mem_normalizer_iff.mp hg b).mp (hBR hb))
  have hUtne : U.map (MulAut.conj t).toMonoidHom ≠ U := by
    intro heq
    apply htH
    rw [← hNU]
    exact mem_normalizer_of_map_conj_le heq.le
  have hUtA : U.map (MulAut.conj t).toMonoidHom = A :=
    (hAS _ (hmaxR hUmax hUR htR)).resolve_left hUtne
  have hAR : A ≤ R := by
    rw [← hUtA, ← hRt]
    exact Subgroup.map_mono hUR
  have hAt : A.map (MulAut.conj t).toMonoidHom = U := by
    rcases hAS _ (hmaxR hAmax hAR htR) with h | h
    · exact h
    · exfalso
      have h1 : A = U :=
        Subgroup.map_injective (MulAut.conj t).injective (h.trans hUtA.symm)
      exact hUtne (hUtA.trans h1)
  have hAU' : A ≠ U := fun h => hUtne (hUtA.trans h)
  have hLHR : LH ≤ Subgroup.normalizer (R : Set G) := c.perfectCore_le_normalizer_pCoreOf_I
  have hLHU : LH ≤ Subgroup.normalizer (U : Set G) := hLHK.trans (le_normalizer_pCoreOf 2 K)
  have hLA : LH ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    rcases hAS _ (hmaxR hAmax hAR (hLHR hx)) with h | h
    · exfalso
      apply hAU'
      have hUx : U.map (MulAut.conj x).toMonoidHom = U :=
        map_conj_eq_of_mem_normalizer (hLHU hx)
      exact Subgroup.map_injective (MulAut.conj x).injective (h.trans hUx.symm)
    · exact mem_normalizer_of_map_conj_le h.le
  have htLH : t ∈ Subgroup.normalizer (LH : Set G) := by
    apply mem_normalizer_of_map_conj_le
    have hLHt : ⁅LH.map (MulAut.conj t).toMonoidHom, LH.map (MulAut.conj t).toMonoidHom⁆ =
        LH.map (MulAut.conj t).toMonoidHom := by
      rw [← Subgroup.map_commutator, hLHperf]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hLHt
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp htL x).mp (perfectCore_le _ hx).1, ?_⟩
    rw [← hNU]
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨u, hu, rfl⟩
    rw [← hAt] at hu ⊢
    obtain ⟨a, ha, rfl⟩ := hu
    refine ⟨x * a * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hLA hx) a).mp ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  let cU : ↥K → ↥U → ↥U := fun g u =>
    ⟨g * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU g.2) u).mp u.2⟩
  have hcU : ∀ (g : ↥K) (u : ↥U) (i : Fin 2),
      Multiplicative.toAdd (β (cU g u)) i =
        ((α g : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
          (Multiplicative.toAdd (β u) i) := by
    intro g u i
    have h := hβeq g u (cU g u) rfl i
    simpa [moduleAct] using h
  let C₀ : Submodule F₂ (Fin 3 → F₂) :=
    { carrier := {x | ∀ a : ↥K, (a : G) ∈ A →
        ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [Matrix.mulVec_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => Matrix.mulVec_zero _
      smul_mem' := fun r x hx a ha => by rw [Matrix.mulVec_smul, hx a ha] }
  have hmemC₀ : ∀ x, x ∈ C₀ ↔ ∀ a : ↥K, (a : G) ∈ A →
      ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x = x := fun _ => Iff.rfl
  have hcentA : ∀ u : ↥U, (∀ i, Multiplicative.toAdd (β u) i ∈ C₀) →
      (u : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro u hu
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have haK : a ∈ K := hAK ha
    have h1 : cU ⟨a, haK⟩ u = u := by
      apply hβinj
      apply Multiplicative.toAdd.injective
      funext i
      rw [hcU]
      exact (hmemC₀ _).mp (hu i) ⟨a, haK⟩ ha
    have h2 : a * u * a⁻¹ = u := congrArg Subtype.val h1
    calc a * (u : G) = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h2]
  have hAU : ¬ A ≤ U := fun hle =>
    hAU' (Subgroup.eq_of_le_of_card_ge hle (hAmax.2.2 U hUmax.1 hUmax.2.1))
  have hdim : Module.finrank F₂ C₀ = 2 := by
    have hcoord : ∀ (u : ↥U), (u : G) ∈ A → ∀ i, Multiplicative.toAdd (β u) i ∈ C₀ := by
      intro u huA i
      refine (hmemC₀ _).mpr fun a ha => ?_
      have h1 : cU a u = u := by
        apply Subtype.ext
        show (a : G) * u * (a : G)⁻¹ = u
        have := hAmax.2.1.1
        rw [setLike_mul_comm ha huA, mul_inv_cancel_right]
      rw [← hcU, h1]
    let φ : ↥(A ⊓ U) → (Fin 2 → ↥C₀) := fun x i =>
      ⟨Multiplicative.toAdd (β ⟨x, x.2.2⟩) i, hcoord ⟨x, x.2.2⟩ x.2.1 i⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : β ⟨x, x.2.2⟩ = β ⟨y, y.2.2⟩ := by
        apply Multiplicative.toAdd.injective
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      exact Subtype.ext (congrArg (fun z : ↥U => (z : G)) (hβinj h1))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [hAcard, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := ↥C₀),
      Module.card_eq_pow_finrank (K := F₂) (V := ↥C₀), hF₂, ← pow_mul, ← pow_mul] at h1
    have hd3 : Module.finrank F₂ C₀ ≤ 3 := by
      have := Submodule.finrank_le C₀
      rwa [Module.finrank_fin_fun] at this
    have hd2 : 2 ≤ Module.finrank F₂ C₀ := by
      have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
      by_contra hlt
      have h3 : Module.finrank F₂ C₀ ≤ 1 := by omega
      have h4 : n₂ * (Module.finrank F₂ C₀ * 2) ≤ n₂ * 2 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rcases Nat.lt_or_ge (Module.finrank F₂ C₀) 3 with h | h
    · omega
    · exfalso
      have htop : C₀ = ⊤ := Submodule.eq_top_of_finrank_eq (by
        rw [Module.finrank_fin_fun]; omega)
      apply hAU
      intro a ha
      have haC : a ∈ (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) := by
        refine ⟨Subgroup.mem_sup_left (hAK ha), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
        have h2 := hcentA ⟨u, hu⟩ (fun i => by rw [htop]; trivial)
        exact (Subgroup.mem_centralizer_iff.mp h2 a ha).symm
      rw [hUC] at haC
      exact haC
  set Y₁ : Subgroup (GL (Fin 3) F₂) := (A₀.map α).map (StatedSL 3 F₂).subtype with hY₁
  have hY₁perf : ⁅Y₁, Y₁⁆ = Y₁ := by
    rw [hY₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hA₀perf]
  have hY₁stab : ∀ y ∈ Y₁, ∀ x ∈ C₀, (y : Matrix (Fin 3) (Fin 3) F₂).mulVec x ∈ C₀ := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩ x hx
    refine (hmemC₀ _).mpr fun a ha => ?_
    have hl' : (l : G) ∈ LH := hl
    have hla : ((l⁻¹ * a * l : ↥K) : G) ∈ A := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLA hl')) a).mp ha
      simpa [mul_assoc] using h1
    have h2 : α a * α l = α l * α (l⁻¹ * a * l) := by
      rw [map_mul, map_mul, map_inv]; group
    have h3 := congrArg (fun g : ↥(StatedSL 3 F₂) =>
      ((g : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂)) h2
    simp only [Subgroup.coe_mul, Units.val_mul] at h3
    show ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
        (((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x) =
      ((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x
    rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, (hmemC₀ x).mp hx _ hla]
  have hULC : ⁅U, LH⁆ ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlK : l ∈ K := hLHK hl
    let w : ↥U := ⟨u, hu⟩ * cU ⟨l, hlK⟩ ⟨u, hu⟩⁻¹
    have hw : (w : G) = ⁅u, l⁆ := by
      show u * (l * u⁻¹ * l⁻¹) = u * l * u⁻¹ * l⁻¹
      group
    rw [← hw]
    refine hcentA w fun i => ?_
    have hyY : ((α ⟨l, hlK⟩ : ↥(StatedSL 3 F₂)) : GL (Fin 3) F₂) ∈ Y₁ :=
      ⟨α ⟨l, hlK⟩, ⟨⟨l, hlK⟩, hl, rfl⟩, rfl⟩
    have h1 := mulVec_sub_mem_of_perfect C₀ hdim Y₁ hY₁perf hY₁stab hyY
      (Multiplicative.toAdd (β ⟨u, hu⟩) i)
    have h2 : Multiplicative.toAdd (β w) i = -(((α ⟨l, hlK⟩ : GL (Fin 3) F₂) :
        Matrix (Fin 3) (Fin 3) F₂).mulVec (Multiplicative.toAdd (β ⟨u, hu⟩) i) -
          Multiplicative.toAdd (β ⟨u, hu⟩) i) := by
      show Multiplicative.toAdd (β (⟨u, hu⟩ * cU ⟨l, hlK⟩ ⟨u, hu⟩⁻¹)) i = _
      rw [map_mul, toAdd_mul, Pi.add_apply, hcU, map_inv, toAdd_inv, Pi.neg_apply,
        Matrix.mulVec_neg]
      abel
    rw [h2]
    exact C₀.neg_mem h1
  have hALU : ⁅A, LH⁆ ≤ U := by
    have h1 : ⁅A, LH⁆ = (⁅U, LH⁆).map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_commutator, hUtA, map_conj_eq_of_mem_normalizer htLH]
    rw [h1]
    rintro _ ⟨w, hw, rfl⟩
    have hwU : w ∈ U := commutator_le_left_of_le_normalizer hLHU hw
    have hwC := hULC hw
    show t * w * t⁻¹ ∈ U
    have hmem : t * w * t⁻¹ ∈ (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨Subgroup.mem_sup_left (hAK (by rw [← hUtA]; exact ⟨w, hwU, rfl⟩)), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [← hAt] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have hwb := Subgroup.mem_centralizer_iff.mp hwC b hb
      show t * b * t⁻¹ * (t * w * t⁻¹) = t * w * t⁻¹ * (t * b * t⁻¹)
      calc t * b * t⁻¹ * (t * w * t⁻¹) = t * (b * w) * t⁻¹ := by group
        _ = t * (w * b) * t⁻¹ := by rw [hwb]
        _ = t * w * t⁻¹ * (t * b * t⁻¹) := by group
    rw [hUC] at hmem
    exact hmem
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ U := by
    by_contra h
    push Not at h
    exact hAU h
  have haK : a ∈ K := hAK haA
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hAmax.2.1.2 a haA
  have haL : ∀ l ∈ LH, ⁅a, l⁆ ∈ pCoreOf 2 K := fun l hl =>
    hALU (Subgroup.commutator_mem_commutator haA hl)
  have haKK := commutator_mem_pCoreOf_of_involution hKG (by omega : 2 ≤ m) hF hα' hkerα' hW'
    hY₀ne hY₀perf hstab₀ hPnorm (Subgroup.le_normalizer haK) ha2 haL
  have hcent : ∀ γ : ↥(StatedSL 3 F), α' ⟨a, haK⟩ * γ = γ * α' ⟨a, haK⟩ := by
    intro γ
    obtain ⟨k, rfl⟩ := hα' γ
    have h1 := haKK k k.2
    have h2 : α' (⟨a, haK⟩ * k * (⟨a, haK⟩ : ↥K)⁻¹ * k⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hkerα', ← mem_pCoreOf_iff']
      simpa [commutatorElement_def] using h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc α' ⟨a, haK⟩ * α' k =
          (α' ⟨a, haK⟩ * α' k * (α' ⟨a, haK⟩)⁻¹ * (α' k)⁻¹) * (α' k * α' ⟨a, haK⟩) := by
          group
      _ = α' k * α' ⟨a, haK⟩ := by rw [h2, one_mul]
  set Ma := ((α' ⟨a, haK⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hMa
  have hscal : Ma ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun ts => ?_
    have h1 := hcent (specialLinearGroupEquivStatedSL 3 F ts.toSpecialLinearGroup)
    have h2 := congrArg (fun g : ↥(StatedSL 3 F) =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, specialLinearGroupEquivStatedSL_coe,
      Matrix.TransvectionStruct.toSpecialLinearGroup_coe] at h2
    exact h2.symm
  obtain ⟨r, hr⟩ := hscal
  have hMa2 : Ma * Ma = 1 := by
    have h1 : α' ⟨a, haK⟩ * α' ⟨a, haK⟩ = 1 := by
      rw [← map_mul]
      convert map_one α'
      exact Subtype.ext ha2
    have h2 := congrArg (fun g : ↥(StatedSL 3 F) =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
    simpa using h2
  have hdet : Ma.det = 1 := by
    obtain ⟨γ, hγ⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective (α' ⟨a, haK⟩)
    have h1 : Ma = (γ : Matrix (Fin 3) (Fin 3) F) := by
      rw [hMa, ← hγ]
      exact specialLinearGroupEquivStatedSL_coe 3 F γ
    rw [h1]
    exact γ.2
  rw [← hr] at hMa2 hdet
  have hr2 : r * r = 1 := by
    have h1 := congrFun (congrFun hMa2 0) 0
    simpa [Matrix.scalar_apply] using h1
  have hr3 : r ^ 3 = 1 := by
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  have hr1 : r = 1 := by
    have h1 : r ^ 3 = r * (r * r) := by ring
    rw [h1, hr2, mul_one] at hr3
    exact hr3
  have hα'a : α' ⟨a, haK⟩ = 1 := by
    apply Subtype.ext
    apply Units.ext
    show Ma = 1
    rw [← hr, hr1, map_one]
  have h1 : (⟨a, haK⟩ : ↥K) ∈ α'.ker := hα'a
  rw [hkerα'] at h1
  exact haU ((mem_pCoreOf_iff' _).mpr h1)

theorem c41Case3_of_isC134Case2 (h2 : IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K) :
    C41Conclusion H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∧
      C41Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K := by
  classical
  obtain ⟨⟨n₂, F₂, _, _, α, hF₂, hαm, hN⟩, -⟩ := (h2 : IsC134Case2 _ _ _)
  have hcardK : Nat.card (ModO2 K) =
      (2 ^ n₂) ^ 3 * (((2 ^ n₂) ^ 2 - 1) * ((2 ^ n₂) ^ 3 - 1)) := by
    rw [card_modO2_of_surjective α hαm.1 hαm.2, card_statedSL_three, hF₂]
  rcases c.described with ⟨hcomp, -⟩ | ⟨-, -, -, -, h41⟩
  ·
    exfalso
    set R := pCoreOf 2 I with hR
    have hKRH : K ⊔ R ≤ H := _root_.sup_le hcomp.1 ((pCoreOf_le 2 I).trans c.inH.1)
    have hle : ⁅K, pCoreOf 2 (K ⊔ R)⁆ ≤ pCoreOf 2 (K ⊔ R) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp
        (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R)))
    have hsolv : Group.IsSolvable ↥⁅K, pCoreOf 2 (K ⊔ R)⁆ := by
      have hp : IsPGroup 2 ↥⁅K, pCoreOf 2 (K ⊔ R)⁆ := (pCoreOf_isPGroup 2 (K ⊔ R)).to_le hle
      have := hp.isNilpotent
      infer_instance
    have h0 := F918V3S3.commutator_eq_bot_of_isSolvable hcomp ((pCoreOf_le 2 _).trans hKRH) hsolv
    have hQ : c134Q (K ⊔ R) K = ⊥ := by
      show ⁅pCoreOf 2 (K ⊔ R), K⁆ = ⊥
      rw [Subgroup.commutator_comm, h0]
    obtain ⟨-, -, β, hβ, -, -⟩ := hN
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ _ => (1 : F₂))
    have key : ∀ x : G, x ∈ c134Q (K ⊔ R) K → x = 1 := by
      rw [hQ]
      exact fun x hx => Subgroup.mem_bot.mp hx
    have hu1 : u = 1 := Subtype.ext (key u u.2)
    rw [hu1, map_one] at hu
    have h1 := congrFun (congrFun (congrArg Multiplicative.toAdd hu) 0) 0
    exact one_ne_zero h1.symm
  · refine ⟨h41, ?_⟩
    rcases h41.2.2.2 with c1 | c2 | c3 | c4
    · exfalso
      obtain ⟨m, hm, -, -, ⟨-, α₁, hα₁, hker₁, -⟩, -, -⟩ := c1
      have h1 := card_modO2_of_surjective α₁ hα₁ hker₁
      rw [card_of_alt' (by omega) (MulEquiv.refl _), hcardK] at h1
      rcases hm with rfl | rfl
      · exact sl3_card_ne (N := (5 + 2).factorial / 2) (Or.inl (by decide)) h1
      · exact sl3_card_ne (N := (6 + 2).factorial / 2) (Or.inr (Or.inl (by decide))) h1
    · exfalso
      obtain ⟨⟨-, F₀, _, _, hF₀, α₀, hα₀, hker₀, -⟩, -⟩ := c2
      have h1 := card_modO2_of_surjective α₀ hα₀ hker₀
      rw [card_statedSp_two_of_card_four hF₀, hcardK] at h1
      exact sl3_card_ne_sp4 h1
    · exact c3
    · exfalso
      obtain ⟨h4, -, -⟩ := c4
      rcases h4 with h | h
      · exact sl3_card_ne (Or.inr (Or.inl rfl)) (hcardK.symm.trans (F420.card_of_l42 h))
      · exact sl3_card_ne (Or.inr (Or.inr rfl)) (hcardK.symm.trans (F420.card_of_l52 h))

end Conf4212

end CFSG.Quasithin.H13.Ch4
