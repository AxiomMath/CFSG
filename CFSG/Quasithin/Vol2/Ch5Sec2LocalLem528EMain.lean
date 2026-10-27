module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528UMain
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528ECfg
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EBlock
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528ESp4
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four
open CFSG.Quasithin.Vol2.Ch11.SecA CFSG.LieType.BorelTits
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem mem_of_commutator_mem_frattini [Finite G] {Kh : Subgroup G}
    (hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh) :
    ∀ y ∈ Kh, (∀ r ∈ pCoreOf 2 Kh, y * r * y⁻¹ * r⁻¹ ∈
      (frattini ↥(pCoreOf 2 Kh)).map (pCoreOf 2 Kh).subtype) → y ∈ pCoreOf 2 Kh := by
  intro y hy hfr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCoreOf 2 Kh) := pCoreOf_isPGroup 2 Kh
  set f := (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
    (frattini ↥(pCoreOf 2 Kh))).comp (pCoreConj Kh) with hf
  have hf2 : IsPGroup 2 (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥(pCoreOf 2 Kh))).ker :=
    CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hR2
  have hker2 : IsPGroup 2 f.ker := by
    intro g
    obtain ⟨n, hn⟩ := hf2 ⟨pCoreConj Kh g, g.2⟩
    have h1 : pCoreConj Kh ((g : ↥Kh) ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have h2 := mem_of_pCoreConj_eq_one hchar h1
    obtain ⟨k, hk⟩ := hR2 ⟨_, h2⟩
    refine ⟨n + k, Subtype.ext (Subtype.ext ?_)⟩
    have hk' : ((((g : ↥Kh) ^ 2 ^ n : ↥Kh) : G)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow] at hk'
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hk']
  have hnorm : Kh ≤ Subgroup.normalizer ((f.ker.map Kh.subtype : Subgroup G) : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [show (f.ker.map Kh.subtype).subgroupOf Kh = f.ker from
      Subgroup.comap_map_eq_self_of_injective Kh.subtype_injective _]
    exact MonoidHom.normal_ker _
  have hle := le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hnorm
    (hker2.map Kh.subtype)
  have hyk : (⟨y, hy⟩ : ↥Kh) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥(pCoreOf 2 Kh)) v
    rw [hf, MonoidHom.comp_apply,
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply, MulAut.one_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    obtain ⟨w, hw, hwe⟩ := hfr x x.2
    have hwe' : (w : G) = y * x * y⁻¹ * (x : G)⁻¹ := hwe
    have : pCoreConj Kh ⟨y, hy⟩ x / x = w := Subtype.ext (by
      rw [hwe', div_eq_mul_inv, Subgroup.coe_mul, pCoreConj_apply_coe, Subgroup.coe_inv])
    rw [this]
    exact hw
  exact hle ⟨⟨y, hy⟩, hyk, rfl⟩

theorem map_subgroupOf_eq_modO2Image {H Kh K : Subgroup G} (hKKh : K ≤ Kh) (hKhH : Kh ≤ H)
    (ρ : ↥Kh →* ↥(modO2Image H Kh))
    (hρ : ∀ k : ↥Kh, (ρ k : ↥H ⧸ CFSG.pCore 2 ↥H) = QuotientGroup.mk ⟨k, hKhH k.2⟩) :
    (K.subgroupOf Kh).map ρ = (modO2Image H K).subgroupOf (modO2Image H Kh) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hKhH k.2⟩, hk, (hρ k).symm⟩
  · rintro ⟨k, hk, hkx⟩
    refine ⟨⟨k, hKKh hk⟩, hk, Subtype.ext ?_⟩
    rw [hρ, ← hkx]
    rfl

theorem perfectCore_subgroupOf [Finite G] {P L : Subgroup G} (hPL : P ≤ L) :
    (perfectCore P).subgroupOf L = perfectCore (P.subgroupOf L) := by
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPL]
  rw [← hcore]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem exists_sl3Data (hSL : FactSL3SmallModule) [Finite G] {Y R : Subgroup G}
    [(R.subgroupOf Y).Normal] {m : ℕ} (hm : 2 ≤ m) (hRY : R ≤ Y) (hR2 : IsPGroup 2 R)
    (hRc : Nat.card R ≤ 2 ^ (3 * m + 1)) {X : Type} [Group X] (θ : ↥Y ⧸ R.subgroupOf Y ≃* X)
    (hX : IsPSL 3 2 m X ∨ IsSL3 (2 ^ m) X)
    (hfaith : ∀ y ∈ Y, (∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ (frattini ↥R).map R.subtype) → y ∈ R) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ m ∧
      ∃ (c : SL3E.SL3Data Y R F) (ε : X ≃* Matrix.SpecialLinearGroup (Fin 3) F),
        (∀ y : ↥Y, c.φ y = ε (θ (QuotientGroup.mk y))) ∧
        ∀ r : ↥R, c.ψ r = 1 → ∀ y ∈ Y, y * (r : G) * y⁻¹ = r := by
  obtain ⟨F, _, _, hF, he⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      (Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∨
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSL 3 F))) := by
    rcases hX with ⟨-, F, _, _, hF, he⟩ | ⟨F, _, _, hF, he⟩
    · exact ⟨F, inferInstance, inferInstance, hF, Or.inr he⟩
    · exact ⟨F, inferInstance, inferInstance, hF, Or.inl he⟩
  have hiso : Nonempty (↥Y ⧸ R.subgroupOf Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∨
      Nonempty (↥Y ⧸ R.subgroupOf Y ≃*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨θ.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨θ.trans e⟩
  obtain ⟨-, e, ψ, hψs, hψk, hψe⟩ := hSL G Y R F m hm hF hRY hR2 hRc hiso hfaith
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have hc2 : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  refine ⟨F, inferInstance, inferInstance, hc2, hF,
    { φ := e.toMonoidHom.comp (QuotientGroup.mk' (R.subgroupOf Y))
      surj := e.surjective.comp (QuotientGroup.mk'_surjective _)
      le := hRY
      ker := fun y => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquivClass.map_eq_one_iff,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      ψ := ψ
      ψsurj := hψs
      equiv := fun y r r' h => hψe y r r' h }, θ.symm.trans e, fun y => ?_,
    fun r hr y hy => hψk r hr y hy⟩
  simp

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem stmt5_2_8_U4_SL3_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (hSL : FactSL3SmallModule) : Stmt5_2_8_U4_SL3 := by
  intro G _ _ T M L V H B D L₂ n m hyp hnm h2n hαU hLb hKq hsp Kh hlt hKh hQR hL3 hPex
  classical
  obtain ⟨P, hP, hBP⟩ := hPex
  have h := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨-, hL₂K, hcore, -, -, -, hKT, halt⟩ := h526 G T M L V H B D L₂ n hyp
  obtain ⟨-, ⟨-, -, -, hSL1, hSL2, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set R := pCoreOf 2 Kh with hRdef
  have hKloc : quasithinIsLocal T K := hyp.isLocal_oTwoUpper hL₂K
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have e : Emb528 T K Kh := ⟨h.qtke, h.simple, h.nonabelian, h.sylow, hKloc, hKh.1, hlt.le, hTN⟩
  have hchar : Kh ⊓ Subgroup.centralizer (R : Set G) ≤ R := e.charTwo_Kh h37
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hST : sec52S M H ≤ T := h.pCoreOf_inf_le hyp.hStar.1.1
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 K
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 Kh
  have hRKh : R ≤ Kh := pCoreOf_le 2 Kh
  obtain ⟨eK⟩ := exists_sl2_of_isL2Quot hKq
  have hFc : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hsp' : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
    rw [← hcore]
    exact hsp
  obtain ⟨hQQ, hZq⟩ := commutator_eq_centerOf_of_isSpecialPow (by norm_num)
    (Nat.le_self_pow (by omega) 2) hsp
  have hQcard : Nat.card Q = (2 ^ m) ^ 5 := hsp.2.1
  have h4m : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTN.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hKSQ : K ⊔ sec52S M H ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 K) (hST.trans hTQ)
  have hRKS : R ≤ pCoreOf 2 (K ⊔ sec52S M H) := by
    have h1 := e.pCoreOf_le_pCoreOf_KT h37
    rwa [hKT] at h1
  have hcardK : Nat.card K = 2 ^ m * oSL2 m * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    congr 1
    · rw [show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card (ModO2 K) from rfl,
        Nat.card_congr eK.toEquiv, card_SL_two hFc]
    · try with_reducible rfl
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have htprops : ∀ t : G, orderOf t = 2 →
      pCoreOf 2 (K ⊔ sec52S M H) = Q ⊔ Subgroup.zpowers t →
        t ∈ Subgroup.normalizer (Q : Set G) ∧ t ^ 2 = 1 ∧
          Q.relIndex (Q ⊔ Subgroup.zpowers t) ≤ 2 := by
    intro t ht2 hKSeq
    have htO : t ∈ pCoreOf 2 (K ⊔ sec52S M H) := by
      rw [hKSeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htN : t ∈ Subgroup.normalizer (Q : Set G) := hKSQ (pCoreOf_le 2 _ htO)
    refine ⟨htN, by rw [← ht2]; exact pow_orderOf_eq_one t, ?_⟩
    have h1 := Subgroup.relIndex_mul_card Q (Q ⊔ Subgroup.zpowers t)
    rw [inf_eq_left.mpr le_sup_left] at h1
    have h2 : Nat.card ↥(Q ⊔ Subgroup.zpowers t) ≤ 2 * Nat.card Q := by
      rw [sup_comm]
      refine (card_sup_le_mul_of_normalizes ((Subgroup.zpowers_le).mpr htN)).trans ?_
      rw [Nat.card_zpowers, ht2]
    have hpos : 0 < Nat.card Q := Nat.card_pos
    by_contra hgt
    have : 3 * Nat.card Q ≤ Q.relIndex (Q ⊔ Subgroup.zpowers t) * Nat.card Q :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  set H' := Kh ⊔ T with hH'
  have hKH' : K ≤ H' := hlt.le.trans le_sup_left
  have hKhH' : Kh ≤ H' := le_sup_left
  set R₀ := Q ⊓ R with hR₀
  have hinfR : Kh ⊓ pCoreOf 2 H' = R := e.inf_pCoreOf_eq h37
  have hKinf : K ⊓ pCoreOf 2 H' = R₀ := by
    apply le_antisymm
    · refine le_inf e.inf_le_blockQ ?_
      rw [← hinfR]
      exact inf_le_inf_right _ hlt.le
    · exact le_inf (inf_le_left.trans hQK) (inf_le_right.trans (e.pCoreOf_le_sup h37))
  obtain ⟨hcent, hQKc, hmod⟩ := module_of_amalgam U4Par.factU4ParabolicModule_holds hm2 hαU hsp'
  rw [← hcore] at hcent hQKc hmod
  have hWR₀ : ⁅pCoreOf 2 H', K⁆ ≤ R₀ := e.commutator_le_inf.trans hKinf.le
  have hR₀Z : ¬ R₀ ≤ centerOf Q := by
    intro hle
    apply e.commutator_ne_bot
    rw [← e.commutator_commutator, eq_bot_iff, Subgroup.commutator_le]
    intro w hw k hk
    have hwZ : w ∈ centerOf Q := hle (hWR₀ hw)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hcent hk) w hwZ
  have hKR₀ : K ≤ Subgroup.normalizer (R₀ : Set G) :=
    (le_inf (le_normalizer_pCoreOf 2 K) (hlt.le.trans (le_normalizer_pCoreOf 2 Kh))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hR₀Q : R₀ ⊔ centerOf Q ≠ Q := by
    intro heq
    apply hQR
    have hZR₀ : centerOf Q ≤ R₀ := by
      rw [← hQQ]
      exact commutator_le_of_sup_center heq inf_le_right (hQK.trans hKR₀)
    exact (heq.symm.trans (sup_eq_left.mpr hZR₀)).le.trans inf_le_right
  obtain ⟨hR₀QZ, hcardR₀Z⟩ := hmod R₀ inf_le_left hKR₀ hR₀Z hR₀Q
  have hZR₀ : centerOf Q ≤ R₀ := by
    rw [← hR₀QZ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQK.trans hKR₀)
  have hcardR₀ : Nat.card R₀ = (2 ^ m) ^ 3 := by
    rwa [sup_eq_left.mpr hZR₀] at hcardR₀Z
  have hcommRK : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ R₀ := by
    intro k hk r hr
    have h1 : ⁅r, k⁆ ∈ R₀ :=
      hWR₀ (Subgroup.commutator_mem_commutator (e.pCoreOf_le_sup h37 hr) hk)
    have h2 : k * r * k⁻¹ * r⁻¹ = ⁅r, k⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact inv_mem h1
  have hRc : Nat.card R ≤ 2 * (2 ^ m) ^ 3 := by
    have h1 := Subgroup.relIndex_mul_card Q R
    have hidx : Q.relIndex R ≤ 2 := by
      rcases halt with ⟨-, -, -, hKSeq⟩ | ⟨m', -, -, -, t, ht2, -, hKSeq, -⟩
      · have : Q.relIndex R = 1 := Subgroup.relIndex_eq_one.mpr (hRKS.trans hKSeq.le)
        omega
      · obtain ⟨-, -, hle2⟩ := htprops t ht2 hKSeq
        have hne : Q.relIndex (Q ⊔ Subgroup.zpowers t) ≠ 0 := by
          intro h0
          have h2 := Subgroup.relIndex_mul_card Q (Q ⊔ Subgroup.zpowers t)
          rw [h0, zero_mul] at h2
          exact (Nat.card_pos (α := ↥(Q ⊔ Subgroup.zpowers t))).ne h2
        exact (Subgroup.relIndex_le_of_le_right (hKSeq ▸ hRKS) hne).trans hle2
    rw [← h1, hcardR₀]
    exact Nat.mul_le_mul_right _ hidx
  have : (R.subgroupOf Kh).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRKh).mpr (le_normalizer_pCoreOf 2 Kh)
  set ρ : ↥Kh →* ↥(modO2Image H' Kh) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H')).subgroupMap (Kh.subgroupOf H')).comp
      (Subgroup.subgroupOfEquivOfLe hKhH').symm.toMonoidHom with hρ
  have hρv : ∀ k : ↥Kh, (ρ k : ↥H' ⧸ CFSG.pCore 2 ↥H') = QuotientGroup.mk ⟨k, hKhH' k.2⟩ :=
    fun k => rfl
  have hρs : Function.Surjective ρ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKhH').symm.surjective
  have hρk : ρ.ker = R.subgroupOf Kh := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hinfR]
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk ⟨k, hKhH' k.2⟩ : ↥H' ⧸ CFSG.pCore 2 ↥H') = 1 :=
        (hρv k).symm.trans (congrArg Subtype.val h1)
      rw [QuotientGroup.eq_one_iff] at h2
      exact ⟨k.2, ⟨_, h2, rfl⟩⟩
    · rintro ⟨-, y, hy, hyk⟩
      apply Subtype.ext
      rw [hρv]
      have hy' : (⟨k, hKhH' k.2⟩ : ↥H') = y := Subtype.ext hyk.symm
      rw [hy', OneMemClass.coe_one, QuotientGroup.eq_one_iff]
      exact hy
  set θ : ↥Kh ⧸ R.subgroupOf Kh ≃* ↥(modO2Image H' Kh) :=
    (QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs) with hθ
  have hRc' : Nat.card R ≤ 2 ^ (3 * m + 1) := by
    rw [show 2 ^ (3 * m + 1) = 2 * (2 ^ m) ^ 3 by ring]
    exact hRc
  obtain ⟨F, _, _, _, hF, c₀, ε, hc₀φ, hc₀k⟩ := exists_sl3Data hSL hm2 hRKh hR2 hRc' θ hL3
    (mem_of_commutator_mem_frattini hchar)
  have := Fintype.ofFinite F
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, Fintype.card_eq_nat_card, hF]; exact h4m)
    exact ⟨s, hs⟩
  have hF3 : Nat.card (Multiplicative (Fin 3 → F)) = (2 ^ m) ^ 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Fin 3 → F)), Nat.card_fun, Nat.card_fin, hF]
  have hφρ : ∀ y : ↥Kh, c₀.φ y = ε (ρ y) := fun y => by rw [hc₀φ]; rfl
  set P' := (P.subgroupOf (modO2Image H' Kh)).map ε.toMonoidHom with hP'
  have hP'max : CFSG.Quasithin.IsMaxParabolic2 ⊤ P' :=
    Vol2Native.A312L.isMaxParabolic2_top_map_equiv ε (isMaxParabolic2_top_subgroupOf hP)
  have himg₀ : c₀.img K = perfectCore P' := by
    have h1 : c₀.img K = ((K.subgroupOf Kh).map ρ).map ε.toMonoidHom := by
      rw [SL3E.SL3Data.img, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun y => hφρ y
    rw [h1, map_subgroupOf_eq_modO2Image hlt.le hKhH' ρ hρv, hBP, perfectCore_subgroupOf hP.1.1,
      CFSG.Quasithin.map_perfectCore]
  have hkerψ : Nat.card c₀.ψ.ker ≤ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup c₀.ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective c₀.ψ c₀.ψsurj).toEquiv,
      hF3] at h1
    have h2 : (2 ^ m) ^ 3 * Nat.card c₀.ψ.ker ≤ (2 ^ m) ^ 3 * 2 := by
      rw [← h1, mul_comm]
      exact hRc
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z : ↥R, (z : G) ∈ centerOf Q ∧ c₀.ψ z ≠ 1 := by
    by_contra hcon
    have hle : (centerOf Q).subgroupOf R ≤ c₀.ψ.ker := fun z hz => by
      by_contra hz1
      exact hcon ⟨z, hz, hz1⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [SL3E.card_subgroupOf_eq, inf_eq_left.mpr (hZR₀.trans inf_le_right), hZq] at h1
    omega
  have hz₀K : ∀ k ∈ K, k * (z₀ : G) * k⁻¹ = z₀ := fun k hk => by
    have h1 := Subgroup.mem_centralizer_iff.mp (hcent hk) z₀ hz₀Z
    rw [← h1, mul_inv_cancel_right]
  obtain ⟨g₁, hg₁⟩ := c₀.exists_conj_eq_perfectCore_Q30 hK4 hP'max himg₀ hz₀K hz₀1
  set c₁ := c₀.conj g₁ with hc₁
  have hinj₁ : ∀ r : ↥R, (r : G) ∈ R₀ → c₁.ψ r = 1 → (r : G) = 1 := fun r hr h1 =>
    c₁.eq_one_of_perfectCore_Q30 hK4 hg₁ inf_le_right hcommRK (by rw [hcardR₀, hF]) hr h1
  have hRQ : R ≤ Q := by
    by_contra hRQ
    have hnotinj : ¬ Function.Injective c₁.ψ := by
      intro hinj
      apply hRQ
      have h1 : Nat.card R ≤ (2 ^ m) ^ 3 := by
        have := Nat.card_le_card_of_injective c₁.ψ hinj
        rwa [hF3] at this
      have h2 : R₀ = R := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardR₀]; exact h1)
      rw [← h2]
      exact inf_le_left
    obtain ⟨z, hz1, hzψ⟩ : ∃ z : ↥R, z ≠ 1 ∧ c₁.ψ z = 1 := by
      by_contra hcon
      apply hnotinj
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      by_contra hz'
      exact hcon ⟨z, hz', hz⟩
    have hzQ : (z : G) ∉ Q := fun hzQ => hz1 (Subtype.ext (hinj₁ z ⟨hzQ, z.2⟩ hzψ))
    have hzψ₀ : c₀.ψ z = 1 := (c₀.conj_ψ_eq_one_iff g₁ z).mp hzψ
    have hzc : ∀ y ∈ Q, (z : G) * y * (z : G)⁻¹ = y := by
      intro y hy
      have h1 := hc₀k z hzψ₀ y (hQK.trans hlt.le hy)
      have h2 : y * (z : G) = z * y := by
        calc y * (z : G) = (y * z * y⁻¹) * y := by group
          _ = z * y := by rw [h1]
      calc (z : G) * y * (z : G)⁻¹ = y * z * (z : G)⁻¹ := by rw [h2]
        _ = y := by group
    rcases halt with ⟨-, -, -, hKSeq⟩ |
        ⟨m', hnm', -, -, t, ht2, -, hKSeq, F', _, _, hF', P'', hP''max, ⟨ι⟩⟩
    · exact hRQ (hRKS.trans hKSeq.le)
    · have hm' : m' = m := by omega
      subst hm'
      obtain ⟨htN, ht2', -⟩ := htprops t ht2 hKSeq
      rcases mem_or_exists_of_mem_sup_zpowers htN ht2' (hKSeq ▸ hRKS z.2) with hzQ' |
          ⟨q₀, hq₀, hzq⟩
      · exact hzQ hzQ'
      · rw [hzq] at hzc
        exact Sp4E.false_of_mem_centralizer_ext hm2 hQK (le_normalizer_pCoreOf 2 K) hQ2 hQQ.le
          hZq hQcard hq₀ hzc hF' hP''max ι
  have hRR₀ : R₀ = R := inf_eq_right.mpr hRQ
  have hψ₁inj : Function.Injective c₁.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have hr₀ : (r : G) ∈ R₀ := by rw [hRR₀]; exact r.2
    exact Subtype.ext (hinj₁ r hr₀ hr)
  have hcardR : Nat.card R = (2 ^ m) ^ 3 := by rw [← hRR₀]; exact hcardR₀
  have hSyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf (le_sup_right : T ≤ K ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTN)
  have hS2 : IsPGroup 2 ↥(T ⊓ K) := hSyl.2.1
  have hcardS : Nat.card ↥(T ⊓ K) = (2 ^ m) ^ 6 := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hS2
    have h1 := Subgroup.relIndex_mul_card (T ⊓ K) K
    rw [inf_eq_left.mpr inf_le_right, ha] at h1
    have hodd : Odd ((T ⊓ K).relIndex K) := Nat.odd_iff.mpr (by
      have := hSyl.2.2
      change ¬ 2 ∣ (T ⊓ K).relIndex K at this
      omega)
    have h2 : 2 ^ a * (T ⊓ K).relIndex K = 2 ^ (6 * m) * oSL2 m := by
      rw [mul_comm, h1, hcardK, hQcard]
      ring
    obtain ⟨rfl, -⟩ := CFSG.Quasithin.Ch1Four.two_pow_mul_odd_inj hodd (odd_oSL2 (by omega)) h2
    rw [ha, ← pow_mul, mul_comm]
  have hSKh : T ⊓ K ≤ Kh := inf_le_right.trans hlt.le
  have hSL : T ⊓ K ≤ L := by
    rw [← hSL2, hSL1]
    exact inf_le_right
  have hQS : Q ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hRS : R ≤ T ⊓ K := hRQ.trans hQS
  obtain ⟨g₂, hg₂⟩ := c₁.exists_conj_img_eq_unitriangular hSKh hS2 (by
    rw [inf_eq_right.mpr hRS, hcardR, hcardS, hF]
    ring_nf
    exact le_rfl)
  set c₂ := c₁.conj g₂ with hc₂
  have hψ₂inj : Function.Injective c₂.ψ := c₁.conj_ψ_injective hψ₁inj g₂
  set c₃ : SL3E.SL3Cfg Kh R F := { c₂ with ψinj := hψ₂inj } with hc₃
  have hS₁ := hLb.1.1
  set U := blockU L with hUdef
  have hUQL : U ≤ pCoreOf 2 L := fun u hu => (Subgroup.mem_inf.mp (hS₁.2.2.1.1 hu)).1
  have hQLT : pCoreOf 2 L ≤ T := by
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L)
        (h.T_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)).trans ?_
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right)
  have hUS : U ≤ T ⊓ K := by
    rw [hSL2.symm.trans hSL1]
    exact le_inf (hUQL.trans hQLT) (hUQL.trans (pCoreOf_le 2 L))
  have hUne : U ≠ ⊥ := by
    intro hU
    have h1 := hS₁.2.2.2.2.1
    rw [← hUdef, hU] at h1
    exact not_lt_bot h1
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of (h.T_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L))
      h.T_le_normalizer
  have hNUL : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hloc : IsTwoLocal (Subgroup.normalizer (U : Set G)) :=
      ⟨U, hUne, (pCoreOf_isPGroup 2 L).to_le hUQL, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hLT : L ⊔ T ≤ M' := (sup_le (Omega4.le_normalizer_blockU L) hTU).trans hle
    have hU := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow h.maximal
    have h1 := hU.2 M' ⟨hM', hLT⟩
    have h2 := hU.2 M ⟨h.maxTwoLocal, h.sup_le_M⟩
    exact (hle.trans (h1.trans h2.symm).le).trans h.normal
  have hUcard : Nat.card F ^ 4 ≤ Nat.card U := by
    rw [hF]
    exact Omega4.card_blockU_ge hLb
  refine c₃.false_of_fixed hK4 (hUS.trans hSKh) (fun a ha => Omega4.blockU_mul_self hS₁ ha)
    (fun a ha b hb => Omega4.blockU_comm hS₁ ha hb) hUcard hUS hSKh hg₂ hRS hSL hR2 hNUL ?_
  intro y hy hyq
  rw [hF] at hyq
  exact Omega4.exists_fixed_of_pow (by omega) hLb hy hyq

end CFSG.Quasithin.H13
