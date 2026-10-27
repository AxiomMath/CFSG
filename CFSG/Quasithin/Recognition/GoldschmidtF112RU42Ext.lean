module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RU42
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Hat
public import CFSG.GH74.QTGen4.U42.ModelExtCore

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut

theorem map_incl_P1_le : P1.map incl ≤ P1h := by
  rintro _ ⟨g, hg, rfl⟩
  change g ∈ P1h.comap incl
  rwa [comap_P1h]

theorem map_incl_P2_le : P2.map incl ≤ P2h := by
  rintro _ ⟨g, hg, rfl⟩
  change g ∈ P2h.comap incl
  rwa [comap_P2h]

theorem P1h_le_normalizer_map_incl_P1 :
    P1h ≤ Subgroup.normalizer ((P1.map incl : Subgroup Ah) : Set Ah) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  haveI : Yh.Normal := Yh_normal
  have key : ∀ x : Ah, x ∈ P1.map incl ↔ x ∈ P1h ∧ x ∈ Yh := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨map_incl_P1_le (Subgroup.mem_map_of_mem _ hy), (mem_Yh_iff_incl _).mpr ⟨y, rfl⟩⟩
    · rintro ⟨hx, hxY⟩
      obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl x).mp hxY
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      change y ∈ P1h.comap incl at hx
      rwa [comap_P1h] at hx
  rw [key, key]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨P1h.mul_mem (P1h.mul_mem hg h1) (P1h.inv_mem hg), Yh_normal.conj_mem _ h2 g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := P1h.mul_mem (P1h.mul_mem (P1h.inv_mem hg) h1) hg
      simpa [mul_assoc] using this
    · have := Yh_normal.conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using this

theorem pCoreOf_P1h_eq : pCoreOf 2 P1h = pCoreOf 2 (P1.map incl) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 (P1.map incl) ≤ pCoreOf 2 P1h := by
    rw [pCoreOf_eq_inf_pCoreOf map_incl_P1_le P1h_le_normalizer_map_incl_P1]
    exact inf_le_right
  have e : ↥(P1.map incl) ≃* ↥P1 := (P1.equivMapOfInjective incl incl_injective).symm
  have h32 : Nat.card (pCoreOf 2 (P1.map incl)) = 32 := by
    rw [card_pCoreOf_of_mulEquiv e 2]
    exact (CFSG.Quasithin.F112R.U42M.isSpecialPow_pCoreOf_P1).2.1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h32, CFSG.GH74.QTGen4.U42.card_pCoreOf_P1h])).symm

theorem isSpecialPow_pCoreOf_P1h : IsSpecialPow 2 2 2 ↥(pCoreOf 2 P1h) := by
  have e : ↥(P1.map incl) ≃* ↥P1 := (P1.equivMapOfInjective incl incl_injective).symm
  exact IsSpecialPow.of_mulEquiv ((pCoreOfMulEquiv e 2).symm.trans
    (MulEquiv.subgroupCongr pCoreOf_P1h_eq.symm))
    CFSG.Quasithin.F112R.U42M.isSpecialPow_pCoreOf_P1

theorem card_pCoreOf_P2h : Nat.card (pCoreOf 2 P2h) = 16 := by
  rw [pCoreOf_P2h_eq, CFSG.GH74.QTGen4.U42.VA_eq_map_Vsub,
    Subgroup.card_map_of_injective incl_injective]
  exact CFSG.GH74.QTGen4.U42.card_Vsub_eq

theorem exists_autIso {G : Type} [Group G] {M₁ M₂ : Subgroup G}
    (hAm : IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups M₁ M₂)) (hO2 : pCoreOf 2 (M₁ ⊔ M₂) = ⊥) :
    Nonempty ((RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P1h P2h)) ∨
      Nonempty ((RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P2h P1h)) := by
  obtain ⟨Yb, _, Gh, _, ι, hY, hinj, hidx, T, N₁, N₂, hpair, ⟨iso0⟩⟩ := hAm
  rcases equiv_A_or_central_involution hY hinj hidx with ⟨⟨ε⟩⟩ | ⟨κ, hκ1, hκ2, hκc⟩
  swap
  · exact (no_central_involution hO2 hpair iso0 hκ1 hκ2 hκc).elim
  have hp₁ := IsYAmalgamPair.map ε hpair
  obtain ⟨c, hc⟩ := CFSG.Quasithin.H13.F431.U42.exists_conj_isSylowTwoOf_top hp₁.1 isSylowTwoOf_That_top
  have hp₂ := IsYAmalgamPair.map (MulAut.conj c) hp₁
  rw [hc] at hp₂
  let iso1 := CFSG.Quasithin.H13.F431.U42.Am.ofSubgroupsMapInj ε.toMonoidHom ε.injective N₁ N₂
  let iso2 := CFSG.Quasithin.H13.F431.U42.Am.ofSubgroupsMapInj (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    (N₁.map ε.toMonoidHom) (N₂.map ε.toMonoidHom)
  rcases pair_eq_of_isYAmalgamPair_A hp₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso0 (CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso1
      (CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso2 (CFSG.Quasithin.H13.F431.U42.Am.ofSubgroupsCongr h1 h2)))⟩
  · exact Or.inr ⟨CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso0 (CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso1
      (CFSG.Quasithin.H13.F431.U42.Am.isoTrans iso2 (CFSG.Quasithin.H13.F431.U42.Am.ofSubgroupsCongr h1 h2)))⟩

section Ext

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin

theorem y9U42_ext {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h2 : VA5 L2)
    (hA : IsU4ExtTwo 1 (f112Amalgam L1 L2 S)) :
    (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
      IsSpecialPow 2 (2 ^ 1) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsBlock2 L2 L2 ∧ IsOmega4MinusType L2 1 ∧ IsAltType L2 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hF.1
  have hN2 := parabolic_le_normalizer_right hH
  have hL2P : L2 ≤ L2 ⊔ bigB L1 L2 S := le_sup_left
  have hc := card_eq_of_VA5 h2
  have hO2 : pCoreOf 2 ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) = ⊥ := by
    have hB : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
      sup_le (sup_le ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
        ((F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
    have : (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S) = L1 ⊔ L2 ⊔ S := by
      apply le_antisymm
      · exact sup_le (sup_le (le_sup_left.trans le_sup_left) hB)
          (sup_le (le_sup_right.trans le_sup_left) hB)
      · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
          ((le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right.trans le_sup_left))
    rw [this]
    exact hH.o2
  rcases exists_autIso hA hO2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  swap
  · exfalso
    have h1152 : Nat.card ↥(L2 ⊔ bigB L1 L2 S) = 1152 :=
      (Nat.card_congr e.φ2.toEquiv).trans card_P1h
    have h5 : 5 ∣ Nat.card ↥(L2 ⊔ bigB L1 L2 S) :=
      (hc ▸ Dvd.dvd.mul_right (by norm_num) _ : 5 ∣ Nat.card L2).trans
        (Subgroup.card_dvd_of_le hL2P)
    rw [h1152] at h5
    norm_num at h5
  have φ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥P1h := e.φ1
  have φ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥P2h := e.φ2
  obtain ⟨P, hP⟩ : ∃ P, P = L2 ⊔ bigB L1 L2 S := ⟨_, rfl⟩
  rw [← hP] at φ2 hN2 hL2P
  have h1920 : Nat.card P = 1920 := (Nat.card_congr φ2.toEquiv).trans card_P2h
  have hO16 : Nat.card (pCoreOf 2 P) = 16 :=
    (card_pCoreOf_of_mulEquiv φ2 2).trans card_pCoreOf_P2h
  have hO2L : pCoreOf 2 L2 = L2 ⊓ pCoreOf 2 P := pCoreOf_eq_inf_pCoreOf hL2P hN2
  have hdvd : Nat.card (pCoreOf 2 L2) ∣ 16 :=
    hO16 ▸ Subgroup.card_dvd_of_le (hO2L ▸ inf_le_right)
  have hidx : L2.relIndex P * Nat.card L2 = 1920 := by
    have := Subgroup.relIndex_mul_card (H := L2) (K := P)
    rwa [inf_eq_left.mpr hL2P, h1920] at this
  have hpos : 0 < Nat.card (pCoreOf 2 L2) := Nat.card_pos
  have hr32 : L2.relIndex P * Nat.card (pCoreOf 2 L2) = 32 := by
    rw [hc] at hidx
    nlinarith
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show L2.relIndex P ∣ 2 ^ 5 from ⟨_, hr32.symm⟩)
  haveI : (L2.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN2
  have hq : IsPGroup 2 (P ⧸ L2.subgroupOf P) := IsPGroup.of_card (n := k) hk
  have hpow : ∀ g ∈ P, ∃ n : ℕ, g ^ 2 ^ n ∈ L2 := by
    intro g hg
    obtain ⟨n, hn⟩ := hq (QuotientGroup.mk (⟨g, hg⟩ : ↥P))
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hn
    simpa using hn
  let ι2 : ↥P2h →* G := P.subtype.comp φ2.symm.toMonoidHom
  have hι2 : Function.Injective ι2 := P.subtype_injective.comp φ2.symm.injective
  set K : Subgroup G := ((P2.map incl).subgroupOf P2h).map ι2 with hK
  have hKP : K ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact (φ2.symm x).2
  have eK : ↥K ≃* ↥P2 :=
    ((((P2.map incl).subgroupOf P2h).equivMapOfInjective ι2 hι2).symm.trans
      (Subgroup.subgroupOfEquivOfLe map_incl_P2_le)).trans
      (P2.equivMapOfInjective incl incl_injective).symm
  have hK960 : Nat.card K = 960 := (Nat.card_congr eK.toEquiv).trans card_P2
  have hKperf : ⁅K, K⁆ = K := perfect_of_mulEquiv eK CFSG.Quasithin.F112R.U42M.perfect_P2
  have hconjK : ∀ g ∈ K, ∀ h ∈ L2 ⊓ K, g * h * g⁻¹ ∈ L2 ⊓ K := by
    intro g hg h hh
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hN2 (hKP hg)) h).mp hh.1, ?_⟩
    exact K.mul_mem (K.mul_mem hg hh.2) (K.inv_mem hg)
  haveI : ((L2 ⊓ K).subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (by
      have := hconjK g g.2 n (Subgroup.mem_subgroupOf.mp hn)
      simpa using this)⟩
  have hqK : IsPGroup 2 (K ⧸ (L2 ⊓ K).subgroupOf K) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨n, hn⟩ := hpow g (hKP g.2)
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_pow]
      exact ⟨hn, K.pow_mem g.2 _⟩
  have hKL : K ≤ L2 := by
    have h := eq_of_perfect_of_pGroup_quotient (inf_le_right : L2 ⊓ K ≤ K) hqK hKperf
    rw [← h]
    exact inf_le_left
  have hL2K : L2 = K := by
    have h16 := Nat.le_of_dvd (by norm_num) hdvd
    exact (Subgroup.eq_of_le_of_card_ge hKL (by rw [hK960, hc]; omega)).symm
  have ψ : ↥L2 ≃* ↥P2 := (MulEquiv.subgroupCongr hL2K).trans eK
  have hO16L : Nat.card (pCoreOf 2 L2) = 16 := by
    rw [card_pCoreOf_of_mulEquiv ψ 2, pCoreOf_P2]
    exact CFSG.GH74.QTGen4.U42.card_Vsub_eq
  have hE : IsElemAbelian 2 (pCoreOf 2 L2) := by
    apply isElemAbelian_pCoreOf_of_mulEquiv ψ
    rw [pCoreOf_P2]
    refine ⟨⟨⟨fun a b => Subtype.ext (Vsub_comm a.2 b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact Vsub_sq hx
  have hNat : ¬ NatSec L2 ⊥ (pCoreOf 2 L2) := by
    have hw := exists_three_fix_of_mulEquiv ψ (p := 2)
      (by rw [pCoreOf_P2]; exact CFSG.Quasithin.F112R.U42M.exists_three_fix_P2)
    obtain ⟨x, hx, ho, v, hv, hv1, hvx⟩ := hw
    intro hn
    apply hv1
    have := hn x hx ho v hv (by
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hvx)
    exact Subgroup.mem_bot.mp this
  have hcenL : ∀ g ∈ L2, (∀ k ∈ L2, g * k = k * g) → g = 1 :=
    fun g hg => eq_one_of_central_of_mulEquiv ψ
      (fun b hb hb' => CFSG.Quasithin.F112R.U42M.eq_one_of_central_P2 hb hb') hg
  have hct : CharTwo L2 := by
    have hctP : CharTwo P := by
      rw [hP, ← bigB_comm L1 L2 S, F1.parabolic_eq]
      exact hH.h2.charTwo
    exact CFSG.QuasithinUnique.CharTwo.of_normal hctP hL2P
      (Subgroup.normal_subgroupOf_of_le_normalizer hN2)
  have hSP : S ≤ P := hP ▸ (le_sup_right.trans le_sup_right)
  have hOPL : pCoreOf 2 P ≤ L2 := by
    have h1 : L2 ⊓ pCoreOf 2 P = pCoreOf 2 P :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [← hO2L, hO16L, hO16])
    rw [← h1]
    exact inf_le_left
  have hCP : ∀ z ∈ P, (∀ k ∈ L2, z * k = k * z) → z = 1 := by
    set C : Subgroup G := P ⊓ Subgroup.centralizer (L2 : Set G) with hC
    have hCL : ∀ c ∈ C, c ∈ L2 → c = 1 := fun c hc hcL =>
      hcenL c hcL (fun k hk => ((Subgroup.mem_centralizer_iff.mp hc.2) k hk).symm)
    have hCp : IsPGroup 2 C := by
      intro c
      obtain ⟨n, hn⟩ := hpow c c.2.1
      refine ⟨n, Subtype.ext ?_⟩
      have hmem : (c : G) ^ 2 ^ n ∈ C := C.pow_mem c.2 _
      simpa using hCL _ hmem hn
    have hfwd : ∀ g ∈ P, ∀ h ∈ C, g * h * g⁻¹ ∈ C := by
      intro g hg h hh
      refine Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hg hh.1) (P.inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : g⁻¹ * k * g ∈ L2 := by
        have := (Subgroup.mem_normalizer_iff.mp (hN2 (P.inv_mem hg)) k).mp hk
        simpa using this
      have h1 := (Subgroup.mem_centralizer_iff.mp hh.2) _ hk'
      calc k * (g * h * g⁻¹) = g * ((g⁻¹ * k * g) * h) * g⁻¹ := by group
        _ = g * (h * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * h * g⁻¹ * k := by group
    have hCn : P ≤ Subgroup.normalizer (C : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hfwd g hg h, fun hh => ?_⟩
      have := hfwd g⁻¹ (P.inv_mem hg) _ hh
      simpa [mul_assoc] using this
    have hCO : C ≤ pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hCp
    intro z hz hzc
    have hzC : z ∈ C :=
      ⟨hz, Subgroup.mem_centralizer_iff.mpr (fun k hk => (hzc k hk).symm)⟩
    exact hCL z hzC (hOPL (hCO hzC))
  haveI : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
  haveI : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
  haveI : DSLeaf LeafM3 := ⟨leafM3⟩
  haveI : DSLeaf LeafAlt5OfOrth := ⟨leafAlt5OfOrth⟩
  refine ⟨?_, ?_, Gold14610.isBlock2_of_short (leafShort2OfA5 h2 hct hE hO16L) le_rfl
    Subgroup.le_normalizer, leafOmega4MinusOfOrth h2 hct hE hO16L hNat,
    leafAlt5OfOrth h2 hct hE hO16L hNat⟩
  · intro hz z hz'
    have hz1 : z = 1 := hCP z (hSP hz'.1) fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hz hz') k hk).symm
    rw [hz1]
    exact Subgroup.one_mem _
  · rw [pow_one]
    exact IsSpecialPow.of_mulEquiv (pCoreOfMulEquiv φ1 2).symm isSpecialPow_pCoreOf_P1h

theorem y9U42 : Y9U42 := by
  intro G _ _ L1 L2 S hF _ h2 hA
  rcases hA with hA | hA
  · exact y9U42_plain hF h2 hA
  · exact y9U42_ext hF h2 hA

end Ext

end CFSG.Quasithin.F112R

