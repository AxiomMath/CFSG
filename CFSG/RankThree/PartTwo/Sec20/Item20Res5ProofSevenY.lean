module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofCyclic
import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofComm
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSevenCyclic

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Res5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem wc_conj {c : G}
    (hwc : ∀ R : Subgroup G, IsPGroup 3 R → c ∈ R → ∀ g : G,
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ R →
        (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c) (a : G) :
    ∀ R : Subgroup G, IsPGroup 3 R → a * c * a⁻¹ ∈ R → ∀ g : G,
      (Subgroup.zpowers (a * c * a⁻¹)).map (MulAut.conj g).toMonoidHom ≤ R →
        (Subgroup.zpowers (a * c * a⁻¹)).map (MulAut.conj g).toMonoidHom =
          Subgroup.zpowers (a * c * a⁻¹) := by
  intro R hR hcR g hgR
  have hza : Subgroup.zpowers (a * c * a⁻¹) =
      (Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hR' : IsPGroup 3 (R.map (MulAut.conj a⁻¹).toMonoidHom) := hR.map _
  have hcR' : c ∈ R.map (MulAut.conj a⁻¹).toMonoidHom :=
    ⟨a * c * a⁻¹, hcR, by simp [mul_assoc]⟩
  have hle : (Subgroup.zpowers c).map (MulAut.conj (a⁻¹ * g * a)).toMonoidHom ≤
      R.map (MulAut.conj a⁻¹).toMonoidHom := by
    have : (Subgroup.zpowers c).map (MulAut.conj (a⁻¹ * g * a)).toMonoidHom =
        (((Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom).map
          (MulAut.conj g).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom := by
      rw [map_conj_map_conj, map_conj_map_conj, mul_assoc]
    rw [this, ← hza]
    exact Subgroup.map_mono hgR
  have h1 := hwc _ hR' hcR' _ hle
  calc (Subgroup.zpowers (a * c * a⁻¹)).map (MulAut.conj g).toMonoidHom
      = ((Subgroup.zpowers c).map (MulAut.conj (a⁻¹ * g * a)).toMonoidHom).map
          (MulAut.conj a).toMonoidHom := by
        rw [hza, map_conj_map_conj, map_conj_map_conj]
        congr 3
        group
    _ = Subgroup.zpowers (a * c * a⁻¹) := by rw [h1, hza]

omit [Finite G] in
theorem cf_conj {c : G}
    (hcf : ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → ⁅x, y⁆ ∈ Subgroup.zpowers c → ⁅x, y⁆ ≠ 1 →
      IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) → False) (a : G) :
    ∀ x y : G, x ^ 3 = 1 → y ^ 3 = 1 → ⁅x, y⁆ ∈ Subgroup.zpowers (a * c * a⁻¹) → ⁅x, y⁆ ≠ 1 →
      IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) → False := by
  intro x y hx3 hy3 hxy hxy1 hp
  have hconj3 : ∀ z : G, z ^ 3 = 1 → (a⁻¹ * z * a) ^ 3 = 1 := fun z hz => by
    rw [show a⁻¹ * z * a = a⁻¹ * z * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hz, mul_one,
      mul_inv_cancel]
  have hcom : ⁅a⁻¹ * x * a, a⁻¹ * y * a⁆ = a⁻¹ * ⁅x, y⁆ * a := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  refine hcf (a⁻¹ * x * a) (a⁻¹ * y * a) (hconj3 x hx3) (hconj3 y hy3) ?_ ?_ ?_
  · rw [hcom]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk, conj_zpow]
    group
  · rw [hcom]
    intro h1
    apply hxy1
    have : ⁅x, y⁆ = a * (a⁻¹ * ⁅x, y⁆ * a) * a⁻¹ := by group
    rw [this, h1]
    group
  · have hcl : Subgroup.closure ({a⁻¹ * x * a, a⁻¹ * y * a} : Set G) =
        (Subgroup.closure ({x, y} : Set G)).map (MulAut.conj a⁻¹).toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
      simp
    rw [hcl]
    exact hp.map _

theorem mem_normalClosureIn_of_pRank_le_one {D : Subgroup G} (hD : CFSG.Open.pRank 3 D ≤ 1)
    {c a : G} (hcD : c ∈ D) (haD : a ∈ D) (hc : orderOf c = 3) (ha : orderOf a = 3) :
    a ∈ normalClosureIn D c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have ha3 : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨P₁, hP₁, hcP₁⟩ := Sec20.exists_isSylowOf_le hc3 (Subgroup.zpowers_le.mpr hcD)
  obtain ⟨P₂, hP₂, haP₂⟩ := Sec20.exists_isSylowOf_le ha3 (Subgroup.zpowers_le.mpr haD)
  obtain ⟨k, hkD, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP₁ hP₂
  have hkc : k * c * k⁻¹ ∈ P₁.map (MulAut.conj k).toMonoidHom :=
    ⟨c, hcP₁ (Subgroup.mem_zpowers c), rfl⟩
  have haP : a ∈ P₁.map (MulAut.conj k).toMonoidHom := haP₂ (Subgroup.mem_zpowers a)
  have hcyc : IsCyclic ↥(P₁.map (MulAut.conj k).toMonoidHom) := by
    obtain ⟨Q, hQ⟩ := hP₂
    rw [← hQ]
    have := Sec16.Proof1622.isCyclic_of_open_pRank_le_one hD Q
    exact isCyclic_of_surjective
      ((Q : Subgroup ↥D).equivMapOfInjective D.subtype D.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)
  set P := P₁.map (MulAut.conj k).toMonoidHom with hPdef
  set u : ↥P := ⟨a, haP⟩ with hu
  set v : ↥P := ⟨k * c * k⁻¹, hkc⟩ with hv
  have hu3 : Nat.card (Subgroup.zpowers u) = 3 := by
    rw [Nat.card_zpowers, hu, Subgroup.orderOf_mk, ha]
  have hv3 : Nat.card (Subgroup.zpowers v) = 3 := by
    rw [Nat.card_zpowers, hv, Subgroup.orderOf_mk,
      show k * c * k⁻¹ = MulAut.conj k c from rfl, MulEquiv.orderOf_eq, hc]
  have heq : Subgroup.zpowers u = Subgroup.zpowers v :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (hu3.trans hv3.symm)
  have humem : u ∈ Subgroup.zpowers v := heq ▸ Subgroup.mem_zpowers u
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp humem
  have hkcI : k * c * k⁻¹ ∈ normalClosureIn D c := Subgroup.subset_closure ⟨k, hkD, rfl⟩
  have : a = (k * c * k⁻¹) ^ j := by
    have := congrArg Subtype.val hj
    simpa [hu, hv] using this.symm
  rw [this]
  exact zpow_mem hkcI j

theorem le_normalizer_normalClosureIn_of_pRank {D T : Subgroup G} {c : G}
    (hD : CFSG.Open.pRank 3 D ≤ 1) (hcD : c ∈ D) (hc : orderOf c = 3)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) :
    T ≤ Subgroup.normalizer (normalClosureIn D c : Set G) := by
  intro t ht
  have hDI : D ≤ Subgroup.normalizer (normalClosureIn D c : Set G) :=
    le_normalizer_normalClosureIn D c
  have htc : t * c * t⁻¹ ∈ normalClosureIn D c := by
    refine mem_normalClosureIn_of_pRank_le_one hD hcD
      ((Subgroup.mem_normalizer_iff.mp (hTD ht) c).mp hcD) hc ?_
    rw [show t * c * t⁻¹ = MulAut.conj t c from rfl, MulEquiv.orderOf_eq, hc]
  refine Subgroup.mem_normalizer_fintype fun i hi => ?_
  have hle : normalClosureIn D c ≤ (normalClosureIn D c).comap (MulAut.conj t).toMonoidHom := by
    rw [normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hm' : t * m * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hTD ht) m).mp hm
    have e : t * (m * c * m⁻¹) * t⁻¹ =
        (t * m * t⁻¹) * (t * c * t⁻¹) * (t * m * t⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hDI hm') _).mp htc
  have := hle hi
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem fTwenty_ne_bot_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (h3 : KIsL3 M c) (hTN : T ≤ N)
    (hKN : ¬ kTwenty M c ≤ N) (hE : eTwenty M N c T ≠ ⊥) : fTwenty M N c T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set Z := zTwenty T with hZdef
  set I := iTwenty M N c with hIdef
  set E := eTwenty M N c T with hEdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTM.trans hMK
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  have hc : orderOf c = 3 := orderOf_eq_three hT hKN
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  have hrank : CFSG.Open.pRank 3 (K ⊓ N) ≤ 1 := by
    have h1 := pRank_three_le hTK hT2
    have h3 := kFactL3OddThreeRank n hn (↥K ⧸ CFSG.pCore 2 ↥K) ⟨e⟩
    have h4 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3
      (by norm_num) (K ⊔ T)
    have h5 := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three
      (inf_le_left.trans le_sup_left : K ⊓ N ≤ K ⊔ T)
    omega
  have hTD : T ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, Subgroup.le_normalizer (hTN ht)⟩
  have hTI : T ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_normalClosureIn_of_pRank hrank ⟨hcK, hcN⟩ hc hTD
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_fourChar T 0)
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := Res3.le_normalizer_commutator hTZ hTI
  set Q := CFSG.Open.pCoreOf 2 (K ⊔ T) with hQdef
  have hXM : K ⊔ T ≤ M := sup_le hKM hTM
  have hZQ : Z ≤ Q := fun z hz => (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).1
  have hIK : I ≤ K := (normalClosureIn_le (show c ∈ K ⊓ N from ⟨hcK, hcN⟩)).trans inf_le_left
  have hEQ : E ≤ Q := Res3.commutator_le_of_le_of_le_normalizer hZQ
    ((hIK.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right hXM)
  have hET : E ≤ T := hEQ.trans hQT
  have hnil : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hnorm : (E.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hET).mpr hTE
  have hne : E.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hE
    rw [eq_bot_iff]
    intro v hv
    have hv' : (⟨v, hET hv⟩ : ↥T) ∈ E.subgroupOf T := hv
    rw [h0, Subgroup.mem_bot] at hv'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hv')
  set W := E.subgroupOf T ⊓ Subgroup.center ↥T with hW
  have hW1 : W ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hW2 : IsPGroup 2 W := hT2.to_subgroup W
  have hWnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW1
  obtain ⟨w, hw⟩ := hW2.exists_card_eq
  have hdvd : 2 ∣ Nat.card W := by
    obtain ⟨m, hm⟩ := hW2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Finite.one_lt_card_iff_nontrivial.mpr hWnt).ne' (by simpa using hm)
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 hdvd
  have hy2 : ((y : ↥T) : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    have := congrArg (fun z : W => ((z : ↥T) : G)) this
    simpa using this
  have hy1 : ((y : ↥T) : G) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hy
    omega
  have hyE : ((y : ↥T) : G) ∈ E := (Subgroup.mem_subgroupOf.mp y.2.1)
  have hyZ : ((y : ↥T) : G) ∈ Z := by
    refine ⟨(y : ↥T), ?_, rfl⟩
    rw [SetLike.mem_coe, Sec20.mem_omegaOneCenter_top_iff]
    refine ⟨y.2.2, Subtype.ext ?_⟩
    simpa using hy2
  intro hF
  have : ((y : ↥T) : G) ∈ fTwenty M N c T := ⟨hyZ, hyE⟩
  rw [hF, Subgroup.mem_bot] at this
  exact hy1 this

omit [Finite G] in
theorem centralizer_ne_top {F : Subgroup G} [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hF : F ≠ ⊥) : Subgroup.centralizer (F : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨⟨f, hfF⟩, hf1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF
  have hf1 : f ≠ 1 := fun h => hf1' (Subtype.ext h)
  have hfZ : f ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (F : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg f hfF).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hfZ
    exact hf1 hfZ
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := ht ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

end Res5

theorem step207YCyclic_core
    (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo) {G : Type} [Group G] [Finite G]
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hN : N = Subgroup.normalizer (L : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hsylTop : ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) →
        CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧
        Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c} ∧
        c ∉ (frattini (Sec18.omegaOneThree P)).map (Sec18.omegaOneThree P).subtype)
    (h3 : KIsL3 M c) (hTN : T ≤ N)
    (hCK : ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hE : eTwenty M N c T ≠ ⊥) {x : G}
    (hcx : x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G)) :
    CFSG.Open.pRank 3
      (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)) ≤ 1 := by
  have : IsSimpleGroup G := hT.isSimpleGroup
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKN : ¬ kTwenty M c ≤ N := fun h => hCK (inf_le_left.trans h)
  have hc : orderOf c = 3 := Res5.orderOf_eq_three hT hKN
  have hF := Res5.fTwenty_ne_bot_core hT hN hAL h3 hTN hKN hE
  have hX : Subgroup.centralizer (fTwenty M N c T : Set G) ≠ ⊤ :=
    Res5.centralizer_ne_top hT.nonabelian hF
  have hc' : orderOf (x * c * x⁻¹) = 3 := by
    rw [show x * c * x⁻¹ = MulAut.conj x c from rfl, MulEquiv.orderOf_eq, hc]
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.normalizer (A : Set G))
  obtain ⟨hPG, hconj, hfrat⟩ := hsylTop P hP
  have hwc := Res5.wc_conj (fun R hR hcR g hgR => Res5.map_conj_eq_of_le hPG hconj hR hcR hgR) x
  have hcf := Res5.cf_conj (fun x y hx3 hy3 hxy hxy1 hp =>
    Res5.false_of_comm hPG hc hconj hfrat hx3 hy3 hxy hxy1 hp) x
  refine Res5.pRank_normalClosureIn_le_one h432 h41 hG2 hT.toTheoremFourHyp hX hc' hcx
    (fun g hg => ?_) hcf
  have hZ : IsPGroup 3 (Subgroup.zpowers (x * c * x⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc', pow_one])
  exact hwc _ (IsPGroup.to_sup_of_normal_left' hZ (hZ.map _) hg)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) g le_sup_right

theorem step207YCyclic_of
    (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo) (h184_5 : Sec18.Item184_5)
    (h184_6 : Sec18.Item184_6) (h1810 : Sec18.Item1810Hyp) (h204 : Item204One)
    (h2051 : Step2051) (h2053 : Step2053) : Step207YCyclic := by
  intro G _ _ A M L N c T hT hTN hCK hE hLE x hxK hxB hcx
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  obtain ⟨H, hH18, hH187, -, hN⟩ := exists_sec18H_of_ctx20One hT
  refine step207YCyclic_core h432 h41 hG2 hT.toCtx20 hN
    (le_normalizer_of_hyp201One hT.hyp201One) (fun P hP => ?_)
    (h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT (h2051 G A M L N c T hT))) hTN hCK hE hcx
  have hconj := h1810 G A M H c hH18 hH187 P hP
  refine ⟨h184_6 G A M H c hH18 P hP, hconj, ?_⟩
  rcases h184_5 G A M H c hH18 P hP with ⟨-, -, hfrat⟩ | ⟨-, h9, hAP, -, -⟩
  · exact hfrat
  · exact (not_case_two hcA hconj hAP h9).elim

end CFSG.RankThree.PartTwo.Sec20
