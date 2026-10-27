module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import CFSG.GroupTheory.OddPGroupNoncyclicChar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.RankThree.PartTwo.Sec10.Item104
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxDel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem omega1_eq_zpowers_sup_of_hom_cyclic {T O : Subgroup G} {C : Type*} [Group C] [Finite C]
    [IsCyclic C] (φ : ↥T →* C) (hOT : T ≤ normalizer (O : Set G))
    (hker : ∀ u : ↥T, φ u = 1 → (u : G) ∈ O) :
    ∃ a ∈ F11.Omega1p 2 T, F11.Omega1p 2 T = zpowers a ⊔ (F11.Omega1p 2 T ⊓ O) := by
  classical
  let Y : Subgroup G := F11.Omega1p 2 T
  have hAON : ∀ (a : G) (haT : a ∈ T), zpowers a ≤ normalizer (O : Set G) :=
    fun a haT => (Subgroup.zpowers_le.mpr haT).trans hOT
  have key : ∀ (a : G) (haT : a ∈ T),
      (∀ (v : G) (hvT : v ∈ T), v * v = 1 → φ ⟨v, hvT⟩ ≠ 1 → φ ⟨v, hvT⟩ = φ ⟨a, haT⟩) →
      Y ≤ zpowers a ⊔ O := by
    intro a haT huniq
    refine (Subgroup.closure_le _).mpr ?_
    rintro v ⟨hvT, hv2⟩
    have hv2' : v * v = 1 := by rwa [pow_two] at hv2
    by_cases hv1 : φ ⟨v, hvT⟩ = 1
    · exact Subgroup.mem_sup_right (hker ⟨v, hvT⟩ hv1)
    · have hva : φ ⟨v, hvT⟩ = φ ⟨a, haT⟩ := huniq v hvT hv2' hv1
      have hmemT : v * a⁻¹ ∈ T := T.mul_mem hvT (T.inv_mem haT)
      have hφ1 : φ ⟨v * a⁻¹, hmemT⟩ = 1 := by
        have hsplit : (⟨v * a⁻¹, hmemT⟩ : ↥T) = (⟨v, hvT⟩ : ↥T) * (⟨a, haT⟩ : ↥T)⁻¹ := rfl
        rw [hsplit, map_mul, map_inv, hva, mul_inv_cancel]
      have hvo : v * a⁻¹ ∈ O := hker ⟨v * a⁻¹, hmemT⟩ hφ1
      have hv_eq : v = (v * a⁻¹) * a := by group
      rw [hv_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hvo)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  by_cases hcase : ∃ (a : G) (haT : a ∈ T), a * a = 1 ∧ φ ⟨a, haT⟩ ≠ 1
  · obtain ⟨a, haT, ha2, ha1⟩ := hcase
    have huniq : ∀ (v : G) (hvT : v ∈ T), v * v = 1 → φ ⟨v, hvT⟩ ≠ 1 →
        φ ⟨v, hvT⟩ = φ ⟨a, haT⟩ := by
      intro v hvT hv2 hv1
      have haa : (⟨a, haT⟩ : ↥T) * ⟨a, haT⟩ = 1 := Subtype.ext (by simpa using ha2)
      have hvv : (⟨v, hvT⟩ : ↥T) * ⟨v, hvT⟩ = 1 := Subtype.ext (by simpa using hv2)
      have hφa2 : φ ⟨a, haT⟩ * φ ⟨a, haT⟩ = 1 := by rw [← map_mul, haa, map_one]
      have hφv2 : φ ⟨v, hvT⟩ * φ ⟨v, hvT⟩ = 1 := by rw [← map_mul, hvv, map_one]
      exact (CFSG.SeitzReduction.EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic (C' := C)
        (by rwa [pow_two]) (by rwa [pow_two]) ha1 hv1).symm
    have hYH : Y ≤ zpowers a ⊔ O := key a haT huniq
    have haY : a ∈ Y := Subgroup.subset_closure ⟨haT, by rwa [pow_two]⟩
    refine ⟨a, haY, ?_⟩
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ zpowers a ⊔ O := hYH hy
      have hset : ((zpowers a ⊔ O : Subgroup G) : Set G) = (zpowers a : Set G) * (O : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hAON a haT)
      rw [← SetLike.mem_coe, hset] at hy'
      rcases Set.mem_mul.mp hy' with ⟨u, hu, z, hz, huz⟩
      have hza : zpowers a ≤ Y := Subgroup.zpowers_le.mpr haY
      have huY : u ∈ Y := hza hu
      have hzY : z ∈ Y := by
        have hz_eq : z = u⁻¹ * y := by rw [← huz]; group
        rw [hz_eq]
        exact Y.mul_mem (Y.inv_mem huY) hy
      rw [← huz]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hzY, hz⟩))
    · exact sup_le (Subgroup.zpowers_le.mpr haY) inf_le_left
  · have hno : ∀ (v : G) (hvT : v ∈ T), v * v = 1 → v ∈ O := by
      intro v hvT hv2
      by_contra hvo
      exact hcase ⟨v, hvT, hv2, fun hφ => hvo (hker ⟨v, hvT⟩ hφ)⟩
    have hYO : Y ≤ O := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro v ⟨hvT, hv2⟩
      exact hno v hvT (by rwa [pow_two] at hv2)
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    apply le_antisymm
    · intro y hy
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hy, hYO hy⟩)
    · exact sup_le (by simp) inf_le_left

theorem inPStar_of_hom_cyclic {D : Data G} {V₀ X : Subgroup G} (hX : F11.InP11 D X)
    {C : Type*} [Group C] [Finite C] [IsCyclic C] (φ : ↥D.T →* C)
    (hker : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ pCoreOf 2 (X ⊔ D.T)) :
    InPStar D V₀ X := by
  have hOT : D.T ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    (le_sup_right : D.T ≤ X ⊔ D.T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T))
  obtain ⟨p, hp, -, -, hXp, -⟩ := id hX
  exact ⟨hX, fun _ => ⟨p, hp, hXp, Or.inr (Or.inl
    (omega1_eq_zpowers_sup_of_hom_cyclic φ hOT hker))⟩⟩

theorem inPStar_of_inP11_of_le_normalizer {D : Data G} {V₀ X T₀ : Subgroup G}
    (hX : F11.InP11 D X) (hT₀T : T₀ ≤ D.T) (hTT₀ : D.T ≤ normalizer (T₀ : Set G))
    (hXT₀ : X ≤ normalizer (T₀ : Set G))
    {C : Type*} [Group C] [Finite C] [IsCyclic C] (φ : ↥D.T →* C)
    (hker : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ T₀) :
    InPStar D V₀ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀2 : IsPGroup 2 ↥T₀ := D.sylowM.isPGroup.to_le hT₀T
  have hle : T₀ ≤ pCoreOf 2 (X ⊔ D.T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hT₀T.trans le_sup_right)
      (sup_le hXT₀ hTT₀) hT₀2
  exact inPStar_of_hom_cyclic hX φ fun u hu => hle (hker u hu)

theorem inPStar_of_strongly_of_le_normalizer_sup {D : Data G} {V₀ : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {X T₀ : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p ↥X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXnc : ¬ IsCyclic ↥X) (hT₀T : T₀ ≤ D.T) (hTT₀ : D.T ≤ normalizer (T₀ : Set G))
    (hXT₀ : X ≤ normalizer (T₀ : Set G))
    (hTXT₀ : D.T ≤ normalizer ((X ⊔ T₀ : Subgroup G) : Set G))
    {C : Type*} [Group C] [Finite C] [IsCyclic C] (φ : ↥D.T →* C)
    (hker : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ T₀) :
    InPStar D V₀ X :=
  inPStar_of_inP11_of_le_normalizer
    (inP11_of_strongly hp hp2 hstr hXM hXp hXexp hXnc
      (TwelveNineteen.permutes_of_le_normalizer_sup hT₀T hTXT₀ hXT₀))
    hT₀T hTT₀ hXT₀ φ hker

theorem exists_isSylowOf_le_normalizer_sup_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K R : Subgroup G} (hA : IsPGroup 2 ↥A) (hR : IsPGroup 2 ↥R) (hRK : R ≤ K)
    (hKR : K ≤ normalizer (R : Set G)) (hAK : A ≤ normalizer (K : Set G))
    (hAR : A ≤ normalizer (R : Set G)) (hodd : Odd (R.relIndex K)) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S K ∧
      A ≤ normalizer ((S ⊔ R : Subgroup G) : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf p K
  let P₀ : Subgroup G := S₀ ⊔ R
  letI : MulDistribMulAction ↥K G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp K.subtype)
  letI : MulAction ↥K (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulDistribMulAction ↥(A ⊔ R) G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp (A ⊔ R).subtype)
  letI : MulAction ↥(A ⊔ R) (Subgroup G) := Subgroup.pointwiseMulAction
  have hsmulK : ∀ (k : ↥K) (P : Subgroup G),
      k • P = P.map (MulAut.conj (k : G)).toMonoidHom := by
    intro k P
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hsmulAR : ∀ (x : ↥(A ⊔ R)) (P : Subgroup G),
      x • P = P.map (MulAut.conj (x : G)).toMonoidHom := by
    intro x P
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hAKN : A ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hAK (hRK.trans Subgroup.le_normalizer)
  have hARN : A ⊔ R ≤ Subgroup.normalizer (R : Set G) :=
    sup_le hAR Subgroup.le_normalizer
  have h2group : IsPGroup 2 ↥(A ⊔ R) := hA.to_sup_of_normal_right' hR hAR
  let Ω : Set (Subgroup G) := MulAction.orbit ↥K P₀
  have hΩmem : ∀ P : Subgroup G, P ∈ Ω ↔
      ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S K ∧ P = S ⊔ R := by
    intro P
    constructor
    · intro hP
      rw [MulAction.mem_orbit_iff] at hP
      obtain ⟨k, hk⟩ := hP
      rw [← hk]
      refine ⟨S₀.map (MulAut.conj (k : G)).toMonoidHom, ?_, ?_⟩
      · have hkK : (k : G) ∈ K := k.2
        have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hS₀ (k : G)
        rwa [CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
          (Subgroup.le_normalizer hkK)] at h
      · rw [hsmulK, Subgroup.map_sup,
          CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
            (hKR k.2)]
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨k, hkK, hk⟩ := uc22p22f_exists_conj_sylow hS hS₀
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨k⁻¹, K.inv_mem hkK⟩, ?_⟩
      have hS_eq : S₀.map (MulAut.conj (k : G)⁻¹).toMonoidHom = S := by
        rw [hk, Subgroup.map_map]
        have hcomp : ((MulAut.conj (k : G)⁻¹).toMonoidHom.comp
            (MulAut.conj (k : G)).toMonoidHom) = MonoidHom.id G := by
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply, MonoidHom.id_apply]
          group
        rw [hcomp, Subgroup.map_id]
      rw [hsmulK, Subgroup.map_sup, hS_eq,
        CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
          (hKR (K.inv_mem hkK))]
  have hRstab : R.subgroupOf K ≤ MulAction.stabilizer ↥K P₀ := by
    intro r hr
    rw [MulAction.mem_stabilizer_iff]
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hrK : (r : G) ∈ K := hRK hrR
    have hcomm_mem : ∀ s ∈ S₀, (r : G) * s * (r : G)⁻¹ * s⁻¹ ∈ R := by
      intro s hs
      have hsK : s ∈ K := hS₀.le hs
      have hx : s⁻¹ * (r : G) * s * (r : G)⁻¹ ∈ R := by
        have h := (Subgroup.mem_normalizer_iff.mp (hKR (K.inv_mem hsK)) (r : G)).mp hrR
        simpa using R.mul_mem h (R.inv_mem hrR)
      have hx' : (r : G) * s * (r : G)⁻¹ * s⁻¹ =
          s * (s⁻¹ * (r : G) * s * (r : G)⁻¹) * s⁻¹ := by group
      rw [hx']
      exact (Subgroup.mem_normalizer_iff.mp (hKR hsK)
        (s⁻¹ * (r : G) * s * (r : G)⁻¹)).mp hx
    have hSle : S₀.map (MulAut.conj (r : G)).toMonoidHom ≤ S₀ ⊔ R := by
      rintro x ⟨s, hs, rfl⟩
      change MulAut.conj (r : G) s ∈ S₀ ⊔ R
      have hx : MulAut.conj (r : G) s = ((r : G) * s * (r : G)⁻¹ * s⁻¹) * s := by
        rw [MulAut.conj_apply]
        group
      rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm_mem s hs))
        (Subgroup.mem_sup_left hs)
    have hRfix : R.map (MulAut.conj (r : G)).toMonoidHom = R :=
      CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
        (Subgroup.le_normalizer hrR)
    have hle_map : (S₀ ⊔ R).map (MulAut.conj (r : G)).toMonoidHom ≤ S₀ ⊔ R := by
      rw [Subgroup.map_sup, hRfix]
      exact sup_le hSle le_sup_right
    have hcard_map : Nat.card ↥((S₀ ⊔ R).map (MulAut.conj (r : G)).toMonoidHom) =
        Nat.card ↥(S₀ ⊔ R) :=
      Subgroup.card_map_of_injective (MulAut.conj (r : G)).injective
    have hcard_le : Nat.card ↥(S₀ ⊔ R) ≤
        Nat.card ↥((S₀ ⊔ R).map (MulAut.conj (r : G)).toMonoidHom) := by
      rw [hcard_map]
    have hmapP : (S₀ ⊔ R).map (MulAut.conj (r : G)).toMonoidHom = S₀ ⊔ R :=
      Subgroup.eq_of_le_of_card_ge hle_map hcard_le
    rw [hsmulK]
    exact hmapP
  have hΩcard : Nat.card Ω = (MulAction.stabilizer ↥K P₀).index := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  have hdiv : (MulAction.stabilizer ↥K P₀).index ∣ R.relIndex K := by
    have hdvd := Subgroup.index_dvd_of_le hRstab
    simpa [Subgroup.relIndex] using hdvd
  have hoddcard : Odd (Nat.card Ω) := by
    rw [hΩcard]
    exact Odd.of_dvd_nat hodd hdiv
  have hΩinv : ∀ (x : ↥(A ⊔ R)) {P : Subgroup G}, P ∈ Ω → x • P ∈ Ω := by
    intro x P hP
    rw [hΩmem] at hP ⊢
    obtain ⟨S, hS, rfl⟩ := hP
    refine ⟨S.map (MulAut.conj (x : G)).toMonoidHom, ?_, ?_⟩
    · have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hS (x : G)
      rwa [CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
        (hAKN x.2)] at h
    · rw [hsmulAR, Subgroup.map_sup,
        CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
          (hARN x.2)]
  letI : MulAction ↥(A ⊔ R) Ω :=
    { smul := fun x P => ⟨x • (P : Subgroup G), hΩinv x P.2⟩
      one_smul := fun P => Subtype.ext (one_smul _ _)
      mul_smul := fun x y P => Subtype.ext (mul_smul _ _ _) }
  obtain ⟨P, hPfix⟩ :=
    h2group.nonempty_fixed_point_of_prime_not_dvd_card Ω hoddcard.not_two_dvd_nat
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp P.2
  let S : Subgroup G := S₀.map (MulAut.conj (k : G)).toMonoidHom
  have hS : CFSG.ABGLocalTools.IsSylowOf p S K := by
    have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hS₀ (k : G)
    rwa [CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer k.2)] at h
  have hPval : (P : Subgroup G) = S ⊔ R := by
    rw [← hk, hsmulK, Subgroup.map_sup,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hKR k.2)]
  refine ⟨S, hS, ?_⟩
  intro a ha
  let aa : ↥(A ⊔ R) := ⟨a, Subgroup.mem_sup_left ha⟩
  have hfix : aa • (P : Subgroup G) = (P : Subgroup G) :=
    congrArg Subtype.val (hPfix aa)
  have hmap : (P : Subgroup G).map (MulAut.conj a).toMonoidHom = (P : Subgroup G) := by
    have h := hsmulAR aa (P : Subgroup G)
    rw [h] at hfix
    simpa using hfix
  rw [← hPval]
  exact CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq hmap

theorem le_normalizer_sup_of_characteristic {p : ℕ} [Fact p.Prime] {A S R X : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S (S ⊔ R)) (hSR : S ≤ normalizer (R : Set G))
    (hA : A ≤ normalizer ((S ⊔ R : Subgroup G) : Set G)) (hAR : A ≤ normalizer (R : Set G))
    (hXS : X ≤ S) (hX : (X.subgroupOf S).Characteristic) :
    A ≤ normalizer ((X ⊔ R : Subgroup G) : Set G) := by
  intro a ha
  have hK : (S ⊔ R).map (MulAut.conj a).toMonoidHom = S ⊔ R :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (hA ha)
  have hSa : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj a).toMonoidHom) (S ⊔ R) := by
    have h := CFSG.RankThree.PartTwo.Sec10.IsSylowOf.map_conj hS a
    rwa [hK] at h
  obtain ⟨g, hg, hgS⟩ := uc22p22f_exists_conj_sylow hS hSa
  have hset : ((S ⊔ R : Subgroup G) : Set G) = (R : Set G) * (S : Set G) := by
    rw [sup_comm]; exact Subgroup.coe_mul_of_right_le_normalizer_left R S hSR
  have hg' : g ∈ (R : Set G) * (S : Set G) := by rw [← hset]; exact hg
  obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hg'
  have hsS : S.map (MulAut.conj s).toMonoidHom = S :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer hs)
  have hrS : S.map (MulAut.conj (r⁻¹ * a)).toMonoidHom = S := by
    have h1 : S.map (MulAut.conj (r⁻¹ * a)).toMonoidHom =
        (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj r⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h2 : S.map (MulAut.conj (r * s)).toMonoidHom =
        (S.map (MulAut.conj s).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1, hgS, h2, hsS, Subgroup.map_map]
    have h3 : (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj r).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [h3, Subgroup.map_id]
  have hNS : r⁻¹ * a ∈ normalizer (S : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq hrS
  have hNX : r⁻¹ * a ∈ normalizer (X : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := S) (X.subgroupOf S) hNS
    rwa [Subgroup.map_subgroupOf_eq_of_le hXS] at h
  have hNR : r⁻¹ * a ∈ normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hr)) (hAR ha)
  have hNXR : r⁻¹ * a ∈ normalizer ((X ⊔ R : Subgroup G) : Set G) := by
    apply CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq
    rw [Subgroup.map_sup,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer hNX,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer hNR]
  have hrXR : r ∈ normalizer ((X ⊔ R : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right hr)
  have ha' : a = r * (r⁻¹ * a) := by group
  rw [ha']
  exact Subgroup.mul_mem _ hrXR hNXR

theorem not_isCyclic_of_isSylowOf_of_le_map {H : Type*} [Group H] {N K S : Subgroup G}
    {p : ℕ} [Fact p.Prime] (f : ↥N →* H) (hKN : K ≤ N)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) {E : Subgroup H} (hE : IsPGroup p ↥E)
    (hEnc : ¬ IsCyclic ↥E) (hEK : E ≤ (K.subgroupOf N).map f) : ¬ IsCyclic ↥S := by
  classical
  intro hScyc
  set Kbar : Subgroup H := (K.subgroupOf N).map f with hKbar
  set Sbar : Subgroup H := (S.subgroupOf N).map f with hSbar
  haveI : Finite ↥Kbar := by
    refine Finite.of_surjective
      (fun x : ↥(K.subgroupOf N) =>
        (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : ↥Kbar)) ?_
    rintro ⟨y, hy⟩
    rw [hKbar] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hStop : CFSG.ABGLocalTools.IsSylowOf p (S.subgroupOf K) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K).mp ?_
    simpa [Subgroup.map_subgroupOf_eq_of_le hS.le, Subgroup.map_top,
      Subgroup.range_subtype] using hS
  let fK : ↥K →* H := f.comp (Subgroup.inclusion hKN)
  have hKbar_eq : (⊤ : Subgroup K).map fK = Kbar := by
    ext x
    constructor
    · rintro ⟨k, -, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(k : G), hKN k.2⟩,
        Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨(n : G), Subgroup.mem_subgroupOf.mp hn⟩, Subgroup.mem_top _, rfl⟩
  have hSbar_eq : (S.subgroupOf K).map fK = Sbar := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(s : G), hKN s.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hs), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨(n : G), hS.le (Subgroup.mem_subgroupOf.mp hn)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hn), ?_⟩
      rfl
  have hSbar_sylow : CFSG.ABGLocalTools.IsSylowOf p Sbar Kbar := by
    rw [← hSbar_eq, ← hKbar_eq]
    exact CFSG.QuasithinUnique.Setup.Lift.isSylowOf_map hStop fK
  have hSbar_cyc : IsCyclic ↥Sbar := by
    have hS'cyc : IsCyclic ↥(S.subgroupOf K) := by
      haveI : IsCyclic ↥S := hScyc
      exact (Subgroup.subgroupOfEquivOfLe hS.le).isCyclic.mpr hScyc
    haveI : IsCyclic ↥(S.subgroupOf K) := hS'cyc
    let φ : ↥(S.subgroupOf K) →* ↥Sbar :=
      ((fK.comp (S.subgroupOf K).subtype)).codRestrict Sbar
        (fun x => by
          rw [← hSbar_eq]
          exact Subgroup.mem_map_of_mem fK x.2)
    have hφ : Function.Surjective φ := by
      intro y
      have hy' : (y : H) ∈ (S.subgroupOf K).map fK := by
        rw [hSbar_eq]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact isCyclic_of_surjective φ hφ
  obtain ⟨Q, hQ⟩ := hSbar_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥Kbar) := by
    let e := (Q : Subgroup ↥Kbar).equivMapOfInjective Kbar.subtype
      Kbar.subtype_injective
    exact e.isCyclic.mpr (hQ.symm ▸ hSbar_cyc)
  have hE' : IsPGroup p (E.subgroupOf Kbar) := hE.comap_subtype
  have hE'cyc : IsCyclic ↥(E.subgroupOf Kbar) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isCyclic_of_isPGroup_of_isCyclic_sylow Q hQcyc hE'
  have hEcyc : IsCyclic ↥E := (Subgroup.subgroupOfEquivOfLe hEK).isCyclic.mp hE'cyc
  exact hEnc hEcyc

theorem inf_sup_eq_sup_inf_of_isSylowOf {p : ℕ} [Fact p.Prime] {M T A B : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hAM : A ≤ M) (hBM : B ≤ M)
    (hMA : M ≤ normalizer (A : Set G)) (hMB : M ≤ normalizer (B : Set G)) :
    T ⊓ (A ⊔ B) = (T ⊓ A) ⊔ (T ⊓ B) := by
  classical
  set PA : Subgroup G := T ⊓ A with hPAdef
  set PB : Subgroup G := T ⊓ B with hPBdef
  set P : Subgroup G := T ⊓ (A ⊔ B) with hPdef
  have hPA : CFSG.ABGLocalTools.IsSylowOf p PA A := by
    rw [hPAdef]
    exact hT.inf_of_le_normalizer hAM hMA
  have hPB : CFSG.ABGLocalTools.IsSylowOf p PB B := by
    rw [hPBdef]
    exact hT.inf_of_le_normalizer hBM hMB
  have hMAB : M ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    fun m hm => CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup A B
      (Subgroup.mem_inf.mpr ⟨hMA hm, hMB hm⟩)
  have hP : CFSG.ABGLocalTools.IsSylowOf p P (A ⊔ B) := by
    rw [hPdef]
    exact hT.inf_of_le_normalizer (sup_le hAM hBM) hMAB
  have hMABinf : M ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hMA hm, hMB hm⟩)
  have hPinf : CFSG.ABGLocalTools.IsSylowOf p (T ⊓ (A ⊓ B)) (A ⊓ B) :=
    hT.inf_of_le_normalizer (inf_le_left.trans hAM) hMABinf
  have hPAnorm : PA ≤ Subgroup.normalizer (PB : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact T.mul_mem (T.mul_mem hx.1 hy.1) (T.inv_mem hx.1)
      · exact (Subgroup.mem_normalizer_iff.mp (hMB (hT.le hx.1)) y).mp hy.2
    · intro hy
      have hx' : x⁻¹ ∈ PA := PA.inv_mem hx
      have hy'' : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ PB := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact T.mul_mem (T.mul_mem hx'.1 hy.1) (T.inv_mem hx'.1)
        · exact (Subgroup.mem_normalizer_iff.mp (hMB (hT.le hx'.1))
            (x * y * x⁻¹)).mp hy.2
      have hsimp : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [hsimp] at hy''
  have hprodP : Nat.card ↥(PA ⊔ PB) * Nat.card ↥(PA ⊓ PB) = Nat.card ↥PA * Nat.card ↥PB := by
    have h := CFSG.ABGTheoremB.card_sup_mul_card_inf_of_le_normalizer
      (A := PB) (B := PA) hPAnorm
    simpa [sup_comm, inf_comm, mul_comm] using h
  have hinf : PA ⊓ PB = T ⊓ (A ⊓ B) := by
    rw [hPAdef, hPBdef]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hcard_inf : Nat.card ↥(PA ⊓ PB) = p ^ (Nat.card ↥(A ⊓ B)).factorization p := by
    rw [hinf]
    exact hPinf.card_eq
  have hPprod : Nat.card ↥(PA ⊔ PB) * p ^ (Nat.card ↥(A ⊓ B)).factorization p =
      p ^ (Nat.card ↥A).factorization p * p ^ (Nat.card ↥B).factorization p := by
    have h := hprodP
    rw [hcard_inf, hPA.card_eq, hPB.card_eq] at h
    simpa [mul_comm] using h
  have hABprod : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B :=
    CFSG.ABGTheoremB.card_sup_mul_card_inf_of_le_normalizer (A := A) (B := B)
      (hBM.trans hMA)
  have hfac := congrArg (fun n => n.factorization p) hABprod
  rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')] at hfac
  simp only [Finsupp.add_apply] at hfac
  have hmain : Nat.card ↥(PA ⊔ PB) * p ^ (Nat.card ↥(A ⊓ B)).factorization p =
      p ^ (Nat.card ↥(A ⊔ B)).factorization p * p ^ (Nat.card ↥(A ⊓ B)).factorization p := by
    calc
      Nat.card ↥(PA ⊔ PB) * p ^ (Nat.card ↥(A ⊓ B)).factorization p
          = p ^ (Nat.card ↥A).factorization p * p ^ (Nat.card ↥B).factorization p := hPprod
      _ = p ^ ((Nat.card ↥A).factorization p + (Nat.card ↥B).factorization p) := by
            rw [pow_add]
      _ = p ^ ((Nat.card ↥(A ⊔ B)).factorization p +
            (Nat.card ↥(A ⊓ B)).factorization p) := by rw [hfac]
      _ = p ^ (Nat.card ↥(A ⊔ B)).factorization p *
            p ^ (Nat.card ↥(A ⊓ B)).factorization p := by rw [pow_add]
  have hcard : Nat.card ↥(PA ⊔ PB) = p ^ (Nat.card ↥(A ⊔ B)).factorization p :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) hmain
  have hle : PA ⊔ PB ≤ P := by
    rw [hPdef]
    refine sup_le ?_ ?_
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)
  have hcardP : Nat.card ↥P = p ^ (Nat.card ↥(A ⊔ B)).factorization p := by
    rw [hPdef]
    exact hP.card_eq
  have hlecard : Nat.card ↥P ≤ Nat.card ↥(PA ⊔ PB) := by rw [hcardP, hcard]
  have heq : PA ⊔ PB = P := Subgroup.eq_of_le_of_card_ge hle hlecard
  rw [hPdef, hPAdef, hPBdef] at heq
  exact heq.symm

theorem exists_noncyclic_exp_le_normalizer_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A K R : Subgroup G} (hA : IsPGroup 2 ↥A) (hR : IsPGroup 2 ↥R) (hRK : R ≤ K)
    (hKR : K ≤ normalizer (R : Set G)) (hAK : A ≤ normalizer (K : Set G))
    (hAR : A ≤ normalizer (R : Set G)) (hodd : Odd (R.relIndex K))
    (hnc : ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S K → ¬ IsCyclic ↥S) :
    ∃ X : Subgroup G, X ≤ K ∧ IsPGroup p ↥X ∧ (∀ x ∈ X, x ^ p = 1) ∧ ¬ IsCyclic ↥X ∧
      A ≤ normalizer ((X ⊔ R : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hAS⟩ :=
    exists_isSylowOf_le_normalizer_sup_of_odd hp hp2 hA hR hRK hKR hAK hAR hodd
  obtain ⟨X, hXS, hXchar, hXnc, hXexp, -⟩ :=
    CFSG.GroupTheory.exists_characteristic_noncyclic_exponent_classTwo hp2 hS.isPGroup (hnc S hS)
  refine ⟨X, hXS.trans hS.le, hS.isPGroup.to_le hXS, hXexp, hXnc, ?_⟩
  exact le_normalizer_sup_of_characteristic
    (hS.of_le le_sup_left (sup_le hS.le hRK)) (hS.le.trans hKR) hAS hAR hXS hXchar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
