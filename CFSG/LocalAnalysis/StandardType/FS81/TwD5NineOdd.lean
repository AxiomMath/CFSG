module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.LieType.BorelTits.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem CFSG.ABGLocalTools

private theorem exists_mul_mem_normalizer_of_sylow_of_normal {G : Type} [Group G] [Finite G]
    {X C T : Subgroup G} (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (hsyl : IsSylowOf 2 T C) :
    ∀ x ∈ X, ∃ n ∈ X ⊓ Subgroup.normalizer (T : Set G), ∃ c ∈ C, x = n * c := by
  classical
  intro x hx
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hQC : (Q : Subgroup ↥C).map C.subtype = T := by
    rw [hQ, Subgroup.map_subgroupOf_eq_of_le hsyl.le]
  have hxN : x ∈ Subgroup.normalizer (C : Set G) := hXC hx
  let φ : ↥C →* ↥C :=
    { toFun := fun c => ⟨x * (c : G) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxN c).mp c.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group }
  have hφsurj : Function.Surjective φ := by
    intro d
    refine ⟨⟨x⁻¹ * (d : G) * x, ?_⟩, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) d).mp d.2
    · ext
      show x * (x⁻¹ * (d : G) * x) * x⁻¹ = (d : G)
      group
  let Qx : Sylow 2 ↥C := Q.mapSurjective hφsurj
  obtain ⟨c, hc⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥C) Q Qx
  have hQx : (Qx : Subgroup ↥C) = (Q : Subgroup ↥C).map φ := by
    exact Sylow.coe_mapSurjective hφsurj Q
  have hconj : (Qx : Subgroup ↥C) = (Q : Subgroup ↥C).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hφeq : C.subtype.comp φ = (MulAut.conj x).toMonoidHom.comp C.subtype := by
    ext q
    rfl
  have hceq : C.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : G)).toMonoidHom.comp C.subtype := by
    ext q
    simp [MulAut.conj_apply]
  have hTconj : T.map (MulAut.conj x).toMonoidHom =
      T.map (MulAut.conj (c : G)).toMonoidHom := by
    have h1 : (Q : Subgroup ↥C).map (C.subtype.comp φ) =
        (Q : Subgroup ↥C).map (C.subtype.comp (MulAut.conj c).toMonoidHom) := by
      rw [← Subgroup.map_map, ← Subgroup.map_map, ← hQx, ← hconj]
    rw [hφeq, hceq] at h1
    rw [← Subgroup.map_map, ← Subgroup.map_map] at h1
    rwa [hQC] at h1
  set n : G := (c : G)⁻¹ * x with hn
  have hnX : n ∈ X := X.mul_mem (X.inv_mem (hCX c.2)) hx
  have hnN : n ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc T.map (MulAut.conj n).toMonoidHom
        = (T.map (MulAut.conj x).toMonoidHom).map (MulAut.conj ((c : G)⁻¹)).toMonoidHom := by
          rw [hn, Subgroup.map_map]
          congr 1
          ext t
          simp [MulAut.conj_apply, mul_assoc]
      _ = (T.map (MulAut.conj (c : G)).toMonoidHom).map
            (MulAut.conj ((c : G)⁻¹)).toMonoidHom := by rw [hTconj]
      _ = T := by
          rw [Subgroup.map_map]
          convert Subgroup.map_id T using 1
          ext t
          simp [MulAut.conj_apply, mul_assoc]
  refine ⟨n, Subgroup.mem_inf.mpr ⟨hnX, hnN⟩, n⁻¹ * (c : G) * n, ?_, ?_⟩
  · have hmem : n⁻¹ * (c : G) * n ∈ C := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXC hnX)) c).mp c.2
    exact hmem
  · rw [hn]
    group

theorem odd_card_centralizer_inf_of_isCharTwoType {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) (hchar : IsCharTwoType G)
    {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) :
    Odd (Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))) := by
  classical
  have hstd0 : StdTwD5 b₀ K E := hstd
  have hB0 : Adapted B b₀ K E := hB
  have hrec0 : RecOutTwD5 B b₀ := hrec
  obtain ⟨hGsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀ord, hKC, hKn, hKz, hKmark, hcyc, hrank, hconj, hEmax, hb₀E, hEcard, hXcard⟩ := hHyp
  obtain ⟨hdisj, hsup, hEKmax, hEKcard, hEKcent⟩ := hCanon
  obtain ⟨hBspan, hBb0, hBmem⟩ := hB
  obtain ⟨hrecCard, hrecNorm, hrecQuad, hrecFus⟩ := hrec
  obtain ⟨hfus1, hfus2⟩ := hfus
  set D : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) with hDdef
  rw [← Nat.not_even_iff_odd]
  intro hDeven
  obtain ⟨hKsimple, -⟩ :=
    isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num) hKmark hKz
  have hEelem : IsElemAbelian 3 E := hEmax.2.1
  have hb₀D : b₀ ∈ D := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hKD : K ≤ Subgroup.centralizer (D : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 k hk).symm
  have hED : E ≤ Subgroup.centralizer (D : Set G) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).1 b₀ (by simp)).symm
    · exact (inf_le_right.trans hKD)
  let T : Sylow 2 ↥D := Classical.choice Sylow.nonempty
  have hTne : (T : Subgroup ↥D) ≠ ⊥ := Sylow.ne_bot_of_dvd_card T hDeven.two_dvd
  set P : Subgroup G := (T : Subgroup ↥D).map D.subtype with hPdef
  have hPD : P ≤ D := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := (T.isPGroup').map D.subtype
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxP : (x : G) ∈ P := ⟨x, hx, rfl⟩
    rw [hbot] at hxP
    exact Subtype.ext (Subgroup.mem_bot.mp hxP)
  set W : Subgroup G := Subgroup.normalizer (P : Set G) with hWdef
  have hWloc : IsTwoLocal W := ⟨P, hPne, hP2, rfl⟩
  set S : Subgroup G := pCoreOf 2 W with hSdef
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W
  have hSW : S ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hWN : W ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 W
  have hPS : P ≤ S := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 P hP2
  have hcharW : W ⊓ Subgroup.centralizer (S : Set G) ≤ S := hchar W hWloc
  have hKW : K ≤ W := by
    intro k hk
    refine Subgroup.centralizer_le_normalizer (P : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hPD hp)).2 k hk).symm
  have hb₀W : b₀ ∈ W := by
    refine Subgroup.centralizer_le_normalizer (P : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hPD hp)).1 b₀ (by simp)).symm
  have hEW : E ≤ W := by
    rw [← hsup]
    exact sup_le (Subgroup.zpowers_le.mpr hb₀W) (inf_le_right.trans hKW)
  have hEKne : E ⊓ K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEKcard
    norm_num at hEKcard
  have hSK : S ⊓ K = ⊥ := by
    have hQ2 : IsPGroup 2 ↥(S ⊓ K) := hS2.to_le inf_le_left
    have hKN : K ≤ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
      have h1 : K ≤ Subgroup.normalizer (S : Set G) := hKW.trans hWN
      have h2 : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
      exact (le_inf h1 h2).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := K))
    have hQn : ((S ⊓ K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKN
    rcases (Subgroup.isSimpleGroup_iff.mp hKsimple).2 (S ⊓ K) inf_le_right hQn with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEKne
      have hx3 : (x : G) ^ 3 = 1 := hEelem.2 x x.2.1
      have hxord : orderOf (x : G) = 3 :=
        orderOf_eq_prime hx3 (by intro h1; exact hx1 (Subtype.ext h1))
      have hK2 : IsPGroup 2 K := h ▸ hQ2
      obtain ⟨n, hn⟩ := hK2.exists_orderOf_eq_pow ⟨(x : G), x.2.2⟩
      rw [Subgroup.orderOf_mk] at hn
      rw [hxord] at hn
      have h3dvd : 3 ∣ 2 ^ n := by rw [← hn]
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)
  have hCSb₀ : S ⊓ Subgroup.centralizer ({b₀} : Set G) = P := by
    refine le_antisymm ?_ ?_
    · intro s hs
      have hsC : s ∈ Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hconjS : s * k * s⁻¹ * k⁻¹ ∈ S := by
          have h1 : k * s * k⁻¹ ∈ S :=
            (Subgroup.mem_normalizer_iff.mp (hWN (hKW hk)) s).mp hs.1
          simpa [mul_assoc] using S.mul_mem hs.1 (S.inv_mem h1)
        have hconjK : s * k * s⁻¹ * k⁻¹ ∈ K := by
          have h2 : s * k * s⁻¹ ∈ K := by
            have hmem := hKn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
              ⟨s, hs.2⟩
            exact hmem
          simpa using K.mul_mem h2 (K.inv_mem hk)
        have hbot : s * k * s⁻¹ * k⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hSK]
          exact Subgroup.mem_inf.mpr ⟨hconjS, hconjK⟩
        have h1 : s * k * s⁻¹ * k⁻¹ = 1 := Subgroup.mem_bot.mp hbot
        have h2 : s * k * s⁻¹ = k := by
          have := congrArg (fun t => t * k) h1
          simpa [mul_assoc] using this
        have h3 : s * k = k * s := by
          have := congrArg (fun t => t * s) h2
          simpa [mul_assoc] using this
        exact h3.symm
      have hsD : s ∈ D := Subgroup.mem_inf.mpr ⟨hs.2, hsC⟩
      have hSD : S ⊓ D ≤ P := by
        have hQ2 : IsPGroup 2 ((S ⊓ D).subgroupOf D) := by
          have h1 : IsPGroup 2 ↥(S ⊓ D) := hS2.to_le inf_le_left
          exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ D ≤ D)).symm
        have hle : (T : Subgroup ↥D) ≤ (S ⊓ D).subgroupOf D := by
          intro x hx
          refine Subgroup.mem_subgroupOf.mpr ?_
          have hxP : (x : G) ∈ P := ⟨x, hx, rfl⟩
          exact Subgroup.mem_inf.mpr ⟨hPS hxP, hPD hxP⟩
        have hmax := T.is_maximal' hQ2 hle
        have hmap := congrArg (Subgroup.map D.subtype) hmax
        rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : S ⊓ D ≤ D), ← hPdef] at hmap
        exact hmap.le
      exact hSD (Subgroup.mem_inf.mpr ⟨hs.1, hsD⟩)
    · intro p hp
      exact Subgroup.mem_inf.mpr ⟨hPS hp, Subgroup.mem_inf.mp (hPD hp) |>.1⟩
  set C : Subgroup G := Subgroup.centralizer (E : Set G) with hCdef
  have hCeq : C = (E ⊓ K) ⊔ D := by
    rw [hCdef, hDdef]
    exact centralizer_span_eq_of_recOutTwD5 hstd0 hB0 hrec0
  have hDC : D ≤ C := hCeq ▸ le_sup_right
  have hPC : P ≤ C := hPD.trans hDC
  have hEKD : E ⊓ K ⊓ D = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨⟨-, hxK⟩, hxD⟩
    have hxC : x ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hxD).2
    have hxcenter : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (g : G) g.2)
    rw [hKz] at hxcenter
    have hx1 : (⟨x, hxK⟩ : ↥K) = 1 := Subgroup.mem_bot.mp hxcenter
    exact Subtype.ext_iff.mp hx1
  have hC2D : ∀ Q : Subgroup G, Q ≤ C → IsPGroup 2 Q → Q ≤ D := by
    intro Q hQC hQ2 q hq
    have hcomm : ∀ a ∈ E ⊓ K, ∀ b ∈ D, Commute a b := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 a (Subgroup.mem_inf.mp ha).2
    obtain ⟨a, ha, d, hd, had⟩ :=
      (CFSG.mem_sup_of_commute hcomm).mp (hCeq ▸ hQC hq)
    obtain ⟨k, hk⟩ := hQ2.exists_orderOf_eq_pow ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    have hqpow : q ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one q
    have ha3 : a ^ 3 = 1 := hEelem.2 a (Subgroup.mem_inf.mp ha).1
    have hpoweq : a ^ (2 ^ k) * d ^ (2 ^ k) = 1 := by
      have h1 : (a * d) ^ (2 ^ k) = 1 := by rw [had]; exact hqpow
      rwa [(hcomm a ha d hd).mul_pow] at h1
    have ha2 : a ^ (2 ^ k) = 1 := by
      have hmem : a ^ (2 ^ k) ∈ (E ⊓ K) ⊓ D := by
        refine Subgroup.mem_inf.mpr ⟨⟨?_, ?_⟩, ?_⟩
        · exact E.pow_mem (Subgroup.mem_inf.mp ha).1 _
        · exact K.pow_mem (Subgroup.mem_inf.mp ha).2 _
        · rw [eq_inv_of_mul_eq_one_left hpoweq]
          exact D.inv_mem (D.pow_mem hd _)
      rw [hEKD] at hmem
      exact Subgroup.mem_bot.mp hmem
    have ha1 : a = 1 := by
      have hdvd3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
      have hdvd2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one ha2
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      have h1 : orderOf a = 1 := by
        have hg : orderOf a ∣ 1 := by
          have h0 : orderOf a ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hdvd3 hdvd2
          rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at h0
        exact Nat.dvd_one.mp hg
      exact orderOf_eq_one_iff.mp h1
    rw [← had, ha1, one_mul]
    exact hd
  let TCsub : Subgroup ↥C := P.subgroupOf C
  have hTCmap : TCsub.map C.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPC
  have hTC2 : IsPGroup 2 TCsub := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hTCmax : ∀ {Q : Subgroup ↥C}, IsPGroup 2 ↥Q → TCsub ≤ Q → Q = TCsub := by
    intro Q hQ2 hle
    have hQg2 : IsPGroup 2 (Q.map C.subtype) := hQ2.map C.subtype
    have hQgD : Q.map C.subtype ≤ D := hC2D _ (Subgroup.map_subtype_le _) hQg2
    have hTle : (T : Subgroup ↥D) ≤ (Q.map C.subtype).subgroupOf D := by
      intro x hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hxP : (x : G) ∈ P := ⟨x, hx, rfl⟩
      rw [← hTCmap] at hxP
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
      rw [← hyx]
      exact Subgroup.mem_map_of_mem C.subtype (hle hy)
    have hQ2' : IsPGroup 2 ((Q.map C.subtype).subgroupOf D) :=
      hQg2.of_equiv (Subgroup.subgroupOfEquivOfLe hQgD).symm
    have hmax := T.is_maximal' hQ2' hTle
    have hQmapP : Q.map C.subtype = P := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQgD, hmax, hPdef]
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (hQmapP ▸ Subgroup.mem_map_of_mem C.subtype hx)
    · intro hx
      exact hle hx
  let TC : Sylow 2 ↥C := Sylow.mk TCsub hTC2 hTCmax
  have hPCsyl : IsSylowOf 2 P C := ⟨TC, by simpa using hTCmap⟩
  have hC_NE : C ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer (E : Set G)
  have hNE_NC : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_NE).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G))
  have hFratt : ∀ x ∈ Subgroup.normalizer (E : Set G),
      ∃ n ∈ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (P : Set G),
        ∃ c ∈ C, x = n * c :=
    exists_mul_mem_normalizer_of_sylow_of_normal hC_NE hNE_NC hPCsyl
  have hCSconj : ∀ w ∈ W, S ⊓ Subgroup.centralizer ({w * b₀ * w⁻¹} : Set G) = P := by
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (S : Set G) := hWN hw
    have hwinvN : w⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hwN
    have hwP : w ∈ Subgroup.normalizer (P : Set G) := hw
    have hwinvP : w⁻¹ ∈ Subgroup.normalizer (P : Set G) := Subgroup.inv_mem _ hwP
    refine le_antisymm ?_ ?_
    · intro s hs
      have h1 : w⁻¹ * s * w ∈ S := by
        simpa using (Subgroup.mem_normalizer_iff.mp hwinvN s).mp hs.1
      have h2 : w⁻¹ * s * w ∈ Subgroup.centralizer ({b₀} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hs2 : s * (w * b₀ * w⁻¹) = (w * b₀ * w⁻¹) * s :=
          Subgroup.mem_centralizer_singleton_iff.mp hs.2
        calc (w⁻¹ * s * w) * b₀ = w⁻¹ * (s * (w * b₀ * w⁻¹)) * w := by group
          _ = w⁻¹ * ((w * b₀ * w⁻¹) * s) * w := by rw [hs2]
          _ = b₀ * (w⁻¹ * s * w) := by group
      have h3 : w⁻¹ * s * w ∈ P := by
        rw [← hCSb₀]
        exact Subgroup.mem_inf.mpr ⟨h1, h2⟩
      have h4 : w * (w⁻¹ * s * w) * w⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hwP (w⁻¹ * s * w)).mp h3
      simpa [mul_assoc] using h4
    · intro p hp
      refine Subgroup.mem_inf.mpr ⟨hPS hp, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpP : w⁻¹ * p * w ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp hwinvP p).mp hp
      have hpC : w⁻¹ * p * w ∈ Subgroup.centralizer ({b₀} : Set G) :=
        (Subgroup.mem_inf.mp (hPD hpP)).1
      have hcomm : (w⁻¹ * p * w) * b₀ = b₀ * (w⁻¹ * p * w) :=
        Subgroup.mem_centralizer_singleton_iff.mp hpC
      calc p * (w * b₀ * w⁻¹) = w * (w⁻¹ * p * w) * b₀ * w⁻¹ := by group
        _ = w * (b₀ * (w⁻¹ * p * w)) * w⁻¹ := by
              rw [show w * (w⁻¹ * p * w) * b₀ * w⁻¹ =
                  w * ((w⁻¹ * p * w) * b₀) * w⁻¹ by group, hcomm]
        _ = (w * b₀ * w⁻¹) * p := by group
  have hline : ∀ y : G, y ∈ B.span →
      (∃ g : G, Subgroup.zpowers (g * b₀ * g⁻¹) = Subgroup.zpowers y) →
      S ⊓ Subgroup.centralizer ({y} : Set G) = P := by
    intro y hyB hconj
    obtain ⟨g, hg⟩ := hconj
    have hmemB : g * b₀ * g⁻¹ ∈ B.span := by
      have h1 : g * b₀ * g⁻¹ ∈ Subgroup.zpowers y := hg ▸ Subgroup.mem_zpowers _
      exact Subgroup.zpowers_le.mpr hyB h1
    obtain ⟨x, hxN, hxeq⟩ := hfus2 g hmemB
    obtain ⟨n, hn, c, hcC, hnc⟩ := hFratt x (hBspan ▸ hxN)
    have hcb : c * b₀ * c⁻¹ = b₀ := by
      have hcomm : b₀ * c = c * b₀ :=
        Subgroup.mem_centralizer_iff.mp hcC b₀ hb₀E
      rw [← hcomm]
      group
    have hnb : n * b₀ * n⁻¹ = x * b₀ * x⁻¹ := by
      rw [hnc]
      calc n * b₀ * n⁻¹ = n * (c * b₀ * c⁻¹) * n⁻¹ := by rw [hcb]
        _ = (n * c) * b₀ * (n * c)⁻¹ := by group
    have hgen : Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers y := by
      rw [hnb, ← hxeq, hg]
    have hcent : Subgroup.centralizer ({n * b₀ * n⁻¹} : Set G) =
        Subgroup.centralizer ({y} : Set G) := by
      have e1 : Subgroup.centralizer ({n * b₀ * n⁻¹} : Set G) =
          Subgroup.centralizer (Subgroup.zpowers (n * b₀ * n⁻¹) : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have e2 : Subgroup.centralizer (Subgroup.zpowers y : Set G) =
          Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      calc Subgroup.centralizer ({n * b₀ * n⁻¹} : Set G)
          = Subgroup.centralizer (Subgroup.zpowers (n * b₀ * n⁻¹) : Set G) := e1
        _ = Subgroup.centralizer (Subgroup.zpowers y : Set G) := by rw [hgen]
        _ = Subgroup.centralizer ({y} : Set G) := e2
    have hconjP := hCSconj n hn.2
    rwa [hcent] at hconjP
  have hb₁K : B.b 1 ∈ K := hBmem 1 (by decide)
  have hb₁E : B.b 1 ∈ E := by rw [← hBspan]; exact B.b_mem_span 1
  have hb₁ne : B.b 1 ≠ 1 := by
    intro h
    have h3 := B.ord 1
    rw [h, orderOf_one] at h3
    omega
  have hb₀notb₁ : b₀ ∉ Subgroup.zpowers (B.b 1) := by
    intro hb
    have hbK : b₀ ∈ K := Subgroup.zpowers_le.mpr hb₁K hb
    have hbot : b₀ ∈ (⊥ : Subgroup G) := hdisj.le_bot ⟨Subgroup.mem_zpowers b₀,
      Subgroup.mem_inf.mpr ⟨hb₀E, hbK⟩⟩
    rw [Subgroup.mem_bot] at hbot
    have h3 := hb₀ord
    rw [hbot, orderOf_one] at h3
    omega
  have hline1 : S ⊓ Subgroup.centralizer ({b₀ * (B.b 1) ^ (1 : ℤ)} : Set G) = P := by
    set e : Coords (5 + 1) := Pi.single 0 1 + Pi.single 1 1 with hedef
    have he0 : e 0 ≠ 0 := by rw [hedef]; decide
    have hwt2 : wt e = 2 := by rw [hedef]; decide
    have hne : e ≠ 0 := by intro h; rw [h] at he0; exact he0 rfl
    have hvec : B.vec e = b₀ * (B.b 1) ^ (1 : ℤ) := by
      rw [hedef, B.vec_add, B.vec_single, B.vec_single, hBb0, zpow_one]
    have hlineMem : b₀ * (B.b 1) ^ (1 : ℤ) ∈ B.span := by
      rw [← hvec]; exact B.vec_mem_span e
    refine hline _ hlineMem ?_
    obtain ⟨g, hg⟩ := (hrecFus e hne).mpr (Or.inl ⟨by omega, he0⟩)
    exact ⟨g, by
      rw [hg]
      show Subgroup.zpowers (B.vec e) = Subgroup.zpowers (b₀ * (B.b 1) ^ (1 : ℤ))
      rw [hvec]⟩
  have hline2 : S ⊓ Subgroup.centralizer ({b₀ * (B.b 1) ^ (2 : ℤ)} : Set G) = P := by
    set e : Coords (5 + 1) := Pi.single 0 1 + Pi.single 1 (-1) with hedef
    have he0 : e 0 ≠ 0 := by rw [hedef]; decide
    have hwt2 : wt e = 2 := by rw [hedef]; decide
    have hne : e ≠ 0 := by intro h; rw [h] at he0; exact he0 rfl
    have hvec : B.vec e = b₀ * (B.b 1) ^ (2 : ℤ) := by
      have h2 : (-1 : ZMod 3).val = 2 := by decide
      rw [hedef, B.vec_add, B.vec_single, B.vec_single_eq_pow, h2, hBb0]
      norm_num
    have hlineMem : b₀ * (B.b 1) ^ (2 : ℤ) ∈ B.span := by
      rw [← hvec]; exact B.vec_mem_span e
    refine hline _ hlineMem ?_
    obtain ⟨g, hg⟩ := (hrecFus e hne).mpr (Or.inl ⟨by omega, he0⟩)
    exact ⟨g, by
      rw [hg]
      show Subgroup.zpowers (B.vec e) = Subgroup.zpowers (b₀ * (B.b 1) ^ (2 : ℤ))
      rw [hvec]⟩
  have hline_zpow : ∀ j : ℤ, 0 ≤ j → j < 3 →
      S ⊓ Subgroup.centralizer ({b₀ * (B.b 1) ^ j} : Set G) = P := by
    intro j hj0 hj3
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · simpa using hCSb₀
    · exact hline1
    · exact hline2
  set A : Subgroup G := Subgroup.closure ({b₀, B.b 1} : Set G) with hAdef
  have hb₀A : b₀ ∈ A := Subgroup.subset_closure (by simp)
  have hb₁A : B.b 1 ∈ A := Subgroup.subset_closure (by simp)
  have hpair : ∀ a ∈ ({b₀, B.b 1} : Set G), ∀ b ∈ ({b₀, B.b 1} : Set G),
      a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · rw [← hBb0]; exact (B.comm 0 1).eq
    · rw [← hBb0]; exact (B.comm 1 0).eq
    · rfl
  have hpow3 : ∀ a ∈ ({b₀, B.b 1} : Set G), a ^ 3 = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · rw [← hBb0, ← B.ord 0]; exact pow_orderOf_eq_one _
    · rw [← B.ord 1]; exact pow_orderOf_eq_one _
  have hAelem : IsElemAbelian 3 A := IsElemAbelian.closure_of_commute hpair hpow3
  have hA3 : 3 ≤ Nat.card A := by
    have hdvd : 3 ∣ Nat.card A := by
      rw [← hb₀ord]
      exact Subgroup.orderOf_dvd_natCard A hb₀A
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hAW : A ≤ W := by
    rw [hAdef]
    refine (Subgroup.closure_le (K := W)).mpr ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact hb₀W
    · exact hKW hb₁K
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hAW.trans hWN
  have hcopS : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    (p := 3) Nat.prime_three hAelem hA3 hAS hcopS
  have hPCb₁ : P ≤ Subgroup.centralizer ({B.b 1} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hPD hp)).2
      (B.b 1) hb₁K).symm
  have hfinal : S ≤ Subgroup.centralizer ({B.b 1} : Set G) := by
    rw [← hgen]
    refine iSup_le fun H => iSup_le fun hH => ?_
    intro s hs
    obtain ⟨hHA, hHcard⟩ := hH
    by_cases hb₁H : B.b 1 ∈ H
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hs.2 (B.b 1) hb₁H).symm
    ·
      have hrelA : H.relIndex A = 3 := by
        have h1 := Subgroup.relIndex_mul_card (H := H) (K := A)
        rw [inf_eq_left.mpr hHA, hHcard] at h1
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
      set K' : Subgroup G := H ⊔ Subgroup.zpowers (B.b 1) with hK'def
      have hK'le : K' ≤ A := sup_le hHA (Subgroup.zpowers_le.mpr hb₁A)
      have hHleK' : H ≤ K' := le_sup_left
      have hrelmul : H.relIndex K' * K'.relIndex A = 3 := by
        rw [Subgroup.relIndex_mul_relIndex H K' A hHleK' hK'le, hrelA]
      have hrelK'ne : H.relIndex K' ≠ 1 := by
        intro h1
        have hK'leH : K' ≤ H := Subgroup.relIndex_eq_one.mp h1
        exact hb₁H (hK'leH (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      have hrelK' : H.relIndex K' = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp ⟨K'.relIndex A, hrelmul.symm⟩ with h | h
        · exact absurd h hrelK'ne
        · exact h
      have hAK' : A ≤ K' := by
        have h1 : K'.relIndex A = 1 := by
          rw [hrelK'] at hrelmul
          omega
        exact Subgroup.relIndex_eq_one.mp h1
      have hK'eq : K' = A := le_antisymm hK'le hAK'
      have hb₀K' : b₀ ∈ K' := hK'eq ▸ hb₀A
      have hcommHZ : ∀ a ∈ H, ∀ b ∈ Subgroup.zpowers (B.b 1), Commute a b := by
        intro a ha b hb
        exact hAelem.comm (hHA ha) (Subgroup.zpowers_le.mpr hb₁A hb)
      obtain ⟨h, hhH, z, hz, hz_eq⟩ := (CFSG.mem_sup_of_commute hcommHZ).mp hb₀K'
      obtain ⟨nn, hnn⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hh_form : h = b₀ * (B.b 1) ^ (-nn) := by
        rw [eq_mul_inv_of_mul_eq hz_eq, ← hnn, ← zpow_neg]
      set j : ℤ := -nn % 3 with hjdef
      have hj0 : 0 ≤ j := Int.emod_nonneg _ (by norm_num)
      have hj3 : j < 3 := Int.emod_lt_of_pos _ (by norm_num)
      have hb₁zpow : (B.b 1) ^ j = (B.b 1) ^ (-nn) := by
        have h3 : (orderOf (B.b 1) : ℤ) = 3 := by rw [B.ord 1]; norm_num
        rw [hjdef, ← h3, zpow_mod_orderOf]
      have hh_j : h = b₀ * (B.b 1) ^ j := by
        rw [hh_form, hb₁zpow]
      have hsh : s ∈ Subgroup.centralizer ({h} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hs.2 h hhH).symm
      have hsP : s ∈ P := by
        have hmem : s ∈ S ⊓ Subgroup.centralizer ({h} : Set G) :=
          Subgroup.mem_inf.mpr ⟨hs.1, hsh⟩
        rw [hh_j] at hmem
        rwa [hline_zpow j hj0 hj3] at hmem
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPCb₁ hsP)
  have hb₁CS : B.b 1 ∈ K ⊓ Subgroup.centralizer (S : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hb₁K, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hfinal hs)
  have hCKS : K ≤ Subgroup.centralizer (S : Set G) := by
    have hconjC : ∀ k ∈ K, ∀ x : G, x ∈ Subgroup.centralizer (S : Set G) →
        k * x * k⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
      intro k hk x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro s hs
      have hsk : k⁻¹ * s * k ∈ S := by
        have hkS : k ∈ Subgroup.normalizer (S : Set G) := hWN (hKW hk)
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkS) s).mp hs
      have hx' := hx (k⁻¹ * s * k) hsk
      have hcalc : (k * x * k⁻¹) * s = s * (k * x * k⁻¹) := by
        calc (k * x * k⁻¹) * s = k * (x * (k⁻¹ * s * k)) * k⁻¹ := by group
          _ = k * ((k⁻¹ * s * k) * x) * k⁻¹ := by rw [hx']
          _ = s * (k * x * k⁻¹) := by group
      exact hcalc.symm
    have hKN : K ≤ Subgroup.normalizer
        ((K ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
      have h1 : K ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
        intro k hk
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          exact hconjC k hk x hx
        · intro hx
          have := hconjC k⁻¹ (Subgroup.inv_mem _ hk) (k * x * k⁻¹) hx
          simpa [mul_assoc] using this
      have h2 : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
      have h3 := (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf
        (H := Subgroup.centralizer (S : Set G)) (K := K))
      rwa [inf_comm] at h3
    have hnormal : ((K ⊓ Subgroup.centralizer (S : Set G)).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKN
    rcases (Subgroup.isSimpleGroup_iff.mp hKsimple).2 _ inf_le_left hnormal with h | h
    · exfalso
      have hmem : B.b 1 ∈ (⊥ : Subgroup G) := h ▸ hb₁CS
      rw [Subgroup.mem_bot] at hmem
      exact hb₁ne hmem
    · intro x hx
      exact (Subgroup.mem_inf.mp (h ▸ hx)).2
  have hKleS : K ≤ S := by
    intro k hk
    exact hcharW (Subgroup.mem_inf.mpr ⟨hKW hk, hCKS hk⟩)
  have hK2 : IsPGroup 2 K := hS2.to_le hKleS
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEKne
  have hx3 : (x : G) ^ 3 = 1 := hEelem.2 x x.2.1
  have hxord : orderOf (x : G) = 3 :=
    orderOf_eq_prime hx3 (by intro h1; exact hx1 (Subtype.ext h1))
  obtain ⟨n, hn⟩ := hK2.exists_orderOf_eq_pow ⟨(x : G), x.2.2⟩
  rw [Subgroup.orderOf_mk] at hn
  rw [hxord] at hn
  have h3dvd : 3 ∣ 2 ^ n := by rw [← hn]
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

end CFSG.StandardType.FrameRoute.FS81

end
