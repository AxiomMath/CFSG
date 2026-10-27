module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPGen
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPSp4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218UR
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.GH72.Sec5DTools
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.Y2ConjugationInvariance

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private structure uc22s2122npSetup (D : Data G) (Ch : Choice2011 G) (c : Ctx21 D Ch)
    (L : Subgroup G) (s : ℕ) (b : G) where
  S : Subgroup G
  V : Subgroup G
  W : Subgroup G
  hS : IsSylowOf 2 S L
  hS_eq : S = D.T ⊓ L
  hbNL : b ∈ normalizer (L : Set G)
  hbS : b ∈ normalizer (S : Set G)
  hV : V = uc22s2122npV L S s
  hW : W = V ⊔ zpowers b
  hWM : W ≤ D.M
  hWN : W ≤ normalizer (S : Set G)
  hSW : S ≤ W
  hSnorm : (S.subgroupOf W).Normal
  hTV : D.T ≤ normalizer (V : Set G)
  hbV : b ∈ normalizer (V : Set G)
  hST : S ≤ D.T

private theorem uc22s2122np_setup_exists {D : Data G} {Ch : Choice2011 G} {c : Ctx21 D Ch}
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {s : ℕ} {b : G} (hbB0 : b ∈ c.B0) (hbT : b ∈ normalizer (D.T : Set G)) :
    Nonempty (uc22s2122npSetup D Ch c L s b) := by
  classical
  have hbM : b ∈ D.M := c.hBM hbB0
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hLN
  let S : Subgroup G := D.T ⊓ L
  have hS : IsSylowOf 2 S L := D.sylowM.inf_of_le_normalizer hL.1.le hML
  let V : Subgroup G := uc22s2122npV L S s
  let W : Subgroup G := V ⊔ zpowers b
  have hbNL : b ∈ normalizer (L : Set G) := hML hbM
  have hST : S ≤ D.T := inf_le_left
  have hTS : D.T ≤ normalizer (S : Set G) := by
    intro t ht
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer ht)
      (hML (D.sylowM.le ht))
  have hbS : b ∈ normalizer (S : Set G) := CFSG.ABGLocalTools.mem_normalizer_inf hbT hbNL
  have hVM : V ≤ D.M := (uc22s2122npV_le hS).trans hL.1.le
  have hWM : W ≤ D.M := sup_le hVM (Subgroup.zpowers_le.2 hbM)
  have hWN : W ≤ normalizer (S : Set G) :=
    sup_le uc22s2122npV_le_normalizer (Subgroup.zpowers_le.2 hbS)
  have hSW : S ≤ W := le_trans le_sup_left le_sup_left
  have hSnorm : (S.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSW).2 hWN
  have hTV : D.T ≤ normalizer (V : Set G) := by
    intro t ht
    exact uc22s2122npV_le_normalizer_of_mem (hML (D.sylowM.le ht)) (hTS ht)
  have hbV : b ∈ normalizer (V : Set G) :=
    uc22s2122npV_le_normalizer_of_mem hbNL hbS
  let d : uc22s2122npSetup D Ch c L s b :=
    { S := S, V := V, W := W, hS := hS, hS_eq := rfl, hbNL := hbNL, hbS := hbS, hV := rfl,
      hW := rfl, hWM := hWM, hWN := hWN, hSW := hSW, hSnorm := hSnorm, hTV := hTV,
      hbV := hbV, hST := hST }
  exact ⟨d⟩

private theorem uc22s2122np_quot_pgroup {L S V W : Subgroup G} {a s : ℕ}
    (hS : IsSylowOf 2 S L) (hV : V = uc22s2122npV L S s) (hX : IsSp4 (Bar2 L) a)
    (hs : s.Prime) (hs2 : s ≠ 2) {b : G} (hbNL : b ∈ normalizer (L : Set G))
    (hbS : b ∈ normalizer (S : Set G)) (hbs : b ^ s = 1) (hW : W = V ⊔ zpowers b)
    [hSnorm : (S.subgroupOf W).Normal] : IsPGroup s (↥W ⧸ S.subgroupOf W) := by
  haveI : Fact s.Prime := ⟨hs⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf W) x
  have hwW : (w : G) ∈ uc22s2122npV L S s ⊔ zpowers b := by
    have h1 : (w : G) ∈ V ⊔ zpowers b := hW ▸ w.2
    rwa [hV] at h1
  have hws : (w : G) ^ s ∈ S :=
    (uc22s2122npV_mod hS hX hs hs2 hbNL hbS hbs (w : G) hwW (w : G) hwW).2
  have h1 : (QuotientGroup.mk' (S.subgroupOf W) w) ^ s = 1 := by
    rw [← map_pow]
    change (QuotientGroup.mk' (S.subgroupOf W)) ((w : ↥W) ^ s) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hcoe : ((w : ↥W) ^ s : ↥W) = ⟨(w : G) ^ s, W.pow_mem w.2 s⟩ := by
      ext
      rfl
    rw [hcoe]
    exact hws
  have hdvd : orderOf (QuotientGroup.mk' (S.subgroupOf W) w) ∣ s :=
    orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hs).1 hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private theorem uc22s2122np_sylow_top {S W : Subgroup G}
    [hSnorm : (S.subgroupOf W).Normal] {s : ℕ} (hs : s.Prime) (hSW : S ≤ W)
    (hWN : W ≤ normalizer (S : Set G))
    (hquot : IsPGroup s (↥W ⧸ S.subgroupOf W)) {b : G} (hbW : b ∈ W)
    (hbs : orderOf b = s) :
    ∃ F : Subgroup G, F ≤ W ∧ b ∈ F ∧ IsSylowOf s F W ∧ W = S ⊔ F := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  let q : ↥W →* ↥W ⧸ S.subgroupOf W := QuotientGroup.mk' (S.subgroupOf W)
  have himage : IsPGroup s ↥((⊤ : Subgroup ↥W).map q) := by
    have htop : ((⊤ : Subgroup ↥W).map q : Subgroup (↥W ⧸ S.subgroupOf W)) = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rw [htop]
    exact hquot.of_equiv Subgroup.topEquiv.symm
  let bW : ↥W := ⟨b, hbW⟩
  have hbWo : orderOf bW = s := by rw [Subgroup.orderOf_mk, hbs]
  let bT : ↥(⊤ : Subgroup ↥W) := ⟨bW, Subgroup.mem_top bW⟩
  have hPb : IsPGroup s (Subgroup.zpowers bT) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hbWo, pow_one])
  obtain ⟨sylow, hPsylow⟩ := hPb.exists_le_sylow
  have hprod := CFSG.SignalizerFunctor.Helpers.normal_pgroup_quotient_sylow_product s hs
    (S.subgroupOf W) ⊤ le_top himage sylow
  let F : Subgroup G := ((sylow : Subgroup (⊤ : Subgroup ↥W)).map
    (⊤ : Subgroup ↥W).subtype).map W.subtype
  have hFsyl : IsSylowOf s F W := by
    have hA : IsSylowOf s ((sylow : Subgroup (⊤ : Subgroup ↥W)).map
        (⊤ : Subgroup ↥W).subtype) ⊤ := ⟨sylow, rfl⟩
    have h := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff W).mpr hA
    simpa [F, Subgroup.map_top, Subgroup.range_subtype] using h
  have hWF : W = S ⊔ F := by
    have hmap := congrArg (Subgroup.map W.subtype) hprod
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSW] at hmap
    exact hmap
  have hbF : b ∈ F := by
    refine Subgroup.mem_map.2 ⟨(⊤ : Subgroup ↥W).subtype bT, ?_, rfl⟩
    exact Subgroup.mem_map.2 ⟨bT, hPsylow (Subgroup.mem_zpowers bT), rfl⟩
  exact ⟨F, hWF ▸ le_sup_right, hbF, hFsyl, hWF⟩

private theorem uc22s2122np_exists_sylow {S W : Subgroup G}
    [hSnorm : (S.subgroupOf W).Normal] {s : ℕ} (hs : s.Prime) (hSW : S ≤ W)
    (hWN : W ≤ normalizer (S : Set G))
    (hquot : IsPGroup s (↥W ⧸ S.subgroupOf W)) {b : G} (hbW : b ∈ W)
    (hbs : orderOf b = s) :
    ∃ F : Subgroup G, F ≤ W ∧ b ∈ F ∧ IsSylowOf s F W ∧ W = S ⊔ F ∧
      (W : Set G) = (F : Set G) * (S : Set G) := by
  obtain ⟨F, hFle, hbF, hFsyl, hWF⟩ :=
    uc22s2122np_sylow_top hs hSW hWN hquot hbW hbs
  have hFS : (W : Set G) = (F : Set G) * (S : Set G) := by
    rw [hWF, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right F S (hFle.trans hWN)
  exact ⟨F, hFle, hbF, hFsyl, hWF, hFS⟩

private theorem uc22s2122np_W_comm {V T W : Subgroup G} {b : G}
    (hWdef : W = V ⊔ zpowers b) (hTV : T ≤ normalizer (V : Set G))
    (hbV : b ∈ normalizer (V : Set G)) (hbT : b ∈ normalizer (T : Set G)) :
    (W : Set G) * (T : Set G) = (T : Set G) * (W : Set G) := by
  have hVTcomm : (V : Set G) * (T : Set G) = (T : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V T hTV,
      ← Subgroup.coe_mul_of_left_le_normalizer_right T V hTV, sup_comm]
  have hbTcomm : (Subgroup.zpowers b : Set G) * (T : Set G) =
      (T : Set G) * (Subgroup.zpowers b : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers b) T
        (Subgroup.zpowers_le.2 hbT),
      ← Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers b)
        (Subgroup.zpowers_le.2 hbT), sup_comm]
  calc (W : Set G) * (T : Set G)
      = ((V : Set G) * (Subgroup.zpowers b : Set G)) * (T : Set G) := by
        rw [hWdef, Subgroup.coe_mul_of_right_le_normalizer_left V (Subgroup.zpowers b)
          (Subgroup.zpowers_le.2 hbV)]
    _ = (V : Set G) * ((Subgroup.zpowers b : Set G) * (T : Set G)) := by rw [mul_assoc]
    _ = (V : Set G) * ((T : Set G) * (Subgroup.zpowers b : Set G)) := by rw [hbTcomm]
    _ = ((V : Set G) * (T : Set G)) * (Subgroup.zpowers b : Set G) := by rw [mul_assoc]
    _ = ((T : Set G) * (V : Set G)) * (Subgroup.zpowers b : Set G) := by rw [hVTcomm]
    _ = (T : Set G) * ((V : Set G) * (Subgroup.zpowers b : Set G)) := by rw [mul_assoc]
    _ = (T : Set G) * (W : Set G) := by
        rw [hWdef, Subgroup.coe_mul_of_right_le_normalizer_left V (Subgroup.zpowers b)
          (Subgroup.zpowers_le.2 hbV)]

private theorem uc22s2122np_sylow_mul_comm {V S T F W : Subgroup G} {b : G}
    (hWdef : W = V ⊔ zpowers b) (hTV : T ≤ normalizer (V : Set G))
    (hbV : b ∈ normalizer (V : Set G)) (hbT : b ∈ normalizer (T : Set G))
    (hST : S ≤ T) (hWF : W = S ⊔ F) (hFS : (W : Set G) = (F : Set G) * (S : Set G)) :
    ((F ⊔ T : Subgroup G) : Set G) = (F : Set G) * (T : Set G) := by
  have hWcomm := uc22s2122np_W_comm hWdef hTV hbV hbT
  have hWmul : ((W ⊔ T : Subgroup G) : Set G) = (W : Set G) * (T : Set G) :=
    CFSG.GH72.G5d.coe_sup_eq_mul_of_mul_comm hWcomm
  have hsup : W ⊔ T = F ⊔ T := by
    rw [hWF, sup_assoc, sup_eq_right.mpr (hST.trans le_sup_right)]
  have hSTmul : (S : Set G) * (T : Set G) = (T : Set G) := by
    ext x
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact T.mul_mem (hST hs) ht
    · intro hx
      exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  have hFT : (F : Set G) * (T : Set G) = (W : Set G) * (T : Set G) := by
    rw [hFS, mul_assoc, hSTmul]
  rw [← hsup, hWmul, ← hFT]

private theorem uc22s2122np_sylow_inf_bot {L S W F : Subgroup G} {s : ℕ}
    (hS : IsSylowOf 2 S L) (hs : s.Prime) (hs2 : s ≠ 2) (hFsyl : IsSylowOf s F W) :
    F ⊓ S = ⊥ := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hFp : IsPGroup s F := hFsyl.isPGroup
  have hSp : IsPGroup 2 S := hS.isPGroup
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  obtain ⟨m, hm⟩ := hSp.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hk, hm]
  exact (Nat.Coprime.pow_left k ((Nat.coprime_primes hs Nat.prime_two).2 hs2)).pow_right m

private theorem uc22s2122np_sylow_isElemAbelian {D : Data G} {L S V W F : Subgroup G} {a s : ℕ}
    (hS : IsSylowOf 2 S L) (hV : V = uc22s2122npV L S s) (hX : IsSp4 (Bar2 L) a)
    (hs : s.Prime) (hs2 : s ≠ 2) {b : G} (hbNL : b ∈ normalizer (L : Set G))
    (hbS : b ∈ normalizer (S : Set G)) (hbs : b ^ s = 1) (hW : W = V ⊔ zpowers b)
    {F : Subgroup G} (hFW : F ≤ W) (hFSbot : F ⊓ S = ⊥) :
    CFSG.Open.IsElemAbelian s F := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hmod := uc22s2122npV_mod hS hX hs hs2 hbNL hbS hbs
  have hFW' : ∀ x ∈ F, (x : G) ∈ uc22s2122npV L S s ⊔ zpowers b := by
    intro x hx
    have h1 : (x : G) ∈ V ⊔ zpowers b := hW ▸ hFW hx
    simpa [hV] using h1
  have hFcomm : IsMulCommutative F := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    have hcS : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ S :=
      (hmod x (hFW' x x.2) y (hFW' y y.2)).1
    have hcF : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ F :=
      F.mul_mem (F.mul_mem (F.mul_mem x.2 y.2) (F.inv_mem x.2)) (F.inv_mem y.2)
    have hc1 : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ = 1 := by
      have hmem : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ F ⊓ S := ⟨hcF, hcS⟩
      rw [hFSbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    calc (x : G) * (y : G) = ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) *
          ((y : G) * (x : G)) := by group
      _ = (y : G) * (x : G) := by rw [hc1, one_mul]
  have hFexp : ∀ x ∈ F, x ^ s = 1 := by
    intro x hx
    have hpS : x ^ s ∈ S := (hmod x (hFW' x hx) x (hFW' x hx)).2
    have hpF : x ^ s ∈ F := F.pow_mem hx s
    have hmem : x ^ s ∈ F ⊓ S := ⟨hpF, hpS⟩
    rw [hFSbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact ⟨hFcomm, hFexp⟩

private theorem uc22s2122np_sylow_elem {D : Data G} {L S V W F : Subgroup G} {a s : ℕ}
    (hS : IsSylowOf 2 S L) (hV : V = uc22s2122npV L S s) (hX : IsSp4 (Bar2 L) a)
    (hs : s.Prime) (hs2 : s ≠ 2) {b : G} (hbNL : b ∈ normalizer (L : Set G))
    (hbS : b ∈ normalizer (S : Set G)) (hbs : b ^ s = 1) (hW : W = V ⊔ zpowers b)
    {F : Subgroup G} (hFW : F ≤ W) (hFsyl : IsSylowOf s F W) (hWM : W ≤ D.M)
    (hrk : CFSG.Open.pRank s D.M ≤ 2) :
    CFSG.Open.IsElemAbelian s F ∧ Nat.card F ∣ s ^ 2 := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hFSbot : F ⊓ S = ⊥ := uc22s2122np_sylow_inf_bot hS hs hs2 hFsyl
  have hFelem := uc22s2122np_sylow_isElemAbelian (D := D) (F := F) hS hV hX hs hs2 hbNL hbS
    hbs hW hFW hFSbot
  have hFM : F ≤ D.M := hFW.trans hWM
  obtain ⟨k, hk⟩ := hFsyl.isPGroup.exists_card_eq
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank hs.one_lt hFM hFelem hk).trans hrk
  refine ⟨hFelem, ?_⟩
  rw [hk]
  exact Nat.pow_dvd_pow s (by omega)

private theorem uc22s2122np_conj_X {D : Data G} {W F X : Subgroup G} {s : ℕ}
    (hs : s.Prime) (hFsyl : IsSylowOf s F W) (hXW : X ≤ W) (hXp : IsPGroup s X)
    (hXU : X ∈ uniqueSet D.M) (hWM : W ≤ D.M) :
    ∃ X' : Subgroup G, X' ≤ F ∧ Nat.card X' = Nat.card X ∧ X' ∈ uniqueSet D.M := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  obtain ⟨w, hwW, hwX⟩ := UC6.exists_conj_le_of_isSylowOf hFsyl hXW hXp
  refine ⟨X.map (MulAut.conj w⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hwX y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective]
  · exact (CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.mem_uniqueSet_map_iff
      (D.M.inv_mem (hWM hwW)) X).mpr hXU

private theorem uc22s2122np_X_pgroup_le {L S V X : Subgroup G} {s : ℕ}
    (hV : V = uc22s2122npV L S s) (hXcard : Nat.card X = s)
    (hXle : X ≤ L ⊓ normalizer (S : Set G)) :
    IsPGroup s X ∧ X ≤ V := by
  have hXp : IsPGroup s X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hXexp : ∀ x ∈ X, x ^ s = 1 := by
    intro x hx
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (Subgroup.orderOf_dvd_natCard X hx).trans (by rw [hXcard])
  refine ⟨hXp, ?_⟩
  intro x hx
  rw [hV]
  exact uc22s2122npV_mem (hXle hx).1 (hXle hx).2 (hXexp x hx)

theorem uc22s2122np_false_of_dvd {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (hSg : UC6S846.SigmaStd D)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    (h218UR : S21_8UR D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {a : ℕ} (ha : Odd a) (hX : IsSp4 (Bar2 L) a) {b : G} (hbB0 : b ∈ c.B0)
    (hbT : b ∈ normalizer (D.T : Set G)) {s : ℕ} (hs : s.Prime) (hbs : orderOf b = s)
    (hsa : s ∣ 2 ^ a - 1) : False := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  have hs2 : s ≠ 2 := uc22p218c_ne_two_of_dvd (by obtain ⟨k, rfl⟩ := ha; omega) hsa
  have hbs' : b ^ s = 1 := hbs ▸ pow_orderOf_eq_one b
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hLN
  obtain ⟨d⟩ := uc22s2122np_setup_exists (s := s) hL hLN hbB0 hbT
  letI : (d.S.subgroupOf d.W).Normal := d.hSnorm
  have hquot := uc22s2122np_quot_pgroup d.hS d.hV hX hs hs2 d.hbNL d.hbS hbs' d.hW
  have hbW : b ∈ d.W := d.hW ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  obtain ⟨F, hFW, hbF, hFsyl, hWF, hFS⟩ :=
    uc22s2122np_exists_sylow hs d.hSW d.hWN hquot hbW hbs
  have hFT := uc22s2122np_sylow_mul_comm d.hW d.hTV d.hbV hbT d.hST hWF hFS
  have hrk : CFSG.Open.pRank s D.M ≤ 2 :=
    uc22s2122np_pRank_le_two hSg h211 h1930 c hσ hL hML hX ha hs hsa
  obtain ⟨hFelem, hFdvd⟩ := uc22s2122np_sylow_elem (F := F) d.hS d.hV hX hs hs2
    d.hbNL d.hbS hbs' d.hW hFW hFsyl d.hWM hrk
  obtain ⟨X, hXcard, hXle, hXU⟩ := h218UR h1930 c L hL a ha hX s hs hsa
  have hXle' : X ≤ L ⊓ normalizer (d.S : Set G) := by
    rw [d.hS_eq]
    exact hXle
  obtain ⟨hXp, hXV⟩ := uc22s2122np_X_pgroup_le d.hV hXcard hXle'
  have hXW : X ≤ d.W := d.hW ▸ (hXV.trans le_sup_left)
  obtain ⟨X', hX'F, hX'card, hX'U⟩ := uc22s2122np_conj_X hs hFsyl hXW hXp hXU d.hWM
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hbs
    exact hs.ne_one hbs.symm
  exact uc22s2122np_false_of_permutes h211 h1930 c hH₁ hH₂ hL0 hfX hs hs2
    (hFW.trans d.hWM) hFsyl.isPGroup hFdvd hFT hbF ((c.hB0).1 hbB0) hb1
    hX'F (hX'card.trans hXcard) hX'U

end CFSG.LocalAnalysis.UniquenessCase.UC22
