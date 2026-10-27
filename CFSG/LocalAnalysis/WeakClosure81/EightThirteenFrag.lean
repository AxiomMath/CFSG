module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFaithful
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

variable {G : Type} [Group G] [Finite G]

private theorem omegaOneCenterOf_le_eGrp (H T : Subgroup G) :
    omegaOneCenterOf T ≤ eGrp H T := le_conjClosure _ _

private theorem omegaOneCenterOf_ne_bot' {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    omegaOneCenterOf T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hZ : Nontrivial (Subgroup.center ↥T) := hT.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := ((hT.to_subgroup (Subgroup.center ↥T)).nontrivial_iff_card).1 hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  intro hbot
  have hmem : ((z : ↥T) : G) ∈ omegaOneCenterOf T := by
    apply Subgroup.subset_closure
    refine ⟨⟨(z : ↥T).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)
    · have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have h3 := congrArg (fun w : Subgroup.center ↥T => ((w : ↥T) : G)) h2
      simpa using h3
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

private theorem eGrp_facts {V H T : Subgroup G} (hV7 : Hyp7 V) (hH0 : IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ normalizer (V : Set G))) :
    IsElemAbelian 2 (eGrp H T) ∧ eGrp H T ≤ H ∧ H ≤ normalizer (eGrp H T : Set G) := by
  have hH : IsCalH V H := hH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hEO : eGrp H T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
    have hC : omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
      intro c hc
      have hcT : c ∈ T := omegaOneCenterOf_le T hc
      have hcC : ∀ y ∈ T, y * c = c * y := fun y hy =>
        mem_centralizer_of_mem_omegaOneCenterOf hc hy
      have hcCen : c ∈ centralizer (pCoreOf 2 H : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => hcC y (hO2T hy)
      have hcO2 : c ∈ pCoreOf 2 H := hH.2.1 ⟨hTH.le hcT, hcCen⟩
      exact mem_omegaOneCenterOf hcO2 (fun y hy => hcC y (hO2T hy))
        ((B2F.isElemAbelian_omegaOneCenterOf T).2 c hc)
    unfold eGrp
    refine conjClosure_le fun h hh c hc => ?_
    have hHnorm : H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H).trans
        (normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H))
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm hh) c).1 (hC hc)
  exact ⟨CFSG.Open.IsElemAbelian.mono (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 H)) hEO,
    hEO.trans ((omegaOneCenterOf_le _).trans (CFSG.openPCoreOf_le 2 H)),
    le_normalizer_conjClosure _ _⟩

private def oTwoSet (N K : Subgroup G) : Set (Subgroup G) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧ ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N}

private theorem oTwoMod_eq_iSup (N K : Subgroup G) :
    oTwoMod N K = ⨆ W ∈ oTwoSet N K, W := rfl

private theorem le_oTwoMod_of {N K W : Subgroup G} (hNW : N ≤ W) (hWK : W ≤ K)
    (hWnorm : (W.subgroupOf K).Normal)
    (hpow : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N) : W ≤ oTwoMod N K :=
  le_iSup₂ (f := fun W (_ : W ∈ oTwoSet N K) => W) W ⟨hNW, hWK, hWnorm, hpow⟩

private theorem le_oTwoMod {N K : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) : N ≤ oTwoMod N K :=
  le_oTwoMod_of le_rfl hNK hN (fun w hw => ⟨0, by simpa using hw⟩)

private theorem oTwoMod_le {N K : Subgroup G} : oTwoMod N K ≤ K :=
  iSup₂_le fun _ hW => hW.2.1

private theorem normal_oTwoMod {N K : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) : ((oTwoMod N K).subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le]
  have hle : K ≤ ⨅ x : oTwoSet N K, Subgroup.normalizer ((x : Subgroup G) : Set G) := by
    intro k hk
    simp only [Subgroup.mem_iInf]
    intro x
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer x.2.2.1).mp x.2.2.2.1 hk
  have hsup : (⨆ x : oTwoSet N K, (x : Subgroup G)) = oTwoMod N K :=
    (iSup_subtype'' (oTwoSet N K) id).trans (oTwoMod_eq_iSup N K).symm
  intro k hk
  have hk' := Subgroup.iInf_normalizer_le_normalizer_iSup
    (fun x : oTwoSet N K => (x : Subgroup G)) (hle hk)
  rwa [hsup] at hk'

private theorem conj_mem_oTwoSet {N K : Subgroup G} {h : G}
    (hhN : h ∈ Subgroup.normalizer (N : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G))
    {W : Subgroup G} (hW : W ∈ oTwoSet N K) : conjSubgroup W h ∈ oTwoSet N K := by
  have hleK : conjSubgroup W h ≤ K := by
    calc conjSubgroup W h ≤ conjSubgroup K h := Subgroup.map_mono hW.2.1
      _ = K := conjSubgroup_eq_iff_mem_normalizer.mpr hhK
  refine ⟨?_, hleK, ?_, ?_⟩
  · calc N = conjSubgroup N h := (conjSubgroup_eq_iff_mem_normalizer.mpr hhN).symm
      _ ≤ conjSubgroup W h := Subgroup.map_mono hW.1
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hleK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [mem_conjSubgroup_iff] at hx ⊢
      have hkK : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hhK k).1 hk
      have hWnorm : K ≤ Subgroup.normalizer (W : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hW.2.1).mp hW.2.2.1
      have hconj : (h * k * h⁻¹) * (h * x * h⁻¹) * (h * k * h⁻¹)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWnorm hkK) (h * x * h⁻¹)).1 hx
      simpa [mul_assoc] using hconj
    · intro hx
      rw [mem_conjSubgroup_iff] at hx ⊢
      have hkK : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hhK k).1 hk
      have hWnorm : K ≤ Subgroup.normalizer (W : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hW.2.1).mp hW.2.2.1
      exact (Subgroup.mem_normalizer_iff.mp (hWnorm hkK) (h * x * h⁻¹)).2
        (by simpa [mul_assoc] using hx)
  · intro w' hw'
    rw [mem_conjSubgroup_iff] at hw'
    obtain ⟨k, hk⟩ := hW.2.2.2 (h * w' * h⁻¹) hw'
    refine ⟨k, ?_⟩
    rw [← conjSubgroup_eq_iff_mem_normalizer.mpr hhN, mem_conjSubgroup_iff, ← conj_pow]
    exact hk

private theorem normalizer_oTwoMod {N K : Subgroup G} :
    Subgroup.normalizer (N : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (oTwoMod N K : Set G) := by
  have hsup : (⨆ x : oTwoSet N K, (x : Subgroup G)) = oTwoMod N K :=
    (iSup_subtype'' (oTwoSet N K) id).trans (oTwoMod_eq_iSup N K).symm
  have key : ∀ h ∈ Subgroup.normalizer (N : Set G),
      h ∈ Subgroup.normalizer (K : Set G) → ∀ x ∈ oTwoMod N K, h * x * h⁻¹ ∈ oTwoMod N K := by
    intro h hhN hhK x hx
    have hhN' : h⁻¹ ∈ Subgroup.normalizer (N : Set G) := (Subgroup.normalizer _).inv_mem hhN
    have hhK' : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer _).inv_mem hhK
    have hx' : x ∈ ⨆ W : oTwoSet N K, (W : Subgroup G) := by rwa [hsup]
    have hgoal : h * x * h⁻¹ ∈ ⨆ W : oTwoSet N K, (W : Subgroup G) := by
      refine Subgroup.iSup_induction (fun W : oTwoSet N K => (W : Subgroup G))
        (C := fun a => h * a * h⁻¹ ∈ ⨆ W : oTwoSet N K, (W : Subgroup G)) hx' ?_ ?_ ?_
      · intro W a haW
        have hWmem : conjSubgroup (W : Subgroup G) h⁻¹ ∈ oTwoSet N K :=
          conj_mem_oTwoSet hhN' hhK' W.2
        have hmem : h * a * h⁻¹ ∈ conjSubgroup (W : Subgroup G) h⁻¹ := by
          rw [mem_conjSubgroup_iff]
          have heq : h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a := by group
          rwa [heq]
        exact Subgroup.mem_iSup_of_mem ⟨conjSubgroup (W : Subgroup G) h⁻¹, hWmem⟩ hmem
      · simpa using Subgroup.one_mem (⨆ W : oTwoSet N K, (W : Subgroup G))
      · intro a b ha hb
        rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
        exact (⨆ W : oTwoSet N K, (W : Subgroup G)).mul_mem ha hb
    rwa [hsup] at hgoal
  intro g hg
  obtain ⟨hgN, hgK⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact key g hgN hgK x hx
  · intro hx
    have h := key g⁻¹ ((Subgroup.normalizer _).inv_mem hgN) ((Subgroup.normalizer _).inv_mem hgK)
      (g * x * g⁻¹) hx
    simpa [mul_assoc] using h

private theorem exists_pow_mem_oTwoMod {N K : Subgroup G} (hN : (N.subgroupOf K).Normal)
    {n : G} (hn : n ∈ oTwoMod N K) : ∃ k : ℕ, n ^ 2 ^ k ∈ N := by
  haveI : (N.subgroupOf K).Normal := hN
  have hnK : n ∈ K := oTwoMod_le hn
  let Sset : Set (Subgroup G) := oTwoSet N K
  let Q := ↥K ⧸ (N.subgroupOf K)
  let q : ↥K →* Q := QuotientGroup.mk' (N.subgroupOf K)
  let P : Subgroup Q := ⨆ W ∈ Sset, (W.subgroupOf K).map q
  have hP2 : IsPGroup 2 P := by
    refine Sylow.biSup_of_normal Sset (fun W => (W.subgroupOf K).map q) ?_ ?_
    · intro W hW
      intro y
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp y.2
      have hk := hW.2.2.2 (w : G) (by simpa [Subgroup.mem_subgroupOf] using hw)
      obtain ⟨k, hk⟩ := hk
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hwy, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hk)
    · intro W hW
      exact (hW.2.2.1).map q (QuotientGroup.mk'_surjective _)
  have hsup : (⨆ x : Sset, (x : Subgroup G)) = oTwoMod N K :=
    (iSup_subtype'' Sset id).trans (oTwoMod_eq_iSup N K).symm
  have hC : ∃ (hnK : n ∈ K), (q ⟨n, hnK⟩ : Q) ∈ P := by
    have hn' : n ∈ ⨆ x : Sset, (x : Subgroup G) := by rwa [hsup]
    have aux : ∀ a ∈ ⨆ x : Sset, (x : Subgroup G),
        ∃ (haK : a ∈ K), (q ⟨a, haK⟩ : Q) ∈ P := by
      intro a ha
      refine Subgroup.iSup_induction (fun x : Sset => (x : Subgroup G))
        (C := fun a => ∃ (haK : a ∈ K), (q ⟨a, haK⟩ : Q) ∈ P) ha ?_ ?_ ?_
      · intro x b hbx
        have hbK : b ∈ K := x.2.2.1 hbx
        refine ⟨hbK, ?_⟩
        have hmem : q ⟨b, hbK⟩ ∈ (x.1.subgroupOf K).map q :=
          Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, by simpa [Subgroup.mem_subgroupOf] using hbx, rfl⟩
        exact le_iSup₂ (f := fun W (_ : W ∈ Sset) => (W.subgroupOf K).map q) x.1 x.2 hmem
      · refine ⟨K.one_mem, ?_⟩
        convert P.one_mem using 1
        show q (1 : ↥K) = 1
        exact map_one q
      · intro a b ha hb
        obtain ⟨haK, hqa⟩ := ha
        obtain ⟨hbK, hqb⟩ := hb
        refine ⟨K.mul_mem haK hbK, ?_⟩
        have hqab : q ⟨a * b, K.mul_mem haK hbK⟩ = q ⟨a, haK⟩ * q ⟨b, hbK⟩ := by
          rw [show (⟨a * b, K.mul_mem haK hbK⟩ : ↥K) = ⟨a, haK⟩ * ⟨b, hbK⟩ from rfl,
            map_mul]
        rw [hqab]
        exact P.mul_mem hqa hqb
    exact aux n hn'
  obtain ⟨hnK', hqnP⟩ := hC
  obtain ⟨k, hk⟩ := hP2 ⟨q ⟨n, hnK'⟩, hqnP⟩
  refine ⟨k, ?_⟩
  have hk' : (q ⟨n, hnK'⟩ : Q) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← map_pow] at hk'
  have hkN : (⟨n, hnK'⟩ : ↥K) ^ 2 ^ k ∈ N.subgroupOf K :=
    (QuotientGroup.eq_one_iff _).mp hk'
  simpa [Subgroup.mem_subgroupOf] using hkN

private theorem relIndex_eq_pow_two_of_pow_mem {C N : Subgroup G} (hCN : C ≤ N)
    (hN : (C.subgroupOf N).Normal)
    (hpow : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ C) : ∃ k : ℕ, C.relIndex N = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (C.subgroupOf N).Normal := hN
  let Q := ↥N ⧸ (C.subgroupOf N)
  have hQ : IsPGroup 2 Q := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf N) x
    obtain ⟨k, hk⟩ := hpow (y : G) y.2
    exact ⟨k, by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hk)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  refine ⟨k, ?_⟩
  change Nat.card Q = 2 ^ k
  exact hk

private theorem cGrp_normal_subgroupOf_K {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ((cGrp H T).subgroupOf K).Normal := by
  have hc := h.concl813
  have hCH : cGrp H T ≤ H := hc.comp.2.1.trans hc.comp.2.2.1
  have hKH : K ≤ H := hc.sub_L.trans hc.comp.2.2.1
  have hHnorm : H ≤ Subgroup.normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp hc.comp.1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hc.ge_C).mpr (hKH.trans hHnorm)

private theorem cenTMod_mem_normalizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {t : G} (ht : t ∈ cenTMod (cGrp H T) L T) :
    t ∈ normalizer (K : Set G) := by
  obtain ⟨-, htC⟩ := ht
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  have h1 : t * k * t⁻¹ * k⁻¹ ∈ cGrp H T := htC k (h.concl813.sub_L hk)
  have h2 : (t * k * t⁻¹ * k⁻¹) * k ∈ K := K.mul_mem (h.concl813.ge_C h1) hk
  have h3 : t * k * t⁻¹ = (t * k * t⁻¹ * k⁻¹) * k := by group
  rw [h3]
  exact h2

private theorem mem_rGrp_iff {H T K : Subgroup G} {t : G} :
    t ∈ rGrp H T K ↔ t ∈ T ∧ t ∈ normalizer (K : Set G) ∧
      ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K := by
  have hnk : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le
  have key : ∀ {x : G}, x ∈ T ∧ x ∈ normalizer (K : Set G) ∧
      (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) →
      x ∈ normalizer (oTwoMod (cGrp H T) K : Set G) := by
    rintro x ⟨-, -, hx⟩
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have h1 : x * n * x⁻¹ * n⁻¹ ∈ oTwoMod (cGrp H T) K := hx n (hnk hn)
    have h2 : (x * n * x⁻¹ * n⁻¹) * n ∈ oTwoMod (cGrp H T) K :=
      (oTwoMod (cGrp H T) K).mul_mem h1 hn
    have h3 : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [h3]
    exact h2
  constructor
  · intro ht
    unfold rGrp at ht
    refine Subgroup.closure_induction
      (p := fun t _ => t ∈ T ∧ t ∈ normalizer (K : Set G) ∧
        ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) ?_ ?_ ?_ ?_ ht
    · rintro t ⟨htT, htK, htC⟩; exact ⟨htT, htK, htC⟩
    · exact ⟨T.one_mem, (Subgroup.normalizer _).one_mem, fun k _ => by simp⟩
    · rintro x y _ _ ⟨hxT, hxK, hxC⟩ ⟨hyT, hyK, hyC⟩
      refine ⟨T.mul_mem hxT hyT, (Subgroup.normalizer _).mul_mem hxK hyK, fun k hk => ?_⟩
      have hxN : x ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) :=
        key ⟨hxT, hxK, hxC⟩
      have hyb : y * k * y⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K := hyC k hk
      have heq : (x * y) * k * (x * y)⁻¹ * k⁻¹ =
          (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
      rw [heq]
      exact (oTwoMod (cGrp H T) K).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hxN _).1 hyb) (hxC k hk)
    · rintro x _ ⟨hxT, hxK, hxC⟩
      have hxN : x ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) := key ⟨hxT, hxK, hxC⟩
      have hxN' : x⁻¹ ∈ Subgroup.normalizer (oTwoMod (cGrp H T) K : Set G) :=
        (Subgroup.normalizer _).inv_mem hxN
      refine ⟨T.inv_mem hxT, (Subgroup.normalizer _).inv_mem hxK, fun k hk => ?_⟩
      have h1 : (x * k * x⁻¹ * k⁻¹)⁻¹ ∈ oTwoMod (cGrp H T) K :=
        (oTwoMod (cGrp H T) K).inv_mem (hxC k hk)
      have heq : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ = x⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
      rw [heq]
      simpa using (Subgroup.mem_normalizer_iff.mp hxN' _).1 h1
  · rintro ⟨htT, htK, htC⟩
    exact Subgroup.subset_closure ⟨htT, htK, htC⟩

private theorem rGrp_le_T {H T K : Subgroup G} : rGrp H T K ≤ T :=
  fun _ ht => (mem_rGrp_iff.mp ht).1

private theorem rGrp_le_normalizer {H T K : Subgroup G} :
    rGrp H T K ≤ normalizer (K : Set G) :=
  fun _ ht => (mem_rGrp_iff.mp ht).2.1

private theorem Sit813.card_A {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    Nat.card A = 4 := by
  obtain ⟨-, g, hAg, -⟩ := h.mem
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hAab : IsElemAbelian 2 A := (isElemAbelian_conjSubgroup' hV g).mono hAg
  have hA2 : IsPGroup 2 ↥A := CFSG.Open.IsElemAbelian.isPGroup hAab
  rw [card_eq_two_pow_of_isPGroup hA2, h.concl812.2.2.1]
  norm_num

private theorem sit813_section_simple {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∃ (X : Type) (_ : Group X) (φ : ↥K →* X), Function.Surjective φ ∧
      (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoMod (cGrp H T) K) ∧
      IsSimpleGroup X ∧ Nat.card X = 60 ∧ ¬ IsMulCommutative X := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hX⟩ := h.concl813.c_shape
  letI : Group X := hXgrp
  have hX' : CFSG.Blueprint.LieModel X .PSL 2 2 2 := hX
  have hXs : IsSimpleGroup X :=
    CFSG.ComponentClassification.FooteLit.isSimpleGroup_of_lieModel_psl_two hX'
  have hXcard : Nat.card X = 60 := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hX',
      show CFSG.Open.ordA 1 (2 ^ 2) = 60 by decide]
  refine ⟨X, hXgrp, φ, hφ, hker, hXs, hXcard, ?_⟩
  intro hcomm
  haveI : IsMulCommutative X := hcomm
  have hp := (Group.is_simple_iff_prime_card (α := X)).mp hXs
  rw [hXcard] at hp
  norm_num at hp

private theorem sit813_KN1 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∀ B : Subgroup G, oTwoMod (cGrp H T) K ≤ B → B ≤ K →
      (B.subgroupOf K).Normal → B = oTwoMod (cGrp H T) K ∨ B = K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hXs, -, -⟩ := sit813_section_simple h
  letI : Group X := hXgrp
  intro B hNB hBK hBnorm
  haveI : ((B.subgroupOf K).map φ).Normal := hBnorm.map φ hφ
  rcases hXs.eq_bot_or_eq_top_of_normal ((B.subgroupOf K).map φ) with hbot | htop
  · left
    apply le_antisymm ?_ hNB
    intro b hb
    have hbK : b ∈ K := hBK hb
    have hbX : φ ⟨b, hbK⟩ ∈ (B.subgroupOf K).map φ :=
      Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, by simpa [Subgroup.mem_subgroupOf] using hb, rfl⟩
    have h1 : φ ⟨b, hbK⟩ = 1 := by
      rw [hbot] at hbX
      exact Subgroup.mem_bot.mp hbX
    exact (hker ⟨b, hbK⟩).mp h1
  · right
    apply le_antisymm hBK
    intro b hb
    have hbK : b ∈ K := hb
    have hbX : φ ⟨b, hbK⟩ ∈ (B.subgroupOf K).map φ := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hxB, hxeq⟩ := Subgroup.mem_map.mp hbX
    have hker' : φ (x⁻¹ * ⟨b, hbK⟩) = 1 := by
      rw [map_mul, map_inv, hxeq, inv_mul_cancel]
    have hmemN : (x : G)⁻¹ * b ∈ oTwoMod (cGrp H T) K := by
      have := (hker (x⁻¹ * ⟨b, hbK⟩)).mp hker'
      simpa using this
    have hmemB : (x : G)⁻¹ * b ∈ B := hNB hmemN
    have heq : b = (x : G) * ((x : G)⁻¹ * b) := by group
    rw [heq]
    exact B.mul_mem hxB hmemB

private theorem sit813_KN2 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∉ oTwoMod (cGrp H T) K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, -, -, hXnab⟩ := sit813_section_simple h
  letI : Group X := hXgrp
  by_contra hcon
  push Not at hcon
  apply hXnab
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨k₁, rfl⟩ := hφ x
  obtain ⟨k₂, rfl⟩ := hφ y
  have hc : φ (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) = 1 := (hker _).mpr (hcon k₁ k₁.2 k₂ k₂.2)
  have h2 : (φ k₁ * φ k₂) * (φ k₂ * φ k₁)⁻¹ = 1 := by
    simpa [mul_inv_rev, mul_assoc] using hc
  exact mul_inv_eq_one.mp h2

private theorem sit813_KN3 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    ∀ k ∈ K, (∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ oTwoMod (cGrp H T) K) →
      k ∈ oTwoMod (cGrp H T) K := by
  obtain ⟨X, hXgrp, φ, hφ, hker, hXs, -, hXnab⟩ := sit813_section_simple h
  letI : Group X := hXgrp
  intro k hkK hcomm
  have hcenter : Subgroup.center X = ⊥ := by
    rcases hXs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exact absurd ((Subgroup.center_eq_top_iff).mp h) hXnab
  have hz : φ ⟨k, hkK⟩ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    have hc : φ ⟨k, hkK⟩ * φ x * (φ ⟨k, hkK⟩)⁻¹ * (φ x)⁻¹ = 1 := by
      have := (hker (⟨k, hkK⟩ * x * ⟨k, hkK⟩⁻¹ * x⁻¹)).mpr (by
        simpa using hcomm (x : G) x.2)
      simpa using this
    have h2 : (φ ⟨k, hkK⟩ * φ x) * (φ x * φ ⟨k, hkK⟩)⁻¹ = 1 := by
      simpa [mul_inv_rev, mul_assoc] using hc
    exact (mul_inv_eq_one.mp h2).symm
  have h1 : φ ⟨k, hkK⟩ = 1 := by
    rw [hcenter] at hz
    exact Subgroup.mem_bot.mp hz
  exact (hker ⟨k, hkK⟩).mp h1

private theorem sit813_KN4 {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    (oTwoMod (cGrp H T) K).relIndex K = 60 := by
  obtain ⟨X, hXgrp, φ, hφ, hker, -, hXcard, -⟩ := sit813_section_simple h
  letI : Group X := hXgrp
  haveI : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal :=
    normal_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h)
  have hker_eq : φ.ker = (oTwoMod (cGrp H T) K).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  have e : (↥K ⧸ φ.ker) ≃* X := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hcard : Nat.card (↥K ⧸ φ.ker) = Nat.card X := Nat.card_congr e.toEquiv
  change ((oTwoMod (cGrp H T) K).subgroupOf K).index = 60
  rw [Subgroup.index_eq_card, ← hker_eq, hcard, hXcard]

private theorem relIndex_inf_eq_of_sup_eq {B R S : Subgroup G} (hBS : B ≤ S) (hRS : R ≤ S)
    (hsup : B ⊔ R = S) (hRn : (R.subgroupOf S).Normal) :
    (B ⊓ R).relIndex B = R.relIndex S := by
  haveI : (R.subgroupOf S).Normal := hRn
  have hsup' : (B.subgroupOf S) ⊔ (R.subgroupOf S) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBS hRS, hsup]
    exact Subgroup.subgroupOf_self S
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf S) (K := R.subgroupOf S)
  rw [hsup', Subgroup.relIndex_top_right] at h1
  have h2 : (R.subgroupOf S).relIndex (B.subgroupOf S) = R.relIndex B :=
    Subgroup.relIndex_subgroupOf hBS
  calc (B ⊓ R).relIndex B = R.relIndex B := Subgroup.inf_relIndex_left (H := B) (K := R)
    _ = (R.subgroupOf S).relIndex (B.subgroupOf S) := h2.symm
    _ = (R.subgroupOf S).index := h1.symm
    _ = R.relIndex S := rfl

private theorem inf_K_T_le_normalizer_rGrp {H T K : Subgroup G}
    (hNnormK : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal) :
    K ⊓ T ≤ normalizer (rGrp H T K : Set G) := by
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le).mp hNnormK
  intro k hk
  obtain ⟨hkK, hkT⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  obtain ⟨hrT, hrN, hrC⟩ := (mem_rGrp_iff.mp hr)
  refine mem_rGrp_iff.mpr ⟨T.mul_mem (T.mul_mem hkT hrT) (T.inv_mem hkT), ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : k⁻¹ * y * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hkK) hy) hkK
    have hr' : r * (k⁻¹ * y * k) * r⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hrN _).1 hy'
    have hfin := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hkK)
      (r * (k⁻¹ * y * k) * r⁻¹)).1 hr'
    have heq : k * r * k⁻¹ * y * (k * r * k⁻¹)⁻¹ =
        k * (r * (k⁻¹ * y * k) * r⁻¹) * k⁻¹ := by group
    rwa [heq]
  · intro x hx
    have hx' : k⁻¹ * x * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hkK) hx) hkK
    have hc : r * (k⁻¹ * x * k) * r⁻¹ * (k⁻¹ * x * k)⁻¹ ∈ oTwoMod (cGrp H T) K :=
      hrC _ hx'
    have hconj : k * (r * (k⁻¹ * x * k) * r⁻¹ * (k⁻¹ * x * k)⁻¹) * k⁻¹ ∈
        oTwoMod (cGrp H T) K := (Subgroup.mem_normalizer_iff.mp (hKN hkK) _).1 hc
    have heq : k * r * k⁻¹ * x * (k * r * k⁻¹)⁻¹ * x⁻¹ =
        k * (r * (k⁻¹ * x * k) * r⁻¹ * (k⁻¹ * x * k)⁻¹) * k⁻¹ := by group
    rwa [heq]

private theorem A_le_sup_inf_sGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ≤ (K ⊓ sGrp H T A K) ⊔ rGrp H T K := by
  have hc := h.concl813
  have hTH : T ≤ H := h.minCex.hyp.sylow.le.trans inf_le_left
  have hCHnorm : H ≤ normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hc.comp.2.1.trans hc.comp.2.2.1)).mp
      hc.comp.1
  intro a ha
  obtain ⟨k, hkK, t, ht, hcC⟩ := hc.a_le a ha
  set c : G := (k * t)⁻¹ * a with hcdef
  have ha_eq : a = k * t * c := by rw [hcdef]; group
  have htR : t ∈ rGrp H T K :=
    mem_rGrp_iff.mpr ⟨ht.1, cenTMod_mem_normalizer h ht, fun k' hk' =>
      le_oTwoMod hc.ge_C (cGrp_normal_subgroupOf_K h) (ht.2 k' (hc.sub_L hk'))⟩
  have htH : t ∈ H := hTH ht.1
  have hc' : t * c * t⁻¹ ∈ cGrp H T :=
    (Subgroup.mem_normalizer_iff.mp (hCHnorm htH) c).1 hcC
  have hk'K : k * (t * c * t⁻¹) ∈ K := K.mul_mem hkK (hc.ge_C hc')
  have hk'S : k * (t * c * t⁻¹) ∈ sGrp H T A K := by
    have heq : k * (t * c * t⁻¹) = a * t⁻¹ := by rw [ha_eq]; group
    rw [heq]
    exact (sGrp H T A K).mul_mem (Subgroup.mem_sup_right ha)
      ((sGrp H T A K).inv_mem (Subgroup.mem_sup_left htR))
  rw [show a = k * (t * c * t⁻¹) * t by rw [ha_eq]; group]
  exact Subgroup.mul_mem_sup ⟨hk'K, hk'S⟩ htR

private theorem A_le_normalizer_rGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ≤ normalizer (rGrp H T K : Set G) := by
  have hNnormK : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal :=
    normal_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h)
  have hKTR : K ⊓ T ≤ normalizer (rGrp H T K : Set G) :=
    inf_K_T_le_normalizer_rGrp hNnormK
  have hSleT : sGrp H T A K ≤ T := sup_le rGrp_le_T h.mem.1
  refine (A_le_sup_inf_sGrp h).trans (sup_le ?_ Subgroup.le_normalizer)
  exact (le_inf inf_le_left (le_trans inf_le_right hSleT)).trans hKTR

theorem Sit813.cGrp_le_normalizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : cGrp H T ≤ normalizer (V : Set G) := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hH : IsCalH V H := h.calH0.1
  have hT := hyp.sylow
  have hVT : V ≤ T := le_of_isCalH hV hH hT
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hyp.hyp7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hTne : T ≠ ⊥ := fun hb => hVne (le_bot_iff.mp (hVT.trans (le_of_eq hb)))
  have hZne : omegaOneCenterOf T ≠ ⊥ := omegaOneCenterOf_ne_bot' hT.isPGroup hTne
  obtain ⟨z, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzZ : (z : G) ∈ omegaOneCenterOf T := z.2
  have hz1 : (z : G) ≠ 1 := fun hh => hz1' (Subtype.ext hh)
  have hzE : (z : G) ∈ eGrp H T := omegaOneCenterOf_le_eGrp H T hzZ
  refine (inf_le_inf_left H (Subgroup.centralizer_le
    (show ({(z : G)} : Set G) ⊆ (eGrp H T : Set G) from
      Set.singleton_subset_iff.mpr hzE))).trans ?_
  exact hyp.centr z (omegaOneCenterOf_le T hzZ)
    (fun t ht => (mem_centralizer_of_mem_omegaOneCenterOf hzZ ht).symm) hz1

theorem Sit813.not_le_centralizer_omegaOneCenter {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : ¬ K ≤ centralizer (omegaOneCenterOf T : Set G) := by
  intro hK
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hH : IsCalH V H := h.calH0.1
  have hVT : V ≤ T := le_of_isCalH hV hH hyp.sylow
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hyp.hyp7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hTne : T ≠ ⊥ := fun hb => hVne (le_bot_iff.mp (hVT.trans (le_of_eq hb)))
  have hZne : omegaOneCenterOf T ≠ ⊥ := omegaOneCenterOf_ne_bot' hyp.sylow.isPGroup hTne
  obtain ⟨z, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzZ : (z : G) ∈ omegaOneCenterOf T := z.2
  have hz1 : (z : G) ≠ 1 := fun hh => hz1' (Subtype.ext hh)
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  have hKM : K ≤ normalizer (V : Set G) :=
    (le_inf hKH (hK.trans (Subgroup.centralizer_le
      (show ({(z : G)} : Set G) ⊆ (omegaOneCenterOf T : Set G) from
        Set.singleton_subset_iff.mpr hzZ)))).trans
      (hyp.centr z (omegaOneCenterOf_le T hzZ)
        (fun t ht => (mem_centralizer_of_mem_omegaOneCenterOf hzZ ht).symm) hz1)
  have hone : (K ⊓ normalizer (V : Set G)).relIndex K = 1 :=
    Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hKM)
  rw [h.concl813.d_index] at hone
  norm_num at hone

theorem Sit813.a_le_normalizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ≤ normalizer (K : Set G) := by
  intro x hx
  obtain ⟨k, hkK, t, ht, hcC⟩ := h.concl813.a_le x hx
  have htN : t ∈ normalizer (K : Set G) := cenTMod_mem_normalizer h ht
  have hcK : (k * t)⁻¹ * x ∈ K := h.concl813.ge_C hcC
  have hmem : x = k * t * ((k * t)⁻¹ * x) := by group
  rw [hmem]
  exact (Subgroup.normalizer (K : Set G)).mul_mem
    ((Subgroup.normalizer (K : Set G)).mul_mem (Subgroup.le_normalizer hkK) htN)
    (Subgroup.le_normalizer hcK)

theorem Sit813.exists_mul_of_mem {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {a : G} (ha : a ∈ A) :
    ∃ k ∈ K ⊓ normalizer (V : Set G), ∃ t ∈ rGrp H T K, ∃ c ∈ cGrp H T, a = k * t * c := by
  obtain ⟨k, hkK, t, ht, hcC⟩ := h.concl813.a_le a ha
  have hTM : T ≤ normalizer (V : Set G) := h.minCex.hyp.sylow.le.trans inf_le_right
  have haT : a ∈ T := h.mem.1 ha
  have hcM : (k * t)⁻¹ * a ∈ normalizer (V : Set G) := h.cGrp_le_normalizer hcC
  have hkM : k ∈ normalizer (V : Set G) := by
    have heq : k = a * ((k * t)⁻¹ * a)⁻¹ * t⁻¹ := by group
    rw [heq]
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (hTM haT)
        ((Subgroup.normalizer (V : Set G)).inv_mem hcM))
      ((Subgroup.normalizer (V : Set G)).inv_mem (hTM ht.1))
  refine ⟨k, ⟨hkK, hkM⟩, t, ?_, (k * t)⁻¹ * a, hcC, by group⟩
  rw [mem_rGrp_iff]
  exact ⟨ht.1, cenTMod_mem_normalizer h ht, fun k' hk' =>
    le_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h) (ht.2 k' (h.concl813.sub_L hk'))⟩

theorem Sit813.oTwoMod_le_normalizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : oTwoMod (cGrp H T) K ≤ normalizer (V : Set G) := by
  have hc := h.concl813
  have hCnormK : ((cGrp H T).subgroupOf K).Normal := cGrp_normal_subgroupOf_K h
  set N : Subgroup G := oTwoMod (cGrp H T) K with hNdef
  set K1 : Subgroup G := K ⊓ normalizer (V : Set G) with hK1def
  set D : Subgroup G := K1 ⊔ N with hDdef
  have hNK : N ≤ K := oTwoMod_le
  have hK1K : K1 ≤ K := inf_le_left
  have hK1D : K1 ≤ D := le_sup_left
  have hND : N ≤ D := le_sup_right
  have hDK : D ≤ K := sup_le hK1K hNK
  have hNnormK : (N.subgroupOf K).Normal := normal_oTwoMod hc.ge_C hCnormK
  have hNnormD : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr
      (hDK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNnormK))
  haveI : (N.subgroupOf D).Normal := hNnormD
  have hDsup : (K1.subgroupOf D) ⊔ (N.subgroupOf D) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK1D hND]
    exact Subgroup.subgroupOf_self D
  have hNidx : (N.subgroupOf D).index = (N.subgroupOf D).relIndex (K1.subgroupOf D) := by
    rw [← Subgroup.relIndex_top_right (H := N.subgroupOf D), ← hDsup]
    exact Subgroup.relIndex_sup_right (H := K1.subgroupOf D) (K := N.subgroupOf D)
  have h1 : (K1.subgroupOf D ⊓ N.subgroupOf D).index =
      (K1.subgroupOf D).relIndex (N.subgroupOf D) * (N.subgroupOf D).index :=
    Subgroup.index_inf
  have h2 : (K1.subgroupOf D ⊓ N.subgroupOf D).index =
      (N.subgroupOf D).relIndex (K1.subgroupOf D) * (K1.subgroupOf D).index := by
    rw [inf_comm]
    exact Subgroup.index_inf
  have hNidx_ne : (N.subgroupOf D).index ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hcancel : (K1.subgroupOf D).relIndex (N.subgroupOf D) = (K1.subgroupOf D).index := by
    apply Nat.mul_right_cancel (show 0 < (N.subgroupOf D).index from Nat.pos_of_ne_zero hNidx_ne)
    rw [← h1, h2, hNidx, mul_comm]
  have hrel : (K1.subgroupOf D).relIndex (N.subgroupOf D) = K1.relIndex N :=
    Subgroup.relIndex_subgroupOf hND
  have hcancel' : K1.relIndex N = K1.relIndex D := by
    rw [← hrel]
    exact hcancel
  have hsec : K1.relIndex D = (N ⊓ K1).relIndex N := by
    rw [← hcancel', Subgroup.inf_relIndex_left (H := N) (K := K1)]
  have hdvd5 : K1.relIndex D ∣ 5 := by
    have h5 : K1.relIndex K = 5 := by rw [hK1def]; exact hc.d_index
    have hmul := Subgroup.relIndex_mul_relIndex (H := K1) (K := D) (L := K) hK1D hDK
    rw [h5] at hmul
    exact ⟨D.relIndex K, hmul.symm⟩
  have hCN : cGrp H T ≤ N := le_oTwoMod hc.ge_C hCnormK
  have hCK1 : cGrp H T ≤ K1 := by rw [hK1def]; exact le_inf hc.ge_C h.cGrp_le_normalizer
  have hCNK1 : cGrp H T ≤ N ⊓ K1 := le_inf hCN hCK1
  have hCNnorm : ((cGrp H T).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (hNK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hc.ge_C).mp hCnormK))
  obtain ⟨m, hm⟩ := relIndex_eq_pow_two_of_pow_mem hCN hCNnorm
    (fun x hx => exists_pow_mem_oTwoMod hCnormK hx)
  have hdvd2 : K1.relIndex D ∣ 2 ^ m := by
    rw [hsec]
    exact hm ▸ Subgroup.relIndex_dvd_of_le_left (H := cGrp H T) (K := N ⊓ K1) (L := N) hCNK1
  have hd1 : K1.relIndex D = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd5 with h | h
    · exact h
    · exfalso
      have h52 : (5 : ℕ) ∣ 2 ^ m := h ▸ hdvd2
      have h52' : (5 : ℕ) ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h52
      norm_num at h52'
  have hND_le : N ≤ K1 := hND.trans (Subgroup.relIndex_eq_one.mp hd1)
  exact hND_le.trans (by rw [hK1def]; exact inf_le_right)

theorem Sit813.inf_rGrp_eq {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    K ⊓ rGrp H T K = T ⊓ oTwoMod (cGrp H T) K := by
  have hc := h.concl813
  have hNnormK : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal :=
    normal_oTwoMod hc.ge_C (cGrp_normal_subgroupOf_K h)
  have hNleK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le
  have hKNnorm : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleK).mp hNnormK
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxK, hxR⟩
    have hxT : x ∈ T := (mem_rGrp_iff.mp hxR).1
    have hxcomm : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K :=
      (mem_rGrp_iff.mp hxR).2.2
    exact Subgroup.mem_inf.mpr ⟨hxT, sit813_KN3 h x hxK hxcomm⟩
  · rintro t ⟨htT, htN⟩
    have htK : t ∈ K := hNleK htN
    refine Subgroup.mem_inf.mpr ⟨htK, ?_⟩
    rw [mem_rGrp_iff]
    refine ⟨htT, ?_, fun k hk => ?_⟩
    · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have h1 : x * t * x⁻¹ ∈ oTwoMod (cGrp H T) K :=
        (Subgroup.mem_normalizer_iff.mp (hKNnorm hx) t).1 htN
      have h3 : t * x * t⁻¹ = (t * (x * t * x⁻¹)⁻¹) * (x : G) := by group
      rw [h3]
      exact K.mul_mem (hNleK ((oTwoMod (cGrp H T) K).mul_mem htN
        ((oTwoMod (cGrp H T) K).inv_mem h1))) hx
    · have h1 : k * t * k⁻¹ ∈ oTwoMod (cGrp H T) K :=
        (Subgroup.mem_normalizer_iff.mp (hKNnorm hk) t).1 htN
      have h3 : t * k * t⁻¹ * k⁻¹ = t * (k * t * k⁻¹)⁻¹ := by group
      rw [h3]
      exact (oTwoMod (cGrp H T) K).mul_mem htN ((oTwoMod (cGrp H T) K).inv_mem h1)

theorem Sit813.card_inf_sGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    Nat.card ↥(K ⊓ sGrp H T A K) =
      Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) * (Nat.card ↥A / Nat.card ↥(A ⊓ rGrp H T K)) := by
  have hRS : rGrp H T K ≤ sGrp H T A K := le_sup_left
  have hAS : A ≤ sGrp H T A K := le_sup_right
  have hRnormS : ((rGrp H T K).subgroupOf (sGrp H T A K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).mpr
      (sup_le Subgroup.le_normalizer (A_le_normalizer_rGrp h))
  have hsup2 : (K ⊓ sGrp H T A K) ⊔ rGrp H T K = sGrp H T A K := by
    apply le_antisymm
    · exact sup_le inf_le_right le_sup_left
    · exact sup_le le_sup_right (A_le_sup_inf_sGrp h)
  have hsupA : A ⊔ rGrp H T K = sGrp H T A K := by
    change A ⊔ rGrp H T K = rGrp H T K ⊔ A
    exact sup_comm (a := A) (b := rGrp H T K)
  have e1 : ((K ⊓ sGrp H T A K) ⊓ rGrp H T K).relIndex (K ⊓ sGrp H T A K) =
      (rGrp H T K).relIndex (sGrp H T A K) :=
    relIndex_inf_eq_of_sup_eq inf_le_right hRS hsup2 hRnormS
  have e2 : (A ⊓ rGrp H T K).relIndex A = (rGrp H T K).relIndex (sGrp H T A K) :=
    relIndex_inf_eq_of_sup_eq hAS hRS hsupA hRnormS
  have hinf : (K ⊓ sGrp H T A K) ⊓ rGrp H T K = K ⊓ rGrp H T K := by
    rw [inf_assoc, inf_of_le_right hRS]
  have e1' : (K ⊓ rGrp H T K).relIndex (K ⊓ sGrp H T A K) =
      (rGrp H T K).relIndex (sGrp H T A K) := by rw [← hinf]; exact e1
  have hcard : Nat.card ↥(K ⊓ sGrp H T A K) =
      Nat.card ↥((K ⊓ sGrp H T A K) ⊓ rGrp H T K) *
        ((K ⊓ sGrp H T A K) ⊓ rGrp H T K).relIndex (K ⊓ sGrp H T A K) := by
    have h := Subgroup.relIndex_mul_card
      (H := (K ⊓ sGrp H T A K) ⊓ rGrp H T K) (K := K ⊓ sGrp H T A K)
    rw [inf_of_le_left inf_le_left] at h
    rw [mul_comm]
    exact h.symm
  have hAcard : (A ⊓ rGrp H T K).relIndex A * Nat.card ↥(A ⊓ rGrp H T K) = Nat.card ↥A := by
    simpa [inf_of_le_left inf_le_right] using
      (Subgroup.relIndex_mul_card (H := A ⊓ rGrp H T K) (K := A))
  have hdiv : (A ⊓ rGrp H T K).relIndex A =
      Nat.card ↥A / Nat.card ↥(A ⊓ rGrp H T K) :=
    Nat.eq_div_of_mul_eq_left (Nat.card_pos.ne') hAcard
  calc Nat.card ↥(K ⊓ sGrp H T A K)
      = Nat.card ↥(K ⊓ rGrp H T K) * (rGrp H T K).relIndex (sGrp H T A K) := by
        rw [hcard, hinf, e1']
    _ = Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) *
          (rGrp H T K).relIndex (sGrp H T A K) := by rw [Sit813.inf_rGrp_eq h]
    _ = Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) * (A ⊓ rGrp H T K).relIndex A := by rw [e2]
    _ = Nat.card ↥(T ⊓ oTwoMod (cGrp H T) K) *
          (Nat.card ↥A / Nat.card ↥(A ⊓ rGrp H T K)) := by rw [hdiv]

private theorem isSylowIn_sup_iff_isSylowIn_inf_aux {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ normalizer (K : Set G)) :
    IsSylowIn 2 S (K ⊔ S) ↔ IsSylowIn 2 (K ⊓ S) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKD : K ≤ K ⊔ S := le_sup_left
  have hSD : S ≤ K ⊔ S := le_sup_right
  have hDn : (K.subgroupOf (K ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mpr (sup_le Subgroup.le_normalizer hSK)
  have e0 : (S ⊓ K).relIndex S = K.relIndex (K ⊔ S) :=
    relIndex_inf_eq_of_sup_eq hSD hKD (sup_comm S K) hDn
  have hcD : K.relIndex (K ⊔ S) * Nat.card ↥K = Nat.card ↥(K ⊔ S) := by
    have h1 := Subgroup.relIndex_mul_card K (K ⊔ S)
    rwa [inf_of_le_left hKD] at h1
  have hcS : K.relIndex (K ⊔ S) * Nat.card ↥(K ⊓ S) = Nat.card ↥S := by
    have h1 := Subgroup.relIndex_mul_card (S ⊓ K) S
    rw [inf_of_le_left (inf_le_left : S ⊓ K ≤ S), e0, inf_comm] at h1
    exact h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hdvd : K.relIndex (K ⊔ S) ∣ 2 ^ k := ⟨_, by rw [← hk, ← hcS]⟩
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hKpos : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card ↥(K ⊔ S)).factorization 2 = a + (Nat.card ↥K).factorization 2 := by
    rw [← hcD, ha, Nat.factorization_mul (by positivity) hKpos]
    simp [Nat.Prime.factorization_pow Nat.prime_two]
  rw [ha] at hcD hcS
  constructor
  · intro hSyl
    refine isSylowIn_of_card_eq inf_le_left ?_
    have hc := hSyl.card_eq
    rw [hv, pow_add, ← hcS] at hc
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hc
  · intro hKS
    refine isSylowIn_of_card_eq hSD ?_
    have hc := hKS.card_eq
    rw [hv, pow_add, ← hc, hcS]

theorem Sit813.isSylowIn_sup_iff {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    IsSylowIn 2 (sGrp H T A K) (K ⊔ sGrp H T A K) ↔
      A ⊓ rGrp H T K = ⊥ ∧
        IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.minCex.hyp.sylow.isPGroup
  have hSleT : sGrp H T A K ≤ T := sup_le rGrp_le_T h.mem.1
  have hS2 : IsPGroup 2 (sGrp H T A K) := hT2.to_le hSleT
  have hSK : sGrp H T A K ≤ normalizer (K : Set G) :=
    sup_le rGrp_le_normalizer (Sit813.a_le_normalizer h)
  rw [isSylowIn_sup_iff_isSylowIn_inf_aux hS2 hSK]
  set N : Subgroup G := oTwoMod (cGrp H T) K with hNdef
  have hNK : N ≤ K := oTwoMod_le
  have hK60 : Nat.card ↥K = 60 * Nat.card ↥N := by
    have h1 := Subgroup.relIndex_mul_card N K
    rw [inf_of_le_left hNK, sit813_KN4 h] at h1
    exact h1.symm
  have hNpos : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hv60 : (60 : ℕ).factorization 2 = 2 := by
    have h4 : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have h15 : (15 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [show (60 : ℕ) = 4 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [h4, h15]
  have hvK : (Nat.card ↥K).factorization 2 = 2 + (Nat.card ↥N).factorization 2 := by
    rw [hK60, Nat.factorization_mul (by norm_num) hNpos]
    simp [hv60]
  have hP2 : IsPGroup 2 ↥(T ⊓ N) := hT2.to_le inf_le_left
  obtain ⟨pe, hpe⟩ := (IsPGroup.iff_card).1 hP2
  have hPdvd : 2 ^ pe ∣ Nat.card ↥N := hpe ▸ Subgroup.card_dvd_of_le (inf_le_right : T ⊓ N ≤ N)
  have hpeN : pe ≤ (Nat.card ↥N).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hNpos).1 hPdvd
  have hAcard : Nat.card ↥A = 2 ^ 2 := by rw [Sit813.card_A h]; norm_num
  have hRdvd : Nat.card ↥(A ⊓ rGrp H T K) ∣ 2 ^ 2 :=
    hAcard ▸ Subgroup.card_dvd_of_le (inf_le_left : A ⊓ rGrp H T K ≤ A)
  obtain ⟨re, hre, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hRdvd
  have hcard := Sit813.card_inf_sGrp h
  rw [hpe, hAcard, hr, Nat.pow_div hre Nat.two_pos, ← pow_add] at hcard
  have hα : A ⊓ rGrp H T K = ⊥ ↔ re = 0 := by
    rw [← Subgroup.card_eq_one, hr]
    exact ⟨fun h1 => (Nat.pow_eq_one.1 h1).resolve_left (by norm_num), fun h0 => by simp [h0]⟩
  have hβ : IsSylowIn 2 (T ⊓ N) N ↔ pe = (Nat.card ↥N).factorization 2 := by
    constructor
    · intro hS
      have := hS.card_eq
      rw [hpe] at this
      exact Nat.pow_right_injective le_rfl this
    · intro hpeq
      exact isSylowIn_of_card_eq inf_le_right (by rw [hpe, hpeq])
  have hKS : IsSylowIn 2 (K ⊓ sGrp H T A K) K ↔
        pe + (2 - re) = 2 + (Nat.card ↥N).factorization 2 := by
    constructor
    · intro hS
      have := hS.card_eq
      rw [hcard, hvK] at this
      exact Nat.pow_right_injective le_rfl this
    · intro heq
      exact isSylowIn_of_card_eq inf_le_left (by rw [hcard, hvK, heq])
  rw [hKS, hα, hβ]
  omega

private theorem cenTMod_mem_rGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {t : G} (ht : t ∈ cenTMod (cGrp H T) L T) : t ∈ rGrp H T K :=
  mem_rGrp_iff.mpr ⟨ht.1, cenTMod_mem_normalizer h ht, fun k' hk' =>
    le_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h) (ht.2 k' (h.concl813.sub_L hk'))⟩

private theorem exists_decomp_not_mem_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∃ x₀ ∈ A, ∃ k₀ ∈ K, ∃ t ∈ cenTMod (cGrp H T) L T,
      (k₀ * t)⁻¹ * x₀ ∈ cGrp H T ∧ k₀ ∉ oTwoMod (cGrp H T) K := by
  have hb := h.concl813.b_not_le
  push Not at hb
  obtain ⟨x₀, hx₀, hx₀'⟩ := hb
  obtain ⟨k₀, hk₀, t, ht, hc⟩ := h.concl813.a_le x₀ hx₀
  exact ⟨x₀, hx₀, k₀, hk₀, t, ht, hc, fun hk₀N => hx₀' k₀ hk₀N t ht hc⟩

private theorem exists_conj_not_mem_normalizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {k₀ : G} (hk₀ : k₀ ∈ K)
    (hk₀N : k₀ ∉ oTwoMod (cGrp H T) K) :
    ∃ k ∈ K, k * k₀ * k⁻¹ ∉ normalizer (V : Set G) := by
  by_contra hcon
  push Not at hcon
  have hNK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le
  have hNnormK : ((oTwoMod (cGrp H T) K).subgroupOf K).Normal :=
    normal_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h)
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNnormK
  let B : Subgroup G :=
    { carrier := {y | y ∈ K ∧ ∀ k ∈ K, k * y * k⁻¹ ∈ normalizer (V : Set G)}
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, fun k hk => ?_⟩
        have heq : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        rw [heq]
        exact (normalizer (V : Set G)).mul_mem (ha k hk) (hb k hk)
      one_mem' := ⟨K.one_mem, fun k hk => by simpa using (normalizer (V : Set G)).one_mem⟩
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, fun k hk => ?_⟩
        have heq : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
        rw [heq]
        exact (normalizer (V : Set G)).inv_mem (ha k hk) }
  have hBK : B ≤ K := fun y hy => hy.1
  have hNB : oTwoMod (cGrp H T) K ≤ B := by
    intro n hn
    refine ⟨hNK hn, fun k hk => ?_⟩
    exact h.oTwoMod_le_normalizer ((Subgroup.mem_normalizer_iff.mp (hKN hk) n).1 hn)
  have hBnorm : (B.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBK]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyK, hy⟩
      refine ⟨K.mul_mem (K.mul_mem hg hyK) (K.inv_mem hg), fun k hk => ?_⟩
      have h1 := hy (k * g) (K.mul_mem hk hg)
      have heq : k * (g * y * g⁻¹) * k⁻¹ = k * g * y * (k * g)⁻¹ := by group
      rw [heq]
      exact h1
    · rintro ⟨hyK, hy⟩
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := K.mul_mem (K.mul_mem (K.inv_mem hg) hyK) hg
        have heq : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rw [heq] at h1
        exact h1
      · have h1 := hy (k * g⁻¹) (K.mul_mem hk (K.inv_mem hg))
        have heq : k * g⁻¹ * (g * y * g⁻¹) * (k * g⁻¹)⁻¹ = k * y * k⁻¹ := by group
        rw [heq] at h1
        exact h1
  rcases sit813_KN1 h B hNB hBK hBnorm with hBN | hBKeq
  · apply hk₀N
    rw [← hBN]
    exact ⟨hk₀, hcon⟩
  · have hKM : K ≤ normalizer (V : Set G) := by
      intro y hy
      have hyB : y ∈ B := hBKeq ▸ hy
      simpa using hyB.2 1 K.one_mem
    have hone : (K ⊓ normalizer (V : Set G)).relIndex K = 1 :=
      Subgroup.relIndex_eq_one.mpr (le_inf le_rfl hKM)
    rw [h.concl813.d_index] at hone
    norm_num at hone

theorem Sit813.inf_centralizer_uGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ⊓ centralizer (uGrp V K : Set G) = ⊥ := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hTI := hyp.hyp7.2.2
  have hc := h.concl813
  obtain ⟨-, g, hAg, -⟩ := h.mem
  have hTM : T ≤ normalizer (V : Set G) := hyp.sylow.le.trans inf_le_right
  have hKnormC : K ≤ normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.ge_C).mp (cGrp_normal_subgroupOf_K h)
  have step1 : ∃ x₀ ∈ A, ∃ k ∈ K, k * x₀ * k⁻¹ ∉ normalizer (V : Set G) := by
    obtain ⟨x₀, hx₀, k₀, hk₀, t, ht, hcC, hk₀N⟩ := exists_decomp_not_mem_oTwoMod h
    obtain ⟨k, hk, hkM⟩ := exists_conj_not_mem_normalizer h hk₀ hk₀N
    refine ⟨x₀, hx₀, k, hk, fun hmem => hkM ?_⟩
    set c : G := (k₀ * t)⁻¹ * x₀ with hcdef
    have hx₀eq : x₀ = k₀ * t * c := by rw [hcdef]; group
    have hc₁ : k * t * k⁻¹ * t⁻¹ ∈ cGrp H T := by
      have h1 := (cGrp H T).inv_mem (ht.2 k (hc.sub_L hk))
      have heq : (t * k * t⁻¹ * k⁻¹)⁻¹ = k * t * k⁻¹ * t⁻¹ := by group
      rwa [heq] at h1
    have hc₂ : k * c * k⁻¹ ∈ cGrp H T :=
      (Subgroup.mem_normalizer_iff.mp (hKnormC hk) c).1 hcC
    have hM : k * (t * c) * k⁻¹ ∈ normalizer (V : Set G) := by
      have heq : k * (t * c) * k⁻¹ = (k * t * k⁻¹ * t⁻¹) * t * (k * c * k⁻¹) := by group
      rw [heq]
      exact (normalizer (V : Set G)).mul_mem
        ((normalizer (V : Set G)).mul_mem (h.cGrp_le_normalizer hc₁) (hTM ht.1))
        (h.cGrp_le_normalizer hc₂)
    have heq : k * k₀ * k⁻¹ = (k * x₀ * k⁻¹) * (k * (t * c) * k⁻¹)⁻¹ := by
      rw [hx₀eq]; group
    rw [heq]
    exact (normalizer (V : Set G)).mul_mem hmem ((normalizer (V : Set G)).inv_mem hM)
  refine eq_bot_iff.mpr fun a ha => ?_
  obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  obtain ⟨x₀, hx₀, k, hk, hkx⟩ := step1
  apply hkx
  have hconj : ∀ y ∈ A, k * y * k⁻¹ ∈ conjSubgroup V (g * k⁻¹) := by
    intro y hy
    rw [mem_conjSubgroup_iff]
    have heq : g * k⁻¹ * (k * y * k⁻¹) * (g * k⁻¹)⁻¹ = g * y * g⁻¹ := by group
    rw [heq]
    exact mem_conjSubgroup_iff.mp (hAg hy)
  have hak1 : k * a * k⁻¹ ≠ 1 := by
    intro h1
    apply ha1
    have heq : a = k⁻¹ * (k * a * k⁻¹) * k := by group
    rw [heq, h1]
    group
  have hVC : V ≤ centralizer ({k * a * k⁻¹} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hvU : k⁻¹ * v * k ∈ uGrp V K := by
      have h1 := mem_conjClosure (Z := V) (H := K) (K.inv_mem hk) hv
      rw [inv_inv] at h1
      exact h1
    have hcomm := Subgroup.mem_centralizer_iff.mp haC (k⁻¹ * v * k) hvU
    calc (k * a * k⁻¹) * v = k * (a * (k⁻¹ * v * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * v * k) * a) * k⁻¹ := by rw [hcomm]
      _ = v * (k * a * k⁻¹) := by group
  have hVN : V ≤ normalizer (conjSubgroup V (g * k⁻¹) : Set G) :=
    hVC.trans (centralizer_le_normalizer_conj hTI (g * k⁻¹) (hconj a haA) hak1)
  have hle : conjSubgroup V (g * k⁻¹) ≤ normalizer (V : Set G) :=
    (le_normalizer_conj_iff hV hTI).mpr hVN
  exact hle (hconj x₀ hx₀)

private theorem le_normalizer_inf_centralizer {K X : Subgroup G}
    (hX : K ≤ normalizer (X : Set G)) :
    K ≤ normalizer ((K ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨hyK, hyC⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hg hyK) (K.inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : g⁻¹ * z * g ∈ X := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hX (K.inv_mem hg)) z).1 hz
    simpa using h1
  have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hz'
  calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * y * g⁻¹) * z := by group

theorem Sit813.inf_rGrp_eq_bot_of_module {V H T A L K W : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hWab : IsElemAbelian 2 W)
    (hWK : K ≤ normalizer (W : Set G)) (hWA : A ≤ normalizer (W : Set G))
    (hNW : W ≤ centralizer (oTwoMod (cGrp H T) K : Set G))
    (hKW : ¬ K ≤ centralizer (W : Set G))
    (hC : ∀ a ∈ A, a ≠ 1 → W ⊓ centralizer (A : Set G) = W ⊓ centralizer ({a} : Set G)) :
    A ⊓ rGrp H T K = ⊥ := by
  have hc := h.concl813
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  obtain ⟨-, g, hAg, -⟩ := h.mem
  have hAab : IsElemAbelian 2 A := (isElemAbelian_conjSubgroup' hV g).mono hAg
  have hNK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le
  have hNW' : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ w ∈ W, n * w = w * n := fun n hn w hw =>
    Subgroup.mem_centralizer_iff.mp (hNW hw) n hn
  have com : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u := fun u hu v hv =>
    E1.commute_of_isElemAbelian hWab hu hv
  have sq : ∀ u ∈ W, u * u = 1 := fun u hu => by
    have h1 := hWab.2 u hu
    rwa [pow_two] at h1
  rw [eq_bot_iff]
  intro x hxAR
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxA, hxR⟩ := Subgroup.mem_inf.mp hxAR
  have hxx : x * x = 1 := by
    have h1 := hAab.2 x hxA
    rwa [pow_two] at h1
  have hxxinv : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hxx, inv_one]
  have key_comm : ∀ r ∈ rGrp H T K, r ∈ normalizer (W : Set G) → ∀ k ∈ K, ∀ w ∈ W,
      r * (k * w * k⁻¹) * r⁻¹ = k * (r * w * r⁻¹) * k⁻¹ := by
    intro r hr hrW k hk w hw
    have hm : r * k * r⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K := (mem_rGrp_iff.mp hr).2.2 k hk
    have hw' : k * (r * w * r⁻¹) * k⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWK hk) _).1
        ((Subgroup.mem_normalizer_iff.mp hrW w).1 hw)
    have hcomm := hNW' _ hm _ hw'
    calc r * (k * w * k⁻¹) * r⁻¹
        = (r * k * r⁻¹ * k⁻¹) * (k * (r * w * r⁻¹) * k⁻¹) * (r * k * r⁻¹ * k⁻¹)⁻¹ := by group
      _ = k * (r * w * r⁻¹) * k⁻¹ := by rw [hcomm]; group
  have hxK_comm := key_comm x hxR (hWA hxA)
  have mem_W0 : ∀ {w : G}, w ∈ W ⊓ centralizer ({x} : Set G) ↔ w ∈ W ∧ x * w * x⁻¹ = w := by
    intro w
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hw, hcx⟩
      refine ⟨hw, ?_⟩
      have h1 := hcx x (Set.mem_singleton x)
      rw [h1]
      group
    · rintro ⟨hw, hxw⟩
      refine ⟨hw, fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc x * w = (x * w * x⁻¹) * x := by group
        _ = w * x := by rw [hxw]
  have hW0A : W ⊓ centralizer ({x} : Set G) ≤ centralizer (A : Set G) := by
    intro w hw
    have h1 : w ∈ W ⊓ centralizer (A : Set G) := by rw [hC x hxA hx1]; exact hw
    exact (Subgroup.mem_inf.mp h1).2
  have hKW0 : K ≤ normalizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨hwW, hxw⟩ := mem_W0.mp hw
    refine mem_W0.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hWK hk) w).1 hwW, ?_⟩
    rw [hxK_comm k hk w hwW, hxw]
  have hconjW0 : ∀ g ∈ K, ∀ w ∈ W ⊓ centralizer ({x} : Set G),
      g * w * g⁻¹ ∈ W ⊓ centralizer ({x} : Set G) := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hKW0 hg) w).1 hw
  obtain ⟨x₀, hx₀, k₀, hk₀, t, ht, hcC, hk₀N⟩ := exists_decomp_not_mem_oTwoMod h
  obtain ⟨c, hcdef⟩ : ∃ c, c = (k₀ * t)⁻¹ * x₀ := ⟨_, rfl⟩
  rw [← hcdef] at hcC
  have hx₀eq : x₀ = k₀ * t * c := by rw [hcdef]; group
  have hcN : c ∈ oTwoMod (cGrp H T) K := le_oTwoMod hc.ge_C (cGrp_normal_subgroupOf_K h) hcC
  have hcW : ∀ w ∈ W, c * w * c⁻¹ = w := fun w hw => by
    rw [hNW' c hcN w hw]
    group
  have hcnorm : c ∈ normalizer (W : Set G) :=
    Subgroup.mem_normalizer_fintype fun w hw => by rw [hcW w hw]; exact hw
  have htR : t ∈ rGrp H T K := cenTMod_mem_rGrp h ht
  have htW : t ∈ normalizer (W : Set G) := by
    have heq : t = k₀⁻¹ * x₀ * c⁻¹ := by rw [hcdef]; group
    rw [heq]
    exact (normalizer (W : Set G)).mul_mem
      ((normalizer (W : Set G)).mul_mem ((normalizer (W : Set G)).inv_mem (hWK hk₀)) (hWA hx₀))
      ((normalizer (W : Set G)).inv_mem hcnorm)
  have htK_comm := key_comm t htR htW
  have hF1 : ∀ w ∈ W ⊓ centralizer ({x} : Set G), k₀⁻¹ * w * k₀ = t * w * t⁻¹ := by
    intro w hw
    obtain ⟨hwW, -⟩ := mem_W0.mp hw
    have h1 : x₀ * w = w * x₀ := Subgroup.mem_centralizer_iff.mp (hW0A hw) x₀ hx₀
    have h2 : c * w * c⁻¹ = w := hcW w hwW
    have h3 : x₀ * w * x₀⁻¹ = w := by
      calc x₀ * w * x₀⁻¹ = (w * x₀) * x₀⁻¹ := by rw [h1]
        _ = w := by group
    calc k₀⁻¹ * w * k₀ = k₀⁻¹ * (x₀ * w * x₀⁻¹) * k₀ := by rw [h3]
      _ = t * (c * w * c⁻¹) * t⁻¹ := by rw [hx₀eq]; group
      _ = t * w * t⁻¹ := by rw [h2]
  have hP9 : ∀ k ∈ K, ∀ w ∈ W ⊓ centralizer ({x} : Set G),
      (k₀⁻¹ * k * k₀ * k⁻¹) * w * (k₀⁻¹ * k * k₀ * k⁻¹)⁻¹ = w := by
    intro k hk w hw
    obtain ⟨w₂, hw₂def⟩ : ∃ w₂, w₂ = k⁻¹ * w * k := ⟨_, rfl⟩
    obtain ⟨w₃, hw₃def⟩ : ∃ w₃, w₃ = k₀ * w₂ * k₀⁻¹ := ⟨_, rfl⟩
    obtain ⟨w₄, hw₄def⟩ : ∃ w₄, w₄ = k * w₃ * k⁻¹ := ⟨_, rfl⟩
    have hw₂ : w₂ ∈ W ⊓ centralizer ({x} : Set G) := by
      have h1 := hconjW0 k⁻¹ (K.inv_mem hk) w hw
      rw [hw₂def]
      simpa using h1
    have hw₃ : w₃ ∈ W ⊓ centralizer ({x} : Set G) := by
      rw [hw₃def]; exact hconjW0 k₀ hk₀ _ hw₂
    have hw₄ : w₄ ∈ W ⊓ centralizer ({x} : Set G) := by
      rw [hw₄def]; exact hconjW0 k hk _ hw₃
    have e1 : k₀⁻¹ * w₄ * k₀ = t * w₄ * t⁻¹ := hF1 w₄ hw₄
    have e2 : t * w₄ * t⁻¹ = k * (t * w₃ * t⁻¹) * k⁻¹ := by
      rw [hw₄def]; exact htK_comm k hk w₃ (mem_W0.mp hw₃).1
    have e3 : t * w₃ * t⁻¹ = k₀⁻¹ * w₃ * k₀ := (hF1 w₃ hw₃).symm
    have e4 : k₀⁻¹ * w₃ * k₀ = w₂ := by rw [hw₃def]; group
    have e5 : k * w₂ * k⁻¹ = w := by rw [hw₂def]; group
    calc (k₀⁻¹ * k * k₀ * k⁻¹) * w * (k₀⁻¹ * k * k₀ * k⁻¹)⁻¹ = k₀⁻¹ * w₄ * k₀ := by
          rw [hw₄def, hw₃def, hw₂def]; group
      _ = w := by rw [e1, e2, e3, e4, e5]
  have hK0 : ∀ k ∈ K, ∀ w ∈ W ⊓ centralizer ({x} : Set G), k * w * k⁻¹ = w := by
    have hBnorm : ((K ⊓ centralizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G)
        ).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (le_normalizer_inf_centralizer hKW0)
    have hNB : oTwoMod (cGrp H T) K ≤
        K ⊓ centralizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
      intro n hn
      refine Subgroup.mem_inf.mpr ⟨hNK hn, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hNW' n hn z (mem_W0.mp hz).1).symm
    rcases sit813_KN1 h _ hNB inf_le_left hBnorm with hBN | hBK
    · exfalso
      apply hk₀N
      have hk₀inv : k₀⁻¹ ∈ oTwoMod (cGrp H T) K := by
        refine sit813_KN3 h k₀⁻¹ (K.inv_mem hk₀) fun y hy => ?_
        have hmemB : k₀⁻¹ * y * k₀ * y⁻¹ ∈
            K ⊓ centralizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hk₀) hy) hk₀) (K.inv_mem hy)
          · rw [Subgroup.mem_centralizer_iff]
            intro z hz
            exact (mul_inv_eq_iff_eq_mul.mp (hP9 y hy z hz)).symm
        rw [hBN] at hmemB
        simpa using hmemB
      simpa using (oTwoMod (cGrp H T) K).inv_mem hk₀inv
    · intro k hk w hw
      have hkB : k ∈ K ⊓ centralizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
        rw [hBK]; exact hk
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkB).2 w hw
      rw [← h1]
      group
  have D1 : ∀ k ∈ K, ∀ u ∈ W, u * (k * u * k⁻¹) ∈ W ⊓ centralizer ({x} : Set G) := by
    intro k hk u hu
    have hku : k * u * k⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWK hk) u).1 hu
    have hu'W : x * u * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWA hxA) u).1 hu
    obtain ⟨u', hu'def⟩ : ∃ u', u' = x * u * x⁻¹ := ⟨_, rfl⟩
    rw [← hu'def] at hu'W
    obtain ⟨φ, hφdef⟩ : ∃ φ, φ = u * u' := ⟨_, rfl⟩
    have hφW : φ ∈ W := by rw [hφdef]; exact W.mul_mem hu hu'W
    have hxu' : x * u' * x⁻¹ = u := by
      rw [hu'def]
      calc x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x⁻¹ * x⁻¹) := by group
        _ = u := by rw [hxx, hxxinv]; group
    have hxφ : x * φ * x⁻¹ = φ := by
      rw [hφdef]
      calc x * (u * u') * x⁻¹ = (x * u * x⁻¹) * (x * u' * x⁻¹) := by group
        _ = u' * u := by rw [← hu'def, hxu']
        _ = u * u' := com u' hu'W u hu
    have hφ0 : φ ∈ W ⊓ centralizer ({x} : Set G) := mem_W0.mpr ⟨hφW, hxφ⟩
    have hKφ : k * φ * k⁻¹ = φ := hK0 k hk φ hφ0
    have hu'φ : u' = u * φ := by
      rw [hφdef]
      calc u' = (u * u) * u' := by rw [sq u hu, one_mul]
        _ = u * (u * u') := by group
    have hexp : k * (u * φ) * k⁻¹ = (k * u * k⁻¹) * φ := by
      calc k * (u * φ) * k⁻¹ = (k * u * k⁻¹) * (k * φ * k⁻¹) := by group
        _ = (k * u * k⁻¹) * φ := by rw [hKφ]
    have hcomm : φ * (k * u * k⁻¹) = (k * u * k⁻¹) * φ := com φ hφW _ hku
    have hφ2 : φ * φ = 1 := sq φ hφW
    refine mem_W0.mpr ⟨W.mul_mem hu hku, ?_⟩
    calc x * (u * (k * u * k⁻¹)) * x⁻¹ = (x * u * x⁻¹) * (x * (k * u * k⁻¹) * x⁻¹) := by group
      _ = u' * (k * u' * k⁻¹) := by rw [hxK_comm k hk u hu, ← hu'def]
      _ = (u * φ) * (k * (u * φ) * k⁻¹) := by rw [hu'φ]
      _ = (u * φ) * ((k * u * k⁻¹) * φ) := by rw [hexp]
      _ = u * (φ * (k * u * k⁻¹)) * φ := by group
      _ = u * ((k * u * k⁻¹) * φ) * φ := by rw [hcomm]
      _ = u * (k * u * k⁻¹) * (φ * φ) := by group
      _ = u * (k * u * k⁻¹) := by rw [hφ2]; group
  have hE : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ u ∈ W,
      k₁ * (k₂ * u * k₂⁻¹) * k₁⁻¹ = k₂ * (k₁ * u * k₁⁻¹) * k₂⁻¹ := by
    intro k₁ hk₁ k₂ hk₂ u hu
    have ha := D1 k₁ hk₁ u hu
    have hb := D1 k₂ hk₂ u hu
    have haK : k₂ * (u * (k₁ * u * k₁⁻¹)) * k₂⁻¹ = u * (k₁ * u * k₁⁻¹) := hK0 k₂ hk₂ _ ha
    have hbK : k₁ * (u * (k₂ * u * k₂⁻¹)) * k₁⁻¹ = u * (k₂ * u * k₂⁻¹) := hK0 k₁ hk₁ _ hb
    have hP : k₁ * u * k₁⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWK hk₁) u).1 hu
    have hQ : k₂ * u * k₂⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWK hk₂) u).1 hu
    have hux : ∀ X : G, u * (u * X) = X := fun X => by rw [← mul_assoc, sq u hu, one_mul]
    have e1 : k₁ * (k₂ * u * k₂⁻¹) * k₁⁻¹ = (k₁ * u * k₁⁻¹) * (u * (k₂ * u * k₂⁻¹)) := by
      calc k₁ * (k₂ * u * k₂⁻¹) * k₁⁻¹ = k₁ * (u * (u * (k₂ * u * k₂⁻¹))) * k₁⁻¹ := by
            rw [hux]
        _ = (k₁ * u * k₁⁻¹) * (k₁ * (u * (k₂ * u * k₂⁻¹)) * k₁⁻¹) := by group
        _ = (k₁ * u * k₁⁻¹) * (u * (k₂ * u * k₂⁻¹)) := by rw [hbK]
    have e2 : k₂ * (k₁ * u * k₁⁻¹) * k₂⁻¹ = (k₂ * u * k₂⁻¹) * (u * (k₁ * u * k₁⁻¹)) := by
      calc k₂ * (k₁ * u * k₁⁻¹) * k₂⁻¹ = k₂ * (u * (u * (k₁ * u * k₁⁻¹))) * k₂⁻¹ := by
            rw [hux]
        _ = (k₂ * u * k₂⁻¹) * (k₂ * (u * (k₁ * u * k₁⁻¹)) * k₂⁻¹) := by group
        _ = (k₂ * u * k₂⁻¹) * (u * (k₁ * u * k₁⁻¹)) := by rw [haK]
    rw [e1, e2]
    calc (k₁ * u * k₁⁻¹) * (u * (k₂ * u * k₂⁻¹))
        = ((k₁ * u * k₁⁻¹) * u) * (k₂ * u * k₂⁻¹) := by group
      _ = (u * (k₁ * u * k₁⁻¹)) * (k₂ * u * k₂⁻¹) := by rw [com _ hP u hu]
      _ = u * ((k₁ * u * k₁⁻¹) * (k₂ * u * k₂⁻¹)) := by group
      _ = u * ((k₂ * u * k₂⁻¹) * (k₁ * u * k₁⁻¹)) := by rw [com _ hP _ hQ]
      _ = (u * (k₂ * u * k₂⁻¹)) * (k₁ * u * k₁⁻¹) := by group
      _ = ((k₂ * u * k₂⁻¹) * u) * (k₁ * u * k₁⁻¹) := by rw [com u hu _ hQ]
      _ = (k₂ * u * k₂⁻¹) * (u * (k₁ * u * k₁⁻¹)) := by group
  have hD : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ K ⊓ centralizer (W : Set G) := by
    intro k₁ hk₁ k₂ hk₂
    refine Subgroup.mem_inf.mpr
      ⟨K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hu : (k₂ * k₁)⁻¹ * w * (k₂ * k₁) ∈ W := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hWK (K.inv_mem (K.mul_mem hk₂ hk₁))) w).1 hw
      simpa using h1
    have key := hE k₁ hk₁ k₂ hk₂ _ hu
    have e : k₁ * (k₂ * ((k₂ * k₁)⁻¹ * w * (k₂ * k₁)) * k₂⁻¹) * k₁⁻¹ =
        (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * w * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)⁻¹ := by group
    have e' : k₂ * (k₁ * ((k₂ * k₁)⁻¹ * w * (k₂ * k₁)) * k₁⁻¹) * k₂⁻¹ = w := by group
    rw [e, e'] at key
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  have hDnorm : ((K ⊓ centralizer (W : Set G)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf_centralizer hWK)
  have hND : oTwoMod (cGrp H T) K ≤ K ⊓ centralizer (W : Set G) := fun n hn =>
    Subgroup.mem_inf.mpr ⟨hNK hn, by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hNW' n hn w hw).symm⟩
  rcases sit813_KN1 h _ hND inf_le_left hDnorm with hDN | hDK
  · obtain ⟨k₁, hk₁, k₂, hk₂, hnot⟩ := sit813_KN2 h
    apply hnot
    rw [← hDN]
    exact hD k₁ hk₁ k₂ hk₂
  · apply hKW
    intro y hy
    have h1 : y ∈ K ⊓ centralizer (W : Set G) := by rw [hDK]; exact hy
    exact (Subgroup.mem_inf.mp h1).2

private theorem mem_normalizer_inf {X Y : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hY : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨hnX, hnY⟩ := Subgroup.mem_inf.mp hn
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hX n).1 hnX,
    (Subgroup.mem_normalizer_iff.mp hY n).1 hnY⟩

private theorem mem_normalizer_centralizer {N : Subgroup G} {g : G}
    (hg : g ∈ normalizer (N : Set G)) :
    g ∈ normalizer ((centralizer (N : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hg' : g⁻¹ ∈ normalizer (N : Set G) := (normalizer (N : Set G)).inv_mem hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hg' n).1 hn
    simpa using h1
  have hcomm := Subgroup.mem_centralizer_iff.mp hz _ hn'
  calc n * (g * z * g⁻¹) = g * ((g⁻¹ * n * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * z * g⁻¹) * n := by group

theorem Sit813.inf_rGrp_eq_bot_of_not_le_centralizer {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hK : ¬ K ≤ centralizer
      ((eGrp H T ⊓ centralizer (oTwoMod (cGrp H T) K : Set G) : Subgroup G) : Set G)) :
    A ⊓ rGrp H T K = ⊥ := by
  have hyp := h.minCex.hyp
  have hc := h.concl813
  obtain ⟨hEab, -, hHE⟩ := eGrp_facts hyp.hyp7 h.calH0 hyp.sylow
  have hKH : K ≤ H := hc.sub_L.trans hc.comp.2.2.1
  have hAH : A ≤ H := h.mem.1.trans (isSylowIn_of_isCalH h.calH0.1 hyp.sylow).le
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le).mp
      (normal_oTwoMod hc.ge_C (cGrp_normal_subgroupOf_K h))
  have hCH : H ≤ normalizer (cGrp H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hc.comp.2.1.trans hc.comp.2.2.1)).mp hc.comp.1
  have hAN : A ≤ normalizer (oTwoMod (cGrp H T) K : Set G) := fun a ha =>
    normalizer_oTwoMod (Subgroup.mem_inf.mpr ⟨hCH (hAH ha), Sit813.a_le_normalizer h ha⟩)
  refine Sit813.inf_rGrp_eq_bot_of_module h
    (W := eGrp H T ⊓ centralizer (oTwoMod (cGrp H T) K : Set G)) (hEab.mono inf_le_left)
    ?_ ?_ inf_le_right hK ?_
  · exact fun k hk => mem_normalizer_inf (hHE (hKH hk)) (mem_normalizer_centralizer (hKN hk))
  · exact fun a ha => mem_normalizer_inf (hHE (hAH ha)) (mem_normalizer_centralizer (hAN ha))
  · intro a ha ha1
    have h1 := (eight_thirteen_faithful hyp.hyp7 h.calH0 hyp.sylow h.mem h.notLe).2 a ha ha1
    rw [inf_right_comm, h1, inf_right_comm]

theorem Sit813.isSylowIn_inf_cGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : IsSylowIn 2 (T ⊓ cGrp H T) (cGrp H T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowIn_of_isCalH h.calH0.1 h.minCex.hyp.sylow).inf_normal
    (h.concl813.comp.2.1.trans h.concl813.comp.2.2.1) h.concl813.comp.1

theorem Sit813.isSylowIn_oTwoMod_of_isSylowIn_inf {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hT : IsSylowIn 2 (T ⊓ K) K) :
    IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hT.inf_normal oTwoMod_le
    (normal_oTwoMod h.concl813.ge_C (cGrp_normal_subgroupOf_K h))
  rw [inf_assoc, inf_of_le_right oTwoMod_le] at h1
  exact h1

theorem Sit813.oTwoMod_le_centralizer_omegaOneCenter {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hβ : IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K)) :
    oTwoMod (cGrp H T) K ≤ centralizer (omegaOneCenterOf T : Set G) := by
  intro n hn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCnormK : ((cGrp H T).subgroupOf K).Normal := cGrp_normal_subgroupOf_K h
  have hCD : cGrp H T ≤ oTwoMod (cGrp H T) K := le_oTwoMod h.concl813.ge_C hCnormK
  have hDK : oTwoMod (cGrp H T) K ≤ K := oTwoMod_le
  have hDnormC : ((cGrp H T).subgroupOf (oTwoMod (cGrp H T) K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCD).mpr
      (hDK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.concl813.ge_C).mp hCnormK))
  have hq : ∀ x ∈ oTwoMod (cGrp H T) K, ∃ k : ℕ, x ^ 2 ^ k ∈ cGrp H T :=
    fun x hx => exists_pow_mem_oTwoMod hCnormK hx
  obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_eq_of_pow_mem hDnormC hq hβ n hn
  obtain ⟨hsT, -⟩ := Subgroup.mem_inf.mp hs
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  have hsz : s * z = z * s := mem_centralizer_of_mem_omegaOneCenterOf hz hsT
  have hcE : c ∈ centralizer (eGrp H T : Set G) := (Subgroup.mem_inf.mp hc).2
  have hcz : z * c = c * z :=
    Subgroup.mem_centralizer_iff.mp hcE z (omegaOneCenterOf_le_eGrp H T hz)
  calc z * (s * c) = (z * s) * c := by group
    _ = (s * z) * c := by rw [← hsz]
    _ = s * (z * c) := by group
    _ = s * (c * z) := by rw [hcz]
    _ = (s * c) * z := by group

theorem Sit813.inf_rGrp_eq_bot_of_isSylowIn {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hβ : IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K)) :
    A ⊓ rGrp H T K = ⊥ := by
  refine Sit813.inf_rGrp_eq_bot_of_not_le_centralizer h fun hK => ?_
  refine h.not_le_centralizer_omegaOneCenter (hK.trans (Subgroup.centralizer_le ?_))
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨omegaOneCenterOf_le_eGrp H T hz, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  exact (Subgroup.mem_centralizer_iff.mp
    ((h.oTwoMod_le_centralizer_omegaOneCenter hβ) hn) z hz).symm

theorem Sit813.isSylowIn_sup_iff_isSylowIn {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    IsSylowIn 2 (sGrp H T A K) (K ⊔ sGrp H T A K) ↔
      IsSylowIn 2 (T ⊓ oTwoMod (cGrp H T) K) (oTwoMod (cGrp H T) K) :=
  ⟨fun hS => ((Sit813.isSylowIn_sup_iff h).mp hS).2,
    fun hβ => (Sit813.isSylowIn_sup_iff h).mpr ⟨h.inf_rGrp_eq_bot_of_isSylowIn hβ, hβ⟩⟩

theorem Sit813.isSylowIn_sup_of_isSylowIn_inf {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hT : IsSylowIn 2 (T ⊓ K) K) :
    IsSylowIn 2 (sGrp H T A K) (K ⊔ sGrp H T A K) :=
  (Sit813.isSylowIn_sup_iff_isSylowIn h).mpr (h.isSylowIn_oTwoMod_of_isSylowIn_inf hT)

theorem Sit813.isSylowIn_sup {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    IsSylowIn 2 (sGrp H T A K) (K ⊔ sGrp H T A K) :=
  h.isSylowIn_sup_of_isSylowIn_inf h.concl813.t_sylow

end CFSG.LocalAnalysis.WeakClosure81

end
