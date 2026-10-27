module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Parab
import CFSG.RankThree.PartTwo.Sec18.Item185O23
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Image

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem o23_barAut_eq_conj {K : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (K : Set G)) (hkK : k ∈ K) :
    Sec3.Sims321.barAut K ⟨k, hk⟩ = MulAut.conj ((⟨k, hkK⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H l =>
    rw [Sec3.Sims321.barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    all_goals rfl

private theorem o23_mem_barActionImage {K S : Subgroup G} {x : MulAut (K ⧸ CFSG.pCore 2 K)} :
    x ∈ barActionImage K S ↔
      ∃ u : Subgroup.normalizer (K : Set G), (u : G) ∈ S ∧ Sec3.Sims321.barAut K u = x := by
  unfold barActionImage
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr hu, rfl⟩

private theorem o23_exists_barAut {K N : Subgroup G} {p : MulAut (K ⧸ CFSG.pCore 2 K)}
    (hp : p ∈ (starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →*
      MulAut (K ⧸ CFSG.pCore 2 K))) :
    ∃ (n : G) (hn : n ∈ Subgroup.normalizer (K : Set G)), n ∈ K ∧ n ∈ N ∧
      Sec3.Sims321.barAut K ⟨n, hn⟩ = p := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
  unfold starIm at hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨k, Subgroup.le_normalizer k.2, k.2, Subgroup.mem_subgroupOf.mp hk,
    o23_barAut_eq_conj _ k.2⟩

private theorem o23_comm_mem_inf {K L : Subgroup G} {n b : G}
    (hnL : n ∈ Subgroup.normalizer (L : Set G)) (hnK : n ∈ K) (hbL : b ∈ L)
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) : n * b * n⁻¹ * b⁻¹ ∈ K ⊓ L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : b * n⁻¹ * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbK n⁻¹).mp (K.inv_mem hnK)
    simpa only [mul_assoc] using K.mul_mem hnK h1
  · have h1 : n * b * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hnL b).mp hbL
    exact L.mul_mem h1 (L.inv_mem hbL)

private theorem o23_conj_mem_inf {K L : Subgroup G} {n k : G}
    (hnL : n ∈ Subgroup.normalizer (L : Set G)) (hnK : n ∈ K) (hk : k ∈ K ⊓ L) :
    n * k * n⁻¹ ∈ K ⊓ L := by
  obtain ⟨hkK, hkL⟩ := Subgroup.mem_inf.mp hk
  exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hnK hkK) (K.inv_mem hnK),
    (Subgroup.mem_normalizer_iff.mp hnL k).mp hkL⟩

private theorem o23_pCoreOf_conj_mem {L : Subgroup G} {k z : G} (hk : k ∈ L)
    (hz : z ∈ CFSG.Open.pCoreOf 2 L) : k * z * k⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  unfold CFSG.Open.pCoreOf at hz ⊢
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : ↥L) * z' * (⟨k, hk⟩ : ↥L)⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥L)).conj_mem z' hz' _
  · simp

private theorem o23_pCoreOf_pow {L : Subgroup G} {z : G}
    (hz : z ∈ CFSG.Open.pCoreOf 2 L) : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  unfold CFSG.Open.pCoreOf at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨z', hz'⟩
  refine ⟨k, ?_⟩
  have h1 : z' ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  simpa using h2

private theorem o23_cube_key {M : Type*} [Group M] (a : M) (h3 : a * a * a = 1) :
    (a⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * a⁻¹)⁻¹ = a := by
  have e : (a⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * a⁻¹)⁻¹ = (a * a) * (a * a) := by
    simp only [mul_inv_rev, inv_inv]
  rw [e]
  calc a * a * (a * a) = (a * a * a) * a := by simp only [mul_assoc]
    _ = a := by rw [h3, one_mul]

private theorem o23_exists_mul_pCoreOf {L M B : Subgroup G} {k b : G} (hBL : B ≤ L)
    (hNorm : ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hkLM : k ∈ L ⊓ M) (hb : b ∈ B) :
    ∃ x ∈ B, ∃ z ∈ CFSG.Open.pCoreOf 2 L, k * b * k⁻¹ = x * z := by
  unfold CFSG.Open.pCoreOf
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkLM).1
  have hbL : b ∈ L := hBL hb
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨k, hkL⟩ : ↥L) ∈
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [← hNorm]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hkLM)
  have hbB : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨b, hbL⟩ : ↥L) ∈
      ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have hconj : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨k, hkL⟩ : ↥L) *
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨b, hbL⟩ : ↥L) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨k, hkL⟩ : ↥L))⁻¹ ∈
      ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    (Subgroup.mem_normalizer_iff.mp hmem _).mp hbB
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hconj
  rw [← map_inv, ← map_mul, ← map_mul] at hxeq
  have hxeq' : (x : ↥L ⧸ CFSG.pCore 2 ↥L) =
      ((⟨k, hkL⟩ * ⟨b, hbL⟩ * (⟨k, hkL⟩ : ↥L)⁻¹ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) := hxeq
  have hz : x⁻¹ * (⟨k, hkL⟩ * ⟨b, hbL⟩ * (⟨k, hkL⟩ : ↥L)⁻¹) ∈ CFSG.pCore 2 ↥L :=
    QuotientGroup.eq.mp hxeq'
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx,
    ((x⁻¹ * (⟨k, hkL⟩ * ⟨b, hbL⟩ * (⟨k, hkL⟩ : ↥L)⁻¹) : ↥L) : G), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨_, hz, rfl⟩
  · simp [Subgroup.coe_mul, Subgroup.coe_inv]

theorem step1923_O23
    (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N)
    (hP : ParabolicShape (K ⧸ CFSG.pCore 2 K) (starIm K N))
    (hpar : barActionImage K (A ⊓ L) ≤
      (starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →* MulAut (K ⧸ CFSG.pCore 2 K)))
    (hw : ∃ (w : G) (hw : w ∈ Subgroup.normalizer (K : Set G)), w ∈ planeGroup A L c ∧
      (∀ b ∈ A ⊓ L, w * b * w⁻¹ = b⁻¹) ∧
      Sec3.Sims321.barAut K ⟨w, hw⟩ ∈ inner (K ⧸ CFSG.pCore 2 K)) :
    barActionImage K (A ⊓ L) ≤
      (Sec4.oTwoP 3 ↥((starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →*
          MulAut (K ⧸ CFSG.pCore 2 K)))).map
        ((starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →*
          MulAut (K ⧸ CFSG.pCore 2 K))).subtype := by
  clear hpar
  haveI : Finite (MulAut (K ⧸ CFSG.pCore 2 K)) :=
    Finite.of_injective
      (fun σ : MulAut (K ⧸ CFSG.pCore 2 K) => (σ : (K ⧸ CFSG.pCore 2 K) → (K ⧸ CFSG.pCore 2 K)))
      DFunLike.coe_injective
  obtain ⟨w, hwK, hwP, hwinv, hwi⟩ := hw
  have hKc : K ∈ oTwoComponentsIn M := step1923_mem_oTwoComponentsIn hK
  have hKM : K ≤ M := by
    obtain ⟨L', -, hL'⟩ := hKc
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hLN : L ≤ N := by
    intro l hl
    rw [← hF.normalizer_eq]
    exact Subgroup.le_normalizer hl
  have hNL : ∀ n ∈ N, n ∈ Subgroup.normalizer (L : Set G) := by
    intro n hn
    rw [hF.normalizer_eq]
    exact hn
  have hBN : ∀ b ∈ A ⊓ L, b ∈ Subgroup.normalizer (K : Set G) := fun b hb =>
    step1923_normalizer_A h hKc (Subgroup.mem_inf.mp hb).1
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hB3 : ∀ b ∈ A ⊓ L, b ^ 3 = 1 := fun b hb =>
    (Hyp1921.isE27 h).1.2 b (Subgroup.mem_inf.mp hb).1
  have hNorm := Hyp1921.map_inf_eq_normalizer_of (B := A ⊓ L) h hBL hF.card
    hF.normalizer_le_M hF.not_le_M hF.pCoreOf_le_M
  have hwL : w ∈ L := by
    rw [planeGroup, Subgroup.mem_inf, Subgroup.mem_inf] at hwP
    exact hwP.1.1
  have hwN : w ∈ N := hLN hwL
  have hwPar := step1923_inner_mem_parab h hP hwN hwK hwi
  set P := (starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →* MulAut (K ⧸ CFSG.pCore 2 K))
    with hPdef
  set Bh := barActionImage K (A ⊓ L) with hBh
  set X := barActionImage K (K ⊓ L) with hXdef
  set Zn : Subgroup G := CFSG.Open.pCoreOf 2 L ⊓ Subgroup.normalizer (K : Set G) with hZn
  set Yh := barActionImage K Zn with hYh
  set Y2 := X ⊓ Yh with hY2
  have hXP : X ≤ P := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := o23_mem_barActionImage.mp hx
    have huK : (u : G) ∈ K := (Subgroup.mem_inf.mp hu).1
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 K) ⟨(u : G), huK⟩, ?_, ?_⟩
    · unfold starIm
      exact Subgroup.mem_map.mpr ⟨⟨(u : G), huK⟩,
        Subgroup.mem_subgroupOf.mpr (hLN (Subgroup.mem_inf.mp hu).2), rfl⟩
    · exact (o23_barAut_eq_conj u.2 huK).symm
  have hXnorm : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X := by
    intro p hp x hx
    obtain ⟨n, hn, hnK, hnN, rfl⟩ := o23_exists_barAut (K := K) (N := N) hp
    obtain ⟨u, hu, rfl⟩ := o23_mem_barActionImage.mp hx
    refine o23_mem_barActionImage.mpr
      ⟨(⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) * u *
        (⟨n, hn⟩ : Subgroup.normalizer (K : Set G))⁻¹,
        o23_conj_mem_inf (hNL n hnN) hnK hu, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hBX : Bh ≤ X := by
    intro β hβ
    obtain ⟨v, hv, rfl⟩ := o23_mem_barActionImage.mp hβ
    obtain ⟨n, hn, hnK, hnN, hnw⟩ := o23_exists_barAut (K := K) (N := N) hwPar
    have hinv : Sec3.Sims321.barAut K ⟨w, hwK⟩ * Sec3.Sims321.barAut K v *
        (Sec3.Sims321.barAut K ⟨w, hwK⟩)⁻¹ = (Sec3.Sims321.barAut K v)⁻¹ := by
      calc Sec3.Sims321.barAut K ⟨w, hwK⟩ * Sec3.Sims321.barAut K v *
            (Sec3.Sims321.barAut K ⟨w, hwK⟩)⁻¹
          = Sec3.Sims321.barAut K
              ((⟨w, hwK⟩ : Subgroup.normalizer (K : Set G)) * v *
                (⟨w, hwK⟩ : Subgroup.normalizer (K : Set G))⁻¹) := by
            rw [map_mul, map_mul, map_inv]
        _ = Sec3.Sims321.barAut K v⁻¹ := by
            rw [show ((⟨w, hwK⟩ : Subgroup.normalizer (K : Set G)) * v *
                (⟨w, hwK⟩ : Subgroup.normalizer (K : Set G))⁻¹) = v⁻¹ from
              Subtype.ext (hwinv _ hv)]
        _ = (Sec3.Sims321.barAut K v)⁻¹ := map_inv _ _
    have hcomm : Sec3.Sims321.barAut K
        ((⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) * v *
          (⟨n, hn⟩ : Subgroup.normalizer (K : Set G))⁻¹ * v⁻¹) ∈ X :=
      o23_mem_barActionImage.mpr
        ⟨(⟨n, hn⟩ : Subgroup.normalizer (K : Set G)) * v *
          (⟨n, hn⟩ : Subgroup.normalizer (K : Set G))⁻¹ * v⁻¹,
          o23_comm_mem_inf (hNL n hnN) hnK (hBL hv) (hBN _ hv), rfl⟩
    have e1 : Sec3.Sims321.barAut K ⟨n, hn⟩ * Sec3.Sims321.barAut K v *
        (Sec3.Sims321.barAut K ⟨n, hn⟩)⁻¹ * (Sec3.Sims321.barAut K v)⁻¹ =
        (Sec3.Sims321.barAut K v)⁻¹ * (Sec3.Sims321.barAut K v)⁻¹ := by
      rw [hnw, hinv]
    have hsq : (Sec3.Sims321.barAut K v)⁻¹ * (Sec3.Sims321.barAut K v)⁻¹ ∈ X := by
      rw [← e1]
      simpa only [map_mul, map_inv] using hcomm
    have hv3 : v ^ 3 = 1 := Subtype.ext (hB3 _ hv)
    have hβ3 : Sec3.Sims321.barAut K v ^ 3 = 1 := by
      rw [← map_pow, hv3, map_one]
    have hcube : Sec3.Sims321.barAut K v * Sec3.Sims321.barAut K v *
        Sec3.Sims321.barAut K v = 1 := by
      rw [← pow_three']
      exact hβ3
    have key := o23_cube_key _ hcube
    have h2 := X.mul_mem (X.inv_mem hsq) (X.inv_mem hsq)
    rwa [key] at h2
  have hconjB : ∀ g ∈ X, ∀ s ∈ Bh, ∃ b' ∈ Bh, ∃ y' ∈ Y2, g * s * g⁻¹ = b' * y' := by
    intro g hg s hs
    obtain ⟨u, hu, rfl⟩ := o23_mem_barActionImage.mp hg
    obtain ⟨v, hv, rfl⟩ := o23_mem_barActionImage.mp hs
    have huK : (u : G) ∈ K := (Subgroup.mem_inf.mp hu).1
    obtain ⟨x, hx, z, hz, hkbk⟩ := o23_exists_mul_pCoreOf (M := M) hBL hNorm
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).2, hKM huK⟩) hv
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBN x hx
    have hzN : z ∈ Subgroup.normalizer (K : Set G) := by
      have hz_eq : z = x⁻¹ * ((u : G) * (v : G) * (u : G)⁻¹) := by
        rw [hkbk, inv_mul_cancel_left]
      rw [hz_eq]
      exact mul_mem (inv_mem hxN) (mul_mem (mul_mem u.2 (hBN _ hv)) (inv_mem u.2))
    have e2 : u * v * u⁻¹ = (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) * ⟨z, hzN⟩ :=
      Subtype.ext hkbk
    have e3 : Sec3.Sims321.barAut K u * Sec3.Sims321.barAut K v *
        (Sec3.Sims321.barAut K u)⁻¹ =
        Sec3.Sims321.barAut K ⟨x, hxN⟩ * Sec3.Sims321.barAut K ⟨z, hzN⟩ := by
      calc Sec3.Sims321.barAut K u * Sec3.Sims321.barAut K v * (Sec3.Sims321.barAut K u)⁻¹
          = Sec3.Sims321.barAut K (u * v * u⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = Sec3.Sims321.barAut K
              ((⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) * ⟨z, hzN⟩) := by rw [e2]
        _ = Sec3.Sims321.barAut K ⟨x, hxN⟩ * Sec3.Sims321.barAut K ⟨z, hzN⟩ := map_mul _ _ _
    have hxB : Sec3.Sims321.barAut K ⟨x, hxN⟩ ∈ Bh :=
      o23_mem_barActionImage.mpr ⟨⟨x, hxN⟩, hx, rfl⟩
    have hgsX : Sec3.Sims321.barAut K u * Sec3.Sims321.barAut K v *
        (Sec3.Sims321.barAut K u)⁻¹ ∈ X :=
      hXnorm _ (hXP hg) _ (hBX hs)
    have hzX : Sec3.Sims321.barAut K ⟨z, hzN⟩ ∈ X := by
      have h1 := X.mul_mem (X.inv_mem (hBX hxB)) hgsX
      rw [e3, inv_mul_cancel_left] at h1
      exact h1
    have hzYh : Sec3.Sims321.barAut K ⟨z, hzN⟩ ∈ Yh :=
      o23_mem_barActionImage.mpr ⟨⟨z, hzN⟩, Subgroup.mem_inf.mpr ⟨hz, hzN⟩, rfl⟩
    exact ⟨Sec3.Sims321.barAut K ⟨x, hxN⟩, hxB, Sec3.Sims321.barAut K ⟨z, hzN⟩,
      Subgroup.mem_inf.mpr ⟨hzX, hzYh⟩, e3⟩
  have hY2X : Y2 ≤ X := inf_le_left
  have hY2n : (Y2.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnX, hnYh⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨u, hu, hu'⟩ := o23_mem_barActionImage.mp g.2
    obtain ⟨z, hz, hz'⟩ := o23_mem_barActionImage.mp hnYh
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem g.2 hnX) (X.inv_mem g.2), ?_⟩
    refine o23_mem_barActionImage.mpr ⟨u * z * u⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨o23_pCoreOf_conj_mem (Subgroup.mem_inf.mp hu).2
        (Subgroup.mem_inf.mp hz).1, mul_mem (mul_mem u.2 z.2) (inv_mem u.2)⟩
    · show Sec3.Sims321.barAut K (u * z * u⁻¹) =
        (g : MulAut (K ⧸ CFSG.pCore 2 K)) * (n : MulAut (K ⧸ CFSG.pCore 2 K)) *
          (g : MulAut (K ⧸ CFSG.pCore 2 K))⁻¹
      rw [map_mul, map_mul, map_inv, hu', hz']
  have hY2_2 : IsPGroup 2 Y2 := by
    intro y
    obtain ⟨z, hz, hz'⟩ := o23_mem_barActionImage.mp (Subgroup.mem_inf.mp y.2).2
    obtain ⟨k, hk⟩ := o23_pCoreOf_pow (Subgroup.mem_inf.mp hz).1
    refine ⟨k, Subtype.ext ?_⟩
    have hzk : z ^ 2 ^ k = 1 := Subtype.ext hk
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hz', ← map_pow, hzk, map_one]
  have hBgrp : IsPGroup 3 Bh := by
    intro β
    obtain ⟨v, hv, hv'⟩ := o23_mem_barActionImage.mp β.2
    have hv3 : v ^ 3 = 1 := Subtype.ext (hB3 _ hv)
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hv', ← map_pow, hv3, map_one]
  have hBN2 : ((Bh ⊔ Y2).subgroupOf X).Normal := by
    rw [Subgroup.subgroupOf_sup hBX hY2X]
    haveI := hY2n
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    have hgs : g * s * g⁻¹ ∈ Bh.subgroupOf X ⊔ Y2.subgroupOf X := by
      obtain ⟨b', hb', y', hy', heq⟩ := hconjB (g : MulAut (K ⧸ CFSG.pCore 2 K)) g.2
        (s : MulAut (K ⧸ CFSG.pCore 2 K)) (Subgroup.mem_subgroupOf.mp hs)
      have e : g * s * g⁻¹ = (⟨b', hBX hb'⟩ : ↥X) * ⟨y', hY2X hy'⟩ := Subtype.ext heq
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hb')
        (Subgroup.mem_subgroupOf.mpr hy')
    have hgt : g * t * g⁻¹ ∈ Bh.subgroupOf X ⊔ Y2.subgroupOf X :=
      Subgroup.mem_sup_right (hY2n.conj_mem t ht g)
    rw [show g * (s * t) * g⁻¹ = (g * s * g⁻¹) * (g * t * g⁻¹) by group]
    exact mul_mem hgs hgt
  have hXnormal : (X.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hXnorm _ g.2 _ hn
  exact le_trans
    (CFSG.RankThree.PartTwo.Sec18.Item185Proof.le_oTwoP_of_normal_closure hBX hY2X hY2_2 hY2n
      hBgrp hBN2)
    (CFSG.RankThree.PartTwo.Sec18.Item185Proof.oTwoP_le_of_normal hXP hXnormal)

end CFSG.RankThree.PartTwo.Late
