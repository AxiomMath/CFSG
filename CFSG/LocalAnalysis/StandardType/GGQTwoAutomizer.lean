module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PerfectSylowCommutator

public section

open scoped commutatorElement Pointwise

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2x_isPGroup {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) : IsPGroup p Bs := by
  intro x
  exact ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hBs.2 (x : G) x.2)⟩

private theorem ggQ2x_ne_bot_of_witness {G : Type} [Group G] {Bs J : Subgroup G} {n : G}
    (hnJ : n ∈ J) (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnC : n ∉ Subgroup.centralizer (Bs : Set G)) :
    ggAutomizer J Bs ≠ ⊥ := by
  let φ : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨n, hnN⟩
  have hφind : φ ∈ ggInduced J Bs :=
    ⟨n, hnJ, hnN,
      fun b => Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨n, hnN⟩ b⟩
  have hφne : φ ≠ 1 := by
    intro hφ
    apply hnC
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : φ ⟨b, hb⟩ = ⟨b, hb⟩ := by rw [hφ]; rfl
    have hcoe := congrArg Subtype.val hb'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hcoe
    calc b * n = (n * b * n⁻¹) * n := by rw [hcoe]
      _ = n * b := by group
  intro hbot
  have hmem : φ ∈ ggAutomizer J Bs := Subgroup.subset_closure hφind
  rw [hbot] at hmem
  rw [Subgroup.mem_bot] at hmem
  exact hφne hmem

private theorem ggQ2x_caseA {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J T : Subgroup G}
    (hBsP : IsPGroup p Bs) (hnorm : Bs ≤ Subgroup.normalizer (J : Set G))
    (h3 : ∀ j ∈ J, j ∈ Subgroup.centralizer (Bs : Set G) →
      IsPGroup p (Subgroup.zpowers j) → j ∈ Bs)
    (hTle : T ≤ J ⊔ Bs) (hBsT : Bs ≤ T) (hTp : IsPGroup p T) (hTne : T ≠ Bs)
    (hH : ∀ n ∈ J, n ∈ Subgroup.normalizer (Bs : Set G) →
      n ∈ Subgroup.centralizer (Bs : Set G)) : False := by
  classical
  let Ht : Subgroup ↥T := Bs.subgroupOf T
  haveI : Group.IsNilpotent ↥T := hTp.isNilpotent
  have hnc := normalizerCondition_of_isNilpotent (G := ↥T)
  have hHlt : Ht < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hTne (le_antisymm ((Subgroup.subgroupOf_eq_top).mp htop) hBsT)
  obtain ⟨s, hsN, hsNotH⟩ := Set.exists_of_ssubset
    (SetLike.coe_ssubset_coe.mpr (hnc Ht hHlt))
  have hsT : (s : G) ∈ T := s.2
  have hsNotBs : (s : G) ∉ Bs := by
    intro hb
    exact hsNotH (by change s ∈ Bs.subgroupOf T; rw [Subgroup.mem_subgroupOf]; exact hb)
  have hsNBs : (s : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h1 : s ∈ (Subgroup.normalizer (Bs : Set G)).subgroupOf T := by
      rw [Subgroup.subgroupOf_normalizer_eq hBsT]
      exact hsN
    exact Subgroup.mem_subgroupOf.mp h1
  have hsup : ((Bs ⊔ J : Subgroup G) : Set G) = (Bs : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Bs J hnorm
  have hsBJ : (s : G) ∈ Bs ⊔ J := by
    have h2 : (s : G) ∈ J ⊔ Bs := hTle hsT
    rwa [sup_comm] at h2
  have hs_mul : (s : G) ∈ (Bs : Set G) * (J : Set G) := by
    rw [← hsup]
    exact hsBJ
  obtain ⟨b, hbBs, j, hjJ, hbjs⟩ := Set.mem_mul.mp hs_mul
  have hj_eq : j = b⁻¹ * (s : G) := by rw [← hbjs]; group
  have hjN : j ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [hj_eq]
    exact mul_mem (Subgroup.le_normalizer (H := Bs) (inv_mem hbBs)) hsNBs
  have hjC : j ∈ Subgroup.centralizer (Bs : Set G) := hH j hjJ hjN
  have hjT : j ∈ T := by
    rw [hj_eq]
    exact mul_mem (hBsT (inv_mem hbBs)) hsT
  have hjP : IsPGroup p (Subgroup.zpowers j) :=
    hTp.to_le (Subgroup.zpowers_le.mpr hjT)
  have hjBs : j ∈ Bs := h3 j hjJ hjC hjP
  have hsBs : (s : G) ∈ Bs := by
    rw [← hbjs]
    exact mul_mem hbBs hjBs
  exact hsNotBs hsBs

private theorem ggQ2x_commutator_mem {G : Type} [Group G] {p : ℕ} {Bs J P : Subgroup G}
    (hnorm : Bs ≤ Subgroup.normalizer (J : Set G)) (hBs : IsElemAbelian p Bs)
    (hPleBs : P ≤ Bs) {k b : G} (hkJ : k ∈ J)
    (hkN : k ∈ Subgroup.normalizer (P : Set G)) (hbBs : b ∈ Bs) :
    ⁅k, b⁆ ∈ J ⊓ Subgroup.centralizer (P : Set G) := by
  have hJ : ⁅k, b⁆ ∈ J := by
    have hb : b * k⁻¹ * b⁻¹ ∈ J := by
      have hbN : b ∈ Subgroup.normalizer (J : Set G) := hnorm hbBs
      rw [Subgroup.mem_normalizer_iff] at hbN
      exact (hbN k⁻¹).mp (inv_mem hkJ)
    have hgoal : ⁅k, b⁆ = k * (b * k⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hgoal]
    exact mul_mem hkJ hb
  have hC : ⁅k, b⁆ ∈ Subgroup.centralizer (P : Set G) := by
    have hbC : b ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer Bs (h := hBs.1) hbBs) x (hPleBs hx)
    have hkbk : k * b * k⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : k⁻¹ * x * k ∈ P := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (inv_mem hkN) x).mp hx
      have hcomm : b * (k⁻¹ * x * k) = (k⁻¹ * x * k) * b :=
        (Subgroup.mem_centralizer_iff.mp hbC (k⁻¹ * x * k) hx').symm
      have hcalc : (k * b * k⁻¹) * x = x * (k * b * k⁻¹) := by
        calc (k * b * k⁻¹) * x = k * (b * (k⁻¹ * x * k)) * k⁻¹ := by group
          _ = k * ((k⁻¹ * x * k) * b) * k⁻¹ := by rw [hcomm]
          _ = x * (k * b * k⁻¹) := by group
      exact hcalc.symm
    have hgoal : ⁅k, b⁆ = (k * b * k⁻¹) * b⁻¹ := by
      rw [commutatorElement_def]
    rw [hgoal]
    exact mul_mem hkbk (inv_mem hbC)
  exact Subgroup.mem_inf.mpr ⟨hJ, hC⟩

private theorem ggQ2x_frattini {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M Bs H' : Subgroup G}
    (hBsH' : Bs ≤ H') (hMleH' : M ≤ H') (hBsM : Bs ≤ M)
    (hMnorm : H' ≤ Subgroup.normalizer (M : Set G))
    (hBsSyl : CFSG.ABGLocalTools.IsSylowOf p Bs H') :
    ∀ h ∈ H', ∃ c ∈ M, ∃ n ∈ H' ⊓ Subgroup.normalizer (Bs : Set G), c * n = h := by
  classical
  haveI hMh : (M.subgroupOf H').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleH').mpr hMnorm
  obtain ⟨Q, hQ⟩ := hBsSyl
  have hQle : (Q : Subgroup ↥H') ≤ M.subgroupOf H' := by
    change (Q : Subgroup ↥H') ≤ M.comap H'.subtype
    rw [← Subgroup.map_le_iff_le_comap, hQ]
    exact hBsM
  have hfr := Sylow.normalizer_sup_eq_top' (N := M.subgroupOf H') Q hQle
  intro h hh
  let x : ↥H' := ⟨h, hh⟩
  have hx : x ∈ M.subgroupOf H' ⊔ Subgroup.normalizer (Q : Set ↥H') := by
    rw [sup_comm, hfr]
    exact Subgroup.mem_top x
  obtain ⟨c, hc, n, hn, hcn⟩ := (Subgroup.mem_sup_of_normal_left).mp hx
  refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, (n : G), ⟨n.2, ?_⟩, ?_⟩
  · have h1 : (n : G) ∈ (Subgroup.normalizer (Q : Set ↥H')).map H'.subtype :=
      Subgroup.mem_map_of_mem H'.subtype hn
    have h2 := Subgroup.le_normalizer_map (f := H'.subtype) (H := (Q : Subgroup ↥H')) h1
    rwa [hQ] at h2
  · exact congrArg Subtype.val hcn

private theorem ggQ2x_caseB {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hnorm : Bs ≤ Subgroup.normalizer (J : Set G))
    (hperf : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J)
    (hBsSylH : CFSG.ABGLocalTools.IsSylowOf p Bs (J ⊔ Bs))
    (hH : ∀ n ∈ J, n ∈ Subgroup.normalizer (Bs : Set G) →
      n ∈ Subgroup.centralizer (Bs : Set G)) : False := by
  classical
  set P : Subgroup G := J ⊓ Bs with hPdef
  have hPleJ : P ≤ J := inf_le_left
  have hPleBs : P ≤ Bs := inf_le_right
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P J := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hBsSylH (N := J)
      (le_sup_left : J ≤ J ⊔ Bs) (sup_le (Subgroup.le_normalizer (H := J)) hnorm)
    simpa [P, inf_comm] using h
  have hpp : p.Prime := Fact.out
  have hkpos : 0 < (Nat.card J).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hpp (Nat.card_pos (α := ↥J)).ne' hpJ
  have hPne : P ≠ ⊥ := by
    intro hPb
    have hcard : Nat.card P = 1 := (Subgroup.eq_bot_iff_card P).mp hPb
    rw [hPsyl.card_eq] at hcard
    exact absurd hcard (ne_of_gt (Nat.one_lt_pow hkpos.ne' hpp.one_lt))
  set K : Subgroup G := J ⊓ Subgroup.normalizer (P : Set G) with hKdef
  set C : Subgroup G := J ⊓ Subgroup.centralizer (P : Set G) with hCdef
  have hKleJ : K ≤ J := by rw [hKdef]; exact inf_le_left
  have hCleJ : C ≤ J := by rw [hCdef]; exact inf_le_left
  have hCleCP : C ≤ Subgroup.centralizer (P : Set G) := by
    rw [hCdef]; exact inf_le_right
  have hNClt : ¬ K ≤ C := by
    intro hNC
    have hperf' : commutator ↥J = ⊤ := by
      apply (Subgroup.map_subtype_inj (H := J)).mp
      rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_subtype_commutator, hperf]
    obtain ⟨Q, hQ⟩ := hPsyl.exists_sylow_eq_subgroupOf
    have hNC' : Subgroup.normalizer (Q : Subgroup ↥J) ≤
        Subgroup.centralizer (Q : Set ↥J) := by
      have hQset : (Q : Set ↥J) = (P.subgroupOf J : Set ↥J) :=
        congrArg (fun H : Subgroup ↥J => (H : Set ↥J)) hQ
      rw [hQ, hQset, ← Subgroup.subgroupOf_normalizer_eq hPleJ]
      intro x hx
      have hxG : (x : G) ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.mem_subgroupOf.mp hx
      have hxJ : (x : G) ∈ J := x.2
      have hxK : (x : G) ∈ K := by rw [hKdef]; exact ⟨hxJ, hxG⟩
      have hxC : (x : G) ∈ Subgroup.centralizer (P : Set G) := by
        have h' := hNC hxK
        rw [hCdef] at h'
        exact h'.2
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro y hy
      apply Subtype.ext
      exact hxC (y : G) (Subgroup.mem_subgroupOf.mp hy)
    have hQbot : (Q : Subgroup ↥J) = ⊥ :=
      CFSG.GroupTheory.sylow_eq_bot_of_normalizer_le_centralizer_of_perfect hperf' Q hNC'
    have hsub : P.subgroupOf J = ⊥ := by rw [← hQ, hQbot]
    have hPbot : P = ⊥ := by
      have hmap := Subgroup.map_subgroupOf_eq_of_le hPleJ
      rw [hsub, Subgroup.map_bot] at hmap
      exact hmap.symm
    exact hPne hPbot
  obtain ⟨k, hkK, hkNotC⟩ :=
    Set.not_subset.mp (fun hsub => hNClt hsub)
  have hkK' : k ∈ J ⊓ Subgroup.normalizer (P : Set G) := by
    rw [hKdef] at hkK; exact hkK
  have hkJ : k ∈ J := hkK'.1
  have hkN : k ∈ Subgroup.normalizer (P : Set G) := hkK'.2
  have hkNotCenP : k ∉ Subgroup.centralizer (P : Set G) := by
    intro hc
    exact hkNotC (by rw [hCdef]; exact ⟨hkJ, hc⟩)
  have hBs_le_CP : Bs ≤ Subgroup.centralizer (P : Set G) :=
    le_trans (Subgroup.le_centralizer Bs (h := hBs.1))
      (Subgroup.centralizer_le hPleBs)
  have hBs_le_NP : Bs ≤ Subgroup.normalizer (P : Set G) :=
    le_trans hBs_le_CP (Subgroup.centralizer_le_normalizer (P : Set G))
  have hBsNNP : Bs ≤ Subgroup.normalizer
      (Subgroup.normalizer (P : Set G) : Set G) :=
    le_trans hBs_le_NP (Subgroup.le_normalizer (H := Subgroup.normalizer (P : Set G)))
  have hBsNK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    le_trans (le_inf hnorm hBsNNP) Subgroup.inf_normalizer_le_normalizer_inf
  have hBsNC_P : Bs ≤ Subgroup.normalizer
      (Subgroup.centralizer (P : Set G) : Set G) :=
    le_trans hBs_le_CP (Subgroup.le_normalizer (H := Subgroup.centralizer (P : Set G)))
  have hBs_le_NC : Bs ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCdef]
    exact le_trans (le_inf hnorm hBsNC_P) Subgroup.inf_normalizer_le_normalizer_inf
  set M : Subgroup G := C ⊔ Bs with hMdef
  have hBsM : Bs ≤ M := le_sup_right
  have hCM : C ≤ M := le_sup_left
  have hMleCP : M ≤ Subgroup.centralizer (P : Set G) := by
    rw [hMdef]
    exact sup_le hCleCP hBs_le_CP
  have hkNotM : k ∉ M := fun hm => hkNotCenP (hMleCP hm)
  set H' : Subgroup G := K ⊔ Bs with hH'def
  have hKleH' : K ≤ H' := le_sup_left
  have hBsH' : Bs ≤ H' := le_sup_right
  have hCleN : C ≤ Subgroup.normalizer (P : Set G) :=
    le_trans hCleCP (Subgroup.centralizer_le_normalizer (P : Set G))
  have hCleK : C ≤ K := by
    rw [hKdef]
    exact le_inf hCleJ hCleN
  have hMleH' : M ≤ H' := by
    rw [hMdef, hH'def]
    exact sup_le (le_trans hCleK le_sup_left) le_sup_right
  have hMset : ((M : Subgroup G) : Set G) = (Bs : Set G) * (C : Set G) := by
    rw [hMdef, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right Bs C hBs_le_NC
  have hconjK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M := by
    intro k hk m hm
    have hkJ' : k ∈ J := hKleJ hk
    have hkN' : k ∈ Subgroup.normalizer (P : Set G) := (hKdef ▸ hk).2
    have hm' : m ∈ (Bs : Set G) * (C : Set G) := by rw [← hMset]; exact hm
    obtain ⟨b, hbBs, c, hcC, hbc⟩ := Set.mem_mul.mp hm'
    have hcC' : c ∈ Subgroup.centralizer (P : Set G) := (hCdef ▸ hcC).2
    have hcJ : c ∈ J := (hCdef ▸ hcC).1
    have hkcJ : k * c * k⁻¹ ∈ J := mul_mem (mul_mem hkJ' hcJ) (inv_mem hkJ')
    have hkcCP : k * c * k⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : k⁻¹ * x * k ∈ P := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (inv_mem hkN') x).mp hx
      have hcomm : c * (k⁻¹ * x * k) = (k⁻¹ * x * k) * c :=
        (Subgroup.mem_centralizer_iff.mp hcC' _ hx').symm
      have hcalc : (k * c * k⁻¹) * x = x * (k * c * k⁻¹) := by
        calc (k * c * k⁻¹) * x = k * (c * (k⁻¹ * x * k)) * k⁻¹ := by group
          _ = k * ((k⁻¹ * x * k) * c) * k⁻¹ := by rw [hcomm]
          _ = x * (k * c * k⁻¹) := by group
      exact hcalc.symm
    have hkc : k * c * k⁻¹ ∈ C := by
      rw [hCdef]
      exact Subgroup.mem_inf.mpr ⟨hkcJ, hkcCP⟩
    have hkb : k * b * k⁻¹ ∈ M := by
      have hcomm_mem : ⁅k, b⁆ ∈ C :=
        hCdef.symm ▸ ggQ2x_commutator_mem hnorm hBs hPleBs hkJ' hkN' hbBs
      have heq : k * b * k⁻¹ = ⁅k, b⁆ * b := by rw [commutatorElement_def]; group
      rw [heq]
      exact mul_mem (hCM hcomm_mem) (hBsM hbBs)
    have hprod : k * m * k⁻¹ = (k * b * k⁻¹) * (k * c * k⁻¹) := by rw [← hbc]; group
    rw [hprod]
    exact mul_mem hkb (hCM hkc)
  have hKNM : K ≤ Subgroup.normalizer (M : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact hconjK k hk m
    · intro hm
      have hkinv : k⁻¹ ∈ K := inv_mem hk
      have hthis := hconjK k⁻¹ hkinv (k * m * k⁻¹) hm
      have heq : k⁻¹ * (k * m * k⁻¹) * (k⁻¹)⁻¹ = m := by group
      rwa [heq] at hthis
  have hBsNM : Bs ≤ Subgroup.normalizer (M : Set G) := by
    rw [hMdef]
    exact le_trans (le_inf hBs_le_NC (Subgroup.le_normalizer (H := Bs)))
      (Subgroup.inf_normalizer_le_normalizer_sup C Bs)
  have hMnorm : H' ≤ Subgroup.normalizer (M : Set G) := by
    rw [hH'def]
    exact sup_le hKNM hBsNM
  have hH'leH : H' ≤ J ⊔ Bs := by
    rw [hH'def]
    exact sup_le (le_trans hKleJ le_sup_left) le_sup_right
  have hBsSylH' : CFSG.ABGLocalTools.IsSylowOf p Bs H' :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hBsSylH hBsH' hH'leH
  have hfratt := ggQ2x_frattini hBsH' hMleH' hBsM hMnorm hBsSylH'
  have hkH' : k ∈ H' := hKleH' hkK
  obtain ⟨c, hcM, n, hnC, hcn⟩ := hfratt k hkH'
  have hnN : n ∈ Subgroup.normalizer (Bs : Set G) := hnC.2
  have hnNotM : n ∉ M := by
    intro hnM
    have : k ∈ M := by rw [← hcn]; exact mul_mem hcM hnM
    exact hkNotM this
  have hH'K : ((Bs ⊔ K : Subgroup G) : Set G) = (Bs : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Bs K hBsNK
  have hnH'K : n ∈ Bs ⊔ K := by
    have hnH' : n ∈ H' := hnC.1
    rw [hH'def] at hnH'
    rwa [sup_comm] at hnH'
  have hn_mul : n ∈ (Bs : Set G) * (K : Set G) := by
    rw [← hH'K]
    exact hnH'K
  obtain ⟨b, hbBs, k', hk'K, hkbn⟩ := Set.mem_mul.mp hn_mul
  have hk'J : k' ∈ J := hKleJ hk'K
  have hk'N : k' ∈ Subgroup.normalizer (Bs : Set G) := by
    have heq : k' = b⁻¹ * n := by rw [← hkbn]; group
    rw [heq]
    exact mul_mem (Subgroup.le_normalizer (H := Bs) (inv_mem hbBs)) hnN
  have hk'NotCP : k' ∉ Subgroup.centralizer (P : Set G) := by
    intro hk'C
    apply hnNotM
    have heq : n = b * k' := by rw [← hkbn]
    rw [heq]
    have hk'Csub : k' ∈ C := by
      rw [hCdef]
      exact Subgroup.mem_inf.mpr ⟨hk'J, hk'C⟩
    exact mul_mem (hBsM hbBs) (hCM hk'Csub)
  have hk'C_Bs : k' ∈ Subgroup.centralizer (Bs : Set G) := hH k' hk'J hk'N
  exact hk'NotCP (Subgroup.centralizer_le hPleBs hk'C_Bs)

theorem ggQ2_automizer_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hnorm : Bs ≤ Subgroup.normalizer (J : Set G))
    (hperf : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J)
    (h3 : ∀ j ∈ J, j ∈ Subgroup.centralizer (Bs : Set G) →
      IsPGroup p (Subgroup.zpowers j) → j ∈ Bs) :
    ggAutomizer J Bs ≠ ⊥ := by
  classical
  have hBsP : IsPGroup p Bs := ggQ2x_isPGroup hBs
  have hwit : ∃ n : G, n ∈ J ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧
      n ∉ Subgroup.centralizer (Bs : Set G) := by
    by_contra hno
    push Not at hno
    let H : Subgroup G := J ⊔ Bs
    have hBsH : Bs ≤ H := le_sup_right
    have hBsSubP : IsPGroup p (Bs.subgroupOf H) := hBsP.comap_subtype
    obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hBsSubP
    let T : Subgroup G := (Q : Subgroup ↥H).map H.subtype
    have hTle : T ≤ H := Subgroup.map_subtype_le _
    have hTp : IsPGroup p T := Q.isPGroup'.map H.subtype
    have hBsT : Bs ≤ T := by
      intro x hx
      exact ⟨⟨x, hBsH hx⟩, hQle (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
    have hTsyl : CFSG.ABGLocalTools.IsSylowOf p T H := ⟨Q, rfl⟩
    by_cases hTeq : T = Bs
    · have hBsSylH : CFSG.ABGLocalTools.IsSylowOf p Bs H := by
        rw [hTeq] at hTsyl
        exact hTsyl
      exact ggQ2x_caseB hBs hnorm hperf hpJ hBsSylH hno
    · exact ggQ2x_caseA hBsP hnorm h3 hTle hBsT hTp hTeq hno
  obtain ⟨n, hnJ, hnN, hnC⟩ := hwit
  exact ggQ2x_ne_bot_of_witness hnJ hnN hnC

end CFSG.StandardType

end
