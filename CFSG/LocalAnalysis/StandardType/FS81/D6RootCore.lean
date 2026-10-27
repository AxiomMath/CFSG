module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Cent
public import CFSG.LocalAnalysis.StandardType.FS81.OrthRowCanon

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Pointwise commutatorElement

theorem d6RootCoreAt_holds : D6RootCoreAt := by
  intro G _ _ b₀ K E hstd B hB hrec g hx _hx' R hRC hRn h3R
  classical
  have hHyp : HypSetup b₀ K E Row.D6.m := hstd.2.1
  have hCanon : CanonPosition b₀ K E Row.D6 := hstd.2.2
  obtain ⟨hA81, hEmaxC, _hb₀E, hEcard, _hm, _haut⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, hZ, _hLarge, _hA2, _hA3, _hA4⟩ := hA81
  obtain ⟨hrow, _hdisj, hEsup, hAmaxK, hAcard, _hAcent⟩ := hCanon
  let C : Subgroup G := Subgroup.centralizer ({b₀} : Set G)
  have hRC' : R ≤ C := hRC
  have hRn' : (R.subgroupOf C).Normal := hRn
  have hKC' : K ≤ C := hKC
  have hAcard6 : Nat.card ↥(E ⊓ K) = 3 ^ 6 := by simpa [Row.n] using hAcard
  have hEcard7 : Nat.card E = 3 ^ 7 := by simpa [Row.m, Row.n] using hEcard
  obtain ⟨hKsimple, ⟨eD6⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_D6 hrow hZ
  have hRKnormal : ((R ⊓ K).subgroupOf K).Normal := by
    haveI : (R.subgroupOf C).Normal := hRn'
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A := C) (A' := R) K
    rwa [inf_eq_right.mpr hKC'] at h
  have hRKbot : R ⊓ K = ⊥ := by
    haveI : ((R ⊓ K).subgroupOf K).Normal := hRKnormal
    rcases hKsimple.eq_bot_or_eq_top_of_normal ((R ⊓ K).subgroupOf K) with hbot | htop
    · have hd : Disjoint (R ⊓ K) K := Subgroup.subgroupOf_eq_bot.mp hbot
      have h : (R ⊓ K) ⊓ K = ⊥ := disjoint_iff.mp hd
      rwa [inf_assoc, inf_idem] at h
    · exfalso
      have hle : K ≤ R := by
        intro x hxK
        have hmem : (⟨x, hxK⟩ : ↥K) ∈ (R ⊓ K).subgroupOf K := by
          rw [htop]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at hmem
        exact hmem.1
      have hAR : E ⊓ K ≤ R := hAmaxK.1.trans hle
      have hdvd : Nat.card ↥(E ⊓ K) ∣ Nat.card R := Subgroup.card_dvd_of_le hAR
      rw [hAcard6] at hdvd
      exact h3R ((show 3 ∣ 3 ^ 6 from by norm_num).trans hdvd)
  have hRcentK : R ≤ Subgroup.centralizer (K : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [eq_bot_iff, ← hRKbot]
    refine Subgroup.commutator_le.mpr ?_
    intro r hr k hk
    constructor
    · have hconj : k * r⁻¹ * k⁻¹ ∈ R :=
        (Subgroup.normal_subgroupOf_iff hRC').mp hRn' r⁻¹ k
          (Subgroup.inv_mem R hr) (hKC' hk)
      have hmem := Subgroup.mul_mem R hr hconj
      simpa [commutatorElement_def, mul_assoc] using hmem
    · have hconj : r * k * r⁻¹ ∈ K :=
        (Subgroup.normal_subgroupOf_iff hKC').mp hKn k r hk (hRC' hr)
      have hmem := Subgroup.mul_mem K hconj (Subgroup.inv_mem K hk)
      simpa [commutatorElement_def, mul_assoc] using hmem
  have hER : E ≤ Subgroup.centralizer (R : Set G) := by
    rw [← hEsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hRC' hy) b₀ (Set.mem_singleton b₀)).symm
    · exact hAmaxK.1.trans (Subgroup.le_centralizer_iff.mp hRcentK)
  have hRE : R ≤ Subgroup.centralizer (E : Set G) := Subgroup.le_centralizer_iff.mpr hER
  obtain ⟨R₀, _hR₀C, _hR₀n, _hR₀3, _hR₀sup, hR₀K, h3elt, h3'elt⟩ :=
    exists_cent_D6 hstd.toLoc hB hrec
  let x : G := g * b₀ * g⁻¹
  have hxK : x ∈ K := hx
  have hxord : orderOf x = 3 := by
    have h : orderOf ((MulAut.conj g) b₀) = orderOf b₀ := (MulAut.conj g).orderOf_eq b₀
    rw [MulAut.conj_apply, hb₀ord] at h
    simpa [x] using h
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  haveI : Finite (Subgroup G) := by
    have h : Fintype G := Fintype.ofFinite G
    let : Fintype G := h
    refine Finite.of_injective (fun S : Subgroup G => (S : Set G).toFinset) ?_
    intro S T hst
    ext y
    have hh : y ∈ (S : Set G).toFinset ↔ y ∈ (T : Set G).toFinset := by
      rw [← Finset.ext_iff.mp hst y]
    simpa using hh
  letI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  let T : Finset (Subgroup G) :=
    Finset.univ.filter (fun M => M ≤ K ∧ IsElemAbelian 3 M ∧ x ∈ M)
  have hTne : T.Nonempty := by
    refine ⟨Subgroup.zpowers x, ?_⟩
    change Subgroup.zpowers x ∈
      Finset.univ.filter (fun M => M ≤ K ∧ IsElemAbelian 3 M ∧ x ∈ M)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Subgroup.zpowers_le.mpr hxK,
      isElemAbelian_zpowers (p := 3) hx3, Subgroup.mem_zpowers x⟩
  obtain ⟨M, hMT, hmax⟩ := Finset.exists_max_image T (fun M => Nat.card M) hTne
  have hMT' : M ∈ Finset.univ.filter (fun M => M ≤ K ∧ IsElemAbelian 3 M ∧ x ∈ M) := hMT
  rw [Finset.mem_filter] at hMT'
  obtain ⟨-, hMK, hMelem, hxM⟩ := hMT'
  have hMmaxK : IsMaxElemAb3 K M := by
    refine ⟨hMK, hMelem, ?_⟩
    intro M' hM'K hM'elem hMM'
    have hM'T : M' ∈ T := by
      change M' ∈ Finset.univ.filter (fun M => M ≤ K ∧ IsElemAbelian 3 M ∧ x ∈ M)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hM'K, hM'elem, hMM' hxM⟩
    exact (Subgroup.eq_of_le_of_card_ge hMM' (hmax M' hM'T)).symm
  have hMcard : Nat.card M = 3 ^ 6 := by
    have hQ : (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
    have hdim : Module.finrank (ZMod 2) (Fin 6 ⊕ Fin 6 → ZMod 2) = 2 * 6 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
    have htype : CFSG.GroupTheory.WeirSylow.IsPlusType
        (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2)) ↔ Even 6 :=
      ⟨fun _ => ⟨3, rfl⟩, fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (ZMod 2) 6⟩
    exact (fs81_canon_of_orthEquiv (V := Fin 6 ⊕ Fin 6 → ZMod 2)
      (Q := CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2)) (n := 6)
      hQ hdim htype eD6 hMmaxK).1
  have hrowfacts := rowElemAb3_D6 hrow hZ hAmaxK.1 hAmaxK.2.1 hAcard6
  obtain ⟨k₁, hk₁K, hk₁M⟩ := hrowfacts.2 M hMK hMelem hMcard
  have hx₁A : k₁ * x * k₁⁻¹ ∈ E ⊓ K := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj k₁).toMonoidHom hxM
    rw [hk₁M] at h
    simpa [MulAut.conj_apply] using h
  let g' : G := k₁ * g
  have hg'b₀ : g' * b₀ * g'⁻¹ ∈ E ⊓ K := by
    have hEq : g' * b₀ * g'⁻¹ = k₁ * x * k₁⁻¹ := by
      simp only [g', x]
      group
    rw [hEq]
    exact hx₁A
  let F : Subgroup G := E.map (MulAut.conj g'⁻¹).toMonoidHom
  have hFelem : IsElemAbelian 3 F := hEmaxC.2.1.map _
  have hFcard7 : Nat.card F = 3 ^ 7 := by
    rw [show F = E.map (MulAut.conj g'⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective, hEcard7]
  have hb₀F : b₀ ∈ F := by
    have h1 : (MulAut.conj g'⁻¹) (g' * b₀ * g'⁻¹) ∈ F :=
      Subgroup.mem_map_of_mem _ ((inf_le_left : E ⊓ K ≤ E) hg'b₀)
    have h2 : (MulAut.conj g'⁻¹) (g' * b₀ * g'⁻¹) = b₀ := by
      rw [MulAut.conj_apply]
      group
    rwa [h2] at h1
  have hFC : F ≤ C := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    haveI : IsMulCommutative F := hFelem.1
    have hcomm := congrArg Subtype.val (mul_comm' (⟨f, hf⟩ : F) ⟨b₀, hb₀F⟩)
    exact hcomm.symm
  have hFle : F ≤ Subgroup.zpowers b₀ ⊔ K := by
    intro f hf
    exact h3elt f (hFC hf) (hFelem.2 f hf)
  have hzple : Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKC' hk) b₀ (Set.mem_singleton b₀)).symm
  have hLE : Subgroup.zpowers b₀ ≤ Subgroup.normalizer (K : Set G) :=
    hzple.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have hFprod : (↑(Subgroup.zpowers b₀ ⊔ K) : Set G) =
      (Subgroup.zpowers b₀ : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE
  have hFdecomp : ∀ f ∈ F, ∃ b ∈ Subgroup.zpowers b₀, ∃ k ∈ F ⊓ K, b * k = f := by
    intro f hf
    have hf' : f ∈ (↑(Subgroup.zpowers b₀ ⊔ K) : Set G) := hFle hf
    rw [hFprod] at hf'
    obtain ⟨b, hb, k, hk, hbk⟩ := Set.mem_mul.mp hf'
    have hkF : k ∈ F := by
      have hbF : b ∈ F := Subgroup.zpowers_le.mpr hb₀F hb
      have hk_eq : k = b⁻¹ * f := by rw [← hbk]; group
      rw [hk_eq]
      exact F.mul_mem (F.inv_mem hbF) hf
    exact ⟨b, hb, k, ⟨hkF, hk⟩, hbk⟩
  have hLE' : Subgroup.zpowers b₀ ≤ Subgroup.normalizer ((F ⊓ K : Subgroup G) : Set G) := by
    refine (le_inf ?_ hLE).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.zpowers_le.mpr hb₀F).trans Subgroup.le_normalizer
  have hFprod' : (↑(Subgroup.zpowers b₀ ⊔ (F ⊓ K)) : Set G) =
      (Subgroup.zpowers b₀ : Set G) * ((F ⊓ K : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE'
  have hFsup : F = Subgroup.zpowers b₀ ⊔ (F ⊓ K) := by
    refine le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr hb₀F) inf_le_left)
    intro f hf
    obtain ⟨b, hb, k, hk, hbk⟩ := hFdecomp f hf
    have hmem : f ∈ (Subgroup.zpowers b₀ : Set G) * ((F ⊓ K : Subgroup G) : Set G) := by
      rw [← hbk]
      exact Set.mul_mem_mul hb hk
    rwa [← hFprod'] at hmem
  have hcardle : Nat.card F ≤
      Nat.card ↥(Subgroup.zpowers b₀) * Nat.card ↥(F ⊓ K) := by
    let φ : ↥(Subgroup.zpowers b₀) × ↥(F ⊓ K) → F := fun p =>
      ⟨(p.1 : G) * (p.2 : G), F.mul_mem (Subgroup.zpowers_le.mpr hb₀F p.1.2) p.2.2.1⟩
    have hφ : Function.Surjective φ := by
      intro f
      obtain ⟨b, hb, k, hk, hbk⟩ := hFdecomp (f : G) f.2
      exact ⟨(⟨b, hb⟩, ⟨k, hk⟩), Subtype.ext hbk⟩
    have h := Nat.card_le_card_of_surjective φ hφ
    rwa [Nat.card_prod] at h
  have h3 : 3 ^ 7 ≤ 3 * Nat.card ↥(F ⊓ K) := by
    have h := hcardle
    rw [hFcard7, Nat.card_zpowers, hb₀ord] at h
    exact h
  have hFKle : Nat.card ↥(F ⊓ K) ≤ 3 ^ 6 :=
    hrowfacts.1 (F ⊓ K) inf_le_right (hFelem.mono inf_le_left)
  have hFKge : 3 ^ 6 ≤ Nat.card ↥(F ⊓ K) := by
    have h := h3
    norm_num at h ⊢
    omega
  have hFKcard : Nat.card ↥(F ⊓ K) = 3 ^ 6 := le_antisymm hFKle hFKge
  obtain ⟨k₂, hk₂K, hk₂FK⟩ :=
    hrowfacts.2 (F ⊓ K) inf_le_right (hFelem.mono inf_le_left) hFKcard
  have hk₂b₀ : (MulAut.conj k₂) b₀ = b₀ := by
    have h := Subgroup.mem_centralizer_iff.mp (hKC' hk₂K) b₀ (Set.mem_singleton b₀)
    rw [MulAut.conj_apply, ← h]
    group
  have hzp : (Subgroup.zpowers b₀).map (MulAut.conj k₂).toMonoidHom =
      Subgroup.zpowers b₀ := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hk₂b₀
  have hFmapE : F.map (MulAut.conj k₂).toMonoidHom = E := by
    rw [hFsup, Subgroup.map_sup, hzp, hk₂FK, hEsup]
  have hcomp : (MulAut.conj k₂).toMonoidHom.comp (MulAut.conj g'⁻¹).toMonoidHom =
      (MulAut.conj (k₂ * g'⁻¹)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hEa : E.map (MulAut.conj (k₂ * g'⁻¹)).toMonoidHom = E := by
    rw [← hcomp, ← Subgroup.map_map (K := E) (g := (MulAut.conj k₂).toMonoidHom)
      (f := (MulAut.conj g'⁻¹).toMonoidHom)]
    exact hFmapE
  have haN : k₂ * g'⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEa
  let n : G := g' * k₂⁻¹
  have hn_eq : n = (k₂ * g'⁻¹)⁻¹ := by
    simp only [n]
    group
  have hnN : n ∈ Subgroup.normalizer (E : Set G) := by
    rw [hn_eq]
    exact Subgroup.inv_mem _ haN
  have hinvN : n⁻¹ ∈ Subgroup.normalizer (E : Set G) := Subgroup.inv_mem _ hnN
  have himg : ⇑(MulAut.conj n⁻¹).toMonoidHom '' (E : Set G) = (E : Set G) := by
    simpa using (Subgroup.mem_normalizer_iff_conj_image_eq.mp hinvN)
  have hrorder : ∀ r ∈ R, ¬ 3 ∣ orderOf r := by
    intro r hr h3d
    exact h3R (h3d.trans (Subgroup.orderOf_dvd_natCard R hr))
  have hconjR : ∀ r ∈ R, (MulAut.conj n⁻¹) r ∈ Subgroup.centralizer (E : Set G) := by
    intro r hr
    have h1 : (MulAut.conj n⁻¹) r ∈
        (Subgroup.centralizer (E : Set G)).map (MulAut.conj n⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hRE hr)
    have h2 := Subgroup.map_centralizer_le_centralizer_image (E : Set G)
      (MulAut.conj n⁻¹).toMonoidHom h1
    rwa [himg] at h2
  have hconjR' : ∀ r ∈ R, (MulAut.conj n⁻¹) r ∈ R₀ := by
    intro r hr
    refine h3'elt _ (hconjR r hr) ?_
    rw [(MulAut.conj n⁻¹).orderOf_eq r]
    exact hrorder r hr
  have hRcentKg : R ≤ Subgroup.centralizer
      ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hsk : (MulAut.conj n⁻¹) r ∈ Subgroup.centralizer (K : Set G) := hR₀K (hconjR' r hr)
    rw [Subgroup.mem_centralizer_iff] at hsk
    have hk'K : k₂ * k * k₂⁻¹ ∈ K := K.mul_mem (K.mul_mem hk₂K hk) (K.inv_mem hk₂K)
    have hcomm := hsk (k₂ * k * k₂⁻¹) hk'K
    have hmain : (n * (k₂ * k * k₂⁻¹) * n⁻¹) * r =
        r * (n * (k₂ * k * k₂⁻¹) * n⁻¹) := by
      have h1 := congrArg (fun t => n * t * n⁻¹) hcomm
      have h2 : (MulAut.conj n⁻¹) r = n⁻¹ * r * n := by
        rw [MulAut.conj_apply, inv_inv]
      rw [h2] at h1
      have h3 : n * ((k₂ * k * k₂⁻¹) * (n⁻¹ * r * n)) * n⁻¹ =
          (n * (k₂ * k * k₂⁻¹) * n⁻¹) * r := by group
      have h4 : n * ((n⁻¹ * r * n) * (k₂ * k * k₂⁻¹)) * n⁻¹ =
          r * (n * (k₂ * k * k₂⁻¹) * n⁻¹) := by group
      rw [h3, h4] at h1
      exact h1
    have hident : n * (k₂ * k * k₂⁻¹) * n⁻¹ = k₁ * (g * k * g⁻¹) * k₁⁻¹ := by
      simp only [n, g']
      group
    have hmain' : (k₁ * (g * k * g⁻¹) * k₁⁻¹) * r =
        r * (k₁ * (g * k * g⁻¹) * k₁⁻¹) := by
      rwa [← hident]
    have hrk₁ : k₁ * r = r * k₁ :=
      (Subgroup.mem_centralizer_iff.mp (hRcentK hr)) k₁ hk₁K
    have hrk₁' : k₁⁻¹ * r = r * k₁⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (hRcentK hr)) k₁⁻¹ (Subgroup.inv_mem K hk₁K)
    have hyr : (g * k * g⁻¹) * r = r * (g * k * g⁻¹) := by
      have h1 : k₁ * ((g * k * g⁻¹) * r) * k₁⁻¹ =
          k₁ * (r * (g * k * g⁻¹)) * k₁⁻¹ := by
        calc k₁ * ((g * k * g⁻¹) * r) * k₁⁻¹
            = k₁ * (g * k * g⁻¹) * (r * k₁⁻¹) := by group
          _ = k₁ * (g * k * g⁻¹) * (k₁⁻¹ * r) := by rw [← hrk₁']
          _ = (k₁ * (g * k * g⁻¹) * k₁⁻¹) * r := by group
          _ = r * (k₁ * (g * k * g⁻¹) * k₁⁻¹) := hmain'
          _ = (r * k₁) * (g * k * g⁻¹) * k₁⁻¹ := by group
          _ = (k₁ * r) * (g * k * g⁻¹) * k₁⁻¹ := by rw [hrk₁]
          _ = k₁ * (r * (g * k * g⁻¹)) * k₁⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h1)
    simpa [MulAut.conj_apply] using hyr
  exact ⟨hRcentK, hRcentKg⟩

end CFSG.StandardType.FrameRoute.FS81
