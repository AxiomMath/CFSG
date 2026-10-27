module

public import CFSG.LocalAnalysis.StandardType.GGResIO2a
public import CFSG.LocalAnalysis.StandardType.GGResIO2bExcl
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggO2aσ {Λ : Type} {b : Λ} (j₀ j₁ : {i : Λ // i ≠ b}) : Fin 4 → Option Λ :=
  ![some j₀.1, some j₁.1, some b, none]

theorem ggO2aσ_injective {Λ : Type} {b : Λ} {j₀ j₁ : {i : Λ // i ≠ b}} (h01 : j₀ ≠ j₁) :
    Function.Injective (ggO2aσ j₀ j₁) := by
  have e01 : j₀.1 ≠ j₁.1 := fun he => h01 (Subtype.ext he)
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp [ggO2aσ] at hkl ⊢
  all_goals first
    | exact h01 hkl | exact h01 hkl.symm | exact e01 hkl | exact e01 hkl.symm
    | exact j₀.2 hkl | exact j₁.2 hkl | exact j₀.2 hkl.symm | exact j₁.2 hkl.symm

theorem ggO2aT_get (c ver : Bool) (k l : Fin 4) :
    (ggO2aT c ver k).get l.castSucc = (ggO2aInt c ver k l : ZMod 3) := by
  simp [ggO2aT]

theorem ggO2a_table {Λ : Type} {b : Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (c ver : Bool) {j₀ j₁ : {i : Λ // i ≠ b}}
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hKa : ∀ j : {i : Λ // i ≠ b}, α (some j.1) (h none) = (CK (some j) none : ZMod 3))
    (haK : ∀ j : {i : Λ // i ≠ b}, α none (h (some j.1)) = (CK none (some j) : ZMod 3))
    (haa : α none (h none) = 2) (hCLd : ∀ i, CL i i = 2)
    (c01 : CL j₀ j₁ = -1) (c10 : CL j₁ j₀ = -1) (c0b : CL j₀ b = -1) (cb0 : CL b j₀ = -1)
    (c1b : CL j₁ b = 0) (cb1 : CL b j₁ = 0)
    (k0a : CK (some j₀) none = if c then (if ver then -1 else -2) else 0)
    (ka0 : CK none (some j₀) = if c then (if ver then -2 else -1) else 0)
    (k1a : CK (some j₁) none = if c then 0 else (if ver then -1 else -2))
    (ka1 : CK none (some j₁) = if c then 0 else (if ver then -2 else -1))
    (hu : α none (h (some b)) = (if ver then 1 else 2))
    (hv : α (some b) (h none) = (if ver then 2 else 1)) :
    GGFTable (RingHom.id (ZMod 3)) (ggO2aT c ver) (h ∘ ggO2aσ j₀ j₁) 0 (α ∘ ggO2aσ j₀ j₁) := by
  refine ⟨fun k l => ?_, fun k => by simp [ggO2aT]⟩
  rw [ggO2aT_get, RingHom.id_apply, Function.comp_apply, Function.comp_apply]
  cases c <;> cases ver <;> fin_cases k <;> fin_cases l <;>
    simp [ggO2aσ, ggO2aInt, hL, hKa, haK, haa, hCLd, c01, c10, c0b, cb0, c1b, cb1, k0a, ka0, k1a,
      ka1, hu, hv]

theorem ggNbr_centralizer_le_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hcyc : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (K : Set G) → IsPGroup p P → IsCyclic P)
    {E : Subgroup G} (hEK : E ≤ K) (hE : IsElemAbelian p E) (hEc : p < Nat.card E) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hcompK : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hNbr)).1
  have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hCy : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) :=
    centralizer_map_conj_of_commute hgy
  have hcompK' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompK g
    rwa [hCy] at h1
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hcompK' hcompK with
    hEq | hComm
  · exact mem_normalizer_iff_map_conj.mpr hEq
  · exfalso
    have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    have hK'cent : K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm
    have hEp : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
    have hEgc : IsCyclic (E.map (MulAut.conj g).toMonoidHom) :=
      hcyc _ ((Subgroup.map_mono hEK).trans hK'cent) (hEp.map _)
    have hcycE : IsCyclic E := (Subgroup.equivMapOfInjective E _ hf).isCyclic.mpr hEgc
    have hexp : Monoid.exponent E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hE.2 e e.2)
    rw [IsCyclic.exponent_eq_card] at hexp
    have := Nat.le_of_dvd (Fact.out : p.Prime).pos hexp
    omega

theorem ggResI_o2a_facts (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) [Fact p.Prime]
    (hD : GGResLeviDatumCell p Bs L J K ggSelI (ggTypRankLt 8)
      (fun b CL CK u v => GGResO2aCell p b CL CK u v)) :
    p = 3 ∧ orderOf y = 3 ∧ K ≤ Subgroup.centralizer ({y} : Set G) ∧
      (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
      (∀ P : Subgroup G, P ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 P → IsCyclic P) ∧
      (∃ g : G, g * y * g⁻¹ ∈ K) ∧
      (∃ B₁ : Subgroup G, B₁ ≤ K ∧ IsElemAbelian 3 B₁ ∧ Nat.card B₁ = 3 ^ 3 ∧
        Subgroup.closure {y} ⊔ B₁ = Bs) ∧
      5 ∣ Nat.card (ggAutomizer ⊤ Bs) := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ,
    hrefl, hL, hK, hsel, -, -, hAL, hAK, -, hJ, hcell⟩ := hD
  obtain ⟨hp3, j₀, j₁, h01, hcov, c01, c10, c0b, cb0, c1b, cb1, c, c', hcc', kc'a, kac', hver⟩ :=
    hcell
  subst hp3
  have hind : LinearIndependent (ZMod 3) h := hsel
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  obtain ⟨cb, ver, k0a, ka0, k1a, ka1, hu, hv⟩ : ∃ cb ver : Bool,
      CK (some j₀) none = (if cb then (if ver then -1 else -2) else 0) ∧
      CK none (some j₀) = (if cb then (if ver then -2 else -1) else 0) ∧
      CK (some j₁) none = (if cb then 0 else (if ver then -1 else -2)) ∧
      CK none (some j₁) = (if cb then 0 else (if ver then -2 else -1)) ∧
      α none (h (some b)) = (if ver then 1 else 2) ∧
      α (some b) (h none) = (if ver then 2 else 1) := by
    rcases hcc' with ⟨hc, hc'⟩ | ⟨hc, hc'⟩ <;> rw [hc'] at kc'a kac' <;> rw [hc] at hver <;>
      rcases hver with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact ⟨true, true, by simpa using a1, by simpa using a2, by simpa using kc'a,
        by simpa using kac', by simpa using a3, by simpa using a4⟩
    · exact ⟨true, false, by simpa using a1, by simpa using a2, by simpa using kc'a,
        by simpa using kac', by simpa using a3, by simpa using a4⟩
    · exact ⟨false, true, by simpa using kc'a, by simpa using kac', by simpa using a1,
        by simpa using a2, by simpa using a3, by simpa using a4⟩
    · exact ⟨false, false, by simpa using kc'a, by simpa using kac', by simpa using a1,
        by simpa using a2, by simpa using a3, by simpa using a4⟩
  set σ := ggO2aσ j₀ j₁ with hσ
  have hσinj : Function.Injective σ := ggO2aσ_injective h01
  have hσsurj : Function.Surjective σ := by
    rintro (_ | i)
    · exact ⟨3, rfl⟩
    · rcases hcov i with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hind' : LinearIndependent (ZMod 3) (h ∘ σ) := hind.comp σ hσinj
  have hspan' : Submodule.span (ZMod 3) (Set.range (h ∘ σ)) = ⊤ := by
    rw [Set.range_comp, hσsurj.range_eq, Set.image_univ, hspan]
  have hKa : ∀ j : {i : Λ // i ≠ b}, α (some j.1) (h none) = (CK (some j) none : ZMod 3) :=
    fun j => hK (some j) none
  have haK : ∀ j : {i : Λ // i ≠ b}, α none (h (some j.1)) = (CK none (some j) : ZMod 3) :=
    fun j => hK none (some j)
  have haa : α none (h none) = 2 := by
    have h1 := hK none none
    rw [hCK.1 none] at h1
    simpa using h1
  have hT' : GGFTable (RingHom.id (ZMod 3)) (ggO2aT cb ver) (h ∘ σ) 0 (α ∘ σ) :=
    ggO2a_table cb ver hL hKa haK haa hCL.1 c01 c10 c0b cb0 c1b cb1 k0a ka0 k1a ka1 hu hv
  have hg' : ∀ k w, (fun k => ggLin (p := 3) ι (φ (σ k))) k w = w - (α ∘ σ) k w • (h ∘ σ) k :=
    fun k w => hφ (σ k) w
  have h2' : ∀ k, (α ∘ σ) k ((h ∘ σ) k) = 2 := fun k => by
    rw [hT'.1 k k]
    exact ggO2a_diag cb ver k
  obtain ⟨hfixL, hfus, h5, h51⟩ := ggResIO2a_linear cb ver hT' hg' hspan' hind'
  have hnb := hH.2.2.2.2.1
  have hBsEA : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hy3 : y ^ 3 = 1 := hBsEA.2 y hyBs
  have hBsNormK : Bs ≤ Subgroup.normalizer (K : Set G) := by
    have hIDK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
    obtain ⟨-, lab, -, hraw⟩ := hIDK
    obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hKmem : ∀ a : Fin 3, φ (σ (ggO2aβ a)) ∈ ggAutomizer K Bs := by
    intro a
    rw [hAK]
    fin_cases a
    · exact Subgroup.subset_closure (Or.inl ⟨j₀, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨j₁, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)
  have hkill : ∀ e : ↥Bs, K ≤ Subgroup.centralizer ({(e : G)} : Set G) →
      ∀ a : Fin 3, (α ∘ σ) (ggO2aβ a) (ι (Additive.ofMul e)) = 0 := fun e he a =>
    ggResI_alpha_eq_zero (by decide) (hφ _) (h2' (ggO2aβ a))
      ((ggLin_fix_iff ι _ _).mp (ggResI_automizer_fix e.2 he _ (hKmem a)))
  set yv : V := ι (Additive.ofMul ⟨y, hyBs⟩) with hyv
  obtain ⟨c₀, hc₀⟩ := hfixL yv (hkill ⟨y, hyBs⟩ hKy)
  have hyv0 : yv ≠ 0 := by
    intro h0
    apply hy1
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (h0.trans (map_zero ι).symm))
    exact congrArg Subtype.val h1
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀
    exact hyv0 hc₀
  have hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
    rintro e ⟨heBs, heK⟩
    have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heK k hk)
    obtain ⟨c₁, hc₁⟩ := hfixL _ (hkill ⟨e, heBs⟩ hKe)
    have hev : ι (Additive.ofMul ⟨e, heBs⟩) = (c₁ * c₀⁻¹) • yv := by
      rw [hc₁, hc₀, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]
    have he' : (⟨e, heBs⟩ : ↥Bs) = (⟨y, hyBs⟩ : ↥Bs) ^ (c₁ * c₀⁻¹).val := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [ofMul_pow, map_nsmul, hev, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    have hey : e = y ^ (c₁ * c₀⁻¹).val := by
      have h1 := congrArg Subtype.val he'
      simpa using h1
    rw [hey]
    exact Subgroup.npow_mem_zpowers y _
  have hcard3 : Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ 3 := by
    calc Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)
        ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hCent
      _ = orderOf y := Nat.card_zpowers y
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy3)
  have hcyc : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 P →
      IsCyclic P := fun P hP hPp =>
    ggSCNoTV_isCyclic (by decide) hBsEA hH.1.2.1.2.2.2 hH.2.2.2.1
      (hBsNormK.trans (normalizer_le_normalizer_centralizer K)) hcard3 hP hPp
  set W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range ((h ∘ σ) ∘ ggO2aβ)) with hW
  set B₁ : Subgroup G := ggSpanSub ι W with hB₁
  have hB₁K : B₁ ≤ K :=
    ggSpanSub_le ι fun a => ggCoroot_mem (by decide) hBsNormK ι (hφ (σ (ggO2aβ a)))
      (h2' (ggO2aβ a)) (hKmem a)
  have hB₁Bs : B₁ ≤ Bs := ggSpanSub_le_bs ι W
  have hβinj : Function.Injective ggO2aβ := by decide
  have hcardB₁ : Nat.card B₁ = 3 ^ 3 := by
    have : Finite V := Finite.of_equiv _ ι.toEquiv
    rw [hB₁, card_ggSpanSub, ← FiniteField.pow_finrank_eq_natCard 3 W, hW,
      finrank_span_eq_card (hind'.comp ggO2aβ hβinj), Fintype.card_fin]
  have hB₁EA : IsElemAbelian 3 B₁ := by
    have := hBsEA.1
    refine ⟨⟨⟨fun a e => ?_⟩⟩, fun z hz => hBsEA.2 z (hB₁Bs hz)⟩
    have hc := congrArg Subtype.val (mul_comm' (⟨a, hB₁Bs a.2⟩ : Bs) ⟨e, hB₁Bs e.2⟩)
    exact Subtype.ext (by simpa using hc)
  have hCN : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    ggNbr_centralizer_le_normalizer hH hcyc hB₁K hB₁EA (by rw [hcardB₁]; norm_num)
  have hyB₁ : y ∉ B₁ := by
    intro hy
    have hyW : yv ∈ W := coe_mem_ggSpanSub_iff.mp hy
    obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hyW
    have hk : ∀ k : Fin 3,
        ∑ a : Fin 3, e a * (ggO2aT cb ver (ggO2aβ k)).get (ggO2aβ a).castSucc = 0 := by
      intro k
      have hT1 : ∀ k l : Fin 4, α (σ k) (h (σ l)) = (ggO2aT cb ver k).get l.castSucc :=
        fun k l => hT'.1 k l
      have h1 := hkill ⟨y, hyBs⟩ hKy k
      rw [← hyv, ← he, map_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, map_smul, smul_eq_mul, hT1]
    have he0 := ggO2a_cartanK cb ver e hk
    apply hyv0
    rw [← he, he0]
    simp
  have hcardBs : Nat.card Bs = 3 ^ 4 := by
    have : Finite V := Finite.of_equiv _ ι.toEquiv
    have h1 := finrank_span_eq_card hind'
    rw [hspan', finrank_top, Fintype.card_fin] at h1
    rw [Nat.card_congr (Additive.ofMul.trans ι.toEquiv), ← FiniteField.pow_finrank_eq_natCard 3 V,
      h1]
  have hSBs : Subgroup.closure {y} ⊔ B₁ ≤ Bs :=
    sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hyBs)) hB₁Bs
  have hS : Subgroup.closure {y} ⊔ B₁ = Bs := by
    refine Subgroup.eq_of_le_of_card_ge hSBs ?_
    have hdvd1 : Nat.card B₁ ∣ Nat.card (Subgroup.closure {y} ⊔ B₁ : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_right
    have hdvd2 : Nat.card (Subgroup.closure {y} ⊔ B₁ : Subgroup G) ∣ Nat.card Bs :=
      Subgroup.card_dvd_of_le hSBs
    have hne : Nat.card (Subgroup.closure {y} ⊔ B₁ : Subgroup G) ≠ Nat.card B₁ := by
      intro heq
      apply hyB₁
      have h1 : B₁ = Subgroup.closure {y} ⊔ B₁ :=
        Subgroup.eq_of_le_of_card_ge le_sup_right heq.le
      rw [h1]
      exact le_sup_left (a := Subgroup.closure {y}) (Subgroup.subset_closure rfl)
    rw [hcardB₁] at hdvd1 hne
    rw [hcardBs] at hdvd2 ⊢
    obtain ⟨m, hm⟩ := hdvd1
    rw [hm] at hdvd2 hne ⊢
    have hm3 : m ∣ 3 := by
      have h1 : 3 ^ 3 * m ∣ 3 ^ 3 * 3 := by simpa using hdvd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hm3 with rfl | rfl
    · exact absurd (by ring) hne
    · norm_num
  set ψH : MulAut ↥Bs := (ggO2aH.map fun k => φ (σ k)).prod with hψH
  have hlin : ∀ ws : List (Fin 4), ggLin (p := 3) ι (ws.map fun k => φ (σ k)).prod =
      (ws.map fun k => ggLin (p := 3) ι (φ (σ k))).prod := fun ws => by
    rw [map_list_prod, List.map_map]
    rfl
  have hmemA : ∀ ws : List (Fin 4), (ws.map fun k => φ (σ k)).prod ∈ ggAutomizer ⊤ Bs := by
    intro ws
    have h1 : (ws.map fun k => φ (σ k)).prod ∈ Subgroup.closure (Set.range φ) :=
      Subgroup.list_prod_mem _ fun t ht => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ht
        exact Subgroup.subset_closure ⟨σ k, rfl⟩
    rw [← ggResI_sup_eq_closure hAL hAK] at h1
    exact Subgroup.subset_closure (ggResI_mem_ggInduced_top h1)
  obtain ⟨gH, -, hgN, hgψ⟩ := eq_ggConjAut_of_mem_ggAutomizer (hmemA ggO2aH)
  have hfusion : gH * y * gH⁻¹ ∈ K := by
    apply hB₁K
    have h1 : ((ψH ⟨y, hyBs⟩ : ↥Bs) : G) = gH * y * gH⁻¹ := by
      rw [hψH, hgψ, ggConjAut_apply]
    rw [← h1, coe_mem_ggSpanSub_iff, ← ggLin_apply_ofMul (p := 3) ι ψH, ← hyv, hc₀, map_smul,
      hψH, hlin]
    exact W.smul_mem _ hfus
  have h5dvd : 5 ∣ Nat.card (ggAutomizer ⊤ Bs) := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    set ψ5 : MulAut ↥Bs := ((ggO2aW5 cb).map fun k => φ (σ k)).prod with hψ5
    have hpow : ψ5 ^ 5 = 1 := by
      apply ggLin_injective (p := 3) ι
      rw [map_pow, hψ5, hlin, map_one]
      exact h5
    have hne : ψ5 ≠ 1 := by
      intro h1
      apply h51
      rw [← hlin, ← hψ5, h1, map_one]
    rw [← orderOf_eq_prime hpow hne]
    exact Subgroup.orderOf_dvd_natCard _ (hmemA (ggO2aW5 cb))
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨rfl, orderOf_eq_prime hy3 hy1, hKy,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKy).mpr hCN, hcyc, ⟨gH, hfusion⟩,
    ⟨B₁, hB₁K, hB₁EA, hcardB₁, hS⟩, h5dvd⟩

end CFSG.StandardType
