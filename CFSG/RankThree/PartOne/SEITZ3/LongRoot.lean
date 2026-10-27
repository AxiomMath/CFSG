module

public import CFSG.RankThree.PartOne.SEITZ3.Conj
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.Bruhat
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley.RootWalk
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld.RankTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {K : Type} [Field K]

abbrev rt (p : ℕ) : Fin 2 → ℤ := (Tag.rootCertificate .G2).root p
noncomputable abbrev xp
    (p : ℕ) (c : K) : adjointGroup .G2 K := xPar
    (rootOperatorFamily .G2) (rt p) c
noncomputable abbrev Xp
    (K : Type) [Field K] (p : ℕ) : Subgroup (adjointGroup .G2 K) :=
  (g2Datum K).rootGroup (rt p)

theorem len_roots : (Tag.rootCertificate .G2).roots.length = 12 := by decide +kernel
theorem isRoot_rt
    {p : ℕ} (hp : p < 12) : IsRoot .G2 (rt p) :=
  isRoot_rootCertificate_root (by rw [len_roots]; exact hp)

theorem mem_Xp_iff
    {p : ℕ} (hp : p < 12)
    (g : adjointGroup .G2 K) :
    g ∈ Xp K p ↔ ∃ c : K, xp p c = g :=
  mem_rootGroup_iff (isRoot_rt hp) g

theorem xp_add
    (p : ℕ) (c d : K) : xp p (c + d) =
    xp p c * xp p d := xPar_add _ _ _

theorem xp_zero
    (p : ℕ) : xp p (0 : K) = 1 := by
  have := xp_add (K := K) p 0 0
  simpa using this

theorem xp_mul_self
    [CharP K 2] (p : ℕ) (c : K) : xp p c
    * xp p c = 1 := by
  rw [← xp_add, CharTwo.add_self_eq_zero, xp_zero]

theorem Xp_mul_self
    [CharP K 2] {p : ℕ} (hp : p < 12)
    {x : adjointGroup .G2 K} (hx : x ∈ Xp K p) :
    x * x = 1 := by
  obtain ⟨c, rfl⟩ := (mem_Xp_iff hp x).1 hx
  exact xp_mul_self p c

theorem commute_of_check
    {a b : ℕ} (ha : a < 12)
    (hb : b < 12) (h : repCheck .G2 a b [] = true) :
    ∀ x ∈ Xp K a, ∀ y ∈ Xp K b, Commute x y := by
  intro x hx y hy
  obtain ⟨s, rfl⟩ := (mem_Xp_iff ha x).1 hx
  obtain ⟨t, rfl⟩ := (mem_Xp_iff hb y).1 hy
  have := commutator_xPar_of_repCheck (τ := .G2) (K := K) h s t
  simp at this
  exact commutatorElement_eq_one_iff_commute.1 this

theorem comm_Xp_of_check
    [CharP K 2] {a b t : ℕ} {C : ℤ}
    (ha : a < 12) (hb : b < 12) (ht : t < 12)
    (h : repCheck .G2 a b [(1, 1, t, C)] = true) (hC : Odd C) :
    ⁅Xp K a, Xp K b⁆ = Xp K t := by
  have hC1 : (C : K) = 1 := cast_odd_eq_one hC
  have key : ∀ s u : K, ⁅xp a s, xp b u⁆ = xp t (s * u) := by
    intro s u
    have := commutator_xPar_of_repCheck (τ := .G2) (K := K) h s u
    simpa [hC1] using this
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨s, rfl⟩ := (mem_Xp_iff ha x).1 hx
    obtain ⟨u, rfl⟩ := (mem_Xp_iff hb y).1 hy
    rw [key]
    exact (mem_Xp_iff ht _).2 ⟨_, rfl⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := (mem_Xp_iff ht z).1 hz
    have hmem : ⁅xp a c, xp b 1⁆ ∈ ⁅Xp K a, Xp K b⁆ :=
      Subgroup.commutator_mem_commutator ((mem_Xp_iff ha _).2 ⟨c, rfl⟩)
        ((mem_Xp_iff hb _).2 ⟨1, rfl⟩)
    rw [key, mul_one] at hmem
    exact hmem


@[expose] def e0 : Fin (Tag.rank .G2) := ⟨0, by decide⟩
@[expose] def e1 : Fin (Tag.rank .G2) := ⟨1, by decide⟩

theorem refl_70 : RootSystem.reflection (Tag.cartan .G2) e0 (rt 7) = rt 3 := by decide +kernel
theorem refl_31 : RootSystem.reflection (Tag.cartan .G2) e1 (rt 3) = rt 0 := by decide +kernel
theorem refl_00 : RootSystem.reflection (Tag.cartan .G2) e0 (rt 0) = rt 2 := by decide +kernel
theorem refl_21 : RootSystem.reflection (Tag.cartan .G2) e1 (rt 2) = rt 6 := by decide +kernel
theorem refl_60 : RootSystem.reflection (Tag.cartan .G2) e0 (rt 6) = rt 10 := by decide +kernel

theorem conj_Xp
    (i : Fin (Tag.rank .G2)) {p q : ℕ}
    (hp : p < 12)
    (h : RootSystem.reflection (Tag.cartan .G2) i (rt p) = rt q) :
    (Xp K p).map (MulAut.conj (weylElement .G2 K i)).toMonoidHom = Xp K q := by
  have hγ : rt p ∈ (g2Datum K).roots := mem_g2_roots.2 (isRoot_rt hp)
  have := map_conj_rootGroup (g2_isCTGroupDatum K) i hγ
  rw [RootSystem.ofCartan_refl_apply] at this
  rw [this]
  congr 1

@[expose] def longPos : Finset ℕ := {0, 2, 3, 6, 7, 10}

theorem refl_long : ∀ t ∈ longPos, ∀ i : Fin (Tag.rank .G2), ∃ t' ∈ longPos,
    RootSystem.reflection (Tag.cartan .G2) i (rt t) = rt t' := by decide +kernel


section Weyl
open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
variable (K)

theorem weylAction_long
    (w : (coxeterMatrix (g2Datum K).isFiniteType).Group) :
    ∀ t ∈ longPos, ∃ t' ∈ longPos, weylAction (g2Datum K).isFiniteType w (rt t) = rt t' := by
  obtain ⟨ω, -, rfl⟩ :=
    ((coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem).exists_isReduced w
  induction ω with
  | nil =>
    intro t ht
    exact ⟨t, ht, by simp⟩
  | cons i l ih =>
    intro t ht
    obtain ⟨t', ht', h'⟩ := ih t ht
    obtain ⟨t'', ht'', h''⟩ := refl_long t' ht' i
    refine ⟨t'', ht'', ?_⟩
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, h', weylAction_simple]
    exact h''

end Weyl


theorem repCheck_pos7 : ∀ p ∈ ({0, 1, 3, 4, 8} : Finset ℕ), repCheck .G2 p 7 [] = true := by
  decide +kernel

theorem ht_pos_aux : ∀ p < 12, 0 < ht (rt p) → p ∈ ({0, 1, 3, 4, 7, 8} : Finset ℕ) := by
  decide +kernel

theorem commute_Xp_pos7
    {p : ℕ}
    (hp : p ∈ ({0, 1, 3, 4, 7, 8} : Finset ℕ)) :
    ∀ x ∈ Xp K p, ∀ y ∈ Xp K 7, Commute x y := by
  intro x hx y hy
  by_cases h7 : p = 7
  · subst h7
    obtain ⟨s, rfl⟩ := (mem_Xp_iff (by norm_num) x).1 hx
    obtain ⟨t, rfl⟩ := (mem_Xp_iff (by norm_num) y).1 hy
    show xp 7 s * xp 7 t = xp 7 t * xp 7 s
    rw [← xp_add, ← xp_add, add_comm]
  · have hp' : p ∈ ({0, 1, 3, 4, 8} : Finset ℕ) := by
      simpa [h7] using hp
    exact commute_of_check (by simp at hp'; omega) (by norm_num) (repCheck_pos7 p hp') x hx y hy

section Reduction
open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
variable (K)

theorem borel_le_normalizer_X7 :
    borel (g2Datum K) (torus (τ := .G2) K) ≤
      Subgroup.normalizer (Xp K 7 : Set (adjointGroup .G2 K)) := by
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    intro h hh
    exact mem_normalizer_rootGroup (g2_isCTGroupDatum K) hh
      (mem_g2_roots.2 (isRoot_rt (by norm_num)))
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    obtain ⟨k, hk, rfl⟩ :=
      RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) (mem_g2_roots.1 hγR)
    have hk' : k < 12 := by simpa [len_roots] using hk
    have hkp := ht_pos_aux k hk' hγp
    exact le_normalizer_of_commute (commute_Xp_pos7 hkp)

end Reduction

section LongClass
open CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
variable (K)

@[expose] def longClass :
    Set (Subgroup (adjointGroup .G2 K)) := Set.range
    (conjSub (Xp K 7))

variable {K}

theorem conjSub_mem_longClass
    {A : Subgroup (adjointGroup .G2 K)} (hA : A ∈ longClass K)
    (g : adjointGroup .G2 K) :
    conjSub A g ∈ longClass K := by
  obtain ⟨h, rfl⟩ := hA
  exact ⟨g * h, by rw [conjSub_mul]⟩


end LongClass

section LongClass2
open CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem conjSub_Xp
    (i : Fin (Tag.rank .G2)) {p q : ℕ}
    (hp : p < 12)
    (h : RootSystem.reflection (Tag.cartan .G2) i (rt p) = rt q) :
    conjSub (Xp K p) (weylElement .G2 K i) = Xp K q := conj_Xp i hp h

theorem Xp_mem_longClass
    {t : ℕ} (ht : t ∈ longPos) : Xp K t
    ∈ longClass K := by
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
  have h3 := conjSub_Xp (K := K) e0 (by norm_num) refl_70
  have h0 := conjSub_Xp (K := K) e1 (by norm_num) refl_31
  have h2 := conjSub_Xp (K := K) e0 (by norm_num) refl_00
  have h6 := conjSub_Xp (K := K) e1 (by norm_num) refl_21
  have h10 := conjSub_Xp (K := K) e0 (by norm_num) refl_60
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨weylElement .G2 K e1 * weylElement .G2 K e0, by rw [conjSub_mul, h3, h0]⟩
  · exact ⟨weylElement .G2 K e0 * (weylElement .G2 K e1 * weylElement .G2 K e0), by
      rw [conjSub_mul, conjSub_mul, h3, h0, h2]⟩
  · exact ⟨weylElement .G2 K e0, h3⟩
  · exact ⟨weylElement .G2 K e1 * (weylElement .G2 K e0 *
      (weylElement .G2 K e1 * weylElement .G2 K e0)), by
      rw [conjSub_mul, conjSub_mul, conjSub_mul, h3, h0, h2, h6]⟩
  · exact ⟨1, by simp⟩
  · exact ⟨weylElement .G2 K e0 * (weylElement .G2 K e1 * (weylElement .G2 K e0 *
      (weylElement .G2 K e1 * weylElement .G2 K e0))), by
      rw [conjSub_mul, conjSub_mul, conjSub_mul, conjSub_mul, h3, h0, h2, h6, h10]⟩

end LongClass2

section Standard
open CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem exists_standard_pair
    {A B : Subgroup (adjointGroup .G2 K)} (hA : A ∈ longClass K)
    (hB : B ∈ longClass K) :
    ∃ g : adjointGroup .G2 K, ∃ t ∈ longPos, conjSub A g = Xp K 7 ∧ conjSub B g = Xp K t := by
  obtain ⟨g₁, rfl⟩ := hA
  obtain ⟨g₂, rfl⟩ := hB
  have hct := g2_isCTGroupDatum K
  have hext := g2_steinbergExtras K
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hh⟩ := exists_mem_bruhatCell hct hext (g₁⁻¹ * g₂)
  obtain ⟨t, ht, hrt⟩ := weylAction_long K w 7 (by simp [longPos])
  refine ⟨b₁⁻¹ * g₁⁻¹, t, ht, ?_, ?_⟩
  · rw [← conjSub_mul, show b₁⁻¹ * g₁⁻¹ * g₁ = b₁⁻¹ by group]
    exact conjSub_of_mem_normalizer (Subgroup.inv_mem _ (borel_le_normalizer_X7 K hb₁))
  · rw [← conjSub_mul]
    have e : b₁⁻¹ * g₁⁻¹ * g₂ = nrep hct w * b₂ := by
      have : g₁⁻¹ * g₂ = b₁ * nrep hct w * b₂ := hh
      calc b₁⁻¹ * g₁⁻¹ * g₂ = b₁⁻¹ * (g₁⁻¹ * g₂) := by group
        _ = b₁⁻¹ * (b₁ * nrep hct w * b₂) := by rw [this]
        _ = nrep hct w * b₂ := by group
    rw [e, conjSub_mul, conjSub_of_mem_normalizer (borel_le_normalizer_X7 K hb₂)]
    have hact := actsAs_nrep hct w (rt 7) (mem_g2_roots.2 (isRoot_rt (by norm_num)))
    rw [hrt] at hact
    exact hact

end Standard

section OppositeLong
open CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS

theorem refl_03 : RootSystem.reflection (Tag.cartan .G2) e1 (rt 0) = rt 3 := by decide +kernel
theorem refl_37 : RootSystem.reflection (Tag.cartan .G2) e0 (rt 3) = rt 7 := by decide +kernel

theorem rt0_eq : rt 0 = Pi.single e0 1 := by
  ext i; fin_cases i <;> decide
theorem rt2_eq : rt 2 = -Pi.single e0 1 := by
  ext i; fin_cases i <;> decide

theorem opposite_Xp_0_2 :
    Opposite (Xp K 0) (Xp K 2) := by
  obtain ⟨φ, hφ, hu, hl⟩ := g2_exists_sl2_hom (K := K) e0
  refine opposite_of_sl2 φ hφ ?_ ?_
  · intro x
    rw [mem_Xp_iff (by norm_num)]
    simp only [hu, xp, rt0_eq, xPar_simple]
  · intro x
    rw [mem_Xp_iff (by norm_num)]
    simp only [hl, xp, rt2_eq, xPar_neg_simple]

theorem opposite_Xp_7_10 :
    Opposite (Xp K 7) (Xp K 10) := by
  have h := opposite_Xp_0_2 (K := K)
  have h1 := conjSub_Xp (K := K) e1 (by norm_num) refl_03
  have h2 := conjSub_Xp (K := K) e1 (by norm_num) refl_21
  have h3 := conjSub_Xp (K := K) e0 (by norm_num) refl_37
  have h4 := conjSub_Xp (K := K) e0 (by norm_num) refl_60
  have := opposite_conj h (weylElement .G2 K e0 * weylElement .G2 K e1)
  rwa [conjSub_mul, conjSub_mul, h1, h2, h3, h4] at this

end OppositeLong

section Dichotomy
open CFSG.Timmesfeld.ARS

theorem rep_3_2 : repCheck .G2 3 2 [] = true := by decide +kernel
theorem rep_0_6 : repCheck .G2 0 6 [] = true := by decide +kernel
theorem rep_2_7 : repCheck .G2 2 7 [(1, 1, 3, 1)] = true := by decide +kernel
theorem rep_6_7 : repCheck .G2 6 7 [(1, 1, 0, -1)] = true := by decide +kernel
theorem rep_7_0 : repCheck .G2 7 0 [] = true := by decide +kernel
theorem rep_7_3 : repCheck .G2 7 3 [] = true := by decide +kernel

theorem standard_dichotomy
    [CharP K 2] {t : ℕ}
    (ht : t ∈ longPos) (ht7 : t ≠ 7) :
    Commuting (Xp K 7) (Xp K t) ∨ Opposite (Xp K 7) (Xp K t) ∨
      Special (longClass K) (Xp K 7) (Xp K t) := by
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (commute_of_check (by norm_num) (by norm_num) rep_7_0)
  · refine Or.inr (Or.inr ?_)
    have hc : ⁅Xp K 7, Xp K 2⁆ = Xp K 3 := by
      rw [Subgroup.commutator_comm]
      exact comm_Xp_of_check (by norm_num) (by norm_num) (by norm_num) rep_2_7 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]; exact Xp_mem_longClass (by simp [longPos])
    · rw [hc]; exact commute_Xp_pos7 (by simp)
    · rw [hc]
      intro a ha b hb
      exact (commute_of_check (K := K) (by norm_num) (by norm_num) rep_3_2) a ha b hb
  · exact Or.inl (commute_of_check (by norm_num) (by norm_num) rep_7_3)
  · refine Or.inr (Or.inr ?_)
    have hc : ⁅Xp K 7, Xp K 6⁆ = Xp K 0 := by
      rw [Subgroup.commutator_comm]
      exact comm_Xp_of_check (by norm_num) (by norm_num) (by norm_num) rep_6_7 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]; exact Xp_mem_longClass (by simp [longPos])
    · rw [hc]; exact commute_Xp_pos7 (by simp)
    · rw [hc]
      intro a ha b hb
      exact (commute_of_check (K := K) (by norm_num) (by norm_num) rep_0_6) a ha b hb
  · exact absurd rfl ht7
  · exact Or.inr (Or.inl opposite_Xp_7_10)

end Dichotomy

section Main
open CFSG.Timmesfeld.ARS

theorem long_pair_dichotomy
    [CharP K 2]
    {A B : Subgroup (adjointGroup .G2 K)} (hA : A ∈ longClass K)
    (hB : B ∈ longClass K) (hne : A ≠ B) :
    Commuting A B ∨ Opposite A B ∨ Special (longClass K) A B := by
  obtain ⟨g, t, ht, hgA, hgB⟩ := exists_standard_pair hA hB
  have ht7 : t ≠ 7 := by
    rintro rfl
    exact hne (conjSub_inj g (hgA.trans hgB.symm))
  have hR : ∀ A ∈ longClass K, ∀ g : adjointGroup .G2 K, conjSub A g ∈ longClass K :=
    fun A hA g => conjSub_mem_longClass hA g
  rcases standard_dichotomy (K := K) ht ht7 with h | h | h
  · left
    rw [← hgA, ← hgB] at h
    have := commuting_conj h g⁻¹
    rwa [conjSub_conjSub_inv', conjSub_conjSub_inv'] at this
  · right; left
    rw [← hgA, ← hgB] at h
    have := opposite_conj h g⁻¹
    rwa [conjSub_conjSub_inv', conjSub_conjSub_inv'] at this
  · right; right
    rw [← hgA, ← hgB] at h
    have := special_conj hR h g⁻¹
    rwa [conjSub_conjSub_inv', conjSub_conjSub_inv'] at this

theorem longClass_mul_self
    [CharP K 2]
    {A : Subgroup (adjointGroup .G2 K)} (hA : A ∈ longClass K) :
    ∀ a ∈ A, a * a = 1 := by
  obtain ⟨g, rfl⟩ := hA
  rintro _ ⟨x, hx, rfl⟩
  have hxx := Xp_mul_self (K := K) (p := 7) (by norm_num) hx
  show (MulAut.conj g).toMonoidHom x * (MulAut.conj g).toMonoidHom x = 1
  rw [← map_mul, hxx, map_one]

theorem longClass_ne_bot
    {A : Subgroup (adjointGroup .G2 K)}
    (hA : A ∈ longClass K) : A ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := hA
  intro h
  have h1 : xp 7 (1 : K) ∈ Xp K 7 := (mem_Xp_iff (by norm_num) _).2 ⟨1, rfl⟩
  have h2 : (MulAut.conj g).toMonoidHom (xp 7 (1 : K)) ∈ conjSub (Xp K 7) g := ⟨_, h1, rfl⟩
  rw [h] at h2
  have h3 : xp 7 (1 : K) = 1 := by
    have : (MulAut.conj g).toMonoidHom (xp 7 (1 : K)) = 1 := h2
    simpa using this
  have := xPar_injective (F := rootOperatorFamily .G2) (K := K) (γ := rt 7)
    (isRoot_rt (by norm_num))
  have h4 : xp 7 (1 : K) = xp 7 0 := by rw [h3, xp_zero]
  exact one_ne_zero (this h4)

end Main

end CFSG.RankThree.PartOne.SEITZ3
