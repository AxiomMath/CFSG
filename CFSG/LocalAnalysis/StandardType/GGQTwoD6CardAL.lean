module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALA
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALB
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALR
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALC
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALD
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2d6l_center_perm_eq_bot (α : Type*) [Fintype α] [DecidableEq α]
    (hα : 3 ≤ Fintype.card α) : Subgroup.center (Equiv.Perm α) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [Subgroup.mem_center_iff] at hσ
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  set c := σ a with hc
  have hca : c ≠ a := by rw [hc]; exact ha
  have hcard : ({a, c} : Finset α).card < Fintype.card α := by
    calc ({a, c} : Finset α).card ≤ 2 := Finset.card_le_two
      _ < 3 := by norm_num
      _ ≤ Fintype.card α := hα
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hba : b ≠ a := hb.1
  have hbc : b ≠ c := hb.2
  have key : σ b = Equiv.swap a b (σ a) := by
    have h := DFunLike.congr_fun (hσ (Equiv.swap a b)) a
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h
    exact h.symm
  have hsw : Equiv.swap a b c = c :=
    Equiv.swap_apply_of_ne_of_ne hca (Ne.symm hbc)
  rw [hsw, hc] at key
  exact hba (σ.injective key)

private lemma ggQ2d6l_refl_iff {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : MulAut ↥Bs) :
    GGIsReflection 3 φ ↔ IsRefl3 (ggLin (p := 3) ι φ) := by
  rw [ggIsReflection_iff (p := 3) ι φ, IsRefl3, pow_two]

private lemma ggQ2d6l_largeEvenLayer_le {G : Type} [Group G] (H : Subgroup G) :
    LargeEvenLayer H ≤ H := by
  change sSup {K : Subgroup G | IsComponentOf K H} ≤ H
  exact sSup_le fun K hK => hK.1

private lemma ggQ2d6l_model_simple_refl {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {x : G} {L D J : Subgroup G} [Fact (Nat.Prime 3)] {y' : G}
    {K' : Subgroup G} (M' : GGQTwoModel 3 Bs x y' D L J K') (i : M'.ι) :
    GGIsReflection 3 (M'.simple i) := by
  have hfx : M'.root i (M'.coroot i) = 2 := by
    rw [M'.pairing i i, M'.isCartan.1 i]
    norm_num
  exact ggIsReflection_of_eq_reflection (by norm_num) M'.model hfx
    (ggLin_eq_reflection M'.model hfx (M'.simple_apply i))

private lemma ggQ2d6l_center_AJ {G : Type} [Group G] {Bs : Subgroup G}
    (AJ : Subgroup (MulAut ↥Bs)) (Φ : Equiv.Perm (Fin 6) ≃* ↥AJ) :
    Subgroup.center ↥AJ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Subgroup.mem_center_iff] at ha
  have hσ : Φ.symm a = 1 := by
    have hc : Φ.symm a ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro τ
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact ha (Φ τ)
    rw [ggQ2d6l_center_perm_eq_bot (Fin 6) (by simp)] at hc
    simpa using hc
  calc a = Φ (Φ.symm a) := (MulEquiv.apply_symm_apply Φ a).symm
    _ = Φ 1 := by rw [hσ]
    _ = 1 := map_one Φ

private lemma ggQ2d6l_refl_ne_one {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection 3 φ) : φ ≠ 1 := by
  intro h1
  have hfix : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun b => rfl)
  rw [h1] at h
  obtain ⟨-, hcard⟩ := h
  rw [hfix] at hcard
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  omega

private lemma ggQ2d6l_card_AJ {G : Type} [Group G] {Bs : Subgroup G}
    (AJ : Subgroup (MulAut ↥Bs)) (Φ : Equiv.Perm (Fin 6) ≃* ↥AJ) :
    Nat.card ↥AJ = 720 := by
  rw [← Nat.card_congr Φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  norm_num

theorem ggQ2_D6_card_AL_gt {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3)
    {y' : G} {K K' : Subgroup G} (N : GGQ2NbrDatum p Bs K) (b : N.Λ) (hb : N.IsD6Fork b)
    (hJ : ggAutomizer J Bs = Subgroup.closure (N.simple '' {k | k ≠ b}))
    (M' : GGQTwoModel p Bs x y' D L J K') :
    1440 < Nat.card ↥(ggAutomizer L Bs) := by
  subst hp
  let AJ : Subgroup (MulAut ↥Bs) := Subgroup.closure (N.simple '' {k | k ≠ b})
  let AL : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  obtain ⟨Φ, Dm, hΦρ, hΦ1⟩ := ggQ2d6l_modData hS N b hb
  have hle : AJ ≤ AL := by
    have hJL : J ≤ L := by
      obtain ⟨-, -, hDJ⟩ := hS.1.1
      obtain ⟨-, -, -, -, hJeq, -, -⟩ := hDJ.1
      rw [hJeq]
      exact (ggQ2d6l_largeEvenLayer_le _).trans inf_le_left
    have h := ggAutomizer_mono Bs hJL
    rw [hJ] at h
    simpa only [AJ, AL] using h
  have hnot : ¬ AL ≤ AJ := by
    have h := ggQ2d6l_not_AL_le_AJ hS M'
    rw [hJ] at h
    simpa only [AJ, AL] using h
  have hVN : Finite N.V := Finite.of_equiv (Additive ↥Bs) N.model.toEquiv
  have : Finite N.V := hVN
  have hΦ2 : ∀ r ∈ AJ, GGIsReflection 3 r → ∃ t ∈ ggTransp 6, r = (Φ t : MulAut ↥Bs) := by
    intro r hr hrrefl
    refine ⟨Φ.symm ⟨r, hr⟩, ?_, ?_⟩
    · apply ggQ2d6l_refl_perm Dm
      rw [hΦρ]
      have hfix : (Φ (Φ.symm ⟨r, hr⟩) : MulAut ↥Bs) = r := by
        rw [MulEquiv.apply_symm_apply]
      rw [hfix]
      exact (ggQ2d6l_refl_iff N.model r).mp hrrefl
    · rw [MulEquiv.apply_symm_apply]
  let Z : Subgroup (MulAut ↥Bs) := Subgroup.centralizer (AJ : Set (MulAut ↥Bs)) ⊓ AL
  have hzAJZ : AJ ⊓ Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxAJ, hxZ⟩ := hx
    rw [Subgroup.mem_inf] at hxZ
    obtain ⟨hxc, -⟩ := hxZ
    have hxcomm : ∀ r : ↥AJ, r * ⟨x, hxAJ⟩ = ⟨x, hxAJ⟩ * r := by
      intro r
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) r r.2)
    have hx1 : (⟨x, hxAJ⟩ : ↥AJ) = 1 := by
      have hmem : (⟨x, hxAJ⟩ : ↥AJ) ∈ Subgroup.center ↥AJ := by
        rw [Subgroup.mem_center_iff]
        exact hxcomm
      have h := (Subgroup.eq_bot_iff_forall (Subgroup.center ↥AJ)).mp
        (ggQ2d6l_center_AJ AJ Φ)
      exact h ⟨x, hxAJ⟩ hmem
    exact Subtype.ext_iff.mp hx1
  by_contra hlt
  push Not at hlt
  have hcard : Nat.card ↥AL ≤ 1440 := hlt
  have hC := ggQ2d6l_inner_of_index_two AJ AL hle hnot Φ hΦ1 hΦ2 hcard
  have hAJcard : Nat.card ↥AJ = 720 := ggQ2d6l_card_AJ AJ Φ
  have hstep4 : ∀ s ∈ AL, GGIsReflection 3 s → s ∈ AJ ∨ s ∈ Z := by
    intro s hsAL hsrefl
    by_cases hsAJ : s ∈ AJ
    · exact Or.inl hsAJ
    · right
      obtain ⟨g, hgAJ, hgconj⟩ := hC s hsAL
      set z : MulAut ↥Bs := g⁻¹ * s with hzdef
      have hzAL : z ∈ AL := AL.mul_mem (AL.inv_mem (hle hgAJ)) hsAL
      have hzcomm : ∀ r ∈ AJ, z * r = r * z := by
        intro r hr
        calc z * r = g⁻¹ * (s * r * s⁻¹) * s := by rw [hzdef]; group
          _ = g⁻¹ * (g * r * g⁻¹) * s := by rw [hgconj r hr]
          _ = r * z := by rw [hzdef]; group
      have hzZ : z ∈ Z := by
        rw [Subgroup.mem_inf]
        exact ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => (hzcomm r hr).symm, hzAL⟩
      have hzg : s * g⁻¹ = g⁻¹ * s := by
        have h := hgconj g⁻¹ (Subgroup.inv_mem _ hgAJ)
        have h' : s * g⁻¹ * s⁻¹ = g⁻¹ := by simpa using h
        calc s * g⁻¹ = (s * g⁻¹ * s⁻¹) * s := by group
          _ = g⁻¹ * s := by rw [h']
      have hss : s * s = 1 := by
        have h := hsrefl.1
        rwa [pow_two] at h
      have hzzAJ : z * z ∈ AJ := by
        have hzz : z * z = (g ^ 2)⁻¹ * (s * s) := by
          calc z * z = g⁻¹ * (s * g⁻¹) * s := by rw [hzdef]; group
            _ = g⁻¹ * (g⁻¹ * s) * s := by rw [hzg]
            _ = (g ^ 2)⁻¹ * (s * s) := by group
        rw [hzz, hss, mul_one]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hgAJ 2)
      have hzzZ : z * z ∈ Z := by
        rw [Subgroup.mem_inf]
        refine ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, AL.mul_mem hzAL hzAL⟩
        show r * (z * z) = (z * z) * r
        calc r * (z * z) = (r * z) * z := by group
          _ = (z * r) * z := by rw [hzcomm r hr]
          _ = z * (r * z) := by group
          _ = z * (z * r) := by rw [hzcomm r hr]
          _ = (z * z) * r := by group
      have hzz1 : z * z = 1 := by
        have hmem : z * z ∈ AJ ⊓ Z := ⟨hzzAJ, hzzZ⟩
        rw [hzAJZ] at hmem
        simpa using hmem
      have hz_ne_one : z ≠ 1 := by
        intro hz1
        apply hsAJ
        have hs_eq : s = g := by
          calc s = g * (g⁻¹ * s) := by group
            _ = g * z := by rw [hzdef]
            _ = g * 1 := by rw [hz1]
            _ = g := mul_one g
        rw [hs_eq]; exact hgAJ
      have hg' : (Φ.symm ⟨g, hgAJ⟩) = 1 := by
        refine ggQ2d6l_refl_mul_central Dm (ggLin (p := 3) N.model z)
          (Φ.symm ⟨g, hgAJ⟩) ?_ ?_ ?_ ?_
        · intro h1
          exact hz_ne_one (ggLin_injective N.model (by rw [h1, map_one]))
        · rw [← map_mul, hzz1, map_one]
        · intro σ
          rw [hΦρ σ, ← map_mul, ← map_mul]
          rw [hzcomm (Φ σ) (Φ σ).2]
        · have hval' : Dm.ρ (Φ.symm ⟨g, hgAJ⟩) * ggLin (p := 3) N.model z =
              ggLin (p := 3) N.model s := by
            rw [hΦρ (Φ.symm ⟨g, hgAJ⟩), MulEquiv.apply_symm_apply, hzdef, ← map_mul]
            group
          rw [hval']
          exact (ggQ2d6l_refl_iff N.model s).mp hsrefl
      have hg1 : g = 1 := by
        have h := congrArg (fun e => (Φ e : MulAut ↥Bs)) hg'
        simpa using h
      have hsz : s = z := by rw [hzdef, hg1]; group
      rw [hsz]; exact hzZ
  have hdecomp : ∀ s ∈ AL, ∃ g ∈ AJ, ∃ z ∈ Z, s = g * z := by
    intro s hs
    obtain ⟨g, hgAJ, hgconj⟩ := hC s hs
    refine ⟨g, hgAJ, g⁻¹ * s, ?_, ?_⟩
    · rw [Subgroup.mem_inf]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_,
        AL.mul_mem (AL.inv_mem (hle hgAJ)) hs⟩
      have h := hgconj r hr
      show r * (g⁻¹ * s) = (g⁻¹ * s) * r
      calc r * (g⁻¹ * s) = g⁻¹ * (g * r * g⁻¹) * s := by group
        _ = g⁻¹ * (s * r * s⁻¹) * s := by rw [← h]
        _ = (g⁻¹ * s) * r := by group
    · group
  let F : AJ × Z → AL := fun p =>
    ⟨(p.1 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs),
      AL.mul_mem (hle p.1.2) (Subgroup.mem_inf.mp p.2.2).2⟩
  have hF : Function.Bijective F := by
    constructor
    · intro p q hpq
      have hpq' : (p.1 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs) =
          (q.1 : MulAut ↥Bs) * (q.2 : MulAut ↥Bs) := Subtype.ext_iff.mp hpq
      have heq : (q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs) =
          (q.2 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs)⁻¹ := by
        calc (q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs)
            = (q.1 : MulAut ↥Bs)⁻¹ * ((p.1 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs)) *
                (p.2 : MulAut ↥Bs)⁻¹ := by group
          _ = (q.1 : MulAut ↥Bs)⁻¹ * ((q.1 : MulAut ↥Bs) * (q.2 : MulAut ↥Bs)) *
                (p.2 : MulAut ↥Bs)⁻¹ := by rw [hpq']
          _ = (q.2 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs)⁻¹ := by group
      have hmemAJ : (q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs) ∈ AJ :=
        AJ.mul_mem (AJ.inv_mem q.1.2) p.1.2
      have hmemZ : (q.2 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs)⁻¹ ∈ Z :=
        Z.mul_mem q.2.2 (Z.inv_mem p.2.2)
      have h1 : (q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs) ∈ AJ ⊓ Z := by
        refine ⟨hmemAJ, ?_⟩
        rw [heq]; exact hmemZ
      rw [hzAJZ] at h1
      have h1' : (q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs) = 1 := by simpa using h1
      have hp1 : p.1 = q.1 := by
        apply Subtype.ext
        calc (p.1 : MulAut ↥Bs) =
            (q.1 : MulAut ↥Bs) * ((q.1 : MulAut ↥Bs)⁻¹ * (p.1 : MulAut ↥Bs)) := by group
          _ = (q.1 : MulAut ↥Bs) * 1 := by rw [h1']
          _ = (q.1 : MulAut ↥Bs) := mul_one _
      have hp2 : p.2 = q.2 := by
        have h2 : (q.2 : MulAut ↥Bs) * (p.2 : MulAut ↥Bs)⁻¹ = 1 := by rw [← heq, h1']
        exact Subtype.ext (mul_inv_eq_one.mp h2).symm
      exact Prod.ext hp1 hp2
    · intro s
      obtain ⟨g, hgAJ, z, hzZ, hsz⟩ := hdecomp s s.2
      refine ⟨(⟨g, hgAJ⟩, ⟨z, hzZ⟩), ?_⟩
      apply Subtype.ext
      show g * z = (s : MulAut ↥Bs)
      rw [hsz]
  have hcardZ : Nat.card ↥AJ * Nat.card ↥Z = Nat.card ↥AL := by
    rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective F hF)]
  have hZle2 : Nat.card ↥Z ≤ 2 := by
    have h := hcard
    rw [← hcardZ, hAJcard] at h
    omega
  have : Fintype ↥Z := Fintype.ofFinite ↥Z
  have hZgt1 : 1 < Nat.card ↥Z := by
    have hnotAJ : ∃ s ∈ AL, s ∉ AJ := by
      by_contra h
      push Not at h
      exact hnot h
    obtain ⟨s, hsAL, hsAJ⟩ := hnotAJ
    obtain ⟨g, hgAJ, z, hzZ, hsz⟩ := hdecomp s hsAL
    have hz_ne : z ≠ 1 := by
      intro hz1
      apply hsAJ
      rw [hsz, hz1, mul_one]
      exact hgAJ
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨1, ⟨z, hzZ⟩,
      fun h => hz_ne (congrArg Subtype.val h).symm⟩
  have hZcard : Nat.card ↥Z = 2 := by omega
  have hgen : ∀ k (hk : k ≠ M'.a), M'.simple k ∈ AL := by
    intro k hk
    have hm : M'.simple k ∈ M'.simple '' {k | k ≠ M'.a} := ⟨k, hk, rfl⟩
    have h := Subgroup.subset_closure hm
    rw [← M'.automizer_L] at h
    exact h
  let T1 : Set M'.ι := {k | k ≠ M'.a ∧ M'.simple k ∈ AJ}
  let T2 : Set M'.ι := {k | k ≠ M'.a ∧ M'.simple k ∉ AJ}
  have hcover : ∀ k, k ≠ M'.a → T1 k ∨ T2 k := by
    intro k hk
    have hrefl := ggQ2d6l_model_simple_refl M' k
    rcases hstep4 (M'.simple k) (hgen k hk) hrefl with h | h
    · exact Or.inl ⟨hk, h⟩
    · refine Or.inr ⟨hk, fun hAJ => ?_⟩
      have hmem : M'.simple k ∈ AJ ⊓ Z := ⟨hAJ, h⟩
      rw [hzAJZ] at hmem
      exact ggQ2d6l_refl_ne_one hrefl (by simpa using hmem)
  have hT2ne : T2.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hle' : AL ≤ AJ := by
      change ggAutomizer L Bs ≤ AJ
      rw [M'.automizer_L, Subgroup.closure_le]
      rintro x ⟨k, hk, rfl⟩
      by_contra hx
      have hmem : k ∈ T2 := ⟨hk, hx⟩
      rw [h] at hmem
      exact hmem
    exact hnot hle'
  have hT1ne : T1.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hle' : AL ≤ Z := by
      change ggAutomizer L Bs ≤ Z
      rw [M'.automizer_L, Subgroup.closure_le]
      rintro x ⟨k, hk, rfl⟩
      have hrefl := ggQ2d6l_model_simple_refl M' k
      rcases hstep4 (M'.simple k) (hgen k hk) hrefl with h1 | h1
      · exfalso
        have hmem : k ∈ T1 := ⟨hk, h1⟩
        rw [h] at hmem
        exact hmem
      · exact h1
    have hcardle : Nat.card ↥AL ≤ 2 := by
      calc Nat.card ↥AL ≤ Nat.card ↥Z :=
            Nat.card_le_card_of_injective (fun x : ↥AL => (⟨(x : MulAut ↥Bs), hle' x.2⟩ : ↥Z))
              (fun a b hab => Subtype.ext (by
                have hh := congrArg (fun y : ↥Z => (y : MulAut ↥Bs)) hab
                simpa using hh))
        _ = 2 := hZcard
    have hAJle : Nat.card ↥AJ ≤ Nat.card ↥AL :=
      Nat.card_le_card_of_injective (fun x : ↥AJ => (⟨(x : MulAut ↥Bs), hle x.2⟩ : ↥AL))
        (fun a b hab => Subtype.ext (by
          have hh := congrArg (fun y : ↥AL => (y : MulAut ↥Bs)) hab
          simpa using hh))
    omega
  have hι3 : 3 ≤ Fintype.card M'.ι := by
    obtain ⟨k, hkT1⟩ := hT1ne
    obtain ⟨l, hlT2⟩ := hT2ne
    have hkl : k ≠ l := by
      intro h
      rw [h] at hkT1
      exact hlT2.2 hkT1.2
    have hcard3 : ({M'.a, k, l} : Finset M'.ι).card = 3 := by
      have h1 : M'.a ∉ ({k, l} : Finset M'.ι) := by
        simp [Ne.symm hkT1.1, Ne.symm hlT2.1]
      have h2 : k ∉ ({l} : Finset M'.ι) := by simp [hkl]
      rw [show ({M'.a, k, l} : Finset M'.ι) = insert M'.a (insert k {l}) by rfl,
        Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_singleton]
    have hcardle := Finset.card_le_card (Finset.subset_univ ({M'.a, k, l} : Finset M'.ι))
    rw [Finset.card_univ, hcard3] at hcardle
    omega
  have hadj : ∃ j, T2 j ∧ ∃ k, T1 k ∧ M'.cartan j k ≠ 0 := by
    obtain ⟨c, hc, hcuniq⟩ := M'.a_leaf
    by_contra hno
    push Not at hno
    have hnoZT1T2 : ∀ j, T1 j → ∀ k, T2 k → (M'.cartan j k : ZMod 3) = 0 := by
      intro j hj k hk
      by_cases hjk : j = k
      · subst hjk
        exact absurd hj.2 hk.2
      · rw [M'.isCartan.eq_zero_symm hjk (hno k hk j hj)]
        simp
    have hnoZT2T1 : ∀ j, T2 j → ∀ k, T1 k → (M'.cartan j k : ZMod 3) = 0 := by
      intro j hj k hk
      rw [hno j hj k hk]
      simp
    have hneighbour : ∀ j, j ≠ M'.a → M'.cartan j M'.a ≠ 0 → j = c := by
      intro j hja hjc
      exact hcuniq j ⟨hja, fun h0 => hjc (M'.isCartan.eq_zero_symm hja h0)⟩
    rcases hcover c hc.1 with hc1 | hc2
    · exfalso
      have hSne : (T1 ∪ {M'.a}).Nonempty := ⟨c, Or.inl hc1⟩
      have hScl : ∀ k ∈ T1 ∪ {M'.a}, ∀ j,
          (M'.cartan j k : ZMod 3) ≠ 0 → j ∈ T1 ∪ {M'.a} := by
        intro k hk j hjk
        rw [Set.mem_union] at hk
        rcases hk with hkT1 | hka
        · by_cases hja : j = M'.a
          · subst hja; exact Or.inr rfl
          · rcases hcover j hja with hj1 | hj2
            · exact Or.inl hj1
            · exact absurd (hnoZT2T1 j hj2 k hkT1) hjk
        · have hka' : k = M'.a := hka
          subst hka'
          by_cases hja : j = M'.a
          · subst hja; exact Or.inr rfl
          · exact Or.inl (by
              have hj' : j = c := hneighbour j hja (fun h0 => hjk (by rw [h0]; simp))
              rw [hj']; exact hc1)
      have hSuniv := ggCartan_closed_eq_univ (p := 3) (by norm_num) M'.isWeyl M'.isCartan hι3
        hSne hScl
      obtain ⟨l, hlT2⟩ := hT2ne
      have hlT2' : T2 l := hlT2
      have hl : l ∈ T1 ∪ {M'.a} := by rw [hSuniv]; trivial
      rw [Set.mem_union] at hl
      rcases hl with hl1 | hla
      · have hl1' : T1 l := hl1
        exact hlT2'.2 hl1'.2
      · exact hlT2'.1 hla
    · exfalso
      have hSne : (T2 ∪ {M'.a}).Nonempty := ⟨c, Or.inl hc2⟩
      have hScl : ∀ k ∈ T2 ∪ {M'.a}, ∀ j,
          (M'.cartan j k : ZMod 3) ≠ 0 → j ∈ T2 ∪ {M'.a} := by
        intro k hk j hjk
        rw [Set.mem_union] at hk
        rcases hk with hkT2 | hka
        · by_cases hja : j = M'.a
          · subst hja; exact Or.inr rfl
          · rcases hcover j hja with hj1 | hj2
            · exact absurd (hnoZT1T2 j hj1 k hkT2) hjk
            · exact Or.inl hj2
        · have hka' : k = M'.a := hka
          subst hka'
          by_cases hja : j = M'.a
          · subst hja; exact Or.inr rfl
          · exact Or.inl (by
              have hj' : j = c := hneighbour j hja (fun h0 => hjk (by rw [h0]; simp))
              rw [hj']; exact hc2)
      have hSuniv := ggCartan_closed_eq_univ (p := 3) (by norm_num) M'.isWeyl M'.isCartan hι3
        hSne hScl
      obtain ⟨l, hlT1⟩ := hT1ne
      have hlT1' : T1 l := hlT1
      have hl : l ∈ T2 ∪ {M'.a} := by rw [hSuniv]; trivial
      rw [Set.mem_union] at hl
      rcases hl with hl2 | hla
      · have hl2' : T2 l := hl2
        exact hl2'.2 hlT1'.2
      · exact hlT1'.1 hla
  obtain ⟨j, hjT2, k, hkT1, hjkC⟩ := hadj
  have hjZ : M'.simple j ∈ Z := by
    rcases hstep4 (M'.simple j) (hgen j hjT2.1) (ggQ2d6l_model_simple_refl M' j) with h | h
    · exact absurd h hjT2.2
    · exact h
  have hcomm : M'.simple j * M'.simple k = M'.simple k * M'.simple j :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hjZ).1) (M'.simple k) hkT1.2).symm
  have hne : M'.simple j ≠ M'.simple k := by
    intro h
    exact hjT2.2 (h.symm ▸ hkT1.2)
  have hjk_ne : j ≠ k := by
    intro h
    exact hjT2.2 (h.symm ▸ hkT1.2)
  exact (ggQ2d6l_adjacent_noncomm hS M' j k hjT2.1 hkT1.1 hjk_ne hjkC hne) hcomm

end CFSG.StandardType

end
