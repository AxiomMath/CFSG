module

public import CFSG.Quasithin.Background.SmithC27RTypeDefs
public import CFSG.Quasithin.Background.C124YZActSix
public import CFSG.Quasithin.Background.B5FinS8Schur
public import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

theorem exists_perm_of_normalizes_eight (φ : MulAut (C124.YZ.DM 8))
    (hφ : ∀ σ ∈ alternatingGroup (Fin 8), ∃ τ ∈ alternatingGroup (Fin 8),
      ∀ y, C124.YZ.dAct 8 σ (φ y) = φ (C124.YZ.dAct 8 τ y)) :
    ∃ ρ : Perm (Fin 8), ∀ y, φ y = C124.YZ.dAct 8 ρ y := by
  classical
  choose! f hfA hf using hφ
  have hinj : Function.Injective (C124.YZ.dAct 8) := C124.YZ.dAct_injective (by norm_num)
  have hrel : ∀ σ ∈ alternatingGroup (Fin 8),
      C124.YZ.dAct 8 (f σ) = φ⁻¹ * C124.YZ.dAct 8 σ * φ := by
    intro σ hσ
    ext y
    show C124.YZ.dAct 8 (f σ) y = φ.symm (C124.YZ.dAct 8 σ (φ y))
    rw [hf σ hσ y, MulEquiv.symm_apply_apply]
  let F : ↥(alternatingGroup (Fin 8)) →* ↥(alternatingGroup (Fin 8)) :=
    { toFun := fun σ => ⟨f σ, hfA σ σ.2⟩
      map_one' := by
        apply Subtype.ext
        apply hinj
        show C124.YZ.dAct 8 (f 1) = C124.YZ.dAct 8 1
        rw [hrel 1 (Subgroup.one_mem _), map_one, mul_one, inv_mul_cancel]
      map_mul' := fun σ τ => by
        apply Subtype.ext
        apply hinj
        show C124.YZ.dAct 8 (f ((σ : Perm (Fin 8)) * τ)) =
          C124.YZ.dAct 8 (f σ * f τ)
        rw [hrel _ (Subgroup.mul_mem _ σ.2 τ.2), map_mul, map_mul, hrel _ σ.2, hrel _ τ.2]
        group }
  have hFinj : Function.Injective F := by
    intro σ τ hστ
    have h1 : f σ = f τ := congrArg Subtype.val hστ
    have h2 : C124.YZ.dAct 8 (σ : Perm (Fin 8)) = C124.YZ.dAct 8 τ := by
      have h3 := congrArg (C124.YZ.dAct 8) h1
      rw [hrel _ σ.2, hrel _ τ.2] at h3
      simpa using h3
    exact Subtype.ext (hinj h2)
  have hFbij : Function.Bijective F := ⟨hFinj, Finite.injective_iff_surjective.1 hFinj⟩
  obtain ⟨g, hg⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)).2 (MulEquiv.ofBijective F hFbij)
  have hfg : ∀ σ ∈ alternatingGroup (Fin 8), f σ = g * σ * g⁻¹ := by
    intro σ hσ
    have h1 := congrArg (fun α : MulAut ↥(alternatingGroup (Fin 8)) =>
      ((α ⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8))) hg
    simp only [MulAut.conjNormal_apply] at h1
    exact h1.symm
  let ψ : C124.YZ.DM 8 →* C124.YZ.DM 8 :=
    φ.toMonoidHom.comp (C124.YZ.dAct 8 g).toMonoidHom
  have hψinj : Function.Injective ψ := fun a b hab =>
    (C124.YZ.dAct 8 g).injective (φ.injective hab)
  have hdm : ∀ (a b : Perm (Fin 8)) (q : C124.YZ.DM 8),
      C124.YZ.dAct 8 a (C124.YZ.dAct 8 b q) = C124.YZ.dAct 8 (a * b) q := by
    intro a b q
    rw [map_mul, MulAut.mul_apply]
  have hψc : ∀ σ ∈ alternatingGroup (Fin 8), ∀ q : C124.YZ.DM 8,
      ψ (C124.YZ.dAct 8 σ q) = C124.YZ.dAct 8 σ (ψ q) := by
    intro σ hσ q
    show φ (C124.YZ.dAct 8 g (C124.YZ.dAct 8 σ q)) = C124.YZ.dAct 8 σ (φ (C124.YZ.dAct 8 g q))
    rw [hf σ hσ, hfg σ hσ, hdm, hdm]
    congr 2
    group
  have hψ : ∀ q : C124.YZ.DM 8, ψ q = q := B5FinS8.k8 ψ hψinj hψc
  refine ⟨g⁻¹, fun y => ?_⟩
  have h1 := hψ (C124.YZ.dAct 8 g⁻¹ y)
  have h2 : ψ (C124.YZ.dAct 8 g⁻¹ y) = φ y := by
    show φ (C124.YZ.dAct 8 g (C124.YZ.dAct 8 g⁻¹ y)) = φ y
    rw [hdm, mul_inv_cancel, map_one]
    rfl
  rw [← h2]
  exact h1

variable {G : Type} [Group G] [Finite G] {R K V : Subgroup G}

structure CaseIICtx (R K V : Subgroup G) (n : ℕ) where
  hV : IsElemAbelian 2 V
  ι : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin n)
  mem_K : ∀ x : ↥(autOn (K ⊔ R) V),
    (x : MulAut ↥V) ∈ autOn K V ↔ ι x ∈ alternatingGroup (Fin n)
  β : ↥(commV (autI hV K)) →* C124.YZ.DM n
  β_surj : Function.Surjective β
  β_ker : ∀ u, β u = 1 ↔ (u : IntMod V hV) ∈ fixV (autI hV K)
  β_equiv : ∀ (g : ↥(autOn (K ⊔ R) V)) (u : ↥(commV (autI hV K)))
    (hu : ((g : MulAut ↥V) : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV K)),
    β ⟨((g : MulAut ↥V) : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
      C124.YZ.dAct n (ι g) (β u)

theorem ffJP_le_self' {W : Type*} [CommGroup W] (P : Set (Subgroup (MulAut W)))
    (Y : Subgroup (MulAut W)) : ffJP P Y ≤ Y :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem nonempty_caseIICtx (hs : StarHyp R K V) (hV : IsElemAbelian 2 V) {n : ℕ}
    (hn : n = 6 ∨ n = 8) (hKJ : autI hV K ≤ jPStar hV R K)
    (π : Equiv.Perm (Fin n) →* ↥(jPStar hV R K))
    (hπ : (FFModel.symDn n).RealizesVia (jPStar hV R K) (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) π)
    (hπK : ∀ σ : Equiv.Perm (Fin n),
      ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
        σ ∈ alternatingGroup (Fin n)) :
    Nonempty (CaseIICtx R K V n) := by
  classical
  have hn5 : 5 ≤ n := by omega
  obtain ⟨hπs, -, -, -, -, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hπ
  have hJX : jPStar hV R K ≤ autI hV (K ⊔ R) := ffJP_le_self' _ _
  let β : ↥(commV (autI hV K)) →* C124.YZ.DM n := β₀
  have hβπ : ∀ (σ : Perm (Fin n)) (u : ↥(commV (autI hV K)))
      (hu : ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) (u : IntMod V hV) ∈
        commV (autI hV K)),
      β ⟨((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        C124.YZ.dAct n σ (β u) := by
    intro σ u hu
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hact : (FFModel.symDn n).act σ (m₀ : (FFModel.symDn n).Amb) ∈ (FFModel.symDn n).sec :=
      G6.permAct_mem_coreMod _ m₀.2
    have h1 := hβ₀e σ u m₀ hu hact hm₀.symm
    have h1' : β ⟨((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        (QuotientGroup.mk (⟨(FFModel.symDn n).act σ (m₀ : (FFModel.symDn n).Amb), hact⟩ :
          ↥(G6.coreMod n)) : C124.YZ.DM n) := h1
    have hm₀' : β u = (QuotientGroup.mk (m₀ : ↥(G6.coreMod n)) : C124.YZ.DM n) := hm₀.symm
    rw [h1', hm₀']
    rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply C124.YZ.dAct_faithful hn5 σ
    intro q
    obtain ⟨u, rfl⟩ := hβ₀s q
    have hu : ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) (u : IntMod V hV) ∈
        commV (autI hV K) := by
      rw [hσ]
      exact u.2
    have h := hβπ σ u hu
    rw [← h]
    congr 1
    apply Subtype.ext
    show ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) (u : IntMod V hV) = u
    rw [hσ]
    rfl
  let πA : ↥(alternatingGroup (Fin n)) →* ↥(autI hV K) :=
    { toFun := fun γ => ⟨((π γ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)), (hπK γ).2 γ.2⟩
      map_one' := by
        apply Subtype.ext
        show ((π 1 : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((π ((a : Perm (Fin n)) * b) : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) =
          ((π a : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) * (π b : ↥(jPStar hV R K))
        rw [map_mul]
        rfl }
  have hπAs : Function.Surjective πA := by
    rintro ⟨k, hk⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin n), π σ = ⟨k, hKJ hk⟩ := hπs _
    have hσk : ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) = k := congrArg Subtype.val hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := (hπK σ).1 (by rw [hσk]; exact hk)
    exact ⟨⟨σ, hσA⟩, Subtype.ext hσk⟩
  have hπAi : Function.Injective πA := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (hπinj (Subtype.ext h1))
  have hKX : autI hV K ≤ autI hV (K ⊔ R) := autI_mono hV le_sup_left
  have hXsN : autI hV (K ⊔ R) ≤
      Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) :=
    C124.YZ.autI_normalizes hV hs.le_normalizer
  have hnorm : ∀ φ : MulAut (C124.YZ.DM n), (∀ σ ∈ alternatingGroup (Fin n),
      ∃ τ ∈ alternatingGroup (Fin n), ∀ y, C124.YZ.dAct n σ (φ y) = φ (C124.YZ.dAct n τ y)) →
      ∃ ρ : Perm (Fin n), ∀ y, φ y = C124.YZ.dAct n ρ y := by
    rcases hn with rfl | rfl
    · exact C124.YZ.exists_perm_of_normalizes_six
    · exact exists_perm_of_normalizes_eight
  obtain ⟨ι₀, hι₀, hι₀π, hβe⟩ := C124.YZ.exists_embedding_of_normalizer hKX
    (commV (autI hV K)) (fun g hg u hu => C124.YZ.apply_mem_commV (hXsN hg) hu)
    (act := C124.YZ.dAct n) (fun ρ hρ => C124.YZ.dAct_faithful hn5 ρ hρ) hnorm πA hπAs β hβ₀s
    (fun γ u hu => hβπ γ u hu)
    (fun g hg u hu h1 => by
      have h3 := (hβ₀k u).1 h1
      have h4 : g (u : IntMod V hV) ∈ fixV (autI hV K) ⊓ commV (autI hV K) :=
        ⟨C124.YZ.apply_mem_fixV (hXsN hg) h3.1, hu⟩
      exact (hβ₀k _).2 h4)
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 (hXsN hg) l).1 hl)
    (fun g hg hc => C124.YZ.eq_one_of_centralizes (by omega) hs.genFitting_eq hπAs hπAi hg hc)
  have hmemK : ∀ x : ↥(autI hV (K ⊔ R)),
      (x : MulAut (IntMod V hV)) ∈ autI hV K ↔ ι₀ x ∈ alternatingGroup (Fin n) := by
    intro x
    constructor
    · intro hx
      obtain ⟨γ, hγ⟩ := hπAs ⟨x, hx⟩
      have h1 := hι₀π γ
      have h2 : Subgroup.inclusion hKX (πA γ) = x := by
        have h0 := congrArg Subtype.val hγ
        exact Subtype.ext h0
      rw [h2] at h1
      rw [h1]
      exact γ.2
    · intro hx
      have h1 := hι₀π ⟨ι₀ x, hx⟩
      have h2 := hι₀ h1
      rw [← h2]
      exact (πA ⟨ι₀ x, hx⟩).2
  have hι₀s : Function.Surjective ι₀ := by
    have hodd : ∃ x : ↥(autI hV (K ⊔ R)), ι₀ x ∉ alternatingGroup (Fin n) := by
      refine ⟨⟨_, hJX (π (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)).2⟩, fun h => ?_⟩
      have h1 := (hmemK _).2 h
      have h2 := (hπK (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)).1 h1
      rw [mem_alternatingGroup, sign_swap (by simp [Fin.ext_iff])] at h2
      exact absurd h2 (by decide)
    obtain ⟨x₀, hx₀⟩ := hodd
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · refine ⟨Subgroup.inclusion hKX (πA ⟨σ, hσ⟩), ?_⟩
      exact hι₀π ⟨σ, hσ⟩
    · have hsg : σ * (ι₀ x₀)⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup] at hσ hx₀ ⊢
        rw [map_mul, map_inv, Int.units_ne_iff_eq_neg.1 hσ, Int.units_ne_iff_eq_neg.1 hx₀]
        decide
      refine ⟨Subgroup.inclusion hKX (πA ⟨_, hsg⟩) * x₀, ?_⟩
      rw [map_mul, hι₀π ⟨_, hsg⟩]
      group
  exact ⟨{ hV := hV
           ι := MulEquiv.ofBijective ι₀ ⟨hι₀, hι₀s⟩
           mem_K := hmemK
           β := β
           β_surj := hβ₀s
           β_ker := fun u => by
             rw [hβ₀k u]
             exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩
           β_equiv := hβe }⟩

namespace CaseIICtx

variable {n : ℕ} (C : CaseIICtx R K V n)

@[expose] noncomputable def bar (Y : Subgroup G) : Subgroup (Equiv.Perm (Fin n)) :=
  ((autOn Y V).subgroupOf (autOn (K ⊔ R) V)).map C.ι.toMonoidHom

omit [Finite G] in
theorem mem_bar_iff {Y : Subgroup G} {σ : Equiv.Perm (Fin n)} :
    σ ∈ C.bar Y ↔ ((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∈ autOn Y V := by
  unfold bar
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem bar_K : C.bar K = alternatingGroup (Fin n) := by
  ext σ
  rw [mem_bar_iff, C.mem_K, MulEquiv.apply_symm_apply]

end CaseIICtx

end CFSG.Quasithin.SmithC27
