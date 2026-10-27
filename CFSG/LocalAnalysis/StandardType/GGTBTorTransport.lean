module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusTorWit.transport {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) :
    GGTorusTorWit m N L2 (A.map (MulAut.congr e).toMonoidHom) where
  T := w.T.map (MulAut.congr e).toMonoidHom
  α := fun k φ => w.α k ((MulAut.congr e).symm φ)
  cor := fun k => e.toMonoidHom.comp (w.cor k)
  n := fun k => e (w.n k)
  hn := fun k => by
    rw [← CFSG.StandardType.congr_conj]
    exact CFSG.StandardType.mem_normalizer_map_congr e (w.hn k)
  Tsc := w.Tsc.map e.toMonoidHom

@[simp] theorem GGTorusTorWit.transport_T {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) :
    (w.transport e).T = w.T.map (MulAut.congr e).toMonoidHom := rfl

@[simp] theorem GGTorusTorWit.transport_α {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) (k : Fin N)
    (φ : MulAut L2) :
    (w.transport e).α k φ = w.α k ((MulAut.congr e).symm φ) := rfl

@[simp] theorem GGTorusTorWit.transport_cor {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) (k : Fin N) :
    (w.transport e).cor k = e.toMonoidHom.comp (w.cor k) := rfl

@[simp] theorem GGTorusTorWit.transport_n {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) (k : Fin N) :
    (w.transport e).n k = e (w.n k) := rfl

@[simp] theorem GGTorusTorWit.transport_Tsc {m N : ℕ} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2) :
    (w.transport e).Tsc = w.Tsc.map e.toMonoidHom := rfl

theorem ggConjAut_map_congr {M M' : Type} [Group M] [Group M']
    {A : Subgroup M} {A' : Subgroup M'} (f : M →* M') (hf : Function.Injective f)
    (hA : A.map f = A')
    {g : M} (hg : g ∈ Subgroup.normalizer (A : Set M))
    {g' : M'} (hg' : g' ∈ Subgroup.normalizer (A' : Set M')) (hgg' : f g = g') :
    MulAut.congr ((A.equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hA)) (ggConjAut A hg) = ggConjAut A' hg' := by
  subst hgg'
  let eA : ↥A ≃* ↥A' := (A.equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr hA)
  have heA : ∀ a : ↥A, (eA a : M') = f (a : M) := by
    intro a
    change (((A.equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hA)) a : M') = f (a : M)
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
  have heA_symm : ∀ a' : ↥A', f ((eA.symm a' : ↥A) : M) = (a' : M') := by
    intro a'
    rw [← heA (eA.symm a'), MulEquiv.apply_symm_apply]
  ext a'
  change (eA (ggConjAut A hg (eA.symm a')) : M') =
    (ggConjAut A' hg' a' : M')
  rw [heA (ggConjAut A hg (eA.symm a')), ggConjAut_apply]
  simp only [map_mul, map_inv, heA_symm, ggConjAut_apply]

theorem GGTorusTorWit.holds_transport {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (w : GGTorusTorWit m N L A) (e : L ≃* L2)
    (hw : w.Holds C M) : (w.transport e).Holds C M := by
  obtain ⟨hTcomm, hAT, hconjT, hαadd, hcorinj, hcorcomm, hfixcor, hpair,
    hnconj, hnel, hsep, hαA, hinnA, hoddTsc, ⟨hCscA, hCscB, hCscC⟩,
    haut, hweyl⟩ := hw
  obtain ⟨eM, hsimple⟩ := hweyl
  let Inn : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range
  let Inn2 : Subgroup (MulAut L2) := (MulAut.conj : L2 →* MulAut L2).range
  let A2 : Subgroup (MulAut L2) := A.map (MulAut.congr e).toMonoidHom
  let eA : ↥A ≃* ↥A2 := (A.equivMapOfInjective (MulAut.congr e).toMonoidHom (fun x y h => (MulAut.congr e).injective h)).trans
    (MulEquiv.subgroupCongr rfl)
  have hT : (w.transport e).T = w.T.map (MulAut.congr e).toMonoidHom := GGTorusTorWit.transport_T w e
  have hTsc : (w.transport e).Tsc = w.Tsc.map e.toMonoidHom :=
    GGTorusTorWit.transport_Tsc w e
  have hcongr_apply : ∀ (τ : MulAut L) (x : L),
      MulAut.congr e τ (e x) = e (τ x) := by
    intro τ x
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hInn : Inn2 = Inn.map (MulAut.congr e).toMonoidHom := by
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨MulAut.conj (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
      change MulAut.congr e (MulAut.conj (e.symm x)) = MulAut.conj x
      rw [CFSG.StandardType.congr_conj, MulEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
      exact ⟨e l, (CFSG.StandardType.congr_conj e l).symm⟩
  have hAuto : ggAutomizer Inn2 A2 =
      (ggAutomizer Inn A).map (MulAut.congr eA).toMonoidHom := by
    rw [hInn]
    simpa [A2, eA, Subgroup.equivMapOfInjective_coe_mulEquiv] using
      (CFSG.StandardType.F4AutWeyl.ggAutomizer_map_eq (f := (MulAut.congr e).toMonoidHom) (fun x y h => (MulAut.congr e).injective h)
        Inn A (rfl : A.map (MulAut.congr e).toMonoidHom = A2))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro x hx y hy
    rw [hT] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hTcomm x₀ hx₀ y₀ hy₀]
  ·
    intro a ha
    change a ∈ A.map (MulAut.congr e).toMonoidHom at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨a₀, hAT ha₀, rfl⟩
  ·
    intro k ζ
    rw [GGTorusTorWit.transport_cor, hT, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← CFSG.StandardType.congr_conj]
    exact ⟨MulAut.conj (w.cor k ζ), hconjT k ζ, rfl⟩
  ·
    intro j x hx y hy
    rw [hT] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul]
    simp only [GGTorusTorWit.transport_α, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    exact hαadd j x₀ hx₀ y₀ hy₀
  ·
    intro k ζ ξ h
    simp only [GGTorusTorWit.transport_cor, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] at h
    exact hcorinj k (e.injective h)
  ·
    intro j k ζ ξ
    simp only [GGTorusTorWit.transport_cor, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    exact (hcorcomm j k ζ ξ).map e.toMonoidHom
  ·
    intro τ hτ k ζ
    rw [hT] at hτ
    obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
    simp only [GGTorusTorWit.transport_cor, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [hcongr_apply τ₀ (w.cor k ζ), hfixcor τ₀ hτ₀ k ζ]
  ·
    intro i j ζ
    simp only [GGTorusTorWit.transport_cor, GGTorusTorWit.transport_α,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← CFSG.StandardType.congr_conj, MulEquiv.symm_apply_apply]
    exact hpair i j ζ
  ·
    intro k τ hτ
    rw [hT] at hτ
    obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
    simp only [GGTorusTorWit.transport_n, GGTorusTorWit.transport_cor,
      GGTorusTorWit.transport_α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    simp only [← CFSG.StandardType.congr_conj]
    rw [← map_inv (MulAut.congr e), ← map_inv (MulAut.congr e),
      ← map_mul (MulAut.congr e), ← map_mul (MulAut.congr e),
      hnconj k τ₀ hτ₀, map_mul (MulAut.congr e), map_inv (MulAut.congr e)]
  ·
    intro k τ hτ
    rw [hT] at hτ
    obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
    simp only [GGTorusTorWit.transport_n, GGTorusTorWit.transport_cor,
      GGTorusTorWit.transport_α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rw [hcongr_apply τ₀ (w.n k)]
    rw [← map_inv, ← map_mul, hnel k τ₀ hτ₀, map_inv]
  ·
    intro τ hτ hτ1
    rw [hT] at hτ
    obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
    have hτ' : τ₀ = 1 := hsep τ₀ hτ₀ (fun k => by
      have h := hτ1 k
      simpa only [GGTorusTorWit.transport_α, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using h)
    rw [hτ', map_one]
  ·
    intro k
    obtain ⟨a, ha, hne⟩ := hαA k
    refine ⟨MulAut.congr e a, ⟨a, ha, rfl⟩, ?_⟩
    intro h
    apply hne
    simpa only [GGTorusTorWit.transport_α, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using h
  ·
    intro a ha haconj
    change a ∈ A.map (MulAut.congr e).toMonoidHom at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have haconj' : MulAut.congr e a₀ ∈
        (MulAut.conj : L2 →* MulAut L2).range := haconj
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp haconj'
    have ha_conj : a₀ ∈ (MulAut.conj : L →* MulAut L).range := by
      refine MonoidHom.mem_range.mpr ⟨e.symm x, ?_⟩
      apply (MulAut.congr e).injective
      rw [CFSG.StandardType.congr_conj, MulEquiv.apply_symm_apply, hx]
    obtain ⟨t, ht, hat⟩ := hinnA a₀ ha₀ ha_conj
    refine ⟨e t, ?_, ?_⟩
    · have hmap : (⨆ k, (w.cor k).range).map e.toMonoidHom =
          ⨆ k, ((w.transport e).cor k).range := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun k => (MonoidHom.range_comp e.toMonoidHom (w.cor k)).symm
      rw [← hmap]
      exact ⟨t, ht, rfl⟩
    · rw [← CFSG.StandardType.congr_conj, hat]
      simp only [MulEquiv.coe_toMonoidHom]
  ·
    intro z hz hodd
    have hz' : e.symm z ∈ Subgroup.center L := by
      rw [← Subgroup.map_center_eq (f := e)] at hz
      exact Subgroup.mem_map_equiv.mp hz
    have hord : orderOf (e.symm z) = orderOf z := by
      rw [← orderOf_injective (f := e.toMonoidHom)
        (by intro x y h; exact e.injective h) (e.symm z)]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have hodd' : Odd (orderOf (e.symm z)) := hord ▸ hodd
    have hzTsc := hoddTsc (e.symm z) hz' hodd'
    rw [hTsc]
    exact ⟨e.symm z, hzTsc, by simp⟩
  ·
    intro g hg
    let g' : L := e.symm g
    have hg' : ∀ a ∈ A, MulAut.conj g' * a = a * MulAut.conj g' := by
      intro a ha
      have ha2 : MulAut.congr e a ∈ A2 := by
        change MulAut.congr e a ∈ A.map (MulAut.congr e).toMonoidHom
        exact ⟨a, ha, rfl⟩
      have h := hg (MulAut.congr e a) ha2
      have h' : MulAut.conj (e g') * MulAut.congr e a =
          MulAut.congr e a * MulAut.conj (e g') := by
        simpa [g'] using h
      apply (MulAut.congr e).injective
      simpa [map_mul, ← CFSG.StandardType.congr_conj] using h' 
    have hmem := hCscA g' hg'
    have hcenter : Subgroup.map e.toMonoidHom (Subgroup.center L) =
        Subgroup.center L2 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change y ∈ Subgroup.center L at hy
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro z
        obtain ⟨w, rfl⟩ := e.surjective z
        simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg e (hy w)
      · intro hx
        change x ∈ Subgroup.center L2 at hx
        refine ⟨e.symm x, ?_, by simp⟩
        change e.symm x ∈ Subgroup.center L
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro y
        apply e.injective
        simpa only [map_mul, MulEquiv.apply_symm_apply] using hx (e y)
    have hmap : (w.Tsc ⊔ Subgroup.center L).map e.toMonoidHom =
        (w.transport e).Tsc ⊔ Subgroup.center L2 := by
      rw [Subgroup.map_sup, hcenter, hTsc]
    have : g ∈ (w.Tsc ⊔ Subgroup.center L).map e.toMonoidHom :=
      ⟨g', hmem, by simp [g']⟩
    rwa [hmap] at this
  ·
    intro τ hτ t ht
    rw [hT] at hτ
    rw [hTsc] at ht
    obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hcongr_apply τ₀ t₀, hCscB τ₀ hτ₀ t₀ ht₀]
  ·
    intro t ht htm
    rw [hTsc] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
    have htm' : t₀ ^ m = 1 := by
      apply e.injective
      simpa [map_pow] using htm
    have htcor := hCscC t₀ ht₀ htm'
    have hmap : (⨆ k, (w.cor k).range).map e.toMonoidHom =
        ⨆ k, ((w.transport e).cor k).range := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun k => (MonoidHom.range_comp e.toMonoidHom (w.cor k)).symm
    rw [← hmap]
    exact ⟨t₀, htcor, rfl⟩
  ·
    rw [hAuto, haut, MonoidHom.map_closure]
    congr 1
    ext φ
    constructor
    · rintro ⟨ψ, ⟨k, rfl⟩, rfl⟩
      refine ⟨k, ?_⟩
      have hgg' : (MulAut.congr e).toMonoidHom (MulAut.conj (w.n k)) =
          MulAut.conj ((w.transport e).n k) := by
        change MulAut.congr e (MulAut.conj (w.n k)) =
          MulAut.conj ((w.transport e).n k)
        rw [GGTorusTorWit.transport_n, CFSG.StandardType.congr_conj]
      exact (ggConjAut_map_congr (MulAut.congr e).toMonoidHom (fun x y h => (MulAut.congr e).injective h) rfl (w.hn k) ((w.transport e).hn k) hgg').symm
    · rintro ⟨k, rfl⟩
      refine ⟨ggConjAut A (w.hn k), ⟨k, rfl⟩, ?_⟩
      have hgg' : (MulAut.congr e).toMonoidHom (MulAut.conj (w.n k)) =
          MulAut.conj ((w.transport e).n k) := by
        change MulAut.congr e (MulAut.conj (w.n k)) =
          MulAut.conj ((w.transport e).n k)
        rw [GGTorusTorWit.transport_n, CFSG.StandardType.congr_conj]
      exact ggConjAut_map_congr (MulAut.congr e).toMonoidHom (fun x y h => (MulAut.congr e).injective h) rfl (w.hn k) ((w.transport e).hn k) hgg'
  ·
    let Eauto : ↥(ggAutomizer Inn A) ≃* ↥(ggAutomizer Inn2 A2) :=
      ((ggAutomizer Inn A).equivMapOfInjective (MulAut.congr eA).toMonoidHom
        (fun x y h => (MulAut.congr eA).injective h)).trans
        (MulEquiv.subgroupCongr hAuto.symm)
    have hEauto : ∀ φ : ↥(ggAutomizer Inn A),
        (Eauto φ : MulAut ↥A2) = MulAut.congr eA (φ : MulAut ↥A) := by
      intro φ
      dsimp only [Eauto]
      rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
        Subgroup.coe_equivMapOfInjective_apply (H := ggAutomizer Inn A)
          (f := (MulAut.congr eA).toMonoidHom)
          (hf := fun x y h => (MulAut.congr eA).injective h) φ,
        MulEquiv.coe_toMonoidHom]
    refine ⟨eM.trans Eauto, fun k => ?_⟩
    change (Eauto (eM (M.simple k)) : MulAut ↥A2) =
      ggConjAut A2 ((w.transport e).hn k)
    rw [hEauto, hsimple k]
    have hgg' : (MulAut.congr e).toMonoidHom (MulAut.conj (w.n k)) =
        MulAut.conj ((w.transport e).n k) := by
      change MulAut.congr e (MulAut.conj (w.n k)) =
        MulAut.conj ((w.transport e).n k)
      rw [GGTorusTorWit.transport_n, CFSG.StandardType.congr_conj]
    exact ggConjAut_map_congr (MulAut.congr e).toMonoidHom (fun x y h => (MulAut.congr e).injective h) rfl (w.hn k) ((w.transport e).hn k) hgg'

theorem GGTorusTorData.transport {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} (h : GGTorusTorData m N C M L A) (e : L ≃* L2) :
    GGTorusTorData m N C M L2 (A.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.transport e, w.holds_transport e hw⟩

theorem GGTorusTorData.transport_eq {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {L L2 : Type} [Group L] [Group L2]
    {A : Subgroup (MulAut L)} {A2 : Subgroup (MulAut L2)}
    (h : GGTorusTorData m N C M L A) (e : L ≃* L2)
    (hA2 : A2 = A.map (MulAut.congr e).toMonoidHom) :
    GGTorusTorData m N C M L2 A2 := by
  subst hA2
  exact h.transport e

theorem exists_inner_model_of_cover {p : ℕ} {L R G : Type} [Group L] [Group R] [Group G]
    (e : L ≃* G) (q : R ≃* G) (ψ : L →* R) (he : ∀ l, e l = q (ψ l))
    (hcenter : Function.Injective (MulAut.conj : G →* MulAut G))
    (A : Subgroup (MulAut L)) (hA : IsElemAbelian p A)
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l))
    (hSC : ∀ g : L, (∀ a ∈ A, a g = g) → g ^ p = 1 → MulAut.conj g ∈ A) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
      (∀ g : G, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) ∧
      A.map (MulAut.congr e).toMonoidHom = E.map (MulAut.conj : G →* MulAut G) := by
  let B : Subgroup (MulAut G) := A.map (MulAut.congr e).toMonoidHom
  let j : G →* MulAut G := MulAut.conj
  have hBinn : B ≤ j.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφeq⟩ := hAI a ha
    obtain ⟨x, rfl⟩ := hI hφ
    refine ⟨q x, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := e.surjective y
    change MulAut.conj (q x) (e l) = MulAut.congr e a (e l)
    rw [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [he, he]
    simp only [← map_inv, ← map_mul]
    exact congrArg q (hφeq l)
  let E : Subgroup G := B.comap j
  have hEB : E.map j = B := Subgroup.map_comap_eq_self hBinn
  have hB : IsElemAbelian p B := TableB.isElemAbelian_map hA _
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hcenter ?_)⟩⟩, fun x hx => hcenter ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hB x.2 y.2
    · rw [map_pow, map_one]
      exact hB.2 _ hx
  have hcard : Nat.card E = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hcenter, hEB,
      Subgroup.card_map_of_injective (MulAut.congr e).injective]
  have hESC : ∀ g : G, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hnp : (e.symm g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hfix : ∀ a ∈ A, a (e.symm g) = e.symm g := by
      intro a ha
      obtain ⟨x, hx⟩ := hBinn (Subgroup.mem_map_of_mem _ ha)
      have hxE : x ∈ E := by
        change j x ∈ B
        exact hx ▸ Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom ha
      apply e.injective
      have hax : MulAut.congr e a g = x * g * x⁻¹ :=
        (congrArg (fun f : MulAut G => f g) hx).symm
      have hconj : x * g * x⁻¹ = g := by rw [← hg x hxE, mul_inv_cancel_right]
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hax.trans hconj
    have hmem := hSC (e.symm g) hfix hnp
    change j g ∈ B
    have h := Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hmem
    change MulAut.congr e (MulAut.conj (e.symm g)) ∈ B at h
    simpa only [congr_conj, MulEquiv.apply_symm_apply] using h
  exact ⟨E, hE, hcard, hESC, hEB.symm⟩

theorem GGTorusTorData.of_inner_model {L G : Type} [Group L] [Group G]
    (e : L ≃* G) {A : Subgroup (MulAut L)} {E : Subgroup G}
    (hA : A.map (MulAut.congr e).toMonoidHom = E.map (MulAut.conj : G →* MulAut G))
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M G (E.map (MulAut.conj : G →* MulAut G))) :
    GGTorusTorData m N C M L A := by
  have hback : (E.map (MulAut.conj : G →* MulAut G)).map (MulAut.congr e.symm).toMonoidHom = A := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  exact h.transport_eq e.symm hback.symm

end CFSG.StandardType
