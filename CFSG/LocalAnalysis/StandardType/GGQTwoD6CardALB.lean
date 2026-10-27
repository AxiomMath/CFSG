module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALB1
public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatumTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2d6l_range_g (jb jc : Fin 6) (hjb : jb = 4 ∨ jb = 5) (hjc : jc = 4 ∨ jc = 5)
    (hne : jb ≠ jc) (g : Fin 5 → Fin 6) (hg : g = ![0, 1, 2, 3, jc]) :
    Set.range g = {n | n ≠ jb} := by
  rcases hjb with rfl | rfl <;> rcases hjc with rfl | rfl
  · exact absurd rfl hne
  · subst hg
    ext n
    fin_cases n <;> decide
  · subst hg
    ext n
    fin_cases n <;> decide
  · exact absurd rfl hne

private lemma ggQ2d6l_inj_g (jb jc : Fin 6) (hjb : jb = 4 ∨ jb = 5) (hjc : jc = 4 ∨ jc = 5)
    (hne : jb ≠ jc) (g : Fin 5 → Fin 6) (hg : g = ![0, 1, 2, 3, jc]) :
    Function.Injective g := by
  rcases hjb with rfl | rfl <;> rcases hjc with rfl | rfl
  · exact absurd rfl hne
  · subst hg
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · subst hg
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact absurd rfl hne

private lemma ggQ2d6l_cartan_g (jb jc : Fin 6) (hjb : jb = 4 ∨ jb = 5) (hjc : jc = 4 ∨ jc = 5)
    (hne : jb ≠ jc) (g : Fin 5 → Fin 6) (hg : g = ![0, 1, 2, 3, jc]) :
    ∀ i j : Fin 5, CartanMatrix.D 6 (g i) (g j) = CartanMatrix.A 5 i j := by
  rcases hjb with rfl | rfl <;> rcases hjc with rfl | rfl
  · exact absurd rfl hne
  · subst hg
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · subst hg
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · exact absurd rfl hne

private lemma ggQ2d6l_transp_conj6 (t : Equiv.Perm (Fin 6)) (ht : t ∈ ggTransp 6) :
    ∃ (π : Equiv.Perm (Fin 6)) (i : Fin 5),
      t = π * Equiv.swap i.castSucc i.succ * π⁻¹ := by
  obtain ⟨a, c, hac, rfl⟩ := ht
  obtain ⟨π, hπ⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_swap (w := (0 : Fin 5).castSucc) (x := (0 : Fin 5).succ) (y := a) (z := c)
      (by decide) hac)
  exact ⟨π, 0, hπ.symm⟩

theorem ggQ2d6l_modData {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} [Fact (Nat.Prime 3)] (hS : GGQTwoSetting 3 B Bs x L D J) {K : Subgroup G}
    (N : GGQ2NbrDatum 3 Bs K) (b : N.Λ) (hb : N.IsD6Fork b) :
    ∃ (Φ : Equiv.Perm (Fin 6) ≃* ↥(Subgroup.closure (N.simple '' {k | k ≠ b}))) (Dm : D6Mod N.V),
      (∀ σ, Dm.ρ σ = ggLin (p := 3) N.model (Φ σ : MulAut ↥Bs)) ∧
        ∀ t ∈ ggTransp 6, GGIsReflection 3 (Φ t : MulAut ↥Bs) := by
  classical
  obtain ⟨e, he, hb45⟩ := hb
  let jb : Fin 6 := if b = e 4 then 4 else 5
  let jc : Fin 6 := if b = e 4 then 5 else 4
  let g : Fin 5 → Fin 6 := ![0, 1, 2, 3, jc]
  let f : Fin 5 → N.Λ := fun i => e (g i)
  have hjb : jb = 4 ∨ jb = 5 := by by_cases h : b = e 4 <;> simp [jb, h]
  have hjc : jc = 4 ∨ jc = 5 := by by_cases h : b = e 4 <;> simp [jc, h]
  have hne : jb ≠ jc := by by_cases h : b = e 4 <;> simp [jb, jc, h]
  have hjb_eq : e jb = b := by
    by_cases h : b = e 4
    · simp [jb, h]
    · have h5 : b = e 5 := hb45.resolve_left h
      simp only [jb, h, if_false]
      exact h5.symm
  have hgr : Set.range g = {n | n ≠ jb} := ggQ2d6l_range_g jb jc hjb hjc hne g rfl
  have hgi : Function.Injective g := ggQ2d6l_inj_g jb jc hjb hjc hne g rfl
  have hgc : ∀ i j : Fin 5, CartanMatrix.D 6 (g i) (g j) = CartanMatrix.A 5 i j :=
    ggQ2d6l_cartan_g jb jc hjb hjc hne g rfl
  have hf_inj : Function.Injective f := fun i j hij => hgi (e.injective hij)
  have hf_range : Set.range f = {k | k ≠ b} := by
    have h1 : Set.range f = e '' Set.range g := by
      ext k; constructor
      · rintro ⟨i, rfl⟩; exact ⟨g i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨n, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [h1, hgr]
    ext k; constructor
    · rintro ⟨n, hn, rfl⟩ hk
      exact hn (e.injective (hk.trans hjb_eq.symm))
    · intro hk
      refine ⟨e.symm k, fun hc => hk (by rw [← e.apply_symm_apply k, hc, hjb_eq]),
        e.apply_symm_apply k⟩
  have hcartE : ∀ a c : Fin 6, N.cartan (e a) (e c) = CartanMatrix.D 6 a c := by
    have hC : GGIntCartan ((ggCoxeterMatrixD 6).reindex e) N.cartan := by
      rw [← he]; exact N.isCartan
    have hC0 : GGIntCartan ((ggCoxeterMatrixD 6).reindex e)
        (Matrix.reindex e e (CartanMatrix.D 6)) := (ggIntCartan_D 6).reindex e
    have hone : GGAtMostOneMultipleEdge ((ggCoxeterMatrixD 6).reindex e) :=
      (ggAtMostOneMultipleEdge_D 6).reindex e
    rcases hC.eq_or_eq_transpose hC0 hone with h | h
    · intro a c
      have hh := congrFun (congrFun h (e a)) (e c)
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm_apply_apply] using hh
    · intro a c
      have hh := congrFun (congrFun h (e a)) (e c)
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        e.symm_apply_apply] at hh
      rw [hh]
      exact (CartanMatrix.D_isSymm 6).apply a c
  have hcart_reindex : N.cartan = Matrix.reindex e e (CartanMatrix.D 6) := by
    ext a c
    rw [← e.apply_symm_apply a, ← e.apply_symm_apply c, hcartE]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm_apply_apply]
  have hdet : ((N.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
    rw [hcart_reindex, Matrix.det_reindex_self e (CartanMatrix.D 6),
      CartanMatrix.D_det (by omega)]
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd 4 3] at h
    norm_num at h
  have hcart : ∀ i j : Fin 5, N.cartan (f i) (f j) = CartanMatrix.A 5 i j := by
    intro i j
    show N.cartan (e (g i)) (e (g j)) = CartanMatrix.A 5 i j
    rw [hcartE (g i) (g j)]
    exact hgc i j
  have hind : LinearIndependent (ZMod 3) N.coroot :=
    N.toWDatum.coroot_linearIndependent_of_det hdet
  have hind' : LinearIndependent (ZMod 3) (fun i : Fin 5 => N.coroot (f i)) :=
    hind.comp f hf_inj
  let r : Fin 5 → (N.V ≃ₗ[ZMod 3] N.V) := fun i => ggLin (p := 3) N.model (N.simple (f i))
  have hr : ∀ i v, r i v = v - N.root (f i) v • N.coroot (f i) := fun i v => N.simple_apply (f i) v
  have hα : ∀ i j, N.root (f i) (N.coroot (f j)) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3) := by
    intro i j
    rw [N.pairing, hcart i j]
  have hrange : Set.range r = (ggLin (p := 3) N.model) '' (N.simple '' {k | k ≠ b}) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨N.simple (f i), ⟨f i, by rw [← hf_range]; exact ⟨i, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
      have hkr : k ∈ Set.range f := by rw [hf_range]; exact hk
      obtain ⟨i, hfi⟩ := hkr
      refine ⟨i, ?_⟩
      rw [← hfi] at hy
      exact hy
  have hnt : ∀ a ∈ Subgroup.closure (Set.range r),
      ∀ (q : Module.Dual (ZMod 3) N.V) (w : N.V),
        q ≠ 0 → w ≠ 0 → q w = 0 → (∀ v, a v = v + q v • w) → False := by
    intro a ha q w hq0 hw0 hqw hform
    have ha' : a ∈ (Subgroup.closure (N.simple '' {k | k ≠ b})).map (ggLin (p := 3) N.model) := by
      rw [MonoidHom.map_closure, ← hrange]
      exact ha
    obtain ⟨φ, hφmem, hφeq⟩ := Subgroup.mem_map.mp ha'
    have hφK : φ ∈ ggAutomizer K Bs := by
      rw [N.automizer_K]
      exact Subgroup.closure_mono (by rintro _ ⟨k, hk, rfl⟩; exact ⟨k, rfl⟩) hφmem
    have hφtop : φ ∈ ggInduced ⊤ Bs := by
      have h1 : φ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφK
      rwa [ggAutomizer_eq] at h1
    exact hS.1.2.2.2.1 φ hφtop (ggIsTransvection_of_apply N.model hw0 hq0 hqw (fun v => by
      rw [hφeq]; exact hform v))
  obtain ⟨Dm, hinjρ, hswap⟩ := ggQ2d6l_A5lift (fun i => N.coroot (f i)) hind'
    (fun i => N.root (f i)) hα r hr hnt
  have hrangeρ : Dm.ρ.range = Subgroup.closure (Set.range r) := by
    rw [MonoidHom.range_eq_map,
      ← Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5),
      MonoidHom.map_closure]
    congr 1
    ext x; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hswap i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hswap i⟩
  have hρmem : ∀ σ, Dm.ρ σ ∈ Subgroup.closure (Set.range r) := fun σ => by
    rw [← hrangeρ]
    exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  let H : Subgroup (MulAut ↥Bs) := Subgroup.closure (N.simple '' {k | k ≠ b})
  have hHmap : H.map (ggLin (p := 3) N.model) = Subgroup.closure (Set.range r) := by
    change (Subgroup.closure (N.simple '' {k | k ≠ b})).map (ggLin (p := 3) N.model) = _
    rw [MonoidHom.map_closure, hrange]
  let gH : ↥H →* ↥(Subgroup.closure (Set.range r)) :=
    { toFun := fun ψ => ⟨ggLin (p := 3) N.model (ψ : MulAut ↥Bs), by
        rw [← hHmap]
        exact Subgroup.mem_map.mpr ⟨ψ, ψ.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun ψ χ => by ext; simp }
  have hgHinj : Function.Injective gH := by
    intro u v huv
    apply Subtype.ext
    apply ggLin_injective (p := 3) N.model
    have h1 := congrArg (fun z : ↥(Subgroup.closure (Set.range r)) => (z : N.V ≃ₗ[ZMod 3] N.V)) huv
    simpa [gH] using h1
  have hgHsurj : Function.Surjective gH := by
    intro y
    have hy : (y : N.V ≃ₗ[ZMod 3] N.V) ∈ H.map (ggLin (p := 3) N.model) := by
      rw [hHmap]; exact y.2
    obtain ⟨φ, hφmem, hφeq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨φ, hφmem⟩, Subtype.ext hφeq⟩
  let eH : ↥H ≃* ↥(Subgroup.closure (Set.range r)) := MulEquiv.ofBijective gH ⟨hgHinj, hgHsurj⟩
  have heH : ∀ ψ : ↥H, (eH ψ : N.V ≃ₗ[ZMod 3] N.V) =
      ggLin (p := 3) N.model (ψ : MulAut ↥Bs) := fun ψ => rfl
  let ρc : Equiv.Perm (Fin 6) →* ↥(Subgroup.closure (Set.range r)) :=
    (Dm.ρ).codRestrict (Subgroup.closure (Set.range r)) hρmem
  have hρcinj : Function.Injective ρc := by
    intro σ τ h
    apply hinjρ
    have h1 := congrArg (fun z : ↥(Subgroup.closure (Set.range r)) => (z : N.V ≃ₗ[ZMod 3] N.V)) h
    simpa [ρc] using h1
  have hρcsurj : Function.Surjective ρc := by
    intro y
    have hy : (y : N.V ≃ₗ[ZMod 3] N.V) ∈ Dm.ρ.range := by
      rw [hrangeρ]; exact y.2
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hy
    exact ⟨σ, Subtype.ext hσ⟩
  let ρe : Equiv.Perm (Fin 6) ≃* ↥(Subgroup.closure (Set.range r)) :=
    MulEquiv.ofBijective ρc ⟨hρcinj, hρcsurj⟩
  let Φ : Equiv.Perm (Fin 6) ≃* ↥H := ρe.trans eH.symm
  have hΦeq : ∀ σ, Dm.ρ σ = ggLin (p := 3) N.model (Φ σ : MulAut ↥Bs) := by
    intro σ
    have h1 : eH (Φ σ) = ρe σ := by
      change eH (eH.symm (ρe σ)) = ρe σ
      exact eH.apply_symm_apply _
    have h3 : (ρe σ : N.V ≃ₗ[ZMod 3] N.V) = Dm.ρ σ := rfl
    calc Dm.ρ σ = (ρe σ : N.V ≃ₗ[ZMod 3] N.V) := h3.symm
      _ = (eH (Φ σ) : N.V ≃ₗ[ZMod 3] N.V) := by rw [h1]
      _ = ggLin (p := 3) N.model (Φ σ : MulAut ↥Bs) := heH (Φ σ)
  have hswapΦ : ∀ i : Fin 5, ((Φ (Equiv.swap i.castSucc i.succ) : ↥H) : MulAut ↥Bs) =
      N.simple (f i) := by
    intro i
    apply ggLin_injective (p := 3) N.model
    rw [← hΦeq (Equiv.swap i.castSucc i.succ), hswap i]
  have hsimple_refl : ∀ k : N.Λ, GGIsReflection 3 (N.simple k) := by
    intro k
    have hfx : N.root k (N.coroot k) = 2 := by
      rw [N.pairing, N.isCartan.1]
      norm_num
    exact ggIsReflection_of_eq_reflection (p := 3) (by decide) N.model hfx
      (ggLin_eq_reflection N.model hfx (fun v => N.simple_apply k v))
  refine ⟨Φ, Dm, hΦeq, ?_⟩
  intro t ht
  obtain ⟨π, i, hti⟩ := ggQ2d6l_transp_conj6 t ht
  rw [hti, map_mul, map_mul, map_inv]
  change GGIsReflection 3 (((Φ π : ↥H) : MulAut ↥Bs) *
    ((Φ (Equiv.swap i.castSucc i.succ) : ↥H) : MulAut ↥Bs) *
      (((Φ π : ↥H) : MulAut ↥Bs))⁻¹)
  rw [hswapΦ i]
  exact (hsimple_refl (f i)).conj' (((Φ π : ↥H) : MulAut ↥Bs))

end CFSG.StandardType

end
