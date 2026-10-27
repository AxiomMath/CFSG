module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepRefl
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] noncomputable def cs6Img (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φ : MulAut ↥Bs) : Module.End (ZMod 3) CS6E :=
  (θ : V →ₗ[ZMod 3] CS6E) ∘ₗ ((ggLin (p := 3) ι φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ∘ₗ
    (θ.symm : CS6E →ₗ[ZMod 3] V)

private lemma cs6Img_mul (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φ ψ : MulAut ↥Bs) :
    cs6Img ι θ (φ * ψ) = cs6Img ι θ φ * cs6Img ι θ ψ := by
  ext v
  simp [cs6Img, LinearMap.comp_apply, map_mul]

private lemma cs6Img_one (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E) :
    cs6Img ι θ (1 : MulAut ↥Bs) = 1 := by
  ext v
  simp [cs6Img]

private lemma cs6Img_conj (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φ : MulAut ↥Bs) :
    ((ggLin (p := 3) ι φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
      θ.symm.toLinearMap.comp ((cs6Img ι θ φ).comp θ.toLinearMap) := by
  ext v
  simp [cs6Img]

private lemma cs6Img_injective (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E) :
    Function.Injective (cs6Img ι θ) := by
  intro φ ψ h
  apply ggLin_injective (p := 3) ι
  apply LinearEquiv.ext
  intro v
  have h2 := congrArg (fun T : Module.End (ZMod 3) CS6E =>
    (θ.symm.toLinearMap.comp (T.comp θ.toLinearMap))) h
  simp only [← cs6Img_conj] at h2
  exact congrArg (fun T : V →ₗ[ZMod 3] V => T v) h2

private lemma cs6Img_apply_ofMul (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φ : MulAut ↥Bs) (b : ↥Bs) :
    cs6Img ι θ φ (θ (ι (Additive.ofMul b))) = θ (ι (Additive.ofMul (φ b))) := by
  simp only [cs6Img, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg θ (ggLin_apply_ofMul ι φ b)

theorem cs6_lift (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φL : Fin 6 → MulAut ↥Bs) (φa : MulAut ↥Bs) (ha aa : CS6E)
    (hL : ∀ i, cs6Img ι θ (φL i) = cs6Refl i)
    (hA : cs6Img ι θ φa = ggDepARefl ha aa)
    {g : Module.End (ZMod 3) CS6E} (hg : g ∈ Submonoid.closure (CS6Gens ha aa)) :
    ∃ φ ∈ Subgroup.closure (Set.range φL ∪ {φa}), cs6Img ι θ φ = g := by
  classical
  induction hg using Submonoid.closure_induction with
  | mem z hz =>
      rcases hz with ⟨i, rfl⟩ | hz
      · exact ⟨φL i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), hL i⟩
      · rw [Set.mem_singleton_iff] at hz
        exact ⟨φa, Subgroup.subset_closure (Or.inr rfl), by rw [hz]; exact hA⟩
  | one => exact ⟨1, Subgroup.one_mem _, cs6Img_one ι θ⟩
  | mul y z _ _ ihy ihz =>
      obtain ⟨φy, hφy, hφye⟩ := ihy
      obtain ⟨φz, hφz, hφze⟩ := ihz
      exact ⟨φy * φz, Subgroup.mul_mem _ hφy hφz, by rw [cs6Img_mul, hφye, hφze]⟩

private lemma cs6_lift_L (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φL : Fin 6 → MulAut ↥Bs) (hL : ∀ i, cs6Img ι θ (φL i) = cs6Refl i)
    {g : Module.End (ZMod 3) CS6E} (hg : g ∈ Submonoid.closure (Set.range cs6Refl)) :
    ∃ φ ∈ Subgroup.closure (Set.range φL), cs6Img ι θ φ = g := by
  classical
  induction hg using Submonoid.closure_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨φL i, Subgroup.subset_closure ⟨i, rfl⟩, hL i⟩
  | one => exact ⟨1, Subgroup.one_mem _, cs6Img_one ι θ⟩
  | mul y z _ _ ihy ihz =>
      obtain ⟨φy, hφy, hφye⟩ := ihy
      obtain ⟨φz, hφz, hφze⟩ := ihz
      exact ⟨φy * φz, Subgroup.mul_mem _ hφy hφz, by rw [cs6Img_mul, hφye, hφze]⟩

end

theorem cs6_outcome_group
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hOrbK : GGResCentBoundNbrInput)
    (hcard : Nat.card Bs = 3 ^ 6)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod 3] CS6E)
    (φL : Fin 6 → MulAut ↥Bs) (φa : MulAut ↥Bs) (ha aa yv : CS6E)
    (hL : ∀ i, cs6Img ι θ (φL i) = cs6Refl i)
    (hA : cs6Img ι θ φa = ggDepARefl ha aa)
    (hclL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hφaK : φa ∈ ggAutomizer K Bs)
    (hcardL : Nat.card ↥(ggAutomizer L Bs) = 51840)
    (hcardK : Nat.card ↥(ggAutomizer K Bs) ≤ 3840)
    (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hx : θ (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = cs6X)
    (hy : θ (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = yv)
    (d : Nat) (hd : d = 6 → Nat.card ↥(ggAutomizer K Bs) ≤ 720)
    (hOut : CS6Outcome d ha aa yv) :
    φa ∈ ggAutomizer L Bs := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let AL : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  let AK : Subgroup (MulAut ↥Bs) := ggAutomizer K Bs
  let A : Subgroup (MulAut ↥Bs) := AL ⊔ AK
  let A' : Subgroup (MulAut ↥Bs) := Subgroup.closure (Set.range φL ∪ {φa})
  let xB : ↥Bs := ⟨x, hxBs⟩
  have hfixL : ∀ s ∈ ggAutomizer L Bs, s xB = xB :=
    ggResI_automizer_fix hxBs hH.1.tableB_facts.2.2.2.1
  have hAL_le_A : AL ≤ A := le_sup_left
  have hAK_le_A : AK ≤ A := le_sup_right
  have hA'_le_A : A' ≤ A := by
    rw [show A' = Subgroup.closure (Set.range φL ∪ {φa}) from rfl, Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨i, rfl⟩ := hx
      exact hAL_le_A (by
        change φL i ∈ ggAutomizer L Bs
        rw [hclL]
        exact Subgroup.subset_closure ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hAK_le_A hφaK
  have hA'_le_top : A' ≤ ggAutomizer ⊤ Bs :=
    le_trans hA'_le_A (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
  rcases hOut with hT | hY | hY' | hW
  ·
    obtain ⟨g, hgS, htv⟩ := hT
    obtain ⟨φ, hφA', hφeq⟩ := cs6_lift ι θ φL φa ha aa hL hA hgS
    have hmem : ggLin (p := 3) ι φ ∈ Subgroup.closure (Set.range (fun i : Fin 6 =>
        ggLin (p := 3) ι (φL i)) ∪ {ggLin (p := 3) ι φa}) := by
      have h1 : ggLin (p := 3) ι φ ∈ A'.map (ggLin (p := 3) ι) :=
        Subgroup.mem_map.mpr ⟨φ, hφA', rfl⟩
      rw [show A' = Subgroup.closure (Set.range φL ∪ {φa}) from rfl,
        MonoidHom.map_closure] at h1
      have hset : Set.range (fun i : Fin 6 => ggLin (p := 3) ι (φL i)) ∪
            {ggLin (p := 3) ι φa} =
          (⇑(ggLin (p := 3) ι) '' (Set.range φL ∪ {φa})) := by
        rw [Set.image_union, Set.range_comp', Set.image_singleton]
      rw [← hset] at h1
      exact h1
    have hnt := ggIndep_nt (p := 3) (ι := ι) hH.2.2.2.1 hA'_le_top (N := 7)
      (Equiv.refl (Fin 6))
      (φ := φL) (fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
      (Subgroup.subset_closure (Or.inr rfl))
    have hconj : ((ggLin (p := 3) ι φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
        θ.symm.toLinearMap.comp (g.comp θ.toLinearMap) := by
      rw [cs6Img_conj, hφeq]
    have hcond : Module.finrank (ZMod 3) (ggLinMove (ggLin (p := 3) ι φ)) = 1 ∧
        ∀ w, ggLin (p := 3) ι φ (ggLin (p := 3) ι φ w - w) =
          ggLin (p := 3) ι φ w - w := by
      constructor
      · rw [l05nPT_conj_finrank θ g (ggLin (p := 3) ι φ) hconj]
        exact htv.1
      · exact l05nPT_conj_move_fix θ g (ggLin (p := 3) ι φ) hconj htv.2
    exact False.elim ((hnt (ggLin (p := 3) ι φ) hmem) hcond)
  ·
    obtain ⟨g, hgS, hgy⟩ := hY
    obtain ⟨φ, hφA', hφeq⟩ := cs6_lift ι θ φL φa ha aa hL hA hgS
    let yB : ↥Bs := ⟨y, hyBs⟩
    have hφx : φ xB = yB ∨ φ xB = yB⁻¹ := by
      have hconj : ((ggLin (p := 3) ι φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
          θ.symm.toLinearMap.comp (g.comp θ.toLinearMap) := by
        rw [cs6Img_conj, hφeq]
      have happ : ggLin (p := 3) ι φ (ι (Additive.ofMul xB)) = θ.symm (g cs6X) := by
        change ((ggLin (p := 3) ι φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)
            (ι (Additive.ofMul xB)) = θ.symm (g cs6X)
        rw [hconj]
        simp [xB, hx]
      rcases hgy with hgy | hgy
      · left
        have h2 : ggLin (p := 3) ι φ (ι (Additive.ofMul xB)) = ι (Additive.ofMul yB) := by
          rw [happ, hgy, ← hy]
          simp [yB]
        have h3 : ι (Additive.ofMul (φ xB)) = ι (Additive.ofMul yB) := by
          simpa only [ggLin_apply_ofMul] using h2
        exact Additive.ofMul.injective (ι.injective h3)
      · right
        have hneg : -yv = θ (ι (Additive.ofMul yB⁻¹)) := by
          rw [← hy, ← map_neg, ← map_neg, ← ofMul_inv]
        have h2 : ggLin (p := 3) ι φ (ι (Additive.ofMul xB)) = ι (Additive.ofMul yB⁻¹) := by
          rw [happ, hgy, hneg]
          simp [yB]
        have h3 : ι (Additive.ofMul (φ xB)) = ι (Additive.ofMul yB⁻¹) := by
          simpa only [ggLin_apply_ofMul] using h2
        exact Additive.ofMul.injective (ι.injective h3)
    have hfixL : ∀ s ∈ ggAutomizer L Bs, s xB = xB :=
      ggResI_automizer_fix hxBs hH.1.tableB_facts.2.2.2.1
    let T : Subgroup (MulAut ↥Bs) := (ggAutomizer L Bs).map (MulAut.conj φ).toMonoidHom
    have hT_le : T ≤ A ⊓ MulAction.stabilizer (MulAut ↥Bs) yB := by
      refine le_inf ?_ ?_
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
        exact A.mul_mem (A.mul_mem (hA'_le_A hφA') (hAL_le_A hs))
          (A.inv_mem (hA'_le_A hφA'))
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
        have hsx : s xB = xB := hfixL s hs
        have hsxinv : s xB⁻¹ = xB⁻¹ := by simp [hsx]
        have h1 : φ⁻¹ yB = xB ∨ φ⁻¹ yB = xB⁻¹ := by
          rcases hφx with hφx | hφx
          · left; rw [← hφx]; simp
          · right
            have hyb : yB = φ (xB⁻¹) := by rw [map_inv, hφx]; simp
            rw [hyb]; simp
        show (MulAut.conj φ s) • yB = yB
        rw [MulAut.conj_apply]
        change ((φ * s * φ⁻¹) : MulAut ↥Bs) yB = yB
        rw [MulAut.mul_apply, MulAut.mul_apply]
        rcases h1 with h1 | h1
        · rw [h1, hsx, ← h1]; simp
        · rw [h1, hsxinv, ← h1]; simp
    have hTcard : Nat.card ↥T = 51840 := by
      show Nat.card ↥((ggAutomizer L Bs).map (MulAut.conj φ).toMonoidHom) = 51840
      rw [Subgroup.card_map_of_injective (MulAut.conj φ).injective, hcardL]
    have hbound := hOrbK G 3 B Bs x L D J y K hH hyBs
    have hfinal : 51840 ≤ 46080 := by
      calc 51840 = Nat.card ↥T := hTcard.symm
        _ ≤ Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut ↥Bs) yB) :=
            Subgroup.card_le_of_le hT_le
        _ ≤ (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := hbound
        _ ≤ (3 - 1) * 6 * 3840 := Nat.mul_le_mul_left ((3 - 1) * 6) hcardK
        _ = 46080 := by norm_num
    exact False.elim (absurd hfinal (by norm_num))
  ·
    obtain ⟨hd6, F, hFcard, hF⟩ := hY'
    choose gv hgvS hgvx using hF
    let φv : F → MulAut ↥Bs := fun v =>
      Classical.choose (cs6_lift ι θ φL φa ha aa hL hA (hgvS v.1 v.2))
    have hφv_mem : ∀ v : F, φv v ∈ A' := fun v =>
      (Classical.choose_spec (cs6_lift ι θ φL φa ha aa hL hA (hgvS v.1 v.2))).1
    have hφv_eq : ∀ v : F, cs6Img ι θ (φv v) = gv v.1 v.2 := fun v =>
      (Classical.choose_spec (cs6_lift ι θ φL φa ha aa hL hA (hgvS v.1 v.2))).2
    let yB : ↥Bs := ⟨y, hyBs⟩
    let ψ : F → ↥Bs := fun v => φv v xB
    have hψinj : Function.Injective ψ := by
      intro u v huv
      have h2 : cs6Img ι θ (φv u) cs6X = cs6Img ι θ (φv v) cs6X := by
        rw [← hx, cs6Img_apply_ofMul, cs6Img_apply_ofMul]
        change θ (ι (Additive.ofMul (ψ u))) = θ (ι (Additive.ofMul (ψ v)))
        rw [huv]
      have h3 : gv u.1 u.2 cs6X = gv v.1 v.2 cs6X := by
        rw [← hφv_eq u, ← hφv_eq v]
        exact h2
      have h4 : u.1 = v.1 := by
        rw [hgvx u.1 u.2, hgvx v.1 v.2] at h3
        exact h3
      exact Subtype.ext h4
    let orb := MulAction.orbit (↥A) xB
    have hψ_mem : ∀ v : F, ψ v ∈ orb := by
      intro v
      refine MulAction.mem_orbit_iff.mpr ⟨⟨φv v, hA'_le_A (hφv_mem v)⟩, ?_⟩
      rfl
    have hcard_orb : F.card ≤ Nat.card orb := by
      have hf : Function.Injective (fun v : F => (⟨ψ v, hψ_mem v⟩ : orb)) := by
        intro u v huv
        exact hψinj (Subtype.ext_iff.mp huv)
      have h := Nat.card_le_card_of_injective (fun v : F => (⟨ψ v, hψ_mem v⟩ : orb)) hf
      rwa [Nat.card_eq_finsetCard] at h
    have horb_ge : 122 ≤ Nat.card orb := le_trans hFcard hcard_orb
    have hstabL : Nat.card ↥(ggAutomizer L Bs) ≤
        Nat.card ↥(MulAction.stabilizer (↥A) xB) := by
      refine Nat.card_le_card_of_injective
        (fun s : ↥(ggAutomizer L Bs) =>
          (⟨⟨(s : MulAut ↥Bs), Subgroup.mem_sup_left s.2⟩, ?_⟩ :
            MulAction.stabilizer (↥A) xB)) ?_
      · change (s : MulAut ↥Bs) xB = xB
        exact hfixL s.1 s.2
      · intro s t h
        exact Subtype.ext (congrArg (fun z : ↥(MulAction.stabilizer (↥A) xB) =>
          ((z : ↥A) : MulAut ↥Bs)) h)
    let _ : Fintype ↥A := Fintype.ofFinite ↥A
    let _ : Fintype orb := Fintype.ofFinite orb
    let _ : Fintype ↥(MulAction.stabilizer (↥A) xB) := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A) xB
    simp only [← Nat.card_eq_fintype_card] at hOS
    have hstabL' : 51840 ≤ Nat.card ↥(MulAction.stabilizer (↥A) xB) := by
      rw [← hcardL]; exact hstabL
    have hlower : 122 * 51840 ≤ Nat.card ↥A := by
      have h := Nat.mul_le_mul horb_ge hstabL'
      rwa [hOS] at h
    have hupper : Nat.card ↥A ≤ 6298560 := by
      have h1 : Nat.card ↥A ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) :=
        ggIndep_card_join_le A yB (hOrbK G 3 B Bs x L D J y K hH hyBs)
      calc Nat.card ↥A ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) := h1
        _ ≤ 3 ^ 6 * ((3 - 1) * 6 * 720) := by
            rw [hcard]
            exact Nat.mul_le_mul_left (3 ^ 6)
              (Nat.mul_le_mul_left ((3 - 1) * 6) (hd hd6))
        _ = 6298560 := by norm_num
    exfalso
    have : 122 * 51840 ≤ 6298560 := le_trans hlower hupper
    norm_num at this
  ·
    obtain ⟨φ, hφL, hφeq⟩ := cs6_lift_L ι θ φL hL hW
    have hφmem : φ ∈ ggAutomizer L Bs := by
      rw [hclL]; exact hφL
    have hEq : cs6Img ι θ φ = cs6Img ι θ φa := by rw [hφeq, hA]
    have hφaeq : φ = φa := cs6Img_injective ι θ hEq
    rw [← hφaeq]; exact hφmem

end CFSG.StandardType
