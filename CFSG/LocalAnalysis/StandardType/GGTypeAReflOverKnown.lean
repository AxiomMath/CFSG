module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverEmb
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverStar
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCount
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverHeart
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrCoreSix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ReflOver

variable {G : Type} [Group G] [Finite G]

private def reflOverR {Bs : Subgroup G} (p n : ℕ)
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p)) : Set (MulAut ↥Bs) :=
  {r | p ∣ n + 3 ∧ ∀ b : ↥Bs,
    κ (Additive.ofMul (r b)) = kThreeRefl p n (κ (Additive.ofMul b))}

private theorem reflOverR_subsingleton {Bs : Subgroup G} {p n : ℕ}
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p)) : (reflOverR p n κ).Subsingleton := by
  intro r hr s hs
  refine MulEquiv.ext fun b => ?_
  apply Additive.ofMul.injective
  apply κ.injective
  rw [hr.2 b, hs.2 b]

private theorem ggTypeAReflOver_aux (hLB : GGLBalanceInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hL : φ₁.range = L) (hK : φ₂.range = K)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (j : Fin n) (hj : j.val + 1 = n)
    {κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p)}
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs,
      κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
        kRefl p n (κ (Additive.ofMul b)))
    {y₀ : G} {K₀ : Subgroup G} (hK₀ : GGNbr p B x D J y₀ K₀)
    (hout₀ : ¬ ggAutomizer K₀ Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ∃ m, GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs) ∧
      ∃ E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs, Function.Injective E ∧
        E.range = ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs ∧
        (∃ r ∈ reflOverR p n κ, r ∈ E.range) ∧
        E.range ≤ Subgroup.closure
          (Set.range hX.permAut₁ ∪ insert (hX.permAut₂ (Equiv.swap j.castSucc j.succ))
            (reflOverR p n κ)) ∧
        n + 1 ≤ m ∧ m ≤ n + 2 ∧
        (m = n + 2 → ∃ T : Equiv.Perm (Fin (n + 3)) →* MulAut ↥Bs,
          Function.Injective T ∧ T.range = E.range ∧
          (∀ a b : Fin (n + 1), T (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) =
            hX.permAut₁ (Equiv.swap a b)) ∧
          T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc) =
            hX.permAut₂ (Equiv.swap j.castSucc j.succ) ∧
          T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 2))) ∈
            reflOverR p n κ) := by
  classical
  have hp2 : p ≠ 2 := hX.odd
  have hn : 3 ≤ n := hX.three_le
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hBs : IsElemAbelian p Bs := by
    obtain ⟨⟨-, hBs, -⟩, -, -, -, -⟩ := h
    exact hBs.2.1
  have hAll : GGSecFiveAllAJoin p B Bs x L D J := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hAll⟩ := h
    exact hAll
  obtain ⟨m, hm1, hW₀⟩ := (ggSecFiveAllAJoin_iff.mp hAll) y₀ K₀ hK₀
  obtain ⟨Ê, hÊ⟩ := exists_permEquiv_of_ggWeylOfType_A hW₀
  let A₀ : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs
  let E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs := A₀.subtype.comp Ê.toMonoidHom
  have hEinj : Function.Injective E := fun a b hab => Ê.injective (Subtype.ext hab)
  have hErange : E.range = A₀ := by
    ext r
    constructor
    · rintro ⟨σ, rfl⟩
      exact (Ê σ).2
    · intro hr
      obtain ⟨σ, hσ⟩ := Ê.surjective ⟨r, hr⟩
      exact ⟨σ, by simpa [E] using congrArg Subtype.val hσ⟩
  have hEind : ∀ σ, E σ ∈ ggInduced ⊤ Bs := by
    intro σ
    have hEA : E σ ∈ A₀ := hErange ▸ (show E σ ∈ E.range from ⟨σ, rfl⟩)
    exact mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizer_sup_le L K₀ Bs hEA)
  have hbase : GGIsReflection p
      (E (Equiv.swap (⟨0, hm1⟩ : Fin m).castSucc (⟨0, hm1⟩ : Fin m).succ)) := by
    simpa [E] using hÊ (⟨0, hm1⟩ : Fin m)
  have hErefl : ∀ a b : Fin (m + 1), a ≠ b →
      GGIsReflection p (E (Equiv.swap a b)) := fun a b hab =>
    ggIsReflection_swap_of_swap E (Fin.castSucc_lt_succ (i := (⟨0, hm1⟩ : Fin m))).ne
      hbase hab
  let bb : MulAut ↥Bs := hX.permAut₂ (Equiv.swap j.castSucc j.succ)
  have hΦA₀ : ∀ σ, hX.permAut₁ σ ∈ A₀ := fun σ =>
    Subgroup.mem_sup_left (hX.range_permAut₁_le hL ⟨σ, rfl⟩)
  have hΦA : ∀ σ, hX.permAut₁ σ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun σ =>
    Subgroup.mem_sup_left (hX.range_permAut₁_le hL ⟨σ, rfl⟩)
  have hbA : bb ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    refine Subgroup.mem_sup_right ?_
    exact ggConjAut_mem_ggAutomizer
      (hK ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩) (hX.perm_mem_normalizer₂ _)
  have houtE : ¬ E.range ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rw [hErange]
    intro hle
    exact hout₀ (le_trans le_sup_right hle)
  let ρ : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (m + 1)) :=
    Ê.symm.toMonoidHom.comp (MonoidHom.codRestrict hX.permAut₁ A₀ hΦA₀)
  have hρE : ∀ σ, E (ρ σ) = hX.permAut₁ σ := by
    intro σ
    show ((Ê (Ê.symm ⟨hX.permAut₁ σ, hΦA₀ σ⟩) : ↥A₀) : MulAut ↥Bs) = hX.permAut₁ σ
    rw [MulEquiv.apply_symm_apply]
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have h : (⟨hX.permAut₁ a, hΦA₀ a⟩ : ↥A₀) = ⟨hX.permAut₁ b, hΦA₀ b⟩ := Ê.symm.injective hab
    exact hX.permAut₁_injective (congrArg Subtype.val h)
  have hsw : ∀ a b : Fin (n + 1), a ≠ b → (ρ (Equiv.swap a b)).IsSwap := by
    intro a b hab
    exact isSwap_of_ggIsReflection hp2 hBs E hEinj hErefl
      (by rw [hρE]; exact hX.permAut₁_swap_isReflection hab)
  obtain ⟨ι, hιinj, hπι, hπz⟩ :=
    exists_embedding_of_isSwap (n := n) (by omega) ρ hρinj hsw
  have hι : ∀ a b : Fin (n + 1),
      E (Equiv.swap (ι a) (ι b)) = hX.permAut₁ (Equiv.swap a b) := by
    intro a b
    rw [← map_swap_eq_swap_of_embedding (g := ⇑ρ) hιinj hπι hπz a b, hρE]
  have hR : (reflOverR p n κ).Subsingleton := reflOverR_subsingleton κ
  have hdich : ∀ z, z ∉ Set.range ι →
      E (Equiv.swap (ι (Fin.last n)) z) = bb ∨
        E (Equiv.swap (ι (Fin.last n)) z) ∈ reflOverR p n κ := by
    intro z hz
    have h := GGFarCtx.star_dichotomy hLB h hX hL hK hJ j hj κ hκ₁ hκ₂ E hEinj hEind hErefl
      ι hιinj ρ hρE hπι hπz hz
    rwa [show hX.permAut₂ (Equiv.swap j.castSucc j.succ) = bb from rfl] at h
  obtain ⟨hexR, hclosure, hnm, hle, hT⟩ :=
    star_struct E hEinj hX.permAut₁ ι hιinj hι bb (reflOverR p n κ) hR hdich
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) hΦA hbA houtE
  exact ⟨m, hW₀, E, hEinj, hErange, hexR, hclosure, hnm, hle, hT⟩

theorem ggTypeAReflOver_of_known (hCD : GGTypeACompatDiagBInput) (hLB : GGLBalanceInput)
    (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput) (hC : GGNbrTableBCardInput)
    (hO : GGNbrTableBOrderRestInput) (hF : GGNbrFrameInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G}
    {K : Subgroup G} (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hTP : GGNbrTablePConfig p B Bs x L D J) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K')
    (hout : ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    p ∣ n + 3 ∧
      GGWeylOfType p (CoxeterMatrix.A (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) ∧
      ∀ (y'' : G) (K'' : Subgroup G), GGNbr p B x D J y'' K'' →
        ggAutomizer K'' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ⊔ ggAutomizer K' Bs := by
  classical
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, hdiag⟩ := hCD G p B Bs x L D J n f y K h
  have hX : GGFarCtx p Bs φ₁ φ₂ x y := ggFarCtx_of_cfg h hL hk₁ hK hk₂ hc hdiag
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hp2 : p ≠ 2 := hX.odd
  have hn : 3 ≤ n := hX.three_le
  have hBs : IsElemAbelian p Bs := by
    obtain ⟨⟨-, hBs, -⟩, -, -, -, -⟩ := h
    exact hBs.2.1
  have hW : GGWeylOfType p (CoxeterMatrix.A (n + 1))
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
    exact hW
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have hi : i.val = 0 := rfl
  have hj : j.val + 1 = n := by simp [j]; omega
  have hmem₁ : ∀ π, hX.permAut₁ π ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro π
    refine Subgroup.mem_sup_left ?_
    have hg : φ₁ (slPerm hX.two π) ∈ L := hL ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    exact ggConjAut_mem_ggAutomizer hg (hX.perm_mem_normalizer₁ π)
  have hmem₂ : ∀ π, hX.permAut₂ π ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro π
    refine Subgroup.mem_sup_right ?_
    have hg : φ₂ (slPerm hX.two π) ∈ K := hK ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    exact ggConjAut_mem_ggAutomizer hg (hX.perm_mem_normalizer₂ π)
  have hr₁ : ∀ a b, a ≠ b → GGIsReflection p (hX.permAut₁ (Equiv.swap a b)) :=
    fun a b hab => hX.permAut₁_swap_isReflection hab
  have hr₂ : ∀ a b, a ≠ b → GGIsReflection p (hX.permAut₂ (Equiv.swap a b)) :=
    fun a b hab => hX.permAut₂_swap_isReflection hab
  have houth : ∀ σ, hX.permAut₁ σ ≠ hX.permAut₂ (Equiv.swap j.castSucc j.succ) := by
    intro σ heq
    have hx := congrArg (fun g : MulAut ↥Bs => g ⟨x, hX.x_mem⟩) heq
    rw [hX.permAut₁_fix_x σ] at hx
    exact hX.permAut₂_swap_ne_x hj hx.symm
  have hfar : hX.permAut₁ (Equiv.swap 0 1) * hX.permAut₂ (Equiv.swap j.castSucc j.succ) =
      hX.permAut₂ (Equiv.swap j.castSucc j.succ) * hX.permAut₁ (Equiv.swap 0 1) := by
    have hcomm := ggFar_aut_commute hX.odd hBs hX.three_le hW hX.permAut₁ hX.permAut₂ hmem₁
      hmem₂ hX.permAut₁_injective hX.permAut₂_injective hr₁ hr₂ hX.permAut_compat hi hj houth
    have h0 : i.castSucc = (0 : Fin (n + 1)) := Fin.ext rfl
    have h1 : i.succ = (1 : Fin (n + 1)) := by
      apply Fin.ext
      simp [i]
      rw [Nat.mod_eq_of_lt (by omega)]
    rwa [h0, h1] at hcomm
  obtain ⟨κ, hκ₁, hκ₂, hκx⟩ := hX.exists_coordEquiv hBs j hj hfar
  obtain ⟨m', hW', E', hE'inj, hE'range, ⟨r', hr'R, hr'E'⟩, hcl', hmn', hmx', hT'⟩ :=
    ggTypeAReflOver_aux hLB h hX hL hK hJ j hj hκ₁ hκ₂ hK' hout
  have hpn : p ∣ n + 3 := hr'R.1
  refine ⟨hpn, ?_, ?_⟩
  · by_cases hm2 : m' = n + 2
    · exfalso
      obtain ⟨hy', hy'K, hy'D, hy'x, hxne⟩ := ggNbr_facts h.1 hK'
      obtain ⟨T, hTinj, hTrange, hT₁, hT₂, hT₃⟩ := hT' hm2
      have hTrange' : T.range = ggAutomizer L Bs ⊔ ggAutomizer K' Bs :=
        hTrange.trans hE'range
      let T' : Equiv.Perm (Fin (n + 3)) →* ((Fin (n + 1) → ZMod p) ≃ₗ[ZMod p]
          (Fin (n + 1) → ZMod p)) := (ggLin (p := p) κ).comp T
      have hT'₁ : ∀ a b : Fin (n + 1),
          T' (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) =
            coordPerm p n (Equiv.swap a b) := by
        intro a b
        refine LinearEquiv.ext fun v => ?_
        rw [MonoidHom.comp_apply, ggLin_apply, hT₁ a b,
          hκ₁ (Equiv.swap a b) (Additive.toMul (κ.symm v))]
        rw [ofMul_toMul, AddEquiv.apply_symm_apply]
      have hT'₂ : T' (Equiv.swap (Fin.last n).castSucc.castSucc
          (Fin.last (n + 1)).castSucc) = kRefl p n := by
        refine LinearEquiv.ext fun v => ?_
        rw [MonoidHom.comp_apply, ggLin_apply, hT₂, hκ₂ (Additive.toMul (κ.symm v))]
        rw [ofMul_toMul, AddEquiv.apply_symm_apply]
      have hT'₃ : T' (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 2))) =
          kThreeRefl p n := by
        refine LinearEquiv.ext fun v => ?_
        rw [MonoidHom.comp_apply, ggLin_apply, hT₃.2 (Additive.toMul (κ.symm v))]
        rw [ofMul_toMul, AddEquiv.apply_symm_apply]
      let P₁ : Subgroup (Equiv.Perm (Fin (n + 3))) := (ggAutomizer L Bs).comap T
      let P₂ : Subgroup (Equiv.Perm (Fin (n + 3))) := (ggAutomizer K' Bs).comap T
      have hle₁ : ggAutomizer L Bs ≤ T.range := by
        rw [hTrange']; exact le_sup_left
      have hle₂ : ggAutomizer K' Bs ≤ T.range := by
        rw [hTrange']; exact le_sup_right
      have hP : P₁ ⊔ P₂ = ⊤ := by
        apply Subgroup.map_injective hTinj
        rw [Subgroup.map_sup, Subgroup.map_comap_eq_self hle₁,
          Subgroup.map_comap_eq_self hle₂, ← MonoidHom.range_eq_map, hTrange']
      let v₁ : Fin (n + 1) → ZMod p := κ (Additive.ofMul ⟨x, hX.x_mem⟩)
      have hv₁ : ∀ σ ∈ P₁, T' σ v₁ = v₁ := by
        intro σ hσ
        have hσ' : T σ ∈ ggAutomizer L Bs := hσ
        rw [MonoidHom.comp_apply, ggLin_apply]
        have hfix : T σ ⟨x, hX.x_mem⟩ = ⟨x, hX.x_mem⟩ :=
          ggAutomizer_fix_of_centralizes (φ := T σ) hX.x_mem h.x_comm_of_mem_L hσ'
        have harg : Additive.toMul (κ.symm v₁) = ⟨x, hX.x_mem⟩ := by
          change Additive.toMul (κ.symm (κ (Additive.ofMul ⟨x, hX.x_mem⟩))) =
            ⟨x, hX.x_mem⟩
          rw [AddEquiv.symm_apply_apply, toMul_ofMul]
        rw [harg, hfix]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hκx
      have hcv : v₁ = fun _ => c := by
        have hv : v₁ = c • (1 : Fin (n + 1) → ZMod p) := hc.symm
        rw [hv]
        funext i
        simp
      have hc0 : c ≠ 0 := by
        intro hc0
        have hxv : (⟨x, hX.x_mem⟩ : ↥Bs) = 1 := by
          apply Additive.ofMul.injective
          apply κ.injective
          change v₁ = κ (Additive.ofMul (1 : ↥Bs))
          rw [hcv, hc0]
          funext i
          simp
        exact hxne (Subtype.ext_iff.mp hxv)
      let v₂ : Fin (n + 1) → ZMod p := κ (Additive.ofMul ⟨y', hy'⟩)
      have hy'K' : ∀ k ∈ K', y' * k = k * y' := fun k hk =>
        (Subgroup.mem_centralizer_iff.mp hy'K k hk).symm
      have hv₂ : ∀ σ ∈ P₂, T' σ v₂ = v₂ := by
        intro σ hσ
        have hσ' : T σ ∈ ggAutomizer K' Bs := hσ
        rw [MonoidHom.comp_apply, ggLin_apply]
        have hfix : T σ ⟨y', hy'⟩ = ⟨y', hy'⟩ :=
          ggAutomizer_fix_of_centralizes (φ := T σ) hy' hy'K' hσ'
        have harg : Additive.toMul (κ.symm v₂) = ⟨y', hy'⟩ := by
          change Additive.toMul (κ.symm (κ (Additive.ofMul ⟨y', hy'⟩))) =
            ⟨y', hy'⟩
          rw [AddEquiv.symm_apply_apply, toMul_ofMul]
        rw [harg, hfix]
      have hnbr : GGNbr p B x D J y K := by
        obtain ⟨-, -, -, -, htypeA⟩ := h
        obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
        exact hnbr
      have hW₂ : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → v₂ i = v₂ j := by
        have hvv : ∀ a b : Fin n, v₂ a.succ = v₂ b.succ := by
          intro a b
          have hgL : φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) ∈ L :=
            hL ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
          have hxg : x * φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) =
              φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) * x :=
            h.x_comm_of_mem_L _ hgL
          have hyg : y * φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) =
              φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) * y := by
            have h := hX.y_comm (slPerm hX.two (Equiv.swap a.castSucc b.castSucc))
            rwa [← hX.map_slPerm_swap_compat a b] at h
          have hDcent : D ≤ Subgroup.centralizer
              ({φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ))} : Set G) := by
            rw [hnbr.2.1]
            refine (Subgroup.closure_le _).mpr ?_
            rintro z (rfl | rfl)
            · exact Subgroup.mem_centralizer_singleton_iff.mpr hxg
            · exact Subgroup.mem_centralizer_singleton_iff.mpr hyg
          have hgy' : φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) * y' =
              y' * φ₁ (slPerm hX.two (Equiv.swap a.succ b.succ)) :=
            Subgroup.mem_centralizer_iff.mp (hDcent hy'D) _ (Set.mem_singleton _)
          have hfix : hX.permAut₁ (Equiv.swap a.succ b.succ) ⟨y', hy'⟩ = ⟨y', hy'⟩ := by
            apply Subtype.ext
            rw [GGFarCtx.permAut₁_apply]
            rw [hgy']
            group
          have hv₂fix : v₂ = coordPerm p n (Equiv.swap a.succ b.succ) v₂ := by
            have h := hκ₁ (Equiv.swap a.succ b.succ) ⟨y', hy'⟩
            rw [hfix] at h
            exact h
          conv_lhs => rw [hv₂fix]
          rw [coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left]
        intro i j hi hj
        obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        exact hvv a b
      have h01 : v₂ 0 ≠ v₂ 1 := by
        intro heq
        have hconst : v₂ = fun _ => v₂ 0 := by
          funext i
          by_cases hi : i = 0
          · rw [hi]
          · have h10 : (1 : Fin (n + 1)) ≠ 0 := by
              haveI : NeZero n := ⟨by omega⟩
              rw [← Fin.succ_zero_eq_one' (n := n)]
              exact Fin.succ_ne_zero _
            have h1 : v₂ i = v₂ 1 := hW₂ i 1 hi h10
            rw [h1, heq]
        have hfixall : ∀ σ, hX.permAut₁ σ ⟨y', hy'⟩ = ⟨y', hy'⟩ := by
          intro σ
          have hcoord : coordPerm p n σ v₂ = v₂ := by
            rw [hconst]
            funext i
            simp [coordPerm_apply]
          have h := hκ₁ σ ⟨y', hy'⟩
          rw [hcoord] at h
          exact Additive.ofMul.injective (κ.injective h)
        exact hy'x (hX.mem_zpowers_of_perm_fixed hL h.mem_zpowers_x_of_comm_L hy' hfixall)
      obtain ⟨hp3, hdvd⟩ := eq_three_and_card_dvd_of_sup_eq_top hp2 hn hpn T' hT'₁ hT'₂ hT'₃
        hP hv₁ hv₂ hc0 hcv hW₂ h01
      have hdvd' : Nat.card ↥(ggAutomizer K' Bs) ∣ 6 * n.factorial := by
        have hmap₂ : Subgroup.map T P₂ = ggAutomizer K' Bs :=
          Subgroup.map_comap_eq_self hle₂
        have hcard : Nat.card ↥(ggAutomizer K' Bs) = Nat.card ↥P₂ := by
          rw [← hmap₂, Subgroup.card_map_of_injective hTinj]
        rw [hcard]
        exact hdvd
      exact ggTypeANbr_false_of_card_dvd hCD hRig hTB hC hO hF h hTP hK' hW' hp3 hpn hdvd'
    · have hm1' : m' = n + 1 := by omega
      exact hm1' ▸ hW'
  · intro y'' K'' hK''
    by_cases hle : ggAutomizer K'' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs
    · exact le_trans hle le_sup_left
    · obtain ⟨m'', hW'', E'', hE''inj, hE''range, ⟨r'', hr''R, hr''E⟩, hcl'', hmn'',
        hmx'', hT''⟩ :=
        ggTypeAReflOver_aux hLB h hX hL hK hJ j hj hκ₁ hκ₂ hK'' hle
      have hsup_le : ggAutomizer L Bs ⊔ ggAutomizer K' Bs ≤
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊔ ggAutomizer K' Bs :=
        sup_le (le_sup_left.trans le_sup_left) le_sup_right
      have hle' : ggAutomizer L Bs ⊔ ggAutomizer K'' Bs ≤
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊔ ggAutomizer K' Bs := by
        rw [← hE''range]
        refine le_trans hcl'' ((Subgroup.closure_le _).mpr ?_)
        rintro x (hx | hx)
        · obtain ⟨σ, rfl⟩ := hx
          exact Subgroup.mem_sup_left
            (Subgroup.mem_sup_left (hX.range_permAut₁_le hL ⟨σ, rfl⟩))
        · rcases hx with rfl | hx
          · exact Subgroup.mem_sup_left (hmem₂ (Equiv.swap j.castSucc j.succ))
          · have hxr : x = r' := reflOverR_subsingleton κ hx hr'R
            rw [hxr]
            exact hsup_le (hE'range ▸ (show r' ∈ E'.range from hr'E'))
      exact le_trans le_sup_right hle'

end ReflOver

end CFSG.StandardType

end
