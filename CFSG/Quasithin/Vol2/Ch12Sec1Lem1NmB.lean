module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped Matrix

namespace Sec1211Ns

theorem exists_mulAut_induced {G K : Type} [Group G] [Group K] [Finite K] {X : Subgroup G}
    (ψ : ↥X →* K) (hψ : Function.Surjective ψ) {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hker : ∀ x : ↥X, ψ x = 1 →
      ψ ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX x).mp x.2⟩ = 1) :
    ∃ σ : MulAut K, ∀ x : ↥X,
      ψ ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX x).mp x.2⟩ = σ (ψ x) := by
  let cg : ↥X →* ↥X :=
    { toFun := fun x => ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let f : ↥X →* K := ψ.comp cg
  have hf : ψ.ker ≤ f.ker := fun x hx => hker x hx
  let σ₀ : K →* K := ψ.liftOfRightInverse (Function.surjInv hψ)
    (Function.rightInverse_surjInv hψ) ⟨f, hf⟩
  have hσ₀ : ∀ x : ↥X, σ₀ (ψ x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hsurj : Function.Surjective σ₀ := by
    intro k
    obtain ⟨x, rfl⟩ := hψ k
    have hx' : g⁻¹ * (x : G) * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgX) x).mp x.2
      rwa [inv_inv] at this
    refine ⟨ψ ⟨g⁻¹ * x * g, hx'⟩, ?_⟩
    rw [hσ₀]
    show ψ ⟨g * (g⁻¹ * x * g) * g⁻¹, _⟩ = ψ x
    congr 1
    exact Subtype.ext (by group)
  have hbij : Function.Bijective σ₀ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  exact ⟨MulEquiv.ofBijective σ₀ hbij, fun x => (hσ₀ x).symm⟩

theorem exists_conj_eq_slConjugation {m : ℕ} (A : GL (Fin m) (ZMod 2)) :
    ∃ z : Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      slConjugation m (ZMod 2) A = MulAut.conj z := by
  have hdet : (A : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1 := by
    have h := Matrix.GeneralLinearGroup.det_ne_zero A
    revert h
    generalize (A : Matrix (Fin m) (Fin m) (ZMod 2)).det = d
    revert d
    decide
  set z : Matrix.SpecialLinearGroup (Fin m) (ZMod 2) := ⟨A, hdet⟩ with hz
  have hA : Matrix.SpecialLinearGroup.toGL z = A := Units.ext rfl
  refine ⟨z, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [← hA, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation, MulAut.conj_apply,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← _root_.map_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

theorem mem_centralizer_V_of_mem_Y (F : Frame S m) (hm : 3 ≤ m) {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G))
    (hxY : x ∈ centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
      (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) :
    x ∈ Subgroup.centralizer (V : Set G) :=
  mem_centralizer_V_of_mem_section F hm hxM hxY.1 ⟨Subgroup.mem_top x, hxY.2⟩

theorem psi_conj_eq_one (F : Frame S m) (hm : 3 ≤ m) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G))
    (x : ↥(Sec1216Lv.lv L (a₀ * c₀))) (hx : psi F S.lv_le_Xv x = 1) :
    psi F S.lv_le_Xv ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN x).mp x.2⟩ = 1 := by
  have hxO : (x : G) ∈ pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)) :=
    mem_pCoreOf_of_mem_centralizer_W F x.2 ((psi_eq_one_iff_gen F S.lv_le_Xv x).mp hx)
  have hgO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hgN
  exact mem_ker_psi_of_mem_pCoreOf F hm ((Subgroup.mem_normalizer_iff.mp hgO _).mp hxO) _

theorem inv_mul_mem_Y_of_inner (F : Frame S m) {g : G}
    (hgH : g ∈ Subgroup.centralizer ({a₀ * c₀} : Set G))
    (hgN : g ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G))
    (l : ↥(Sec1216Lv.lv L (a₀ * c₀)))
    (h : ∀ x : ↥(Sec1216Lv.lv L (a₀ * c₀)),
      psi F S.lv_le_Xv ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN x).mp x.2⟩ =
        psi F S.lv_le_Xv l * psi F S.lv_le_Xv x * (psi F S.lv_le_Xv l)⁻¹) :
    (l : G)⁻¹ * g ∈ centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
      (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) := by
  have hlN : (l : G) ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) :=
    Subgroup.le_normalizer l.2
  have hyN : (l : G)⁻¹ * g ∈ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hlN) hgN
  have hlH : (l : G) ∈ Subgroup.centralizer ({a₀ * c₀} : Set G) :=
    Sec1216Lv.lv_le_centralizer L _ l.2
  refine (mem_centralizerSection_iff_of_le
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Sec1216Lv.lv L (a₀ * c₀)))).mpr
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hlH) hgH, fun x hx => ?_⟩
  have hxinv : x⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) := (Sec1216Lv.lv L (a₀ * c₀)).inv_mem hx
  have hgx : g * x⁻¹ * g⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) :=
    (Subgroup.mem_normalizer_iff.mp hgN _).mp hxinv
  have hyx : (l : G)⁻¹ * g * x⁻¹ * ((l : G)⁻¹ * g)⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp hxinv
  have hcomm : x * ((l : G)⁻¹ * g) * x⁻¹ * ((l : G)⁻¹ * g)⁻¹ ∈ Sec1216Lv.lv L (a₀ * c₀) := by
    have e : x * ((l : G)⁻¹ * g) * x⁻¹ * ((l : G)⁻¹ * g)⁻¹ =
        x * ((l : G)⁻¹ * g * x⁻¹ * ((l : G)⁻¹ * g)⁻¹) := by group
    rw [e]
    exact (Sec1216Lv.lv L (a₀ * c₀)).mul_mem hx hyx
  refine mem_pCoreOf_of_mem_centralizer_W F hcomm ((psi_eq_one_iff_gen F S.lv_le_Xv
    ⟨_, hcomm⟩).mp ?_)
  have h1 := h ⟨x⁻¹, hxinv⟩
  have e1 : (⟨x * ((l : G)⁻¹ * g) * x⁻¹ * ((l : G)⁻¹ * g)⁻¹, hcomm⟩ : ↥(Sec1216Lv.lv L (a₀ * c₀))) =
      ⟨x, hx⟩ * l⁻¹ * ⟨g * x⁻¹ * g⁻¹, hgx⟩ * l := Subtype.ext (by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        group)
  rw [e1, map_mul, map_mul, map_mul, map_inv, h1]
  have e2 : psi F S.lv_le_Xv ⟨x⁻¹, hxinv⟩ = (psi F S.lv_le_Xv ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e2]
  group

variable (S) in
theorem exists_mul_mem_section (F : Frame S m) (hm : 3 ≤ m)
    (hnorm : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤
      Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G))
    {g : G} (hgH : g ∈ Subgroup.centralizer ({a₀ * c₀} : Set G)) :
    ∃ x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G),
      x⁻¹ * g ∈ centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
        (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) := by
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLv
  set Y := centralizerSection H Lv (pCoreOf 2 Lv) with hY
  set ψ := psi F S.lv_le_Xv with hψdef
  have hψs : Function.Surjective ψ := psi_lv_surjective F
  have hinner : ∀ {h : G} (hhH : h ∈ H), ∀ σ : MulAut (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)),
      (∀ x : ↥Lv, ψ ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hnorm hhH) x).mp x.2⟩ =
        σ (ψ x)) → ∀ z, σ = MulAut.conj z → ∃ l ∈ Lv, (l : G)⁻¹ * h ∈ Y := by
    intro h hhH σ hσ z hz
    obtain ⟨l, rfl⟩ := hψs z
    refine ⟨l, l.2, inv_mul_mem_Y_of_inner F hhH (hnorm hhH) l fun x => ?_⟩
    rw [hσ, hz, MulAut.conj_apply]
  obtain ⟨σ, hσ⟩ := exists_mulAut_induced ψ hψs (hnorm hgH) (psi_conj_eq_one F hm (hnorm hgH))
  obtain ⟨A, ε, hε, hσA⟩ := SLnTwo.exists_conj_graph hm σ
  obtain ⟨z, hz⟩ := exists_conj_eq_slConjugation A
  have hLvM : Lv ≤ Subgroup.normalizer (L : Set G) ⊓ H := fun l hl =>
    ⟨Subgroup.le_normalizer (Sec1216Lv.lv_le_L L _ hl), Sec1216Lv.lv_le_centralizer L _ hl⟩
  interval_cases ε
  ·
    rw [pow_zero, mul_one, hz] at hσA
    obtain ⟨l, hl, hlY⟩ := hinner hgH σ hσ z hσA
    exact ⟨l, hLvM hl, hlY⟩
  ·
    rw [pow_one, hz] at hσA
    obtain ⟨t, ht, hta, htc, hs₁, -⟩ := S.exists_swap_pair
    have htH : t ∈ H := S.mem_centralizer_of_swap hta htc
    obtain ⟨σt, hσt⟩ := exists_mulAut_induced ψ hψs (hnorm htH) (psi_conj_eq_one F hm (hnorm htH))
    obtain ⟨At, εt, hεt, hσtA⟩ := SLnTwo.exists_conj_graph hm σt
    obtain ⟨zt, hzt⟩ := exists_conj_eq_slConjugation At
    have hεt1 : εt = 1 := by
      interval_cases εt
      · exfalso
        rw [pow_zero, mul_one, hzt] at hσtA
        obtain ⟨l, hl, hlY⟩ := hinner htH σt hσt zt hσtA
        have hC := mem_centralizer_V_of_mem_Y F hm (Subgroup.mul_mem _
          (Subgroup.inv_mem _ (hLvM hl).1) ht) hlY
        have hlN₁ : (l : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
          S.hyp.norm₁ (Sec1216Lv.lv_le_L L _ hl)
        have htc' : t * c₀ * t⁻¹ = c₀ := by
          have hc := Subgroup.mem_centralizer_iff.mp hC c₀ (S.le₂ S.hc₀)
          have hl1 : (l : G) * c₀ * (l : G)⁻¹ = c₀ := (S.lv_fix hl).2
          calc t * c₀ * t⁻¹ = (l : G) * (((l : G)⁻¹ * t) * c₀ * ((l : G)⁻¹ * t)⁻¹) *
              (l : G)⁻¹ := by group
            _ = (l : G) * c₀ * (l : G)⁻¹ := by
              rw [show ((l : G)⁻¹ * t) * c₀ * ((l : G)⁻¹ * t)⁻¹ = c₀ by
                rw [← hc]; group]
            _ = c₀ := hl1
        rw [htc] at htc'
        have h1 : c₀ ∈ V₁ ⊓ V₂ := ⟨htc' ▸ S.ha₀, S.hc₀⟩
        rw [S.hyp.inf, Subgroup.mem_bot] at h1
        exact S.c₀_ne h1
      · rfl
    rw [hεt1, pow_one, hzt] at hσtA
    have hgt : g * t⁻¹ ∈ H := H.mul_mem hgH (H.inv_mem htH)
    obtain ⟨σ', hσ'⟩ := exists_mulAut_induced ψ hψs (hnorm hgt) (psi_conj_eq_one F hm (hnorm hgt))
    have hσ'eq : σ' = σ * σt⁻¹ := by
      refine MulEquiv.ext fun k => ?_
      obtain ⟨x, rfl⟩ := hψs k
      have htx : t⁻¹ * (x : G) * t ∈ Lv := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hnorm htH)) x).mp x.2
        rwa [inv_inv] at this
      have h1 : σt⁻¹ (ψ x) = ψ ⟨t⁻¹ * x * t, htx⟩ := by
        show σt.symm (ψ x) = _
        rw [MulEquiv.symm_apply_eq, ← hσt]
        congr 1
        exact Subtype.ext (by group)
      rw [MulAut.mul_apply, h1, ← hσ, ← hσ']
      congr 1
      exact Subtype.ext (by group)
    have hσ'inner : σ' = MulAut.conj (z * zt⁻¹) := by
      rw [hσ'eq, hσA, hσtA, map_mul, map_inv]
      group
    obtain ⟨l, hl, hlY⟩ := hinner hgt σ' hσ' (z * zt⁻¹) hσ'inner
    refine ⟨(l : G) * t, ⟨Subgroup.mul_mem _ (hLvM hl).1 ht, H.mul_mem (hLvM hl).2 htH⟩, ?_⟩
    have htY : t⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.inv_mem _ (mem_normalizer_centralizerSection htH (hnorm htH))
    have h1 := (Subgroup.mem_normalizer_iff.mp htY _).mp hlY
    have e : t⁻¹ * ((l : G)⁻¹ * (g * t⁻¹)) * t⁻¹⁻¹ = ((l : G) * t)⁻¹ * g := by group
    rwa [e] at h1

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
