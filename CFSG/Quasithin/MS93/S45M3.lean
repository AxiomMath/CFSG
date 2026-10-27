module

public import CFSG.Quasithin.MS93.S45M2
public import CFSG.Quasithin.MS93.S45M1
public import CFSG.Quasithin.MS93.S46Fin

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem exists_branch (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h10 : 10 ≤ a)
    (haN : a + 3 ≤ N) :
    ∃ p' : ℕ → Vtx (puAmalgam c.hyp.le), IsGoodPath _ p' N ∧ (∀ i, i ≤ a + 2 → p' i = p i) ∧
      Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)) ∧
      Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
        Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) := by
  have h := c.hyp
  obtain ⟨γ, hγa, hγZ, hγne⟩ := c.exists_adj_branch hp (y := a + 2) (ha.add even_two)
    (by omega) (by omega)
  rw [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at hγne
  rw [show a + 2 - 8 = a - 6 by omega] at hγZ
  obtain ⟨p₁, hp₁e, hp₁, hU⟩ := (hp.mono (show a + 2 ≤ N by omega)).extend_of h c.b8 c.c444
    (by omega) (ha.add even_two) hγa hγZ
  obtain ⟨p', hp'e, hp'⟩ := c.exists_extend hp₁ (by omega) ((ha.add even_two).add even_two) N
  have hp'N : IsGoodPath _ p' N := hp'.mono (by omega)
  have hpp' : ∀ i, i ≤ a + 2 → p' i = p i := fun i hi => (hp'e i (by omega)).trans (hp₁e i hi)
  have hp'3 : Usup (puAmalgam h.le) (p (a + 2)) (p' (a + 3)) = Usup _ (p (a + 2)) γ := by
    rw [hp'e (a + 3) (by omega)]
    exact hU
  refine ⟨p', hp'N, hpp', fun heq => hγZ ?_, by rw [hp'3]; exact hγne⟩
  rw [← hp'3, heq]
  have hα := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have ha6 : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc := hp.crit (a - 6) ha6 (by omega)
  rw [show a - 6 + 8 = a + 2 by omega] at hc
  have hZ := c.zm_le_qv_geo_one hc
  rw [show geo (puAmalgam h.le) (p (a + 2)) (p (a - 6)) 1 = p (a + 1) by
    rw [hp.eq_geo_rev (i := a - 6) (j := a + 2) (k := a + 1) (by omega) (by omega) (by omega),
      show a + 2 - (a + 1) = 1 by omega]] at hZ
  exact hZ.trans (c.qv_le_normalizer_usup hα (hp.adj (a + 1) (by omega)).symm)

theorem mid_layer (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h24 : 24 ≤ a) (haN : a + 24 ≤ N)
    {p' : ℕ → Vtx (puAmalgam c.hyp.le)} (hp' : IsGoodPath _ p' N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) (p (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) ⊔
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p' (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) = whv c.hyp (p a) (p (a + 2)) ∧
    (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) ⊓
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p' (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) = Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) ∧
    IsSumOfNaturalModulesVia (stab _ (p a))
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ψ true 1 ∧
    IsSumOfNaturalModulesVia (stab _ (p a))
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p' (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ψ true 1 := by
  have h := c.hyp
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  set W₁ := conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p (a + 4))) ⊔ Vh with hW₁
  set W₂ := conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p' (a + 4))) ⊔ Vh with hW₂
  set Wh := whv h (p a) (p (a + 2)) with hWh
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa1 : p' (a + 1) = p (a + 1) := hpp' (a + 1) (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) (by omega)
  have hpa4 : p' (a - 4) = p (a - 4) := hpp' (a - 4) (by omega)
  have h₁ := c.mid_isSum h14 hSQ hZV hQ4 hp ha h24 haN hψs hψ hT
  have key : ∀ (ψ' : ↥(stab (puAmalgam h.le) (p' a)) →* ↥(StatedSL 3 F)),
      Function.Surjective ψ' →
      IsSumOfNaturalModulesVia (stab _ (p' a)) (Uloc h.le L (p' a)) ⊥ ψ' false 1 →
      natImage ψ' (Qv (puAmalgam h.le) (p' (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0 →
      IsSumOfNaturalModulesVia (stab _ (p' a))
        (conjCl (stab (puAmalgam h.le) (p' a)) (ZM _ (p' (a + 4))) ⊔
          (Vcirc h.le L (p' a) ⊔ ZM _ (p' a))) (Vcirc h.le L (p' a) ⊔ ZM _ (p' a)) ψ' true 1 :=
    fun ψ' h1 h2 h3 => c.mid_isSum h14 hSQ hZV hQ4 hp' ha h24 haN h1 h2 h3
  rw [hpa, hpa1] at key
  have h₂ := key ψ hψs hψ hT
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hW₁Wh : W₁ ≤ Wh :=
    sup_le (conjCl_le_of_le_normalizer (c.zm_le_whv_right hZV hp ha (by omega) (by omega)) hKWh)
      hVhWh
  have hZ'Wh : ZM (puAmalgam h.le) (p' (a + 4)) ≤ Wh := by
    have := c.zm_le_whv_right hZV hp' ha (by omega) (by omega)
    rwa [hpa, hpa2] at this
  have hW₂Wh : W₂ ≤ Wh := sup_le (conjCl_le_of_le_normalizer hZ'Wh hKWh) hVhWh
  have hsup : W₁ ⊔ W₂ = Wh :=
    le_antisymm (sup_le hW₁Wh hW₂Wh) (c.whv_le_sup_of_branch hZV hp ha h24 haN hp' hpp' hU1 hU3)
  refine ⟨hsup, ?_, h₁, h₂⟩
  have hKVh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKW₁ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (W₁ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKVh
  have hKW₂ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (W₂ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKVh
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  by_contra hcon
  obtain ⟨x, hx, hxV⟩ := Set.not_subset.mp hcon
  have hW12 : W₁ ≤ W₂ := by
    intro v hv
    obtain ⟨w, hw, -, hwv⟩ := (NatSec.ofIsSum h₁).exists_inv_mul_mem_of_invariant hψs
      (fun l y hy => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hKW₁ l.2) y).mp (Subgroup.mem_inf.mp hy).1,
          (Subgroup.mem_normalizer_iff.mp (hKW₂ l.2) y).mp (Subgroup.mem_inf.mp hy).2⟩)
      hx (Subgroup.mem_inf.mp hx).1 hxV hv
    have e : v = w * (w⁻¹ * v) := by group
    rw [e]
    exact W₂.mul_mem (Subgroup.mem_inf.mp hw).2 (le_sup_right (a := conjCl _ _) hwv)
  have hW₂Q : W₂ ≤ Qv (puAmalgam h.le) (p' (a + 4)) := by
    refine sup_le (iSup₂_le fun g hg => ?_) ?_
    · rw [← zm_smul]
      have := hQ4 p' N hp' a ha h24 haN g (by rw [hpa]; exact hg)
      exact this
    · refine (c.vhat_le_vv hα).trans (vi_le_qv _ ?_)
      rw [← hpa, hp'.dist_eq' (by omega) (by omega), c.b8]; omega
  have hWhQ : Wh ≤ Qv (puAmalgam h.le) (p' (a + 4)) := by
    rw [← hsup, sup_eq_right.mpr hW12]
    exact hW₂Q
  have hZ := c.zm_le_whv_left hZV hp ha (by omega) (by omega)
  have ha4 : Even (a - 4) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hcrit := c.isCritical_of_isGoodPath hp' ha4 (show a - 4 + 8 ≤ N by omega)
  rw [hpa4, show a - 4 + 8 = a + 4 by omega] at hcrit
  exact hcrit.2.2 (hZ.trans hWhQ)

theorem isSum_whv (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h24 : 24 ≤ a) (haN : a + 24 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) (p (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    IsSumOfNaturalModulesVia (stab _ (p a)) (whv c.hyp (p a) (p (a + 2)))
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ψ true 2 := by
  have h := c.hyp
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  obtain ⟨hsup, hinf, h₁, h₂⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha h24 haN hp' hpp' hU1 hU3 hψs hψ hT
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hWK : whv h (p a) (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
    S4A.conjCl_le_of_le (((c.vhat_le_vv (c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega)
      (ha.add even_two))).trans (vi_le_qv _ (by
        rw [tdist_comm, hp.dist_eq' (by omega) (by omega), c.b8]; omega))).trans
      (qv_le_stab _ _))
  refine S46.isSumOfNaturalModulesVia_two h₁ h₂ (S4A.le_normalizer_conjCl _ _)
    (hWK.trans h₁.1) (hWK.trans h₂.1) hinf hsup

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
