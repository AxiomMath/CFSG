module

public import CFSG.LocalAnalysis.StandardType.GGTorusInducedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

noncomputable def ggInducedAutOf {L' R : Type} [Group L'] [Group R] (ψ : L' →* R) (τ : MulAut L') :
    MulAut R := by
  classical
  exact if h : ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (τ l) then h.choose else 1

theorem ggInducedAutOf_eq {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {τ : MulAut L'} {φ : MulAut R} (hφ : ∀ l, φ (ψ l) = ψ (τ l)) :
    ggInducedAutOf ψ τ = φ := by
  classical
  have h : ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (τ l) := ⟨φ, hφ⟩
  unfold ggInducedAutOf
  rw [dif_pos h]
  exact TypeA.induced_unique ψ hψ h.choose_spec hφ

theorem ggInducedAutOf_conj {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (g : L') :
    ggInducedAutOf ψ (MulAut.conj g) = MulAut.conj (ψ g) :=
  ggInducedAutOf_eq hψ fun l => by simp only [MulAut.conj_apply, map_mul, map_inv]

variable {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}

theorem GGTorusTorWit.exists_liftTwo {L' R : Type} [Group L'] [Group R] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (h2 : IsPGroup 2 ψ.ker)
    (hperf : commutator L' = ⊤) (hZ : Subgroup.center R = ⊥) (hm : Odd m)
    {A : Subgroup (MulAut L')} (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {Ab : Subgroup (MulAut R)} (hAb : Ab = TypeA.inducedSub ψ A)
    (w : GGTorusTorWit m N R Ab) (hw : w.Holds C M)
    (hT : ∀ τ ∈ w.T, ∃ s ∈ w.Tsc, τ = MulAut.conj s) (hTsc : Odd (Nat.card w.Tsc)) :
    ∃ w' : GGTorusTorWit m N L' A, w'.Holds C M ∧ (∀ k, ψ (w'.n k) = w.n k) ∧
      (∀ k ζ, ψ (w'.cor k ζ) = w.cor k ζ) ∧ w'.Tsc.map ψ = w.Tsc := by
  classical
  subst hAb
  obtain ⟨hTc, hAT, hcorT, hαhom, hcorinj, hcorcomm, hTfix, hpair, hnT, hnel, hsep, hαA, hinn,
    -, ⟨hcent, hTscfix, hTscm⟩, haut, ⟨e, he⟩⟩ := hw
  have : Finite R := Finite.of_surjective ψ hψ
  have hconjR : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hcenker : ∀ z ∈ Subgroup.center L', ψ z = 1 := by
    intro z hz
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hfib : ∀ x y : L', ψ x = ψ y → MulAut.conj x = MulAut.conj y := by
    intro x y h
    have hz : x⁻¹ * y ∈ Subgroup.center L' :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
    ext l
    simp only [MulAut.conj_apply]
    have hc := Subgroup.mem_center_iff.mp hz l
    calc x * l * x⁻¹ = x * (l * (x⁻¹ * y)) * (x⁻¹ * y)⁻¹ * x⁻¹ := by group
      _ = x * ((x⁻¹ * y) * l) * (x⁻¹ * y)⁻¹ * x⁻¹ := by rw [hc]
      _ = y * l * y⁻¹ := by group
  have hconjind : ∀ g l : L', MulAut.conj (ψ g) (ψ l) = ψ (MulAut.conj g l) := by
    intro g l
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨lam, hlam⟩ := CFSG.Wielandt.exists_lift_of_surjective_isPGroup_ker_of_coprime ψ hψ h2
    (Nat.Coprime.symm (Nat.coprime_two_right.mpr hTsc)) w.Tsc.subtype
  have hlam' : ∀ s : w.Tsc, ψ (lam s) = s := fun s => congrArg (fun f => f s) hlam
  have hlampow : ∀ s : w.Tsc, lam s ^ Nat.card w.Tsc = 1 := fun s => by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hcorTsc : ∀ k ζ, w.cor k ζ ∈ w.Tsc := by
    intro k ζ
    have h := hcent (w.cor k ζ) fun a ha => by
      have hfix := hTfix a (hAT ha) k ζ
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]
    rwa [hZ, sup_bot_eq] at h
  let corR : Fin N → Multiplicative (ZMod m) →* w.Tsc := fun k =>
    (w.cor k).codRestrict w.Tsc (hcorTsc k)
  let cor' : Fin N → Multiplicative (ZMod m) →* L' := fun k => lam.comp (corR k)
  have hcor' : ∀ k ζ, ψ (cor' k ζ) = w.cor k ζ := fun k ζ => hlam' (corR k ζ)
  have hzm : ∀ ζ : Multiplicative (ZMod m), ζ ^ m = 1 := fun ζ => by
    obtain ⟨y, rfl⟩ : ∃ y : ZMod m, Multiplicative.ofAdd y = ζ := ⟨Multiplicative.toAdd ζ, rfl⟩
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hcor'm : ∀ k ζ, cor' k ζ ^ m = 1 := fun k ζ => by rw [← map_pow, hzm, map_one]
  choose n' hn' using fun k => hψ (w.n k)
  have hnN : ∀ k, MulAut.conj (n' k) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun k => inducedSub_conj_mem_normalizer hker hperf hA (hn' k) (w.hn k)
  let T' : Subgroup (MulAut L') :=
    (Subgroup.comap ((MulAut.conj : R →* MulAut R).comp ψ) w.T).map MulAut.conj
  let α' : Fin N → MulAut L' → Multiplicative (ZMod m) := fun k τ => w.α k (ggInducedAutOf ψ τ)
  have hα'conj : ∀ k (s : w.Tsc), α' k (MulAut.conj (lam s)) = w.α k (MulAut.conj (s : R)) :=
    fun k s => by simp only [α', ggInducedAutOf_conj hψ, hlam']
  have hrep : ∀ τ ∈ T', ∃ s : w.Tsc, MulAut.conj (s : R) ∈ w.T ∧ τ = MulAut.conj (lam s) := by
    rintro τ ⟨l, hl, rfl⟩
    have hl' : MulAut.conj (ψ l) ∈ w.T := hl
    obtain ⟨s, hs, hsl⟩ := hT _ hl'
    refine ⟨⟨s, hs⟩, hsl ▸ hl', hfib _ _ ?_⟩
    rw [hlam']
    exact hconjR hsl
  have hmemT' : ∀ s : w.Tsc, MulAut.conj (s : R) ∈ w.T → MulAut.conj (lam s) ∈ T' :=
    fun s hs => ⟨lam s, show MulAut.conj (ψ (lam s)) ∈ w.T by rw [hlam']; exact hs, rfl⟩
  have h1 : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := hrep x hx
    obtain ⟨s', hs', rfl⟩ := hrep y hy
    have hss : s * s' = s' * s := Subtype.ext (hconjR (by
      simp only [Subgroup.coe_mul, map_mul]
      exact hTc _ hs _ hs'))
    rw [← map_mul, ← map_mul, hss, map_mul, map_mul]
  have h2' : A ≤ T' := by
    intro a ha
    obtain ⟨φ, hφ⟩ := hA a ha
    have hφAb : φ ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hφ⟩
    obtain ⟨s, hs, rfl⟩ := hT φ (hAT hφAb)
    have hal : a = MulAut.conj (lam ⟨s, hs⟩) :=
      TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by
        rw [← hφ, ← hconjind, hlam']
    rw [hal]
    exact hmemT' ⟨s, hs⟩ (hAT hφAb)
  have h3 : ∀ k ζ, MulAut.conj (cor' k ζ) ∈ T' := fun k ζ =>
    ⟨cor' k ζ, show MulAut.conj (ψ (cor' k ζ)) ∈ w.T by rw [hcor']; exact hcorT k ζ, rfl⟩
  have h4 : ∀ j, ∀ x ∈ T', ∀ y ∈ T', α' j (x * y) = α' j x * α' j y := by
    intro j x hx y hy
    obtain ⟨s, hs, rfl⟩ := hrep x hx
    obtain ⟨s', hs', rfl⟩ := hrep y hy
    rw [← map_mul, ← map_mul lam, hα'conj, hα'conj, hα'conj, Subgroup.coe_mul, map_mul]
    exact hαhom j _ hs _ hs'
  have h5 : ∀ k, Function.Injective (cor' k) := fun k x y h =>
    hcorinj k (by rw [← hcor', ← hcor', h])
  have h6 : ∀ j k ζ ξ, Commute (cor' j ζ) (cor' k ξ) := by
    intro j k ζ ξ
    have hc : corR j ζ * corR k ξ = corR k ξ * corR j ζ := Subtype.ext (hcorcomm j k ζ ξ).eq
    show lam (corR j ζ) * lam (corR k ξ) = lam (corR k ξ) * lam (corR j ζ)
    rw [← map_mul, ← map_mul, hc]
  have hscor : ∀ s : w.Tsc, MulAut.conj (s : R) ∈ w.T → ∀ k ζ,
      s * corR k ζ * s⁻¹ = corR k ζ := fun s hs k ζ => Subtype.ext (by
    have hfix := hTfix _ hs k ζ
    rw [MulAut.conj_apply] at hfix
    exact hfix)
  have h7 : ∀ τ ∈ T', ∀ k ζ, τ (cor' k ζ) = cor' k ζ := by
    intro τ hτ k ζ
    obtain ⟨s, hs, rfl⟩ := hrep τ hτ
    show lam s * lam (corR k ζ) * (lam s)⁻¹ = lam (corR k ζ)
    rw [← map_inv, ← map_mul, ← map_mul, hscor s hs k ζ]
  have h8 : ∀ i j ζ, α' i (MulAut.conj (cor' j ζ)) = ζ ^ C i j := by
    intro i j ζ
    simp only [α', ggInducedAutOf_conj hψ, hcor']
    exact hpair i j ζ
  have hnR : ∀ k (s : w.Tsc), MulAut.conj (s : R) ∈ w.T →
      w.n k * (s : R) * (w.n k)⁻¹ = s * (w.cor k (w.α k (MulAut.conj (s : R))))⁻¹ := by
    intro k s hs
    apply hconjR
    have h := hnT k _ hs
    simp only [map_mul, map_inv]
    exact h
  have h9 : ∀ k, ∀ τ ∈ T', MulAut.conj (n' k) * τ * (MulAut.conj (n' k))⁻¹ =
      τ * (MulAut.conj (cor' k (α' k τ)))⁻¹ := by
    intro k τ hτ
    obtain ⟨s, hs, rfl⟩ := hrep τ hτ
    rw [hα'conj, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
    apply hfib
    simp only [map_mul, map_inv, hn', hlam', hcor']
    exact hnR k s hs
  have h10 : ∀ k, ∀ τ ∈ T', n' k * (τ (n' k))⁻¹ = (cor' k (α' k τ))⁻¹ := by
    intro k τ hτ
    obtain ⟨s, hs, rfl⟩ := hrep τ hτ
    rw [hα'conj]
    set c := cor' k (w.α k (MulAut.conj (s : R))) with hc
    have hsc : lam s * c = c * lam s := by
      have h := hscor s hs k (w.α k (MulAut.conj (s : R)))
      have h' : s * corR k (w.α k (MulAut.conj (s : R))) =
          corR k (w.α k (MulAut.conj (s : R))) * s := by
        calc s * corR k (w.α k (MulAut.conj (s : R)))
            = s * corR k (w.α k (MulAut.conj (s : R))) * s⁻¹ * s := by group
          _ = corR k (w.α k (MulAut.conj (s : R))) * s := by rw [h]
      show lam s * lam (corR k _) = lam (corR k _) * lam s
      rw [← map_mul, ← map_mul, h']
    have hodd : Odd (Nat.card w.Tsc * m) := hTsc.mul hm
    have hxy : n' k * lam s * (n' k)⁻¹ = lam s * c⁻¹ := by
      refine eq_of_map_eq_of_pow_odd hker h2 hodd ?_ ?_ ?_
      · simp only [map_mul, map_inv, hn', hlam', hc, hcor']
        exact hnR k s hs
      · rw [conj_pow, pow_mul, hlampow, one_pow, mul_one, mul_inv_cancel]
      · rw [(Commute.inv_right (show Commute (lam s) c from hsc)).mul_pow, pow_mul, hlampow,
          one_pow, one_mul, inv_pow, mul_comm, pow_mul, hcor'm, one_pow, inv_one]
    simp only [MulAut.conj_apply]
    calc n' k * (lam s * n' k * (lam s)⁻¹)⁻¹ = (n' k * lam s * (n' k)⁻¹) * (lam s)⁻¹ := by group
      _ = lam s * c⁻¹ * (lam s)⁻¹ := by rw [hxy]
      _ = c⁻¹ := by
          rw [show lam s * c⁻¹ = c⁻¹ * lam s from
            (Commute.inv_right (show Commute (lam s) c from hsc)).eq]
          group
  have h11 : ∀ τ ∈ T', (∀ k, α' k τ = 1) → τ = 1 := by
    intro τ hτ h
    obtain ⟨s, hs, rfl⟩ := hrep τ hτ
    have h1 : MulAut.conj (s : R) = 1 := hsep _ hs fun k => by rw [← hα'conj]; exact h k
    have hs1 : s = 1 := Subtype.ext (hconjR (by rw [h1, Subgroup.coe_one, map_one]))
    rw [hs1, map_one, map_one]
  have h12 : ∀ k, ∃ a ∈ A, α' k a ≠ 1 := by
    intro k
    obtain ⟨φ, hφAb, hφ⟩ := hαA k
    obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφAb
    refine ⟨a, ha, ?_⟩
    simp only [α', ggInducedAutOf_eq hψ hφa]
    exact hφ
  have hcorle : (⨆ k, (w.cor k).range) ≤ w.Tsc :=
    iSup_le fun k => by rintro _ ⟨ζ, rfl⟩; exact hcorTsc k ζ
  have hiSup : ∀ t : w.Tsc, (t : R) ∈ ⨆ k, (w.cor k).range → lam t ∈ ⨆ k, (cor' k).range := by
    intro t ht
    have e1 : (⨆ k, (w.cor k).range) = (⨆ k, (corR k).range).map w.Tsc.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      funext k
      rw [← MonoidHom.range_comp]
      rfl
    rw [e1] at ht
    obtain ⟨t', ht', heq⟩ := ht
    have htt : t' = t := Subtype.ext heq
    have e2 : (⨆ k, (corR k).range).map lam = ⨆ k, (cor' k).range := by
      rw [Subgroup.map_iSup]
      congr 1
      funext k
      rw [← MonoidHom.range_comp]
    rw [← e2, ← htt]
    exact Subgroup.mem_map_of_mem lam ht'
  have h13 : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range →
      ∃ t ∈ ⨆ k, (cor' k).range, a = MulAut.conj t := by
    rintro a ha ⟨l, rfl⟩
    have hφAb : MulAut.conj (ψ l) ∈ TypeA.inducedSub ψ A :=
      TypeA.mem_inducedSub.mpr ⟨_, ha, hconjind l⟩
    obtain ⟨t, ht, heq⟩ := hinn _ hφAb ⟨ψ l, rfl⟩
    refine ⟨lam ⟨t, hcorle ht⟩, hiSup _ ht, hfib _ _ ?_⟩
    rw [hlam']
    exact hconjR heq
  have h14 : ∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ lam.range := by
    intro z hz hzo
    have hz1 : z = 1 := eq_one_of_isPGroup_two_of_pow_odd h2 hzo
      (show z ∈ ψ.ker from hcenker z hz) (pow_orderOf_eq_one z)
    rw [hz1]
    exact one_mem _
  have h15a : ∀ g : L', (∀ a ∈ A, MulAut.conj g * a = a * MulAut.conj g) →
      g ∈ lam.range ⊔ Subgroup.center L' := by
    intro g hg
    have hgR : ψ g ∈ w.Tsc := by
      have h := hcent (ψ g) fun φ hφ => by
        obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
        refine TypeA.induced_unique ψ hψ (a := MulAut.conj g * a) (fun l => ?_) (fun l => ?_)
        · rw [MulAut.mul_apply, hφa, hconjind, MulAut.mul_apply]
        · rw [MulAut.mul_apply, hconjind, hφa, hg a ha, MulAut.mul_apply]
      rwa [hZ, sup_bot_eq] at h
    have hk : (lam ⟨ψ g, hgR⟩)⁻¹ * g ∈ Subgroup.center L' :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hlam', inv_mul_cancel])
    have hg' : g = lam ⟨ψ g, hgR⟩ * ((lam ⟨ψ g, hgR⟩)⁻¹ * g) := by group
    rw [hg']
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ hk
  have h15b : ∀ τ ∈ T', ∀ t ∈ lam.range, τ t = t := by
    rintro τ hτ _ ⟨s', rfl⟩
    obtain ⟨s, hs, rfl⟩ := hrep τ hτ
    have hfix := hTscfix _ hs s' s'.2
    have hss : s * s' * s⁻¹ = s' := Subtype.ext (by
      rw [MulAut.conj_apply] at hfix
      exact hfix)
    show lam s * lam s' * (lam s)⁻¹ = lam s'
    rw [← map_inv, ← map_mul, ← map_mul, hss]
  have h15c : ∀ t ∈ lam.range, t ^ m = 1 → t ∈ ⨆ k, (cor' k).range := by
    rintro _ ⟨s', rfl⟩ hm'
    have hs'm : (s' : R) ^ m = 1 := by rw [← hlam', ← map_pow, hm', map_one]
    exact hiSup s' (hTscm _ s'.2 hs'm)
  set Φ := MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hA).symm with hΦ
  have hmap := map_ggAutomizer_inducedSub hψ hker hperf hA
  have hgens : ∀ k, Φ (ggConjAut (TypeA.inducedSub ψ A) (w.hn k)) = ggConjAut A (hnN k) := by
    intro k
    have key : ∀ (x : R) (hx : MulAut.conj x ∈
        Subgroup.normalizer ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R))),
        x = ψ (n' k) → Φ (ggConjAut (TypeA.inducedSub ψ A) hx) = ggConjAut A (hnN k) := by
      rintro x hx rfl
      exact mulAutCongr_ggConjAut hψ hker hperf hA (hnN k) hx
    exact key _ _ (hn' k).symm
  have h16 : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range fun k => ggConjAut A (hnN k)) := by
    rw [← hmap, haut, MonoidHom.map_closure, ← Set.range_comp]
    have hfun : (⇑Φ.toMonoidHom ∘ fun k => ggConjAut (TypeA.inducedSub ψ A) (w.hn k)) =
        fun k => ggConjAut A (hnN k) := funext fun k => hgens k
    rw [hfun]
  have h17 : ∃ e' : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
      ∀ k, (e' (M.simple k) : MulAut ↥A) = ggConjAut A (hnN k) := by
    refine ⟨e.trans ((Φ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)), fun k => ?_⟩
    change Φ ((e (M.simple k) : MulAut ↥(TypeA.inducedSub ψ A))) = ggConjAut A (hnN k)
    rw [he k]
    exact hgens k
  refine ⟨⟨T', α', cor', n', hnN, lam.range⟩, ⟨h1, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, ⟨h15a, h15b, h15c⟩, h16, h17⟩, hn', hcor', ?_⟩
  rw [← MonoidHom.range_comp, hlam, Subgroup.range_subtype]

theorem ggTorusTorData_liftTwo {L' R : Type} [Group L'] [Group R] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (h2 : IsPGroup 2 ψ.ker)
    (hperf : commutator L' = ⊤) (hZ : Subgroup.center R = ⊥) (hm : Odd m)
    {A : Subgroup (MulAut L')} (hA : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {Ab : Subgroup (MulAut R)} (hAb : Ab = TypeA.inducedSub ψ A)
    (w : GGTorusTorWit m N R Ab) (hw : w.Holds C M)
    (hT : ∀ τ ∈ w.T, ∃ s ∈ w.Tsc, τ = MulAut.conj s) (hTsc : Odd (Nat.card w.Tsc)) :
    GGTorusTorData m N C M L' A :=
  (w.exists_liftTwo hψ hker h2 hperf hZ hm hA hAb hw hT hTsc).imp fun _ h => h.1

end CFSG.StandardType

end
