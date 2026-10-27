module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDynT
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDynA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSp4)

@[expose] def FinGraphOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → (IsAlt ↥L 6 ∨ IsSp4 ↥L 2) →
    Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
    ∀ a : Y, orderOf a = 2 → ¬ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x}

private lemma w183b5_mulAut_conj_conj {X : Type} [Group X] (y : MulAut X) (x : X) :
    y * MulAut.conj x * y⁻¹ = MulAut.conj (y x) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulAut.apply_inv_self]

private lemma w183b5_conj_injective {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro x y hxy
  have h1 : MulAut.conj (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hc : x * y⁻¹ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun f : MulAut X => f z) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    have hz' : (x * y⁻¹) * z = z * (x * y⁻¹) := by
      have := congrArg (fun w : X => w * (x * y⁻¹)) hz
      simpa [mul_assoc] using this
    exact hz'.symm
  rw [hZ] at hc
  exact eq_of_mul_inv_eq_one (Subgroup.mem_bot.mp hc)

private lemma w183b5_alpha_eq_one_of_mem_K {G : Type} [Group G] {K H L : Subgroup G}
    (hL : IsComponentModN K H L) {X : Type} [Group X] (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K)
    (α : ↥(H ⊓ Subgroup.normalizer (L : Set G)) →* MulAut X)
    (hα : ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l l' : ↥L),
      (n : G) * (l : G) * (n : G)⁻¹ = (l' : G) → α n (φ l) = φ l')
    (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (hn : (n : G) ∈ K) :
    α n = 1 := by
  have hKL : K ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have hKN : (K.subgroupOf H).Normal := hL.1
  have hKconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    have hkH : k ∈ H := hLH (hKL hk)
    have hkN : (⟨k, hkH⟩ : ↥H) ∈ K.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact hk
    have hconj := hKN.conj_mem (⟨k, hkH⟩ : ↥H) hkN (⟨h, hh⟩ : ↥H)
    simpa [Subgroup.mem_subgroupOf] using hconj
  ext x
  obtain ⟨l, rfl⟩ := hφs x
  have hnl : (n : G) * (l : G) * (n : G)⁻¹ ∈ L :=
    (Subgroup.mem_set_normalizer_iff.mp n.2.2 (l : G)).mp l.2
  rw [hα n l ⟨(n : G) * (l : G) * (n : G)⁻¹, hnl⟩ rfl]
  have hker : ((⟨(n : G) * (l : G) * (n : G)⁻¹, hnl⟩ * l⁻¹ : ↥L) : G) ∈ K := by
    show (n : G) * (l : G) * (n : G)⁻¹ * (l : G)⁻¹ ∈ K
    have hconj : (l : G) * (n : G)⁻¹ * (l : G)⁻¹ ∈ K :=
      hKconj (l : G) (hLH l.2) (n : G)⁻¹ (K.inv_mem hn)
    have hmul : (n : G) * ((l : G) * (n : G)⁻¹ * (l : G)⁻¹) ∈ K := K.mul_mem hn hconj
    rwa [show (n : G) * (l : G) * (n : G)⁻¹ * (l : G)⁻¹ =
      (n : G) * ((l : G) * (n : G)⁻¹ * (l : G)⁻¹) from by group]
  have hphi : φ (⟨(n : G) * (l : G) * (n : G)⁻¹, hnl⟩ * l⁻¹) = 1 := (hφk _).mpr hker
  rw [map_mul, map_inv] at hphi
  simpa using eq_of_mul_inv_eq_one hphi

theorem false_of_normalizing_class (hGraph : FinGraphOdd) {G : Type} [Group G] [Finite G]
    {K H L : Subgroup G} (hL : IsComponentModN K H L) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnc : ∃ u v : X, u * v ≠ v * u) (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K)
    (hX : IsAlt X 6 ∨ IsSp4 X 2) {t : G} (htH : t ∈ H)
    (hDyn : ActsOnDynkinMod K L t) {d : G} (hdH : d ∈ H)
    (hdn : d ∈ Subgroup.normalizer (L : Set G)) (hd2 : d ^ 2 ∈ K)
    (hnt : ∃ l ∈ L, d * l * d⁻¹ * l⁻¹ ∉ K)
    (hOT : ∀ y ∈ H, ∀ y' ∈ H, ∃ m : ℕ, 0 < m ∧ (m ∣ 2 ∨ Odd m) ∧
      ((y * d * y⁻¹) * (y' * d * y'⁻¹)) ^ m ∈ K) : False := by
  classical
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hnc
      have hu : u ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top u
      exact huv ((Subgroup.mem_center_iff.mp hu v).symm)
  obtain ⟨α, hα⟩ := exists_autAction hL φ hφs hφk
  have hKL : K ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have hKtriv : ∀ n : ↥(H ⊓ Subgroup.normalizer (L : Set G)), (n : G) ∈ K → α n = 1 :=
    fun n hn => w183b5_alpha_eq_one_of_mem_K hL φ hφs hφk α hα n hn
  let gal : ↥(H ⊓ Subgroup.normalizer (L : Set G)) :=
    ⟨d, Subgroup.mem_inf.mpr ⟨hdH, hdn⟩⟩
  let L' : Subgroup ↥α.range :=
    ((MulAut.conj : X →* MulAut X).range).subgroupOf α.range
  let a : ↥α.range := ⟨α gal, MonoidHom.mem_range.mpr ⟨gal, rfl⟩⟩
  let τ : ↥α.range :=
    ⟨α ⟨t, Subgroup.mem_inf.mpr ⟨htH, hDyn.1⟩⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  have hconj_le : (MulAut.conj : X →* MulAut X).range ≤ α.range := by
    rintro y ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := hφs x
    refine ⟨⟨l, Subgroup.mem_inf.mpr ⟨hLH l.2, Subgroup.le_normalizer l.2⟩⟩, ?_⟩
    ext z
    obtain ⟨l₀, rfl⟩ := hφs z
    rw [hα ⟨l, Subgroup.mem_inf.mpr ⟨hLH l.2, Subgroup.le_normalizer l.2⟩⟩ l₀
        (l * l₀ * l⁻¹) rfl]
    simp only [map_mul, map_inv, MulAut.conj_apply]
  have hconjInj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    w183b5_conj_injective hZ
  have eL' : X ≃* ↥L' :=
    (MonoidHom.ofInjective (f := (MulAut.conj : X →* MulAut X)) hconjInj).trans
      (Subgroup.subgroupOfEquivOfLe hconj_le).symm
  have hIso : IsAlt ↥L' 6 ∨ IsSp4 ↥L' 2 := by
    rcases hX with h | h
    · exact Or.inl ⟨eL'.symm.trans h.some⟩
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eL' h)
  have hNorm : L'.Normal := by
    change (((MulAut.conj : X →* MulAut X).range).subgroupOf α.range).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hconj_le]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hy
      exact MonoidHom.mem_range.mpr
        ⟨α n x, (w183b5_mulAut_conj_conj (α n) x).symm⟩
    · rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hy
      have hz : z = (α n)⁻¹ * MulAut.conj x * (α n) := by
        rw [hx, ← hn]
        group
      refine MonoidHom.mem_range.mpr ⟨(α n)⁻¹ x, ?_⟩
      rw [← w183b5_mulAut_conj_conj (α n)⁻¹ x, hz, inv_inv]
  have hCent : Subgroup.centralizer (L' : Set ↥α.range) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext x
    have hcomm : ∀ z : X, (σ : MulAut X) * MulAut.conj z = MulAut.conj z * (σ : MulAut X) := by
      intro z
      have hz : (⟨MulAut.conj z, hconj_le ⟨z, rfl⟩⟩ : ↥α.range) ∈ L' := by
        change (⟨MulAut.conj z, hconj_le ⟨z, rfl⟩⟩ : ↥α.range) ∈
          ((MulAut.conj : X →* MulAut X).range).subgroupOf α.range
        rw [Subgroup.mem_subgroupOf]
        exact ⟨z, rfl⟩
      exact (congrArg (fun w : ↥α.range => (w : MulAut X))
        ((Subgroup.mem_centralizer_iff.mp hσ) _ hz)).symm
    have hconj : MulAut.conj ((σ : MulAut X) x) = MulAut.conj x := by
      rw [← w183b5_mulAut_conj_conj (σ : MulAut X) x, hcomm x]
      group
    simpa using hconjInj hconj
  have hTau : ∃ τ' : ↥α.range, ActsOnDynkinMod (⊥ : Subgroup ↥α.range) L' τ' :=
    ⟨τ, actsOnDynkinMod_bot_of_autAction hL hZ φ hφs hφk α hα htH hDyn⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change (α gal) ^ 2 = (1 : MulAut X)
    rw [← map_pow]
    exact hKtriv (gal ^ 2) (by rw [Subgroup.coe_pow]; change d ^ 2 ∈ K; exact hd2)
  have hane : a ≠ 1 := by
    intro h
    have hval : (a : MulAut X) = 1 := by
      simpa using congrArg (fun y : ↥α.range => (y : MulAut X)) h
    obtain ⟨l, hlL, hlK⟩ := hnt
    have hnl : d * l * d⁻¹ ∈ L := (Subgroup.mem_set_normalizer_iff.mp hdn l).mp hlL
    have h1 : (a : MulAut X) (φ ⟨l, hlL⟩) = φ ⟨l, hlL⟩ := by
      rw [hval]; rfl
    have h2 : (a : MulAut X) (φ ⟨l, hlL⟩) = φ ⟨d * l * d⁻¹, hnl⟩ := by
      change α gal (φ ⟨l, hlL⟩) = φ ⟨d * l * d⁻¹, hnl⟩
      exact hα gal ⟨l, hlL⟩ ⟨d * l * d⁻¹, hnl⟩ rfl
    have heq : φ ⟨d * l * d⁻¹, hnl⟩ = φ ⟨l, hlL⟩ := h2 ▸ h1
    have hker : ((⟨d * l * d⁻¹, hnl⟩ * ⟨l, hlL⟩⁻¹ : ↥L) : G) ∈ K := by
      apply (hφk _).mp
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    exact hlK (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hker)
  have haord : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hane
    · exact h2
  have hOTclass : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : ↥α.range | IsConj a x} := by
    constructor
    · intro x hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      rw [← hc]
      exact (SemiconjBy.orderOf_eq c (by
        show c * a = (c * a * c⁻¹) * c
        group)).symm.trans haord
    · intro x hx x' hx'
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      obtain ⟨c', hc'⟩ := isConj_iff.mp hx'
      obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp c.2
      obtain ⟨n', hn'⟩ := MonoidHom.mem_range.mp c'.2
      have hc_eq : c = ⟨α n, MonoidHom.mem_range.mpr ⟨n, rfl⟩⟩ := Subtype.ext hn.symm
      have hc'_eq : c' = ⟨α n', MonoidHom.mem_range.mpr ⟨n', rfl⟩⟩ := Subtype.ext hn'.symm
      rw [← hc, ← hc', hc_eq, hc'_eq]
      obtain ⟨m, _hmpos, hmdiv, hmK⟩ := hOT (n : G) n.2.1 (n' : G) n'.2.1
      let w : ↥(H ⊓ Subgroup.normalizer (L : Set G)) := (n * gal * n⁻¹) * (n' * gal * n'⁻¹)
      have hwK : ((w ^ m : ↥(H ⊓ Subgroup.normalizer (L : Set G))) : G) ∈ K := by
        rw [Subgroup.coe_pow]
        have hwval : (w : G) =
            ((n : G) * d * (n : G)⁻¹) * ((n' : G) * d * (n' : G)⁻¹) := by
          dsimp only [w, gal]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hwval]
        exact hmK
      let T : ↥α.range :=
        (⟨α n, MonoidHom.mem_range.mpr ⟨n, rfl⟩⟩ * a *
            (⟨α n, MonoidHom.mem_range.mpr ⟨n, rfl⟩⟩)⁻¹) *
          (⟨α n', MonoidHom.mem_range.mpr ⟨n', rfl⟩⟩ * a *
            (⟨α n', MonoidHom.mem_range.mpr ⟨n', rfl⟩⟩)⁻¹)
      change orderOf T ∣ 2 ∨ Odd (orderOf T)
      have hprod : T = ⟨α w, MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        change (α n * α gal * (α n)⁻¹) * (α n' * α gal * (α n')⁻¹) = α w
        rw [show w = (n * gal * n⁻¹) * (n' * gal * n'⁻¹) from rfl]
        simp only [map_mul, map_inv]
      have hdvd : orderOf T ∣ m := by
        rw [orderOf_dvd_iff_pow_eq_one, hprod]
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        change (α w) ^ m = (1 : MulAut X)
        rw [← map_pow]
        exact hKtriv (w ^ m) hwK
      rcases hmdiv with h2 | hodd
      · exact Or.inl (hdvd.trans h2)
      · exact Or.inr (hodd.of_dvd_nat hdvd)
  exact (hGraph ↥α.range L' hNorm hIso hCent hTau a haord) hOTclass

end CFSG.LocalAnalysis.WeakClosure81

end
