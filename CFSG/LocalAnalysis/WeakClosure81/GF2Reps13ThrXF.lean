module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXFA
public import CFSG.RankThree.S4Free.Stellmacher25
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

structure HAb (A X Q : Subgroup (MulAut W)) (t : MulAut W) (p : ℕ) : Prop where
  hW : ∀ w : W, w * w = 1
  hp : p = 3 ∨ p = 7
  htA : t ∈ A
  ht2 : t ^ 2 = 1
  ht1 : t ≠ 1
  hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  hXe : IsElemAbelian p X
  hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X
  hXO : X ≤ pCoreOf p A
  hQX : Q ≤ X
  hQ1 : Q ≠ ⊥
  hQinv : ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹
  hXgen : X = conjClosure A Q
  hQ7 : p = 7 → Nat.card ↥Q = 7

private theorem w16g_conjClosure_map_conj (A Q : Subgroup (MulAut W)) {a : MulAut W}
    (ha : a ∈ A) :
    conjClosure A (Q.map (MulAut.conj a).toMonoidHom) = conjClosure A Q := by
  unfold conjClosure
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨g, hg, y, hy, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.subset_closure ⟨g * a, A.mul_mem hg ha, q, hq, ?_⟩
    change g * (MulAut.conj a) q * g⁻¹ = g * a * q * (g * a)⁻¹
    rw [MulAut.conj_apply]
    group
  · rw [Subgroup.closure_le]
    rintro x ⟨g, hg, q, hq, rfl⟩
    refine Subgroup.subset_closure
      ⟨g * a⁻¹, A.mul_mem hg (A.inv_mem ha), (MulAut.conj a) q,
        Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    rw [MulAut.conj_apply]
    group

private theorem w16g_rk_commSub_conj (A : Subgroup (MulAut W)) {a t : MulAut W} (ha : a ∈ A) :
    rk ↥(commSub ⊤ (Subgroup.zpowers (a * t * a⁻¹))) =
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  have hs : a * t * a⁻¹ = MulAut.conj a t := (MulAut.conj_apply a t).symm
  have hcomm : commSub ⊤ (Subgroup.zpowers (a * t * a⁻¹)) =
      (commSub ⊤ (Subgroup.zpowers t)).map a.toMonoidHom := by
    have hs_zp : Subgroup.zpowers (a * t * a⁻¹) =
        (Subgroup.zpowers t).map (MulAut.conj a).toMonoidHom := by
      rw [hs]
      simpa using
        (MonoidHom.map_zpowers (f := (MulAut.conj a).toMonoidHom) t).symm
    rw [hs_zp, CFSG.RankThree.S4Free.Stell.map_commSub a ⊤ (Subgroup.zpowers t),
      Subgroup.map_top_of_surjective _ a.surjective]
  rw [hcomm, CFSG.RankThree.S4Free.Stell.rk_map_mulAut]

variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

theorem HAb.conj (h : HAb A X Q t p) {a : MulAut W} (ha : a ∈ A) :
    HAb A X (Q.map (MulAut.conj a).toMonoidHom) (a * t * a⁻¹) p := by
  have hsA : a * t * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha h.htA) (A.inv_mem ha)
  have hs : a * t * a⁻¹ = MulAut.conj a t := (MulAut.conj_apply a t).symm
  refine ⟨h.hW, h.hp, hsA, ?_, ?_, ?_, h.hXe, h.hXA, h.hXO, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, ← map_pow, h.ht2, map_one]
  · intro h1
    rw [hs] at h1
    refine h.ht1 ((MulAut.conj a).injective ?_)
    rw [h1, map_one]
  · rw [w16g_rk_commSub_conj A ha]
    exact h.hrk
  · rintro q' hq'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hq'
    change (MulAut.conj a) q ∈ X
    rw [MulAut.conj_apply]
    exact h.hXA a ha q (h.hQX hq)
  · intro hbot
    exact h.hQ1 ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj a).toMonoidHom) Q
      (fun _ _ h => (MulAut.conj a).injective h)).mp hbot)
  · intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hq'
    change (a * t * a⁻¹) * ((MulAut.conj a) q) * (a * t * a⁻¹)⁻¹ = ((MulAut.conj a) q)⁻¹
    rw [MulAut.conj_apply]
    calc (a * t * a⁻¹) * (a * q * a⁻¹) * (a * t * a⁻¹)⁻¹
        = a * (t * q * t⁻¹) * a⁻¹ := by group
      _ = a * q⁻¹ * a⁻¹ := by rw [h.hQinv q hq]
      _ = (a * q * a⁻¹)⁻¹ := by group
  · rw [w16g_conjClosure_map_conj A Q ha]
    exact h.hXgen
  · intro hp7
    rw [← h.hQ7 hp7]
    exact Subgroup.card_map_of_injective (MulAut.conj a).injective

private theorem w16g_sup_zpowers_eq_of_relIndex {H X : Subgroup (MulAut W)} {ℓ : MulAut W}
    {p : ℕ} (hp : p.Prime) (hHle : H ≤ X) (hHrel : H.relIndex X = p) (hℓX : ℓ ∈ X)
    (hℓnot : ℓ ∉ H) : H ⊔ Subgroup.zpowers ℓ = X := by
  have hle : H ⊔ Subgroup.zpowers ℓ ≤ X := sup_le hHle (Subgroup.zpowers_le.mpr hℓX)
  have h1 := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers ℓ) X le_sup_left hle
  rw [hHrel] at h1
  have hne1 : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ≠ 1 := by
    intro h
    have hle' : H ⊔ Subgroup.zpowers ℓ ≤ H := Subgroup.relIndex_eq_one.mp h
    have hzle : Subgroup.zpowers ℓ ≤ H :=
      le_trans (le_sup_right : Subgroup.zpowers ℓ ≤ H ⊔ Subgroup.zpowers ℓ) hle'
    exact hℓnot (hzle (Subgroup.mem_zpowers ℓ))
  have hdvd : H.relIndex (H ⊔ Subgroup.zpowers ℓ) ∣ p := ⟨_, h1.symm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with hd1 | hdp
  · exact absurd hd1 hne1
  · have he1 : (H ⊔ Subgroup.zpowers ℓ).relIndex X = 1 := by
      have h1' := h1
      rw [hdp] at h1'
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h1')
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp he1)

private theorem w16g_conj_mem_s13KerOn {X : Subgroup (MulAut W)} {U : Subgroup W}
    {s : MulAut W}
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X)
    (hfix : U.map s.toMonoidHom = U) :
    ∀ h ∈ s13KerOn X U, s * h * s⁻¹ ∈ s13KerOn X U := by
  intro h hh
  obtain ⟨hhX, hhcent⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨hsX h hhX, ?_⟩
  rw [mem_centSub] at hhcent ⊢
  intro w hw
  have hw' : s.symm w ∈ U := by
    have hwU : w ∈ U.map s.toMonoidHom := by rw [hfix]; exact hw
    obtain ⟨v, hv, hvv⟩ := Subgroup.mem_map.mp hwU
    rw [← hvv]
    simpa using hv
  show s (h (s.symm w)) = w
  rw [hhcent (s.symm w) hw']
  exact MulEquiv.apply_symm_apply s w

private theorem w16g_inverted_mod_hyperplane {X H : Subgroup (MulAut W)} {s q : MulAut W}
    (hXcomm : ∀ y ∈ X, ∀ z ∈ X, y * z = z * y)
    (hHle : H ≤ X) (hHrel : H.relIndex X = 3) (hqX : q ∈ X) (hqnot : q ∉ H)
    (hqinv : s * q * s⁻¹ = q⁻¹) (hsH : ∀ h ∈ H, s * h * s⁻¹ ∈ H) :
    ∀ x ∈ X, s * x * s⁻¹ * x ∈ H := by
  have hsup : H ⊔ Subgroup.zpowers q = X :=
    w16g_sup_zpowers_eq_of_relIndex (p := 3) (by norm_num) hHle hHrel hqX hqnot
  have hqnorm : Subgroup.zpowers q ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg k hk
    have hgX : g ∈ X := Subgroup.zpowers_le.mpr hqX hg
    have hgk : g * k * g⁻¹ = k := by
      rw [← hXcomm k (hHle hk) g hgX]
      group
    rw [hgk]
    exact hk
  intro x hxX
  rw [← hsup] at hxX
  have hxmem : x ∈ ((H ⊔ Subgroup.zpowers q : Subgroup (MulAut W)) : Set (MulAut W)) := hxX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H (Subgroup.zpowers q) hqnorm] at hxmem
  obtain ⟨h', hh'H, k, hk, hk_eq⟩ := Set.mem_mul.mp hxmem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hk)
  rw [← hk_eq]
  have hconj : s * (h' * q ^ j) * s⁻¹ = (s * h' * s⁻¹) * q ^ (-j) := by
    have h1 : s * q ^ j * s⁻¹ = q ^ (-j) := by
      rw [← conj_zpow, hqinv, inv_zpow']
    calc s * (h' * q ^ j) * s⁻¹ = (s * h' * s⁻¹) * (s * q ^ j * s⁻¹) := by group
      _ = (s * h' * s⁻¹) * q ^ (-j) := by rw [h1]
  have hqh : q ^ (-j) * h' = h' * q ^ (-j) :=
    hXcomm (q ^ (-j)) (X.zpow_mem hqX (-j)) h' (hHle hh'H)
  have hprod : s * (h' * q ^ j) * s⁻¹ * (h' * q ^ j) = (s * h' * s⁻¹) * h' := by
    rw [hconj]
    calc (s * h' * s⁻¹) * q ^ (-j) * (h' * q ^ j)
        = (s * h' * s⁻¹) * (q ^ (-j) * h') * q ^ j := by group
      _ = (s * h' * s⁻¹) * (h' * q ^ (-j)) * q ^ j := by rw [hqh]
      _ = (s * h' * s⁻¹) * h' := by group
  rw [hprod]
  exact H.mul_mem (hsH h' hh'H) hh'H

private theorem w16g_exists_inverted_nontrivial (h : HAb A X Q t p) {a : MulAut W}
    (ha : a ∈ A) {U : Subgroup W} (hU : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) :
    ∃ q ∈ X, (a * t * a⁻¹) * q * (a * t * a⁻¹)⁻¹ = q⁻¹ ∧ q ∉ s13KerOn X U := by
  classical
  obtain ⟨q, hqQ', hqnot⟩ : ∃ q ∈ Q.map (MulAut.conj a).toMonoidHom, q ∉ s13KerOn X U := by
    by_contra hc
    push Not at hc
    refine hU.2 (commSub_eq_bot_iff.mpr (fun u hu => mem_fixV.mpr (fun q hq => ?_)))
    exact (mem_centSub.mp (Subgroup.mem_inf.mp (hc q hq)).2) u hu
  obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hqQ'
  refine ⟨_, ?_, ?_, hqnot⟩
  · change (MulAut.conj a) q₀ ∈ X
    rw [MulAut.conj_apply]
    exact h.hXA a ha q₀ (h.hQX hq₀)
  · change (a * t * a⁻¹) * ((MulAut.conj a) q₀) * (a * t * a⁻¹)⁻¹ = ((MulAut.conj a) q₀)⁻¹
    rw [MulAut.conj_apply]
    calc (a * t * a⁻¹) * (a * q₀ * a⁻¹) * (a * t * a⁻¹)⁻¹
        = a * (t * q₀ * t⁻¹) * a⁻¹ := by group
      _ = a * q₀⁻¹ * a⁻¹ := by rw [h.hQinv q₀ hq₀]
      _ = (a * q₀ * a⁻¹)⁻¹ := by group

theorem fixed_comp_inverted (h : HAb A X Q t 3) {a : MulAut W} (ha : a ∈ A) {U : Subgroup W}
    (hU : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom))
    (hfix : U.map (a * t * a⁻¹).toMonoidHom = U) :
    ∀ x ∈ X, (a * t * a⁻¹) * x * (a * t * a⁻¹)⁻¹ * x ∈ s13KerOn X U := by
  classical
  have hsA : a * t * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha h.htA) (A.inv_mem ha)
  have hcommX : ∀ y ∈ X, ∀ z ∈ X, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val ((h.hXe.1.is_comm).comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hH := s13KerOn_mem_hyperplanes h.hW (p := 3) (by norm_num) (by norm_num)
    h.hXe hU.1
  obtain ⟨q, hqX, hqinv, hqnot⟩ := w16g_exists_inverted_nontrivial h ha hU
  refine w16g_inverted_mod_hyperplane hcommX hH.1 hH.2 hqX hqnot hqinv
    (w16g_conj_mem_s13KerOn ?_ hfix)
  intro x hx
  exact h.hXA (a * t * a⁻¹) hsA x hx

theorem not_fixed_comp (h : HAb A X Q t 7) {a : MulAut W} (ha : a ∈ A) {U : Subgroup W}
    (hU : U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) :
    U.map (a * t * a⁻¹).toMonoidHom ≠ U := by
  intro hfix
  obtain ⟨q, hqX, hqinv, hqnot⟩ := w16g_exists_inverted_nontrivial h ha hU
  obtain ⟨U₀, hIrr₀, -, hUeq⟩ := hU.1
  have hnt : ∃ u ∈ U₀, q u ≠ u := by
    by_contra hc
    push Not at hc
    apply hqnot
    rw [s13KerOn, hUeq, w16g_inf_centSub_s13IsoSum_eq hIrr₀]
    exact ⟨hqX, mem_centSub.mpr hc⟩
  have hfixU : s13IsoSum X U₀ ⊓ fixV (Subgroup.zpowers q) = ⊥ :=
    w16g_inf_fixV_zpowers_eq_bot h.hW h.hXe.1 hIrr₀ hqX hnt
  have hann := s13_seven_annihilator h.hW h.hXe.1 hIrr₀ hqX (h.hXe.2 q hqX) hfixU
  rw [← hUeq] at hann hfixU
  have hbot := s13_seven_inverted_false hqinv hfix hfixU hann
  have hle : U₀ ≤ U := by
    rw [hUeq]
    exact w16g_le_s13IsoSum_self hIrr₀
  rw [hbot] at hle
  exact lt_irrefl _ (lt_of_lt_of_le hIrr₀.1 hle)

end CFSG.LocalAnalysis.WeakClosure81
