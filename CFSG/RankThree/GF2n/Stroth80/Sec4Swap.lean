module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Comp
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

structure SwapHyp (Γ : Type) [Group Γ] (Λ : Subgroup Γ) : Prop where
  comm : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a
  sq : ∀ a ∈ Λ, a ^ 2 = 1
  sylow : ∀ S : Subgroup Γ, IsPGroup 2 ↥S → Λ ≤ S → S ≤ Subgroup.normalizer (Λ : Set Γ)

section Conj

variable {Γ : Type} [Group Γ]

theorem conjSubgroup_mul_sec4 (a b : Γ) (T : Subgroup Γ) :
    conjSubgroup (a * b) T = conjSubgroup a (conjSubgroup b T) := by
  ext x
  simp only [mem_conjSubgroup, mul_inv_rev, mul_assoc]

theorem conjSubgroup_one_sec4 (T : Subgroup Γ) : conjSubgroup (1 : Γ) T = T := by
  ext x
  simp [mem_conjSubgroup]

theorem mul_mem_conjSubgroup_iff {g x : Γ} {T : Subgroup Γ} :
    g * x * g⁻¹ ∈ conjSubgroup g T ↔ x ∈ T := by
  rw [mem_conjSubgroup]
  have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [this]

theorem conjSubgroup_conjSubgroup_of_sq {t : Γ} (ht : t ^ 2 = 1) (T : Subgroup Γ) :
    conjSubgroup t (conjSubgroup t T) = T := by
  rw [← conjSubgroup_mul_sec4, ← pow_two, ht, conjSubgroup_one_sec4]

end Conj

section Swap

variable {Γ : Type} [Group Γ] [Finite Γ] {Λ : Subgroup Γ}

section Setup

variable (hΛ : SwapHyp Γ Λ) (hcs : CompSimple Γ) {Y : Subgroup Γ} (hY : IsComponent Y) {t : Γ}
  (ht : t ∈ Λ) (hne : conjSubgroup t Y ≠ Y)

include hY hne

theorem swap_comm : ∀ x ∈ Y, ∀ y ∈ conjSubgroup t Y, x * y = y * x :=
  comm_of_ne_component hY (isComponent_conjSubgroup t hY) (Ne.symm hne)

include hcs

theorem swap_inf_eq_bot : Y ⊓ conjSubgroup t Y = ⊥ :=
  hcs.inf_eq_bot hY (isComponent_conjSubgroup t hY) (Ne.symm hne)

theorem swap_unique_decomp {a a' b b' : Γ} (ha : a ∈ Y) (ha' : a' ∈ Y)
    (hb : b ∈ conjSubgroup t Y) (hb' : b' ∈ conjSubgroup t Y) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ Y ⊓ conjSubgroup t Y :=
    ⟨Y.mul_mem (Y.inv_mem ha') ha,
      h1 ▸ (conjSubgroup t Y).mul_mem hb' ((conjSubgroup t Y).inv_mem hb)⟩
  rw [swap_inf_eq_bot hcs hY hne, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem swap_sup_le {N : Subgroup Γ} (hNY : ∀ c ∈ Y, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hNY' : ∀ c ∈ conjSubgroup t Y, ∀ n ∈ N, c * n * c⁻¹ ∈ N) {s : Γ} (hs : s ∈ Y)
    (hs1 : s ≠ 1) (hmem : s * (t * s * t⁻¹) ∈ N) : Y ⊔ conjSubgroup t Y ≤ N := by
  have hc := swap_comm hY hne
  have hY'c := isComponent_conjSubgroup t hY
  have hu : t * s * t⁻¹ ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr hs
  have hu1 : t * s * t⁻¹ ≠ 1 := by
    intro h
    apply hs1
    have : s = t⁻¹ * (t * s * t⁻¹) * t := by group
    rw [this, h]
    group
  refine sup_le ?_ ?_
  · exact hcs.le_of_mul_mem hY hY'c (Ne.symm hne) hNY hs hu hmem hs1
  · refine hcs.le_of_mul_mem hY'c hY hne hNY' hu hs ?_ hu1
    have := hc s hs _ hu
    rwa [← this]

include hΛ ht

end Setup

section Chi

variable {Y : Subgroup Γ} {t : Γ}

@[expose] def swapChi (Y : Subgroup Γ) (t : Γ)
    (hc : ∀ x ∈ Y, ∀ y ∈ conjSubgroup t Y, x * y = y * x) : ↥Y →* Γ where
  toFun g := (g : Γ) * (t * (g : Γ) * t⁻¹)
  map_one' := by simp
  map_mul' g h := by
    have h1 : (h : Γ) * (t * (g : Γ) * t⁻¹) = (t * (g : Γ) * t⁻¹) * (h : Γ) :=
      hc h h.2 _ (mul_mem_conjSubgroup_iff.mpr g.2)
    show ((g : Γ) * (h : Γ)) * (t * ((g : Γ) * (h : Γ)) * t⁻¹) =
      ((g : Γ) * (t * (g : Γ) * t⁻¹)) * ((h : Γ) * (t * (h : Γ) * t⁻¹))
    calc ((g : Γ) * (h : Γ)) * (t * ((g : Γ) * (h : Γ)) * t⁻¹)
        = (g : Γ) * ((h : Γ) * (t * (g : Γ) * t⁻¹)) * (t * (h : Γ) * t⁻¹) := by group
      _ = (g : Γ) * ((t * (g : Γ) * t⁻¹) * (h : Γ)) * (t * (h : Γ) * t⁻¹) := by rw [h1]
      _ = ((g : Γ) * (t * (g : Γ) * t⁻¹)) * ((h : Γ) * (t * (h : Γ) * t⁻¹)) := by group

variable (hc : ∀ x ∈ Y, ∀ y ∈ conjSubgroup t Y, x * y = y * x)

theorem swapChi_apply (g : ↥Y) : swapChi Y t hc g = (g : Γ) * (t * (g : Γ) * t⁻¹) := rfl

theorem swapChi_injective (hinf : Y ⊓ conjSubgroup t Y = ⊥) :
    Function.Injective (swapChi Y t hc) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [swapChi_apply] at hg
  have h1 : (g : Γ) ∈ conjSubgroup t Y := by
    have h2 : (t * (g : Γ) * t⁻¹) ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr g.2
    have h3 : (g : Γ) = (t * (g : Γ) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hg
    rw [h3]
    exact (conjSubgroup t Y).inv_mem h2
  have h4 : (g : Γ) ∈ Y ⊓ conjSubgroup t Y := ⟨g.2, h1⟩
  rw [hinf, Subgroup.mem_bot] at h4
  exact Subtype.ext h4

theorem swapChi_mem_conj (g : ↥Y) : t * (g : Γ) * t⁻¹ ∈ conjSubgroup t Y :=
  mul_mem_conjSubgroup_iff.mpr g.2

theorem swapChi_comm_t (ht2 : t ^ 2 = 1) (g : ↥Y) :
    t * swapChi Y t hc g * t⁻¹ = swapChi Y t hc g := by
  rw [swapChi_apply]
  have h1 : (g : Γ) * (t * (g : Γ) * t⁻¹) = (t * (g : Γ) * t⁻¹) * (g : Γ) :=
    hc g g.2 _ (swapChi_mem_conj g)
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [hti] at h1 ⊢
  calc t * ((g : Γ) * (t * (g : Γ) * t)) * t
      = t * ((t * (g : Γ) * t) * (g : Γ)) * t := by rw [h1]
    _ = (t * t) * (g : Γ) * t * (g : Γ) * t := by group
    _ = (g : Γ) * (t * (g : Γ) * t) := by rw [htt]; group

theorem swapChi_conj (n : Γ) (hnt : n * t = t * n) (hnY : conjSubgroup n Y = Y) (g : ↥Y) :
    ∃ g' : ↥Y, (g' : Γ) = n * (g : Γ) * n⁻¹ ∧ n * swapChi Y t hc g * n⁻¹ = swapChi Y t hc g' := by
  have hmem : n * (g : Γ) * n⁻¹ ∈ Y := by
    have := (mul_mem_conjSubgroup_iff (g := n) (T := Y)).mpr g.2
    rwa [hnY] at this
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  rw [swapChi_apply, swapChi_apply]
  show n * ((g : Γ) * (t * (g : Γ) * t⁻¹)) * n⁻¹ =
    (n * (g : Γ) * n⁻¹) * (t * (n * (g : Γ) * n⁻¹) * t⁻¹)
  calc n * ((g : Γ) * (t * (g : Γ) * t⁻¹)) * n⁻¹
      = (n * (g : Γ) * n⁻¹) * ((n * t) * (g : Γ) * (n * t)⁻¹) := by group
    _ = (n * (g : Γ) * n⁻¹) * ((t * n) * (g : Γ) * (t * n)⁻¹) := by rw [hnt]
    _ = (n * (g : Γ) * n⁻¹) * (t * (n * (g : Γ) * n⁻¹) * t⁻¹) := by group

end Chi

section Square

variable (hΛ : SwapHyp Γ Λ) (hcs : CompSimple Γ) {Y : Subgroup Γ} (hY : IsComponent Y) {t : Γ}
  (ht : t ∈ Λ) (hne : conjSubgroup t Y ≠ Y)

include hΛ hcs hY ht hne

theorem swap_sq_eq_one_of_mem {s : Γ} (hsY : s ∈ Y) (hψ : s⁻¹ * (t * s * t⁻¹) ∈ Λ) :
    s ^ 2 = 1 := by
  have hc := swap_comm hY hne
  have hu : t * s * t⁻¹ ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr hsY
  have hsq := hΛ.sq _ hψ
  have hcomm : s⁻¹ * (t * s * t⁻¹) = (t * s * t⁻¹) * s⁻¹ := hc s⁻¹ (Y.inv_mem hsY) _ hu
  have h2 : s⁻¹ * s⁻¹ * ((t * s * t⁻¹) * (t * s * t⁻¹)) = 1 := by
    calc s⁻¹ * s⁻¹ * ((t * s * t⁻¹) * (t * s * t⁻¹))
        = s⁻¹ * ((s⁻¹ * (t * s * t⁻¹)) * (t * s * t⁻¹)) := by group
      _ = s⁻¹ * (((t * s * t⁻¹) * s⁻¹) * (t * s * t⁻¹)) := by rw [hcomm]
      _ = (s⁻¹ * (t * s * t⁻¹)) * (s⁻¹ * (t * s * t⁻¹)) := by group
      _ = (s⁻¹ * (t * s * t⁻¹)) ^ 2 := (pow_two _).symm
      _ = 1 := hsq
  have h3 : s⁻¹ * s⁻¹ ∈ conjSubgroup t Y := by
    have : s⁻¹ * s⁻¹ = ((t * s * t⁻¹) * (t * s * t⁻¹))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; exact h2
    rw [this]
    exact (conjSubgroup t Y).inv_mem ((conjSubgroup t Y).mul_mem hu hu)
  have h4 : s⁻¹ * s⁻¹ ∈ Y ⊓ conjSubgroup t Y :=
    ⟨Y.mul_mem (Y.inv_mem hsY) (Y.inv_mem hsY), h3⟩
  rw [swap_inf_eq_bot hcs hY hne, Subgroup.mem_bot] at h4
  have h5 : s * s = 1 := by
    have : (s⁻¹ * s⁻¹)⁻¹ = 1 := by rw [h4, inv_one]
    simpa [mul_inv_rev] using this
  rw [pow_two]
  exact h5

theorem swap_not_le_normalizer : ¬ Y ≤ Subgroup.normalizer (Λ : Set Γ) := by
  intro hN
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hY
  have hsq : ∀ s ∈ Y, s ^ 2 = 1 := by
    intro s hs
    refine swap_sq_eq_one_of_mem hΛ hcs hY ht hne hs ?_
    have h1 : s⁻¹ * t * s⁻¹⁻¹ ∈ Λ :=
      (Subgroup.mem_normalizer_iff.mp (hN (Y.inv_mem hs)) t).mp ht
    have e : s⁻¹ * (t * s * t⁻¹) = (s⁻¹ * t * s⁻¹⁻¹) * t⁻¹ := by group
    rw [e]
    exact Λ.mul_mem h1 (Λ.inv_mem ht)
  apply hab
  apply Subtype.ext
  show (a : Γ) * b = b * a
  have h1 := hsq ((a : Γ) * b) (Y.mul_mem a.2 b.2)
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hinv : ∀ x : Γ, x ^ 2 = 1 → x⁻¹ = x := fun x hx => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hx
  have h2 : ((a : Γ) * b)⁻¹ = a * b := hinv _ h1
  rw [mul_inv_rev, hinv _ ha, hinv _ hb] at h2
  exact h2.symm

end Square

section Sylow

variable (hΛ : SwapHyp Γ Λ) (hcs : CompSimple Γ) {Y : Subgroup Γ} (hY : IsComponent Y) {t : Γ}
  (ht : t ∈ Λ) (hne : conjSubgroup t Y ≠ Y)

include hΛ hcs hY ht hne

theorem swap_sylow_data : ∃ S : Sylow 2 Γ, Λ ≤ (S : Subgroup Γ) ∧
    (∀ s ∈ (S : Subgroup Γ) ⊓ Y, s ^ 2 = 1 ∧ s⁻¹ * (t * s * t⁻¹) ∈ Λ) ∧
    ∃ s ∈ (S : Subgroup Γ) ⊓ Y, s ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΛ2 : IsPGroup 2 ↥Λ := fun x => ⟨1, Subtype.ext (by simpa using hΛ.sq x x.2)⟩
  obtain ⟨S, hS⟩ := hΛ2.exists_le_sylow
  have hSN : (S : Subgroup Γ) ≤ Subgroup.normalizer (Λ : Set Γ) := hΛ.sylow S S.isPGroup' hS
  have hc := swap_comm hY hne
  refine ⟨S, hS, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsS, hsY⟩ := hs
    have hu : t * s * t⁻¹ ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr hsY
    have hψ : s⁻¹ * (t * s * t⁻¹) ∈ Λ := by
      have h1 : s⁻¹ * t * s⁻¹⁻¹ ∈ Λ :=
        (Subgroup.mem_normalizer_iff.mp (hSN ((S : Subgroup Γ).inv_mem hsS)) t).mp ht
      have e : s⁻¹ * (t * s * t⁻¹) = (s⁻¹ * t * s⁻¹⁻¹) * t⁻¹ := by group
      rw [e]
      exact Λ.mul_mem h1 (Λ.inv_mem ht)
    exact ⟨swap_sq_eq_one_of_mem hΛ hcs hY ht hne hsY hψ, hψ⟩
  · have hev : 2 ∣ Nat.card ↥Y := by
      by_contra hn
      have hodd : Odd (Nat.card ↥Y) := Nat.odd_iff.mpr (by omega)
      haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥Y hodd
      obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hY
      haveI : Nontrivial ↥Y := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        exact hab (Subsingleton.elim _ _)
      haveI : Group.IsPerfect ↥Y := hY.1.1
      exact Group.IsPerfect.not_isSolvable ↥Y inferInstance
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 hev
    have hy2 : (y : Γ) ^ 2 ^ 1 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    have hy1 : (y : Γ) ≠ 1 := by
      intro h
      have : y = 1 := Subtype.ext h
      rw [this, orderOf_one] at hy
      omega
    obtain ⟨g, hgY, hg⟩ := exists_conj_mem_sylow_of_isSubnormal S hY.2 y.2 ⟨1, hy2⟩
    refine ⟨g⁻¹ * (y : Γ) * g, ⟨hg, Y.mul_mem (Y.mul_mem (Y.inv_mem hgY) y.2) hgY⟩, ?_⟩
    intro h
    apply hy1
    have : (y : Γ) = g * (g⁻¹ * (y : Γ) * g) * g⁻¹ := by group
    rw [this, h]
    group

theorem swap_exp_two : ∀ y ∈ Y, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 = 1 := by
  obtain ⟨S, -, hdata, -⟩ := swap_sylow_data hΛ hcs hY ht hne
  intro y hy hy2
  obtain ⟨g, hg, hgy⟩ := exists_conj_mem_sylow_of_isSubnormal S hY.2 hy hy2
  have h1 := (hdata _ ⟨hgy, Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hy) hg⟩).1
  have e : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by simp only [pow_two]; group
  rw [e] at h1
  have : y ^ 2 = g * (g⁻¹ * y ^ 2 * g) * g⁻¹ := by group
  rw [this, h1]
  group

theorem swap_exists_involution :
    ∃ s ∈ Y, s ≠ 1 ∧ s ^ 2 = 1 ∧ s * (t * s * t⁻¹) ∈ Λ := by
  obtain ⟨S, -, hdata, s, ⟨hsS, hsY⟩, hs1⟩ := swap_sylow_data hΛ hcs hY ht hne
  obtain ⟨hs2, hψ⟩ := hdata s ⟨hsS, hsY⟩
  refine ⟨s, hsY, hs1, hs2, ?_⟩
  have : s⁻¹ = s := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hs2
  rwa [this] at hψ

theorem swap_exists_d : ∃ d ∈ Λ, d ≠ 1 ∧ d ∈ Y ⊔ conjSubgroup t Y := by
  obtain ⟨s, hsY, hs1, -, hd⟩ := swap_exists_involution hΛ hcs hY ht hne
  have hu : t * s * t⁻¹ ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr hsY
  refine ⟨_, hd, ?_, Subgroup.mul_mem_sup hsY hu⟩
  intro h
  apply hs1
  have h1 : s ∈ conjSubgroup t Y := by
    have : s = (t * s * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (conjSubgroup t Y).inv_mem hu
  have h2 : s ∈ Y ⊓ conjSubgroup t Y := ⟨hsY, h1⟩
  rw [swap_inf_eq_bot hcs hY hne, Subgroup.mem_bot] at h2
  exact h2

theorem swap_orbit : ∀ r ∈ Λ, conjSubgroup r Y = Y ∨ conjSubgroup r Y = conjSubgroup t Y := by
  intro r hr
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨d, hdΛ, hd1, hdK⟩ := swap_exists_d hΛ hcs hY ht hne
  have hrr : r ^ 2 = 1 := hΛ.sq r hr
  have htt : t ^ 2 = 1 := hΛ.sq t ht
  have hrt : r * t = t * r := hΛ.comm r hr t ht
  have hrr' : r * r = 1 := by rw [← pow_two]; exact hrr
  have htt' : t * t = 1 := by rw [← pow_two]; exact htt
  set Y' := conjSubgroup t Y with hY'
  set Yr := conjSubgroup r Y with hYr
  set Y'r := conjSubgroup r Y' with hY'r
  have hY'c : IsComponent Y' := isComponent_conjSubgroup t hY
  have hYrc : IsComponent Yr := isComponent_conjSubgroup r hY
  have hY'rc : IsComponent Y'r := isComponent_conjSubgroup r hY'c
  have hconj_rr : ∀ T : Subgroup Γ, conjSubgroup r (conjSubgroup r T) = T := fun T => by
    rw [← conjSubgroup_mul_sec4, hrr', conjSubgroup_one_sec4]
  have hconj_tt : ∀ T : Subgroup Γ, conjSubgroup t (conjSubgroup t T) = T := fun T => by
    rw [← conjSubgroup_mul_sec4, htt', conjSubgroup_one_sec4]
  have hcomm_rt : ∀ T : Subgroup Γ, conjSubgroup r (conjSubgroup t T) =
      conjSubgroup t (conjSubgroup r T) := fun T => by
    rw [← conjSubgroup_mul_sec4, ← conjSubgroup_mul_sec4, hrt]
  have d12 : Y ≠ Y' := Ne.symm hne
  have d13 : Y ≠ Yr := Ne.symm h1
  have d14 : Y ≠ Y'r := by
    intro h
    apply h2
    have : conjSubgroup r Y = conjSubgroup r (conjSubgroup r Y') := by rw [← hY'r, ← h]
    rw [hconj_rr] at this
    exact this
  have d23 : Y' ≠ Yr := fun h => h2 h.symm
  have d24 : Y' ≠ Y'r := by
    intro h
    apply h1
    have h3 : conjSubgroup t Y = conjSubgroup t (conjSubgroup r Y) := by
      calc conjSubgroup t Y = Y' := rfl
        _ = Y'r := h
        _ = conjSubgroup r (conjSubgroup t Y) := rfl
        _ = conjSubgroup t (conjSubgroup r Y) := hcomm_rt Y
    have := congrArg (conjSubgroup t) h3
    rw [hconj_tt, hconj_tt] at this
    exact this.symm
  have d34 : Yr ≠ Y'r := by
    intro h
    apply hne
    have := congrArg (conjSubgroup r) h
    rw [hconj_rr, hconj_rr] at this
    exact this.symm
  have hbot := hcs.sup_inf_sup_eq_bot hY hY'c hYrc hY'rc d12 d13 d14 d23 d24 d34
  have hdr : d ∈ Yr ⊔ Y'r := by
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute (swap_comm hY hne) hdK
    have hdd : r * d * r⁻¹ = d := by
      rw [mul_inv_eq_iff_eq_mul, hΛ.comm r hr d hdΛ]
    rw [← hdd, hab]
    have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (mul_mem_conjSubgroup_iff.mpr ha)
      (mul_mem_conjSubgroup_iff.mpr hb)
  have : d ∈ (Y ⊔ Y') ⊓ (Yr ⊔ Y'r) := ⟨hdK, hdr⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hd1 this

theorem swapChi_range_le_sup :
    (swapChi Y t (swap_comm hY hne)).range ≤ Y ⊔ conjSubgroup t Y := by
  rintro _ ⟨g, rfl⟩
  rw [swapChi_apply]
  exact Subgroup.mul_mem_sup g.2 (swapChi_mem_conj g)

theorem swap_normalizes_range : ∀ n ∈ Λ, ∀ x ∈ (swapChi Y t (swap_comm hY hne)).range,
    n * x * n⁻¹ ∈ (swapChi Y t (swap_comm hY hne)).range := by
  have hc := swap_comm hY hne
  have htt : t ^ 2 = 1 := hΛ.sq t ht
  have htt' : t * t = 1 := by rw [← pow_two]; exact htt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt'
  have key : ∀ n ∈ Λ, conjSubgroup n Y = Y →
      ∀ x ∈ (swapChi Y t hc).range, n * x * n⁻¹ ∈ (swapChi Y t hc).range := by
    rintro n hn hnY _ ⟨g, rfl⟩
    obtain ⟨g', -, hg'⟩ := swapChi_conj hc n (hΛ.comm n hn t ht) hnY g
    rw [hg']
    exact ⟨g', rfl⟩
  intro n hn x hx
  rcases swap_orbit hΛ hcs hY ht hne n hn with h | h
  · exact key n hn h x hx
  ·
    have hm : t * n ∈ Λ := Λ.mul_mem ht hn
    have hmY : conjSubgroup (t * n) Y = Y := by
      rw [conjSubgroup_mul_sec4, h, conjSubgroup_conjSubgroup_of_sq htt]
    have h1 := key (t * n) hm hmY x hx
    have hxt : ∀ y ∈ (swapChi Y t hc).range, t * y * t⁻¹ = y := by
      rintro _ ⟨g, rfl⟩
      exact swapChi_comm_t hc htt g
    have h2 := hxt _ h1
    have e : n * x * n⁻¹ = t * ((t * n) * x * (t * n)⁻¹) * t⁻¹ := by
      calc n * x * n⁻¹ = (t * t) * (n * x * n⁻¹) * (t * t)⁻¹ := by rw [htt']; group
        _ = t * ((t * n) * x * (t * n)⁻¹) * t⁻¹ := by group
    rw [e, h2]
    exact h1

theorem swap_mem_range_of_comm_t : ∀ k ∈ Y ⊔ conjSubgroup t Y, t * k * t⁻¹ = k →
    k ∈ (swapChi Y t (swap_comm hY hne)).range := by
  intro k hk hkt
  have hc := swap_comm hY hne
  have htt : t ^ 2 = 1 := hΛ.sq t ht
  have htt' : t * t = 1 := by rw [← pow_two]; exact htt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt'
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hk
  obtain ⟨b₀, hb₀, rfl⟩ : ∃ b₀ ∈ Y, b = t * b₀ * t⁻¹ :=
    ⟨t⁻¹ * b * t, (mem_conjSubgroup (g := t) (T := Y) (x := b)).mp hb, by group⟩
  have hua : t * a * t⁻¹ ∈ conjSubgroup t Y := mul_mem_conjSubgroup_iff.mpr ha
  have h1 : (t * a * t⁻¹) * b₀ = a * (t * b₀ * t⁻¹) := by
    calc (t * a * t⁻¹) * b₀ = t * (a * (t * b₀ * t⁻¹)) * t⁻¹ := by
          rw [hti]
          calc (t * a * t) * b₀ = (t * a * t) * b₀ * (t * t) := by rw [htt', mul_one]
            _ = t * (a * (t * b₀ * t)) * t := by group
      _ = a * (t * b₀ * t⁻¹) := hkt
  have h2 : b₀ * (t * a * t⁻¹) = a * (t * b₀ * t⁻¹) := by
    rw [← h1]
    exact (hc b₀ hb₀ _ hua)
  obtain ⟨h3, h4⟩ := swap_unique_decomp hcs hY hne hb₀ ha
    (mul_mem_conjSubgroup_iff.mpr ha) (mul_mem_conjSubgroup_iff.mpr hb₀) h2
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [swapChi_apply]
  show a * (t * a * t⁻¹) = a * (t * b₀ * t⁻¹)
  rw [h3]

theorem swap_Lam_inf_range_eq_map :
    ∃ P : Sylow 2 ↥Y, Λ ⊓ (swapChi Y t (swap_comm hY hne)).range =
      (P : Subgroup ↥Y).map (swapChi Y t (swap_comm hY hne)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := swap_comm hY hne
  obtain ⟨S, -, hdata, -⟩ := swap_sylow_data hΛ hcs hY ht hne
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hY.2
  have hχP : ∀ g ∈ (P : Subgroup ↥Y), swapChi Y t hc g ∈ Λ := by
    intro g hg
    have h1 : (g : Γ) ∈ (S : Subgroup Γ) ⊓ Y := by
      rw [← hP]
      exact ⟨g, hg, rfl⟩
    obtain ⟨hs2, hψ⟩ := hdata _ h1
    have hinv : (g : Γ)⁻¹ = (g : Γ) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hs2
    rw [swapChi_apply]
    rw [hinv] at hψ
    exact hψ
  refine ⟨P, ?_⟩
  apply le_antisymm
  · rintro _ ⟨hxΛ, g, rfl⟩
    let T : Subgroup ↥Y := Λ.comap (swapChi Y t hc)
    have hTp : IsPGroup 2 ↥T := by
      intro x
      refine ⟨1, ?_⟩
      have h1 : (swapChi Y t hc (x : ↥Y)) ^ 2 = 1 := hΛ.sq _ x.2
      have h2 : swapChi Y t hc ((x : ↥Y) ^ 2) = 1 := by rw [map_pow]; exact h1
      have h3 : (x : ↥Y) ^ 2 = 1 :=
        swapChi_injective hc (swap_inf_eq_bot hcs hY hne) (h2.trans (map_one _).symm)
      exact Subtype.ext (by simpa using h3)
    have hPT : (P : Subgroup ↥Y) ≤ T := fun g hg => hχP g hg
    have hTP : T = (P : Subgroup ↥Y) := P.is_maximal' hTp hPT
    have hgT : g ∈ T := hxΛ
    rw [hTP] at hgT
    exact ⟨g, hgT, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨hχP g hg, g, rfl⟩

theorem swap_Lam_inf_range_ne_bot :
    ∃ d ∈ Λ ⊓ (swapChi Y t (swap_comm hY hne)).range, d ≠ 1 := by
  obtain ⟨s, hsY, hs1, -, hd⟩ := swap_exists_involution hΛ hcs hY ht hne
  refine ⟨swapChi Y t (swap_comm hY hne) ⟨s, hsY⟩, ⟨hd, ⟨s, hsY⟩, rfl⟩, ?_⟩
  intro h
  apply hs1
  have := swapChi_injective (swap_comm hY hne) (swap_inf_eq_bot hcs hY hne)
    (h.trans (map_one _).symm)
  exact congrArg Subtype.val this

theorem swap_card_eq_two_mul :
    Nat.card ↥Λ = 2 * Nat.card ↥(Λ ⊓ Subgroup.normalizer (Y : Set Γ)) := by
  have hNΛ : Λ ⊓ Subgroup.normalizer (Y : Set Γ) ≤ Λ := inf_le_left
  have htt : conjSubgroup t (conjSubgroup t Y) = Y :=
    conjSubgroup_conjSubgroup_of_sq (hΛ.sq t ht) Y
  have hidx : ((Λ ⊓ Subgroup.normalizer (Y : Set Γ)).subgroupOf Λ).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, ht⟩, fun b => ?_⟩
    have hb : (b : Γ) ∈ Λ := b.2
    have hcb : (b : Γ) * t = t * (b : Γ) := hΛ.comm _ hb t ht
    have hcomm : conjSubgroup (b : Γ) (conjSubgroup t Y) =
        conjSubgroup t (conjSubgroup (b : Γ) Y) := by
      rw [← conjSubgroup_mul_sec4, ← conjSubgroup_mul_sec4, hcb]
    rcases swap_orbit hΛ hcs hY ht hne b hb with h | h
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨hb, conjSubgroup_eq_self_iff.mp h⟩, fun hbt => ?_⟩
      have h1 : conjSubgroup ((b : Γ) * t) Y = Y :=
        conjSubgroup_eq_self_iff.mpr (Subgroup.mem_subgroupOf.mp hbt).2
      rw [conjSubgroup_mul_sec4, hcomm, h] at h1
      exact hne h1
    · left
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨Λ.mul_mem hb ht, conjSubgroup_eq_self_iff.mp ?_⟩,
        fun hbN => ?_⟩
      · show conjSubgroup ((b : Γ) * t) Y = Y
        rw [conjSubgroup_mul_sec4, hcomm, h, htt]
      · have h1 : conjSubgroup (b : Γ) Y = Y :=
          conjSubgroup_eq_self_iff.mpr (Subgroup.mem_subgroupOf.mp hbN).2
        rw [h1] at h
        exact hne h.symm
  have h1 := Subgroup.index_mul_card (H := (Λ ⊓ Subgroup.normalizer (Y : Set Γ)).subgroupOf Λ)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNΛ).toEquiv] at h1
  exact h1.symm

theorem swap_range_isSimpleGroup :
    IsSimpleGroup ↥(swapChi Y t (swap_comm hY hne)).range := by
  haveI := isSimpleGroup_of_center_eq_bot hY (hcs Y hY)
  exact (MulEquiv.isSimpleGroup_congr (MonoidHom.ofInjective
    (swapChi_injective (swap_comm hY hne) (swap_inf_eq_bot hcs hY hne)))).mp inferInstance

theorem swap_range_nonabelian :
    ∃ a b : ↥(swapChi Y t (swap_comm hY hne)).range, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hY
  let e := MonoidHom.ofInjective (swapChi_injective (swap_comm hY hne)
    (swap_inf_eq_bot hcs hY hne))
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem swap_centralizes_of_centralizes_range {c : Γ} (hcΛ : c ∈ Λ)
    (hcY : conjSubgroup c Y = Y)
    (hcŶ : ∀ x ∈ (swapChi Y t (swap_comm hY hne)).range, c * x * c⁻¹ = x) :
    (∀ g ∈ Y, c * g * c⁻¹ = g) ∧ (∀ g ∈ conjSubgroup t Y, c * g * c⁻¹ = g) := by
  have hc := swap_comm hY hne
  have hct : c * t = t * c := hΛ.comm c hcΛ t ht
  have h1 : ∀ g ∈ Y, c * g * c⁻¹ = g := by
    intro g hg
    obtain ⟨g', hg'1, hg'2⟩ := swapChi_conj hc c hct hcY ⟨g, hg⟩
    have h2 : swapChi Y t hc g' = swapChi Y t hc ⟨g, hg⟩ := by
      rw [← hg'2]
      exact hcŶ _ ⟨⟨g, hg⟩, rfl⟩
    have h3 := swapChi_injective hc (swap_inf_eq_bot hcs hY hne) h2
    rw [← hg'1, h3]
  refine ⟨h1, fun g hg => ?_⟩
  obtain ⟨g₀, hg₀, rfl⟩ : ∃ g₀ ∈ Y, g = t * g₀ * t⁻¹ :=
    ⟨t⁻¹ * g * t, (mem_conjSubgroup (g := t) (T := Y) (x := g)).mp hg, by group⟩
  calc c * (t * g₀ * t⁻¹) * c⁻¹ = (c * t) * g₀ * (c * t)⁻¹ := by group
    _ = (t * c) * g₀ * (t * c)⁻¹ := by rw [hct]
    _ = t * (c * g₀ * c⁻¹) * t⁻¹ := by group
    _ = t * g₀ * t⁻¹ := by rw [h1 g₀ hg₀]

end Sylow

end Swap

end CFSG.RankThree.GF2n.Stroth80
