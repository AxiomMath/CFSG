module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G]

private theorem mem_omegaCenter_iff {q : ℕ} {T : Subgroup G} {z : G} :
    z ∈ omegaCenter q T ↔ z ∈ T ∧ (∀ t ∈ T, z * t = t * z) ∧ z ^ q = 1 :=
  Iff.rfl

theorem thompsonJ_le (q : ℕ) (T : Subgroup G) : thompsonJ q T ≤ T :=
  sSup_le fun _ hE => hE.1

theorem omegaCenter_le (q : ℕ) (T : Subgroup G) : omegaCenter q T ≤ T :=
  fun _ hz => (mem_omegaCenter_iff.1 hz).1

theorem omegaCenter_le_centralizer (q : ℕ) (T : Subgroup G) :
    omegaCenter q T ≤ Subgroup.centralizer (T : Set G) :=
  fun _ hz => Subgroup.mem_centralizer_iff.2 fun t ht => ((mem_omegaCenter_iff.1 hz).2.1 t ht).symm

theorem omegaCenter_map (q : ℕ) (T : Subgroup G) (f : G ≃* G) :
    (omegaCenter q T).map f.toMonoidHom = omegaCenter q (T.map f.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxT, hxc, hxq⟩ := mem_omegaCenter_iff.1 hx
    refine mem_omegaCenter_iff.2 ⟨⟨x, hxT, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hxc t ht]
    · simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hxq, map_one]
  · intro hy
    obtain ⟨⟨x, hxT, rfl⟩, hyc, hyq⟩ := mem_omegaCenter_iff.1 hy
    refine ⟨x, mem_omegaCenter_iff.2 ⟨hxT, fun t ht => f.injective ?_, f.injective ?_⟩, rfl⟩
    · simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hyc _ ⟨t, ht, rfl⟩
    · simpa only [MulEquiv.coe_toMonoidHom, map_pow, map_one] using hyq

private theorem map_map_symm (f : G ≃* G) (K : Subgroup G) :
    (K.map f.toMonoidHom).map f.symm.toMonoidHom = K :=
  f.mapSubgroup.symm_apply_apply K

private theorem map_symm_map (f : G ≃* G) (K : Subgroup G) :
    (K.map f.symm.toMonoidHom).map f.toMonoidHom = K :=
  f.mapSubgroup.apply_symm_apply K

private theorem isElemAbelian_map {q : ℕ} {E : Subgroup G} (hE : IsElemAbelian q E)
    (f : G ≃* G) : IsElemAbelian q (E.map f.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

private theorem map_maximal {q : ℕ} {T E : Subgroup G}
    (hE : E ≤ T ∧ IsElemAbelian q E ∧
      ∀ E' : Subgroup G, E' ≤ T → IsElemAbelian q E' → Nat.card E' ≤ Nat.card E)
    (f : G ≃* G) :
    E.map f.toMonoidHom ≤ T.map f.toMonoidHom ∧ IsElemAbelian q (E.map f.toMonoidHom) ∧
      ∀ E' : Subgroup G, E' ≤ T.map f.toMonoidHom → IsElemAbelian q E' →
        Nat.card E' ≤ Nat.card (E.map f.toMonoidHom) := by
  obtain ⟨hET, hEa, hmax⟩ := hE
  refine ⟨Subgroup.map_mono hET, isElemAbelian_map hEa f, fun E' hE'T hE'a => ?_⟩
  have h1 : E'.map f.symm.toMonoidHom ≤ T := by
    simpa only [map_map_symm] using Subgroup.map_mono (f := f.symm.toMonoidHom) hE'T
  have h2 := hmax _ h1 (isElemAbelian_map hE'a f.symm)
  have c1 : Nat.card (E'.map f.symm.toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective (f := f.symm.toMonoidHom) f.symm.injective
  have c2 : Nat.card (E.map f.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective
  omega

theorem thompsonJ_map (q : ℕ) (T : Subgroup G) (f : G ≃* G) :
    (thompsonJ q T).map f.toMonoidHom = thompsonJ q (T.map f.toMonoidHom) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (sSup_le fun E hE => ?_))
    (sSup_le fun E' hE' => ?_)
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_maximal hE f)
  · have h1 := map_maximal hE' f.symm
    rw [map_map_symm] at h1
    have h2 : E'.map f.symm.toMonoidHom ≤ thompsonJ q T := le_sSup h1
    simpa only [map_symm_map] using Subgroup.map_mono (f := f.toMonoidHom) h2

theorem normalizer_le_normalizer_omegaCenter (q : ℕ) (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (omegaCenter q T : Set G) := by
  intro g hg
  have hg' : T.map (MulAut.conj g).toMonoidHom = T := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  have h := omegaCenter_map q T (MulAut.conj g)
  rw [hg'] at h
  exact h

theorem normalizer_le_normalizer_thompsonJ (q : ℕ) (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (thompsonJ q T : Set G) := by
  intro g hg
  have hg' : T.map (MulAut.conj g).toMonoidHom = T := Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  have h := thompsonJ_map q T (MulAut.conj g)
  rw [hg'] at h
  exact h

theorem omegaCenter_inf_le_omegaCenter {q : ℕ} {S T : Subgroup G} (h : T ≤ S) :
    omegaCenter q S ⊓ T ≤ omegaCenter q T := by
  rintro z ⟨hzS, hzT⟩
  obtain ⟨-, hzc, hzq⟩ := mem_omegaCenter_iff.1 hzS
  exact ⟨hzT, fun t ht => hzc t (h ht), hzq⟩

private theorem exists_mul_of_mem_sup_omegaCenter {q : ℕ} {T E : Subgroup G} (hET : E ≤ T)
    {x : G} (hx : x ∈ E ⊔ omegaCenter q T) : ∃ e ∈ E, ∃ z ∈ omegaCenter q T, e * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    · exact ⟨1, one_mem _, x, hx, one_mul x⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e₁, he₁, z₁, hz₁, rfl⟩ := hx
    obtain ⟨e₂, he₂, z₂, hz₂, rfl⟩ := hy
    have hc : z₁ * e₂ = e₂ * z₁ := (mem_omegaCenter_iff.1 hz₁).2.1 e₂ (hET he₂)
    refine ⟨e₁ * e₂, mul_mem he₁ he₂, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
    calc e₁ * e₂ * (z₁ * z₂) = e₁ * (e₂ * z₁) * z₂ := by group
      _ = e₁ * (z₁ * e₂) * z₂ := by rw [hc]
      _ = e₁ * z₁ * (e₂ * z₂) := by group
  | inv x _ hx =>
    obtain ⟨e, he, z, hz, rfl⟩ := hx
    have hc : Commute z e := (mem_omegaCenter_iff.1 hz).2.1 e (hET he)
    exact ⟨e⁻¹, inv_mem he, z⁻¹, inv_mem hz, by rw [mul_inv_rev]; exact hc.inv_inv.eq.symm⟩

private theorem isElemAbelian_sup_omegaCenter {q : ℕ} {T E : Subgroup G} (hET : E ≤ T)
    (hE : IsElemAbelian q E) : IsElemAbelian q (E ⊔ omegaCenter q T) := by
  obtain ⟨hEc, hEq⟩ := hE
  have hcomm : ∀ e ∈ E, ∀ z ∈ omegaCenter q T, Commute e z := fun e he z hz =>
    ((mem_omegaCenter_iff.1 hz).2.1 e (hET he)).symm
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨e₁, he₁, z₁, hz₁, rfl⟩ := exists_mul_of_mem_sup_omegaCenter hET hx
    obtain ⟨e₂, he₂, z₂, hz₂, rfl⟩ := exists_mul_of_mem_sup_omegaCenter hET hy
    have h12 : Commute e₁ e₂ := setLike_mul_comm he₁ he₂
    have hz12 : Commute z₁ z₂ := (mem_omegaCenter_iff.1 hz₁).2.1 z₂ (omegaCenter_le q T hz₂)
    exact ((h12.mul_right (hcomm e₁ he₁ z₂ hz₂)).mul_left
      ((hcomm e₂ he₂ z₁ hz₁).symm.mul_right hz12)).eq
  · obtain ⟨e, he, z, hz, rfl⟩ := exists_mul_of_mem_sup_omegaCenter hET hx
    rw [(hcomm e he z hz).mul_pow, hEq e he, (mem_omegaCenter_iff.1 hz).2.2, one_mul]

theorem omegaCenter_le_thompsonJ [Finite G] (q : ℕ) (T : Subgroup G) :
    omegaCenter q T ≤ thompsonJ q T := by
  obtain ⟨E, ⟨hET, hEa⟩, hmax⟩ := Set.exists_max_image
    {E : Subgroup G | E ≤ T ∧ IsElemAbelian q E} (fun E => Nat.card E) (Set.toFinite _)
    ⟨⊥, bot_le, ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩⟩
  have hle : E ≤ thompsonJ q T := le_sSup ⟨hET, hEa, fun E' h1 h2 => hmax E' ⟨h1, h2⟩⟩
  have hsup : E = E ⊔ omegaCenter q T :=
    Subgroup.eq_of_le_of_card_ge le_sup_left
      (hmax _ ⟨sup_le hET (omegaCenter_le q T), isElemAbelian_sup_omegaCenter hET hEa⟩)
  calc omegaCenter q T ≤ E ⊔ omegaCenter q T := le_sup_right
    _ = E := hsup.symm
    _ ≤ thompsonJ q T := hle

theorem omegaCenter_ne_bot [Finite G] {q : ℕ} (hq : q.Prime) {T : Subgroup G}
    (hT : IsPGroup q T) (hne : T ≠ ⊥) : omegaCenter q T ≠ ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  have : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hT.to_subgroup (Subgroup.center T))
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial (Subgroup.center T))
    rw [hn, pow_zero] at h
    exact lt_irrefl 1 h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q (hn ▸ dvd_pow_self q hn0)
  have hxq : x ^ q = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => hq.one_lt.ne' (hx ▸ h ▸ orderOf_one)
  have hmem : ((x : T) : G) ∈ omegaCenter q T := by
    refine mem_omegaCenter_iff.2 ⟨(x : T).2, fun t ht => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 x.2 ⟨t, ht⟩).symm
    · have h := congrArg (fun z : Subgroup.center T => ((z : T) : G)) hxq
      simpa using h
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hx1 (Subtype.ext (Subtype.ext hmem))

theorem thompsonJ_ne_bot [Finite G] {q : ℕ} (hq : q.Prime) {T : Subgroup G}
    (hT : IsPGroup q T) (hne : T ≠ ⊥) : thompsonJ q T ≠ ⊥ := fun h =>
  omegaCenter_ne_bot hq hT hne (le_bot_iff.1 (h ▸ omegaCenter_le_thompsonJ q T))

end CFSG.SignalizerFunctorTheorem.Glauberman
