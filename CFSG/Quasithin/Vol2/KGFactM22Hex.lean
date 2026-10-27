module

public import CFSG.Quasithin.Vol2.KGFactM22HexData

public section

namespace CFSG.Quasithin.H13.S126M22

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  PermLat CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Certificates
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def a6a : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a6b : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem a6a_pow : a6a ^ 3 = 1 := by decide

theorem a6a_ne : a6a ≠ 1 := by decide

theorem a6_noncomm : a6a * a6b ≠ a6b * a6a := by decide

theorem le_of_normal_of_quot {Y : Type*} [Group Y] {V W : Subgroup Y} [V.Normal]
    (e : Y ⧸ V ≃* ↥(alternatingGroup (Fin 6))) (hW : W.Normal)
    (h : IsPGroup 2 ↥W ∨ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : W ≤ V := by
  set f : Y →* ↥(alternatingGroup (Fin 6)) := e.toMonoidHom.comp (QuotientGroup.mk' V) with hf
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective V)
  have hfk : ∀ y, f y = 1 → y ∈ V := fun y hy => by
    simp only [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    exact hy
  have hn : (W.map f).Normal := hW.map f hfs
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map f) with h1 | h1
  · intro w hw
    have hw' : f w ∈ W.map f := Subgroup.mem_map_of_mem f hw
    rw [h1, Subgroup.mem_bot] at hw'
    exact hfk w hw'
  · exfalso
    obtain ⟨a', ha', haa⟩ : a6a ∈ W.map f := h1 ▸ Subgroup.mem_top a6a
    rcases h with h2 | h2
    · obtain ⟨k, hk⟩ := h2 ⟨a', ha'⟩
      have hk' : a6a ^ 2 ^ k = 1 := by
        rw [← haa, ← map_pow]
        have : a' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [this, map_one]
      have ha3 : orderOf a6a = 3 := orderOf_eq_prime a6a_pow a6a_ne
      have h3 := orderOf_dvd_of_pow_eq_one hk'
      rw [ha3] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · obtain ⟨b', hb', hbb⟩ : a6b ∈ W.map f := h1 ▸ Subgroup.mem_top a6b
      have h3 := congrArg f (h2 a' ha' b' hb')
      rw [map_mul, map_mul, haa, hbb] at h3
      exact a6_noncomm h3

abbrev E0 : Subgroup (Perm (Fin 22)) := Subgroup.closure {g | g ∈ eL}

theorem mem_eL {a : Perm (Fin 22)} : a ∈ eL ↔ a = e1 ∨ a = e2 ∨ a = e3 ∨ a = e4 := by
  simp [eL]

theorem eL_mem_l6 : ∀ a ∈ eL, a ∈ Subgroup.closure {g | g ∈ l6Gens} := by
  intro a ha
  rcases mem_eL.1 ha with rfl | rfl | rfl | rfl
  · rw [Equiv.ext e1_eq]; exact evalW_mem_closure _ _
  · rw [Equiv.ext e2_eq]; exact evalW_mem_closure _ _
  · rw [Equiv.ext e3_eq]; exact evalW_mem_closure _ _
  · rw [Equiv.ext e4_eq]; exact evalW_mem_closure _ _

theorem E0_le : E0 ≤ Subgroup.closure {g | g ∈ l6Gens} := (Subgroup.closure_le _).2 eL_mem_l6

theorem eL_comm : ∀ a ∈ eL, ∀ b ∈ eL, a * b = b * a := by
  intro a ha b hb
  have p12 : e1 * e2 = e2 * e1 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c12 x
  have p13 : e1 * e3 = e3 * e1 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c13 x
  have p14 : e1 * e4 = e4 * e1 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c14 x
  have p23 : e2 * e3 = e3 * e2 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c23 x
  have p24 : e2 * e4 = e4 * e2 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c24 x
  have p34 : e3 * e4 = e4 * e3 := Equiv.ext fun x => by
    rw [Perm.mul_apply, Perm.mul_apply]; exact c34 x
  rcases mem_eL.1 ha with rfl | rfl | rfl | rfl <;> rcases mem_eL.1 hb with rfl | rfl | rfl | rfl
  exacts [rfl, p12, p13, p14, p12.symm, rfl, p23, p24, p13.symm, p23.symm, rfl, p34, p14.symm,
    p24.symm, p34.symm, rfl]

theorem E0_comm : ∀ a ∈ E0, ∀ b ∈ E0, a * b = b * a := by
  have h1 : ∀ a ∈ eL, E0 ≤ Subgroup.centralizer {a} := fun a ha =>
    (Subgroup.closure_le _).2 fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.2 (eL_comm b hb a ha)
  have h2 : E0 ≤ Subgroup.centralizer (E0 : Set (Perm (Fin 22))) :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.1 (h1 a ha hb)
  intro a ha b hb
  exact Subgroup.mem_centralizer_iff.1 (h2 hb) a ha

theorem spanOf_mem {S : Subgroup (Perm (Fin 22))} :
    ∀ gs : List (Perm (Fin 22)), (∀ g ∈ gs, g ∈ S) → ∀ s ∈ spanOf gs, s ∈ S
  | [], _, s, hs => by
    simp only [spanOf, List.mem_singleton] at hs
    rw [hs]
    exact S.one_mem
  | g :: gs, h, s, hs => by
    simp only [spanOf, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨t, ht, rfl⟩
    · exact spanOf_mem gs (fun g hg => h g (List.mem_cons_of_mem _ hg)) s hs
    · exact S.mul_mem (h g List.mem_cons_self)
        (spanOf_mem gs (fun g hg => h g (List.mem_cons_of_mem _ hg)) t ht)

theorem spanOf_mem_E0 : ∀ s ∈ spanOf eL, s ∈ E0 :=
  spanOf_mem eL fun _ hg => Subgroup.subset_closure hg

theorem conjEq {g a b : Perm (Fin 22)} (h : ∀ x : Fin 22, g (a (g⁻¹ x)) = b x) :
    g * a * g⁻¹ = b :=
  Equiv.ext fun x => by rw [Perm.mul_apply, Perm.mul_apply]; exact h x

theorem conjEq' {g a b : Perm (Fin 22)} (h : ∀ x : Fin 22, g⁻¹ (a (g x)) = b x) :
    g⁻¹ * a * g = b :=
  Equiv.ext fun x => by rw [Perm.mul_apply, Perm.mul_apply]; exact h x

theorem conj_mem_E0 {g : Perm (Fin 22)} (hg : ∀ a ∈ eL, g * a * g⁻¹ ∈ E0) :
    ∀ h ∈ E0, g * h * g⁻¹ ∈ E0 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem a ha => exact hg a ha
  | one => simp
  | mul a b _ _ iha ihb =>
    have := E0.mul_mem iha ihb
    rwa [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
  | inv a _ ih =>
    have := E0.inv_mem ih
    rwa [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]

theorem e_mem (i : Fin 4) : [e1, e2, e3, e4].getD i 1 ∈ E0 :=
  Subgroup.subset_closure (by fin_cases i <;> simp [eL])

theorem e1_mem : e1 ∈ E0 := e_mem 0
theorem e2_mem : e2 ∈ E0 := e_mem 1
theorem e3_mem : e3 ∈ E0 := e_mem 2
theorem e4_mem : e4 ∈ E0 := e_mem 3

theorem l6_le_normalizer :
    Subgroup.closure {g | g ∈ l6Gens} ≤ Subgroup.normalizer (E0 : Set (Perm (Fin 22))) := by
  have key : ∀ g : Perm (Fin 22), (∀ a ∈ eL, g * a * g⁻¹ ∈ E0) → (∀ a ∈ eL, g⁻¹ * a * g ∈ E0) →
      g ∈ Subgroup.normalizer (E0 : Set (Perm (Fin 22))) := by
    intro g h1 h2
    have h2' : ∀ a ∈ eL, g⁻¹ * a * g⁻¹⁻¹ ∈ E0 := fun a ha => by rw [inv_inv]; exact h2 a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_E0 h1 x, fun hx => ?_⟩
    have := conj_mem_E0 h2' _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, l6Gens_eq, List.mem_pair] at hg
  rcases hg with rfl | rfl
  · refine key _ (fun a ha => ?_) (fun a ha => ?_)
    · rcases mem_eL.1 ha with rfl | rfl | rfl | rfl
      · rw [conjEq n01]; exact e2_mem
      · rw [conjEq n02]; exact E0.mul_mem e1_mem e2_mem
      · rw [conjEq n03]; exact E0.mul_mem e3_mem e4_mem
      · rw [conjEq n04]; exact e3_mem
    · rcases mem_eL.1 ha with rfl | rfl | rfl | rfl
      · rw [conjEq' m01]; exact E0.mul_mem e1_mem e2_mem
      · rw [conjEq' m02]; exact e1_mem
      · rw [conjEq' m03]; exact e4_mem
      · rw [conjEq' m04]; exact E0.mul_mem e3_mem e4_mem
  · refine key _ (fun a ha => ?_) (fun a ha => ?_)
    · rcases mem_eL.1 ha with rfl | rfl | rfl | rfl
      · rw [conjEq n11]; exact e1_mem
      · rw [conjEq n12]; exact E0.mul_mem (E0.mul_mem e1_mem e2_mem) e3_mem
      · rw [conjEq n13]; exact E0.mul_mem e1_mem e2_mem
      · rw [conjEq n14]; exact E0.mul_mem e2_mem e4_mem
    · rcases mem_eL.1 ha with rfl | rfl | rfl | rfl
      · rw [conjEq' m11]; exact e1_mem
      · rw [conjEq' m12]; exact E0.mul_mem e1_mem e3_mem
      · rw [conjEq' m13]; exact E0.mul_mem e2_mem e3_mem
      · rw [conjEq' m14]; exact E0.mul_mem (E0.mul_mem e1_mem e3_mem) e4_mem

theorem exists_span_fix {k : Perm (Fin 22)} (hk : ∀ a ∈ eL, k * a = a * k) :
    ∃ s ∈ spanOf eL, ∀ x : Fin 22, x ∉ hexL → (s⁻¹ * k) x = x := by
  have hkE : ∀ s ∈ E0, k * s = s * k := by
    have h : E0 ≤ Subgroup.centralizer {k} := (Subgroup.closure_le _).2 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.2 (hk a ha).symm
    exact fun s hs => (Subgroup.mem_centralizer_singleton_iff.1 (h hs)).symm
  have hk3 : k 3 ∉ hexL := by
    intro h
    have h1 : e1 (k 3) = k 3 := f1 _ h
    have h2 : k (e1 3) = e1 (k 3) := by
      have := congrArg (fun σ : Perm (Fin 22) => σ 3) (hkE e1 e1_mem)
      simpa only [Perm.mul_apply] using this
    rw [h1, e1_three] at h2
    exact absurd (k.injective h2) (by decide)
  obtain ⟨s, hs, hs3⟩ := orbit3 _ hk3
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨t, ht, rfl⟩ := orbit3 x hx
  have hsE := spanOf_mem_E0 s hs
  have htE := spanOf_mem_E0 t ht
  have e1' : k (t 3) = t (k 3) := by
    have := congrArg (fun σ : Perm (Fin 22) => σ 3) (hkE t htE)
    simpa only [Perm.mul_apply] using this
  have e2' : t (s 3) = s (t 3) := by
    have := congrArg (fun σ : Perm (Fin 22) => σ 3) (E0_comm t htE s hsE)
    simpa only [Perm.mul_apply] using this
  rw [Perm.mul_apply, e1', ← hs3, e2']
  simp

end CFSG.Quasithin.H13.S126M22
