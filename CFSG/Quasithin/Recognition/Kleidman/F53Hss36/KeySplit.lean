module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolModel
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Quasithin CFSG.Quasithin.F53Mod Equiv

@[expose] def kleinAt (p : Fin 5) : Subgroup (Perm (Fin 5)) where
  carrier := {y | Perm.sign y = 1 ∧ y * y = 1 ∧ y p = p}
  one_mem' := ⟨by simp, by simp, by simp⟩
  mul_mem' := by
    intro y z hy hz
    have h : ∀ q : Fin 5, ∀ y z : Perm (Fin 5), (Perm.sign y = 1 ∧ y * y = 1 ∧ y q = q) →
        (Perm.sign z = 1 ∧ z * z = 1 ∧ z q = q) →
        (Perm.sign (y * z) = 1 ∧ (y * z) * (y * z) = 1 ∧ (y * z) q = q) := by
      decide +kernel
    exact h p y z hy hz
  inv_mem' := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hy
    have hinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
    show Perm.sign y⁻¹ = 1 ∧ y⁻¹ * y⁻¹ = 1 ∧ y⁻¹ p = p
    rw [hinv]
    exact ⟨h1, h2, h3⟩

theorem mem_kleinAt {p : Fin 5} {y : Perm (Fin 5)} :
    y ∈ kleinAt p ↔ Perm.sign y = 1 ∧ y * y = 1 ∧ y p = p := Iff.rfl

theorem kleinAt_le_alt (p : Fin 5) : kleinAt p ≤ alternatingGroup (Fin 5) :=
  fun _ hy => Perm.mem_alternatingGroup.mpr hy.1

theorem card_kleinAt (p : Fin 5) : Nat.card (kleinAt p) = 4 := by
  classical
  have h : ∀ q : Fin 5, (Finset.univ.filter fun y : Perm (Fin 5) =>
      Perm.sign y = 1 ∧ y * y = 1 ∧ y q = q).card = 4 := by decide +kernel
  rw [← h p, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by simp [mem_kleinAt]))

@[expose] def d0 : Perm (Fin 5) := swap 0 1 * swap 1 2

theorem d0_mem_alt : d0 ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem orderOf_d0 : orderOf d0 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem conj_mem_kleinAt {p : Fin 5} {g : Perm (Fin 5)} (hg : g p = p) {y : Perm (Fin 5)}
    (hy : y ∈ kleinAt p) : g * y * g⁻¹ ∈ kleinAt p := by
  obtain ⟨h1, h2, h3⟩ := hy
  have hg' : g⁻¹ p = p := by rw [Perm.inv_eq_iff_eq]; exact hg.symm
  refine ⟨by simp [h1], ?_, ?_⟩
  · have e : g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    rw [e, h2, mul_one, mul_inv_cancel]
  · simp [Perm.mul_apply, hg', h3, hg]

theorem mem_normalizer_kleinAt {p : Fin 5} {g : Perm (Fin 5)} (hg : g p = p) :
    g ∈ Subgroup.normalizer (kleinAt p : Set (Perm (Fin 5))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hg' : g⁻¹ p = p := by rw [Perm.inv_eq_iff_eq]; exact hg.symm
  refine ⟨conj_mem_kleinAt hg, fun h => ?_⟩
  have := conj_mem_kleinAt hg' h
  simpa [mul_assoc] using this

theorem kleinAt_sup_eq : kleinAt 3 ⊔ kleinAt 4 = alternatingGroup (Fin 5) := by
  have hle : kleinAt 3 ⊔ kleinAt 4 ≤ alternatingGroup (Fin 5) :=
    sup_le (kleinAt_le_alt 3) (kleinAt_le_alt 4)
  set a : Perm (Fin 5) := swap 0 1 * swap 2 3 with ha
  set b : Perm (Fin 5) := swap 0 1 * swap 2 4 with hb
  set c : Perm (Fin 5) := swap 0 2 * swap 1 4 with hc
  have haK : a ∈ kleinAt 4 := by rw [mem_kleinAt]; decide
  have hbK : b ∈ kleinAt 3 := by rw [mem_kleinAt]; decide
  have hcK : c ∈ kleinAt 3 := by rw [mem_kleinAt]; decide
  set K := kleinAt 3 ⊔ kleinAt 4 with hK
  have h3 : orderOf (a * b) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have h5 : orderOf (a * c) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have hab : a * b ∈ K := K.mul_mem (Subgroup.mem_sup_right haK) (Subgroup.mem_sup_left hbK)
  have hac : a * c ∈ K := K.mul_mem (Subgroup.mem_sup_right haK) (Subgroup.mem_sup_left hcK)
  have d3 : 3 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hab
    rwa [h3] at this
  have d5 : 5 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hac
    rwa [h5] at this
  have d4 : 4 ∣ Nat.card K := by
    rw [← card_kleinAt 4]
    exact Subgroup.card_dvd_of_le le_sup_right
  have d60 : 60 ∣ Nat.card K := by
    have h12 : 12 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d4 d3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 d5
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := F53.card_alt5
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcardA]
  exact Nat.le_of_dvd Nat.card_pos d60

section Model

variable (Mo : Model 5)

theorem isInvSub_sup {B₁ B₂ : Subgroup (Perm (Fin 5))} {X : Subgroup Mo.W}
    (h₁ : IsInvSub Mo B₁ X) (h₂ : IsInvSub Mo B₂ X) : IsInvSub Mo (B₁ ⊔ B₂) X := by
  have hmap : ∀ σ : Perm (Fin 5), (∀ x ∈ X, Mo.act σ x ∈ X) →
      X.map (Mo.act σ).toMonoidHom = X := by
    intro σ hσ
    have hle : X.map (Mo.act σ).toMonoidHom ≤ X := by
      rintro _ ⟨x, hx, rfl⟩; exact hσ x hx
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (Mo.act σ).injective])
  let St : Subgroup (Perm (Fin 5)) :=
    { carrier := {σ | X.map (Mo.act σ).toMonoidHom = X}
      one_mem' := by
        show X.map (Mo.act 1).toMonoidHom = X
        rw [map_one]
        ext x; simp
      mul_mem' := by
        intro σ τ hσ hτ
        show X.map (Mo.act (σ * τ)).toMonoidHom = X
        have e : (Mo.act (σ * τ)).toMonoidHom =
            (Mo.act σ).toMonoidHom.comp (Mo.act τ).toMonoidHom := by
          ext x; simp [map_mul]
        rw [e, ← Subgroup.map_map, hτ, hσ]
      inv_mem' := by
        intro σ hσ
        show X.map (Mo.act σ⁻¹).toMonoidHom = X
        have hσ' : X.map (Mo.act σ).toMonoidHom = X := hσ
        apply hmap
        intro x hx
        have hx' : x ∈ X.map (Mo.act σ).toMonoidHom := by rw [hσ']; exact hx
        obtain ⟨y, hy, rfl⟩ := hx'
        simpa [map_inv] using hy }
  have hle : B₁ ⊔ B₂ ≤ St := sup_le (fun σ hσ => hmap σ (h₁ σ hσ)) (fun σ hσ => hmap σ (h₂ σ hσ))
  intro σ hσ x hx
  have h : X.map (Mo.act σ).toMonoidHom = X := hle hσ
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem isInvSub_fixW_alt : IsInvSub Mo ⊤ (fixW Mo (alternatingGroup (Fin 5))) := by
  intro τ _ c hc σ hσ
  have hσ' : τ⁻¹ * σ * τ ∈ alternatingGroup (Fin 5) := by
    have h := (alternatingGroup.normal (α := Fin 5)).conj_mem σ hσ τ⁻¹
    simpa using h
  have h1 := hc _ hσ'
  calc Mo.act σ (Mo.act τ c) = Mo.act τ (Mo.act (τ⁻¹ * σ * τ) c) := by
        rw [← act_mul_apply, ← act_mul_apply]; group
    _ = Mo.act τ c := by rw [h1]

theorem isInvSub_commW_alt' : IsInvSub Mo ⊤ (commW Mo (alternatingGroup (Fin 5)) ⊤) :=
  isInvSub_commW_of_normal Mo (fun c _ b hb => (alternatingGroup.normal (α := Fin 5)).conj_mem b hb c)
    (fun _ _ _ _ => Subgroup.mem_top _)

theorem commW_conj_eq (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    commW Mo (B.map (MulAut.conj g).toMonoidHom) ⊤ = (commW Mo B ⊤).map (Mo.act g).toMonoidHom := by
  rw [map_commW_conj, map_act_top]

theorem fixW_alt_eq_bot_of_split
    (hd : fixW Mo (Subgroup.zpowers d0) ≤ fixW Mo (alternatingGroup (Fin 5)))
    (hT : commW Mo (kleinAt 4) ⊤ ⊓ fixW Mo (alternatingGroup (Fin 5)) = ⊥)
    (hG : commW Mo ⊤ ⊤ = ⊤) :
    fixW Mo (alternatingGroup (Fin 5)) = ⊥ := by
  set A := alternatingGroup (Fin 5) with hA
  set F := fixW Mo A with hF
  set X := commW Mo (Subgroup.zpowers d0) ⊤ with hX
  have hdodd : Odd (orderOf d0) := by rw [orderOf_d0]; decide
  have hcompl := bf3_isCompl Mo hdodd
  have hdA : Subgroup.zpowers d0 ≤ A := (Subgroup.zpowers_le).mpr d0_mem_alt
  have hFd : fixW Mo (Subgroup.zpowers d0) = F :=
    le_antisymm hd (fun c hc b hb => hc b (hdA hb))
  rw [hFd] at hcompl
  have hFinv := isInvSub_fixW_alt Mo
  have hsub : ∀ p : Fin 5, d0 p = p → commW Mo (kleinAt p) ⊤ ⊓ F = ⊥ →
      commW Mo (kleinAt p) ⊤ ≤ X := by
    intro p hp hTp
    have hinv : IsInvSub Mo (Subgroup.zpowers d0) (commW Mo (kleinAt p) ⊤) := by
      refine isInvSub_commW_of_normal Mo ?_ (fun _ _ _ _ => Subgroup.mem_top _)
      intro c hc b hb
      have hcN : c ∈ Subgroup.normalizer (kleinAt p : Set (Perm (Fin 5))) :=
        (Subgroup.zpowers_le.mpr (mem_normalizer_kleinAt hp)) hc
      exact (Subgroup.mem_normalizer_iff.mp hcN b).mp hb
    have h1 := bf3_sup_eq Mo hdodd hinv
    rw [hFd, hTp, bot_sup_eq] at h1
    rw [← h1]
    exact inf_le_right
  have hT3 : commW Mo (kleinAt 3) ⊤ ⊓ F = ⊥ := by
    set σ : Perm (Fin 5) := swap 3 4 * swap 0 1 with hσ
    have hσT : kleinAt 3 = (kleinAt 4).map (MulAut.conj σ).toMonoidHom := by
      ext y
      rw [Subgroup.mem_map]
      constructor
      · intro hy
        refine ⟨σ⁻¹ * y * σ, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have h : ∀ y : Perm (Fin 5), y ∈ kleinAt 3 → σ⁻¹ * y * σ ∈ kleinAt 4 := by
          intro y; simp only [mem_kleinAt, hσ]; revert y; decide +kernel
        exact h y hy
      · rintro ⟨z, hz, rfl⟩
        have h : ∀ z : Perm (Fin 5), z ∈ kleinAt 4 → σ * z * σ⁻¹ ∈ kleinAt 3 := by
          intro z; simp only [mem_kleinAt, hσ]; revert z; decide +kernel
        simpa [MulAut.conj_apply] using h z hz
    rw [hσT, commW_conj_eq, eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxF⟩
    have hx' : x ∈ F := by
      have := hFinv σ⁻¹ (Subgroup.mem_top _) _ hxF
      simpa [act_inv_act] using this
    have : x ∈ commW Mo (kleinAt 4) ⊤ ⊓ F := ⟨hx, hx'⟩
    rw [hT, Subgroup.mem_bot] at this
    simp [this]
  have h4X := hsub 4 (by decide) hT
  have h3X := hsub 3 (by decide) hT3
  have hXT : ∀ p : Fin 5, commW Mo (kleinAt p) ⊤ ≤ X → IsInvSub Mo (kleinAt p) X := by
    intro p hpX t ht x hx
    have h1 : Mo.act t x * x⁻¹ ∈ X :=
      hpX (Subgroup.subset_closure ⟨t, ht, x, Subgroup.mem_top _, rfl⟩)
    have e : Mo.act t x = (Mo.act t x * x⁻¹) * x := by group
    rw [e]
    exact X.mul_mem h1 hx
  have hXA : IsInvSub Mo A X := by
    rw [hA, ← kleinAt_sup_eq]
    exact isInvSub_sup Mo (hXT 3 h3X) (hXT 4 h4X)
  have hdec : ∀ w : Mo.W, ∃ c ∈ F, ∃ x ∈ X, c * x = w := by
    intro w
    have hw : w ∈ F ⊔ X := by rw [hcompl.sup_eq_top]; exact Subgroup.mem_top w
    exact Subgroup.mem_sup.mp hw
  have hXeq : X = commW Mo A ⊤ := by
    apply le_antisymm
    · unfold commW
      exact Subgroup.closure_mono fun w ⟨b, hb, u, hu, hw⟩ => ⟨b, hdA hb, u, hu, hw⟩
    · unfold commW
      rw [Subgroup.closure_le]
      rintro _ ⟨σ, hσ, w, -, rfl⟩
      obtain ⟨c, hc, x, hx, rfl⟩ := hdec w
      have e : Mo.act σ (c * x) * (c * x)⁻¹ = Mo.act σ x * x⁻¹ := by
        rw [map_mul, hc σ hσ, mul_inv, ← mul_assoc, mul_comm c (Mo.act σ x),
          mul_inv_cancel_right]
      rw [e]
      exact X.mul_mem (hXA σ hσ x hx) (X.inv_mem hx)
  have hXS : IsInvSub Mo ⊤ X := by rw [hXeq]; exact isInvSub_commW_alt' Mo
  set s : Perm (Fin 5) := swap 0 1 with hs
  have hs2 : s * s = 1 := by rw [hs]; exact swap_mul_self 0 1
  have hsodd : Perm.sign s = -1 := by rw [hs]; exact Perm.sign_swap (by decide)
  have hWs : ∀ w : Mo.W, ∃ x ∈ X, ∃ u ∈ commW Mo (Subgroup.zpowers s) ⊤, x * u = w := by
    intro w
    have hw : w ∈ commW Mo ⊤ ⊤ := by rw [hG]; exact Subgroup.mem_top w
    have hle : commW Mo ⊤ ⊤ ≤ X ⊔ commW Mo (Subgroup.zpowers s) ⊤ := by
      unfold commW
      rw [Subgroup.closure_le]
      rintro _ ⟨τ, -, w', -, rfl⟩
      by_cases hτ : Perm.sign τ = 1
      · have hτA : τ ∈ A := Perm.mem_alternatingGroup.mpr hτ
        refine Subgroup.mem_sup_left ?_
        rw [hXeq]
        exact Subgroup.subset_closure ⟨τ, hτA, w', Subgroup.mem_top _, rfl⟩
      · have hτs : τ * s ∈ A := by
          rw [Perm.mem_alternatingGroup, Perm.sign_mul, hsodd]
          rcases Int.units_eq_one_or (Perm.sign τ) with h | h
          · exact absurd h hτ
          · rw [h]; decide
        have e : Mo.act τ w' * w'⁻¹ = (Mo.act (τ * s) (Mo.act s w') * (Mo.act s w')⁻¹) *
            (Mo.act s w' * w'⁻¹) := by
          rw [act_mul_apply, ← act_mul_apply Mo s s, hs2, map_one]
          simp only [MulAut.one_apply]
          group
        rw [e]
        refine Subgroup.mul_mem_sup ?_ ?_
        · rw [hXeq]
          exact Subgroup.subset_closure ⟨τ * s, hτs, _, Subgroup.mem_top _, rfl⟩
        · exact Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, w', Subgroup.mem_top _, rfl⟩
    exact Subgroup.mem_sup.mp (hle hw)
  have hFfix : ∀ c ∈ F, Mo.act s c = c := by
    intro c hc
    obtain ⟨x, hx, u, hu, rfl⟩ := hWs c
    have hus : Mo.act s u = u := commW_le_fixW_of_sq Mo hs2 hu s (Subgroup.mem_zpowers s)
    have h1 : Mo.act s (x * u) * (x * u)⁻¹ = Mo.act s x * x⁻¹ := by
      rw [map_mul, hus, mul_inv, ← mul_assoc, mul_right_comm (Mo.act s x) u x⁻¹,
        mul_inv_cancel_right]
    have h2 : Mo.act s (x * u) * (x * u)⁻¹ ∈ X := by
      rw [h1]; exact X.mul_mem (hXS s (Subgroup.mem_top _) x hx) (X.inv_mem hx)
    have h3 : Mo.act s (x * u) * (x * u)⁻¹ ∈ F :=
      F.mul_mem (hFinv s (Subgroup.mem_top _) _ hc) (F.inv_mem hc)
    have h4 := hcompl.disjoint.le_bot ⟨h3, h2⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h4
    exact h4
  have hFall : ∀ τ : Perm (Fin 5), ∀ c ∈ F, Mo.act τ c = c := by
    intro τ c hc
    by_cases hτ : Perm.sign τ = 1
    · exact hc τ (Perm.mem_alternatingGroup.mpr hτ)
    · have hτs : τ * s ∈ A := by
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, hsodd]
        rcases Int.units_eq_one_or (Perm.sign τ) with h | h
        · exact absurd h hτ
        · rw [h]; decide
      have e : τ = (τ * s) * s := by rw [mul_assoc, hs2, mul_one]
      rw [e, act_mul_apply, hFfix c hc, hc _ hτs]
  have hGX : commW Mo ⊤ ⊤ ≤ X := by
    unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨τ, -, w, -, rfl⟩
    obtain ⟨c, hc, x, hx, rfl⟩ := hdec w
    have e : Mo.act τ (c * x) * (c * x)⁻¹ = Mo.act τ x * x⁻¹ := by
      rw [map_mul, hFall τ c hc, mul_inv, ← mul_assoc, mul_comm c (Mo.act τ x),
        mul_inv_cancel_right]
    rw [e]
    exact X.mul_mem (hXS τ (Subgroup.mem_top _) x hx) (X.inv_mem hx)
  rw [hG] at hGX
  exact eq_bot_iff.mpr fun c hc => hcompl.disjoint.le_bot ⟨hc, hGX (Subgroup.mem_top c)⟩

end Model

end CFSG.Quasithin.Kleidman.F53Hss36
