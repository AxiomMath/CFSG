module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinA6Aux1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6
public import CFSG.LocalAnalysis.WeakClosure81.W183Fin2
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.A6Facts.Core
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

theorem w183fin_exists_embedding {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (e : ↥L ≃* alternatingGroup (Fin 6)) :
    ∃ f : Y →* P10, Function.Injective f ∧ (∀ y, f y ∈ A6Models.autA6) ∧
      (∀ l ∈ L, f l ∈ A6Models.psl29) ∧ (∀ x ∈ A6Models.psl29, ∃ l ∈ L, f l = x) := by
  obtain ⟨θ, ψ, -, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  let φ : ↥L ≃* ↥A6Models.psl29 := e.trans ψ.symm
  let Θ := Unc25K1.A6Model.thetaEquiv φ
  have hconj : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := congrArg (fun m : MulAut ↥L => ((m ⟨l, hl⟩ : ↥L) : Y)) (MonoidHom.mem_ker.1 hy)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc l * y = (y * l * y⁻¹) * y := by rw [this]
        _ = y * l := by group
    rw [hC] at hy'
    exact hy'
  let f : Y →* P10 := (A6Models.autA6.subtype.comp Θ.toMonoidHom).comp MulAut.conjNormal
  have hΘ : ∀ l' : ↥L, Θ (MulAut.conjNormal (l' : Y)) =
      ⟨(φ l' : P10), A6Facts.psl29_le_autA6 (φ l').2⟩ := by
    intro l'
    apply Unc25K1.A6Model.thetaEquiv_eq φ
    intro k
    have hk : (MulAut.conjNormal (l' : Y) : MulAut ↥L) k = l' * k * l'⁻¹ := rfl
    rw [hk, map_mul, map_mul, map_inv]
    simp
  refine ⟨f, Subtype.val_injective.comp (Θ.injective.comp hconj),
    fun y => (Θ (MulAut.conjNormal y)).2,
    fun l hl => ?_, fun x hx => ⟨((φ.symm ⟨x, hx⟩ : ↥L) : Y), (φ.symm ⟨x, hx⟩).2, ?_⟩⟩
  · show ((Θ (MulAut.conjNormal l)) : P10) ∈ A6Models.psl29
    have := hΘ ⟨l, hl⟩
    simp only at this
    rw [this]
    exact (φ ⟨l, hl⟩).2
  · show ((Θ (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y))) : P10) = x
    rw [hΘ]
    simp

theorem w183fin_finG3_A6 : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal →
    Subgroup.centralizer (L : Set Y) = ⊥ → IsAlt ↥L 6 →
    ∀ A : Subgroup Y, Nat.card A = 4 → CFSG.Open.IsElemAbelian 2 A →
      (∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) → False := by
  intro Y _ _ L hLn hC hL A hcard hel hTI1
  haveI := hLn
  obtain ⟨e⟩ := hL
  obtain ⟨f, hfinj, hfaut, hfL, hfsurj⟩ := w183fin_exists_embedding L hC e
  have hcardA' : Nat.card (A.map f) = 4 := by
    rw [Subgroup.card_map_of_injective hfinj]; exact hcard
  have hsqA' : ∀ x ∈ A.map f, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hel.2 a ha, map_one]
  have hle : A.map f ≤ A6Models.autA6 := by
    rintro _ ⟨a, _, rfl⟩
    exact hfaut a
  obtain ⟨t', ht', ht'1, g', hg'P, hcomm', a', ha', hnc⟩ :=
    w183fin_g3_sound (A.map f) hle hcardA' hsqA'
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨l, hl, rfl⟩ := hfsurj g' hg'P
  obtain ⟨a, ha, rfl⟩ := ha'
  have ht1 : t ≠ 1 := fun h => ht'1 (by rw [h, map_one])
  have hlt : l * t = t * l := hfinj (by rw [map_mul, map_mul]; exact hcomm')
  have hla := hTI1 t ht ht1 l hl hlt a ha
  exact hnc (by rw [← map_mul, ← map_mul, hla])

private theorem w183fin_finA6_of_T2a
    (hT2a : ∀ {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
      (e : ↥L ≃* alternatingGroup (Fin 6)) (θ : ↥s6 →* Equiv.Perm (Fin 6))
      (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
      (hψθ : ∀ x : ↥A6Models.psl29, ((ψ x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        θ (Subgroup.inclusion psl29_le_s6 x))
      (τ : Y), ActsOnDynkinMod ⊥ L τ →
        ((Unc25K1.A6Model.thetaEquiv (e.trans ψ.symm) (MulAut.conjNormal τ) :
          ↥A6Models.autA6) : P10) ∉ s6) : FinA6 := by
  intro Y _ _ L hLn hL hC hτ A hcard hel hTI
  haveI : L.Normal := hLn
  obtain ⟨e⟩ := hL
  obtain ⟨θ, ψ, -, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  let φ : ↥L ≃* ↥A6Models.psl29 := e.trans ψ.symm
  let Θ := Unc25K1.A6Model.thetaEquiv φ
  have hconj : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := congrArg (fun m : MulAut ↥L => ((m ⟨l, hl⟩ : ↥L) : Y)) (MonoidHom.mem_ker.1 hy)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc l * y = (y * l * y⁻¹) * y := by rw [this]
        _ = y * l := by group
    rw [hC] at hy'
    exact hy'
  let f : Y →* P10 := (A6Models.autA6.subtype.comp Θ.toMonoidHom).comp MulAut.conjNormal
  have hfinj : Function.Injective f :=
    Subtype.val_injective.comp (Θ.injective.comp hconj)
  have hB1 : ∀ y : Y, f y ∈ A6Models.autA6 := fun y => (Θ (MulAut.conjNormal y)).2
  have hB2 : A6Models.psl29 ≤ f.range := by
    intro x hx
    refine ⟨((φ.symm ⟨x, hx⟩ : ↥L) : Y), ?_⟩
    have hΘ : Θ (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y)) =
        ⟨x, A6Facts.psl29_le_autA6 hx⟩ := by
      apply Unc25K1.A6Model.thetaEquiv_eq φ
      intro k
      have hk : (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y) : MulAut ↥L) k =
          φ.symm ⟨x, hx⟩ * k * (φ.symm ⟨x, hx⟩)⁻¹ := rfl
      rw [hk, map_mul, map_mul, map_inv]
      simp
    show ((Θ (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y)) : ↥A6Models.autA6) : P10) = x
    rw [hΘ]
  obtain ⟨τ, hτd⟩ := hτ
  have hB3 : ∃ σ ∈ f.range, σ ∉ s6 := ⟨f τ, ⟨τ, rfl⟩, hT2a L e θ ψ hψθ τ hτd⟩
  have hB1' : f.range ≤ A6Models.autA6 := by
    rintro _ ⟨y, rfl⟩
    exact hB1 y
  have hclass := Unc25K1.A6Model.classify f.range hB1' hB2 hB3
  have hcardA' : Nat.card (A.map f) = 4 := by
    rw [Subgroup.card_map_of_injective hfinj]; exact hcard
  have hsqA' : ∀ x ∈ A.map f, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hel.2 a ha, map_one]
  have hA'le : A.map f ≤ f.range := Subgroup.map_le_range f A
  have key : ∀ (l : List (List Nat)), w183fin_noTI l = true →
      (∀ x : P10, x ∈ f.range ↔ code x ∈ l) →
      (∀ c ∈ l, ∃ x ∈ f.range, code x = c) → False := by
    intro l hl hmem hsurj
    obtain ⟨t', ht', ht'1, g', hg', hcomm, hnotnorm⟩ :=
      w183fin_noTI_sound f.range l hmem hsurj hl (A.map f) hA'le hcardA' hsqA'
    obtain ⟨t, ht, rfl⟩ := ht'
    obtain ⟨g, rfl⟩ := hg'
    have ht1 : t ≠ 1 := fun h => ht'1 (by rw [h, map_one])
    have hcg : g * t = t * g := hfinj (by rw [map_mul, map_mul]; exact hcomm)
    exact hnotnorm (w183fin_map_normalizer f A (hTI t ht ht1 g hcg))
  rcases hclass with h | h | h
  · obtain ⟨hl1, hl2⟩ := w183fin_cosetL_spec (B := f.range) (t := A6Models.tMul)
      (tC := w183fin_tMulC) (by decide +kernel) (fun x => by rw [h]; exact Out21.A6.mem_pgl29_iff x)
    exact key w183fin_lPGL w183fin_ti_pgl hl1 hl2
  · obtain ⟨hl1, hl2⟩ := w183fin_cosetL_spec (B := f.range) (t := A6Models.tMulFrob)
      (tC := w183fin_tMulFrobC) (by decide +kernel)
      (fun x => by rw [h]; exact Out21.A6.mem_m10_iff x)
    exact key w183fin_lM10 w183fin_ti_m10 hl1 hl2
  · obtain ⟨hl1, hl2⟩ := w183fin_autL_spec
    exact key autL w183fin_ti_aut (fun x => by rw [h]; exact hl1 x) (fun c hc => by
      obtain ⟨x, hx, hxc⟩ := hl2 c hc
      exact ⟨x, by rw [h]; exact hx, hxc⟩)

private theorem w183fin_exists_three_embedding_of_T2a
    (hT2a : ∀ {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
      (e : ↥L ≃* alternatingGroup (Fin 6)) (θ : ↥s6 →* Equiv.Perm (Fin 6))
      (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
      (hψθ : ∀ x : ↥A6Models.psl29, ((ψ x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        θ (Subgroup.inclusion psl29_le_s6 x))
      (τ : Y), ActsOnDynkinMod ⊥ L τ →
        ((Unc25K1.A6Model.thetaEquiv (e.trans ψ.symm) (MulAut.conjNormal τ) :
          ↥A6Models.autA6) : P10) ∉ s6)
    {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (e : ↥L ≃* alternatingGroup (Fin 6)) (τ : Y)
    (hτ : ActsOnDynkinMod ⊥ L τ) :
    ∃ f : Y →* P10, Function.Injective f ∧
      (f.range = A6Models.pgl29 ∨ f.range = A6Models.m10 ∨ f.range = A6Models.autA6) := by
  obtain ⟨θ, ψ, -, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  let φ : ↥L ≃* ↥A6Models.psl29 := e.trans ψ.symm
  let Θ := Unc25K1.A6Model.thetaEquiv φ
  have hconj : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hy' : y ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := congrArg (fun m : MulAut ↥L => ((m ⟨l, hl⟩ : ↥L) : Y)) (MonoidHom.mem_ker.1 hy)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc l * y = (y * l * y⁻¹) * y := by rw [this]
        _ = y * l := by group
    rw [hC] at hy'
    exact hy'
  let f : Y →* P10 := (A6Models.autA6.subtype.comp Θ.toMonoidHom).comp MulAut.conjNormal
  have hfinj : Function.Injective f := Subtype.val_injective.comp (Θ.injective.comp hconj)
  have hB2 : A6Models.psl29 ≤ f.range := by
    intro x hx
    refine ⟨((φ.symm ⟨x, hx⟩ : ↥L) : Y), ?_⟩
    have hΘ : Θ (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y)) =
        ⟨x, A6Facts.psl29_le_autA6 hx⟩ := by
      apply Unc25K1.A6Model.thetaEquiv_eq φ
      intro k
      have hk : (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y) : MulAut ↥L) k =
          φ.symm ⟨x, hx⟩ * k * (φ.symm ⟨x, hx⟩)⁻¹ := rfl
      rw [hk, map_mul, map_mul, map_inv]
      simp
    show ((Θ (MulAut.conjNormal ((φ.symm ⟨x, hx⟩ : ↥L) : Y)) : ↥A6Models.autA6) : P10) = x
    rw [hΘ]
  have hB3 : ∃ σ ∈ f.range, σ ∉ s6 := ⟨f τ, ⟨τ, rfl⟩, hT2a L e θ ψ hψθ τ hτ⟩
  have hB1' : f.range ≤ A6Models.autA6 := by
    rintro _ ⟨y, rfl⟩
    exact (Θ (MulAut.conjNormal y)).2
  exact ⟨f, hfinj, Unc25K1.A6Model.classify f.range hB1' hB2 hB3⟩

private theorem w183fin_finGraphOdd_A6_of_T2a
    (hT2a : ∀ {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
      (e : ↥L ≃* alternatingGroup (Fin 6)) (θ : ↥s6 →* Equiv.Perm (Fin 6))
      (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
      (hψθ : ∀ x : ↥A6Models.psl29, ((ψ x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        θ (Subgroup.inclusion psl29_le_s6 x))
      (τ : Y), ActsOnDynkinMod ⊥ L τ →
        ((Unc25K1.A6Model.thetaEquiv (e.trans ψ.symm) (MulAut.conjNormal τ) :
          ↥A6Models.autA6) : P10) ∉ s6) :
    ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsAlt ↥L 6 →
      Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ a : Y, orderOf a = 2 →
        ¬ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x} := by
  intro Y _ _ L hLn hL hC hτ a ha hOT
  haveI : L.Normal := hLn
  obtain ⟨e⟩ := hL
  obtain ⟨τ, hτd⟩ := hτ
  obtain ⟨f, hfinj, hclass⟩ := w183fin_exists_three_embedding_of_T2a hT2a L hC e τ hτd
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha, pow_two] at this
    exact this
  have key : ∀ l, w183fin_oddT l = true → (∀ x : P10, x ∈ f.range ↔ code x ∈ l) →
      (∀ c ∈ l, ∃ x ∈ f.range, code x = c) → False := by
    intro l hl hmem hsurj
    obtain ⟨g', hg', h2, h4⟩ := w183fin_oddT_sound f.range l hmem hsurj hl (f a) ⟨a, rfl⟩
      (by rw [← map_mul, ha2, map_one]) (fun h => ha1 (hfinj (by rw [h, map_one])))
    obtain ⟨g, rfl⟩ := hg'
    have hx : f (a * (g * a * g⁻¹)) = f a * (f g * f a * (f g)⁻¹) := by simp [map_mul, map_inv]
    have hx2 : (a * (g * a * g⁻¹)) ^ 2 ≠ 1 := fun h => h2 (by rw [← hx, ← map_pow, h, map_one])
    have hx4 : (a * (g * a * g⁻¹)) ^ 4 = 1 := hfinj (by rw [map_pow, hx, h4, map_one])
    have hdvd : orderOf (a * (g * a * g⁻¹)) ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hn2 : ¬ orderOf (a * (g * a * g⁻¹)) ∣ 2 := fun h =>
      hx2 (orderOf_dvd_iff_pow_eq_one.1 h)
    have hconj : IsConj a (g * a * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    rcases hOT.2 a (IsConj.refl a) _ hconj with h | h
    · exact hn2 h
    · have hle : orderOf (a * (g * a * g⁻¹)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf (a * (g * a * g⁻¹)) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      generalize orderOf (a * (g * a * g⁻¹)) = n at hdvd hn2 h hle hpos
      interval_cases n
      · exact hn2 (one_dvd 2)
      · exact hn2 dvd_rfl
      · omega
      · exact absurd h (by decide)
  rcases hclass with h | h | h
  · obtain ⟨hl1, hl2⟩ := w183fin_cosetL_spec (B := f.range) (t := A6Models.tMul)
      (tC := w183fin_tMulC) (by decide +kernel) (fun x => by rw [h]; exact Out21.A6.mem_pgl29_iff x)
    exact key w183fin_lPGL w183fin_odd_pgl hl1 hl2
  · obtain ⟨hl1, hl2⟩ := w183fin_cosetL_spec (B := f.range) (t := A6Models.tMulFrob)
      (tC := w183fin_tMulFrobC) (by decide +kernel)
      (fun x => by rw [h]; exact Out21.A6.mem_m10_iff x)
    exact key w183fin_lM10 w183fin_odd_m10 hl1 hl2
  · obtain ⟨hl1, hl2⟩ := w183fin_autL_spec
    exact key autL w183fin_odd_aut (fun x => by rw [h]; exact hl1 x) (fun c hc => by
      obtain ⟨x, hx, hxc⟩ := hl2 c hc
      exact ⟨x, by rw [h]; exact hx, hxc⟩)

section T2aSec

open CFSG.Quasithin Equiv

theorem w183fin_T2a {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal]
    (e : ↥L ≃* alternatingGroup (Fin 6)) (θ : ↥s6 →* Perm (Fin 6))
    (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
    (hψθ : ∀ x : ↥A6Models.psl29, ((ψ x : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      θ (Subgroup.inclusion psl29_le_s6 x))
    (τ : Y) (h : ActsOnDynkinMod ⊥ L τ) :
    ((Unc25K1.A6Model.thetaEquiv (e.trans ψ.symm) (MulAut.conjNormal τ) :
      ↥A6Models.autA6) : P10) ∉ s6 := by
  classical
  intro h6
  obtain ⟨hτN, P, hPpar, hmove⟩ := h
  obtain ⟨-, hPL, hPmax, S, -, hSL, hSpow, hSidx, hNS⟩ := hPpar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowIn 2 S L := by
    refine ⟨hSL, fun g => ?_, hSidx⟩
    obtain ⟨k, hk⟩ := hSpow (g : Y) g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTsyl : IsSylowIn 2 (S.map (MulAut.conj τ).toMonoidHom) L :=
    Ch1Sec3.isSylowIn_map_conj hSyl hτN
  obtain ⟨hh, hhL, hconjT⟩ := Ch1Sec3.exists_conj_of_isSylowIn hSyl hTsyl
  have hmemT : ∀ x : Y, x ∈ S.map (MulAut.conj τ).toMonoidHom ↔ τ⁻¹ * x * τ ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨τ⁻¹ * x * τ, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hτ'S : ∀ k : Y, k ∈ S ↔ (hh⁻¹ * τ) * k * (hh⁻¹ * τ)⁻¹ ∈ S := by
    intro k
    have h1 := hconjT (τ * k * τ⁻¹)
    rw [hmemT] at h1
    have e1 : τ⁻¹ * (τ * k * τ⁻¹) * τ = k := by group
    have e2 : hh⁻¹ * (τ * k * τ⁻¹) * hh = (hh⁻¹ * τ) * k * (hh⁻¹ * τ)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have hτ'N : (hh⁻¹ * τ) ∈ Subgroup.normalizer (L : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hhL)) hτN
  set φ : ↥L ≃* ↥A6Models.psl29 := e.trans ψ.symm with hφ
  set Θ := Unc25K1.A6Model.thetaEquiv φ with hΘdef
  have hΘL : ∀ l' : ↥L, ((Θ (MulAut.conjNormal (l' : Y)) : ↥A6Models.autA6) : P10) ∈
      A6Models.psl29 := by
    intro l'
    have : Θ (MulAut.conjNormal (l' : Y)) =
        ⟨(φ l' : P10), A6Facts.psl29_le_autA6 (φ l').2⟩ := by
      apply Unc25K1.A6Model.thetaEquiv_eq φ
      intro k
      have hk : (MulAut.conjNormal (l' : Y) : MulAut ↥L) k = l' * k * l'⁻¹ := rfl
      rw [hk, map_mul, map_mul, map_inv]
      simp
    rw [this]
    exact (φ l').2
  have hΘτ' : ((Θ (MulAut.conjNormal (hh⁻¹ * τ)) : ↥A6Models.autA6) : P10) ∈ s6 := by
    have e1 : (MulAut.conjNormal (hh⁻¹ * τ) : MulAut ↥L) =
        (MulAut.conjNormal hh : MulAut ↥L)⁻¹ * MulAut.conjNormal τ := by
      rw [map_mul, map_inv]
    rw [e1, map_mul, map_inv]
    have := s6.mul_mem (s6.inv_mem (psl29_le_s6 (hΘL ⟨hh, hhL⟩))) h6
    simpa using this
  obtain ⟨π, hπ⟩ := Unc25K1.A6Model.s6_induces θ ψ hψθ e (MulAut.conjNormal (hh⁻¹ * τ)) hΘτ'
  have hLcard : Nat.card ↥L = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact Unc25K1.A6Model.card_alt6
  have hScard : Nat.card S = 8 := by
    rw [hSyl.card_eq, hLcard, Unc25K1.A6Model.factorization_360]
    norm_num
  have hS'card : Nat.card (S.subgroupOf L) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv]
    exact hScard
  have hSP : S ≤ P := fun x hx => hNS (Subgroup.mem_inf.2 ⟨hSL hx, Subgroup.le_normalizer hx⟩)
  have hPstab : ∀ x : Y, x ∈ P ↔ (hh⁻¹ * τ) * x * (hh⁻¹ * τ)⁻¹ ∈ P := by
    by_cases hPS : P = S
    · subst hPS
      exact hτ'S
    · have hPX' : S.subgroupOf L ≤ P.subgroupOf L := fun k hk => hSP hk
      have hXP' : P.subgroupOf L ≠ S.subgroupOf L := by
        intro h
        apply hPS
        refine le_antisymm ?_ hSP
        intro x hx
        have hxK : x ∈ L := hPL.le hx
        have : (⟨x, hxK⟩ : ↥L) ∈ P.subgroupOf L := hx
        rw [h] at this
        exact this
      have hXtop : P.subgroupOf L ≠ ⊤ := by
        intro h
        apply hPL.ne
        refine le_antisymm hPL.le fun x hx => ?_
        have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := by rw [h]; trivial
        exact this
      have hγP : ∀ k : ↥L, k ∈ S.subgroupOf L ↔
          (MulAut.conjNormal (hh⁻¹ * τ) : MulAut ↥L) k ∈ S.subgroupOf L := by
        intro k
        exact hτ'S (k : Y)
      have key := Unc25K1.A6Model.key_of_iso e (S.subgroupOf L) (P.subgroupOf L) hS'card hPX'
        hXP' hXtop (MulAut.conjNormal (hh⁻¹ * τ)) π hπ hγP
      intro x
      by_cases hxL : x ∈ L
      · exact key ⟨x, hxL⟩
      · constructor
        · intro hx
          exact absurd (hPL.le hx) hxL
        · intro hx
          exact absurd ((Subgroup.mem_normalizer_iff.1 hτ'N x).2 (hPL.le hx)) hxL
  apply hmove hh hhL
  ext x
  rw [mem_conjSubgroup_iff]
  have h1 := hPstab ((τ⁻¹ * hh) * x * (τ⁻¹ * hh)⁻¹)
  have e3 : (hh⁻¹ * τ) * ((τ⁻¹ * hh) * x * (τ⁻¹ * hh)⁻¹) * (hh⁻¹ * τ)⁻¹ = x := by group
  rw [e3] at h1
  exact h1

end T2aSec

theorem w183fin_finA6 : FinA6 :=
  w183fin_finA6_of_T2a fun {_} _ _ L _ e θ ψ hψθ τ h => w183fin_T2a L e θ ψ hψθ τ h

theorem w183fin_finGraphOdd_A6 :
    ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsAlt ↥L 6 →
      Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ a : Y, orderOf a = 2 →
        ¬ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x} :=
  w183fin_finGraphOdd_A6_of_T2a fun {_} _ _ L _ e θ ψ hψθ τ h => w183fin_T2a L e θ ψ hψθ τ h

end CFSG.LocalAnalysis.WeakClosure81

end
