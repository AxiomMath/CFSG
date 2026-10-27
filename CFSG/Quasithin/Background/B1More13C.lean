module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1MoreTwelve

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B113

variable {V : Type} [CommGroup V] [Finite V]

theorem conjClosure_inf_pCoreOf_twelveM {T K : Subgroup (MulAut V)} (hK3 : Nat.card ↥K = 3)
    (hsub : IsSubnormal K (T ⊔ K)) :
    conjClosure K T ⊓ pCoreOf 2 (twelveM T K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (twelveM T K)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (twelveM T K)
  obtain ⟨j, hj⟩ := hQ2 ⟨x, hx.2⟩
  exact B19Aux.eq_one_of_odd_orderOf_of_pow
    (B1Red.odd_orderOf_of_isPGroup_three (B1Red.isPGroup_conjClosure hK3 hsub) hx.1) (k := j)
    (congrArg Subtype.val hj)

omit [Finite V] in
theorem twelveM_le_normalizer_conjClosure (T K : Subgroup (MulAut V)) :
    twelveM T K ≤ Subgroup.normalizer (conjClosure K T : Set (MulAut V)) :=
  sup_le ((B6.ffJ_le T).trans (le_normalizer_conjClosure K T)) Subgroup.le_normalizer

theorem conj_inv_aux {Γ : Type*} [Group Γ] (Y S Kk : Γ) (hS : S⁻¹ = S)
    (h2 : S * Kk * S⁻¹ = Kk⁻¹) (hcomm : Kk⁻¹ * Y = Y * Kk⁻¹) :
    (Y * S⁻¹) * Kk * (Y * S⁻¹)⁻¹ = Kk⁻¹ := by
  calc (Y * S⁻¹) * Kk * (Y * S⁻¹)⁻¹ = Y * (S⁻¹ * Kk * S) * Y⁻¹ := by group
    _ = Y * (S * Kk * S⁻¹) * Y⁻¹ := by rw [hS]
    _ = Y * Kk⁻¹ * Y⁻¹ := by rw [h2]
    _ = Kk⁻¹ := by rw [← hcomm]; group

theorem exists_inverting_element (hV : ∀ v : V, v ^ 2 = 1) {G T K L : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hK3 : Nat.card ↥K = 3)
    (hKJ : ⁅K, ffJ T⁆ = K) (hsub : IsSubnormal K (T ⊔ K))
    (hMnormL : twelveM T K ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {t : MulAut V} (ht : t ∈ T) (htL : t ∈ L) (hnorm : ¬ ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    ∃ e ∈ L, ∀ k ∈ K, e * k * e⁻¹ = k⁻¹ := by
  obtain ⟨-, hMnorm, -, -, Mb, hMbIDP, hMbSL, hMbImg, hMbEq⟩ := B1_12 hV hT hK3 hKJ hsub
  let i₀ : conjSetUnder T K := ⟨K, 1, T.one_mem, Subgroup.ext fun x =>
    ⟨fun hx => ⟨x, hx, by simp⟩, by rintro ⟨y, hy, rfl⟩; simpa using hy⟩⟩
  let j : conjSetUnder T K := ⟨K.map (MulAut.conj t).toMonoidHom, t, ht, rfl⟩
  have hji : i₀ ≠ j := by
    intro h
    apply hnorm
    intro k hk
    have hjK : K.map (MulAut.conj t).toMonoidHom = K := (congrArg Subtype.val h).symm
    have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, by simp⟩
    rwa [hjK] at hmem
  obtain ⟨e0⟩ := hMbSL i₀
  obtain ⟨s₀, hs₀1, hs₀2⟩ : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      s ≠ 1 ∧ s ^ 2 = 1 := by decide
  obtain ⟨sb, hsb⟩ : ∃ sb : ↥(Mb i₀), sb = e0.symm s₀ := ⟨_, rfl⟩
  have hsb1 : sb ≠ 1 := fun h => hs₀1 (by simpa [hsb] using congrArg e0 h)
  have hsb2 : sb ^ 2 = 1 := by
    apply e0.injective
    rw [map_pow, hsb, MulEquiv.apply_symm_apply, map_one]
    exact hs₀2
  have h6 : Nat.card ↥(Mb i₀) = 6 := by
    rw [Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hsbinv : (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))⁻¹ =
      (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K))) := by
    have : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsb2)
    exact congrArg Subtype.val this
  obtain ⟨m, hm⟩ := secMk_surjective (A := twelveM T K) (B := pCoreOf 2 (twelveM T K))
    (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))
  obtain ⟨y, hy⟩ : ∃ y : ↥(twelveM T K), (y : MulAut V) = t * (m : MulAut V) * t⁻¹ :=
    ⟨⟨t * (m : MulAut V) * t⁻¹, hMnorm t ht m m.2⟩, rfl⟩
  have hu : secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y ∈ Mb j :=
    (hMbEq t ht i₀ j rfl m y hy).1 (by rw [hm]; exact sb.2)
  obtain ⟨e, he⟩ : ∃ e : ↥(twelveM T K), e = y * m⁻¹ := ⟨_, rfl⟩
  have heval : (e : MulAut V) = t * (m : MulAut V) * t⁻¹ * (m : MulAut V)⁻¹ := by
    rw [he]
    simp [hy]
  refine ⟨(e : MulAut V), ?_, ?_⟩
  · rw [heval]
    have h1 : (m : MulAut V) * t⁻¹ * (m : MulAut V)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hMnormL m.2) t⁻¹).1 (L.inv_mem htL)
    have h2 : t * (m : MulAut V) * t⁻¹ * (m : MulAut V)⁻¹ =
        t * ((m : MulAut V) * t⁻¹ * (m : MulAut V)⁻¹) := by group
    rw [h2]
    exact L.mul_mem htL h1
  · intro k hk
    have hkK₀ : k ∈ conjClosure K T := le_conjClosure K T hk
    have hkM : k ∈ twelveM T K := Subgroup.mem_sup_right hkK₀
    obtain ⟨kk, hkk⟩ : ∃ kk : ↥(twelveM T K), kk = ⟨k, hkM⟩ := ⟨_, rfl⟩
    have hkkval : (kk : MulAut V) = k := by rw [hkk]
    have hkbar : secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk ∈ oddCoreOfSub (Mb i₀) := by
      rw [← hMbImg i₀]
      exact secMk_mem_secImg (x := kk) (by rw [hkkval]; exact hk)
    obtain ⟨hkbM, hkb3⟩ := (B1Red.mem_oddCoreOfSub_iff_of_card_six h6).1 hkbar
    obtain ⟨Kb, hKb⟩ : ∃ Kb : ↥(Mb i₀),
        (Kb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K))) =
          secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk := ⟨⟨_, hkbM⟩, rfl⟩
    have hsKs : sb * Kb * sb⁻¹ = Kb⁻¹ := by
      by_cases hK1 : Kb = 1
      · rw [hK1]; simp
      · refine B1Red.conj_inv_of_mulEquiv e0 ?_ hK1 hsb2 hsb1
        apply Subtype.ext
        rw [Subgroup.coe_pow, hKb]
        exact hkb3
    have h2 : (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K))) *
        secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk *
        (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))⁻¹ =
        (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk)⁻¹ := by
      rw [← hKb]
      exact congrArg Subtype.val hsKs
    have hcomm : (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk)⁻¹ *
        secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y =
        secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y *
          (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk)⁻¹ := by
      rw [← hKb]
      exact hMbIDP.1 i₀ j hji ((Kb⁻¹ : ↥(Mb i₀)) : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))
        (Kb⁻¹).2 _ hu
    have h1 : secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) e =
        secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y *
          (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))⁻¹ := by
      rw [he, map_mul, map_inv, hm]
    have hmk : secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) (e * kk * e⁻¹) =
        secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk⁻¹ := by
      have e1 : secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) (e * kk * e⁻¹) =
          (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y *
              (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))⁻¹) *
            secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) kk *
            (secMk (twelveM T K) (pCoreOf 2 (twelveM T K)) y *
              (sb : SecQuot (twelveM T K) (pCoreOf 2 (twelveM T K)))⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv, h1]
      rw [e1, map_inv]
      exact conj_inv_aux _ _ _ hsbinv h2 hcomm
    have hekK₀ : (e : MulAut V) * k * (e : MulAut V)⁻¹ ∈ conjClosure K T :=
      B19Aux.conj_mem_of_le_normalizer (twelveM_le_normalizer_conjClosure T K) e.2 hkK₀
    have hmem : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V)⁻¹ *
        ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) ∈ pCoreOf 2 (twelveM T K) :=
      secMk_eq_secMk_iff.1 hmk
    have hone : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V)⁻¹ *
        ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) = 1 := by
      have hmemK₀ : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V)⁻¹ *
          ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) ∈ conjClosure K T := by
        refine (conjClosure K T).mul_mem ((conjClosure K T).inv_mem ?_) ?_
        · have : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V) =
              (e : MulAut V) * k * (e : MulAut V)⁻¹ := by rw [← hkkval]; rfl
          rw [this]
          exact hekK₀
        · have : ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) = k⁻¹ := by rw [← hkkval]; rfl
          rw [this]
          exact (conjClosure K T).inv_mem hkK₀
      have hmem' : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V)⁻¹ *
          ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) ∈
          conjClosure K T ⊓ pCoreOf 2 (twelveM T K) := ⟨hmemK₀, hmem⟩
      rw [conjClosure_inf_pCoreOf_twelveM hK3 hsub] at hmem'
      exact hmem'
    have h3 : ((e * kk * e⁻¹ : ↥(twelveM T K)) : MulAut V) =
        (e : MulAut V) * k * (e : MulAut V)⁻¹ := by rw [← hkkval]; rfl
    have h4 : ((kk⁻¹ : ↥(twelveM T K)) : MulAut V) = k⁻¹ := by rw [← hkkval]; rfl
    rw [h3, h4] at hone
    exact inv_mul_eq_one.1 hone

omit [Finite V] in
theorem le_of_inverting {K L : Subgroup (MulAut V)} (hK3 : Nat.card ↥K = 3)
    (hKL : K ≤ Subgroup.normalizer (L : Set (MulAut V))) {e : MulAut V} (heL : e ∈ L)
    (hinv : ∀ k ∈ K, e * k * e⁻¹ = k⁻¹) : K ≤ L := by
  intro k hk
  have hk3 : k ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥K) (x := (⟨k, hk⟩ : ↥K))
    rw [hK3] at this
    exact congrArg Subtype.val this
  have h1 : k⁻¹ * e * k ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (hKL (K.inv_mem hk)) e).1 heL
    simpa using this
  have h2 : (k⁻¹ * e * k) * e⁻¹ = k := by
    have h3 : e * k * e⁻¹ = k⁻¹ := hinv k hk
    calc (k⁻¹ * e * k) * e⁻¹ = k⁻¹ * (e * k * e⁻¹) := by group
      _ = k⁻¹ * k⁻¹ := by rw [h3]
      _ = k := by
        have : k⁻¹ * k⁻¹ = k⁻¹ * k⁻¹ * (k ^ 3) := by rw [hk3, mul_one]
        rw [this]
        group
  rw [← h2]
  exact L.mul_mem h1 (L.inv_mem heL)

theorem card_three_le_or_centralizes (hV : ∀ v : V, v ^ 2 = 1) {G T K L : Subgroup (MulAut V)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hK3 : Nat.card ↥K = 3)
    (hKJ : ⁅K, ffJ T⁆ = K) (hsub : IsSubnormal K (T ⊔ K))
    (hMnormL : twelveM T K ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hKL : K ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    K ≤ L ∨ K ≤ Subgroup.centralizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
  by_cases hc : K ≤ Subgroup.centralizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))
  · exact Or.inr hc
  left
  obtain ⟨k₀, hk₀K, hk₀⟩ : ∃ k₀ ∈ K, k₀ ∉ Subgroup.centralizer
      ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
    by_contra hcon
    push Not at hcon
    exact hc fun k hk => hcon k hk
  rw [Subgroup.mem_centralizer_iff] at hk₀
  push Not at hk₀
  obtain ⟨t, htTL, htk⟩ := hk₀
  have htT : t ∈ T := htTL.1
  have htL : t ∈ L := htTL.2
  by_cases hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K
  ·
    have htn : t ∈ Subgroup.normalizer (K : Set (MulAut V)) :=
      A4.mem_normalizer_of_conj_mem hnorm
    have hzn : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
      Subgroup.zpowers_le.2 htn
    have hbK : ∀ b ∈ Subgroup.zpowers t, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
      B19Aux.conj_mem_of_le_normalizer hzn hb hk
    rcases B1Red.commutator_eq_or_commute (Or.inr hK3) hbK with h | h
    · calc K = ⁅K, Subgroup.zpowers t⁆ := h.symm
        _ ≤ L := by
          rw [Subgroup.commutator_le]
          intro k hk b hb
          have hbL : b ∈ L := (Subgroup.zpowers_le.2 htL) hb
          have h1 : k * b * k⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.1 (hKL hk) b).1 hbL
          have h3 : ⁅k, b⁆ = (k * b * k⁻¹) * b⁻¹ := rfl
          rw [h3]
          exact L.mul_mem h1 (L.inv_mem hbL)
    · exact absurd (h t (Subgroup.mem_zpowers t) k₀ hk₀K) htk
  ·
    obtain ⟨e, heL, hinv⟩ := exists_inverting_element hV hT hK3 hKJ hsub hMnormL htT htL hnorm
    exact le_of_inverting hK3 hKL heL hinv

end B113

end CFSG.Quasithin
