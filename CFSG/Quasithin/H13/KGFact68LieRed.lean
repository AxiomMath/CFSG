module

public import CFSG.Quasithin.H13.KGFact68AltBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Defs

variable {S : Type} [Group S]

structure CartanSingerHyp (P : Subgroup S) (𝓡 : Subgroup (MulAut S)) (G : Subgroup S) :
    Prop where
  isPGroup : IsPGroup 2 𝓡
  normalizes : ∀ ρ ∈ 𝓡, ∀ p ∈ P, ρ p ∈ P
  inner : ∀ p ∈ P, MulAut.conj p ∈ 𝓡
  le : ∀ g ∈ G, g ∈ P ∧ ∀ t ∈ P, g * t = t * g
  sq : ∀ g ∈ G, g * g = 1
  four_le : 4 ≤ Nat.card G
  fixed : ∀ ρ ∈ 𝓡, ∀ g ∈ G, ρ g = g

@[expose] def CentralizerCond (G : Subgroup S) : Prop :=
  ∀ g ∈ G, g ≠ 1 → ∀ y : S, y * g = g * y → (∃ k : ℕ, y ^ 2 ^ k = 1) →
    ∀ g' ∈ G, y * g' = g' * y

@[expose] def CartanSingerConcl (P : Subgroup S) (𝓡 : Subgroup (MulAut S)) (G : Subgroup S) :
    Prop :=
  ∃ x ∈ Subgroup.normalizer (P : Set S), Odd (orderOf x) ∧ (∀ ρ ∈ 𝓡, ρ x * x⁻¹ ∈ P) ∧
    ((∀ g ∈ G, x * g * x⁻¹ ∈ G) →
      ∀ j : ℕ, (∀ g ∈ G, x ^ j * g = g * x ^ j) ↔ (Nat.card G - 1) ∣ j)

end Defs

@[expose] def CartanSinger (S : Type) [Group S] : Prop :=
  ∀ (P : Sylow 2 S) (𝓡 : Subgroup (MulAut S)) (G : Subgroup S),
    CartanSingerHyp (P : Subgroup S) 𝓡 G → CentralizerCond G →
      CartanSingerConcl (P : Subgroup S) 𝓡 G

@[expose] def CartanSingerCover (S : Type) [Group S] : Prop :=
  ∀ (P : Sylow 2 S) (𝓡 : Subgroup (MulAut S)) (G : Subgroup S),
    CartanSingerHyp (P : Subgroup S) 𝓡 G → CartanSingerConcl (P : Subgroup S) 𝓡 G

theorem CartanSingerCover.cartanSinger {S : Type} [Group S] (h : CartanSingerCover S) :
    CartanSinger S :=
  fun P 𝓡 G hG _ => h P 𝓡 G hG

theorem cartanSingerCover_of_card_omegaZ {S : Type} [Group S] [Finite S]
    (h : ∀ P : Sylow 2 S, Nat.card (omegaZ (P : Subgroup S)) ≤ 2) : CartanSingerCover S := by
  intro P 𝓡 G hG
  exfalso
  have h1 : Nat.card G ≤ Nat.card (omegaZ (P : Subgroup S)) :=
    Nat.card_le_card_of_injective
      (fun g : G => (⟨g, (hG.le g g.2).1, (hG.le g g.2).2, hG.sq g g.2⟩ :
        omegaZ (P : Subgroup S)))
      fun a b hab => by
        have h := congrArg (fun w : omegaZ (P : Subgroup S) => (w : S)) hab
        exact Subtype.ext h
  have h2 := hG.four_le
  have h3 := h P
  omega

theorem cartanSingerCover_of_isCyclic {S : Type} [Group S] [Finite S]
    (h : ∀ P : Sylow 2 S, IsCyclic (Subgroup.center ↥(P : Subgroup S))) :
    CartanSingerCover S :=
  cartanSingerCover_of_card_omegaZ fun P => card_omegaZ_le_two _ (h P)

@[expose] def U33AutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 3 1 →
    ∀ β : K ≃* K, (∀ x, β (β x) = x) → (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) →
      Ch1.IsInnerAut β

section Facts

theorem le_sylow_of_normal {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : IsPGroup 2 N) (P : Sylow 2 X) : N ≤ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := hN.to_sup_of_normal_left P.isPGroup'
  have heq := P.is_maximal' hsup le_sup_right
  rw [← heq]
  exact le_sup_left

theorem pow_mul_inv_mem {S : Type} [Group S] {Q : Subgroup S} {ρ : MulAut S} {x : S}
    (hxN : x ∈ Subgroup.normalizer (Q : Set S)) (hx : ρ x * x⁻¹ ∈ Q) (n : ℕ) :
    ρ (x ^ n) * (x ^ n)⁻¹ ∈ Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ n * (ρ x * x⁻¹) * (x ^ n)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxN n) _).mp hx
    have h2 := Q.mul_mem ih h1
    convert h2 using 1
    rw [pow_succ, map_mul]
    group

theorem conj_pow_mem {S : Type} [Group S] {G : Subgroup S} {y : S}
    (hy : ∀ g ∈ G, y * g * y⁻¹ ∈ G) (u : ℕ) : ∀ g ∈ G, y ^ u * g * (y ^ u)⁻¹ ∈ G := by
  induction u with
  | zero =>
    intro g hg
    simpa using hg
  | succ u ih =>
    intro g hg
    have := ih _ (hy g hg)
    convert this using 1
    rw [pow_succ]
    group

end Facts

section Reduction

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem center_eq_bot_of_simple (h : E6.E68Hyp L A R z) (hS : IsSimpleGroup ↥L) :
    Subgroup.center ↥L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h1 | h1
  · exact h1
  · exfalso
    have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial h.quasisimple
    have hle : commutator ↥L ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have hb : b ∈ Subgroup.center ↥L := h1 ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
    rw [Group.isPerfect_def.mp h.quasisimple.1] at hle
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    exact hx (Subgroup.mem_bot.mp (hle (Subgroup.mem_top x)))

theorem e68Concl_of_quot {S : Type} [Group S] [Finite S] (h : E6.E68Hyp L A R z)
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) (ψ : (↥L ⧸ Subgroup.center ↥L) ≃* S)
    (hinn : ∀ β : S ≃* S, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 S, ∀ t ∈ (P : Subgroup S), β t = t) → Ch1.IsInnerAut β)
    (hCS : ∀ (P : Sylow 2 S) (𝓡 : Subgroup (MulAut S)) (G : Subgroup S),
      CartanSingerHyp (P : Subgroup S) 𝓡 G → (Subgroup.center ↥L = ⊥ → CentralizerCond G) →
        CartanSingerConcl (P : Subgroup S) 𝓡 G) :
    E6.E68Concl L A R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp h.quasisimple.1
  have hZS : Subgroup.center S = ⊥ := by
    have hq : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
      have := h.quasisimple.2.1
      obtain ⟨u, v, huv⟩ := h.quasisimple.2.2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (↥L ⧸ Subgroup.center ↥L)) with h1 | h1
      · exact h1
      · exfalso
        apply huv
        have hv : v ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := h1 ▸ Subgroup.mem_top v
        exact Subgroup.mem_center_iff.mp hv u
    rw [eq_bot_iff]
    intro c hc
    have h1 : ψ.symm c ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc (ψ g)
    rw [hq, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← ψ.apply_symm_apply c, h1, map_one]
  have hinjS := conj_injective_of_center hZS
  let ind : MulAut ↥L →* MulAut S :=
    { toFun := fun α => MulAut.congr ψ (quotAut (Subgroup.center ↥L) α)
      map_one' := by simp only [quotAut_one, map_one]
      map_mul' := fun α β => by simp only [quotAut_mul, map_mul] }
  have hind_inj : Function.Injective ind := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have h1 : quotAut (Subgroup.center ↥L) α = 1 :=
      (MulAut.congr ψ).injective (hα.trans (map_one _).symm)
    exact eq_one_of_quotAut_eq_one le_rfl hperf h1
  have hind_apply : ∀ (α : MulAut ↥L) (x : ↥L),
      ind α (ψ (x : ↥L ⧸ Subgroup.center ↥L)) = ψ ((α x : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
    intro α x
    show ψ (quotAut _ α (ψ.symm (ψ (x : ↥L ⧸ Subgroup.center ↥L)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  let f : ↥L →* S := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Surjective f := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hf_apply : ∀ x : ↥L, f x = ψ (x : ↥L ⧸ Subgroup.center ↥L) := fun _ => rfl
  have hind_f : ∀ (α : MulAut ↥L) (x : ↥L), ind α (f x) = f (α x) := fun α x => by
    rw [hf_apply, hf_apply, hind_apply]
  have hind_conj : ∀ u : ↥L, ind (MulAut.conj u) = MulAut.conj (f u) := by
    intro u
    ext s
    obtain ⟨w, rfl⟩ := hf s
    rw [hind_f, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  let Q : Sylow 2 S := (sylowIn h).mapSurjective hf
  have hQmem : ∀ t, t ∈ (Q : Subgroup S) ↔
      ∃ p ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L), f p = t := fun t => Subgroup.mem_map
  have hP_R : ∀ p ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L), (p : Y) ∈ R := fun p hp => by
    rw [sylowIn_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hp
    exact hp.1
  have hfix : ∀ a (ha : a ∈ A), ∀ t ∈ (Q : Subgroup S), ind (conjOn L a (leN h ha)) t = t := by
    intro a ha t ht
    obtain ⟨p, hp, rfl⟩ := (hQmem t).mp ht
    rw [hind_f, conjOn_fix_of_hyp h ha hp]
  have hsqA : ∀ a (ha : a ∈ A),
      ind (conjOn L a (leN h ha)) * ind (conjOn L a (leN h ha)) = 1 := by
    intro a ha
    rw [← map_mul, conjOn_sq_of_hyp h ha, map_one]
  have hAin : ∀ a (ha : a ∈ A), ∃ g : S, ind (conjOn L a (leN h ha)) = MulAut.conj g := by
    intro a ha
    obtain ⟨l, hl⟩ := hinn _ (fun x => by
        have := congrArg (fun γ : MulAut S => γ x) (hsqA a ha)
        simpa using this) ⟨Q, hfix a ha⟩
    exact ⟨l⁻¹, by ext x; rw [hl x, MulAut.conj_apply, inv_inv]⟩
  have hΩ : ∀ (g : S) (a : Y) (ha : a ∈ A), ind (conjOn L a (leN h ha)) = MulAut.conj g →
      g ∈ omegaZ (Q : Subgroup S) := by
    intro g a ha hag
    have hgg : g * g = 1 := by
      apply hinjS
      rw [map_mul, ← hag, hsqA a ha, map_one]
    refine mem_omegaZ_of_commute Q (fun t ht => ?_) hgg
    have h1 := hfix a ha t ht
    rw [hag, MulAut.conj_apply] at h1
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [h1]
  set H := ((actHom L A (leN h)).range).map ind with hH
  set G := H.comap (MulAut.conj : S →* MulAut S) with hG
  have hHle : H ≤ (MulAut.conj : S →* MulAut S).range := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨g, hg⟩ := hAin a a.2
    exact ⟨g, hg.symm⟩
  have hGmem : ∀ g : S,
      g ∈ G ↔ ∃ a, ∃ ha : a ∈ A, ind (conjOn L a (leN h ha)) = MulAut.conj g := by
    intro g
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, hag⟩
      exact ⟨a, a.2, hag⟩
    · rintro ⟨a, ha, hag⟩
      exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, hag⟩
  have hGcard : Nat.card G = (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A := by
    have h1 : Nat.card G = Nat.card H := by
      rw [← Subgroup.card_map_of_injective hinjS, hG, Subgroup.map_comap_eq_self hHle]
    rw [h1, relIndex_eq_card_range L A (leN h), hH, Subgroup.card_map_of_injective hind_inj]
  set 𝓡 := ((actHom L R h.normalizer).range).map ind with h𝓡
  have h𝓡mem : ∀ ρ ∈ 𝓡, ∃ r, ∃ hr : r ∈ R, ρ = ind (conjOn L r (h.normalizer hr)) := by
    rintro _ ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  have hR𝓡 : ∀ r (hr : r ∈ R), ind (conjOn L r (h.normalizer hr)) ∈ 𝓡 :=
    fun r hr => ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
  have hHyp : CartanSingerHyp (Q : Subgroup S) 𝓡 G := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : IsPGroup 2 (actHom L R h.normalizer).range :=
        h.isPGroup.of_surjective _ (actHom L R h.normalizer).rangeRestrict_surjective
      exact h1.map ind
    · intro ρ hρ t ht
      obtain ⟨r, hr, rfl⟩ := h𝓡mem ρ hρ
      obtain ⟨p, hp, rfl⟩ := (hQmem t).mp ht
      refine (hQmem _).mpr ⟨conjOn L r (h.normalizer hr) p, ?_, (hind_f _ p).symm⟩
      rw [sylowIn_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hp ⊢
      refine ⟨?_, (conjOn L r (h.normalizer hr) p).2⟩
      rw [conjOn_coe]
      exact R.mul_mem (R.mul_mem hr hp.1) (R.inv_mem hr)
    · intro t ht
      obtain ⟨p, hp, rfl⟩ := (hQmem t).mp ht
      rw [← hind_conj, ← conjOn_of_mem L p (h.normalizer (hP_R p hp))]
      exact hR𝓡 _ (hP_R p hp)
    · intro g hg
      obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
      exact ⟨(hΩ g a ha hag).1, (hΩ g a ha hag).2.1⟩
    · intro g hg
      obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
      exact (hΩ g a ha hag).2.2
    · rw [hGcard]
      exact h.four_le
    · intro ρ hρ g hg
      obtain ⟨r, hr, rfl⟩ := h𝓡mem ρ hρ
      obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
      have hra : r * a = a * r :=
        (Subgroup.mem_centralizer_iff.mp (h.centralizer hr) a ha).symm
      have hcomm : conjOn L r (h.normalizer hr) * conjOn L a (leN h ha) =
          conjOn L a (leN h ha) * conjOn L r (h.normalizer hr) := by
        rw [← conjOn_mul, ← conjOn_mul]
        congr 1
      apply hinjS
      rw [← mulAut_conj_conj, ← hag, ← map_mul, ← map_inv, ← map_mul, hcomm,
        mul_inv_cancel_right]
  have hCg : Subgroup.center ↥L = ⊥ → CentralizerCond G := by
    intro hZL g hg hg1 y hyg hy2 g' hg'
    obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
    obtain ⟨a', ha', hag'⟩ := (hGmem g').mp hg'
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have h1 : (u : ↥L ⧸ Subgroup.center ↥L) = 1 := ψ.injective (hu.trans (map_one ψ).symm)
      rw [QuotientGroup.eq_one_iff, hZL, Subgroup.mem_bot] at h1
      exact h1
    obtain ⟨y₁, rfl⟩ := hf y
    have hna : a ∉ Subgroup.centralizer (L : Set Y) := by
      intro hc
      apply hg1
      apply hinjS
      rw [← hag, (conjOn_eq_one_iff L (leN h ha)).mpr hc, map_one, map_one]
    have hya : conjOn L a (leN h ha) y₁ = y₁ := by
      apply hfinj
      rw [← hind_f, hag, MulAut.conj_apply, ← hyg, mul_inv_cancel_right]
    have hya' : (y₁ : Y) * a = a * y₁ := by
      have h1 := congrArg Subtype.val hya
      rw [conjOn_coe] at h1
      calc (y₁ : Y) * a = (a * y₁ * a⁻¹) * a := by rw [h1]
        _ = a * y₁ := by group
    have hy2' : ∃ k : ℕ, (y₁ : Y) ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hy2
      refine ⟨k, ?_⟩
      have h1 : y₁ ^ 2 ^ k = 1 := hfinj (by rw [map_pow, hk, map_one])
      rw [← Subgroup.coe_pow, h1]
      rfl
    have hyA := h.centralizes a ha hna y₁ y₁.2 hya' hy2'
    have h3 := Subgroup.mem_centralizer_iff.mp hyA a' ha'
    have h4 : conjOn L a' (leN h ha') y₁ = y₁ := by
      apply Subtype.ext
      rw [conjOn_coe, h3, mul_inv_cancel_right]
    have h5 := hind_f (conjOn L a' (leN h ha')) y₁
    rw [h4, hag', MulAut.conj_apply] at h5
    calc f y₁ * g' = (g' * f y₁ * g'⁻¹) * g' := by rw [h5]
      _ = g' * f y₁ := by group
  obtain ⟨xq, hxN, hxodd, hxR, hxS⟩ := hCS Q 𝓡 G hHyp hCg
  obtain ⟨x₁, hx₁⟩ := hf xq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  set n := Nat.card ↥(Subgroup.center ↥L) with hn
  set x := x₁ ^ n with hxdef
  have hfx : f x = xq ^ n := by rw [hxdef, map_pow, hx₁]
  have hxodd' : Odd (orderOf x) := by
    have h1 : x ^ orderOf xq = 1 := by
      have h2 : x₁ ^ orderOf xq ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        apply ψ.injective
        rw [map_pow, map_one, ← hf_apply, hx₁]
        exact pow_orderOf_eq_one xq
      have h3 : (⟨_, h2⟩ : ↥(Subgroup.center ↥L)) ^ n = 1 := pow_card_eq_one'
      have h4 := congrArg Subtype.val h3
      rw [SubmonoidClass.coe_pow] at h4
      rw [hxdef, ← pow_mul, Nat.mul_comm, pow_mul]
      exact h4
    exact hxodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hGeven : 2 ∣ Nat.card G := by
    have hGp : IsPGroup 2 G := fun g => ⟨1, by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, pow_one, sq]
      exact hHyp.sq g g.2⟩
    rcases hGp.card_eq_or_dvd with h1 | h1
    · have := hHyp.four_le
      omega
    · exact h1
  have hcop : Nat.Coprime n (Nat.card G - 1) := by
    rw [hk]
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    obtain ⟨m, hm⟩ := hGeven
    have := hHyp.four_le
    exact ⟨m - 1, by omega⟩
  have hconj : ∀ (u : ↥L) {a : Y} (ha : a ∈ A) {g : S},
      ind (conjOn L a (leN h ha)) = MulAut.conj g →
      ((u : Y) * a * (u : Y)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set Y) ↔ f u * g = g * f u) := by
    intro u a ha g hag
    have hu : (u : Y) ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer u.2
    have hua : (u : Y) * a * (u : Y)⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hu (leN h ha)) (Subgroup.inv_mem _ hu)
    have hmem := Subgroup.mul_mem _ hua (Subgroup.inv_mem _ (leN h ha))
    have key : ind (conjOn L _ hmem) = MulAut.conj (f u * g * (f u)⁻¹ * g⁻¹) := by
      rw [conjOn_mul L hua (Subgroup.inv_mem _ (leN h ha)), conjOn_conj L u (leN h ha) hua,
        conjOn_inv L (leN h ha)]
      simp only [map_mul, map_inv, hind_conj, hag]
    rw [← conjOn_eq_one_iff L hmem, ← hind_inj.eq_iff, key, map_one, ← map_one MulAut.conj,
      hinjS.eq_iff]
    constructor
    · intro h1
      calc f u * g = (f u * g * (f u)⁻¹ * g⁻¹) * (g * f u) := by group
        _ = g * f u := by rw [h1, one_mul]
    · intro h1
      rw [h1]
      group
  refine ⟨(x : Y), x.2, by rwa [Subgroup.orderOf_coe], fun r hr => ?_, fun hnorm j => ?_⟩
  ·
    have h1 : ind (conjOn L r (h.normalizer hr)) (xq ^ n) * (xq ^ n)⁻¹ ∈ (Q : Subgroup S) :=
      pow_mul_inv_mem hxN (hxR _ (hR𝓡 r hr)) n
    have h2 : f (conjOn L r (h.normalizer hr) x * x⁻¹) ∈ (Q : Subgroup S) := by
      rw [map_mul, map_inv, ← hind_f, hfx]
      exact h1
    obtain ⟨p, hp, hpe⟩ := (hQmem _).mp h2
    have h3 : p⁻¹ * (conjOn L r (h.normalizer hr) x * x⁻¹) ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      apply ψ.injective
      rw [map_one, ← hf_apply, map_mul, map_inv, hpe, inv_mul_cancel]
    have hZP := le_sylow_of_normal hZ2 (sylowIn h)
    have h4 : conjOn L r (h.normalizer hr) x * x⁻¹ ∈
        ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) := by
      have := Subgroup.mul_mem _ hp (hZP h3)
      rwa [mul_inv_cancel_left] at this
    have h5 := hP_R _ h4
    rw [Subgroup.coe_mul, conjOn_coe, Subgroup.coe_inv] at h5
    have h6 := R.inv_mem h5
    convert h6 using 1
    group
  ·
    have hxGn : ∀ g ∈ G, xq ^ n * g * (xq ^ n)⁻¹ ∈ G := by
      intro g hg
      obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
      obtain ⟨b, hb, hab⟩ := hnorm a ha
      refine (hGmem _).mpr ⟨b, hb, ?_⟩
      have hx' : (x : Y) ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer x.2
      have hxa : (x : Y) * a * (x : Y)⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' (leN h ha)) (Subgroup.inv_mem _ hx')
      have hmem := Subgroup.mul_mem _ hxa (Subgroup.inv_mem _ (leN h hb))
      have h1 : conjOn L _ hmem = 1 := (conjOn_eq_one_iff L hmem).mpr hab
      rw [conjOn_mul L hxa (Subgroup.inv_mem _ (leN h hb)), conjOn_inv L (leN h hb),
        mul_inv_eq_one, conjOn_conj L x (leN h ha) hxa] at h1
      rw [← h1]
      simp only [map_mul, map_inv, hind_conj, hag, hfx]
    have hxG : ∀ g ∈ G, xq * g * xq⁻¹ ∈ G := by
      by_cases h1 : orderOf xq = 1
      · rw [orderOf_eq_one_iff] at h1
        intro g hg
        rw [h1]
        simpa using hg
      · have hm1 : 1 < orderOf xq := by
          have := orderOf_pos xq
          omega
        have hcop' : Nat.Coprime n (orderOf xq) := by
          rw [hk]
          exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxodd)
        obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop' hm1
        have hxu : (xq ^ n) ^ u = xq := by
          rw [← pow_mul, ← pow_mod_orderOf, hu, pow_one]
        intro g hg
        have := conj_pow_mem hxGn u g hg
        rwa [hxu] at this
    rw [← hGcard, ← hcop.symm.dvd_mul_left, ← hxS hxG (n * j)]
    constructor
    · intro hj g hg
      obtain ⟨a, ha, hag⟩ := (hGmem g).mp hg
      have h1 := (hconj (x ^ j) ha hag).mp (by rw [Subgroup.coe_pow]; exact hj a ha)
      rwa [map_pow, hfx, ← pow_mul] at h1
    · intro hj a ha
      obtain ⟨g, hag⟩ := hAin a ha
      rw [← Subgroup.coe_pow]
      refine (hconj (x ^ j) ha hag).mpr ?_
      rw [map_pow, hfx, ← pow_mul]
      exact hj g ((hGmem g).mpr ⟨a, ha, hag⟩)

theorem e68Concl_of_cartanSinger (h : E6.E68Hyp L A R z) (hS : IsSimpleGroup ↥L)
    (hinn : ∀ β : ↥L ≃* ↥L, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 ↥L, ∀ t ∈ (P : Subgroup ↥L), β t = t) → Ch1.IsInnerAut β)
    (hCS : CartanSinger ↥L) : E6.E68Concl L A R := by
  have hZ := center_eq_bot_of_simple h hS
  refine e68Concl_of_quot h (by rw [hZ]; exact IsPGroup.of_bot)
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hinn
    fun P 𝓡 G hG hC => hCS P 𝓡 G hG (hC hZ)

theorem e68Concl_of_cartanSingerCover {S : Type} [Group S] [Finite S] (h : E6.E68Hyp L A R z)
    (hZP : Subgroup.center ↥L = CFSG.pCore 2 ↥L) (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S)
    (hinn : ∀ β : S ≃* S, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 S, ∀ t ∈ (P : Subgroup S), β t = t) → Ch1.IsInnerAut β)
    (hCS : CartanSingerCover S) : E6.E68Concl L A R :=
  e68Concl_of_quot h (by rw [hZP]; exact CFSG.pCore_isPGroup)
    ((QuotientGroup.quotientMulEquivOfEq hZP).trans ψ) hinn fun P 𝓡 G hG _ => hCS P 𝓡 G hG

end Reduction

end CFSG.Quasithin.H13.KG68
