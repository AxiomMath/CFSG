module

public import CFSG.Quasithin.H13.L32NLem14331d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

theorem perm3_sq_of_two_pow {σ : Equiv.Perm (Fin 3)} {k : ℕ} (h : σ ^ (2 ^ k) = 1) :
    σ ^ 2 = 1 := by
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 ∨ (σ ^ 3 = 1 ∧ σ ≠ 1) := by decide
  rcases key σ with h2 | ⟨h3, h1⟩
  · exact h2
  · exfalso
    have ho : orderOf σ = 3 := orderOf_eq_prime h3 h1
    have hd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
    rw [ho] at hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)

theorem eq_bot_of_normal_isPGroup_perm3 {K : Subgroup (Equiv.Perm (Fin 3))} (hKn : K.Normal)
    (hK2 : IsPGroup 2 K) : K = ⊥ := by
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 →
      (σ * ((Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹)) ^ 2 = 1 →
      σ = 1 := by decide
  rw [eq_bot_iff]
  intro σ hσ
  have h2 : ∀ τ ∈ K, τ ^ 2 = 1 := by
    intro τ hτ
    obtain ⟨k, hk⟩ := hK2 ⟨τ, hτ⟩
    exact perm3_sq_of_two_pow (k := k) (by simpa using congrArg Subtype.val hk)
  have hc : (Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ ∈ K :=
    hKn.conj_mem σ hσ _
  exact Subgroup.mem_bot.mpr (key σ (h2 σ hσ) (h2 _ (K.mul_mem hσ hc)))

@[expose] def c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c3l : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := (c3, 1)

@[expose] def c3r : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := (1, c3)

theorem s3s3_left : ∀ σ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), σ * σ = 1 → σ.1 ≠ 1 →
    σ.2 ≠ 1 → (σ * (c3l * σ * c3l⁻¹)).2 = 1 ∧ (σ * (c3l * σ * c3l⁻¹)).1 ^ 3 = 1 ∧
      (σ * (c3l * σ * c3l⁻¹)).1 ≠ 1 := by
  decide +kernel

theorem s3s3_right : ∀ σ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), σ * σ = 1 → σ.1 ≠ 1 →
    σ.2 ≠ 1 → (σ * (c3r * σ * c3r⁻¹)).1 = 1 ∧ (σ * (c3r * σ * c3r⁻¹)).2 ^ 3 = 1 ∧
      (σ * (c3r * σ * c3r⁻¹)).2 ≠ 1 := by
  decide +kernel

theorem s3_gen : ∀ s : Equiv.Perm (Fin 3), s * s = 1 → s ≠ 1 → ∀ x : Equiv.Perm (Fin 3),
    ∃ g h : Equiv.Perm (Fin 3), x = g * s * g⁻¹ ∨ x = (g * s * g⁻¹) * (h * s * h⁻¹) := by
  decide

variable {W : Type} [Group W]

theorem s3s3_factor {N : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))} (hN : N.Normal)
    (h6 : Nat.card N = 6) {σ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)} (hσ : σ ∈ N)
    (hσ2 : σ * σ = 1) : σ.1 = 1 ∨ σ.2 = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hg2, hg3, hg1⟩ := s3s3_left σ hσ2 hcon.1 hcon.2
  obtain ⟨hh1, hh3, hh2⟩ := s3s3_right σ hσ2 hcon.1 hcon.2
  set x := σ * (c3l * σ * c3l⁻¹)
  set y := σ * (c3r * σ * c3r⁻¹)
  have hxN : x ∈ N := N.mul_mem hσ (hN.conj_mem σ hσ _)
  have hyN : y ∈ N := N.mul_mem hσ (hN.conj_mem σ hσ _)
  have hx3 : x ^ 3 = 1 := Prod.ext hg3 (by rw [Prod.pow_snd, hg2, one_pow]; rfl)
  have hy3 : y ^ 3 = 1 := Prod.ext (by rw [Prod.pow_fst, hh1, one_pow]; rfl) hh3
  have hx1 : x ≠ 1 := fun h' => hg1 (by rw [h']; rfl)
  have hy1 : y ≠ 1 := fun h' => hh2 (by rw [h']; rfl)
  have hxy : x * y = y * x := Prod.ext (by simp [Prod.fst_mul, hh1]) (by simp [Prod.snd_mul, hg2])
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply hh2
    have e : (x ^ k).2 = x.2 ^ k := map_zpow (MonoidHom.snd _ _) x k
    rw [← hk, e, hg2, one_zpow]
  have h9 := card_e9 (orderOf_eq_prime hx3 hx1) (orderOf_eq_prime hy3 hy1) hxy hyx
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ N :=
    sup_le ((Subgroup.zpowers_le).mpr hxN) ((Subgroup.zpowers_le).mpr hyN)
  have := Subgroup.card_dvd_of_le hle
  rw [h9, h6] at this
  norm_num at this

theorem s3s3_fst_of {N : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))} (hN : N.Normal)
    (h6 : Nat.card N = 6) {s : Equiv.Perm (Fin 3)} (hs : ((s, 1) : _ × _) ∈ N) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) : (∀ x : Equiv.Perm (Fin 3), ((x, 1) : _ × _) ∈ N) ∧ ∀ n ∈ N, n.2 = 1 := by
  have hconj : ∀ g : Equiv.Perm (Fin 3), ((g * s * g⁻¹, 1) : _ × _) ∈ N := by
    intro g
    have := hN.conj_mem _ hs ((g, 1) : _ × _)
    simpa using this
  have hall : ∀ x : Equiv.Perm (Fin 3), ((x, 1) : _ × _) ∈ N := by
    intro x
    obtain ⟨g, h, hx | hx⟩ := s3_gen s hs2 hs1 x
    · rw [hx]
      exact hconj g
    · rw [hx]
      simpa using N.mul_mem (hconj g) (hconj h)
  refine ⟨hall, ?_⟩
  set F := (MonoidHom.inl (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))).range with hF
  have hFN : F ≤ N := by
    rintro _ ⟨x, rfl⟩
    exact hall x
  have hF6 : Nat.card F = 6 := by
    rw [hF, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (fun a b h => congrArg Prod.fst h), Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    rfl
  have heq : F = N := Subgroup.eq_of_le_of_card_ge hFN (by rw [h6, hF6])
  intro n hn
  rw [← heq] at hn
  obtain ⟨x, rfl⟩ := hn
  rfl

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {t : G} {m : ℕ}
    (hcop : Nat.Coprime m (orderOf t)) (ht : t ^ m ∈ K) : t ∈ K := by
  rcases Nat.lt_or_ge 1 (orderOf t) with h1 | h1
  · obtain ⟨u, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e : t = (t ^ m) ^ u := by
      rw [← pow_mul, ← pow_mod_orderOf, hu.2, pow_one]
    rw [e]
    exact K.pow_mem ht u
  · have h1' : orderOf t = 1 := le_antisymm h1 (orderOf_pos t)
    rw [orderOf_eq_one_iff.mp h1']
    exact K.one_mem

theorem mem_of_odd_of_mem_sup {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ T) {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) : x ∈ K := by
  obtain ⟨k, hk, t, ht, rfl⟩ := L14328.exists_mul_of_mem_sup hTK hx
  have h1 := L32NSet14.pow_mul_inv_mem hk (hTK ht) m
  rw [hxm, one_mul] at h1
  have htm : t ^ m ∈ K := by simpa using K.inv_mem h1
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime m (orderOf t) := Nat.Coprime.coprime_dvd_right
    (orderOf_dvd_of_pow_eq_one hj') (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm))
  exact K.mul_mem hk (mem_of_pow_mem_of_coprime hcop htm)

theorem eq_one_or_eq_of_card_two {W : Type*} [Group W] {A : Subgroup W} (hA : Nat.card A = 2)
    {t x : W} (ht : t ∈ A) (ht1 : t ≠ 1) (hx : x ∈ A) : x = 1 ∨ x = t := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (⟨1, A.one_mem⟩ : A)).mp hA
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have h1 := hy ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    have h2 := hy ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_two_pow_of_odd {W : Type*} [Group W] [Finite W] {S : Subgroup W}
    (h : ∀ s ∈ S, Odd (orderOf s) → s = 1) {s : W} (hs : s ∈ S) : ∃ n : ℕ, s ^ 2 ^ n = 1 := by
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  refine ⟨k, h _ (S.pow_mem hs _) ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hord]; exact Dvd.intro m rfl), hord,
    Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  exact hm

theorem exists_mulEquiv_fst {Γ : Type*} [Group Γ]
    (φ₀ : Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) {N : Subgroup Γ} (hN : N.Normal)
    (h6 : Nat.card N = 6) {t : Γ} (ht : t ∈ N) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ φ : Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
      (∀ n ∈ N, (φ n).2 = 1) ∧ ∀ s : Equiv.Perm (Fin 3), ∃ n ∈ N, (φ n).1 = s := by
  have key : ∀ φ : Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), (φ t).2 = 1 →
      (∀ n ∈ N, (φ n).2 = 1) ∧ ∀ s : Equiv.Perm (Fin 3), ∃ n ∈ N, (φ n).1 = s := by
    intro φ hφt
    have hN' : (N.map (φ : Γ →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).Normal :=
      hN.map _ φ.surjective
    have h6' : Nat.card (N.map (φ : Γ →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) = 6 := by
      rw [Subgroup.card_map_of_injective φ.injective, h6]
    have hts : ((φ t).1, (1 : Equiv.Perm (Fin 3))) ∈
        N.map (φ : Γ →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
      ⟨t, ht, Prod.ext rfl hφt⟩
    have hs2 : (φ t).1 * (φ t).1 = 1 := by
      have := congrArg Prod.fst (show φ t * φ t = 1 by rw [← map_mul, ht2, map_one])
      simpa using this
    have hs1 : (φ t).1 ≠ 1 := by
      intro h
      apply ht1
      apply φ.injective
      rw [map_one]
      exact Prod.ext h hφt
    obtain ⟨hall, hsnd⟩ := s3s3_fst_of hN' h6' hts hs2 hs1
    refine ⟨fun n hn => hsnd _ (Subgroup.mem_map_of_mem _ hn), fun s => ?_⟩
    obtain ⟨n, hn, hns⟩ := Subgroup.mem_map.mp (hall s)
    exact ⟨n, hn, congrArg Prod.fst hns⟩
  have hNm : (N.map (φ₀ : Γ →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).Normal :=
    hN.map _ φ₀.surjective
  have h6m : Nat.card (N.map (φ₀ : Γ →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) = 6 := by
    rw [Subgroup.card_map_of_injective φ₀.injective, h6]
  rcases s3s3_factor hNm h6m (Subgroup.mem_map_of_mem _ ht)
      (by rw [← map_mul, ht2, map_one]) with h1 | h2
  · refine ⟨φ₀.trans MulEquiv.prodComm, key _ ?_⟩
    simpa using h1
  · exact ⟨φ₀, key _ h2⟩

structure CaseI {G : Type} [Group G] [Finite G] (T L V : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : G) : Prop where
  h14325 : Lemma14325One
  h1222 : Stmt12_2_2
  h12213 : Stmt12_2_13
  h12810 : Lemma12_8_10
  h12813 : Lemma12_8_13
  hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)
  he : e ∈ centerOf (i128 T L V (fsuV1 T V))
  he1 : e ≠ 1
  he2 : e * e = 1
  hi : Case14323i T L V g D
  hd : Module.finrank (ZMod 2) D.V = 4

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_a_H (X : CaseI T L V g D e) : l⁻¹ * e * l ∈ l32nH T V :=
  L14332.conj_zU_le X.h12813 C.setting C.gP C.gN (C.conj_mem_zIl X.he).1

theorem caseI_a_N (X : CaseI T L V g D e) :
    l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V (C.caseI_a_H D X)

theorem caseI_K_H (X : CaseI T L V g D e) : kA T V (l⁻¹ * e * l) ≤ l32nH T V :=
  kA_le (C.caseI_a_H D X)

theorem caseI_K_Z (X : CaseI T L V g D e) :
    kA T V (l⁻¹ * e * l) ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G) :=
  kA_le_centralizer fun _ hw => C.comm_zU X.h14325 X.h1222 X.h12813 (C.conj_mem_zIl X.he) hw

theorem caseI_rho_ne (X : CaseI T L V g D e) : D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N D X⟩ ≠ 1 :=
  (C.rho_a_mem D X.h14325 X.h1222 X.h12213 X.h12810 X.h12813 X.he X.he1 _).2

omit [IsMulCommutative ↥V] C in
theorem caseI_rho_sq (X : CaseI T L V g D e)
    (hN : l⁻¹ * e * l ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨l⁻¹ * e * l, hN⟩ * D.ρ ⟨l⁻¹ * e * l, hN⟩ = 1 := by
  rw [← map_mul]
  have : (⟨l⁻¹ * e * l, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) *
      ⟨l⁻¹ * e * l, hN⟩ = 1 := Subtype.ext (by
    show l⁻¹ * e * l * (l⁻¹ * e * l) = 1
    rw [show l⁻¹ * e * l * (l⁻¹ * e * l) = l⁻¹ * (e * e) * l by group, X.he2]
    group)
  rw [this, map_one]

theorem caseI_zU_ne_bot (X : CaseI T L V g D e) :
    D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
  intro h
  have hmem := L128A.HatU.rho_mem_img D (C.conj_mem_zIl X.he).1 (C.caseI_a_N D X)
  rw [h, Subgroup.mem_bot] at hmem
  exact C.caseI_rho_ne D X hmem

theorem caseI_img_kA (X : CaseI T L V g D e) :
    D.img (kA T V (l⁻¹ * e * l)) =
      D.img (conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V)) := by
  have hZgH := L14332.conj_zU_le X.h12813 C.setting C.gP C.gN
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have ha := C.conj_mem_zIl X.he
  have haN := C.caseI_a_N D X
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKK' : K ≤ conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) :=
    conjClosure_mono (Subgroup.zpowers_le.mpr ha.1) le_rfl
  apply le_antisymm
  · intro γ hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (hKK' hk) hkN
  ·
    set S : Subgroup G := ((D.img K).comap D.ρ).map
      (Subgroup.normalizer (fsuU T V : Set G)).subtype with hS
    have hSmem : ∀ {y : G}, y ∈ S → ∀ hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G),
        D.ρ ⟨y, hyN⟩ ∈ D.img K := by
      rintro y ⟨y', hy', rfl⟩ hyN
      exact hy'
    obtain ⟨-, h2, -⟩ := X.hi.zU (C.caseI_zU_ne_bot D X)
    have hZ2 : ∀ x ∈ CFSG.conjugate (centerOf (fsuU T V)) g,
        ∀ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G),
        D.ρ ⟨x, hxN⟩ = 1 ∨ D.ρ ⟨x, hxN⟩ = D.ρ ⟨l⁻¹ * e * l, haN⟩ := fun x hx hxN =>
      eq_one_or_eq_of_card_two h2 (L128A.HatU.rho_mem_img D ha.1 haN) (C.caseI_rho_ne D X)
        (L128A.HatU.rho_mem_img D hx hxN)
    have hK'S : conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) ≤ S := by
      refine conjClosure_le fun h hh x hx => ?_
      have hxH := hZgH hx
      have hy : h * x * h⁻¹ ∈ l32nH T V :=
        (l32nH T V).mul_mem ((l32nH T V).mul_mem hh hxH) ((l32nH T V).inv_mem hh)
      refine ⟨⟨h * x * h⁻¹, hN hy⟩, ?_, rfl⟩
      show D.ρ ⟨h * x * h⁻¹, hN hy⟩ ∈ D.img K
      have e1 : D.ρ ⟨h * x * h⁻¹, hN hy⟩ =
          D.ρ ⟨h, hN hh⟩ * D.ρ ⟨x, hN hxH⟩ * (D.ρ ⟨h, hN hh⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rcases hZ2 x hx (hN hxH) with h1 | h1
      · rw [e1, h1, mul_one, mul_inv_cancel]
        exact (D.img K).one_mem
      · have hcH : h * (l⁻¹ * e * l) * h⁻¹ ∈ l32nH T V :=
          (l32nH T V).mul_mem ((l32nH T V).mul_mem hh (C.caseI_a_H D X)) ((l32nH T V).inv_mem hh)
        have e2 : D.ρ ⟨h, hN hh⟩ * D.ρ ⟨l⁻¹ * e * l, haN⟩ * (D.ρ ⟨h, hN hh⟩)⁻¹ =
            D.ρ ⟨h * (l⁻¹ * e * l) * h⁻¹, hN hcH⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e1, h1, e2]
        exact L128A.HatU.rho_mem_img D (mem_conjClosure hh (Subgroup.mem_zpowers _)) _
    intro γ hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact hSmem (hK'S hk) hkN

theorem caseI_exists_phi (X : CaseI T L V g D e) :
    ∃ φ : ↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
      (∀ k ∈ kA T V (l⁻¹ * e * l), ∀ hk : k ∈ l32nH T V,
        (φ (L14332.imgHom D ⟨k, hk⟩)).2 = 1) ∧
      ∀ s : Equiv.Perm (Fin 3), ∃ k ∈ kA T V (l⁻¹ * e * l), ∃ hk : k ∈ l32nH T V,
        (φ (L14332.imgHom D ⟨k, hk⟩)).1 = s := by
  set K := kA T V (l⁻¹ * e * l) with hK
  set Hd := D.img (l32nH T V) with hHd
  have hKH := C.caseI_K_H D X
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have haK : l⁻¹ * e * l ∈ K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have himg : D.img K ≤ Hd := fun γ hγ => by
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (hKH hk) hkN
  have hconj : ∀ γ ∈ Hd, ∀ κ ∈ D.img K, γ * κ * γ⁻¹ ∈ D.img K := by
    intro γ hγ κ hκ
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hκ
    have hmem : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kA _ hh) k).mp hk
    have e1 : D.ρ ⟨h, hhN⟩ * D.ρ ⟨k, hkN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ =
        D.ρ ⟨h * k * h⁻¹, hN (hKH hmem)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact L128A.HatU.rho_mem_img D hmem _
  have hnorm : Hd ≤ Subgroup.normalizer (D.img K : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro κ
    refine ⟨fun hκ => hconj γ hγ κ hκ, fun hκ => ?_⟩
    have := hconj γ⁻¹ (Hd.inv_mem hγ) _ hκ
    rwa [show γ⁻¹ * (γ * κ * γ⁻¹) * γ⁻¹⁻¹ = κ by group] at this
  have hNn : ((D.img K).subgroupOf Hd).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have h6 : Nat.card ((D.img K).subgroupOf Hd) = 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe himg).toEquiv, C.caseI_img_kA D X]
    obtain ⟨-, -, ⟨ψ⟩, -⟩ := X.hi.zU (C.caseI_zU_ne_bot D X)
    rw [Nat.card_congr ψ.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  obtain ⟨φ₀⟩ := X.hi.iso
  set t : ↥Hd := ⟨D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N D X⟩,
    L128A.HatU.rho_mem_img D (C.caseI_a_H D X) _⟩ with ht
  have htK : t ∈ (D.img K).subgroupOf Hd :=
    Subgroup.mem_subgroupOf.mpr (L128A.HatU.rho_mem_img D haK _)
  have ht2 : t * t = 1 := Subtype.ext (by
    show D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N D X⟩ * D.ρ ⟨l⁻¹ * e * l, C.caseI_a_N D X⟩ = 1
    exact caseI_rho_sq D X _)
  have ht1 : t ≠ 1 := fun h => C.caseI_rho_ne D X (congrArg Subtype.val h)
  obtain ⟨φ, hφ2, hφ1⟩ := exists_mulEquiv_fst φ₀ hNn h6 htK ht2 ht1
  refine ⟨φ, fun k hk hkH => hφ2 _ ?_, fun s => ?_⟩
  · rw [Subgroup.mem_subgroupOf, L14332.imgHom_apply]
    exact L128A.HatU.rho_mem_img D hk _
  · obtain ⟨n, hn, hns⟩ := hφ1 s
    obtain ⟨k, hk, hkN, hkn⟩ := (L128A.HatU.mem_img D).mp (Subgroup.mem_subgroupOf.mp hn)
    refine ⟨k, hk, hKH hk, ?_⟩
    have : L14332.imgHom D ⟨k, hKH hk⟩ = n := Subtype.ext (by
      rw [L14332.imgHom_apply]
      exact hkn)
    rw [this]
    exact hns

theorem eq_one_of_mem_cHat
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    {K : Subgroup G} (hKZ : K ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G))
    {c : G} (hcK : c ∈ K) (hcE : c ∈ l32nCHat T V) (hc : Odd (orderOf c)) : c = 1 := by
  have hU2 : IsPGroup 2 ↥(fsuU T V) := C.S.hH.sylow.1.to_le C.U_T
  have hcU : ∀ u ∈ fsuU T V, c * u * c⁻¹ = u := by
    intro u hu
    set d := c * u * c⁻¹ * u⁻¹ with hd
    have hdZ : d ∈ centerOf (fsuU T V) := hcE.2.2 u hu
    have hcd : c * d * c⁻¹ = d := by
      rw [← Subgroup.mem_centralizer_iff.mp (hKZ hcK) d hdZ, mul_inv_cancel_right]
    have hcu : c * u * c⁻¹ = d * u := by rw [hd]; group
    have h3 := L14332.pow_conj_eq hcd hcu (orderOf c)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h3
    have hdo : d ^ orderOf c = 1 := by
      have : u * u⁻¹ = d ^ orderOf c * u * u⁻¹ := by rw [← h3]
      simpa using this.symm
    obtain ⟨k, hk⟩ := hU2 ⟨d, hdZ.1⟩
    have hd2 : d ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc))
      (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hdo))
    rw [hcu, hd1, one_mul]
  have hcQ : c ∈ pCoreOf 2 (l32nH T V) := by
    rw [← hQ]
    refine ⟨hcE.1, hcE.1, fun u hu => ?_⟩
    rw [hcU u hu, mul_inv_cancel]
    exact one_mem _
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨c, hcQ⟩
  have hc2 : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc))
    (orderOf_dvd_of_pow_eq_one hc2) dvd_rfl)

theorem caseI_exists_chi (X : CaseI T L V g D e) :
    ∃ χ : ↥(kA T V (l⁻¹ * e * l) ⊔ T) →* Equiv.Perm (Fin 3), Function.Surjective χ ∧
      ∀ x : ↥(kA T V (l⁻¹ * e * l) ⊔ T), χ x = 1 → ∃ n : ℕ, (x : G) ^ 2 ^ n = 1 := by
  obtain ⟨φ, hφ2, hφ1⟩ := C.caseI_exists_phi D X
  set K := kA T V (l⁻¹ * e * l) with hK
  have hKH := C.caseI_K_H D X
  have hTH : T ≤ l32nH T V := C.setting.v1.2.2
  have hKTH : K ⊔ T ≤ l32nH T V := sup_le hKH hTH
  set χ : ↥(K ⊔ T) →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp
      ((L14332.imgHom D).comp (Subgroup.inclusion hKTH))) with hχ
  have hχapp : ∀ x : ↥(K ⊔ T), χ x = (φ (L14332.imgHom D ⟨x, hKTH x.2⟩)).1 := fun _ => rfl
  refine ⟨χ, fun s => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, hkH, hks⟩ := hφ1 s
    exact ⟨⟨k, Subgroup.mem_sup_left hk⟩, by rw [hχapp]; exact hks⟩
  · have hT2 : IsPGroup 2 ↥T := C.S.hH.sylow.1
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans (le_normalizer_kA _)
    have hodd : ∀ y ∈ χ.ker, Odd (orderOf y) → y = 1 := by
      intro y hy hyo
      have hyo' : Odd (orderOf (y : G)) := by rwa [Subgroup.orderOf_coe]
      have hyK : (y : G) ∈ K :=
        mem_of_odd_of_mem_sup hT2 hTK y.2 hyo' (pow_orderOf_eq_one _)
      have h2 := hφ2 _ hyK (hKTH y.2)
      have h1 : (φ (L14332.imgHom D ⟨y, hKTH y.2⟩)).1 = 1 := by
        rw [← hχapp]
        exact hy
      have hφy : φ (L14332.imgHom D ⟨y, hKTH y.2⟩) = 1 := Prod.ext h1 h2
      have himg1 : L14332.imgHom D ⟨y, hKTH y.2⟩ = 1 := φ.injective (hφy.trans φ.map_one.symm)
      have hyC : (y : G) ∈ l32nCHat T V := by
        refine (L14332.rho_eq_one_iff_mem (D := D) (hKTH y.2)
          (L14332.l32nH_le_normalizer_fsuU T V (hKTH y.2))).mp ?_
        have := congrArg Subtype.val himg1
        rwa [L14332.imgHom_apply] at this
      exact Subtype.ext (C.eq_one_of_mem_cHat X.hQ (C.caseI_K_Z D X) hyK hyC hyo')
    obtain ⟨n, hn⟩ := exists_two_pow_of_odd hodd hx
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem caseI_quotient_KT (X : CaseI T L V g D e) :
    Nonempty (↥(kA T V (l⁻¹ * e * l) ⊔ T) ⧸ CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T) ≃*
      Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨χ, hs, hker2⟩ := C.caseI_exists_chi D X
  have hker : CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T) = χ.ker := by
    apply le_antisymm
    · have hn : ((CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ).Normal :=
        Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _ hs
      have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
      have hbot := eq_bot_of_normal_isPGroup_perm3 hn hp
      intro x hx
      have : χ x ∈ (CFSG.Open.pCore 2 ↥(kA T V (l⁻¹ * e * l) ⊔ T)).map χ :=
        Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun x => ?_
      obtain ⟨k, hk⟩ := hker2 _ x.2
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)⟩

end Ctx

end L14328

end CFSG.Quasithin.H13
