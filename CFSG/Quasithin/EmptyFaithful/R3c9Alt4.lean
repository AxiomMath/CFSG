module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.R3c9

open Equiv

theorem perm4_three_cycle_mem {H : Subgroup (Perm (Fin 4))} (hH : H.index = 2) :
    alternatingGroup (Fin 4) ≤ H := by
  have hn : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hsq : ∀ g : Perm (Fin 4), g ^ 2 ∈ H := by
    intro g
    have hcard : Nat.card (Perm (Fin 4) ⧸ H) = 2 := by rw [← Subgroup.index, hH]
    have h := pow_card_eq_one' (G := Perm (Fin 4) ⧸ H) (x := (g : Perm (Fin 4) ⧸ H))
    rw [hcard] at h
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mp (by simpa [map_pow] using h)
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have h3 : σ ^ 3 = 1 := hσ.orderOf ▸ pow_orderOf_eq_one σ
  have : σ = (σ ^ 2) ^ 2 := by
    calc σ = σ ^ 4 * (σ ^ 3)⁻¹ := by group
      _ = (σ ^ 2) ^ 2 := by rw [h3]; group
  rw [this]
  exact H.pow_mem (hsq σ) 2

theorem isAlt4_of_structure {A : Type} [Group A] [Finite A] (W : Subgroup A) [hWn : W.Normal]
    (c : A) (hW4 : Nat.card W = 4) (hc3 : orderOf c = 3)
    (hfpf : ∀ w ∈ W, w ≠ 1 → c * w * c⁻¹ ≠ w) (hcard : Nat.card A = 12) :
    Nonempty (A ≃* alternatingGroup (Fin 4)) := by
  classical
  set P : Subgroup A := Subgroup.zpowers c with hP
  have hPcard : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hc3]
  have hidx : P.index = 4 := by
    have := Subgroup.index_mul_card P
    rw [hPcard, hcard] at this
    omega
  have hΩ : Nat.card (A ⧸ P) = 4 := hidx
  let φ₀ : A →* Perm (A ⧸ P) := MulAction.toPermHom A (A ⧸ P)
  have hW1 : ∃ w ∈ W, w ≠ 1 := by
    have : 1 < Nat.card W := by rw [hW4]; norm_num
    have hnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp this
    obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : W)
    exact ⟨w, hw, fun h => hw1 (Subtype.ext h)⟩
  have hinj₀ : Function.Injective φ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hfix : ∀ x : A, g • (x : A ⧸ P) = (x : A ⧸ P) := fun x => by
      have := congrArg (fun π : Perm (A ⧸ P) => π (x : A ⧸ P)) hg
      simpa [φ₀] using this
    have hgP : g ∈ P := by
      have h1 := hfix 1
      rw [MulAction.Quotient.smul_mk] at h1
      simp only [smul_eq_mul, mul_one] at h1
      have := QuotientGroup.eq.mp h1
      simpa using this
    have hcomm : ∀ w ∈ W, g * w = w * g := by
      intro w hw
      have h1 := hfix w
      rw [MulAction.Quotient.smul_mk] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      have h3 : w⁻¹ * (g * w) ∈ P := by simpa [mul_assoc] using h2
      have h4 : w⁻¹ * (g * w) * g⁻¹ ∈ P := P.mul_mem h3 (P.inv_mem hgP)
      have h5 : w⁻¹ * (g * w) * g⁻¹ ∈ W := by
        have : w⁻¹ * (g * w) * g⁻¹ = w⁻¹ * (g * w * g⁻¹) := by group
        rw [this]
        exact W.mul_mem (W.inv_mem hw) (hWn.conj_mem w hw g)
      have h6 : W ⊓ P = ⊥ := by
        apply disjoint_iff.mp
        apply Subgroup.disjoint_of_coprime_natCard
        rw [hW4, hPcard]; norm_num
      have h7 : w⁻¹ * (g * w) * g⁻¹ ∈ W ⊓ P := ⟨h5, h4⟩
      rw [h6, Subgroup.mem_bot] at h7
      calc g * w = w * (w⁻¹ * (g * w) * g⁻¹) * g := by group
        _ = w * g := by rw [h7]; group
    by_contra hg1
    rw [Subgroup.mem_bot] at hg1
    have hg3 : orderOf g = 3 := by
      have hdvd : orderOf g ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard P hgP
        rwa [hPcard] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have hzg : Subgroup.zpowers g = P := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hgP
      · rw [hPcard, Nat.card_zpowers, hg3]
    have hcg : c ∈ Subgroup.zpowers g := by rw [hzg]; exact Subgroup.mem_zpowers c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcg
    obtain ⟨w, hw, hw1⟩ := hW1
    have hcw : c * w = w * c := by
      rw [← hk]
      exact ((Commute.zpow_left (show Commute g w from hcomm w hw) k)).eq
    exact hfpf w hw hw1 (by rw [hcw]; group)
  let e : A ⧸ P ≃ Fin 4 := Finite.equivFinOfCardEq hΩ
  let φ : A →* Perm (Fin 4) := (Equiv.permCongrHom e).toMonoidHom.comp φ₀
  have hinj : Function.Injective φ := by
    intro a b hab
    apply hinj₀
    exact (Equiv.permCongrHom e).injective hab
  have hrange : Nat.card φ.range = 12 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hcard
  have h24 : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hindex : φ.range.index = 2 := by
    have := Subgroup.index_mul_card φ.range
    rw [hrange, h24] at this
    omega
  have hle := perm4_three_cycle_mem hindex
  have hcardAlt : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    have := Nat.card_eq_fintype_card (α := alternatingGroup (Fin 4))
    rw [this]
    decide
  have heq : alternatingGroup (Fin 4) = φ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcardAlt])
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr heq.symm)⟩


theorem exists_mulAut_embedding (V : Type) [Group V] [Finite V] (hV : Nat.card V = 4) :
    ∃ ι : MulAut V →* Perm (Fin 3), Function.Injective ι ∧
      ∀ (f : MulAut V) (v : V), v ≠ 1 → f v = v → ∃ i, ι f i = i := by
  classical
  let Ω := {v : V // v ≠ 1}
  have hΩ : Nat.card Ω = 3 := by
    have h1 : Nat.card {v : V // v = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨1, rfl⟩⟩⟩
    have h2 := Nat.card_congr (Equiv.sumCompl (fun v : V => v = 1))
    rw [Nat.card_sum, h1] at h2
    have h3 : Nat.card Ω + 1 = 4 := by rw [← hV, ← h2]; exact add_comm _ _
    omega
  let e : Ω ≃ Fin 3 := Finite.equivFinOfCardEq hΩ
  have hf : ∀ (f : MulAut V) (v : V), f v ≠ 1 ↔ v ≠ 1 := fun f v => by
    rw [Ne, Ne, MulEquiv.map_eq_one_iff]
  let ι₀ : MulAut V →* Perm Ω :=
    { toFun := fun f => Equiv.subtypeEquiv f.toEquiv (fun v => (hf f v).symm)
      map_one' := by ext v; rfl
      map_mul' := by intro f g; ext v; rfl }
  let ι : MulAut V →* Perm (Fin 3) := (Equiv.permCongrHom e).toMonoidHom.comp ι₀
  refine ⟨ι, ?_, ?_⟩
  · intro f g hfg
    have h1 : ι₀ f = ι₀ g := (Equiv.permCongrHom e).injective hfg
    ext v
    by_cases hv : v = 1
    · subst hv; simp
    · have h2 := congrArg (fun p : Perm Ω => ((p ⟨v, hv⟩ : Ω) : V)) h1
      exact h2
  · intro f v hv hfv
    refine ⟨e ⟨v, hv⟩, ?_⟩
    have : ι₀ f ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext hfv
    change (e.permCongr (ι₀ f)) (e ⟨v, hv⟩) = e ⟨v, hv⟩
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, this]



theorem perm3_pow3_of_threePow {τ : Perm (Fin 3)} {k : ℕ} (h : τ ^ 3 ^ k = 1) : τ ^ 3 = 1 := by
  have h1 : orderOf τ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf τ ∣ 6 := by
    have := orderOf_dvd_natCard τ
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have h4 : 9 ∣ 3 ^ j := by
      have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
      simpa using this
    have : 9 ∣ 6 := h4.trans (hj' ▸ h2)
    omega
  have : orderOf τ ∣ 3 := by
    rw [hj']
    interval_cases j <;> simp
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem perm3_mem_powers : ∀ σ τ : Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 → τ ^ 3 = 1 →
    τ = 1 ∨ τ = σ ∨ τ = σ ^ 2 := by decide

theorem perm3_no_fixed : ∀ σ : Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 → ∀ i, σ i ≠ i := by decide

theorem isAlt4_of_selfCent {G : Type} [Group G] [Finite G] {K V Y : Subgroup G}
    (hVK : V ≤ K) (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVc : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u)
    (hY : Y = Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, orderOf x = 3 ^ k})
    (hVY : V ≤ Y) (hK3 : ¬ 9 ∣ Nat.card K) (hact : ¬ Y ≤ Subgroup.centralizer (V : Set G))
    (hF : ∀ c ∈ K, (∀ v ∈ V, c * v = v * c) → ¬ 3 ∣ orderOf c → c ∈ V) :
    Nonempty (↥Y ≃* alternatingGroup (Fin 4)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYK : Y ≤ K := by
    rw [hY, Subgroup.closure_le]
    exact fun x hx => hx.1
  obtain ⟨ι, hιinj, hιfix⟩ := exists_mulAut_embedding ↥V hV4
  let ψ : ↥K →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hKN)
  have hψ : ∀ (k : ↥K) (v : ↥V), ((ψ k v : ↥V) : G) = (k : G) * v * (k : G)⁻¹ := fun k v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨k, hKN k.2⟩ v
  let θ : ↥K →* Perm (Fin 3) := ι.comp ψ
  have hker : ∀ k : ↥K, θ k = 1 ↔ ∀ v ∈ V, (k : G) * v = v * k := by
    intro k
    constructor
    · intro h v hv
      have h1 : ι (ψ k) = ι 1 := by rw [map_one]; exact h
      have h2 : ψ k = 1 := hιinj h1
      have h3 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) h2
      simp only [hψ, MulAut.one_apply] at h3
      calc (k : G) * v = ((k : G) * v * (k : G)⁻¹) * k := by group
        _ = v * k := by rw [h3]
    · intro h
      have h2 : ψ k = 1 := by
        ext v
        rw [hψ]
        have := h v v.2
        simp only [MulAut.one_apply]
        calc (k : G) * v * (k : G)⁻¹ = (v * k) * (k : G)⁻¹ := by rw [this]
          _ = v := by group
      show ι (ψ k) = 1
      rw [h2, map_one]
  obtain ⟨a, haK, ⟨j, haj⟩, haact⟩ : ∃ a ∈ K, (∃ j : ℕ, orderOf a = 3 ^ j) ∧
      ¬ ∀ v ∈ V, a * v = v * a := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hY, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hx.1 hx.2 v hv).symm
  let a₀ : ↥K := ⟨a, haK⟩
  have hθa : θ a₀ ≠ 1 := fun h => haact ((hker a₀).mp h)
  have hθa3 : (θ a₀) ^ 3 = 1 := by
    apply perm3_pow3_of_threePow (k := j)
    rw [← map_pow]
    have : a₀ ^ 3 ^ j = 1 := by
      apply Subtype.ext
      have h1 : a ^ 3 ^ j = 1 := by rw [← haj]; exact pow_orderOf_eq_one a
      simpa [a₀] using h1
    rw [this, map_one]
  have hθaord : orderOf (θ a₀) = 3 := by
    have hdvd : orderOf (θ a₀) ∣ 3 := orderOf_dvd_of_pow_eq_one hθa3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hθa
    · exact h
  have hrange3 : 3 ∣ Nat.card θ.range := by
    have hmem : θ a₀ ∈ θ.range := ⟨a₀, rfl⟩
    have := Subgroup.orderOf_dvd_natCard θ.range hmem
    rwa [hθaord] at this
  have hkerindex : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
  have hcardK : Nat.card θ.ker * θ.ker.index = Nat.card K := Subgroup.card_mul_index θ.ker
  have h3ker : ¬ 3 ∣ Nat.card θ.ker := by
    intro h3
    apply hK3
    rw [← hcardK, hkerindex]
    have := Nat.mul_dvd_mul h3 hrange3
    simpa using this
  have hkerV : θ.ker = V.subgroupOf K := by
    ext k
    constructor
    · intro hk
      have hk' : θ k = 1 := hk
      have hcent := (hker k).mp hk'
      have h1 : ¬ 3 ∣ orderOf (k : G) := by
        intro h
        apply h3ker
        have h2 : orderOf k ∣ Nat.card θ.ker := Subgroup.orderOf_dvd_natCard θ.ker hk
        rw [← Subgroup.orderOf_coe] at h2
        exact h.trans h2
      exact Subgroup.mem_subgroupOf.mpr (hF k k.2 hcent h1)
    · intro hk
      rw [Subgroup.mem_subgroupOf] at hk
      apply (hker k).mpr
      intro v hv
      exact hVc k hk v hv
  have hkerCard : Nat.card θ.ker = 4 := by
    rw [hkerV, ← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hpow : ∀ x : ↥K, (∃ k : ℕ, orderOf (x : G) = 3 ^ k) → θ x ∈ Subgroup.zpowers (θ a₀) := by
    rintro x ⟨k, hk⟩
    have hx3 : (θ x) ^ 3 = 1 := by
      apply perm3_pow3_of_threePow (k := k)
      rw [← map_pow]
      have : x ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have h1 : (x : G) ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one (x : G)
        simpa using h1
      rw [this, map_one]
    rcases perm3_mem_powers (θ a₀) (θ x) hθa hθa3 hx3 with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2
  have haY : a ∈ Y := by
    rw [hY]
    exact Subgroup.subset_closure ⟨haK, j, haj⟩
  let φY : ↥Y →* Perm (Fin 3) := θ.comp (Subgroup.inclusion hYK)
  have hYle : Y ≤ ((Subgroup.zpowers (θ a₀)).comap θ).map K.subtype := by
    rw [hY, Subgroup.closure_le]
    intro x hx
    exact ⟨⟨x, hx.1⟩, hpow ⟨x, hx.1⟩ hx.2, rfl⟩
  have hφrange : φY.range = Subgroup.zpowers (θ a₀) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨s, hs, hsy⟩ := hYle y.2
      have : s = Subgroup.inclusion hYK y := Subtype.ext hsy
      rw [this] at hs
      exact hs
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨a, haY⟩, rfl⟩
  have hφker : φY.ker = V.subgroupOf Y := by
    ext y
    constructor
    · intro hy
      have : Subgroup.inclusion hYK y ∈ θ.ker := hy
      rw [hkerV, Subgroup.mem_subgroupOf] at this
      exact Subgroup.mem_subgroupOf.mpr this
    · intro hy
      have h1 : Subgroup.inclusion hYK y ∈ V.subgroupOf K := Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hy)
      rw [← hkerV] at h1
      exact h1
  have hYcard : Nat.card Y = 12 := by
    have h1 : Nat.card φY.ker * φY.ker.index = Nat.card Y := Subgroup.card_mul_index φY.ker
    have h2 : φY.ker.index = Nat.card φY.range := Subgroup.index_ker φY
    have h3 : Nat.card φY.range = 3 := by rw [hφrange, Nat.card_zpowers, hθaord]
    have h4 : Nat.card φY.ker = 4 := by
      rw [hφker, ← hV4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
    rw [← h1, h2, h3, h4]
  have ha3 : orderOf a = 3 := by
    have h1 : a₀ ^ 3 ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_pow]; exact hθa3
    rw [hkerV, Subgroup.mem_subgroupOf] at h1
    have h2 : a ^ 3 ∈ V := h1
    have h3 : a ^ 6 = 1 := by
      have := hV2 _ h2
      rw [← pow_mul] at this
      exact this
    have hd1 : orderOf a ∣ 6 := orderOf_dvd_of_pow_eq_one h3
    have hj6 : 3 ^ j ∣ 6 := haj ▸ hd1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have h4 : 9 ∣ 3 ^ j := by
        have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
        simpa using this
      have : 9 ∣ 6 := h4.trans hj6
      omega
    interval_cases j
    · exfalso
      have ha1 : a = 1 := orderOf_eq_one_iff.mp (by simpa using haj)
      apply hθa
      have : a₀ = 1 := Subtype.ext ha1
      rw [this, map_one]
    · simpa using haj
  have haY' : (⟨a, haY⟩ : ↥Y) ∈ (⊤ : Subgroup ↥Y) := Subgroup.mem_top _
  let W : Subgroup ↥Y := V.subgroupOf Y
  have hWn : W.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVY).mpr (hYK.trans hKN)
  have hW4 : Nat.card W = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
  have hc3 : orderOf (⟨a, haY⟩ : ↥Y) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ha3
  have hfpf : ∀ w ∈ W, w ≠ 1 → (⟨a, haY⟩ : ↥Y) * w * (⟨a, haY⟩ : ↥Y)⁻¹ ≠ w := by
    intro w hw hw1 hcomm
    have hv : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have hvne : (⟨(w : G), hv⟩ : ↥V) ≠ 1 := by
      intro h
      apply hw1
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this
    have hav : a * (w : G) * a⁻¹ = (w : G) := by
      have := congrArg Subtype.val hcomm
      simpa using this
    have hfix : ψ a₀ ⟨(w : G), hv⟩ = ⟨(w : G), hv⟩ := by
      apply Subtype.ext
      rw [hψ]
      exact hav
    obtain ⟨i, hi⟩ := hιfix (ψ a₀) ⟨(w : G), hv⟩ hvne hfix
    exact perm3_no_fixed (θ a₀) hθa hθa3 i hi
  exact isAlt4_of_structure W ⟨a, haY⟩ hW4 hc3 hfpf hYcard

end CFSG.Quasithin.R3c9
