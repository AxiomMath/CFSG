module

public import CFSG.RankThree.PartOne.KF.SymNormalizer
public import CFSG.RankThree.PartOne.S12.Sec12Restrict

public section

namespace CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem IsAutTransvection.pow_eq_one {p : ℕ} {E : Subgroup G}
    (hpow : ∀ a : E, a ^ p = 1) {φ : MulAut E} (h : IsAutTransvection p E φ) : φ ^ p = 1 := by
  refine MulEquiv.ext fun e => ?_
  have hn : φ e * e⁻¹ ∈ autMoved E φ := Subgroup.subset_closure ⟨e, rfl⟩
  have hfix : φ (φ e * e⁻¹) = φ e * e⁻¹ := h.2.2 hn
  have key : ∀ k : ℕ, (φ ^ k) e = (φ e * e⁻¹) ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, pow_succ]
      group
  rw [key p, hpow, one_mul]
  rfl

end CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.RankThree.PartOne

structure SymCtx {G : Type} [Group G] (p n : ℕ) (K : Type) [Field K] (L F : Subgroup G) where
  tor : torusVec p n K ≃* F
  exists_elt : ∀ σ : Equiv.Perm (Fin n), ∃ (g : G) (hg : g ∈ Subgroup.normalizer (F : Set G)),
    g ∈ L ∧ F.normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor (symAut p K σ)
  induced : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (F : Set G)), g ∈ L →
    ∃ σ : Equiv.Perm (Fin n), F.normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor (symAut p K σ)

namespace SymCtx

theorem congr_apply_tor {A B : Type} [Group A] [Group B] (e : A ≃* B) (α : MulAut A) (a : A) :
    (MulAut.congr e α) (e a) = e (α a) := by
  show e (α (e.symm (e a))) = _
  rw [MulEquiv.symm_apply_apply]

variable {G : Type} [Group G] {p n : ℕ} {K : Type} [Field K] {L F : Subgroup G}
  (S : SymCtx p n K L F)

@[expose] noncomputable def act : Equiv.Perm (Fin n) →* MulAut F :=
  (MulAut.congr S.tor).toMonoidHom.comp (symAut p K)

theorem act_eq (σ : Equiv.Perm (Fin n)) : S.act σ = MulAut.congr S.tor (symAut p K σ) := rfl

theorem act_apply (σ : Equiv.Perm (Fin n)) (d : torusVec p n K) :
    S.act σ (S.tor d) = S.tor (symAct p K σ d) := by
  show S.tor (symAct p K σ (S.tor.symm (S.tor d))) = _
  rw [MulEquiv.symm_apply_apply]

theorem coe_normalizerMonoidHom_apply {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G)) (e : F) :
    ((F.normalizerMonoidHom ⟨g, hg⟩ e : F) : G) = g * e * g⁻¹ := rfl

include S in
theorem torusImage_eq_range : torusImage F L = S.act.range := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwL, hwF, rfl⟩ := Sec12Three.mem_torusImage_iff.mp ht
    obtain ⟨σ, hσ⟩ := S.induced w hwF hwL
    exact ⟨σ, hσ.symm⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt σ
    exact Sec12Three.mem_torusImage_iff.mpr ⟨g, hgL, hg, hgσ⟩

include S in
theorem act_injective [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : Function.Injective S.act := by
  intro σ τ h
  apply symAut_injective hp hp2 hζ
  exact (MulAut.congr S.tor).injective h

@[expose] noncomputable def weylEquiv [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : ↥(torusImage F L) ≃* Equiv.Perm (Fin n) :=
  ((MulEquiv.subgroupCongr S.torusImage_eq_range).trans
    (MonoidHom.ofInjective (S.act_injective hp hp2 hζ)).symm)

include S in
theorem card_F [Finite K] {m : ℕ} (hn : n = m + 1) (hp : 0 < p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : Nat.card F = p ^ m := by
  subst hn
  rw [← Nat.card_congr S.tor.toEquiv]
  exact card_torusVec_eq hp hζ m

theorem autMoved_act (σ : Equiv.Perm (Fin n)) :
    autMoved F (S.act σ) = (movedSub p K σ).map S.tor.toMonoidHom := by
  unfold autMoved movedSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨symAct p K σ d * d⁻¹, ⟨d, rfl⟩, by simp [S.act_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.act_apply, map_mul, map_inv]⟩

include S in
theorem isAutReflection_swap [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {a b : Fin n} (hab : a ≠ b) :
    IsAutReflection p F (S.act (Equiv.swap a b)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ (S.act_injective hp hp2 hζ) _]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) ?_
    intro h
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) h
    simp [Equiv.swap_apply_left] at this
    exact hab this.symm
  · rw [autMoved_act, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedSub_swap hp hp2 hζ hab

include S in
theorem torusImage_eq_closure [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
  apply le_antisymm
  · have h : torusImage F L = Subgroup.closure (S.act '' {σ | σ.IsSwap}) := by
      rw [S.torusImage_eq_range, MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap,
        MonoidHom.map_closure]
    calc torusImage F L = Subgroup.closure (S.act '' {σ | σ.IsSwap}) := h
      _ ≤ Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨σ, ⟨a, b, hab, rfl⟩, rfl⟩
        exact ⟨by rw [S.torusImage_eq_range]; exact ⟨_, rfl⟩,
          S.isAutReflection_swap hp hp2 hζ hab⟩
  · exact (Subgroup.closure_le _).mpr fun t ht => ht.1

include S in
theorem torusIrreducible [Finite K] (hp : p.Prime) (hn : 2 ≤ n) (hpn : ¬ p ∣ n) (B : Subgroup G)
    (hBF : B ≤ F) (hB : torusInvariant F L B) : B = ⊥ ∨ B = F := by
  set B' : Subgroup (torusVec p n K) := (B.subgroupOf F).comap S.tor.toMonoidHom with hB'
  have hinv : ∀ σ : Equiv.Perm (Fin n), ∀ d ∈ B', symAct p K σ d ∈ B' := by
    intro σ d hd
    have hd' : ((S.tor d : F) : G) ∈ B := hd
    obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt σ
    have hw : g ∈ L ⊓ torusNormalizer F := Subgroup.mem_inf.mpr ⟨hgL, hg⟩
    have h1 := hB _ hw _ hd'
    have h2 : ((S.tor (symAct p K σ d) : F) : G) = g * ((S.tor d : F) : G) * g⁻¹ := by
      rw [← S.act_apply, S.act_eq, ← hgσ]
      rfl
    show ((S.tor (symAct p K σ d) : F) : G) ∈ B
    rw [h2]
    exact h1
  rcases eq_bot_or_eq_top_of_symInvariant hp hn hpn B' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro b hb
    have hbF : b ∈ F := hBF hb
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨b, hbF⟩
    have hdB : d ∈ B' := by
      show ((S.tor d : F) : G) ∈ B
      rw [hd]
      exact hb
    rw [h, Subgroup.mem_bot] at hdB
    subst hdB
    rw [map_one] at hd
    have := congrArg (fun x : F => (x : G)) hd
    exact (Subgroup.mem_bot.mpr this.symm)
  · right
    apply le_antisymm hBF
    intro e he
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨e, he⟩
    have hdB : d ∈ B' := by rw [h]; trivial
    have : ((S.tor d : F) : G) ∈ B := hdB
    rwa [hd] at this

include S in
theorem exists_act_of_normalizes [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (hφp : (F.normalizerMonoidHom ⟨y, hyF⟩) ^ p = 1) :
    ∃ π : Equiv.Perm (Fin n), π ^ p = 1 ∧ F.normalizerMonoidHom ⟨y, hyF⟩ = S.act π := by
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  let φV : MulAut (torusVec p n K) := (MulAut.congr S.tor).symm φ
  have hφV : φV ^ p = 1 := by rw [← map_pow, hφp, map_one]
  have hnorm : ∀ σ : Equiv.Perm (Fin n), ∃ τ : Equiv.Perm (Fin n),
      φV * symAut p K σ * φV⁻¹ = symAut p K τ := by
    intro σ
    obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt σ
    have hywL : y * g * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp hgL
    have hywF : y * g * y⁻¹ ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyF hg) (Subgroup.inv_mem _ hyF)
    obtain ⟨τ, hτ⟩ := S.induced _ hywF hywL
    refine ⟨τ, ?_⟩
    have h1 : φ * MulAut.congr S.tor (symAut p K σ) * φ⁻¹ = MulAut.congr S.tor (symAut p K τ) := by
      rw [← hτ, ← hgσ]
      have : (⟨y * g * y⁻¹, hywF⟩ : Subgroup.normalizer (F : Set G)) =
          ⟨y, hyF⟩ * ⟨g, hg⟩ * ⟨y, hyF⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have h2 := congrArg (MulAut.congr S.tor).symm h1
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  obtain ⟨π, hπ, hπφ⟩ := exists_symAut_of_symNormalizer hp hp2 hn hζ hinner φV hφV hnorm
  refine ⟨π, hπ, ?_⟩
  have h3 : MulAut.congr S.tor φV = MulAut.congr S.tor (symAut p K π) := by rw [hπφ]
  rw [MulEquiv.apply_symm_apply] at h3
  exact h3

include S in
theorem not_isAutTransvection_of [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    (hπ : ∀ π : Equiv.Perm (Fin n), π ^ p = 1 → π = 1 ∨
      ∃ a, π a ≠ a ∧ π (π a) ≠ a ∧ π (π (π a)) ≠ a)
    (hpow : ∀ a : F, a ^ p = 1) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  intro hT
  obtain ⟨π, hπp, hφ⟩ := S.exists_act_of_normalizes hp hp2 hn hζ hinner hyL hyF
    (hT.pow_eq_one hpow)
  rcases hπ π hπp with rfl | ⟨a, h1, h2, h3⟩
  · apply hT.1
    rw [hφ, map_one]
  · have hc := hT.2.1
    rw [hφ, autMoved_act, Subgroup.card_map_of_injective S.tor.injective] at hc
    exact card_movedSub_ne_prime_of_cycle hp hζ π h1 h2 h3 hc

include S in
theorem not_isAutTransvection [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hpn : ∀ π : Equiv.Perm (Fin n), π ^ p = 1 → π = 1) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    (hpow : ∀ a : F, a ^ p = 1) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) :=
  S.not_isAutTransvection_of hp hp2 hn hζ hinner (fun π hπ => Or.inl (hpn π hπ)) hpow hyL hyF

@[expose] def scalarImage : Subgroup G :=
  (scalarSub p n K).map (F.subtype.comp S.tor.toMonoidHom)

include S in
theorem torusInvariant_cases [Finite K] (hp : p.Prime) (B : Subgroup G) (hBF : B ≤ F)
    (hB : torusInvariant F L B) : B ≤ S.scalarImage ∨ B = F := by
  set B' : Subgroup (torusVec p n K) := (B.subgroupOf F).comap S.tor.toMonoidHom with hB'
  have hinv : ∀ σ : Equiv.Perm (Fin n), ∀ d ∈ B', symAct p K σ d ∈ B' := by
    intro σ d hd
    have hd' : ((S.tor d : F) : G) ∈ B := hd
    obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt σ
    have hw : g ∈ L ⊓ torusNormalizer F := Subgroup.mem_inf.mpr ⟨hgL, hg⟩
    have h1 := hB _ hw _ hd'
    have h2 : ((S.tor (symAct p K σ d) : F) : G) = g * ((S.tor d : F) : G) * g⁻¹ := by
      rw [← S.act_apply, S.act_eq, ← hgσ]
      rfl
    show ((S.tor (symAct p K σ d) : F) : G) ∈ B
    rw [h2]
    exact h1
  rcases le_scalarSub_or_eq_top hp B' hinv with h | h
  · left
    intro b hb
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨b, hBF hb⟩
    have hdB : d ∈ B' := by
      show ((S.tor d : F) : G) ∈ B
      rw [hd]
      exact hb
    exact ⟨d, h hdB, congrArg Subtype.val hd⟩
  · right
    apply le_antisymm hBF
    intro e he
    obtain ⟨d, hd⟩ := S.tor.surjective ⟨e, he⟩
    have hdB : d ∈ B' := by rw [h]; trivial
    have : ((S.tor d : F) : G) ∈ B := hdB
    rwa [hd] at this

end SymCtx

end CFSG.RankThree.PartOne.KFU
