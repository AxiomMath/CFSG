module

public import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas
public import CFSG.Quasithin.Vol2.Ch11SKFIto

public section

namespace CFSG.HardMathSupport.C14Group

theorem not_dvd_card_of_gen_two {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hgen : Subgroup.closure {x : L | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (hcen : ∀ x : L, x ^ p = 1 → x ∈ Subgroup.center L) : ¬ p ∣ Nat.card L := by
  haveI := Fact.mk hp
  obtain ⟨N, hNn, hNc, k, hk⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.ito_normalPComplement (p := p) hp2 hcen
  haveI := hNn
  have hle : Subgroup.closure {x : L | ∃ k : ℕ, x ^ 2 ^ k = 1} ≤ N := by
    rw [Subgroup.closure_le]
    rintro x ⟨m, hm⟩
    have h1 : (QuotientGroup.mk x : L ⧸ N) ^ 2 ^ m = 1 := by rw [← QuotientGroup.mk_pow, hm]; rfl
    have h2 : (QuotientGroup.mk x : L ⧸ N) ^ p ^ k = 1 := by
      rw [← hk, Subgroup.index]; exact pow_card_eq_one'
    have hcop : Nat.Coprime (2 ^ m) (p ^ k) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h3 : orderOf (QuotientGroup.mk x : L ⧸ N) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)
  have htop : N = ⊤ := top_le_iff.1 (hgen ▸ hle)
  subst htop
  intro hdvd
  rw [Subgroup.card_top] at hNc
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hNc.symm hdvd)

end CFSG.HardMathSupport.C14Group

namespace CFSG.HardMathSupport.C14ExcIso

open CFSG.HardMathSupport.C14Group

abbrev fixG {G : Type*} [Group G] (F : G →* G) : Subgroup G := F.eqLocus (MonoidHom.id G)

theorem mem_fixG {G : Type*} [Group G] {F : G →* G} {g : G} : g ∈ fixG F ↔ F g = g :=
  Iff.rfl

theorem card_fixed_eq_of_isogeny {H H' : Type*} [Group H] [Group H'] (μ : H →* H')
    (hμ : Function.Surjective μ) (hK : μ.ker ≤ Subgroup.center H) [Finite μ.ker]
    (F : H →* H) (F' : H' →* H') (hcomm : ∀ h, μ (F h) = F' (μ h))
    (hLang : ∀ k ∈ μ.ker, ∃ x : H, x⁻¹ * F x = k) :
    Nat.card (fixG F) = Nat.card (fixG F') := by
  set X : Subgroup H := (fixG F').comap μ with hX
  have hmemX : ∀ x : H, x ∈ X ↔ x⁻¹ * F x ∈ μ.ker := by
    intro x
    rw [hX, Subgroup.mem_comap, mem_fixG, MonoidHom.mem_ker, map_mul, map_inv, hcomm,
      inv_mul_eq_one, eq_comm]
  have hcen : ∀ x : X, (x : H)⁻¹ * F x ∈ Subgroup.center H := fun x => hK ((hmemX x).1 x.2)
  let ψ : X →* μ.ker :=
    { toFun := fun x => ⟨(x : H)⁻¹ * F x, (hmemX x).1 x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have h := Subgroup.mem_center_iff.1 (hcen x) ((y : H)⁻¹)
        calc (y : H)⁻¹ * (x : H)⁻¹ * (F x * F y) = (y : H)⁻¹ * ((x : H)⁻¹ * F x) * F y := by
              group
          _ = ((x : H)⁻¹ * F x) * (y : H)⁻¹ * F y := by rw [h]
          _ = (x : H)⁻¹ * F x * ((y : H)⁻¹ * F y) := by group }
  have hψ : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := hLang k hk
    refine ⟨⟨x, (hmemX x).2 (hx ▸ hk)⟩, ?_⟩
    ext
    exact hx
  have hψker : Nat.card ψ.ker = Nat.card (fixG F) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : X) : H), ?_⟩
        invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
      change ((x : X) : H)⁻¹ * F ((x : X) : H) = 1 at h
      exact (mem_fixG.2 (inv_mul_eq_one.1 h).symm)
    · exact (hmemX y).2 (by rw [mem_fixG.1 y.2, inv_mul_cancel]; exact one_mem _)
    · apply MonoidHom.mem_ker.2
      ext
      change (y : H)⁻¹ * F y = 1
      rw [mem_fixG.1 y.2, inv_mul_cancel]
  let ν : X →* fixG F' := (μ.comp X.subtype).codRestrict (fixG F') fun x => x.2
  have hν : Function.Surjective ν := by
    rintro ⟨h', hh'⟩
    obtain ⟨h, rfl⟩ := hμ h'
    exact ⟨⟨h, hh'⟩, rfl⟩
  have hνker : Nat.card ν.ker = Nat.card μ.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : X) : H), ?_⟩
        invFun := fun k => ⟨⟨k, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun k => rfl }
    · have h := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
      exact MonoidHom.mem_ker.2 h
    · change μ k ∈ fixG F'
      rw [MonoidHom.mem_ker.1 k.2]
      exact one_mem _
    · apply MonoidHom.mem_ker.2
      ext
      exact MonoidHom.mem_ker.1 k.2
  have h1 : Nat.card X = Nat.card (fixG F) * Nat.card μ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hψker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, mul_comm]
  have h2 : Nat.card X = Nat.card (fixG F') * Nat.card μ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ν.ker, hνker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ν hν).toEquiv]
  have hpos : 0 < Nat.card μ.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)

theorem card_fixed_prod {A B : Type*} [Group A] [Group B] (FA : A →* A) (FB : B →* B) :
    Nat.card (fixG (FA.prodMap FB)) = Nat.card (fixG FA) * Nat.card (fixG FB) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
      invFun := fun y => ⟨(y.1, y.2), Prod.ext y.1.2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem exists_fixed_of_iterate {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (f : H →* H) (hf : ∀ x, f^[p] x = x) (hH : p ∣ Nat.card H) :
    ∃ x : H, orderOf x = p ∧ f x = x := by
  have hinj : Function.Injective f := by
    intro x y h
    have hx := hf x
    have hy := hf y
    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hk, Function.iterate_succ_apply] at hx hy
    rw [← hx, ← hy, h]
  let α : MulAut H := MulEquiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hpow : ∀ n (x : H), (α ^ n) x = f^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
      rfl
  obtain ⟨x, hx, hxα⟩ := exists_fixed_of_order_p hp α (by ext x; rw [hpow, hf]; rfl) hH
  exact ⟨x, hx, hxα⟩

theorem not_dvd_card_fixed_of_index {S : Type*} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (G₀ G : S →* S) (hG : ∀ x, G x = G₀^[p] x) [Finite (fixG G)]
    (hSat : ∀ x : fixG G₀, x ^ p = 1 → x ∈ Subgroup.center (fixG G₀))
    (hidx : ¬ p ∣ (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}).index) :
    ¬ p ∣ Nat.card (fixG G) := by
  have hle : fixG G₀ ≤ fixG G := by
    intro x hx
    rw [mem_fixG, hG]
    exact Function.iterate_fixed hx p
  haveI : Finite (fixG G₀) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  set D := Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1} with hD
  have hgenD : Subgroup.closure {x : D | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    refine Subgroup.closure_induction (p := fun y hy => (⟨y, hy⟩ : D) ∈
      Subgroup.closure {x : D | ∃ k : ℕ, x ^ 2 ^ k = 1}) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Subgroup.subset_closure (show ∃ k : ℕ, (⟨y, Subgroup.subset_closure hy⟩ : D) ^ 2 ^ k = 1
        from hy.imp fun k hk => Subtype.ext hk)
    · exact one_mem _
    · intro y z hy hz hy' hz'
      exact mul_mem hy' hz'
    · intro y hy hy'
      exact inv_mem hy'
  have hD1 : ¬ p ∣ Nat.card D := by
    refine not_dvd_card_of_gen_two hp hp2 hgenD fun x hx => ?_
    have hc := hSat (x : fixG G₀) (by simpa using congrArg Subtype.val hx)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact Subtype.ext (hc g)
  have hL : ¬ p ∣ Nat.card (fixG G₀) := by
    rw [← D.index_mul_card]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hidx h
    · exact hD1 h
  intro hdvd
  have hmap : ∀ x ∈ fixG G, G₀ x ∈ fixG G := by
    intro x hx
    rw [mem_fixG, hG, ← Function.iterate_succ_apply, Function.iterate_succ_apply', ← hG,
      mem_fixG.1 hx]
  let f : fixG G →* fixG G := (G₀.comp (fixG G).subtype).codRestrict (fixG G) fun x => hmap x x.2
  have hf : ∀ x, f^[p] x = x := by
    intro x
    have h : ∀ n, ((f^[n] x : fixG G) : S) = G₀^[n] x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    apply Subtype.ext
    rw [h, ← hG]
    exact x.2
  obtain ⟨x, hxo, hxf⟩ := exists_fixed_of_iterate hp f hf hdvd
  have hx0 : (x : S) ∈ fixG G₀ := congrArg Subtype.val hxf
  apply hL
  have : orderOf (⟨x, hx0⟩ : fixG G₀) = p :=
    (Subgroup.orderOf_coe (⟨x, hx0⟩ : fixG G₀)).symm.trans ((Subgroup.orderOf_coe x).trans hxo)
  rw [← this]
  exact orderOf_dvd_natCard _

theorem pElt_mem_of_card {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (F : M →* M)
    [Finite (fixG F)] (Z : Subgroup M) (hZ : Z ≤ Subgroup.center M) (s : ℕ)
    (hord : Nat.card (fixG F) = Nat.card (Z ⊓ fixG F : Subgroup M) * s) (hs : ¬ p ∣ s)
    (g : M) (hg : F g = g) (hgp : ∃ n : ℕ, g ^ p ^ n = 1) : g ∈ Z := by
  have hZF : Finite (Z ⊓ fixG F : Subgroup M) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right : Z ⊓ fixG F ≤ fixG F))
  have hN : Nat.card (Z.subgroupOf (fixG F)) = Nat.card (Z ⊓ fixG F : Subgroup M) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hNn : (Z.subgroupOf (fixG F)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h : (k : M) * n * (k : M)⁻¹ = n := by
      rw [Subgroup.mem_center_iff.1 (hZ hn) k, mul_inv_cancel_right]
    simpa [h] using hn
  have hidx : (Z.subgroupOf (fixG F)).index = s := by
    have h1 := (Z.subgroupOf (fixG F)).index_mul_card
    rw [hN, hord, mul_comm (Nat.card (Z ⊓ fixG F : Subgroup M))] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  obtain ⟨n, hn⟩ := hgp
  have key : ∀ (H : Type _) [Group H] (N : Subgroup H) [N.Normal] (x : H) (m : ℕ),
      x ^ m = 1 → Nat.Coprime m N.index → x ∈ N := by
    intro H _ N _ x m hm hc
    have hx1 : (QuotientGroup.mk x : H ⧸ N) ^ N.index = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.pow_index_mem N x
    have hx2 : (QuotientGroup.mk x : H ⧸ N) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, hm, QuotientGroup.mk_one]
    have := pow_gcd_eq_one.2 ⟨hx2, hx1⟩
    rw [hc, pow_one, QuotientGroup.eq_one_iff] at this
    exact this
  have hmem := key (fixG F) (Z.subgroupOf (fixG F)) ⟨g, hg⟩ (p ^ n)
    (Subtype.ext (by simpa using hn))
    (by rw [hidx]; exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hs))
  exact Subgroup.mem_subgroupOf.1 hmem

end CFSG.HardMathSupport.C14ExcIso
