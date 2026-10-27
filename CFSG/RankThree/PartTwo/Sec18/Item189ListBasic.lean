module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListDefs
public import CFSG.RankThree.PartTwo.Sec18.Item189O2
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec12.Item124

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def UniqueSylowOver189 {Y : Type} [Group Y] (X : Subgroup Y) : Prop :=
  ∀ R : Subgroup Y, R ≤ X → IsPGroup 2 R → R ≠ ⊥ →
    ∃! U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U X ∧ R ≤ U

namespace ListData189

variable {Y : Type} [Group Y] {X Q : Subgroup Y} {Γ : Subgroup (MulAut Y)} {x : Y}

theorem le_of_normal_ne_bot (h : ListData189 X Q Γ x) {N : Subgroup Y} (hN : N.Normal)
    (hN1 : N ≠ ⊥) : X ≤ N := by
  haveI := h.normal
  haveI := h.simple
  haveI hn : ((X ⊓ N).subgroupOf X).Normal := Subgroup.Normal.subgroupOf inferInstance X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X ⊓ N).subgroupOf X) with hb | ht
  · exfalso
    have hdisj : Disjoint (X ⊓ N) X := Subgroup.subgroupOf_eq_bot.mp hb
    have hXN : X ⊓ N = ⊥ := by
      rw [disjoint_iff, inf_eq_left.mpr (inf_le_left : X ⊓ N ≤ X)] at hdisj
      exact hdisj
    apply hN1
    rw [eq_bot_iff]
    intro n hn'
    have hc : n ∈ Subgroup.centralizer (X : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 : g * n * g⁻¹ * n⁻¹ ∈ X ⊓ N := by
        refine ⟨?_, N.mul_mem (hN.conj_mem n hn' g) (N.inv_mem hn')⟩
        have e : g * n * g⁻¹ * n⁻¹ = g * (n * g⁻¹ * n⁻¹) := by group
        rw [e]
        exact X.mul_mem hg (h.normal.conj_mem _ (X.inv_mem hg) n)
      rw [hXN, Subgroup.mem_bot] at h1
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    rw [h.centralizer_eq] at hc
    exact hc
  · rw [Subgroup.subgroupOf_eq_top] at ht
    exact (le_inf_iff.mp ht).2

theorem isPerfect (h : ListData189 X Q Γ x) : Group.IsPerfect ↥X := by
  haveI := h.simple
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥X) with hb | ht
  · exfalso
    have hcomm : ∀ a b : ↥X, a * b = b * a := by
      intro a b
      have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hle : X ≤ Subgroup.centralizer (X : Set Y) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb'
      exact congrArg Subtype.val (hcomm ⟨b, hb'⟩ ⟨a, ha⟩)
    rw [h.centralizer_eq, le_bot_iff] at hle
    exact (Subgroup.nontrivial_iff_ne_bot X).mp h.simple.toNontrivial hle
  · exact ht

theorem apply_mem (h : ListData189 X Q Γ x) (α : MulAut Y) {t : Y} (ht : t ∈ X) :
    α t ∈ X := by
  haveI := h.normal
  have hX1 : X ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot X).mp h.simple.toNontrivial
  have key : ∀ β : MulAut Y, X ≤ X.map β.toMonoidHom := by
    intro β
    haveI : (X.map β.toMonoidHom).Normal :=
      Subgroup.Normal.map h.normal β.toMonoidHom β.surjective
    refine h.le_of_normal_ne_bot inferInstance ?_
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ β.injective]
  obtain ⟨z, hz, hzt⟩ := key α⁻¹ ht
  have : α t = z := by
    rw [← hzt]
    simp
  rw [this]
  exact hz

theorem mem_of_conjNormal_inner [hX : X.Normal] (h : ListData189 X Q Γ x) {σ : Y} {g : ↥X}
    (hg : MulAut.conjNormal σ = MulAut.conj g) : σ ∈ X := by
  have hc : (g : Y)⁻¹ * σ ∈ Subgroup.centralizer (X : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := congrArg (fun φ : MulAut ↥X => ((φ ⟨a, ha⟩ : ↥X) : Y)) hg
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    have h1' : σ * a * σ⁻¹ = (g : Y) * a * (g : Y)⁻¹ := by simpa using h1
    calc a * ((g : Y)⁻¹ * σ) = (g : Y)⁻¹ * ((g : Y) * a * (g : Y)⁻¹) * σ := by group
      _ = (g : Y)⁻¹ * (σ * a * σ⁻¹) * σ := by rw [← h1']
      _ = ((g : Y)⁻¹ * σ) * a := by group
  rw [h.centralizer_eq, Subgroup.mem_bot] at hc
  have : σ = (g : Y) := by
    calc σ = (g : Y) * ((g : Y)⁻¹ * σ) := by group
      _ = (g : Y) := by rw [hc, mul_one]
  rw [this]
  exact g.2

theorem apply_x (h : ListData189 X Q Γ x) {γ : MulAut Y} (hγ : γ ∈ Γ) : γ x = x := by
  have hc := h.comm γ hγ _ h.conj_mem
  have key : ∀ y : Y, (γ x) * γ y * (γ x)⁻¹ = x * γ y * x⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut Y => φ y) hc
    simpa [MulAut.conj_apply, map_mul, map_inv] using this
  have hz : x⁻¹ * γ x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := γ.surjective z
    calc γ y * (x⁻¹ * γ x) = x⁻¹ * (x * γ y * x⁻¹) * γ x := by group
      _ = x⁻¹ * (γ x * γ y * (γ x)⁻¹) * γ x := by rw [key y]
      _ = x⁻¹ * γ x * γ y := by group
  have hz' : x⁻¹ * γ x ∈ Subgroup.centralizer (X : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.mp hz g
  rw [h.centralizer_eq, Subgroup.mem_bot] at hz'
  exact (inv_mul_eq_one.mp hz').symm

theorem commutator_mem (h : ListData189 X Q Γ x) {q : Y} (hq : q ∈ Q) :
    x * q * x⁻¹ * q⁻¹ ∈ Q ⊓ X := by
  refine ⟨Q.mul_mem (h.inv _ h.conj_mem q hq) (Q.inv_mem hq), ?_⟩
  have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [e]
  exact X.mul_mem h.mem (h.normal.conj_mem _ (X.inv_mem h.mem) q)

theorem gammaInv_inf (h : ListData189 X Q Γ x) : GammaInv189 Γ (Q ⊓ X) :=
  fun γ hγ t ht => ⟨h.inv γ hγ t ht.1, h.apply_mem γ ht.2⟩

theorem mem_normalizer_inf (h : ListData189 X Q Γ x) :
    x ∈ Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have hinv : GammaInv189 Γ (Q ⊓ X) := h.gammaInv_inf
  constructor
  · intro ht
    exact hinv _ h.conj_mem t ht
  · intro ht
    have := hinv _ (Γ.inv_mem h.conj_mem) _ ht
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem comm_of_inf_eq_bot (h : ListData189 X Q Γ x) (hQ : Q ⊓ X = ⊥) {q : Y} (hq : q ∈ Q) :
    q * x = x * q := by
  have h1 := h.commutator_mem hq
  rw [hQ, Subgroup.mem_bot] at h1
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem absInnerFree_iff (h : ListData189 X Q Γ x) : AbsInnerFree189 X Q ↔ Q ⊓ X = ⊥ := by
  unfold AbsInnerFree189
  rw [h.centralizer_eq, sup_bot_eq, le_bot_iff]

theorem card_inf_mul_outOrder [Finite Y] (h : ListData189 X Q Γ x) :
    Nat.card ↥(Q ⊓ X) * absOutOrder189 X = Nat.card Q := by
  haveI := h.normal
  have h1 : X.relIndex Q * Nat.card ↥(X ⊓ Q) = Nat.card Q :=
    Subgroup.relIndex_mul_card X Q
  have h2 : X.relIndex (Q ⊔ X) = X.relIndex Q :=
    Subgroup.relIndex_sup_right Q X
  rw [sup_comm, h.sup_eq, Subgroup.relIndex_top_right] at h2
  unfold absOutOrder189
  rw [h.centralizer_eq, sup_bot_eq, h2, inf_comm, mul_comm]
  exact h1

theorem isSylowOf_map [Finite Y] (h : ListData189 X Q Γ x) (α : MulAut Y) {U : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.map α.toMonoidHom) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : X.map α.toMonoidHom = X := by
    apply le_antisymm
    · rintro t ⟨s, hs, rfl⟩
      exact h.apply_mem α hs
    · intro t ht
      exact ⟨α⁻¹ t, h.apply_mem α⁻¹ ht, by simp⟩
  have := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hU α.toMonoidHom
  rwa [hX] at this

theorem mem_normalizer_map (α : MulAut Y) {V : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (V : Set Y)) :
    α g ∈ Subgroup.normalizer ((V.map α.toMonoidHom : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro t
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simpa using hg (α.symm t)

theorem mem_normalizer_of_map_conj {U : Subgroup Y} {σ : Y}
    (hσ : U.map (MulAut.conj σ).toMonoidHom = U) : σ ∈ Subgroup.normalizer (U : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hu := Subgroup.ext_iff.mp hσ (σ * u * σ⁻¹)
  rw [Subgroup.mem_map_equiv] at hu
  have e : (MulAut.conj σ).symm (σ * u * σ⁻¹) = u := by
    rw [MulAut.conj_symm_apply]
    group
  rw [e] at hu
  exact hu

theorem le_of_normalizes (h : ListData189 X Q Γ x) {U : Subgroup Y} (hU2 : IsPGroup 2 U)
    (hQN : Q ≤ Subgroup.normalizer (U : Set Y)) (hUΓ : GammaInv189 Γ U) : U ≤ Q := by
  have hT2 : IsPGroup 2 (Q ⊔ U : Subgroup Y) := h.isPGroup.to_sup_of_normal_right' hU2 hQN
  have hTΓ : GammaInv189 Γ (Q ⊔ U) := by
    intro γ hγ t ht
    have hle : (Q ⊔ U).map γ.toMonoidHom ≤ Q ⊔ U := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (by rintro _ ⟨s, hs, rfl⟩; exact h.inv γ hγ s hs)
        (by rintro _ ⟨s, hs, rfl⟩; exact hUΓ γ hγ s hs)
    exact hle ⟨t, ht, rfl⟩
  exact le_sup_right.trans (h.maximal _ hT2 le_sup_left hTΓ).le

theorem isSylowOf_top_of_inf_ne_bot [Finite Y] (h : ListData189 X Q Γ x)
    (hTI : UniqueSylowOver189 X) (hne : Q ⊓ X ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf 2 Q ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.normal
  have hRp : IsPGroup 2 (Q ⊓ X : Subgroup Y) := h.isPGroup.to_le inf_le_left
  obtain ⟨U₁, ⟨hU₁, hRU₁⟩, huniq⟩ := hTI (Q ⊓ X) inf_le_right hRp hne
  have hinv : ∀ α : MulAut Y, (∀ t ∈ (Q ⊓ X : Subgroup Y), α⁻¹ t ∈ (Q ⊓ X : Subgroup Y)) →
      U₁.map α.toMonoidHom = U₁ := fun α hα =>
    huniq _ ⟨h.isSylowOf_map α hU₁, fun t ht => ⟨α⁻¹ t, hRU₁ (hα t ht), by simp⟩⟩
  have hQN : Q ≤ Subgroup.normalizer (U₁ : Set Y) := by
    intro σ hσ
    refine mem_normalizer_of_map_conj (hinv (MulAut.conj σ) fun t ht => ?_)
    rw [← map_inv, MulAut.conj_apply, inv_inv]
    exact ⟨Q.mul_mem (Q.mul_mem (Q.inv_mem hσ) ht.1) hσ,
      by simpa using h.normal.conj_mem t ht.2 σ⁻¹⟩
  have hΓ : GammaInv189 Γ U₁ := by
    intro γ hγ t ht
    have h1 := hinv γ (fun s hs => h.gammaInv_inf γ⁻¹ (Γ.inv_mem hγ) s hs)
    have h2 : γ t ∈ U₁.map γ.toMonoidHom := ⟨t, ht, rfl⟩
    rwa [h1] at h2
  have hU₁Q : U₁ ≤ Q := h.le_of_normalizes hU₁.isPGroup hQN hΓ
  have hRU : Q ⊓ X = U₁ := le_antisymm hRU₁ (le_inf hU₁Q hU₁.le)
  have h2 : Q.relIndex ⊤ = Q.relIndex X := by
    have := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal X Q
    rwa [h.sup_eq] at this
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, h.isPGroup, ?_⟩
  rw [h2, ← Subgroup.inf_relIndex_right Q X, hRU]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hU₁).2.2

theorem map_eq_of_pair [Finite Y] (h : ListData189 X Q Γ x) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hne : U ≠ U') (hxU : x ∈ Subgroup.normalizer (U : Set Y))
    (hxU' : x ∈ Subgroup.normalizer (U' : Set Y))
    (hfix : ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
      x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U')
    {γ : MulAut Y} (hγ : γ ∈ Γ) : U.map γ.toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγx : γ x = x := h.apply_x hγ
  have hperm : ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
      x ∈ Subgroup.normalizer (V : Set Y) → V.map γ.toMonoidHom = U ∨ V.map γ.toMonoidHom = U' :=
    fun V hV hxV => hfix _ (h.isSylowOf_map γ hV) (by
      have := mem_normalizer_map γ hxV
      rwa [hγx] at this)
  have hinj := Subgroup.map_injective (f := γ.toMonoidHom) γ.injective
  rcases hperm U hU hxU with h1 | h1
  · exact h1
  · exfalso
    rcases hperm U' hU' hxU' with h2 | h2
    · have e3 : ∀ t : Y, γ (γ (γ t)) = t := by
        intro t
        have := congrArg (fun φ : MulAut Y => φ t) (h.pow_three γ hγ)
        simpa [pow_succ, MulAut.mul_apply] using this
      have hUU' : U ≤ U' := by
        intro t ht
        have a1 : γ t ∈ U' := h1 ▸ (⟨t, ht, rfl⟩ : γ t ∈ U.map γ.toMonoidHom)
        have a2 : γ (γ t) ∈ U := h2 ▸ (⟨γ t, a1, rfl⟩ : γ (γ t) ∈ U'.map γ.toMonoidHom)
        have a3 : γ (γ (γ t)) ∈ U' := h1 ▸ (⟨γ (γ t), a2, rfl⟩ :
          γ (γ (γ t)) ∈ U.map γ.toMonoidHom)
        rwa [e3] at a3
      exact hne (hU.eq_of_le hUU' hU'.le hU'.isPGroup).symm
    · exact hne (hinj (h1.trans h2.symm))

theorem exists_swap [Finite Y] (h : ListData189 X Q Γ x) (hQ : Q ⊓ X = ⊥) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hne : U ≠ U') (hxU : x ∈ Subgroup.normalizer (U : Set Y))
    (hxU' : x ∈ Subgroup.normalizer (U' : Set Y))
    (hfix : ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
      x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U') :
    ∃ σ ∈ Q, U.map (MulAut.conj σ).toMonoidHom = U' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hQN : Q ≤ Subgroup.normalizer (U : Set Y) := by
    intro σ hσ
    apply mem_normalizer_of_map_conj
    have hσx : (MulAut.conj σ) x = x := by
      rw [MulAut.conj_apply, h.comm_of_inf_eq_bot hQ hσ]
      group
    have h1 : x ∈ Subgroup.normalizer
        ((U.map (MulAut.conj σ).toMonoidHom : Subgroup Y) : Set Y) := by
      have := mem_normalizer_map (MulAut.conj σ) hxU
      rwa [hσx] at this
    rcases hfix _ (h.isSylowOf_map _ hU) h1 with h2 | h2
    · exact h2
    · exact absurd h2 (hcon σ hσ)
  have hUΓ : GammaInv189 Γ U := by
    intro γ hγ t ht
    have h1 := h.map_eq_of_pair hU hU' hne hxU hxU' hfix hγ
    have h2 : γ t ∈ U.map γ.toMonoidHom := ⟨t, ht, rfl⟩
    rwa [h1] at h2
  have hUQ : U ≤ Q := h.le_of_normalizes hU.isPGroup hQN hUΓ
  have hU1 : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h3 : u ∈ Q ⊓ X := ⟨hUQ hu, hU.le hu⟩
    rwa [hQ] at h3
  have hc : Nat.card U' = Nat.card U := by rw [hU.card_eq, hU'.card_eq]
  have hU1' : U' = ⊥ := by
    rw [hU1, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  exact hne (hU1.trans hU1'.symm)

theorem absOutOrder_eq [Finite Y] (h : ListData189 X Q Γ x) (hQ : Q ⊓ X = ⊥) {k : ℕ}
    (hdvd : Nat.card Q ∣ 2 ^ k) {σ : Y} (hσ : σ ∈ Q) (hord : 2 ^ k ∣ orderOf σ) :
    absOutOrder189 X = 2 ^ k := by
  have h1 := h.card_inf_mul_outOrder
  rw [hQ, Subgroup.card_bot, one_mul] at h1
  rw [h1]
  exact Nat.dvd_antisymm hdvd (hord.trans (Subgroup.orderOf_dvd_natCard Q hσ))

end ListData189

theorem fusionIsBenderGroup_of_projSL_two {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* projSL 2 (GaloisField 2 n)) : CFSG.Open.fusionIsBenderGroup X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Or.inl ⟨n, hn, ⟨e.trans (Sec4.projSLEquivPSL (GaloisField 2 n))⟩⟩

theorem fusionIsBenderGroup_of_projSU_three {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* projSU 3 2 n) : CFSG.Open.fusionIsBenderGroup X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ^ n ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨e'⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn
    (statedClassicalModel_psu189 (by omega) hq e)
  exact Or.inr (Or.inl ⟨n, hn, ⟨e'⟩⟩)

end CFSG.RankThree.PartTwo.Sec18
