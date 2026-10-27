module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallSwap
import CFSG.HardMathSupport.RichardWeiss.Proving.ThreeCycleGen

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem permBar_eq_of_add_eq_zero {v w : permBar n} (h : v + w = 0) : v = w := by
  have h1 : v = -w := eq_neg_of_add_eq_zero_left h
  rw [h1, permBar_neg_eq]

theorem mem_of_two_pi (C : Cfg G M X n) (D : C.PiData) (hn : 5 ≤ n) {g : G} {t t' : ↥C.K}
    (ht : (t : G) ∈ conjSubgroup g (Rc X)) (ht' : (t' : G) ∈ conjSubgroup g (Rc X))
    (hv : Multiplicative.toAdd (D.π t) ≠ 0) (hw : Multiplicative.toAdd (D.π t') ≠ 0)
    (hvw : Multiplicative.toAdd (D.π t) ≠ Multiplicative.toAdd (D.π t')) : g ∈ M := by
  classical
  set v := Multiplicative.toAdd (D.π t) with hvdef
  set w := Multiplicative.toAdd (D.π t') with hwdef
  have hne1 : ∀ k : ↥C.K, Multiplicative.toAdd (D.π k) ≠ 0 → (k : G) ≠ 1 := by
    intro k hk0 h1
    apply hk0
    have : k = 1 := Subtype.ext h1
    rw [this, map_one]
    rfl
  have htt' : ((t * t' : ↥C.K) : G) ∈ conjSubgroup g (Rc X) :=
    (conjSubgroup g (Rc X)).mul_mem ht ht'
  have hvw' : Multiplicative.toAdd (D.π (t * t')) = v + w := by
    rw [map_mul, toAdd_mul]
  have hvw0 : v + w ≠ 0 := fun h => hvw (permBar_eq_of_add_eq_zero h)
  set N : Subgroup ↥X := (conjSubgroup g M).subgroupOf X with hN
  have hmemN : ∀ x : ↥X, x ∈ N ↔ g⁻¹ * (x : G) * g ∈ M := fun x => by
    rw [hN, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  have hcomm : ∀ (k : ↥C.K), (k : G) ∈ conjSubgroup g (Rc X) →
      Multiplicative.toAdd (D.π k) ≠ 0 → ∀ c : Perm (Fin n), c.IsThreeCycle →
      barAct c (Multiplicative.toAdd (D.π k)) = Multiplicative.toAdd (D.π k) →
      ∃ x ∈ N, (C.α x : Perm (Fin n)) = c := by
    intro k hk hk0 c hc hfix
    obtain ⟨x, hx3, hxc⟩ := exists_lift_pow_three C hc
    refine ⟨x, ?_, hxc⟩
    have hxk : (x : G) * k = k * x := comm_of_pow_three D hx3 (by rw [hxc]; exact hfix)
    exact (hmemN x).2 (conj_mem_of_comm C.S hk (hne1 k hk0) hxk)
  have hαN : N.map C.α = ⊤ := by
    rw [eq_top_iff,
      ← CFSG.HardMathSupport.RichardWeiss.Proving.closure_threeCycles_alternatingGroup,
      Subgroup.closure_le]
    rintro ⟨σ, hσA⟩ hσ3
    have hcl := isThreeCycle_mem_closure_of_fixes hn v w hσ3
    have hle : Subgroup.closure {τ : Perm (Fin n) | τ.IsThreeCycle ∧
        (barAct τ v = v ∨ barAct τ w = w ∨ barAct τ (v + w) = v + w)} ≤
        (N.map C.α).map (alternatingGroup (Fin n)).subtype := by
      rw [Subgroup.closure_le]
      rintro c ⟨hc3, hfix⟩
      obtain ⟨x, hxN, hxc⟩ : ∃ x ∈ N, (C.α x : Perm (Fin n)) = c := by
        rcases hfix with h | h | h
        · exact hcomm t ht hv c hc3 h
        · exact hcomm t' ht' hw c hc3 h
        · exact hcomm (t * t') htt' (by rw [hvw']; exact hvw0) c hc3 (by rw [hvw']; exact h)
      exact ⟨C.α x, ⟨x, hxN, rfl⟩, hxc⟩
    obtain ⟨y, hy, hyσ⟩ := hle hcl
    have : (⟨σ, hσA⟩ : alternatingGroup (Fin n)) = y := Subtype.ext hyσ.symm
    rw [SetLike.mem_coe, this]
    exact hy
  have hdecomp : ∀ x : ↥X, ∃ h ∈ N, C.α (h⁻¹ * x) = 1 := by
    intro x
    have hx : C.α x ∈ N.map C.α := by rw [hαN]; exact Subgroup.mem_top _
    obtain ⟨h, hh, hhx⟩ := hx
    exact ⟨h, hh, by rw [map_mul, map_inv, hhx, inv_mul_cancel]⟩
  have hWN : ∀ x : ↥X, (x : G) ∈ blockU X → x ∈ N := by
    intro x hx
    have hxt : (x : G) * t = t * x := (K_comm_W C t.2 hx).symm
    exact (hmemN x).2 (conj_mem_of_comm C.S ht (hne1 t hv) hxt)
  have hNnorm : N.Normal := ⟨fun m hm x => by
    obtain ⟨h, hh, hy⟩ := hdecomp x
    set y : ↥X := h⁻¹ * x with hydef
    have hyY : (y : G) ∈ CFSG.Open.pCoreOf 2 X := (C.α_eq_one_iff y).1 hy
    have hc : ((⁅y, m⁆ : ↥X) : G) ∈ blockU X :=
      Subgroup.commutator_mem_commutator (H₁ := blockQ X) hyY m.2
    have hym : y * m * y⁻¹ ∈ N := by
      have e : y * m * y⁻¹ = ⁅y, m⁆ * m := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hWN _ hc) hm
    have hx : x = h * y := by rw [hydef]; group
    rw [hx]
    have e : h * y * m * (h * y)⁻¹ = h * (y * m * y⁻¹) * h⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hh hym) (N.inv_mem hh)⟩
  have hq2 : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h, hh, hy⟩ := hdecomp x
    have hyY : h⁻¹ * x ∈ CFSG.pCore 2 ↥X := by rw [← C.α_ker]; exact hy
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, hyY⟩
    refine ⟨j, ?_⟩
    have e : (x : ↥X ⧸ N) = ((h⁻¹ * x : ↥X) : ↥X ⧸ N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (N.inv_mem hh), one_mul]
    rw [e, ← QuotientGroup.mk_pow]
    have : (h⁻¹ * x) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    rw [this, QuotientGroup.mk_one]
  have hNtop := C.S.block.1.eq_twoResidual N hq2
  apply mem_of_le_conj C.S
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
  exact (hmemN _).1 this

theorem conj_ne_of_not_mem (S : Setting G M X n) (hR : Rc X ≠ ⊥) {g : G} (hgM : g ∉ M) :
    conjSubgroup g (Rc X) ≠ Rc X := by
  intro h
  apply hgM
  rw [← S.normalizer_R hR, Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have : g * r * g⁻¹ ∈ conjSubgroup g (Rc X) := mem_conjSubgroup.2 (by simpa [mul_assoc] using hr)
    rwa [h] at this
  · intro hr
    rw [← h] at hr
    simpa [mul_assoc] using mem_conjSubgroup.1 hr

theorem eq_one_of_mem_conj_of_mem_C (S : Setting G M X n)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    {g : G} (hne : conjSubgroup g (Rc X) ≠ Rc X) {τ : G} (hτ : τ ∈ conjSubgroup g (Rc X))
    (hτC : τ ∈ Subgroup.centralizer (X : Set G)) : τ = 1 := by
  obtain ⟨j, hj⟩ := two_pow_of_mem_conj hτ
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
  have h2 : IsPGroup 2 (Subgroup.zpowers τ) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hR' := hRsyl _ h2 (Subgroup.zpowers_le.2 hτC)
  have h5 : τ ∈ Rc X ⊓ conjSubgroup g (Rc X) := ⟨hR' (Subgroup.mem_zpowers τ), hτ⟩
  rw [inf_conj_eq_bot S hne, Subgroup.mem_bot] at h5
  exact h5

theorem eq_of_mem_T_K (C : Cfg G M X n) (D : C.PiData) (hn : 5 ≤ n)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    (hR : Rc X ≠ ⊥) {g : G} (hgM : g ∉ M) {k k' : ↥C.K} (hk : (k : G) ∈ conjSubgroup g (Rc X))
    (hk' : (k' : G) ∈ conjSubgroup g (Rc X)) (h1 : (k : G) ≠ 1) (h1' : (k' : G) ≠ 1) :
    k = k' := by
  have hne := conj_ne_of_not_mem C.S hR hgM
  have hpi0 : ∀ k₀ : ↥C.K, (k₀ : G) ∈ conjSubgroup g (Rc X) → (k₀ : G) ≠ 1 →
      Multiplicative.toAdd (D.π k₀) ≠ 0 := by
    intro k₀ hk₀ hk₀1 h0
    apply hk₀1
    refine eq_one_of_mem_conj_of_mem_C C.S hRsyl hne hk₀ ((D.ker k₀).1 ?_)
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  by_contra hkk
  apply hgM
  refine mem_of_two_pi C D hn hk hk' (hpi0 k hk h1) (hpi0 k' hk' h1') fun h => hkk ?_
  have h2 : D.π (k * k'⁻¹) = 1 := by
    rw [map_mul, map_inv, Multiplicative.toAdd.injective h, mul_inv_cancel]
  have h3 := eq_one_of_mem_conj_of_mem_C C.S hRsyl hne
    ((conjSubgroup g (Rc X)).mul_mem hk ((conjSubgroup g (Rc X)).inv_mem hk')) ((D.ker _).1 h2)
  have h4 : k * k'⁻¹ = 1 := Subtype.ext h3
  exact mul_inv_eq_one.1 h4

omit [Finite G] in
theorem false_of_three_le_of_two {T : Subgroup G} (hT : ∃ a b c : ↥T, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {x y : G} (h : ∀ τ ∈ T, τ = x ∨ τ = y) : False := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hT
  rcases h a a.2 with ha | ha <;> rcases h b b.2 with hb | hb <;> rcases h c c.2 with hc | hc
  · exact hab (Subtype.ext (ha.trans hb.symm))
  · exact hab (Subtype.ext (ha.trans hb.symm))
  · exact hac (Subtype.ext (ha.trans hc.symm))
  · exact hbc (Subtype.ext (hb.trans hc.symm))
  · exact hbc (Subtype.ext (hb.trans hc.symm))
  · exact hac (Subtype.ext (ha.trans hc.symm))
  · exact hab (Subtype.ext (ha.trans hb.symm))
  · exact hab (Subtype.ext (ha.trans hb.symm))

theorem exists_three_of_card (g : G) (hcard : 3 ≤ Nat.card ↥(Rc X)) :
    ∃ a b c : ↥(conjSubgroup g (Rc X)), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  have : Fintype ↥(conjSubgroup g (Rc X)) := Fintype.ofFinite _
  rw [← Fintype.two_lt_card_iff, ← Nat.card_eq_fintype_card, card_conj]
  omega

theorem caseII_structure (C : Cfg G M X n) (D : C.PiData) (hn : 6 ≤ n)
    (hRsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X)
    {g : G} (hgM : g ∉ M) (hTM : conjSubgroup g (Rc X) ≤ M) (hcard : 3 ≤ Nat.card ↥(Rc X))
    (hTQ : conjSubgroup g (Rc X) ⊓ CFSG.Open.pCoreOf 2 M ≠ ⊥) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ t₁ ∈ conjSubgroup g (Rc X), ∃ ht₁W : t₁ ∈ blockU X, t₁ ≠ 1 ∧
      (∀ τ ∈ conjSubgroup g (Rc X), τ ∈ C.K → τ = 1 ∨ τ = t₁) ∧
      (∀ τ (hτ : τ ∈ conjSubgroup g (Rc X)),
        C.θ ⟨τ, hTM hτ⟩ = 1 ∨ C.θ ⟨τ, hTM hτ⟩ = swap a b) ∧
      (∃ s, ∃ hs : s ∈ conjSubgroup g (Rc X), C.θ ⟨s, hTM hs⟩ = swap a b) ∧
      Multiplicative.toAdd (D.π ⟨t₁, C.blockU_le_K ht₁W⟩) = barPt a + barPt b ∧
      ∀ q ∈ CFSG.Open.pCoreOf 2 M, g⁻¹ * q * g ∈ M := by
  classical
  set T := conjSubgroup g (Rc X) with hT
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hR : Rc X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hthree := exists_three_of_card g hcard
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTQ
  have ht₁T : t₁ ∈ T := (Subgroup.mem_inf.1 ht₁).1
  have ht₁Q : t₁ ∈ Q := (Subgroup.mem_inf.1 ht₁).2
  have ht₁1' : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  have ht₁K : t₁ ∈ C.K := Q_le_K C ht₁Q
  have hTK : ∀ τ ∈ T, τ ∈ C.K → τ = 1 ∨ τ = t₁ := by
    intro τ hτ hτK
    by_cases hτ1 : τ = 1
    · exact Or.inl hτ1
    · right
      have := eq_of_mem_T_K C D (by omega) hRsyl hR hgM (k := ⟨τ, hτK⟩) (k' := ⟨t₁, ht₁K⟩)
        hτ ht₁T hτ1 ht₁1'
      exact congrArg Subtype.val this
  have hWg : ∀ w ∈ blockU X, g⁻¹ * w * g ∈ M := fun w hw =>
    conj_mem_of_comm C.S ht₁T ht₁1' (K_comm_W C ht₁K hw).symm
  have hcommWT : ∀ w ∈ blockU X, ∀ τ ∈ T, w * τ * w⁻¹ * τ⁻¹ = 1 ∨ w * τ * w⁻¹ * τ⁻¹ = t₁ := by
    intro w hw τ hτ
    have h1 : w * τ * w⁻¹ ∈ T := conj_normalized C.S (hWg w hw) hτ
    have h2 : w * τ * w⁻¹ * τ⁻¹ ∈ blockU X := by
      have h3 : τ * w⁻¹ * τ⁻¹ ∈ blockU X := C.S.W_normalized (hTM hτ) ((blockU X).inv_mem hw)
      have e : w * τ * w⁻¹ * τ⁻¹ = w * (τ * w⁻¹ * τ⁻¹) := by group
      rw [e]
      exact (blockU X).mul_mem hw h3
    exact hTK _ (T.mul_mem h1 (T.inv_mem hτ)) (C.blockU_le_K h2)
  have hnotK : ∃ τ, ∃ hτ : τ ∈ T, C.θ ⟨τ, hTM hτ⟩ ≠ 1 := by
    by_contra h
    push Not at h
    exact false_of_three_le_of_two hthree fun τ hτ =>
      hTK τ hτ (C.mem_K.2 ⟨hTM hτ, h τ hτ⟩)
  have ht₁W : t₁ ∈ blockU X := by
    by_contra hW
    obtain ⟨τ, hτ, hθ⟩ := hnotK
    apply hθ
    refine (C.theta_eq_one_iff C.S.five_le_degree ⟨τ, hTM hτ⟩).2 fun u v hv => ?_
    have hc : (u : G) * τ * (u : G)⁻¹ * τ⁻¹ = 1 := by
      rcases hcommWT u u.2 τ hτ with h | h
      · exact h
      · exfalso
        apply hW
        rw [← h]
        have h3 : τ * (u : G)⁻¹ * τ⁻¹ ∈ blockU X :=
          C.S.W_normalized (hTM hτ) ((blockU X).inv_mem u.2)
        have e : (u : G) * τ * (u : G)⁻¹ * τ⁻¹ = u * (τ * (u : G)⁻¹ * τ⁻¹) := by group
        rw [e]
        exact (blockU X).mul_mem u.2 h3
    have hvu : v = u := Subtype.ext (by
      rw [hv]
      show τ * (u : G) * τ⁻¹ = u
      have : (u : G) * τ = τ * u := by
        calc (u : G) * τ = ((u : G) * τ * (u : G)⁻¹ * τ⁻¹) * (τ * u) := by group
          _ = τ * u := by rw [hc, one_mul]
      rw [← this]
      group)
    rw [hvu]
  set z : altHeart n := Multiplicative.toAdd (C.β ⟨t₁, ht₁W⟩) with hz
  have ht₁sq : t₁ * t₁ = 1 := by
    have := C.S.elemU.2 t₁ ht₁W
    rwa [pow_two] at this
  have hmove : ∀ τ (hτ : τ ∈ T), ∀ u : altHeart n,
      altAct (C.θ ⟨τ, hTM hτ⟩) u = u ∨ altAct (C.θ ⟨τ, hTM hτ⟩) u = u + z := by
    intro τ hτ u
    obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
    have hu : u = Multiplicative.toAdd (C.β w) := by rw [hw]; rfl
    have hspec := C.θ_spec ⟨τ, hTM hτ⟩ w ⟨τ * w * τ⁻¹, C.S.W_normalized (hTM hτ) w.2⟩ rfl
    rw [hu, ← hspec]
    rcases hcommWT w w.2 τ hτ with h | h
    · left
      have : τ * (w : G) * τ⁻¹ = w := by
        calc τ * (w : G) * τ⁻¹ = ((w : G) * τ * (w : G)⁻¹ * τ⁻¹)⁻¹ * w := by group
          _ = w := by rw [h, inv_one, one_mul]
      have e : (⟨τ * w * τ⁻¹, C.S.W_normalized (hTM hτ) w.2⟩ : ↥(blockU X)) = w :=
        Subtype.ext this
      rw [e]
    · right
      have : τ * (w : G) * τ⁻¹ = w * t₁ := by
        calc τ * (w : G) * τ⁻¹ = ((w : G) * τ * (w : G)⁻¹ * τ⁻¹)⁻¹ * w := by group
          _ = t₁⁻¹ * w := by rw [h]
          _ = w * t₁ := by
            rw [show t₁⁻¹ = t₁ from inv_eq_of_mul_eq_one_right ht₁sq]
            exact (C.S.elemU.1.is_comm.comm ⟨t₁, ht₁W⟩ w |> congrArg Subtype.val)
      have e : (⟨τ * w * τ⁻¹, C.S.W_normalized (hTM hτ) w.2⟩ : ↥(blockU X)) =
          w * ⟨t₁, ht₁W⟩ := Subtype.ext this
      rw [e, map_mul, toAdd_mul]
  obtain ⟨s, hs, hθs⟩ := hnotK
  rcases eq_one_or_isSwap_of_altAct (by omega) (hmove s hs) with h1 | ⟨a, b, hab, hsab⟩
  · exact absurd h1 hθs
  set P : Subgroup (Perm (Fin n)) := (T.subgroupOf M).map C.θ with hP
  have hPswap : ∀ σ ∈ P, σ = 1 ∨ σ.IsSwap := by
    rintro σ ⟨τ, hτ, rfl⟩
    exact eq_one_or_isSwap_of_altAct (by omega) (hmove τ (Subgroup.mem_subgroupOf.1 hτ))
  have hsP : C.θ ⟨s, hTM hs⟩ ∈ P := ⟨⟨s, hTM hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hall : ∀ τ (hτ : τ ∈ T), C.θ ⟨τ, hTM hτ⟩ = 1 ∨ C.θ ⟨τ, hTM hτ⟩ = swap a b := by
    intro τ hτ
    by_cases h1 : C.θ ⟨τ, hTM hτ⟩ = 1
    · exact Or.inl h1
    · right
      rw [← hsab]
      exact eq_of_isSwap_of_mem hPswap ⟨⟨τ, hTM hτ⟩, Subgroup.mem_subgroupOf.2 hτ, rfl⟩ hsP h1 hθs
  have hzab : z = (pairEW a b : altHeart n) :=
    eq_pairEW_of_swap (by omega) hab (by rw [← hsab]; exact hmove s hs)
  refine ⟨a, b, hab, t₁, ht₁T, ht₁W, ht₁1', hTK, hall, ⟨s, hs, hsab⟩, ?_, ?_⟩
  · rw [D.π_W ⟨t₁, C.blockU_le_K ht₁W⟩ ⟨t₁, ht₁W⟩ rfl, ← hz, hzab, heartToBar_pairEW]
  · intro q hq
    exact conj_mem_of_comm C.S ht₁T ht₁1' (W_comm_Q C ht₁W hq).symm

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall
