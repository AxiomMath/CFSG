module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Quasithin.Background.A1bGL2
public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)
open CFSG.RankThree.CentralExtension (autCommutator)
open scoped IsMulCommutative

section GeneralLinear

variable {F : Type*} [Field F]

theorem card_le_four_of_injective_GL_two (h2 : (2 : F) ≠ 0) {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1) (θ : A →* GL (Fin 2) F)
    (hθ : Function.Injective θ) : Nat.card A ≤ 4 := by
  classical
  set m : A → Matrix (Fin 2) (Fin 2) F := fun a => (θ a : Matrix (Fin 2) (Fin 2) F) with hmdef
  have hm : Function.Injective m := fun a b h => hθ (Units.ext h)
  have hmsq : ∀ a, m a * m a = 1 := fun a => by
    simp only [hmdef]
    rw [← Units.val_mul, ← map_mul, ← pow_two, hsq, map_one, Units.val_one]
  have hmc : ∀ a b, m a * m b = m b * m a := fun a b => by
    simp only [hmdef]
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm]
  by_cases hs : ∃ a₁, m a₁ ≠ 1 ∧ m a₁ ≠ -1
  · obtain ⟨a₁, h1, h1'⟩ := hs
    have hsub : ∀ a, m a ∈ ({1, -1, m a₁, -m a₁} : Finset (Matrix (Fin 2) (Fin 2) F)) := by
      intro a
      by_cases ha1 : m a = 1
      · simp [ha1]
      by_cases ha2 : m a = -1
      · simp [ha2]
      rcases CFSG.Quasithin.A1b.GL2.eq_or_eq_neg_of_commute h2 (hmsq a₁) (hmsq a) (hmc a₁ a) h1
        h1' ha1 ha2 with h | h <;> simp [h]
    calc Nat.card A ≤ Nat.card ({1, -1, m a₁, -m a₁} : Finset (Matrix (Fin 2) (Fin 2) F)) :=
          Nat.card_le_card_of_injective (fun a => ⟨m a, hsub a⟩)
            (fun a b h => hm (congrArg Subtype.val h))
      _ ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact Finset.card_le_four
  · push Not at hs
    have hsub : ∀ a, m a ∈ ({1, -1} : Finset (Matrix (Fin 2) (Fin 2) F)) := by
      intro a
      by_cases ha1 : m a = 1
      · simp [ha1]
      · simp [hs a ha1]
    calc Nat.card A ≤ Nat.card ({1, -1} : Finset (Matrix (Fin 2) (Fin 2) F)) :=
          Nat.card_le_card_of_injective (fun a => ⟨m a, hsub a⟩)
            (fun a b h => hm (congrArg Subtype.val h))
      _ ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact (Finset.card_le_two).trans (by norm_num)

theorem card_le_two_of_injective_GL_one {A : Type*} [Group A] (hsq : ∀ a : A, a ^ 2 = 1)
    (θ : A →* GL (Fin 1) F) (hθ : Function.Injective θ) : Nat.card A ≤ 2 := by
  classical
  set m : A → Matrix (Fin 1) (Fin 1) F := fun a => (θ a : Matrix (Fin 1) (Fin 1) F) with hmdef
  have hm : Function.Injective m := fun a b h => hθ (Units.ext h)
  have hsub : ∀ a, m a ∈ ({1, -1} : Finset (Matrix (Fin 1) (Fin 1) F)) := by
    intro a
    have hmsq : m a * m a = 1 := by
      simp only [hmdef]
      rw [← Units.val_mul, ← map_mul, ← pow_two, hsq, map_one, Units.val_one]
    have he : m a 0 0 * m a 0 0 = 1 := by
      have := congrFun (congrFun hmsq 0) 0
      simpa [Matrix.mul_apply] using this
    rcases mul_self_eq_one_iff.1 he with h | h
    · have : m a = 1 := by
        ext i j
        fin_cases i
        fin_cases j
        simpa using h
      simp [this]
    · have : m a = -1 := by
        ext i j
        fin_cases i
        fin_cases j
        simpa using h
      simp [this]
  calc Nat.card A ≤ Nat.card ({1, -1} : Finset (Matrix (Fin 1) (Fin 1) F)) :=
        Nat.card_le_card_of_injective (fun a => ⟨m a, hsub a⟩)
          (fun a b h => hm (congrArg Subtype.val h))
    _ ≤ 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact Finset.card_le_two

end GeneralLinear

theorem card_le_four_of_faithful_frattini {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (hV : Nat.card (P ⧸ frattini P) ≤ p ^ 2)
    {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a) (hsq : ∀ a : A, a ^ 2 = 1)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) : Nat.card A ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hVcomm, hVpow, -, d, hVd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  have hd2 : d ≤ 2 := by
    rw [hVd] at hV
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hV
  set ψ : A →* MulAut (P ⧸ frattini P) := (quotientAutomorphism (frattini P)).comp φ
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [mem_bot]
    have hker := (CFSG.GroupTheory.frattini_automorphism_kernel hP).2
    obtain ⟨k, hk⟩ := hker ⟨φ a, ha⟩
    have hk' : φ a ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : φ a ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_left.2 (hp.eq_two_or_odd'.resolve_left hp2))
    have h1 : φ a = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h2, hk'⟩
      rwa [hcop, pow_one] at this
    exact hφ (h1.trans (map_one φ).symm)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p)
    (fun a b => hVcomm.is_comm.comm a b) hVpow hVd
  set θ := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ψ
  have hθ : Function.Injective θ := (MulEquiv.injective _).comp hψ
  have h2F : (2 : ZMod p) ≠ 0 := CFSG.Quasithin.A1b.GL2.two_ne_zero_zmod hp2
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
  · have : Subsingleton (GL (Fin 0) (ZMod p)) := by
      constructor
      intro x y
      exact Units.ext (Subsingleton.elim _ _)
    have : Subsingleton A := ⟨fun a b => hθ (Subsingleton.elim _ _)⟩
    rw [Nat.card_unique]
    norm_num
  · exact (card_le_two_of_injective_GL_one hsq θ hθ).trans (by norm_num)
  · exact card_le_four_of_injective_GL_two h2F hcomm hsq θ hθ

theorem rank_two_exponent_prime_action_has_inverted_cyclic_detector {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Type*} [Group P] [Finite P] [Nontrivial P] (hP : IsPGroup p P)
    (hexp : ∀ x : P, x ^ p = 1) (hrank : CFSG.pRank p P ≤ 2) {A : Type*} [Group A]
    [Nontrivial A] [IsElementaryAbelian 2 A] (φ : A →* MulAut P) (hφ : Function.Injective φ)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (P ⋊[φ] A) V)
    (hV : ∃ g ∈ autCommutator φ.range, ∃ v : V, ρ (SemidirectProduct.inl g) v ≠ v) :
    (∃ a : ℕ, Nat.card A = 2 ^ a ∧ a ≤ 2) ∧
    (∃ B : Subgroup A, B.index = 2 ∧ ∃ a₀ : A, a₀ ∉ B ∧ ∃ x : P, (∀ b ∈ B, φ b x = x) ∧
      (∃ v : V, ρ (SemidirectProduct.inl (x⁻¹ * φ a₀ x)) v ≠ v) ∧
      Nat.card (zpowers (x⁻¹ * φ a₀ x)) = p ∧
      (∀ b ∈ B, φ b (x⁻¹ * φ a₀ x) = x⁻¹ * φ a₀ x) ∧
      φ a₀ (x⁻¹ * φ a₀ x) = (x⁻¹ * φ a₀ x)⁻¹ ∧
      (∀ a : A, (zpowers (x⁻¹ * φ a₀ x)).map (φ a).toMonoidHom = zpowers (x⁻¹ * φ a₀ x)) ∧
      ∃ c ∈ zpowers (x⁻¹ * φ a₀ x), ∃ v : V, ρ (SemidirectProduct.inl c) v ≠ v) ∧
    (IsCyclic P → Nat.card P = 3 → Nat.card A = 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite A := Finite.of_injective φ hφ
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm a b
  have hsq : ∀ a : A, a ^ 2 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup P) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank
  have hV2 := (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hP hexp hrank').2
  have h4 := card_le_four_of_faithful_frattini hp hp2 hP hV2 hcomm hsq φ hφ
  have hn2 : n ≤ 2 := by
    rw [hn] at h4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h4.trans (by norm_num))
  refine ⟨⟨n, hn, hn2⟩, ?_, ?_⟩
  ·
    let : MulDistribMulAction A P := MulDistribMulAction.compHom P φ
    have hsmul : ∀ (a : A) (x : P), a • x = φ a x := fun _ _ => rfl
    set K := (ρ.comp SemidirectProduct.inl).ker with hK
    have hKn : K.Normal := MonoidHom.normal_ker _
    have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P)
      (fun h => by
        obtain ⟨k, hk⟩ := hP.exists_card_eq
        rw [hk] at h
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h)
        exact hp2 this.symm)
    by_contra hcon
    push Not at hcon
    have htriv : ∀ B : Subgroup A, B.index = 2 → ∀ a₀ : A, a₀ ∉ B →
        ∀ x : P, (∀ b ∈ B, φ b x = x) → x⁻¹ * φ a₀ x ∈ K := by
      intro B hB a₀ ha₀ x hx
      by_contra hxK
      have hne : ∃ v : V, ρ (SemidirectProduct.inl (x⁻¹ * φ a₀ x)) v ≠ v := by
        by_contra h
        push Not at h
        exact hxK (MonoidHom.mem_ker.2 (LinearMap.ext h))
      set t := x⁻¹ * φ a₀ x with ht
      have ht1 : t ≠ 1 := by
        rintro h
        obtain ⟨v, hv⟩ := hne
        rw [h, map_one, map_one, Module.End.one_apply] at hv
        exact hv rfl
      have htord : orderOf t = p :=
        orderOf_eq_prime (hexp t) ht1
      have hBt : ∀ b ∈ B, φ b t = t := by
        intro b hb
        rw [ht, map_mul, map_inv, hx b hb, ← MulAut.mul_apply, ← map_mul, hcomm b a₀, map_mul,
          MulAut.mul_apply, hx b hb]
      have ha₀t : φ a₀ t = t⁻¹ := by
        rw [ht, map_mul, map_inv, ← MulAut.mul_apply, ← map_mul, ← pow_two, hsq, map_one,
          MulAut.one_apply, mul_inv_rev, inv_inv]
      have hinvt : ∀ a : A, (zpowers t).map (φ a).toMonoidHom = zpowers t := by
        intro a
        rw [MonoidHom.map_zpowers]
        by_cases haB : a ∈ B
        · exact congrArg zpowers (hBt a haB)
        · have hmem : a * a₀ ∈ B := (Subgroup.mul_mem_iff_of_index_two hB).2
            ⟨fun h => absurd h haB, fun h => absurd h ha₀⟩
          have h1 : φ a (φ a₀ t) = t := by
            rw [← MulAut.mul_apply, ← map_mul]
            exact hBt _ hmem
          rw [ha₀t, map_inv] at h1
          have h2 : φ a t = t⁻¹ := by
            rw [← inv_inv (φ a t), h1]
          change zpowers (φ a t) = zpowers t
          rw [h2, Subgroup.zpowers_inv]
      obtain ⟨v, hv⟩ := hne
      exact hv (hcon B hB a₀ ha₀ x hx ⟨v, hv⟩ (by rw [Nat.card_zpowers, htord]) hBt ha₀t hinvt
        t (mem_zpowers t) v)
    let Fx : Subgroup P :=
      { carrier := {x | ∀ a : A, x⁻¹ * φ a x ∈ K}
        mul_mem' := by
          intro x y hx hy a
          have e : (x * y)⁻¹ * φ a (x * y) = y⁻¹ * (x⁻¹ * φ a x) * y * (y⁻¹ * φ a y) := by
            rw [map_mul]
            group
          rw [e]
          exact K.mul_mem (by simpa using hKn.conj_mem _ (hx a) y⁻¹) (hy a)
        one_mem' := by
          intro a
          rw [map_one, inv_one, one_mul]
          exact K.one_mem
        inv_mem' := by
          intro x hx a
          have e : x⁻¹⁻¹ * φ a x⁻¹ = x * (x⁻¹ * φ a x)⁻¹ * x⁻¹ := by
            rw [map_inv]
            group
          rw [e]
          exact hKn.conj_mem _ (K.inv_mem (hx a)) x }
    have hFx : (⊤ : Subgroup P) ≤ Fx := by
      rw [← hgen]
      refine iSup₂_le fun B hB x hx a => ?_
      have hxB : ∀ b ∈ B, φ b x = x := fun b hb => hx ⟨b, hb⟩
      by_cases haB : a ∈ B
      · rw [hxB a haB, inv_mul_cancel]
        exact K.one_mem
      · exact htriv B hB a haB x hxB
    obtain ⟨g, hg, v, hv⟩ := hV
    have hgK : g ∈ K := by
      have hle : autCommutator φ.range ≤ K := by
        rw [autCommutator, closure_le]
        rintro _ ⟨u, _, ⟨a, rfl⟩, rfl⟩
        exact hFx (mem_top u) a
      exact hle hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hgK
    exact hv (by rw [hgK, Module.End.one_apply])
  ·
    intro hcyc h3
    have : IsCyclic P := hcyc
    have hAut : Nat.card (MulAut P) = 2 := by
      rw [Nat.card_congr (IsCyclic.mulAutMulEquiv (G := P)).toEquiv, h3, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient]
      decide
    have hle : Nat.card A ≤ 2 := hAut ▸ Nat.card_le_card_of_injective φ hφ
    have hge : 2 ≤ Nat.card A := Finite.one_lt_card
    omega

end CFSG.Quasithin.H13.NQTerm
