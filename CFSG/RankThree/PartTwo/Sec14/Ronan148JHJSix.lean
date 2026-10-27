module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo

theorem fst_eq_one_of_pow_seven_eq_one {A B : Type*} [Group A] [Group B] (hA : Nat.card A = 60)
    {p : A × B} (hp : p ^ 7 = 1) : p.1 = 1 := by
  have h7 : p.1 ^ 7 = 1 := by simpa using congrArg Prod.fst hp
  have hdvd : orderOf p.1 ∣ Nat.gcd 7 60 := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h7) ?_
    have h := orderOf_dvd_natCard p.1
    rwa [hA] at h
  have hg : Nat.gcd 7 60 = 1 := by norm_num
  rw [hg] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem nonempty_mulEquiv_of_mem_iff {Z A B : Type*} [Group Z] [Group A] [Group B]
    (ψ : Z ≃* A × B) (K : Subgroup Z) (hK : ∀ x : Z, x ∈ K ↔ (ψ x).1 = 1) :
    Nonempty (↥K ≃* B) := by
  refine ⟨MulEquiv.ofBijective ((MonoidHom.snd A B).comp (ψ.toMonoidHom.comp K.subtype)) ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : ψ x = ψ y := Prod.ext (((hK x).mp hx).trans ((hK y).mp hy).symm) hxy
    exact Subtype.ext (ψ.injective hxy')
  · intro j
    have hz : ψ.symm (1, j) ∈ K := (hK _).mpr (by rw [MulEquiv.apply_symm_apply])
    refine ⟨⟨ψ.symm (1, j), hz⟩, ?_⟩
    show (ψ (ψ.symm (1, j))).2 = j
    rw [MulEquiv.apply_symm_apply]

theorem closure_normal_of_conj_mem {G : Type*} [Group G] (S : Set G)
    (hS : ∀ g : G, ∀ x ∈ S, g * x * g⁻¹ ∈ S) : (Subgroup.closure S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.closure_induction (p := fun y _ => g * y * g⁻¹ ∈ Subgroup.closure S)
    ?_ ?_ ?_ ?_ hn
  · intro x hx
    exact Subgroup.subset_closure (hS g x hx)
  · show g * 1 * g⁻¹ ∈ Subgroup.closure S
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · intro x y _ _ hx hy
    show g * (x * y) * g⁻¹ ∈ Subgroup.closure S
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  · intro x _ hx
    show g * x⁻¹ * g⁻¹ ∈ Subgroup.closure S
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem closure_pow_eq_top {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {p : ℕ}
    [Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    Subgroup.closure {x : G | x ^ p = 1} = ⊤ := by
  have hS : ∀ g : G, ∀ x ∈ {x : G | x ^ p = 1}, g * x * g⁻¹ ∈ {x : G | x ^ p = 1} := by
    intro g x hx
    show (g * x * g⁻¹) ^ p = 1
    rw [conj_pow, show x ^ p = 1 from hx, mul_one, mul_inv_cancel]
  haveI := closure_normal_of_conj_mem _ hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {x : G | x ^ p = 1}) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      have := (Fact.out : p.Prime).two_le
      omega
    have hxS : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxC : x ∈ Subgroup.closure {x : G | x ^ p = 1} := Subgroup.subset_closure hxS
    rw [h, Subgroup.mem_bot] at hxC
    exact hx1 hxC
  · exact h

theorem conj_mem_of_closure_eq_top {Γ : Type*} [Group Γ] (V : Subgroup Γ) (a : Γ)
    (S : Set V) (hS : Subgroup.closure S = ⊤) (hconj : ∀ z ∈ S, a * (z : Γ) * a⁻¹ ∈ V) :
    ∀ u ∈ V, a * u * a⁻¹ ∈ V := by
  intro u hu
  have huC : (⟨u, hu⟩ : V) ∈ Subgroup.closure S := by
    rw [hS]
    exact Subgroup.mem_top _
  have key : ∀ w : V, w ∈ Subgroup.closure S → a * (w : Γ) * a⁻¹ ∈ V := by
    intro w hw
    refine Subgroup.closure_induction (p := fun (y : V) _ => a * (y : Γ) * a⁻¹ ∈ V)
      ?_ ?_ ?_ ?_ hw
    · intro z hz
      exact hconj z hz
    · show a * ((1 : V) : Γ) * a⁻¹ ∈ V
      simp
    · intro z y _ _ hz hy
      have e' : a * ((z * y : V) : Γ) * a⁻¹ = (a * (z : Γ) * a⁻¹) * (a * (y : Γ) * a⁻¹) := by
        simp only [Subgroup.coe_mul]
        group
      show a * ((z * y : V) : Γ) * a⁻¹ ∈ V
      rw [e']
      exact mul_mem hz hy
    · intro z _ hz
      have e' : a * ((z⁻¹ : V) : Γ) * a⁻¹ = (a * (z : Γ) * a⁻¹)⁻¹ := by
        simp only [Subgroup.coe_inv]
        group
      show a * ((z⁻¹ : V) : Γ) * a⁻¹ ∈ V
      rw [e']
      exact inv_mem hz
  exact key ⟨u, hu⟩ huC

theorem exists_factor_of_mulEquiv {Γ A B : Type*} [Group Γ] [Group A] [Group B]
    {Z : Subgroup Γ} (hA : Nat.card A = 60) (ψ : ↥Z ≃* A × B) :
    ∃ V : Subgroup Γ, V ≤ Z ∧ Nonempty (↥V ≃* B) ∧ ∀ g ∈ Z, g ^ 7 = 1 → g ∈ V := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup ↥Z, ∀ x : ↥Z, x ∈ K ↔ (ψ x).1 = 1 :=
    ⟨((MonoidHom.fst A B).comp ψ.toMonoidHom).ker, fun x => MonoidHom.mem_ker⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_mem_iff ψ K hK
  obtain ⟨V, hV⟩ : ∃ V : Subgroup Γ, V = K.map Z.subtype := ⟨_, rfl⟩
  have eV : ↥V ≃* ↥K := by
    subst hV
    exact (K.equivMapOfInjective Z.subtype Z.subtype_injective).symm
  have hVZ : V ≤ Z := by
    rw [hV]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hVmem : ∀ x : ↥Z, x ∈ K → (x : Γ) ∈ V := by
    intro x hx
    rw [hV]
    exact Subgroup.mem_map_of_mem Z.subtype hx
  refine ⟨V, hVZ, ⟨eV.trans eK⟩, fun g hg h7 => ?_⟩
  have hx : (⟨g, hg⟩ : ↥Z) ^ 7 = 1 := Subtype.ext (by simpa using h7)
  have hψ : ψ ⟨g, hg⟩ ^ 7 = 1 := by rw [← map_pow, hx, map_one]
  exact hVmem ⟨g, hg⟩ ((hK _).mpr (fst_eq_one_of_pow_seven_eq_one hA hψ))

theorem mem_normalizer_of_pow_seven {Γ : Type*} [Group Γ] [Finite Γ] {Z V : Subgroup Γ}
    (hVZ : V ≤ Z) (hkey : ∀ g ∈ Z, g ^ 7 = 1 → g ∈ V)
    (htop : Subgroup.closure {x : V | x ^ 7 = 1} = ⊤) :
    ∀ a ∈ Subgroup.normalizer (Z : Set Γ), a ∈ Subgroup.normalizer (V : Set Γ) := by
  intro a ha
  refine CFSG.RankThree.PartTwo.Sec14.Item148HJ.mem_normalizer_of_conj_mem
    (conj_mem_of_closure_eq_top V a _ htop ?_)
  intro z hz
  have hz0 : z ^ 7 = 1 := hz
  have hz' : (z : Γ) ^ 7 = 1 := by
    simpa using congrArg (fun y : V => (y : Γ)) hz0
  have haZ : a * (z : Γ) * a⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp ha (z : Γ)).mp (hVZ z.2)
  apply hkey _ haZ
  rw [conj_pow, hz', mul_one, mul_inv_cancel]

theorem isSimpleGroup_of_mulEquiv_j2 {V : Type*} [Group V]
    (e : V ≃* CFSG.Blueprint.NativeSporadic.J2) : IsSimpleGroup V := by
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  exact MulEquiv.isSimpleGroup e

theorem seven_dvd_card_of_mulEquiv_j2 {V : Type*} [Group V]
    (e : V ≃* CFSG.Blueprint.NativeSporadic.J2) : 7 ∣ Nat.card V := by
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
  norm_num

theorem exists_j2_factor_le_normalizer {Γ : Type} [Group Γ]
    [Finite Γ] {Z : Subgroup Γ}
    (ψ : ↥Z ≃* alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) :
    ∃ V : Subgroup Γ, V ≤ Z ∧ Nonempty (↥V ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      ∀ a ∈ Subgroup.normalizer (Z : Set Γ), a ∈ Subgroup.normalizer (V : Set Γ) := by
  obtain ⟨V, hVZ, ⟨e⟩, hkey⟩ :=
    exists_factor_of_mulEquiv CFSG.RankThree.PartTwo.Sec14.Item148HJ.card_alternatingGroup_five ψ
  have hs : IsSimpleGroup ↥V := isSimpleGroup_of_mulEquiv_j2 e
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ⟨V, hVZ, ⟨e⟩, mem_normalizer_of_pow_seven hVZ hkey
    (closure_pow_eq_top (seven_dvd_card_of_mulEquiv_j2 e))⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
