module

public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1SolvAux

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

section NormalSylow

variable {Q : Type*} [Group Q] [Finite Q]

theorem le_of_isSylowIn_of_normal {R P M : Subgroup Q} (hP : IsSylowIn 2 P R)
    (hPn : (P.subgroupOf R).Normal) (hMR : M ≤ R) (hM2 : IsPGroup 2 M) : M ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnorm : R ≤ Subgroup.normalizer (P : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP.le).mp hPn
  obtain ⟨S, hS, hMS⟩ := exists_isSylowIn_ge 2 hMR hM2
  obtain ⟨r, hr, hrS⟩ := B6.isSylowTwoOf_exists_conj hP hS
  have : S = P := by
    rw [hrS]
    exact B6.conjSub_eq_self (hRnorm hr)
  exact this ▸ hMS

theorem normal_of_isSylowIn_of_normal {R P : Subgroup Q} [R.Normal] (hP : IsSylowIn 2 P R)
    (hPn : (P.subgroupOf R).Normal) : P.Normal := by
  have key : ∀ M : Subgroup Q, M ≤ R → IsPGroup 2 M → M ≤ P := fun M hMR hM2 =>
    le_of_isSylowIn_of_normal hP hPn hMR hM2
  refine ⟨fun x hx q => ?_⟩
  have hqR : conjSub q P ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance y (hP.le hy) q
  have h2 : IsPGroup 2 (conjSub q P) :=
    hP.isPGroup.of_equiv (Subgroup.equivMapOfInjective P (MulAut.conj q).toMonoidHom
      (MulAut.conj q).injective)
  exact key _ hqR h2 (mem_conjSub_of_mem hx)

end NormalSylow

section Radical

variable {Q Q' : Type*} [Group Q] [Group Q'] [Finite Q] [Finite Q'] (φ : Q →* Q')

theorem solvableRadical_eq_comap (hφ : Function.Surjective φ) (hker : Group.IsSolvable φ.ker) :
    CFSG.solvableRadical Q = (CFSG.solvableRadical Q').comap φ := by
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.map_le_iff_le_comap]
    refine A3.le_solvableRadical (Subgroup.Normal.map inferInstance φ hφ) ?_
    have : Group.IsSolvable (CFSG.solvableRadical Q) := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective _)
  · refine A3.le_solvableRadical (Subgroup.normal_comap φ) ?_
    set R' := CFSG.solvableRadical Q' with hR'
    have hR's : Group.IsSolvable R' := A3.solvableRadical_isSolvable
    let g : ↥(R'.comap φ) →* ↥R' := (φ.comp (R'.comap φ).subtype).codRestrict R' (fun p => p.2)
    have hle : φ.ker ≤ R'.comap φ := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact R'.one_mem
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g (fun p hp => ?_)
    have h1 : φ p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
    exact ⟨⟨(p : Q), MonoidHom.mem_ker.mpr h1⟩, rfl⟩

theorem exists_quotRadEquiv (hφ : Function.Surjective φ) (hker : Group.IsSolvable φ.ker) :
    ∃ ψ : (Q ⧸ CFSG.solvableRadical Q) ≃* (Q' ⧸ CFSG.solvableRadical Q'),
      ∀ x : Q, ψ (QuotientGroup.mk' (CFSG.solvableRadical Q) x) =
        QuotientGroup.mk' (CFSG.solvableRadical Q') (φ x) := by
  have hR := solvableRadical_eq_comap φ hφ hker
  let ψ₀ : (Q ⧸ CFSG.solvableRadical Q) →* (Q' ⧸ CFSG.solvableRadical Q') :=
    QuotientGroup.map _ _ φ hR.le
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    induction y using QuotientGroup.induction_on with
    | H x =>
      have h1 : ((φ x : Q') : Q' ⧸ CFSG.solvableRadical Q') = 1 := hy
      have hx : φ x ∈ CFSG.solvableRadical Q' := (QuotientGroup.eq_one_iff _).mp h1
      have : x ∈ CFSG.solvableRadical Q := by
        rw [hR]
        exact hx
      exact (QuotientGroup.eq_one_iff x).mpr this
  have hsurj : Function.Surjective ψ₀ := by
    intro y'
    induction y' using QuotientGroup.induction_on with
    | H x' =>
      obtain ⟨x, rfl⟩ := hφ x'
      exact ⟨x, rfl⟩
  exact ⟨MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩, fun x => rfl⟩

theorem oInftyE_eq_comap (hφ : Function.Surjective φ) (hker : Group.IsSolvable φ.ker) :
    oInftyE Q = (oInftyE Q').comap φ := by
  obtain ⟨ψ, hψ⟩ := exists_quotRadEquiv φ hφ hker
  have hlayer := layer_map_mulEquiv ψ
  ext x
  unfold oInftyE
  simp only [Subgroup.mem_comap]
  rw [← hψ x, ← hlayer]
  exact (Subgroup.mem_map_iff_mem ψ.injective).symm

end Radical

section TwoClosed

variable {Q Q' : Type*} [Group Q] [Group Q'] [Finite Q] [Finite Q']

theorem pCore_two_quotient_eq_top_iff (N : Subgroup Q) [N.Normal] :
    CFSG.Open.pCore 2 (Q ⧸ N) = ⊤ ↔ ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h x
    have hx : (x : Q ⧸ N) ∈ CFSG.Open.pCore 2 (Q ⧸ N) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2) ⟨_, hx⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    simpa using congrArg Subtype.val hk
  · intro h
    have h2g : IsPGroup 2 (⊤ : Subgroup (Q ⧸ N)) := by
      intro y
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (y : Q ⧸ N)
      obtain ⟨k, hk⟩ := h q
      refine ⟨k, Subtype.ext ?_⟩
      show (y : Q ⧸ N) ^ 2 ^ k = 1
      rw [← hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
    have hle := CFSG.LieType.BorelTits.le_pCore 2 inferInstance h2g
    exact eq_top_iff.mpr fun x _ => hle (Subgroup.mem_top _)

variable (φ : Q →* Q')

omit [Finite Q'] in
theorem isSolvable_ker_of_isTwoClosed (hZ : IsTwoClosed ((CFSG.Open.pCore 2 Q').comap φ)) :
    Group.IsSolvable φ.ker := by
  have hsolv := isSolvable_of_isTwoClosed hZ
  have hle : φ.ker ≤ (CFSG.Open.pCore 2 Q').comap φ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem isTwoClosed_solvableRadical (hφ : Function.Surjective φ)
    (hZ : IsTwoClosed ((CFSG.Open.pCore 2 Q').comap φ))
    (hR' : IsTwoClosed (CFSG.solvableRadical Q')) : IsTwoClosed (CFSG.solvableRadical Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := isSolvable_ker_of_isTwoClosed φ hZ
  have hRc := solvableRadical_eq_comap φ hφ hker
  set R' := CFSG.solvableRadical Q' with hR'def
  set O' := CFSG.Open.pCore 2 Q' with hO'
  set R := CFSG.solvableRadical Q with hRdef
  have hZn : ((CFSG.Open.pCore 2 Q').comap φ).Normal := Subgroup.normal_comap φ
  obtain ⟨PZ, hPZ, hPZn⟩ := hZ
  have hPZnorm : PZ.Normal := normal_of_isSylowIn_of_normal hPZ hPZn
  obtain ⟨P', hP', hP'n⟩ := hR'
  have hP'norm : P'.Normal := normal_of_isSylowIn_of_normal hP' hP'n
  have hO'R' : O' ≤ R' :=
    A3.le_solvableRadical inferInstance
      (isSolvable_of_isPGroup_two (CFSG.LieType.BorelTits.pCore_isPGroup 2))
  have hO'P' : O' ≤ P' :=
    hP'.le_of_normal hO'R' ((Subgroup.normal_subgroupOf_iff_le_normalizer hO'R').mpr
      (by
        intro x _
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top x)) (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have hP'O' : P' ≤ O' := CFSG.LieType.BorelTits.le_pCore 2 hP'norm hP'.isPGroup
  have hO'eq : O' = P' := le_antisymm hO'P' hP'O'
  have hZR : (O'.comap φ) ≤ R := by
    rw [hRc]
    exact Subgroup.comap_mono hO'R'
  refine ⟨PZ, ⟨hPZ.le.trans hZR, hPZ.isPGroup, ?_⟩, hPZnorm.subgroupOf R⟩
  have h1 : PZ.relIndex (O'.comap φ) * (O'.comap φ).relIndex R = PZ.relIndex R :=
    Subgroup.relIndex_mul_relIndex PZ _ R hPZ.le hZR
  have h2 : (O'.comap φ).relIndex R = O'.relIndex R' := by
    rw [Subgroup.relIndex_comap, hRc, Subgroup.map_comap_eq_self_of_surjective hφ]
  intro hdvd
  rw [← h1] at hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hPZ.not_dvd_relIndex h
  · rw [h2, hO'eq] at h
    exact hP'.not_dvd_relIndex h

end TwoClosed

section ETwoLift

variable {Q Q' : Type*} [Group Q] [Group Q'] [Finite Q] [Finite Q'] (φ : Q →* Q')

omit [Finite Q'] in
theorem tauOf_top_map_eq_of_isTwoClosed (hφ : Function.Surjective φ)
    (hZ : IsTwoClosed ((CFSG.Open.pCore 2 Q').comap φ)) {S B : Subgroup Q} (hS : IsPGroup 2 S)
    (hBS : B ≤ S) : (tauOf ⊤ S B).map φ = tauOf ⊤ (S.map φ) (B.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormQ : ∀ x : Q, x ∈ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup Q) : Set Q) := fun x => by
    rw [pCoreOf_top_eq, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top x
  have hnormQ' : ∀ x : Q', x ∈ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup Q') : Set Q') :=
    fun x => by
    rw [pCoreOf_top_eq, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top x
  ext t'
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem φ ht.1, hnormQ' _, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have h1 := ht.2.2 b hb
    have h2 := map_pCoreOf_le φ ⊤ (Subgroup.mem_map_of_mem φ h1)
    rw [Subgroup.map_top_of_surjective φ hφ] at h2
    simpa [map_commutatorElement] using h2
  · rintro ⟨hS', -, hc'⟩
    obtain ⟨t, htS, rfl⟩ := hS'
    refine ⟨t, ⟨htS, hnormQ t, fun b hb => ?_⟩, rfl⟩
    have h1 : φ ⁅t, b⁆ ∈ pCoreOf 2 (⊤ : Subgroup Q') := by
      simpa [map_commutatorElement] using hc' (φ b) (Subgroup.mem_map_of_mem φ hb)
    rw [pCoreOf_top_eq] at h1
    rw [pCoreOf_top_eq]
    obtain ⟨PZ, hPZ, hPZn⟩ := hZ
    have hZn : ((CFSG.Open.pCore 2 Q').comap φ).Normal := Subgroup.normal_comap φ
    have hPZnorm : PZ.Normal := normal_of_isSylowIn_of_normal hPZ hPZn
    have hcS : ⁅t, b⁆ ∈ S := by
      have e : ⁅t, b⁆ = t * b * t⁻¹ * b⁻¹ := rfl
      rw [e]
      exact S.mul_mem (S.mul_mem (S.mul_mem htS (hBS hb)) (S.inv_mem htS)) (S.inv_mem (hBS hb))
    have hcZ : ⁅t, b⁆ ∈ (CFSG.Open.pCore 2 Q').comap φ := h1
    have hle : S ⊓ (CFSG.Open.pCore 2 Q').comap φ ≤ PZ :=
      le_of_isSylowIn_of_normal hPZ hPZn inf_le_right (hS.to_le inf_le_left)
    exact CFSG.LieType.BorelTits.le_pCore 2 hPZnorm hPZ.isPGroup (hle ⟨hcS, hcZ⟩)

theorem card_barRad_eq_of_surjective (hφ : Function.Surjective φ)
    (hker : Group.IsSolvable φ.ker) (B : Subgroup Q) :
    Nat.card (barRad Q' (B.map φ)) = Nat.card (barRad Q B) := by
  obtain ⟨ψ, hψ⟩ := exists_quotRadEquiv φ hφ hker
  have h : (barRad Q B).map ψ.toMonoidHom = barRad Q' (B.map φ) := by
    unfold barRad
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hψ x
  rw [← h]
  exact Subgroup.card_map_of_injective ψ.injective

theorem eTwo_of_surjective (hφ : Function.Surjective φ)
    (hZ : IsTwoClosed ((CFSG.Open.pCore 2 Q').comap φ)) {S B : Subgroup Q} (hS : IsPGroup 2 S)
    (hBS : B ≤ S) (hres : twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q))
    (h : ETwo Q' (S.map φ) (B.map φ)) : ETwo Q S B := by
  have hker := isSolvable_ker_of_isTwoClosed φ hZ
  obtain ⟨hR', h2, -, h4⟩ := h
  refine ⟨isTwoClosed_solvableRadical φ hφ hZ hR', ?_, hres, ?_⟩
  · rw [pCore_two_quotient_eq_top_iff] at h2 ⊢
    intro x
    obtain ⟨k, hk⟩ := h2 (φ x)
    refine ⟨k, ?_⟩
    rw [oInftyE_eq_comap φ hφ hker, Subgroup.mem_comap, map_pow]
    exact hk
  · obtain ⟨ψ, hψ⟩ := exists_quotRadEquiv φ hφ hker
    have htau := tauOf_top_map_eq_of_isTwoClosed φ hφ hZ hS hBS
    have hτ : ((tauOf ⊤ S B).map (QuotientGroup.mk' (CFSG.solvableRadical Q))).map
        ψ.toMonoidHom =
        (tauOf ⊤ (S.map φ) (B.map φ)).map (QuotientGroup.mk' (CFSG.solvableRadical Q')) := by
      rw [Subgroup.map_map, ← htau, Subgroup.map_map]
      congr 1
      ext x
      exact hψ x
    have hbar : (barRad Q B).map ψ.toMonoidHom = barRad Q' (B.map φ) := by
      unfold barRad
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      exact hψ x
    refine (exists_subgroup_congr ψ fun L => ?_).mpr h4
    refine and_congr ((CFSG.LocalCores.component_isomorphism ψ).1 L) (and_congr ?_ ?_)
    · rw [← map_inj_mulEquiv ψ, layer_map_mulEquiv, map_biSup_conjSub, hτ]
    · rw [card_barRad_eq_of_surjective φ hφ hker, ← hbar, ← Subgroup.map_commutator,
        map_inj_mulEquiv, ← Subgroup.map_equiv_normalizer_eq, map_le_map_iff_mulEquiv]

theorem twoResidual_eq_perfectCore_of_surjective (hφ : Function.Surjective φ) {S : Subgroup Q}
    (hS : IsSylowIn 2 S ⊤)
    (hmin : ∀ M : Subgroup Q, S ≤ M → M ⊔ φ.ker = ⊤ → M = ⊤)
    (h' : twoResidual (⊤ : Subgroup Q') = perfectCore (⊤ : Subgroup Q')) :
    twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := perfectCore (⊤ : Subgroup Q) with hP
  have hnormP : ⊤ ≤ Subgroup.normalizer (P : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le ⊤)).mp (perfectCore_normal ⊤)
  have hSb : IsSylowIn 2 (S.map φ) ⊤ := isSylowIn_two_map_top hφ hS
  have hker1 : φ.ker.map φ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hPmap : P.map φ = twoResidual (⊤ : Subgroup Q') := by
    rw [h', hP, map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
  have hfull : (P ⊔ S) ⊔ φ.ker = ⊤ := by
    have h1 : ((P ⊔ S) ⊔ φ.ker).map φ = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_sup, hker1, sup_bot_eq, hPmap]
      exact top_le_iff.mp (le_twoResidual_sup_of_isSylowIn hSb)
    have h2 := Subgroup.comap_map_eq φ ((P ⊔ S) ⊔ φ.ker)
    rw [h1, Subgroup.comap_top, sup_assoc, sup_idem] at h2
    exact h2.symm
  have hM : P ⊔ S = ⊤ := hmin _ le_sup_right hfull
  apply le_antisymm
  · refine twoResidual_le_of_isTwoQuotient le_top hnormP fun y _ => ?_
    have hy : y ∈ P ⊔ S := by
      rw [hM]
      exact Subgroup.mem_top y
    exact exists_pow_mem_of_mem_sup hS.isPGroup (fun s _ => hnormP (Subgroup.mem_top s)) hy
  · have hsolv : Group.IsSolvable S := isSolvable_of_isPGroup_two hS.isPGroup
    refine perfectCore_le_of_sup_solvable (A := twoResidual (⊤ : Subgroup Q)) (B := S)
      (Y := ⊤) le_top ?_ ?_ hsolv
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
        (le_normalizer_twoResidual ⊤)
    · exact (top_le_iff.mp (le_twoResidual_sup_of_isSylowIn hS)).symm

end ETwoLift

end E1

end CFSG.Quasithin
