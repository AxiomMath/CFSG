module

public import CFSG.Quasithin.Background.E1SolvAux
public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

universe u

section ETwo

theorem not_isSolvable_of_isComponent {P : Type*} [Group P] {L : Subgroup P}
    (hL : CFSG.IsComponent L) : ¬ Group.IsSolvable L := by
  intro hsolv
  obtain ⟨⟨hperf, -, a, b, hab⟩, -⟩ := hL
  have hnt : Nontrivial L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
    exact hab (Subsingleton.elim _ _)
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L)
  rw [hperf.commutator_eq_top] at h1
  exact lt_irrefl _ h1

theorem not_eTwo_of_isSolvable {Q : Type*} [Group Q] {S B : Subgroup Q}
    (hQ : Group.IsSolvable Q) : ¬ ETwo Q S B := by
  rintro ⟨-, -, -, L, hL, -⟩
  have h1 : Group.IsSolvable (Q ⧸ solvableRadical Q) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have h2 : Group.IsSolvable L := inferInstance
  exact not_isSolvable_of_isComponent hL h2

theorem isE_eOne_of_isSolvable {Q : Type*} [Group Q] {i : ℕ} {H T A K : Subgroup Q}
    (h : IsE i H T A K) (hK : Group.IsSolvable K) :
    EOne ↥K (A.subgroupOf K) ∧ Nat.card (barO2 ↥K (A.subgroupOf K)) ≤ 2 ^ i := by
  rcases h.2.2.2 with h' | ⟨h', -⟩
  · exact h'
  · exact absurd h' (not_eTwo_of_isSolvable hK)

end ETwo

section NormalSubgroup

variable {Q : Type*} [Group Q] [Finite Q]

theorem normal_pGroup_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T N M : Subgroup Q} [N.Normal]
    (hT : IsSylowIn 2 T ⊤) (hN : IsPGroup p N) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω)
    (hM1 : eGen 1 ⊤ T Ω ≤ M) (hM2 : Subgroup.normalizer (weakClosure T Ω : Set Q) ≤ M) :
    N ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  set W := weakClosure T Ω with hW
  have hTM : T ≤ M := (le_normalizer_weakClosure hΩ).trans hM2
  have hNnorm : ∀ g : Q, g ∈ Subgroup.normalizer (N : Set Q) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hAM : ∀ A ∈ Ω, A ≤ T → ⁅N, A⁆ ≤ N ⊓ M := by
    intro A hA hAT
    refine le_inf ?_ ?_
    · refine Subgroup.commutator_le.mpr fun n hn a ha => ?_
      have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n⁻¹ (N.inv_mem hn) a)
    · refine (comm_le_iSup_twoResidual hp hp2 hT hAT (hΩ.isElemAbelian A hA) hN).trans ?_
      refine iSup₂_le fun K hK => (twoResidual_le K).trans ?_
      exact (le_eGen hA hAT hK.1).trans hM1
  have hN₁ : T ≤ Subgroup.normalizer ((N ⊓ M : Subgroup Q) : Set Q) := fun t ht =>
    mem_normalizer_inf (hNnorm t) (Subgroup.le_normalizer (hTM ht))
  have hcomm : ⁅N, W⁆ ≤ N ⊓ M := commutator_weakClosure_le hN₁ hAM
  have hWN : W ≤ Subgroup.normalizer (N : Set Q) := fun w _ => hNnorm w
  have hW2 : IsPGroup 2 W := hT.isPGroup.to_le weakClosure_le
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  have hNsolv : Group.IsSolvable N := by
    have := hN.isNilpotent
    infer_instance
  have hfac := comm_sup_inf_centralizer_eq hWN hW2 hcop hNsolv
  rw [← hfac]
  refine sup_le (hcomm.trans inf_le_right) ?_
  intro x hx
  apply hM2
  apply mem_normalizer_of_conj_mem
  intro w hw
  have hxw : w * x = x * w := Subgroup.mem_centralizer_iff.mp hx.2 w hw
  have e : x * w * x⁻¹ = w := by
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [hxw]
      _ = w := by group
  rw [e]
  exact hw

end NormalSubgroup

section Induction

variable {Q : Type u} [Group Q] [Finite Q]

theorem inEFor_one_of_quotient (hQ : Group.IsSolvable Q) {N : Subgroup Q} [N.Normal] {r : ℕ}
    (hr : r.Prime) (hN : IsPGroup r N) (hIH : InE 1 (⊤ : Subgroup (Q ⧸ N)))
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  intro Ω hΩ
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set W := weakClosure T Ω with hW
  set M : Subgroup Q := eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (W : Set Q)) with hM
  have hM1 : eGen 1 ⊤ T Ω ≤ M := le_sup_left
  have hM2 : Subgroup.normalizer (W : Set Q) ≤ M := fun x hx =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩
  have hTM : T ≤ M := (le_normalizer_weakClosure hΩ).trans hM2
  have hTb : IsSylowIn 2 (T.map π) ⊤ := isSylowIn_two_map_top hπs hT
  have hΩb : IsInvColl ⊤ (Subgroup.map π '' Ω) := isInvColl_map_of_surjective π hπs hΩ
  have hIHT := hIH _ hTb _ hΩb
  have hQb : Group.IsSolvable (Q ⧸ N) := Group.isSolvable_of_surjective hπs
  have hMπ : ⊤ ≤ M.map π := by
    refine hIHT.symm.trans_le (sup_le ?_ ?_)
    ·
      refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => ?_
      obtain ⟨A₀, hA₀, rfl⟩ := hB
      obtain ⟨n, hn, hnA⟩ := exists_mem_conj_le_of_map_le hT
        (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A₀ hA₀)) hBT
      have hAΩ : conjSub n A₀ ∈ Ω := hΩ.conj A₀ hA₀ n (Subgroup.mem_top n)
      have hAT : conjSub n A₀ ≤ T := by
        intro y hy
        rw [mem_conjSub_iff] at hy
        have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
        have := hnA _ hy
        rwa [e] at this
      have hAeq : (conjSub n A₀).map π = A₀.map π := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have hy' : y ∈ conjSub n A₀ := hy
          rw [mem_conjSub_iff] at hy'
          refine ⟨n⁻¹ * y * n, hy', ?_⟩
          have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
          simp [hπn]
        · rintro _ ⟨a, ha, rfl⟩
          refine ⟨n * a * n⁻¹, mem_conjSub_of_mem ha, ?_⟩
          have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
          simp [hπn]
      have hK' : IsE 1 ⊤ (T.map π) ((conjSub n A₀).map π) K := by
        rw [hAeq]
        exact hK
      have hKsolv : Group.IsSolvable K := inferInstance
      obtain ⟨J, hJ, hJK⟩ := ten_seven_eOne hT hAT (hΩ.isElemAbelian _ hAΩ) hK'
        (isE_eOne_of_isSolvable hK' hKsolv)
      have hJM : J ≤ M := (le_eGen hAΩ hAT hJ).trans hM1
      calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := le_twoResidual_sup_of_isSylowIn hK.2.2.1
        _ ≤ (twoResidual J).map π ⊔ T.map π := by
          rw [hJK]
          exact sup_le_sup le_rfl inf_le_left
        _ ≤ M.map π := sup_le (Subgroup.map_mono ((twoResidual_le J).trans hJM))
          (Subgroup.map_mono hTM)
    ·
      intro x hx
      rw [weakClosure_map_quotient hT hΩ] at hx
      obtain ⟨g, rfl⟩ := hπs x
      obtain ⟨g', hg', hg'x⟩ := exists_mem_normalizer_of_mem_normalizer_map hT hΩ hx.2
      exact ⟨g', hM2 hg', hg'x⟩
  have hNM : N ≤ M := by
    by_cases hr2 : r = 2
    · subst hr2
      have : Fact (Nat.Prime 2) := ⟨hr⟩
      exact (hT.le_of_normal le_top inferInstance hN).trans hTM
    · exact normal_pGroup_le hr hr2 hT hN hΩ hM1 hM2
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨m, hm, hmq⟩ := hMπ (Subgroup.mem_top (π q))
  have h1 : m⁻¹ * q ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
    change (π m)⁻¹ * π q = 1
    rw [hmq]
    exact inv_mul_cancel _
  have e : q = m * (m⁻¹ * q) := by group
  rw [e]
  exact M.mul_mem hm (hNM h1)

theorem inE_one_top_of_isSolvable :
    ∀ (n : ℕ) (Q : Type u) [Group Q] [Finite Q], Nat.card Q ≤ n → Group.IsSolvable Q →
      InE 1 (⊤ : Subgroup Q) := by
  intro n
  induction n with
  | zero =>
    intro Q _ _ h
    exact absurd h (by have := Nat.card_pos (α := Q); omega)
  | succ n ih =>
    intro Q _ _ hn hQ
    by_cases hsub : Subsingleton Q
    · refine inE_of_odd ?_
      rw [Subgroup.card_top]
      have : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      rw [this]
      exact odd_one
    · have hnt : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
      have htop : (⊤ : Subgroup Q) ≠ ⊥ := Ne.symm bot_ne_top
      obtain ⟨N, hNn, -, hNbot, hNmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
      have : N.Normal := hNn
      have hIM : CFSG.IsMinimalNormal N := ⟨fun K _ hKN => by
        by_cases hK : K = ⊥
        · exact Or.inl hK
        · exact Or.inr (hNmin K ‹_› hKN hK)⟩
      have hNs : Group.IsSolvable N := inferInstance
      obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
      have hNp : IsPGroup r N := CFSG.IsElementaryAbelian.isPGroup r N
      have hQN : Nat.card (Q ⧸ N) ≤ n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot
        have h3 := Nat.card_pos (α := Q ⧸ N)
        nlinarith
      have hIH := ih (Q ⧸ N) hQN
        (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N))
      intro T hT
      exact inEFor_one_of_quotient hQ hr hNp hIH hT

end Induction

theorem solvable_nParam_le_one {G : Type u} [Group G] [Finite G] {H : Subgroup G}
    (hH : Group.IsSolvable ↥H) : nParam H ≤ 1 := by
  have h := inE_one_top_of_isSolvable (Nat.card H) ↥H le_rfl hH
  have := (nParam_le_iff (H := H) (n := 1) Nat.one_pos).mpr ((inE_subgroupOf 1 H).mpr h)
  simpa using this

end E1

end CFSG.Quasithin
