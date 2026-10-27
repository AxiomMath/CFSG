module

public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

universe u

variable {Q : Type u} [Group Q] [Finite Q]

theorem le_normalizer_eGen (i : ℕ) {T : Subgroup Q} {Ω : Set (Subgroup Q)}
    (hΩ : IsInvColl ⊤ Ω) : T ≤ Subgroup.normalizer (eGen i ⊤ T Ω : Set Q) := by
  intro t ht
  rw [← conjSub_eq_iff_mem_normalizer]
  have hT' : conjSub t T = T := conjSub_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer ht)
  have htop : conjSub t (⊤ : Subgroup Q) = ⊤ :=
    conjSub_eq_iff_mem_normalizer.2 (by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top t)
  have h := eGen_conj i t ⊤ T (fun A hA => hΩ.conj A hA t (Subgroup.mem_top t))
    (fun A hA => hΩ.conj A hA t⁻¹ (Subgroup.mem_top t⁻¹))
  rw [htop, hT'] at h
  exact h.symm

theorem eGen_map_le_eGen_sup_map {N T : Subgroup Q} [N.Normal] (hQ : Group.IsSolvable Q)
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω) :
    eGen 1 ⊤ (T.map (QuotientGroup.mk' N)) (Subgroup.map (QuotientGroup.mk' N) '' Ω) ≤
      (eGen 1 ⊤ T Ω ⊔ T).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
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
    rw [hAeq]; exact hK
  haveI : Group.IsSolvable (Q ⧸ N) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  have hKsolv : Group.IsSolvable K := inferInstance
  obtain ⟨J, hJ, hJK⟩ := ten_seven_eOne hT hAT (hΩ.isElemAbelian _ hAΩ) hK'
    (isE_eOne_of_isSolvable hK' hKsolv)
  calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) := le_twoResidual_sup_of_isSylowIn hK.2.2.1
    _ ≤ (twoResidual J).map π ⊔ T.map π := by
        rw [hJK]
        exact sup_le_sup le_rfl inf_le_left
    _ ≤ (eGen 1 ⊤ T Ω ⊔ T).map π := by
        refine sup_le ?_ ?_
        · exact (Subgroup.map_mono ((twoResidual_le J).trans (le_eGen hAΩ hAT hJ))).trans
            (Subgroup.map_mono le_sup_left)
        · exact Subgroup.map_mono le_sup_right

theorem commutator_le_eGen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T N : Subgroup Q} [N.Normal]
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω)
    (hN : IsPGroup p N) : ⁅N, weakClosure T Ω⁆ ≤ eGen 1 ⊤ T Ω := by
  refine commutator_weakClosure_le (le_normalizer_eGen 1 hΩ) ?_
  intro A hA hAT
  refine (comm_le_iSup_twoResidual hp hp2 hT hAT (hΩ.isElemAbelian A hA) hN).trans ?_
  refine iSup₂_le fun K hK => (twoResidual_le K).trans (le_eGen hA hAT hK.1)

theorem eGen_mul_normalizer_of_solvable_aux :
    ∀ (n : ℕ) (Q : Type u) [Group Q] [Finite Q], Nat.card Q ≤ n → Group.IsSolvable Q →
      ∀ (T : Subgroup Q), IsSylowIn 2 T ⊤ → ∀ (Ω : Set (Subgroup Q)), IsInvColl ⊤ Ω →
        ∀ g : Q, ∃ e ∈ eGen 1 ⊤ T Ω,
          ∃ n ∈ Subgroup.normalizer (weakClosure T Ω : Set Q), g = e * n := by
  intro n
  induction n with
  | zero =>
    intro Q _ _ h
    exact absurd h (by have := Nat.card_pos (α := Q); omega)
  | succ n ih =>
    intro Q _ _ hn hQ
    by_cases hsub : Subsingleton Q
    · intro T hT Ω hΩ g
      have hg : g = 1 := Subsingleton.elim g 1
      exact ⟨1, (eGen 1 ⊤ T Ω).one_mem, 1, (Subgroup.normalizer _).one_mem, by rw [hg, one_mul]⟩
    · have hnt : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
      have htop : (⊤ : Subgroup Q) ≠ ⊥ := Ne.symm bot_ne_top
      obtain ⟨R, hRn, -, hRbot, hRmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
      haveI : R.Normal := hRn
      have hIM : CFSG.IsMinimalNormal R := ⟨fun K _ hKN => by
        by_cases hK : K = ⊥
        · exact Or.inl hK
        · exact Or.inr (hRmin K ‹_› hKN hK)⟩
      have hRsolv : Group.IsSolvable R := inferInstance
      obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian R
      have hRp : IsPGroup r R := CFSG.IsElementaryAbelian.isPGroup r R
      have hQN : Nat.card (Q ⧸ R) ≤ n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R
        have h2 : 1 < Nat.card R := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRbot
        have h3 := Nat.card_pos (α := Q ⧸ R)
        nlinarith
      have hIH := ih (Q ⧸ R) hQN
        (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective R))
      intro T hT Ω hΩ g
      set π := QuotientGroup.mk' R with hπ
      have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
      set Tbar : Subgroup (Q ⧸ R) := T.map π with hTbar
      set Ωbar : Set (Subgroup (Q ⧸ R)) := Subgroup.map π '' Ω with hΩbar
      have hTbar' : IsSylowIn 2 Tbar ⊤ := isSylowIn_two_map_top hπs hT
      have hΩbar' : IsInvColl ⊤ Ωbar := isInvColl_map_of_surjective π hπs hΩ
      set E : Subgroup Q := eGen 1 ⊤ T Ω with hE
      set W : Subgroup Q := weakClosure T Ω with hW
      set Nrm : Subgroup Q := Subgroup.normalizer (W : Set Q) with hNrm
      have hTN : T ≤ Nrm := le_normalizer_weakClosure hΩ
      have hTE : T ≤ Subgroup.normalizer (E : Set Q) := le_normalizer_eGen 1 hΩ
      have hRsub : (R : Set Q) ⊆ (E : Set Q) * (Nrm : Set Q) := by
        intro ρ hρ
        by_cases hr2 : r = 2
        · have hR2 : IsPGroup 2 R := hr2 ▸ hRp
          have hRT : R ≤ T := hT.le_of_normal le_top inferInstance hR2
          exact ⟨1, E.one_mem, ρ, hTN (hRT hρ), one_mul ρ⟩
        · haveI : Fact r.Prime := ⟨hr⟩
          have hRodd : Nat.Coprime 2 (Nat.card R) := by
            obtain ⟨k, hk⟩ := hRp.exists_card_eq
            rw [hk]
            exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hr).mpr (by omega))
          have hWR : W ≤ Subgroup.normalizer (R : Set Q) := fun w _ => by
            rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
            exact Subgroup.mem_top w
          have hW2 : IsPGroup 2 W := hT.isPGroup.to_le weakClosure_le
          have hcomm : ⁅R, W⁆ ≤ E := commutator_le_eGen hr (by omega) hT hΩ hRp
          have hRfac := comm_sup_inf_centralizer_eq hWR hW2 hRodd hRsolv
          have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
            congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
          have hcommRW_le_R : ⁅R, W⁆ ≤ R := by
            refine Subgroup.commutator_le.mpr fun r hr w _ => ?_
            have e : ⁅r, w⁆ = r * (w * r⁻¹ * w⁻¹) := by
              simp only [commutatorElement_def]; group
            rw [e]
            exact R.mul_mem hr (hRn.conj_mem r⁻¹ (R.inv_mem hr) w)
          have hRc : R ≤ Subgroup.centralizer (R : Set Q) := fun x hx =>
            Subgroup.mem_centralizer_iff.2 (fun y hy => (hcommR x hx y hy).symm)
          have hnorm : R ⊓ Subgroup.centralizer (W : Set Q) ≤
              Subgroup.normalizer ((⁅R, W⁆ : Subgroup Q) : Set Q) :=
            ((inf_le_left.trans hRc).trans (Subgroup.centralizer_le hcommRW_le_R)).trans
              (Subgroup.centralizer_le_normalizer ((⁅R, W⁆ : Subgroup Q) : Set Q))
          have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left ⁅R, W⁆
            (R ⊓ Subgroup.centralizer (W : Set Q)) hnorm
          rw [hRfac] at hcoe
          have hmem : ρ ∈ (⁅R, W⁆ : Subgroup Q) *
              ((R ⊓ Subgroup.centralizer (W : Set Q)) : Set Q) := hcoe ▸ hρ
          rw [Set.mem_mul] at hmem
          obtain ⟨h, hh, k, hk, hkρ⟩ := hmem
          exact ⟨h, hcomm hh, k, Subgroup.centralizer_le_normalizer (W : Set Q) hk.2, hkρ⟩
      obtain ⟨ebar, hebar, nbar, hnbar, hgn⟩ := hIH Tbar hTbar' Ωbar hΩbar' (π g)
      have hgen_le := eGen_map_le_eGen_sup_map (N := R) hQ hT hΩ
      obtain ⟨m, hm, hmeb⟩ := hgen_le hebar
      have hEsup : (↑(E ⊔ T) : Set Q) = (E : Set Q) * (T : Set Q) :=
        Subgroup.coe_mul_of_right_le_normalizer_left E T hTE
      have hm' : m ∈ (E : Set Q) * (T : Set Q) := hEsup ▸ hm
      rw [Set.mem_mul] at hm'
      obtain ⟨e, he, t, ht, het⟩ := hm'
      have hnbar' : nbar ∈ Subgroup.normalizer (W.map π : Set (Q ⧸ R)) := by
        rw [← weakClosure_map_quotient hT hΩ]
        exact hnbar
      obtain ⟨gn, hgn'⟩ := hπs nbar
      obtain ⟨nn, hnn, hnnbar⟩ := exists_mem_normalizer_of_mem_normalizer_map hT hΩ
        (g := gn) (by rw [hgn']; exact hnbar')
      have hπeq : π (e * t * nn) = π g := by
        have h1 : π (e * t) = ebar := by rw [het, hmeb]
        rw [map_mul, h1, hnnbar, hgn']
        exact hgn.symm
      set ρ : Q := g * (e * t * nn)⁻¹ with hρdef
      have hρ : ρ ∈ R := by
        rw [hρdef, ← QuotientGroup.ker_mk' R, MonoidHom.mem_ker, map_mul, map_inv, hπeq]
        exact mul_inv_cancel _
      have hρ₁ : e⁻¹ * ρ * e ∈ R := by simpa using hRn.conj_mem ρ hρ e⁻¹
      obtain ⟨e₃, he₃, n₃, hn₃, he₃n₃⟩ := by
        have := hRsub hρ₁
        rw [Set.mem_mul] at this
        exact this
      refine ⟨e * e₃, E.mul_mem he he₃, n₃ * t * nn,
        Nrm.mul_mem (Nrm.mul_mem hn₃ (hTN ht)) hnn, ?_⟩
      have hkey : g = (e * e₃) * (n₃ * t * nn) := by
        have h1 : (e * e₃) * (n₃ * t * nn) = e * (e₃ * n₃) * t * nn := by group
        rw [h1, he₃n₃, hρdef]
        group
      exact hkey

theorem eGen_mul_normalizer_of_isSolvable (hQ : Group.IsSolvable Q) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsInvColl ⊤ Ω) (g : Q) :
    ∃ e ∈ eGen 1 ⊤ T Ω,
      ∃ n ∈ Subgroup.normalizer (weakClosure T Ω : Set Q), g = e * n :=
  eGen_mul_normalizer_of_solvable_aux (Nat.card Q) Q le_rfl hQ T hT Ω hΩ g

private theorem isElemAbelian_of_map_injective' {G' : Type*} [Group G'] {p : ℕ} {f : Q →* G'}
    (hf : Function.Injective f) {A : Subgroup Q} (h : IsElemAbelian p (A.map f)) :
    IsElemAbelian p A := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := commute_of_isElemAbelian h (Subgroup.mem_map_of_mem f x.2)
      (Subgroup.mem_map_of_mem f y.2)
    exact hf (by simpa [map_mul] using this)
  · exact hf (by simpa [map_pow] using h.2 (f x) (Subgroup.mem_map_of_mem f hx))

theorem eGen_mul_normalizer_of_isSolvable_subgroup {K T : Subgroup Q} (hTK : T ≤ K)
    (hQ : Group.IsSolvable ↥K) (hT : IsSylowIn 2 T K) {Ω : Set (Subgroup Q)}
    (hΩ : IsInvColl K Ω) (g : ↥K) :
    ∃ e ∈ eGen 1 K T Ω,
      ∃ n ∈ Subgroup.normalizer (weakClosure T Ω : Set Q) ⊓ K, (g : Q) = e * n := by
  set Ω' : Set (Subgroup ↥K) := {A' : Subgroup ↥K | A'.map K.subtype ∈ Ω}
  have hT' : IsSylowIn 2 (T.subgroupOf K) (⊤ : Subgroup ↥K) := by
    have h := (isSylowIn_subgroupOf_iff (P := T) (K := K) (H := K) hTK le_rfl).mpr hT
    rwa [Subgroup.subgroupOf_self] at h
  have hΩ' : IsInvColl (⊤ : Subgroup ↥K) Ω' := by
    refine ⟨fun _ _ => le_top, fun A' hA' => ?_, fun A' hA' x _ => ?_⟩
    · exact isElemAbelian_of_map_injective' K.subtype_injective (hΩ.isElemAbelian _ hA')
    · show (conjSub x A').map K.subtype ∈ Ω
      rw [map_conjSub]
      exact hΩ.conj _ hA' _ x.2
  obtain ⟨e, he, n, hn, hgen⟩ := eGen_mul_normalizer_of_isSolvable hQ hT' hΩ' g
  have hmapT : (T.subgroupOf K).map K.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTK
  have hmapΩ : Subgroup.map K.subtype '' Ω' = Ω := by
    ext A
    refine ⟨by rintro ⟨A', hA', rfl⟩; exact hA', fun hA => ⟨A.subgroupOf K, ?_,
      Subgroup.map_subgroupOf_eq_of_le (hΩ.le A hA)⟩⟩
    show (A.subgroupOf K).map K.subtype ∈ Ω
    rwa [Subgroup.map_subgroupOf_eq_of_le (hΩ.le A hA)]
  have heG : (e : Q) ∈ eGen 1 K T Ω := by
    have hm := eGen_map_subtype (G := Q) 1 K (T.subgroupOf K) Ω'
    rw [hmapT, hmapΩ] at hm
    rw [hm]
    simpa using Subgroup.mem_map_of_mem K.subtype he
  have hnG : (n : Q) ∈ Subgroup.normalizer (weakClosure T Ω : Set Q) ⊓ K := by
    have hnc : (n : Q) ∈ Subgroup.normalizer (weakClosure T Ω : Set Q) := by
      refine (conjSub_eq_iff_mem_normalizer (g := (n : Q)) (H := weakClosure T Ω)).mp ?_
      have hwc := weakClosure_map_image_of_injective K.subtype_injective
        (T.subgroupOf K) Ω'
      rw [hmapT, hmapΩ] at hwc
      rw [hwc]
      have hmc := map_conjSub K.subtype n (weakClosure (T.subgroupOf K) Ω')
      rw [conjSub_eq_iff_mem_normalizer.mpr hn] at hmc
      exact hmc.symm
    exact ⟨hnc, n.2⟩
  exact ⟨e, heG, n, hnG, congrArg (Subgroup.subtype K) hgen⟩

end E1

end CFSG.Quasithin
