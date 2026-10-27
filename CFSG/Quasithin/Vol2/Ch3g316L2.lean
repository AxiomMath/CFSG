module

public import CFSG.Quasithin.Vol2.Ch3n317A5
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

open scoped commutatorElement

namespace CFSG.Quasithin.Ch3g316

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section SL2

open CFSG.SL2MinimalFaithful

variable {F : Type*} [Field F] [Finite F]

theorem comm_of_card_eq_sl2 {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hQ : Nat.card Q = Nat.card F) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hF hQ
  let f : F → Q := fun t => ⟨g * unipotent t * g⁻¹, hg t⟩
  have hfinj : Function.Injective f := by
    intro s t hst
    have h1 := Subtype.mk.inj hst
    exact unipotent_injective (mul_left_cancel (mul_right_cancel h1))
  have hfbij : Function.Bijective f := by
    refine hfinj.bijective_of_nat_card_le ?_
    rw [hQ]
  have hQmem : ∀ γ ∈ Q, ∃ t : F, γ = g * unipotent t * g⁻¹ := by
    intro γ hγ
    obtain ⟨t, ht⟩ := hfbij.2 ⟨γ, hγ⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  intro a ha b hb
  obtain ⟨s, rfl⟩ := hQmem a ha
  obtain ⟨t, rfl⟩ := hQmem b hb
  calc g * unipotent s * g⁻¹ * (g * unipotent t * g⁻¹)
      = g * (unipotent s * unipotent t) * g⁻¹ := by group
    _ = g * (unipotent t * unipotent s) * g⁻¹ := by
        rw [← unipotent_add, ← unipotent_add, add_comm]
    _ = g * unipotent t * g⁻¹ * (g * unipotent s * g⁻¹) := by group

end SL2

section Natural

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {C : Subgroup W} {n : ℕ}

theorem comm_of_isL2Natural (h : E2.IsL2Natural L C n) {Q : Subgroup (MulAut W)} (hQL : Q ≤ L)
    (hQ : Nat.card Q = 2 ^ n) : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hQ₁ : Nat.card ((Q.subgroupOf L).map e.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective e.injective, hFc, ← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  intro a ha b hb
  have key := comm_of_card_eq_sl2 hFc hQ₁ (e ⟨a, hQL ha⟩) ⟨⟨a, hQL ha⟩, ha, rfl⟩
    (e ⟨b, hQL hb⟩) ⟨⟨b, hQL hb⟩, hb, rfl⟩
  rw [← map_mul, ← map_mul] at key
  exact congrArg Subtype.val (e.injective key)

theorem twoPart_of_isL2Natural (h : E2.IsL2Natural L C n) : twoPart L = 2 ^ n := by
  have hn : 1 ≤ n := h.1
  have h1 := Ch3n317A5.card_of_isL2Natural h
  have hodd : Odd (4 ^ n - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) ?_ odd_one
    exact Nat.even_pow.mpr ⟨by decide, by omega⟩
  have hne : 4 ^ n - 1 ≠ 0 := hodd.pos.ne'
  have h2 : ¬ 2 ∣ 4 ^ n - 1 := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  rw [twoPart, h1, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd h2, add_zero]

end Natural

section Decomp

variable {Γ : Type*} [Group Γ] [Finite Γ] {I : Finset (Subgroup Γ)}

theorem twoPart_sup_of_commute {A B : Subgroup Γ} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hind : A ⊓ B = ⊥) : twoPart (A ⊔ B) = twoPart A * twoPart B := by
  have e := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hAB
  rw [hind, Subgroup.card_bot, mul_one] at e
  rw [twoPart, twoPart, twoPart, e, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, pow_add]

theorem sylow_decomp_gen (hIcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S (⨆ L ∈ I, L)) :
    (∀ L ∈ I, IsSylowTwoOf (S ⊓ L) L) ∧ S = ⨆ L ∈ I, (S ⊓ L) := by
  classical
  have hN : ∀ L ∈ I, (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set Γ) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · subst hLL
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm L' hL' L hL hLL a ha b hb).symm
  have hle : ∀ L ∈ I, L ≤ ⨆ L' ∈ I, L' := fun L hL =>
    le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') L hL le_rfl
  have h4 : ∀ L ∈ I, IsSylowTwoOf (S ⊓ L) L := fun L hL =>
    B6.isSylowTwoOf_inf_normal hS (hle L hL) (hN L hL)
  refine ⟨h4, ?_⟩
  rcases Ch3n317A5.card_cases hIcard with ⟨L, rfl⟩ | ⟨L₁, L₂, hne, rfl⟩
  · simp only [Finset.iSup_singleton] at hS ⊢
    exact (inf_eq_left.mpr hS.1).symm
  · simp only [Finset.iSup_insert, Finset.iSup_singleton] at hS ⊢
    have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) := Finset.mem_insert_self _ _
    have h2 : L₂ ∈ ({L₁, L₂} : Finset (Subgroup Γ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcomm' : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hcomm L₁ h1 L₂ h2 hne
    have hind' : L₁ ⊓ L₂ = ⊥ := by
      have h := hind L₁ h1
      rw [eq_bot_iff] at h ⊢
      intro x hx
      refine h ⟨hx.1, ?_⟩
      refine le_iSup₂_of_le (f := fun L' (_ : L' ∈ ({L₁, L₂} : Finset (Subgroup Γ))) =>
        ⨆ (_ : L' ≠ L₁), L') L₂ h2 ?_ hx.2
      exact le_iSup_of_le (Ne.symm hne) le_rfl
    have hcommP : ∀ a ∈ S ⊓ L₁, ∀ b ∈ S ⊓ L₂, a * b = b * a := fun a ha b hb =>
      hcomm' a ha.2 b hb.2
    have hindP : (S ⊓ L₁) ⊓ (S ⊓ L₂) = ⊥ := by
      rw [eq_bot_iff, ← hind']
      exact inf_le_inf inf_le_right inf_le_right
    have hcard : Nat.card S = Nat.card ↥((S ⊓ L₁) ⊔ (S ⊓ L₂)) := by
      have e := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcommP
      rw [hindP, Subgroup.card_bot, mul_one] at e
      rw [e, hS.card_eq, twoPart_sup_of_commute hcomm' hind', (h4 L₁ h1).card_eq,
        (h4 L₂ h2).card_eq]
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) hcard.le).symm

end Decomp

section SylowComm

variable {W : Type*} [CommGroup W] [Finite W] {C : Subgroup W}
  {I : Finset (Subgroup (MulAut W))}

theorem sylow_comm (hIcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, E2.IsL2Natural L C n)
    {S : Subgroup (MulAut W)} (hS : IsSylowTwoOf S (⨆ L ∈ I, L)) :
    ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  classical
  obtain ⟨hSL, hSeq⟩ := sylow_decomp_gen hIcard hcomm hind hS
  have habel : ∀ L ∈ I, ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a := by
    intro L hL
    obtain ⟨n, hn⟩ := hnat L hL
    refine comm_of_isL2Natural hn inf_le_right ?_
    rw [(hSL L hL).card_eq, twoPart_of_isL2Natural hn]
  intro a ha b hb
  rw [hSeq] at ha hb
  rcases Ch3n317A5.card_cases hIcard with ⟨L, rfl⟩ | ⟨L₁, L₂, hne, rfl⟩
  · simp only [Finset.iSup_singleton] at ha hb
    exact habel L (Finset.mem_singleton_self L) a ha b hb
  · simp only [Finset.iSup_insert, Finset.iSup_singleton] at ha hb
    have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) := Finset.mem_insert_self _ _
    have h2 : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hcommP : ∀ a ∈ S ⊓ L₁, ∀ b ∈ S ⊓ L₂, a * b = b * a := fun a ha b hb =>
      hcomm L₁ h1 L₂ h2 hne a ha.2 b hb.2
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Ch3n317A5.exists_mul_of_mem_sup hcommP ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Ch3n317A5.exists_mul_of_mem_sup hcommP hb
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcommP b₁ hb₁ a₂ ha₂]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
      _ = (b₁ * a₁) * (b₂ * a₂) := by
          rw [habel L₁ h1 a₁ ha₁ b₁ hb₁, habel L₂ h2 a₂ ha₂ b₂ hb₂]
      _ = b₁ * (a₁ * b₂) * a₂ := by group
      _ = b₁ * (b₂ * a₁) * a₂ := by rw [hcommP a₁ ha₁ b₂ hb₂]
      _ = b₁ * b₂ * (a₁ * a₂) := by group

end SylowComm

section Main

variable {G : Type} [Group G] [Finite G]

theorem l2_structure {H T M₂ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmp : MinParabolic H T M₂) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hKJ : twoResidual H ≤ thompsonJ H)
    (I : Finset (Subgroup (MulAut (IntMod V hV))))
    (hcard : I.card = 1 ∨ I.card = 2)
    (hJI : autI hV (thompsonJ H) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    (hSyl : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H))) :
    ⁅T ⊓ twoResidual H, T ⊓ twoResidual H⁆ ≤ pCoreOf 2 (twoResidual H) ∧
    ∀ p ∈ T ⊓ twoResidual H, ∃ j ∈ thompsonJ T, ∃ c ∈ pCoreOf 2 H, j = p * c := by
  classical
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set K := twoResidual H with hKdef
  set P := T ⊓ K with hPdef
  have hTH : T ≤ H := hmp.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((B6.thompsonJ_le T).trans (hTH.trans h))
  have hQ : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H :=
    hmp.inf_centralizer_eq_pCoreOf hred hHV
  have hSyl' : IsSylowTwoOf (autI hV (thompsonJ T)) (⨆ L ∈ I, L) := by
    rw [← hJI]
    exact hSyl
  have hScomm : ∀ a ∈ autI hV (thompsonJ T), ∀ b ∈ autI hV (thompsonJ T), a * b = b * a :=
    sylow_comm hcard hcomm hind hnat hSyl'
  have hTX : autI hV (thompsonJ T) = autI hV T ⊓ autI hV (thompsonJ H) :=
    F1.eq_of_isSylowTwoOf_le hSyl inf_le_right
      ((B2F.isPGroup_autI hV hT2 hTN).to_le inf_le_left)
      (le_inf (autI_mono hV (B6.thompsonJ_le T)) hSyl.1)
  have hPS : autI hV P ≤ autI hV (thompsonJ T) := by
    rw [hTX]
    exact le_inf (autI_mono hV inf_le_left) (autI_mono hV (inf_le_right.trans hKJ))
  have hPCK : P ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := by
    have h1 : P ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H ⊓ K := by
      rw [← hQ, hPdef, inf_right_comm]
    rw [h1]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk), hHK (hKH hk)⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  refine ⟨?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro p hp p' hp'
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := hTN hp.1
    have hp'N : p' ∈ Subgroup.normalizer (V : Set G) := hTN hp'.1
    have hc := hScomm _ (hPS (convI_mem_autI hV hp hpN)) _ (hPS (convI_mem_autI hV hp' hp'N))
    have hmem : ⁅p, p'⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hp hp') (P.inv_mem hp)) (P.inv_mem hp')
    have h1 : convI hV (⟨p, hpN⟩ * ⟨p', hp'N⟩ * ⟨p, hpN⟩⁻¹ * ⟨p', hp'N⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
    exact hPCK ⟨hmem, (convI_eq_one_iff hV _).1 h1⟩
  · intro p hp
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := hTN hp.1
    obtain ⟨j, hjJ, hj⟩ := (mem_autI hV).1 (hPS (convI_mem_autI hV hp hpN))
    have hjT : (j : G) ∈ T := B6.thompsonJ_le T hjJ
    have hc : p⁻¹ * (j : G) ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : convI hV (⟨p, hpN⟩⁻¹ * j) = 1 := by
        rw [map_mul, map_inv, hj, inv_mul_cancel]
      exact (convI_eq_one_iff hV _).1 h1
    refine ⟨(j : G), hjJ, p⁻¹ * (j : G), ?_, by group⟩
    rw [← hQ]
    exact ⟨T.mul_mem (T.inv_mem hp.1) hjT, hc⟩

end Main

end CFSG.Quasithin.Ch3g316
