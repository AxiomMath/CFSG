module

public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
import CFSG.HardMathSupport.Solomon.Coordinator.WeakBalance
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofX
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163Rigid

open CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Lang.Triality
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec14

theorem eq_map_conj_of_forall_fix {L : Type} [Group L] [Finite L]
    (hZ : Subgroup.center L = ⊥) {E D : Subgroup L} (hE : IsPGroup 3 E)
    (hD : IsMaxInvTwo E D) {T : Subgroup (MulAut L)} (hT : IsPGroup 2 T)
    (hDT : D.map (MulAut.conj : L →* MulAut L) ≤ T)
    (hET : E.map (MulAut.conj : L →* MulAut L) ≤
      Subgroup.normalizer (T : Set (MulAut L)))
    (hfix : ∀ τ ∈ T, (∀ e ∈ E, τ e = e) → τ = 1) :
    T = D.map (MulAut.conj : L →* MulAut L) := by
  let c : L →* MulAut L := MulAut.conj
  have hc : Function.Injective c := conj_injective_of_center_eq_bot hZ
  have hA : IsPGroup 3 (E.map c) := hE.map c
  have hY : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT.exists_card_dvd_pow
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    exact fun h => (Nat.prime_three.coprime_iff_not_dvd.mp hcop) (h.trans hn)
  have hcent : T ⊓ Subgroup.centralizer ((E.map c : Subgroup (MulAut L)) :
      Set (MulAut L)) = ⊥ := by
    ext τ
    rw [Subgroup.mem_inf, Subgroup.mem_bot]
    constructor
    · rintro ⟨hτT, hτC⟩
      refine hfix τ hτT fun e he => ?_
      have hcomm : MulAut.conj e * τ = τ * MulAut.conj e :=
        (Subgroup.mem_centralizer_iff.mp hτC) (MulAut.conj e)
          (Subgroup.mem_map_of_mem c he)
      have hconj : MulAut.conj (τ e) = MulAut.conj e := by
        calc MulAut.conj (τ e) = τ * MulAut.conj e * τ⁻¹ :=
              (mulAut_mul_conj_mul_inv τ e).symm
          _ = MulAut.conj e := by rw [← hcomm]; group
      exact hc hconj
    · rintro rfl
      simp
  have hcomm : ⁅T, E.map c⁆ ≤ c.range := by
    refine Subgroup.commutator_le.mpr ?_
    intro τ hτ a ha
    obtain ⟨e, he, rfl⟩ := ha
    refine MonoidHom.mem_range.mpr ⟨τ e * e⁻¹, ?_⟩
    rw [commutatorElement_def]
    have h1 : τ * c e * τ⁻¹ = MulAut.conj (τ e) := by
      simpa [c] using mulAut_mul_conj_mul_inv τ e
    rw [h1]
    change c (τ e * e⁻¹) = c (τ e) * (c e)⁻¹
    rw [← map_inv c e, ← map_mul c]
  have hle : T ≤ c.range :=
    (le_commutator_sup_inf_centralizer_of_isPGroup (p := 3) Nat.prime_three
      (A := E.map c) (Y := T) hA hET hY).trans
      (sup_le hcomm (by rw [hcent]; exact bot_le))
  let D' : Subgroup L := T.comap c
  have hD'map : D'.map c = T := Subgroup.map_comap_eq_self hle
  have hD'2 : IsPGroup 2 D' := hT.comap_of_injective c hc
  have hEnorm : E ≤ Subgroup.normalizer (D' : Set L) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change c x ∈ T ↔ c (e * x * e⁻¹) ∈ T
    have hce : c e ∈ Subgroup.normalizer (T : Set (MulAut L)) :=
      hET (Subgroup.mem_map_of_mem c he)
    rw [Subgroup.mem_normalizer_iff] at hce
    have hconj : c (e * x * e⁻¹) = MulAut.conj (c e) (c x) := by
      simp [map_mul, MulAut.conj_apply]
    rw [hconj]
    exact hce (c x)
  have hle' : D ≤ D' := fun d hd => hDT (Subgroup.mem_map_of_mem c hd)
  have hD'le : D' ≤ D := hD.2 ⟨hD'2, hEnorm⟩ hle'
  have hD'eq : D' = D := le_antisymm hD'le hle'
  rw [← hD'eq]
  exact hD'map.symm

theorem eq_map_conj_of_rigid {L : Type} [Group L] [Finite L]
    (hZ : Subgroup.center L = ⊥) {E D : Subgroup L} (hE : IsPGroup 3 E)
    (hD : IsMaxInvTwo E D)
    (hrig : ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1)
    {T : Subgroup (MulAut L)} (hT : IsPGroup 2 T)
    (hDT : D.map (MulAut.conj : L →* MulAut L) ≤ T)
    (hET : E.map (MulAut.conj : L →* MulAut L) ≤
      Subgroup.normalizer (T : Set (MulAut L))) :
    T = D.map (MulAut.conj : L →* MulAut L) := by
  refine eq_map_conj_of_forall_fix hZ hE hD hT hDT hET fun τ hτ hfix => ?_
  exact hrig τ hfix (by
    simpa using hT.orderOf_coprime (by norm_num : Nat.Coprime 2 3) ⟨τ, hτ⟩)

theorem rigid_of_alternating_seven {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* alternatingGroup (Fin 7))) {E : Subgroup L}
    (hE : Nat.card E = 9) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 := by
  intro σ hfix hcop
  obtain ⟨φ⟩ := hL
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'E⟩ := Res5Types.exists_equiv_map_eq (P := Res5TypesA7.P7) φ
    Res5TypesA7.card_P7 hE hfac
  let β : MulAut ↥(alternatingGroup (Fin 7)) := MulAut.congr φ' σ
  have hfixP : ∀ p ∈ Res5TypesA7.P7, β p = p := by
    intro p hp
    have hp' : p ∈ E.map φ'.toMonoidHom := by rw [hφ'E]; exact hp
    obtain ⟨e, he, rfl⟩ := hp'
    change (MulAut.congr φ') σ (φ' e) = φ' e
    rw [MulAut.congr_apply]
    simp [hfix e he]
  have hβ1 : β = 1 := by
    refine Res5TypesA7.aut_eq_one_A7 (τ := β) (n := orderOf σ) hfixP ?_ ?_
    · exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop.symm
    · rw [← MulEquiv.orderOf_eq (MulAut.congr φ') σ]
      exact pow_orderOf_eq_one β
  have hcongr : (MulAut.congr φ') σ = 1 := hβ1
  exact (MulAut.congr φ').injective (by rw [hcongr, map_one])

theorem rigid_of_m22 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M22)) {E : Subgroup L}
    (hE : Nat.card E = 9) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 := by
  intro σ hfix hcop
  obtain ⟨c, hcE, rfl⟩ := KP4.m22_aut_fix_eq_conj hL hE hfix
  obtain ⟨φ⟩ := hL
  have hZ : Subgroup.center L = ⊥ := by
    have hmap := Subgroup.map_center_eq (f := φ)
    rw [CFSG.Sporadic.Schreier.m22_center_eq_bot'] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center L)
      (f := (φ : L →* CFSG.Blueprint.NativeSporadic.M22)) φ.injective).mp hmap
  have hord : orderOf (MulAut.conj c) = orderOf c :=
    orderOf_injective (MulAut.conj : L →* MulAut L)
      (conj_injective_of_center_eq_bot hZ) c
  have hcop' : Nat.Coprime (orderOf c) 3 := hord ▸ hcop
  have hdvd : orderOf c ∣ 9 := by
    rw [← hE]
    exact Subgroup.orderOf_dvd_natCard E hcE
  have h3 : orderOf c ∣ 3 := by
    have h9 : orderOf c ∣ 3 * 3 := by simpa using hdvd
    exact (hcop'.dvd_mul_right).mp h9
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl h3)
  rw [hc1]
  simp

theorem rigid_of_j2 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup L}
    (hE : Nat.card E = 9) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 := by
  intro σ hfix hcop
  exact CFSG.RankThree.PartTwo.Sec17.Proof17Res3.j2_aut_eq_one_of_coprime hL hE hcop.symm hfix

theorem ks163P6Norm_alternating_seven {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* alternatingGroup (Fin 7))) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 →
      D.map σ.toMonoidHom = D := by
  intro σ hfix hcop
  rw [rigid_of_alternating_seven hL hE9 σ hfix hcop]
  exact Subgroup.map_id D

theorem ks163P6Norm_m22 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M22)) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 →
      D.map σ.toMonoidHom = D := by
  intro σ hfix hcop
  rw [rigid_of_m22 hL hE9 σ hfix hcop]
  exact Subgroup.map_id D

theorem ks163P6Norm_j2 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J2)) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 →
      D.map σ.toMonoidHom = D := by
  intro σ hfix hcop
  rw [rigid_of_j2 hL hE9 σ hfix hcop]
  exact Subgroup.map_id D

theorem ks163P6Cent_alternating_seven {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* alternatingGroup (Fin 7))) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ T : Subgroup (MulAut L), IsPGroup 2 T →
      D.map (MulAut.conj : L →* MulAut L) ≤ T →
      T ≤ D.map (MulAut.conj : L →* MulAut L) ⊔
        Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
          Set (MulAut L)) →
      E.map (MulAut.conj : L →* MulAut L) ≤ Subgroup.normalizer (T : Set (MulAut L)) →
        T = D.map (MulAut.conj : L →* MulAut L) := by
  intro T hT hDT _ hET
  have hrig : ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 :=
    fun σ hσ hc => rigid_of_alternating_seven hL hE9 σ hσ hc
  obtain ⟨φ⟩ := hL
  have hZ : Subgroup.center L = ⊥ := by
    have hmap := Subgroup.map_center_eq (f := φ)
    rw [alternatingGroup.center_eq_bot (α := Fin 7) (by simp)] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center L)
      (f := (φ : L →* ↥(alternatingGroup (Fin 7)))) φ.injective).mp hmap
  exact eq_map_conj_of_rigid hZ hE.isPGroup hD hrig hT hDT hET

theorem ks163P6Cent_m22 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M22)) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ T : Subgroup (MulAut L), IsPGroup 2 T →
      D.map (MulAut.conj : L →* MulAut L) ≤ T →
      T ≤ D.map (MulAut.conj : L →* MulAut L) ⊔
        Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
          Set (MulAut L)) →
      E.map (MulAut.conj : L →* MulAut L) ≤ Subgroup.normalizer (T : Set (MulAut L)) →
        T = D.map (MulAut.conj : L →* MulAut L) := by
  intro T hT hDT _ hET
  have hrig : ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 :=
    fun σ hσ hc => rigid_of_m22 hL hE9 σ hσ hc
  obtain ⟨φ⟩ := hL
  have hZ : Subgroup.center L = ⊥ := by
    have hmap := Subgroup.map_center_eq (f := φ)
    rw [CFSG.Sporadic.Schreier.m22_center_eq_bot'] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center L)
      (f := (φ : L →* CFSG.Blueprint.NativeSporadic.M22)) φ.injective).mp hmap
  exact eq_map_conj_of_rigid hZ hE.isPGroup hD hrig hT hDT hET

theorem ks163P6Cent_j2 {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J2)) (E : Subgroup L)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (D : Subgroup L)
    (hD : IsMaxInvTwo E D) :
    ∀ T : Subgroup (MulAut L), IsPGroup 2 T →
      D.map (MulAut.conj : L →* MulAut L) ≤ T →
      T ≤ D.map (MulAut.conj : L →* MulAut L) ⊔
        Subgroup.centralizer ((D.map (MulAut.conj : L →* MulAut L) : Subgroup (MulAut L)) :
          Set (MulAut L)) →
      E.map (MulAut.conj : L →* MulAut L) ≤ Subgroup.normalizer (T : Set (MulAut L)) →
        T = D.map (MulAut.conj : L →* MulAut L) := by
  intro T hT hDT _ hET
  have hZ : Subgroup.center L = ⊥ := KS14.Native.center_eq_bot_of_j2 hL
  have hrig : ∀ σ : MulAut L, (∀ e ∈ E, σ e = e) → Nat.Coprime (orderOf σ) 3 → σ = 1 :=
    fun σ hσ hc => rigid_of_j2 hL hE9 σ hσ hc
  exact eq_map_conj_of_rigid hZ hE.isPGroup hD hrig hT hDT hET

end CFSG.RankThree.PartTwo.KFacts.KF163Rigid

namespace CFSG.RankThree.PartTwo.KFacts

open KF163Rigid

theorem ks163P6Norm_of_l3
    (h : KS163P6NormL3) : KS163P6Norm := by
  intro L _ _ htype E hE hE9 D hD σ hfix hcop
  rcases htype with hA7 | hM22 | hJ2 | ⟨p, e, hp, hp2, he1, hiso, hmod⟩
  · exact ks163P6Norm_alternating_seven hA7 E hE hE9 D hD σ hfix hcop
  · exact ks163P6Norm_m22 hM22 E hE hE9 D hD σ hfix hcop
  · exact ks163P6Norm_j2 hJ2 E hE hE9 D hD σ hfix hcop
  · letI : Fact p.Prime := hp
    exact h L p e hp2 he1 hiso hmod E hE hE9 D hD σ hfix hcop

theorem ks163P6Cent_of_l3
    (h : KS163P6CentL3) : KS163P6Cent := by
  intro L _ _ htype E hE hE9 D hD T hT hDT hcent hET
  rcases htype with hA7 | hM22 | hJ2 | ⟨p, e, hp, hp2, he1, hiso, hmod⟩
  · exact ks163P6Cent_alternating_seven hA7 E hE hE9 D hD T hT hDT hcent hET
  · exact ks163P6Cent_m22 hM22 E hE hE9 D hD T hT hDT hcent hET
  · exact ks163P6Cent_j2 hJ2 E hE hE9 D hD T hT hDT hcent hET
  · letI : Fact p.Prime := hp
    exact h L p e hp2 he1 hiso hmod E hE hE9 D hD T hT hDT hcent hET

end CFSG.RankThree.PartTwo.KFacts
