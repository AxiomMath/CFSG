module

public import CFSG.Quasithin.H13.NQBlockCcommCritical
public import CFSG.Quasithin.H13.NQBlockCcommWholeShape
public import CFSG.Quasithin.H13.NQBlockCcommHomocyclic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

@[expose] noncomputable def wholeFrattiniAction {L : Type*} [Group L] (Q : Subgroup L)
    [Q.Normal] : L →* MulAut (Q ⧸ frattini Q) :=
  (autQuotient (frattini Q)).comp MulAut.conjNormal

noncomputable def rangeEquivOfKerEq {L A B : Type*} [Group L] [Group A] [Group B] (φ : L →* A)
    (ψ : L →* B) (h : φ.ker = ψ.ker) : φ.range ≃* ψ.range :=
  (QuotientGroup.quotientKerEquivRange φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange ψ))

theorem projective_data_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Nontrivial B) (hBq : CFSG.IsQuasisimple B) {s : ℕ}
    (hBs : Nonempty (B ⧸ center B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) :
    Nontrivial A ∧ CFSG.IsQuasisimple A ∧
      Nonempty (A ⧸ center A ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) := by
  obtain ⟨ψ⟩ := hBs
  refine ⟨e.toEquiv.nontrivial, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hBq,
    ⟨(QuotientGroup.congr _ _ e (map_center_eq e)).trans ψ⟩⟩

section Inputs

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem closure_conj_eq_top_of_commutator_eq {Q : Subgroup L} [Q.Normal]
    (hQ : ⁅Q, (⊤ : Subgroup L)⁆ = Q) :
    closure {y : Q | ∃ x : Q, ∃ h : L, x⁻¹ * (MulAut.conjNormal h) x = y} = ⊤ := by
  set S := closure {y : Q | ∃ x : Q, ∃ h : L, x⁻¹ * (MulAut.conjNormal h) x = y} with hS
  have hle' : ⁅Q, (⊤ : Subgroup L)⁆ ≤ S.map Q.subtype := by
    rw [commutator_le]
    intro q hq l _
    refine ⟨⟨q, hq⟩⁻¹⁻¹ * MulAut.conjNormal l ⟨q, hq⟩⁻¹, subset_closure ⟨_, l, rfl⟩, ?_⟩
    simp only [inv_inv, coe_mul, MulAut.conjNormal_apply, coe_inv, subtype_apply,
      commutatorElement_def]
    group
  have hle : Q ≤ S.map Q.subtype := by
    rw [hQ] at hle'
    exact hle'
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [Subtype.ext hyx] at hy

omit [Finite L] in
theorem conj_eq_conjNormal {Q : Subgroup L} [Q.Normal] (q : Q) :
    MulAut.conj q = (MulAut.conjNormal (q : L) : MulAut Q) := by
  ext x
  simp

theorem exists_involution_preimage {M : Type*} [Group M] (ρ : L →* M)
    (hodd : Odd (Nat.card ρ.ker)) {g : M} (hg : g ∈ ρ.range) (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    ∃ t : L, orderOf t = 2 ∧ ρ t = g := by
  classical
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg2) hg1
  set T := (zpowers g).comap ρ with hT
  let f : T →* zpowers g := (ρ.comp T.subtype).codRestrict (zpowers g) fun x => x.2
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨l, hl⟩ := hg
    refine ⟨⟨l ^ k, ?_⟩, Subtype.ext ?_⟩
    · rw [hT, mem_comap, map_zpow, hl]
      exact zpow_mem (mem_zpowers g) k
    · change ρ (l ^ k) = g ^ k
      rw [map_zpow, hl]
  have h2 : 2 ∣ Nat.card T := by
    have := Subgroup.card_dvd_of_surjective (f := f) hfs
    rwa [Nat.card_zpowers, hord] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : L) = 2 := by rwa [Subgroup.orderOf_coe]
  refine ⟨t, ht', ?_⟩
  have hmem : ρ t ∈ zpowers g := t.2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hne : ρ t ≠ 1 := by
    intro h1
    have htK : (t : L) ∈ ρ.ker := h1
    have h3 := Subgroup.orderOf_dvd_natCard ρ.ker htK
    rw [ht'] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  rw [← hk, ← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hne ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hne
    exact absurd rfl hne
  · rw [h, zpow_one]

theorem mem_frattini_iff_of_eq_top {Q : Type*} [Group Q] {D : Subgroup Q} (hD : D = ⊤)
    (x : D) : x ∈ frattini D ↔ (x : Q) ∈ frattini Q := by
  set e : D ≃* Q := (MulEquiv.subgroupCongr hD).trans topEquiv with he
  have he' : ∀ y : D, e y = (y : Q) := fun _ => rfl
  constructor
  · intro hx
    have h1 := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, he'] at h1
  · intro hx
    have h1 := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
      hx
    rw [mem_comap, MulEquiv.coe_toMonoidHom] at h1
    have h2 : e.symm (x : Q) = x := by rw [MulEquiv.symm_apply_eq, he']
    rwa [h2] at h1

end Inputs

theorem whole_Frattini_assembly_core {L : Type*} [Group L] [Finite L]
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hCF : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L)
    (hodd : Odd (Nat.card (CFSG.fittingSubgroup L)))
    (hcomm : ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ ≠ ⊥)
    (hcores : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      CFSG.pCore r L ≠ ⊥ ∧ CFSG.pRank r (CFSG.pCore r L) ≤ 2) :
    ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      (∀ S : Sylow r (CFSG.fittingSubgroup L),
        (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
          CFSG.pCore r L) ∧
      r ≠ 2 ∧ CFSG.pCore r L ≠ ⊥ ∧
      Nat.card (CFSG.pCore r L ⧸ frattini (CFSG.pCore r L)) = r ^ 2 ∧
      (wholeFrattiniAction (CFSG.pCore r L)).range ≠ ⊥ ∧
      CFSG.IsQuasisimple (wholeFrattiniAction (CFSG.pCore r L)).range ∧
      (∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = r ∨ s = 5) ∧
        Nonempty ((wholeFrattiniAction (CFSG.pCore r L)).range ⧸
            center (wholeFrattiniAction (CFSG.pCore r L)).range ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) ∧
      ((¬ IsMulCommutative (CFSG.pCore r L) ∧ Nat.card (CFSG.pCore r L) = r ^ 3 ∧
          ∀ x : CFSG.pCore r L, x ^ r = 1) ∨
        (IsMulCommutative (CFSG.pCore r L) ∧ ∃ a : ℕ, 1 ≤ a ∧
          Nonempty (CFSG.pCore r L ≃*
            Multiplicative (ZMod (r ^ a)) × Multiplicative (ZMod (r ^ a))))) := by
  classical
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_core hLC hCF hodd hcomm hcores
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr (by
    rw [commutator_def]
    exact hLC.2.1)
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hr))
  have hQne := (hcores r hr).1
  have hsyl : ∀ S : Sylow r (CFSG.fittingSubgroup L),
      (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
        CFSG.pCore r L := fun S => sylow_fitting_map_eq_pCore S
  set Q := CFSG.pCore r L with hQdef
  obtain ⟨hQL, D, hDc, hD, hker⟩ := hcrit r hr
  have hQp : IsPGroup r Q := CFSG.pCore_isPGroup
  have hQF : Q ≤ CFSG.fittingSubgroup L := CFSG.pCore_le_fitting L r
  have hQH := closure_conj_eq_top_of_commutator_eq hQL
  have hirr : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = r →
      ∃ h : L, ∃ u ∈ U, frattiniAction D (MulAut.conjNormal h) u ∉ U := by
    intro U hU
    obtain ⟨g, ⟨l, rfl⟩, u, hu, hgu⟩ := hD.irreducible U hU
    exact ⟨l, u, hu, hgu⟩
  have hQtriv : ∀ q : Q, frattiniAction D (MulAut.conj q) = 1 := by
    intro q
    rw [conj_eq_conjNormal]
    have h1 : (q : L) ∈ (criticalAction D).ker := by rw [hker]; exact hQF q.2
    exact h1
  have ht : ∃ t : L, orderOf t = 2 ∧ ∀ w, frattiniAction D (MulAut.conjNormal t) w = w⁻¹ := by
    obtain ⟨g, hg, hg1, hginv⟩ := hD.inv_mem
    have hg2 : g * g = 1 := MulEquiv.ext fun w => by
      rw [MulAut.mul_apply, hginv, hginv, inv_inv, MulAut.one_apply]
    have hodd' : Odd (Nat.card (criticalAction D).ker) := by rw [hker]; exact hodd
    obtain ⟨t, ht2, htg⟩ := exists_involution_preimage (criticalAction D) hodd' hg hg1 hg2
    refine ⟨t, ht2, fun w => ?_⟩
    have h1 : criticalAction D t = frattiniAction D (MulAut.conjNormal t) := rfl
    rw [← h1, htg, hginv]
  have hshapeD : (IsElementaryAbelian r D ∧ Nat.card D = r ^ 2) ∨
      (¬ IsMulCommutative D ∧ Nat.card D = r ^ 3 ∧ (∀ x ∈ D, x ^ r = 1) ∧
        frattini D = center D ∧ Nat.card (frattini D) = r) := by
    rcases hD.shape with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hD.pow_eq_one, h3, h4⟩
  obtain ⟨hnab, hab⟩ := supercritical_whole_pgroup_shape hr2 hQp MulAut.conjNormal D hQH
    hD.torsion hshapeD hirr hQtriv ht
  obtain ⟨s, hs, hs5, hsr, hJs⟩ := hD.projective
  have hJnt : Nontrivial (criticalAction D).range :=
    (nontrivial_iff_ne_bot _).mpr hD.range_ne_bot
  suffices hsuff : (wholeFrattiniAction Q).ker = CFSG.fittingSubgroup L ∧
      Nat.card (Q ⧸ frattini Q) = r ^ 2 ∧
      ((¬ IsMulCommutative Q ∧ Nat.card Q = r ^ 3 ∧ ∀ x : Q, x ^ r = 1) ∨
        (IsMulCommutative Q ∧ ∃ a : ℕ, 1 ≤ a ∧
          Nonempty (Q ≃* Multiplicative (ZMod (r ^ a)) × Multiplicative (ZMod (r ^ a))))) by
    obtain ⟨hkerW, hcardW, hshapeQ⟩ := hsuff
    have e := rangeEquivOfKerEq (wholeFrattiniAction Q) (criticalAction D) (hkerW.trans hker.symm)
    obtain ⟨hWnt, hWq, hWs⟩ := projective_data_of_mulEquiv e hJnt hD.isQuasisimple hJs
    exact ⟨hsyl, hr2, hQne, hcardW, (nontrivial_iff_ne_bot _).mp hWnt, hWq,
      ⟨s, hs, hs5, hsr, hWs⟩, hshapeQ⟩
  by_cases hDab : IsMulCommutative D
  ·
    have hDel : IsElementaryAbelian r D := by
      rcases hD.shape with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hDab h
    obtain ⟨hQab, ⟨a, ha, ⟨eQ⟩⟩, hDΩ⟩ := hab hDel
    have : Fact (IsPGroup r D) := ⟨hQp.to_subgroup D⟩
    have hΦD : frattini D = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := D) (p := r)
    have hDmem : ∀ x : Q, x ^ r = 1 ↔ x ∈ D := by
      intro x
      constructor
      · intro hx
        rw [hDΩ]
        exact subset_closure (show x ^ r ^ 1 = 1 by rw [pow_one]; exact hx)
      · exact hD.pow_eq_one x
    have hkerC : ∀ l : L, l ∈ (criticalAction D).ker ↔
        ∀ x : Q, x ^ r = 1 → MulAut.conjNormal l x = x := by
      intro l
      change MulAut.conjNormal l ∈ (frattiniAction D).ker ↔ _
      rw [mem_ker_frattiniAction, hΦD]
      constructor
      · intro h x hx
        have h1 := h ⟨x, (hDmem x).mp hx⟩
        rw [mem_bot, inv_mul_eq_one] at h1
        have h2 := congrArg Subtype.val h1
        have e1 : ((MulAut.characteristic D (MulAut.conjNormal l) ⟨x, (hDmem x).mp hx⟩ : D) :
            Q) = MulAut.conjNormal l x := by simp
        rw [e1] at h2
        exact h2.symm
      · intro h d
        rw [mem_bot, inv_mul_eq_one]
        apply Subtype.ext
        have e1 : ((MulAut.characteristic D (MulAut.conjNormal l) d : D) : Q) =
            MulAut.conjNormal l d := by simp
        rw [e1, h d ((hDmem d).mpr d.2)]
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQab.is_comm.comm }
    obtain ⟨-, -, -, hcardQ, -, -, hkerT, -⟩ :=
      homocyclic_frattini_transport ha eQ (MulAut.conjNormal : L →* MulAut Q)
    refine ⟨?_, hcardQ, Or.inr ⟨hQab, a, ha, ⟨eQ⟩⟩⟩
    rw [← hker]
    ext l
    have h1 : l ∈ (wholeFrattiniAction Q).ker ↔
        l ∈ ((omegaAut r).comp (MulAut.conjNormal : L →* MulAut Q)).ker := by
      rw [← hkerT]
      rfl
    rw [h1, hkerC, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h x hx
      have h2 := congrArg (fun f : MulAut (powMonoidHom r : Q →* Q).ker => ((f ⟨x, hx⟩ : _) : Q)) h
      exact h2
    · intro h
      exact MulEquiv.ext fun x => Subtype.ext (h x x.2)
  ·
    have hDtop : D = ⊤ := hnab hDab
    have hkerW : (wholeFrattiniAction Q).ker = (criticalAction D).ker := by
      ext l
      change MulAut.conjNormal l ∈ (autQuotient (frattini Q)).ker ↔
        MulAut.conjNormal l ∈ (frattiniAction D).ker
      rw [mem_ker_autQuotient, mem_ker_frattiniAction]
      constructor
      · intro h d
        rw [mem_frattini_iff_of_eq_top hDtop]
        have e1 : ((d⁻¹ * MulAut.characteristic D (MulAut.conjNormal l) d : D) : Q) =
            (d : Q)⁻¹ * MulAut.conjNormal l d := by simp
        rw [e1]
        exact h d
      · intro h x
        have hx : x ∈ D := by rw [hDtop]; exact mem_top x
        have h1 := (mem_frattini_iff_of_eq_top hDtop _).mp (h ⟨x, hx⟩)
        have e1 : ((⟨x, hx⟩⁻¹ * MulAut.characteristic D (MulAut.conjNormal l) ⟨x, hx⟩ : D) :
            Q) = x⁻¹ * MulAut.conjNormal l x := by simp
        rwa [e1] at h1
    set eD : D ≃* Q := (MulEquiv.subgroupCongr hDtop).trans topEquiv with heD
    have hmapΦ : (frattini D).map eD.toMonoidHom = frattini Q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (mem_frattini_iff_of_eq_top hDtop y).mp hy
      · intro hx
        have hx' : x ∈ D := by rw [hDtop]; exact mem_top x
        exact ⟨⟨x, hx'⟩, (mem_frattini_iff_of_eq_top hDtop _).mpr hx, rfl⟩
    have hcardW : Nat.card (Q ⧸ frattini Q) = r ^ 2 := by
      rw [← hD.card_quotient]
      exact (Nat.card_congr (QuotientGroup.congr _ _ eD hmapΦ).toEquiv).symm
    refine ⟨hkerW.trans hker, hcardW, Or.inl ⟨fun hQc => hDab ?_, ?_, fun x => ?_⟩⟩
    · exact ⟨⟨fun a b => Subtype.ext (hQc.is_comm.comm (a : Q) b)⟩⟩
    · rcases hD.shape with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact absurd h.toIsMulCommutative hDab
      · rw [← h, hDtop, card_top]
    · exact hD.pow_eq_one x (by rw [hDtop]; exact mem_top x)

theorem whole_Frattini_assembly {G : Type*} [Group G] [Finite G]
    (hSQT : CFSG.IsStronglyQuasithin G) (hO2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G}
    (hL : CFSG.IsCComponent L) (hq : ¬ CFSG.IsQuasisimple L) :
    CFSG.generalizedFitting L = CFSG.fittingSubgroup L ∧ CFSG.fittingSubgroup L ≠ ⊥ ∧
      Group.IsNilpotent (CFSG.fittingSubgroup L) ∧ Odd (Nat.card (CFSG.fittingSubgroup L)) ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        (∀ S : Sylow r (CFSG.fittingSubgroup L),
          (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
            CFSG.pCore r L) ∧
        r ≠ 2 ∧ CFSG.pCore r L ≠ ⊥ ∧
        Nat.card (CFSG.pCore r L ⧸ frattini (CFSG.pCore r L)) = r ^ 2 ∧
        (wholeFrattiniAction (CFSG.pCore r L)).range ≠ ⊥ ∧
        CFSG.IsQuasisimple (wholeFrattiniAction (CFSG.pCore r L)).range ∧
        (∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s = r ∨ s = 5) ∧
          Nonempty ((wholeFrattiniAction (CFSG.pCore r L)).range ⧸
              center (wholeFrattiniAction (CFSG.pCore r L)).range ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))) ∧
        ((¬ IsMulCommutative (CFSG.pCore r L) ∧ Nat.card (CFSG.pCore r L) = r ^ 3 ∧
            ∀ x : CFSG.pCore r L, x ^ r = 1) ∨
          (IsMulCommutative (CFSG.pCore r L) ∧ ∃ a : ℕ, 1 ≤ a ∧
            Nonempty (CFSG.pCore r L ≃*
              Multiplicative (ZMod (r ^ a)) × Multiplicative (ZMod (r ^ a))))) := by
  obtain ⟨hFstar, hFne, hnil, hodd, hcomm, -, -, hcores⟩ := odd_Fitting_cores hSQT hO2 hL hq
  have hCF : centralizer (CFSG.fittingSubgroup L : Set L) ≤ CFSG.fittingSubgroup L := by
    have h1 := CFSG.centralizer_generalizedFitting_le L
    rwa [hFstar] at h1
  exact ⟨hFstar, hFne, hnil, hodd, whole_Frattini_assembly_core
    (isCComponent_top_of_isCComponent hL) hCF hodd hcomm
    fun r hr => ⟨(hcores r hr).1, (hcores r hr).2.2.2⟩⟩

end CFSG.Quasithin.H13.NQBlock
