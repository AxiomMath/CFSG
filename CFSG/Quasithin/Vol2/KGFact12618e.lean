module

public import CFSG.Quasithin.Vol2.KGFact12618d
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Vol2.KGFact12618c

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

section Stab8

@[expose] def stab8 (p q : Fin 8) : Subgroup (Perm (Fin 8)) :=
  alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Perm (Fin 8)) p ⊓
    MulAction.stabilizer (Perm (Fin 8)) q

theorem mem_stab8 {p q : Fin 8} {σ : Perm (Fin 8)} :
    σ ∈ stab8 p q ↔ σ ∈ alternatingGroup (Fin 8) ∧ σ p = p ∧ σ q = q :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem exists_alt8_apply_eq (p q : Fin 8) : ∃ g ∈ alternatingGroup (Fin 8), g p = q := by
  by_cases hpq : p = q
  · exact ⟨1, Subgroup.one_mem _, by rw [hpq]; rfl⟩
  obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 8, r ≠ p ∧ r ≠ q := by
    revert p q
    decide
  refine ⟨swap p r * swap p q, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm hrp),
      Perm.sign_swap hpq]
    decide
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hpq) (Ne.symm hrq)]

theorem exists_alt8_fix_apply_eq {p q r : Fin 8} (hq : q ≠ p) (hr : r ≠ p) :
    ∃ g ∈ alternatingGroup (Fin 8), g p = p ∧ g q = r := by
  by_cases hqr : q = r
  · exact ⟨1, Subgroup.one_mem _, rfl, by rw [hqr]; rfl⟩
  obtain ⟨s, hsp, hsq, hsr⟩ : ∃ s : Fin 8, s ≠ p ∧ s ≠ q ∧ s ≠ r := by
    clear hq hr hqr
    revert p q r
    decide
  refine ⟨swap q s * swap q r, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm hsq),
      Perm.sign_swap hqr]
    decide
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hq) (Ne.symm hr),
      swap_apply_of_ne_of_ne (Ne.symm hq) (Ne.symm hsp)]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hqr) (Ne.symm hsr)]

theorem card_alt8_stab (p : Fin 8) :
    Nat.card ↥(alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Perm (Fin 8)) p) = 2520 := by
  classical
  have hidx := MulAction.index_stabilizer ↥(alternatingGroup (Fin 8)) p
  have horb : MulAction.orbit ↥(alternatingGroup (Fin 8)) p = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨g, hg, hgq⟩ := exists_alt8_apply_eq p q
    exact ⟨⟨g, hg⟩, hgq⟩
  rw [horb, Set.ncard_univ, Nat.card_fin] at hidx
  have hc := (MulAction.stabilizer ↥(alternatingGroup (Fin 8)) p).card_mul_index
  rw [hidx, nat_card_alternatingGroup, Nat.card_fin] at hc
  have e : Nat.card ↥(MulAction.stabilizer ↥(alternatingGroup (Fin 8)) p) =
      Nat.card ↥(alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Perm (Fin 8)) p) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← e]
  have : (8 : ℕ).factorial / 2 = 20160 := by decide
  omega

theorem card_stab8 {p q : Fin 8} (hpq : p ≠ q) : Nat.card ↥(stab8 p q) = 360 := by
  classical
  set A := alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Perm (Fin 8)) p with hA
  have hidx := MulAction.index_stabilizer ↥A q
  have horb : MulAction.orbit ↥A q = ({p}ᶜ : Set (Fin 8)) := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      have h1 : (g : Perm (Fin 8)) p = p := g.2.2
      have h2 : (g : Perm (Fin 8)) q = p := h
      exact hpq ((g : Perm (Fin 8)).injective (h2.trans h1.symm)).symm
    · intro hr
      obtain ⟨g, hg, hgp, hgq⟩ := exists_alt8_fix_apply_eq (Ne.symm hpq) hr
      exact ⟨⟨g, hg, hgp⟩, hgq⟩
  have h7 : ({p}ᶜ : Set (Fin 8)).ncard = 7 := by
    have := Set.ncard_add_ncard_compl ({p} : Set (Fin 8))
    rw [Set.ncard_singleton, Nat.card_fin] at this
    omega
  rw [horb, h7] at hidx
  have hc := (MulAction.stabilizer ↥A q).card_mul_index
  rw [hidx, card_alt8_stab] at hc
  have e : Nat.card ↥(MulAction.stabilizer ↥A q) = Nat.card ↥(stab8 p q) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, ⟨g.1.2.1, g.1.2.2⟩, g.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1.1, g.2.1.2⟩, g.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← e]
  omega

theorem card_le_sixteen {W : Subgroup (Perm (Fin 8))} {p q : Fin 8} (hpq : p ≠ q)
    (hW : W ≤ alternatingGroup (Fin 8)) (hW2 : IsPGroup 2 ↥W)
    (hWp : ∀ g ∈ W, g p = p ∨ g p = q) (hWq : ∀ g ∈ W, g q = p ∨ g q = q) :
    Nat.card ↥W ≤ 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := MulAction.stabilizer ↥W p with hM
  have hidx : M.index = (MulAction.orbit ↥W p).ncard := MulAction.index_stabilizer ↥W p
  have horb : (MulAction.orbit ↥W p).ncard ≤ 2 := by
    have hsub : MulAction.orbit ↥W p ⊆ ({p, q} : Set (Fin 8)) := by
      rintro _ ⟨g, rfl⟩
      rcases hWp g g.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_pair hpq).le
  have hle : M.map W.subtype ≤ stab8 p q := by
    rintro _ ⟨g, hg, rfl⟩
    have hgp : (g : Perm (Fin 8)) p = p := hg
    refine mem_stab8.2 ⟨hW g.2, hgp, ?_⟩
    rcases hWq g g.2 with h | h
    · exact absurd ((g : Perm (Fin 8)).injective (h.trans hgp.symm)) (Ne.symm hpq)
    · exact h
  have hcM : Nat.card ↥(M.map W.subtype) = Nat.card ↥M :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hd360 : Nat.card ↥M ∣ 360 := by
    rw [← hcM, ← card_stab8 hpq]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hW2
  have hdW : Nat.card ↥M ∣ 2 ^ m := hm ▸ M.card_subgroup_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdW
  have hj3 : j ≤ 3 := by
    by_contra h
    have h1 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have h2 : 2 ^ 4 ∣ 360 := h1.trans (hj ▸ hd360)
    norm_num at h2
  have hM8 : Nat.card ↥M ≤ 8 := by
    rw [hj]
    calc 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
      _ = 8 := by norm_num
  have hc := M.card_mul_index
  rw [hidx] at hc
  rw [← hc]
  calc Nat.card ↥M * (MulAction.orbit ↥W p).ncard ≤ 8 * 2 := Nat.mul_le_mul hM8 horb
    _ = 16 := by norm_num

end Stab8

variable {Γ : Type} [Group Γ] [Finite Γ]

open scoped commutatorElement

theorem relIndex_ne_zero_of_finite (H K : Subgroup Γ) : H.relIndex K ≠ 0 := by
  intro h
  have := Subgroup.relIndex_mul_card H K
  rw [h, zero_mul] at this
  exact (Nat.card_pos (α := ↥K)).ne this

theorem a8_branch {Y K T T₀ B : Subgroup Γ} (hYK : Y ≤ Subgroup.normalizer (K : Set Γ))
    (hKY : K ≤ Y) (e : ↥K ≃* ↥(alternatingGroup (Fin 8))) (hT : IsSylowTwoOf T Y)
    (hBK : B < K) (hT₀4 : T₀.relIndex T ≤ 4)
    (hT₀N : T₀ ≤ Subgroup.normalizer (B : Set Γ)) (hBB : ⁅B, B⁆ = B)
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)))
    (hBc : ⁅pCoreOf 2 B, B⁆ = ⊥) : T₀.relIndex T = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  have hD := KG12614.dataA6_of φ hφs (by exact hφk)
  obtain ⟨a, ha⟩ := hD.card
  set H := imgA e B with hHdef
  let iB : ↥B ≃* ↥H := (Subgroup.subgroupOfEquivOfLe hBK.le).symm.trans
    ((B.subgroupOf K).equivMapOfInjective _ (injective_imgA_hom e))
  set ψ : ↥H →* ↥(alternatingGroup (Fin 6)) := φ.comp iB.symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := hφs.comp iB.symm.surjective
  have hcent : ∀ z ∈ CFSG.Open.pCore 2 ↥B, ∀ b : ↥B, z * b = b * z := by
    intro z hz b
    have h1 : ⁅(z : Γ), (b : Γ)⁆ ∈ ⁅pCoreOf 2 B, B⁆ :=
      Subgroup.commutator_mem_commutator (by unfold pCoreOf; exact ⟨z, hz, rfl⟩) b.2
    rw [hBc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hZ : ∀ z ∈ ψ.ker, ∀ h : ↥H, z * h = h * z := by
    intro z hz h
    have hz' : iB.symm z ∈ CFSG.Open.pCore 2 ↥B := by
      rw [← hφk, MonoidHom.mem_ker]
      exact (MonoidHom.mem_ker).1 hz
    have h2 := congrArg iB (hcent _ hz' (iB.symm h))
    simpa using h2
  have hBperf : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hBB]
  have hperf : ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ = ⊤ := by
    have h1 := congrArg (Subgroup.map iB.toMonoidHom) hBperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ iB.surjective] at h1
  have hcH : Nat.card ↥H = 2 ^ a * 360 := by
    rw [← ha]
    exact (Nat.card_congr iB.toEquiv).symm
  have h7 : ¬ 7 ∣ Nat.card ↥H := by
    rw [hcH]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
      norm_num at this
    · norm_num at h
  have hH1 : ∃ h ∈ H, h ≠ 1 := by
    by_contra hc
    push Not at hc
    have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hc
    rw [this, Subgroup.card_bot] at hcH
    have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega
  obtain ⟨p, q, hpq, hfix, honly⟩ := exists_two_fixed_eight
    (orbit_ncard_eq_six ψ hψs (eq_top_of_map_index_le ψ hZ hperf) h7) hH1
  set W := Subgroup.normalizer (B : Set Γ) ⊓ (T ⊓ K) with hWdef
  have hWK : W ≤ K := inf_le_right.trans inf_le_right
  have hpres : ∀ g ∈ imgA e W, ∀ r : Fin 8, (∀ h ∈ H, h r = r) → ∀ h ∈ H, h (g r) = g r := by
    rintro _ ⟨⟨w, hwK⟩, hwW, rfl⟩ r hr h hh
    have hw : w ∈ Subgroup.normalizer (B : Set Γ) := (Subgroup.mem_subgroupOf.1 hwW).1
    have hBw : B.map (MulAut.conj w).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hw
    have hNH : H.map (MulAut.conj ((e ⟨w, hwK⟩ : ↥(alternatingGroup (Fin 8))) :
        Perm (Fin 8))).toMonoidHom = H := by
      rw [hHdef, ← imgA_conj e hBK.le hwK, hBw]
    rw [← hNH] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, MulAut.conj_apply, Perm.mul_apply, Perm.inv_def,
      Equiv.symm_apply_apply, hr h' hh']
  have hWcard : Nat.card ↥W ≤ 16 := by
    rw [← card_imgA e hWK]
    refine card_le_sixteen hpq (imgA_le e W) ?_ (fun g hg => honly _ (hpres g hg p fun h hh =>
      (hfix h hh).1)) (fun g hg => honly _ (hpres g hg q fun h hh => (hfix h hh).2))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1
      (hT.2.1.to_le (inf_le_right.trans inf_le_left) : IsPGroup 2 ↥W)
    exact IsPGroup.of_card (by rw [card_imgA e hWK, hm])
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hKY hKn.isSubnormal
  have hK : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hTK64 : Nat.card ↥(T ⊓ K) = 64 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hTK.2.1
    have hodd := hTK.2.2
    have hc := ((T ⊓ K).subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv, hj,
      hK] at hc
    have hj7 : j < 7 := by
      by_contra h
      have h1 : 2 ^ 7 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have h2 : 2 ^ 7 ∣ 20160 := hc ▸ h1.trans (dvd_mul_right _ _)
      norm_num at h2
    have hj6 : 6 ≤ j := by
      by_contra h
      apply hodd
      have h1 : 2 ^ j * 2 ∣ 2 ^ j * ((T ⊓ K).subgroupOf K).index := by
        rw [hc]
        have h2 : 2 ^ j * 2 ∣ 2 ^ 6 := by
          rw [← pow_succ]
          exact pow_dvd_pow 2 (by omega)
        exact h2.trans (by norm_num)
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    rw [hj, show j = 6 by omega]
    norm_num
  have h1 := Subgroup.relIndex_mul_card (Subgroup.normalizer (B : Set Γ)) (T ⊓ K)
  rw [hTK64, ← hWdef] at h1
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  have h4 : 4 ≤ (Subgroup.normalizer (B : Set Γ)).relIndex (T ⊓ K) := by
    by_contra h
    push Not at h
    have : (Subgroup.normalizer (B : Set Γ)).relIndex (T ⊓ K) * Nat.card ↥W ≤ 3 * 16 :=
      Nat.mul_le_mul (by omega) hWcard
    omega
  have h2 := Subgroup.relIndex_le_of_le_right (inf_le_left : T ⊓ K ≤ T)
    (relIndex_ne_zero_of_finite (Subgroup.normalizer (B : Set Γ)) T)
  have h3 := Subgroup.relIndex_le_of_le_left hT₀N (relIndex_ne_zero_of_finite T₀ T)
  omega

end CFSG.Quasithin.H13.KG12618
