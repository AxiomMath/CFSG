module

public import CFSG.Sporadic.SuzI301.Spec
public import CFSG.Sporadic.SuzOddCore.ExtModel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271
  CFSG.LocalAnalysis.GLTheoremA.H301

local notation "Ω₁₀" => Subgroup.closure (Set.range fun j : Fin 10 => tabP matTabs[(j : ℕ)]!)

local notation "O₁₁" => Subgroup.closure (Set.range fun j : Fin 11 => tabP oGens[(j : ℕ)]!)

theorem exists_embedding_suzT
    {A : Type*} [Group A]
    (ι : ↥suzM →* A) (hι : Function.Injective ι) (hN : ι.range.Normal)
    (hC : Subgroup.centralizer (ι.range : Set A) = ⊥) :
    ∃ f : A →* Equiv.Perm (Fin 1782), Function.Injective f ∧ (∀ a, f a ∈ suzT) ∧
      ∀ m : suzM, f (ι m) = m := by
  have := hN
  have hinj : Function.Injective (MulAut.conjNormal : A →* MulAut ι.range) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : a ∈ Subgroup.centralizer (ι.range : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg (fun α : MulAut ι.range => ((α ⟨f, hf⟩ : ι.range) : A)) ha
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc f * a = a * f * a⁻¹ * a := by rw [h1]
        _ = a * f := by group
    rw [hC, Subgroup.mem_bot] at hc
    exact hc
  set ψ : suzT ≃* MulAut suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  set e : suzM ≃* ι.range := MonoidHom.ofInjective hι
  set j : A →* suzT :=
    ψ.symm.toMonoidHom.comp ((MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal)
  have hj : Function.Injective j :=
    ψ.symm.injective.comp ((MulAut.congr e.symm).injective.comp hinj)
  refine ⟨suzT.subtype.comp j, suzT.subtype_injective.comp hj, fun a => (j a).2, fun m => ?_⟩
  have hm : ι m ∈ ι.range := MonoidHom.mem_range.2 ⟨m, rfl⟩
  have h1 : (MulAut.conjNormal (ι m) : MulAut ι.range) = MulAut.conj ⟨ι m, hm⟩ :=
    MulAut.conjNormal_val (h := ⟨ι m, hm⟩)
  have h2 : e.symm ⟨ι m, hm⟩ = m := hι (MonoidHom.apply_ofInjective_symm hι ⟨ι m, hm⟩)
  have h3 : j (ι m) = ⟨m, suzM_le_suzT m.2⟩ := by
    apply ψ.injective
    simp only [j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, h1,
      mulAut_congr_conj, h2]
    ext q
    simp [ψ, suzConjT_apply, MulAut.conj_apply]
  exact congrArg Subtype.val h3

private theorem tabP_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 64)} (ht : Rep 64 t g) :
    tabP t = g := by
  have hc : (∀ i < 64, t[i]! < 64) ∧ ∀ i < 64, ∀ j < 64, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => ht.lt hi, fun i hi j hj hij => ?_⟩
    rw [ht.apply hi, ht.apply hj] at hij
    exact congrArg Fin.val (g.injective (Fin.ext hij))
  refine Equiv.ext fun x => Fin.ext ?_
  rw [tabP, permOfArr, dite_eq_left hc]
  exact ht x

private theorem oGens_get {j : ℕ} (hj : j < 10) : oGens[j]! = matTabs[j]! := by
  have h1 : j < matTabs.size := by rw [matTabs_size]; exact hj
  have h2 : j < (matTabs.push (mat64 (sTau ()))).size := by rw [Array.size_push]; omega
  rw [oGens, getElem!_pos (matTabs.push (mat64 (sTau ()))) j h2, getElem!_pos matTabs j h1,
    Array.getElem_push_lt h1]

private theorem oGens_ten : oGens[10]! = mat64 (sTau ()) := by
  have h : matTabs.size < (matTabs.push (mat64 (sTau ()))).size := by
    rw [Array.size_push]; omega
  rw [oGens, show (10 : ℕ) = matTabs.size from matTabs_size.symm,
    getElem!_pos (matTabs.push (mat64 (sTau ()))) matTabs.size h, Array.getElem_push_eq]

private theorem omega_le_O : Ω₁₀ ≤ O₁₁ := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j, by omega⟩, congrArg tabP (oGens_get j.2)⟩

private theorem tau_mem_O : tabP (mat64 (sTau ())) ∈ O₁₁ :=
  Subgroup.subset_closure ⟨⟨10, by norm_num⟩, congrArg tabP oGens_ten⟩

section Max


private theorem tauP_mem_centralizer : tauP ∈ Subgroup.centralizer {suzInv 1} :=
  Subgroup.mem_centralizer_singleton_iff.2 commute_facts.2.2.2.symm.eq

private theorem tauP_mem_suzT : tauP ∈ suzT :=
  suzT.mul_mem suzV_mem_suzT (suzM_le_suzT gens_mem.2.2.2)

private theorem tauP_mem_normalizer :
    tauP ∈ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) := by
  refine coord_qVec.mem_normalizer commute_facts.2.2.2.symm.eq fun i hi => ?_
  have hi64 : 2 ^ i < 64 :=
    calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
      _ = 64 := by norm_num
  obtain ⟨hlt, a, ha, he⟩ := conj_qVec_facts.2.2.2.1 (2 ^ i) hi64
  rw [he]
  exact coord_qVec.mem_Q_iff.2 ⟨_, hlt, a, ha, rfl⟩

private theorem mem_invE_or {c : Equiv.Perm (Fin 1782)} (hcT : c ∈ suzT)
    (hct : c ∈ Subgroup.centralizer {suzInv 1}) : c ∈ invE 1 ∨ tauP⁻¹ * c ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num)]
  rcases (mem_suzT_iff c).1 hcT with h | h
  · exact Or.inl (Subgroup.mem_inf.2 ⟨hct, h⟩)
  · refine Or.inr (Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ tauP_mem_centralizer)
      hct, ?_⟩)
    have e : tauP⁻¹ * c = mP⁻¹ * (suzV * c) := by
      rw [tauP, mul_inv_rev, suzV_inv, mul_assoc]
    rw [e]
    exact suzM.mul_mem (suzM.inv_mem gens_mem.2.2.2) h

private theorem mem_centralizer_of_mem_normalizer {c : Equiv.Perm (Fin 1782)}
    (hc : c ∈ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782)))) :
    c ∈ Subgroup.centralizer {suzInv 1} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hN := Subgroup.mem_normalizer_iff.1 hc
  have ht : c * suzInv 1 * c⁻¹ ∈ coord_qVec.Q := (hN _).1 coord_qVec.t_mem
  have hz : c * suzInv 1 * c⁻¹ ∈ Subgroup.zpowers (suzInv 1) := by
    refine (coord_qVec.forall_comm_iff ht).1 fun y hy => ?_
    have hy' : c⁻¹ * y * c ∈ coord_qVec.Q := by
      refine (hN _).2 ?_
      rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
    have h1 := (coord_qVec.forall_comm_iff coord_qVec.t_mem).2 (Subgroup.mem_zpowers _) _ hy'
    calc c * suzInv 1 * c⁻¹ * y = c * (suzInv 1 * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * suzInv 1) * c⁻¹ := by rw [h1]
      _ = y * (c * suzInv 1 * c⁻¹) := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h1 := zpow_mod_orderOf (suzInv 1) k
  rw [coord_qVec.orderOf_t, Nat.cast_ofNat] at h1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [h0, zpow_zero, hk] at h1
    exfalso
    apply coord_qVec.t_ne
    calc suzInv 1 = c⁻¹ * (c * suzInv 1 * c⁻¹) * c := by group
      _ = 1 := by rw [← h1]; group
  · rw [h0, zpow_one, hk] at h1
    calc c * suzInv 1 = c * suzInv 1 * c⁻¹ * c := by group
      _ = suzInv 1 * c := by rw [← h1]

private theorem exists_mem_normalizer {S : Subgroup (Equiv.Perm (Fin 1782))} (hS : IsPGroup 2 S)
    (hQS : coord_qVec.Q ≤ S) (hne : ¬ S ≤ coord_qVec.Q) :
    ∃ x ∈ S, x ∈ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ∧
      x ∉ coord_qVec.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.isNilpotent
  set Q' : Subgroup S := coord_qVec.Q.subgroupOf S
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : S) ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  refine ⟨y, y.2, Subgroup.mem_normalizer_fintype fun q hq => ?_,
    fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hyN ⟨q, hQS hq⟩).1 (Subgroup.mem_subgroupOf.2 hq)
  exact Subgroup.mem_subgroupOf.1 h1

section Rho

variable {K : Subgroup (Equiv.Perm (Fin 1782))}
  (hK : K ≤ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
    Subgroup.centralizer {suzInv 1})

private theorem rho_eq_rho1 (c : K) (hc : (c : Equiv.Perm (Fin 1782)) ∈ invE 1) :
    coord_qVec.rho hK c = rho1 ⟨c, hc⟩ := by
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨a, ha, rfl⟩ := coord_qVec.psi_surj u
  rw [coord_qVec.rho_psi hK c ha]
  exact (coord_qVec.rho_psi invE_le ⟨c, hc⟩ ha).symm

private theorem kappa_rho_eq (c : K) {tb : Array ℕ}
    (h : ∀ v < 64, tb[v]! < 64 ∧ ∃ a < 2,
      (c : Equiv.Perm (Fin 1782)) * qVec v * (c : Equiv.Perm (Fin 1782))⁻¹ =
        qVec tb[v]! * suzInv 1 ^ a)
    (hrep : Rep 64 tb (tabP tb)) : kappa (coord_qVec.rho hK c) = tabP tb := by
  refine Equiv.ext fun x => Fin.ext ?_
  obtain ⟨hlt, a, ha, hc⟩ := h x x.2
  rw [kappa_apply, ← coord_qVec.psi_q x.2, coord_qVec.rho_psi hK c (coord_qVec.q_mem x.2), hc,
    coord_qVec.psi_eq hlt ha, bitEquiv_symm_bitVec hlt]
  exact hrep x

private theorem rep_tau : Rep 64 (mat64 (sTau ())) (tabP (mat64 (sTau ()))) :=
  conj_qVec_facts.2.2.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

private theorem kappa_rho_tau (hτ : tauP ∈ K) :
    kappa (coord_qVec.rho hK ⟨tauP, hτ⟩) = tabP (mat64 (sTau ())) :=
  kappa_rho_eq hK ⟨tauP, hτ⟩ conj_qVec_facts.2.2.2.1 rep_tau

end Rho

private theorem kappa_rho1_mem_omega (c : ↥(invE 1)) : kappa (rho1 c) ∈ Ω₁₀ := by
  set S₀ : Set (Equiv.Perm (Fin 1782)) := {g | g ∈ (invInnerChain 1).original.toList} with hS₀
  have htop : Subgroup.closure (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hrange : rho1.range.map kappa =
      Subgroup.closure ((kappa.comp rho1) '' ((↑) ⁻¹' S₀)) := by
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_map, MonoidHom.map_closure]
  have hmem : kappa (rho1 c) ∈ rho1.range.map kappa := Subgroup.mem_map_of_mem _ ⟨c, rfl⟩
  rw [hrange] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk, hrep⟩ := gen_rep hg
  exact ⟨⟨k, hk⟩, tabP_eq_of_rep (tabRep_gen hk g hrep).2⟩

section Ker

variable {K : Subgroup (Equiv.Perm (Fin 1782))}
  (hK : K ≤ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
    Subgroup.centralizer {suzInv 1}) (hKT : K ≤ suzT) (hτ : tauP ∈ K) (hE : invE 1 ≤ K)

include hKT hτ hE

private theorem kappa_rho_mem_O (c : K) : kappa (coord_qVec.rho hK c) ∈ O₁₁ := by
  rcases mem_invE_or (hKT c.2) (hK c.2).2 with h | h
  · rw [rho_eq_rho1 hK c h]
    exact omega_le_O (kappa_rho1_mem_omega _)
  · have hc : c = ⟨tauP, hτ⟩ * ⟨tauP⁻¹ * c, hE h⟩ :=
      Subtype.ext (mul_inv_cancel_left tauP (c : Equiv.Perm (Fin 1782))).symm
    rw [hc, map_mul, map_mul, kappa_rho_tau hK hτ, rho_eq_rho1 hK ⟨tauP⁻¹ * c, hE h⟩ h]
    exact Subgroup.mul_mem _ tau_mem_O (omega_le_O (kappa_rho1_mem_omega _))

private theorem mem_Q_of_rho_eq_one (c : K) (h1 : coord_qVec.rho hK c = 1) :
    (c : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := by
  rcases mem_invE_or (hKT c.2) (hK c.2).2 with h | h
  · rw [rho_eq_rho1 hK c h] at h1
    have h2 : (⟨c, h⟩ : ↥(invE 1)) ∈ rho1.ker := MonoidHom.mem_ker.2 h1
    rw [ker_rho1] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  · exfalso
    have hc : c = ⟨tauP, hτ⟩ * ⟨tauP⁻¹ * c, hE h⟩ :=
      Subtype.ext (mul_inv_cancel_left tauP (c : Equiv.Perm (Fin 1782))).symm
    rw [hc, map_mul, mul_eq_one_iff_eq_inv, ← map_inv] at h1
    have h3 := congrArg kappa h1
    rw [kappa_rho_tau hK hτ, rho_eq_rho1 hK (⟨tauP⁻¹ * c, hE h⟩⁻¹) (inv_mem h)] at h3
    exact tau_not_mem_omega (by rw [h3]; exact kappa_rho1_mem_omega _)

end Ker

theorem eq_Q1_of_invariant (S : Subgroup (Equiv.Perm (Fin 1782))) (hST : S ≤ suzT)
    (hS : IsPGroup 2 S) (hB : B1 ≤ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 1782))))
    (hQS : coord_qVec.Q ≤ S) : S = coord_qVec.Q := by
  refine le_antisymm ?_ hQS
  by_contra hne
  obtain ⟨x, hxS, hxN, hxQ⟩ := exists_mem_normalizer hS hQS hne
  set K : Subgroup (Equiv.Perm (Fin 1782)) :=
    Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
      Subgroup.centralizer {suzInv 1} ⊓ suzT with hKdef
  have hK : K ≤ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
      Subgroup.centralizer {suzInv 1} := inf_le_left
  have hKT : K ≤ suzT := inf_le_right
  have hτ : tauP ∈ K := Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨tauP_mem_normalizer, tauP_mem_centralizer⟩, tauP_mem_suzT⟩
  have hE : invE 1 ≤ K := fun c hc =>
    Subgroup.mem_inf.2 ⟨invE_le hc, suzM_le_suzT (invE_le_centM (by norm_num) hc).2⟩
  have hxK : x ∈ K := Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨hxN, mem_centralizer_of_mem_normalizer hxN⟩, hST hxS⟩
  set φ : K →* Equiv.Perm (Fin 64) := kappa.comp (coord_qVec.rho hK) with hφ
  set TC : Subgroup K := S.comap K.subtype with hTC
  set SS : Subgroup (Equiv.Perm (Fin 64)) := TC.map φ with hSS
  have hSS2 : IsPGroup 2 SS := (hS.comap_subtype (K := K)).map φ
  have hSSne : SS ≠ ⊥ := by
    intro h
    have hmem : φ ⟨x, hxK⟩ ∈ SS := Subgroup.mem_map_of_mem φ (show (⟨x, hxK⟩ : K) ∈ TC from hxS)
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : coord_qVec.rho hK ⟨x, hxK⟩ = 1 :=
      kappa_injective (hmem.trans (map_one kappa).symm)
    exact hxQ (mem_Q_of_rho_eq_one hK hKT hτ hE _ h1)
  obtain ⟨X, hXS, hX1, hX2, hXc⟩ := exists_central_involution hSS2 hSSne
  have hnorm : ∀ b ∈ B1.comap K.subtype,
      φ b ∈ Subgroup.normalizer (SS : Set (Equiv.Perm (Fin 64))) :=
    fun b hb => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ
      (Subgroup.le_normalizer_comap K.subtype
        (Subgroup.mem_comap.2 (hB (Subgroup.mem_comap.1 hb)))))
  have hdK : dP ∈ K := hE gens_mem.1
  have hb2K : b2P ∈ K := hE gens_mem.2.1
  have hb3K : b3P ∈ K := hE gens_mem.2.2.1
  have hdB : (⟨dP, hdK⟩ : K) ∈ B1.comap K.subtype := Subgroup.mem_comap.2
    (show dP ∈ B1 from Subgroup.subset_closure (Set.mem_insert _ _))
  have hb2B : (⟨b2P, hb2K⟩ : K) ∈ B1.comap K.subtype := Subgroup.mem_comap.2
    (show b2P ∈ B1 from Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hb3B : (⟨b3P, hb3K⟩ : K) ∈ B1.comap K.subtype := Subgroup.mem_comap.2
    (show b3P ∈ B1 from Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hd : φ ⟨dP, hdK⟩ = tabP (mat64 (sD ())) :=
    kappa_rho_eq hK ⟨dP, hdK⟩ conj_qVec_facts.1 (conj_qVec_facts.2.2.2.2 _ List.mem_cons_self)
  have hb2 : φ ⟨b2P, hb2K⟩ = tabP (mat64 (sB2 ())) :=
    kappa_rho_eq hK ⟨b2P, hb2K⟩ conj_qVec_facts.2.1
      (conj_qVec_facts.2.2.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hb3 : φ ⟨b3P, hb3K⟩ = tabP (mat64 (sB3 ())) :=
    kappa_rho_eq hK ⟨b3P, hb3K⟩ conj_qVec_facts.2.2.1
      (conj_qVec_facts.2.2.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
  have hY1 : φ (⟨dP, hdK⟩ * ⟨b2P, hb2K⟩ * ⟨b3P, hb3K⟩ ^ 2) =
      tabP (mat64 (sD ())) * tabP (mat64 (sB2 ())) * tabP (mat64 (sB3 ())) ^ 2 := by
    rw [map_mul, map_mul, map_pow, hd, hb2, hb3]
  have hY2 : φ (⟨b2P, hb2K⟩ ^ 2 * ⟨b3P, hb3K⟩ ^ 2) =
      tabP (mat64 (sB2 ())) ^ 2 * tabP (mat64 (sB3 ())) ^ 2 := by
    rw [map_mul, map_pow, map_pow, hb2, hb3]
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hXS
  obtain ⟨y, hy, hyc⟩ := six4_facts (φ c) (kappa_rho_mem_O hK hKT hτ hE c) hX2 hX1
  have hyN : y ∈ Subgroup.normalizer (SS : Set (Equiv.Perm (Fin 64))) := by
    rcases hy with rfl | rfl
    · rw [← hY1]
      exact hnorm _ (mul_mem (mul_mem hdB hb2B) (pow_mem hb3B 2))
    · rw [← hY2]
      exact hnorm _ (mul_mem (pow_mem hb2B 2) (pow_mem hb3B 2))
  exact hyc (hXc _ ((Subgroup.mem_normalizer_iff.1 hyN _).1 hXS))

end Max

end CFSG.Sporadic.SuzI301
