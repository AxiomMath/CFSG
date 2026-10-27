module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Basic
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Conj

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_chiefStep_not_twoResidual_le {H X Z : Subgroup G} (hX : IsNormalIn H X X)
    (hZ : IsNormalIn H X Z) (hXX : ⁅X, X⁆ ≤ Z) (hsq : ∀ x ∈ X, x * x ∈ Z)
    (hnot : ¬ twoResidual H ≤ centralizerMod Z H X) :
    ∃ L N : Subgroup G, IsChiefStep H X L N ∧ Z ≤ L ∧
      ¬ twoResidual H ≤ centralizerMod L H N := by
  classical
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := D14.le_normalizer_of_isNormalIn hZ
  obtain ⟨N, -, ⟨hNn, hZN, hNnot⟩, hNmin⟩ := A4.exists_minimal_le_subgroup
    (p := fun K : Subgroup G => IsNormalIn H X K ∧ Z ≤ K ∧
      ¬ twoResidual H ≤ centralizerMod Z H K) (a := X) ⟨hX, hZ.1, hnot⟩
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hNn
  have hZltN : Z < N := by
    refine lt_of_le_of_ne hZN ?_
    rintro rfl
    refine hNnot fun h hh => ⟨twoResidual_le H hh, hHZ (twoResidual_le H hh), fun u hu => ?_⟩
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHZ (twoResidual_le H hh)) u).mp hu)
      (Z.inv_mem hu)
  obtain ⟨L, hZL, ⟨hLn, -, hLN⟩, hLmax⟩ := Finite.exists_le_maximal
    (p := fun K : Subgroup G => IsNormalIn H X K ∧ Z ≤ K ∧ K < N) (a := Z) ⟨hZ, le_rfl, hZltN⟩
  have hstep : IsChiefStep H X L N := by
    refine ⟨hNn, hLn, hLN, fun K hK hLK hKN => ?_⟩
    by_cases hKN' : K = N
    · exact Or.inr hKN'
    · exact Or.inl (le_antisymm (hLmax ⟨hK, hZL.trans hLK, lt_of_le_of_ne hKN hKN'⟩ hLK) hLK)
  refine ⟨L, N, hstep, hZL, fun hcent => ?_⟩
  have hLcent : twoResidual H ≤ centralizerMod Z H L := by
    by_contra hc
    exact hLN.ne (le_antisymm hLN.le (hNmin ⟨hLn, hZL, hc⟩ hLN.le))
  have hNX : N ≤ X := hNn.1
  refine hNnot (twoResidual_le_of_isTwoQuotient (centralizerMod_le_left _ _ _)
    (le_normalizer_centralizerMod hHZ Subgroup.le_normalizer hHN) fun y hy => ?_)
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have hy'H : y ^ 2 ^ k ∈ H := H.pow_mem hy _
  have hord' : orderOf (y ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hodd : Odd (orderOf (y ^ 2 ^ k)) := hord' ▸ hm
  have hy'R : y ^ 2 ^ k ∈ twoResidual H := F6.mem_twoResidual_of_odd hy'H hodd
  refine ⟨hy'H, hHZ hy'H, ?_⟩
  exact CFSG.GroupTheory.commutator_mem_of_odd_pow (X := N) (Y := Z) (W := L) hLN.le hZN
    ((Subgroup.commutator_mono hNX hNX).trans hXX) (fun x hx => hsq x (hNX hx)) (hHZ hy'H)
    (fun w hw => (hLcent hy'R).2.2 w hw) (fun x hx => (hcent hy'R).2.2 x hx) hodd
    (fun x _ => by rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, mul_inv_cancel]; exact Z.one_mem)

section Vertex

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_pCoreOf_sup_left (hfr : Str83G4Frame L1 L2 S a) :
    pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  rw [sup_eq_of_S_eq hS1]
  exact pCoreOf_sup_pCoreOf hF.1

theorem str83G4_q1_le_s (hfr : Str83G4Frame L1 L2 S a) :
    Q1 L1 L2 S ≤ S := by
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  conv_rhs => rw [hS1]
  exact le_sup_right

theorem str83G4_isSylowTwoOf_sup_left
    (hfr : Str83G4Frame L1 L2 S a) : IsSylowTwoOf S (L1 ⊔ S) := by
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  rw [sup_eq_of_S_eq hS1]
  exact isSylowTwoOf_sup_pCoreOf hF.1 hS1

theorem sup_left_le_p1 (L1 L2 S : Subgroup G) : L1 ⊔ S ≤ P1 L1 L2 S :=
  sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)

theorem str83G4_exists_equiv_sylow
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hfr : Str83G4Frame L1 L2 S a) :
    ∃ e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K,
      (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K := by
  classical
  have hSyl1 := str83G4_isSylowTwoOf_sup_left hfr
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  let e0 : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K :=
    (F112R.oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans (eSz.trans (suzukiGroupEquivSz a K hK).symm))
  have hSylTop : IsSylowTwoOf (S.subgroupOf (L1 ⊔ S)) ⊤ :=
    CFSG.Quasithin.H13.NQCat.A314D.isSylowTwoOf_top_subgroupOf hSyl1
  have hP : IsSylowTwoOf ((szSbar L1 L2 S).map e0.toMonoidHom) ⊤ := by
    have h := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylTop
      (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) (QuotientGroup.mk'_surjective _)
    exact CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective h e0.toMonoidHom e0.surjective
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hP hU
  refine ⟨e0.trans (MulAut.conj g), ?_⟩
  have hmap : (szSbar L1 L2 S).map (e0.trans (MulAut.conj g)).toMonoidHom =
      ((szSbar L1 L2 S).map e0.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [show (e0.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e0.toMonoidHom from rfl, ← Subgroup.map_map]
  rw [hmap, hg]
  rfl

theorem bigB_le_normalizer_z2 (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
  (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
    (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)))

theorem le_normalizer_centralizerMod_bigB (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ Subgroup.normalizer
      (centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S) (str83X L1 L2 S) : Set G) :=
  le_normalizer_centralizerMod (bigB_le_normalizer_z2 L1 L2 S)
    ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
    ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S))

theorem str83G4_exists_lift_bigB
    {K : Type} [Field K] [Finite K] (hfr : Str83G4Frame L1 L2 S a)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K)
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K) {g : suzukiGroup a K}
    (hg : g ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K))) :
    ∃ h : ↥(L1 ⊔ S), (h : G) ∈ bigB L1 L2 S ∧ e (QuotientGroup.mk h) = g := by
  have hpc := str83G4_pCoreOf_sup_left hfr
  have hQ1S := str83G4_q1_le_s hfr
  obtain ⟨hF, hB, -, -, -, -⟩ := hfr
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hhg : e (QuotientGroup.mk h) = g := by rw [hh, MulEquiv.apply_symm_apply]
  refine ⟨h, ?_, hhg⟩
  have hNS : (h : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hmaps : ∀ s ∈ S, (h : G) * s * (h : G)⁻¹ ∈ S := by
      intro s hs
      let s' : ↥(L1 ⊔ S) := ⟨s, (le_sup_right : S ≤ L1 ⊔ S) hs⟩
      have hsU : e (QuotientGroup.mk s') ∈ suzukiU a K := by
        rw [← he]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr hs))
      have hcU : e (QuotientGroup.mk (h * s' * h⁻¹)) ∈ suzukiU a K := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
          map_inv, hhg]
        exact (Subgroup.mem_normalizer_iff.mp hg _).mp hsU
      rw [← he] at hcU
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hcU
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy
      have hyq : (QuotientGroup.mk t : oTwoQuot ↥(L1 ⊔ S)) =
          QuotientGroup.mk (h * s' * h⁻¹) := by
        have := e.injective hye
        rw [← hty] at this
        exact this
      have hmem : t⁻¹ * (h * s' * h⁻¹) ∈ pCore 2 ↥(L1 ⊔ S) := QuotientGroup.eq.mp hyq
      have hmemG : ((t⁻¹ * (h * s' * h⁻¹) : ↥(L1 ⊔ S)) : G) ∈ Q1 L1 L2 S := by
        rw [← hpc]
        exact Subgroup.mem_map_of_mem _ hmem
      have htS : (t : G) ∈ S := Subgroup.mem_subgroupOf.mp ht
      have hprod : (h : G) * s * (h : G)⁻¹ =
          (t : G) * ((t⁻¹ * (h * s' * h⁻¹) : ↥(L1 ⊔ S)) : G) := by
        simp [s', mul_assoc]
      rw [hprod]
      exact S.mul_mem htS (hQ1S hmemG)
    have hsurj : ∀ s ∈ S, ∃ x ∈ S, (h : G) * x * (h : G)⁻¹ = s := by
      intro s hs
      have hinj : Function.Injective
          fun x : ↥S => (⟨(h : G) * x * (h : G)⁻¹, hmaps x x.2⟩ : ↥S) :=
        fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy)
      obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨s, hs⟩
      exact ⟨x, x.2, congrArg Subtype.val hx⟩
    refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hmaps s hs, fun hs => ?_⟩
    obtain ⟨x, hx, hxs⟩ := hsurj _ hs
    have hxeq : x = s := by simpa using hxs
    exact hxeq ▸ hx
  exact str86_p1_inf_normalizer_le_bigB hF hB
    (Subgroup.mem_inf.mpr ⟨sup_left_le_p1 L1 L2 S h.2, hNS⟩)

theorem str83X_mul_self_mem_z1
    (hfr : Str83G4Frame L1 L2 S a) : ∀ x ∈ str83X L1 L2 S, x * x ∈ Z1 L1 L2 S := by
  have hXX : ⁅str83X L1 L2 S, str83X L1 L2 S⁆ ≤ Z1 L1 L2 S :=
    (Subgroup.commutator_mono le_rfl (str83X_le_q1 hfr)).trans (str83G4_commutator_x_q1_le hfr)
  let Sq : Subgroup G :=
    { carrier := {x | x ∈ str83X L1 L2 S ∧ x * x ∈ Z1 L1 L2 S}
      mul_mem' := by
        rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
        refine ⟨(str83X L1 L2 S).mul_mem hx hy, ?_⟩
        have hc : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ ∈ Z1 L1 L2 S :=
          hXX (Subgroup.commutator_mem_commutator ((str83X L1 L2 S).inv_mem hx) hy)
        have e : x * y * (x * y) = x * x * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹) * (y * y) := by group
        rw [e]
        exact (Z1 L1 L2 S).mul_mem ((Z1 L1 L2 S).mul_mem hxx hc) hyy
      one_mem' := ⟨(str83X L1 L2 S).one_mem, by simpa using (Z1 L1 L2 S).one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hxx⟩
        refine ⟨(str83X L1 L2 S).inv_mem hx, ?_⟩
        have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        rw [e]
        exact (Z1 L1 L2 S).inv_mem hxx }
  have hle : str83X L1 L2 S ≤ Sq := by
    refine conjClosure_le fun h hh z hz => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hh) z).mp
        (z2_le_str83X L1 L2 S hz)
    · have hz2 : z * z = 1 := by
        rw [← sq]
        exact (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 z hz
      have e : h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
      rw [e, hz2, mul_one, mul_inv_cancel]
      exact (Z1 L1 L2 S).one_mem
  exact fun x hx => (hle hx).2

theorem str83G4_exists_chiefStep
    (hfr : Str83G4Frame L1 L2 S a) :
    ∃ L N : Subgroup G, IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) L N ∧ Z1 L1 L2 S ≤ L ∧
      ¬ twoResidual (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N := by
  have hHX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  have hZ1X : Z1 L1 L2 S ≤ str83X L1 L2 S := (str83G4_z1_le_center_x hfr).trans inf_le_left
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
    exact (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  refine exists_chiefStep_not_twoResidual_le
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHX hg) x).mp hx⟩
    ⟨hZ1X, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHZ1 hg) x).mp hx⟩
    ((Subgroup.commutator_mono le_rfl (str83X_le_q1 hfr)).trans (str83G4_commutator_x_q1_le hfr))
    (str83X_mul_self_mem_z1 hfr) fun hle => str83G4_not_le_normalizer_z2 hfr ?_
  have hconj : ∀ y ∈ twoResidual (L1 ⊔ S), ∀ z ∈ Z2 L1 L2 S, y * z * y⁻¹ ∈ Z2 L1 L2 S := by
    intro y hy z hz
    have h1 : y * z * y⁻¹ * z⁻¹ ∈ Z2 L1 L2 S :=
      hZ1Z2 ((hle hy).2.2 z (z2_le_str83X L1 L2 S hz))
    have e : y * z * y⁻¹ = y * z * y⁻¹ * z⁻¹ * z := by group
    rw [e]
    exact (Z2 L1 L2 S).mul_mem h1 hz
  have hRN : twoResidual (L1 ⊔ S) ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨fun hz => hconj y hy z hz, fun hz => ?_⟩
    have := hconj y⁻¹ ((twoResidual (L1 ⊔ S)).inv_mem hy) _ hz
    simpa [mul_assoc] using this
  have hSN : S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (bigB_le_normalizer_z2 L1 L2 S)
  rw [← sup_twoResidual_eq (str83G4_isSylowTwoOf_sup_left hfr)]
  exact sup_le hSN hRN

end Vertex

end CFSG.Quasithin.Stroth

end
