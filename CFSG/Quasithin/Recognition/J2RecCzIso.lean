module

public import CFSG.Quasithin.Recognition.J2RecCzModel
public import CFSG.Quasithin.Recognition.J2RecAmalgam
public import CFSG.Quasithin.Recognition.J2RecLines

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv J2Cz J2Cz.QM

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem anti_of_sq {a b w : G} (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 2 = w)
    (hwa : w * a = a * w) : b * a = w * (a * b) := by
  have h1 : a * b * (a * b) = w := by rw [← sq]; exact hab
  calc b * a = a * (a * b * (a * b)) * b := by
        rw [show a * (a * b * (a * b)) * b = (a * a) * b * a * (b * b) by group, ha, hb]
        group
    _ = a * w * b := by rw [h1]
    _ = w * (a * b) := by rw [← hwa]; group

omit [Finite G] in
theorem J2FiveLines.liftRel {d : G} {x' : Fin 5 → G} (h : J2FiveLines d x') :
    LiftRel d (fun j : Fin 4 => x' j.succ) :=
  ⟨h.d_sq, fun j => (h.d_comm j.succ).eq, fun j => h.x_sq j.succ, fun _ _ hij =>
    anti_of_sq (h.x_sq _) (h.x_sq _) (h.sq_eq _ _ fun e => hij.ne (Fin.succ_injective _ e))
      (h.d_comm _).eq⟩

omit [Finite G] in
theorem liftT_mem {K : Subgroup G} {w : G} {y : Fin 4 → G} (hw : w ∈ K) (hy : ∀ j, y j ∈ K)
    (p : QM) : liftT w y p 1 ∈ K := by
  have hpw : ∀ (g : G) (t : F2), g ∈ K → pw g t ∈ K := fun g t hg => by
    cases t
    · exact K.one_mem
    · exact hg
  simp only [liftT, mul_one]
  exact K.mul_mem (hpw _ _ hw) (K.mul_mem (hpw _ _ (hy 0)) (K.mul_mem (hpw _ _ (hy 1))
    (K.mul_mem (hpw _ _ (hy 2)) (hpw _ _ (hy 3)))))

theorem card_QM : Nat.card QM = 32 := by
  rw [Nat.card_eq_fintype_card]
  rfl

namespace IsTypeH2

omit [Finite G] in
theorem exists_equiv_QM (h : IsTypeH2 G z) :
    ∃ χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM, (χ.symm (QM.z) : G) = z := by
  obtain ⟨x', hxQ, hfive, hcl⟩ := h.exists_fiveLines
  set Q := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQ
  have hrel := hfive.liftRel
  set φ0 := hrel.liftHom with hφ0
  have hmem : ∀ p, φ0 p ∈ Q := fun p =>
    liftT_mem h.z_mem_pCoreOf (fun j => hxQ j.succ) p
  set χ' : QM →* Q := φ0.codRestrict Q hmem with hχ'
  have hx : ∀ j, φ0 (QM.x j) = x' j := by
    have h14 : ∀ j : Fin 4, φ0 (QM.x j.succ) = x' j.succ := fun j => by
      rw [hφ0, LiftRel.liftHom_apply]
      fin_cases j <;> simp [liftT, QM.x]
    intro j
    refine Fin.cases ?_ (fun j => h14 j) j
    have h0 : QM.x 0 = QM.x 1 * QM.x 2 * QM.x 3 * QM.x 4 := by decide
    have hsq : φ0 (QM.x 0) * φ0 (QM.x 0) = 1 := by rw [← map_mul, QM.x_sq, map_one]
    have hp := hfive.prod_eq
    have e1 : φ0 (QM.x 1) = x' 1 := h14 0
    have e2 : φ0 (QM.x 2) = x' 2 := h14 1
    have e3 : φ0 (QM.x 3) = x' 3 := h14 2
    have e4 : φ0 (QM.x 4) = x' 4 := h14 3
    show φ0 (QM.x 0) = x' 0
    rw [h0, map_mul, map_mul, map_mul, e1, e2, e3, e4]
    rw [h0, map_mul, map_mul, map_mul, e1, e2, e3, e4] at hsq
    have e0 : x' 0 = (x' 1 * x' 2 * x' 3 * x' 4)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      exact hp
    rw [e0, inv_eq_of_mul_eq_one_right hsq]
  have hsurj : Function.Surjective χ' := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro q _
    have hq : (q : G) ∈ Subgroup.closure (Set.range x') := by rw [hcl]; exact q.2
    have hle : Subgroup.closure (Set.range x') ≤ φ0.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨QM.x j, hx j⟩
    obtain ⟨p, hp⟩ := hle hq
    exact ⟨p, Subtype.ext hp⟩
  have hcard : Nat.card QM = Nat.card Q := by rw [card_QM, h.card_pCoreOf]
  have hbij : Function.Bijective χ' :=
    ⟨(Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩ |>.1, hsurj⟩
  refine ⟨(MulEquiv.ofBijective χ' hbij).symm, ?_⟩
  rw [MulEquiv.symm_symm, MulEquiv.ofBijective_apply]
  show φ0 QM.z = z
  rw [hφ0, LiftRel.liftHom_apply]
  simp [liftT, QM.z]

end IsTypeH2

theorem closure_pa_pb : Subgroup.closure ({pa, pb} : Set (Perm (Fin 5))) =
    alternatingGroup (Fin 5) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  set a' : alternatingGroup (Fin 5) := ⟨pa, pa_mem⟩
  set b' : alternatingGroup (Fin 5) := ⟨pb, pb_mem⟩
  set X := Subgroup.closure ({a', b'} : Set (alternatingGroup (Fin 5))) with hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb : orderOf b' = 3 := orderOf_eq_prime (Subtype.ext (by
      show pb ^ 3 = 1
      rw [pow_succ, sq, pb_cube]))
    (fun h1 => pb_ne_one (congrArg Subtype.val h1))
  have hab : orderOf (a' * b') = 5 := orderOf_eq_prime (Subtype.ext (by
      show (pa * pb) ^ 5 = 1
      exact papb_pow_five))
    (fun h1 => papb_ne_one (congrArg Subtype.val h1))
  have h3 : 3 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    rwa [hb] at this
  have h5 : 5 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (X.mul_mem (Subgroup.subset_closure
      (Set.mem_insert _ _)) (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    rwa [hab] at this
  have hXtop : X = ⊤ := subgroup_eq_top_of_fifteen_dvd h60
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5)
  have hmap := congrArg (Subgroup.map (alternatingGroup (Fin 5)).subtype) hXtop
  rw [hX, MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap
  exact hmap

attribute [local instance] CFSG.LieType.BorelTits.pCore_normal

theorem nonempty_mulEquiv_model_of_complement {P K : Subgroup G}
    (hQ : Nonempty (↥(pCoreOf 2 P) ≃* QM)) (hchar : CharTwo P) (hP : Nat.card P = 1920)
    (hKP : K ≤ P) (hKQ : K ⊓ pCoreOf 2 P = ⊥) (hK : Nat.card K = 60) :
    Nonempty (↥P ≃* Model) := by
  classical
  set N := CFSG.Open.pCore 2 ↥P with hN
  set K' := K.subgroupOf P with hK'
  obtain ⟨χQ⟩ := hQ
  set χN : ↥N ≃* QM :=
    (N.equivMapOfInjective P.subtype P.subtype_injective).trans (χQ : ↥(N.map P.subtype) ≃* QM)
    with hχN
  have hQcard : Nat.card (pCoreOf 2 P) = 32 := by
    rw [Nat.card_congr χQ.toEquiv, card_QM]
  have hNcard : Nat.card N = 32 := by
    rw [Nat.card_congr (N.equivMapOfInjective P.subtype P.subtype_injective).toEquiv]
    exact hQcard
  have hKcard : Nat.card K' = 60 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, hK]
  have hdisj : Disjoint N K' := by
    rw [Subgroup.disjoint_def]
    intro n hnN hnK
    have h1 : (n : G) ∈ K ⊓ pCoreOf 2 P := ⟨hnK, ⟨n, hnN, rfl⟩⟩
    rw [hKQ, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hcomp : N.IsComplement' K' := Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [hNcard, hKcard, hP]) hdisj
  set φ₁ : ↥K' →* MulAut ↥N :=
    (N.normalizerMonoidHom).comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top)) with hφ₁
  have hφ₁ : ∀ (k : K') (n : N), ((φ₁ k n : N) : P) = (k : P) * n * (k : P)⁻¹ := fun k n => by
    rw [hφ₁, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  set ψ : ↥K' →* MulAut QM := (MulAut.congr χN).toMonoidHom.comp φ₁ with hψ
  have hψ : ∀ (k : K') (p : QM), ψ k p = χN (φ₁ k (χN.symm p)) := fun k p => rfl
  set lam : ↥K' →* Perm (Fin 5) := linePermHom.comp ψ with hlam
  have hlam_inj : Function.Injective lam := by
    rw [injective_iff_map_eq_one]
    intro k hk
    obtain ⟨q, hq⟩ := eq_conj_of_linePerm_eq_one hk
    set q' : N := χN.symm q with hq'
    have hcomm : ∀ n : N, (k : P) * n * (k : P)⁻¹ = (q' : P) * n * (q' : P)⁻¹ := fun n => by
      have h1 : χN (φ₁ k n) = χN (q' * n * q'⁻¹) := by
        have := DFunLike.congr_fun hq (χN n)
        rw [hψ, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
        rw [this, map_mul, map_mul, map_inv, hq', MulEquiv.apply_symm_apply]
      rw [← hφ₁, χN.injective h1]
      rfl
    have hgQ : ((q' : P) : G)⁻¹ * ((k : P) : G) ∈ pCoreOf 2 P := by
      apply hchar
      refine ⟨P.mul_mem (P.inv_mem (q' : P).2) (k : P).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨n, hn, rfl⟩
      have h1 := hcomm ⟨n, hn⟩
      have h2 : (q' : P)⁻¹ * (k : P) * n = n * ((q' : P)⁻¹ * (k : P)) := by
        calc (q' : P)⁻¹ * (k : P) * n
            = (q' : P)⁻¹ * ((k : P) * n * (k : P)⁻¹) * (k : P) := by group
          _ = (q' : P)⁻¹ * ((q' : P) * n * (q' : P)⁻¹) * (k : P) := by rw [h1]
          _ = n * ((q' : P)⁻¹ * (k : P)) := by group
      have h3 := congrArg Subtype.val h2
      simpa [mul_assoc] using h3.symm
    have hkQ : ((k : P) : G) ∈ pCoreOf 2 P := by
      have := (pCoreOf 2 P).mul_mem (⟨(q' : P), q'.2, rfl⟩ : ((q' : P) : G) ∈ pCoreOf 2 P) hgQ
      simpa using this
    have hkL : ((k : P) : G) ∈ K ⊓ pCoreOf 2 P := ⟨k.2, hkQ⟩
    rw [hKQ, Subgroup.mem_bot] at hkL
    exact Subtype.ext (Subtype.ext hkL)
  have hlam_range : lam.range = alternatingGroup (Fin 5) := by
    apply Perm.eq_alternatingGroup_of_index_eq_two
    have h1 := lam.range.card_mul_index
    rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl] at h1
    have h2 : Nat.card lam.range = 60 := by
      rw [← hKcard]
      exact (Nat.card_congr (MonoidHom.ofInjective hlam_inj).toEquiv).symm
    rw [h2] at h1
    omega
  obtain ⟨ka, hka⟩ : pa ∈ lam.range := hlam_range ▸ pa_mem
  obtain ⟨kb, hkb⟩ : pb ∈ lam.range := hlam_range ▸ pb_mem
  have hka2 : ka * ka = 1 := hlam_inj (by rw [map_mul, hka, pa_sq, map_one])
  have hkb3 : kb * kb * kb = 1 := hlam_inj (by rw [map_mul, map_mul, hkb, pb_cube, map_one])
  have hA : ∀ j, ψ ka (x j) = x (pa j) ∨ ψ ka (x j) = QM.z * x (pa j) := fun j => by
    have := linePerm_spec (ψ ka) j
    rwa [show linePerm (ψ ka) = pa from hka] at this
  have hB : ∀ j, ψ kb (x j) = x (pb j) ∨ ψ kb (x j) = QM.z * x (pb j) := fun j => by
    have := linePerm_spec (ψ kb) j
    rwa [show linePerm (ψ kb) = pb from hkb] at this
  obtain ⟨g, hgA, hgB⟩ := exists_conj_eq_phi hA hB
    (by rw [← map_mul, hka2, map_one]) (by rw [← map_mul, ← map_mul, hkb3, map_one])
  set χ' : ↥N ≃* QM := χN.trans g with hχ'
  set eK : ↥K' →* MulAut QM := (MulAut.congr χ').toMonoidHom.comp φ₁ with heK
  have heK : ∀ k, eK k = g * ψ k * g⁻¹ := fun k => MulEquiv.ext fun p => rfl
  have hM : L0.comap eK = ⊤ := by
    have hle : Subgroup.closure {ka, kb} ≤ L0.comap eK := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        show eK ka ∈ L0
        rw [heK, hgA]
        exact phiA_mem
      · rw [Set.mem_singleton_iff.mp hy]
        show eK kb ∈ L0
        rw [heK, hgB]
        exact phiB_mem
    have hcl : (Subgroup.closure {ka, kb}).map lam = alternatingGroup (Fin 5) := by
      rw [MonoidHom.map_closure, Set.image_pair, hka, hkb, closure_pa_pb]
    have hcard : Nat.card (Subgroup.closure ({ka, kb} : Set K')) = 60 := by
      rw [← Subgroup.card_map_of_injective hlam_inj, hcl, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have htop : Subgroup.closure ({ka, kb} : Set K') = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hKcard])
    exact eq_top_iff.mpr (htop ▸ hle)
  set eK' : ↥K' →* ↥L0 := eK.codRestrict L0 (fun k => by
    have : k ∈ L0.comap eK := hM ▸ Subgroup.mem_top k
    exact this) with heK'
  have heK'_inj : Function.Injective eK' := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : eK k = 1 := congrArg Subtype.val hk
    rw [heK] at h1
    have h2 : ψ k = 1 := by
      calc ψ k = g⁻¹ * (g * ψ k * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact hlam_inj (by rw [map_one]; show linePermHom (ψ k) = 1; rw [h2, map_one])
  have heK'_bij : Function.Bijective eK' := by
    have hle := Nat.card_le_card_of_injective _ heK'_inj
    rw [hKcard] at hle
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨heK'_inj, ?_⟩
    rw [hKcard]
    exact (le_antisymm card_L0_le hle).symm
  set eKe : ↥K' ≃* ↥L0 := MulEquiv.ofBijective eK' heK'_bij with heKe
  refine ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm.trans
    (SemidirectProduct.congr χ' eKe fun k => MulEquiv.ext fun n => ?_)⟩
  show χ' (φ₁ k n) = ((MulAut.congr χ') (φ₁ k)) (χ' n)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

namespace IsTypeH2

theorem nonempty_mulEquiv_model (h : IsTypeH2 G z) {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLQ : L ⊓ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) (hL : Nat.card L = 60) :
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* Model) := by
  obtain ⟨χQ, -⟩ := h.exists_equiv_QM
  exact nonempty_mulEquiv_model_of_complement (P := Subgroup.centralizer ({z} : Set G))
    (K := L) ⟨χQ⟩ h.charTwo h.card_centralizer hLC hLQ hL

end IsTypeH2

end CFSG.Quasithin
