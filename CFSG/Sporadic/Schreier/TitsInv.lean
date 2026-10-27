module

public import CFSG.Sporadic.Schreier.TitsInvCheck
public import CFSG.LieType.Ree.TitsSylowLocalSchreier
public import CFSG.Sporadic.Schreier.TitsAbel
public import CFSG.Sporadic.Schreier.TitsPair

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.ChainArrays CFSG.LieType.Chevalley CFSG.LieType.Ree

section GroupTheory

variable {G : Type*} [Group G]

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hx : IsPGroup p (Subgroup.zpowers x)) : ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : x ∈ ((g • P : Sylow p G) : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [coe_smul_sylow_eq_map] at hmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
  refine ⟨g⁻¹, ?_⟩
  rw [← hyx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  simpa [mul_assoc] using hy

theorem isPGroup_zpowers_of_orderOf_two {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem index_centralizer_eq_ncard (x : G) :
    (Subgroup.centralizer {x}).index = {y | IsConj x y}.ncard := by
  have h1 : (Subgroup.centralizer {x}).index = (MulAction.stabilizer (ConjAct G) x).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective
  rw [h1, MulAction.index_stabilizer]
  congr 1
  ext y
  simp only [ConjAct.mem_orbit_conjAct, Set.mem_ofPred_eq]
  exact isConj_comm

theorem map_conj_centralizer (g y : G) :
    (Subgroup.centralizer {y}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * y * g⁻¹} := by
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    calc g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
      _ = g * (y * u) * g⁻¹ := by rw [hu]
      _ = g * y * g⁻¹ * (g * u * g⁻¹) := by group
  · intro hw
    refine ⟨g⁻¹ * w * g, ?_, by group⟩
    calc g⁻¹ * w * g * y = g⁻¹ * (w * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * w) * g := by rw [hw]
      _ = y * (g⁻¹ * w * g) := by group

theorem map_subtype_centralizer {D : Subgroup G} (y : D) :
    (Subgroup.centralizer {y}).map D.subtype = D ⊓ Subgroup.centralizer {(y : G)} := by
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, congrArg Subtype.val hu⟩
  · rintro ⟨hw, hc⟩
    exact ⟨⟨w, hw⟩, Subtype.ext hc, rfl⟩

@[expose] def NoOddNormal (G : Type*) [Group G] : Prop :=
  ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥

theorem NoOddNormal.of_equiv {H : Type*} [Group H] (e : G ≃* H) (h : NoOddNormal H) :
    NoOddNormal G := by
  intro R hR hodd
  have hR' : (R.map e.toMonoidHom).Normal := hR.map _ e.surjective
  have hc : Nat.card (R.map e.toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective e.injective
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 (h _ hR' (hc ▸ hodd))

theorem noOddNormal_of_two_core [Finite G] {J : Subgroup G} [J.Normal] {k : ℕ}
    (hJ : Nat.card J = 2 ^ k) (hC : Subgroup.centralizer (J : Set G) ≤ J) : NoOddNormal G := by
  intro R hR hodd
  have hcop : Nat.Coprime (Nat.card R) (Nat.card J) := by
    rw [hJ]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hRJ : R ⊓ J = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    exact Nat.eq_one_of_dvd_coprimes hcop (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
  have hcomm : ⁅R, J⁆ = ⊥ := le_bot_iff.1 (hRJ ▸ Subgroup.commutator_le_inf R J)
  have hle : R ≤ J := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans hC
  rw [← hRJ, inf_of_le_left hle]

end GroupTheory

@[expose] def titsTInv : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsTWord

theorem titsTInv_rep :
    Rep 1755 titsTArr titsTInv :=
  rep_wordArr_titsT titsInv_check.1

theorem titsTInv_mem_titsD : titsTInv ∈ titsD :=
  wordIn_titsT_mem_titsD _

theorem mem_titsK_iff_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inK a = true ↔ g ∈ titsK := by
  rw [← titsQK_facts.2.2.1]
  exact siftA_iff_mem_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.2.1 ha

theorem titsTInv_mem_titsK :
    titsTInv ∈ titsK :=
  (mem_titsK_iff_sift titsTInv_rep).1 titsInv_check.2.1

theorem titsTInv_ne_one :
    titsTInv ≠ 1 := by
  intro h
  have := (eqA_iff titsTInv_rep rep_idA).2 h
  rw [titsInv_check.2.2.1] at this
  exact Bool.false_ne_true this

theorem titsTInv_mul_self :
    titsTInv * titsTInv = 1 :=
  eq_of_eqA (rep_compA titsTInv_rep titsTInv_rep) rep_idA titsInv_check.2.2.2.1

theorem orderOf_titsTInv :
    orderOf titsTInv = 2 :=
  orderOf_eq_prime (by rw [sq]; exact titsTInv_mul_self) titsTInv_ne_one

@[expose] def titsZD : titsD := ⟨titsZ, titsZ_mem_titsD⟩

@[expose] def titsTD : titsD := ⟨titsTInv, titsTInv_mem_titsD⟩

theorem orderOf_titsZD :
    orderOf titsZD = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_titsZ

theorem orderOf_titsTD :
    orderOf titsTD = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_titsTInv

theorem titsGen1_rep :
    Rep 1755 titsGenArrs[1]! (titsGen 1) := titsGen_rep (by norm_num)

theorem rep_conjArr {g x : Array ℕ} {u v : Equiv.Perm (Fin 1755)} (hg : Rep 1755 g u)
    (hgi : isInvA 1755 g (invCand 1755 g) = true) (hx : Rep 1755 x v) :
    Rep 1755 (conjArr g x) (u * v * u⁻¹) :=
  rep_compA (rep_compA hg hx) (rep_inv_of_isInvA hg hgi)

theorem titsGen1_conj_S :
    ∀ s ∈ titsS, titsGen 1 * s * (titsGen 1)⁻¹ ∈ titsS := by
  have hle : titsS ≤ titsS.comap (MulAut.conj (titsGen 1)).toMonoidHom := by
    conv_lhs => rw [titsS_eq_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_titsS_iff_sift (rep_conjArr titsGen1_rep (titsGen_inv (by norm_num))
      (titsSGen_rep b.2))).1 (titsInv_check.2.2.2.2.1 b b.2)
  intro s hs
  have := Subgroup.mem_comap.1 (hle hs)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem titsGen1_mem_normalizer :
    titsGen 1 ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755))) :=
  mem_normalizer_of_conj titsGen1_conj_S

theorem titsGen1_conj_inv_S
    {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsS) :
    (titsGen 1)⁻¹ * s * titsGen 1 ∈ titsS := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem titsGen1_mem_normalizer) s).1 hs
  rwa [inv_inv] at this

theorem titsGen1_sq_mem :
    titsGen 1 * titsGen 1 ∈ titsS :=
  (mem_titsS_iff_sift (rep_compA titsGen1_rep titsGen1_rep)).1 titsInv_check.2.2.2.2.2.1

theorem titsGen1_not_mem :
    titsGen 1 ∉ titsS := fun h => by
  have := (mem_titsS_iff_sift titsGen1_rep).2 h
  rw [titsInv_check.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem titsGen1_mul_sq_ne
    {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsS) :
    s * titsGen 1 * (s * titsGen 1) ≠ 1 := by
  have hsQ : s ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hs
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 (by show (finList 1755 titsSBase).length = 5; simp [finList,
      titsCentral_check.1]) titsInv_check.2.2.2.2.2.2.2 hsQ
  intro h
  have h1 := rep_compA (rep_compA ha titsGen1_rep) (rep_compA ha titsGen1_rep)
  rw [(eqA_iff h1 rep_idA).2 h] at hp
  exact Bool.false_ne_true hp

@[expose] def titsPA :
    Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {x | x ∈ titsS ∨ x * (titsGen 1)⁻¹ ∈ titsS}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have : x * y * (titsGen 1)⁻¹ = x * (titsGen 1)⁻¹ * (titsGen 1 * y * (titsGen 1)⁻¹) := by
        group
      rw [this]
      exact mul_mem hx (titsGen1_conj_S y hy)
    · refine Or.inl ?_
      have : x * y = x * (titsGen 1)⁻¹ * (titsGen 1 * (y * (titsGen 1)⁻¹) * (titsGen 1)⁻¹) *
          (titsGen 1 * titsGen 1) := by group
      rw [this]
      exact mul_mem (mul_mem hx (titsGen1_conj_S _ hy)) titsGen1_sq_mem
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have : x⁻¹ * (titsGen 1)⁻¹ = (titsGen 1)⁻¹ * (x * (titsGen 1)⁻¹)⁻¹ * titsGen 1 *
          (titsGen 1 * titsGen 1)⁻¹ := by group
      rw [this]
      exact mul_mem (titsGen1_conj_inv_S (inv_mem hx)) (inv_mem titsGen1_sq_mem)

theorem coe_titsPA :
    (titsPA : Set (Equiv.Perm (Fin 1755))) =
    (titsS : Set (Equiv.Perm (Fin 1755))) ∪ (fun s => s * titsGen 1) '' titsS := by
  ext x
  simp only [Set.mem_union, SetLike.mem_coe, Set.mem_image]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨_, h, by group⟩
  · rintro (h | ⟨s, hs, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [mul_inv_cancel_right]; exact hs)

theorem card_titsPA :
    Nat.card titsPA = 4096 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, coe_titsPA]
  have hdisj : Disjoint (titsS : Set (Equiv.Perm (Fin 1755)))
      ((fun s => s * titsGen 1) '' titsS) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨s, hs, rfl⟩
    apply titsGen1_not_mem
    have := mul_mem (inv_mem hs) hx
    rwa [inv_mul_cancel_left] at this
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (mul_left_injective (titsGen 1)), ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, titsQS_facts.2.2.2]

theorem titsPA_le_titsA :
    titsPA ≤ titsA := by
  rintro x (hx | hx)
  · exact titsD_le_titsA (titsS_le_titsD hx)
  · have := mul_mem (titsD_le_titsA (titsS_le_titsD hx)) (titsGen_mem_titsA (by norm_num : 1 < 4))
    rwa [inv_mul_cancel_right] at this

@[expose] def titsPASylow :
    Sylow 2 titsA :=
  (IsPGroup.of_card (n := 12) (by rw [card_subgroupOf_eq titsPA_le_titsA, card_titsPA]; norm_num) :
    IsPGroup 2 (titsPA.subgroupOf titsA)).toSylow (by
      have h := Subgroup.card_mul_index (titsPA.subgroupOf titsA)
      rw [card_subgroupOf_eq titsPA_le_titsA, card_titsPA, card_titsA] at h
      have : (titsPA.subgroupOf titsA).index = 8775 := by omega
      rw [this]
      decide)

theorem titsD_normal_A : (titsD.subgroupOf titsA).Normal :=
  Subgroup.normal_of_index_eq_two titsD_index

theorem titsA_involution_mem_D
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsA)
    (h2 : orderOf x = 2) : x ∈ titsD := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (p := 2) titsPASylow (x := ⟨x, hx⟩)
    (isPGroup_zpowers_of_orderOf_two (by rw [← Subgroup.orderOf_coe]; exact h2))
  have hP : (titsPASylow : Subgroup titsA) = titsPA.subgroupOf titsA := IsPGroup.toSylow_coe _ _
  rw [hP, Subgroup.mem_subgroupOf] at hg
  have hg' : (g : Equiv.Perm (Fin 1755)) * x * (g : Equiv.Perm (Fin 1755))⁻¹ ∈ titsPA := by
    simpa using hg
  have hsq : (g : Equiv.Perm (Fin 1755)) * x * (g : Equiv.Perm (Fin 1755))⁻¹ *
      ((g : Equiv.Perm (Fin 1755)) * x * (g : Equiv.Perm (Fin 1755))⁻¹) = 1 := by
    have hx2 : x * x = 1 := by rw [← sq, ← h2]; exact pow_orderOf_eq_one x
    calc _ = (g : Equiv.Perm (Fin 1755)) * (x * x) * (g : Equiv.Perm (Fin 1755))⁻¹ := by group
      _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
  rcases hg' with hS | hS
  · have hD : (g * ⟨x, hx⟩ * g⁻¹ : titsA) ∈ titsD.subgroupOf titsA := by
      rw [Subgroup.mem_subgroupOf]
      simpa using titsS_le_titsD hS
    have := titsD_normal_A.conj_mem _ hD g⁻¹
    rw [Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this
  · exfalso
    apply titsGen1_mul_sq_ne hS
    simpa [mul_assoc] using hsq

theorem titsInvCert_facts
    {bw : Bool × List ℤ} (h : bw ∈ titsInvCert) :
    lettersOK 13 bw.2 = true ∧ isInvA 1755 (wordArr 1755 titsDerivedArrs bw.2)
      (invCand 1755 (wordArr 1755 titsDerivedArrs bw.2)) = true := by
  have := List.all_eq_true.1 titsClass_check.1 bw h
  simpa [Bool.and_eq_true] using this

theorem titsS_involution_conj
    {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsS) (h2 : s * s = 1)
    (h1 : s ≠ 1) : ∃ g ∈ titsD, g * titsZ * g⁻¹ = s ∨ g * titsTInv * g⁻¹ = s := by
  have hsQ : s ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hs
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 (by show (finList 1755 titsSBase).length = 5; simp [finList,
      titsCentral_check.1]) titsClass_check.2 hsQ
  rw [(eqA_iff (rep_compA ha ha) rep_idA).2 h2,
    (show eqA 1755 a (idA 1755) = false from Bool.eq_false_iff.2 fun e =>
      h1 (eq_of_eqA ha rep_idA e))] at hp
  simp only [Bool.not_true, Bool.false_or, anyEq, List.any_eq_true, titsInvConj,
    List.mem_map] at hp
  obtain ⟨_, ⟨bw, hbw, rfl⟩, hac⟩ := hp
  obtain ⟨hl, hinv⟩ := titsInvCert_facts hbw
  have hw := rep_wordArr_titsT hl
  refine ⟨wordIn 13 titsT bw.2, wordIn_titsT_mem_titsD _, ?_⟩
  cases hb : bw.1
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hac
    exact Or.inr (eq_of_eqA ha (rep_conjArr hw hinv titsTInv_rep) hac).symm
  · simp only [hb, ↓reduceIte] at hac
    exact Or.inl (eq_of_eqA ha (rep_conjArr hw hinv titsZ_rep) hac).symm

theorem isConj_of_conj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsD) {y : titsD}
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsD) (h : g * y * g⁻¹ = x) :
    IsConj y ⟨x, hx⟩ :=
  isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using h)⟩

theorem titsD_involution_conj
    (x : titsD) (h2 : orderOf x = 2) :
    IsConj titsZD x ∨ IsConj titsTD x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow titsSylow (isPGroup_zpowers_of_orderOf_two h2)
  rw [coe_titsSylow, Subgroup.mem_subgroupOf] at hg
  have hx2 : x * x = 1 := by rw [← sq, ← h2]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by norm_num)
  have hy2 : ((g * x * g⁻¹ : titsD) : Equiv.Perm (Fin 1755)) *
      ((g * x * g⁻¹ : titsD) : Equiv.Perm (Fin 1755)) = 1 := by
    rw [← Subgroup.coe_mul]
    have : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
      calc _ = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
    rw [this, Subgroup.coe_one]
  have hy1 : ((g * x * g⁻¹ : titsD) : Equiv.Perm (Fin 1755)) ≠ 1 := fun h => by
    have : g * x * g⁻¹ = 1 := Subtype.ext h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [this, mul_one, inv_mul_cancel]
  obtain ⟨c, hc, hzt⟩ := titsS_involution_conj hg hy2 hy1
  have hconj : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases hzt with h | h
  · exact Or.inl ((isConj_of_conj hc (y := titsZD) (g * x * g⁻¹).2 h).trans hconj)
  · exact Or.inr ((isConj_of_conj hc (y := titsTD) (g * x * g⁻¹).2 h).trans hconj)

theorem titsD_centralizer_z :
    titsD ⊓ Subgroup.centralizer {titsZ} = titsH := by
  rw [titsH_eq_CZS]
  congr 1
  rw [titsS_center]
  ext g
  simp [Subgroup.mem_centralizer_iff]

theorem card_centralizer_titsZD :
    Nat.card (Subgroup.centralizer {titsZD}) = 10240 := by
  rw [← Subgroup.card_map_of_injective titsD.subtype_injective, map_subtype_centralizer,
    show ((titsZD : titsD) : Equiv.Perm (Fin 1755)) = titsZ from rfl, titsD_centralizer_z,
    titsQH_facts.2.2.2]

theorem ncard_class_z :
    {y | IsConj titsZD y}.ncard = 1755 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer {titsZD})
  rw [card_centralizer_titsZD, card_titsD, index_centralizer_eq_ncard] at h
  omega

abbrev titsCt : Subgroup (Equiv.Perm (Fin 1755)) := titsN ⊓ Subgroup.centralizer {titsTInv}

abbrev titsQ : Subgroup (Equiv.Perm (Fin 1755)) := titsCt ⊓ titsK

theorem titsCNt_facts {c : Array ℕ} (hc : c ∈ titsCNt) :
    isInvA 1755 c (invCand 1755 c) = true ∧ commA c titsTArr = true ∧ inN c = true := by
  have := List.all_eq_true.1 titsCNt_check.2.2.2.2.1 c hc
  simpa [Bool.and_eq_true, and_assoc] using this

theorem commA_iff {a b : Array ℕ} {g h : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hb : Rep 1755 b h) : commA a b = true ↔ g * h = h * g :=
  eqA_iff (rep_compA ha hb) (rep_compA hb ha)

theorem mem_centralizer_t_iff {g : Equiv.Perm (Fin 1755)} :
    g ∈ Subgroup.centralizer {titsTInv} ↔ g * titsTInv = titsTInv * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem titsCt_eq :
    ((titsCt : Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) =
    {g | g ∈ titsCNt.map (permOfArr 1755)} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hgN, hgC⟩
    have hgQ : g ∈ titsQN.originalSubgroup := by rw [titsQN_facts.2.2.1]; exact hgN
    obtain ⟨a, ha, hp⟩ := all5_spec titsN_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.2.2.1 (by show (finList 1755 titsNBase).length = 5; simp [finList,
        titsCentral_check.2.2.1]) titsCNt_check.1 hgQ
    have hcomm := (commA_iff ha titsTInv_rep).2 (mem_centralizer_t_iff.1 hgC)
    simp only [hcomm, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨c, hc, hac⟩ := hp
    exact ⟨c, hc, (eq_of_eqA ha (rep_permOfArr (titsCNt_facts hc).1).1 hac).symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hinv, hcomm, hN⟩ := titsCNt_facts hc
    have hr := (rep_permOfArr hinv).1
    exact ⟨mem_titsN_of_sift hr hN, mem_centralizer_t_iff.2 ((commA_iff hr titsTInv_rep).1 hcomm)⟩

theorem titsCNt_nodup : (titsCNt.map (permOfArr 1755)).Nodup :=
  nodup_map_permOfArr (fun _ hc => (titsCNt_facts hc).1) titsCNt_check.2.2.2.2.2.1

theorem card_titsCt :
    Nat.card titsCt = 1536 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCt_eq, ncard_list_set titsCNt_nodup,
    List.length_map, titsCNt_check.2.1]

theorem titsQ_eq :
    ((titsQ : Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) =
    {g | g ∈ titsQt.map (permOfArr 1755)} := by
  ext g
  rw [Subgroup.coe_inf, Set.mem_inter_iff, titsCt_eq]
  simp only [Set.mem_ofPred_eq, List.mem_map, SetLike.mem_coe, titsQt, List.mem_filter]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hK⟩
    exact ⟨c, ⟨hc, (mem_titsK_iff_sift (rep_permOfArr (titsCNt_facts hc).1).1).2 hK⟩, rfl⟩
  · rintro ⟨c, ⟨hc, hK⟩, rfl⟩
    exact ⟨⟨c, hc, rfl⟩, (mem_titsK_iff_sift (rep_permOfArr (titsCNt_facts hc).1).1).1 hK⟩

theorem card_titsQ :
    Nat.card titsQ = 256 := by
  have hnd : (titsQt.map (permOfArr 1755)).Nodup :=
    nodup_map_permOfArr (fun _ hc => (titsCNt_facts (List.mem_of_mem_filter hc)).1)
      (titsCNt_check.2.2.2.2.2.1.filter _)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsQ_eq, ncard_list_set hnd,
    List.length_map, titsCNt_check.2.2.1]

theorem mem_centralizer_titsQ_iff
    {c : Array ℕ} (hc : c ∈ titsCNt) :
    permOfArr 1755 c ∈ Subgroup.centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) ↔
      titsQt.all (fun q => commA c q) = true := by
  have hr := (rep_permOfArr (titsCNt_facts hc).1).1
  rw [Subgroup.mem_centralizer_iff, List.all_eq_true]
  constructor
  · intro h q hq
    have hqr := (rep_permOfArr (titsCNt_facts (List.mem_of_mem_filter hq)).1).1
    have hmem : permOfArr 1755 q ∈ (titsQ : Set (Equiv.Perm (Fin 1755))) := by
      rw [titsQ_eq]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    exact (commA_iff hr hqr).2 (h _ hmem).symm
  · intro h g hg
    rw [titsQ_eq] at hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
    have hqr := (rep_permOfArr (titsCNt_facts (List.mem_of_mem_filter hq)).1).1
    exact ((commA_iff hr hqr).1 (h q hq)).symm

theorem titsCCQ_eq :
    ((titsCt ⊓ Subgroup.centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) :
    Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) =
    {g | g ∈ titsCCQ.map (permOfArr 1755)} := by
  ext g
  rw [Subgroup.coe_inf, Set.mem_inter_iff, titsCt_eq]
  simp only [Set.mem_ofPred_eq, List.mem_map, SetLike.mem_coe, titsCCQ, List.mem_filter]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hC⟩
    exact ⟨c, ⟨hc, (mem_centralizer_titsQ_iff hc).1 hC⟩, rfl⟩
  · rintro ⟨c, ⟨hc, hC⟩, rfl⟩
    exact ⟨⟨c, hc, rfl⟩, (mem_centralizer_titsQ_iff hc).2 hC⟩

theorem card_titsCCQ :
    Nat.card (titsCt ⊓ Subgroup.centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) = 8 := by
  have hnd : (titsCCQ.map (permOfArr 1755)).Nodup :=
    nodup_map_permOfArr (fun _ hc => (titsCNt_facts (List.mem_of_mem_filter hc)).1)
      (titsCNt_check.2.2.2.2.2.1.filter _)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCCQ_eq, ncard_list_set hnd,
    List.length_map, titsCNt_check.2.2.2.1]

theorem titsCCQ_le :
    titsCt ⊓ Subgroup.centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) ≤ titsQ := by
  intro g hg
  have hg' : g ∈ ((titsCt ⊓ Subgroup.centralizer (titsQ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := hg
  rw [titsCCQ_eq] at hg'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg'
  have hcC := List.mem_of_mem_filter hc
  have hr := (rep_permOfArr (titsCNt_facts hcC).1).1
  refine ⟨hg.1, (mem_titsK_iff_sift hr).1 (List.all_eq_true.1 titsCNt_check.2.2.2.2.2.2 c hc)⟩

theorem titsQ_normal :
    (titsQ.subgroupOf titsCt).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
  exact inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer titsK_le_titsN).1
    titsK_normal_N)

theorem mem_titsH_iff
    {g : Equiv.Perm (Fin 1755)} : g ∈ titsH ↔ g ∈ titsD ∧ g 0 = 0 := by
  rw [titsH_eq_stab, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hx
    exact ⟨x.2, hx⟩
  · rintro ⟨hD, h0⟩
    exact ⟨⟨g, hD⟩, by rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]; exact h0, rfl⟩

theorem titsTInv_zero :
    titsTInv 0 = 0 :=
  (mem_titsH_iff.1 (titsS_le_titsH (titsK_le_titsS titsTInv_mem_titsK))).2

theorem titsCHt_facts {c : Array ℕ} (hc : c ∈ titsCHt) :
    isInvA 1755 c (invCand 1755 c) = true ∧ commA c titsTArr = true ∧ inH c = true := by
  have := List.all_eq_true.1 titsFix_check.2.2.2.2.2.1 c hc
  simpa [Bool.and_eq_true, and_assoc] using this

theorem titsCHt_eq :
    ((titsH ⊓ Subgroup.centralizer {titsTInv} : Subgroup (Equiv.Perm (Fin 1755))) :
      Set (Equiv.Perm (Fin 1755))) = {g | g ∈ titsCHt.map (permOfArr 1755)} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hgH, hgC⟩
    have hgQ : g ∈ titsQH.originalSubgroup := by rw [titsQH_facts.2.2.1]; exact hgH
    obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.1 (by show (finList 1755 titsHBase).length = 5; simp [finList,
        titsCentral_check.2.1]) titsFix_check.2.2.2.1 hgQ
    have hcomm := (commA_iff ha titsTInv_rep).2 (mem_centralizer_t_iff.1 hgC)
    simp only [hcomm, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨c, hc, hac⟩ := hp
    exact ⟨c, hc, (eq_of_eqA ha (rep_permOfArr (titsCHt_facts hc).1).1 hac).symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hinv, hcomm, hH⟩ := titsCHt_facts hc
    have hr := (rep_permOfArr hinv).1
    exact ⟨mem_titsH_of_sift hr hH, mem_centralizer_t_iff.2 ((commA_iff hr titsTInv_rep).1 hcomm)⟩

theorem card_titsCHt :
    Nat.card (titsH ⊓ Subgroup.centralizer {titsTInv} : Subgroup (Equiv.Perm (Fin 1755))) =
      512 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, titsCHt_eq,
    ncard_list_set (nodup_map_permOfArr (fun _ hc => (titsCHt_facts hc).1)
      titsFix_check.2.2.2.2.2.2), List.length_map, titsFix_check.2.2.2.2.1]

theorem titsFixWords_facts
    {pw : ℕ × List ℤ} (h : pw ∈ titsFixWords) :
    lettersOK 13 pw.2 = true ∧ (wordArr 1755 titsDerivedArrs pw.2)[0]! = pw.1 ∧
      isInvA 1755 (wordArr 1755 titsDerivedArrs pw.2)
        (invCand 1755 (wordArr 1755 titsDerivedArrs pw.2)) = true := by
  have := List.all_eq_true.1 titsFix_check.2.1 pw h
  simpa [Bool.and_eq_true, and_assoc] using this

theorem titsDt_apply_zero
    {c : Equiv.Perm (Fin 1755)} (hcD : c ∈ titsD)
    (hct : c * titsTInv = titsTInv * c) : ((c 0 : Fin 1755) : ℕ) ≤ 2 := by
  have hfix : titsTInv (c 0) = c 0 := by
    have h1 : (c * titsTInv) 0 = (titsTInv * c) 0 := by rw [hct]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, titsTInv_zero] at h1
    exact h1.symm
  have hmem : ((c 0 : Fin 1755) : ℕ) ∈ titsFixWords.map Prod.fst := by
    refine titsFix_check.1 _ (c 0).2 ?_
    rw [titsTInv_rep (c 0), hfix]
  obtain ⟨pw, hpw, hp⟩ := List.mem_map.1 hmem
  obtain ⟨hl, h0, hinv⟩ := titsFixWords_facts hpw
  have hu := rep_wordArr_titsT hl
  have hu0 : wordIn 13 titsT pw.2 0 = c 0 := by
    apply Fin.ext
    rw [← hu 0, ← hp]
    exact h0
  by_contra hgt
  have hh : (wordIn 13 titsT pw.2)⁻¹ * c ∈ titsH := by
    refine mem_titsH_iff.2 ⟨mul_mem (inv_mem (wordIn_titsT_mem_titsD _)) hcD, ?_⟩
    rw [Equiv.Perm.mul_apply, ← hu0, perm_inv_apply]
  have hconj : (wordIn 13 titsT pw.2)⁻¹ * c * titsTInv * ((wordIn 13 titsT pw.2)⁻¹ * c)⁻¹ =
      (wordIn 13 titsT pw.2)⁻¹ * titsTInv * wordIn 13 titsT pw.2 := by
    have e1 : c * titsTInv * c⁻¹ = titsTInv := by rw [hct, mul_inv_cancel_right]
    calc (wordIn 13 titsT pw.2)⁻¹ * c * titsTInv * ((wordIn 13 titsT pw.2)⁻¹ * c)⁻¹
        = (wordIn 13 titsT pw.2)⁻¹ * (c * titsTInv * c⁻¹) * wordIn 13 titsT pw.2 := by
          rw [mul_inv_rev, inv_inv]
          simp only [mul_assoc]
      _ = _ := by rw [e1]
  have hhQ : (wordIn 13 titsT pw.2)⁻¹ * c ∈ titsQH.originalSubgroup := by
    rw [titsQH_facts.2.2.1]
    exact hh
  obtain ⟨a, ha, hpa⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.1 (by show (finList 1755 titsHBase).length = 5; simp [finList,
      titsCentral_check.2.1]) titsFix_check.2.2.1 hhQ
  rw [Bool.and_eq_true, List.all_eq_true] at hpa
  obtain ⟨hai, hall⟩ := hpa
  have hy : compA 1755 (compA 1755 (invCand 1755 (wordArr 1755 titsDerivedArrs pw.2)) titsTArr)
      (wordArr 1755 titsDerivedArrs pw.2) ∈ titsExcl :=
    List.mem_map.2 ⟨pw, List.mem_filter.2 ⟨hpw, decide_eq_true (by omega)⟩, rfl⟩
  have hne := hall _ hy
  rw [(eqA_iff (rep_conjArr ha hai titsTInv_rep)
    (rep_compA (rep_compA (rep_inv_of_isInvA hu hinv) titsTInv_rep) hu)).2 hconj] at hne
  exact Bool.false_ne_true hne

abbrev titsDt : Subgroup (Equiv.Perm (Fin 1755)) := titsD ⊓ Subgroup.centralizer {titsTInv}

theorem map_stabilizer_titsDt :
    (MulAction.stabilizer titsDt (0 : Fin 1755)).map titsDt.subtype =
      titsH ⊓ Subgroup.centralizer {titsTInv} := by
  ext g
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype,
    Subgroup.mem_inf, mem_titsH_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(Subgroup.mem_inf.1 x.2).1, hx⟩, (Subgroup.mem_inf.1 x.2).2⟩
  · rintro ⟨⟨hD, h0⟩, hc⟩
    exact ⟨⟨g, Subgroup.mem_inf.2 ⟨hD, hc⟩⟩, h0, rfl⟩

theorem card_titsDt_le :
    Nat.card titsDt ≤ 1536 := by
  have hstab : Nat.card (MulAction.stabilizer titsDt (0 : Fin 1755)) = 512 := by
    rw [← Subgroup.card_map_of_injective titsDt.subtype_injective, map_stabilizer_titsDt,
      card_titsCHt]
  have horb : (MulAction.orbit titsDt (0 : Fin 1755)).ncard ≤ 3 := by
    have hsub : MulAction.orbit titsDt (0 : Fin 1755) ⊆ ({0, 1, 2} : Set (Fin 1755)) := by
      rintro _ ⟨g, rfl⟩
      have hle := titsDt_apply_zero (Subgroup.mem_inf.1 g.2).1
        (mem_centralizer_t_iff.1 (Subgroup.mem_inf.1 g.2).2)
      have hval : ((g • (0 : Fin 1755) : Fin 1755) : ℕ) = 0 ∨
          ((g • (0 : Fin 1755) : Fin 1755) : ℕ) = 1 ∨
          ((g • (0 : Fin 1755) : Fin 1755) : ℕ) = 2 := by
        have : ((g • (0 : Fin 1755) : Fin 1755) : ℕ) = (((g : Equiv.Perm (Fin 1755)) 0 :
            Fin 1755) : ℕ) := rfl
        omega
      rcases hval with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    calc (MulAction.orbit titsDt (0 : Fin 1755)).ncard ≤ ({0, 1, 2} : Set (Fin 1755)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_pair (by decide)]
  have h := Subgroup.card_mul_index (MulAction.stabilizer titsDt (0 : Fin 1755))
  rw [hstab, MulAction.index_stabilizer] at h
  rw [← h]
  omega

theorem titsD_centralizer_t :
    titsCt = titsD ⊓ Subgroup.centralizer {titsTInv} ∧
    Nat.card (Subgroup.centralizer {titsTD}) = 1536 ∧ {y | IsConj titsTD y}.ncard = 11700 := by
  have hle : titsCt ≤ titsDt := inf_le_inf_right _ titsN_le_titsD
  have hge : Nat.card titsDt ≤ Nat.card titsCt := by rw [card_titsCt]; exact card_titsDt_le
  have hCt := Subgroup.eq_of_le_of_card_ge hle hge
  have hmap : (Subgroup.centralizer {titsTD}).map titsD.subtype = titsDt :=
    map_subtype_centralizer titsTD
  have hcard : Nat.card (Subgroup.centralizer {titsTD}) = 1536 := by
    rw [← Subgroup.card_map_of_injective titsD.subtype_injective, hmap, ← hCt, card_titsCt]
  refine ⟨hCt, hcard, ?_⟩
  have h := Subgroup.card_mul_index (Subgroup.centralizer {titsTD})
  rw [hcard, card_titsD, index_centralizer_eq_ncard] at h
  omega

theorem noOddNormal_H :
    NoOddNormal titsH :=
  have := AT_Tits_intrinsic_local_pair.2.2.2.2.2.2.1
  noOddNormal_of_two_core (J := titsJ.subgroupOf titsH) (k := 9)
    (by rw [card_subgroupOf_eq titsJ_le_titsH, titsQJ_facts.2.2.2]; norm_num)
    (centralizer_subgroupOf_le titsJ_le_titsH CHJ_le_J)

theorem noOddNormal_Ct :
    NoOddNormal titsCt :=
  have := titsQ_normal
  noOddNormal_of_two_core (J := titsQ.subgroupOf titsCt) (k := 8)
    (by rw [card_subgroupOf_eq inf_le_left, card_titsQ]; norm_num)
    (centralizer_subgroupOf_le inf_le_left titsCCQ_le)

theorem noOddNormal_centralizer_of_conj {x y : titsD} (h : IsConj y x)
    (hy : NoOddNormal (Subgroup.centralizer {y})) : NoOddNormal (Subgroup.centralizer {x}) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  have e : Subgroup.centralizer {y} ≃* Subgroup.centralizer {x} :=
    ((Subgroup.centralizer {y}).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (by rw [map_conj_centralizer, hg]))
  exact hy.of_equiv e.symm

theorem noOddNormal_centralizer_of_map_eq {y : titsD} {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : titsD ⊓ Subgroup.centralizer {(y : Equiv.Perm (Fin 1755))} = X) (h : NoOddNormal X) :
    NoOddNormal (Subgroup.centralizer {y}) :=
  h.of_equiv (((Subgroup.centralizer {y}).equivMapOfInjective _ titsD.subtype_injective).trans
    (MulEquiv.subgroupCongr (by rw [map_subtype_centralizer, hX])))

theorem CTUC_Tits_two_involution_classes_and_centralizer_two_kernels :
    (∀ x ∈ titsA, orderOf x = 2 → x ∈ titsD) ∧
    orderOf titsZD = 2 ∧ orderOf titsTD = 2 ∧
    (∀ x : titsD, orderOf x = 2 → IsConj titsZD x ∨ IsConj titsTD x) ∧
    ¬ IsConj titsZD titsTD ∧
    {y | IsConj titsZD y}.ncard = 1755 ∧ {y | IsConj titsTD y}.ncard = 11700 ∧
    titsD ⊓ Subgroup.centralizer {titsZ} = titsH ∧ Nat.card titsH = 10240 ∧
    Nat.card titsJ = 512 ∧ (titsJ.subgroupOf titsH).Normal ∧
    titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) ≤ titsJ ∧
    titsTInv ∈ titsK ∧
    titsN ⊓ Subgroup.centralizer {titsTInv} = titsD ⊓ Subgroup.centralizer {titsTInv} ∧
    Nat.card (titsN ⊓ Subgroup.centralizer {titsTInv} : Subgroup (Equiv.Perm (Fin 1755))) =
      1536 ∧
    (((titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ titsK).subgroupOf
      (titsN ⊓ Subgroup.centralizer {titsTInv})).Normal ∧
    Nat.card ((titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ titsK :
      Subgroup (Equiv.Perm (Fin 1755))) = 256 ∧
    (titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ Subgroup.centralizer
      (((titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ titsK : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) ≤ (titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ titsK ∧
    Nat.card ((titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ Subgroup.centralizer
      (((titsN ⊓ Subgroup.centralizer {titsTInv}) ⊓ titsK : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) : Subgroup (Equiv.Perm (Fin 1755))) = 8 ∧
    (∀ x : titsD, orderOf x = 2 → ∀ R : Subgroup (Subgroup.centralizer {x}), R.Normal →
      Odd (Nat.card R) → R = ⊥) := by
  obtain ⟨hCt, -, hct⟩ := titsD_centralizer_t
  have hz : NoOddNormal (Subgroup.centralizer {titsZD}) :=
    noOddNormal_centralizer_of_map_eq titsD_centralizer_z noOddNormal_H
  have ht : NoOddNormal (Subgroup.centralizer {titsTD}) :=
    noOddNormal_centralizer_of_map_eq hCt.symm noOddNormal_Ct
  refine ⟨fun x hx h2 => titsA_involution_mem_D hx h2, orderOf_titsZD, orderOf_titsTD,
    titsD_involution_conj, fun h => ?_, ncard_class_z, hct, titsD_centralizer_z,
    titsQH_facts.2.2.2, titsQJ_facts.2.2.2, AT_Tits_intrinsic_local_pair.2.2.2.2.2.2.1, CHJ_le_J,
    titsTInv_mem_titsK, hCt, card_titsCt, titsQ_normal, card_titsQ, titsCCQ_le, card_titsCCQ,
    fun x h2 => ?_⟩
  · have e : {y | IsConj titsZD y} = {y | IsConj titsTD y} := by
      ext y
      exact ⟨fun hy => h.symm.trans hy, fun hy => h.trans hy⟩
    rw [← e, ncard_class_z] at hct
    exact absurd hct (by norm_num)
  · rcases titsD_involution_conj x h2 with h | h
    · exact noOddNormal_centralizer_of_conj h hz
    · exact noOddNormal_centralizer_of_conj h ht

end CFSG.Sporadic.Schreier.Tits
