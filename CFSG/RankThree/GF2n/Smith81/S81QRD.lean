module

public import CFSG.RankThree.GF2n.Smith81.S81QRDP
public import CFSG.RankThree.GF2n.Smith81.S81QStab
public import CFSG.RankThree.GF2n.Smith81.S81XD6Mon
public import CFSG.RankThree.GF2n.Smith81.S81VRoot

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.S81V
open scoped commutatorElement

abbrev alphaA2 : Rt := Pi.single nodeA2 1

theorem isRoot_alphaA2 : IsRoot .E7 alphaA2 := IsRoot.basis nodeA2

theorem alphaA2_mem_Perp : alphaA2 ∈ Perp := by
  rw [perp_iff]
  refine ⟨isRoot_alphaA2, ?_⟩
  show (Pi.single nodeA2 (1 : ℤ) : Rt) node1 = 0
  rw [Pi.single_eq_of_ne (show node1 ≠ nodeA2 by decide)]

theorem alphaA2_mem : alphaA2 ∈ Psi0 := mem_Psi0.2 ⟨alphaA2_mem_Perp, by simp [alphaA2]⟩

theorem pr_alphaA2 : pr (a0 : Fin e7Data.d) alphaA2 = 1 := pr_a0_Psi0 alphaA2_mem

variable {K : Type} [Field K] [CharP K 2]

@[expose] def tauD : ND K →ₗ[K] K := LinearMap.proj (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0)

@[expose] def n1D : ND K := Pi.single (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0) 1

theorem tauD_n1D : tauD (n1D : ND K) = 1 := by
  simp [tauD, n1D]

@[expose] def uΛ (n : ND K) : ↥(LamG K) := ⟨uD n, URge_Rd6_le_LamG (uD_mem_URge n)⟩

theorem uΛ_add (n m : ND K) : uΛ (n + m) = uΛ n * uΛ m := Subtype.ext (uD_add n m)

@[expose] def PΛ (K : Type) [Field K] [CharP K 2] : Subgroup ↥(LamG K) :=
  (linNorm (K := K) (uD : ND K → Gp K) uD_injective).subgroupOf (LamG K)

theorem mem_PΛ {g : ↥(LamG K)} :
    g ∈ PΛ K ↔ (g : Gp K) ∈ linNorm (K := K) (uD : ND K → Gp K) uD_injective := Iff.rfl

@[expose] def PΛtoLin (K : Type) [Field K] [CharP K 2] :
    ↥(PΛ K) →* ↥(linNorm (K := K) (uD : ND K → Gp K) uD_injective) :=
  (((LamG K).subtype).comp (PΛ K).subtype).codRestrict _ fun x => x.2

@[expose] def AdΛ (K : Type) [Field K] [CharP K 2] : ↥(PΛ K) →* (ND K ≃ₗ[K] ND K) :=
  (linAd (K := K) (uD : ND K → Gp K) uD_injective).comp (PΛtoLin K)

theorem uΛ_AdΛ (g : ↥(PΛ K)) (n : ND K) :
    uΛ (AdΛ K g n) = (g : ↥(LamG K)) * uΛ n * (g : ↥(LamG K))⁻¹ :=
  Subtype.ext (u_linAd (K := K) (uD : ND K → Gp K) uD_injective (PΛtoLin K g) n)

@[expose] def hΛ (c : Kˣ) : ↥(LamG K) := ⟨e7Data_valid.hm K nodeA2 c, d0Lam_mem K c⟩

theorem hΛ_mem_PΛ (c : Kˣ) : hΛ c ∈ PΛ K := hm_mem_linNorm0 nodeA2 c

@[expose] def dHomD : Kˣ →* ↥(PΛ K) where
  toFun c := ⟨hΛ c, hΛ_mem_PΛ c⟩
  map_one' := Subtype.ext (Subtype.ext (e7Data_valid.hm_one K nodeA2))
  map_mul' c c' := Subtype.ext (Subtype.ext (e7Data_valid.hm_mul K nodeA2 c c'))

theorem toWeight_alphaA2 : MinData.toWeight alphaA2 nodeA2 = 2 := by
  unfold alphaA2
  rw [MinData.toWeight_single]
  exact Tag.cartan_self _ _

theorem Ad_dD (c : Kˣ) :
    AdΛ K (dHomD c) (n1D : ND K) = (c : K) ^ 2 • (n1D : ND K) := by
  have h := linAd_hm0 (K := K) nodeA2 c n1D
  show linAd (K := K) uD uD_injective ⟨e7Data_valid.hm K nodeA2 c, hm_mem_linNorm0 nodeA2 c⟩ n1D = _
  rw [h, n1D, diagD_single, toWeight_alphaA2]
  funext δ
  by_cases hδ : δ = (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0)
  · subst hδ
    simp
  · simp [Pi.single_apply, hδ]

@[expose] def sD (K : Type) [Field K] : ↥(LamG K) :=
  ⟨e7Data_valid.nm K nodeA2, nm_mem_LamG nodeA2 (by decide)⟩

theorem coe_sD : ((sD K : ↥(LamG K)) : Gp K) = e7Data_valid.nm K nodeA2 := rfl

theorem neg_one_unit' : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])

theorem sD_sq : sD K * sD K = 1 := by
  have h := e7Data_valid.nm_sq K nodeA2
  rw [pow_two, neg_one_unit'] at h
  refine Subtype.ext ?_
  show e7Data_valid.nm K nodeA2 * e7Data_valid.nm K nodeA2 = 1
  rw [h]
  exact e7Data_valid.hm_one K nodeA2

theorem sD_inv : (sD K)⁻¹ = sD K := inv_eq_of_mul_eq_one_right sD_sq

theorem hm_inv_unit' (i : Fin (Tag.rank .E7)) (c : Kˣ) :
    e7Data_valid.hm K i c⁻¹ = (e7Data_valid.hm K i c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← e7Data_valid.hm_mul K i c c⁻¹, mul_inv_cancel]
  exact e7Data_valid.hm_one K i

theorem sD_dD (c : Kˣ) :
    sD K * ((dHomD c : ↥(PΛ K)) : ↥(LamG K)) * sD K = ((dHomD c : ↥(PΛ K)) : ↥(LamG K))⁻¹ := by
  have h := e7Data_valid.nm_conj_hm K nodeA2 nodeA2 c
  rw [Tag.cartan_self, ← e7Data_valid.hm_mul K nodeA2 c] at h
  have h2 : c * c ^ (-(2 : ℤ)) = c⁻¹ := by group
  rw [h2] at h
  have hs : (e7Data_valid.nm K nodeA2)⁻¹ = e7Data_valid.nm K nodeA2 :=
    congrArg Subtype.val (sD_inv (K := K))
  refine Subtype.ext ?_
  show e7Data_valid.nm K nodeA2 * e7Data_valid.hm K nodeA2 c * e7Data_valid.nm K nodeA2 =
    (e7Data_valid.hm K nodeA2 c)⁻¹
  calc e7Data_valid.nm K nodeA2 * e7Data_valid.hm K nodeA2 c * e7Data_valid.nm K nodeA2
      = e7Data_valid.nm K nodeA2 * e7Data_valid.hm K nodeA2 c * (e7Data_valid.nm K nodeA2)⁻¹ := by
        rw [hs]
    _ = e7Data_valid.hm K nodeA2 c⁻¹ := h
    _ = (e7Data_valid.hm K nodeA2 c)⁻¹ := hm_inv_unit' nodeA2 c

theorem sD_conj_xE {γ : Rt} (hγ : IsRoot .E7 γ) (c : K) :
    e7Data_valid.nm K nodeA2 * xE γ c * e7Data_valid.nm K nodeA2 = xE (reflect .E7 nodeA2 γ) c := by
  obtain ⟨σ, hσ, h⟩ := e7Data_valid.nm_conj_xm K hγ nodeA2
  have hσ1 : σ = 1 := by
    rcases hσ with h1 | h1
    · exact h1
    · rw [h1]
      exact CharTwo.neg_eq (1 : K)
  have hs : (e7Data_valid.nm K nodeA2)⁻¹ = e7Data_valid.nm K nodeA2 :=
    congrArg Subtype.val (sD_inv (K := K))
  calc e7Data_valid.nm K nodeA2 * xE γ c * e7Data_valid.nm K nodeA2
      = e7Data_valid.nm K nodeA2 * xE γ c * (e7Data_valid.nm K nodeA2)⁻¹ := by rw [hs]
    _ = xE (reflect .E7 nodeA2 γ) (σ * c) := h c
    _ = xE (reflect .E7 nodeA2 γ) c := by rw [hσ1, one_mul]

theorem sD_eq : e7Data_valid.nm K nodeA2 = xE alphaA2 1 * xE (-alphaA2) 1 * xE alphaA2 1 := by
  have h1 : (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) = 1 := by simp [CharTwo.neg_eq]
  show e7Data_valid.nt K nodeA2 1 = _
  unfold MinData.Valid.nt
  rw [h1]
  rfl

theorem braidD : e7Data_valid.nm K nodeA2 =
    xE alphaA2 1 * (e7Data_valid.nm K nodeA2 * xE alphaA2 1 * e7Data_valid.nm K nodeA2) *
      xE alphaA2 1 := by
  rw [sD_conj_xE isRoot_alphaA2 (1 : K), alphaA2, reflect_single_self]
  exact sD_eq

theorem refl_pr_mem0 : ∀ γ : Rt, IsRoot .E7 γ → γ node1 = 0 → γ nodeA2 = 1 → γ ≠ alphaA2 →
    ((reflect .E7 nodeA2 γ) node1 = 0 ∧
      (pr b0 (reflect .E7 nodeA2 γ) = 0 ∨ pr b0 (reflect .E7 nodeA2 γ) = 1)) := by
  refine (forall_isRoot_iff fun γ => γ node1 = 0 → γ nodeA2 = 1 → γ ≠ alphaA2 →
    ((reflect .E7 nodeA2 γ) node1 = 0 ∧
      (pr b0 (reflect .E7 nodeA2 γ) = 0 ∨ pr b0 (reflect .E7 nodeA2 γ) = 1))).2 ?_
  unfold pr alphaA2 nodeA2 node1 reflect b0
  decide +kernel

theorem exists_down_simple0 : ∀ γ : Rt, IsRoot .E7 γ → γ node1 = 0 → γ nodeA2 = 1 → γ ≠ alphaA2 →
    ∃ i : Fin (Tag.rank .E7), i ≠ nodeA2 ∧ i ≠ node1 ∧ ∃ m : Fin 126,
      (Tag.rootCertificate .E7).root m = γ - Pi.single i 1 := by
  refine (forall_isRoot_iff fun γ => γ node1 = 0 → γ nodeA2 = 1 → γ ≠ alphaA2 →
    ∃ i : Fin (Tag.rank .E7), i ≠ nodeA2 ∧ i ≠ node1 ∧ ∃ m : Fin 126,
      (Tag.rootCertificate .E7).root m = γ - Pi.single i 1).2 ?_
  unfold alphaA2 nodeA2 node1
  decide +kernel

theorem pr_single_ne0 (i : Fin (Tag.rank .E7)) (hi : i ≠ nodeA2) (hi1 : i ≠ node1) :
    pr (a0 : Fin e7Data.d) (Pi.single i 1 : Rt) = 0 := by
  have hP : (Pi.single i 1 : Rt) ∈ Perp := by
    rw [perp_iff]
    refine ⟨IsRoot.basis i, ?_⟩
    rw [Pi.single_eq_of_ne (show node1 ≠ i from fun h => hi1 h.symm)]
  rw [pr_a0_eq hP, Pi.single_eq_of_ne (show nodeA2 ≠ i from fun h => hi h.symm)]

theorem pr_neg0 (a : Fin e7Data.d) (γ : Rt) : pr a (-γ) = - pr a γ := by
  unfold pr
  exact dotProduct_neg _ _

theorem single_mem_Perp0 (i : Fin (Tag.rank .E7)) (hi1 : i ≠ node1) : (Pi.single i 1 : Rt) ∈ Perp := by
  rw [perp_iff]
  refine ⟨IsRoot.basis i, ?_⟩
  rw [Pi.single_eq_of_ne (show node1 ≠ i from fun h => hi1 h.symm)]

theorem conj_list_prod' {G : Type*} [Group G] (g : G) (l : List G) :
    g * l.prod * g⁻¹ = (l.map fun x => g * x * g⁻¹).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [← ih]
    group

theorem ker_stab_D (n : ND K) (hn : tauD n = 0) :
    ∃ g : ↥(PΛ K), (g : ↥(LamG K)) = sD K * uΛ n * sD K := by
  refine ⟨⟨sD K * uΛ n * sD K, ?_⟩, rfl⟩
  rw [mem_PΛ]
  have hu : uD n = ((Phi (a0 : Fin e7Data.d)).toList.map fun β => xE β (extD n β)).prod := rfl
  have key := conj_list_prod' (e7Data_valid.nm K nodeA2)
    ((Phi (a0 : Fin e7Data.d)).toList.map fun β => xE β (extD n β))
  have hs : (e7Data_valid.nm K nodeA2)⁻¹ = e7Data_valid.nm K nodeA2 :=
    congrArg Subtype.val (sD_inv (K := K))
  rw [hs, ← hu] at key
  show e7Data_valid.nm K nodeA2 * uD n * e7Data_valid.nm K nodeA2 ∈ _
  rw [key]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hy
  have hβa : β ∈ Phi (a0 : Fin e7Data.d) := Finset.mem_toList.1 hβ
  have hroot : IsRoot .E7 β := (mem_Phi.1 hβa).1
  rw [sD_conj_xE hroot]
  by_cases hβΨ : β ∈ Psi0
  · by_cases hb : β = alphaA2
    · subst hb
      have : extD n alphaA2 = 0 := by
        rw [extD_of_mem alphaA2_mem]
        exact hn
      rw [this, show xE (reflect .E7 nodeA2 alphaA2) (0 : K) = 1 from e7Data_valid.xm_zero K _]
      exact Subgroup.one_mem _
    · have hP := mem_Psi0.1 hβΨ
      have hP' := perp_iff.1 hP.1
      obtain ⟨h1, h2⟩ := refl_pr_mem0 β hP'.1 hP'.2 hP.2 hb
      have hrefP : reflect .E7 nodeA2 β ∈ Perp := perp_iff.2 ⟨hP'.1.reflect nodeA2, h1⟩
      exact xE_mem_linNorm0 hrefP h2 _
  · rw [extD_of_not_mem hβΨ, show xE (reflect .E7 nodeA2 β) (0 : K) = 1 from
      e7Data_valid.xm_zero K _]
    exact Subgroup.one_mem _

theorem Ad_xE_neg_coord0 (γ : Rt) (hγP : γ ∈ Perp) (hpr : pr (a0 : Fin e7Data.d) γ = 0) (n : ND K)
    (δ β : ↥Psi0) (hδβ : δ.1 + γ = β.1) :
    AdΛ K ⟨⟨xE (-γ) 1, xE_mem_LamG (neg_mem_Perp hγP) 1⟩,
      xE_mem_linNorm0 (neg_mem_Perp hγP) (Or.inl (by rw [pr_neg0, hpr, neg_zero])) 1⟩ n δ
      = n δ + n β := by
  have h := linAd_xE0 (K := K) (neg_mem_Perp hγP) (Or.inl (by rw [pr_neg0, hpr, neg_zero])) 1 n
  have h2 : (AdΛ K ⟨⟨xE (-γ) 1, xE_mem_LamG (neg_mem_Perp hγP) 1⟩,
      xE_mem_linNorm0 (neg_mem_Perp hγP) (Or.inl (by rw [pr_neg0, hpr, neg_zero])) 1⟩) n =
      n + (1 : K) • shiftD (-γ) n := h
  rw [h2, Pi.add_apply, Pi.smul_apply, shiftD_apply, smul_eq_mul, one_mul]
  unfold shiftFunD
  have hmem : δ.1 - -γ ∈ Psi0 := by
    rw [sub_neg_eq_add, hδβ]
    exact β.2
  have h3 : (⟨δ.1 - -γ, hmem⟩ : ↥Psi0) = β :=
    Subtype.ext (show δ.1 - -γ = β.1 by rw [sub_neg_eq_add, hδβ])
  rw [dif_pos hmem, h3]

theorem isRoot_cert0 (m : Fin 126) : IsRoot .E7 ((Tag.rootCertificate .E7).root m) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) m (by omega)

theorem ht_single_one0 (i : Fin (Tag.rank .E7)) : ht (Pi.single i 1 : Rt) = 1 := by
  simp [ht]

theorem ht_sub_single0 (β : Rt) (i : Fin (Tag.rank .E7)) : ht (β - Pi.single i 1) = ht β - 1 := by
  have h := S81Z.ht_add (β - Pi.single i 1) (Pi.single i 1)
  rw [sub_add_cancel, ht_single_one0] at h
  omega

theorem ht_pos_Psi0 {γ : Rt} (hγ : γ ∈ Psi0) : 0 < ht γ := (mem_Rd6.1 (Psi0_subset_Rd6 hγ)).2

theorem exists_translate0 (H : ℕ) : ∀ n : ND K, (∃ β : ↥Psi0, n β ≠ 0 ∧ ht β.1 ≤ H) →
    ∃ g : ↥(PΛ K), tauD (AdΛ K g n) ≠ 0 := by
  induction H with
  | zero =>
    rintro n ⟨β, -, hβ⟩
    exfalso
    have := ht_pos_Psi0 β.2
    simp only [Nat.cast_zero] at hβ
    omega
  | succ H ih =>
    rintro n ⟨β, hβn, hβH⟩
    by_cases hlow : ht β.1 ≤ H
    · exact ih n ⟨β, hβn, hlow⟩
    by_cases hb : β.1 = alphaA2
    · refine ⟨1, ?_⟩
      have h1 : β = ⟨alphaA2, alphaA2_mem⟩ := Subtype.ext hb
      subst h1
      simpa [tauD] using hβn
    · have hP := mem_Psi0.1 β.2
      have hP' := perp_iff.1 hP.1
      obtain ⟨i, hi, hi1, m, hm⟩ := exists_down_simple0 β.1 hP'.1 hP'.2 hP.2 hb
      have hγroot : IsRoot .E7 (Pi.single i 1 : Rt) := IsRoot.basis i
      have hγP : (Pi.single i 1 : Rt) ∈ Perp := single_mem_Perp0 i hi1
      have hγpr : pr (a0 : Fin e7Data.d) (Pi.single i 1 : Rt) = 0 := pr_single_ne0 i hi hi1
      have hδroot : IsRoot .E7 (β.1 - Pi.single i 1) := hm ▸ isRoot_cert0 m
      have hδmem : β.1 - Pi.single i 1 ∈ Psi0 := by
        refine mem_Psi0.2 ⟨perp_iff.2 ⟨hδroot, ?_⟩, ?_⟩
        · show β.1 node1 - (Pi.single i 1 : Rt) node1 = 0
          rw [hP'.2, Pi.single_eq_of_ne (show node1 ≠ i from fun h => hi1 h.symm), sub_zero]
        · show β.1 nodeA2 - (Pi.single i 1 : Rt) nodeA2 = 1
          rw [hP.2, Pi.single_eq_of_ne (show nodeA2 ≠ i from fun h => hi h.symm), sub_zero]
      set δ : ↥Psi0 := ⟨β.1 - Pi.single i 1, hδmem⟩ with hδ
      have hhtδ : ht δ.1 ≤ H := by
        have := ht_sub_single0 β.1 i
        have h2 : ht δ.1 = ht β.1 - 1 := this
        push_cast at hβH
        omega
      by_cases hnδ : n δ ≠ 0
      · exact ih n ⟨δ, hnδ, hhtδ⟩
      · push Not at hnδ
        have hcoord := Ad_xE_neg_coord0 (K := K) (Pi.single i 1) hγP hγpr n δ β
          (by rw [hδ]; exact sub_add_cancel _ _)
        obtain ⟨g, hg⟩ := ih (AdΛ K ⟨⟨xE (-(Pi.single i 1 : Rt)) 1,
          xE_mem_LamG (neg_mem_Perp hγP) 1⟩, xE_mem_linNorm0 (neg_mem_Perp hγP)
          (Or.inl (by rw [pr_neg0, hγpr, neg_zero])) 1⟩ n) ⟨δ, by rw [hcoord, hnδ, zero_add]; exact hβn,
          hhtδ⟩
        refine ⟨g * ⟨⟨xE (-(Pi.single i 1 : Rt)) 1, xE_mem_LamG (neg_mem_Perp hγP) 1⟩,
          xE_mem_linNorm0 (neg_mem_Perp hγP) (Or.inl (by rw [pr_neg0, hγpr, neg_zero])) 1⟩, ?_⟩
        rw [map_mul, LinearEquiv.mul_apply]
        exact hg

theorem lemmaS_D (n : ND K) (hn : n ≠ 0) : ∃ g : ↥(PΛ K), tauD (AdΛ K g n) ≠ 0 := by
  obtain ⟨β, hβ⟩ := Function.ne_iff.1 hn
  refine exists_translate0 (ht β.1).toNat n ⟨β, hβ, ?_⟩
  exact Int.self_le_toNat _

@[expose] noncomputable def rootDatumLam (K : Type) [Field K] [CharP K 2] : RootDatum K ↥(LamG K) where
  N := ND K
  u := uΛ
  u_add := uΛ_add
  τ := tauD
  n₁ := n1D
  τ_n₁ := tauD_n1D
  P := PΛ K
  Ad := AdΛ K
  u_Ad := fun g n => uΛ_AdΛ g n
  d := dHomD
  Ad_d := Ad_dD
  s := sD K
  s_sq := sD_sq
  s_d := sD_dD
  ker_stab := ker_stab_D
  lemmaS := lemmaS_D
  braid := by
    have h1 : uΛ ((1 : K) • (n1D : ND K)) = ⟨xE alphaA2 1, xE_mem_LamG alphaA2_mem_Perp 1⟩ := by
      refine Subtype.ext ?_
      rw [one_smul, n1D]
      exact uD_single ⟨alphaA2, alphaA2_mem⟩ 1
    rw [h1]
    refine Subtype.ext ?_
    exact braidD

end CFSG.RankThree.GF2n.Smith81.D6Spin
