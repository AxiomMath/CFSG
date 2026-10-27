module

public import CFSG.RankThree.GF2n.Smith81.S81ZRDP
public import CFSG.RankThree.GF2n.Smith81.S81VRoot

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81V
open scoped commutatorElement

abbrev nodeA : Fin (Tag.rank .E7) := ⟨6, by decide⟩

abbrev alpha7 : Rt := Pi.single nodeA 1

theorem isRoot_alpha7 : IsRoot .E7 alpha7 := IsRoot.basis nodeA

theorem pr_alpha7 : pr a7 alpha7 = 1 := by
  unfold pr
  decide +kernel

theorem alpha7_mem : alpha7 ∈ Phi a7 := mem_Phi.2 ⟨isRoot_alpha7, pr_alpha7⟩

variable {K : Type} [Field K] [CharP K 2]

@[expose] def tauN : NU K →ₗ[K] K := LinearMap.proj (⟨alpha7, alpha7_mem⟩ : ↥(Phi a7))

@[expose] def n1N : NU K := Pi.single (⟨alpha7, alpha7_mem⟩ : ↥(Phi a7)) 1

theorem tauN_n1N : tauN (n1N : NU K) = 1 := by
  simp [tauN, n1N]

abbrev PN (K : Type) [Field K] [CharP K 2] : Subgroup (Gp K) :=
  linNorm (K := K) (uN : NU K → Gp K) uN_injective

noncomputable abbrev AdN (K : Type) [Field K] [CharP K 2] : ↥(PN K) →* (NU K ≃ₗ[K] NU K) :=
  linAd (K := K) (uN : NU K → Gp K) uN_injective

@[expose] def dHomN : Kˣ →* ↥(PN K) where
  toFun c := ⟨e7Data_valid.hm K nodeA c, hm_mem_linNorm nodeA c⟩
  map_one' := Subtype.ext (e7Data_valid.hm_one K nodeA)
  map_mul' c c' := Subtype.ext (e7Data_valid.hm_mul K nodeA c c')

theorem toWeight_alpha7 : MinData.toWeight alpha7 nodeA = 2 := by
  unfold alpha7
  rw [MinData.toWeight_single]
  exact Tag.cartan_self _ _

theorem Ad_dN (c : Kˣ) :
    AdN K (dHomN c) (n1N : NU K) = (c : K) ^ 2 • (n1N : NU K) := by
  have h := linAd_hm (K := K) nodeA c n1N
  show linAd (K := K) uN uN_injective ⟨e7Data_valid.hm K nodeA c, hm_mem_linNorm nodeA c⟩ n1N = _
  rw [h, n1N, diagN_single, toWeight_alpha7]
  funext δ
  by_cases hδ : δ = (⟨alpha7, alpha7_mem⟩ : ↥(Phi a7))
  · subst hδ
    simp
  · simp [Pi.single_apply, hδ]

@[expose] def sN (K : Type) [Field K] : Gp K := e7Data_valid.nm K nodeA

theorem neg_one_unit : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])

theorem sN_sq : sN K * sN K = 1 := by
  have h := e7Data_valid.nm_sq K nodeA
  rw [pow_two, neg_one_unit] at h
  rw [sN]
  rw [h]
  exact e7Data_valid.hm_one K nodeA

theorem sN_inv : (sN K)⁻¹ = sN K := inv_eq_of_mul_eq_one_right sN_sq

theorem hm_inv_unit (i : Fin (Tag.rank .E7)) (c : Kˣ) :
    e7Data_valid.hm K i c⁻¹ = (e7Data_valid.hm K i c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← e7Data_valid.hm_mul K i c c⁻¹, mul_inv_cancel]
  exact e7Data_valid.hm_one K i

theorem sN_dN (c : Kˣ) :
    sN K * ((dHomN c : ↥(PN K)) : Gp K) * sN K = ((dHomN c : ↥(PN K)) : Gp K)⁻¹ := by
  have h := e7Data_valid.nm_conj_hm K nodeA nodeA c
  rw [Tag.cartan_self, ← e7Data_valid.hm_mul K nodeA c] at h
  have h2 : c * c ^ (-(2 : ℤ)) = c⁻¹ := by group
  rw [h2] at h
  calc sN K * e7Data_valid.hm K nodeA c * sN K
      = sN K * e7Data_valid.hm K nodeA c * (sN K)⁻¹ := by rw [sN_inv]
    _ = e7Data_valid.hm K nodeA c⁻¹ := h
    _ = (e7Data_valid.hm K nodeA c)⁻¹ := hm_inv_unit nodeA c

theorem sN_conj_xE {γ : Rt} (hγ : IsRoot .E7 γ) (c : K) :
    sN K * xE γ c * sN K = xE (reflect .E7 nodeA γ) c := by
  obtain ⟨σ, hσ, h⟩ := e7Data_valid.nm_conj_xm K hγ nodeA
  have hσ1 : σ = 1 := by
    rcases hσ with h1 | h1
    · exact h1
    · rw [h1]
      exact CharTwo.neg_eq (1 : K)
  calc sN K * xE γ c * sN K = sN K * xE γ c * (sN K)⁻¹ := by rw [sN_inv]
    _ = xE (reflect .E7 nodeA γ) (σ * c) := h c
    _ = xE (reflect .E7 nodeA γ) c := by rw [hσ1, one_mul]

theorem sN_eq : sN K = xE alpha7 1 * xE (-alpha7) 1 * xE alpha7 1 := by
  have h1 : (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) = 1 := by simp [CharTwo.neg_eq]
  show e7Data_valid.nt K nodeA 1 = _
  unfold MinData.Valid.nt
  rw [h1]
  rfl

theorem braidN : sN K = xE alpha7 1 * (sN K * xE alpha7 1 * sN K) * xE alpha7 1 := by
  rw [sN_conj_xE isRoot_alpha7 (1 : K), alpha7, reflect_single_self]
  exact sN_eq

theorem refl_pr_mem : ∀ γ : Rt, IsRoot .E7 γ → pr a7 γ = 1 → γ ≠ alpha7 →
    (pr a7 (reflect .E7 nodeA γ) = 0 ∨ pr a7 (reflect .E7 nodeA γ) = 1) := by
  refine (forall_isRoot_iff fun γ => pr a7 γ = 1 → γ ≠ alpha7 →
    (pr a7 (reflect .E7 nodeA γ) = 0 ∨ pr a7 (reflect .E7 nodeA γ) = 1)).2 ?_
  unfold pr alpha7 nodeA reflect
  decide +kernel

theorem exists_down_simple : ∀ γ : Rt, IsRoot .E7 γ → pr a7 γ = 1 → γ ≠ alpha7 →
    ∃ i : Fin (Tag.rank .E7), i ≠ nodeA ∧ ∃ m : Fin 126,
      (Tag.rootCertificate .E7).root m = γ - Pi.single i 1 := by
  refine (forall_isRoot_iff fun γ => pr a7 γ = 1 → γ ≠ alpha7 →
    ∃ i : Fin (Tag.rank .E7), i ≠ nodeA ∧ ∃ m : Fin 126,
      (Tag.rootCertificate .E7).root m = γ - Pi.single i 1).2 ?_
  unfold pr alpha7 nodeA
  decide +kernel

theorem ht_pos_psi : ∀ γ : Rt, IsRoot .E7 γ → pr a7 γ = 1 → 0 < ht γ := by
  refine (forall_isRoot_iff fun γ => pr a7 γ = 1 → 0 < ht γ).2 ?_
  unfold pr
  decide +kernel

theorem pr_single_ne (i : Fin (Tag.rank .E7)) (hi : i ≠ nodeA) : pr a7 (Pi.single i 1 : Rt) = 0 := by
  revert i
  unfold pr nodeA
  decide +kernel

theorem pr_neg (a : Fin e7Data.d) (γ : Rt) : pr a (-γ) = - pr a γ := by
  unfold pr
  exact dotProduct_neg _ _

theorem pr_sub (a : Fin e7Data.d) (γ δ : Rt) : pr a (γ - δ) = pr a γ - pr a δ := by
  unfold pr
  exact dotProduct_sub _ _ _

theorem conj_list_prod {G : Type*} [Group G] (g : G) (l : List G) :
    g * l.prod * g⁻¹ = (l.map fun x => g * x * g⁻¹).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [← ih]
    group

theorem ker_stab_N (n : NU K) (hn : tauN n = 0) :
    ∃ g : ↥(PN K), (g : Gp K) = sN K * uN n * sN K := by
  refine ⟨⟨sN K * uN n * sN K, ?_⟩, rfl⟩
  have hu : uN n = ((Phi a7).toList.map fun β => xE β (extN n β)).prod := rfl
  have key := conj_list_prod (sN K) ((Phi a7).toList.map fun β => xE β (extN n β))
  rw [sN_inv, ← hu] at key
  rw [key]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hy
  have hβa : β ∈ Phi a7 := Finset.mem_toList.1 hβ
  have hroot : IsRoot .E7 β := (mem_Phi.1 hβa).1
  rw [sN_conj_xE hroot]
  by_cases hb : β = alpha7
  · subst hb
    have : extN n alpha7 = 0 := by
      rw [extN_of_mem alpha7_mem]
      exact hn
    rw [this, xE_zero]
    exact Subgroup.one_mem _
  · exact xE_mem_linNorm (hroot.reflect nodeA) (refl_pr_mem β hroot (mem_Phi.1 hβa).2 hb) _

theorem Ad_xE_neg_coord (γ : Rt) (hγ : IsRoot .E7 γ) (hpr : pr a7 γ = 0) (n : NU K)
    (δ β : ↥(Phi a7)) (hδβ : δ.1 + γ = β.1) :
    AdN K ⟨xE (-γ) 1, xE_mem_linNorm (isRoot_neg hγ) (Or.inl (by rw [pr_neg, hpr, neg_zero])) 1⟩ n δ
      = n δ + n β := by
  have h := linAd_xE (K := K) (isRoot_neg hγ) (Or.inl (by rw [pr_neg, hpr, neg_zero])) 1 n
  have h2 : (AdN K ⟨xE (-γ) 1, xE_mem_linNorm (isRoot_neg hγ)
      (Or.inl (by rw [pr_neg, hpr, neg_zero])) 1⟩) n = n + (1 : K) • shiftN (-γ) n := h
  rw [h2, Pi.add_apply, Pi.smul_apply, shiftN_apply, smul_eq_mul, one_mul]
  unfold shiftFun
  have hmem : δ.1 - -γ ∈ Phi a7 := by
    rw [sub_neg_eq_add, hδβ]
    exact β.2
  have h3 : (⟨δ.1 - -γ, hmem⟩ : ↥(Phi a7)) = β :=
    Subtype.ext (show δ.1 - -γ = β.1 by rw [sub_neg_eq_add, hδβ])
  rw [dif_pos hmem, h3]

theorem isRoot_cert (m : Fin 126) : IsRoot .E7 ((Tag.rootCertificate .E7).root m) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) m (by omega)

theorem ht_single_one (i : Fin (Tag.rank .E7)) : ht (Pi.single i 1 : Rt) = 1 := by
  simp [ht]

theorem ht_sub_single (β : Rt) (i : Fin (Tag.rank .E7)) : ht (β - Pi.single i 1) = ht β - 1 := by
  have h := ht_add (β - Pi.single i 1) (Pi.single i 1)
  rw [sub_add_cancel, ht_single_one] at h
  omega

theorem exists_translate (H : ℕ) : ∀ n : NU K, (∃ β : ↥(Phi a7), n β ≠ 0 ∧ ht β.1 ≤ H) →
    ∃ g : ↥(PN K), tauN (AdN K g n) ≠ 0 := by
  induction H with
  | zero =>
    rintro n ⟨β, -, hβ⟩
    exfalso
    have := ht_pos_psi β.1 (mem_Phi.1 β.2).1 (mem_Phi.1 β.2).2
    simp only [Nat.cast_zero] at hβ
    omega
  | succ H ih =>
    rintro n ⟨β, hβn, hβH⟩
    by_cases hlow : ht β.1 ≤ H
    · exact ih n ⟨β, hβn, hlow⟩
    by_cases hb : β.1 = alpha7
    · refine ⟨1, ?_⟩
      have h1 : β = ⟨alpha7, alpha7_mem⟩ := Subtype.ext hb
      subst h1
      simpa [tauN] using hβn
    · obtain ⟨i, hi, m, hm⟩ := exists_down_simple β.1 (mem_Phi.1 β.2).1 (mem_Phi.1 β.2).2 hb
      have hγroot : IsRoot .E7 (Pi.single i 1 : Rt) := IsRoot.basis i
      have hγpr : pr a7 (Pi.single i 1 : Rt) = 0 := pr_single_ne i hi
      have hδroot : IsRoot .E7 (β.1 - Pi.single i 1) := hm ▸ isRoot_cert m
      have hδpr : pr a7 (β.1 - Pi.single i 1) = 1 := by
        rw [pr_sub, (mem_Phi.1 β.2).2, hγpr]
        norm_num
      have hδmem : β.1 - Pi.single i 1 ∈ Phi a7 := mem_Phi.2 ⟨hδroot, hδpr⟩
      set δ : ↥(Phi a7) := ⟨β.1 - Pi.single i 1, hδmem⟩ with hδ
      have hhtδ : ht δ.1 ≤ H := by
        have := ht_sub_single β.1 i
        have h2 : ht δ.1 = ht β.1 - 1 := this
        push_cast at hβH
        omega
      by_cases hnδ : n δ ≠ 0
      · exact ih n ⟨δ, hnδ, hhtδ⟩
      · push Not at hnδ
        have hcoord := Ad_xE_neg_coord (K := K) (Pi.single i 1) hγroot hγpr n δ β
          (by rw [hδ]; exact sub_add_cancel _ _)
        obtain ⟨g, hg⟩ := ih (AdN K ⟨xE (-(Pi.single i 1 : Rt)) 1, xE_mem_linNorm (isRoot_neg hγroot)
          (Or.inl (by rw [pr_neg, hγpr, neg_zero])) 1⟩ n) ⟨δ, by rw [hcoord, hnδ, zero_add]; exact hβn, hhtδ⟩
        refine ⟨g * ⟨xE (-(Pi.single i 1 : Rt)) 1, xE_mem_linNorm (isRoot_neg hγroot)
          (Or.inl (by rw [pr_neg, hγpr, neg_zero])) 1⟩, ?_⟩
        rw [map_mul, LinearEquiv.mul_apply]
        exact hg

theorem lemmaS_N (n : NU K) (hn : n ≠ 0) : ∃ g : ↥(PN K), tauN (AdN K g n) ≠ 0 := by
  obtain ⟨β, hβ⟩ := Function.ne_iff.1 hn
  refine exists_translate (ht β.1).toNat n ⟨β, hβ, ?_⟩
  exact Int.self_le_toNat _

@[expose] noncomputable def rootDatumE7 (K : Type) [Field K] [CharP K 2] : RootDatum K (Gp K) where
  N := NU K
  u := uN
  u_add := uN_add
  τ := tauN
  n₁ := n1N
  τ_n₁ := tauN_n1N
  P := PN K
  Ad := AdN K
  u_Ad := fun g n => u_linAd uN uN_injective g n
  d := dHomN
  Ad_d := Ad_dN
  s := sN K
  s_sq := sN_sq
  s_d := sN_dN
  ker_stab := ker_stab_N
  lemmaS := lemmaS_N
  braid := by
    have h1 : uN ((1 : K) • (n1N : NU K)) = xE alpha7 1 := by
      rw [one_smul, n1N, uN_single]
    rw [h1]
    exact braidN

end CFSG.RankThree.GF2n.Smith81.S81Z
