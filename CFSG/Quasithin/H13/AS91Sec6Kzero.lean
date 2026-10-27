module

public import CFSG.Quasithin.H13.AS91Sec5ResFacts
public import Certificates.Certificate89023

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem kz_repT_one : RepT Native.kzeroId 1 := by
  unfold RepT
  decide +kernel

theorem kz_repT_mul {a b : Array ℕ} {σ τ : S24} (ha : RepT a σ) (hb : RepT b τ) :
    RepT (Native.kzeroMul a b) (σ * τ) := by
  intro i
  have hi : i.val < ((Array.range 24).map fun j => a[b[j]!]!).size := by simp
  have h1 : (Native.kzeroMul a b)[i.val]! = a[b[i.val]!]! := by
    unfold Native.kzeroMul
    rw [getElem!_pos ((Array.range 24).map fun j => a[b[j]!]!) i.val hi]
    simp
  rw [h1, hb i]
  exact ha (τ i)

theorem kz_size_mul (a b : Array ℕ) : (Native.kzeroMul a b).size = 24 := by
  simp [Native.kzeroMul]

theorem kz_repT_conj {p : Array ℕ × Array ℕ} {σ : S24} (h1 : RepT p.1 σ) (h2 : RepT p.2 σ⁻¹)
    {x : Array ℕ} {τ : S24} (hx : RepT x τ) : RepT (Native.kzeroConj p x) (σ * τ * σ⁻¹) := by
  unfold Native.kzeroConj
  rw [mul_assoc]
  exact kz_repT_mul h1 (kz_repT_mul hx h2)

theorem kz_repT_unique {a : Array ℕ} {σ τ : S24} (hσ : RepT a σ) (hτ : RepT a τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).symm.trans (hτ i))

theorem kz_eq_of_repT {a b : Array ℕ} {σ : S24} (ha : RepT a σ) (hb : RepT b σ)
    (sa : a.size = 24) (sb : b.size = 24) : a = b := by
  refine Array.ext (sa.trans sb.symm) fun i hia hib => ?_
  have h := (ha ⟨i, sa ▸ hia⟩).trans (hb ⟨i, sa ▸ hia⟩).symm
  simpa [getElem!_pos a i hia, getElem!_pos b i hib] using h

open Classical in
@[expose] noncomputable def kzPerm (t : Array ℕ) : S24 :=
  if h : ∃ σ : S24, RepT t σ then h.choose else 1

theorem kzPerm_repT {t : Array ℕ} {σ : S24} (h : RepT t σ) : RepT t (kzPerm t) := by
  have h' : ∃ σ : S24, RepT t σ := ⟨σ, h⟩
  rw [kzPerm, dif_pos h']
  exact h'.choose_spec

theorem kzPerm_eq {t : Array ℕ} {σ : S24} (h : RepT t σ) : kzPerm t = σ :=
  kz_repT_unique (kzPerm_repT h) h

theorem kz_card_image {L : List (Array ℕ)} (hnd : L.Nodup) (hsz : ∀ t ∈ L, t.size = 24)
    (hex : ∀ t ∈ L, ∃ σ : S24, RepT t σ) : (L.toFinset.image kzPerm).card = L.length := by
  classical
  rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
  intro t ht t' ht' h
  have ht1 := List.mem_toFinset.1 ht
  have ht2 := List.mem_toFinset.1 ht'
  obtain ⟨σ, hr⟩ := hex t ht1
  obtain ⟨σ', hr'⟩ := hex t' ht2
  have e1 := kzPerm_repT hr
  have e2 := kzPerm_repT hr'
  have h' : kzPerm t = kzPerm t' := h
  rw [h'] at e1
  exact kz_eq_of_repT e1 e2 (hsz t ht1) (hsz t' ht2)

theorem kz_repT_of_tree {H : Subgroup S24} {gens : List (Array ℕ)} {m : ℕ}
    (hm : gens.length = m) (P : Fin m → S24) (hP : ∀ j, P j ∈ H)
    (hrep : ∀ j : Fin m, RepT (gens.getD j #[]) (P j))
    {valid : Array ℕ → Bool} {base : Array ℕ} (hb : RepT base 1)
    {r : Array (Array ℕ) × Array ℕ × Array ℕ}
    (h : Native.treeValid valid (gens.map Native.kzeroMul) base r = true) :
    ∀ q ∈ r.1.toList, ∃ σ ∈ H, RepT q σ := by
  obtain ⟨-, h0, hall⟩ := treeValid_get h
  have key : ∀ j, j < r.1.size → ∃ σ ∈ H, RepT r.1[j]! σ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases (hall j hj).2 with rfl | ⟨hpar, hgen, hstp⟩
      · exact ⟨1, H.one_mem, by rw [h0]; exact hb⟩
      · obtain ⟨σ, hσ, hσf⟩ := ih r.2.1[j]! hpar (lt_trans hpar hj)
        have hgm : r.2.2[j]! < m := hm ▸ (by simpa using hgen)
        refine ⟨P ⟨r.2.2[j]!, hgm⟩ * σ, H.mul_mem (hP _) hσ, ?_⟩
        have e : ((gens.map Native.kzeroMul).getD r.2.2[j]! id) r.1[r.2.1[j]!]! =
            Native.kzeroMul (gens.getD r.2.2[j]! #[]) r.1[r.2.1[j]!]! := by
          rw [getD_map_of_lt _ gens #[] id (hm ▸ hgm)]
        rw [← hstp, e]
        exact kz_repT_mul (hrep ⟨r.2.2[j]!, hgm⟩) hσf
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hq)
  obtain ⟨σ, hσ, hσf⟩ := key j hj
  rw [getElem!_pos r.1 j hj] at hσf
  exact ⟨σ, hσ, hσf⟩

@[expose] def kzCj : Fin 8 → S24 :=
  ![uPerm 0, uPerm 1, uPerm 2, uPerm 3, (uPerm 0)⁻¹, (uPerm 1)⁻¹, (uPerm 2)⁻¹, (uPerm 3)⁻¹]

theorem kz_Cj_rep (j : Fin 8) :
    RepT ((Native.kzeroHs ()).getD j (#[], #[])).1 (kzCj j) ∧
      RepT ((Native.kzeroHs ()).getD j (#[], #[])).2 (kzCj j)⁻¹ := by
  revert j
  unfold RepT
  decide +kernel

theorem kzCj_mem (j : Fin 8) : kzCj j ∈ M24g := by
  fin_cases j
  · exact uPerm_mem 0
  · exact uPerm_mem 1
  · exact uPerm_mem 2
  · exact uPerm_mem 3
  · exact M24g.inv_mem (uPerm_mem 0)
  · exact M24g.inv_mem (uPerm_mem 1)
  · exact M24g.inv_mem (uPerm_mem 2)
  · exact M24g.inv_mem (uPerm_mem 3)

@[expose] def kzPair : Array ℕ × Array ℕ := (Native.kzeroHs ()).getD 4 (#[], #[])

theorem kz_pair_rep : RepT kzPair.1 (uPerm 0)⁻¹ ∧ RepT kzPair.2 (uPerm 0)⁻¹⁻¹ := by
  unfold RepT kzPair
  decide +kernel

@[expose] def kzK (r : Array (Array ℕ) × Array ℕ × Array ℕ) : List (Array ℕ) :=
  Native.kzeroK0 r.1 kzPair

structure KzeroData (r : Array (Array ℕ) × Array ℕ × Array ℕ) : Prop where
  tree : Native.treeValid Native.kzeroValid (Native.s0Tabs.map Native.kzeroMul) Native.kzeroId r =
    true
  size : r.1.size = 1024
  nodup : (r.1.toList.map Native.kzeroKey).Nodup
  ufix : Native.kzeroUFix () = true
  card : (kzK r).length = 64
  deriv : ∀ k ∈ kzK r, k = Native.kzeroId ∨ ∃ D : Array Native.KzEntry,
    Native.kzeroDerivValid (Native.kzeroHs ()) k D = true ∧ ∀ x ∈ kzK r, ∃ j < D.size, D[j]!.tab = x

theorem kz_syl_mem {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r) :
    ∀ t ∈ r.1.toList, ∃ σ ∈ sylS0, RepT t σ :=
  kz_repT_of_tree (H := sylS0) (gens := Native.s0Tabs) (m := 4) rfl s0Perm s0Perm_mem_sylS0
    repT_s0Perm kz_repT_one hd.tree

theorem kz_size_of_mem {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r) :
    ∀ t ∈ r.1.toList, t.size = 24 := by
  intro t ht
  have h := treeValid_valid hd.tree t ht
  simpa [Native.kzeroValid] using h

theorem kz_K_sub {r : Array (Array ℕ) × Array ℕ × Array ℕ} {t : Array ℕ} (ht : t ∈ kzK r) :
    t ∈ r.1.toList ∧ Native.kzeroConj kzPair t ∈ r.1.toList := by
  unfold kzK Native.kzeroK0 at ht
  rw [List.mem_filter] at ht
  exact ⟨ht.1, Array.mem_toList_iff.2 (Array.contains_iff_mem.1 ht.2)⟩

theorem kz_K_size {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r) :
    ∀ t ∈ kzK r, t.size = 24 := fun t ht => kz_size_of_mem hd t (kz_K_sub ht).1

theorem kz_K_nodup {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r) :
    (kzK r).Nodup :=
  List.Nodup.filter _ (List.Nodup.of_map _ hd.nodup)

theorem kz_deriv_mem (N : Subgroup S24)
    (hcj : ∀ j : Fin 8, ∀ n ∈ N, kzCj j * n * (kzCj j)⁻¹ ∈ N) {k : Array ℕ}
    (hk : ∃ σ ∈ N, RepT k σ) {D : Array Native.KzEntry}
    (hD : Native.kzeroDerivValid (Native.kzeroHs ()) k D = true) :
    ∀ j < D.size, ∃ σ ∈ N, RepT D[j]!.tab σ := by
  unfold Native.kzeroDerivValid at hD
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Native.allLt_iff,
    Bool.or_eq_true] at hD
  obtain ⟨⟨-, h0⟩, hall⟩ := hD
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases hall j hj with (hj0 | ⟨⟨⟨-, hlen⟩, hb⟩, htab⟩) | ⟨⟨⟨-, ha⟩, hb⟩, htab⟩
    · subst hj0
      rw [h0]
      exact hk
    · obtain ⟨σ, hσ, hrep⟩ := ih D[j]!.b hb (lt_trans hb hj)
      have hlen' : D[j]!.a < 8 := by
        have : (Native.kzeroHs ()).length = 8 := by decide +kernel
        omega
      have hCj := kz_Cj_rep ⟨D[j]!.a, hlen'⟩
      refine ⟨kzCj ⟨D[j]!.a, hlen'⟩ * σ * (kzCj ⟨D[j]!.a, hlen'⟩)⁻¹, hcj _ σ hσ, ?_⟩
      rw [htab]
      exact kz_repT_conj hCj.1 hCj.2 hrep
    · obtain ⟨σ, hσ, hσr⟩ := ih D[j]!.a ha (lt_trans ha hj)
      obtain ⟨τ, hτ, hτr⟩ := ih D[j]!.b hb (lt_trans hb hj)
      refine ⟨σ * τ, N.mul_mem hσ hτ, ?_⟩
      rw [htab]
      exact kz_repT_mul hσr hτr

@[expose] noncomputable def K0base : Subgroup S24 :=
  sylS0 ⊓ sylS0.comap (MulAut.conj (uPerm 0)⁻¹).toMonoidHom

theorem mem_K0base {k : S24} :
    k ∈ K0base ↔ k ∈ sylS0 ∧ (uPerm 0)⁻¹ * k * (uPerm 0)⁻¹⁻¹ ∈ sylS0 := Iff.rfl

theorem K0base_le_sylS0 : K0base ≤ sylS0 := inf_le_left

theorem K0base_le : K0base ≤ M24g := K0base_le_sylS0.trans sylS0_le

section Cert89023

theorem kzeroData : KzeroData (Native.kzeroSyl ()) :=
  have h := Certificates.certificate89023
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Cert89023

section Cert89021

theorem sylS0_fix_sext {x : S24} (hx : x ∈ sylS0) : x ∈ M24g ∧ x • sextFin 0 = sextFin 0 := by
  have hle : sylS0 ≤ M24g ⊓ MulAction.stabilizer S24 (sextFin 0) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨s0Perm_mem j, MulAction.mem_stabilizer_iff.2 ?_⟩
    obtain ⟨-, -, h3, -⟩ := s0Fix_spec _ (s0Tabs_getD_mem j)
    rw [smul_sextFin (q := 0) (repT_s0Perm j) zero_lt_1771, sextList_zero, h3, sextFin,
      sextList_zero]
  exact ⟨(hle hx).1, MulAction.mem_stabilizer_iff.1 (hle hx).2⟩

section Cert3017

theorem kz_syl_enum {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r) :
    ∀ x ∈ sylS0, ∃ t ∈ r.1.toList, RepT t x := by
  classical
  have hmem := kz_syl_mem hd
  have hsz := kz_size_of_mem hd
  have hnd : r.1.toList.Nodup := List.Nodup.of_map _ hd.nodup
  have hex : ∀ t ∈ r.1.toList, ∃ σ : S24, RepT t σ := fun t ht =>
    (hmem t ht).elim fun σ h => ⟨σ, h.2⟩
  have hsub :
      ((r.1.toList.toFinset.image kzPerm : Finset S24) : Set S24) ⊆ (sylS0 : Set S24) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨σ, hσ, hrep⟩ := hmem t (List.mem_toFinset.1 ht)
    rw [kzPerm_eq hrep]
    exact hσ
  have hcard : (r.1.toList.toFinset.image kzPerm).card = 1024 := by
    rw [kz_card_image hnd hsz hex]
    simpa using hd.size
  have hsyl : (sylS0 : Set S24).ncard = 1024 := by
    rw [← Nat.card_coe_set_eq]
    have h := card_sylS0
    exact h.trans (by norm_num)
  have heq :
      ((r.1.toList.toFinset.image kzPerm : Finset S24) : Set S24) = (sylS0 : Set S24) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hcard, hsyl]
  intro x hx
  have hx' : x ∈ ((r.1.toList.toFinset.image kzPerm : Finset S24) : Set S24) := heq ▸ hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx')
  obtain ⟨σ, -, hr⟩ := hmem t (List.mem_toFinset.1 ht)
  exact ⟨t, List.mem_toFinset.1 ht, kzPerm_repT hr⟩

theorem le_sylS0_of_normalized (N : Subgroup S24) (hNM : N ≤ M24g) (hN2 : IsPGroup 2 N)
    (hxn : ∀ x ∈ sylS0, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : N ≤ sylS0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 sylS0 := IsPGroup.of_card (n := 10) card_sylS0
  have hnorm : sylS0 ≤ Subgroup.normalizer (N : Set S24) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hxn x hx n hn, fun h => ?_⟩
    have h1 := hxn x⁻¹ (sylS0.inv_mem hx) _ h
    have e : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
    rwa [e] at h1
  have hQ : IsPGroup 2 ↥(sylS0 ⊔ N) := hS.to_sup_of_normal_right' hN2 hnorm
  have hle : sylS0 ⊔ N ≤ M24g := sup_le sylS0_le hNM
  have hG : Nat.card ↥M24g = 244823040 := CFSG.Monster.Code.card_AutPerm
  have hdvd : Nat.card ↥(sylS0 ⊔ N) ∣ 244823040 := hG ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ
  have hk10 : k ≤ 10 := by
    by_contra hcon
    have h1 : 2 ^ 11 ∣ 244823040 :=
      (pow_dvd_pow 2 (by omega : 11 ≤ k)).trans (hk ▸ hdvd)
    exact absurd h1 (by norm_num)
  have hcard : Nat.card ↥(sylS0 ⊔ N) ≤ Nat.card sylS0 := by
    rw [hk, card_sylS0]
    exact Nat.pow_le_pow_right (by norm_num) hk10
  have heq : sylS0 = sylS0 ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact le_sup_right

theorem mem_K0base_iff_kzK {r : Array (Array ℕ) × Array ℕ × Array ℕ} (hd : KzeroData r)
    {k : S24} : k ∈ K0base ↔ ∃ t ∈ kzK r, RepT t k := by
  have hmem := kz_syl_mem hd
  have hsz := kz_size_of_mem hd
  constructor
  · intro hk
    obtain ⟨hk1, hk2⟩ := mem_K0base.1 hk
    obtain ⟨t, ht, hrep⟩ := kz_syl_enum hd k hk1
    obtain ⟨t', ht', hrep'⟩ := kz_syl_enum hd _ hk2
    have hc := kz_repT_conj kz_pair_rep.1 kz_pair_rep.2 hrep
    have e : Native.kzeroConj kzPair t = t' :=
      kz_eq_of_repT hc hrep' (kz_size_mul _ _) (hsz t' ht')
    refine ⟨t, ?_, hrep⟩
    unfold kzK Native.kzeroK0
    rw [List.mem_filter]
    refine ⟨ht, ?_⟩
    rw [e]
    exact Array.contains_iff_mem.2 (Array.mem_toList_iff.1 ht')
  · rintro ⟨t, ht, hrep⟩
    obtain ⟨ht1, ht2⟩ := kz_K_sub ht
    obtain ⟨σ, hσ, hσr⟩ := hmem t ht1
    obtain ⟨σ', hσ', hσr'⟩ := hmem _ ht2
    have hk : σ = k := kz_repT_unique hσr hrep
    subst hk
    have hc := kz_repT_conj kz_pair_rep.1 kz_pair_rep.2 hσr
    have e : σ' = (uPerm 0)⁻¹ * σ * (uPerm 0)⁻¹⁻¹ := kz_repT_unique hσr' hc
    exact mem_K0base.2 ⟨hσ, e ▸ hσ'⟩

end Cert3017

end Cert89021

section CertU

theorem kzCj_fix (j : Fin 8) : kzCj j • sextFin 0 = sextFin 0 := by
  have hu : ∀ i : Fin 4, uPerm i • sextFin 0 = sextFin 0 := by
    intro i
    have h1 : Native.imgSext (Native.uTabs.getD i #[]) Native.baseSext = Native.baseSext :=
      beq_iff_eq.1 (List.all_eq_true.1 kzeroData.ufix _ (uTabs_getD_mem i))
    rw [smul_sextFin (q := 0) (repT_uPerm i) zero_lt_1771, sextList_zero, h1, sextFin,
      sextList_zero]
  fin_cases j
  · exact hu 0
  · exact hu 1
  · exact hu 2
  · exact hu 3
  · exact (inv_smul_eq_iff.2 (hu 0).symm)
  · exact (inv_smul_eq_iff.2 (hu 1).symm)
  · exact (inv_smul_eq_iff.2 (hu 2).symm)
  · exact (inv_smul_eq_iff.2 (hu 3).symm)

end CertU

section Cert

theorem mem_K0base_iff_native {k : S24} :
    k ∈ K0base ↔ ∃ t ∈ Native.kzeroK0List (), RepT t k :=
  mem_K0base_iff_kzK kzeroData

theorem mem_K0base_of_contains {k : S24} {t : Array ℕ} (hk : RepT t k)
    (h : (Native.kzeroK0List ()).contains t = true) : k ∈ K0base :=
  mem_K0base_iff_native.2 ⟨t, List.contains_iff_mem.1 h, hk⟩

theorem card_K0base : Nat.card K0base = 2 ^ 6 := by
  classical
  have hd := kzeroData
  have hmem := kz_syl_mem hd
  have hex : ∀ t ∈ kzK (Native.kzeroSyl ()), ∃ σ : S24, RepT t σ := fun t ht =>
    (hmem t (kz_K_sub ht).1).elim fun σ h => ⟨σ, h.2⟩
  have hset : (K0base : Set S24) =
      ((kzK (Native.kzeroSyl ())).toFinset.image kzPerm : Finset S24) := by
    ext k
    constructor
    · intro hk
      obtain ⟨t, ht, hrep⟩ := (mem_K0base_iff_kzK hd).1 hk
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, List.mem_toFinset.2 ht, kzPerm_eq hrep⟩)
    · intro hk
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hk)
      obtain ⟨σ, hr⟩ := hex t (List.mem_toFinset.1 ht)
      exact (mem_K0base_iff_kzK hd).2 ⟨t, List.mem_toFinset.1 ht, kzPerm_repT hr⟩
  have h1 : Nat.card K0base = (K0base : Set S24).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_coe_finset, kz_card_image (kz_K_nodup hd) (kz_K_size hd) hex, hd.card]
  norm_num

theorem le_K0base_of_normal (N : Subgroup S24) (hNM : N ≤ M24g) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) :
    N ≤ K0base := by
  have hNle : N ≤ sylS0 := le_sylS0_of_normalized N hNM hN2 fun x hx n hn =>
    hnorm x (sylS0_fix_sext hx).1 (sylS0_fix_sext hx).2 n hn
  intro n hn
  exact mem_K0base.2 ⟨hNle hn, hNle (hnorm (kzCj 4) (kzCj_mem 4) (kzCj_fix 4) n hn)⟩

theorem K0base_le_of_ne_bot (N : Subgroup S24) (hNM : N ≤ M24g) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N)
    (hne : N ≠ ⊥) : K0base ≤ N := by
  have hd := kzeroData
  have hNK := le_K0base_of_normal N hNM hN2 hnorm
  have hcj : ∀ j : Fin 8, ∀ n ∈ N, kzCj j * n * (kzCj j)⁻¹ ∈ N := fun j n hn =>
    hnorm (kzCj j) (kzCj_mem j) (kzCj_fix j) n hn
  obtain ⟨⟨n, hn⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
  obtain ⟨t, ht, hrep⟩ := (mem_K0base_iff_kzK hd).1 (hNK hn)
  have ht1 : t ≠ Native.kzeroId := by
    rintro rfl
    exact hn1' (kz_repT_unique hrep kz_repT_one)
  obtain ⟨D, hvalid, hcover⟩ := (hd.deriv t ht).resolve_left ht1
  have hall := kz_deriv_mem N hcj ⟨n, hn, hrep⟩ hvalid
  intro x hx
  obtain ⟨t', ht', hrep'⟩ := (mem_K0base_iff_kzK hd).1 hx
  obtain ⟨j, hj, hjt⟩ := hcover t' ht'
  obtain ⟨σ, hσ, hσr⟩ := hall j hj
  rw [hjt] at hσr
  rw [kz_repT_unique hrep' hσr]
  exact hσ

theorem normal_two_subgroup_of_base_sextet (N : Subgroup S24) (hNM : N ≤ M24g)
    (hN2 : IsPGroup 2 N)
    (hnorm : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) :
    N = ⊥ ∨ N = K0base := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · exact Or.inr (le_antisymm (le_K0base_of_normal N hNM hN2 hnorm)
      (K0base_le_of_ne_bot N hNM hN2 hnorm hbot))

theorem eq_K0base_of_normal (N : Subgroup S24) (hNM : N ≤ M24g) (hN2 : IsPGroup 2 N)
    (hNU : ∀ σ ∈ N, σ • sextFin 0 = sextFin 0)
    (hnorm : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N)
    (hcard : Nat.card N = 2 ^ 6) : N = K0base := by
  clear hNU
  exact Subgroup.eq_of_le_of_card_ge (le_K0base_of_normal N hNM hN2 hnorm)
    (by rw [card_K0base, hcard])

theorem normal_two_subgroup_of_sextet {U : Finset (Finset (Fin 24))} (hU : IsSextet U)
    (N : Subgroup S24) (hNM : N ≤ M24g) (hN2 : IsPGroup 2 N) (hNU : ∀ σ ∈ N, σ • U = U)
    (hnorm : ∀ σ ∈ M24g, σ • U = U → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) :
    N = ⊥ ∨ Nat.card N = 2 ^ 6 := by
  clear hNU
  obtain ⟨g, hg, hgU⟩ := sextet_transitive hU
  let N' : Subgroup S24 := N.map (MulAut.conj g).toMonoidHom
  have hmem : ∀ x, x ∈ N' ↔ ∃ y ∈ N, g * y * g⁻¹ = x := fun x => Iff.rfl
  have hN'M : N' ≤ M24g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
    exact M24g.mul_mem (M24g.mul_mem hg (hNM hy)) (M24g.inv_mem hg)
  have hN'2 : IsPGroup 2 N' := hN2.map _
  have hgU' : g⁻¹ • sextFin 0 = U := inv_smul_eq_iff.2 hgU.symm
  have hnorm' : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N', σ * n * σ⁻¹ ∈ N' := by
    intro σ hσ hσU n hn
    obtain ⟨y, hy, rfl⟩ := (hmem n).1 hn
    have hτ : g⁻¹ * σ * g ∈ M24g := M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hg) hσ) hg
    have hτU : (g⁻¹ * σ * g) • U = U := by
      rw [mul_smul, mul_smul, hgU, hσU, hgU']
    refine (hmem _).2 ⟨(g⁻¹ * σ * g) * y * (g⁻¹ * σ * g)⁻¹, hnorm _ hτ hτU y hy, ?_⟩
    group
  have hcard : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective (MulEquiv.injective _)
  rcases normal_two_subgroup_of_base_sextet N' hN'M hN'2 hnorm' with h | h
  · left
    refine Subgroup.card_eq_one.1 ?_
    calc Nat.card N = Nat.card N' := hcard.symm
      _ = Nat.card (⊥ : Subgroup S24) := by rw [h]
      _ = 1 := Subgroup.card_bot
  · right
    rw [← hcard, h]
    exact card_K0base

end Cert

end CFSG.Quasithin.H13.AS91.M24G
