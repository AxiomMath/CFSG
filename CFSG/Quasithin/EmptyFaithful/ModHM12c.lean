module

public import CFSG.Quasithin.EmptyFaithful.ModHM12b
public import CFSG.Quasithin.EmptyFaithful.ModGSolv

public section

namespace CFSG.Quasithin.ModH.R12

open CFSG.Quasithin.ModH.S12 CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.ModG (memB memB_iff allL allL_iff ev ev_mem ev_append ev_invW ev_nil ev_cons invW)
open CFSG.Quasithin
open scoped Pointwise
open MulAction

theorem dataOK_facts {comp : ℕ → ℕ → ℕ} {kId : ℕ} {gC K : List ℕ} {j z : ℕ}
    (h : dataOK comp kId gC K (buckets K j) j z = true) :
    K.Nodup ∧ kId ∈ K ∧ (∀ k ∈ K, ∀ g ∈ gC, comp k g ∈ K) := by
  simp only [dataOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hnd, h1⟩, hcl⟩, -⟩ := h
  refine ⟨nodup_of_buckets K j hnd, (memBk_iff K j kId).1 h1, fun k hk g hg => ?_⟩
  exact (memBk_iff K j _).1 (allL_iff.1 (allL_iff.1 hcl k hk) g hg)

@[expose] def Sg : Subgroup G := Subgroup.closure {x | x ∈ tg}

theorem Sg_data : tK.Nodup ∧ kIdn 12 ∈ tK ∧ ∀ k ∈ tK, ∀ g ∈ tg, compn 12 k (cd g) ∈ tK := by
  obtain ⟨h1, h2, h3⟩ := dataOK_facts dataOK_true
  refine ⟨h1, h2, fun k hk g hg => h3 k hk (cd g) ?_⟩
  rw [← tg_codes]
  exact List.mem_map_of_mem hg

theorem tK_eq' : tW.map (evcg (compn 12) (kIdn 12) (tg.map cd)) = tK := by
  rw [tg_codes]
  exact tK_eq

theorem mem_Sg_iff (x : G) : x ∈ Sg ↔ cd x ∈ tK :=
  mem_closure_iff_code cd (compn 12) (kIdn 12) cd_mul cd_one cd_injective tg tW tK tK_eq' Sg_data.2.1
    Sg_data.2.2 x

theorem card_Sg : Nat.card Sg = 64 := by
  have := card_closure_code cd (compn 12) (kIdn 12) cd_mul cd_one cd_injective tg tW tK tK_eq'
    Sg_data.2.1 Sg_data.2.2 Sg_data.1
  rw [tK_length] at this
  exact this

theorem Sg_isPGroup : IsPGroup 2 ↥Sg := IsPGroup.of_card (n := 6) (by rw [card_Sg]; norm_num)

theorem Sg_sylow : IsSylowTwoOf Sg ⊤ := by
  rw [K1.isSylowTwoOf_top_iff]
  refine ⟨Sg_isPGroup, ?_⟩
  have h := Subgroup.card_mul_index Sg
  rw [card_Sg, show Nat.card G = Nat.card NativeSporadic.M12 from rfl, CFSG.Sporadic.Schreier.m12_card] at h
  have : Sg.index = 1485 := by omega
  rw [this]
  norm_num

@[expose] def B0 : Finset (Fin 12) := {1, 6, 8, 11}

theorem chi_B0 : chi B0 = B0l := by decide +kernel

theorem smul_chi (g : G) (B : Finset (Fin 12)) : chi (g • B) = actL (cd g) (chi B) := by
  have h : g • B = B.image g.1 := by
    ext x
    simp only [Finset.mem_smul_finset, Finset.mem_image]
    rfl
  rw [h, chi_image]
  rfl

@[expose] def K : Subgroup G := stabilizer G B0

@[expose] def rE (k : ℕ) : G := ev alph (rW.getD k [])

@[expose] def cE (i : ℕ) : G := ev alph (cW.getD i [])

theorem cd_ev_alph (w : List ℕ) : cd (ev alph w) = evcg (compn 12) (kIdn 12) aC w := by
  rw [c_evg cd (compn 12) (kIdn 12) cd_mul cd_one, alph_codes]

theorem cd_rE (k : ℕ) : cd (rE k) = evcg (compn 12) (kIdn 12) aC (rW.getD k []) := cd_ev_alph _

theorem cd_cE (i : ℕ) : cd (cE i) = evcg (compn 12) (kIdn 12) aC (cW.getD i []) := cd_ev_alph _

theorem rC_getD (k : ℕ) (hk : k < 19) : rC.getD k 0 = cd (rE k) := by
  rw [cd_rE]
  have : rW.length = 19 := by decide +kernel
  rw [rC, List.getD_eq_getElem _ _ (by simpa [this] using hk)]
  simp only [List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [this] using hk)]

theorem exists_of_mem_tK {s : ℕ} (hs : s ∈ tK) : ∃ σ ∈ Sg, cd σ = s := by
  rw [← tK_eq', List.mem_map] at hs
  obtain ⟨w, -, hw⟩ := hs
  refine ⟨ev tg w, ev_mem (fun y hy => Subgroup.subset_closure hy) w, ?_⟩
  rw [c_evg cd (compn 12) (kIdn 12) cd_mul cd_one, hw]

theorem actL_length (c : ℕ) (l : List Bool) : (actL c l).length = 12 := by simp [actL]

theorem four_set_cover (B : Finset (Fin 12)) (hB : B.card = 4) :
    ∃ σ ∈ Sg, ∃ k < 19, B = σ • (rE k • B0) := by
  have hmem := mem_allBools 12 (chi B) (chi_length B)
  have hpop : popL (chi B) = 4 := by rw [popL_chi, hB]
  have h3 := memB_iff.1 (chk1 (chi B) hmem hpop)
  simp only [Uim, List.mem_flatMap, List.mem_map] at h3
  obtain ⟨o, ho, s, hs, hso⟩ := h3
  obtain ⟨σ, hσ, rfl⟩ := exists_of_mem_tK hs
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ho
  have hlen : Om.length = 19 := chk8.2.1
  have hk19 : k < 19 := by omega
  have hOk : Om[k] = Om.getD k [] := (List.getD_eq_getElem _ _ hk).symm
  have hchi : chi B = actL (cd σ) (Om.getD k []) := by
    rw [← hOk]
    apply bn_inj
    · rw [chi_length, actL_length]
    · exact hso.symm
  refine ⟨σ, hσ, k, hk19, ?_⟩
  apply chi_inj
  rw [hchi, smul_chi, smul_chi, chi_B0, ← rC_getD k hk19, chk2 k hk19]

theorem Sg_le_K : Sg ≤ K := by
  rw [Sg, Subgroup.closure_le]
  intro g hg
  have h1 : cd g ∈ gC := by
    rw [← tg_codes]
    exact List.mem_map_of_mem hg
  have := chk3 (cd g) h1
  show g • B0 = B0
  apply chi_inj
  rw [smul_chi, chi_B0]
  exact this

theorem orbit_B0 : orbit G B0 = {B : Finset (Fin 12) | B.card = 4} := by
  ext B
  constructor
  · rintro ⟨g, rfl⟩
    show (g • B0).card = 4
    rw [Finset.card_smul_finset]
    decide
  · intro hB
    obtain ⟨σ, -, k, -, rfl⟩ := four_set_cover B hB
    exact ⟨σ * rE k, by show (σ * rE k) • B0 = _; exact mul_smul σ (rE k) B0⟩

theorem card_K : Nat.card K = 192 := by
  have e : Nat.card (orbit G B0) = Nat.card (G ⧸ stabilizer G B0) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G B0)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer G B0)
  have h2 : Nat.card (orbit G B0) = 495 := by
    rw [orbit_B0]
    have : {B : Finset (Fin 12) | B.card = 4} = ↑(Finset.powersetCard 4 (Finset.univ : Finset (Fin 12))) := by
      ext B
      simp [Finset.mem_powersetCard]
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_powersetCard]
    simp [Nat.choose]
  rw [show Nat.card G = Nat.card NativeSporadic.M12 from rfl, CFSG.Sporadic.Schreier.m12_card, ← e, h2] at h1
  show Nat.card (stabilizer G B0) = 192
  omega

theorem cC_getD (i : ℕ) (hi : i < 3) : cC.getD i 0 = cd (cE i) := by
  rw [cd_cE]
  have : cW.length = 3 := chk8.2.2
  rw [cC, List.getD_eq_getElem _ _ (by simpa [this] using hi)]
  simp only [List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [this] using hi)]

theorem cE_zero : cE 0 = 1 := by
  have : cW.getD 0 [] = [] := by decide +kernel
  rw [cE, this, ev_nil]

theorem cE_mem_K (i : ℕ) (hi : i < 3) : cE i ∈ K := by
  have h := chk4a i hi
  rw [cC_getD i hi] at h
  show cE i • B0 = B0
  apply chi_inj
  rw [smul_chi, chi_B0]
  exact h

theorem rW_letters (k : ℕ) : ∀ l ∈ rW.getD k [], l < 4 := by
  intro l hl
  by_cases hk : k < rW.length
  · rw [List.getD_eq_getElem _ _ hk] at hl
    exact chk7 _ (by simp [List.getElem_mem]) l hl
  · rw [List.getD_eq_default _ _ (not_lt.mp hk)] at hl
    exact absurd hl (by simp)

theorem cW_letters (i : ℕ) : ∀ l ∈ cW.getD i [], l < 4 := by
  intro l hl
  by_cases hi : i < cW.length
  · rw [List.getD_eq_getElem _ _ hi] at hl
    exact chk7 _ (by simp [List.getElem_mem]) l hl
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)] at hl
    exact absurd hl (by simp)

theorem gW_letters : ∀ v ∈ gW, ∀ l ∈ v, l < 4 := by
  intro v hv l hl
  exact chk7 v (by simp [hv]) l hl

theorem alph_inv : ∀ l < 2, alph.getD (l + 2) 1 = (alph.getD l 1)⁻¹ := by
  intro l hl
  interval_cases l <;> rfl

theorem coset_cover : ∀ x ∈ K, ∃ i < 3, (cE i)⁻¹ * x ∈ Sg := by
  have hidx : (Sg.subgroupOf K).index = 3 := by
    have h := Subgroup.card_mul_index (Sg.subgroupOf K)
    have hc : Nat.card (Sg.subgroupOf K) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Sg_le_K).toEquiv, card_Sg]
    rw [hc, card_K] at h
    omega
  have hmain := ModG.exists_coset_rep K Sg [cE 0, cE 1, cE 2]
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cE_mem_K 0 (by norm_num)
      · exact cE_mem_K 1 (by norm_num)
      · exact cE_mem_K 2 (by norm_num))
    (by
      have h4 := chk4b
      have hn1 : cE 1 ∉ Sg := by
        rw [mem_Sg_iff, ← cC_getD 1 (by norm_num)]
        intro h
        have := memB_iff.2 h
        rw [h4.1] at this
        exact Bool.noConfusion this
      have hn2 : cE 2 ∉ Sg := by
        rw [mem_Sg_iff, ← cC_getD 2 (by norm_num)]
        intro h
        have := memB_iff.2 h
        rw [h4.2.1] at this
        exact Bool.noConfusion this
      have hn12 : (cE 1)⁻¹ * cE 2 ∉ Sg := by
        rw [mem_Sg_iff, cd_mul]
        have hinv : cd (cE 1)⁻¹ = evcg (compn 12) (kIdn 12) aC (invW 2 (cW.getD 1 [])) := by
          rw [cE, ← ev_invW alph_inv (cW.getD 1 []) (fun l hl => by have := cW_letters 1 l hl; omega)]
          exact cd_ev_alph _
        rw [hinv, ← cC_getD 2 (by norm_num)]
        intro h
        have := memB_iff.2 h
        rw [h4.2.2] at this
        exact Bool.noConfusion this
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.Pairwise.nil⟩⟩⟩
      · intro a' ha'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
        rcases ha' with rfl | rfl
        · rw [cE_zero, inv_one, one_mul]; exact hn1
        · rw [cE_zero, inv_one, one_mul]; exact hn2
      · intro a' ha'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
        rcases ha' with rfl
        exact hn12
      · intro a' ha'
        exact absurd ha' List.not_mem_nil)
    (by simp [hidx])
  intro x hx
  obtain ⟨d, hd, hdx⟩ := hmain x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨0, by norm_num, hdx⟩
  · exact ⟨1, by norm_num, hdx⟩
  · exact ⟨2, by norm_num, hdx⟩

theorem cover (x : G) :
    ∃ σ ∈ Sg, ∃ k < 19, ∃ i < 3, ∃ τ ∈ Sg, x = σ * (rE k * cE i) * τ := by
  have hB : (x • B0).card = 4 := by
    rw [Finset.card_smul_finset]
    decide
  obtain ⟨σ, hσ, k, hk, hxB⟩ := four_set_cover _ hB
  have hmem : (σ * rE k)⁻¹ * x ∈ K := by
    show ((σ * rE k)⁻¹ * x) • B0 = B0
    rw [mul_smul, hxB, smul_smul, smul_smul]
    have : (σ * rE k)⁻¹ * σ * rE k = 1 := by group
    rw [this, one_smul]
  obtain ⟨i, hi, hτ⟩ := coset_cover _ hmem
  refine ⟨σ, hσ, k, hk, i, hi, _, hτ, ?_⟩
  group

end CFSG.Quasithin.ModH.R12
