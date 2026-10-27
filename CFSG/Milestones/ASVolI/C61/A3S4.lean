module

public import CFSG.Milestones.ASVolI.C61.A3Local
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Rec

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem burnsideC56_perm_four {K U : Subgroup G} {c t : G} (hK : Nat.card K = 24) (hUK : U ≤ K)
    (hKU : K ≤ normalizer (U : Set G)) (hU4 : Nat.card U = 4)
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hcK : c ∈ K) (hc3 : orderOf c = 3)
    (hfpf : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u) (htK : t ∈ K) (ht2 : t * t = 1)
    (hmove : ∃ u ∈ U, t * u * t⁻¹ ≠ u) : Nonempty (K ≃* Equiv.Perm (Fin 4)) := by
  refine CFSG.Quasithin.Fan86.Sigma3.Klein24.nonempty_perm_four
    (N := U.subgroupOf K) (x := ⟨c, hcK⟩) (t := ⟨t, htK⟩) ?_
  refine
    { card := hK
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr hKU
      card_N := ?_
      comm := ?_
      ord := ?_
      fix := ?_
      sq := Subtype.ext ht2
      moved := ?_ }
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv, hU4]
  · intro a ha b hb
    exact Subtype.ext (hUc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  · rw [Subgroup.orderOf_mk]
    exact hc3
  · intro n hn hnx
    by_contra h1
    exact hfpf _ (Subgroup.mem_subgroupOf.mp hn) (fun h => h1 (Subtype.ext h))
      (congrArg Subtype.val hnx)
  · obtain ⟨u, hu, hne⟩ := hmove
    exact ⟨⟨u, hUK hu⟩, Subgroup.mem_subgroupOf.mpr hu, fun h => hne (congrArg Subtype.val h)⟩

omit [Finite G] in
theorem burnsideC56_mul_self_of_mem_conj {U : Subgroup G} (hUe : ∀ u ∈ U, u ^ 2 = 1) {x v : G}
    (hv : v ∈ conjSubgroup U x) : v * v = 1 := by
  have h := hUe _ (mem_conjSubgroup_iff.mp hv)
  have h' : x * (v * v) * x⁻¹ = 1 := by
    rw [← h, pow_two]
    group
  calc v * v = x⁻¹ * (x * (v * v) * x⁻¹) * x := by group
    _ = 1 := by rw [h']; group

omit [Finite G] in
theorem burnsideC56_conj_ne_of_not_comm {u v : G} (hne : u * v ≠ v * u) : v * u * v⁻¹ ≠ u := by
  intro h
  apply hne
  calc u * v = (v * u * v⁻¹) * v := by rw [h]
    _ = v * u := by group

theorem burnsideC56_exists_mem_diff {S M₀ : Subgroup G} (hSM : S ≤ M₀) (h2 : S.relIndex M₀ = 2) :
    ∃ x ∈ M₀, x ∉ S := by
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  by_contra hcon
  push Not at hcon
  exact hne (le_antisymm hSM hcon)

theorem burnsideC56_a3_perm_four (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L)
    {c : G} (hl : A3Local H S L (blockU L) (H ⊓ Subgroup.centralizer (L : Set G)) c)
    (hD : H ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  obtain ⟨x, hx, hxS⟩ := burnsideC56_exists_mem_diff hSM h2
  have hd := burnsideC56_a3Data hcs hj hl hSM hMT h2 hx hxS
  obtain ⟨u, hu, v, hv, hne⟩ := hd.exists_noncomm
  have hSH : S ≤ H := hcs.sylow.1
  have hLH : L ≤ H := (C56.H_eq hcs hj) ▸ le_sup_left
  have hH : Nat.card H = 24 := by
    have h1 := hl.card_H
    have h2 := hl.card_S
    rw [hD, Subgroup.card_bot] at h2
    omega
  exact burnsideC56_perm_four hH (hl.U_le_S.trans hSH) hl.H_normalizes_U hl.card_U hl.U_comm
    (hLH hl.c_mem) hl.c_order hl.c_fpf (hSH (hd.U'_le hv))
    (burnsideC56_mul_self_of_mem_conj hl.U_exp hv) ⟨u, hu, burnsideC56_conj_ne_of_not_comm hne⟩

theorem burnsideC56_a3_perm_four_prod (hcs : burnsideC56_CS G T M H S L) (h3 : IsAltType L 3)
    (hj : conjJoin S L = L) {c : G}
    (hl : A3Local H S L (blockU L) (H ⊓ Subgroup.centralizer (L : Set G)) c)
    (hD : H ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Nonempty (H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))) := by
  classical
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  obtain ⟨x, hx, hxS⟩ := burnsideC56_exists_mem_diff hSM h2
  have hd := burnsideC56_a3Data hcs hj hl hSM hMT h2 hx hxS
  obtain ⟨u, hu, v, hv, hne⟩ := hd.exists_noncomm
  have hL12 : Nat.card L = 12 := (hcs.block.1.1.alt3_structure h3).2.2.2.2.1
  have hSH : S ≤ H := hcs.sylow.1
  have hHeq : H = L ⊔ S := C56.H_eq hcs hj
  have hLH : L ≤ H := hHeq ▸ le_sup_left
  have hUL : blockU L ≤ L := (le_sup_left : blockU L ≤ blockU L ⊔ zpowers c).trans hl.L_eq.symm.le
  have hD2 : Nat.card ↥(H ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    have h1 := hd.card_D_le_two
    have h0 : Nat.card ↥(H ⊓ Subgroup.centralizer (L : Set G)) ≠ 1 := fun h =>
      hD (Subgroup.card_eq_one.mp h)
    have hpos : 0 < Nat.card ↥(H ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
    omega
  have hS16 : Nat.card S = 16 := by rw [hl.card_S, hD2]
  have hH48 : Nat.card H = 48 := by rw [hl.card_H, hS16]
  have hLS : L ⊓ S = blockU L := by
    have hle : blockU L ≤ L ⊓ S := le_inf hUL hl.U_le_S
    have hdvd1 : Nat.card ↥(L ⊓ S) ∣ 12 := hL12 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(L ⊓ S) ∣ 16 := hS16 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hg : Nat.gcd 12 16 = 4 := by norm_num
    have hdvd : Nat.card ↥(L ⊓ S) ∣ 4 := hg ▸ Nat.dvd_gcd hdvd1 hdvd2
    have h4 : Nat.card ↥(L ⊓ S) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hl.card_U]; exact h4)).symm
  have hVS : conjSubgroup (blockU L) x ≤ S := hd.U'_le
  have hVL : conjSubgroup (blockU L) x ≤ normalizer (L : Set G) :=
    (hVS.trans hSH).trans hl.H_normalizes_L
  have hLV : L ⊓ conjSubgroup (blockU L) x = blockU L ⊓ conjSubgroup (blockU L) x := by
    apply le_antisymm
    · intro g hg
      have h1 : g ∈ L ⊓ S := ⟨hg.1, hVS hg.2⟩
      rw [hLS] at h1
      exact ⟨h1, hg.2⟩
    · exact inf_le_inf_right _ hUL
  have hK24 : Nat.card ↥(L ⊔ conjSubgroup (blockU L) x) = 24 := by
    have h := C5.card_sup_mul_card_inf_of_le_normalizer hVL
    rw [sup_comm, inf_comm, hLV, hd.card_inter, hd.card_U', hL12] at h
    omega
  have hKH : L ⊔ conjSubgroup (blockU L) x ≤ H := sup_le hLH (hVS.trans hSH)
  have hUK : blockU L ≤ L ⊔ conjSubgroup (blockU L) x := hUL.trans le_sup_left
  obtain ⟨eK⟩ : Nonempty (↥(L ⊔ conjSubgroup (blockU L) x) ≃* Equiv.Perm (Fin 4)) :=
    burnsideC56_perm_four hK24 hUK (hKH.trans hl.H_normalizes_U) hl.card_U hl.U_comm
      (Subgroup.mem_sup_left hl.c_mem) hl.c_order hl.c_fpf (Subgroup.mem_sup_right hv)
      (burnsideC56_mul_self_of_mem_conj hl.U_exp hv) ⟨u, hu, burnsideC56_conj_ne_of_not_comm hne⟩
  have hKS : (L ⊔ conjSubgroup (blockU L) x) ⊓ S = blockU L ⊔ conjSubgroup (blockU L) x := by
    have hle : blockU L ⊔ conjSubgroup (blockU L) x ≤ (L ⊔ conjSubgroup (blockU L) x) ⊓ S :=
      le_inf (sup_le hUK le_sup_right) hd.R_le
    have hdvd1 : Nat.card ↥((L ⊔ conjSubgroup (blockU L) x) ⊓ S) ∣ 24 :=
      hK24 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥((L ⊔ conjSubgroup (blockU L) x) ⊓ S) ∣ 16 :=
      hS16 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hg : Nat.gcd 24 16 = 8 := by norm_num
    have hdvd : Nat.card ↥((L ⊔ conjSubgroup (blockU L) x) ⊓ S) ∣ 8 :=
      hg ▸ Nat.dvd_gcd hdvd1 hdvd2
    have h8 : Nat.card ↥((L ⊔ conjSubgroup (blockU L) x) ⊓ S) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hdvd
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hd.card_R]; exact h8)).symm
  have hKD : (L ⊔ conjSubgroup (blockU L) x) ⊓ (H ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ (L ⊔ conjSubgroup (blockU L) x) ⊓ S := ⟨hg.1, hl.D_le_S hg.2⟩
    rw [hKS] at h1
    have h2 : g ∈ (blockU L ⊔ conjSubgroup (blockU L) x) ⊓ (H ⊓ Subgroup.centralizer (L : Set G)) :=
      ⟨h1, hg.2⟩
    rw [hd.R_inf_D] at h2
    exact h2
  have hDcomm : ∀ d ∈ H ⊓ Subgroup.centralizer (L : Set G),
      ∀ d' ∈ H ⊓ Subgroup.centralizer (L : Set G), d * d' = d' * d := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic ↥(H ⊓ Subgroup.centralizer (L : Set G)) := isCyclic_of_prime_card hD2
    intro d hd' d' hd''
    have := (inferInstance : IsMulCommutative ↥(H ⊓ Subgroup.centralizer (L : Set G))).is_comm.comm
      ⟨d, hd'⟩ ⟨d', hd''⟩
    exact congrArg Subtype.val this
  have hSC : S ≤ Subgroup.centralizer ((H ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := by
    calc S = (blockU L ⊔ conjSubgroup (blockU L) x) ⊔ (H ⊓ Subgroup.centralizer (L : Set G)) :=
          hd.S_eq_R_sup_D
      _ ≤ _ := by
        refine sup_le ?_ ?_
        · intro r hr
          rw [Subgroup.mem_centralizer_iff]
          intro d hd'
          exact (hd.R_comm_D r hr d hd').symm
        · intro d hd'
          rw [Subgroup.mem_centralizer_iff]
          intro d' hd''
          exact hDcomm d' hd'' d hd'
  have hHC : H ≤ Subgroup.centralizer ((H ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := by
    calc H = L ⊔ S := hHeq
      _ ≤ _ := by
        refine sup_le ?_ hSC
        intro l hl'
        rw [Subgroup.mem_centralizer_iff]
        intro d hd'
        exact hl.D_comm_L d hd' l hl'
  have hDH : H ⊓ Subgroup.centralizer (L : Set G) ≤ H := inf_le_left
  let φ : ↥(L ⊔ conjSubgroup (blockU L) x) × ↥(H ⊓ Subgroup.centralizer (L : Set G)) →* ↥H :=
    (Subgroup.inclusion hKH).noncommCoprod (Subgroup.inclusion hDH) (fun k d => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hHC (hKH k.2)) d d.2).symm)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, d⟩ h
    have h' : (k : G) * (d : G) = 1 := by
      have h1 : Subgroup.inclusion hKH k * Subgroup.inclusion hDH d = 1 := h
      exact congrArg Subtype.val h1
    have hkD : (k : G) ∈ H ⊓ Subgroup.centralizer (L : Set G) := by
      have : (k : G) = (d : G)⁻¹ := eq_inv_of_mul_eq_one_left h'
      rw [this]
      exact inv_mem d.2
    have hk1 : (k : G) = 1 := by
      have : (k : G) ∈ (L ⊔ conjSubgroup (blockU L) x) ⊓ (H ⊓ Subgroup.centralizer (L : Set G)) :=
        ⟨k.2, hkD⟩
      rw [hKD] at this
      exact this
    have hd1 : (d : G) = 1 := by
      rw [hk1, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext hk1) (Subtype.ext hd1)
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hK24, hD2, hH48])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have eD : ↥(H ⊓ Subgroup.centralizer (L : Set G)) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hD2 (by simp [Nat.card_eq_fintype_card])
  exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans (eK.prodCongr eD)⟩

end CFSG.QuasithinUnique.burnsideC56_P
