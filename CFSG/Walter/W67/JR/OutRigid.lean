module

public import CFSG.Walter.W67.JR.OutHall
public import CFSG.Walter.W67.JR.R123
public import CFSG.Walter.W67.JR.R5
public import CFSG.Walter.W67.Transport

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open JROut

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

theorem mod_eight
    (hq : 5 < h.q) : h.p ^ h.f % 8 = 3 ∨ h.p ^ h.f % 8 = 5 :=
  (JT.lemma_2_1 (h.toJTHyp hq) h.p_ne_two).1

theorem index_K : (h.K.subgroupOf (Subgroup.centralizer ({h.J} : Set L))).index = 2 := by
  have hH : Nat.card (Subgroup.centralizer ({h.J} : Set L)) = 2 * Nat.card h.K := by
    rw [h.centralizer_eq, h.card_zpowers_J_sup_of h.le_centralizer h.J_not_mem]
  have h1 := (h.K.subgroupOf (Subgroup.centralizer ({h.J} : Set L))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_centralizer).toEquiv, hH] at h1
  have hpos : 0 < Nat.card h.K := Nat.card_pos
  have h2 : Nat.card h.K * (h.K.subgroupOf (Subgroup.centralizer ({h.J} : Set L))).index =
      Nat.card h.K * 2 := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem mem_K_of_apply_J
    (hq : 5 < h.q) (β : MulAut L) (hβ : β h.J = h.J) {x : L}
    (hx : x ∈ h.K) : β x ∈ h.K := by
  set H := Subgroup.centralizer ({h.J} : Set L) with hH
  have hβH : ∀ y ∈ H, β y ∈ H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hβ, ← map_mul, ← map_mul, hy]
  set M := h.K.map β.toMonoidHom with hM
  have hMH : M ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact hβH y (h.le_centralizer hy)
  have : (h.K.subgroupOf H).Normal := h.normal_K
  let e : ↥(M.subgroupOf H) ≃* PSL(2, GaloisField h.p h.f) :=
    (Subgroup.subgroupOfEquivOfLe hMH).trans
      ((h.K.equivMapOfInjective β.toMonoidHom β.injective).symm.trans h.iso)
  have hle := PSL2Sub.le_of_normal_index_two (G := H) e h.odd_p h.f_pos (h.mod_eight hq)
    (W := h.K.subgroupOf H) h.index_K
  have hβx : β x ∈ M := ⟨x, hx, rfl⟩
  have hmem : (⟨β x, hMH hβx⟩ : H) ∈ M.subgroupOf H := Subgroup.mem_subgroupOf.mpr hβx
  exact Subgroup.mem_subgroupOf.mp (hle hmem)

theorem normalizer_sup_centralizer
    (hJT : JTThreeHyp) (hq : 5 < h.q) (fr : Frame h.toHyp) :
    Subgroup.normalizer ((fr.S : Subgroup L) : Set L) ⊔ Subgroup.centralizer ({h.J} : Set L) =
      ⊤ := by
  classical
  set S : Subgroup L := (fr.S : Subgroup L) with hS
  set N := Subgroup.normalizer (S : Set L) with hN
  set H := Subgroup.centralizer ({h.J} : Set L) with hH
  set Ls := N ⊔ H with hLs
  have hHL : H ≤ Ls := le_sup_right
  have hNL : N ≤ Ls := le_sup_left
  have hSL : S ≤ Ls := Subgroup.le_normalizer.trans hNL
  have hKL : h.K ≤ Ls := h.le_centralizer.trans hHL
  have hJH : h.J ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have : IsElementaryAbelian 2 S := h.elementary_sylow fr.S
  have hsq : ∀ s ∈ S, s ^ 2 = 1 := fun s hs => elemPow_eq_one_of_isElementaryAbelian s hs
  have hidx2 : ∀ M : Subgroup L, M ≤ Ls → (M.subgroupOf Ls).Normal →
      (M.subgroupOf Ls).index ≠ 2 := by
    intro M hML hMn hMidx
    let e : ↥(h.K.subgroupOf Ls) ≃* PSL(2, GaloisField h.p h.f) :=
      (Subgroup.subgroupOfEquivOfLe hKL).trans h.iso
    have hKM' := PSL2Sub.le_of_normal_index_two (G := Ls) e h.odd_p h.f_pos (h.mod_eight hq)
      (W := M.subgroupOf Ls) hMidx
    have hKM : h.K ≤ M := fun x hx =>
      Subgroup.mem_subgroupOf.mp (hKM' (Subgroup.mem_subgroupOf.mpr hx :
        (⟨x, hKL hx⟩ : Ls) ∈ h.K.subgroupOf Ls))
    have hT1 : fr.T ≠ ⊥ := by
      intro hb
      have h4 := fr.card_T
      rw [show (fr.S : Subgroup L) ⊓ h.toHyp.K = fr.T from rfl, hb, Subgroup.card_bot] at h4
      omega
    obtain ⟨⟨v, hvT⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    have hvo : orderOf v = 2 := orderOf_eq_prime (hsq v hvT.1) hv1'
    have hvM : v ∈ M := hKM hvT.2
    have htrans := (lemma_2_2 L h.toHyp fr h.index_ne_two).2.1
    have hSM : S ≤ M := by
      intro s hs
      by_cases hs1 : s = 1
      · rw [hs1]
        exact M.one_mem
      have hso : orderOf s = 2 := orderOf_eq_prime (hsq s hs) hs1
      obtain ⟨n, hnN, hns⟩ := htrans v hvT.1 s hs hvo hso
      have hconj := hMn.conj_mem (⟨v, hKL hvT.2⟩ : Ls)
        (Subgroup.mem_subgroupOf.mpr hvM) ⟨n, hNL hnN⟩
      rw [Subgroup.mem_subgroupOf] at hconj
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hconj
      rw [hns] at hconj
      exact hconj
    have hcardM : Nat.card Ls = 2 * Nat.card M := by
      have h1 := (M.subgroupOf Ls).card_mul_index
      rw [hMidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv] at h1
      omega
    have h8M : 8 ∣ Nat.card M := by
      rw [← h.card_sylow fr.S]
      exact Subgroup.card_dvd_of_le hSM
    have h16 : 16 ∣ Nat.card L := by
      obtain ⟨k, hk⟩ := h8M
      exact Dvd.dvd.trans ⟨k, by rw [hcardM, hk]; ring⟩ (Subgroup.card_subgroup_dvd_card Ls)
    have hcS := (S : Subgroup L).card_mul_index
    rw [h.card_sylow fr.S] at hcS
    apply fr.S.not_dvd_index
    obtain ⟨k, hk⟩ := h16
    exact ⟨k, by change (S : Subgroup L).index = 2 * k; omega⟩
  have hJR : IsJRSubgroup Ls h.J h.K h.p h.f :=
    ⟨hHL hJH, h.orderOf_J, le_inf hKL h.le_centralizer, h.J_not_mem,
      by rw [inf_eq_right.mpr hHL]; exact h.centralizer_eq, ⟨h.iso⟩, hidx2,
      ⟨fr.S, hSL, h.elementary_sylow fr.S, h.card_sylow fr.S⟩⟩
  obtain ⟨hL', hp', hf', -, -⟩ := IsJRSubgroup.nonempty_jrGroup L h.p_ne_two h.f_pos hJR
  have hqq : hL'.q = h.q := by
    change hL'.p ^ hL'.f = h.p ^ h.f
    rw [hp', hf']
  have hq' : 5 < hL'.q := hqq ▸ hq
  have hc1 : Nat.card Ls = hL'.q ^ 3 * (hL'.q ^ 3 + 1) * (hL'.q - 1) :=
    (Ward.ward_order (hL'.toReeTypeHyp hJT hq')).2
  have hc2 : Nat.card L = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) :=
    (Ward.ward_order (h.toReeTypeHyp hJT hq)).2
  rw [hqq, ← hc2] at hc1
  exact Subgroup.eq_top_of_card_eq Ls hc1

theorem eq_one_or_eq_conj_J
    (hJT : JTThreeHyp) (hq : 5 < h.q) (β : MulAut L)
    (hβJ : β h.J = h.J) (hβK : ∀ x ∈ h.K, β x = x) : β = 1 ∨ β = MulAut.conj h.J := by
  classical
  obtain ⟨fr⟩ := Frame.nonempty L h.toHyp
  set S : Subgroup L := (fr.S : Subgroup L) with hS
  set H := Subgroup.centralizer ({h.J} : Set L) with hH
  have hl := JT.lemma_2_1 (h.toJTHyp hq) h.p_ne_two
  have : IsElementaryAbelian 2 S := h.elementary_sylow fr.S
  have : IsMulCommutative S := (h.elementary_sylow fr.S).toIsMulCommutative
  have hβH : ∀ x ∈ H, β x = x := by
    have hle : Subgroup.zpowers h.J ⊔ h.K ≤ β.toMonoidHom.eqLocus (MonoidHom.id L) :=
      sup_le ((Subgroup.zpowers_le).mpr hβJ) fun x hx => hβK x hx
    intro x hx
    rw [hH, h.centralizer_eq] at hx
    exact hle hx
  have hSH : S ≤ H := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_mem hs fr.J_mem)
  have hβS : ∀ s ∈ S, β s = s := fun s hs => hβH s (hSH hs)
  have hcop : Nat.Coprime (Nat.card S)
      (S.subgroupOf (Subgroup.normalizer (S : Set L))).index := by
    rw [h.card_sylow fr.S, (hl.2.2.2.2.1 fr.S).1]
    norm_num
  obtain ⟨t, htS, ht⟩ := exists_conj_on_normalizer hcop (hl.2.2.2.1 fr.S).le β hβS
  set T := fr.T with hT
  have hTK : T ≤ h.K := inf_le_right
  have hTS : T ≤ S := inf_le_left
  have hTV : IsKleinFour T :=
    PSL2Sub.isKleinFour_of_card h.iso h.odd_p h.f_pos (h.mod_eight hq) hTK fr.card_T
  have h12 := PSL2Sub.card_inf_normalizer h.iso h.odd_p h.f_pos (h.mod_eight hq) hTK hTV
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (h.K ⊓ Subgroup.normalizer (T : Set L) :
    Subgroup L)) 3 (by rw [h12]; norm_num)
  have hz3 : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzK : (z : L) ∈ h.K := z.2.1
  have hzT : (z : L) ∈ Subgroup.normalizer (T : Set L) := z.2.2
  have hzC : (z : L) ∉ Subgroup.centralizer (T : Set L) := by
    intro hzC
    have hzKC : (z : L) ∈ h.K ⊓ Subgroup.centralizer (T : Set L) := ⟨hzK, hzC⟩
    rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos hTK hTV] at hzKC
    have h4 : orderOf (z : L) ∣ 4 := fr.card_T ▸ Subgroup.orderOf_dvd_natCard _ hzKC
    rw [hz3] at h4
    omega
  have hfwd : ∀ w ∈ h.K ⊓ Subgroup.normalizer (T : Set L), ∀ s ∈ S, w * s * w⁻¹ ∈ S := by
    intro w hw s hs
    have hwJ : w * h.J = h.J * w := (h.commute_J_of_mem_K hw.1)
    rcases h.mem_K_or_of_mem_H hq (hSH hs) with hsK | hsK
    · exact hTS ((Subgroup.mem_normalizer_iff.mp hw.2 s).mp ⟨hs, hsK⟩)
    · have hJs : h.J * s ∈ T := ⟨S.mul_mem fr.J_mem hs, hsK⟩
      have h1 := hTS ((Subgroup.mem_normalizer_iff.mp hw.2 _).mp hJs)
      have h2 : w * s * w⁻¹ = h.J⁻¹ * (w * (h.J * s) * w⁻¹) := by
        calc w * s * w⁻¹ = h.J⁻¹ * (h.J * w) * s * w⁻¹ := by group
          _ = h.J⁻¹ * (w * h.J) * s * w⁻¹ := by rw [hwJ]
          _ = h.J⁻¹ * (w * (h.J * s) * w⁻¹) := by group
      rw [h2]
      exact S.mul_mem (S.inv_mem fr.J_mem) h1
  have hzS : (z : L) ∈ Subgroup.normalizer (S : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd z z.2 y, fun hy => ?_⟩
    have h1 := hfwd (z : L)⁻¹ (Subgroup.inv_mem _ z.2) _ hy
    simpa [mul_assoc] using h1
  have htz : (z : L) * t * (z : L)⁻¹ = t := by
    have h1 : β z = t * z * t⁻¹ := ht z hzS
    rw [hβK z hzK] at h1
    calc (z : L) * t * (z : L)⁻¹ = (t * z * t⁻¹) * t * (z : L)⁻¹ := by rw [← h1]
      _ = t := by group
  have ht1 : t = 1 ∨ t = h.J := by
    rcases h.mem_K_or_of_mem_H hq (hSH htS) with htK | htK
    · left
      exact JT.eq_one_of_conj_eq_of_orderOf_eq_three hTV hz3 hzT hzC ⟨htS, htK⟩ htz
    · right
      have hzJ : (z : L) * h.J = h.J * z := h.commute_J_of_mem_K hzK
      have hJt : (z : L) * (h.J * t) * (z : L)⁻¹ = h.J * t := by
        calc (z : L) * (h.J * t) * (z : L)⁻¹ = ((z : L) * h.J) * t * (z : L)⁻¹ := by group
          _ = h.J * ((z : L) * t * (z : L)⁻¹) := by rw [hzJ]; group
          _ = h.J * t := by rw [htz]
      have h1 : h.J * t = 1 := JT.eq_one_of_conj_eq_of_orderOf_eq_three hTV hz3 hzT hzC
        ⟨S.mul_mem fr.J_mem htS, htK⟩ hJt
      calc t = h.J⁻¹ * (h.J * t) := by group
        _ = h.J := by rw [h1, mul_one, h.J_inv]
  have hagree : ∀ x, β x = MulAut.conj t x := by
    have hle : Subgroup.normalizer (S : Set L) ⊔ H ≤
        β.toMonoidHom.eqLocus (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact ht x hx
      · change β x = MulAut.conj t x
        rw [hβH x hx, MulAut.conj_apply]
        rcases ht1 with rfl | rfl
        · group
        · have hxJ : x * h.J = h.J * x := Subgroup.mem_centralizer_singleton_iff.mp hx
          rw [← hxJ, h.J_inv, mul_assoc, h.J_mul_J, mul_one]
    rw [h.normalizer_sup_centralizer hJT hq fr] at hle
    intro x
    exact hle (Subgroup.mem_top x)
  rcases ht1 with rfl | rfl
  · left
    ext x
    rw [hagree, map_one]
  · right
    ext x
    exact hagree x

end JRGroup

end CFSG.Walter.W67
