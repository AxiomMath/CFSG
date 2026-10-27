module

public import CFSG.Quasithin.Vol2.Ch3E213MOS8
public import CFSG.GH74.GLS.IVK.L2.Fixed14a

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem inf_innAut_eq (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {P M₀ : Subgroup (MulAut K)} {z₀ : K}
    (hzOf : E2P.zOf P = Subgroup.zpowers (MulAut.conj z₀))
    (hD' : M₀ ⊓ innAut K = innAut K ⊓ Subgroup.centralizer (E2P.zOf P : Set (MulAut K))) :
    M₀ ⊓ innAut K = (Subgroup.centralizer ({z₀} : Set K)).map MulAut.conj := by
  have hzc : MulAut.conj z₀ ∈ E2P.zOf P := hzOf ▸ Subgroup.mem_zpowers _
  rw [hD']
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    have hy' : MulAut.conj y ∈ Subgroup.centralizer (E2P.zOf P : Set (MulAut K)) := hy
    refine ⟨y, ?_, rfl⟩
    show y ∈ Subgroup.centralizer ({z₀} : Set K)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.mp hy' (MulAut.conj z₀) hzc
    exact (hinj (by rw [map_mul, map_mul]; exact h)).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [hzOf] at hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute (MulAut.conj z₀) (MulAut.conj y) := by
      show MulAut.conj z₀ * MulAut.conj y = MulAut.conj y * MulAut.conj z₀
      rw [← map_mul, ← map_mul, ← Subgroup.mem_centralizer_singleton_iff.mp hy]
    exact (hc.zpow_left j).eq

theorem false_of_sq (h13a : IVK_1_3a) (h13b : IVK_1_3b) (hF : L2Field F) (e : K ≃* L2 F)
    (N : L2Notation e) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : Nat.card F = p ^ 2)
    {T₀ M₀ V₀ : Subgroup (MulAut K)} (hPT : N.P ≤ T₀) (hT : T₀ ≤ N.T) (hVT : V₀ ≤ T₀)
    (hVn : T₀ ≤ Subgroup.normalizer (V₀ : Set (MulAut K))) (hsq : ∀ v ∈ V₀, v * v = 1)
    (hV4 : 4 ≤ Nat.card V₀) (hVM : V₀ ≤ pCoreOf 2 M₀)
    (hD' : M₀ ⊓ innAut K = innAut K ⊓ Subgroup.centralizer (E2P.zOf N.P : Set (MulAut K)))
    (uniq : ∀ Y : Subgroup (MulAut K), Y ≤ innAut K → N.P ≤ Y → Y ≠ innAut K →
      T₀ ≤ Subgroup.normalizer (Y : Set (MulAut K)) → Y ≤ M₀)
    (hcoat : ∀ u : K, orderOf u = 2 → IsCoatom (Subgroup.centralizer ({u} : Set K))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := conj_injective_of_L2 e
  obtain ⟨f₀, hf₀R, hf₀2, hallF, hf₀D, hf₀P⟩ := exists_fieldInv hF e N hp hq
  have hff : f₀ * f₀ = 1 := by rw [← pow_two, ← hf₀2, pow_orderOf_eq_one]
  have hf₀1 : f₀ ≠ 1 := fun h => hf₀D (h ▸ (innDiagSub e).one_mem)
  have hidx := index_innDiagSub hf₀2 hallF hf₀D
  obtain ⟨n, hn⟩ : ∃ n, Nat.card N.P = 2 ^ n := ⟨_, card_P_eq e N⟩
  have hn3 := three_le_of_involution_mem_R hF N hf₀R hf₀2 n hn
  have h8 : 8 ≤ Nat.card N.P := by
    rw [hn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨z₀, hz₀, hzOf⟩ := exists_z₀ ivk_1_2c hF N h8
  have hzc : MulAut.conj z₀ ∈ E2P.zOf N.P := hzOf ▸ Subgroup.mem_zpowers _
  have hD := inf_innAut_eq hinj hzOf hD'
  obtain ⟨hq4, h3⟩ := sq_facts hp hp3
  rw [← hq] at hq4
  have hq1 : 1 ≤ Nat.card F := by rw [hq]; exact Nat.one_le_pow _ _ hp.pos
  obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (h13a F hF K e 1 (Or.inl rfl) hq4 (Nat.card F - 1)
    (by omega) z₀ hz₀).2.1
  obtain ⟨a, m, hmodd, hkam⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  have h3k : 3 ∣ k := by omega
  have hm3 : 3 ≤ m := by
    have h3m : 3 ∣ m := Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)) (hkam ▸ h3k)
    exact Nat.le_of_dvd hmodd.pos h3m
  have hk : ∀ j : ℕ, k ≠ 2 ^ j := by
    intro j hj
    have h32 : 3 ∣ 2 ^ j := hj ▸ h3k
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega
  have hkq : 2 * k + 1 = Nat.card F := by omega
  have hinn : ∀ v ∈ V₀ ⊓ innDiagSub e, v ∈ innAut K := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact (innAut K).one_mem
    have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq v hv.1) hv1
    exact mem_innAut_of_mem h13b hF e hq4 ψ hD hkam hm3 hmodd hkq (hVM hv.1) hv.2 hv2
  have hle2 : Nat.card ↥(V₀ ⊓ innDiagSub e) ≤ 2 := by
    have hle : V₀ ⊓ innDiagSub e ≤ V₀ ⊓ innAut K := fun v hv => ⟨hv.1, hinn v hv⟩
    exact (Subgroup.card_le_of_le hle).trans (card_inf_le_two hinj ψ hk hD hVM hsq)
  obtain ⟨w, hw, hw2, hallw, v, hv, hvD, hall⟩ :=
    exists_inf_eq_and_hall (innDiagSub_normal e) hidx hVn hV4 hle2
  have hwV : w ∈ V₀ := hw.1
  have hwP : w ∈ N.P := ⟨hT (hVT hwV), hinn w hw⟩
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    omega
  have hww : w * w = 1 := hsq w hwV
  have hwc : ∀ y ∈ N.P, w * y = y * w := by
    intro y hy
    have h1 : y * w * y⁻¹ ∈ V₀ ⊓ innDiagSub e :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hVn (hPT hy)) w).mp hwV,
        (innDiagSub_normal e).conj_mem w hw.2 y⟩
    rcases hallw _ h1 with h | h
    · exfalso
      apply hw1
      calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · have h2 : y * w * y⁻¹ * y = w * y := by rw [h]
      calc w * y = y * w * y⁻¹ * y := h2.symm
        _ = y * w := by group
  have hv1 : v ≠ 1 := fun h => hvD (h ▸ (innDiagSub e).one_mem)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq v hv) hv1
  obtain ⟨x, hxP, rfl⟩ : ∃ x ∈ N.P, v = x * f₀ := by
    rcases ivk_1_2i_c F hF K e N f₀ hf₀R hf₀2 v (hT (hVT hv)) hv2 with h | h | h
    · exact absurd (Pt_le_innDiagSub N (P_le_Pt N h)) hvD
    · exact absurd (Pt_le_innDiagSub N h.1) hvD
    · exact h
  have hxf : x * f₀ = f₀ * x := hf₀P x hxP
  have hx2 : x * x = 1 := by
    have h1 : x * f₀ * (x * f₀) = x * x * (f₀ * f₀) := by
      calc x * f₀ * (x * f₀) = x * (f₀ * x) * f₀ := by group
        _ = x * (x * f₀) * f₀ := by rw [← hxf]
        _ = x * x * (f₀ * f₀) := by group
    have h2 := hsq _ hv
    rw [h1, hff, mul_one] at h2
    exact h2
  have hcomm : ∀ g ∈ N.P, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = w * x := by
    intro g hg
    have hgf : f₀ * g⁻¹ = g⁻¹ * f₀ := (hf₀P _ (N.P.inv_mem hg)).symm
    have h1 : g * (x * f₀) * g⁻¹ = g * x * g⁻¹ * f₀ := by
      calc g * (x * f₀) * g⁻¹ = g * x * (f₀ * g⁻¹) := by group
        _ = g * x * (g⁻¹ * f₀) := by rw [hgf]
        _ = g * x * g⁻¹ * f₀ := by group
    rcases hall g (hPT hg) with h | h
    · rw [h1] at h
      exact Or.inl (mul_right_cancel h)
    · rw [h1, ← mul_assoc] at h
      exact Or.inr (mul_right_cancel h)
  have hCcard : Nat.card (Subgroup.centralizer ({z₀} : Set K)) = Nat.card F - 1 := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    omega
  have hcard : Nat.card (fixedSubgroup K f₀) =
      p * Nat.card (Subgroup.centralizer ({z₀} : Set K)) := by
    rw [hCcard]
    exact card_fixed_of_fieldAut ivk_1_4a hF e hq hf₀R.2 hf₀2
  by_cases hxw : x = 1 ∨ x = w
  ·
    have hxV : x ∈ V₀ := by
      rcases hxw with rfl | rfl
      · exact V₀.one_mem
      · exact hwV
    have hfV : f₀ ∈ V₀ := by
      have h1 : f₀ = x * (x * f₀) := by rw [← mul_assoc, hx2, one_mul]
      rw [h1]
      exact V₀.mul_mem hxV hv
    set S : Subgroup K := N.P.comap MulAut.conj with hSdef
    have hSmap : S.map MulAut.conj = N.P := Subgroup.map_comap_eq_self inf_le_right
    have hcardS : Nat.card S = 2 ^ (Nat.card K).factorization 2 := by
      rw [← card_P_eq e N, ← hSmap, Subgroup.card_map_of_injective hinj]
    have hSodd : Odd S.index := by
      have h := (Sylow.ofCard S hcardS).not_dvd_index
      exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
    have hSC : S ≤ Subgroup.centralizer ({z₀} : Set K) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_iff.mp hzc.2 (MulAut.conj s) hs
      exact hinj (by rw [map_mul, map_mul]; exact h)
    have hSfix : ∀ s ∈ S, f₀ s = s := fun s hs =>
      (conj_mem_centralizer_iff hinj f₀ s).mp
        (Subgroup.mem_centralizer_singleton_iff.mpr (hf₀P _ hs))
    exact false_of_fixes hinj (hcoat z₀ hz₀) ψ hD hkam (by omega) hmodd hSC hSodd (hVM hfV)
      hf₀1 hSfix hp.one_lt hcard
  · obtain ⟨hx1, hxw'⟩ := not_or.mp hxw
    have hn8 : n = 3 := by
      by_contra hne
      rcases mem_of_comm hF N hn (by omega) hwP hw1 hwc hxP hx2 hcomm with h | h
      · exact hx1 h
      · exact hxw' h
    subst hn8
    rcases eq_or_eq ivk_1_2d hF N (le_inf hPT (P_le_Pt N)) inf_le_right with h | h
    ·
      have hf₀T : f₀ ∈ T₀ := by
        have h1 : f₀ = x⁻¹ * (x * f₀) := by group
        rw [h1]
        exact T₀.mul_mem (T₀.inv_mem (hPT hxP)) (hVT hv)
      have hcent := comm_of_inf_eq N hT h hf₀2 hallF hf₀T hf₀P
      have hlt : Nat.card (Subgroup.centralizer ({z₀} : Set K)) <
          Nat.card (fixedSubgroup K f₀) := by
        rw [hcard]
        have hpos : 0 < Nat.card (Subgroup.centralizer ({z₀} : Set K)) := Nat.card_pos
        nlinarith [hp.two_le]
      exact false_of_central hinj uniq hD inf_le_right hf₀1 hcent hf₀P hlt
    ·
      have hPtT : N.Pt ≤ T₀ := by
        rw [← h]
        exact inf_le_left
      exact false_of_Pt_le hF N hn hf₀R hf₀2 hf₀P hwP hw1 hww hwc hxP hx2 hx1 hxw'
        (fun g hg => hall g (hPtT hg))

end CFSG.Quasithin.Ch3E213M.OS
