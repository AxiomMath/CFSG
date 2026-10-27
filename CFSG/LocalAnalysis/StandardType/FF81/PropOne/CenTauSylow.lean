module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenbStruct
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LNormalizer

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

theorem card_le_nine_of_isPGroup {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (hodd : Odd (Nat.card ↥(cB b z)))
    {τ c : G} (hτc : TauC z τ c) {T : Subgroup G} (hT : IsPGroup 3 T)
    (hTle : T ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
      Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) :
    Nat.card T ≤ 3 ^ 2 := by
  obtain ⟨O, hOb, hOL, _hOodd, hOnot3, hdecomp⟩ := exists_cen_decomp h hodd
  let M : Subgroup G := Subgroup.zpowers b ⊔ O
  let K : Subgroup G := L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({τ} : Set G)
  have hτL : τ ∈ L := hτc.tau_mem
  have hB1le : bOne z ≤ L := by
    rw [bOne, GGFF.tor]
    exact (Subgroup.closure_le L).mpr (by rintro x ⟨i, rfl⟩; exact (z i).2)
  have hKL : K ≤ L := by
    intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hzpL : Subgroup.zpowers b ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (h.hypA.le hy)) b (Set.mem_singleton b)).symm
  have hML : M ≤ Subgroup.centralizer (L : Set G) := sup_le hzpL hOL
  have hMB1 : M ≤ Subgroup.centralizer ((bOne z : Subgroup G) : Set G) :=
    hML.trans (Subgroup.centralizer_le (by intro x hx; exact hB1le hx))
  have hMτ : M ≤ Subgroup.centralizer ({τ} : Set G) :=
    hML.trans (Subgroup.centralizer_le (by rintro x rfl; exact hτL))
  have hzpK : Subgroup.zpowers b ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (h.hypA.le (hKL hk))) b (Set.mem_singleton b)).symm
  have hOK : O ≤ Subgroup.centralizer (K : Set G) :=
    hOL.trans (Subgroup.centralizer_le (by intro x hx; exact hKL hx))
  have hMK : M ≤ Subgroup.centralizer (K : Set G) := sup_le hzpK hOK
  let μ : M × K →* G := MonoidHom.mk' (fun p => (p.1 : G) * (p.2 : G)) (by
    intro p q
    have hq1p2 : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
      ((Subgroup.mem_centralizer_iff.mp (hMK q.1.2)) (p.2 : G) p.2.2).symm
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
        = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
      _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hq1p2]
      _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group)
  have hzpO : Subgroup.zpowers b ≤ Subgroup.centralizer (O : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro o ho
    exact ((Subgroup.mem_centralizer_iff.mp (hOb ho)) b (Set.mem_singleton b)).symm
  have hzpN : Subgroup.zpowers b ≤ Subgroup.normalizer (O : Set G) :=
    hzpO.trans (Subgroup.centralizer_le_normalizer (O : Set G))
  let f : Subgroup.zpowers b × O →* M :=
    MonoidHom.mk' (fun p => ⟨(p.1 : G) * (p.2 : G),
      M.mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩) (by
      intro p q
      have hq1p2 : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
        ((Subgroup.mem_centralizer_iff.mp (hzpO q.1.2)) (p.2 : G) p.2.2).symm
      apply Subtype.ext
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
          = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hq1p2]
        _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group)
  have hf_surj : Function.Surjective f := by
    intro m
    have hm : (m : G) ∈ (↑M : Set G) := m.2
    change (m : G) ∈ (↑(Subgroup.zpowers b ⊔ O) : Set G) at hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers b) O hzpN] at hm
    rw [Set.mem_mul] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hm
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  have hMcard : Nat.card M ∣ 3 * Nat.card O := by
    have := Subgroup.card_dvd_of_surjective hf_surj
    rwa [Nat.card_prod, Nat.card_zpowers, h.hypA.ord] at this
  have hTmap : (Subgroup.comap μ T).map μ = T := by
    apply le_antisymm
    · intro y hy
      obtain ⟨w, hw, hwμ⟩ := (Subgroup.mem_map).mp hy
      rw [← hwμ]
      exact (Subgroup.mem_comap).mp hw
    · intro x hx
      have hxIn : x ∈ Subgroup.centralizer ({b} : Set G) ⊓
          Subgroup.centralizer ({τ} : Set G) ⊓
          Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := hTle hx
      have hxCB : x ∈ Subgroup.centralizer ({b} : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxIn).1).1
      have hxCT : x ∈ Subgroup.centralizer ({τ} : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxIn).1).2
      have hxN : x ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp hxIn).2
      obtain ⟨i, o, ho, l, hlL, hxe⟩ := hdecomp x hxCB
      have hmM : b ^ i * o ∈ M :=
        M.mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem (Subgroup.zpowers b)
          (Subgroup.mem_zpowers b) i)) (Subgroup.mem_sup_right ho)
      let m : M := ⟨b ^ i * o, hmM⟩
      have hm_eq : (m : G) = b ^ i * o := rfl
      have hmN : (m : G) ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
        (Subgroup.centralizer_le_normalizer ((bOne z : Subgroup G) : Set G)) (hMB1 m.2)
      have hmMτ : (m : G) ∈ Subgroup.centralizer ({τ} : Set G) := hMτ m.2
      have hl_eq : l = (m : G)⁻¹ * x := by rw [hxe, hm_eq]; group
      have hlN : l ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
        rw [hl_eq]
        exact (Subgroup.normalizer _).mul_mem (Subgroup.inv_mem _ hmN) hxN
      have hlC : l ∈ Subgroup.centralizer ({τ} : Set G) := by
        rw [hl_eq]
        exact (Subgroup.centralizer _).mul_mem (Subgroup.inv_mem _ hmMτ) hxCT
      have hK_mem : l ∈ K :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hlL, hlN⟩, hlC⟩
      have hmul : (m : G) * l = x := by rw [hxe, hm_eq]
      have hz0 : (m, ⟨l, hK_mem⟩) ∈ Subgroup.comap μ T := by
        show μ (m, ⟨l, hK_mem⟩) ∈ T
        change (m : G) * l ∈ T
        rw [hmul]
        exact hx
      exact (Subgroup.mem_map).mpr ⟨(m, ⟨l, hK_mem⟩), hz0, hmul⟩
  have d1 : Nat.card T ∣ Nat.card ↥(Subgroup.comap μ T) := by
    have := Subgroup.card_map_dvd (Subgroup.comap μ T) μ
    rwa [hTmap] at this
  have d2 : Nat.card ↥(Subgroup.comap μ T) ∣ Nat.card M * Nat.card K := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.comap μ T)
    rwa [Nat.card_prod] at this
  have d3 : Nat.card T ∣ 3 * Nat.card O * Nat.card K :=
    d1.trans (d2.trans (Nat.mul_dvd_mul_right hMcard (Nat.card K)))
  obtain ⟨a, ha⟩ := IsPGroup.exists_card_eq hT
  have hOcop : Nat.Coprime 3 (Nat.card O) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hOnot3
  have hdiv3K : 3 ^ a ∣ 3 * Nat.card K := by
    have hcop : Nat.Coprime (3 ^ a) (Nat.card O) := hOcop.pow_left a
    have hd : 3 ^ a ∣ 3 * Nat.card O * Nat.card K := by rwa [ha] at d3
    refine hcop.dvd_of_dvd_mul_right ?_
    have heq : 3 * Nat.card O * Nat.card K = (3 * Nat.card K) * Nat.card O := by ring
    exact heq ▸ hd
  have hKnot9 : ¬ 9 ∣ Nat.card K := not_nine_dvd_card_cen_tau h hτL hτc.tau_sq hτc.inv
  have ha_le : a ≤ 2 := by
    by_contra hcon
    have ha3 : 3 ≤ a := by omega
    have hpow : 3 ^ 3 ∣ 3 ^ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mpr ha3
    have h27 : 27 ∣ 3 * Nat.card K := by
      have := hpow.trans hdiv3K
      rwa [show (3 : ℕ) ^ 3 = 27 from by norm_num] at this
    have h9 : 9 ∣ Nat.card K := by
      have h27' : 3 * 9 ∣ 3 * Nat.card K := by
        rw [show (3 : ℕ) * 9 = 27 from by norm_num]; exact h27
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < (3 : ℕ)) h27'
    exact hKnot9 h9
  rw [ha]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mpr ha_le

end CFSG.StandardType.FF81.PropOne

end
