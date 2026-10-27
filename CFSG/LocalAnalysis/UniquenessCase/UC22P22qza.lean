module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22qo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

section Burnside

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem uc22p22qza_normalizer_le_centralizer (R : Sylow p X) (hR : IsCyclic (R : Subgroup X))
    {z₀ : X} (hz₀R : z₀ ∈ (R : Subgroup X)) (hz₀ : orderOf z₀ = p) (hz₀c : ∀ x : X, x * z₀ = z₀ * x) :
    normalizer (R : Set X) ≤ centralizer (R : Set X) := by
  classical
  have hp : p.Prime := Fact.out
  intro k hk
  haveI := hR
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(R : Subgroup X))
  have hpow : ∀ y ∈ (R : Subgroup X), ∃ i : ℕ, (g : X) ^ i = y := by
    intro y hy
    have h1 : (⟨y, hy⟩ : ↥(R : Subgroup X)) ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg _)
    obtain ⟨i, hi⟩ := h1
    exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  have hkg : k * (g : X) * k⁻¹ ∈ (R : Subgroup X) := (mem_normalizer_iff.1 hk _).1 g.2
  obtain ⟨u, hu⟩ := hpow _ hkg
  have hconj : ∀ y ∈ (R : Subgroup X), k * y * k⁻¹ = y ^ u := by
    intro y hy
    obtain ⟨i, rfl⟩ := hpow y hy
    rw [← conj_pow, ← hu, ← pow_mul, ← pow_mul, mul_comm]
  have hiter : ∀ j : ℕ, ∀ y ∈ (R : Subgroup X), k ^ j * y * (k ^ j)⁻¹ = y ^ (u ^ j) := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
      intro y hy
      calc k ^ (j + 1) * y * (k ^ (j + 1))⁻¹ = k * (k ^ j * y * (k ^ j)⁻¹) * k⁻¹ := by group
        _ = k * y ^ (u ^ j) * k⁻¹ := by rw [ih y hy]
        _ = (k * y * k⁻¹) ^ (u ^ j) := by rw [conj_pow]
        _ = y ^ (u ^ (j + 1)) := by rw [hconj y hy, ← pow_mul, pow_succ']
  have hu1 : (p : ℤ) ∣ (u : ℤ) - 1 := by
    have h0 : k * z₀ * k⁻¹ = z₀ := by rw [hz₀c k, mul_inv_cancel_right]
    have h1 : z₀ ^ u = z₀ ^ 1 := by rw [← hconj z₀ hz₀R, h0, pow_one]
    have h2 := pow_eq_pow_iff_modEq.1 h1
    rw [hz₀] at h2
    have h3 := Nat.modEq_iff_dvd.1 h2.symm
    simpa using h3
  obtain ⟨a, ha⟩ := R.isPGroup'.exists_card_eq
  have hka : k ^ (p ^ a) ∈ centralizer (R : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h2 : y ^ (u ^ (p ^ a)) = y ^ 1 := by
      apply pow_eq_pow_iff_modEq.2
      rw [Nat.modEq_iff_dvd]
      have ho : orderOf y ∣ p ^ (a + 1) :=
        (ha ▸ Subgroup.orderOf_dvd_natCard _ hy).trans (pow_dvd_pow p a.le_succ)
      have ho' : (orderOf y : ℤ) ∣ (p : ℤ) ^ (a + 1) := by exact_mod_cast ho
      have h1 := dvd_sub_pow_of_dvd_sub hu1 a
      rw [one_pow] at h1
      have h3 : (p : ℤ) ^ (a + 1) ∣ (1 : ℤ) - (u : ℤ) ^ (p ^ a) := by
        have := dvd_neg.2 h1
        rwa [neg_sub] at this
      push_cast
      exact ho'.trans h3
    have h3 := hiter (p ^ a) y hy
    rw [h2, pow_one] at h3
    calc y * k ^ (p ^ a) = k ^ (p ^ a) * y * (k ^ (p ^ a))⁻¹ * k ^ (p ^ a) := by rw [h3]
      _ = k ^ (p ^ a) * y := by group
  obtain ⟨b, m, hpm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k).ne' p hp.ne_one
  have hkmR : k ^ m ∈ (R : Subgroup X) := by
    have hpg : IsPGroup p (zpowers (k ^ m)) := by
      have h1 : (k ^ m) ^ (p ^ b) = 1 := by
        rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h1)
      exact IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
    have hle : zpowers (k ^ m) ≤ normalizer ((R : Subgroup X) : Set X) := zpowers_le.2 (pow_mem hk m)
    have hsup := R.is_maximal' (R.isPGroup'.to_sup_of_normal_left' hpg hle) le_sup_left
    have hmem : k ^ m ∈ (R : Subgroup X) ⊔ zpowers (k ^ m) := mem_sup_right (mem_zpowers _)
    rwa [hsup] at hmem
  have hkm' : k ^ m ∈ centralizer (R : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := hpow y hy
    obtain ⟨j, hj⟩ := hpow _ hkmR
    rw [← hj, pow_mul_comm]
  have hcop : Nat.Coprime m (p ^ a) :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)).symm
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hkk : k = (k ^ m) ^ x * (k ^ (p ^ a)) ^ y := by
    calc k = k ^ (x * (m : ℤ) + y * ((p ^ a : ℕ) : ℤ)) := by rw [hxy, zpow_one]
      _ = (k ^ m) ^ x * (k ^ (p ^ a)) ^ y := by
        rw [zpow_add, mul_comm x, mul_comm y, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hkk]
  exact mul_mem (zpow_mem hkm' x) (zpow_mem hka y)

theorem uc22p22qza_mem_ker_of_coprime (R : Sylow p X)
    (hN : normalizer (R : Set X) ≤ centralizer (R : Set X)) {x : X} (hx : ¬ p ∣ orderOf x) :
    x ∈ (MonoidHom.transferSylow R hN).ker := by
  have hp : p.Prime := Fact.out
  rw [MonoidHom.mem_ker]
  obtain ⟨a, ha⟩ := R.isPGroup'.exists_card_eq
  have h1 : orderOf (MonoidHom.transferSylow R hN x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (MonoidHom.transferSylow R hN x) ∣ p ^ a := ha ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf x) (p ^ a) :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hx)).symm
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end Burnside

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qza_comm_of_isCyclic {H : Subgroup G} (hH : IsCyclic H) {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : x * y = y * x := by
  haveI := hH
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥H)
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (hg ⟨x, hx⟩)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hg ⟨y, hy⟩)
  have h1 : x = ((g ^ i : H) : G) := by rw [hi]
  have h2 : y = ((g ^ j : H) : G) := by rw [hj]
  rw [h1, h2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, zpow_mul_comm]

theorem uc22p22qza_fpf_of_mem_centralizer {p : ℕ} [Fact p.Prime] {M P P₀ : Subgroup G}
    (hcl : uniqueFourClauseTwo M P P₀ p)
    {d : G} (hd : d ∈ centralizer (uniqueFourLayer (centralizer (P₀ : Set G)) : Set G))
    (hdc : d ∈ centralizer (P₀ : Set G)) (hd1 : d ≠ 1) :
    ∀ t ∈ pCoreOf 2 M, t * d = d * t → t = 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨-, hcard, -, -, -, hcyc, hfrob, -⟩ := hcl
  obtain ⟨-, -, -, -, -, -, -, hfpf⟩ := hfrob
  set C : Subgroup G := centralizer (P₀ : Set G) with hC
  set E : Subgroup G := uniqueFourLayer C with hE
  set K : Subgroup G := C ⊓ centralizer (E : Set G) with hK
  have hEC : E ≤ C := uc22p22q_layer_le C
  have hP₀cyc : IsCyclic P₀ := isCyclic_of_prime_card hcard
  have hP₀K : P₀ ≤ K := fun z hz =>
    ⟨mem_centralizer_iff.2 fun y hy => uc22p22qza_comm_of_isCyclic hP₀cyc hy hz,
      mem_centralizer_iff.2 fun l hl => ((mem_centralizer_iff.1 (hEC hl)) z hz).symm⟩
  have hKn : ∀ c ∈ C, ∀ x ∈ K, c * x * c⁻¹ ∈ K := by
    intro c hc x hx
    refine ⟨C.mul_mem (C.mul_mem hc hx.1) (C.inv_mem hc), mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : c⁻¹ * l * c⁻¹⁻¹ ∈ E := uc22p22qo_layer_conj (C.inv_mem hc) hl
    rw [inv_inv] at hl'
    have h1 := mem_centralizer_iff.1 hx.2 _ hl'
    calc l * (c * x * c⁻¹) = c * ((c⁻¹ * l * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * l * c)) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * l := by group
  have huniq : ∀ u ∈ K, orderOf u = p → u ∈ P₀ := by
    intro u hu hup
    have hpu : IsPGroup p (zpowers u) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hup, pow_one])
    have hpP₀ : IsPGroup p P₀ := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
    have hle : zpowers u ≤ normalizer (P₀ : Set G) :=
      zpowers_le.2 (_root_.Subgroup.centralizer_le_normalizer (P₀ : Set G) hu.1)
    have hpH : IsPGroup p ↥(zpowers u ⊔ P₀) := hpu.to_sup_of_normal_right' hpP₀ hle
    have hHK : zpowers u ⊔ P₀ ≤ K := sup_le (zpowers_le.2 hu) hP₀K
    have hHc : IsCyclic ↥(zpowers u ⊔ P₀) := hcyc _ hHK hpH
    have hcu : Nat.card ↥((zpowers u).subgroupOf (zpowers u ⊔ P₀)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, Nat.card_zpowers, hup]
    have hcP : Nat.card ↥(P₀.subgroupOf (zpowers u ⊔ P₀)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hcard]
    haveI := hHc
    have heq : (zpowers u).subgroupOf (zpowers u ⊔ P₀) = P₀.subgroupOf (zpowers u ⊔ P₀) :=
      IsCyclic.subgroup_eq_iff_card_eq.2 (hcu.trans hcP.symm)
    have h2 : (⟨u, mem_sup_left (mem_zpowers u)⟩ : ↥(zpowers u ⊔ P₀)) ∈
        (zpowers u).subgroupOf (zpowers u ⊔ P₀) := mem_subgroupOf.2 (mem_zpowers u)
    rw [heq] at h2
    exact mem_subgroupOf.1 h2
  intro t ht htd
  by_cases hpd : p ∣ orderOf d
  ·
    have hup : orderOf (d ^ (orderOf d / p)) = p := orderOf_pow_orderOf_div (orderOf_pos d).ne' hpd
    have huP₀ : d ^ (orderOf d / p) ∈ P₀ := huniq _ (pow_mem (show d ∈ K from ⟨hdc, hd⟩) _) hup
    have hu1 : d ^ (orderOf d / p) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hup
      exact hp.ne_one hup.symm
    have htu : t * d ^ (orderOf d / p) = d ^ (orderOf d / p) * t := Commute.pow_right htd _
    exact hfpf _ (mem_sup_right huP₀) hu1 t ht htu
  ·
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥K))
    have hRc : IsCyclic (R : Subgroup ↥K) := by
      have h1 : (R : Subgroup ↥K).map K.subtype ≤ K := map_subtype_le _
      have h2 : IsPGroup p ↥((R : Subgroup ↥K).map K.subtype) := R.isPGroup'.map _
      haveI := hcyc _ h1 h2
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective (R : Subgroup ↥K) K.subtype K.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) p (by rw [hcard])
    set z₀ : ↥K := ⟨(z : G), hP₀K z.2⟩ with hz₀def
    have hz₀ : orderOf z₀ = p := by
      rw [hz₀def, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz]
    have hz₀c : ∀ x : ↥K, x * z₀ = z₀ * x := fun x =>
      Subtype.ext ((mem_centralizer_iff.1 x.2.1 z z.2).symm)
    have hz₀R : z₀ ∈ (R : Subgroup ↥K) := by
      haveI hn : (zpowers z₀).Normal := ⟨fun n hn g => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hn
        have h1 : g * z₀ ^ i = z₀ ^ i * g := Commute.zpow_right (hz₀c g) i
        rw [h1, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers z₀) i⟩
      have hpg : IsPGroup p (zpowers z₀) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₀, pow_one])
      exact hpg.le_sylow_of_normal R (mem_zpowers z₀)
    have hNC := uc22p22qza_normalizer_le_centralizer R hRc hz₀R hz₀ hz₀c
    have hNp : ¬ p ∣ Nat.card (MonoidHom.transferSylow R hNC).ker :=
      MonoidHom.not_dvd_card_ker_transferSylow R hNC
    set N' : Subgroup G := (MonoidHom.transferSylow R hNC).ker.map K.subtype with hN'
    have hN'K : N' ≤ K := map_subtype_le _
    have hmem : ∀ x ∈ K, ¬ p ∣ orderOf x → x ∈ N' := by
      intro x hx hpx
      refine ⟨⟨x, hx⟩, uc22p22qza_mem_ker_of_coprime R hNC ?_, rfl⟩
      rwa [Subgroup.orderOf_mk]
    have hN'ord : ∀ x ∈ N', ¬ p ∣ orderOf x := by
      rintro _ ⟨y, hy, rfl⟩ hdvd
      apply hNp
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hdvd
      exact hdvd.trans (Subgroup.orderOf_dvd_natCard _ hy)
    have hN'n : (N'.subgroupOf C).Normal := by
      refine ⟨fun x hx c => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      have h1 : (c : G) * (x : G) * (c : G)⁻¹ ∈ K := hKn c c.2 x (hN'K hx)
      have h2 : orderOf ((c : G) * (x : G) * (c : G)⁻¹) = orderOf (x : G) := by
        have := orderOf_injective (MulAut.conj (c : G)).toMonoidHom (MulAut.conj (c : G)).injective (x : G)
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
      have h3 := hmem _ h1 (by rw [h2]; exact hN'ord _ hx)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h3
    have hN'Q : N' ≤ uniqueFourPrimeCore p C := by
      unfold uniqueFourPrimeCore relPPrimeCore
      refine le_sSup ⟨hN'K.trans inf_le_left, hN'n, ?_⟩
      have hc : Nat.card N' = Nat.card (MonoidHom.transferSylow R hNC).ker :=
        Subgroup.card_map_of_injective K.subtype_injective
      rw [hc]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hNp
    have hdN' : d ∈ N' := hmem d ⟨hdc, hd⟩ hpd
    exact hfpf d (mem_sup_left (hN'Q hdN')) hd1 t ht htd

end CFSG.LocalAnalysis.UniquenessCase.UC22
