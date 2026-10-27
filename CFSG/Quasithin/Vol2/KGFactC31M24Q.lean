module

public import CFSG.Quasithin.Vol2.KGFactC31M24Set
public import CFSG.Quasithin.Vol2.KGFactC31NatSec
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Vol2.KGFactC31M24Nor

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
  _root_.Certificates

variable {A : Type} [Group A] [Finite A]

theorem not_isPGroup_sl3 : ¬ IsPGroup 2 ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [E8.card_statedSL3] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem mem_of_sylow {p : ℕ} [hp : Fact p.Prime] {N M₀ : Subgroup A} {x y : A} (hxN : x ∈ N)
    (hx : orderOf x = p) (hNp : ¬ p ^ 2 ∣ Nat.card N) (hM₀N : M₀ ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (M₀ : Set A)) (hy : y ∈ M₀) (hyk : ∃ k, y ^ p ^ k = 1)
    (hy1 : y ≠ 1) : x ∈ M₀ := by
  set x' : ↥N := ⟨x, hxN⟩
  set y' : ↥N := ⟨y, hM₀N hy⟩
  have hox : orderOf x' = p := by rw [← Subgroup.orderOf_coe]; exact hx
  have hP : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
  have hPi : ¬ p ∣ (Subgroup.zpowers x').index := by
    intro hd
    have h1 := (Subgroup.zpowers x').card_mul_index
    rw [Nat.card_zpowers, hox] at h1
    obtain ⟨c, hc⟩ := hd
    exact hNp ⟨c, by rw [← h1, hc]; ring⟩
  have hyk' : ∃ k : ℕ, y' ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hyk
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi hyk'
  have hz1 : g⁻¹ * y' * g ≠ 1 := by
    intro h1
    apply hy1
    have := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc y = (g : A) * ((g : A)⁻¹ * y * g) * (g : A)⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hxz := mem_zpowers_of_prime hp.out hox hg hz1
  have hzM : ((g⁻¹ * y' * g : ↥N) : A) ∈ M₀ := by
    have hgN := hnorm (Subgroup.inv_mem N g.2)
    have := (Subgroup.mem_normalizer_iff.mp hgN y).mp hy
    simpa [mul_assoc] using this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hxi : x = ((g⁻¹ * y' * g : ↥N) : A) ^ i := by
    have := congrArg Subtype.val hi
    simpa using this.symm
  rw [hxi]
  exact M₀.zpow_mem hzM i

theorem concl_q
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) (hR : R = Qg.map f)
    (hV : V = (eSub basis_u5).map f) {y : A} (hy : y ∈ M₀) (hyk : ∃ k, y ^ 7 ^ k = 1)
    (hy1 : y ≠ 1) : Concl S M₀ R M V := by
  have hvA : EBasis fun i => f (vU5 i) := basis_u5.map hf.inj
  have hVA : (eSub basis_u5).map f = eSub hvA := eSub_map basis_u5 hf.inj
  have hNQ : Subgroup.normalizer (R : Set A) = (Subgroup.normalizer (Qg : Set G₀)).map f := by
    rw [hR, hf.map_normalizer]
  have hN5 : eNorm basis_u5 ≤ Subgroup.normalizer (Qg : Set G₀) := by
    rw [← cent_u5]
    exact normalizer_le_normalizer_centralizer _
  have hNqN : Nq.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hNQ]
    exact Subgroup.map_mono (Nq_le.trans hN5)
  have hRc : Nat.card R = 128 := by rw [hR, hf.card_map, card_Qg]
  have hNc : Nat.card (Subgroup.normalizer (R : Set A)) = 21504 := by
    rcases card_normalizer_eq hf h.R_ne_bot (by rw [hRc]; norm_num) h.hrad hNqN
        (by rw [card_Nq]; norm_num) with
      ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [hRc] at h2; norm_num at h2
    · rw [hRc] at h2; norm_num at h2
    · rw [hRc] at h2; norm_num at h2
    · exact h1
    all_goals rw [hRc] at h2; norm_num at h2
  have hLqN : Lq.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hNQ]
    exact Subgroup.map_mono (Lq_le.trans hN5)
  have hi : (Lq.map f).relIndex (Subgroup.normalizer (R : Set A)) ≤ 4 := by
    have h1 := (Lq.map f).relIndex_mul_card (K := Subgroup.normalizer (R : Set A))
    rw [inf_eq_left.mpr hLqN, hNc, hf.card_map, card_Lq] at h1
    omega
  have hM₀Lq : M₀ ≤ Lq.map f := le_of_perfect_of_relIndex_le h.hM₀R h.hper hi
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy7N : f y7 ∈ Subgroup.normalizer (R : Set A) := by
    rw [hNQ]
    exact ⟨y7, hN5 y7_mem, rfl⟩
  have hoy7 : orderOf (f y7) = 7 := by rw [orderOf_injective f hf.inj, orderOf_y7]
  have hNp : ¬ 7 ^ 2 ∣ Nat.card (Subgroup.normalizer (R : Set A)) := by rw [hNc]; norm_num
  have hy7M : f y7 ∈ M₀ :=
    mem_of_sylow hy7N hoy7 hNp h.hM₀R h.normal_in_normalizer hy hyk hy1
  have hLqM : Lq.map f ≤ M₀ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine conjGenOf_le fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hmN : f (elt w) ∈ Subgroup.normalizer (R : Set A) := by
      rw [hNQ]
      exact ⟨elt w, hN5 (mj_mem w hw), rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (h.normal_in_normalizer hmN) (f y7)).mp hy7M
  have hM₀eq : M₀ = Lq.map f := le_antisymm hM₀Lq hLqM
  have hNV : eNorm hvA = (eNorm basis_u5).map f := by
    show Subgroup.normalizer (eSub hvA : Set A) = _
    rw [← hVA, ← hf.map_normalizer]
  have hM₀N : M₀ ≤ eNorm hvA := by
    rw [hNV, hM₀eq]
    exact Subgroup.map_mono Lq_le
  have hCV : Subgroup.centralizer (eSub hvA : Set A) = R := by
    rw [← hVA, ← hf.map_centralizer, cent_u5, hR]
  have hCM₀ : M₀ ⊓ Subgroup.centralizer (eSub hvA : Set A) = (eSub basis_et).map f := by
    rw [← hVA, ← hf.map_centralizer, hM₀eq, ← Subgroup.map_inf _ _ f hf.inj, Lq_inf_cent]
  have hker₀ := ker_eNHom hvA hM₀N hCM₀
  have hEtM₀ : (eSub basis_et).map f ≤ M₀ := hM₀eq ▸ Subgroup.map_mono et_le_Lq
  have hEtc : Nat.card ((eSub basis_et).map f) = 64 := by
    rw [hf.card_map, card_eSub]; norm_num
  have hcM₀ : Nat.card M₀ = 10752 := by rw [hM₀eq, hf.card_map, card_Lq]
  have hsurj₀ : Function.Surjective (E16.eNHom hvA hM₀N) := by
    have h1 := card_range_eq hEtM₀ (E16.eNHom hvA hM₀N) hker₀
    rw [hEtc, hcM₀] at h1
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (by rw [E8.card_statedSL3]; omega)
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hEt2 : IsPGroup 2 ↥((eSub basis_et).map f) :=
    IsPGroup.of_card (n := 6) (by rw [hEtc]; norm_num)
  have hO : pCoreOf 2 M₀ = (eSub basis_et).map f := pCoreOf_eq_of_surj hEtM₀ hEt2 _ hsurj₀ hker₀
    (noNormalTwo_of_simple not_isPGroup_sl3)
  have hpk : CFSG.pCore 2 ↥M₀ = (E16.eNHom hvA hM₀N).ker := by
    rw [← Hex.pCoreOf_subgroupOf' M₀, hO, hker₀]
  have hpsl : IsPSL 3 2 1 (ModO2 M₀) := E8.isPSL_of_equiv3
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀))
  have hext : IsExt ↥M₀ (fun N _ => IsE2 6 N) (fun Y _ => IsPSL 3 2 1 Y) := by
    have hn : (((eSub basis_et).map f).subgroupOf M₀).Normal := by
      rw [← hker₀]
      exact MonoidHom.normal_ker _
    exact ⟨((eSub basis_et).map f).subgroupOf M₀, hn, ⟨(Subgroup.subgroupOfEquivOfLe hEtM₀).trans
      ((MulEquiv.subgroupCongr (eSub_map basis_et hf.inj)).trans
        (ecoords (basis_et.map hf.inj)))⟩, E8.isPSL_of_equiv3
        ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀))⟩
  have hRCA : R ≤ Subgroup.centralizer (eSub hvA : Set A) := hCV.symm.le
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (eSub hvA : Set A) = R := by
    rw [hCV]
    exact inf_eq_right.mpr le_sup_right
  have hsum : IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) false 1 := by
    rw [hV, hVA]
    exact sum_natural_of_surj hvA hM₀N hRCA hsurj₀ hXC
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' h.hMN
  refine ⟨Or.inr (Or.inr (Or.inl ⟨h.hSs, Or.inr (Or.inr ?_)⟩)),
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact hext
  · refine summand_of_card ?_
    rw [hV, hf.card_map, card_eSub]
    norm_num

end CFSG.Quasithin.KGC31.M24

end
