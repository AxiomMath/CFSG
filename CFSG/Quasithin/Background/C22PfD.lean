module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Background.C22PfB
public import CFSG.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

namespace C22Pf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_of_mul {N : Subgroup G} {a n : G} (ha : a ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) (m : ℕ) : (a ^ m)⁻¹ * (a * n) ^ m ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (a ^ (m + 1))⁻¹ * (a * n) ^ (m + 1) =
        a⁻¹ * ((a ^ m)⁻¹ * (a * n) ^ m) * a⁻¹⁻¹ * n := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) _).mp ih) hn

theorem asc22One_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y) :
    ASC22One G := by
  intro H R L hH hR hL
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hRH : R ≤ H := hR.1
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  set Z := pCoreOf 2 L with hZ
  set C := centralizerSection H L Z with hC
  have hZL : Z ≤ L := pCoreOf_le 2 L
  have hZ2 : IsPGroup 2 ↥Z := pCoreOf_isPGroup 2 L
  have hCn : ∀ g ∈ H, g ∈ Subgroup.normalizer (L : Set G) →
      g ∈ Subgroup.normalizer (C : Set G) := fun g hgH hgL =>
    A4.mem_normalizer_of_conj_mem fun m hm =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hgH) hgL
        (normalizer_le_normalizer_pCoreOf 2 L hgL) hm
  have hCH : C ≤ H := centralizerSection_le_left _ _ _
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := centralizerSection_le_normalizer_left _ _ _
  have hZC : Z ≤ C := by
    intro o ho
    refine ⟨hLH (hZL ho), Subgroup.le_normalizer (hZL ho), Subgroup.le_normalizer ho,
      fun x hx => ?_⟩
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hx) o).mp ho)
      (Z.inv_mem ho)
  apply Set.Subset.antisymm
  · rintro s ⟨hsR, hsLC⟩
    obtain ⟨x, hxL, c, hcC, hxc⟩ := Set.mem_mul.mp hsLC
    set A := R ⊓ (L ⊔ C) with hA
    have hLCN : L ⊔ C ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hCL
    have hLCH : L ⊔ C ≤ H := sup_le hLH hCH
    have hAC : A ≤ Subgroup.normalizer (C : Set G) := fun a ha =>
      hCn a (hLCH ha.2) (hLCN ha.2)
    have hA2 : IsPGroup 2 ↥A := hR2.to_le inf_le_left
    set Y := (L ⊓ (A ⊔ C)) ⊔ Z with hY
    have hYL : Y ≤ L := sup_le inf_le_left hZL
    have hYAC : Y ≤ A ⊔ C := sup_le inf_le_right (hZC.trans le_sup_right)
    have hYn : H ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (Y : Set G) := by
      intro g hg
      have hgC := hCn g hg.1.1 hg.2
      have hgLC : g ∈ Subgroup.normalizer ((L ⊔ C : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_sup L C ⟨hg.2, hgC⟩
      have hgA : g ∈ Subgroup.normalizer (A : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1.2, hgLC⟩
      have hgAC : g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_sup A C ⟨hgA, hgC⟩
      have hgLAC : g ∈ Subgroup.normalizer ((L ⊓ (A ⊔ C) : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, hgAC⟩
      exact Subgroup.inf_normalizer_le_normalizer_sup _ Z
        ⟨hgLAC, normalizer_le_normalizer_pCoreOf 2 L hg.2⟩
    set Z' := Y ⊓ C with hZ'
    have hYC : Y ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
      hCn y (hLH (hYL hy)) (Subgroup.le_normalizer (hYL hy))
    have hY2 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ Z' := by
      intro y hy
      have hy' := hYAC hy
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A C hAC] at hy'
      obtain ⟨a, ha, c', hc', hac⟩ := Set.mem_mul.mp hy'
      obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
      have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, Y.pow_mem hy _, ?_⟩
      have h1 := pow_mem_of_mul (hAC ha) hc' (2 ^ k)
      rwa [hk', inv_one, one_mul, hac] at h1
    obtain ⟨S, hS, hZS⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_sup_right : Z ≤ Y) hZ2
    have hZ'n : (Z'.subgroupOf Y).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨Y.mul_mem (Y.mul_mem g.2 hn.1) (Y.inv_mem g.2), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hYC g.2) _).mp hn.2
    have hidx2 : ∃ n : ℕ, Z'.relIndex Y = 2 ^ n := by
      have hq : IsPGroup 2 (↥Y ⧸ Z'.subgroupOf Y) := by
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨k, hk⟩ := hY2 y y.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := hq.exists_card_eq
      exact ⟨n, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]⟩
    have hSZ : Y ≤ S ⊔ Z' := by
      obtain ⟨n, hn⟩ := hidx2
      have h1 : (S ⊔ Z').relIndex Y ∣ 2 ^ n :=
        hn ▸ Subgroup.relIndex_dvd_of_le_left Y le_sup_right
      have h2 : (S ⊔ Z').relIndex Y ∣ S.relIndex Y :=
        Subgroup.relIndex_dvd_of_le_left Y le_sup_left
      have hcop : Nat.Coprime (2 ^ n) (S.relIndex Y) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2)
      exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have hZ'S : Z' ≤ Subgroup.normalizer (S : Set G) := by
      refine fun z hz => A4.mem_normalizer_of_conj_mem fun t ht => ?_
      have htL : t ∈ L := hYL (hS.1 ht)
      have h1 : t * z * t⁻¹ * z⁻¹ ∈ Z := hz.2.2.2.2 t htL
      have e : z * t * z⁻¹ = (t * z * t⁻¹ * z⁻¹)⁻¹ * t := by group
      rw [e]
      exact S.mul_mem (hZS (Z.inv_mem h1)) ht
    have hYS : Y ≤ Subgroup.normalizer (S : Set G) :=
      hSZ.trans (sup_le Subgroup.le_normalizer hZ'S)
    have hSR : S ≤ R := by
      have hSO : S ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer 2 hS.1 hYS hS.2.1
      refine hSO.trans (le_of_le_cComp_of_sqtk hA37 hH hR hL ((pCoreOf_le 2 Y).trans hYL)
        (pCoreOf_isPGroup 2 Y) fun g hg => normalizer_le_normalizer_pCoreOf 2 Y (hYn hg))
    have hsA : s ∈ A := by
      refine ⟨hsR, ?_⟩
      rw [← hxc]
      exact Subgroup.mul_mem_sup hxL hcC
    have hxY : x ∈ Y := by
      refine Subgroup.mem_sup_left ⟨hxL, ?_⟩
      have e : x = s * c⁻¹ := by rw [← hxc]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hsA) (Subgroup.mem_sup_right (C.inv_mem hcC))
    have hxSZ := hSZ hxY
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left S Z' hZ'S] at hxSZ
    obtain ⟨r, hr, q, hq, hrq⟩ := Set.mem_mul.mp hxSZ
    refine Set.mem_mul.mpr ⟨r, ⟨hSR hr, hYL (hS.1 hr)⟩, q * c, ?_, ?_⟩
    · have hqc : q * c ∈ C := C.mul_mem hq.2 hcC
      have hqcR : q * c ∈ R := by
        have e : q * c = r⁻¹ * s := by rw [← hxc, ← hrq]; group
        rw [e]
        exact R.mul_mem (R.inv_mem (hSR hr)) hsR
      exact ⟨hqcR, hqc.2⟩
    · rw [← mul_assoc, hrq, hxc]
  · rintro s hs
    obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.mp hs
    refine ⟨R.mul_mem hr.1 hc.1, Set.mem_mul.mpr ⟨r, hr.2, c, ?_, rfl⟩⟩
    exact centralizerSection_mono hRH _ _ hc

end C22Pf

end CFSG.Quasithin
