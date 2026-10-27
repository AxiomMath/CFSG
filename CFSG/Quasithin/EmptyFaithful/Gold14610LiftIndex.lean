module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

theorem mem_of_pow_three_of_map_mem {Q : Type*} [Group Q] (N K' : Subgroup Q) [N.Normal]
    [K'.Normal] (hN : Nat.Coprime 3 (Nat.card N)) {x : Q} (hx : x ^ 3 = 1)
    (hxK : QuotientGroup.mk' N x ∈ K'.map (QuotientGroup.mk' N)) : x ∈ K' := by
  obtain ⟨k, hk, hkx⟩ := hxK
  have hn : k⁻¹ * x ∈ N := QuotientGroup.eq.mp hkx
  have h1 : (k⁻¹ * x) ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := ↥N) (x := ⟨_, hn⟩)
    exact congrArg Subtype.val this
  have hxk : (QuotientGroup.mk x : Q ⧸ K') = QuotientGroup.mk (k⁻¹ * x) := by
    rw [QuotientGroup.eq]
    have := Subgroup.Normal.conj_mem inferInstance k⁻¹ (K'.inv_mem hk) x⁻¹
    simpa [mul_assoc] using this
  have h2 : (QuotientGroup.mk x : Q ⧸ K') ^ Nat.card N = 1 := by
    rw [hxk, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have h3 : (QuotientGroup.mk x : Q ⧸ K') ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have h4 : (QuotientGroup.mk x : Q ⧸ K') ^ Nat.gcd 3 (Nat.card N) = 1 :=
    pow_gcd_eq_one.mpr ⟨h3, h2⟩
  rw [Nat.Coprime.gcd_eq_one hN, pow_one] at h4
  exact (QuotientGroup.eq_one_iff _).mp h4

theorem map_subtype_inf_subgroupOf {G : Type*} [Group G] {I K L : Subgroup G} :
    (K.subgroupOf I ⊓ L.subgroupOf I).map I.subtype = K ⊓ L ⊓ I := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨⟨hy1, hy2⟩, y.2⟩
  · rintro ⟨⟨hx1, hx2⟩, hx3⟩
    exact ⟨⟨x, hx3⟩, ⟨hx1, hx2⟩, rfl⟩

theorem eq_sup_inf_of_twoResidual_le {G : Type} [Group G] [Finite G] {I I₁ I₂ K : Subgroup G}
    (hKI : K ≤ I) (hn : I ≤ Subgroup.normalizer (K : Set G))
    (hT : F6.IsGoldschmidtTripleIn I I₁ I₂)
    (h₁ : twoResidual (imgMod3 I I₁) ≤ imgMod3 I K)
    (h₂ : twoResidual (imgMod3 I I₂) ≤ imgMod3 I K) : I = K ⊔ (I₁ ⊓ I₂) := by
  have hT' := hT.subgroupOf
  have hI₁ : I₁ ≤ I := hT.1 ▸ le_sup_left
  have hI₂ : I₂ ≤ I := hT.1 ▸ le_sup_right
  set N := CFSG.pPrimeCore 3 ↥I with hNdef
  set K' := K.subgroupOf I with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hn
  have hN3 : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have key : ∀ {G₁ G₂ : Subgroup ↥I}, IsGoldschmidtTriple G₁ G₂ →
      twoResidual (G₁.map (QuotientGroup.mk' N)) ≤ K'.map (QuotientGroup.mk' N) →
      twoResidual G₁ ≤ K' := by
    intro G₁ G₂ hG hres
    rw [F6.twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxG, hxo⟩ := hx
    have hx3 : orderOf x ∣ 3 := F6.orderOf_dvd_three_of_odd hG hxG hxo
    have hx3' : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hx3
    have hdo : Odd (orderOf (QuotientGroup.mk' N x)) :=
      Odd.of_dvd_nat hxo (orderOf_map_dvd _ _)
    have hd := F6.mem_twoResidual_of_odd (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hxG) hdo
    exact mem_of_pow_three_of_map_mem N K' hN3 hx3' (hres hd)
  have hG₁ : I₁.subgroupOf I ≤ K' ⊔ (I₁.subgroupOf I ⊓ I₂.subgroupOf I) :=
    calc I₁.subgroupOf I
        = I₁.subgroupOf I ⊓ I₂.subgroupOf I ⊔ twoResidual (I₁.subgroupOf I) :=
          (F6.inf_sup_twoResidual_left hT').symm
      _ ≤ I₁.subgroupOf I ⊓ I₂.subgroupOf I ⊔ K' := sup_le_sup_left (key hT' h₁) _
      _ = K' ⊔ (I₁.subgroupOf I ⊓ I₂.subgroupOf I) := sup_comm _ _
  have hG₂ : I₂.subgroupOf I ≤ K' ⊔ (I₁.subgroupOf I ⊓ I₂.subgroupOf I) :=
    calc I₂.subgroupOf I
        = I₁.subgroupOf I ⊓ I₂.subgroupOf I ⊔ twoResidual (I₂.subgroupOf I) :=
          (F6.inf_sup_twoResidual_right hT').symm
      _ ≤ I₁.subgroupOf I ⊓ I₂.subgroupOf I ⊔ K' := sup_le_sup_left (key hT'.symm h₂) _
      _ = K' ⊔ (I₁.subgroupOf I ⊓ I₂.subgroupOf I) := sup_comm _ _
  have htop : K' ⊔ (I₁.subgroupOf I ⊓ I₂.subgroupOf I) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hT'.gen]
    exact sup_le hG₁ hG₂
  have hmap := congrArg (Subgroup.map I.subtype) htop
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hKI, map_subtype_inf_subgroupOf,
    inf_eq_left.mpr (inf_le_left.trans hI₁)] at hmap
  exact hmap.symm

theorem inf_eq_of_isSylowTwoOf {G : Type} [Group G] [Finite G] {I I₁ I₂ S : Subgroup G}
    (hT : F6.IsGoldschmidtTripleIn I I₁ I₂) (hS : IsSylowTwoOf S I) (h₁ : S ≤ I₁) (h₂ : S ≤ I₂) :
    I₁ ⊓ I₂ = S := by
  have hS' : IsSylowTwoOf (I₁ ⊓ I₂) I := hT.2.2.2
  have hle : S ≤ I₁ ⊓ I₂ := le_inf h₁ h₂
  have hmul := Subgroup.relIndex_mul_relIndex S (I₁ ⊓ I₂) I hle hS'.1
  have hodd : ¬ 2 ∣ S.relIndex (I₁ ⊓ I₂) := fun hd => by
    have h3 : 2 ∣ S.relIndex I := by
      rw [← hmul]
      exact Dvd.dvd.mul_right hd _
    exact hS.2.2 h3
  obtain ⟨k, hk⟩ := hS'.2.1.exists_card_eq
  have hdvd : S.relIndex (I₁ ⊓ I₂) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hne
    exact hodd (hj ▸ dvd_pow_self 2 hne)
  rw [hj0, pow_zero] at hj
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hj) hle

end Gold14610

end CFSG.Quasithin
