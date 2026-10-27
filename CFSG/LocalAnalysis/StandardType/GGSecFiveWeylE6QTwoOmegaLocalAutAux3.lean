module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux2

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

theorem qMap_surjective {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    Function.Surjective (qMap (K := K) θ) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (θ.symm x)
  exact ⟨a, by rw [qMap_apply, ha, θ.apply_symm_apply]⟩

theorem bstar_basic {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    x ∈ Bs ∧ x ∉ L ∧ orderOf x = 3 ∧
      (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥ ∧
      (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
  classical
  have hxmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := hBL ▸ Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := hxmem.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hxmem.2
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  let ZL : Subgroup G := (Subgroup.center L).map L.subtype
  have hZ2ZL : IsPGroup 2 ZL :=
    hZ2.of_equiv (Subgroup.equivMapOfInjective (Subgroup.center L) L.subtype
      L.subtype_injective)
  have hxZL : x ∈ L → x ∈ ZL := by
    intro hxL
    have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp hxC l l.2
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hxZ, rfl⟩
  have hEbot : (Bs ⊓ L) ⊓ ZL = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have heBs : (e : G) ∈ Bs := he.1.1
    have heZ : (e : G) ∈ ZL := he.2
    have he3 : (e : G) ^ 3 = 1 := hBs.2 (e : G) heBs
    obtain ⟨n, hn⟩ := hZ2ZL ⟨(e : G), heZ⟩
    have he2 : (e : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd3 : orderOf (e : G) ∣ 3 := orderOf_dvd_of_pow_eq_one he3
    have hdvd2 : orderOf (e : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one he2
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    have hone : orderOf (e : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp hone
  have hxL : x ∉ L := by
    intro hxL
    have hxbot : x ∈ (Bs ⊓ L) ⊓ ZL := ⟨⟨hxBs, hxL⟩, hxZL hxL⟩
    rw [hEbot] at hxbot
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  have hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have heE : e ∈ Bs ⊓ L := he.1
    have hezx : (e : G) ∈ Subgroup.zpowers x := he.2
    have heC : (e : G) ∈ Subgroup.centralizer (L : Set G) :=
      (Subgroup.zpowers_le.mpr hxC) hezx
    have heZL : (e : G) ∈ ZL := by
      refine Subgroup.mem_map.mpr ⟨⟨(e : G), heE.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp heC l l.2
    have hbot : (e : G) ∈ (Bs ⊓ L) ⊓ ZL := ⟨heE, heZL⟩
    rw [hEbot] at hbot
    exact Subgroup.mem_bot.mp hbot
  exact ⟨hxBs, hxL, hord, hEbot, hExbot⟩

theorem Ebar_selfCent {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ∀ g : OrthRest.RPlus K 4, (∀ y ∈ Ebar Bs L θ, g * y = y * g) → g ^ 3 = 1 →
      g ∈ Ebar Bs L θ := by
  classical
  intro g hcent hg3
  obtain ⟨hxBs, hxL, hxord, hEbot, hExbot⟩ := bstar_basic hZ2 hBs hx1 hBL
  have hcp : ¬ 3 ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  obtain ⟨l, hl, hl3⟩ := exists_lift_pow_eq_one (p := 3) Nat.prime_three (qMap_surjective θ)
    (le_of_eq (qMap_ker (K := K) θ)) hcp (g := g) hg3
  have hZL : ∀ e : ↥L, e ∈ EL Bs L → ⁅l, e⁆ ∈ Subgroup.center ↥L := by
    intro e he
    rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker, map_commutatorElement, hl]
    exact (show Commute g (qMap (K := K) θ e) from
      hcent (qMap (K := K) θ e) ((mem_Ebar θ).mpr ⟨e, he, rfl⟩)).commutator_eq
  have hcentE : ∀ e : ↥L, e ∈ EL Bs L → l * e = e * l := by
    intro e he
    have h1 : ⁅(l : ↥L) ^ 3, e⁆ = 1 := by
      have hc : (l : ↥L) ^ 3 ∈ Subgroup.center ↥L := by
        rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker, map_pow, hl]
        exact hg3
      exact (show Commute ((l : ↥L) ^ 3) e from
        (Subgroup.mem_center_iff.mp hc e).symm).commutator_eq
    have h2 := CFSG.LocalAnalysis.ComponentInitial.commutatorElement_pow_left_of_mem_center
      (x := l) (y := e) (hZL e he) 3
    have h3 : ⁅l, e⁆ ^ 3 = 1 := by rw [← h2]; exact h1
    have hz := hZL e he
    obtain ⟨n, hn⟩ := hZ2 ⟨⁅l, e⁆, hz⟩
    have h2e : ⁅l, e⁆ ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd3 : orderOf ⁅l, e⁆ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hdvd2 : orderOf ⁅l, e⁆ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2e
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    have hone : orderOf ⁅l, e⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
    have hcomm : ⁅l, e⁆ = 1 := orderOf_eq_one_iff.mp hone
    rw [commutatorElement_def] at hcomm
    calc l * e = l * e * l⁻¹ * e⁻¹ * (e * l) := by group
      _ = 1 * (e * l) := by rw [hcomm]
      _ = e * l := one_mul _
  have hdecomp : ∀ b (hb : b ∈ Bs),
      ∃ (e : ↥(EB Bs L)) (y : ↥((Subgroup.zpowers x).subgroupOf Bs)),
        (e : G) * (y : G) = b := by
    intro b hb
    have hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) :=
      bstar_isComplement hBs hcard hcardE hxBs hxord hExbot
    have hex := (Subgroup.isComplement_iff_existsUnique.mp
      (Subgroup.isComplement'_def.mp hcompl)) (⟨b, hb⟩ : ↥Bs)
    obtain ⟨⟨⟨e, he⟩, ⟨y, hy⟩⟩, hey⟩ := hex.exists
    exact ⟨⟨e, he⟩, ⟨y, hy⟩, by simpa using congrArg (fun z : ↥Bs => (z : G)) hey⟩
  have hcentBs : (l : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨e, y, hey⟩ := hdecomp b hb
    have heE : ((e : ↥Bs) : G) ∈ Bs ⊓ L := mem_EB.mp e.2
    have hyx : ((y : ↥Bs) : G) ∈ Subgroup.zpowers x :=
      Subgroup.mem_subgroupOf.mp y.2
    have hle : (l : G) * ((e : ↥Bs) : G) = ((e : ↥Bs) : G) * (l : G) := by
      have h1 := hcentE ⟨((e : ↥Bs) : G), heE.2⟩ (mem_EL.mpr heE)
      simpa using congrArg (fun z : ↥L => (z : G)) h1
    have hxcent : x ∈ Subgroup.centralizer ({(l : G)} : Set G) := by
      have h0 : (l : G) * x = x * (l : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2)
      exact Subgroup.mem_centralizer_singleton_iff.mpr h0.symm
    have hly : (l : G) * ((y : ↥Bs) : G) = ((y : ↥Bs) : G) * (l : G) := by
      have h1 : ((y : ↥Bs) : G) ∈ Subgroup.centralizer ({(l : G)} : Set G) :=
        (Subgroup.zpowers_le (H := Subgroup.centralizer ({(l : G)} : Set G))).mpr hxcent hyx
      exact (Subgroup.mem_centralizer_singleton_iff.mp h1).symm
    rw [← hey]
    calc (((e : ↥Bs) : G) * ((y : ↥Bs) : G)) * (l : G)
        = ((e : ↥Bs) : G) * (((y : ↥Bs) : G) * (l : G)) := by group
      _ = ((e : ↥Bs) : G) * ((l : G) * ((y : ↥Bs) : G)) := by rw [hly]
      _ = (((e : ↥Bs) : G) * (l : G)) * ((y : ↥Bs) : G) := by group
      _ = ((l : G) * ((e : ↥Bs) : G)) * ((y : ↥Bs) : G) := by rw [hle]
      _ = (l : G) * (((e : ↥Bs) : G) * ((y : ↥Bs) : G)) := by group
  have hlBs : (l : G) ∈ Bs :=
    hstar (l : G) hcentBs (by simpa using congrArg (fun z : ↥L => (z : G)) hl3)
  exact (mem_Ebar θ).mpr ⟨l, mem_EL.mpr ⟨hlBs, l.2⟩, hl⟩

end CFSG.StandardType.E6QTwo

end
