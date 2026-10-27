module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.SzN18

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem fitting_primes_of_case34 {X : Type} [Group X] [Finite X]
    (h34 : A36Case3 X ∨ A36Case4 X) :
    CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(CFSG.fittingSubgroup X) → r ≠ 2 ∧ r ≠ 3 := by
  rcases h34 with ⟨p, hp, hp3, hgf, ⟨e⟩, -⟩ | ⟨hgf, -, -, hprimes⟩
  · refine ⟨hgf, fun r hr hdvd => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have hcard : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard] at hdvd
    have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hdvd)
    subst hrp
    constructor <;> omega
  · refine ⟨hgf, fun r hr hdvd => ?_⟩
    have h5 := (hprimes r hr hdvd).1
    constructor <;> intro h <;> subst h <;> omega

section Bar

variable {G : Type} [Group G]

@[expose] noncomputable def toBar {I L : Subgroup G} (hLI : L ≤ I) : ↥L →* ↥(modO2Image I L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hLI)).codRestrict _
    fun j => ⟨⟨j, hLI j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩

theorem toBar_coe {I L : Subgroup G} (hLI : L ≤ I) (l : ↥L) :
    ((toBar hLI l : ↥(modO2Image I L)) : ↥I ⧸ CFSG.pCore 2 ↥I) =
      QuotientGroup.mk (⟨l, hLI l.2⟩ : ↥I) := rfl

@[expose] def fitBar (I L : Subgroup G) : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) :=
  (CFSG.fittingSubgroup ↥(modO2Image I L)).map (modO2Image I L).subtype

@[expose] def imgBar (I Y : Subgroup G) : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) :=
  (Y.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I))

theorem conj_mem_modO2Image {I L : Subgroup G} {b : ↥I}
    (hb : (b : G) ∈ Subgroup.normalizer (L : Set G)) {u : ↥I ⧸ CFSG.pCore 2 ↥I}
    (hu : u ∈ modO2Image I L) :
    QuotientGroup.mk b * u * (QuotientGroup.mk b)⁻¹ ∈ modO2Image I L := by
  obtain ⟨a, ha, rfl⟩ := hu
  have ha' : (a : G) ∈ L := Subgroup.mem_subgroupOf.1 ha
  refine ⟨b * a * b⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
  simpa using (Subgroup.mem_normalizer_iff.1 hb _).1 ha'

theorem mk_mem_normalizer_modO2Image {I L : Subgroup G} {b : ↥I}
    (hb : (b : G) ∈ Subgroup.normalizer (L : Set G)) :
    (QuotientGroup.mk b : ↥I ⧸ CFSG.pCore 2 ↥I) ∈
      Subgroup.normalizer ((modO2Image I L : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨conj_mem_modO2Image hb, fun h => ?_⟩
  have hb' : ((b⁻¹ : ↥I) : G) ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.coe_inv]
    exact inv_mem hb
  have := conj_mem_modO2Image hb' h
  simpa [mul_assoc] using this

end Bar

section Conj

@[expose] def conjNorm {Γ : Type*} [Group Γ] (X : Subgroup Γ) {z : Γ}
    (hz : z ∈ Subgroup.normalizer (X : Set Γ)) : ↥X ≃* ↥X where
  toFun u := ⟨z * u * z⁻¹, (Subgroup.mem_normalizer_iff.1 hz u).1 u.2⟩
  invFun u := ⟨z⁻¹ * u * z, (Subgroup.mem_normalizer_iff.1 hz _).2 (by simp [mul_assoc])⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem conjNorm_coe {Γ : Type*} [Group Γ] (X : Subgroup Γ) {z : Γ}
    (hz : z ∈ Subgroup.normalizer (X : Set Γ)) (u : ↥X) :
    ((conjNorm X hz u : ↥X) : Γ) = z * u * z⁻¹ := rfl

end Conj

section Main

variable {G : Type} [Group G]

theorem comm_fitBar_imgBar {I L Y : Subgroup G} (hLI : L ≤ I) (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hY : ∃ a b : ℕ, Nat.card ↥Y = 2 ^ a * 3 ^ b)
    (hF6 : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L)) →
      r ≠ 2 ∧ r ≠ 3)
    (hQ : ∀ l : ↥L, toBar hLI l ∈ CFSG.fittingSubgroup ↥(modO2Image I L) →
      (l : G) ∈ Subgroup.normalizer (Y : Set G)) :
    ⁅fitBar I L, imgBar I Y⁆ = ⊥ := by
  obtain ⟨a₀, b₀, hYcard⟩ := hY
  have hcop : Nat.Coprime (2 ^ a₀ * 3 ^ b₀)
      (Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L))) := by
    have h2 : Nat.Coprime 2 (Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h => (hF6 2 Nat.prime_two h).1 rfl
    have h3 : Nat.Coprime 3 (Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => (hF6 3 Nat.prime_three h).2 rfl
    exact Nat.Coprime.mul_left (h2.pow_left a₀) (h3.pow_left b₀)
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro f ⟨x, hxF, rfl⟩ y ⟨b, hb, rfl⟩
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha, hax⟩ := x.2
  have haL : (a : G) ∈ L := Subgroup.mem_subgroupOf.1 ha
  have hbY : (b : G) ∈ Y := Subgroup.mem_subgroupOf.1 hb
  have hxl : toBar hLI ⟨(a : G), haL⟩ = x := Subtype.ext (by rw [toBar_coe]; exact hax)
  have haN : (a : G) ∈ Subgroup.normalizer (Y : Set G) := hQ ⟨(a : G), haL⟩ (hxl ▸ hxF)
  have hz : (QuotientGroup.mk b : ↥I ⧸ CFSG.pCore 2 ↥I) ∈
      Subgroup.normalizer ((modO2Image I L : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) : Set _) :=
    mk_mem_normalizer_modO2Image (hYN hbY)
  set β := conjNorm (modO2Image I L) hz with hβ
  have hFβ : ∀ u : ↥(modO2Image I L), u ∈ CFSG.fittingSubgroup ↥(modO2Image I L) →
      β u ∈ CFSG.fittingSubgroup ↥(modO2Image I L) := by
    intro u hu
    have hchar := (inferInstance : (CFSG.fittingSubgroup ↥(modO2Image I L)).Characteristic).fixed β
    have : u ∈ (CFSG.fittingSubgroup ↥(modO2Image I L)).comap β.toMonoidHom := by
      rw [hchar]
      exact hu
    exact this
  have hwF : x * β x⁻¹ ∈ CFSG.fittingSubgroup ↥(modO2Image I L) :=
    mul_mem hxF (hFβ _ (inv_mem hxF))
  have hcomm : ⁅((x : ↥(modO2Image I L)) : ↥I ⧸ CFSG.pCore 2 ↥I),
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b⁆ = (((x * β x⁻¹ : ↥(modO2Image I L)) : _)) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, conjNorm_coe, hβ, QuotientGroup.mk'_apply,
      Subgroup.coe_inv, mul_assoc]
  set g : ↥I := ⁅a, b⁆ with hg
  have hgY : ((g : ↥I) : G) ∈ Y := by
    have h1 := (Subgroup.mem_normalizer_iff.1 haN (b : G)).1 hbY
    have h2 : ((a : G) * (b : G) * (a : G)⁻¹) * (b : G)⁻¹ ∈ Y := mul_mem h1 (inv_mem hbY)
    simpa [hg, commutatorElement_def] using h2
  have hd1 : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) g) ∣ 2 ^ a₀ * 3 ^ b₀ := by
    refine (orderOf_map_dvd _ g).trans ?_
    rw [← Subgroup.orderOf_coe, ← hYcard]
    exact Subgroup.orderOf_dvd_natCard Y hgY
  have hmapg : (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) g =
      (((x * β x⁻¹ : ↥(modO2Image I L)) : _)) := by
    rw [← hcomm, hg, map_commutatorElement, hax]
  have hd2 : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) g) ∣
      Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L)) := by
    rw [hmapg, Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hwF
  have h1 : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) g) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  change ⁅((x : ↥(modO2Image I L)) : ↥I ⧸ CFSG.pCore 2 ↥I),
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b⁆ = 1
  rw [hcomm, ← hmapg]
  exact orderOf_eq_one_iff.1 h1

end Main

section Final

variable {G : Type} [Group G] [Finite G]

theorem false_of_fitting_comm {I L Y : Subgroup G} (hLI : L ≤ I) (hYI : Y ≤ I) (hLY : ⁅L, Y⁆ = L)
    (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hY : ∃ a b : ℕ, Nat.card ↥Y = 2 ^ a * 3 ^ b)
    (hF6 : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L)) →
      r ≠ 2 ∧ r ≠ 3)
    (hQ : ∀ l : ↥L, toBar hLI l ∈ CFSG.fittingSubgroup ↥(modO2Image I L) →
      (l : G) ∈ Subgroup.normalizer (Y : Set G))
    (hgf : CFSG.generalizedFitting ↥(modO2Image I L) = CFSG.fittingSubgroup ↥(modO2Image I L))
    (hqs : CFSG.IsQuasisimple (↥(modO2Image I L) ⧸ CFSG.fittingSubgroup ↥(modO2Image I L))) :
    False := by
  have h1 := comm_fitBar_imgBar hLI hYN hY hF6 hQ
  have h2 : ⁅modO2Image I L, imgBar I Y⁆ = modO2Image I L := by
    have hc : ⁅L.subgroupOf I, Y.subgroupOf I⁆ = L.subgroupOf I := by
      apply Subgroup.map_injective I.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLI,
        Subgroup.map_subgroupOf_eq_of_le hYI, hLY]
    unfold modO2Image imgBar
    rw [← Subgroup.map_commutator, hc]
  have hFX : ⁅fitBar I L, modO2Image I L⁆ ≤ fitBar I L := by
    rw [Subgroup.commutator_le]
    rintro f ⟨u, hu, rfl⟩ x hx
    refine ⟨⁅u, ⟨x, hx⟩⁆, ?_, rfl⟩
    exact Subgroup.commutator_le_left (CFSG.fittingSubgroup ↥(modO2Image I L)) ⊤
      (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top _))
  have hh1 : ⁅⁅imgBar I Y, fitBar I L⁆, modO2Image I L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (imgBar I Y) (fitBar I L), h1, Subgroup.commutator_bot_left]
  have hh2 : ⁅⁅fitBar I L, modO2Image I L⁆, imgBar I Y⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono_left hFX).trans h1.le)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := modO2Image I L)
    (H₂ := imgBar I Y) (H₃ := fitBar I L) hh1 hh2
  rw [h2] at h3
  have hcent : ∀ (x : ↥(modO2Image I L)), ∀ f ∈ CFSG.fittingSubgroup ↥(modO2Image I L),
      f * x = x * f := by
    intro x f hf
    have hmem : ⁅((x : ↥(modO2Image I L)) : ↥I ⧸ CFSG.pCore 2 ↥I),
        ((f : ↥(modO2Image I L)) : ↥I ⧸ CFSG.pCore 2 ↥I)⁆ ∈ ⁅modO2Image I L, fitBar I L⁆ :=
      Subgroup.commutator_mem_commutator x.2 ⟨f, hf, rfl⟩
    rw [h3, Subgroup.mem_bot] at hmem
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
  have hle : ∀ x : ↥(modO2Image I L), x ∈ CFSG.fittingSubgroup ↥(modO2Image I L) := by
    intro x
    have hx : x ∈ Subgroup.centralizer
        ((CFSG.generalizedFitting ↥(modO2Image I L) : Subgroup ↥(modO2Image I L)) :
          Set ↥(modO2Image I L)) := by
      rw [hgf]
      exact Subgroup.mem_centralizer_iff.2 fun f hf => hcent x f hf
    rw [← hgf]
    exact CFSG.centralizer_generalizedFitting_le ↥(modO2Image I L) hx
  obtain ⟨u, v, huv⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hqs).exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective v
  exact huv (QuotientGroup.eq.2 (hle _))

end Final

end CFSG.Quasithin.SzN18
