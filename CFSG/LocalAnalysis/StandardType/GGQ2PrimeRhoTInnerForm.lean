module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTLiftComm
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4Torus
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3600

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU card_torusSU_le)

theorem rhoTInner_exists_not_mem
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) :
    ∃ (b : G) (hb : b ∈ Bs), ρ ⟨b, h.setting.Bs_norm hb⟩ ∉ T46 := by
  by_contra hcon
  have hall : ∀ (b : G) (hb : b ∈ Bs), ρ ⟨b, h.setting.Bs_norm hb⟩ ∈ T46 := fun b hb =>
    Classical.byContradiction fun hn => hcon ⟨b, hb, hn⟩
  obtain ⟨-, -, hx1, -, -, -, -, -⟩ := ggThmIHyp_unpack h.setting.hyp
  obtain ⟨-, hBab, -, -⟩ := h.setting.bstar
  have hxBs : x ∈ Bs := h.coords.x_mem
  have hBN : Bs ≤ normalizer (L : Set G) := h.setting.Bs_norm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : ∀ d : Bs, d ^ 3 = 1 := fun d => Subtype.ext (by simpa using hBab.2 d d.2)
  set R : Bs →* Equiv.Perm (Fin 693) := ρ.comp (inclusion hBN) with hR
  have hkercard : Nat.card R.ker = 3 := by
    have hkereq : R.ker = (zpowers x).subgroupOf Bs := by
      ext d
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact rhoT_eq_one_iff_mem_zpowers h hρ d.2
    have hx3 : orderOf x = 3 := orderOf_eq_prime (hBab.2 x hxBs) hx1
    rw [hkereq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 hxBs)).toEquiv,
      Nat.card_zpowers, hx3]
  have hrange : Nat.card R.range = 243 := by
    have h1 := card_ker_mul_card_range R
    have h729 : (3 : ℕ) ^ 6 = 729 := by norm_num
    rw [hkercard, h.setting.Bs_card, h729] at h1
    omega
  let Ê : Subgroup SU0 := R.range.comap piSU
  have hÊmem : ∀ a : SU0, a ∈ Ê ↔ ∃ d : Bs, R d = piSU a := fun a => by
    simp only [Ê, Subgroup.mem_comap, MonoidHom.mem_range]
  have hcomm : ∀ a ∈ Ê, ∀ a' ∈ Ê, a * a' = a' * a := fun a ha a' ha' => by
    obtain ⟨d, hd⟩ := (hÊmem a).1 ha
    obtain ⟨d', hd'⟩ := (hÊmem a').1 ha'
    exact rhoT_lift_commute h hρ (K := Bs) le_rfl (fun b hb _ => hb) hall
      (b := d.1) (b' := d'.1) d.2 d'.2 hd.symm hd'.symm
  have hcube : ∀ a ∈ Ê, a ^ 3 = 1 := fun a ha => by
    obtain ⟨d, hd⟩ := (hÊmem a).1 ha
    refine rhoTInner_pow_three_of_piSU_pow ?_
    rw [← hd, ← map_pow, hB3 d, map_one]
  let E : Subgroup (GL (Fin 6) F4) := Ê.map SU0.subtype
  have hEle : E ≤ SU0 := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact congrArg Subtype.val (hcomm a ha a' ha')
  have hE3 : ∀ u ∈ E, u ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hcube a ha)
  obtain ⟨y, -, hy⟩ := exists_conj_le_torusSU hEle hEcomm hE3
  have hup : Nat.card Ê ≤ 3 ^ 5 := by
    have hinj : Function.Injective (MulAut.conj y⁻¹).toMonoidHom :=
      fun u v huv => (MulAut.conj y⁻¹).injective huv
    have h1 : Nat.card (E.map (MulAut.conj y⁻¹).toMonoidHom) = Nat.card Ê := by
      rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective
        Subtype.val_injective]
    have h2 := Subgroup.card_le_of_le hy
    have h3 : Nat.card (torusSU 3 6 F4) ≤ 3 ^ 5 := card_torusSU_le (by norm_num) 5
    omega
  have hlow : 3 * 243 ≤ Nat.card Ê := by
    let f : Ê →* Equiv.Perm (Fin 693) := piSU.comp Ê.subtype
    have h1 := card_ker_mul_card_range f
    have h2 : 243 ≤ Nat.card f.range := by
      rw [← hrange]
      refine Subgroup.card_le_of_le fun t ht => ?_
      obtain ⟨d, rfl⟩ := ht
      have hr : R d ∈ piSU.range := by
        rw [range_piSU]
        exact hall d.1 d.2
      obtain ⟨a, ha⟩ := hr
      exact ⟨⟨a, (hÊmem a).2 ⟨d, ha.symm⟩⟩, ha⟩
    have hZÊ : center SU0 ≤ Ê := fun z hz =>
      (hÊmem z).2 ⟨1, by rw [map_one]; exact (MonoidHom.mem_ker.1 (center_le_ker hz)).symm⟩
    have h3 : 3 ≤ Nat.card f.ker := by
      have h4 : (center SU0).subgroupOf Ê ≤ f.ker := fun z hz =>
        MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 (center_le_ker (Subgroup.mem_subgroupOf.1 hz)))
      calc 3 ≤ Nat.card (center SU0) := three_le_card_center
        _ = Nat.card ((center SU0).subgroupOf Ê) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZÊ).toEquiv).symm
        _ ≤ Nat.card f.ker := Subgroup.card_le_of_le h4
    calc 3 * 243 ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul h3 h2
      _ = Nat.card Ê := h1
  omega

end CFSG.GGQ2Prime
