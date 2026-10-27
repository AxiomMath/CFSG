module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoT
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3600
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer

private theorem rhoTKer_comm_of_central {G : Type} [Group G] {L : Subgroup G} {b u v cu cv : G}
    (hu : u ∈ L) (hv : v ∈ L) (hcu : cu ∈ L) (hcv : cv ∈ L)
    (hbu : b * u * b⁻¹ = u * cu) (hbv : b * v * b⁻¹ = v * cv)
    (hcu' : ∀ m ∈ L, m * cu = cu * m) (hcv' : ∀ m ∈ L, m * cv = cv * m) :
    b * (u * v * u⁻¹ * v⁻¹) * b⁻¹ = u * v * u⁻¹ * v⁻¹ := by
  have hcuv : cu * v = v * cu := (hcu' v hv).symm
  have hcvu : cv * u = u * cv := (hcv' u hu).symm
  have hcc : cu * cv = cv * cu := hcv' cu hcu
  have R1 : (u * cu) * (v * cv) = (u * v) * (cu * cv) := by
    calc (u * cu) * (v * cv) = u * (cu * v) * cv := by group
      _ = u * (v * cu) * cv := by rw [hcuv]
      _ = (u * v) * (cu * cv) := by group
  have R2 : (v * cv) * (u * cu) = (v * u) * (cu * cv) := by
    calc (v * cv) * (u * cu) = v * (cv * u) * cu := by group
      _ = v * (u * cv) * cu := by rw [hcvu]
      _ = (v * u) * (cv * cu) := by group
      _ = (v * u) * (cu * cv) := by rw [hcc]
  calc b * (u * v * u⁻¹ * v⁻¹) * b⁻¹
      = (b * u * b⁻¹) * (b * v * b⁻¹) * (b * u * b⁻¹)⁻¹ * (b * v * b⁻¹)⁻¹ := by group
    _ = (u * cu) * (v * cv) * (u * cu)⁻¹ * (v * cv)⁻¹ := by rw [hbu, hbv]
    _ = ((u * cu) * (v * cv)) * ((v * cv) * (u * cu))⁻¹ := by group
    _ = ((u * v) * (cu * cv)) * ((v * u) * (cu * cv))⁻¹ := by rw [R1, R2]
    _ = u * v * u⁻¹ * v⁻¹ := by group

private theorem rhoTKer_conj_apply {G : Type} [Group G]
    {L : Subgroup G} {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {b : G}
    (hbN : b ∈ normalizer (L : Set G)) (l : L) (hl : b * (l : G) * b⁻¹ ∈ L) :
    ρ ⟨b, hbN⟩ * (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) * (ρ ⟨b, hbN⟩)⁻¹ =
      (e (QuotientGroup.mk (⟨b * (l : G) * b⁻¹, hl⟩ : L)) : Equiv.Perm (Fin 693)) :=
  hρ.conj ⟨b, hbN⟩ l hl

private theorem rhoTKer_cent_of_one {G : Type} [Group G]
    {L : Subgroup G} {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {b : G}
    (hbN : b ∈ normalizer (L : Set G)) (hone : ρ ⟨b, hbN⟩ = 1)
    (hperf : commutator L = ⊤) : b ∈ centralizer (L : Set G) := by
  have hbL : ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.1 hbN l).1 hl
  have hcen : ∀ l ∈ L, ∀ m ∈ L,
      m * ((l : G)⁻¹ * (b * l * b⁻¹)) = ((l : G)⁻¹ * (b * l * b⁻¹)) * m := by
    intro l hl m hm
    have hc := rhoTKer_conj_apply hρ hbN ⟨l, hl⟩ (hbL l hl)
    rw [hone, one_mul, inv_one, mul_one] at hc
    have hq := QuotientGroup.eq.1 (e.injective (Subtype.ext hc))
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hq ⟨m, hm⟩)
  have hK : (⊤ : Subgroup L) ≤ (centralizer ({b} : Set G)).subgroupOf L := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 ?_
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcu : (x : G)⁻¹ * (b * x * b⁻¹) ∈ L := L.mul_mem (L.inv_mem x.2) (hbL _ x.2)
    have hcv : (y : G)⁻¹ * (b * y * b⁻¹) ∈ L := L.mul_mem (L.inv_mem y.2) (hbL _ y.2)
    have hbu : b * (x : G) * b⁻¹ = (x : G) * ((x : G)⁻¹ * (b * x * b⁻¹)) := by group
    have hbv : b * (y : G) * b⁻¹ = (y : G) * ((y : G)⁻¹ * (b * y * b⁻¹)) := by group
    exact mul_inv_eq_iff_eq_mul.1
      (rhoTKer_comm_of_central x.2 y.2 hcu hcv hbu hbv (hcen _ x.2) (hcen _ y.2))
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hgK : (⟨g, hg⟩ : L) ∈ (centralizer ({b} : Set G)).subgroupOf L := hK (Subgroup.mem_top _)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hgK
  exact (hgK b (Set.mem_singleton b)).symm

private theorem rhoTKer_one_of_cent
    {G : Type} [Group G] {L : Subgroup G} {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {b : G}
    (hbN : b ∈ normalizer (L : Set G)) (hbC : b ∈ centralizer (L : Set G)) :
    ρ ⟨b, hbN⟩ = 1 := by
  have hcent : ρ ⟨b, hbN⟩ ∈ centralizer (T46 : Set (Equiv.Perm (Fin 693))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨q, hq⟩ := e.surjective ⟨t, ht⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hlb : (l : G) * b = b * (l : G) := Subgroup.mem_centralizer_iff.1 hbC (l : G) l.2
    have hcomm : b * (l : G) * b⁻¹ = (l : G) := by rw [← hlb]; group
    have hl : b * (l : G) * b⁻¹ ∈ L := by rw [hcomm]; exact l.2
    have hc := rhoTKer_conj_apply hρ hbN l hl
    have hl_eq : (⟨b * (l : G) * b⁻¹, hl⟩ : L) = l := Subtype.ext hcomm
    rw [hl_eq] at hc
    have ht' : (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) = t := congrArg Subtype.val hq
    rw [ht'] at hc
    exact (mul_inv_eq_iff_eq_mul.1 hc).symm
  have hbot : ρ ⟨b, hbN⟩ ∈ (⊥ : Subgroup (Equiv.Perm (Fin 693))) := by
    rw [← CFSG.EvenSmallLie.UnitarySix.YamadaHAut.centralizer_T46]
    exact hcent
  exact Subgroup.mem_bot.1 hbot

theorem rhoT_eq_one_iff_mem_zpowers
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {b : G}
    (hb : b ∈ Bs) : ρ ⟨b, h.setting.Bs_norm hb⟩ = 1 ↔ b ∈ zpowers x := by
  obtain ⟨-, hxB, hx1, hLc, hcyc, hperf, -, -⟩ := ggThmIHyp_unpack h.setting.hyp
  obtain ⟨hBB, hBab, -, -⟩ := h.setting.bstar
  have hBs3 : ∀ g ∈ Bs, g ^ 3 = 1 := hBab.2
  have hxBs : x ∈ Bs := hBB hxB
  have hLx : L ≤ centralizer ({x} : Set G) := hLc.1
  have hxC : x ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hLx hk) x (Set.mem_singleton x)).symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hBs3 x hxBs) hx1
  constructor
  · intro hone
    have hbC : b ∈ centralizer (L : Set G) := rhoTKer_cent_of_one hρ _ hone hperf
    have hPgrp : IsPGroup 3 ↥(Bs ⊓ centralizer (L : Set G)) :=
      fun g => ⟨1, Subtype.ext (by simpa using hBs3 g.1 g.2.1)⟩
    have hPcyc : IsCyclic ↥(Bs ⊓ centralizer (L : Set G)) :=
      hcyc (Bs ⊓ centralizer (L : Set G)) inf_le_right hPgrp
    have hexp : Monoid.exponent ↥(Bs ⊓ centralizer (L : Set G)) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hBs3 g.1 g.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    have hcard : Nat.card ↥(Bs ⊓ centralizer (L : Set G)) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hexp
    have hzle : zpowers x ≤ Bs ⊓ centralizer (L : Set G) :=
      zpowers_le.2 (Subgroup.mem_inf.2 ⟨hxBs, hxC⟩)
    have hzcard : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
    have heq : zpowers x = Bs ⊓ centralizer (L : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard]; exact hcard)
    rw [heq]
    exact Subgroup.mem_inf.2 ⟨hb, hbC⟩
  · intro hbz
    exact rhoTKer_one_of_cent hρ _ (zpowers_le.2 hxC hbz)

end CFSG.GGQ2Prime
