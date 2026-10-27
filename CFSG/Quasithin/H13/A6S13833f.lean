module

public import CFSG.Quasithin.H13.A6S13833e
public import CFSG.Quasithin.H13.A6S13721a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

@[expose] def onesEv : ↥(evenWeight 6) := ⟨onesV, mem_ev_of_sum_zero sum_ones⟩

theorem permWeight_onesEv (σ : Perm (Fin 6)) : permWeight 6 σ onesEv = onesEv := rfl

theorem mem_constWeight_iff (x : ↥(evenWeight 6)) :
    x ∈ constWeight 6 ↔ x = 0 ∨ x = onesEv := by
  constructor
  · intro hx
    rcases (constWeight_iff (x : Fin 6 → ZMod 2)).1 hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact (constWeight 6).zero_mem
    · exact fun i j => rfl

theorem permWeight_eq_of_mem_constWeight (σ : Perm (Fin 6)) {x : ↥(evenWeight 6)}
    (hx : x ∈ constWeight 6) : permWeight 6 σ x = x := by
  rcases (mem_constWeight_iff x).1 hx with rfl | rfl
  · rfl
  · exact permWeight_onesEv σ

theorem e0_moved_of_cube : ∀ σ ∈ cList, σ ^ 3 = 1 → σ ≠ 1 → ∃ e ∈ e0List, σ * e * σ⁻¹ ≠ e := by
  decide +kernel

theorem card_D_tri012 : (Finset.univ.filter fun σ : Perm (Fin 6) => InD6 σ ∧
    InD6 (c012 * σ * c012⁻¹) ∧ InD6 (c012⁻¹ * σ * c012)).card ≤ 8 := by
  decide +kernel
namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] noncomputable def U1c (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)) :
    Subgroup G :=
  ((AddSubgroup.toSubgroup (constWeight 6)).comap β).map (conjClosure S.V3 S.G1).subtype

include S

section U1

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)} (hβs : Function.Surjective β)
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))

theorem mem_U1c {u : G} : u ∈ S.U1c β ↔ ∃ hu : u ∈ conjClosure S.V3 S.G1,
    Multiplicative.toAdd (β ⟨u, hu⟩) ∈ constWeight 6 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

theorem U1c_le_UH : S.U1c β ≤ conjClosure S.V3 S.G1 := Subgroup.map_subtype_le _

include hβk in
theorem V1_le_U1c : fsuV1 T V ≤ S.U1c β := by
  intro u hu
  have hu' : u ∈ conjClosure S.V3 S.G1 := S.V3_le_UH (S.V1_le_V3 hu)
  refine (S.mem_U1c).2 ⟨hu', ?_⟩
  rw [(hβk ⟨u, hu'⟩).2 hu, toAdd_one]
  exact (constWeight 6).zero_mem

include hβe in
theorem comm_mem_V1_of_U1c (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V) {h u : G}
    (hh : h ∈ S.G1) (hu : u ∈ S.U1c β) : h * u * h⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  obtain ⟨huU, hc⟩ := (S.mem_U1c).1 hu
  have hhu : h * u * h⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) u).mp huU
  have he := hβe ⟨h, hh⟩ ⟨u, huU⟩ ⟨_, hhu⟩ rfl
  rw [permWeight_eq_of_mem_constWeight _ hc] at he
  have hmem : h * u * h⁻¹ * u⁻¹ ∈ conjClosure S.V3 S.G1 :=
    (conjClosure S.V3 S.G1).mul_mem hhu ((conjClosure S.V3 S.G1).inv_mem huU)
  refine (hβk ⟨_, hmem⟩).1 ?_
  have e : (⟨h * u * h⁻¹ * u⁻¹, hmem⟩ : ↥(conjClosure S.V3 S.G1)) =
      ⟨_, hhu⟩ * (⟨u, huU⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, he, add_neg_cancel, toAdd_one]

include hβe in
theorem G1_le_normalizer_U1c (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V) :
    S.G1 ≤ Subgroup.normalizer (S.U1c β : Set G) := by
  intro h hh
  refine mem_normalizer_of_conj_mem_fin fun u hu => ?_
  have hc := S.comm_mem_V1_of_U1c hβe hβk hh hu
  have e : h * u * h⁻¹ = (h * u * h⁻¹ * u⁻¹) * u := by group
  rw [e]
  exact (S.U1c β).mul_mem (S.V1_le_U1c hβk hc) hu

include hβs hβk in
theorem card_U1c : Nat.card (S.U1c β) = 4 := by
  set A := (AddSubgroup.toSubgroup (constWeight 6)).comap β with hA
  have h1 : Nat.card (S.U1c β) = Nat.card A :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A _
      (conjClosure S.V3 S.G1).subtype_injective).toEquiv).symm
  rw [h1]
  let φ : ↥A →* Multiplicative ↥(evenWeight 6) := β.comp A.subtype
  have hker : φ.ker = β.ker.subgroupOf A := by
    ext a
    simp [φ, Subgroup.mem_subgroupOf]
  have hrange : φ.range = AddSubgroup.toSubgroup (constWeight 6) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hy
      obtain ⟨u, hu⟩ := hβs y
      exact ⟨⟨u, by rw [hA, Subgroup.mem_comap, hu]; exact hy⟩, hu⟩
  have hk : Nat.card β.ker = 2 := by
    have e : β.ker.map (conjClosure S.V3 S.G1).subtype = fsuV1 T V := by
      ext u
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hβk w).1 hw
      · intro hu
        exact ⟨⟨u, S.V3_le_UH (S.V1_le_V3 hu)⟩, (hβk _).2 hu, rfl⟩
    calc Nat.card β.ker = Nat.card ↥(β.ker.map (conjClosure S.V3 S.G1).subtype) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ _
            (conjClosure S.V3 S.G1).subtype_injective).toEquiv
      _ = Nat.card ↥(fsuV1 T V) := by rw [e]
      _ = 2 := S.card_V1
  have hkA : Nat.card (β.ker.subgroupOf A) = 2 := by
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ?_).toEquiv).trans hk
    intro u hu
    show β u ∈ AddSubgroup.toSubgroup (constWeight 6)
    rw [MonoidHom.mem_ker.1 hu]
    exact Subgroup.one_mem _
  have hc2 : Nat.card ↥(AddSubgroup.toSubgroup (constWeight 6)) = 2 := by
    have e : ∀ y : Multiplicative ↥(evenWeight 6), y ∈ AddSubgroup.toSubgroup (constWeight 6) ↔
        y = 1 ∨ y = Multiplicative.ofAdd onesEv := by
      intro y
      rw [Multiplicative.mem_toSubgroup, mem_constWeight_iff]
      constructor
      · rintro (h | h)
        · left; exact Multiplicative.toAdd.injective (by rw [h, toAdd_one])
        · right; exact Multiplicative.toAdd.injective (by rw [h, toAdd_ofAdd])
      · rintro (rfl | rfl)
        · left; rfl
        · right; rfl
    have hne : (1 : Multiplicative ↥(evenWeight 6)) ≠ Multiplicative.ofAdd onesEv := by
      intro h
      have := congrArg (fun y => ((Multiplicative.toAdd y : ↥(evenWeight 6)) : Fin 6 → ZMod 2) 0) h
      simp [onesEv, onesV] at this
    rw [Nat.card_eq_two_iff' 1]
    refine ⟨⟨Multiplicative.ofAdd onesEv, (e _).2 (Or.inr rfl)⟩, fun h => hne ?_, ?_⟩
    · exact (congrArg Subtype.val h).symm
    · rintro ⟨y, hy⟩ hy1
      rcases (e y).1 hy with h | h
      · exact absurd (Subtype.ext h) hy1
      · exact Subtype.ext h
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hc2, hker, hkA] at h2
  exact h2

@[expose] noncomputable def U0c (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)) :
    Subgroup G :=
  conjClosure (S.U1c β) L

include hβk in
theorem V_le_U0c : V ≤ S.U0c β := by
  calc V = conjClosure (fsuV1 T V) L := S.conjClosure_V1_L.symm
    _ ≤ S.U0c β := conjClosure_mono (S.V1_le_U1c hβk) le_rfl

theorem U0c_le_UL : S.U0c β ≤ conjClosure (conjClosure S.V3 S.G1) L :=
  conjClosure_mono S.U1c_le_UH le_rfl

include hβe in
theorem LT_le_normalizer_U0c (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V) :
    L ⊔ T ≤ Subgroup.normalizer (S.U0c β : Set G) := by
  have hTH : T ≤ S.G1 := fun t ht => by
    have := S.T_le_NV1 ht
    rwa [S.normalizer_V1] at this
  refine sup_le (le_normalizer_conjClosure _ L) fun t ht => ?_
  have hU : conjSub t (S.U1c β) = S.U1c β :=
    F7.conjSub_eq_of_mem_normalizer (S.G1_le_normalizer_U1c hβe hβk (hTH ht))
  have hL : conjSub t L = L := F7.conjSub_eq_of_mem_normalizer (S.T_le_NL ht)
  have e : conjSub t (S.U0c β) = S.U0c β := by
    rw [U0c, conjSub_conjClosure_eq, hU, hL]
  refine F7.mem_normalizer_of_conj_le e.le ?_
  rw [← e, conjSub_conjSub_inv, e]

include hβs hβk in
theorem card_UH_cover : Nat.card ↥(conjClosure S.V3 S.G1) = 64 := by
  have hk : β.ker = (fsuV1 T V).subgroupOf (conjClosure S.V3 S.G1) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have h2 : Nat.card (↥(conjClosure S.V3 S.G1) ⧸ β.ker) = 32 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative ↥(evenWeight 6) ≃ ↥(evenWeight 6)),
      card_evenWeight6]
  have h3 : Nat.card ↥β.ker = 2 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (S.V1_le_V3.trans (le_conjClosure S.V3 S.G1))).toEquiv, S.card_V1]
  rw [h1, h2, h3]

include hβk hβe in
theorem cfix_UH_eq_U1c {c : G} (hcH : c ∈ S.G1) (hc3 : c ^ 3 = 1)
    (hfp : ∀ i, ρ ⟨c, hcH⟩ i ≠ i) : cfix c (conjClosure S.V3 S.G1) = S.U1c β := by
  have hρ3 : ρ ⟨c, hcH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcH⟩ : ↥S.G1) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  ext u
  rw [mem_cfix]
  constructor
  · rintro ⟨huU, hcu⟩
    refine (S.mem_U1c).2 ⟨huU, ?_⟩
    have hcu' : c * u * c⁻¹ = u := by rw [hcu, mul_inv_cancel_right]
    have he := hβe ⟨c, hcH⟩ ⟨u, huU⟩ ⟨u, huU⟩ hcu'.symm
    set x := Multiplicative.toAdd (β ⟨u, huU⟩) with hx
    have hfix : vp (ρ ⟨c, hcH⟩) (x : Fin 6 → ZMod 2) = (x : Fin 6 → ZMod 2) := by
      have := congrArg Subtype.val he
      exact this.symm
    rcases fpf3_fix _ hρ3 hfp (x : Fin 6 → ZMod 2) (sum_eq_zero x) (Or.inl hfix) with h | h
    · exact (mem_constWeight_iff x).2 (Or.inl (Subtype.ext h))
    · exact (mem_constWeight_iff x).2 (Or.inr (Subtype.ext h))
  · intro hu
    obtain ⟨huU, -⟩ := (S.mem_U1c).1 hu
    refine ⟨huU, ?_⟩
    have hz := S.comm_mem_V1_of_U1c hβe hβk hcH hu
    have hzc : c * S.z = S.z * c := by
      have : c ∈ Subgroup.centralizer ({S.z} : Set G) := hcH
      exact (Subgroup.mem_centralizer_singleton_iff.mp this)
    rcases (S.mem_V1_iff).1 hz with h | h
    · calc c * u = (c * u * c⁻¹ * u⁻¹) * u * c := by group
        _ = u * c := by rw [h, one_mul]
    · exfalso
      have e1 : c * u * c⁻¹ = S.z * u := by
        calc c * u * c⁻¹ = (c * u * c⁻¹ * u⁻¹) * u := by group
          _ = S.z * u := by rw [h]
      have hz2 : S.z * S.z = 1 := by
        have := S.elemAbelian_V.2 S.z S.z_mem_V
        rwa [sq] at this
      have e2 : c ^ 3 * u * (c ^ 3)⁻¹ = S.z * u := by
        have hcz : c * S.z * c⁻¹ = S.z := by rw [hzc, mul_inv_cancel_right]
        calc c ^ 3 * u * (c ^ 3)⁻¹ = c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ := by
              simp only [pow_succ, pow_zero, one_mul]; group
          _ = c * (c * (S.z * u) * c⁻¹) * c⁻¹ := by rw [e1]
          _ = c * ((c * S.z * c⁻¹) * (c * u * c⁻¹)) * c⁻¹ := by group
          _ = c * (S.z * (S.z * u)) * c⁻¹ := by rw [hcz, e1]
          _ = c * u * c⁻¹ := by rw [show S.z * (S.z * u) = u by rw [← mul_assoc, hz2, one_mul]]
          _ = S.z * u := e1
      rw [hc3, one_mul, inv_one, mul_one] at e2
      apply S.z_ne_one
      calc S.z = S.z * u * u⁻¹ := by group
        _ = u * u⁻¹ := by rw [← e2]
        _ = 1 := mul_inv_cancel u

include hβs hβk hβe in
theorem relIndex_QH_QC_eq (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    (hUab : IsElemAbelian 2 (conjClosure S.V3 S.G1)) {c : G} (hcH : c ∈ S.G1) (hc3 : c ^ 3 = 1)
    (hfp : ∀ i, ρ ⟨c, hcH⟩ i ≠ i)
    (hZ : conjClosure S.V3 S.G1 ⊓ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) ≤ S.U1c β) :
    (cfix c (pCoreOf 2 S.G1) ⊔ (pCoreOf 2 S.G1 ⊓
      Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G))).relIndex (pCoreOf 2 S.G1) = 16 := by
  rw [nu_dual_F97 hF.toHypF91 hUab hcH hc3, S.cfix_UH_eq_U1c hβk hβe hcH hc3 hfp,
    sup_eq_left.2 hZ]
  have h := Subgroup.relIndex_mul_card (S.U1c β) (conjClosure S.V3 S.G1)
  rw [inf_eq_left.2 S.U1c_le_UH, S.card_U1c hβs hβk, S.card_UH_cover hβs hβk] at h
  omega

end U1

section Nu

theorem four_mul_nu_QH_le_nu_R {ρ' : ↥S.G1 →* Perm (Fin 6)}
    (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
    (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hL1H : S.L1 ≤ S.G1) (hTH : T ≤ S.G1) (hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ'))
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    4 * nu c (pCoreOf 2 S.G1) ≤ nu c (pCoreOf 2 (S.L1 ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set QH := pCoreOf 2 S.G1 with hQHdef
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  have hLTH : S.L1 ⊔ T ≤ S.G1 := sup_le hL1H hTH
  have hQHN : S.G1 ≤ Subgroup.normalizer (QH : Set G) := le_normalizer_pCoreOf 2 S.G1
  have hQHT : QH ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hQHR : QH ≤ R := le_pCoreOf_of_le_normalizer 2 (hQHT.trans le_sup_right)
    (hLTH.trans hQHN) (pCoreOf_isPGroup 2 _)
  have hcR : c ∈ Subgroup.normalizer (R : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hcL)
  have hcQH : c ∈ Subgroup.normalizer (QH : Set G) := hQHN (hL1H hcL)
  have hN : cfix c R ≤ Subgroup.normalizer (QH : Set G) := fun x hx =>
    hQHN (hLTH (pCoreOf_le 2 _ hx.1))
  refine four_mul_nu_le hc3 (pCoreOf_isPGroup 2 _) hQHR hcR hcQH hN ?_
  set C : ↥S.G1 := ⟨c, hL1H hcL⟩ with hC
  have hC3 : C ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hC1 : C ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hcl : ρ' C ∈ cList := (hN' C).2 (S.L1T_le_NV3 (Subgroup.mem_sup_left hcL))
  have hc3' : ρ' C ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
  have hc1' : ρ' C ≠ 1 := S.rho_ne_one_of_cube hker' hC3 hC1
  obtain ⟨e, he, hce⟩ := e0_moved_of_cube _ hcl hc3' hc1'
  obtain ⟨l, hlL, hle⟩ := S.exists_L1_E0 hN' hker' hL1H hT8 e he
  have hlE : (l : G) ∈ pCoreOf 2 (S.L1 ⊔ QH) :=
    S.mem_O2_of_E0 hN' hker' hL1H (Subgroup.mem_sup_left hlL) (by rw [hle]; exact he)
  have hER : pCoreOf 2 (S.L1 ⊔ QH) ≤ R := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (sup_le_sup_left hQHT _)) ?_
      (pCoreOf_isPGroup 2 _)
    intro y hy
    refine normalizer_le_normalizer_pCoreOf 2 _ ?_
    have hyL1 : y ∈ Subgroup.normalizer (S.L1 : Set G) :=
      (sup_le Subgroup.le_normalizer S.T_le_normalizer_L1) hy
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hyL1, hQHN (hLTH hy)⟩
  refine ⟨l, hER hlE, fun hmem => hce ?_⟩
  have h1 : ρ' (C * l * C⁻¹ * l⁻¹) = 1 := (hker' _).2 hmem
  simp only [map_mul, map_inv, hle] at h1
  calc ρ' C * e * (ρ' C)⁻¹ = (ρ' C * e * (ρ' C)⁻¹ * e⁻¹) * e := by group
    _ = e := by rw [h1, one_mul]

theorem relIndex_R_Q_le_four (hhat : ¬ IsHatA6 L) :
    (cfix (S.cL1 hhat : G) (pCoreOf 2 (S.L1 ⊔ T)) ⊔ pCoreOf 2 (L ⊔ T)).relIndex
      (pCoreOf 2 (S.L1 ⊔ T)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL1 : c ∈ S.L1 := S.cL1_mem hhat
  have hRT : R ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hQT : Q ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hL1LT : S.L1 ⊔ T ≤ L ⊔ T := sup_le_sup_right S.L1_le_L T
  have hQR : Q ≤ R := le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (hL1LT.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hcR : c ∈ Subgroup.normalizer (R : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hcL1)
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left (S.L1_le_L hcL1))
  have hN : cfix c R ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right (hRT hx.1))
  have hmul := nu_mul c hQR hN
  obtain ⟨k, hk⟩ := exists_nu_eq_four_pow hc3 (pCoreOf_isPGroup 2 _) hcR
  obtain ⟨j, hj⟩ := exists_nu_eq_four_pow hc3 (pCoreOf_isPGroup 2 _) hcQ
  set m := (cfix c R ⊔ Q).relIndex R with hm
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRT.trans S.frame.T_le
  let ρR : ↥R →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hRN)
  have hker : ρR.ker = Q.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hC : (r : G) ∈ Subgroup.centralizer (V : Set G) :=
        (S.rho_eq_one_iff (Subgroup.inclusion hRN r)).1 h
      rw [hQdef, ← S.cT]
      exact ⟨hRT r.2, hC⟩
    · intro h
      have h' : (r : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by rw [S.cT]; exact h
      exact (S.rho_eq_one_iff (Subgroup.inclusion hRN r)).2 h'.2
  have hidx : Q.relIndex R = Nat.card ρR.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hρc : S.frame.ρ (S.cL1 hhat) = c012 := S.cL1_rho hhat
  have hcinv : c⁻¹ ∈ Subgroup.normalizer (R : Set G) := Subgroup.inv_mem _ hcR
  have hmem : ∀ σ ∈ ρR.range, InD6 σ ∧ InD6 (c012 * σ * c012⁻¹) ∧ InD6 (c012⁻¹ * σ * c012) := by
    rintro _ ⟨r, rfl⟩
    have hcrc : c * r * c⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcR r).mp r.2
    have hcrc' : c⁻¹ * r * c⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcinv r).mp r.2
    rw [inv_inv] at hcrc'
    refine ⟨S.frame.T_D (Subgroup.inclusion hRN r) (hRT r.2), ?_, ?_⟩
    · have h1 := S.frame.T_D (S.cL1 hhat * Subgroup.inclusion hRN r * (S.cL1 hhat)⁻¹) (hRT hcrc)
      rw [map_mul, map_mul, map_inv, hρc] at h1
      exact h1
    · have h1 := S.frame.T_D ((S.cL1 hhat)⁻¹ * Subgroup.inclusion hRN r * S.cL1 hhat) (hRT hcrc')
      rw [map_mul, map_mul, map_inv, hρc] at h1
      exact h1
  have hle8 : Q.relIndex R ≤ 8 := by
    rw [hidx]
    refine le_trans ?_ card_D_tri012
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective
      (fun σ : ρR.range => (⟨σ.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem σ.1 σ.2⟩⟩ :
        ↥(Finset.univ.filter fun σ : Perm (Fin 6) => InD6 σ ∧ InD6 (c012 * σ * c012⁻¹) ∧
          InD6 (c012⁻¹ * σ * c012))))
      (fun a b h => Subtype.ext (by have := congrArg Subtype.val h; exact this))
  have hmQ : m ≤ Q.relIndex R := by
    have h := Subgroup.relIndex_mul_relIndex Q (cfix c R ⊔ Q) R le_sup_right
      (sup_le inf_le_left hQR)
    have hpos : Q.relIndex (cfix c R ⊔ Q) ≠ 0 := by
      show (Q.subgroupOf (cfix c R ⊔ Q)).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    rw [← h]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hpos)
  rw [hk, hj] at hmul
  have hm8 : m ≤ 8 := hmQ.trans hle8
  by_cases hkj : j ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have hm4 : m = 4 ^ d := by
      have h4 : 0 < 4 ^ j := by positivity
      have e : 4 ^ d * 4 ^ j = m * 4 ^ j := by rw [← pow_add, add_comm]; exact hmul
      exact (Nat.eq_of_mul_eq_mul_right h4 e).symm
    have hd : d ≤ 1 := by
      by_contra hd
      push Not at hd
      have h16 : 16 ≤ m := by
        rw [hm4]
        calc (16 : ℕ) = 4 ^ 2 := by norm_num
          _ ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hd
      omega
    rw [hm4]
    interval_cases d <;> norm_num
  · exfalso
    push Not at hkj
    have h1 : 4 ^ k < 4 ^ j := Nat.pow_lt_pow_right (by norm_num) hkj
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      exact absurd hmul (by positivity)
    have h2 : 4 ^ j ≤ m * 4 ^ j := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)
    rw [← hmul] at h2
    exact absurd h1 (not_lt.2 h2)

end Nu

end Setting4

end CFSG.Quasithin.H13.A6
