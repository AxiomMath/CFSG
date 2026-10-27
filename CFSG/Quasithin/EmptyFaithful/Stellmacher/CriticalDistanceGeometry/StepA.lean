module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.CritPairs

public section

namespace CFSG.Quasithin
open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace F53
open Equiv
open scoped Pointwise

theorem D0fin_center : ∀ y ∈ D0fin, (∀ w ∈ D0fin, w * y = y * w) → Perm.sign y = 1 := by
  decide +kernel

theorem sign_eq_one_of_central_card_eight (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8)
    (z : Perm (Fin 5)) (hz : z ∈ P) (hc : ∀ y ∈ P, y * z = z * y) :
    z ∈ alternatingGroup (Fin 5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, -⟩ := sylow_of_card_eight D0 D0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) (hP2.toSylow hPs)
  have hPeq : ∀ x, x ∈ P ↔ ∃ y ∈ D0, g * y * g⁻¹ = x := by
    intro x
    have h1 : P = MulAut.conj g • D0 := by
      have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply]
  obtain ⟨y, hy, rfl⟩ := (hPeq z).mp hz
  have hy' : y ∈ D0fin := hy
  have := D0fin_center y hy' (fun w hw => by
    have h1 := hc (g * w * g⁻¹) ((hPeq _).mpr ⟨w, hw, rfl⟩)
    have h2 : g * (w * y) * g⁻¹ = g * (y * w) * g⁻¹ := by
      calc g * (w * y) * g⁻¹ = (g * w * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * w * g⁻¹) := h1
        _ = g * (y * w) * g⁻¹ := by group
    simpa using h2)
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [Perm.sign_mul, Perm.sign_inv, this]


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_subgroupOf_eq {A N : Subgroup G} {n : ℕ} (ψ : ↥A →* Perm (Fin n))
    (hker : ∀ x : ↥A, ψ x = 1 ↔ (x : G) ∈ N) {K : Subgroup G} (hK : K ≤ A) :
    Nat.card ((K.subgroupOf A).map ψ) = N.relIndex K := by
  have h1 : ψ.ker = N.comap A.subtype := by
    ext x; exact (MonoidHom.mem_ker.trans (hker x))
  rw [← Subgroup.relIndex_ker, h1, Subgroup.relIndex_comap, Subgroup.map_subgroupOf_eq_of_le hK]

end F53

namespace F53.Stellmacher

open CosetGeom Equiv

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss113aAt (H M : Subgroup G) : Prop :=
  ∀ δ δ' : Geo H M, IsCritPair₁ δ δ' → ⁅Zv δ, Zv δ'⁆ ≠ ⊥ →
    (Zv δ ⊓ Qv δ').relIndex (Zv δ) = (Zv δ' ⊓ Qv δ).relIndex (Zv δ')

@[expose] def NoA5Transvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V : Subgroup G) (ψ : ↥X →* Equiv.Perm (Fin 5)),
    Function.Surjective ψ → (∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 X) →
    V ≤ pCoreOf 2 X → X ≤ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 V →
    X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X →
    ∀ (s : G) (hs : s ∈ X), ψ ⟨s, hs⟩ ≠ 1 → ψ ⟨s, hs⟩ ^ 2 = 1 → ψ ⟨s, hs⟩ ∈ alternatingGroup (Fin 5) →
      (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V ≠ 2

variable {H M S : Subgroup G}

theorem stepA_core (hA : F53Amalgam H M S) (h113a : Hss113aAt H M) (hM6 : NoA5Transvection)
    {α β : Geo H M} (hadj : (graph (H ⊔ M) H M).Adj α β) (hvα : vtype α = true)
    (hnle : ¬ Zv α ≤ Qv β) (hd : dist α β = bMin H M) (hcomm : ⁅Zv α, Zv β⁆ ≠ ⊥)
    (hZβα : Zv β ≤ stab α) (hbα : bAt α = bMin H M) (hbβ : bAt β = bMin H M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvβ : vtype β = false := by
    have := vtype_ne_of_adj hadj
    revert this; cases hvβ : vtype β <;> simp [hvα]
  have hαβ : β ∈ nbrs α := hadj
  have hβα : α ∈ nbrs β := hadj.symm
  have hZαβ : Zv α ≤ stab β := (Zv_le_Qv hA α).trans (Qv_le_stab_of_mem_nbrs hA hαβ)
  have hZαα : Zv α ≤ stab α := (Zv_le_Qv hA α).trans (pCoreOf_le 2 _)
  have h113 := h113a α β ⟨hnle, hd⟩ hcomm
  obtain ⟨ψα, hsα, hkα⟩ := exists_quotHom_true hA hvα
  have hZβ2 : IsPGroup 2 (Zv β) := (pCoreOf_isPGroup 2 (stab β)).to_le (Zv_le_Qv hA β)
  have hcardβ : Nat.card (((Zv β).subgroupOf (stab α)).map ψα) = (Zv β ⊓ Qv α).relIndex (Zv β) := by
    rw [card_map_subgroupOf_eq ψα hkα hZβα, Subgroup.inf_relIndex_left]
  have ha'le : (Zv β ⊓ Qv α).relIndex (Zv β) ≤ 2 := by
    rw [← hcardβ]
    exact perm3_card_le_two_of_isPGroup _ (isPGroup_map_subgroupOf ψα hZβ2)
  have ha'pos : 0 < (Zv β ⊓ Qv α).relIndex (Zv β) := by
    rw [← hcardβ]; exact Nat.card_pos
  have ha1 : (Zv α ⊓ Qv β).relIndex (Zv α) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro h; exact hnle (h.trans inf_le_right)
  have ha2 : (Zv β ⊓ Qv α).relIndex (Zv β) = 2 := by omega
  obtain ⟨n, ψβ, hn, hsurjβ, hkβ⟩ := exists_quotHom hA β
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
  swap
  · simp [hvβ] at hv
  have hT : (Qv β).relIndex (stab β ⊓ stab α) = 8 := relIndex_Qv_inf_false hA hβα hvβ
  set Zb : Subgroup (Perm (Fin 5)) := ((Zv α).subgroupOf (stab β)).map ψβ with hZb
  set Pb : Subgroup (Perm (Fin 5)) := ((stab β ⊓ stab α).subgroupOf (stab β)).map ψβ with hPb
  have hZbcard : Nat.card Zb = 2 := by
    rw [hZb, card_map_subgroupOf_eq ψβ hkβ hZαβ, ← Subgroup.inf_relIndex_left, h113, ha2]
  have hPbcard : Nat.card Pb = 8 := by
    rw [hPb, card_map_subgroupOf_eq ψβ hkβ inf_le_left, hT]
  have hZbP : Zb ≤ Pb := by
    refine Subgroup.map_mono fun x hx => ?_
    exact ⟨x.2, hZαα hx⟩
  obtain ⟨z, hzmem, hz1, huniq⟩ : ∃ z ∈ Zb, z ≠ 1 ∧ ∀ y ∈ Zb, y ≠ 1 → y = z := by
    obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : Zb)).mp hZbcard
    refine ⟨z, z.2, fun h => hz (Subtype.ext h), fun y hy hy1 => ?_⟩
    have := huniq ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  obtain ⟨⟨s, hsβ⟩, hsZ, hψs⟩ := hzmem
  have hsZ' : s ∈ Zv α := hsZ
  have hcentral : ∀ p ∈ Pb, p * z = z * p := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ stab β ⊓ stab α := hu
    have hmem : (u * ⟨s, hsβ⟩ * u⁻¹ : ↥(stab β)) ∈ (Zv α).subgroupOf (stab β) := by
      show (u : G) * s * (u : G)⁻¹ ∈ Zv α
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hu'.2) s).mp hsZ'
    have h1 : ψβ u * z * (ψβ u)⁻¹ ∈ Zb := ⟨_, hmem, by simp [hψs]⟩
    have h2 : ψβ u * z * (ψβ u)⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = (ψβ u)⁻¹ * (ψβ u * z * (ψβ u)⁻¹) * ψβ u := by group
        _ = 1 := by rw [h]; simp
    have := huniq _ h1 h2
    calc ψβ u * z = (ψβ u * z * (ψβ u)⁻¹) * ψβ u := by group
      _ = z * ψβ u := by rw [this]
  have hzalt : z ∈ alternatingGroup (Fin 5) :=
    sign_eq_one_of_central_card_eight Pb hPbcard z (hZbP ⟨_, hsZ, hψs⟩) (fun y hy => hcentral y hy)
  have hs2 : (s : G) ^ 2 = 1 := (isElemAbelian_Zv hA α).2 s hsZ'
  have hz2 : z ^ 2 = 1 := by
    rw [← hψs, ← map_pow]
    have : (⟨s, hsβ⟩ : ↥(stab β)) ^ 2 = 1 := Subtype.ext (by simpa using hs2)
    rw [this, map_one]
  have hcα : stab α ⊓ Subgroup.centralizer (Zv α : Set G) = Qv α :=
    centralizer_Zv_eq_Qv_of_bAt hA hbα
  have hcβ : stab β ⊓ Subgroup.centralizer (Zv β : Set G) = pCoreOf 2 (stab β) :=
    centralizer_Zv_eq_Qv_of_bAt hA hbβ
  have hs1 : ψβ ⟨s, hsβ⟩ ≠ 1 := by rw [hψs]; exact hz1
  have hceq : Zv β ⊓ Subgroup.centralizer ({s} : Set G) = Zv β ⊓ Qv α := by
    ext x
    constructor
    · rintro ⟨hxZ, hxs⟩
      refine ⟨hxZ, ?_⟩
      rw [← hcα]
      refine ⟨hZβα hxZ, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      have hxQ : ∀ q ∈ Qv β, q * x = x * q :=
        Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hxZ).2
      have hxs' : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxs s rfl
      have hwβ : w ∈ stab β := hZαβ hw
      have hwZ : ψβ ⟨w, hwβ⟩ ∈ Zb := ⟨_, hw, rfl⟩
      by_cases hw1 : ψβ ⟨w, hwβ⟩ = 1
      · exact hxQ w ((hkβ _).mp hw1)
      · have heq : ψβ ⟨w, hwβ⟩ = ψβ ⟨s, hsβ⟩ := by rw [hψs]; exact huniq _ hwZ hw1
        have hq : s⁻¹ * w ∈ Qv β := by
          rw [← hkβ ⟨s⁻¹ * w, (stab β).mul_mem ((stab β).inv_mem hsβ) hwβ⟩]
          have : (⟨s⁻¹ * w, (stab β).mul_mem ((stab β).inv_mem hsβ) hwβ⟩ : ↥(stab β)) =
              ⟨s, hsβ⟩⁻¹ * ⟨w, hwβ⟩ := rfl
          rw [this, map_mul, map_inv, heq, inv_mul_cancel]
        have hq' := hxQ _ hq
        calc w * x = s * ((s⁻¹ * w) * x) := by group
          _ = s * (x * (s⁻¹ * w)) := by rw [hq']
          _ = (s * x) * (s⁻¹ * w) := by group
          _ = (x * s) * (s⁻¹ * w) := by rw [hxs']
          _ = x * w := by group
    · rintro ⟨hxZ, hxQ⟩
      refine ⟨hxZ, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hsZ').2 x hxQ).symm
  refine hM6 G (stab β) (Zv β) ψβ hsurjβ hkβ (Zv_le_Qv hA β) (stab_le_normalizer_Zv hA β)
    (isElemAbelian_Zv hA β) hcβ s hsβ hs1 (by rw [hψs]; exact hz2) (by rw [hψs]; exact hzalt) ?_
  rw [hceq, ha2]

theorem one_lt_bMin_of_comm_ne (hA : F53Amalgam H M S) (h113a : Hss113aAt H M)
    (hM6 : NoA5Transvection) {α β α' : Geo H M} (hc : IsCritData α β α')
    (hα : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) : 1 < bMin H M := by
  by_contra hb
  have hb1 : bMin H M = 1 := by have := bMin_pos hA; omega
  have hβ : β = α' := (CosetGeom.dist_eq_zero_iff hA.amalgam.gen).mp (by
    have := hc.dist_eq'; omega)
  subst hβ
  obtain ⟨hbα, hbβ⟩ := crit_bAt_eq hA ⟨hc.not_le, hc.dist_eq⟩ hcomm
  exact stepA_core hA h113a hM6 hc.adj hα hc.not_le hc.dist_eq hcomm
    (Zv_le_stab_of_comm_ne hA hc hcomm).2 hbα hbβ

end F53.Stellmacher

end CFSG.Quasithin
