module

public import CFSG.Sporadic.Recognition.YCoverDouble

public section

namespace CFSG.Sporadic.Recognition.YCover

open Subgroup CFSG.Monster.Schur
open scoped commutatorElement

theorem exists_section {E G Q : Type} [Group E] [Group G] [Group Q] (π : E →* G)
    (hπ : Function.Surjective π) (hk : Nat.card π.ker = 2) (ι : Q →* G)
    (hperf : Group.IsPerfect Q) (hnd : NoPerfectDoubleCover Q) :
    ∃ s : Q →* E, ∀ q, π (s q) = ι q := by
  let P : Subgroup (Q × E) :=
    MonoidHom.eqLocus (ι.comp (MonoidHom.fst Q E)) (π.comp (MonoidHom.snd Q E))
  have hmemP : ∀ x : Q × E, x ∈ P ↔ ι x.1 = π x.2 := fun x => Iff.rfl
  let p : P →* Q := (MonoidHom.fst Q E).comp P.subtype
  have hps : Function.Surjective p := by
    intro q
    obtain ⟨e, he⟩ := hπ (ι q)
    exact ⟨⟨(q, e), (hmemP _).2 he.symm⟩, rfl⟩
  have hker : ∀ x : P, x ∈ p.ker ↔ (x : Q × E).1 = 1 := fun x => Iff.rfl
  have hker_mem : ∀ x : P, x ∈ p.ker → π (x : Q × E).2 = 1 := by
    intro x hx
    have h1 := (hmemP _).1 x.2
    rw [(hker x).1 hx, map_one] at h1
    exact h1.symm
  have hcentral : ∀ x : P, x ∈ p.ker → ∀ y : P, y * x = x * y := by
    intro x hx y
    have hxc : (x : Q × E).2 ∈ center E :=
      mem_center_of_mem_ker π hk (MonoidHom.mem_ker.2 (hker_mem x hx))
    apply Subtype.ext
    have h1 : (x : Q × E).1 = 1 := (hker x).1 hx
    refine Prod.ext ?_ ?_
    · show (y : Q × E).1 * (x : Q × E).1 = (x : Q × E).1 * (y : Q × E).1
      rw [h1, mul_one, one_mul]
    · show (y : Q × E).2 * (x : Q × E).2 = (x : Q × E).2 * (y : Q × E).2
      exact mem_center_iff.1 hxc _
  have hcard_ker : Nat.card p.ker = 2 := by
    rw [← hk]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Q × E).2, MonoidHom.mem_ker.2 (hker_mem x.1 x.2)⟩
        invFun := fun e => ⟨⟨(1, e.1), (hmemP _).2 (by
          rw [map_one]; exact (MonoidHom.mem_ker.1 e.2).symm)⟩, rfl⟩
        left_inv := fun x => by
          apply Subtype.ext; apply Subtype.ext
          exact Prod.ext ((hker x.1).1 x.2).symm rfl
        right_inv := fun e => rfl }
  let D : Subgroup P := commutator P
  have htop : (⊤ : Subgroup P).map p = ⊤ := by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.2 hps
  have hDmap : D.map p = ⊤ := by
    have h1 : D.map p = commutator Q := by
      show (commutator P).map p = _
      rw [_root_.commutator_def, Subgroup.map_commutator, htop, ← _root_.commutator_def]
    rw [h1]; exact Group.isPerfect_def.1 hperf
  have hsup : ∀ x : P, ∃ d ∈ D, d⁻¹ * x ∈ p.ker := by
    intro x
    obtain ⟨d, hd, hdx⟩ := (Subgroup.mem_map.1 (hDmap ▸ (Subgroup.mem_top (p x))))
    refine ⟨d, hd, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)
    · show (commutator P) ≤ ⁅D, D⁆
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨a', ha', hka⟩ := hsup a
      obtain ⟨b', hb', hkb⟩ := hsup b
      have ea : a = a' * (a'⁻¹ * a) := by group
      have eb : b = b' * (b'⁻¹ * b) := by group
      have c1 : ∀ g : P, g * (a'⁻¹ * a) = (a'⁻¹ * a) * g := fun g => hcentral _ hka g
      have c2 : ∀ g : P, g * (b'⁻¹ * b) = (b'⁻¹ * b) * g := fun g => hcentral _ hkb g
      rw [ea, eb, (commutatorElement_mul_central c1).1, (commutatorElement_mul_central c2).2]
      exact Subgroup.commutator_mem_commutator ha' hb'
  have hDperf' : Group.IsPerfect ↥D := by
    rw [Group.isPerfect_def]
    refine Subgroup.map_injective D.subtype_injective ?_
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    simpa using hDperf
  let pD : D →* Q := p.comp D.subtype
  have hpDs : Function.Surjective pD := by
    intro q
    obtain ⟨x, hx, hxq⟩ := (Subgroup.mem_map.1 (hDmap ▸ (Subgroup.mem_top q)))
    exact ⟨⟨x, hx⟩, hxq⟩
  have hker1 : Nat.card pD.ker = 1 := by
    have hdvd : Nat.card pD.ker ∣ 2 := by
      rw [← hcard_ker]
      have hle : pD.ker.map D.subtype ≤ p.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have h1 : Nat.card (pD.ker.map D.subtype) ∣ Nat.card p.ker := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective D.subtype_injective] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exact absurd h (hnd ↥D pD hpDs hDperf')
  have hinj : Function.Injective pD := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hker1
  let e : D ≃* Q := MulEquiv.ofBijective pD ⟨hinj, hpDs⟩
  let s : Q →* E := ((MonoidHom.snd Q E).comp (P.subtype.comp D.subtype)).comp e.symm.toMonoidHom
  refine ⟨s, fun q => ?_⟩
  have hq : pD (e.symm q) = q := e.apply_symm_apply q
  have h1 := (hmemP (e.symm q : P)).1 (e.symm q : P).2
  have h2 : ((e.symm q : D) : P).1.1 = q := hq
  show π ((((e.symm q : D) : P) : Q × E).2) = ι q
  rw [← h1, h2]

end CFSG.Sporadic.Recognition.YCover
