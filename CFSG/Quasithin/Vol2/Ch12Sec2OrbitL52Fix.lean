module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public import CFSG.Quasithin.Vol2.Ch12Sec4Pre

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open Orbit
open scoped Pointwise

theorem wedgeRep_apply_apply (a b : G5) (w : Fin 10 → ZMod 2) :
    wedgeRep a (wedgeRep b w) = wedgeRep (a * b) w := by
  rw [map_mul, Module.End.mul_apply]

theorem wedgeRep_inv_apply (g : G5) (w : Fin 10 → ZMod 2) : wedgeRep g⁻¹ (wedgeRep g w) = w := by
  rw [wedgeRep_apply_apply, inv_mul_cancel, map_one, Module.End.one_apply]

theorem wedgeRep_apply_inv (g : G5) (w : Fin 10 → ZMod 2) : wedgeRep g (wedgeRep g⁻¹ w) = w := by
  rw [wedgeRep_apply_apply, mul_inv_cancel, map_one, Module.End.one_apply]

theorem l52TenSylowFixedLine
    : L52TenSylowFixedLine := by
  intro G _ _ L V S hLV h2 hab hcard hirr ⟨ψ⟩ hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  have h2' : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using h2 v v.2)
  have hmem : ∀ l : ↥L, conjAct V (Subgroup.inclusion hLV l) ∈ autOn L V := fun l =>
    ⟨Subgroup.inclusion hLV l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  let f : ↥L →* ↥(autOn L V) :=
    ((conjAct V).comp (Subgroup.inclusion hLV)).codRestrict (autOn L V) hmem
  have hf : Function.Surjective f := by
    rintro ⟨a, n, hn, rfl⟩
    refine ⟨⟨n, Subgroup.mem_subgroupOf.1 hn⟩, Subtype.ext ?_⟩
    rfl
  have hf_apply : ∀ (l : ↥L) (v : ↥V), (((f l : ↥(autOn L V)) : MulAut ↥V) v : G) =
      (l : G) * v * (l : G)⁻¹ := fun _ _ => rfl
  have hirr' : ∀ W : Subgroup ↥V, (∀ a ∈ autOn L V, ∀ w ∈ W, (a : MulAut ↥V) w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hconj : ∀ l ∈ L, ∀ x ∈ W.map V.subtype, l * x * l⁻¹ ∈ W.map V.subtype := by
      intro l hl x hx
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨(f ⟨l, hl⟩ : MulAut ↥V) w, hW _ (f ⟨l, hl⟩).2 w hw, ?_⟩
      exact hf_apply ⟨l, hl⟩ w
    have hnorm : L ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hconj l hl x, fun hx => ?_⟩
      have := hconj l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using this
    rcases hirr.2 (W.map V.subtype) (Subgroup.map_subtype_le W) hnorm with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 h
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : G) ∈ W.map V.subtype := by
        rw [h]
        exact w.2
      obtain ⟨w', hw', hww'⟩ := hw
      rw [show w = w' from Subtype.ext hww'.symm]
      exact hw'
  obtain ⟨e, γ, -, he⟩ := exists_wedge_coords h2' hcard ψ hirr'
  set Q : Subgroup G5 := ((S.subgroupOf L).map f).map γ.toMonoidHom with hQdef
  have hSp : IsPGroup 2 ↥(S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hQp : IsPGroup 2 ↥Q := (hSp.map f).map _
  have hQi : ¬ 2 ∣ Q.index := by
    intro h
    apply hS.2.2
    refine h.trans ((Subgroup.index_map_dvd _ γ.surjective).trans ?_)
    exact Subgroup.index_map_dvd _ hf
  have hUi : ¬ 2 ∣ Ugrp.index := by
    have h := Ugrp.index_mul_card
    rw [card_Ugrp, card_G5] at h
    generalize Ugrp.index = n at h ⊢
    have h' : n * 1024 = 9999360 := by rw [← h]; norm_num
    have h9765 : n = 9765 := by omega
    subst h9765
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G5 (hQp.toSylow hQi) (isPGroup_Ugrp.toSylow hUi)
  have hgU : ∀ u : G5, u ∈ Ugrp ↔ g⁻¹ * u * g ∈ Q := by
    intro u
    have h1 : MulAut.conj g • Q = Ugrp := congrArg (fun P : Sylow 2 G5 => (P : Subgroup G5)) hg
    rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h2 : (MulAut.conj g)⁻¹ • u = g⁻¹ * u * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [h2]
  have hfixQ : ∀ v : ↥V, (∀ s ∈ S, s * (v : G) = v * s) ↔
      ∀ q ∈ Q, wedgeRep q (e v) = e v := by
    intro v
    constructor
    · intro hv q hq
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hq
      have hs' : ((s : ↥L) : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      change wedgeRep (γ (f s)) (e v) = e v
      rw [← he]
      congr 1
      apply Subtype.ext
      rw [hf_apply, hv _ hs', mul_assoc, mul_inv_cancel, mul_one]
    · intro hv s hs
      have hq : γ (f ⟨s, hS.1 hs⟩) ∈ Q := ⟨_, ⟨⟨s, hS.1 hs⟩, hs, rfl⟩, rfl⟩
      have h1 := hv _ hq
      rw [← he] at h1
      have h3 := congrArg Subtype.val (e.injective h1)
      rw [hf_apply] at h3
      change s * (v : G) * s⁻¹ = v at h3
      calc s * (v : G) = s * v * s⁻¹ * s := by group
        _ = v * s := by rw [h3]
  have hfixU : ∀ w : Fin 10 → ZMod 2, (∀ q ∈ Q, wedgeRep q (wedgeRep g⁻¹ w) = wedgeRep g⁻¹ w) ↔
      w ∈ fixU wedgeRep := by
    intro w
    rw [mem_fixU]
    constructor
    · intro hw u hu
      have hq := hw _ ((hgU u).1 hu)
      calc wedgeRep u w = wedgeRep (g * ((g⁻¹ * u * g) * g⁻¹)) w := by
            rw [show g * ((g⁻¹ * u * g) * g⁻¹) = u by group]
        _ = wedgeRep g (wedgeRep (g⁻¹ * u * g) (wedgeRep g⁻¹ w)) := by
            rw [wedgeRep_apply_apply, wedgeRep_apply_apply, mul_assoc g (g⁻¹ * u * g) g⁻¹]
        _ = w := by rw [hq, wedgeRep_apply_inv]
    · intro hw q hq
      have hu : g * q * g⁻¹ ∈ Ugrp := by
        rw [hgU]
        convert hq using 1
        group
      calc wedgeRep q (wedgeRep g⁻¹ w) = wedgeRep (g⁻¹ * (g * q * g⁻¹)) w := by
            rw [wedgeRep_apply_apply, show g⁻¹ * (g * q * g⁻¹) = q * g⁻¹ by group]
        _ = wedgeRep g⁻¹ w := by rw [← wedgeRep_apply_apply, hw _ hu]
  let Φ : (Fin 10 → ZMod 2) → G := fun w => ((e.symm (wedgeRep g⁻¹ w) : ↥V) : G)
  have hΦ : Function.Injective Φ := by
    intro w w' h
    have h1 := e.symm.injective (Subtype.ext h)
    rw [← wedgeRep_apply_inv g w, h1, wedgeRep_apply_inv]
  have himage : ((V ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) =
      Φ '' ({0, e01} : Set (Fin 10 → ZMod 2)) := by
    ext x
    constructor
    · rintro ⟨hxV, hxS⟩
      set v : ↥V := ⟨x, hxV⟩
      have hv : ∀ s ∈ S, s * (v : G) = v * s := fun s hs =>
        (Subgroup.mem_centralizer_iff.1 hxS s hs)
      refine ⟨wedgeRep g (e v), ?_, ?_⟩
      · have hmemU : wedgeRep g (e v) ∈ fixU wedgeRep := by
          rw [← hfixU]
          intro q hq
          rw [wedgeRep_inv_apply]
          exact (hfixQ v).1 hv q hq
        rcases wedge_fix hmemU with h | h
        · exact Or.inl h
        · exact Or.inr h
      · change ((e.symm (wedgeRep g⁻¹ (wedgeRep g (e v))) : ↥V) : G) = x
        rw [wedgeRep_inv_apply, Equiv.symm_apply_apply]
    · rintro ⟨w, hw, rfl⟩
      have hwU : w ∈ fixU wedgeRep := by
        rcases hw with rfl | rfl
        · exact Submodule.zero_mem _
        · exact e01_mem_fixU
      refine ⟨(e.symm (wedgeRep g⁻¹ w)).2, Subgroup.mem_centralizer_iff.2 ?_⟩
      have h1 := (hfixU w).2 hwU
      rw [← Equiv.apply_symm_apply e (wedgeRep g⁻¹ w)] at h1
      exact fun s hs => (hfixQ (e.symm (wedgeRep g⁻¹ w))).2 h1 s hs
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, himage, Set.ncard_image_of_injective _ hΦ,
    Set.ncard_pair e01_ne.symm]

end CFSG.Quasithin.H13
