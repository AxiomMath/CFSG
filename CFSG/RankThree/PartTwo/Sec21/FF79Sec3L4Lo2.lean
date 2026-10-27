module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs
import all CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOP
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lo
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4LoAut
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4LoComp

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem isSylowOf_top_sylow {G : Type} [Group G] [Finite G] (P : Sylow 3 G) :
    IsSylowOf 3 (P : Subgroup G) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index

theorem lnq_cyclic_exp3_false {L : Type} [Group L] [Finite L] (x : MulAut L) (hx : x ^ 3 = 1)
    (h : IsLnq 2 2 6 (⊤ : Subgroup L) ∨ IsLnq 2 5 3 (⊤ : Subgroup L)) :
    ∃ g : L, orderOf g = 9 ∧ ∃ k : ℤ, x g = g ^ k ∧ 9 ∣ (k - 1) ^ 2 := by
  obtain ⟨P, hP⟩ := exists_invariant_sylow3 x hx
  obtain ⟨hcyc, hcard⟩ := lnq_syl_cyclic9 L h (P : Subgroup L) (isSylowOf_top_sylow P)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgo : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  set g0 : L := (g : L) with hg0
  have hg0o : orderOf g0 = 9 := by rw [hg0, Subgroup.orderOf_coe]; exact hgo
  have hxg : x g0 ∈ (P : Subgroup L) := hP g0 g.2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, g0 ^ k = x g0 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x g0, hxg⟩)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hpow : ∀ m : ℤ, x (g0 ^ m) = g0 ^ (k * m) := fun m => by
    rw [map_zpow, ← hk, ← zpow_mul]
  have h3 : g0 ^ (k * (k * k)) = g0 := by
    have := aut_cube_apply hx g0
    rw [← hk, hpow, hpow] at this
    exact this
  have hdiv : (9 : ℤ) ∣ k * (k * k) - 1 := by
    have h1 : g0 ^ (k * (k * k) - 1) = 1 := by rw [zpow_sub, h3, zpow_one, mul_inv_cancel]
    have h2 := (orderOf_dvd_iff_zpow_eq_one).2 h1
    rw [hg0o] at h2
    exact_mod_cast h2
  refine ⟨g0, hg0o, k, hk.symm, ?_⟩
  have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).2 hdiv
  push_cast at h4
  have h5 : ∀ r : ZMod 9, r * (r * r) - 1 = 0 → (r - 1) ^ 2 = 0 := by decide
  have h6 := h5 _ h4
  have h7 : (((k - 1) ^ 2 : ℤ) : ZMod 9) = 0 := by push_cast; exact h6
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).1 h7

theorem exp3_contra {G : Type} [Group G] [Finite G] (β : MulAut G) (s : G) (k : ℤ)
    (hs : orderOf s = 9) (hk : β s = s ^ k) (hdiv : 9 ∣ (k - 1) ^ 2)
    (hexp : ∀ S : Subgroup G, IsMulCommutative S → IsPGroup 3 S → (∀ y ∈ S, β y ∈ S) →
      ∀ y ∈ S, β (β y * y⁻¹) = β y * y⁻¹ → y ^ 3 = 1) : False := by
  have hp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hs]; norm_num)
  have hstab : ∀ y ∈ Subgroup.zpowers s, β y ∈ Subgroup.zpowers s := by
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, hk, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) _
  have hfix : β (β s * s⁻¹) = β s * s⁻¹ := by
    rw [map_mul, map_inv, hk, map_zpow, hk, ← zpow_mul]
    have e2 : s ^ (k * k) * (s ^ k)⁻¹ = s ^ (k * k - k) := (zpow_sub s _ _).symm
    have e3 : s ^ k * s⁻¹ = s ^ (k - 1) := by rw [zpow_sub, zpow_one]
    rw [e2, e3, zpow_eq_zpow_iff_modEq, hs, Int.modEq_iff_dvd]
    have e4 : (k - 1) - (k * k - k) = -((k - 1) ^ 2) := by ring
    rw [e4]
    exact_mod_cast (dvd_neg).2 hdiv
  have h3 := hexp _ inferInstance hp hstab s (Subgroup.mem_zpowers s) hfix
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hs] at this
  omega

theorem ap_of_struct_K (hO : FF79KLemmaOP) {β : MulAut H} {K L : Subgroup H}
    (hβ : β ^ 3 = 1) (hS : FF79APStruct β K L) (hKfix : ∀ k ∈ K, β k = k)
    (hK5 : Nonempty (K ≃* alternatingGroup (Fin 5))) :
    IsLnq 3 2 2 (⊤ : Subgroup ↥(layer H)) := by
  have hL := hS.layer_eq
  subst hL
  have hm := hS.β_mem
  let x : MulAut ↥(layer H) := restrAut β (layer H) hβ hm
  have hxc : ∀ l : ↥(layer H), ((x l : ↥(layer H)) : H) = β (l : H) := fun l => rfl
  have hx3 : x ^ 3 = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    have h1 : ((x ^ 3) l : ↥(layer H)) = x (x (x l)) := by simp [pow_succ]
    rw [h1]
    show β (β (β (l : H))) = (l : H)
    exact aut_cube_apply hβ _
  have hx1 : x ≠ 1 := by
    intro h1
    apply hS.outer 1 (one_mem _)
    intro l hl
    have e : β l = l := congrArg (fun f : MulAut ↥(layer H) => ((f ⟨l, hl⟩ : ↥(layer H)) : H)) h1
    simpa using e
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxconj : ∀ c : ↥(layer H), x ≠ MulAut.conj c := by
    intro c hc
    apply hS.outer c c.2
    intro l hl
    have e : β l = c * l * (c : H)⁻¹ :=
      congrArg (fun f : MulAut ↥(layer H) => ((f ⟨l, hl⟩ : ↥(layer H)) : H)) hc
    exact e
  have hE : (x.toMonoidHom.eqLocus (MonoidHom.id ↥(layer H))).map (layer H).subtype =
      apFix β (layer H) := by
    ext h
    simp only [apFix, Subgroup.mem_map, MonoidHom.eqLocus, Subgroup.mem_inf,
      MulEquiv.coe_toMonoidHom,
      MonoidHom.id_apply, Subgroup.subtype_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, congrArg Subtype.val hl⟩
    · rintro ⟨hh, hb⟩
      exact ⟨⟨h, hh⟩, Subtype.ext hb, rfl⟩
  have hinj : Function.Injective (layer H).subtype := Subtype.coe_injective
  have hcomp := isComponent_subgroupOf_map_iff (layer H).subtype hinj hE
  have hKmap : ((K.subgroupOf (layer H)).map (layer H).subtype) = K :=
    Subgroup.map_subgroupOf_eq_of_le hS.K_le
  have hAb : HasAbelianSylow3 ↥(layer H) := by
    obtain ⟨S, hSL, hSyl, hcomm⟩ := hS.absyl
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 (S.subgroupOf (layer H)) := hSyl.2.1.comap_subtype
    have hnd : ¬ 3 ∣ (S.subgroupOf (layer H)).index := fun hd => by
      have := Nat.Coprime.eq_one_of_dvd hSyl.2.2 hd
      omega
    refine ⟨hp.toSylow hnd, fun a ha b hb => ?_⟩
    apply Subtype.ext
    have h1 : (a : H) ∈ S := ha
    have h2 : (b : H) ∈ S := hb
    have hc := congrArg Subtype.val (hcomm.is_comm.comm ⟨(a : H), h1⟩ ⟨(b : H), h2⟩)
    exact hc
  have hInv : ThreeRankLeOneInv ↥(layer H) := by
    intro t u v ht htu htv huv hu hv
    have h := hS.inv3 t u v t.2 (by rw [Subgroup.orderOf_coe]; exact ht) u.2 v.2
      (by rw [Subgroup.orderOf_coe]; exact hu) (by rw [Subgroup.orderOf_coe]; exact hv)
      (congrArg Subtype.val htu.symm) (congrArg Subtype.val htv.symm)
      (congrArg Subtype.val huv)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  have hfalse : IsLnq 2 2 6 (⊤ : Subgroup ↥(layer H)) ∨ IsLnq 2 5 3 (⊤ : Subgroup ↥(layer H)) →
      False := by
    intro h
    obtain ⟨g0, hg0o, k, hk, hdiv⟩ := lnq_cyclic_exp3_false x hx3 h
    refine exp3_contra β (g0 : H) k (by rw [Subgroup.orderOf_coe]; exact hg0o) ?_ hdiv hS.exp3
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h1
    exact h1
  have hdisj := hO ↥(layer H) hS.simple hS.nonab hS.catalog hAb hInv x hxo hxconj
    (K.subgroupOf (layer H)) ?_ ?_ ?_ ?_
  · rcases hdisj with h | h | h
    · exact (hfalse (Or.inl h)).elim
    · exact (hfalse (Or.inr h)).elim
    · exact h
  · intro l hl
    exact Subtype.ext (hKfix _ hl)
  · obtain ⟨e⟩ := hK5
    exact ⟨(Subgroup.subgroupOfEquivOfLe hS.K_le).trans e⟩
  · exact (hcomp (K.subgroupOf (layer H))).2 (by rw [hKmap]; exact hS.K_comp)
  · intro K'' hle hc hne
    have hle' : K''.map (layer H).subtype ≤ apFix β (layer H) := hE ▸ Subgroup.map_mono hle
    have hc' := (hcomp K'').1 hc
    have hne' : K''.map (layer H).subtype ≠ K := by
      intro h
      apply hne
      rw [← Subgroup.comap_map_eq_self_of_injective hinj K'', h]
      rfl
    have := hS.others _ hle' hc' hne'
    rwa [Nat.card_congr (K''.equivMapOfInjective _ hinj).toEquiv.symm] at this

end CFSG.RankThree.PartTwo.Sec21.FF79
