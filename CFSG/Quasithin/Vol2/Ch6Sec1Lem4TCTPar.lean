module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TE

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_inner_of_pow_three {G : Type*} [Group G] (hcard : Nat.card (Outer G) = 2)
    {α : MulAut G} (hα : α ^ 3 = 1) : α ∈ inner G := by
  have h3 : orderOf (QuotientGroup.mk α : Outer G) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk α : Outer G) ∣ 2 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hg : orderOf (QuotientGroup.mk α : Outer G) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h3 h2
  have hg1 : Nat.gcd 3 2 = 1 := by norm_num
  rw [hg1] at hg
  have h1 : orderOf (QuotientGroup.mk α : Outer G) = 1 := Nat.dvd_one.mp hg
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

section Tits

theorem stabilizer_zero_eq_titsH :
    MulAction.stabilizer titsD (0 : Fin 1755) = titsH.subgroupOf titsD := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← titsDStab_zero, mem_titsDStab]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem isCoatom_titsH : IsCoatom (titsH.subgroupOf titsD) := by
  haveI : MulAction.IsPreprimitive titsD (Fin 1755) := CERT_Tits_derived_primitive
  rw [← stabilizer_zero_eq_titsH]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := titsD) (0 : Fin 1755)

theorem card_titsH_subgroupOf : Nat.card (titsH.subgroupOf titsD) = 10240 := by
  rw [card_subgroupOf_eq titsH_le_titsD]
  exact titsQH_facts.2.2.2

theorem normalizer_oTwoUpper_titsH :
    Subgroup.normalizer ((oTwoUpper (titsH.subgroupOf titsD) : Subgroup titsD) : Set titsD) =
      titsH.subgroupOf titsD := by
  haveI : IsSimpleGroup titsD := titsD_simple
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set H' : Subgroup titsD := titsH.subgroupOf titsD with hH'
  set K : Subgroup titsD := oTwoUpper H' with hK
  have hHN : H' ≤ Subgroup.normalizer (K : Set titsD) := le_normalizer_oTwoUpper H'
  rcases eq_or_lt_of_le hHN with h | h
  · exact h.symm
  · exfalso
    have hNtop : Subgroup.normalizer (K : Set titsD) = ⊤ := isCoatom_titsH.2 _ h
    have hKn : K.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hb | ht
    ·
      have hdvd : 5 ∣ Nat.card H' := by
        rw [hH', card_titsH_subgroupOf]
        norm_num
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
      have hxK : (x : titsD) ∈ K := by
        apply mem_oTwoUpper_of_odd x.2
        rw [Subgroup.orderOf_coe, hx]
        decide
      rw [hb] at hxK
      have h1 : (x : titsD) = 1 := Subgroup.mem_bot.mp hxK
      have h2 : x = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hx
      norm_num at hx
    ·
      have hle : K ≤ H' := oTwoUpper_le H'
      rw [ht] at hle
      have htop : H' = ⊤ := top_le_iff.mp hle
      have hc : Nat.card H' = Nat.card titsD := by rw [htop, Subgroup.card_top]
      rw [card_titsH_subgroupOf, card_titsD] at hc
      norm_num at hc

theorem eq_one_of_mem_titsH_of_pow_three {d : titsD} (hd : d ∈ titsH.subgroupOf titsD)
    (h3 : d ^ 3 = 1) : d = 1 := by
  have h1 : orderOf (⟨d, hd⟩ : ↥(titsH.subgroupOf titsD)) ∣
      Nat.card (titsH.subgroupOf titsD) := orderOf_dvd_natCard _
  rw [card_titsH_subgroupOf] at h1
  have h2 : orderOf (⟨d, hd⟩ : ↥(titsH.subgroupOf titsD)) ∣ 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one h3
  have hg : orderOf (⟨d, hd⟩ : ↥(titsH.subgroupOf titsD)) ∣ Nat.gcd 10240 3 :=
    Nat.dvd_gcd h1 h2
  have hg1 : Nat.gcd 10240 3 = 1 := by norm_num
  rw [hg1] at hg
  have h3' : (⟨d, hd⟩ : ↥(titsH.subgroupOf titsD)) = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  exact congrArg Subtype.val h3'

theorem titsParabolicNormalizerFact_holds : TitsParabolicNormalizerFact := by
  intro Y _ hfin hY P hP φ hφ3 hφN
  obtain ⟨e⟩ := titsModelEquiv Y 2 1 hY
  have hYcard : Nat.card Y = 17971200 := by
    rw [Nat.card_congr e.toEquiv, card_titsD]
  obtain ⟨S₁, hS₁⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := P) (n := 11)
    (by rw [hP]; exact dvd_mul_right _ _)
  set S₀ : Subgroup Y := S₁.map P.subtype with hS₀def
  have hS₀card : Nat.card S₀ = 2 ^ 11 := by
    rw [hS₀def, Subgroup.card_map_of_injective P.subtype_injective, hS₁]
  have hS₀P : S₀ ≤ P := Subgroup.map_subtype_le S₁
  have hS₀syl : IsSylowTwoOf S₀ ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 11) hS₀card, ?_⟩
    have h1 := (S₀.subgroupOf ⊤).card_mul_index
    rw [card_subgroupOf_eq le_top, hS₀card, Subgroup.card_top, hYcard] at h1
    intro h2
    obtain ⟨m, hm⟩ := h2
    rw [hm] at h1
    omega
  have hrel : S₀.relIndex P = 5 := by
    have h1 := (S₀.subgroupOf P).card_mul_index
    rw [card_subgroupOf_eq hS₀P, hS₀card, hP] at h1
    have h2 : (S₀.subgroupOf P).index = 5 := by
      have hpos : (2 : ℕ) ^ 11 ≠ 0 := by norm_num
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) (by rw [h1])
    exact h2
  have hP5 : P = titsH614 S₀ := titsOver5Fact_holds Y hY S₀ P hS₀syl hS₀P hrel
  obtain ⟨F, hF⟩ := exists_mulEquiv_titsS614 e hS₀syl
  have hPF : P.map F.toMonoidHom = titsH.subgroupOf titsD := by
    rw [hP5, map_titsH614, hF, titsH614_titsS]
  set ψ : MulAut titsD := MulAut.congr F φ with hψdef
  have hψ3 : ψ ^ 3 = 1 := by
    rw [hψdef, ← map_pow, hφ3, map_one]
  have hcomm : ∀ y : Y, ψ (F y) = F (φ y) := by
    intro y
    rw [hψdef]
    simp only [MulAut.congr, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hψN : (oTwoUpper (titsH.subgroupOf titsD)).map ψ.toMonoidHom =
      oTwoUpper (titsH.subgroupOf titsD) := by
    rw [← hPF, oTwoUpper_map, Subgroup.map_map]
    have hcomp : ψ.toMonoidHom.comp F.toMonoidHom = F.toMonoidHom.comp φ.toMonoidHom :=
      MonoidHom.ext fun y => hcomm y
    rw [hcomp, ← Subgroup.map_map, hφN]
  have hinner : ψ ∈ (MulAut.conj : titsD →* MulAut titsD).range :=
    mem_inner_of_pow_three card_outer_titsD hψ3
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hinner
  have hd3 : d ^ 3 = 1 := by
    haveI : (Subgroup.center titsD).Normal := inferInstance
    have h1 : MulAut.conj (d ^ 3) = 1 := by rw [map_pow, hd, hψ3]
    have hz : d ^ 3 ∈ Subgroup.center titsD := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun α : MulAut titsD => α g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [titsD_center] at hz
    exact Subgroup.mem_bot.mp hz
  have hdN : d ∈ Subgroup.normalizer
      ((oTwoUpper (titsH.subgroupOf titsD) : Subgroup titsD) : Set titsD) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hψh : ψ h = d * h * d⁻¹ := by
      rw [← hd, MulAut.conj_apply]
    rw [← hψh]
    constructor
    · intro hh
      rw [← hψN]
      exact Subgroup.mem_map_of_mem _ hh
    · intro hh
      rw [← hψN] at hh
      obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.mp hh
      have hkh' : k = h := ψ.injective hkh
      rw [← hkh']
      exact hk
  rw [normalizer_oTwoUpper_titsH] at hdN
  have hd1 : d = 1 := eq_one_of_mem_titsH_of_pow_three hdN hd3
  have hψ1 : ψ = 1 := by
    rw [← hd, hd1, map_one]
  exact (MulAut.congr F).injective (by rw [map_one]; exact hψ1)

end Tits

end CFSG.Quasithin.H13.T614

end
