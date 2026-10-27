module

public import CFSG.Quasithin.MS93.S46SL2
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec92Quot
import CFSG.RankThree.GF2n.Stroth80.HeringSec91N5
import CFSG.RankThree.GF2n.Stroth80.HeringSec9Quot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Split92

open CFSG.QuasithinUnique.Setup.SL2Modules (uElt dElt)
open scoped commutatorElement MatrixGroups

section Abstract

variable {H : Type*} [Group H]

theorem map_commutator_eq_top {S : Type*} [Group S] (θ : H →* S) (hperf : commutator S = ⊤)
    {C : Subgroup H} (hC : C.map θ = ⊤) : (⁅C, C⁆).map θ = ⊤ := by
  rw [Subgroup.map_commutator, hC, ← commutator_def, hperf]

theorem map_eq_top_of_sup {S : Type*} [Group S] (θ : H →* S) (hθ : Function.Surjective θ)
    {C R₀ : Subgroup H} (hR₀ : R₀ ≤ θ.ker) (hcov : C ⊔ R₀ = ⊤) : C.map θ = ⊤ := by
  have h1 : (C ⊔ R₀).map θ = ⊤ := by rw [hcov, Subgroup.map_top_of_surjective θ hθ]
  rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff R₀).mpr hR₀, sup_bot_eq] at h1

theorem comm_mul_right_eq {a b k : H} (h : k * b = b * k) : ⁅a * k, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  rw [show a * k * b * (k⁻¹ * a⁻¹) * b⁻¹ = a * (k * b) * k⁻¹ * a⁻¹ * b⁻¹ by group, h]
  group

theorem comm_mul_right_eq' {a b k : H} (h : k * a = a * k) : ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have h' : k * a⁻¹ = a⁻¹ * k := by
    calc k * a⁻¹ = a⁻¹ * (a * k) * a⁻¹ := by group
      _ = a⁻¹ * (k * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * k := by group
  simp only [commutatorElement_def, mul_inv_rev]
  rw [show a * (b * k) * a⁻¹ * (k⁻¹ * b⁻¹) = a * b * (k * a⁻¹) * k⁻¹ * b⁻¹ by group, h']
  group

theorem commutator_commutator_eq {C K : Subgroup H}
    (hcov : ∀ c ∈ C, ∃ y ∈ ⁅C, C⁆, y⁻¹ * c ∈ K) (hK : ∀ k ∈ K, ∀ c ∈ C, c * k = k * c) :
    ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := by
  have hYC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le_self C
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [Subgroup.commutator_le]
  intro c₁ hc₁ c₂ hc₂
  obtain ⟨y₁, hy₁, hk₁⟩ := hcov c₁ hc₁
  obtain ⟨y₂, hy₂, hk₂⟩ := hcov c₂ hc₂
  have hk₂C : y₂⁻¹ * c₂ ∈ C := C.mul_mem (C.inv_mem (hYC hy₂)) hc₂
  have e₁ : c₁ = y₁ * (y₁⁻¹ * c₁) := by group
  have e₂ : c₂ = y₂ * (y₂⁻¹ * c₂) := by group
  have a1 : (y₁⁻¹ * c₁) * (y₂ * (y₂⁻¹ * c₂)) = (y₂ * (y₂⁻¹ * c₂)) * (y₁⁻¹ * c₁) :=
    (hK _ hk₁ _ (C.mul_mem (hYC hy₂) hk₂C)).symm
  have a2 : (y₂⁻¹ * c₂) * y₁ = y₁ * (y₂⁻¹ * c₂) := (hK _ hk₂ _ (hYC hy₁)).symm
  have key : ⁅c₁, c₂⁆ = ⁅y₁, y₂⁆ := by
    rw [e₁, e₂, comm_mul_right_eq a1, comm_mul_right_eq' a2]
  rw [key]
  exact Subgroup.commutator_mem_commutator hy₁ hy₂

theorem exists_inv_mul_conj_eq {S : Type*} [Group S] {U : Subgroup S} [Finite U] {d : S}
    (hd : d ∈ Subgroup.normalizer (U : Set S)) (hfpf : ∀ u ∈ U, d⁻¹ * u * d = u → u = 1) :
    ∀ u ∈ U, ∃ v ∈ U, v⁻¹ * (d⁻¹ * v * d) = u := by
  have hconj : ∀ v ∈ U, d⁻¹ * v * d ∈ U := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set S)).inv_mem hd) v).mp hv
    simpa using this
  let f : U → U := fun v => ⟨v⁻¹ * (d⁻¹ * v * d), U.mul_mem (U.inv_mem v.2) (hconj v v.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : (a : S)⁻¹ * (d⁻¹ * a * d) = (b : S)⁻¹ * (d⁻¹ * b * d) := congrArg Subtype.val hab
    have hw : d⁻¹ * ((b : S) * (a : S)⁻¹) * d = (b : S) * (a : S)⁻¹ := by
      have e' : d⁻¹ * (b : S) * d = (b : S) * (a : S)⁻¹ * (d⁻¹ * (a : S) * d) := by
        calc d⁻¹ * (b : S) * d = (b : S) * ((b : S)⁻¹ * (d⁻¹ * (b : S) * d)) := by group
          _ = (b : S) * ((a : S)⁻¹ * (d⁻¹ * (a : S) * d)) := by rw [e]
          _ = (b : S) * (a : S)⁻¹ * (d⁻¹ * (a : S) * d) := by group
      calc d⁻¹ * ((b : S) * (a : S)⁻¹) * d
          = (d⁻¹ * (b : S) * d) * (d⁻¹ * (a : S) * d)⁻¹ := by group
        _ = (b : S) * (a : S)⁻¹ := by rw [e']; group
    have h1 := hfpf _ (U.mul_mem b.2 (U.inv_mem a.2)) hw
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  intro u hu
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem comm_of_cover {R₀ Y L : Subgroup H} [R₀.Normal]
    (hYC : Y ≤ Subgroup.centralizer (R₀ : Set H)) (hL : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    {h : H} (hhY : h ∈ Y) (hhL : h ∈ Subgroup.normalizer (L : Set H))
    (hsurj : ∀ p ∈ Y ⊓ (L ⊔ R₀), ∃ p' ∈ Y ⊓ (L ⊔ R₀), (p'⁻¹ * (h⁻¹ * p' * h))⁻¹ * p ∈ R₀) :
    ∀ a ∈ Y ⊓ (L ⊔ R₀), ∀ b ∈ Y ⊓ (L ⊔ R₀), a * b = b * a := by
  have hcen : ∀ y ∈ Y, ∀ r ∈ R₀, y * r = r * y := fun y hy r hr =>
    (Subgroup.mem_centralizer_iff.mp (hYC hy) r hr).symm
  have he : ∀ p' ∈ Y ⊓ (L ⊔ R₀), p'⁻¹ * (h⁻¹ * p' * h) ∈ L ⊓ Y := by
    rintro p' ⟨hpY, hpL⟩
    refine ⟨?_, Y.mul_mem (Y.inv_mem hpY) (Y.mul_mem (Y.mul_mem (Y.inv_mem hhY) hpY) hhY)⟩
    rw [sup_comm] at hpL
    obtain ⟨r, hr, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hpL
    have hrh : r * h = h * r := (hcen h hhY r hr).symm
    have hlh : h⁻¹ * l * h ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set H)).inv_mem hhL) l).mp hl
      simpa using this
    have e : (r * l)⁻¹ * (h⁻¹ * (r * l) * h) = l⁻¹ * (h⁻¹ * l * h) := by
      have e1 : h⁻¹ * r = r * h⁻¹ := by
        calc h⁻¹ * r = h⁻¹ * (r * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * r) * h⁻¹ := by rw [hrh]
          _ = r * h⁻¹ := by group
      calc (r * l)⁻¹ * (h⁻¹ * (r * l) * h) = l⁻¹ * r⁻¹ * ((h⁻¹ * r) * l * h) := by group
        _ = l⁻¹ * (h⁻¹ * l * h) := by rw [e1]; group
    rw [e]
    exact L.mul_mem (L.inv_mem hl) hlh
  have hdec : ∀ a ∈ Y ⊓ (L ⊔ R₀), ∃ e ∈ L ⊓ Y, ∃ z ∈ R₀ ⊓ Y, a = e * z := by
    intro a ha
    obtain ⟨p', hp', hz⟩ := hsurj a ha
    refine ⟨_, he p' hp', _, ⟨hz, Y.mul_mem (Y.inv_mem (he p' hp').2) ha.1⟩, ?_⟩
    group
  intro a ha b hb
  obtain ⟨e₁, ⟨he₁L, he₁Y⟩, z₁, ⟨hz₁R, hz₁Y⟩, rfl⟩ := hdec a ha
  obtain ⟨e₂, ⟨he₂L, he₂Y⟩, z₂, ⟨hz₂R, hz₂Y⟩, rfl⟩ := hdec b hb
  have c1 : e₂ * z₁ = z₁ * e₂ := hcen e₂ he₂Y z₁ hz₁R
  have c2 : e₁ * z₂ = z₂ * e₁ := hcen e₁ he₁Y z₂ hz₂R
  have c3 : z₂ * z₁ = z₁ * z₂ := hcen z₂ hz₂Y z₁ hz₁R
  have c4 : e₁ * e₂ = e₂ * e₁ := hL e₁ he₁L e₂ he₂L
  calc e₁ * z₁ * (e₂ * z₂) = e₁ * (z₁ * e₂) * z₂ := by group
    _ = e₁ * e₂ * (z₁ * z₂) := by rw [← c1]; group
    _ = e₂ * e₁ * (z₂ * z₁) := by rw [c4, c3]
    _ = e₂ * (e₁ * z₂) * z₁ := by group
    _ = e₂ * z₂ * (e₁ * z₁) := by rw [c2]; group

open scoped IsMulCommutative in
theorem eq_one_of_transfer [Finite H] {Y P : Subgroup H} (hY : ⁅Y, Y⁆ = Y) (hPY : P ≤ Y)
    (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (P.relIndex Y)) {z : H} (hz : z ∈ P)
    (hzY : ∀ y ∈ Y, y * z = z * y) {k : ℕ} (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  classical
  haveI : IsMulCommutative (P.subgroupOf Y) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hP _ a.2 _ b.2))⟩⟩
  let τ : Y →* P.subgroupOf Y := (MonoidHom.id (P.subgroupOf Y)).transfer
  have hperf : commutator Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Y.range_subtype, hY]
  let z' : Y := ⟨z, hPY hz⟩
  have h1 : τ z' = 1 := Abelianization.commutator_subset_ker τ (hperf ▸ Subgroup.mem_top z')
  have hcomm : ∀ g₀ : Y, g₀ * z' = z' * g₀ := fun g₀ => Subtype.ext (hzY g₀ g₀.2)
  have h2 := MonoidHom.transfer_eq_pow (MonoidHom.id (P.subgroupOf Y)) z' (fun j g₀ _ => by
    have hc : Commute g₀ (z' ^ j) := (Commute.pow_right (hcomm g₀) j)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul])
  rw [h1] at h2
  have h3 : z ^ (P.subgroupOf Y).index = 1 := by
    have := congrArg (fun x : P.subgroupOf Y => ((x : Y) : H)) h2
    simpa [z'] using this.symm
  have hd1 : orderOf z ∣ P.relIndex Y := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hcop : Nat.Coprime (2 ^ k) (P.relIndex Y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd2 hd1))

theorem exists_odd_pow [Finite H] (h₀ : H) : ∃ a : ℕ, Odd (orderOf (h₀ ^ (2 ^ a))) := by
  obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h₀).ne'
  refine ⟨a, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)⟩
  rw [← pow_mul, ← he, pow_orderOf_eq_one]

theorem split_abstract [Finite H] {S : Type*} [Group S] [Finite S]
    (R₀ : Subgroup H) [R₀.Normal] (θ : H →* S) (hθ : Function.Surjective θ) (hker : θ.ker = R₀)
    (hperf : commutator S = ⊤) (hcover : Subgroup.centralizer (R₀ : Set H) ⊔ R₀ = ⊤)
    (h2 : IsPGroup 2 ↥(Subgroup.centralizer (R₀ : Set H) ⊓ R₀))
    (L : Subgroup H) (hL : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hnorm : ∀ g ∈ Subgroup.centralizer (R₀ : Set H),
      θ g ∈ Subgroup.normalizer ((L.map θ : Subgroup S) : Set S) →
        g ∈ Subgroup.normalizer (L : Set H))
    {d : S} (hd : d ∈ Subgroup.normalizer ((L.map θ : Subgroup S) : Set S))
    (hfpf : ∀ u ∈ L.map θ, d⁻¹ * u * d = u → u = 1)
    (hdodd : Odd (orderOf d)) (hUodd : Odd (L.map θ).index) :
    ∃ Y : Subgroup H, Y ≤ Subgroup.centralizer (R₀ : Set H) ∧ Y ⊔ R₀ = ⊤ ∧ Y ⊓ R₀ = ⊥ ∧
      Function.Bijective (θ.comp Y.subtype) := by
  classical
  set C := Subgroup.centralizer (R₀ : Set H) with hCdef
  set Y := ⁅C, C⁆ with hYdef
  have hYC : Y ≤ C := Subgroup.commutator_le_self C
  have hR₀ker : R₀ ≤ θ.ker := hker.ge
  have hCθ : C.map θ = ⊤ := map_eq_top_of_sup θ hθ hR₀ker hcover
  have hYθ : Y.map θ = ⊤ := map_commutator_eq_top θ hperf hCθ
  have hlift : ∀ s : S, ∃ y ∈ Y, θ y = s := fun s => by
    have : s ∈ Y.map θ := hYθ ▸ Subgroup.mem_top s
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨y, hy, rfl⟩
  have hmemR₀ : ∀ g : H, θ g = 1 → g ∈ R₀ := fun g hg => hker ▸ hg
  have hcen : ∀ y ∈ C, ∀ r ∈ R₀, y * r = r * y := fun y hy r hr =>
    (Subgroup.mem_centralizer_iff.mp hy r hr).symm
  have hYperf : ⁅Y, Y⁆ = Y := by
    refine commutator_commutator_eq (K := R₀) (fun c _ => ?_) (fun k hk c hc => hcen c hc k hk)
    obtain ⟨y, hy, hyc⟩ := hlift (θ c)
    exact ⟨y, hy, hmemR₀ _ (by rw [map_mul, map_inv, hyc, inv_mul_cancel])⟩
  have hsup : Y ⊔ R₀ = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨y, hy, hyg⟩ := hlift (θ g)
    have hr : y⁻¹ * g ∈ R₀ := hmemR₀ _ (by rw [map_mul, map_inv, hyg, inv_mul_cancel])
    have : g = y * (y⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hr
  obtain ⟨h₀, hh₀Y, hh₀⟩ := hlift d
  obtain ⟨a, ha⟩ := exists_odd_pow h₀
  set h := h₀ ^ (2 ^ a) with hhdef
  have hhY : h ∈ Y := Y.pow_mem hh₀Y _
  set U := L.map θ with hUdef
  have hθh : θ h = d ^ (2 ^ a) := by rw [hhdef, map_pow, hh₀]
  have hdU : θ h ∈ Subgroup.normalizer (U : Set S) := by
    rw [hθh]; exact (Subgroup.normalizer (U : Set S)).pow_mem hd _
  have hcop : (2 ^ a).Coprime (orderOf d) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hdodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hfpf' : ∀ u ∈ U, (θ h)⁻¹ * u * θ h = u → u = 1 := by
    intro u hu hfix
    refine hfpf u hu ?_
    have hc : Commute (θ h) u := by
      have : θ h * ((θ h)⁻¹ * u * θ h) = θ h * u := by rw [hfix]
      rw [show θ h * ((θ h)⁻¹ * u * θ h) = u * θ h by group] at this
      exact this.symm
    have hc' : Commute d u := by
      rw [← hm, ← hθh]
      exact hc.pow_left m
    rw [mul_assoc, ← hc'.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hhL : h ∈ Subgroup.normalizer (L : Set H) := hnorm h (hYC hhY) hdU
  set P := Y ⊓ (L ⊔ R₀) with hPdef
  have hθP : ∀ g : H, g ∈ L ⊔ R₀ ↔ θ g ∈ U := by
    intro g
    constructor
    · intro hg
      obtain ⟨l, hl, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      have hr1 : θ r = 1 := (hker ▸ hr : r ∈ θ.ker)
      rw [map_mul, hr1, mul_one]
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, hlg⟩
      have hr : l⁻¹ * g ∈ R₀ := hmemR₀ _ (by rw [map_mul, map_inv, hlg, inv_mul_cancel])
      have : g = l * (l⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hl hr
  have hsurj : ∀ p ∈ P, ∃ p' ∈ P, (p'⁻¹ * (h⁻¹ * p' * h))⁻¹ * p ∈ R₀ := by
    intro p hp
    obtain ⟨v, hvU, hv⟩ := exists_inv_mul_conj_eq hdU hfpf' (θ p) ((hθP p).mp hp.2)
    obtain ⟨y, hyY, hyv⟩ := hlift v
    have hyP : y ∈ P := ⟨hyY, (hθP y).mpr (hyv ▸ hvU)⟩
    refine ⟨y, hyP, hmemR₀ _ ?_⟩
    simp only [map_mul, map_inv, hyv, hv, inv_mul_cancel]
  have hPcomm := comm_of_cover hYC hL hhY hhL hsurj
  have hPidx : P.relIndex Y = U.index := by
    have hsub : P.subgroupOf Y = U.comap (θ.comp Y.subtype) := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.coe_comp,
        Subgroup.coe_subtype, Function.comp_apply]
      exact ⟨fun hy => (hθP y).mp hy.2, fun hy => ⟨y.2, (hθP y).mpr hy⟩⟩
    have hsurjY : Function.Surjective (θ.comp Y.subtype) := fun s => by
      obtain ⟨y, hy, hys⟩ := hlift s
      exact ⟨⟨y, hy⟩, hys⟩
    rw [Subgroup.relIndex, hsub, Subgroup.index_comap_of_surjective _ hsurjY]
  have hinf : Y ⊓ R₀ = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have hzC : z ∈ C ⊓ R₀ := ⟨hYC hz.1, hz.2⟩
    obtain ⟨k, hk⟩ := (h2 ⟨z, hzC⟩)
    have hzk : z ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hzP : z ∈ P := ⟨hz.1, Subgroup.mem_sup_right hz.2⟩
    exact (eq_one_of_transfer hYperf inf_le_left hPcomm (hPidx ▸ hUodd) hzP
      (fun y hy => hcen y (hYC hy) z hz.2) hzk)
  refine ⟨Y, hYC, hsup, hinf, ⟨?_, fun s => ?_⟩⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hyR : (y : H) ∈ R₀ := hmemR₀ _ hy
    have : (y : H) ∈ Y ⊓ R₀ := ⟨y.2, hyR⟩
    rw [hinf] at this
    exact Subtype.ext this
  · obtain ⟨y, hy, hys⟩ := hlift s
    exact ⟨⟨y, hy⟩, hys⟩

end Abstract

section Torus

variable {F : Type*} [Field F]

theorem dElt_mul_uElt (z : Fˣ) (t : F) :
    dElt z * uElt t = uElt ((z : F) * z * t) * dElt z := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hz : (z : F) ≠ 0 := z.ne_zero
  fin_cases i <;> fin_cases j <;> simp [dElt, uElt, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

theorem dElt_mul' (a b : Fˣ) : dElt (a * b) = dElt a * dElt b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul, mul_comm]

theorem dElt_one' : dElt (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dElt]

theorem dElt_pow (z : Fˣ) (n : ℕ) : dElt z ^ n = dElt (z ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, dElt_one']
  | succ n ih => rw [pow_succ, ih, ← dElt_mul', ← pow_succ]

theorem uElt_injective : Function.Injective (uElt (F := F)) := by
  intro s t h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uElt] using this

theorem dElt_conj (z : Fˣ) (t : F) : dElt z * uElt t * (dElt z)⁻¹ = uElt ((z : F) * z * t) := by
  rw [dElt_mul_uElt, mul_assoc, mul_inv_cancel, mul_one]

theorem dElt_inv' (z : Fˣ) : (dElt z)⁻¹ = dElt z⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dElt_mul', mul_inv_cancel, dElt_one']

theorem exists_torus [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F) (U : Subgroup SL(2, F))
    (hU : IsPGroup 2 U) (hUc : Nat.card U = Nat.card F) :
    ∃ d : SL(2, F), d ∈ Subgroup.normalizer (U : Set SL(2, F)) ∧
      (∀ u ∈ U, d⁻¹ * u * d = u → u = 1) ∧
      Odd (orderOf d) := by
  classical
  obtain ⟨x, hx⟩ := CFSG.Quasithin.MS93.S46.exists_eq_conj_uElt U hU hUc
  have hunits : 1 < Fintype.card Fˣ := by rw [Fintype.card_units]; omega
  haveI : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp hunits
  obtain ⟨z, hz⟩ := exists_ne (1 : Fˣ)
  set w : F := ((z⁻¹ : Fˣ) : F) with hw
  have hww : w * w ≠ 1 := by
    intro h
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h1 : (w - 1) * (w - 1) = 0 := by linear_combination h + (1 - w) * h2
    have h3 : w = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp h1)
    exact hz (inv_eq_one.mp (Units.val_eq_one.mp h3))
  set d := x * dElt z * x⁻¹ with hd
  have hdconj : ∀ t : F, d * (x * uElt t * x⁻¹) * d⁻¹ = x * uElt ((z : F) * z * t) * x⁻¹ := by
    intro t
    rw [← dElt_conj z t, hd]
    group
  have hdconj' : ∀ t : F, d⁻¹ * (x * uElt t * x⁻¹) * d = x * uElt (w * w * t) * x⁻¹ := by
    intro t
    have e := dElt_conj z⁻¹ t
    rw [← dElt_inv', inv_inv] at e
    rw [← e, hd]
    group
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨t, rfl⟩ := (hx g).mp hg
      exact (hx _).mpr ⟨_, hdconj t⟩
    · intro hg
      obtain ⟨s, hs⟩ := (hx _).mp hg
      have e : g = d⁻¹ * (x * uElt s * x⁻¹) * d := by rw [← hs]; group
      rw [e, hdconj' s]
      exact (hx _).mpr ⟨_, rfl⟩
  · intro u hu hfix
    obtain ⟨t, rfl⟩ := (hx u).mp hu
    rw [hdconj' t] at hfix
    have h1 : uElt (w * w * t) = uElt t := by
      have := congrArg (fun g => x⁻¹ * g * x) hfix
      simpa [mul_assoc] using this
    have h2 : (w * w - 1) * t = 0 := by
      have := uElt_injective h1
      linear_combination this
    have ht : t = 0 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hww)
    rw [ht, CFSG.QuasithinUnique.Setup.SL2Modules.uElt_zero, mul_one, mul_inv_cancel]
  · have hord : orderOf d = orderOf (dElt z) := by
      rw [hd]
      exact MulEquiv.orderOf_eq (MulAut.conj x) (dElt z)
    rw [hord]
    have hpow : dElt z ^ (Fintype.card F - 1) = 1 := by
      rw [dElt_pow, ← Fintype.card_units, pow_card_eq_one, dElt_one']
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hq : Odd (Fintype.card F - 1) := by
      rw [hn]
      have : 1 ≤ (n : ℕ) := n.pos
      obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by omega⟩
      rw [hk, pow_succ]
      refine ⟨2 ^ k - 1, ?_⟩
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    exact Odd.of_dvd_nat hq (orderOf_dvd_of_pow_eq_one hpow)

end Torus

section ProdSimple

variable {S : Type} [Group S]

theorem eq_one_of_central [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) {s : S}
    (hs : ∀ u : S, s * u = u * s) : s = 1 := by
  have hmem : s ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun u => (hs u).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · rw [h] at hmem; exact hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem normal_prod_cases [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (N : Subgroup (S × S)) [N.Normal] (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ p : S × S, p ∈ N ↔ p.2 = 1) ∨ (∀ p : S × S, p ∈ N ↔ p.1 = 1) := by
  have hfst : ∀ p ∈ N, p.1 ≠ 1 → ∃ c : S, c ≠ 1 ∧ ((c, 1) : S × S) ∈ N := by
    intro p hp hp1
    obtain ⟨s, hs⟩ := sec9_exists_comm_ne_one hS hp1
    refine ⟨⁅s, p.1⁆, hs, ?_⟩
    have h1 : ((s, 1) : S × S) * p * ((s, 1) : S × S)⁻¹ * p⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hp _) (N.inv_mem hp)
    have e : ((s, 1) : S × S) * p * ((s, 1) : S × S)⁻¹ * p⁻¹ = (⁅s, p.1⁆, 1) := by
      refine Prod.ext ?_ ?_
      · simp [commutatorElement_def]
      · simp
    rwa [e] at h1
  have hsnd : ∀ p ∈ N, p.2 ≠ 1 → ∃ c : S, c ≠ 1 ∧ ((1, c) : S × S) ∈ N := by
    intro p hp hp1
    obtain ⟨s, hs⟩ := sec9_exists_comm_ne_one hS hp1
    refine ⟨⁅s, p.2⁆, hs, ?_⟩
    have h1 : ((1, s) : S × S) * p * ((1, s) : S × S)⁻¹ * p⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hp _) (N.inv_mem hp)
    have e : ((1, s) : S × S) * p * ((1, s) : S × S)⁻¹ * p⁻¹ = (1, ⁅s, p.2⁆) := by
      refine Prod.ext ?_ ?_
      · simp
      · simp [commutatorElement_def]
    rwa [e] at h1
  have hK₁ : ∀ c : S, c ≠ 1 → ((c, 1) : S × S) ∈ N → ∀ a : S, ((a, 1) : S × S) ∈ N := by
    intro c hc hcN a
    let K₁ : Subgroup S := N.comap (MonoidHom.inl S S)
    haveI : K₁.Normal := ⟨fun u hu g => by
      have h1 := Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ hu ((g, 1) : S × S)
      simpa [K₁] using h1⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁ with h | h
    · exfalso
      have : c ∈ K₁ := hcN
      rw [h] at this
      exact hc this
    · have : a ∈ K₁ := h ▸ Subgroup.mem_top a
      exact this
  have hK₂ : ∀ c : S, c ≠ 1 → ((1, c) : S × S) ∈ N → ∀ a : S, ((1, a) : S × S) ∈ N := by
    intro c hc hcN a
    let K₂ : Subgroup S := N.comap (MonoidHom.inr S S)
    haveI : K₂.Normal := ⟨fun u hu g => by
      have h1 := Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ hu ((1, g) : S × S)
      simpa [K₂] using h1⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₂ with h | h
    · exfalso
      have : c ∈ K₂ := hcN
      rw [h] at this
      exact hc this
    · have : a ∈ K₂ := h ▸ Subgroup.mem_top a
      exact this
  by_cases hA : ∃ p ∈ N, p.1 ≠ 1
  · obtain ⟨p, hp, hp1⟩ := hA
    obtain ⟨c, hc, hcN⟩ := hfst p hp hp1
    have hall₁ := hK₁ c hc hcN
    by_cases hB : ∃ p ∈ N, p.2 ≠ 1
    · exfalso
      obtain ⟨p', hp', hp'1⟩ := hB
      obtain ⟨c', hc', hc'N⟩ := hsnd p' hp' hp'1
      have hall₂ := hK₂ c' hc' hc'N
      apply htop
      refine eq_top_iff.mpr fun y _ => ?_
      have := N.mul_mem (hall₁ y.1) (hall₂ y.2)
      simpa using this
    · push Not at hB
      left
      intro y
      refine ⟨fun hy => hB y hy, fun hy => ?_⟩
      have := hall₁ y.1
      rw [show y = (y.1, 1) from Prod.ext rfl hy]
      exact this
  · push Not at hA
    have hB : ∃ p ∈ N, p.2 ≠ 1 := by
      by_contra hB
      push Not at hB
      apply hbot
      refine eq_bot_iff.mpr fun y hy => ?_
      rw [Subgroup.mem_bot]
      exact Prod.ext (hA y hy) (hB y hy)
    obtain ⟨p, hp, hp1⟩ := hB
    obtain ⟨c, hc, hcN⟩ := hsnd p hp hp1
    have hall₂ := hK₂ c hc hcN
    right
    intro y
    refine ⟨fun hy => hA y hy, fun hy => ?_⟩
    have := hall₂ y.2
    rw [show y = (1, y.2) from Prod.ext hy rfl]
    exact this

theorem map_eq_prod_of_card {Γ : Type*} [Group Γ] [Finite Γ] [Finite S] (L₀ : Subgroup Γ)
    (hL₀ : IsPGroup 2 L₀) (ψ : Γ →* S × S) {q : ℕ} (hq : 0 < q)
    (hcard : Nat.card (L₀.map ψ) = q * q)
    (hle : ∀ U : Subgroup S, IsPGroup 2 U → Nat.card U ≤ q) :
    Nat.card (L₀.map ((MonoidHom.fst S S).comp ψ)) = q ∧
      Nat.card (L₀.map ((MonoidHom.snd S S).comp ψ)) = q ∧
      L₀.map ψ = (L₀.map ((MonoidHom.fst S S).comp ψ)).prod
        (L₀.map ((MonoidHom.snd S S).comp ψ)) := by
  set U₁ := L₀.map ((MonoidHom.fst S S).comp ψ)
  set U₂ := L₀.map ((MonoidHom.snd S S).comp ψ)
  have h₁ : Nat.card U₁ ≤ q := hle U₁ (hL₀.map _)
  have h₂ : Nat.card U₂ ≤ q := hle U₂ (hL₀.map _)
  have hsub : L₀.map ψ ≤ U₁.prod U₂ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl, rfl⟩, ⟨l, hl, rfl⟩⟩
  have hprod : Nat.card (U₁.prod U₂) = Nat.card U₁ * Nat.card U₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv U₁ U₂).toEquiv, Nat.card_prod]
  have hge : q * q ≤ Nat.card U₁ * Nat.card U₂ := by
    rw [← hcard, ← hprod]
    exact Subgroup.card_le_of_le hsub
  have e₁ : Nat.card U₁ = q := by
    by_contra hne
    have hlt : Nat.card U₁ < q := lt_of_le_of_ne h₁ hne
    have := Nat.mul_lt_mul_of_lt_of_le hlt h₂ hq
    omega
  have e₂ : Nat.card U₂ = q := by
    by_contra hne
    have hlt : Nat.card U₂ < q := lt_of_le_of_ne h₂ hne
    have := Nat.mul_lt_mul_of_le_of_lt h₁ hlt hq
    omega
  refine ⟨e₁, e₂, Subgroup.eq_of_le_of_card_ge hsub ?_⟩
  rw [hprod, e₁, e₂, hcard]

end ProdSimple

end CFSG.RankThree.GF2n.Stroth80.Split92

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace Split92

theorem card_le_of_isPGroup_statedSL {K : Type} [Field K] [Finite K] [CharP K 2]
    (U : Subgroup ↥(StatedSL 2 K)) (hU : IsPGroup 2 U) : Nat.card U ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hdvd : Nat.card U ∣ Nat.card ↥(StatedSL 2 K) := Subgroup.card_subgroup_dvd_card U
  rw [StatedAPI.card_statedSL_two, hk] at hdvd
  rw [hk]
  letI := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have h2 : 2 ∣ Nat.card K := by
    rw [hq]; exact dvd_pow_self 2 m.ne_zero
  exact HS9.le_of_two_pow_dvd_mul_sq_sub_one h2 Nat.card_pos hdvd

theorem comm_of_mul_self {X : Type*} [Group X] {L : Subgroup X} (h : ∀ a ∈ L, a * a = 1) :
    ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  have hab := h _ (L.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left (h b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

theorem factor (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G}
    (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) (hlt : Sec9R0 hc t x < Rt M (LB M Q B) t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
      ∃ ψ : ↥(Rt M (LB M Q B) t) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K),
        Function.Surjective ψ ∧ ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
        ∀ g : ↥(Rt M (LB M Q B) t), (g : G) ∈ Sec9R0 hc t x ↔ (ψ g).2 = 1 := by
  obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk⟩ := HS9.exists_psi91 hs
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  haveI : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have hnonab : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a :=
    sec9_nonabelian_of_commutator_eq_top
      (statedSL_quasisimple_of_card 2 K le_rfl h4).1.commutator_eq_top
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hR₀R : Sec9R0 hc t x ≤ Rt M (LB M Q B) t := Sec9R0_le_Rt hc hxR
  have hNR₀ : hc.CN t ≤ Sec9R0 hc t x := CN_le_Sec9R0 hc t x
  haveI hnormR₀ : ((Sec9R0 hc t x).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact Sec9R0_conj_mem hc ht g.2 ha
  set H₀ := ((Sec9R0 hc t x).subgroupOf (Rt M (LB M Q B) t)).map ψ with hH₀
  haveI : H₀.Normal := Subgroup.Normal.map hnormR₀ ψ hψs
  have hmemker : ∀ g : ↥(Rt M (LB M Q B) t), ψ g = 1 → (g : G) ∈ Sec9R0 hc t x := by
    intro g hg
    have : g ∈ ψ.ker := hg
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact hNR₀ this
  have hmem : ∀ g : ↥(Rt M (LB M Q B) t), (g : G) ∈ Sec9R0 hc t x ↔ ψ g ∈ H₀ := by
    intro g
    refine ⟨fun hg => ⟨g, hg, rfl⟩, ?_⟩
    rintro ⟨r, hr, hrg⟩
    have h1 := hmemker (r⁻¹ * g) (by rw [map_mul, map_inv, hrg, inv_mul_cancel])
    have e : (g : G) = (r : G) * ((r⁻¹ * g : ↥(Rt M (LB M Q B) t)) : G) := by simp
    rw [e]
    exact (Sec9R0 hc t x).mul_mem hr h1
  have hbot : H₀ ≠ ⊥ := by
    intro hb
    have hx : ψ ⟨x, hxR⟩ ∈ H₀ := (hmem ⟨x, hxR⟩).mp (mem_Sec9R0 hc t hxR)
    rw [hb, Subgroup.mem_bot] at hx
    have : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ ψ.ker := hx
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact hxN this
  have htop : H₀ ≠ ⊤ := by
    intro htop
    apply hlt.ne
    refine le_antisymm hR₀R fun g hg => ?_
    exact (hmem ⟨g, hg⟩).mpr (htop ▸ Subgroup.mem_top _)
  rcases Split92.normal_prod_cases hnonab H₀ hbot htop with h | h
  · exact ⟨K, fK, finK, hch, hK, ψ, hψs, hψk, fun g => (hmem g).trans (h (ψ g))⟩
  · let sw : ↥(StatedSL 2 K) × ↥(StatedSL 2 K) ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
      MulEquiv.prodComm
    refine ⟨K, fK, finK, hch, hK, sw.toMonoidHom.comp ψ, fun p => ?_, ?_,
      fun g => (hmem g).trans ((h (ψ g)).trans ?_)⟩
    · obtain ⟨g, hg⟩ := hψs (sw.symm p)
      exact ⟨g, by simp [hg]⟩
    · rw [← hψk]
      ext g
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply]
      constructor
      · intro h1
        have := congrArg sw.symm h1
        simpa using this
      · intro h1
        rw [h1, map_one]
    · simp [sw]

theorem conj_LB_of_psi (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {S : Type} [Group S]
    (ψ : ↥(Rt M (LB M Q B) t) →* S × S)
    (hψk : ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) {U₁ U₂ : Subgroup S}
    (hprod : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map ψ = U₁.prod U₂)
    (g : ↥(Rt M (LB M Q B) t)) (hg1 : (ψ g).1 = 1)
    (hg2 : (ψ g).2 ∈ Subgroup.normalizer (U₂ : Set S)) :
    conjSubgroup (g : G) (LB M Q B) = LB M Q B := by
  have ht := hs.mem
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hgM : (g : G) ∈ M := hc.Rt_le_M t g.2
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hstep : ∀ l ∈ LB M Q B, ∃ l' ∈ LB M Q B, ∃ m ∈ hc.CN t,
      (g : G)⁻¹ * l * g = l' * m := by
    intro l hl
    set lR : ↥(Rt M (LB M Q B) t) := ⟨l, hLR hl⟩
    have hl' : ψ lR ∈ U₁.prod U₂ := hprod ▸ ⟨lR, hl, rfl⟩
    have hmem : ψ (g⁻¹ * lR * g) ∈ U₁.prod U₂ := by
      rw [map_mul, map_mul, map_inv]
      refine ⟨?_, ?_⟩
      · simpa [hg1] using hl'.1
      · have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (U₂ : Set S)).inv_mem hg2) _).mp hl'.2
        simpa using this
    rw [← hprod] at hmem
    obtain ⟨l', hl'L, hl'e⟩ := hmem
    have hker : l'⁻¹ * (g⁻¹ * lR * g) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hl'e, inv_mul_cancel]
    rw [hψk, Subgroup.mem_subgroupOf] at hker
    refine ⟨l', hl'L, _, hker, ?_⟩
    simp [lR]
  refine hc.conj_LB_eq_of_le_sup_Z hgM fun y hy => ?_
  have hb : (g : G)⁻¹ * y * g ∈ B := mem_conjSubgroup.mp hy
  set b := (g : G)⁻¹ * y * g with hbdef
  have hy' : y = (g : G) * b * (g : G)⁻¹ := by rw [hbdef]; group
  have hbBZ : b ∈ ((B ⊔ Z : Subgroup G) : Set G) := Subgroup.mem_sup_left hb
  rw [← h35] at hbBZ
  have hcq : y ∈ CQt Q Z (LB M Q B) := by
    refine ⟨?_, fun l hl => ?_⟩
    · rw [hy']
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) b).mp hbBZ.1
    · obtain ⟨l', hl'L, m, hm, hlm⟩ := hstep l hl
      have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
      have hmb : ⁅m, b⁆ ∈ Z := (Ctx.mem_CN.mp hm).2 b hbV
      have hl'b : ⁅l', b⁆ ∈ Z := hbBZ.2 l' hl'L
      have hl'M : l' ∈ M := hc.LB_le_M hl'L
      have e : ⁅l, y⁆ = (g : G) * ((l' * ⁅m, b⁆ * l'⁻¹) * ⁅l', b⁆) * (g : G)⁻¹ := by
        have hl2 : l = (g : G) * (l' * m) * (g : G)⁻¹ := by rw [← hlm]; group
        rw [hy', hl2]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hZn _ hgM _ (Z.mul_mem (hZn _ hl'M _ hmb) hl'b)
  rw [h35] at hcq
  exact hcq

theorem split_of_elem (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B)
    (hxN : x ∉ hc.CN t) (hlt : Sec9R0 hc t x < Rt M (LB M Q B) t)
    {g₀ : G} (hg₀R : g₀ ∈ Rt M (LB M Q B) t) (hg₀ : g₀ ∉ Sec9R0 hc t x)
    (hg₀c : ∀ a ∈ Sec9R0 hc t x, ⁅g₀, a⁆ ∈ Q) :
    ∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  set R := Rt M (LB M Q B) t with hRdef
  set R₀ := Sec9R0 hc t x with hR₀def
  set N := hc.CN t with hNdef
  have hxR : x ∈ R := le_Rt (M := M) (LB M Q B) ht hxL
  have hQR : Q ≤ R := hc.Q_le_Rt ht
  have hQR₀ : Q ≤ R₀ := Q_le_Sec9R0 hc ht x
  have hR₀R : R₀ ≤ R := Sec9R0_le_Rt hc hxR
  have hQN : Q ≤ N := sec9_Q_le_CN hc ht
  have hNR : N ≤ R := sec9_CN_le_Rt hc t
  have hRM : R ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ R := le_Rt (M := M) (LB M Q B) ht
  obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk, hψR₀⟩ := factor hc hs hxL hxN hlt
  letI : Fintype K := Fintype.ofFinite K
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  have hqpos : 0 < Nat.card K := Nat.card_pos
  haveI hsimp : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have hnonab : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a :=
    sec9_nonabelian_of_commutator_eq_top
      (statedSL_quasisimple_of_card 2 K le_rfl h4).1.commutator_eq_top
  haveI hQn : (Q.subgroupOf R).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM g.2)) a).mp ha⟩
  set π : ↥R →* ↥R ⧸ Q.subgroupOf R := QuotientGroup.mk' (Q.subgroupOf R) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπeq : ∀ a b : ↥R, π a = π b ↔ ((a⁻¹ * b : ↥R) : G) ∈ Q := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
  have hπone : ∀ a : ↥R, π a = 1 ↔ (a : G) ∈ Q := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQker : Q.subgroupOf R ≤ ψ.ker := by
    rw [hψk]
    intro g hg
    exact hQN hg
  set ψb := QuotientGroup.lift (Q.subgroupOf R) ψ hQker with hψb
  have hψbπ : ∀ g, ψb (π g) = ψ g := fun g => QuotientGroup.lift_mk' _ _ g
  set e := specialLinearGroupEquivStatedSL 2 K with he
  set θ' : (↥R ⧸ Q.subgroupOf R) →* ↥(StatedSL 2 K) := (MonoidHom.snd _ _).comp ψb with hθ'
  set θ : (↥R ⧸ Q.subgroupOf R) →* SL(2, K) := e.symm.toMonoidHom.comp θ' with hθ
  have hθ'π : ∀ g, θ' (π g) = (ψ g).2 := fun g => by simp [hθ', hψbπ]
  have hθπ : ∀ g, θ (π g) = e.symm (ψ g).2 := fun g => by simp [hθ, hθ'π]
  haveI hnormR₀ : (R₀.subgroupOf R).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact Sec9R0_conj_mem hc ht g.2 ha
  set Rb₀ := (R₀.subgroupOf R).map π with hRb₀
  haveI : Rb₀.Normal := Subgroup.Normal.map hnormR₀ π hπs
  have hmemRb₀ : ∀ g : ↥R, π g ∈ Rb₀ ↔ (g : G) ∈ R₀ := by
    intro g
    refine ⟨?_, fun hg => ⟨g, hg, rfl⟩⟩
    rintro ⟨r, hr, hrg⟩
    have h1 : ((r⁻¹ * g : ↥R) : G) ∈ Q := (hπeq r g).mp hrg
    have e1 : (g : G) = (r : G) * ((r⁻¹ * g : ↥R) : G) := by simp
    rw [e1]
    exact R₀.mul_mem hr (hQR₀ h1)
  have hθs : Function.Surjective θ := by
    intro s
    obtain ⟨g, hg⟩ := hψs (1, e s)
    exact ⟨π g, by rw [hθπ, hg]; simp⟩
  have hθker : θ.ker = Rb₀ := by
    ext h
    obtain ⟨g, rfl⟩ := hπs h
    rw [MonoidHom.mem_ker, hθπ, hmemRb₀, hψR₀]
    constructor
    · intro h1
      have := congrArg e h1
      simpa using this
    · intro h1
      rw [h1, map_one]
  have hperf : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4).commutator_eq_top
  have hcen1 : ∀ g : ↥R, π g ∈ Subgroup.centralizer (Rb₀ : Set _) → (ψ g).1 = 1 := by
    intro g hg
    refine Split92.eq_one_of_central hnonab fun u => ?_
    obtain ⟨r, hr⟩ := hψs (u, 1)
    have hrR₀ : π r ∈ Rb₀ := (hmemRb₀ r).mpr ((hψR₀ r).mpr (by rw [hr]))
    have h1 := Subgroup.mem_centralizer_iff.mp hg (π r) hrR₀
    have h2 := congrArg (fun y => (ψb y).1) h1
    simp only [map_mul, hψbπ, Prod.fst_mul, hr] at h2
    exact h2.symm
  set C := Subgroup.centralizer (Rb₀ : Set (↥R ⧸ Q.subgroupOf R)) with hCdef
  haveI : C.Normal := Subgroup.normal_centralizer
  have hg₀C : π ⟨g₀, hg₀R⟩ ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    rintro h ⟨a, ha, rfl⟩
    have hco : ((⁅(⟨g₀, hg₀R⟩ : ↥R), a⁆ : ↥R) : G) = ⁅g₀, (a : G)⁆ := by
      simp [commutatorElement_def]
    have h1 : π ⁅(⟨g₀, hg₀R⟩ : ↥R), a⁆ = 1 :=
      (hπone _).mpr (by rw [hco]; exact hg₀c a (Subgroup.mem_subgroupOf.mp ha))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hθ's : Function.Surjective θ' := fun s => by
    obtain ⟨g, hg⟩ := hψs (1, s)
    exact ⟨π g, by rw [hθ'π, hg]⟩
  have hCθ' : C.map θ' = ⊤ := by
    haveI : (C.map θ').Normal := Subgroup.Normal.map inferInstance θ' hθ's
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map θ') with h | h
    · exfalso
      have hmem : θ' (π ⟨g₀, hg₀R⟩) ∈ C.map θ' := ⟨_, hg₀C, rfl⟩
      rw [h, Subgroup.mem_bot, hθ'π] at hmem
      exact hg₀ ((hψR₀ ⟨g₀, hg₀R⟩).mpr hmem)
    · exact h
  have hcover : C ⊔ Rb₀ = ⊤ := by
    refine eq_top_iff.mpr fun h _ => ?_
    have hmem : θ' h ∈ C.map θ' := hCθ' ▸ Subgroup.mem_top _
    obtain ⟨c, hcC, hch⟩ := hmem
    have hr : c⁻¹ * h ∈ Rb₀ := by
      rw [← hθker, MonoidHom.mem_ker, map_mul, map_inv]
      simp only [hθ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hch,
        inv_mul_cancel]
    rw [show h = c * (c⁻¹ * h) by group]
    exact Subgroup.mul_mem_sup hcC hr
  have hNp : IsPGroup 2 ↥N := Ctx.isPGroup_CN_of_311 h34 hc hs5
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
  have hNbp : IsPGroup 2 ↥((N.subgroupOf R).map π) :=
    (hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNR).symm).map π
  have h2 : IsPGroup 2 ↥(C ⊓ Rb₀) := by
    refine hNbp.to_le fun c hc => ?_
    obtain ⟨g, rfl⟩ := hπs c
    have e1 := hcen1 g hc.1
    have e2 := (hψR₀ g).mp ((hmemRb₀ g).mp hc.2)
    have hker : g ∈ ψ.ker := by rw [MonoidHom.mem_ker]; exact Prod.ext e1 e2
    rw [hψk] at hker
    exact ⟨g, hker, rfl⟩
  set Lb := ((LB M Q B).subgroupOf R).map π with hLb
  have hLcomm : ∀ a ∈ Lb, ∀ b ∈ Lb, a * b = b * a := by
    refine comm_of_mul_self fun a ha => ?_
    obtain ⟨l, hl, rfl⟩ := ha
    rw [← map_mul, hπone]
    have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp hl)
    simpa [pow_two] using this
  have hLp : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hLRp : IsPGroup 2 ↥((LB M Q B).subgroupOf R) :=
    hLp.of_equiv (Subgroup.subgroupOfEquivOfLe hLR).symm
  have hcardψ : Nat.card (((LB M Q B).subgroupOf R).map ψ) = Nat.card K * Nat.card K := by
    rw [← Subgroup.relIndex_ker, hψk, Subgroup.relIndex_subgroupOf hLR,
      HS9.relIndex_LB_CN h34 hs, hK, pow_two]
  obtain ⟨-, hU₂c, hprod⟩ := map_eq_prod_of_card _ hLRp ψ hqpos hcardψ
    (fun U hU => card_le_of_isPGroup_statedSL U hU)
  set U₂ := ((LB M Q B).subgroupOf R).map ((MonoidHom.snd _ _).comp ψ) with hU₂
  have hLbθ : Lb.map θ = U₂.map e.symm.toMonoidHom := by
    rw [hLb, hU₂, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hnorm : ∀ g ∈ C, θ g ∈ Subgroup.normalizer ((Lb.map θ : Subgroup SL(2, K)) : Set SL(2, K)) →
      g ∈ Subgroup.normalizer (Lb : Set (↥R ⧸ Q.subgroupOf R)) := by
    intro c hcC hcn
    obtain ⟨g, rfl⟩ := hπs c
    have e1 := hcen1 g hcC
    have e2 : (ψ g).2 ∈ Subgroup.normalizer (U₂ : Set ↥(StatedSL 2 K)) := by
      rw [hLbθ, hθπ, ← Subgroup.map_equiv_normalizer_eq] at hcn
      obtain ⟨s, hs', hse⟩ := hcn
      have : s = (ψ g).2 := e.symm.injective hse
      rwa [← this]
    have hconj := conj_LB_of_psi h34 hs5 ψ hψk hprod g e1 e2
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨l, hl, rfl⟩ := ha
    have hl' : (g : G) * l * (g : G)⁻¹ ∈ LB M Q B := by
      have : (g : G) * l * (g : G)⁻¹ ∈ conjSubgroup (g : G) (LB M Q B) :=
        mem_conjSubgroup.mpr (by
          rw [show (g : G)⁻¹ * ((g : G) * l * (g : G)⁻¹) * g = l by group]
          exact Subgroup.mem_subgroupOf.mp hl)
      rwa [hconj] at this
    exact ⟨g * l * g⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa using hl'), by simp⟩
  have hUp : IsPGroup 2 ↥(Lb.map θ) := (hLRp.map π).map θ
  have hUc : Nat.card ↥(Lb.map θ) = Nat.card K := by
    rw [hLbθ, Subgroup.card_map_of_injective e.symm.injective, hU₂c]
  have hF : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨d, hd, hfpf, hdodd⟩ := exists_torus hF (Lb.map θ) hUp hUc
  have hUodd : Odd (Lb.map θ).index := by
    have h1 := Subgroup.index_mul_card (Lb.map θ)
    have hcardSL : Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_two]
    rw [hUc, hcardSL, mul_comm (Nat.card K)] at h1
    rw [Nat.eq_of_mul_eq_mul_right hqpos h1]
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    have hq : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
    have hev : Even (Nat.card K ^ 2) := by
      rw [hq, ← pow_mul]
      exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hqpos) hev odd_one
  obtain ⟨Yb, hYbC, hYbsup, hYbinf, hYbbij⟩ :=
    split_abstract Rb₀ θ hθs hθker hperf hcover h2 Lb hLcomm hnorm hd hfpf hdodd hUodd
  set Y : Subgroup G := (Yb.comap π).map R.subtype with hYdef
  have hmemY : ∀ g : ↥R, (g : G) ∈ Y ↔ π g ∈ Yb := by
    intro g
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      rw [← this]
      exact hg'
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hYR : Y ≤ R := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hQY : Q ≤ Y := fun q hq =>
    (hmemY ⟨q, hQR hq⟩).mpr (by rw [(hπone _).mpr hq]; exact Yb.one_mem)
  refine ⟨Y, ⟨hQR₀, hR₀R, hQY, hYR, ?_, ?_, ?_⟩, ?_⟩
  · refine le_antisymm (sup_le hR₀R hYR) fun g hg => ?_
    have hmem : π ⟨g, hg⟩ ∈ Yb ⊔ Rb₀ := hYbsup ▸ Subgroup.mem_top _
    obtain ⟨yb, hyb, rb, hrb, he1⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    obtain ⟨y, rfl⟩ := hπs yb
    obtain ⟨r, hr, rfl⟩ := hrb
    have hq : (((y * r)⁻¹ * ⟨g, hg⟩ : ↥R) : G) ∈ Q := (hπeq _ _).mp (by rw [map_mul, he1])
    have e1 : g = (y : G) * ((r : G) * (((y * r)⁻¹ * ⟨g, hg⟩ : ↥R) : G)) := by
      simp [mul_assoc]
    rw [e1, sup_comm]
    exact Subgroup.mul_mem_sup ((hmemY y).mpr hyb)
      (R₀.mul_mem (Subgroup.mem_subgroupOf.mp hr) (hQR₀ hq))
  · refine le_antisymm (fun g hg => ?_) (le_inf hQR₀ hQY)
    have hgR : g ∈ R := hR₀R hg.1
    have h1 : π ⟨g, hgR⟩ ∈ Yb ⊓ Rb₀ := ⟨(hmemY ⟨g, hgR⟩).mp hg.2, (hmemRb₀ _).mpr hg.1⟩
    rw [hYbinf, Subgroup.mem_bot] at h1
    exact (hπone _).mp h1
  · intro a ha y hy
    have haR := hR₀R ha
    have hyR := hYR hy
    have h1 : π ⟨y, hyR⟩ ∈ C := hYbC ((hmemY ⟨y, hyR⟩).mp hy)
    have h2 := Subgroup.mem_centralizer_iff.mp h1 (π ⟨a, haR⟩) ((hmemRb₀ _).mpr ha)
    have h3 : π ⁅(⟨a, haR⟩ : ↥R), ⟨y, hyR⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h2
    have hco : ((⁅(⟨a, haR⟩ : ↥R), ⟨y, hyR⟩⁆ : ↥R) : G) = ⁅a, y⁆ := by
      simp [commutatorElement_def]
    rw [← hco]
    exact (hπone _).mp h3
  ·
    let f : ↥Y →* SL(2, K) := θ.comp (π.comp (Subgroup.inclusion hYR))
    have hfs : Function.Surjective f := by
      intro s
      obtain ⟨⟨yb, hyb⟩, hybs⟩ := hYbbij.2 s
      obtain ⟨g, rfl⟩ := hπs yb
      exact ⟨⟨g, (hmemY g).mpr hyb⟩, hybs⟩
    have hfker : f.ker = Q.subgroupOf Y := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hyYb : π (Subgroup.inclusion hYR y) ∈ Yb := (hmemY _).mp y.2
      constructor
      · intro hy1
        have h1 : π (Subgroup.inclusion hYR y) ∈ Yb ⊓ Rb₀ := ⟨hyYb, hθker ▸ hy1⟩
        rw [hYbinf, Subgroup.mem_bot] at h1
        exact (hπone _).mp h1
      · intro hyQ
        have h1 : π (Subgroup.inclusion hYR y) = 1 := (hπone _).mpr hyQ
        show θ (π (Subgroup.inclusion hYR y)) = 1
        rw [h1, map_one]
    haveI hnQY : (Q.subgroupOf Y).Normal := hfker ▸ f.normal_ker
    refine ⟨hnQY, K, fK, finK, hK, ⟨?_⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)).trans e

end Split92

end CFSG.RankThree.GF2n.Stroth80
