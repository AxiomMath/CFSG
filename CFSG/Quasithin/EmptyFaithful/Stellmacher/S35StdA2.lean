module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35StdA1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_edge_not_Qv (hS : Sit H M S) {l β : Geo H M} (hβ : β ∈ nbrs l)
    {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hs : Function.Surjective ψ) (hψ : IsRed l ψ) :
    ∃ a ∈ stab l ⊓ stab β, a ∉ Qv l := by
  by_contra hcon
  push Not at hcon
  have hker : ψ.ker = (stab l ⊓ stab β).subgroupOf (stab l) := by
    ext x
    rw [MonoidHom.mem_ker, hψ x, Subgroup.mem_subgroupOf]
    exact ⟨fun h => Qv_le_edge hS.glob.amalg hβ h, fun h => hcon _ h⟩
  have hodd := (sylow_stab_inf_left hS.glob.amalg hβ).2.2
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top,
    card_perm3] at hodd
  exact hodd (by norm_num)

theorem centerOf_stab_bot (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    centerOf (stab l) = ⊥ := by
  obtain ⟨β, δ, δ', hn, -⟩ := nbrs_S3 hS hl
  have hβ : β ∈ nbrs l := by rw [hn]; simp
  exact centerOf_eq_bot_of_Zv_central hS.glob.amalg (mem_nbrs_symm.mp hβ)
    (hS.glob.central β (vtype_nbr_S3 hl hβ))

omit [Finite G] in
theorem commute_of_words {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)}
    (hψ : IsRed l ψ) {a b e : G} (ha : a ∈ stab l) (hb : b ∈ stab l)
    (h1 : ψ ⟨a, ha⟩ * ψ ⟨a, ha⟩ = 1) (h2 : ψ ⟨b, hb⟩ * ψ ⟨b, hb⟩ = 1)
    (h1' : ψ ⟨a, ha⟩ ≠ 1) (h2' : ψ ⟨b, hb⟩ ≠ 1) (h12 : ψ ⟨a, ha⟩ ≠ ψ ⟨b, hb⟩)
    (hea : Commute e a) (heb : Commute e b) (heq : ∀ q ∈ Qv l, Commute e q) :
    ∀ g ∈ stab l, Commute e g := by
  intro g hg
  have hw := perm3_words _ _ (ψ ⟨g, hg⟩) h1 h2 h1' h2' h12
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have key : ∃ (g₀ : G) (h₀ : g₀ ∈ stab l), Commute e g₀ ∧ ψ ⟨g₀, h₀⟩ = ψ ⟨g, hg⟩ := by
    rcases hw with h | h | h | h | h | h
    · exact ⟨1, Subgroup.one_mem _, Commute.one_right e, by rw [h]; exact map_one ψ⟩
    · exact ⟨a, ha, hea, h.symm⟩
    · exact ⟨b, hb, heb, h.symm⟩
    · exact ⟨a * b, Subgroup.mul_mem _ ha hb, hea.mul_right heb,
        (map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩).trans h.symm⟩
    · exact ⟨b * a, Subgroup.mul_mem _ hb ha, heb.mul_right hea,
        (map_mul ψ ⟨b, hb⟩ ⟨a, ha⟩).trans h.symm⟩
    · exact ⟨a * b * a, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha,
        (hea.mul_right heb).mul_right hea,
        ((map_mul ψ (⟨a, ha⟩ * ⟨b, hb⟩) ⟨a, ha⟩).trans
          (congrArg (· * ψ ⟨a, ha⟩) (map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩))).trans h.symm⟩
  obtain ⟨g₀, h₀, hc₀, hp⟩ := key
  have hmem : g₀⁻¹ * g ∈ stab l := Subgroup.mul_mem _ (Subgroup.inv_mem _ h₀) hg
  have hq : g₀⁻¹ * g ∈ Qv l := by
    refine (hψ ⟨g₀⁻¹ * g, hmem⟩).mp ?_
    have : (⟨g₀⁻¹ * g, hmem⟩ : ↥(stab l)) = ⟨g₀, h₀⟩⁻¹ * ⟨g, hg⟩ := rfl
    rw [this, map_mul, map_inv, hp, inv_mul_cancel]
  have := hc₀.mul_right (heq _ hq)
  rwa [mul_inv_cancel_left] at this

omit [Finite G] in
theorem conj_fixed {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ)
    {c : G} (hc : c ∈ stab l) (hc3 : ψ ⟨c, hc⟩ * ψ ⟨c, hc⟩ * ψ ⟨c, hc⟩ = 1) {t : G}
    (ht : t ∈ stab l) {y : G} (hy : InY l y) (hfix : c * y * c⁻¹ = y) :
    c * (t * y * t⁻¹) * c⁻¹ = t * y * t⁻¹ := by
  have hg : t⁻¹ * c * t ∈ stab l :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hc) ht
  have hcases := perm3_conj_cases (ψ ⟨c, hc⟩) (ψ ⟨t, ht⟩) hc3
  have e : c * (t * y * t⁻¹) * c⁻¹ = t * ((t⁻¹ * c * t) * y * (t⁻¹ * c * t)⁻¹) * t⁻¹ := by
    group
  rw [e]
  have hmap : ψ ⟨t⁻¹ * c * t, hg⟩ = (ψ ⟨t, ht⟩)⁻¹ * ψ ⟨c, hc⟩ * ψ ⟨t, ht⟩ := by
    have : (⟨t⁻¹ * c * t, hg⟩ : ↥(stab l)) = ⟨t, ht⟩⁻¹ * ⟨c, hc⟩ * ⟨t, ht⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
  rcases hcases with h | h
  · rw [conj_eq_of_psi hψ hg hc (hmap.trans h) hy, hfix]
  · have hci : c⁻¹ ∈ stab l := Subgroup.inv_mem _ hc
    have hmap' : ψ ⟨t⁻¹ * c * t, hg⟩ = ψ ⟨c⁻¹, hci⟩ := by
      have : (⟨c⁻¹, hci⟩ : ↥(stab l)) = ⟨c, hc⟩⁻¹ := rfl
      rw [hmap, h, this, map_inv]
    rw [conj_eq_of_psi hψ hg hci hmap' hy]
    calc t * (c⁻¹ * y * c⁻¹⁻¹) * t⁻¹ = t * (c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹) * t⁻¹ := by
          rw [hfix]
      _ = t * y * t⁻¹ := by group

theorem fixed_trivial (hS : Sit H M S) {l β : Geo H M} (hl : vtype l = true)
    (hβ : β ∈ nbrs l) {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ) {a b : G}
    (ha : a ∈ stab l ⊓ stab β) (hb : b ∈ stab l)
    (h1 : ψ ⟨a, ha.1⟩ * ψ ⟨a, ha.1⟩ = 1) (h2 : ψ ⟨b, hb⟩ * ψ ⟨b, hb⟩ = 1)
    (h1' : ψ ⟨a, ha.1⟩ ≠ 1) (h2' : ψ ⟨b, hb⟩ ≠ 1) (h12 : ψ ⟨a, ha.1⟩ ≠ ψ ⟨b, hb⟩)
    {e : G} (he : InY l e) (hfix : (a * b) * e * (a * b)⁻¹ = e) : e = 1 := by
  by_contra hne
  have hc : a * b ∈ stab l := Subgroup.mul_mem _ ha.1 hb
  have hc3 : ψ ⟨a * b, hc⟩ * ψ ⟨a * b, hc⟩ * ψ ⟨a * b, hc⟩ = 1 := by
    have hm : ψ ⟨a * b, hc⟩ = ψ ⟨a, ha.1⟩ * ψ ⟨b, hb⟩ := map_mul ψ ⟨a, ha.1⟩ ⟨b, hb⟩
    rw [hm]
    exact (perm3_two_involutions _ _ h1 h2 h1' h2' h12).1
  let F : Subgroup G :=
    { carrier := {y | InY l y ∧ (a * b) * y * (a * b)⁻¹ = y}
      one_mem' := ⟨InY.one l, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨hx.1.mul hy.1, by
        calc (a * b) * (x * y) * (a * b)⁻¹
            = ((a * b) * x * (a * b)⁻¹) * ((a * b) * y * (a * b)⁻¹) := by group
          _ = x * y := by rw [hx.2, hy.2]⟩
      inv_mem' := fun {x} hx => ⟨hx.1.inv, by
        calc (a * b) * x⁻¹ * (a * b)⁻¹ = ((a * b) * x * (a * b)⁻¹)⁻¹ := by group
          _ = x⁻¹ := by rw [hx.2]⟩ }
  have hT2 := (sylow_stab_inf_left hS.glob.amalg hβ).2.1
  have hFT : F ≤ stab l ⊓ stab β := fun y hy => Qv_le_edge hS.glob.amalg hβ hy.1.1
  have hnorm : ∀ t ∈ stab l, ∀ y ∈ F, t * y * t⁻¹ ∈ F := fun t ht y hy =>
    ⟨hy.1.conj hψ ht, conj_fixed hψ hc hc3 ht hy.1 hy.2⟩
  have hTn : stab l ⊓ stab β ≤ Subgroup.normalizer (F : Set G) := fun t ht =>
    F53B3.O1.mem_normalizer_of_conj (fun n hn => hnorm t ht.1 n hn)
      (fun n hn => by simpa using hnorm t⁻¹ (Subgroup.inv_mem _ ht.1) n hn)
  have hFne : F ≠ ⊥ := by
    intro h
    have : e ∈ F := ⟨he, hfix⟩
    rw [h, Subgroup.mem_bot] at this
    exact hne this
  obtain ⟨⟨e', he'⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (F53B3.O1.inf_centralizer_ne_bot_of_normalized hT2 hFT hTn hFne)
  obtain ⟨heF, heC⟩ := Subgroup.mem_inf.mp he'
  have hcomT : ∀ t ∈ stab l ⊓ stab β, Commute e' t := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp heC t ht).symm
  have hea : Commute e' a := hcomT a ha
  have hbc : Commute e' b := by
    have hce : (a * b) * e' * (a * b)⁻¹ = e' := heF.2
    have h3 : a * (b * e' * b⁻¹) * a⁻¹ = e' :=
      calc a * (b * e' * b⁻¹) * a⁻¹ = (a * b) * e' * (a * b)⁻¹ := by group
        _ = e' := hce
    have h4 : b * e' * b⁻¹ = e' :=
      calc b * e' * b⁻¹ = a⁻¹ * (a * (b * e' * b⁻¹) * a⁻¹) * a := by group
        _ = a⁻¹ * e' * a := by rw [h3]
        _ = e' := by rw [mul_assoc, hea.eq, inv_mul_cancel_left]
    exact (mul_inv_eq_iff_eq_mul.mp h4).symm
  have hall := commute_of_words hψ ha.1 hb h1 h2 h1' h2' h12 hea hbc
    (fun q hq => hcomT q (Qv_le_edge hS.glob.amalg hβ hq))
  have hmem : e' ∈ centerOf (stab l) :=
    ⟨pCoreOf_le 2 _ heF.1.1, Subgroup.mem_centralizer_iff.mpr fun g hg => (hall g hg).eq.symm⟩
  rw [centerOf_stab_bot hS hl] at hmem
  exact he1 (Subtype.ext (Subgroup.mem_bot.mp hmem))

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin
