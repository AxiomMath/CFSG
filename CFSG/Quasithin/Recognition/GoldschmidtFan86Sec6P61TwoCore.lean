module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Swap
public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeDef
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P61

open P514

theorem sq_comm_of_conj_eq {x u : G} (h : x * u * x⁻¹ = x⁻¹ * u * x) :
    (x * x) * u = u * (x * x) := by
  have h1 : x * (x * u * x⁻¹) * x⁻¹ = x * (x⁻¹ * u * x) * x⁻¹ := by rw [h]
  have h3 : x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
  have h4 : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
  rw [h3, h4] at h1
  calc x * x * u = x * x * u * (x * x)⁻¹ * (x * x) := by group
    _ = u * (x * x) := by rw [h1]

theorem fix_mid (F : FanTree Γ G) {v₁ v₂ v₃ : V} (h₂ : Γ.Adj v₁ v₂) (h₃ : Γ.Adj v₂ v₃)
    (hn : v₁ ≠ v₃) {g : G} (hg₁ : g • v₁ = v₁) (hg₃ : g • v₃ = v₃) : g • v₂ = v₂ := by
  have e₁ : Γ.Adj v₁ (g • v₂) := by
    have := (F.adj_smul g v₁ v₂).2 h₂
    rwa [hg₁] at this
  have e₃ : Γ.Adj v₃ (g • v₂) := by
    have := (F.adj_smul g v₃ v₂).2 h₃.symm
    rwa [hg₃] at this
  exact common_nbr_unique F.isTree hn e₁ e₃ h₂ h₃.symm

theorem two_fix_prod (F : FanTree Γ G) {z : G} {α o : V} (C : LblCtx Γ z α o) {v₁ v₂ v₃ : V}
    (h₁ : Γ.Adj o v₁) (h₂ : Γ.Adj v₁ v₂) (h₃ : Γ.Adj v₂ v₃)
    (hM : ∀ u, Γ.Adj o u → Lb z α u ∈ nbrStab Γ G v₁) {p q : V} (hp : Γ.Adj o p)
    (hq : Γ.Adj o q) (hpq : Lb z α p • v₃ = v₃ ↔ Lb z α q • v₃ = v₃) :
    (Lb z α p * Lb z α q) • v₃ = v₃ := by
  by_cases hfp : Lb z α p • v₃ = v₃
  · rw [mul_smul, (hpq.1 hfp), hfp]
  · have hfq : ¬ Lb z α q • v₃ = v₃ := fun h => hfp (hpq.2 h)
    have key : ∀ u, Γ.Adj o u → Lb z α u ∈
        MulAction.stabilizer G v₂ ⊓ MulAction.stabilizer G v₁ := fun u hu => by
      refine ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 (hM u hu) v₂ h₂),
        MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1
          (Lb_mem_nbrStab F C.cinv C.ball C.adj hu) v₁ h₁)⟩
    have hnot : ∀ u, Γ.Adj o u → ¬ Lb z α u • v₃ = v₃ → Lb z α u ∉ nbrStab Γ G v₂ :=
      fun u hu hmove hmem => hmove (mem_nbrStab.1 hmem v₃ h₃)
    have hsq : ∀ u, Γ.Adj o u → Lb z α u * Lb z α u ∈ nbrStab Γ G v₂ := fun u hu => by
      rw [C.sq F hu]
      exact Subgroup.one_mem _
    have := P62.mul_mem_nbrStab_of_sq_mem F h₂.symm (key p hp) (key q hq) (hsq p hp) (hsq q hq)
      (hnot p hp hfp) (hnot q hq hfq)
    exact mem_nbrStab.1 this v₃ h₃

theorem r2_core (F : FanTree Γ G) {z : G} {α o : V} (C : LblCtx Γ z α o) {v₁ v₂ v₃ : V}
    (h₁ : Γ.Adj o v₁) (h₂ : Γ.Adj v₁ v₂) (h₃ : Γ.Adj v₂ v₃) (hn₂ : v₁ ≠ v₃) {t : G}
    (ht2 : t * t = 1) (hto : t • o = o) (htK : t ∉ nbrStab Γ G o) (ht₁ : t • v₁ = v₁)
    (htc : ∀ h : G, h • v₂ = v₂ → h • v₃ = v₃ → h * t = t * h)
    (hM : ∀ u, Γ.Adj o u → Lb z α u ∈ nbrStab Γ G v₁) : False := by
  classical
  have hv5 : valence Γ o = 5 := C.v5
  obtain ⟨x₁, hx₁, hx₁o⟩ := F.exists_orderOf_eq_valence o
  obtain ⟨x, hx, hxo, hinv⟩ := F.exists_inverted (MulAction.mem_stabilizer_iff.2 hto) ht2
    ⟨v₁, h₁, ht₁⟩ htK hx₁ hx₁o
  rw [hv5] at hxo
  have hxo' : x • o = o := MulAction.mem_stabilizer_iff.1 hx
  have hnbr : ∀ u, Γ.Adj o u → Γ.Adj o (x⁻¹ • u) := fun u hu => by
    have := (F.adj_smul x⁻¹ o u).2 hu
    rwa [inv_smul_eq_iff.2 hxo'.symm] at this
  have hN : (finite_nbr hv5).toFinset.card = 5 := by
    rw [← Set.ncard_eq_toFinset_card _ (finite_nbr hv5)]
    exact ncard_nbr hv5
  obtain ⟨p, hpN, q, hqN, hpq, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (finite_nbr hv5).toFinset) (t := (Finset.univ : Finset (Bool × Bool)))
    (f := fun u => (decide (Lb z α u • v₃ = v₃), decide (Lb z α (x⁻¹ • u) • v₃ = v₃)))
    (by rw [hN]; simp) (fun _ _ => Finset.mem_univ _)
  have hp : Γ.Adj o p := (Set.Finite.mem_toFinset _).1 hpN
  have hq : Γ.Adj o q := (Set.Finite.mem_toFinset _).1 hqN
  have hf1 : Lb z α p • v₃ = v₃ ↔ Lb z α q • v₃ = v₃ := by
    have := (Prod.ext_iff.1 hf).1
    simpa using this
  have hf2 : Lb z α (x⁻¹ • p) • v₃ = v₃ ↔ Lb z α (x⁻¹ • q) • v₃ = v₃ := by
    have := (Prod.ext_iff.1 hf).2
    simpa using this
  set u₀ := Lb z α p * Lb z α q with hu₀
  have hfix₀ : u₀ • v₃ = v₃ := two_fix_prod F C h₁ h₂ h₃ hM hp hq hf1
  have hu₁eq : x⁻¹ * u₀ * x = Lb z α (x⁻¹ • p) * Lb z α (x⁻¹ • q) := by
    have e1 := Lb_conj C.cinv (C.conj_ex F hp) x⁻¹
    have e2 := Lb_conj C.cinv (C.conj_ex F hq) x⁻¹
    rw [inv_inv] at e1 e2
    rw [hu₀, ← e1, ← e2]
    group
  have hfix₁ : (x⁻¹ * u₀ * x) • v₃ = v₃ := by
    rw [hu₁eq]
    exact two_fix_prod F C h₁ h₂ h₃ hM (hnbr p hp) (hnbr q hq) hf2
  have hfixo : ∀ u u', Γ.Adj o u → Γ.Adj o u' → (Lb z α u * Lb z α u') • v₁ = v₁ := by
    intro u u' hu hu'
    rw [mul_smul, mem_nbrStab.1 (Lb_mem_nbrStab F C.cinv C.ball C.adj hu') v₁ h₁,
      mem_nbrStab.1 (Lb_mem_nbrStab F C.cinv C.ball C.adj hu) v₁ h₁]
  have hc₀ : u₀ * t = t * u₀ :=
    htc u₀ (fix_mid F h₂ h₃ hn₂ (hfixo p q hp hq) hfix₀) hfix₀
  have hc₁ : (x⁻¹ * u₀ * x) * t = t * (x⁻¹ * u₀ * x) := by
    refine htc _ (fix_mid F h₂ h₃ hn₂ ?_ hfix₁) hfix₁
    rw [hu₁eq]
    exact hfixo _ _ (hnbr p hp) (hnbr q hq)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [hti] at hinv
  have htx : t * x = x⁻¹ * t := by
    calc t * x = t * x * t * t := by rw [mul_assoc (t * x) t t, ht2, mul_one]
      _ = x⁻¹ * t := by rw [hinv]
  have h3 : t * x⁻¹ * t = x := by
    calc t * x⁻¹ * t = t * (t * x * t) * t := by rw [hinv]
      _ = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; simp
  have htx' : t * x⁻¹ = x * t := by
    calc t * x⁻¹ = t * x⁻¹ * t * t := by rw [mul_assoc (t * x⁻¹) t t, ht2, mul_one]
      _ = x * t := by rw [h3]
  have hsq : x * u₀ * x⁻¹ = x⁻¹ * u₀ * x := by
    have h1 : t * (x⁻¹ * u₀ * x) = x * u₀ * x⁻¹ * t := by
      calc t * (x⁻¹ * u₀ * x) = (t * x⁻¹) * u₀ * x := by group
        _ = x * (t * u₀) * x := by rw [htx']; group
        _ = x * (u₀ * t) * x := by rw [← hc₀]
        _ = x * u₀ * (t * x) := by group
        _ = x * u₀ * (x⁻¹ * t) := by rw [htx]
        _ = x * u₀ * x⁻¹ * t := by group
    exact (mul_right_cancel (hc₁.trans h1)).symm
  have hcomm2 : (x * x) * u₀ = u₀ * (x * x) := sq_comm_of_conj_eq hsq
  have hx5 : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxe : x = (x * x) ^ 3 := by
    rw [← pow_two, ← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hx5, one_mul]
  have hcomm : x * u₀ = u₀ * x := by
    have h6 := (Commute.pow_left (show Commute (x * x) u₀ from hcomm2) 3).eq
    rw [← hxe] at h6
    exact h6
  exact not_comm_five F C hxo hx hp hq hpq hcomm

end P61

end CFSG.Quasithin.Fan86
