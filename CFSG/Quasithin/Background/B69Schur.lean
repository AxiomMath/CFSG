module

public import CFSG.Quasithin.Background.B1MoreIrr
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V]

theorem trivial_of_sq_one_commute (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {g : MulAut V} (hgL : ∀ l ∈ L, g * l = l * g)
    (hgW : ∀ w ∈ W, g w ∈ W) (hg2 : ∀ w ∈ W, g (g w) = w) : ∀ w ∈ W, g w = w := by
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  let F : V →* V := g.toMonoidHom * (MonoidHom.id V)⁻¹
  have hF : ∀ v, F v = g v * v⁻¹ := fun v => rfl
  have hsq : ∀ v : V, v * v = 1 := fun v => by simpa [pow_two] using hV v
  have hFW : ∀ w ∈ W, F w ∈ W := fun w hw => by
    rw [hF]
    exact W.mul_mem (hgW w hw) (W.inv_mem hw)
  have hFF : ∀ w ∈ W, F (F w) = 1 := by
    intro w hw
    rw [hF, hF, map_mul, map_inv, hg2 w hw, mul_inv_rev, inv_inv]
    have h1 := hsq w
    have h2 := hsq (g w)
    calc w * (g w)⁻¹ * (w * (g w)⁻¹) = (w * w) * ((g w * g w)⁻¹) := by
          rw [mul_inv_rev]; ac_rfl
      _ = 1 := by rw [h1, h2]; simp
  have hFL : ∀ l ∈ L, ∀ w : V, F (l w) = l (F w) := by
    intro l hl w
    have h1 : g (l w) = l (g w) := congrArg (fun x : MulAut V => x w) (hgL l hl)
    rw [hF, hF, h1, map_mul, map_inv]
  set C : Subgroup V := W ⊓ fixV L with hC
  set Imf : Subgroup V := W.map F with hImf
  have hFC : ∀ c ∈ C, F c ∈ C := by
    intro c hc
    refine ⟨hFW c hc.1, fun l hl => ?_⟩
    rw [← hFL l hl, hc.2 l hl]
  have hJinv : ∀ x ∈ L, ∀ w ∈ C ⊔ Imf, x w ∈ C ⊔ Imf := by
    intro x hx w hw
    obtain ⟨c, hc, i, hi, rfl⟩ := Subgroup.mem_sup.1 hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hi
    rw [map_mul, hc.2 x hx, ← hFL x hx w']
    exact Subgroup.mul_mem_sup hc (Subgroup.mem_map.2 ⟨x w', hinv x hx w' hw', rfl⟩)
  have hJW : C ⊔ Imf ≤ W := sup_le inf_le_left (by
    rintro _ ⟨w, hw, rfl⟩
    exact hFW w hw)
  have hImC : Imf ≤ C := by
    rcases hirr (C ⊔ Imf) hJinv le_sup_left hJW with hJ | hJ
    · exact le_sup_right.trans hJ.le
    · exfalso
      have hImC' : Imf ≤ C := by
        rintro _ ⟨w, hw, rfl⟩
        have hwJ : w ∈ C ⊔ Imf := by rw [hJ]; exact hw
        obtain ⟨c, hc, i, hi, rfl⟩ := Subgroup.mem_sup.1 hwJ
        obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hi
        rw [map_mul, hFF w' hw', mul_one]
        exact hFC c hc
      have : C ⊔ Imf = C := sup_eq_left.2 hImC'
      rw [this] at hJ
      rw [hJ] at hlt
      exact lt_irrefl _ hlt
  have hker : commSub W L ≤ F.ker := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hFL x hx w]
    have h1 : F w ∈ fixV L := (hImC (Subgroup.mem_map.2 ⟨w, hw, rfl⟩)).2
    rw [h1 x hx, mul_inv_cancel]
  intro w hw
  have hw' : w ∈ commSub W L := by rw [hcomm]; exact hw
  have := MonoidHom.mem_ker.1 (hker hw')
  rw [hF, mul_inv_eq_one] at this
  exact this

theorem trivial_of_perfect_commute [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L K : Subgroup (MulAut V)}
    {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hKperf : Group.IsPerfect ↥K)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hKW : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W) :
    ∀ k ∈ K, ∀ w ∈ W, k w = w := by
  classical
  have hKst : K ≤ stabSub W := B1.le_stabSub_of_invariant hKW
  have : Finite (MulAut ↥W) := MulEquiv.finite_left
  let f : ↥K →* ↥(autSub K W) :=
    ((resHom W).subgroupMap (K.subgroupOf (stabSub W))).comp
      (Subgroup.subgroupOfEquivOfLe hKst).symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((resHom W).subgroupMap_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKst).symm.surjective
  have hfapp : ∀ (k : ↥K) (w : ↥W), (((f k : ↥(autSub K W)) : MulAut ↥W) w : V) = (k : MulAut V) w :=
    fun k w => rfl
  have hPperf : Group.IsPerfect ↥(autSub K W) := Group.IsPerfect.ofSurjective hf
  by_contra hcon
  push Not at hcon
  obtain ⟨k₁, hk₁, w₁, hw₁, hne⟩ := hcon
  have hnt : Nontrivial ↥(autSub K W) := by
    refine ⟨⟨f ⟨k₁, hk₁⟩, 1, fun h => hne ?_⟩⟩
    have := congrArg (fun φ : ↥(autSub K W) => (((φ : MulAut ↥W) ⟨w₁, hw₁⟩ : ↥W) : V)) h
    simpa [hfapp] using this
  have hnsolv : ¬ Group.IsSolvable ↥(autSub K W) := Group.IsPerfect.not_isSolvable _
  have hnodd : ¬ Odd (Nat.card ↥(autSub K W)) := fun hodd => hnsolv (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have h2 : 2 ∣ Nat.card ↥(autSub K W) := by
    rcases Nat.even_or_odd (Nat.card ↥(autSub K W)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hnodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨k, rfl⟩ := hf φ
  have hk2 : ∀ w ∈ W, (k : MulAut V) ((k : MulAut V) w) = w := by
    intro w hw
    have h1 : (f k) ^ 2 = 1 := by rw [← hφ]; exact pow_orderOf_eq_one _
    have h3 := congrArg (fun φ : ↥(autSub K W) => (((φ : MulAut ↥W) ⟨w, hw⟩ : ↥W) : V)) h1
    simpa [pow_two, hfapp] using h3
  have htriv := trivial_of_sq_one_commute hV hW (g := (k : MulAut V)) (fun l hl => hKL k k.2 l hl)
    (fun w hw => hKW k k.2 w hw) hk2
  have h1 : f k = 1 := by
    apply Subtype.ext
    ext w
    exact htriv w w.2
  rw [h1, orderOf_one] at hφ
  omega

end B69

end CFSG.Quasithin
