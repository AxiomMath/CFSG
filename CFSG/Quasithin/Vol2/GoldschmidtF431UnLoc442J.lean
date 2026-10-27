module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442G
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442I

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin

section Core


variable {G : Type} [Group G] [Finite G] {X Y V U R K P : Subgroup G} {z t : G}

theorem Loc442UCore.le (D : Loc442UCore X Y V U R K P z t) : Y ≤ X := by
  by_contra hYX
  obtain ⟨W, hW, hmax⟩ := D.exists_maximal hYX
  rcases hW.2.1.eq_or_lt with h | h
  · rw [h] at hW
    exact D.false_of_eq hW.2.2
  · exact D.false_of_lt hW.1 h hW.2.2 hmax

end Core

section Transport

variable {Mb : Type*} [Group Mb] {G : Type*} [Group G] {N : Subgroup Mb} {b : ↥N →* G}

theorem img_ne_one (hb : Function.Injective b) {a : Mb} (ha : a ∈ N) (h : a ≠ 1) :
    b ⟨a, ha⟩ ≠ 1 := fun h1 =>
  h (congrArg Subtype.val (hb (h1.trans (map_one b).symm)))

theorem img_eq_iff (hb : Function.Injective b) {a c : Mb} (ha : a ∈ N) (hc : c ∈ N) :
    b ⟨a, ha⟩ = b ⟨c, hc⟩ ↔ a = c :=
  ⟨fun h => congrArg Subtype.val (hb h), fun h => by subst h; rfl⟩

theorem isSolvable_subImg_iff (hb : Function.Injective b) {A : Subgroup Mb} (hA : A ≤ N) :
    Group.IsSolvable ↥(subImg b A) ↔ Group.IsSolvable ↥A := by
  let e : ↥A ≃* ↥(subImg b A) :=
    (Subgroup.subgroupOfEquivOfLe hA).symm.trans (Subgroup.equivMapOfInjective _ b hb)
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem nonsolv_img (hb : Function.Injective b) {C Vb Ub : Subgroup Mb} (hCN : C ≤ N)
    (hVN : Vb ≤ N)
    (h : ∃ L : Subgroup Mb, L ≤ C ∧ ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup Mb, L' ≤ L →
      (∀ x ∈ L', ∀ v ∈ Vb, x * v * x⁻¹ * v⁻¹ ∈ Ub) → Group.IsSolvable ↥L') :
    ∃ L : Subgroup G, L ≤ subImg b C ∧ ¬ Group.IsSolvable ↥L ∧ ∀ L' : Subgroup G, L' ≤ L →
      (∀ x ∈ L', ∀ v ∈ subImg b Vb, x * v * x⁻¹ * v⁻¹ ∈ subImg b Ub) →
        Group.IsSolvable ↥L' := by
  obtain ⟨L, hLC, hLns, hL⟩ := h
  refine ⟨subImg b L, subImg_mono b hLC, fun hs => hLns ((isSolvable_subImg_iff hb
    (hLC.trans hCN)).mp hs), fun L' hL' hcond => ?_⟩
  obtain ⟨A, hAL, rfl⟩ := exists_preimage hb hL'
  have hAN : A ≤ N := hAL.trans (hLC.trans hCN)
  refine (isSolvable_subImg_iff hb hAN).mpr (hL A hAL fun x hx v hv => ?_)
  have hxN : x ∈ N := hAN hx
  have hvN : v ∈ N := hVN hv
  have hm : x * v * x⁻¹ * v⁻¹ ∈ N := N.mul_mem (N.mul_mem (N.mul_mem hxN hvN) (N.inv_mem hxN))
    (N.inv_mem hvN)
  have h1 := hcond (b ⟨x, hxN⟩) (mem_subImg_of_mem b hxN hx) (b ⟨v, hvN⟩)
    (mem_subImg_of_mem b hvN hv)
  have h2 : b ⟨x, hxN⟩ * b ⟨v, hvN⟩ * (b ⟨x, hxN⟩)⁻¹ * (b ⟨v, hvN⟩)⁻¹ =
      b ⟨x * v * x⁻¹ * v⁻¹, hm⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [h2] at h1
  exact (mem_subImg_iff_of_injective hb hm).mp h1

end Transport

end CFSG.Quasithin.H13.F431.Un
