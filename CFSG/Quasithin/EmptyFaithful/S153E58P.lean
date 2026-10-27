module

public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.EmptyFaithful.S153E57F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section Pairing

variable {G : Type} [Group G]

open scoped Classical in
theorem ite_mul_of_card_two {Z : Subgroup G} (hZ : Nat.card ↥Z = 2) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z) :
    (if a * b = 1 then (0 : ZMod 2) else 1) = (if a = 1 then 0 else 1) + (if b = 1 then 0 else 1) := by
  by_cases ha1 : a = 1
  · simp [ha1]
  by_cases hb1 : b = 1
  · simp [hb1]
  have hab : a = b := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).1 hZ
    have h1 : (⟨a, ha⟩ : ↥Z) = y := hy _ (fun h => ha1 (congrArg Subtype.val h))
    have h2 : (⟨b, hb⟩ : ↥Z) = y := hy _ (fun h => hb1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hsq : a * a = 1 := by
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨a, ha⟩)
    rw [hZ, pow_two] at h
    exact congrArg Subtype.val h
  rw [← hab]
  simp [ha1, hsq]
  decide

open scoped Classical in
theorem ite_congr_eq {c c' : G} (h : c = c') :
    (if c = 1 then (0 : ZMod 2) else 1) = (if c' = 1 then 0 else 1) := by
  subst h
  rfl

end Pairing

section Form

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem commutator_mem_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {x u : G} (hx : x ∈ UH153 T M V₁ Mc)
    (hu : u ∈ UH153 T M V₁ Mc) : ⁅x, u⁆ ∈ quasithinOmegaOneCenter T := by
  have := cx.hF.commutator_mem_V₁ (S153E.U_le_Q cx hx) hu
  simpa [commutatorElement_def] using this

theorem comm153_mul_left (cx : Ctx15350 T Mc M V₁ V₂ t) {x₁ x₂ u : G} (h₁ : x₁ ∈ UH153 T M V₁ Mc)
    (h₂ : x₂ ∈ UH153 T M V₁ Mc) (hu : u ∈ UH153 T M V₁ Mc) :
    comm153 (x₁ * x₂) u = comm153 x₁ u + comm153 x₂ u := by
  have e := cx.hF.commutator_mul_left (S153E.U_le_Q cx h₁) (S153E.U_le_Q cx h₂) hu
  have m₁ := commutator_mem_Z cx h₁ hu
  have m₂ := commutator_mem_Z cx h₂ hu
  simp only [commutatorElement_def] at m₁ m₂
  unfold comm153
  simp only [commutatorElement_def]
  exact (ite_congr_eq e).trans (ite_mul_of_card_two (Z_card cx) m₁ m₂)

theorem comm153_mul_right (cx : Ctx15350 T Mc M V₁ V₂ t) {x u₁ u₂ : G} (hx : x ∈ UH153 T M V₁ Mc)
    (h₁ : u₁ ∈ UH153 T M V₁ Mc) (h₂ : u₂ ∈ UH153 T M V₁ Mc) :
    comm153 x (u₁ * u₂) = comm153 x u₁ + comm153 x u₂ := by
  have e := cx.hF.commutator_mul_right (S153E.U_le_Q cx hx) h₁ h₂
  have m₁ := commutator_mem_Z cx hx h₁
  have m₂ := commutator_mem_Z cx hx h₂
  simp only [commutatorElement_def] at m₁ m₂
  unfold comm153
  simp only [commutatorElement_def]
  exact (ite_congr_eq e).trans (ite_mul_of_card_two (Z_card cx) m₁ m₂)

omit [Finite G] in
theorem comm153_symm (u v : G) : comm153 u v = comm153 v u := by
  unfold comm153
  have h : ⁅u, v⁆ = 1 ↔ ⁅v, u⁆ = 1 := by
    rw [← commutatorElement_inv, inv_eq_one]
  by_cases hc : ⁅u, v⁆ = 1
  · have h' : ⁅v, u⁆ = 1 := h.1 hc
    simp [hc, h']
  · have h' : ¬ ⁅v, u⁆ = 1 := fun h' => hc (h.2 h')
    simp [hc, h']

theorem comm153_conj (cx : Ctx15350 T Mc M V₁ V₂ t) {k u v : G} (hk : k ∈ Mc) (hu : u ∈ UH153 T M V₁ Mc)
    (hv : v ∈ UH153 T M V₁ Mc) : comm153 (k * u * k⁻¹) (k * v * k⁻¹) = comm153 u v := by
  have e := cx.hF.commutator_conj hk (S153E.U_le_Q cx hu) hv
  unfold comm153
  simp only [commutatorElement_def]
  exact ite_congr_eq e

theorem comm153_mul_central_left (cx : Ctx15350 T Mc M V₁ V₂ t) {u v z : G}
    (hv : v ∈ UH153 T M V₁ Mc) (hz : z ∈ quasithinOmegaOneCenter T) :
    comm153 (u * z) v = comm153 u v := by
  have hzv : z * v = v * z := Subgroup.mem_centralizer_iff.1
    (Mc_le_centralizer_Z cx (pCoreOf_le 2 Mc (S153E.U_le_Q cx hv))) z hz
  unfold comm153
  have e : ⁅u * z, v⁆ = ⁅u, v⁆ := by
    simp only [commutatorElement_def]
    calc u * z * v * (u * z)⁻¹ * v⁻¹ = u * (z * v) * z⁻¹ * u⁻¹ * v⁻¹ := by group
      _ = u * (v * z) * z⁻¹ * u⁻¹ * v⁻¹ := by rw [hzv]
      _ = u * v * u⁻¹ * v⁻¹ := by group
  rw [e]

theorem comm153_mul_central_right (cx : Ctx15350 T Mc M V₁ V₂ t) {u v z : G}
    (hu : u ∈ UH153 T M V₁ Mc) (hz : z ∈ quasithinOmegaOneCenter T) :
    comm153 u (v * z) = comm153 u v := by
  have hzu : z * u = u * z := Subgroup.mem_centralizer_iff.1
    (Mc_le_centralizer_Z cx (pCoreOf_le 2 Mc (S153E.U_le_Q cx hu))) z hz
  unfold comm153
  have e : ⁅u, v * z⁆ = ⁅u, v⁆ := by
    simp only [commutatorElement_def]
    calc u * (v * z) * u⁻¹ * (v * z)⁻¹ = u * v * (z * u⁻¹) * z⁻¹ * v⁻¹ := by group
      _ = u * v * (u⁻¹ * z) * z⁻¹ * v⁻¹ := by
        have : z * u⁻¹ = u⁻¹ * z := by
          have h := hzu
          calc z * u⁻¹ = u⁻¹ * (u * z) * u⁻¹ := by group
            _ = u⁻¹ * (z * u) * u⁻¹ := by rw [h]
            _ = u⁻¹ * z := by group
        rw [this]
      _ = u * v * u⁻¹ * v⁻¹ := by group
  rw [e]

@[expose] noncomputable def bilU (cx : Ctx15350 T Mc M V₁ V₂ t)
    (a b : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : ZMod 2 :=
  comm153 ((Function.surjInv (piU_surjective cx) a : ↥(UH153 T M V₁ Mc)) : G)
    ((Function.surjInv (piU_surjective cx) b : ↥(UH153 T M V₁ Mc)) : G)

theorem bilU_piU (cx : Ctx15350 T Mc M V₁ V₂ t) (u v : ↥(UH153 T M V₁ Mc)) :
    bilU cx (piU cx u) (piU cx v) = comm153 (u : G) (v : G) := by
  unfold bilU
  set u' := Function.surjInv (piU_surjective cx) (piU cx u) with hu'
  set v' := Function.surjInv (piU_surjective cx) (piU cx v) with hv'
  have h1 : (u : G)⁻¹ * (u' : G) ∈ quasithinOmegaOneCenter T := by
    have : piU cx (u⁻¹ * u') = 1 := by
      rw [map_mul, map_inv, hu', Function.surjInv_eq (piU_surjective cx), inv_mul_cancel]
    simpa using (piU_eq_one_iff cx _).1 this
  have h2 : (v : G)⁻¹ * (v' : G) ∈ quasithinOmegaOneCenter T := by
    have : piU cx (v⁻¹ * v') = 1 := by
      rw [map_mul, map_inv, hv', Function.surjInv_eq (piU_surjective cx), inv_mul_cancel]
    simpa using (piU_eq_one_iff cx _).1 this
  have e1 : (u' : G) = (u : G) * ((u : G)⁻¹ * u') := by group
  have e2 : (v' : G) = (v : G) * ((v : G)⁻¹ * v') := by group
  calc comm153 (u' : G) (v' : G) = comm153 ((u : G) * ((u : G)⁻¹ * u')) (v' : G) := by rw [← e1]
    _ = comm153 (u : G) (v' : G) := comm153_mul_central_left cx v'.2 h1
    _ = comm153 (u : G) ((v : G) * ((v : G)⁻¹ * v')) := by rw [← e2]
    _ = comm153 (u : G) (v : G) := comm153_mul_central_right cx u.2 h2

theorem bilU_left (cx : Ctx15350 T Mc M V₁ V₂ t)
    (a b c : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    bilU cx (a * b) c = bilU cx a c + bilU cx b c := by
  obtain ⟨u, rfl⟩ := piU_surjective cx a
  obtain ⟨v, rfl⟩ := piU_surjective cx b
  obtain ⟨w, rfl⟩ := piU_surjective cx c
  rw [← map_mul, bilU_piU, bilU_piU, bilU_piU]
  exact comm153_mul_left cx u.2 v.2 w.2

theorem bilU_right (cx : Ctx15350 T Mc M V₁ V₂ t)
    (a b c : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    bilU cx a (b * c) = bilU cx a b + bilU cx a c := by
  obtain ⟨u, rfl⟩ := piU_surjective cx a
  obtain ⟨v, rfl⟩ := piU_surjective cx b
  obtain ⟨w, rfl⟩ := piU_surjective cx c
  rw [← map_mul, bilU_piU, bilU_piU, bilU_piU]
  exact comm153_mul_right cx u.2 v.2 w.2

theorem bilU_symm (cx : Ctx15350 T Mc M V₁ V₂ t)
    (a b : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : bilU cx a b = bilU cx b a := by
  obtain ⟨u, rfl⟩ := piU_surjective cx a
  obtain ⟨v, rfl⟩ := piU_surjective cx b
  rw [bilU_piU, bilU_piU]
  exact comm153_symm _ _

theorem bilU_inv (cx : Ctx15350 T Mc M V₁ V₂ t) {h : MulAut ↥(tildeOf (quasithinOmegaOneCenter T)
    (UH153 T M V₁ Mc))} (hh : h ∈ HStar153 T M V₁ Mc)
    (a b : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : bilU cx (h a) (h b) = bilU cx a b := by
  obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff cx Mc h).1 hh
  have hnMc : (n : G) ∈ Mc := hn
  obtain ⟨u, rfl⟩ := piU_surjective cx a
  obtain ⟨v, rfl⟩ := piU_surjective cx b
  rw [← piU_conj cx n hnMc, ← piU_conj cx n hnMc, bilU_piU, bilU_piU]
  exact comm153_conj cx hnMc u.2 v.2

theorem bilU_nondeg (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hnd : ∀ u ∈ UH153 T M V₁ Mc, (∀ v ∈ UH153 T M V₁ Mc, ⁅u, v⁆ = 1) → u ∈ quasithinOmegaOneCenter T)
    (a : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (ha : ∀ b, bilU cx a b = 0) : a = 1 := by
  obtain ⟨u, rfl⟩ := piU_surjective cx a
  rw [← map_one (piU cx)]
  have hZ : (u : G) ∈ quasithinOmegaOneCenter T := by
    apply hnd u u.2
    intro v hv
    have := ha (piU cx ⟨v, hv⟩)
    rw [bilU_piU] at this
    unfold comm153 at this
    by_contra hne
    simp [hne] at this
  have : piU cx u = 1 := (piU_eq_one_iff cx u).2 hZ
  rw [this, map_one]

end Form

end S153E58

end CFSG.Quasithin
